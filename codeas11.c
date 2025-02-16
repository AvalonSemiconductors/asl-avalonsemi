/*
 * (Tholin, 20/10/2024) Added support for AS-11
 */

#include "stdinc.h"
#include <string.h>
#include <ctype.h>

#include "nls.h"
#include "chunks.h"
#include "bpemu.h"
#include "strutil.h"

#include "asmdef.h"
#include "asmsub.h"
#include "asmpars.h"
#include "asmitree.h"
#include "codevars.h"
#include "headids.h"
#include "intpseudo.h"
#include "errmsg.h"

#include "codeas11.h"

static CPUVar CPUAS11;

#define MODE_REGISTER 0
#define MODE_DEFERRED 1
#define MODE_AUTOINCREMENT 2
#define MODE_AUTOINCREMENT_DEFERRED 3
#define MODE_AUTODECREMENT 4
#define MODE_AUTODECREMENT_DEFERRED 5
#define MODE_INDEXED 6
#define MODE_INDEXED_DEFERRED 7

static Boolean DecodeMode(struct sStrComp *pComp, Boolean bodgefix, Boolean secondarg, Word *mode, Byte *reg, sint *immediate, Boolean *has_immediate) {
	*reg = 0;
	*has_immediate = False;
	Boolean OK;
	char* pAsc = pComp->str.p_str;
	int len = strlen(pAsc);
	if(pAsc[0] == 'R' || pAsc[0] == 'r') {
		if(len < 2) goto bad_reg;
		*reg = pAsc[1] - '0';
		if(*reg < 0 || *reg >= 8 || pAsc[2] != 0) goto bad_reg;
		*mode = MODE_REGISTER;
		return True;
	}
	Boolean deferred = False;
	if(pAsc[0] == '@') {
		deferred = True;
		StrCompCutLeft(pComp, 1);
		len = strlen(pAsc);
	}
	if(pAsc[0] == '-') {
		if(pAsc[1] != '(' || pAsc[len-1] != ')') return False;
		StrCompCutLeft(pComp, 2);
		StrCompShorten(pComp, 1);
		if((pAsc[0] != 'R' && pAsc[0] != 'r') || pAsc[2] != 0) goto bad_reg;
		*reg = pAsc[1] - '0';
		if(*reg < 0 || *reg >= 8) goto bad_reg;
		*mode = deferred ? MODE_AUTODECREMENT_DEFERRED : MODE_AUTODECREMENT;
		return True;
	}
	if(pAsc[0] == '#') {
		*reg = 7;
		*mode = deferred ? MODE_AUTOINCREMENT_DEFERRED : MODE_AUTOINCREMENT;
		StrCompCutLeft(pComp, 1);
		len = strlen(pAsc);
		*immediate = (Word)EvalStrIntExpression(pComp, Int16, &OK);
		*has_immediate = True;
		return OK;
	}
	if(pAsc[0] == '(') {
		//Register Deferred, Autoincrement or Autoincrement Deferred
		Boolean autoincrement = False;
		if(pAsc[len-1] == '+') {
			autoincrement = True;
			StrCompShorten(pComp, 1);
			len = strlen(pAsc);
		}
		if(pAsc[len-1] != ')') return False;
		StrCompCutLeft(pComp, 1);
		//Note: @(Rn) is not a valid combination!
		if(deferred && !autoincrement) return False;
		len = strlen(pAsc);
		if(pAsc[0] != 'R' && pAsc[0] != 'r') goto bad_reg;
		*reg = pAsc[1] - '0';
		if(*reg < 0 || *reg >= 8) goto bad_reg;
		*mode = autoincrement ? (deferred ? MODE_AUTOINCREMENT_DEFERRED : MODE_AUTOINCREMENT) : MODE_DEFERRED;
		return True;
	}
	
	//If all else fails, try to parse immediate
	//First, search for ')' in string
	//If found: relative or relative deferred
	//Otherwise: Indexed/Indexed Deferred
	if(pAsc[len-1] == '+') return False;
	if(pAsc[len-1] == ')') {
		if(pAsc[len-4] != '(') return False;
		if(pAsc[len-3] != 'R' && pAsc[len-3] != 'r') goto bad_reg;
		*reg = pAsc[len-2] - '0';
		if(*reg < 0 || *reg >= 8) goto bad_reg;
		StrCompShorten(pComp, 4);
		len = strlen(pAsc);
		*mode = deferred ? MODE_INDEXED_DEFERRED : MODE_INDEXED;
		Word target = EvalStrIntExpression(pComp, UInt16, &OK);
		if(!OK) return False;
		*immediate = target;
		*has_immediate = True;
		return OK;
	}
	*mode = deferred ? MODE_INDEXED_DEFERRED : MODE_INDEXED;
	*reg = 7;
	Word target = EvalStrIntExpression(pComp, UInt16, &OK);
	if(!OK) return False;
	sint diff = (sint)target - (sint)EProgCounter() - (bodgefix ? 4 : 2) - (secondarg ? 2 : 0);
	if(diff >= 32768 || diff < -32768) {
		WrStrErrorPos(ErrNum_WOverRange, pComp);
		return False;
	}
	*immediate = diff;
	*has_immediate = True;
	return OK;
bad_reg:
	WrStrErrorPos(ErrNum_InvReg, pComp);
	return False;
}

static void DecodeSingle(Word Index) {
	if(!ChkArgCnt(1, 1));
	else {
		Word mode;
		Byte reg;
		sint immediate;
		Boolean has_immediate;
		Boolean OK = DecodeMode(&ArgStr[1], False, Index == 1, &mode, &reg, &immediate, &has_immediate);
		if(!OK) {
			WrError(ErrNum_InvAddrMode);
			return;
		}
		CodeLen = 2;
		WAsmCode[0] = (Index << 6) | (mode << 3) | reg;
		if(has_immediate) {
			CodeLen = 4;
			WAsmCode[1] = (Word)immediate;
		}
	}
}

static void DecodeDouble(Word Index) {
	if(!ChkArgCnt(2, 2));
	else {
		Word mode;
		Byte reg;
		sint immediate;
		Boolean has_immediate;
		Boolean OK = DecodeMode(&ArgStr[1], False, False, &mode, &reg, &immediate, &has_immediate);
		if(!OK) {
			WrError(ErrNum_InvAddrMode);
			return;
		}
		Word mode2;
		Byte reg2;
		sint immediate2;
		Boolean has_immediate2;
		OK = DecodeMode(&ArgStr[2], has_immediate, True, &mode2, &reg2, &immediate2, &has_immediate2);
		if(!OK) {
			WrError(ErrNum_InvAddrMode);
			return;
		}
		if(has_immediate && has_immediate2 && reg == 7 && (mode == MODE_INDEXED_DEFERRED || mode == MODE_INDEXED)) {
			immediate -= 2;
		}
		CodeLen = 2;
		WAsmCode[0] = (Index << 12) | (mode << 9) | (reg << 6) | (mode2 << 3) | reg2;
		if(has_immediate) {
			CodeLen = 4;
			WAsmCode[1] = (Word)immediate;
		}
		if(has_immediate2) {
			WAsmCode[CodeLen == 2 ? 1 : 2] = (Word)immediate2;
			CodeLen += 2;
		}
	}
}

//Note: order of operands may swap here, since its opcode src,dest
static void DecodeRegSource(Word Index) {
	if(!ChkArgCnt(2, 2));
	else {
		Boolean swap = (Index & 32768) != 0;
		Word mode;
		Byte reg;
		sint immediate;
		Boolean has_immediate;
		Boolean OK = DecodeMode(&ArgStr[swap ? 1 : 2], False, False, &mode, &reg, &immediate, &has_immediate);
		if(!OK) {
			WrError(ErrNum_InvAddrMode);
			return;
		}
		char* pAsc = ArgStr[swap ? 2 : 1].str.p_str;
		if(pAsc[0] != 'R' && pAsc[0] != 'r') {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[swap ? 2 : 1]);
			return;
		}
		Byte reg2 = pAsc[swap ? 2 : 1] - '0';
		if(reg2 < 0 || reg2 >= 8) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[swap ? 2 : 1]);
			return;
		}
		CodeLen = 2;
		WAsmCode[0] = ((Index & 0x7FFF) << 9) | (reg2 << 6) | (mode << 3) | reg;
		if(has_immediate) {
			CodeLen = 4;
			WAsmCode[1] = (Word)immediate;
		}
	}
}

static void DecodeJSR(Word Index) {
	if(!ChkArgCnt(1, 2));
	else {
		if(ArgCnt == 2) DecodeRegSource(Index);
		else {
			Word mode;
			Byte reg;
			sint immediate;
			Boolean has_immediate;
			Boolean OK = DecodeMode(&ArgStr[1], False, False, &mode, &reg, &immediate, &has_immediate);
			if(!OK) {
				WrError(ErrNum_InvAddrMode);
				return;
			}
			CodeLen = 2;
			WAsmCode[0] = (Index << 9) | (7 << 6) | (mode << 3) | reg;
			if(has_immediate) {
				CodeLen = 4;
				WAsmCode[1] = (Word)immediate;
			}
		}
	}
}

static void DecodeRTS(Word Index) {
	if(!ChkArgCnt(0, 1));
	else {
		Byte reg = 7;
		if(ArgCnt == 1) {
			char* pAsc = ArgStr[1].str.p_str;
			if(pAsc[0] != 'R' && pAsc[0] != 'r') {
				WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
				return;
			}
			if(reg < 0 || reg >= 8) {
				WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
				return;
			}
		}
		CodeLen = 2;
		WAsmCode[0] = (Index << 3) | reg;
	}
}

static void DecodeBranch(Word Index) {
	if(!ChkArgCnt(1, 1));
	else {
		Boolean OK;
		Word dest = EvalStrIntExpression(&ArgStr[1], UInt16, &OK);
		if(OK) {
			sint diff = (sint)dest - (sint)EProgCounter() - 2;
			if((diff & 1) != 0) {
				WrStrErrorPos(ErrNum_NotAligned, &ArgStr[1]);
				return;
			}
			if(diff >= 256 || diff < -256) {
				WrStrErrorPos(ErrNum_DistTooBig, &ArgStr[1]);
				return;
			}
			CodeLen = 2;
			WAsmCode[0] = (Index << 8) | (Byte)((Word)diff >> 1);
		}
	}
}

static void DecodeMark(Word Index) {
	if(!ChkArgCnt(1, 1));
	else {
		Boolean OK;
		if(ArgStr[1].str.p_str[0] != '#') {
			WrError(ErrNum_InvAddrMode);
			return;
		}
		StrCompCutLeft(&ArgStr[1], 1);
		Word dest = EvalStrIntExpression(&ArgStr[1], UInt6, &OK);
		if(OK) {
			if((dest & 1) != 0) WrStrErrorPos(ErrNum_NotAligned, &ArgStr[1]);
			else {
				WAsmCode[0] = Index | (dest >> 1);
				CodeLen = 2;
			}
		}
	}
}

static void DecodeTrap(Word Index) {
	if(!ChkArgCnt(0, 1));
	else {
		Word imm = 0x0621;
		if(ArgCnt == 1) {
			if(ArgStr[1].str.p_str[0] != '#') {
				WrError(ErrNum_InvAddrMode);
				return;
			}
			StrCompCutLeft(&ArgStr[1], 1);
			Boolean OK;
			imm = EvalStrIntExpression(&ArgStr[1], UInt8, &OK);
			if(!OK) return;
		}
		WAsmCode[0] = Index | imm;
		CodeLen = 2;
	}
}

static void DecodeSOB(Word Index) {
	if(!ChkArgCnt(2, 2));
	else {
		if(ArgStr[2].str.p_str[0] == '#' || ArgStr[2].str.p_str[0] == '@') {
			WrError(ErrNum_InvAddrMode);
			return;
		}
		Boolean OK;
		Word dest = EvalStrIntExpression(&ArgStr[2], UInt16, &OK);
		if(!OK) return;
		sint diff = (sint)dest - (sint)EProgCounter() - 2;
		if((diff & 1) != 0) {
			WrStrErrorPos(ErrNum_NotAligned, &ArgStr[2]);
			return;
		}
		if(diff > 0 || diff < -126) {
			WrStrErrorPos(ErrNum_DistTooBig, &ArgStr[2]);
			return;
		}
		diff = (-diff) >> 1;
		
		char* pAsc = ArgStr[1].str.p_str;
		if(pAsc[0] != 'R' && pAsc[0] != 'r') {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
			return;
		}
		Byte reg2 = pAsc[1] - '0';
		if(reg2 < 0 || reg2 >= 8) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
			return;
		}
		
		WAsmCode[0] = Index | diff | (reg2 << 6);
		CodeLen = 2;
	}
}

static void DecodeCC(Word Index) {
	if(!ChkArgCnt(1, 1));
	else {
		Word clear = 0xF;
		if(ArgCnt == 1) {
			if(ArgStr[1].str.p_str[0] != '#') {
				WrError(ErrNum_InvAddrMode);
				return;
			}
			StrCompCutLeft(&ArgStr[1], 1);
			Boolean OK;
			clear = EvalStrIntExpression(&ArgStr[1], UInt4, &OK);
			if(!OK) return;
		}
		WAsmCode[0] = Index | clear;
		CodeLen = 2;
	}
}

static void DecodeImplied(Word Index) {
	CodeLen = 2;
	WAsmCode[0] = Index;
}

static void AddImplied(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeImplied);
}

static void AddBranch(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeBranch);
}

static void AddRegSource(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeRegSource);
}

static void AddDouble(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeDouble);
}

static void AddSingle(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeSingle);
}

static void InitFields(void) {
	InstTable = CreateInstTable(100);
	
	AddSingle("CLR", 0b0000101000);
	AddSingle("CLRB", 0b1000101000);
	AddSingle("COM", 0b0000101001);
	AddSingle("COMB", 0b1000101001);
	AddSingle("INC", 0b0000101010);
	AddSingle("INCB", 0b1000101010);
	AddSingle("DEC", 0b0000101011);
	AddSingle("DECB", 0b1000101011);
	AddSingle("NEG", 0b0000101100);
	AddSingle("NEGB", 0b1000101100);
	AddSingle("TST", 0b0000101111);
	AddSingle("TSTB", 0b1000101111);
	AddSingle("ASR", 0b0000110010);
	AddSingle("ASRB", 0b1000110010);
	AddSingle("ASL", 0b0000110011);
	AddSingle("ASLB", 0b1000110011);
	AddSingle("ROR", 0b0000110000);
	AddSingle("RORB", 0b1000110000);
	AddSingle("ROL", 0b0000110001);
	AddSingle("ROLB", 0b1000110001);
	AddSingle("SWAB", 0b0000000011);
	AddSingle("ADC", 0b0000101101);
	AddSingle("ADCB", 0b1000101101);
	AddSingle("SBC", 0b0000101110);
	AddSingle("SBCB", 0b1000101110);
	AddSingle("SXT", 0b0000110111);
	
	AddDouble("MOV", 0b0001);
	AddDouble("MOVB", 0b1001);
	AddDouble("CMP", 0b0010);
	AddDouble("CMPB", 0b1010);
	AddDouble("ADD", 0b0110);
	AddDouble("SUB", 0b1110);
	AddDouble("BIT", 0b0011);
	AddDouble("BITB", 0b1011);
	AddDouble("BIC", 0b0100);
	AddDouble("BICB", 0b1100);
	AddDouble("BIS", 0b0101);
	AddDouble("BISB", 0b1101);
	
	AddRegSource("MUL", 0b0111000);
	AddRegSource("DIV", 0b0111001);
	AddRegSource("ASH", 0b0111010);
	AddRegSource("ASHC", 0b0111011);
	AddRegSource("XOR", 0b0111100);
	
	AddBranch("BR", 0b00000001);
	AddBranch("BNE", 0b00000010);
	AddBranch("BEQ", 0b00000011);
	AddBranch("BPL", 0b10000000);
	AddBranch("BMI", 0b10000001);
	AddBranch("BVC", 0b10000100);
	AddBranch("BVS", 0b10000101);
	AddBranch("BCC", 0b10000110);
	AddBranch("BCS", 0b10000111);
	AddBranch("BGE", 0b00000100);
	AddBranch("BLT", 0b00000101);
	AddBranch("BGT", 0b00000110);
	AddBranch("BLE", 0b00000111);
	AddBranch("BHI", 0b10000010);
	AddBranch("BLOS", 0b10000011);
	
	AddSingle("JMP", 0b0000000001);
	
	AddInstTable(InstTable, "JSR", 0b0000100, DecodeJSR);
	
	AddInstTable(InstTable, "RTS", 0b0000000010000, DecodeRTS);
	
	AddInstTable(InstTable, "MARK", 0b0000110100000000, DecodeMark);
	AddInstTable(InstTable, "SOB", 0b0111111000000000, DecodeSOB);
	AddInstTable(InstTable, "EMT", 0b1000100000000000, DecodeTrap);
	AddInstTable(InstTable, "TRAP", 0b1000100100000000, DecodeTrap);
	
	AddImplied("BPT", 0b11);
	AddImplied("IOT", 0b100);
	AddImplied("RTI", 0b10);
	AddImplied("RTT", 0b110);
	AddImplied("HALT", 0b0);
	AddImplied("WAIT", 0b1);
	AddImplied("RESET", 0b101);
	AddImplied("SVB", 0b1111000000000100);
	AddImplied("TRACE", 0b1111000000001010);
	
	AddSingle("MFPS", 0b1000110111);
	AddSingle("MTPS", 0b1000110100);
	
	AddImplied("MFTP", 0b1111000000000011);
	
	AddRegSource("IOR", 0b0111101 + 32768);
	AddRegSource("IOW", 0b0111110 + 32768);
	
	AddImplied("CLC", 0x00A1);
	AddImplied("CLV", 0x00A2);
	AddImplied("CLZ", 0x00A4);
	AddImplied("CLN", 0x00A8);
	AddImplied("SEC", 0x00B1);
	AddImplied("SEV", 0x00B2);
	AddImplied("SEZ", 0x00B4);
	AddImplied("SEN", 0x00B8);
	AddImplied("NOP", 0x00A0);
	
	AddInstTable(InstTable, "SCC", 0x0B0, DecodeCC);
	AddInstTable(InstTable, "CCC", 0x0A0, DecodeCC);
}

static void DeinitFields(void) {
	DestroyInstTable(InstTable);
}

static void MakeCode_as11(void) {
	char *pPos;
	CodeLen = 0;
	DontPrint = False;
	
	if((*OpPart.str.p_str == '\0') && (ArgCnt == 0)) return;
	if(DecodeIntelPseudo(False)) return;
	
	pPos = strchr(OpPart.str.p_str, ',');
	if(pPos) {
		int ArgC;
		InsertArg(1, strlen(OpPart.str.p_str));
		StrCompSplitRight(&OpPart, &ArgStr[1], pPos);
	}
	if(!LookupInstTable(InstTable, OpPart.str.p_str)) WrStrErrorPos(ErrNum_UnknownInstruction, &OpPart);
}

static Boolean IsDef_as11(void) {
	return FALSE;
}

static void SwitchFrom_as11(void) {
	DeinitFields();
}

static void SwitchTo_as11(void) {
	const TFamilyDescr *pDescr;
	TurnWords = False; SetIntConstMode(eIntConstModeMoto); ShiftIsOccupied = False;
	pDescr = FindFamilyByName("AS-11");
	PCSymbol = "$"; HeaderID = pDescr->Id; NOPCode = 0x00A0;
	DivideChars = ","; HasAttrs = False;
	
	ValidSegs = (1 << SegCode);
	Grans[SegCode] = 1; ListGrans[SegCode] = 2; SegInits[SegCode] = 0;
	SegLimits[SegCode] = 0xffffl;
	MakeCode = MakeCode_as11; IsDef = IsDef_as11;
	
	SwitchFrom = SwitchFrom_as11; InitFields();
}

void codeas11_init(void) {
	CPUAS11 = AddCPU("AS-11", SwitchTo_as11);
}
