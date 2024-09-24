/* codeas2650-2.c */

/*
 * (Tholin, 24/09/2024) Added support for AS2650-2
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

#include "codeas2650-2.h"

static CPUVar CPUAS2650;

static Boolean DecodeReg(const char *pAsc, Byte *pRes, char *modifier) {
	Boolean Result;
	*modifier = 0;
	int aaa = strlen(pAsc);
	if(aaa == 3) {
		*modifier = pAsc[2];
	}
	
	Result = ((aaa == 2 || aaa == 3) && (_toupper(pAsc[0]) == 'R') && (pAsc[1] >= '0') && (pAsc[1] <= '3'));
	if(Result) *pRes = pAsc[1] - '0';
	return Result;
}

static Boolean DecodeCondition(const char *pAsc, Byte *pRes) {
	Boolean Result = TRUE;
	
	if(!strcasecmp(pAsc, "EQ") || !strcasecmp(pAsc, "0")) *pRes = 0;
	else if(!strcasecmp(pAsc, "GT") || !strcasecmp(pAsc, "1")) *pRes = 1;
	else if(!strcasecmp(pAsc, "LT") || !strcasecmp(pAsc, "2")) *pRes = 2;
	else if((!strcasecmp(pAsc, "ALWAYS")) || (!strcasecmp(pAsc, "UN"))) *pRes = 3;
	else Result = FALSE;
	
	return Result;
}

static void DecodeFixed(Word Index) {
	if(ChkArgCnt(0, 0)) {
		CodeLen = 0;
		if((Index & 16384) != 0) {
			BAsmCode[CodeLen] = 0xB7;
			CodeLen++;
			Index &= 0xFF;
		}
		BAsmCode[CodeLen] = Index;
		CodeLen++;
	}
}

static void DecodeOneReg(Word Index) {
	Byte Reg;
	char mod = 0;
	
	if(!ChkArgCnt(1, 1));
	else if(!DecodeReg(ArgStr[1].str.p_str, &Reg, &mod) || mod != 0) WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
	else {
		CodeLen = 0;
		if((Index & 16384) != 0) {
			BAsmCode[CodeLen] = 0xB7;
			CodeLen++;
			Index &= 0xFF;
		}
		BAsmCode[CodeLen] = Index | Reg;
		CodeLen++;
	}
}

static void DecodeImm(Word Index) {
	Boolean OK;
	
	if(ChkArgCnt(1, 1)) {
		BAsmCode[1] = EvalStrIntExpression(&ArgStr[1], Int8, &OK);
		if(OK) {
			BAsmCode[0] = Index;
			CodeLen = 2;
		}
	}
}

static void DecodeRegImm(Word Index) {
	Byte Reg;
	Boolean OK;
	char mod;
	
	if(!ChkArgCnt(2, 2));
	else if(!DecodeReg(ArgStr[1].str.p_str, &Reg, &mod) || mod != 0) WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
	else {
		BAsmCode[1] = EvalStrIntExpression(&ArgStr[2], Int8, &OK);
		if(OK) {
			BAsmCode[0] = Index | Reg;
			CodeLen = 2;
		}
	}
}

static void DecodeRegAbs(Word Index) {
	Byte DReg, IReg;
	Word AbsVal;
	Boolean OK, IndFlag;
	char mod;
	
	if(!ChkArgCnt(2, 4));
	else if(!DecodeReg(ArgStr[1].str.p_str, &DReg, &mod) || mod != 0) WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
	else {
		IndFlag = *ArgStr[2].str.p_str == '*';
		AbsVal = EvalStrIntExpressionOffs(&ArgStr[2], IndFlag, UInt16, &OK);
		if(!OK) return;
		
		if((AbsVal & 0xE000) != (EProgCounter() & 0xE000)) {
			WrError(ErrNum_InvAddrMode);
			return;
		}
		AbsVal &= 0x1FFF;
		
		BAsmCode[0] = Index;
		BAsmCode[1] = Hi(AbsVal);
		BAsmCode[2] = Lo(AbsVal);
		if(IndFlag) BAsmCode[1] |= 0x80;
		if(ArgCnt == 2) {
			BAsmCode[0] |= DReg;
			CodeLen = 3;
		}else {
			if(!DecodeReg(ArgStr[3].str.p_str, &IReg, &mod)) WrStrErrorPos(ErrNum_InvReg, &ArgStr[3]);
			else if (DReg != 0) WrError(ErrNum_InvAddrMode);
			else {
				BAsmCode[0] |= IReg;
				if(mod == 0) {
					BAsmCode[1] |= 0x60;
					CodeLen = 3;
				}
				else if(mod == '-') {
					BAsmCode[1] |= 0x40;
					CodeLen = 3;
				}else if(mod == '+') {
					BAsmCode[1] |= 0x20;
					CodeLen = 3;
				}else WrError(ErrNum_InvAddrMode);
			}
		}
	}
}

static void DecodeRegRel(Word Index) {
	Byte Reg;
	Boolean IndFlag, OK;
	int Dist;
	char mod;
	
	if(!ChkArgCnt(2, 2));
	else if(!DecodeReg(ArgStr[1].str.p_str, &Reg, &mod) || mod != 0) WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
	else {
		BAsmCode[0] = Index | Reg;
		IndFlag = *ArgStr[2].str.p_str == '*';
		Dist = EvalStrIntExpressionOffs(&ArgStr[2], IndFlag, UInt15, &OK) - (EProgCounter() + 2);
		if(OK) {
			if(((Dist < - 64) || (Dist > 63)) && (!eSymbolFlag_Questionable)) WrError(ErrNum_JmpDistTooBig);
			else {
				BAsmCode[1] = Dist & 0x7f;
				if(IndFlag) BAsmCode[1] |= 0x80;
				CodeLen = 2;
			}
		}
	}
}

static void DecodeCondAbs(Word Index) {
	Byte Cond;
	Word Address;
	Boolean OK, IndFlag;
	
	if(!ChkArgCnt(2, 2));
	else if(!DecodeCondition(ArgStr[1].str.p_str, &Cond)) WrStrErrorPos(ErrNum_UndefCond, &ArgStr[1]);
	else {
		IndFlag = *ArgStr[2].str.p_str == '*';
		Address = EvalStrIntExpressionOffs(&ArgStr[2], IndFlag, UInt16, &OK);
		if(OK) {
			if((Address & 0x8000) != (EProgCounter() & 0x8000)) {
				WrError(ErrNum_InvAddrMode);
				return;
			}
			Address &= 0x7FFF;
			BAsmCode[0] = Index | Cond;
			BAsmCode[1] = Hi(Address);
			if(IndFlag) BAsmCode[1] |= 0x80;
			BAsmCode[2] = Lo(Address);
			CodeLen = 3;
		}
	}
}

static void DecodeCondFar(Word Index) {
	Byte Cond;
	Word Address;
	Boolean OK;
	if(!ChkArgCnt(2, 2));
	else if(!DecodeCondition(ArgStr[1].str.p_str, &Cond)) WrStrErrorPos(ErrNum_UndefCond, &ArgStr[1]);
	else {
		Address = EvalStrIntExpressionOffs(&ArgStr[2], 0, UInt16, &OK);
		if(OK) {
			BAsmCode[0] = 0xB7;
			BAsmCode[1] = Index | Cond;
			BAsmCode[2] = Hi(Address);
			BAsmCode[3] = Lo(Address);
			CodeLen = 4;
		}
	}
}

static void DecodeCondRel(Word Index) {
	Byte Cond;
	Boolean IndFlag, OK;
	int Dist;
	
	if(!ChkArgCnt(2, 2));
	else if(!DecodeCondition(ArgStr[1].str.p_str, &Cond)) WrStrErrorPos(ErrNum_UndefCond, &ArgStr[1]);
	else {
		BAsmCode[0] = Index | Cond;
		IndFlag = *ArgStr[2].str.p_str == '*';
		Dist = EvalStrIntExpressionOffs(&ArgStr[2], IndFlag, UInt15, &OK) - (EProgCounter() + 2);
		if(OK) {
			if(((Dist < - 64) || (Dist > 63)) && (!eSymbolFlag_Questionable)) WrError(ErrNum_JmpDistTooBig);
			else {
				BAsmCode[1] = Dist & 0x7f;
				if(IndFlag) BAsmCode[1] |= 0x80;
				CodeLen = 2;
			}
		}
	}
}

static void DecodeRegAbs2(Word Index) {
	Byte Reg;
	Word AbsVal;
	Boolean IndFlag, OK;
	char mod;
	
	if(!ChkArgCnt(2, 2));
	else if(!DecodeReg(ArgStr[1].str.p_str, &Reg, &mod) || mod != 0) WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
	else {
		BAsmCode[0] = Index | Reg;
		IndFlag = *ArgStr[2].str.p_str == '*';
		AbsVal = EvalStrIntExpressionOffs(&ArgStr[2], IndFlag, UInt16, &OK);
		if((AbsVal & 0x8000) != (EProgCounter() & 0x8000)) {
			WrError(ErrNum_InvAddrMode);
			return;
		}
		AbsVal &= 0x7FFF;
		if(OK) {
			BAsmCode[1] = Hi(AbsVal);
			if(IndFlag) BAsmCode[1] |= 0x80;
			BAsmCode[2] = Lo(AbsVal);
			CodeLen = 3;
		}
	}
}

static void DecodeRegFar(Word Index) {
	Byte Reg;
	Word AbsVal;
	Boolean OK;
	char mod;
	
	if(!ChkArgCnt(2, 2));
	else if(!DecodeReg(ArgStr[1].str.p_str, &Reg, &mod) || mod != 0) WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
	else {
		BAsmCode[0] = Index | Reg;
		AbsVal = EvalStrIntExpressionOffs(&ArgStr[2], 0, UInt16, &OK);
		if(OK) {
			BAsmCode[1] = Hi(AbsVal);
			BAsmCode[2] = Lo(AbsVal);
			CodeLen = 3;
		}
	}
}

static void DecodeBrAbs(Word Index) {
	Byte Reg = 3;
	Word AbsVal;
	Boolean IndFlag, OK;
	char mod;
	
	if(!ChkArgCnt(1, 2));
	else if((ArgCnt == 2) && (!DecodeReg(ArgStr[2].str.p_str, &Reg, &mod) || mod != 0)) WrStrErrorPos(ErrNum_InvReg, &ArgStr[2]);
	else if(Reg != 3) WrError(ErrNum_InvAddrMode);
	else {
		BAsmCode[0] = Index | Reg;
		IndFlag = *ArgStr[1].str.p_str == '*';
		AbsVal = EvalStrIntExpressionOffs(&ArgStr[1], IndFlag, UInt13, &OK);
		if(OK) {
			BAsmCode[1] = Hi(AbsVal);
			if(IndFlag) BAsmCode[1] |= 0x80;
			BAsmCode[2] = Lo(AbsVal);
			CodeLen = 3;
		}
	}
}

static void DecodeCond(Word Index) {
	Byte Cond;
	
	if(!ChkArgCnt(1, 1));
	else if(!DecodeCondition(ArgStr[1].str.p_str, &Cond)) WrStrErrorPos(ErrNum_UndefCond, &ArgStr[1]);
	else {
		BAsmCode[0] = Index | Cond;
		CodeLen = 1;
	}
}

static void DecodeZero(Word Index) {
	Boolean IndFlag, OK;
	
	if(ChkArgCnt(1, 1)) {
		BAsmCode[0] = Index;
		IndFlag = *ArgStr[1].str.p_str == '*';
		BAsmCode[1] = EvalStrIntExpressionOffs(&ArgStr[1], IndFlag, UInt7, &OK);
		if(!OK) return;
		if(IndFlag) BAsmCode[1] |= 0x80; 
		CodeLen = 2;
	}
}

static void AddFixed(char *pName, Word Code, Boolean Extended) {
	AddInstTable(InstTable, pName, Code | (Extended ? 16384 : 0), DecodeFixed);
}

static void AddOneReg(char *pName, Word Code, Boolean Extended) {
	AddInstTable(InstTable, pName, Code | (Extended ? 16384 : 0), DecodeOneReg);
}

static void AddImm(char *pName, Word Code, Boolean Extended) {
	AddInstTable(InstTable, pName, Code, DecodeImm);
}

static void AddRegImm(char *pName, Word Code, Boolean Extended) {
	AddInstTable(InstTable, pName, Code, DecodeRegImm);
}

static void AddRegAbs(char *pName, Word Code, Boolean Extended) {
	AddInstTable(InstTable, pName, Code, DecodeRegAbs);
}

static void AddRegRel(char *pName, Word Code, Boolean Extended) {
	AddInstTable(InstTable, pName, Code, DecodeRegRel);
}

static void AddCondAbs(char *pName, Word Code, Boolean Extended) {
	AddInstTable(InstTable, pName, Code, DecodeCondAbs);
}

static void AddCondRel(char *pName, Word Code, Boolean Extended) {
	AddInstTable(InstTable, pName, Code, DecodeCondRel);
}

static void AddRegAbs2(char *pName, Word Code, Boolean Extended) {
	AddInstTable(InstTable, pName, Code, DecodeRegAbs2);
}
   
static void AddBrAbs(char *pName, Word Code, Boolean Extended) {
	AddInstTable(InstTable, pName, Code, DecodeBrAbs);
}  

static void AddCond(char *pName, Word Code, Boolean Extended) {
	AddInstTable(InstTable, pName, Code, DecodeCond);
}

static void AddZero(char *pName, Word Code, Boolean Extended) {
	AddInstTable(InstTable, pName, Code, DecodeZero);
}

static void AddCondFar(char *pName, Word Code) {
	AddInstTable(InstTable, pName, Code, DecodeCondFar);
}

static void AddRegFar(char *pName, Word Code) {
	AddInstTable(InstTable, pName, Code, DecodeRegFar);
}

static void InitFields(void) {
	InstTable = CreateInstTable(203);
	
	AddFixed("NOP", 0xc0, FALSE);
	AddFixed("HALT", 0x40, FALSE);
	AddFixed("LPSL", 0x93, FALSE);
	AddFixed("LPSU", 0x92, FALSE);
	AddFixed("SPSL", 0x13, FALSE);
	AddFixed("SPSU", 0x12, FALSE);
	AddFixed("MUL", 0x90, FALSE);
	AddFixed("XCHG", 0x91, FALSE);
	AddFixed("TRAP", 0x90, TRUE);
	AddFixed("CLRT", 0x91, TRUE);
	AddFixed("PSHS", 0x10, TRUE);
	AddFixed("POPS", 0x11, TRUE);
	AddFixed("SVB", 0x12, TRUE);
	AddFixed("CHRP", 0x13, TRUE);
	AddFixed("LIR", 0x92, TRUE);
	AddFixed("SIR", 0x93, TRUE);
	
	AddOneReg("ADDZ", 0x80, FALSE);
	AddOneReg("ANDZ", 0x40, FALSE);
	AddOneReg("COMZ", 0xe0, FALSE);
	AddOneReg("DAR", 0x94, FALSE);
	AddOneReg("EORZ", 0x20, FALSE);
	AddOneReg("IORZ", 0x60, FALSE);
	AddOneReg("LODZ", 0x00, FALSE);
	AddOneReg("REDC", 0x30, FALSE);
	AddOneReg("REDD", 0x70, FALSE);
	AddOneReg("RRL", 0xd0, FALSE);
	AddOneReg("RRR", 0x50, FALSE);
	AddOneReg("STRZ", 0xc0, FALSE);
	AddOneReg("SUBZ", 0xa0, FALSE);
	AddOneReg("WRTC", 0xb0, FALSE);
	AddOneReg("WRTD", 0xf0, FALSE);
	AddOneReg("CLR", 0xc4, FALSE);
	AddOneReg("CPL", 0xe0, TRUE);
	
	AddImm("CPSL", 0x75, FALSE);
	AddImm("CPSU", 0x74, FALSE);
	AddImm("PPSL", 0x77, FALSE);
	AddImm("PPSU", 0x76, FALSE);
	AddImm("TPSL", 0xb5, FALSE);
	AddImm("TPSU", 0xb4, FALSE);
	
	AddRegImm("ADDI", 0x84, FALSE);
	AddRegImm("ANDI", 0x44, FALSE);
	AddRegImm("COMI", 0xe4, FALSE);
	AddRegImm("EORI", 0x24, FALSE);
	AddRegImm("IORI", 0x64, FALSE);
	AddRegImm("LODI", 0x04, FALSE);
	AddRegImm("REDE", 0x54, FALSE);
	AddRegImm("SUBI", 0xa4, FALSE);
	AddRegImm("TMI", 0xf4, FALSE);
	AddRegImm("WRTE", 0xd4, FALSE);
	
	AddRegAbs("ADDA", 0x8c, FALSE);
	AddRegAbs("ANDA", 0x4c, FALSE);
	AddRegAbs("COMA", 0xec, FALSE);
	AddRegAbs("EORA", 0x2c, FALSE);
	AddRegAbs("IORA", 0x6c, FALSE);
	AddRegAbs("LODA", 0x0c, FALSE);
	AddRegAbs("STRA", 0xcc, FALSE);
	AddRegAbs("SUBA", 0xac, FALSE);
	
	AddRegRel("ADDR", 0x88, FALSE);
	AddRegRel("ANDR", 0x48, FALSE);
	AddRegRel("BDRR", 0xf8, FALSE);
	AddRegRel("BIRR", 0xd8, FALSE);
	AddRegRel("BRNR", 0x58, FALSE);
	AddRegRel("BSNR", 0x78, FALSE);
	AddRegRel("COMR", 0xe8, FALSE);
	AddRegRel("EORR", 0x28, FALSE);
	AddRegRel("IORR", 0x68, FALSE);
	AddRegRel("LODR", 0x08, FALSE);
	AddRegRel("STRR", 0xc8, FALSE);
	AddRegRel("SUBR", 0xa8, FALSE);
	
	AddCondAbs("BCFA", 0x9c, FALSE);
	AddCondAbs("BCTA", 0x1c, FALSE);
	AddCondAbs("BSFA", 0xbc, FALSE);
	AddCondAbs("BSTA", 0x3c, FALSE);
	
	AddCondRel("BCFR", 0x98, FALSE);
	AddCondRel("BCTR", 0x18, FALSE);
	AddCondRel("BSFR", 0xb8, FALSE);
	AddCondRel("BSTR", 0x38, FALSE);
	
	AddRegAbs2("BDRA", 0xfc, FALSE);
	AddRegAbs2("BIRA", 0xdc, FALSE);
	AddRegAbs2("BRNA", 0x5c, FALSE);
	AddRegAbs2("BSNA", 0x7c, FALSE);
	
	AddBrAbs("BSXA", 0xbf, FALSE);
	AddBrAbs("BXA", 0x9f, FALSE);
	
	AddCond("RETC", 0x14, FALSE);
	AddCond("RETE", 0x34, FALSE);
	
	AddZero("ZBRR", 0x9b, FALSE);
	AddZero("ZBSR", 0xbb, FALSE);
	
	AddCondFar("BCTF", 0x1c);
	AddCondFar("BSTF", 0x3c);
	AddCondFar("BCFF", 0x9c);
	AddCondFar("BSFF", 0xbc);
	
	AddRegFar("BRNF", 0x5C);
	AddRegFar("BSNF", 0x7C);
	AddRegFar("BIRF", 0xDC);
	AddRegFar("BDRF", 0xFC);
}

static void DeinitFields(void) {
	DestroyInstTable(InstTable);
}

static void MakeCode_as2650(void) {
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

static Boolean IsDef_as2650(void) {
	return FALSE;
}

static void SwitchFrom_as2650(void) {
	DeinitFields();
}

static void SwitchTo_as2650(void) {
	const TFamilyDescr *pDescr;
	
	TurnWords = False; IntConstMode = eIntConstModeMoto; ShiftIsOccupied = False;
	
	pDescr = FindFamilyByName("AS2650-2");
	PCSymbol = "$"; HeaderID = pDescr->Id; NOPCode = 0xc0;
	DivideChars = ","; HasAttrs = False;
	
	ValidSegs = (1 << SegCode);
	Grans[SegCode] = 1; ListGrans[SegCode] = 1; SegInits[SegCode] = 0;
	SegLimits[SegCode] = 0xffffl;
	
	MakeCode = MakeCode_as2650; IsDef = IsDef_as2650;
	
	SwitchFrom = SwitchFrom_as2650; InitFields();
}

void codeas2650_init(void) {
	CPUAS2650 = AddCPU("AS2650-2", SwitchTo_as2650);
}
