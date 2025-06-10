#include "stdinc.h"
#include <ctype.h>
#include <string.h>

#include "bpemu.h"
#include "strutil.h"
#include "asmdef.h"
#include "asmsub.h"
#include "asmpars.h"
#include "asmitree.h"
#include "codevars.h"
#include "headids.h"
#include "fourpseudo.h"
#include "errmsg.h"

#include "codePDK13.h"

static CPUVar CPUPDK13;

#define A_ONLY 0x4000
#define M_ONLY 0x8000
#define SUPPORTS_LITERAL 0x8000

static void DecodeAri(Word Code);

static void DecodeFixed(Word Code) {
  if(ChkArgCnt(0, 0)) {
    WAsmCode[CodeLen++] = Code;
    if(Memo("OPTION")) WrError(ErrNum_Obsolete);
  }
}

static void DecodeAddcSubc(Word Code) {
	if(ChkArgCnt(1, 2)) {
		if(ArgCnt == 2) {
			DecodeAri(Code == 0 ? (2 << 6) : (3 << 6));
		}else {
			if(strcasecmp(ArgStr[1].str.p_str, "A") == 0) {
				WAsmCode[0] = Code == 0 ? 0x0010 : 0x0011;
				CodeLen = 1;
			}else {
				Boolean OK;
				WAsmCode[0] = EvalStrIntExpression(&ArgStr[1], UInt6, &OK);
				if(OK) {
					WAsmCode[0] |= Code == 0 ? 0x0800 : 0x0840;
					CodeLen = 1;
				}
			}
		}
	}
}

static void DecodeSingle(Word Code) {
	if(ChkArgCnt(1, 1)) {
		if(strcasecmp(ArgStr[1].str.p_str, "A") == 0) {
			if((Code & A_ONLY) == 0) WrError(ErrNum_InvFormat);
			else {
				WAsmCode[0] = 0x0010;
				WAsmCode[0] |= Code & 0x1FFF;
				CodeLen = 1;
			}
		}else {
			if((Code & M_ONLY) == 0) WrError(ErrNum_InvFormat);
			else {
				Boolean OK;
				WAsmCode[0] = EvalStrIntExpression(&ArgStr[1], UInt6, &OK);
				if(OK) {
					WAsmCode[0] |= 0x0800;
					WAsmCode[0] |= (Code & 0x1FFF) << 6;
					CodeLen = 1;
				}
			}
		}
	}
}

static void DecodeAri(Word Code) {
	if(ChkArgCnt(2, 2)) {
		if(strcasecmp(ArgStr[1].str.p_str, "A") == 0) {
			if(ArgStr[2].str.p_str[0] == '#') {
				if((Code & SUPPORTS_LITERAL) == 0) WrError(ErrNum_InvFormat);
				else {
					Boolean OK;
					StrCompCutLeft(&ArgStr[2], 1);
					WAsmCode[0] = EvalStrIntExpression(&ArgStr[2], UInt8, &OK);
					WAsmCode[0] |= (Code & 0x1FFF) << 8;
					WAsmCode[0] |= 0x1000;
					CodeLen = 1;
				}
			}else {
				Boolean OK;
				WAsmCode[0] = EvalStrIntExpression(&ArgStr[2], UInt6, &OK);
				if(OK) {
					WAsmCode[0] |= (Code & 0x1FFF) << 6;
					WAsmCode[0] |= 0x0600;
					CodeLen = 1;
				}
			}
		}else if(strcasecmp(ArgStr[2].str.p_str, "A") == 0)  {
			Boolean OK;
			WAsmCode[0] = EvalStrIntExpression(&ArgStr[1], UInt6, &OK);
			if(OK) {
				WAsmCode[0] |= (Code & 0x1FFF) << 6;
				WAsmCode[0] |= 0x0400;
				CodeLen = 1;
			}
		}else WrError(ErrNum_InvFormat);
	}
}

static void DecodeXor(Word Code) {
	if(ChkArgCnt(2, 2)) {
		if(ArgStr[1].str.p_str[0] == '^') {
			if(strcasecmp(ArgStr[2].str.p_str, "A") != 0) WrError(ErrNum_InvFormat);
			else {
				StrCompCutLeft(&ArgStr[1], 1);
				Boolean OK;
				WAsmCode[0] = EvalStrIntExpression(&ArgStr[1], UInt5, &OK);
				if(OK) {
					WAsmCode[0] |= 0x0060;
					CodeLen = 1;
				}
			}
		}else DecodeAri(0x6 | SUPPORTS_LITERAL);
	}
}

static void DecodeBranch(Word Code) {
	if(ChkArgCnt(1, 1)) {
		Boolean OK;
		WAsmCode[0] = EvalStrIntExpression(&ArgStr[1], UInt10, &OK);
		if(OK) {
			WAsmCode[0] |= Code << 10;
			CodeLen = 1;
		}
	}
}

static void DecodeMov(Word Code) {
	if(ChkArgCnt(2, 2)) {
		if(ArgStr[1].str.p_str[0] == '^' || ArgStr[2].str.p_str[0] == '^') {
			Boolean OK;
			Word val = 0;
			if(ArgStr[1].str.p_str[0] == '^') {
				if(strcasecmp(ArgStr[2].str.p_str, "A") != 0) {
					WrError(ErrNum_InvFormat);
					return;
				}
				WAsmCode[0] = 0x0080;
				StrCompCutLeft(&ArgStr[1], 1);
				val = EvalStrIntExpression(&ArgStr[1], UInt5, &OK);
			}else {
				if(strcasecmp(ArgStr[1].str.p_str, "A") != 0) {
					WrError(ErrNum_InvFormat);
					return;
				}
				WAsmCode[0] = 0x00A0;
				StrCompCutLeft(&ArgStr[2], 1);
				val = EvalStrIntExpression(&ArgStr[2], UInt5, &OK);
			}
			if(!OK) return;
			WAsmCode[0] |= val;
			CodeLen = 1;
		}else DecodeAri(0x7 | SUPPORTS_LITERAL);
	}
}

static void DecodeCeqsn(Word Code) {
	if(ChkArgCnt(2, 2)) {
		if(strcasecmp(ArgStr[1].str.p_str, "A") != 0) WrError(ErrNum_InvFormat);
		else {
			Boolean OK;
			if(ArgStr[2].str.p_str[0] == '#') {
				StrCompCutLeft(&ArgStr[2], 1);
				WAsmCode[0] = EvalStrIntExpression(&ArgStr[2], UInt8, &OK);
				if(OK) {
					WAsmCode[0] |= 0x1200;
					CodeLen = 1;
				}
			}else {
				WAsmCode[0] = EvalStrIntExpression(&ArgStr[2], UInt6, &OK);
				if(OK) {
					WAsmCode[0] |= 0x0BC0;
					CodeLen = 1;
				}
			}
		}
	}
}

static void DecodeBit(Word Code) {
	if(ChkArgCnt(1, 1)) {
		Boolean isIo = False;
		if(ArgStr[1].str.p_str[0] == '^') {
			StrCompCutLeft(&ArgStr[1], 1);
			isIo = True;
		}
		char* p = strchr(ArgStr[1].str.p_str, '.');
		if(!p) {
			WrError(ErrNum_InvFormat);
			return;
		}
		tStrComp AddrArg, BitArg;
		StrCompSplitRef(&AddrArg, &BitArg, &ArgStr[1], p);
		if(!AddrArg.str.p_str || !BitArg.str.p_str) {
			WrError(ErrNum_InvFormat);
			return;
		}
		Boolean OK;
		WAsmCode[0] = EvalStrIntExpression(&AddrArg, isIo ? UInt5 : UInt4, &OK);
		if(!OK) return;
		WAsmCode[0] |= EvalStrIntExpression(&BitArg, UInt3, &OK) << 5;
		if(!OK) return;
		if(isIo) {
			WAsmCode[0] |= Code << 8;
			WAsmCode[0] |= 0x0C00;
		}else {
			if((Code & 1) != 0) WAsmCode[0] |= 0x0010;
			if((Code & 2) != 0) WAsmCode[0] |= 0x0100;
			WAsmCode[0] |= 0x0200;
		}
		CodeLen = 1;
	}
}

static void Decode16bit(Word Code) {
	Word val = 0;
	Boolean OK;
	if((Code & M_ONLY) != 0) {
		if(ChkArgCnt(1, 1)) {
			val = EvalStrIntExpression(&ArgStr[1], UInt6, &OK);
			if(!OK) return;
		}
	}else {
		if(strcasecmp(ArgStr[1].str.p_str, "A") == 0) val = EvalStrIntExpression(&ArgStr[2], UInt6, &OK);
		else if(strcasecmp(ArgStr[2].str.p_str, "A") == 0) val = EvalStrIntExpression(&ArgStr[1], UInt6, &OK);
		else {
			WrError(ErrNum_InvFormat);
			return;
		}
		if(!OK) return;
	}
	WAsmCode[0] = val;
	if((WAsmCode[0] & 1) != 0) WrError(ErrNum_NotAligned);
	else {
		if((Code & 1) != 0) WAsmCode[0] |= 1;
		if((Code & 2) != 0) WAsmCode[0] |= 64;
		WAsmCode[0] |= 0x00C0;
		CodeLen = 1;
	}
}

static void AddFixed(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeFixed);
}

static void AddAri(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeAri);
}

static void AddSingle(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeSingle);
}

static void AddBranch(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeBranch);
}

static void AddBit(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeBit);
}

static void Add16bit(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, Decode16bit);
}

static void InitFields(void) {
	InstTable = CreateInstTable(46);
	
	AddFixed("NOP"      , 0x0000);
	AddFixed("LDSPTL"   , 0x0006);
	AddFixed("LDSPTH"   , 0x0007);
	AddFixed("WDRESET"  , 0x0030);
	AddFixed("PUSHAF"   , 0x0032);
	AddFixed("POPAF"    , 0x0033);
	AddFixed("RESET"    , 0x0035);
	AddFixed("STOPSYS"  , 0x0036);
	AddFixed("STOPEXE"  , 0x0037);
	AddFixed("ENGINT"   , 0x0038);
	AddFixed("DISGINT"  , 0x0039);
	AddFixed("RET"      , 0x003A);
	AddFixed("RETI"     , 0x003B);
	
	AddAri("ADD"        , 0x0 | SUPPORTS_LITERAL);
	AddAri("SUB"        , 0x1 | SUPPORTS_LITERAL);
	AddAri("AND"        , 0x4 | SUPPORTS_LITERAL);
	AddAri("OR"         , 0x5 | SUPPORTS_LITERAL);
	AddInstTable(InstTable, "ADDC", 0, DecodeAddcSubc);
	AddInstTable(InstTable, "SUBC", 1, DecodeAddcSubc);
	AddInstTable(InstTable, "XOR", 0, DecodeXor);
	
	AddSingle("IZSN", 0x2 | A_ONLY | M_ONLY);
	AddSingle("DZSN", 0x3 | A_ONLY | M_ONLY);
	AddSingle("PCADD", 0x7 | A_ONLY);
	AddSingle("NOT", 0x8 | A_ONLY | M_ONLY);
	AddSingle("NEG", 0x9 | A_ONLY | M_ONLY);
	AddSingle("SR", 0xA | A_ONLY | M_ONLY);
	AddSingle("SL", 0xB | A_ONLY | M_ONLY);
	AddSingle("SRC", 0xC | A_ONLY | M_ONLY);
	AddSingle("SLC", 0xD | A_ONLY | M_ONLY);
	AddSingle("SWAP", 0xE | A_ONLY);
	AddSingle("INC", 0x4 | M_ONLY);
	AddSingle("DEC", 0x5 | M_ONLY);
	AddSingle("CLEAR", 0x6 | M_ONLY);
	AddSingle("XCH", 0x7 | M_ONLY);
	
	AddBit("T0SN", 0x0);
	AddBit("T1SN", 0x1);
	AddBit("SET0", 0x2);
	AddBit("SET1", 0x3);
	
	Add16bit("STT16", 0x0000 | M_ONLY);
	Add16bit("LDT16", 0x0001 | M_ONLY);
	Add16bit("IDXM", 0x0020);
	
	AddBranch("GOTO", 0x6);
	AddBranch("CALL", 0x7);
	
	//Oddballs
	AddInstTable(InstTable, "MOV", 0, DecodeMov);
	AddInstTable(InstTable, "CEQSN", 0, DecodeCeqsn);
}

static void DeinitFields(void) {
	DestroyInstTable(InstTable);
}

static void MakeCode_PDK13(void) {
  CodeLen = 0; DontPrint = False;
  
  if((*OpPart.str.p_str == '\0') && (ArgCnt == 0)) return;
  
  if(Memo("")) return;
  
  if(!LookupInstTable(InstTable, OpPart.str.p_str)) WrStrErrorPos(ErrNum_UnknownInstruction, &OpPart);
}

static Boolean IsDef_PDK13(void) {
	return FALSE;
}

static void SwitchFrom_PDK13(void) {
	DeinitFields();
}

static void SwitchTo_PDK13(void) {
	TurnWords = False;
	SetIntConstMode(eIntConstModeMoto);
	ShiftIsOccupied = False;
	
	PCSymbol = "*";
	HeaderID = 0x0088;
	NOPCode = 0x000;
	DivideChars = ",";
	HasAttrs = False;

	ValidSegs = (1 << SegCode) + (1 << SegData);
	Grans[SegCode] = 2; ListGrans[SegCode] = 2; SegInits[SegCode] = 0;
	SegLimits[SegCode ] = 0x3ff;
	
	Grans[SegData] = 1; ListGrans[SegData] = 1; SegInits[SegData] = 0;
	SegLimits[SegData ] = 0x3f;
	
	MakeCode = MakeCode_PDK13;
	IsDef = IsDef_PDK13;
	SwitchFrom = SwitchFrom_PDK13;
	
	InitFields();
}

void code_PDK13_init(void) {
	CPUPDK13 = AddCPU("PDK13", SwitchTo_PDK13);
}
