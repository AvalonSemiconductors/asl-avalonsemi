/*
 * (Tholin, 23/01/2025) Added support for ScrapCPU
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

#include "codescrapcpu.h"

static CPUVar CPUScrapCPU;

static void DecodeALU(Word Index) {
	if(!ChkArgCnt(0, 1));
	else {
		if(ArgCnt == 1) {
			BAsmCode[0] = Index;
			Boolean OK;
			Byte AbsVal = EvalStrIntExpressionOffs(&ArgStr[1], 0, UInt6, &OK);
			if(OK) {
				BAsmCode[1] = AbsVal;
				CodeLen = 2;
			}
		}else {
			BAsmCode[0] = Index | (1 << 5);
			CodeLen = 1;
		}
	}
}

static void DecodeImplied(Word Index) {
	BAsmCode[0] = Index;
	CodeLen = 1;
}

static void DecodeImmediate(Word Index) {
	if(!ChkArgCnt(1, 1));
	else {
		Boolean OK;
		Byte AbsVal = EvalStrIntExpressionOffs(&ArgStr[1], 0, UInt6, &OK);
		if(OK) {
			BAsmCode[0] = Index;
			BAsmCode[1] = AbsVal;
			CodeLen = 2;
		}
	}
}

static void DecodeJump(Word Index) {
	if(!ChkArgCnt(0, 1));
	else {
		if(ArgCnt == 1) {
			Boolean OK;
			Word Dest = EvalStrIntExpressionOffs(&ArgStr[1], 0, UInt12, &OK);
			if(OK) {
				BAsmCode[0] = 1 << 4;
				BAsmCode[1] = Dest >> 6;
				BAsmCode[2] = Index;
				BAsmCode[3] = Dest & 0x3F;
				CodeLen = 4;
			}
		}else {
			BAsmCode[0] = Index | (1 << 5);
			CodeLen = 1;
		}
	}
}

static void DecodeOut(Word Index) {
	if(!ChkArgCnt(0, 0));
	else {
		BAsmCode[0] = 0b000010;
		BAsmCode[1] = 0b111111;
		CodeLen = 2;
	}
}

static void DecodeCall(Word Index) {
	if(!ChkArgCnt(0, 1));
	else {
		Word target = EProgCounter();
		if(ArgCnt == 0) target += 9;
		else target += 12;
		BAsmCode[0] = 0b111111;
		BAsmCode[1] = target >> 6;
		BAsmCode[2] = 0b000011;
		BAsmCode[3] = 61;
		BAsmCode[4] = 0b111111;
		BAsmCode[5] = target & 0x3F;
		BAsmCode[6] = 0b000011;
		BAsmCode[7] = 62;
		if(ArgCnt == 0) {
			BAsmCode[8] = Index | (1 << 5);
			CodeLen = 9;
		}else {
			Boolean OK;
			Word Dest = EvalStrIntExpressionOffs(&ArgStr[1], 0, UInt12, &OK);
			if(OK) {
				BAsmCode[8] = 1 << 4;
				BAsmCode[9] = Dest >> 6;
				BAsmCode[10] = Index;
				BAsmCode[11] = Dest & 0x3F;
				CodeLen = 12;
			}
		}
	}
}

static void DecodeReturn(Word Index) {
	if(!ChkArgCnt(0, 0));
	else {
		BAsmCode[0] = 0b001111;
		BAsmCode[1] = 61;
		BAsmCode[2] = 0b110000;
		BAsmCode[3] = 0b001111;
		BAsmCode[4] = 62;
		BAsmCode[5] = Index | (1 << 5);
		CodeLen = 6;
	}
}

static void AddALU(char *pName, Word Code) {
	AddInstTable(InstTable, pName, Code, DecodeALU);
}

static void AddImplied(char *pName, Word Code) {
	AddInstTable(InstTable, pName, Code, DecodeImplied);
}

static void AddImmediate(char *pName, Word Code) {
	AddInstTable(InstTable, pName, Code, DecodeImmediate);
}

static void AddJump(char *pName, Word Code) {
	AddInstTable(InstTable, pName, Code, DecodeJump);
}

static void InitFields(void) {
	InstTable = CreateInstTable(37);
	AddALU("LDA", 0b00001);
	AddALU("STA", 0b00011);
	AddALU("STB", 0b00010);
	AddALU("LDP", 0b10000);
	AddALU("LDM", 0b01111);
	AddALU("ADD", 0b00100);
	AddALU("QADD", 0b10100);
	AddALU("ADC", 0b00101);
	AddALU("QADC", 0b10101);
	AddALU("SUB", 0b00110);
	AddALU("QSUB", 0b10110);
	AddALU("SBC", 0b00111);
	AddALU("QSBC", 0b10111);
	AddALU("EQL", 0b01000);
	AddALU("QEQL", 0b11000);
	AddALU("MAG", 0b01001);
	AddALU("QMAG", 0b11001);
	
	AddJump("JMP", 0b01100);
	AddJump("JZ", 0b01101);
	AddJump("JNZ", 0b01110);
	
	AddImmediate("LDI", 0b111111);
	
	AddImplied("NOP", 0b000000);
	
	//Extended ISA
	AddALU("XOR", 0b01010);
	AddALU("QXOR", 0b11010);
	AddALU("AND", 0b01011);
	AddALU("QAND", 0b11011);
	
	AddImplied("RSH", 0b010010);
	AddImplied("RSHC", 0b010011);
	AddImplied("SEC", 0b010001);
	AddImplied("CLC", 0b100000);
	AddImplied("IRET", 0b110010);
	AddImplied("TC", 0b110001);
	
	AddJump("JC", 0b11110);
	
	//Built-in macros
	AddInstTable(InstTable, "OUT", 0, DecodeOut);
	AddInstTable(InstTable, "CALL", 0b001100, DecodeCall);
	AddInstTable(InstTable, "RETURN", 0b001100, DecodeReturn);
}

static void DeinitFields(void) {
	DestroyInstTable(InstTable);
}

static void MakeCode_scrapcpu(void) {
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

static Boolean IsDef_scrapcpu(void) {
	return FALSE;
}

static void SwitchFrom_scrapcpu(void) {
	DeinitFields();
}

static void SwitchTo_scrapcpu(void) {
	const TFamilyDescr *pDescr;
	
	SetIntConstMode(eIntConstModeMoto);
	TurnWords = False; ShiftIsOccupied = False;
	
	pDescr = FindFamilyByName("ScrapCPU");
	PCSymbol = "$"; HeaderID = pDescr->Id;
	DivideChars = ","; HasAttrs = False;
	
	ValidSegs = (1 << SegCode) + (1 << SegData);
	Grans[SegCode] = 1; ListGrans[SegCode] = 1; SegInits[SegCode] = 0;
	SegLimits[SegCode ] = 0xffff;
	
	Grans[SegData] = 1; ListGrans[SegData] = 1; SegInits[SegData] = 0;
	SegLimits[SegData ] = 0x3f;
	
	MakeCode = MakeCode_scrapcpu; IsDef = IsDef_scrapcpu;
	
	SwitchFrom = SwitchFrom_scrapcpu; InitFields();
}

void codescrapcpu_init(void) {
	CPUScrapCPU = AddCPU("ScrapCPU", SwitchTo_scrapcpu);
}
