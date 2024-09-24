/*
 * (Tholin, 24/09/2024) Added support for QCPU
 */

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

#include "codeqcpu.h"

#define SUPPORT_IMMEDIATE 32768
#define J_CODE 0

static CPUVar CPUqcpu;

static void DecodeFixed(Word Code) {
  if(ChkArgCnt(0, 0)) {
    WAsmCode[CodeLen++] = Code;
    if(Memo("OPTION")) WrError(ErrNum_Obsolete);
  }
}

static void DecodeSingleReg(Word Code) {
	if(ChkArgCnt(1, 1)) {
		if(ArgStr[1].str.p_str[0] != 'r') WrError(ErrNum_InvFormat);
		else {
			Boolean OK;
			StrCompCutLeft(&ArgStr[1], 1);
			WAsmCode[0] = EvalStrIntExpression(&ArgStr[1], UInt4, &OK);
			if(OK) {
				WAsmCode[0] <<= 8;
				WAsmCode[0] |= Code;
				CodeLen = 1;
			}
		}
	}
}

static void DecodeIOA(Word Code) {
	if(ChkArgCnt(1, 1)) {
		if(ArgStr[1].str.p_str[0] == 'r') {
			DecodeSingleReg(0x605F);
		}else {
			if(ArgStr[1].str.p_str[0] != '#') WrError(ErrNum_InvFormat);
			else {
				StrCompCutLeft(&ArgStr[1], 1);
				Boolean OK;
				WAsmCode[0] = EvalStrIntExpression(&ArgStr[1], UInt8, &OK);
				if(OK) {
					WAsmCode[0] <<= 8;
					WAsmCode[0] |= Code;
					CodeLen = 1;
				}
			}
		}
	}
}

static void DecodeMul(Word Code) {
	if(ChkArgCnt(2, 2)) {
		if(strcasecmp(ArgStr[1].str.p_str, "r1") != 0) WrError(ErrNum_InvFormat);
		else {
			Boolean OK;
			WAsmCode[0] = EvalStrIntExpression(&ArgStr[2], UInt4, &OK);
			if(OK) {
				WAsmCode[0] <<= 8;
				WAsmCode[0] |= Code;
				CodeLen = 1;
			}
		}
	}
}

static void DecodeJump(Word Code) {
	if(ChkArgCnt(1, 1)) {
		Boolean OK;
		Word dest = EvalStrIntExpression(&ArgStr[1], UInt14, &OK);
		if(OK) {
			WAsmCode[0] = (dest >> 8) & 0x3F;
			WAsmCode[0] |= (dest & 0xFF) << 8;
			WAsmCode[0] |= Code;
			CodeLen = 1;
		}
	}
}

static void DecodeBranch(Word Code) {
	if(ChkArgCnt(1, 1)) {
		Boolean OK;
		int dest = EvalStrIntExpression(&ArgStr[1], UInt14, &OK) - EProgCounter();
		if(!eSymbolFlag_Questionable && ((dest < -1024) || (dest > 1024))) WrError(ErrNum_JmpDistTooBig);
		unsigned int destu = (unsigned int)dest;
		if(OK) {
			WAsmCode[0] = (destu >> 8) & 0x07;
			WAsmCode[0] |= (destu & 0xFF) << 8;
			WAsmCode[0] |= Code;
			CodeLen = 1;
		}
	}
}

static void DecodeAri(Word Code) {
	if(ChkArgCnt(2, 2)) {
		if(ArgStr[1].str.p_str[0] != 'r') WrError(ErrNum_InvFormat);
		else {
			StrCompCutLeft(&ArgStr[1], 1);
			Boolean OK;
			WAsmCode[0] = EvalStrIntExpression(&ArgStr[1], UInt4, &OK);
			if(!OK) return;
			WAsmCode[0] <<= 12;
			if(ArgStr[2].str.p_str[0] != 'r') {
				if((Code & SUPPORT_IMMEDIATE) == 0) WrError(ErrNum_InvFormat);
				else {
					Code &= 0x7FFF;
					Code |= 0x0008;
				}
			}else {
				Code &= 0x7FFF;
			}
			StrCompCutLeft(&ArgStr[2], 1);
			Word s2 = EvalStrIntExpression(&ArgStr[2], UInt4, &OK);
			if(!OK) return;
			WAsmCode[0] |= s2 << 8;
			WAsmCode[0] |= Code;
			CodeLen = 1;
		}
	}
}

static void DecodeCmp(Word Code) {
	if(ChkArgCnt(2, 2)) {
		if(strcasecmp(ArgStr[1].str.p_str, "r1") == 0 && ArgStr[2].str.p_str[0] == '#') {
			Boolean OK;
			StrCompCutLeft(&ArgStr[2], 1);
			WAsmCode[0] = EvalStrIntExpression(&ArgStr[2], UInt4, &OK);
			if(OK) {
				WAsmCode[0] <<= 8;
				WAsmCode[0] |= 0x905F;
				CodeLen = 1;
			}
		}else {
			DecodeAri(0x005E);
		}
	}
}

static void DecodeLoadstore(Word Code) {
	if(ChkArgCnt(2, 2)) {
		if(ArgStr[1].str.p_str[0] != 'r') WrError(ErrNum_InvFormat);
		else if(ArgStr[2].str.p_str[0] != 'r') WrError(ErrNum_InvFormat);
		else {
			StrCompCutLeft(&ArgStr[1], 1);
			StrCompCutLeft(&ArgStr[2], 1);
			Boolean OK;
			WAsmCode[0] = EvalStrIntExpression(&ArgStr[1], UInt4, &OK);
			if(!OK) return;
			WAsmCode[0] <<= 12;
			char* p = strchr(ArgStr[2].str.p_str, '(');
			if(!p) {
				WrError(ErrNum_InvFormat);
				return;
			}
			tStrComp RegArg, DispArg;
			StrCompSplitRef(&RegArg, &DispArg, &ArgStr[2], p);
			if(!RegArg.str.p_str || !DispArg.str.p_str || DispArg.str.p_str[strlen(DispArg.str.p_str) - 1] != ')') {
				WrError(ErrNum_InvFormat);
				return;
			}
			StrCompShorten(&DispArg, 1);
			Word reg = EvalStrIntExpression(&RegArg, UInt4, &OK);
			if(!OK) return;
			WAsmCode[0] |= reg << 8;
			WAsmCode[0] |= EvalStrIntExpression(&DispArg, UInt6, &OK);
			if(!OK) return;
			WAsmCode[0] |= Code;
			CodeLen = 1;
		}
	}
}

static void DecodeLdi(Word Code) {
	if(ChkArgCnt(2, 2)) {
		if(ArgStr[1].str.p_str[0] != 'r') WrError(ErrNum_InvFormat);
		else if(ArgStr[2].str.p_str[0] != '#') WrError(ErrNum_InvFormat);
		else {
			StrCompCutLeft(&ArgStr[1], 1);
			StrCompCutLeft(&ArgStr[2], 1);
			Boolean OK;
			WAsmCode[0] = EvalStrIntExpression(&ArgStr[1], UInt4, &OK);
			if(!OK) return;
			if(WAsmCode[0] == 0) {
				WrError(ErrNum_InvFormat);
				return;
			}
			Word imm = EvalStrIntExpression(&ArgStr[2], UInt8, &OK);
			if(!OK) return;
			WAsmCode[0] |= imm << 8;
			WAsmCode[0] |= Code;
			CodeLen = 1;
		}
	}
}

static void DecodeCall(Word Code) {
	if(ChkArgCnt(1, 1)) {
		Boolean OK;
		Word dest = EvalStrIntExpression(&ArgStr[1], UInt14, &OK);
		if(OK) {
			WAsmCode[0] = 0x005C;
			WAsmCode[1] = J_CODE;
			WAsmCode[1] |= (dest >> 8) & 0x3F;
			WAsmCode[1] |= (dest & 0xFF) << 8;
			CodeLen = 2;
		}
	}
}

static void AddFixed(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeFixed);
}

static void AddSingleReg(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeSingleReg);
}

static void AddBranch(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeBranch);
}

static void AddAri(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeAri);
}

static void AddLoadstore(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeLoadstore);
}

static void InitFields(void) {
	InstTable = CreateInstTable(36);
	
	AddFixed("WAIT", 0xA05F);
	AddFixed("RTI", 0xB05F);
	AddFixed("LDC", 0xF05F);
	AddFixed("RETURN", 0xD050);
	AddFixed("NOP", 0x0055); //or r0,r0
	
	AddSingleReg("SR", 0x005F);
	AddSingleReg("SRC", 0x105F);
	AddSingleReg("SL", 0x205F);
	AddSingleReg("SLC", 0x305F);
	AddSingleReg("ROR", 0x405F);
	AddSingleReg("ROL", 0x505F);
	AddSingleReg("OUT", 0x705F);
	AddSingleReg("IN", 0x805F);
	AddSingleReg("GF", 0xD05F);
	AddSingleReg("PF", 0xE05F);
	
	AddBranch("BNC", 0x0060);
	AddBranch("BC", 0x0068);
	AddBranch("BNZ", 0x0070);
	AddBranch("BZ", 0x0078);
	
	AddAri("ADD", 0x0050 | SUPPORT_IMMEDIATE);
	AddAri("ADC", 0x0051 | SUPPORT_IMMEDIATE);
	AddAri("SUB", 0x0052 | SUPPORT_IMMEDIATE);
	AddAri("SBC", 0x0053 | SUPPORT_IMMEDIATE);
	AddAri("AND", 0x0054);
	AddAri("OR", 0x0055);
	AddAri("XOR", 0x0056);
	AddAri("NOT", 0x0057);
	
	AddLoadstore("LD", 0x00C0);
	AddLoadstore("ST", 0x0080);
	
	AddInstTable(InstTable, "IOA", 0x0040, DecodeIOA);
	AddInstTable(InstTable, "MUL", 0xC05F, DecodeMul);
	AddInstTable(InstTable, "J", J_CODE, DecodeJump);
	AddInstTable(InstTable, "CMP", 0x000E, DecodeCmp);
	AddInstTable(InstTable, "CALL", 0x0000, DecodeCall);
	AddInstTable(InstTable, "LDI", 0x0040, DecodeLdi);
}

static void DeinitFields(void) {
	DestroyInstTable(InstTable);
}

static void MakeCode_qcpu(void) {
	CodeLen = 0; DontPrint = False;
	
	if(Memo("")) return;
	
	if(!LookupInstTable(InstTable, OpPart.str.p_str)) WrStrErrorPos(ErrNum_UnknownInstruction, &OpPart);
}

static Boolean IsDef_qcpu(void) {
	return Memo("REG");
}

static void SwitchFrom_qcpu(void) {
	DeinitFields();
}

static void SwitchTo_qcpu(void) {
	TurnWords = False;
	IntConstMode = eIntConstModeMoto;
	ShiftIsOccupied = False;
	
	PCSymbol = "*";
	HeaderID = 0x0089;
	NOPCode = 0x0055; //or r0,r0
	DivideChars = ",";
	HasAttrs = False;
	
	ValidSegs = (1 << SegCode) + (1 << SegData);
	Grans[SegCode] = 2; ListGrans[SegCode] = 2; SegInits[SegCode] = 0;
	SegLimits[SegCode ] = 0x3fff;
	
	Grans[SegData] = 1; ListGrans[SegData] = 1; SegInits[SegData] = 0;
	SegLimits[SegData ] = 0x3f;
	
	MakeCode = MakeCode_qcpu;
	IsDef = IsDef_qcpu;
	SwitchFrom = SwitchFrom_qcpu;
	
	InitFields();
}

void code_qcpu_init(void) {
	CPUqcpu = AddCPU("QCPU", SwitchTo_qcpu);
}
