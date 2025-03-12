/*
 * (Tholin, 27/09/2024) Added support for LVDC
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
#include "intpseudo.h"
#include "errmsg.h"

#include "codelvdc.h"

static CPUVar CPUlvdc;

#define FLAG_RESIDUAL_ALLOWED 128
#define FLAG_IMM_VALUE 256

static void DecodeSimple(Word Code) {
	if(ChkArgCnt(1, 1)) {
		Boolean OK;
		Boolean residual = False;
		if(ArgStr[1].str.p_str[0] == '+') {
			if((Code & FLAG_RESIDUAL_ALLOWED) == 0) {
				WrStrErrorPos(ErrNum_InvAddrMode, &ArgStr[1]);
				return;
			}
			residual = True;

		}
		Word addr = EvalStrIntExpressionOffs(&ArgStr[1], residual, (Code & FLAG_IMM_VALUE) != 0 ? UInt9 : UInt15, &OK);
		if(!OK) return;
		if((Code & FLAG_IMM_VALUE) != 0 && (addr & 256) != 0) {
			addr &= 0xFF;
			residual = True;
		}
		if((Code & FLAG_IMM_VALUE) == 0 && (addr >> 8) != (EProgCounter() >> 8)) {
			WrStrErrorPos(ErrNum_ArgOutOfRange, &ArgStr[1]);
			return;
		}
		Word fullInstr = 0;
		if(OK) {
			Code &= 0x0F;
			fullInstr |= Code;
			if(residual) fullInstr |= (1 << 4);
			fullInstr |= (addr & 0xFF) << 5;
			DAsmCode[0] = fullInstr;
			CodeLen = 1;
		}
	}
}

static void DecodeExtendedHOP(Word Code) {
	if((EProgCounter() & 0xFF) == 0xFF) {
		WrError(ErrNum_ArgOutOfRange);
		return;
	}
	//HOP Destination, [Data Module], [Data Sector]
	//Same DM and DS as destination instruction module and instruction sector
	if(!ChkArgCnt(1, 3)) return;
	Boolean OK;
	Word destination = EvalStrIntExpression(&ArgStr[1], UInt15, &OK);
	if(!OK) return;
	Word dm, ds, im, is;
	is = (destination >> 8) & 0xF;
	im = (destination >> 12) & 0x7;
	destination &= 0xFF;
	if(ArgCnt == 3) {
		dm = EvalStrIntExpression(&ArgStr[2], UInt3, &OK);
		if(!OK) return;
		ds = EvalStrIntExpression(&ArgStr[3], UInt4, &OK);
		if(!OK) return;
	}else {
		dm = im;
		ds = is;
	}
	//Assemble new HOP constant
	Word newHop = (im >> 1) | (is << 2) | (destination << 7) | (dm << 17) | (ds << 20) | ((im & 1) << 25);
	DAsmCode[0] = Code | (((EProgCounter() + 1) & 0xFF) << 5);
	DAsmCode[1] = newHop;
	CodeLen += 2;
}

static void DecodeCDS(Word Code) {
	if(ChkArgCnt(1, 2)) {
		Boolean OK;
		if(ArgCnt == 1) {
			if((Code & 2) == 0) {
				WrError(ErrNum_InvAddrMode);
				return;
			}
			Word setting = EvalStrIntExpression(&ArgStr[1], UInt8, &OK);
			if(OK) {
				Word fullInstr = setting << 5;
				fullInstr |= 0xE;
				WAsmCode[0] = fullInstr;
				CodeLen = 1;
			}
		}else {
			if((Code & 2) != 0) {
				WrError(ErrNum_InvAddrMode);
				return;
			}
			Word DM = EvalStrIntExpression(&ArgStr[1], UInt3, &OK);
			if(OK) {
				Word DS = EvalStrIntExpression(&ArgStr[2], UInt4, &OK);
				if(OK) {
					Word fullInstr = (DM << 1) | (DS << 4);
					if((Code & 1) != 0) fullInstr |= 1;
					fullInstr <<= 5;
					fullInstr |= 0xE;
					DAsmCode[0] = fullInstr;
					CodeLen = 1;
				}
			}
		}
	}
}

static void DecodeShift(Word Code) {
	if((Code & 2) != 0) {
		//Clear-accumulator to zero is technically a shift instruction
		Word fullInstr = 0x1E;
		DAsmCode[0] = fullInstr;
		CodeLen = 1;
		return;
	}
	if(ChkArgCnt(1, 1)) {
		Boolean OK;
		Word shiftBy = EvalStrIntExpression(&ArgStr[1], UInt4, &OK);
		if(shiftBy > 2 || shiftBy == 0) {
			WrStrErrorPos(ErrNum_InvOpSize, &ArgStr[1]);
			return;
		}
		Word fullInstr = 0x1E;
		if((Code & 1) != 0) {
			//Right-shift
			if(shiftBy == 1) fullInstr |= (1 << 5);
			else if(shiftBy == 2) fullInstr |= (1 << 6);
		}else {
			//Left-shift
			if(shiftBy == 1) fullInstr |= (1 << 9);
			else if(shiftBy == 2) fullInstr |= (1 << 10);
		}
		DAsmCode[0] = fullInstr;
		CodeLen = 1;
	}
}

static void DecodeEXM(Word Code) {
	if(ChkArgCnt(3, 3)) {
		Boolean OK;
		Word adr = EvalStrIntExpression(&ArgStr[1], UInt2, &OK);
		if(OK) {
			Word syl = EvalStrIntExpression(&ArgStr[2], UInt1, &OK);
			if(OK) {
				Word mod = EvalStrIntExpression(&ArgStr[3], UInt4, &OK);
				Word fullInstr = 0x101E;
				fullInstr |= (mod << 5);
				if(syl != 0) fullInstr |= (1 << 9);
				fullInstr |= (adr << 10);
				DAsmCode[0] = fullInstr;
				CodeLen = 1;
			}
		}
	}
}

static void AddSimple(char *NName, Word NCode, Boolean residualAllowed) {
	if(residualAllowed) NCode |= FLAG_RESIDUAL_ALLOWED;
	AddInstTable(InstTable, NName, NCode, DecodeSimple);
}

static void AddCDS(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeCDS);
}

static void AddShift(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeShift);
}

static void InitFields(void) {
	InstTable = CreateInstTable(24);
	
	AddSimple("HOP", 0x0, True);
	AddSimple("MPY", 0x1, True);
	AddSimple("SUB", 0x2, True);
	AddSimple("DIV", 0x3, True);
	AddSimple("TNZ", 0x4, True);
	AddSimple("MPH", 0x5, True);
	AddSimple("AND", 0x6, True);
	AddSimple("ADD", 0x7, True);
	AddSimple("TRA", 0x8, True);
	AddSimple("XOR", 0x9, True);
	AddSimple("PIO", 0xA | FLAG_IMM_VALUE, False);
	AddSimple("STO", 0xB, True);
	AddSimple("TMI", 0xC, True);
	AddSimple("RSU", 0xD, True);
	AddSimple("CLA", 0xF, True);

	AddCDS("CDS", 2);
	AddCDS("CDSD", 1);
	AddCDS("CDSS", 0);

	AddShift("CL", 2);
	AddShift("SHL", 0);
	AddShift("SHR", 1);

	AddInstTable(InstTable, "EXM", 0, DecodeEXM);
	
	AddInstTable(InstTable, "HOP*", 0, DecodeExtendedHOP);
}

static void DeinitFields(void) {
	DestroyInstTable(InstTable);
}

static void MakeCode_lvdc(void) {
	CodeLen = 0; DontPrint = False;
	if((*OpPart.str.p_str == '\0') && (ArgCnt == 0)) return;
	if(DecodeIntelPseudo(False)) return;
	if(Memo("")) return;
	if(!LookupInstTable(InstTable, OpPart.str.p_str)) WrStrErrorPos(ErrNum_UnknownInstruction, &OpPart);
}

static Boolean IsDef_lvdc(void) {
	return FALSE;
}

static void SwitchFrom_lvdc(void) {
	DeinitFields();
}

static void SwitchTo_lvdc(void) {
	const TFamilyDescr *pDescr = FindFamilyByName("LVDC");
	SetIntConstMode(eIntConstModeMoto);
	TurnWords = False;
	ShiftIsOccupied = False;
	PCSymbol = "$";
	HeaderID = pDescr->Id;
	DivideChars = ",";
	HasAttrs = False;
	
	ValidSegs = (1 << SegCode);
	Grans[SegCode] = 4; ListGrans[SegCode] = 4; SegInits[SegCode] = 0;
	SegLimits[SegCode] = 0x7fffl;
	
	MakeCode = MakeCode_lvdc;
	IsDef = IsDef_lvdc;
	SwitchFrom = SwitchFrom_lvdc;
	InitFields();
}

void code_lvdc_init(void) {
	CPUlvdc = AddCPU("LVDC", SwitchTo_lvdc);
}
