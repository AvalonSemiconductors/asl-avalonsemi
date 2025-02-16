/*
 * (Tholin, 14/01/2025) Added support for VLIW
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

#include "codevliw.h"

static CPUVar CPUvliw;

//DONTFORGET: predicates

Byte pIdx = 0;
QuadWord pack[3];

const QuadWord impliedCodes[] = {
	0, //NOP
};

static void DecodeImplied(Word Index) {
	pack[pIdx++] = impliedCodes[Index];
}

static void AddImplied(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeImplied);
}

static void InitFields(void) {
	InstTable = CreateInstTable(55);
	AddImplied("NOP", 0);
}

static void DeinitFields(void) {
	DestroyInstTable(InstTable);
}

static void MakeCode_vliw(void) {
	CodeLen = 0; DontPrint = False;
	Byte prevIdx;
	if((*OpPart.str.p_str == '\0') && (ArgCnt == 0)) return;
	if(DecodeIntelPseudo(False)) {
		if(pIdx != 0) {
			printf("Pseudo-op inside a pack is not allowed\r\n");
			WrStrErrorPos(ErrNum_InvFormat, &OpPart);
		}
		return;
	}
	if(Memo("")) return;
	if(pIdx >= 3) {
		if(strcmp(OpPart.str.p_str, "---") != 0) {
			printf("Invalid pack terminator\r\n");
			WrStrErrorPos(ErrNum_InvFormat, &OpPart);
		}
		if(pIdx == 0) {}
		if(pIdx > 3) {
			printf("Too many instructions in pack\r\n");
			WrStrErrorPos(ErrNum_InvFormat, &OpPart);
			pIdx = 3;
		}
		if(pIdx != 3) {
			//Too few instructions for pack, insert NOPs in unused slots
			for(Byte i = pIdx; i < 3; i++) pack[i] = NOPCode;
		}
		CodeLen = 0;
		QuadWord instr = pack[0];
		for(Byte i = 0; i < 5; i++) {
			BAsmCode[CodeLen++] = instr & 0xFF;
			instr >>= 8;
		}
		BAsmCode[CodeLen] = instr & 0x03;
		instr = pack[1];
		BAsmCode[CodeLen++] |= (instr & 0x3F) << 2;
		instr >>= 6;
		for(Byte i = 0; i < 4; i++) {
			BAsmCode[CodeLen++] = instr & 0xFF;
			instr >>= 8;
		}
		BAsmCode[CodeLen] = instr & 0x0F;
		instr = pack[2];
		BAsmCode[CodeLen++] |= (instr & 0x0F) << 4;
		instr >>= 4;
		for(Byte i = 0; i < 4; i++) {
			BAsmCode[CodeLen++] = instr & 0xFF;
			instr >>= 8;
		}
		BAsmCode[CodeLen] = instr & 0x3F;
		//TODO: breaks
		CodeLen++;
		pIdx = 0;
	}
	prevIdx = pIdx;
	if(!LookupInstTable(InstTable, OpPart.str.p_str)) WrStrErrorPos(ErrNum_UnknownInstruction, &OpPart);
	else {
		if(pIdx == prevIdx) {
			printf("Instruction(s) failed to assemble, inserting NOP\r\n");
			pack[pIdx++] = NOPCode;
		}
	}
}

static Boolean IsDef_vliw(void) {
	return FALSE;
}

static void SwitchFrom_vliw(void) {
	DeinitFields();
}

static void SwitchTo_vliw(void) {
	pIdx = 0;
	const TFamilyDescr *pDescr = FindFamilyByName("VLIW");
	SetIntConstMode(eIntConstModeMoto);
	TurnWords = False;
	ShiftIsOccupied = False;
	PCSymbol = "$";
	HeaderID = pDescr->Id;
	DivideChars = ",";
	HasAttrs = False;
	
	ValidSegs = (1 << SegCode);
	Grans[SegCode] = 2; ListGrans[SegCode] = 2; SegInits[SegCode] = 0;
	NOPCode = 0;
	SegLimits[SegCode] = 0xFFFFFFFFul;
	MakeCode = MakeCode_vliw; IsDef = IsDef_vliw;
	
	SwitchFrom = SwitchFrom_vliw; InitFields();
}

void code_vliw_init(void) {
	CPUvliw = AddCPU("VLIW", SwitchTo_vliw);
}
