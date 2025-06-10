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
Boolean breaks[3];

const QuadWord impliedCodes[] = {
	0xF<<3, //NOP
	0xABAB<<3, //BPT
};

static Word DisectRegStr(char* pAsc, Boolean isDest) {
	if(strcmp(pAsc, "zero") == 0) return isDest ? 0 : 59; //Silicon bug workaround: r59 is the zero-reg now
	if(pAsc[0] != 'r' && pAsc[0] != 'R') return 1000;
	pAsc++;
	Word res = pAsc[0] - '0';
	if(res > 9) return 1000;
	if(pAsc[1] == 0) return res;
	res *= 10;
	Word temp = pAsc[1] - '0';
	if(temp > 9) return 1000;
	res = res + temp;
	if(res > 63) return 1000;
	return res;
}

static Word DisectReg(struct sStrComp *pComp, Boolean isDest) {
	char* pAsc = pComp->str.p_str;
	return DisectRegStr(pAsc, isDest);
}

static Word DisectPredStr(char* pAsc) {
	if(strcmp(pAsc, "always") == 0) return 0;
	if(pAsc[0] != 'p' && pAsc[0] != 'P') return 1000;
	pAsc++;
	Word res = pAsc[0] - '0';
	if(res > 7) return 1000;
	return res;
}

static Word DisectPred(struct sStrComp *pComp) {
	char* pAsc = pComp->str.p_str;
	return DisectPredStr(pAsc);
}

static void DecodeImplied(Word Index) {
	pack[pIdx++] = impliedCodes[Index];
}

static void DecodeALU(Word Index) {
	if(ChkArgCnt(3, 3)) {
		Word rd = DisectReg(&ArgStr[1], TRUE);
		Word ri1 = DisectReg(&ArgStr[2], FALSE);
		Word ri2 = DisectReg(&ArgStr[3], FALSE);
		if(ri1 == 1000 || ri2 == 1000 || rd == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
			return;
		}
		Boolean halfword = (Index & 64) != 0;
		Boolean upper = (Index & 128) != 0;
		Index &= 0x1F;
		QuadWord instr = 0b001;
		instr |= Index << 3;
		instr |= (QuadWord)rd << 11;
		instr |= (QuadWord)ri1 << 18;
		instr |= (QuadWord)ri2 << 25;
		if(halfword) instr |= 1UL << 40;
		if(upper) instr |= 1UL << 41;
		pack[pIdx++] = instr;
	}
}

static void DecodeALUSingle(Word Index) {
	if(ChkArgCnt(2, 2)) {
		Word rd = DisectReg(&ArgStr[1], TRUE);
		Word ri1 = DisectReg(&ArgStr[2], FALSE);
		if(rd == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
			return;
		}
		if(ri1 == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[2]);
			return;
		}
		Boolean halfword = (Index & 64) != 0;
		Boolean upper = (Index & 128) != 0;
		Index &= 0x1F;
		QuadWord instr = 0b001;
		instr |= Index << 3;
		instr |= (QuadWord)rd << 11;
		instr |= (QuadWord)ri1 << 18;
		if(halfword) instr |= 1UL << 40;
		if(upper) instr |= 1UL << 41;
		pack[pIdx++] = instr;	
	}
}

static void DecodeCpy(Word Index) {
	if(ChkArgCnt(2, 2)) {
		Word rd = DisectReg(&ArgStr[1], TRUE);
		if(rd == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
			return;
		}
		Word ri1 = DisectReg(&ArgStr[2], FALSE);
		if(ri1 == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[2]);
			return;
		}
		QuadWord instr = 0b10100001;
		instr |= (QuadWord)rd << 11;
		instr |= (QuadWord)ri1 << 18;
		instr |= (QuadWord)ri1 << 25;
		Boolean halfword = (Index & 64) != 0;
		Boolean upper = (Index & 128) != 0;
		if(halfword) instr |= 1UL << 40;
		if(upper) instr |= 1UL << 41;
		pack[pIdx++] = instr;
	}
}

static void DecodeALUImmediate(Word Index) {
	if(ChkArgCnt(3, 3)) {
		Word rd = DisectReg(&ArgStr[1], TRUE);
		if(rd == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
			return;
		}
		Word ri1 = DisectReg(&ArgStr[2], FALSE);
		if(ri1 == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[2]);
			return;
		}
		Boolean halfword = (Index & 64) != 0;
		Boolean upper = (Index & 128) != 0;
		Boolean si = (Index & 256) != 0;
		Boolean dynamicSignedness = (Index & 512) != 0;
		Index &= 0x1F;
		Boolean OK;
		QuadWord imm;
		if(halfword) {
			if(dynamicSignedness) {
				si = 0;
				imm = EvalStrIntExpression(&ArgStr[3], UInt16, &OK);
				if(!OK) {
					imm = EvalStrIntExpression(&ArgStr[3], Int16, &OK);
					if(!OK) return;
					si = 1;
				}
			}else {
				imm = EvalStrIntExpression(&ArgStr[3], si ? Int16 : UInt16, &OK);
				if(!OK) return;
			}
		}else {
			if(dynamicSignedness) {
				si = 0;
				imm = EvalStrIntExpression(&ArgStr[3], UInt32, &OK);
				if(!OK) {
					imm = EvalStrIntExpression(&ArgStr[3], Int32, &OK);
					if(!OK) return;
					si = 1;
				}
			}else {
				imm = EvalStrIntExpression(&ArgStr[3], si ? Int32 : UInt32, &OK);
				if(!OK) return;
			}
			if((imm & 0xFFFF0000U) == 0 || (si && (imm & 0xFFFF0000U) == 0xFFFF0000U)) upper = 0;
			else if((imm & 0x0000FFFFU) != 0) {
				WrStrErrorPos(ErrNum_InvFormat, &ArgStr[3]);
				return;
			}else {
				upper = 1;
				imm >>= 16;
			}
		}
		imm &= 0x0000FFFFU;
		QuadWord instr = 0b010;
		instr |= Index << 3;
		instr |= (QuadWord)rd << 11;
		if(halfword) instr |= 1UL << 17;
		instr |= (QuadWord)ri1 << 18;
		if(si) instr |= 1UL << 24;
		if(upper) instr |= 1UL << 25;
		instr |= imm << 26;
		pack[pIdx++] = instr;
	}
}

static void DecodeLI(Word Index) {
	if(ChkArgCnt(2, 2)) {
		Word rd = DisectReg(&ArgStr[1], TRUE);
		if(rd == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
			return;
		}
		if((Index & 1) != 0) {
			Boolean OK;
			QuadWord imm = EvalStrIntExpression(&ArgStr[2], UInt16, &OK);
			if(!OK) {
				imm = EvalStrIntExpression(&ArgStr[2], Int16, &OK);
				if(!OK) return;
			}
			
			imm &= 0x0000FFFFU;
			QuadWord instr = 0b10100010;
			instr |= (QuadWord)rd << 11;
			instr |= 1U << 17;
			instr |= 1U << 25;
			instr |= imm << 26;
			pack[pIdx++] = instr;
			return;
		}
		Boolean si = (Index & 256) != 0;
		Boolean OK;
		QuadWord imm = EvalStrIntExpression(&ArgStr[2], si ? Int16 : UInt16, &OK);
		if(!OK) return;
		imm &= 0x0000FFFFU;
		QuadWord instr = 0b10100010;
		instr |= (QuadWord)rd << 11;
		if(si) instr |= 1U << 24;
		else if((Index & 128) == 0) instr |= 1U << 17;
		instr |= imm << 26;
		pack[pIdx++] = instr;
	}
}

static void DecodeLIPC(Word Index) {
	if(ChkArgCnt(2, 2)) {
		Word rd = DisectReg(&ArgStr[1], TRUE);
		if(rd == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
			return;
		}
		Word ri1 = DisectReg(&ArgStr[2], FALSE);
		if(ri1 == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[2]);
			return;
		}
		QuadWord instr = 0b0001010;
		instr |= 1UL << 31;
		instr |= (QuadWord)rd << 11;
		instr |= (QuadWord)ri1 << 18;
		pack[pIdx++] = instr;
	}
}

static void DecodeLoadstore(Word Index) {
	if(ChkArgCnt(2, 2)) {
		Word rdrs = DisectReg(&ArgStr[1], (Index & 1) != 0 ? FALSE : TRUE);
		if(rdrs == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
			return;
		}
		char* pAsc = ArgStr[2].str.p_str;
		char regBuff[8];
		memset(regBuff, 0, 8);
		int counter = 0;
		int bracketPos = 0;
		Boolean inBrackets = 0;
		while(1) {
			Word a = counter - bracketPos - 1;
			if(inBrackets) {
				regBuff[a] = pAsc[counter];
				if(a >= 7) {
					WrStrErrorPos(ErrNum_InvReg, &ArgStr[2]);
					return;
				}
			}
			if(pAsc[counter] == '(') {
				if(inBrackets) {
					WrStrErrorPos(ErrNum_InvReg, &ArgStr[2]);
					return;
				}
				inBrackets = 1;
				bracketPos = counter;
			}
			if(pAsc[counter] == 0) {
				WrStrErrorPos(ErrNum_InvFormat, &ArgStr[2]);
				return;
			}
			if(pAsc[counter] == ')') {
				if(!inBrackets) {
					WrStrErrorPos(ErrNum_InvFormat, &ArgStr[2]);
					return;
				}
				regBuff[a] = 0;
				break;
			}
			counter++;
		}
		Word ridx = DisectRegStr(regBuff, FALSE);
		if(ridx == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[2]);
			return;
		}
		StrCompShorten(&ArgStr[2], strlen(ArgStr[2].str.p_str) - bracketPos);
		Boolean OK;
		QuadWord imm = EvalStrIntExpression(&ArgStr[2], Int24, &OK);
		if(!OK) return;
		Boolean si = (imm & 0x1000000000U) != 0;
		if(!si && imm >= 0x10000U) {
			WrStrErrorPos(ErrNum_OverRange, &ArgStr[2]);
			return;
		}
		if(si && ((imm & 0x10000U) == 0 || (imm & 0xFFFFE0000U) != 0xFFFFE0000U)) {
			WrStrErrorPos(ErrNum_UnderRange, &ArgStr[2]);
			return;
		}
		imm &= 0x0001FFFFU;
		QuadWord instr = 0b100;
		instr |= (QuadWord)(Index & 0xF) << 3;
		instr |= (QuadWord)rdrs << 11;
		instr |= (QuadWord)ridx << 18;
		instr |= imm << 25;
		if((Index & 0x10) != 0) instr |= 1U << 7;
		if((Index & 0x20) != 0) instr |= 1U << 24;
		pack[pIdx++] = instr;
	}
}

static void DecodeJump(Word Index) {
	if(ChkArgCnt(3, 3)) {
		Word rd = DisectReg(&ArgStr[1], TRUE);
		if(rd == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
			return;
		}
		Word ridx = DisectReg(&ArgStr[2], FALSE);
		if(ridx == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[2]);
			return;
		}
		Boolean OK;
		QuadWord imm = EvalStrIntExpression(&ArgStr[3], Int24, &OK);
		if(!OK) return;
		Boolean si = (imm & 0x1000000000U) != 0;
		if(!si && imm >= 0x10000U) {
			WrStrErrorPos(ErrNum_OverRange, &ArgStr[2]);
			return;
		}
		if(si && ((imm & 0x10000U) == 0 || (imm & 0xFFFFE0000U) != 0xFFFFE0000U)) {
			WrStrErrorPos(ErrNum_UnderRange, &ArgStr[2]);
			return;
		}
		imm &= 0x0001FFFFU;
		QuadWord instr = 0b110;
		instr |= (QuadWord)(Index & 0xF) << 3;
		instr |= (QuadWord)rd << 11;
		instr |= (QuadWord)ridx << 18;
		instr |= imm << 25;
		pack[pIdx++] = instr;
	}
}

static void DecodeBranch(Word Index) {
	Boolean single = (Index & 64) != 0;
	if(ChkArgCnt(single ? 2 : 3, single ? 2 : 3)) {
		int iIdx = 3;
		Word ri1 = DisectReg(&ArgStr[1], FALSE);
		if(ri1 == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
			return;
		}
		Word ri2 = 59; //Silicon bug workaround
		if(ArgCnt == 2) {
			iIdx = 2;
		}else {
			ri2 = DisectReg(&ArgStr[2], FALSE);
			if(ri2 == 1000) {
				WrStrErrorPos(ErrNum_InvReg, &ArgStr[2]);
				return;
			}
		}
		Boolean OK;
		QuadInt targ = EvalStrIntExpression(&ArgStr[iIdx], Int32, &OK);
		if(!OK) return;
		QuadInt dist = targ - EProgCounter();
		dist /= 16;
		if(dist > 65535) {
			WrStrErrorPos(ErrNum_OverRange, &ArgStr[iIdx]);
			return;
		}
		if(dist < -65536) {
			WrStrErrorPos(ErrNum_UnderRange, &ArgStr[iIdx]);
			return;
		}
		Boolean si = (Index & 128) != 0;
		Index &= 0x7;
		QuadWord instr = 0b101;
		instr |= (QuadWord)Index << 3;
		if(si) instr |= 1U << 6;
		instr |= (QuadWord)ri1 << 11;
		instr |= (QuadWord)ri2 << 18;
		instr |= dist << 25;
		pack[pIdx++] = instr;
	}
}

static void DecodePredicate(Word Index) {
	Boolean single = (Index & 64) != 0;
	if(ChkArgCnt(single ? 2 : 3, single ? 2 : 3)) {
		Word dp = DisectPred(&ArgStr[1]);
		if(dp == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[1]);
			return;
		}
		Word ri1 = DisectReg(&ArgStr[2], FALSE);
		if(ri1 == 1000) {
			WrStrErrorPos(ErrNum_InvReg, &ArgStr[2]);
			return;
		}
		Word ri2 = 59; //Silicon bug workaround
		if(ArgCnt != 2) {
			ri2 = DisectReg(&ArgStr[3], FALSE);
			if(ri2 == 1000) {
				WrStrErrorPos(ErrNum_InvReg, &ArgStr[3]);
				return;
			}
		}
		Boolean si = (Index & 128) != 0;
		Index &= 0x7;
		QuadWord instr = 0b011;
		instr |= (QuadWord)Index << 3;
		if(si) instr |= 1U << 6;
		instr |= (QuadWord)dp << 11;
		instr |= (QuadWord)ri1 << 18;
		instr |= (QuadWord)ri2 << 25;
		pack[pIdx++] = instr;
	}
}

static void AddImplied(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeImplied);
}

static void AddALU(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeALU);
}

static void AddALUSingle(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeALUSingle);
}

static void AddALUImmediate(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeALUImmediate);
}

static void AddLoadstore(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeLoadstore);
}

static void AddBranch(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodeBranch);
}

static void AddPredicate(char *NName, Word NCode) {
	AddInstTable(InstTable, NName, NCode, DecodePredicate);
}

static void InitFields(void) {
	InstTable = CreateInstTable(122);
	AddImplied("NOP", 0);
	AddImplied("BPT", 1);
	
	AddALU("ADD", 0);
	AddALU("ADD.L", 0 + 64);
	AddALU("ADD.U", 0 + 64 + 128);
	AddALU("SUB", 16);
	AddALU("SUB.L", 16 + 64);
	AddALU("SUB.U", 16 + 64 + 128);
	AddALU("SRA", 1);
	AddALU("SRL", 2);
	AddALU("SLL", 18);
	AddALU("SLA", 18);
	AddALU("SLTU", 3);
	AddALU("SLT", 4);
	AddALU("AND", 5);
	AddALU("AND.L", 5 + 64);
	AddALU("AND.U", 5 + 64 + 128);
	AddALU("OR", 6);
	AddALU("OR.L", 6 + 64);
	AddALU("OR.U", 6 + 64 + 128);
	AddALU("XOR", 7);
	AddALU("XOR.L", 7 + 64);
	AddALU("XOR.U", 7 + 64 + 128);
	AddALU("MULU", 8);
	AddALU("MULHU", 9);
	AddALU("MUL", 24);
	AddALU("MULH", 25);
	AddALU("DIVU", 10);
	AddALU("MODU", 11);
	AddALU("DIV", 26);
	AddALU("MOD", 27);
	AddALUSingle("NOT", 12);
	AddALUSingle("NOT.L", 12 + 64);
	AddALUSingle("NOT.U", 12 + 64 + 128);
	AddALUSingle("NEG", 13);
	AddALUSingle("NEG.L", 13 + 64);
	AddALUSingle("NEG.U", 13 + 64 + 128);
	AddInstTable(InstTable, "CPY", 0, DecodeCpy);
	AddInstTable(InstTable, "CPY.L", 64, DecodeCpy);
	AddInstTable(InstTable, "CPY.U", 64 + 128, DecodeCpy);
	
	AddALUImmediate("ADDI", 0 + 512);
	AddALUImmediate("ADDI.L", 0 + 64 + 512);
	AddALUImmediate("ADDI.U", 0 + 64 + 128 + 512);
	AddALUImmediate("SUBI", 16 + 512);
	AddALUImmediate("SUBI.L", 16 + 64 + 512);
	AddALUImmediate("SUBI.H", 16 + 64 + 128 + 512);
	AddALUImmediate("SRAI", 1);
	AddALUImmediate("SRLI", 2);
	AddALUImmediate("SLLI", 18);
	AddALUImmediate("SLAI", 18);
	AddALUImmediate("SLTIU", 3);
	AddALUImmediate("SLTI", 4 + 256);
	AddALUImmediate("ANDI", 5);
	AddALUImmediate("ANDI.L", 5 + 64);
	AddALUImmediate("ANDI.U", 5 + 64 + 128);
	AddALUImmediate("ORI", 6);
	AddALUImmediate("ORI.L", 6 + 64);
	AddALUImmediate("ORI.U", 6 + 64 + 128);
	AddALUImmediate("XORI", 7);
	AddALUImmediate("XORI.L", 7 + 64);
	AddALUImmediate("XORI.U", 7 + 64 + 128);
	AddALUImmediate("MULIU", 8);
	AddALUImmediate("MULHIU", 9);
	AddALUImmediate("MULI", 24 + 256);
	AddALUImmediate("MULHI", 25);
	AddALUImmediate("DIVIU", 10);
	AddALUImmediate("MODIU", 11);
	AddALUImmediate("DIVI", 26);
	AddALUImmediate("MODI", 27);
	AddInstTable(InstTable, "LLI", 256, DecodeLI); //Signed, updates whole reg
	AddInstTable(InstTable, "LLIU", 0, DecodeLI); //Unsigned, updates only bits 0 - 15
	AddInstTable(InstTable, "LUI", 1, DecodeLI); //Signed or Unsigned, updates only bits 16 - 31
	AddInstTable(InstTable, "LIU", 128, DecodeLI); //Unsigned, updates bits 0 - 15 and clears bit 16 - 31
	
	AddInstTable(InstTable, "LIPC", 0, DecodeLIPC);
	
	AddLoadstore("LB", 0b000010);
	AddLoadstore("LBU", 0b000000);
	AddLoadstore("LB.L", 0b100010);
	AddLoadstore("LBU.L", 0b100000);
	AddLoadstore("LBU.LL", 0b110000);
	AddLoadstore("LH", 0b000110);
	AddLoadstore("LHU", 0b000100);
	AddLoadstore("LHU.L", 0b100100);
	AddLoadstore("LW", 0b001000);
	AddLoadstore("SB", 0b000001);
	AddLoadstore("SH", 0b000101);
	AddLoadstore("SW", 0b001001);
	
	AddInstTable(InstTable, "JALR", 0, DecodeJump);
	
	AddBranch("BE", 0);
	AddBranch("BL", 1);
	AddBranch("BLE", 3);
	AddBranch("BNE", 4);
	AddBranch("BGE", 5);
	AddBranch("BG", 7);
	AddBranch("BS", 0 + 128);
	AddBranch("BLS", 1 + 128);
	AddBranch("BLES", 3 + 128);
	AddBranch("BNS", 4 + 128);
	AddBranch("BGES", 5 + 128);
	AddBranch("BGS", 7 + 128);
	AddBranch("BEZ", 0 + 64);
	AddBranch("BNEZ", 4 + 64);
	AddBranch("BP", 0 + 64 + 128);
	AddBranch("BN", 4 + 64 + 128);
	AddBranch("BGTZ", 7 + 64 + 128);
	
	AddPredicate("PE", 0);
	AddPredicate("PL", 1);
	AddPredicate("PLE", 3);
	AddPredicate("PNE", 4);
	AddPredicate("PGE", 5);
	AddPredicate("PG", 7);
	AddPredicate("PS", 0 + 128);
	AddPredicate("PLS", 1 + 128);
	AddPredicate("PLES", 3 + 128);
	AddPredicate("PNS", 4 + 128);
	AddPredicate("PGES", 5 + 128);
	AddPredicate("PGS", 7 + 128);
	AddPredicate("PEZ", 0 + 64);
	AddPredicate("PNEZ", 4 + 64);
	AddPredicate("PP", 0 + 64 + 128);
	AddPredicate("PN", 4 + 64 + 128);
	AddPredicate("PGTZ", 7 + 64 + 128);
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
	Boolean isTerminator = strcmp(OpPart.str.p_str, "---") == 0;
	if(pIdx >= 3 || isTerminator) {
		if(!isTerminator) {
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
		if(breaks[0]) BAsmCode[CodeLen] |= 64;
		if(breaks[1]) BAsmCode[CodeLen] |= 128;
		CodeLen++;
		pIdx = 0;
		return;
	}
	prevIdx = pIdx;
	char* pAsc = ArgStr[ArgCnt].str.p_str;
	int l = strlen(pAsc);
	Word predicate = 0xFFFF;
	if(pAsc[l - 1] == ']') {
		int i = l - 1;
		int shortLen = 1;
		do {
			i--;
			shortLen++;
			if(pAsc[i] == '[') break;
		}while(i);
		if(pAsc[i] != '[') {
			WrError(ErrNum_InvFormat);
		}else {
			i++;
			pAsc[l - 1] = 0;
			predicate = DisectPredStr(pAsc + i);
			if(predicate == 1000) {
				predicate = 0xFFFF;
				WrError(ErrNum_InvFormat);
			}
		}
		StrCompShorten(&ArgStr[ArgCnt], shortLen);
		pAsc = ArgStr[ArgCnt - 1].str.p_str;
		l = strlen(pAsc);
	}
	if(pAsc[l - 1] == '#' && pAsc[l - 2] == ' ') {
		StrCompShorten(&ArgStr[ArgCnt], 2);
		breaks[pIdx] = 1;
	}else breaks[pIdx] = 0;
	if(!LookupInstTable(InstTable, OpPart.str.p_str)) WrStrErrorPos(ErrNum_UnknownInstruction, &OpPart);
	if(pIdx == prevIdx) {
		printf("Instruction(s) failed to assemble, inserting NOP\r\n");
		pack[pIdx++] = NOPCode;
	}
	if(predicate != 0xFFFF) pack[pIdx - 1] |= (QuadWord)predicate << 8;
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
	SetIntConstMode(eIntConstModeC);
	TurnWords = False;
	ShiftIsOccupied = False;
	PCSymbol = "$";
	HeaderID = pDescr->Id;
	DivideChars = ",";
	HasAttrs = False;
	
	ValidSegs = (1 << SegCode);
	Grans[SegCode] = 1; ListGrans[SegCode] = 1; SegInits[SegCode] = 0;
	NOPCode = 0xF<<3;
	SegLimits[SegCode] = 0xFFFFFFFFul;
	MakeCode = MakeCode_vliw; IsDef = IsDef_vliw;
	
	SwitchFrom = SwitchFrom_vliw; InitFields();
}

void code_vliw_init(void) {
	CPUvliw = AddCPU("VLIW", SwitchTo_vliw);
}
