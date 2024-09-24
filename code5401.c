/*
 * (Tholin, 24/09/2024) Added support for AS5401
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

#include "code5401.h"

static CPUVar CPU5401;

static void DecodeFixed(Word Code, Boolean canHaveArg)
{
  CPUVar MinCPU = CPU5401 + (CPUVar)Hi(Code);

  if(ChkArgCnt(0, canHaveArg ? 1 : 0) && ChkMinCPU(MinCPU))
  {
    if(ArgCnt == 1) {
      Boolean OK;
      BAsmCode[0] = EvalStrIntExpression(&ArgStr[1], UInt4, &OK);
      if(OK)
      {
        BAsmCode[0] <<= 4;
        BAsmCode[0] |= Lo(Code);
        CodeLen = 1;
      }
    }else {
      BAsmCode[0] = Lo(Code);
      CodeLen = 1;
    }
  }
}

static void DecodeFixedArgOptional(Word Code)
{
  DecodeFixed(Code, True);
}

static void DecodeFixedNoArg(Word Code)
{
  DecodeFixed(Code, False);
}

static void DecodeJump(Word Code)
{
  CPUVar MinCPU = CPU5401 + (CPUVar)Hi(Code);
  if(ChkArgCnt(0, 1) && ChkMinCPU(MinCPU))
  {
    if(ArgCnt == 1) {
      Boolean OK;
      int branchDest = EvalStrIntExpression(&ArgStr[1], UInt12, &OK);
      if(OK) {
        BAsmCode[0] = 0b0010;
        BAsmCode[1] = 0b0111 | ((branchDest & 15) << 4);
        BAsmCode[2] = 0b0111 | (((branchDest >> 4) & 15) << 4);
        BAsmCode[3] = 0b0111 | (((branchDest >> 8) & 15) << 4);
        BAsmCode[4] = Lo(Code);
        CodeLen = 5;
      }
    }else {
      BAsmCode[0] = Lo(Code);
      CodeLen = 1;
    }
  }
}

static void InitFields(void)
{
  InstTable = CreateInstTable(17);
  
  AddInstTable(InstTable, "LD", 0b0000, DecodeFixedArgOptional);
  AddInstTable(InstTable, "STR", 0b0001, DecodeFixedArgOptional);
  AddInstTable(InstTable, "SEI", 0b0010, DecodeFixedNoArg);
  AddInstTable(InstTable, "LML", 0b0011, DecodeFixedArgOptional);
  AddInstTable(InstTable, "JMP", 0b0100, DecodeJump);
  AddInstTable(InstTable, "JC", 0b0101, DecodeJump);
  AddInstTable(InstTable, "JZ", 0b0110, DecodeJump);
  AddInstTable(InstTable, "LDR", 0b0111, DecodeFixedArgOptional);
  AddInstTable(InstTable, "ADD", 0b1000, DecodeFixedArgOptional);
  AddInstTable(InstTable, "SUB", 0b1001, DecodeFixedArgOptional);
  AddInstTable(InstTable, "ADC", 0b1010, DecodeFixedArgOptional);
  AddInstTable(InstTable, "SUC", 0b1011, DecodeFixedArgOptional);
  AddInstTable(InstTable, "OR", 0b1100, DecodeFixedArgOptional);
  AddInstTable(InstTable, "AND", 0b1101, DecodeFixedArgOptional);
  AddInstTable(InstTable, "XOR", 0b1110, DecodeFixedArgOptional);
  AddInstTable(InstTable, "LMH", 0b1111, DecodeFixedArgOptional);
}

static void DeinitFields(void)
{
  DestroyInstTable(InstTable);
}

/*---------------------------------------------------------------------------*/
/* Callbacks */

static void MakeCode_5401(void)
{
  CodeLen = 0;
  DontPrint = False;

  /* zu ignorierendes */

  if (Memo(""))
    return;

  if (!LookupInstTable(InstTable, OpPart.str.p_str))
    WrStrErrorPos(ErrNum_UnknownInstruction, &OpPart);
}

static Boolean IsDef_5401(void)
{
  return Memo("REG");
}

static void SwitchFrom_5401(void)
{
  DeinitFields();
}

static void SwitchTo_5401(void)
{
  const TFamilyDescr *pDescr;

  pDescr = FindFamilyByName("5401");

  TurnWords = False;
  IntConstMode = eIntConstModeMoto;
  ShiftIsOccupied = False;

  PCSymbol = "$";
  HeaderID = pDescr->Id;
  NOPCode = 0x00;
  DivideChars = ",";
  HasAttrs = False;

  ValidSegs = (1 << SegCode);
  Grans[SegCode ] = 1; ListGrans[SegCode ] = 1; SegInits[SegCode ] = 0;
  SegLimits[SegCode] = 0xfff;

  MakeCode = MakeCode_5401;
  IsDef = IsDef_5401;
  SwitchFrom = SwitchFrom_5401;

  InitFields();
}

/*---------------------------------------------------------------------------*/
/* Initialisierung */

void code5401_init(void)
{
  CPU5401 = AddCPU("5401", SwitchTo_5401);
}
