#ifndef _ASMSUB_H
#define _ASMSUB_H
/* asmsub.h */
/*****************************************************************************/
/* SPDX-License-Identifier: GPL-2.0-only OR GPL-3.0-only                     */
/*                                                                           */
/* AS-Portierung                                                             */
/*                                                                           */
/* Unterfunktionen, vermischtes                                              */
/*                                                                           */
/*****************************************************************************/

#include <stddef.h>

#define LISTLINESPACE 20

struct sLineComp;
struct sStrComp;

typedef void (*TSwitchProc)(
#ifdef __PROTOS__
void
#endif
);


extern void AsmSubPassInit(void);


extern long GTime(void);


extern void UpString(char *s);

extern char *QuotPosQualify(const char *s, char Zeichen, tQualifyQuoteFnc QualifyQuoteFnc);
#define QuotPos(s, Zeichen) QuotPosQualify(s, Zeichen, NULL)
extern char *QuotMultPosQualify(const char *s, const char *pSearch, tQualifyQuoteFnc QualifyQuoteFnc);
#define QuotMultPos(s, pSearch) QuotMultPosQualify(s, pSearch, NULL)
extern char *QuotSMultPosQualify(const char *s, const char *pStrs, tQualifyQuoteFnc QualifyQuoteFnc);
#define QuotSMultPos(s, pStrs) QuotSMultPosQualify(s, pStrs, NULL)

extern char *RQuotPos(char *s, char Zeichen);

extern char *FirstBlank(const char *s);

extern void SplitString(char *Source, char *Left, char *Right, char *Trenner);

extern void TranslateString(char *s, int Length);

extern ShortInt StrCaseCmp(const char *s1, const char *s2, LongInt Hand1, LongInt Hand2);

extern char *MatchChars(const char *pStr, const char *pPattern, ...);
extern char *MatchCharsRev(const char *pStr, const char *pPattern, ...);

extern char *FindClosingParenthese(const char *pStr);

extern char *FindOpeningParenthese(const char *pStrBegin, const char *pStrEnd, const char Bracks[2]);

#ifdef PROFILE_MEMO
static inline Boolean Memo(const char *s)
{
  NumMemo++;
  return !strcmp(OpPart.Str, s);
}
#else
# define Memo(s) (!strcmp(OpPart.Str,(s)))
#endif


extern void AddSuffix(char *s, const char *Suff);

extern void KillSuffix(char *s);

extern const char *NamePart(const char *Name);

extern char *PathPart(char *Name);


extern void FloatString(char *pDest, size_t DestSize, Double f);

extern void StrSym(TempResult *t, Boolean WithSystem, char *Dest, size_t DestLen, unsigned Radix);


extern void ResetPageCounter(void);

extern void NewPage(ShortInt Level, Boolean WithFF);

extern void WrLstLine(const char *Line);

extern void SetListLineVal(TempResult *t);

extern void LimitListLine(void);

extern void PrintOneLineMuted(FILE *pFile, const char *pLine,
                              const struct sLineComp *pMuteComponent,
                              const struct sLineComp *pMuteComponent2);
extern void PrLineMarker(FILE *pFile, const char *pLine, const char *pPrefix, const char *pTrailer,
                         char Marker, const struct sLineComp *pLineComp);

extern LargeWord ProgCounter(void);

extern LargeWord EProgCounter(void);

extern Word Granularity(void);

extern Word ListGran(void);

extern void ChkSpace(Byte AddrSpace, unsigned AddrSpaceMask);


extern void PrintUseList(void);

extern void ClearUseList(void);


extern int CompressLine(const char *TokNam, unsigned TokenNum, char *Line, unsigned LineSize, Boolean CaseSensitive);

extern void ExpandLine(const char *TokNam, unsigned TokenNum, char *Line, unsigned LineSize);

extern void KillCtrl(char *Line);

#ifdef __TURBOC__
extern void ChkStack(void);

extern void ResetStack(void);

extern LongWord StackRes(void);
#else
#define ChkStack() {}
#define ResetStack() {}
#define StackRes() 0
#endif


extern void AddCopyright(const char *NewLine);

extern void WriteCopyrights(TSwitchProc NxtProc);


extern char *ChkSymbNameUpTo(const char *pSym, const char *pUpTo);
extern Boolean ChkSymbName(const char *pSym);

extern char *ChkMacSymbNameUpTo(const char *pSym, const char *pUpTo);
extern Boolean ChkMacSymbName(const char *pSym);

extern unsigned visible_strlen(const char *pSym);


extern void AddIncludeList(char *NewPath);

extern void RemoveIncludeList(char *RemPath);


extern void ClearOutList(void);

extern void AddToOutList(const char *NewName);

extern void RemoveFromOutList(const char *OldName);

extern char *GetFromOutList(void);


extern void ClearShareOutList(void);

extern void AddToShareOutList(const char *NewName);

extern void RemoveFromShareOutList(const char *OldName);

extern char *GetFromShareOutList(void);


extern void ClearListOutList(void);

extern void AddToListOutList(const char *NewName);

extern void RemoveFromListOutList(const char *OldName);

extern char *GetFromListOutList(void);


extern void BookKeeping(void);


extern long DTime(long t1, long t2);


extern void InitPass(void);
extern void AddInitPassProc(SimpProc NewProc);

extern void ClearUp(void);
extern void AddClearUpProc(SimpProc NewProc);

extern void asmsub_init(void);

#include "asmerr.h"

#endif /* _ASMSUB_H */
