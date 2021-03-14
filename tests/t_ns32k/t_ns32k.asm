	cpu	ns32016
	fpu	ns32381
	pmmu	on
	relaxed	on
	supmode on

	page	0

	; register aliases

reg0	reg	r0
reg1	reg	r1
reg2	reg	r2
reg3	reg	r3
reg4	reg	r4
reg5	reg	r5
reg6	reg	r6
reg7	reg	r7
freg0	reg	f0
freg1	reg	f1
freg2	reg	f2
freg3	reg	f3
freg4	reg	f4
freg5	reg	f5
freg6	reg	f6
freg7	reg	f7
fptr	equ	fp
sptr	equ	sp
sbase	equ	sb

	absf	f0,f2

	absb	r5,r6
	absw	10,@20
	absd	8(sp),r7

	; iterate through addressing modes

	absd	r0,r0
	absd	r1,r0
	absd	r2,r0
	absd	r3,r0
	absd	r4,r0
	absd	r5,r0
	absd	r6,r0
	absd	r7,r0

	absd	(r0),r0
	absd	20(r1),r0
	absd	-20(r2),r0
	absd	200(r3),r0
	absd	-200(r4),r0
	absd	200000(r5),r0
	absd	-200000(r6),r0
	absd	0(r7),r0

	irp	reg,fp,sp,sb
	irp	disp2,,0,20,-20,200,-200,200000,-200000
	irp	disp1,,0,20,-20,200,-200,200000,-200000
	absd	disp2(disp1(reg)),r0
	endm
	endm
	endm

	absd	-3,r0		; immediate op always has full length
	absd	-300,r0
	absd	-3000000,r0

	absd	@20,r0
	absd	@200,r0
	absd	@200000,r0
	absd	@0ffffc0h,r0	; 24 bit address space, so code like 0ffffffc0h in 8 bits
	absd	@0ffe000h,r0	; ditto, code like 0ffffe000h in 16 bits
	absd	@100000h,r0	; 32 bit displacement

	irp	disp2,,0,20,-20,200,-200,200000,-200000
	irp	disp1,0,20,-20,200,-200,200000,-200000
	absd	ext(disp1)disp2,r0
	absd	ext ( disp1 )  disp2,r0
	endm
	endm

	absd	tos,r0		; something like (sp+)

	irp	reg,fp,sp,sb
	irp	disp,,0,20,-20,200,-200,200000,-200000
	absd	disp(reg),r0
	endm
	endm

	irp	disp,,+0,+20,-20,+200,-200,+200000,-200000
	absd	*disp,r0
	endm

	absd	0(SB)[r1:b],r0
	absd	10000 ( r4 ) [ r1 : w ] , r0
	absd	@10000[r1:d],r0
	absd	-100000(100000(sp)) [ r1:q ],r0

	irp	instr,beq,bne,bcs,bcc,bhi,bls,bgt,ble,bfs,bfc,blo,bhs,blt,bge,br
	instr	*-9ah
	instr	*+10
	endm

	; now by their alphabetical order:

	absf	f0,f2		; BE B5 00

	absb	r5,r6		; 4E B0 29
	absd	8(sp),r7	; 4E F3 C9 08

$$loop:	db 0ceh,63h,10h; muld	r2,r1		; CE 63 10
	acbb	-1,r0,$$loop	; CC 07 7D

	addf	f0,f7		; BE C1 01
	addl	f2,16(sb)	; BE 80 16 10

	addb	r0, r1		; 40 00
	addd	4(sb), -4(fp)	; 03 D6 04 7C

	addcb	32, r0		; 10 A0 20
	addcd	8(SB), r0	; 13 D0 08

	addpd	r0, r1		; 4E 7F 00
	addpb	5(sb), tos	; 4E FC D5 05

	addqb	-8, r0		; 0C 04

	addr	4(fp), r0	; 27 C0 04

	adjspd	-4(fp)		; 7F C5 7C

	andb	r0,r1		; 68 00

	ashb	2, 16(sb)  	; 4E 84 A6 02 10
	ashb	tos, 16(sb)	; 4E 84 BE 10

loop	set	*-154
	blo	loop		; AA BF 66
	bne	*+10		; 1A 0A

	bicb	r0, 3(sb)	; 88 06 03

	bicpsrb	b'10100010	; 7C A1 A2
	bicpsrw	b'10100010	; 7D A1 00 A2

	bispsrb	b'10100010	; 7C A3 A2

	bpt			; F2

ERROR	set	*-154
	br	ERROR		; EA BF 66
	br	*+10		; EA 0A

CALC	set	*+16
	bsr	CALC		; 02 10

	caseb	table[r7:b]	; 7C E7 DF 04
table:	db	x'0a, x'1a, x'3a, x'5a, x'7a, x'6a, x'4a

	cbitw	r0,0(r1)	; 4E 49 02 00

	checkb	r0, 4(sb), r2	; EE 80 D0 04

	expect	1500,1500
	cinv	a,d,i,r3	; 1E A7 1B
	cinv	i,r3		; 1E 27 19
	endexpect

	cpu	ns32532
	cinv	a,d,i,r3	; 1E A7 1B
	cinv	i,r3		; 1E 27 19

	cmpf	f0,f2		; BE 89 00

	cmpb	7(sb), 4(r0)	; 04 D2 07 04

	cmpmw	10(r0), 16(r1), 4; CE 45 42 0A 10 06

	cmpqb	-8,r0		; 1C 04

	cmpsb			; 0E 04 00

	comb	r0,-4(fp)	; 4E 34 06 7C

	cvtp	r0,32(sb),r2	; 6E 83 D0 20

	cxp	0		; 22 00
	cxp	1		; 22 01

	cxpd	8(sb)		; 7F D0 08

	deiw	r2, r0		; CE 2D 10

	dia			; C2

	divf	f0, f7	      	; BE E1 01
	divl	-8(fp), 16(sb)	; BE A0 C6 78 10

	divw	10(sp), 4(sp) 	; CE 7D CE 0A 04
	divd	-6(fp), 12(sb)	; CE BF C6 7A 0C

	dotf	f2, f3		; FE CD 10

	enter	[r0, r2, r7], 16; 82 85 10

	exit	[r0, r2, r7]	; 92 A1

	extw	r0, 0(r1), r2, 7; 2E 81 48 00 07

	extsw	16(sb), r2, 4, 7; CE 8D D0 10 86

	ffsw	8(sb), r0  	; 6E 05 D0 08
	ffsb	-4(fp), tos	; 6E C4 C5 7C

	flag			; D2

	floorfb	f0, r0	  	; 3B 3C 00
	floorld	f2, 16(sb)	; 3E BB 16 10

	ibitw	r0, 1(r1)	; 4E 79 02 01

	indexb	r0, 20(sb), -4(fp); 2E 04 D6 14 7C

	insw	r0, r2, 0(r1), 7; AE 41 12 00 07

	inssw	r2, 16(sb), 4, 7; CE 89 16 10 86

	jsr	0(4(sb))	; 7F 96 04 00

	jump	0(-8(fp))	; 7F 82 78 00

	lfsr	r0		; 3E 0F 00

	lmr	ptb0, r0	; 1E 0B 06

	logbf	f3, f2		; FE 95 18

	lprd	fp, r0		; 6F 04
	lprw	mod, 4(sb)	; ED D7 04

	lshb	4, 8(sb)     	; 4E 94 A6 04 08
	lshb	-4(fp), 8(sb)	; 4E 94 C6 7C 08

	meiw	r2, 10(sb)	; CE A5 16 0A
	meiw	r2, r0		; CE 25 10

	modb	4(sb), 8(sb)	; CE B8 D6 04 08

	movf	f0, 8(sb)	; BE 85 06 08

	movd	r0, 8(sb)	; 97 06 08

	movbf	2, f0	  	; 3E 04 A0 02
	movdl	16(sb), f2	; 3E 83 D0 10

	movfl	8(sb), f0	; 3E 1B D0 08

	movlf	f0, 12(sb)	; 3E 96 06 0C

	movmw	10(r0), 16(r1), 4;CE 41 42 0A 10 06

	movqw	7, tos		; DD BB

	movst			; 0E 80 00

	movsub	5(sp), 9(sb)	; AE 8C CE 05 09

	movusb	9(sb), 5(sp)	; AE 5C D6 09 05

	movxbw	2(sb), r0	; CE 10 D0 02

	movzbw	-4(fp), r0	; CE 14 C0 7C

	mulf	f0, f7	     	; BE F1 01
	mull	-8(fp), 8(sb)	; BE B0 C6 78 08

	mulw	5, r0		; CE 21 A0 00 05
	muld	4(-4(fp)), 3(sb); CE A3 86 7C 04 03

	negf 	f0, f2		; BE 95 00

	negb	r5, r6	    	; 4E A0 29
	negw	4(sb), 6(sb)	; 4E A1 D6 04 06

	nop

	notb	r0, r0	   	; 4E 24 00
	notw	10(r1), tos	; 4E E5 4D 0A

	orb	-6(fp), 11(sb)	; 98 C6 7A 0B

	polyf	f2, f3		; FE C9 10

	quob	r0, r7	    	; CE F0 01
	quow	4(sb), 8(sb)	; CE B1 D6 04 08

	rdval	512(r0)		; 1E 03 40 82 00

	remb	4(sb), 8(sb)	; CE B4 D6 04 08

	restore	[r0, r2, r7]	; 72 A1

	ret	16		; 12 10
	
	reti			; 52

	rett	16		; 42 10

	rotb	4, r5	  	; 4E 40 A1 04
	rotb	-3, 16(sp)	; 4E 40 A6 FD 10

	roundfb	f0, r0	  	; 3E 24 00
	roundld	f2, 12(sb)	; 3E A3 16 0C

	rxp	16		; 32 10

	seqb	r0		; 3C 00
	slow	10(sb)		; 3D D5 0A
	shid	tos		; 3F BA

	save	[r0, r2, r7]	; 62 85

	sbitw	r0, 1(r1)	; 4E 59 02 01

	scalbf	f3, f2		; FE 91 18

	setcfg	[i,m,f]		; 0E 8B 03

	sfsr	tos		; 3E F7 05

	skpsb	u		; 0E 0C 06

	subf	f0, f7	  	; BE D1 01
	subl	f2, 16(sb)	; BE 90 16 10

	subb	r0, r1	     	; 60 00
	subd	4(sb), 20(sb)	; A3 D6 04 14

	smr	ptb0, r0	; 1E 0F 06

	sprd	fp, r0	  	; 2F 04
	sprw	mod, 4(sb)	; AD D7 04

	subcb	32, r1	   	; 70 A0 20
	subcw	tos, -8(fp)	; 31 BE 78

	subpd	h'99, r1      	; 4E 6F A0 00 00 00 99
	subpb	-8(fp), 16(fp)	; 4E 2C C6 78 10

	svc			; E2

	tbitw	r0, 0(r1)	; 75 02 00

	truncfb	f0, r0	 	; 3E 2C 00
	truncld	f2, 8(sb)	; 3E AB 16 08

	wait			; B2

	wrval	512(r0)		; 1E 07 40 82 00

	xorb	-8(fp), -4(fp)	; 38 C6 78 7C
