	cpu	68020
	page	0

	irp	op,b,w,l,q,s,d,x,p
	dc.op	[3]25
	dc.op	"Hello World"
	ds.op	9
	endm

	irp	op,s,d,x,p
	dc.op	1.5
	dc.op	constpi*1000
        dc.op	constpi/1000
        dc.op   -constpi
	endm

	padding	off

	dc.b	0
	dc.b	255
	dc.b	-128
	dc.b	'A'
	expect	1320
	dc.b	'AB'
	endexpect
	expect	1320
	dc.b	'ABC'
	endexpect
	expect	1320
	dc.b	'ABCD'
	endexpect
	dc.b	"A"
	dc.b	"AB"
	dc.b	"ABC"
	dc.b	"ABCD"

	dc.w	0
	dc.w	65535
	dc.w	-32768
	dc.w	'A'
	dc.w	'AB'
	expect	1320
	dc.w	'ABC'
	endexpect
	expect	1320
	dc.w	'ABCD'
	endexpect
	dc.w	"A"
	dc.w	"AB"
	dc.w	"ABC"
	dc.w	"ABCD"

	dc.l	0
	dc.l	4294967295
	dc.l	-2147483648
	dc.l	'A'
	dc.l	'AB'
	dc.l	'ABC'
	dc.l	'ABCD'
	dc.l	"A"
	dc.l	"AB"
	dc.l	"ABC"
	dc.l	"ABCD"

	dc.q	0
	dc.q	2147483647
	dc.q	-2147483648
	dc.q	'A'
	dc.q	'AB'
	dc.q	'ABC'
	dc.q	'ABCD'
	dc.q	"A"
	dc.q	"AB"
	dc.q	"ABC"
	dc.q	"ABCD"

	dc.s	0
	dc.s	2147483647
	dc.s	-2147483648
	dc.s	'A'
	dc.s	'AB'
	dc.s	'ABC'
	dc.s	'ABCD'
	dc.s	"A"
	dc.s	"AB"
	dc.s	"ABC"
	dc.s	"ABCD"

	dc.d	0
	dc.d	2147483647
	dc.d	-2147483648
	dc.d	'A'
	dc.d	'AB'
	dc.d	'ABC'
	dc.d	'ABCD'
	dc.d	"A"
	dc.d	"AB"
	dc.d	"ABC"
	dc.d	"ABCD"

	dc.x	0
	dc.x	2147483647
	dc.x	-2147483648
	dc.x	'A'
	dc.x	'AB'
	dc.x	'ABC'
	dc.x	'ABCD'
	dc.x	"A"
	dc.x	"AB"
	dc.x	"ABC"
	dc.x	"ABCD"

	dc.p	0
	dc.p	2147483647
	dc.p	-2147483648
	dc.p	'A'
	dc.p	'AB'
	dc.p	'ABC'
	dc.p	'ABCD'
	dc.p	"A"
	dc.p	"AB"
	dc.p	"ABC"
	dc.p	"ABCD"
