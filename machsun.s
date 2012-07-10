LL0:
	.data
	.text
|#PROC# 04
	.globl	_word_add
_word_add:
	link	a6,#0
	addl	#-LF12,sp
	moveml	#LS12,sp@
	movl	a6@(8),d0
	moveq	#0,d6
	addl	a6@(12),d0
	jvc	ofla
	moveq	#1,d6
ofla:
	movl	d0,d7
	movl	a6@(16),a0
	movl	d6,a0@
	movl	d7,d0
	jra	LE12
	jra	LE12
LE12:
   LF12 = 8
	moveml	a6@(-LF12),#LS12
	unlk	a6
	rts
	LS12 = 0xc0
	LP12 =	8
	.data
	.text
|#PROC# 04
	.globl	_word_sub
_word_sub:
	link	a6,#0
	addl	#-LF18,sp
	moveml	#LS18,sp@
	movl	a6@(8),d0
	moveq	#0,d6
	subl	a6@(12),d0
	jvc	oflc
	moveq	#1,d6
oflc:
	movl	d0,d7
	movl	a6@(16),a0
	movl	d6,a0@
	movl	d7,d0
	jra	LE18
	jra	LE18
LE18:
   LF18 = 8
	moveml	a6@(-LF18),#LS18
	unlk	a6
	rts
	LS18 = 0xc0
	LP18 =	8
	.data
	.text
|#PROC# 04
	.globl	_long_add
_long_add:
	link	a6,#0
	addl	#-LF21,sp
	moveml	#LS21,sp@
	movl	a6@(8),d0
	moveq	#0,d6
	addl	a6@(12),d0
	jvc	ofld
	moveq	#1,d6
ofld:
	movl	d0,d7
	movl	a6@(16),a0
	movl	d6,a0@
	movl	d7,d0
	jra	LE21
	jra	LE21
LE21:
   LF21 = 8
	moveml	a6@(-LF21),#LS21
	unlk	a6
	rts
	LS21 = 0xc0
	LP21 =	8
	.data
	.text
|#PROC# 04
	.globl	_long_sub
_long_sub:
	link	a6,#0
	addl	#-LF27,sp
	moveml	#LS27,sp@
	movl	a6@(8),d0
	moveq	#0,d6
	subl	a6@(12),d0
	jvc	oflf
	moveq	#1,d6
oflf:
	movl	d0,d7
	movl	a6@(16),a0
	movl	d6,a0@
	movl	d7,d0
	jra	LE27
	jra	LE27
LE27:
   LF27 = 8
	moveml	a6@(-LF27),#LS27
	unlk	a6
	rts
	LS27 = 0xc0
	LP27 =	8
	.data
