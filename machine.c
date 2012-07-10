/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/* machine.c - procedures which optionally may be recoded in assembly language
 * 
 * This file contains procedures which perform the integer arithmetic 
 * operations (addition, subtraction and multiplication) which require 
 * overflow detection of the result. C does not provide an efficient 
 * mechanism for catching overflows, so this is accomplished by doing 
 * some checking of the signs of the operands and result. 
 * 
 * A more appropriate mechanism, would be to have this computation and 
 * overflow check written in assembly language, where more control of 
 * the overflow bit can be realized.
 *
 * Each of the arithmetic procedures accept three parameters. The first 
 * two are the operands and the third is a pointer to an int representating
 * a flag indicating whether there was an overflow in the operation or not.
 *
 * All of the arithmetic procedures can be compiled as is, however 
 * if there is a desire for an more efficient implementation assembly 
 * routine can be supplied which will supercede the C versions. If 
 * this is done you must define the appropriate symbolic name immediately 
 * below to avoid compiling the c prototype code. For example, once 
 * word_add is done in assembly, insert a define for WORD_ADD under 
 * an "ifdef" for the appropriate machine (sun, vax, etc) as is shown 
 * for the IBM_PC case below.
 * 
 * MOVE_MEM is included here only because some run-time libraries might
 * contain a routine which does the equivalent job and therefore could
 * be substituted for the C code given here for it.
 */

#include "config.h"
#include "machineprots.h"

/*
 * macros used to check for overflow condition on integer addition and 
 * subtraction. We assume twos complement arithmetic with wraparound on 
 * overflow 
 */

#define sign(x) (x < 0 ? 1 : 0)
#define addoverflow(op1,op2,res) (sign(op1)==sign(op2) && sign(res)!=sign(op1))
#define suboverflow(op1,op2,res) (sign(op1)!=sign(op2) && sign(res)!=sign(op1))

#ifndef WORD_ADD
int word_add(int a, int b, int *overflow)						/*;word_add*/
{
	/* add with overflow check */

	register int r;

	r = a + b;
	*overflow = addoverflow(a, b, r);
	return r;
}
#endif

#ifndef WORD_SUB
int word_sub(int a, int b, int *overflow)						/*;word_sub*/
{
	/* subtract with overflow check */

	register int r;

	r = a - b;
	*overflow = suboverflow(a, b, r);
	return r;
}
#endif

#ifndef WORD_MUL
int word_mul(int a, int b, int *overflow)						/*;word_mul*/
{
	/* multiply with overflow check */

	register int r;

	if(a) {
		r = a * b;
		*overflow = (b != r/a) || (a == -1 && b < 0 && r < 0);
	}
	else {
		*overflow = r = 0;
	}
	return r;
}
#endif

#ifndef LONG_ADD
long long_add(long a, long b, int *overflow)					/*;long_add*/
{
	/* add with overflow check */

	register long r;

	r = a + b;
	*overflow = addoverflow(a, b, r);
	return r;
}
#endif

#ifndef LONG_SUB
long long_sub(long a, long b, int *overflow)			/*;long_sub*/
{
	/* subtract with overflow check */

	register long r;

	r = a - b;
	*overflow = suboverflow(a, b, r);
	return r;
}
#endif

#ifndef LONG_MUL
long long_mul(long a, long b, int *overflow)					/*;long_mul*/
{
	/* multiply with overflow check */

	register long r;

	if(a) {
		r = a * b;
		*overflow = (b != r/a) || (a == -1 && b < 0 && r < 0);
	}
	else {
		r = 0;
		*overflow = (int)r;
	}
	return r;
}
#endif

#ifndef MOVE_MEM
void move_mem(int *src, int *dst, int n)					/*;move_mem*/
{
	/* move n words from src to dst
	 * We must watch for possible overlap.
	 */

	unsigned long usrc, udst;
	unsigned int i;

	/* View pointers as unsigned to see if possible overlap */
	if (n==0) return;
	usrc = (unsigned) src;
	udst = (unsigned) dst;
	if (usrc >= udst) { /* if no possibility of overlap */
		for (i=0;i<n;i++)
			*dst++ = *src++;
	}
	else {
		/* Here if possible overlap (usrc<udst) , set base to smaller 
		 * of pointer values and determine corresponding indices 
		 */
		if ((usrc + sizeof(int)*(n-1)) < udst ) { /* can use upwards loops */
			for (i=0; i<n; i++)
				*dst++ = *src++;
		}
		else { /* overlap, must move backwards */
			;
			n--;
			dst += n;
			src += n;
			for (i=0; i<=n; i++) {
				*dst-- = *src--;
			}
		}
	}
}
#endif
