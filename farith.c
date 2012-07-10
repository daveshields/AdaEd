/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/*
 * multi-precision multiplication, division and exponentiation
 * for fixed point computations.
 */

#include <stdlib.h>
#include "config.h"
#include "int.h"
#include "ivars.h"
#include "intbprots.h"
#include "miscprots.h"
#include "farithprots.h"

#define int_copy(u,v)   for(i=0;i<=FIX_LENGTH;i++) v[i] = u[i]
#define int_conv(v,w)   w[0]=1, w[1]=v

static void int_norm(int *);
static void int_print(int *);

#ifdef DEBUG_FARITH
void int_print();
#endif

/*
 * M U L T I P L E     P R E C I S I O N     I N T E G E R
 *
 *	   A R I T H M E T I C	   P A C K A G E
 *
 *		     Robert B. K. Dewar
 *		      June 16th, 1980
 *
 * This package of routines implements multiple precision integer
 * arithmetic using what are called the "classical algorithms" in
 * Knuth "Art of Programming", Volume 2, Section 4.3.1. The style
 * of the algorithms follows Knuth fairly closely, and section
 * 4.3.1 can be consulted for further theoretical details.
 *
 * Multiple precision integers are represented as tuples of small
 * integers in the range 0 to FIX_BAS - 1, where FIX_BAS is a power of 2
 * (actually 2 ** FIX_DIGS) which is the base used to represent the
 * long integers. Essentially the successive elements of the tuple
 * are the digits of the representation in base FIX_BAS. All integers
 * are normalized so that the first digit is non-zero, except in
 * the case of zero itself. All values are positive.
 *

 * The constants FIX_BAS and FIX_DIGS must be defined as global constants
 * in a program using these routines. It is assumed that the value
 * FIX_BAS * FIX_BAS - 1 can be represented as an integer value.

 * The following routines are provided:

 *      int_norm        integer normalization
 *	int_div		integer division
 *	int_mul		integer multiplication
 *	int_tom		conversion to multi-precision
 *	int_tol		conversion to long integer
 */


void int_tom(int *v, long n)									/*;int_tom*/
{
	/* Convert a positive integer to a multiple precision integer. */

	int	    d;

	/* Build up v in groups of FIX_BAS digits until n is depleted. */

	d = v[0] = 5;
	while(d) {
		v[d--] = n % FIX_BAS;
		n /= FIX_BAS;
	}
	int_norm(v);
}

void int_mp2(int *u, int p)    /*;int_mp2*/
{
	/* Multiplication by a power of 2. (Shift) */

	int     s;
	int     m;
	int     i,f,t,c;

	m = p % FIX_DIGS;
	s = p / FIX_DIGS;
	c = 0;

	if (m) { /* needs multiplication */
		f = 2;
		for (i=1;i<m;i++) f *= 2; /* f = 2 ** m */
		if (f * u[1] > FIX_BAS) { /* carry: needs extension */
			for (i = u[0]; i > 0; i--) {
				t = u[i] * f + c;
				u[i+1] = t % FIX_BAS;
				c = t / FIX_BAS;
			}
			u[1] = c;
			u[0] += 1;
		}
		else {
			for (i = u[0]; i > 0; i--) {
				t = u[i] * f + c;
				u[i] = t % FIX_BAS;
				c = t / FIX_BAS;
			}
			/* carry is zero now */
		}
	}
	/* now we just have to add some zeros at the end */
	if (s) { /* needs shift */
		for (i=1;i<=s;i++)
			u[u[0]+i] = 0;
		u[0] += s;
	}
}

void int_mul(int *u, int *v, int *w)								/*;int_mul*/
{
	/* Multiply unsigned integers, cf Knuth 4.3.1 Algorithm M
	 *
	 * Multiplication is similar to, but not identical with, the
	 * usual pencil and paper algorithm. The main difference is
	 * that the sum is accumulated as we go along, rather than
	 * forming all the partial sums and adding them up at the end.
	 *
	 */

	int	    i, j, k, t;

	/* Initialize result to all zeroes(actually it is only absolutely
	 * necessary to initialize the last #v digits of w to zero).
	 */

#ifdef DEBUG_FARITH
	printf("int_mul\n"); 
	int_print(u); 
	int_print(v);
#endif
	w[0] = u[0] + v[0];
	for (i = 1; i <= FIX_LENGTH; i++) w[i] = 0;

	/* Outer loop, through digits of multiplier */

	for (j = v[0]; j > 0; j--) {
		/* The inner loop, through the digits of the multiplicand, is
		 * similar to the inner loop of the addition, except that the
		 * product is added in, and the carry, k, can exceed 1.
		 */

		k = 0;
		for (i = u[0]; i > 0; i--) {
			t = u[i] * v[j] + w[i + j] + k;
			w[i + j] = t % FIX_BAS;
			k = t / FIX_BAS;
		}

		/* The final step in the inner loop is to store the final
		 * carry in the next position in the result.
		 */

		w[j] = k;
	}

	/* The result must be normalized(there could be one leading zero),
	 * and then the result sign attached to the returned value.
	 */

	int_norm(w);
#ifdef DEBUG_FARITH
	int_print(w);
#endif
}

long int_tol(int *t)											/*;int_tol*/
{
	/* Convert a multiple precision integer to a C long integer, if possible.
	 * Otherwise, return 'OVERFLOW'.
	 *
	 * First check if it overflows.
	 */

	long    x;
	int	    i;

	arith_overflow = 0;		/* reset overflow flag */

	if (t[0] > 5) {
		arith_overflow = 1;
		return 0;
	}
	if (t[0] == 5 && t[1] >= 8) { /* t >= 8 * 2**28 = 2**31 */
		arith_overflow = 1;
		return 0;
	}

	x = t[1]; /* set first part of result */
	for (i = 2; i <= t[0]; i++)
		x = FIX_BAS * x + t[i];

	return (x);
}

void int_div(int *u, int *v, int *q)							/*;int_div*/
{
	/* Obtain quotient and remainder of signed integers,
	 * cf Knuth 4.3.1 Algorithm D
	 * Result is returned as a tuple [quotient,remainder].
	 *
	 * This is by far the most difficult of the four basic operations.
	 * This is because the paper and pencil algorithm involves certain
	 * amounts of guess work which cannot be programmed directly. The
	 * approach(which is analyzed in detail in Knuth) is to reduce
	 * the guess work by computing a rather good guess at each digit
	 * of the result, and then correcting if the guess is wrong.
	 *
	 * If the divisor is zero, return om.
	 */

	int	    i, j, k, du, p, c, d;
	int	    rr, n, m, qe;

	/* A special case, if u is shorter than v, the result is 0 */

	if (u[0] < v[0]) {
		int_conv(0,q);
		return;
	}

	/* The case of a one digit divisor is treated specially. Not only
	 * is this more efficient, but the general algorithm assumes that
	 * the divisor contains at least two digits.
	 */

	if (v[0] == 1) {
		q[0] = u[0];

		/* Basically this case is straight-forward. Since we can represent
		 * numbers up to FIX_BAS * FIX_BAS - 1, we can do the steps of the
		 * division exactly without any need for guess work. The division is
		 *  then * done left to right (essentially it is the short division
		 * case).
		 */
		rr = 0;
		for (j = 1; j <= u[0]; j++) {
			du = rr * FIX_BAS + u[j];
			q[j] = du / v[1];
			rr = du % v[1];
		}
	}
	/* Here is where we must do the full long division algorithm */

	else {
		n = v[0];
		m = u[0] - v[0];
		u[0] += 1; /* extend u */
		for(i=u[0];i>1;i--) u[i] = u[i-1];
		u[1] = 0;
		q[0] = m+1;

		/* The first step is to multiply both the divisor and dividend
		 * by a scale factor. Obviously such scaling does not affect
		 * the quotient. The purpose of this scaling is to ensure that
		 * the first digit of the divisor is at least FIX_BAS / 2. This
		 * condition is required for proper operation of the quotient
		 * estimation algorithm used in the division loop. Note that
		 * we added an extra digit at the front of the dividend above.
		 */

		d = FIX_BAS /(v[1] + 1);

		c = 0;
		for (j = u[0]; j > 0; j--) {
			p = u[j] * d + c;
			u[j] = p % FIX_BAS;
			c = p / FIX_BAS;
		}

		c = 0;
		for (j = v[0]; j > 0; j--) {
			p = v[j] * d + c;
			v[j] = p % FIX_BAS;
			c = p / FIX_BAS;
		}

		/* This is the major loop, corresponding to long division steps */

		for (j = 1; j <=(m + 1); j++) {
			/* Guess the next quotient digit by doing a division based on the
			 * leading digits. This estimate is never low and at most 2 high.
			 */
			qe =(u[j] != v[1])
			  ? ((u[j] * FIX_BAS + u[j + 1]) / v[1]) :(FIX_BAS - 1);

			/* The following loop refines this guess so that it is almost always
			 * correct and is at worst one too high(see Knuth for proofs).
			 */

			while((v[2] * qe) >
			  ((u[j] * FIX_BAS + u[j + 1] - qe * v[1]) * FIX_BAS + u[j + 2])) {
				qe -= 1;
			}

			/* Now(for the moment accepting the estimate as correct), we
			 * subtract the appropriate multiple of the divisor. This is
			 * similar to the inner loop of the multiplication routine.
			 */
			c = 0;
			for (k = n; k > 0; k--) {
				du = u[j + k] - qe * v[k] + c;
				u[j + k] = du % FIX_BAS;
				c = du / FIX_BAS;
				if (u[j + k] < 0) {
					u[j + k] += FIX_BAS;
					c -= 1;
				}
			}
			u[j] += c;

			/* If the estimate was one off, then u(j) went negative when the
			 * final carry was added above. In this case, we add back the
			 * divisor once, and adjust the quotient digit.
			 */

			if (u[j] < 0) {
				qe -= 1;

				c = 0;
				for (k = n; k > 0; k--) {
					u[j + k] += v[k] + c;
					if (u[j + k] >= FIX_BAS) {
						u[j + k] -= FIX_BAS;
						c = 1;
					}
					else
						c = 0;
				}

				u[j] += c;
			}

			/* Store the next quotient digit */

			q[j] = qe;
		}
	}

	/* All done, except for normalizing the quotient
	 * to remove leading zeroes and supplying the
	 * proper result sign to the returned values.
	 */

	int_norm(q);
}

static void int_norm(int *u)		/*;int__norm*/
{
	/* Remove leading zeroes from calculated value
	 *
	 * The representation used in this package requires that all integer
	 * values be normalized, i.e. the first digit of any stored value
	 * must be non-zero except for the special case of zero itself. The
	 * normalize routine is called to ensure this condition is met.
	 *
	 */

	int	    i, j;

	if (u[0] == 1 || u[1] != 0)
		return;

	for (i = 2; i <= u[0]; i++) {
		if (u[i]) {
			u[0] = u[0] -(i - 1);
			for (j = 1; j <= u[0]; j++)
				u[j] = u[i++];
			return;
		}
	}
	/*  Return zero if all components zero */
	u[0] = 1;
	return;
}

/* debugging and test procedures */
static void int_print(int *u)									/*;int_print*/
{
	/* Dump multi-precision integer to standard output */

	int	    i,n;

	n = u[0];
	if (n <= 0)
		chaos("ill-formatted arbitrary precision integer - lengt <=0");
	printf("integer: %d components\n", u[0]);
	printf("%3d %*d\n", 1, DIGS+1, u[1]); /* allow for possible sign */
	for (i = 2; i <= u[0]; i++)
		printf("%3d  %0*d\n", i, DIGS, u[i]);
}

#ifdef DEBUG_FARITH
#define NUMBER 20
#define LENGTH 10
main ()
{
	int pow5[100];
	int i,j,c,v;
	pow5[0] = 1;
	pow5[1] = 1;
	printf("static int pow5[%d] [%d] = {\n",NUMBER+1,LENGTH+1);
	for (i=0;i<NUMBER;i++) {
		printf("    {");
		for (j=0;j<=pow5[0];j++) {
			printf(" %3d,",pow5[j]);
		}
		for (;j<LENGTH;j++) {
			printf("   0,");
		}
		printf("   0 },\n");
		for (c=0,j=pow5[0];j;j--) {
			v = 5 * pow5[j] + c;
			pow5[j+1] = v % FIX_BAS;
			c = v / FIX_BAS;
		}
		if (c) {
			pow5[1] = c;
			pow5[0] = pow5[0] + 1;
		}
		else {
			for (j=1;j<=pow5[0];j++) {
				pow5[j] = pow5[j+1];
			}
		}
	}
	printf("    {");
	for (j=0;j<=pow5[0];j++) {
		printf(" %3d,",pow5[j]);
	}
	for (;j<LENGTH;j++) {
		printf("   0,");
	}
	printf("   0 }\n};\n");
	if (pow5[0] >= LENGTH) {
		printf("Fatal: LENGTH is too short\n");
		exit();
	}

	printf("pow_of5(v,p)\t\t\t/*;pow_of5*/\n");
	printf("/* This procedure is generated automatically \n");
	printf(" * and therefore should not be modified.\n */\n");
	printf("int *v,p;\n{\nint i,*u;\n");
	printf("\tif (p < 0 || p > %d) {\n",NUMBER);
	printf("\t\tv[0] = v[1] = 1;\n");
	printf("\t\traise(SYSTEM_ERROR,\"power of 5 too large\");\n\t}\n");
	printf("\tu = pow5[p];\n");
	printf("\tfor (i=0;i<=u[0];i++) v[i] = u[i];\n}\n");
}

#undef LENGTH
#undef NUMBER	
#endif

static int pow5[21] [11] = {
	{   1,   1,   0,   0,   0,   0,   0,   0,   0,   0,   0 },
	{   1,   5,   0,   0,   0,   0,   0,   0,   0,   0,   0 },
	{   1,  25,   0,   0,   0,   0,   0,   0,   0,   0,   0 },
	{   1, 125,   0,   0,   0,   0,   0,   0,   0,   0,   0 },
	{   2,   4, 113,   0,   0,   0,   0,   0,   0,   0,   0 },
	{   2,  24,  53,   0,   0,   0,   0,   0,   0,   0,   0 },
	{   2, 122,   9,   0,   0,   0,   0,   0,   0,   0,   0 },
	{   3,   4,  98,  45,   0,   0,   0,   0,   0,   0,   0 },
	{   3,  23, 107,  97,   0,   0,   0,   0,   0,   0,   0 },
	{   3, 119,  26, 101,   0,   0,   0,   0,   0,   0,   0 },
	{   4,   4,  84,   5, 121,   0,   0,   0,   0,   0,   0 },
	{   4,  23,  36,  29,  93,   0,   0,   0,   0,   0,   0 },
	{   4, 116,  53,  20,  81,   0,   0,   0,   0,   0,   0 },
	{   5,   4,  70,   9, 103,  21,   0,   0,   0,   0,   0 },
	{   5,  22,  94,  49,   3, 105,   0,   0,   0,   0,   0 },
	{   5, 113,  87, 117,  19,  13,   0,   0,   0,   0,   0 },
	{   6,   4,  56,  55,  73,  95,  65,   0,   0,   0,   0 },
	{   6,  22,  26,  21, 112,  93,  69,   0,   0,   0,   0 },
	{   6, 111,   2, 109,  51,  83,  89,   0,   0,   0,   0 },
	{   7,   4,  43,  14,  35,   2,  34,  61,   0,   0,   0 },
	{   7,  21,  87,  71,  47,  11,  44,  49,   0,   0,   0 }
};

void pow_of5(int *v, int p)										/*;pow_of5*/
/* This procedure is generated automatically 
 * and therefore should not be modified.
 */
/* It has been modified for ANSI C */
{
	int i,*u;
	if (p < 0 || p > 20) {
		v[0] = v[1] = 1;
		raise(SYSTEM_ERROR,"power of 5 too large");
	}
	u = pow5[p];
	for (i=0;i<=u[0];i++) v[i] = u[i];
}
