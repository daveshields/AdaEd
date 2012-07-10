/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/* Avoid problems with library routines on PC that require pointer
 * to double instead of double (this is violation of ANSI specs).
 * for now do not compile these modules
 */

/* 
 * 11-oct-85	shields
 * fix so can handle most negative integer properly. The changes
 * are more in the nature of a patch than a solution. The proper
 * way is NOT to convert negative values to positive form before
 * processing; instead, positive values should be converted to
 * negative and conversions done on negative values. However, this
 * can be put off until later.
 *
 * 5-jun-85	shields
 * add rat_tol and int_tol which are like rat_toi and int_toi, resp.,
 * except that they return long results. These are needed to support
 * fixed-point in generator. 
 *
 * 1-aug-85	shields
 * add calls to int_free() to free intermediate values known to be dead.
 * add some copies where needed in building new rational values.
 */

#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <math.h>
#include "config.h"
#include "miscprots.h"

typedef struct Rational_s {
	int	   *rnum;		/* numerator */
	int	   *rden;		/* denominator */
}			    Rational_s;
typedef Rational_s * Rational;

#include "arithprots.h"

static int *int_frl(long);
static int *int_ptn(int);
static int *subu_int(int *, int *);
static void int_div(int *, int *, int **, int **);
static int *int__addu(int *, int *);
static int *int__norm(int *);
static int *int_new(int);
static void int_free(int *);
static void rat_free(Rational);
static double pow2(int);

/* Some of the procedures want to signal overflow by returning the
 * string 'OVERFLOW'. In C we do this by setting global arith_overflow
 * to non-zero if overflow occurs, zero otherwise
 */
int arith_overflow = 0;


int	ADA_MIN_INTEGER;
int	ADA_MAX_INTEGER;
int    *ADA_MAX_INTEGER_MP;
int    *ADA_MIN_INTEGER_MP;
long	ADA_MIN_FIXED, ADA_MAX_FIXED;
int	*ADA_MIN_FIXED_MP, *ADA_MAX_FIXED_MP;
/* _LONG form is form that can be held in C (long) */
#ifdef MAX_INTEGER_LONG
long	MIN_INTEGER_LONG;
int    *MAX_INTEGER_LONG_MP;
int    *MIN_INTEGER_LONG_MP;
#endif

#define ABS(x) ((x)<0 ? -(x) : (x))
#define SIGN(x) ((x)<0 ? -1 : (x) == 0 ? 0 : 1)


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
 * integers in the range 0 to BAS - 1, where BAS is a power of 10
 *(actually 10 ** DIGS) which is the base used to represent the
 * long integers. Essentially the successive elements of the tuple
 * are the digits of the representation in base BAS. All integers
 * are normalized so that the first digit is non-zero, except in
 * the case of zero itself. The sign is carried with the first
 * digit value, all remaining digits are always positive.
 *
 * Some examples of the representation, assuming DIGS = 4 and
 * BAS = 10000(note that the choice of BAS as a power of 10
 * is for convenience of the conversion routines, and is not
 * required for correct operation of the arithmetic algorithms).

 *     -123456789     [-1 , 2345 , 6789]
 *		0     [0]
 *	123456789     [1 , 2345, 6789]

 * The constants BAS and DIGS must be defined as global constants
 * in a program using these routines. It is assumed that the value
 * BAS * BAS - 1 can be represented as a SETL integer value.

 * The following routines are provided:

 *	int_abs		integer absolute value
 *	int_add		integer addition
 *	int_div		integer division
 *	int_eql		integer equal to
 *	int_exp		raise multiple integer to multiple integer power
 *	int_fri		convert multiple precision integer from integer
 *	int_frs		convert multiple precision integer from string
 *	int_geq		integer greater than or equal to
 *	int_gtr		integer greater than
 *	int_len		number of digits in multiple precision integer
 *	int_leq		integer less than or equal to
 *	int_lss		integer less than
 *	int_mod		integer modulus
 *	int_mul		integer multiplication
 *	int_neq		integer not equal to
 *	int_ptn		integer power of ten
 *	int_quo		integer quotient
 *	int_rem		integer remainder
 *	int_sub		integer subtraction
 *	int_toi		convert integer to C integer
 *	int_tos		integer to string
 *	int_umin	integer unary minus
 */

/* Internal procedures have names starting with int__ */

int    *int_abs(int *u)												/*;int_abs*/
{
	/* Absolute value of multiple precision integer */
	int *pu;

	pu = int_copy(u);
	if (pu[1] < 0)
		pu[1] = -pu[1];
	return pu;
}

int    *int_add(int *u, int *v)										/*;int_add*/
{
	/* Add signed integers
	 * This procedure implements the familiar algorithm of comparing
	 * the signs, if the signs are the same, then the result is the
	 * sum of the magnitudes with the sign of the operands. If the
	 * signs differ, then the number with the smaller magnitude is
	 * subtracted from the larger magnitude and the result sign is
	 * that of the operand with the larger magnitude.
	 */

	int	   *t;

	if (u[1] >= 0 && v[1] >= 0)
		return (int__addu(u, v));
	else
		if (u[1] < 0 && v[1] < 0) {
			u[1] = -u[1];
			v[1] = -v[1];
			t = int__addu(u, v);
			u[1] = -u[1];
			v[1] = -v[1];
			t[1] = -t[1];
			return t;
		}
		else {
			int	    us, vs;
			if (us = (u[1] < 0)) {
				u[1] = -u[1];
			}
			if (vs = (v[1] < 0)) {
				v[1] = -v[1];
			}
			if (int_gtr(u, v)) {
				t = subu_int(u, v);
				if (vs) v[1] = -v[1];
				if (us) {
					u[1] = -u[1];
					t[1] = -t[1];
				}
				return t;
			}
			else {
				t = subu_int(v, u);
				if (us) u[1] = -u[1];
				if (vs) {
					v[1] = -v[1];
					t[1] = -t[1];
				}
				return t;
			}
		}
}

int    int_eql(int *u, int *v)										/*;int_eql*/
{
	/* Compare multiple precision integers for equality */

	int	    n;

	if (u[0] != v[0])
		return FALSE;

	for (n = u[0]; n > 0; n--)
		if (u[n] != v[n]) return FALSE;
	return TRUE;
}

int    *int_exp(int *u, int *v)										/*;int_exp*/
{
	/* Raise a multiple precision integer to a multiple precision integer
	 * power using a modified version of the Russian Peasant algorithm
	 * for exponentiation.
	 */

	int	    sn;
	int	    u1;
	int	    i;
	int	    carry;
	int	    half;
	int	   *running, *runningp;
	int	   *result, *resultp;

	/* Compute sign of result: positive if v is even, the sign of u if
	 * v is odd.
	 */

	sn =((v[v[0]] % 2) == 1) ? SIGN(u[1]) : 1;
	u1 = u[1];
	if (u[1] < 0)
		u[1] = -u1;
	v = int_copy(v);

	/* Starting the result at 1 and running at u, loop through the binary
	 * digits of v, squaring running each time, and multiplying the result
	 * by the current value of running each time a 1-bit is found.
	 */

	result = int_con(1);
	running = int_copy(u);

	while(int_nez(v)) {
		/* If v is odd then multiply result by running. */

		if (v[v[0]] % 2 == 1) {
			resultp = result; /* save current value */
			result = int_mul(result, running);
			int_free(resultp); /* free dead value */
		}

		/* Square running. */

		runningp = running; /* save current value */
		running = int_mul(running, running);
		int_free(runningp); /* free dead value */

		/* Halve v. */

		carry = 0;
		for (i = 1; i <= v[0]; i++) {
			half = BAS * carry + v[i];
			carry = half % 2;
			v[i] = half / 2;
		}
		v = int__norm(v);
	}

	int_free(running);
	int_free(v);

	if (sn < 1)
		result[1] = -result[1];
	u[1] = u1;
	return result;
}

int    *int_fri(int i)												/*;int_fri*/
{
	/* Convert an integer to a multiple precision integer.
	 *
	 * First check the sign of i.
	 */

	int	    sn = 0;
	int	    n = i;
	int	   *t;
	int	    ti;
	int	    d;

	if (i < 0) {
		/* Special test for most negative as code below won't work
		 * for this single value (on twos-complement machines)
		 */
		if (i == ADA_MIN_INTEGER)
			return int_copy(ADA_MIN_INTEGER_MP);
		sn = -1;
		n = -i;
	}
	/* Determine length of result */
	d = 0;
	while(n) {
		d++;
		n /= BAS;
	}
	/* Now build up t in groups of BAS digits until i is depleted. */

	if (i < 0)
		i = -i;
	if (i > 0) {
		t = int_new(d);
		ti = t[0];
		while(i) {
			t[ti--] = i % BAS;
			i /= BAS;
		}
	}
	else
		t = int_con(0);

	if (sn < 0)
		t[1] = -t[1];

	return t;
}

#ifdef MAX_INTEGER_LONG
/* variant of int_fri needed for PC only */
static int *int_frl(long i)										/*;int_frl*/
{
	/* Convert a long integer to a multiple precision integer.
	 *
	 * First check the sign of i.
	 */

	int	    sn = 0;
	long    n = i;
	int	   *t;
	int	    ti;
	int	    d;

	if (i < 0) {
		/* Special test for most negative as code below won't work
		 * for this single value (on twos-complement machines)
		 */
		sn = -1;
		n = -i;
	}
	/* Determine length of result */
	d = 0;
	while(n) {
		d++;
		n /= BAS;
	}
	/* Now build up t in groups of BAS digits until i is depleted. */

	if (i < 0)
		i = -i;
	if (i > 0) {
		t = int_new(d);
		ti = t[0];
		while(i) {
			t[ti--] = i % BAS;
			i /= BAS;
		}
	}
	else
		t = int_con(0);

	if (sn < 0)
		t[1] = -t[1];

	return t;
}
#else
/* if ints and longs same size, just use int_fri */
static int    *int_frl(long i)										/*;int_frl*/
{
	return int_fri((int)i);
}
#endif

int    *int_frs(char *s)											/*;int_frs*/
{
	/* Convert a string to multiple precision integer format.  The string
	 * s is a non-empty sequence of digits, possibly preceded by a sign
	 *(+ or -).
	 *
	 * Erroneous strings are converted to OM.
	 *
	 * Since the base is a power of ten, the process of conversion
	 * amounts simply to converting groups of DIGS digits.
	 */

	char   *t;
	int	    dg;
	int	   *r, len;
	int	    ri, z, sn;
	int	    n;

	if (*s == '+') {
		sn = 0;
		s++;
	}
	else
		if (*s == '-') {
			sn = -1;
			s++;
		}
		else
			sn = 0;

	/* now determine length */
	t = s;
	dg = 0;
	while(*t) {
		if (!isdigit(*t++))
			return (int *)0;
		dg++;
	}
	if (dg == 0)
		return (int *)0;

	z = dg % DIGS;
	r = int_new((dg / DIGS) +(z ? 1 : 0));
	ri = 1;
	len = z ? z : DIGS;

	while(dg > 0) {
		n = 0;
		dg -= len;
		while(len--) {		/* convert next len digits */
			n = n * 10 +(*s++ - '0');
		}
		len = DIGS;
		r[ri++] = n;
	}
	if (sn < 0)
		r[1] = -r[1];
	return int__norm(r);
}

int    int_geq(int *u, int *v)										/*;int_geq*/
{
	/* Compare multiple precision integers: return true if u >= v, false
	 * otherwise.
	 */

	return int_eql(u, v) || int_gtr(u, v);
}

int    int_gtr(int *u, int *v)										/*;int_gtr*/
{
	/* Compare multiple precision integers: return true if u > v, false
	 * otherwise.
	 */

	int	    i, neg;

	/* signs are different                       */

	if (u[1] >= 0 && v[1] < 0) return TRUE;

	if (u[1] < 0 && v[1] >= 0) return FALSE;

	/* Now we have a real compare(signs the same) */

	neg = u[1] < 0;   /* get the sign */

	if (u[0] > v[0]) return (neg ? FALSE : TRUE);

	if (u[0] < v[0]) return (neg ? TRUE : FALSE);

	/* Now the lengths are the same  */

	if(u[1] != v[1]) return (u[1] > v[1]);

	/* Most significant digit is the same */

	for (i = 2; i <= u[0]; i++) {
		if (u[i] != v[i]) {
			return (neg ?(v[i] > u[i]) :(u[i] > v[i]));
		}
	}

	/* Numbers are the same */

	return FALSE;
}

/* Not used */
int    int_len(int *u)												/*;int_len*/
{
	/* Return the number of digits in a multiple precision integer. */

	int	    n = 1;
	int	    v;

	v = u[1];
	if (v < 0)
		v = -v;			/* take absolute value */
	while(v) {
		n++;
		v /= 10;
	}
	return n +(u[0] - 1) * DIGS;
}

/* Not used */
int int_leq(int *u, int *v)											/*;int_leq*/
{
	/* Compare multiple precision integers: return true if u <= v, false
	 * otherwise.
	 */

	return ! int_gtr(u, v);
}

int    int_lss(int *u, int *v)										/*;int_lss*/
{
	/* Compare multiple precision integers: return true if u < v, false
	 * otherwise.
	 */

	return ! int_geq(u, v);
}

int    *int_mod(int *u, int *v)										/*;int_mod*/
{
	/* Find u mod v where the mod operation is defined as:
	 *
	 *	u mod v = u - v * N	such that sign(u mod v) = sign v
	 *				      and  abs(u mod v) < abs v
	 */

	int	   *r, *s;

	r = int_rem(u, v);

	if (r == (int *)0 || r[1] == 0 ||(SIGN(u[1]) == SIGN(v[1])))
		return r;
	else {
		s = int_add(r, v);
		int_free(r);
		return s;
	}
}

int    *int_mul(int *u, int *v)		/*;int_mul*/
{
	/* Multiply signed integers, cf Knuth 4.3.1 Algorithm M
	 *
	 * Multiplication is similar to, but not identical with, the
	 * usual pencil and paper algorithm. The main difference is
	 * that the sum is accumulated as we go along, rather than
	 * forming all the partial sums and adding them up at the end.
	 *
	 * First we acquire the sign of the result, and set each number
	 * to its absolute value, thus the multiplication proper always
	 * works with non-negative integers.
	 */

	int	    sn;
	int	    u1;
	int	    v1;
	int	   *w;
	int	    i, j;
	int	    k;
	int	    t;

	sn = u[1] * v[1];
	u1 = u[1];
	v1 = v[1];
	if (u[1] < 0)
		u[1] = -u1;
	if (v[1] < 0)
		v[1] = -v1;
	/* Initialize result to all zeroes(actually it is only absolutely
	 * necessary to initialize the last #v digits of w to zero).
	 */

	w = int_new(u[0] + v[0]);

	/* Outer loop, through digits of multiplier */

	for (j = v[0]; j > 0; j--) {
		/* The inner loop, through the digits of the multiplicand, is
		 * similar to the inner loop of the addition, except that the
		 * product is added in, and the carry, k, can exceed 1.
		 */

		k = 0;
		for (i = u[0]; i > 0; i--) {
			t = u[i] * v[j] + w[i + j] + k;
			w[i + j] = t % BAS;
			k = t / BAS;
		}

		/* The final step in the inner loop is to store the final
		 * carry in the next position in the result.
		 */

		w[j] = k;
	}

	/* The result must be normalized(there could be one leading zero),
	 * and then the result sign attached to the returned value.
	 */

	w = int__norm(w);
	/* Restore arguments to entry value */
	u[1] = u1;
	v[1] = v1;
	if (sn < 0)
		w[1] = -w[1];
	return w;
}

/* Not used */
int    int_neq(int *u, int *v)										/*;int_neq*/
{
	/* Compare multiple precision integers for inequality */

	return ! int_eql(u, v);
}

static int    *int_ptn(int n)										/*;int_ptn*/
{
	/* Return the result 10**n as a multiple precision
	 * integer, where n is a non-negative simple integer.
	 */

	int	    d1;
	int	   *p;
	int	    i;

	d1 = 1;
	for (i = 1; i <= (n % DIGS); i++)
		d1 *= 10;
	p = int_new(1 +(n / DIGS));
	p[1] = d1;
	return p;
}

int    *int_quo(int *u, int *v)										/*;int_quo*/
{
	/* Obtain quotient of dividing u by v */

	int	   *q, *r;

	if (int_eqz(v))
		return (int *)0;
	int_div(u, v, &q, &r);
	if(r != (int *)0) int_free(r); /* remainder not needed, free it */
	return q;
}

int    *int_rem(int *u, int *v)										/*;int_rem*/
{
	/* Obtain remainder from dividing u by v, where u rem v is defined as:
	 *
	 *	u rem v = u -(u/v) * v	   such that sign(u rem v) = sign u
	 *					  and  abs(u rem v) < abs v
	 */

	int	   *q, *r;

	if (int_eqz(v))
		return (int *)0;
	int_div(u, v, &q, &r);
	if (q != (int *) 0) int_free(q); /* quotient not needed, free it */
	return r;
}

int    *int_sub(int *u, int *v)										/*;int_sub*/
{
	/* Subtract signed integers
	 *
	 * There is no point in duplicating the int_add code, so we
	 * simply negate the right argument and call the add routine!
	 */

	int *w;

	v[1] = -v[1];
	w = int_add(u, v);
	v[1] = -v[1];
	return w;
}

int    int_toi(int *t)												/*;int_toi*/
{
	/* Convert a multiple precision integer to a SETL integer, if possible.
	 * Otherwise, return 'OVERFLOW'.
	 *
	 * First check if it overflows.
	 */

	int	    sgn;

	int	    x;
	int	    i;

	arith_overflow = 0;		/* reset overflow flag */
	sgn = SIGN(t[1]);

	if (sgn == 0)
		return 0;
	if (sgn > 0)
		t[1] = -t[1];

	/* the value of t must be in the interval */
	if (int_lss(t, ADA_MIN_INTEGER_MP)
	  || int_gtr(t, ADA_MAX_INTEGER_MP)) {
		if (sgn > 0)
			t[1] = -t[1];	/* restore first component */
		arith_overflow = 1;
		return 0;
	}

	x = t[1]; /* set first part of result (must do here since negative) */
	for (i = 2; i <= t[0]; i++)
		x = BAS * x - t[i];

	if (sgn > 0) {
		t[1] = -t[1];		/* restore sign if negative */
		x = -x;			/* and give result proper value */
	}

	return x;
}

#ifdef MAX_INTEGER_LONG
long int_tol(int *t)											/*;int_tol*/
{
	/* Convert a multiple precision integer to a long integer, if possible.
	 * Otherwise, return 'OVERFLOW'.
	 *
	 * First check if it overflows.
	 */

	int	    sgn;
	long	    x;
	long    res;
	int	    i;

	arith_overflow = 0;		/* reset overflow flag */
	sgn = SIGN(t[1]);

	if (sgn == 0)
		return (long)0;
	if (sgn < 0) {
#ifdef MAX_INTEGER_LONG
		if (int_eql(t, MIN_INTEGER_LONG_MP)) 
			return MIN_INTEGER_LONG;
#else
		if (int_eql(t, ADA_MIN_INTEGER_MP))
			return ADA_MIN_INTEGER;
#endif

		/* since not most negative, can change sign */
		t[1] = -t[1];
	}

#ifdef MAX_INTEGER_LONG
	if (int_gtr(t, MAX_INTEGER_LONG_MP)) {
		arith_overflow = 1;
		return (long) 0;
	}
#else
	if (int_gtr(t, ADA_MAX_INTEGER_MP)) {
		arith_overflow = 1;
		return (long) 0;
	}
#endif

	x = 0;
	for (i = 1; i <= t[0]; i++)
		x = BAS * x + t[i];

	if (sgn < 0)
		t[1] = -t[1];		/* restore sign if negative */

	return (sgn * x);
}
#else
/* if longs and ints are same size, no need for separate procedure */
long int_tol(int *t)											/*;int_tol*/
{
	return (long) int_toi(t);
}
#endif

char   *int_tos(int *u)												/*;int_tos*/
{
	/* Convert a multiple precision integer to a string.
	 * The string is a non-empty digit sequence with a possible leading
	 * minus sign(but a plus sign is never generated).
	 *
	 * As in int_frs, the fact that the base is a power of ten means
	 * that the conversion is simply a matter of converting successive
	 * digits to decimal strings of length DIGS.
	 */

	char   *s, *t;
	int	    i, n;
	if (u == (int *)0) chaos("int_tos: arg null *");

	n = u[0] * DIGS;
	if (u[1] < 0)
		n += 1;			/* if need minus sign */
	s = t = emalloct((unsigned) n + 1, "int-to-s");
	sprintf(s, "%d", u[1]);
	for (i = 2; i <= u[0]; i++) {
		while(*++s);		/* move to end of converted string */
		sprintf(s, "%0*d", DIGS, u[i]);
	}

	return t;
}

int    *int_umin(int *u)										/*;int_umin*/
{
	/* Unary minus on multiple precision integer. */

	u = int_copy(u);
	u[1] = -u[1];
	return u;
}

static int    *subu_int(int *u, int *v)								/*subu_int*/
{
	/* Subtract unsigned integers, u >= v, cf Knuth 4.3.1 Algorithm S
	 *
	 *(note that we know as an entry condition that #u >= #v).
	 */

	int	    ui, vi;
	int	   *w;
	int	    k;			/* borrow */

	w = int_new(u[0]);
	ui = u[0];
	vi = v[0];

	/* The subtraction is similar to the addition, except that k now
	 * represents the borrow condition and has values 0 or -1.
	 */

	k = 0;
	while(vi) {
		w[ui] = u[ui] - v[vi--] + k;
		if (w[ui] < 0) {
			w[ui] += BAS;
			k = -1;
		}
		else
			k = 0;
		ui--;
	}

	/* Loop over remaining digits(if any) of u */

	while(ui) {
		w[ui] = u[ui] + k;
		if (w[ui] < 0) {
			w[ui] += BAS;
			k = -1;
		}
		else
			k = 0;
		ui--;
	}

	/* We cannot have a final borrow(since the entry condition
	 * required that u >= v). However, we must normalize the
	 * result since it is possible for leading zeroes to appear.
	 */

	w = int__norm(w);
	return w;
}

static void int_div(int *u, int *v, int **qa, int **ra)				/*;int_div*/
{
	/* Obtain quotient and remainder of signed integers,
	 * cf Knuth 4.3.1 Algorithm D
	 * Result is returned as a tuple [quotient, remainder].
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

	int	    i, j, k, du, v1, p, c, d;
	int	    rr, rs;
	int	   *r, *q;
	int	   *t, *tt;
	int	    ti, n, m, qe, qs;

	if (int_eqz(v)) {
		*qa = (int *)0;
		*ra = (int *)0;
		return;
	}

	/* A special case, if u is shorter than v, the result is 0 */

	if (u[0] < v[0]) {
		*qa = int_con(0);
		*ra = int_copy(u);
		return;
	}

	/* Otherwise we initialize as in multiplication by obtaining the
	 * result sign and then working with non-negative integers.
	 */

	u = int_copy(u); /* arguments used destructively, so copy */
	v = int_copy(v);
	qs = u[1] * v[1];
	rs = u[1];
	v1 = v[1];
	if (rs < 0)
		u[1] = -rs;
	if (v1 < 0)
		v[1] = -v1;

	/* The case of a one digit divisor is treated specially. Not only
	 * is this more efficient, but the general algorithm assumes that
	 * the divisor contains at least two digits.
	 */

	if (v[0] == 1) {
		q = int_new(u[0]);

		/* Basically this case is straight-forward. Since we can represent
		 * numbers up to BAS * BAS - 1, we can do the steps of the division
		 * exactly without any need for guess work. The division is then
		 * done left to right(essentially it is the short division case).
		 */
		rr = 0;
		for (j = 1; j <= u[0]; j++) {
			du = rr * BAS + u[j];
			q[j] = du / v[1];
			rr = du % v[1];
		}

		r = int_con(rr);
	}
	/* Here is where we must do the full long division algorithm */

	else {
		n = v[0];
		m = u[0] - v[0];
		q = int_new(m+1);
		t = int_new(u[0] + 1);	/* extend u */
		for (j = 1; j <= u[0]; j++)
			t[j + 1] = u[j];
		int_free(u);
		u = t;

		/* The first step is to multiply both the divisor and dividend
		 * by a scale factor. Obviously such scaling does not affect
		 * the quotient. The purpose of this scaling is to ensure that
		 * the first digit of the divisor is at least BAS / 2. This
		 * condition is required for proper operation of the quotient
		 * estimation algorithm used in the division loop. Note that
		 * we added an extra digit at the front of the dividend above.
		 */

		d = BAS /(v[1] + 1);

		c = 0;
		for (j = u[0]; j > 0; j--) {
			p = u[j] * d + c;
			u[j] = p % BAS;
			c = p / BAS;
		}

		c = 0;
		for (j = v[0]; j > 0; j--) {
			p = v[j] * d + c;
			v[j] = p % BAS;
			c = p / BAS;
		}

		/* This is the major loop, corresponding to long division steps */

		for (j = 1; j <= (m + 1); j++) {
			/* Guess the next quotient digit by doing a division based on the
			 * leading digits. This estimate is never low and at most 2 high.
			 */
			qe =(u[j] != v[1])
			    ?((u[j] * BAS + u[j + 1]) / v[1])
			    :(BAS - 1);

			/* The following loop refines this guess so that it is almost always
			 * correct and is at worst one too high(see Knuth for proofs).
			 */

			while((v[2] * qe) >
			    ((u[j] * BAS + u[j + 1] - qe * v[1]) * BAS + u[j + 2])) {
				qe -= 1;
			}

			/* Now(for the moment accepting the estimate as correct), we
			 * subtract the appropriate multiple of the divisor. This is
			 * similar to the inner loop of the multiplication routine.
			 */
			c = 0;
			for (k = n; k > 0; k--) {
				du = u[j + k] - qe * v[k] + c;
				u[j + k] = du % BAS;
				c = du / BAS;
				if (u[j + k] < 0) {
					u[j + k] += BAS;
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
					if (u[j + k] >= BAS) {
						u[j + k] -= BAS;
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

		/* Remainder is in u(m+2..m+n+1) but must be divided by d. */


		/* SETL:      r:=int_quo(u(m+2..m+n+1), [d]); */
		t = int_new(n);
		ti = 1;
		for (i = m + 2; i <= (m + n + 1); i++)
			t[ti++] = u[i];
		r = int_quo(t, tt=int_con(d));
		int_free(t);
		int_free(tt);
	}

	/* All done, except for normalizing the quotient
	 * to remove leading zeroes and supplying the
	 * proper result sign to the returned values.
	 */

	q = int__norm(q);
	if (qs < 0)
		q[1] = -q[1];
	if (rs < 0)
		r[1] = -r[1];
	*qa = q;
	*ra = r;

	int_free(u);
	int_free(v);
}

static int    *int__addu(int *u, int *v)						/*;int__addu*/
{
	/* Add unsigned integers, cf Knuth 4.3.1 Algorithm A
	 *
	 * We first do the addition just to see if final carry, so we
	 * can determine correct length of result. Then we allocate
	 * the result and perform the addition.
	 */

	int	    k = 0;		/* carry */
	int	   *w;
	int	    r;
	int	    ui, vi, wi;

	/* Adjust so u points to longer argument */

	if (v[0] > u[0]) {		/* if second longer */
		w = u;
		u = v;
		v = w;
	}
	ui = u[0];			/* length of first argument */
	vi = v[0];
	while(vi) {
		r = u[ui--] + v[vi--] + k;
		if (r >= BAS)
			k = 1;
		if (r < BAS)
			k = 0;
	}
	while(ui) {
		r = u[ui--] + k;
		if (r >= BAS)
			k = 1;
		if (r < BAS)
			k = 0;
	}
	/* if k nonzero, result needs extra component */
	w = int_new(u[0] + k);
	/* Now perform addition for real */

	/* Now we perform the addition from right to left in the familiar
	 * paper and pencil manner. The variable k is the carry from the
	 * previous column, which has either the value zero or one.
	 */

	ui = u[0];
	vi = v[0];
	wi = w[0];
	k = 0;
	while(vi) {
		w[wi] = u[ui--] + v[vi--] + k;
		if (w[wi] >= BAS) {
			w[wi] -= BAS;
			k = 1;
		}
		else
			k = 0;
		wi--;
	}
	/* Now add in remainder of longer number */
	while(ui) {
		w[wi] += u[ui--] + k;
		if (w[wi] >= BAS) {
			w[wi] -= BAS;
			k = 1;
		}
		else
			k = 0;
		wi--;
	}
	if (k)
		w[1] = 1;		/* if final carry */

	return w;
}

/* Note that int__norm does not alter its argument, but returns
 * pointer to(possibly normalized) multi-precision integer.
 */
static int    *int__norm(int *u)								/*;int__norm*/
{
	/* Remove leading zeroes from calculated value
	 *
	 * The representation used in this package requires that all integer
	 * values be normalized, i.e. the first digit of any stored value
	 * must be non-zero except for the special case of zero itself. The
	 * normalize routine is called to ensure this condition is met.
	 *
	 */

	int	    i, j, *v;

	if (u[0] == 1 || u[1] != 0)
		return (u);

	for (i = 2; i <= u[0]; i++) {
		if (u[i]) {
			v = int_new(u[0] -(i - 1));
			for (j = 1; j <= v[0]; j++) {
				v[j] = u[i++];
			}
			int_free(u);
			return (v);
		}
	}
	/*  Return zero if all components zero */
	return int_con(0);
}

/* Not used */
int	value(char *s)													/*;value*/
{
	/* Convert a numeric string to an integer. */
	return atoi(s);
}

static int    *int_new(int n)										/*;int_new*/
{
	/* Allocate new integer with n components, each initially zero */
	int	   *p;
	int	    i;

	p =(int *) ecalloct((unsigned) n + 1, sizeof(int), "int-new");
	p[0] = n;
	for (i = 1; i <= n; i++)
		p[i] = 0;
	return p;
}

static void int_free(int *n)									/*;int_free*/
{
	efreet((char *) n, "int-free");
}

int    *int_con(int i)												/*;int_con*/
{
	/* Build multi-precision integer from standard (short) integer */
	int	   *p;

	if (i<-BAS || i > BAS) chaos("int_con arg out of range ");

	p = int_new(1);
	p[1] = i;
	return p;
}

int    *int_copy(int *u)										/*;int_copy*/
{
	/* Return copy of multi-precision integer u */
	int	   *p;
	int	    n, i;

	p = int_new(n = u[0]);
	for (i = 1; i <= n; i++)
		p[i] = u[i];

	return p;
}

int	int_eqz(int *u)												/*;int_eqz*/
{
	/*  Compare multi-precision integer with zero */

	int	    i;

	for (i = 1; i <= u[0]; i++)
		if (u[i]) return (FALSE);
	return TRUE;
}

int	int_nez(int *u)													/*;int_nez*/
{
	/* Compare multi-precision integer with zero; true if not zero */
	return ! int_eqz(u);
}

/* end module ada - arith */

#ifdef DEBUG
/* debugging and test procedures */
void int_print(int *u)											/*;int_print*/
{
	/* Dump multi-precision integer to standard output */
	int	    i, n;
	n = u[0];
	if (n <= 0) {
		chaos("ill-formatted arbitrary precision integer - lengt <= 0");
	}
	printf("integer: %d components\n", u[0]);
	printf("%3d %*d\n", 1, DIGS+1, u[1]); /* allow for possible sign */
	for (i = 2; i <= u[0]; i++)
		printf("%3d  %0*d\n", i, DIGS, u[i]);
}
#endif

/*		module ada - arith   */
/*
 * All integers are stored in the multiple precision form used
 * in the package which is included as part of this program,
 * and rationals are stored as a pair [numerator, denominator],
 * with the denominator always positive, and [0] stored as [[0], n].
 * A rational plus or minus infinity may be represnted as
 * [n, [0]] or [-n, [0]] respectively. A rational of the form [[0], [0]]
 * will have an undefined effect if used in an operation.
 */

/* Macros for access to rational numbers: */

#define num(x) x->rnum
#define den(x) x->rden

Rational RAT_TWO;
Rational ADA_MAX_FLOAT;

/*
 * R A T I O N A L     A R I T H M E T I C     P A C K A G E

 *		     Robert B. K. Dewar
 *		      June 18th, 1980

 * This package contains a set of routines for performing
 * rational multiple precision arithmetic.

 *
 * A rational number is represented as a struct with two components, rnum
 * and rden, where num is the numerator, which may be negative, and den is
 * the denominator, which is non-zero and positive. Usually rational
 * numbers are reduced to lowest terms(see procedure rat_red), but none of
 * the routines depend on this assumption. The numerator and denominator
 * are represented as multiple precision integers, using the standard
 * formats for the multiple precision integer package, which must be
 * included as part of the program.
 * The macros num() and den() are used often, for comparison with the
 * original SETL code.
 *
 * The following routines are provided in the package

 *	rat_abs		rational absolute value
 *	rat_add		rational addition
 *	rat_div		rational division
 *	rat_eql		rational equal to
 *	rat_exp		raise rational to multiple precision integer power
 *	rat_fri		convert multiple precision integers to rational
 *	rat_frr		convert real to rational
 *	rat_frs		convert rational from string
 *	rat_geq		rational greater than or equal to
 *	rat_gtr		rational greater than
 *	rat_leq		rational less than or equal to
 *	rat_lss		rational less than
 *	rat_mul		rational multiplication
 *	rat_neq		rational not equal to
 *	rat_rec		rational reciprocal
 *	rat_red		reduce rational to lowest terms
 *	rat_str		convert integral fraction to string fraction
 *	rat_sub		rational subtraction
 *	rat_tor		convert rational to real
 *	rat_toi		convert rational to integer(rounds)
 *	rat_tos		convert rational to string
 *	rat_tup		convert string fraction to integral fraction
 *	rat_umin	rational unary minus
 */

/*
 * The following procedures are introduced in the translation to C:
 *	rat_new		allocate new rational, set components
 *	rat_free	free rational(deallocate space, including
 *			  space used by components
 */

void rat_init()													/*;rat_init*/
{
	/* Initialize rational and multi-precision packages */

	extern  Rational RAT_TWO;
	extern  Rational ADA_MAX_FLOAT;

	RAT_TWO = rat_new(int_con(2), int_con(1));

	/*    ADA_MAX_FLOAT	=
	 *	[[79, 228, 162, 514, 264, 337, 593, 543, 950, 336], [1]],
	 *				$ rational form of MAX_FLOAT
	 *    ADA_MAX_INTEGER_MP= [1, 073, 741, 823],
	 *				$ long form of ADA_MAX_INTEGER
	 */
	/* Some C compilers do not like to see the most negative integer as
	 * a constant, so we initialize ADA_MIN_INTEGER here by assingment
	 * (assuming they can subtract properly!)
	 */
	ADA_MAX_INTEGER = MAX_INTEGER; /* to be sure */
	ADA_MIN_INTEGER = -ADA_MAX_INTEGER;
	ADA_MIN_INTEGER--;
	ADA_MAX_INTEGER_MP = int_fri(ADA_MAX_INTEGER);
	ADA_MIN_INTEGER_MP = int_sub(int_umin(ADA_MAX_INTEGER_MP), int_fri(1));
#ifdef MAX_INTEGER_LONG
	MIN_INTEGER_LONG = - MAX_INTEGER_LONG;
	MIN_INTEGER_LONG--;
	MAX_INTEGER_LONG_MP = int_frs(MAX_INTEGER_LONG_STRING);
	MIN_INTEGER_LONG_MP = int_sub(int_umin(MAX_INTEGER_LONG_MP),
	  int_fri(1));
	ADA_MIN_FIXED = MIN_INTEGER_LONG;
	ADA_MAX_FIXED = MAX_INTEGER_LONG;
	MAX_INTEGER_LONG_MP = int_frs(MAX_INTEGER_LONG_STRING);
	MIN_INTEGER_LONG_MP = int_sub(int_umin(MAX_INTEGER_LONG_MP),
	  int_fri(1));
	ADA_MIN_FIXED_MP = MIN_INTEGER_LONG_MP;
	ADA_MAX_FIXED_MP = MAX_INTEGER_LONG_MP;
#endif
#ifndef MAX_INTEGER_LONG
	ADA_MIN_FIXED = ADA_MIN_INTEGER;
	ADA_MAX_FIXED = ADA_MAX_INTEGER;
	ADA_MIN_FIXED_MP = ADA_MIN_INTEGER_MP;
	ADA_MAX_FIXED_MP = ADA_MAX_INTEGER_MP;
#endif
	ADA_MAX_FLOAT = rat_new(
	  int_frs("79228162514264337593543950336"),
	  int_con(1));
}

Rational rat_new(int *u, int *v)								/*;rat_new*/
{
	Rational r;

	r =(Rational) emalloct(sizeof(Rational_s), "rat-new");
	r -> rnum = u;
	r -> rden = v;
	return r;
}

static void rat_free(Rational r)								/*;rat_free*/
{
	if (r->rnum != (int *)0) efreet((char *) r->rnum, "rat-free-num");
	if (r->rden != (int *)0) efreet((char *) r->rden, "rat-free-den");
	efreet((char *) r, "rat-free-rat");
}

#ifdef DEBUG
void rat_print(Rational r)									/*;rat_print*/
{
	printf("rational \n");
	int_print(r -> rnum);
	int_print(r -> rden);
}
#endif

Rational rat_abs(Rational u)										/*;rat_abs*/
{
	/* Absolute value of rational number */

	return rat_new(int_abs(num(u)), int_copy(den(u)));
}

Rational rat_add(Rational u, Rational v)							/*;rat_add*/
{
	/* Add rational numbers
	 *
	 *   un	    vn	      un * vd  +  vn * ud
	 *   --	 +  --	 =    -------------------
	 *   ud	    vd		    ud * vd
	 */

	int	   *rn, *rm, *tn, *tm;

	tn = int_mul(num(u), den(v));
	tm = int_mul(num(v), den(u));
	rn = int_add(tn, tm);
	rm = int_mul(den(u), den(v));
	int_free(tn); 
	int_free(tm); /* free temporaries */

	return rat_new(rn, rm);
}


Rational rat_div(Rational u, Rational v)							/*;rat_div*/
{
	/*
	 * Divide rational numbers
	 *
	 *    un
	 *    --
	 *    ud
	 *		  un * vd
	 *   ----    =	  -------
	 *		  vn * ud
	 *    vn
	 *    --
	 *    vd
	 *
	 * Test for division by zero
	 */

	int	   *rn, *rm;

	/* Return NULL instead of OM */
	if (int_eqz(num(v))) return ((Rational)0);

	/* Divisor is non-zero */

	else {
		rn = int_mul(num(u), den(v));
		rm = int_mul(num(v), den(u));
		/*   if rm < 0 then
		 *	rn := -rn;
		 *	rm := abs rm;
		 *   end if;
		 */
		if (rm[1] < 0) {
			rn[1] = -rn[1];
			rm[1] = -rm[1];
		}

		return rat_new(rn, rm);
	}
}

int rat_eql(Rational u, Rational v)									/*;rat_eql*/
{
	/* Test rational numbers for equality */
	int	*rm, *rn, res;

	rn = int_mul(num(u), den(v));
	rm = int_mul(num(v), den(u));
	res = int_eql(rn, rm);
	int_free(rn); 
	int_free(rm); /* free temporaries */
	return res;
}

Rational rat_exp(Rational u, int *ea)		/*;rat_exp*/
{
	/* Raise rational number to multiple precision integer power
	 *
	 *  If e >= 0:		   If e < 0:
	 *
	 *    un	un ** e	     un		     1		 ud **(-e)
	 *    -- ** e = -------	     -- ** e = --------------- = ----------
	 *    ud	ud ** e	     ud	      (un/ud) **(-e)	 un **(-e)
	 */

	int	   *e;

	if (int_eqz(num(u)))
		return int_eqz(ea) ? rat_new(int_con(1), int_con(1))
		  : rat_new(int_con(0), int_con(1));

	e = int_copy(ea);		/* preserve value semantics */

	if (e[1] < 0) {
		u = rat_rec(u);
		e[1] = -e[1];
	}

	return rat_new(int_exp(num(u), e), int_exp(den(u), e));
}

Rational rat_fri(int *u, int *v)		/*;rat_fri*/
{
	/* Convert multiple precision integers to a rational number. */

	return rat_new(int_copy(u), int_copy(v));
}

Rational rat_frr(double u)											/*;rat_frr*/
{
	/* Convert a SETL real to a rational number.
	 *
	 * converts a floating number u to a pair of integers [p, y] such that
	 * u = 2.0**p * float y
	 * Here y satisfies 2**(N-1) <= abs y < 2 ** N
	 * where N is the number of mantissa bits.
	 * This essentially separates the fraction and the exponent.
	 */
	/* The present C version is a straightforward translation of the SETL
	 * code. Still unanswered is the question of whether real values will
	 * be represented in C using doubles or floats; for now we assume reals
	 * as floats. A more efficient version using library function 'frexp'
	 * may be possible.
	 */

	int	    sgn;
	float   ub, lb;
	int	    p, y;
	if (u == 0.0)
		return rat_new(int_con(0), int_con(1));

	if (u < 0) {
		u = -u;
		sgn = -1;
	}
	else {
		sgn = 1;
	}
	ub = pow2(ADA_MANTISSA_SIZE);
	lb = pow2(ADA_MANTISSA_SIZE - 1);

	p =(int)(log((double) u) / log((double) 2.0)) - ADA_MANTISSA_SIZE;
	/* estimate the exponent */
	u = u * pow2(-p);
	/* and adjust number */
	while(u >= ub) {
		u /= 2.0;		/* scale down */
		p += 1;
	}
	while(u < lb) {
		u *= 2.0;		/* scale up; */
		p -= 1;
	}
	y = sgn *(int) u;
	return rat_mul(rat_exp(RAT_TWO, int_fri(p)),
	  rat_new(int_fri(y), int_con(1)));
}

/* Not used */
Rational rat_frs(char *s)											/*;rat_frs*/
{
	/* Convert a string representing a decimal fraction to the corresponding
	 * rational number.  The string consists of a digit string, optionally
	 * containing a decimal point and preceded by an optional sign.	 If an
	 * erroneous string is passed as an argument, then OM is returned.
	 *
	 * First step is to find number of digits after decimal point
	 */

	int	    dp, n, frac;
	int	   *i;
	char   *t;

	n = strlen(s);

	t = strrchr(s, '.');
	frac =(t == (char *)0) ? 0 :(t - s + 1);
	/* find position of decimal point */
	dp = 0;
	if (frac != 0) {
		dp = n - frac;
		t = emalloct((unsigned) n, "rat-frs");
		*t = '\0';		/* mark end of(initially) null string */
		if (frac > 1)
			strncat(t, s, frac - 1);
		strncat(t, s + frac, (n - frac));
	}
	else
		t = s;
	/* Then number is converted as integer, and result is obtained
	 * by supplying the appropriate power of ten as the denominator.
	 */

	i = int_frs(t);

#ifdef XDEFER
	/* defer this while putting salloc in place DS (2-22-86) */
	if (frac)
		efreet(t, "rat-frs");		/* return t if allocated here */
#endif

	if (i == (int *)0)
		return (Rational)0;
	else
		return rat_red(i, int_ptn(dp));
}

int rat_geq(Rational u, Rational v)									/*;rat_geq*/
{
	/* Compare rational numbers: return true if u >= v, false otherwise. */

	return ! rat_lss(u, v);
}

int rat_gtr(Rational u, Rational v)									/*;rat_gtr*/
{
	/* Compare rational numbers: return true if u > v, false otherwise. */

	return (rat_eql(u, v) ? 0 : rat_lss(v, u));
}

int rat_leq(Rational u, Rational v)									/*;rat_leq*/
{
	/* Compare rational numbers: return true if u <= v, false otherwise. */

	return (rat_eql(u, v) ? 1 : rat_lss(u, v));
}

int rat_lss(Rational u, Rational v)			/*;rat_lss*/
{
	/* Compare rational numbers: return true if u < v, false otherwise.
	 *
	 *   un	    vn
	 *   -- <  --	iff   un * vd  <  vn * ud
	 *   ud	    vd
	 */
	int	*rn, *rd, res;
	rn = int_mul(num(u), den(v));
	rd = int_mul(num(v), den(u));
	res = int_lss(rn, rd);
	int_free(rn); 
	int_free(rd);
	return res;
}

Rational rat_mul(Rational u, Rational v)							/*;rat_mul*/
{
	/*
	 * Multiply rational numbers
	 *
	 *   un	    vn	      un * vn
	 *   --	 *  --	 =    -------
	 *   ud	    vd	      ud * vd
	 */

	int	   *rn, *rm;

	rn = int_mul(num(u), num(v));
	rm = int_mul(den(u), den(v));

	return rat_red(rn, rm);
}

int rat_neq(Rational u, Rational v)									/*;rat_neq*/
{
	/* Test rational numbers for inequality */

	return ! rat_eql(u, v);
}

Rational rat_rec(Rational u)										/*;rat_rec*/
{
	/* Find reciprocal of rational number(number should not be zero). */

	int	   *un, *dn;

	un = int_copy(den(u));
	dn = int_copy(num(u));
	if (dn[1] < 0) {
		un[1] = -un[1];
		dn[1] = -dn[1];
	}
	return rat_new(un, dn);
}

Rational rat_red(int *un, int *ud)									/*;rat_red*/
{
	/* Form rational reduced to lowest terms
	 *
	 * This procedure is given as arguments the numerator and denominator
	 * of a rational value(as multiple precision integers). It returns
	 * the rational formed by reducing these values to lowest terms.
	 *
	 * First a special case: zero is reduced to [[0], [1]] .
	 */

	int	   *i, *j, *t, *gcd, usign, dsign, rsign;

	if (int_eqz(un)) {
		return rat_new(int_con(0), int_con(1));

		/* Another special case: plus or minus infinity is reduced to [[1], [0]]
		 * or [[-1], [0]] .
		 */
	}
	else {
		if (int_eqz(ud)) {
			return rat_new(int_con((un[1] < 0 ? -1 :((un)[1] > 0 ? 1 : 0))),
			  int_con(0));
		}
		/* Else we must compute GCD, using Euclid's algorithm. */

		else {
			usign = SIGN(un[1]); 
			dsign = SIGN(ud[1]);
			rsign = usign == dsign ? 1 : -1;
			i = int_copy(un);
			i[1] = i[1] >= 0 ? i[1] : -i[1];
			j = int_copy(ud);
			j[1] = j[1] >= 0 ? j[1] : -j[1];
			if (int_gtr(j, i)) {
				t = i;
				i = j;
				j = t;
			}
			/* Steps of Euclid's algorithm, at each step, i is greater than
			 * or equal to j, i is replaced by j and j is replaced by the
			 * remainder of dividing i by j. The algorithm terminates when
			 * j is zero, with i being the greatest common divisor.
			 */

			while(int_nez(j)) {
				t = j;
				j = int_rem(i, j);
				i = t;
				/* [i, j] := [j, int_rem(i, j)]; */
			}

			gcd = i;

			/* Now reduce the original to lowest terms using the computed GCD */

			i = int_quo(un, gcd);
			j = int_quo(ud, gcd);
			/* adjust signs if needed */
			if (i[1] < 0) i[1] = -i[1];
			if (j[1] < 0) j[1] = -j[1];
			if (rsign < 0) i[1] = -i[1];
			return  rat_new(i, j);

		}
	}
}

#ifdef TBSN
char **rat_str(int **q)												/*;rat_str*/
{
	/* Convert tuple of multiple precision integers to tuple of
	 * strings.
	 * We interpret the argument q as a pointer to an array of pointers
	 * to multi-precision integers.
	 */

	char *emalloct();
	char *p;

	p = ecalloct(2, sizeof(char *), "rat-str");
	p[0] = int_tos(*q[0]);
	p[1] = int_tos(*q[1]);
	return &p;
}
#endif

Rational rat_sub(Rational u, Rational v)							/*;rat_sub*/
{
	/* Subtract rational numbers
	 *
	 *   un	    vn	      un * vd  -  vn * ud
	 *   --	 -  --	 =    -------------------
	 *   ud	    vd		    ud * vd
	 */

	int	   *rn, *rm, *tn, *tm;

	tn = int_mul(num(u), den(v));
	tm = int_mul(num(v), den(u));
	rn = int_sub(tn, tm);
	int_free(tn); 
	int_free(tm);
	rm = int_mul(den(u), den(v));
	return rat_new(rn, rm);
}

double rat_tor (Rational u, int n)									/*;rat_tor*/
{
	/* TBSL: need to review and test this code		ds 11 sep 84 */
	double	real1;
	int	sgn, numpow, denpow;
	int	*nu, *du;
	int	*ub, *lb, p, *lbnd;
	int	*iquo;
	long	ntmp;
	double	log_bas, rpow, res;
	/* Convert a multiple precision real to a SETL real, if possible.
	 * Make copy and work with positives
	 */
	u = rat_red(num(u), den(u));
	arith_overflow = 0;
	nu = num(u);
	sgn   = SIGN(nu[1]);
	nu[1] = ABS(nu[1]);

	/* Check for 0 */

	if (sgn == 0 ) { 
		rat_free(u);
		return 0.0;
	}

	/* Check for overflow */

	if (rat_gtr(u, ADA_MAX_FLOAT)) {
		arith_overflow = 1;
		return 0.0;
	}

	/* To find an accurate floating representation of a rational number,
	 * we normalize it so that
	 *
	 *		2 ** (N - 1) <= (num/den) < 2 ** N
	 *
	 * where N is the size of the mantissa.
	 * We can then perform a long division, and know that the mantissa is
	 * accurate to 2 ** (-N) i.e. to the last bit.
	 */
	real1 = BAS;
	log_bas = log(real1) / log(2.0);
	ub = int_frl((long) pow2(ADA_MANTISSA_SIZE));
	lb = int_frl((long) pow2(ADA_MANTISSA_SIZE - 1));

	nu = num(u);
	du = den(u);
	numpow = (int)((double)((nu[0]-1)) * log_bas + log((double)nu[1])/log(2.0));
	denpow = (int)((double)((du[0]-1)) * log_bas + log((double)du[1])/log(2.0));

	p = numpow - denpow - ADA_MANTISSA_SIZE;
	if (p < 0 ) {				/* -p > 0 */
		nu = int_mul(nu, int_exp(int_fri(2), int_fri(-p)));
	}
	else {					/*  p >= 0  */
		du = int_mul(du, int_exp(int_fri(2), int_fri(p)));
	}

	while (int_geq(nu, int_mul(ub, du))) {
		du = int_add(du, du);
		p++;
	}
	lbnd = int_mul(lb, du);
	while (int_lss(nu, lbnd)) {
		nu = int_add(nu, nu);
		p--;
	}
	iquo = int_quo(nu, du);
	ntmp = int_tol(iquo);
	real1 = sgn * ntmp;
	rpow = pow2(p);
	res = real1 * rpow;
	return res;
}

int	rat_toi(Rational u)												/*;rat_toi*/
{
	/* Convert the rational number u to a SETL integer.  The number
	 * u is rounded by adding rational 1/2 or -1/2.	 The int_quo
	 * procedure is used to obtain the result of dividing the
	 * numerator by the denominator.  The resuling extended integer is
	 * then converted to a SETL integer using int_toi.
	 */

	int	    t, s;
	Rational r;

	t = num(u)[1];
	s = t == 0 ? 0 : t > 0 ? 1 : -1;/* get sign of u */
	/* s := sign num(u)(1);		$ get sign of u */
	/*	add or subtract 1/2(or 0) */
	r = rat_add(u, rat_new(int_con(s), int_con(2)));
	return int_toi(int_quo(num(r), den(r)));
	/* get quotient and convert it */
}

long rat_tol(Rational u)										/*;rat_tol*/
{
	/* Convert the rational number u to a (long)integer.  The number
	 * u is rounded by adding rational 1/2 or -1/2.	 The int_quo
	 * procedure is used to obtain the result of dividing the
	 * numerator by the denominator.  The resuling extended integer is
	 * then converted to a SETL integer using int_toi.
	 */

	int	    t, s;
	Rational r;

	t = num(u)[1];
	s = t == 0 ? 0 : t > 0 ? 1 : -1;/* get sign of u */
	/* s := sign num(u)(1);		$ get sign of u */
	/*	add or subtract 1/2(or 0) */
	r = rat_add(u, rat_new(int_con(s), int_con(2)));
	return int_tol(int_quo(num(r), den(r)));
	/* get quotient and convert it */
}

#ifdef TBSN
	proc rat_tos (u, n);		/*;rat_tos*/
	
	/*
	 * Convert a rational number u to a decimal
	 * string with n places after the decimal point. The result
	 * is correctly rounded and always has the specified number
	 * of digits after the decimal place (even if they are zero)
	 *
	 * First acquire the sign (and then work with positive numbers)
	 */
	
	int *q, *r;
	
	sn :
	= '';
	if num(u)(1) < 0 then
	num(u)(1) :
	= abs num(u)(1);
	sn	      :
	= '-';
	end if;
	
	/*
	 * Form result by multiplying by power of ten corresponding
	 * to number of decimal places and then doing division.
	 */
	
	un :
	= int_mul (num(u), int_ptn (n));
	ud :
	= den(u);
	int_div(un, ud, &q, &r);
	if int_gtr (int_mul (r, [2]), ud) then
	q:
	=int_add(q, [1]);
	end if;
	
	/*
	 * Return result by converting this integer to a string and
	 * then supplying the decimal point at the appropriate position.
	 */
	
	q :
	= int_tos (q);
	if #q <= n then
	q :
	= (n + 1 - #q) * '0' + q;
	end if;
	
	return sn + q(1..#q-n) + '.' + q(#q-n+1..);
	
	end proc rat_tos;
#endif

#ifdef TBSN
Rational *rat_tup(char **q)											/*;rat_tup*/
{
	/* Convert tuple of strings to tuple of multiple precision integers.
	 * We interpret tuple of strings as pointer to array of pointers to
	 * strings.
	 */

	char *ecalloct();
	Rational *p;

	p = ecalloct(2, sizeof(Rational ), "rat-tup");

	p[0] = int_frs(*q[0]);
	p[1] = int_frs(*q[1]);
	return &p;
}
#endif

Rational rat_umin(Rational u)									/*;rat_umin*/
{
	/* Rational unary minus */

	return rat_new(int_umin(num(u)), int_copy(den(u)));
}

static double pow2(int p)							                 /*;pow2*/
{
	double running, result;

    result = 1.0;

    if (p < 0) {
		running = 0.5;
	    p = -p;
	}
	else {
		running = 2.0;
	}

	while(p != 0) {

		/* If p is odd then multiply result by running. */

		if (p % 2 == 1)
			result = result * running;

		/* Square running. */

		running = running * running;

	    p /= 2;
	}

	return result;
}
