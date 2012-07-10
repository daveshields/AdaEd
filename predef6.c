/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/*    +---------------------------------------------------+
      |                                                   |
      |          I N T E R P     P R E D E F S            |
      |            Part 6: Editing Procedures             |
      |                  (C Version)                      |
      |                                                   |
      |   Adapted From Low Level SETL version written by  |
      |                                                   |
      |                  Monte Zweben                     |
      |               Philippe Kruchten                   |
      |               Jean-Pierre Rosen                   |
      |                                                   |
      |    Original High Level SETL version written by    |
      |                                                   |
      |                   Clint Goss                      |
      |               Tracey M. Siesser                   |
      |               Bernard D. Banner                   |
      |               Stephen C. Bryant                   |
      |                  Gerry Fisher                     |
      |                                                   |
      |              C version written by                 |
      |                                                   |
      |               Robert B. K. Dewar                  |
      |                                                   |
      +---------------------------------------------------+
*/

/* This module contains routines for the implementation of some of
 * the predefined Ada packages and routines, namely SEQUENTIAL_IO,
 * DIRECT_IO, TEXT_IO, and CALENDAR. Part 6 contains the routines
 * for generating string images of internal objects.
*/

#include <math.h>
#include "ipredef.h"

static double image_real_digits (double, int, char *);
static void image_real (double, int, int, int);

/* IMAGE_REAL_DIGITS */

/* Procedure to output number of digits specified by multiplying dval, which
 * is non-negative and less than 1.0, successively by 10. Output digits are
 * placed in string s. The value returned is the reduced value of dval. For
 * example, if dval is 0.314689 on entry, and n is 3, then the characters 314
 * are output, and the returned value is 0.689
*/

static double image_real_digits (double dval, int n, char *s)
														/*;image_real_digits*/
{
	int     i;

	while (n--) {
		dval *= 10.0;
		i = (int)floor(dval);
		*s++ = '0' + i;
		dval = dval - (double)i;
	}
	return dval;
}


/* IMAGE_REAL */

/* This routine is shared for fixed and float values. It returns a string image
 * of the double value dval, using fore, aft, exp as described in 14.3.8. The
 * resulting string image is stored in work_string. Note: if fore is zero, then
 * the string has the minimum required number of characters before the point.
 * If an out of range value is encountered, the exception in data_exception
 * is raised. If a bad character is encountered, DATA_ERROR is raised.
*/

static void image_real (double dval, int fore, int aft, int exp) /*;image_real*/
{
	int     exponent;
	char    sign;
	char    *s, *t;
	int     total_digits;
	int     exp_digits;
	double  round;

	/* Set pointer s to generate output characters in work string */

	s = work_string;

	/* Make sure fore, aft, exp have acceptable values. 14.3.7 does not
     * justify limiting fore, aft and exp to 512, but it seems reasonable!
    */

	if (fore <= 0) fore = 1;
	else if (fore > 512) fore = 512;

	if (aft < 0) aft = 0;
	else if (aft > 512) aft = 512;

	if (exp < 0) exp = 0;
	else if (exp > 512) exp = 512;

	/* Deal with 0.0 specially */

	if (dval == 0.0) {
		while (fore-- > 1) *s++ = ' ';
		*s++ = '0';
		*s++ = '.';

		while (aft--) *s++ = '0';

		if (exp) {
			*s++ = 'E';
			*s++ = '+';
			exp--;
			exp = MAX(exp,1);

			while (exp--) *s++ = '0';
		}
		*s = 0;
		return;
	}

	/* If non-zero capture sign */

	if (dval < 0.0) {
		sign = '-';
		dval = -dval;
		fore--;
	}
	else sign = '+';

	/* Reduce number to range 0.1 <= dval < 1.0, except that we do not
     * scale up if there is no exponent field, since we are happy with
     * leading zeroes in this case
    */

	exponent = 0;
	if (exp != 0) {
		while (dval < 0.1) {
			exponent--;
			dval *= 10.0;
		}
	}

	while (dval >= 1.0) {
		exponent++;
		dval /= 10.0;
	}

	/* A special case, if there is no exponent field, we want at least one
     * digit in front of the point, which means that the exponent value
     * should be at least one to get the proper value for this digit.
    */

	if (exp == 0 && exponent == 0) {
		exponent++;
		dval /= 10.0;
	}

	/* To round up, we must add a 5 in the place one past the last one to
     * be displayed. For the case of no exponent field there are exponent
     * digits before the point, otherwise there is only one digit. Note
     * that it is possible for rounding to push us back over 1.0
    */

	if (exp == 0) total_digits = aft + exponent;
	else total_digits = aft + 1;

	round = 0.5;
	while (total_digits--) round /= 10.0;

	dval += round;

	if (dval >= 1.0) {
		dval /= 10.0;
		exponent++;
	}

	/* Convert number for case of no exponent field present */

	if (exp == 0) {
		while (fore > exponent) {
			fore--;
			*s++ = ' ';
		}

		if (sign == '-') *s++ = sign;

		dval = image_real_digits(dval,exponent,s);
		s += exponent;
		*s++ = '.';
		image_real_digits(dval,aft,s);
		s += aft;
	}

	/* Convert number for case of exponent present */

	else {
		while (fore > 1) {
			fore--;
			*s++ = ' ';
		}

		if (sign == '-') *s++ = sign;

		dval = image_real_digits(dval,1,s);
		s++;
		*s++ = '.';
		image_real_digits(dval,aft,s);
		s += aft;

		/* Convert the exponent, first output E and sign */

		exponent--;          /* since one digit before point */
		*s++ = 'E';
		if (exponent < 0) {
			exponent = -exponent;
			*s++ = '-';
		}
		else *s++ = '+';
		exp--;               /* to account for sign */
		if (exp == 0) exp=1; /* but leave at least one digit */

		/* Output digits of exponent */

		t = s + 64;          /* cannot be more than 64 non-zero dec digits! */
		exp_digits = 0;
		while (exponent) {
			exp_digits++;
			*--t = '0' + (exponent % 10);
			exponent /= 10;
		}

		while (exp-- > exp_digits) *s++ = '0';
		while (exp_digits--) *s++ = *t++;
	}

	/* Conversion is complete */

	*s = 0;
}


/* IMAGE_INTEGER */

/* Returns a string image of item using the given base in work_string. If
 * an out of range value is encountered, the exception in data_exception
 * is raised. If a bad character is encountered, DATA_ERROR is raised.
*/

void image_integer(int item, int base)               /*;image_integer*/
{
	char    *p, *q;
	int     digit;

	/* Convert base if not 10 */

	p = work_string;
	if (base != 10) {
		if (base > 10) {
			*p++ = '1';
			*p++ = '0' + base - 10;
		}
		else *p++ = base + '0';
		*p++ = '#';
	}

	/* Deal with sign. Note: we work with the negative of the absolute
     * value of the number so that we do not have to make special checks
     * for the largest negative number in the twos complement case.
    */

	if (item < 0) *p++ = '-';
	else item = -item;

	/* Convert value to digit string in specified base */

	if (item == 0) {
		*p++ = '0';
	}
	else {
		q = work_string + 15;
		*q = 0;
		while(item) {
			digit = -(item % base);
			item /= base;
			*--q = (digit > 9) ? digit - 10 + 'A' : digit + '0';
		}
		while(*p++ = *q++);
		p--;
	}

	/* Add final # if based, and we are done */

	if (base != 10) *p++ = '#';
	*p = 0;
}


/* IMAGE_FIXED */

/* Returns a string image of the fixed point value item_val, where item_type
 * is a pointer to the type template, and fore, aft and exp control the
 * format according to the rules in 14.3.8. The result is in work_string.
 * Note: if fore is zero, then the result string has the minimum required
 * number of characters before the point. If an out of range value is
 * encountered, the exception in data_exception is raised. If a bad character
 * is encountered, DATA_ERROR is raised.
*/

void image_fixed (long item_val, int *item_type, int fore, int aft, int exp)
															/*;image_fixed*/
{
	int     exp2, exp5;
	double  dval;

	exp2 = FX_RANGE(item_type)->small_exp_2;
	exp5 = FX_RANGE(item_type)->small_exp_5;

	dval = (double)item_val;

	while (exp2 > 0) {
		exp2--; 
		dval *= 2.0;
	}
	while (exp2 < 0) {
		exp2++; 
		dval /= 2.0;
	}
	while (exp5 > 0) {
		exp5--; 
		dval *= 5.0;
	}
	while (exp5 < 0) {
		exp5++; 
		dval /= 5.0;
	}

	image_real (dval,fore,aft,exp);
}


/* IMAGE_FLOAT */

/* Returns a string image of the float value item_val, where fore, aft and
 * exp control the format according to the rules in 143.8. The result is in
 * work_string. Note: if fore is zero, then the result string has the minimum
 * required number of characters before the point. If an out of range value is
 * encountered, the exception in data_exception is raised. If a bad character
 * is encountered, DATA_ERROR is raised.
*/

void image_float (float num, int fore, int aft, int exp)		/*;image_float*/
{
	image_real ((double)(num),fore,aft,exp);
}


/* IMAGE_ENUM */

/* Procedure to return the value of the given enumeration type value as a
 * string in work_string. The type_ptr parameter points to the type or
 * subtype template to be used for the operation.
 */

void image_enum(int enum_val, int *type_ptr)                  /*;image_enum*/
{
	int     *ptr;
	char    *c;
	int     lit_len;

	if (TYPE(type_ptr) == TT_E_RANGE)	/* an actual subtype */
		type_ptr = ADDR(E_RANGE(type_ptr) -> ebase, E_RANGE(type_ptr) -> eoff);

	enum_val -= E_RANGE(type_ptr) -> elow;
	ptr = type_ptr + WORDS_E_RANGE;/* names are just past template */
	lit_len = *ptr++;
	c = work_string;
	if (lit_len == -1) { /* special case for character */
		*c++ = QUOTE;
		*c++ = enum_val;
		*c++ = QUOTE;
	}
	else {
		while(enum_val--) {
			ptr += lit_len;
			lit_len = *ptr++;
		}
		while(lit_len--) *c++ = *ptr++;
	}
	*c = 0;
}
