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
	  |         Part 5: TEXT_IO Scan Procedures           |
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

/*  This module contains routines for the implementation of some of
 *  the predefined Ada packages and routines, namely SEQUENTIAL_IO,
 *  DIRECT_IO, TEXT_IO, and CALENDAR. Part 5 contains the scanning
 *  procedures used for TEXT_IO input.
*/

#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include "ipredef.h"
#include "machineprots.h"
#include "predefprots.h"

static char getcp();
static char nextc();
static void skipc();
static void copyc();
static void copy_integer();
static void copy_based_integer();
static void scan_blanks();
static void setup_fixed_field(int);
static void test_fixed_field_end();
static int alpha(char);
static int alphanum(char);
static int graphic(char);
static int digit(char);
static int extended_digit(char);
static int sign(char);
static void check_digit();
static void check_hash(char);
static void check_extended_digit();
static void range();
static int scan_int();
static int scan_based_int(int);
static double scan_real_val(int);
static void scan_enum_val();
static int scan_integer_val(int *, int);
static long scan_fixed_val(int *, int);
static float scan_float_val(int *, int);

/* The following variables control whether we are scanning from a file or
 * from a string. The flag scan_mode is 'F' if scanning from a file and 'S'
 * if scanning from a string. The pointer ins points to the next character
 * to be scanned in the case where we are scanning from a string.
 */

static char scan_mode;
static char *ins;

/* The variable s is used to store characters in work_string */

static char *s;


/* GETCP */

/* This procedure gets the next character from the string or file being scanned
 * according to the setting of scan_mode. In string mode, ins is updated. If no
 * more character remain to be scanned, then END error is signalled.
 */

static char getcp()													/*;getcp*/
{
	if (scan_mode == 'F') {
		return get_char();
	}
	else {
		if (*ins == 0)
		    predef_raise(END_ERROR, "End of string encountered");
		return * ins++;
	}
}


/* NEXTC */

/* This procedure returns the next character to be read from the string or file
 * being scanned, according to the setting of scan_mode. In string mode, ins is
 * updated. If we are currently at end of string then a line feed is returned.
 */

static char nextc()													/*;nextc*/
{

	if (scan_mode == 'F') {
		load_look_ahead(FALSE);
		return CHAR1;
	}
	else {
		if (*ins) return *ins;
		else return LINE_FEED;
	}
}


/* SKIPC */

/* This procedure skips the next input character */

static void skipc()				                                  /*;skipc*/
{
	char c;

	if (scan_mode == 'F')
		c = get_char();
	else
		ins++;
}

/* COPYC */

/* This procedure copies the next input character to work_string using s */

static void copyc()                                  				/*;copyc*/
{
	char c;

	if (scan_mode == 'F')
		c = get_char();
	else
		c = *ins++;
	if (c)
		*s++ = UPPER_CASE(c);
	else
		predef_raise (SYSTEM_ERROR, "End of string encountered");
}

/* COPY_INTEGER */

/* This procedure copies a string with the syntax of "integer" from the
 * input to the work string. Underscores are allowed but not copied.
 */

static void copy_integer()									  /*;copy_integer*/
{
	check_digit();

	while (digit(nextc())) {
		copyc();
		if (nextc() == '_') {
		    skipc();
		    check_digit();
		}
	}
}


/* COPY_BASED_INTEGER */

/* This procedure copies a string with the syntax of "based_integer" from
 * the input to the work string. Underscores are allowed but not copied.
 */

static void copy_based_integer()					  /*;copy_based_integer*/
{
	check_extended_digit();

	while (extended_digit(nextc())) {
		copyc();
		if (nextc() == '_') {
		    skipc();
		    check_extended_digit();
		}
	}
}

/* SCAN_BLANKS */

/* Routine to scan past leading blanks to find first non-blank. Signals
 * an exception if no non-blank character is located.
*/

static void scan_blanks()			                         /*;scan_blanks*/
{
	char c;

	if (scan_mode == 'F') {
		for (;;) {
		    load_look_ahead(FALSE);
		    if (CHARS == 0)
		        predef_raise(END_ERROR, "No item found");
		    c = nextc();
		    if (c == ' ' || c == HT || c == PAGE_MARK || c == LINE_FEED)
		        getcp();
		    else break;
		}
		return;
	}
	else {
		while(*ins == ' ' || *ins == HT) ins++;
		return;
	}
}


/* SETUP_FIXED_FIELD */

/* This procedure is used for numeric conversions where the field to be scanned
 * has a fixed width(i.e. width parameter is non-zero). It acquires the field
 * from the input file and copies it to work_string. It returns to the caller
 * ready to scan the data from work_string.
 */

static void setup_fixed_field(int width)                /*;setup_fixed_field*/
{
	char   *p;

	p = work_string;
	for (;;) {
		load_look_ahead(FALSE);
		if (width-- != 0 && CHARS != 0 && CHAR1 != PAGE_MARK
		                               && CHAR1 != LINE_FEED) {
		    *p++ = get_char();
		}
		else break;
	}
	*p = '\0';
	scan_mode = 'S';
	ins = work_string;
}


/* TEST_FIXED_FIELD_END */

/* This procedure is called after scanning an item from a fixed length field
 * to ensure that only blanks remain in the field. An exception is raised if
 * there are any unexpected non-blank characters left in the field.
*/

static void test_fixed_field_end()			        /*;test_fixed_field_end*/
{
	scan_blanks();
	if (*ins)
		predef_raise(data_exception,"Unexpected non-blank characters in field");
}

/* ALPHA */

/* Procedure to test if character argument is an upper or lower case letter,
 * returns TRUE if the argument is a letter, FALSE if it is not.
*/

static int alpha(char c)			                                /*;alpha*/
{
	if (c > 'Z')
		c -= 32;
	return ('A' <= c && c <= 'Z');
}


/* ALPHANUM */

/* Procedure to test if character argument is an upper or lower case letter,
 * or a digit. Returns TRUE if the argument is a letter or digit, else FALSE.
*/

static int alphanum(char c)                             /*;alphanum*/
{
	if (c > 'Z')
		c -= 32;
	return (('A' <= c && c <= 'Z') ||('0' <= c && c <= '9'));
}


/* GRAPHIC */

/*  Procedure to test if character is an ASCII graphic character. Returns
 *  Returns TRUE if the argument is an ASCII graphic, else FALSE.
*/

static int graphic(char c)			                              /*;graphic*/
{
	return (0x20 <= c && c <= 0x7f);
}


/* DIGIT */

/* Procedure to test if character is a digit, returns TRUE or FALSE */

static int digit(char c)                                /*;digit*/
{
	return ('0' <= c && c <= '9');
}


/* EXTENDED_DIGIT */

/* Procedure to test if character is extended digit, returns TRUE or FALSE */

static int extended_digit(char c)                       /*;extended_digit*/
{
	return ('0' <= c && c <= '9') || ('a' <= c && c <= 'f') ||
	  ('A' <= c && c <= 'F');
}


/* SIGN */

/* Procedure to test if character is a sign, returns TRUE or FALSE */

static int sign(char c)				                                 /*;sign*/
{
	return (c == '-' || c == '+');
}


/* CHECK_DIGIT */

/* Procedure to determine if next character is a digit, exception if not */

static void check_digit() 			                         /*;check_digit*/
{
	char c = nextc();
	if (c < '0' || c > '9')
		predef_raise(data_exception, "Invalid digit");
}

/* CHECK_HASH */

/* Procedure to determine if next character is a matching hash,
 * exception if not. Stores '#' in work string.
 */

static void check_hash(char c)		                           /*;check_hash*/
{
	if (nextc() != c)
		predef_raise(data_exception, "Missing # in based number");
	skipc();
	*s++ = '#';
}

/* CHECK_EXTENDED_DIGIT */

/* Procedure to determine if next char is extended digit, exception if not */

static void check_extended_digit()                  /*;check_extended_digit*/
{
	if (!extended_digit(nextc()))
		predef_raise(data_exception, "Invalid extended digit");
}

/* RANGE */

/* Procedure called if scanned number is out of range */

static void range()					                               /*;range*/
{
	predef_raise(data_exception, "Number out of range");
}


/* SCAN_INT */

/* This routine scans an integer value from the string pointed to by the
 * global pointer s. On exit s is updated to point to the first non-digit.
 * The result returned is always negative. This allows the largest negative
 * integer value to be properly stored and converted. A value of +1 returned
 * indicates that overflow occured.
*/

static int scan_int()				                          /*;scan_int*/
{
	int     ival;
	int     digit_value;
	int     overflow1, overflow2;

	ival = 0;
	while (digit(*s)) {
		ival = word_mul(ival,10,&overflow1);
		digit_value = *s++ - '0';
		ival = word_sub(ival,digit_value,&overflow2);
		if (overflow1 || overflow2) {
		    while (digit(*s)) s++;
		    return 1;
		}
	}
	return ival;
}


/* SCAN_BASED_INT */

/* This routine scans a based integer value from the string pointed to by the
 * global pointer s. On exit s is updated to point to the first non-digit.
 * The result returned is always negative. This allows the largest negative
 * integer value to be properly stored and converted. If overflow is detected,
 * then the value +1 is returned to signal overflow.
*/

static int scan_based_int(int base)		                   /*;scan_based_int*/
{
	int     ival;
	int     digit_value;
	int     overflow1, overflow2;

	ival = 0;
	while (extended_digit(*s)) {
		ival = word_mul(ival,base,&overflow1);
		digit_value = *s++ - '0';
		if (digit_value > 9) digit_value -= 7;
		if (digit_value >= base) {
		    predef_raise (data_exception,"Digit out of range of base");
		}
		ival = word_sub(ival,digit_value,&overflow2);
		if (overflow1 || overflow2) {
		    while (extended_digit(*s)) s++;
		    return 1;
		}
	}
	return ival;
}


/* SCAN_REAL_VAL */

/* Procedure to scan a real value and return the result as a double real.
 * A range exception is signalled if the value is out of range of allowed
 * Ada real values, but no other range check is made.
 */

static double scan_real_val(int fixed_field)			     /*;scan_real_val*/
{
	double  dval;            /* value being scanned */
	char    sign_val;        /* sign of mantissa */
	char    exp_sign_val;    /* sign of exponent */
	char    c;               /* character scanned */
	int     base;            /* base as integer */
	double  dbase;           /* base as real */
	double  fraction;        /* power of ten fraction after decimal point */
	int     dig;             /* next digit value */
	double  ddig;            /* next digit as real */
	int     based;           /* TRUE if number is based */
	long    exponent;        /* value of exponent */
	int     before_point;    /* TRUE if before decimal point */

	/* First scan out item with the proper syntax and put it in work_string */

	s = work_string;

	if (sign(nextc())) copyc();

	copy_integer();

	c = nextc();
	if (c == '#' || c == ':') {
		skipc();
		*s++ = '#';
		copy_based_integer();
		if (nextc() != '.')
		    predef_raise(DATA_ERROR,"Missing period in real value");
		copyc();
		copy_based_integer();
		check_hash(c);
		based = TRUE;
	}
	else {
		based = FALSE;
		if (nextc() != '.')
		    predef_raise(DATA_ERROR,"Missing period in real value");
		copyc();
		copy_integer();
	}

	c = nextc();
	if (c == 'e' || c == 'E') {
		copyc();
		c = nextc();
		if (sign(nextc())) copyc();
		copy_integer();
	}
	 
	if (fixed_field)
		test_fixed_field_end();        

	*s = 0;

	/* Now we have the real literal stored in work_string, so prepare to
	 * convert the value, dealing first with setting the proper sign. Note
	 * that we can assume that the syntax of the literal is correct since
	 * we did all the checking above as we scanned it out.
	*/

	s = work_string;
	if (sign(*s)) sign_val = *s++; else sign_val = '+';

	/* Acquire the proper base value. Note that scan_int returns the negative
	 * of the value scanned, with +1 indicating overflow which will be invalid.
	*/

	if (based) {
		base = scan_int();
		if (base < -16 || base > -2)
		    predef_raise(DATA_ERROR, "Invalid base");
		base = -base;
		s++;
	}
	else base = 10;
	dbase = (double)base;

	/* Scan and convert digits */

	dval = 0.0;
	before_point = TRUE;
	for (;;) {
		if (*s == 0) break;
		if (*s == '#') {
		    s++;
		    break;
		}
		if (!based && *s == 'E') break;
		c = *s++;
		if (c == '.') {
		    before_point = FALSE;
		    fraction = 1.0;
		}
		else {
		    dig = c - '0';
		    if (dig > 9) dig -= 7;     /* convert hex digit */
		    if (dig > base) predef_raise (DATA_ERROR, "Digit > base");
		    ddig = (double)dig;
		    if (before_point) {
		        dval = dval * dbase + ddig;
		        if (dval > ADA_MAX_REAL) range();
		    }
		    else {
		        fraction /= base;
		        dval = dval + ddig * fraction;
		    }
		}
	}

	/* Deal with exponent if present */

	if (*s == 'E') {
		s++;

		if (sign(*s)) exp_sign_val = *s++; else exp_sign_val = '+';
		exponent = scan_int();

		/* A value of +1 in exponent means that scan_int detected overflow.
		 * This is not yet a range error. If the mantissa is 0 or 1, the
		 * effect is as if we had an exponent of 1.
		*/

		if (exponent == 1) {
		    if (dval == 0.0 || dval == 1.0) {
		        exponent = 1;
		    }

		/* If we have a positive exponent, then if the mantissa is greater than
		 * 1.0, we do have an overflow, otherwise if the mantissa is less than
		 * 1.0, we have an underflow situation giving a result of zero.
		*/

		    else if (exp_sign_val == '+') {
		        if (dval > 1.0) range();
		        else dval = 0.0;
		    }

		/* For a negative exponent, the situation is the other way round, since
		 * we want in effect the reciprocal of the value for the positive case.
		*/

		    else {
		        if (dval > 1.0) dval = 0.0;
		        else range();
		    }
		}

		/* If no overflow, get abs value of exponent (scan_int returned -exp) */

		else exponent = -exponent;

		/* An optimization: if the mantissa is zero , save a lot of time
		 * in converting silly numbers like 0E+25000 by resetting exponent.
		*/

		if (dval == 0.0) {
		    exponent = 0;
		}

		/* Adjust mantissa by exponent, using proper exponent sign */

		if (exp_sign_val == '+') {
		    while (exponent > 0) {
		        dval *= dbase;
		        if (dval > ADA_MAX_REAL) range();
		        exponent--;
		    }
		}
		else {
		    while (exponent > 0) {
		        dval /= dbase;
		        exponent--;
		    }
		}
	}

	/* Return scanned value with proper sign */

	if (sign_val == '+') return dval;
	else return -dval;
}


/* SCAN_ENUM_VAL */

/* Procedure to scan an Ada enumeration literal, which may be an identifier
 * identifier or a character literal. The result is stored in work_string.
*/

static void scan_enum_val() 				              /*;scan_enum_val*/
{
	scan_blanks();
	if (scan_mode == 'S' && *ins == 0) {
		predef_raise(END_ERROR, "String is all blanks");
	}
	s = work_string;

 /* Try identifier */

	if (alpha(nextc())) {
		while(alphanum(nextc())) {
		    copyc();
		    if (nextc() == '_')
		        copyc();
		}
		*s = '\0';
		return;
	}

 /* Try character literal: */

	if (nextc() == QUOTE) {
		copyc();
		if (graphic(nextc())) {
		    *s++ = getcp();     /* can't use copyc, do not want fold */
		    if (nextc() == QUOTE) {
		        copyc();
		        *s = 0;
		        return;
		    }
		}
		predef_raise(data_exception, "Illegal character literal");
	}
	predef_raise(data_exception, "Illegal enumeration literal");
}


/* SCAN_ENUM */

/* Procedure to scan an Ada enumeration literal, which may be an identifier
 * identifier or a character literal. The result is stored in work_string.
 * For this case, the input is from the current TEXT_IO input file.
*/

void scan_enum()					                         /*scan_enum*/
{
	scan_mode = 'F';
	scan_enum_val();
}


/* SCAN_ENUM_STRING */

/* Procedure to scan an Ada enumeration literal, which may be an identifier
 * identifier or a character literal. The result is stored in work_string.
 * For this case, the input is from the string stored in work_string. On
 * return, last is the count of characters scanned minus one.
*/

void scan_enum_string(int *last)                  /*;scan_enum_string*/
{
	scan_mode = 'S';
	ins = work_string;
	scan_enum_val();
	*last = ins - work_string - 1;
}


/* SCAN_INTEGER_VAL */

/* Procedure to scan an Ada integer value and return the integer result. The
 * parameter num_type is a pointer to the type template for the integer.
 */

static int scan_integer_val(int *num_type, int fixed_field)/*;scan_integer_val*/
{
	int    ival;             /* value of integer signed */
	char   sign_val;         /* sign of value '+' or '-' */
	char   c;                /* character scanned from string */
	int    base;             /* base value 2-16 */
	int    based;            /* TRUE if number is based */
	int    exponent;         /* exponent value */
	int    overflow;         /* flag used to detect overflow */

	/* First scan out item with the proper syntax and put it in work_string */

	s = work_string;

	if (sign(nextc())) copyc();

	copy_integer();

	c = nextc();
	if (c == '#' || c == ':') {
		skipc();
		*s++ = '#';
		copy_based_integer();
		check_hash(c);
		based = TRUE;
	}
	else based = FALSE;

	c = nextc();
	if (c == 'e' || c == 'E') {
		copyc();
		c = nextc();
		if (c == '+' || c == '-') skipc();
		copy_integer();
		if (c == '-')
		    predef_raise(data_exception,"Negative exponent in integer value");
	}

	if (fixed_field)
		test_fixed_field_end();

	*s = 0;

	/* Now we have the integer literal stored in work_string */

	s = work_string;
	if (sign(*s)) sign_val = *s++; else sign_val = '+';

	if (based) {
		base = -scan_int();
		if (base < 2 || base > 16)
		    predef_raise(data_exception, "Invalid base");
		s++;
		ival = scan_based_int(base);
		s++;
	}
	else {
		ival = scan_int();
		base = 10;
	}

	/* Number is in ival (in negative form), deal with exponent */

	if (ival == 1) range();
	if (*s++ == 'E') {
		exponent = scan_int();
		if (exponent < -64 || exponent == 1) range();
		while (exponent++) {
		    ival = word_mul(ival,base,&overflow);
		    if (overflow) range();
		}
	}

	if (sign_val == '+') {
		ival = -ival;
		if (ival < 0) range();         /* twos complement wrap test */
	}

	/* Check number is in range of type */

	if (ival < I_RANGE(num_type)->ilow || ival > I_RANGE(num_type)->ihigh)
		range();

	return ival;
}


/* SCAN_INTEGER */

/* Procedure to scan an Ada integer value and return the integer result
 * The parameter num_type is a pointer to the type template for the integer.
 * and width specifies the width of the field(zero = unlimited scan).
 * For this case, the input is from the current TEXT_IO input file.
*/

int scan_integer(int *num_type, int width)			         /*;scan_integer*/
{
	int     result;

	if (width != 0) {
		setup_fixed_field(width);
		scan_blanks();
		if (*ins == 0)
		    predef_raise(DATA_ERROR, "String is all blanks");
		result = scan_integer_val(num_type,TRUE);
	}
	else {
		scan_mode = 'F';
		scan_blanks();
		result = scan_integer_val(num_type,FALSE);
	}
	return result;
}


/* SCAN_INTEGER_STRING */

/* Procedure to scan an Ada integer value and return the integer result
 * For this case, the input is from the string stored in work_string. On
 * return, last is the count of characters scanned minus one.
*/

int scan_integer_string(int *num_type, int *last)     /*;scan_integer_string*/
{
	int     result;

	scan_mode = 'S';
	ins = work_string;
	scan_blanks();
	if (*ins == 0) {
		predef_raise(END_ERROR, "String is all blanks");
	}
	result = scan_integer_val(num_type,FALSE);
	*last = ins - work_string - 1;
	return result;
}


/* SCAN_FIXED_VAL */

/* Procedure to scan an Ada fixed value and return the fixed result. The
 * parameter num_type is a pointer to the type template for the fixed type.
*/

static long scan_fixed_val(int *num_type, int fixed_field)   /*;scan_fixed_val*/
{
	double dval = scan_real_val(fixed_field);
	int exp2, exp5;

	/* Convert real to equivalent fixed value, using powers of 2 and 5 */

	exp2 = FX_RANGE(num_type)->small_exp_2;
	exp5 = FX_RANGE(num_type)->small_exp_5;

	while (exp2 > 0) {exp2--; dval /= 2.0;}
	while (exp2 < 0) {exp2++; dval *= 2.0;}
	while (exp5 > 0) {exp5--; dval /= 5.0;}
	while (exp5 < 0) {exp5++; dval *= 5.0;}

	/* We now have the proposed fixed value, still stored in real form, in
	 * dval. Round to nearest integer, ready for conversion to fixed form.
	*/

	if (dval >= 0.0) dval += 0.5;
	else dval -= 0.5;

	/* Check that value is in range */

	if ( (long)dval > (FX_RANGE(num_type)->fxhigh)
	  || (long)dval < (FX_RANGE(num_type)->fxlow))
		range();

	return (long)dval;
}

/* SCAN_FIXED */

/* Procedure to scan an Ada fixed value and return the fixed result. The
 * parameter num_type is a pointer to the type template for the fixed type.
 * and width specifies the width of the field(zero = unlimited scan).
 * For this case, the input is from the current TEXT_IO input file.
*/

long scan_fixed(int *num_type, int width)     /*;scan_fixed*/
{
	long    result;

	if (width != 0) {
		setup_fixed_field(width);
		scan_blanks();
		if (*ins == 0)
		    predef_raise(DATA_ERROR, "String is all blanks");
		result = scan_fixed_val(num_type,TRUE);
	}
	else {
		scan_mode = 'F';
		scan_blanks();
		result = scan_fixed_val(num_type,FALSE);
	}

	return result;
}

/* SCAN_FIXED_STRING */

/* Procedure to scan an Ada fixed value and return the integer result. The
 * parameter num_type is a pointer to the type template for the integer.
 * and width specifies the width of the field(zero = unlimited scan).
 * For this case, the input is from the string stored in work_string. On
 * return, last is the count of characters scanned minus one.
*/

long scan_fixed_string(int *num_type, int *last)       /*;scan_fixed_string*/
{
	long    result;

	scan_mode = 'S';
	ins = work_string;
	scan_blanks();
	if (*ins == 0)
		predef_raise(END_ERROR, "String is all blanks");
	result = scan_fixed_val(num_type,FALSE);
	*last = ins - work_string - 1;
	return result;
}


/* SCAN_FLOAT_VAL */

/* Procedure to scan an Ada float value and return the float result. The
 * parameter num_type is a pointer to the type template for the float type.
*/

static float scan_float_val(int *num_type, int fixed_field)  /*;scan_float_val*/
{
	double    dval;

	dval = scan_real_val(fixed_field);

	/* Check that value is in range */

	if ( dval > (double)(FL_RANGE(num_type)->flhigh)
	  || dval < (double)(FL_RANGE(num_type)->fllow))
		range();
	return (float)dval;
}

/* SCAN_FLOAT */

/* Procedure to scan an Ada float value and return the float result. The
 * parameter num_type is a pointer to the type template for the float type.
 * and width specifies the width of the field(zero = unlimited scan).
 * For this case, the input is from the current TEXT_IO input file.
*/

float scan_float(int *num_type, int width)					     /*;scan_float*/
{
	float   result;

	if (width != 0) {
		setup_fixed_field(width);
		scan_blanks();
		if (*ins == 0)
		    predef_raise(DATA_ERROR, "String is all blanks");
		result = scan_float_val(num_type,TRUE);
	}
	else {
		scan_mode = 'F';
		scan_blanks();
		result = scan_float_val(num_type,FALSE);
	}

	return result;
}

/* SCAN_FLOAT_STRING */

/* Procedure to scan an Ada float value and return the integer result. The
 * parameter num_type is a pointer to the type template for the integer.
 * and width specifies the width of the field(zero = unlimited scan).
 * For this case, the input is from the string stored in work_string. On
 * return, last is the count of characters scanned minus one.
*/

float scan_float_string(int *num_type, int *last)       /*;scan_float_string*/
{
	float   result;

	scan_mode = 'S';
	ins = work_string;
	scan_blanks();
	if (*ins == 0)
		predef_raise(END_ERROR, "String is all blanks");
	result = scan_float_val(num_type,FALSE);
	*last = ins - work_string - 1;
	return result;
}

/* ENUM_ORD */

/* Returns the ORD value corresponding to the literal stored in the global
 * variable work_string. The parameter type_ptr points to the template for
 * the enumeration subtype. An exception is signalled if there is no matching
 * value, using the exception code given as an argument.
*/

int enum_ord(int *type_ptr, int slen, int exception_to_raise)      /*;enum_ord*/
{
	int     lbd, ubd, type_ubd;
	int     *lit_ptr;
	int     lit_len, str_len;
	int     i;
	int     *lp;
	char    *sp;
	int     item_val;

	/* slen is non-negative if string length known */
	if (slen == -1)		/* if length uncertain, compute it */
		str_len = strlen(work_string);
	else			/* if length known, use it */
		str_len = slen;    /* This is true for character literal case */

	lbd = E_RANGE(type_ptr) -> elow;
	ubd = E_RANGE(type_ptr) -> ehigh;
	if (TYPE(type_ptr) == TT_E_RANGE)     /* an actual subtype */
		type_ptr = ADDR(E_RANGE(type_ptr) -> ebase, E_RANGE(type_ptr) -> eoff);

	type_ubd = E_RANGE(type_ptr) -> ehigh;
	lit_ptr = type_ptr + WORDS_E_RANGE;
	item_val = 0;

	if (*lit_ptr == -1) { /* special case for type CHARACTER */
		if (str_len == 3 && work_string[0] == '\'' && work_string[2] == '\'')
			item_val = work_string[1];
		else
			predef_raise(exception_to_raise, "Illegal character literal");
	}
	else { /* normal case */
		while(item_val <= type_ubd) {
		    lit_len = *lit_ptr++;
		    if (lit_len == str_len) {
		        i = lit_len;
		        lp = lit_ptr;
		        sp = work_string;
				/* Do not fold character literals to upper case */
				if (work_string[0] != '\'') {
					while(i--) {
						char c = (islower(*sp) ? toupper(*sp) : *sp);
						*sp++ = c;
					}
				}
				sp = work_string;
		 		i = lit_len;
				while(i &&(*lp++ == *sp++))
					i--;
				if (i == 0)
					break;
			}
		    lit_ptr += lit_len;
		    item_val++;
		}
	}

	/* If the literal is not found, item_val is surely out of bounds... */

	if (item_val < lbd || item_val > ubd)
		predef_raise(exception_to_raise, "Illegal enumeration literal");

	return item_val;
}
