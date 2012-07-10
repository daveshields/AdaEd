/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/* translation of adautil.stl to c */
#include "hdr.h"
#include "vars.h"
#include "arithprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "utilprots.h"

static Const adavall(Symbol, char *, int);
static char *breakc(char *, int, char);
static int spanc(char *, int, char *);
static Const adavali(char *, int, char);

Const adaval(Symbol mde, char *number)							/*;adaval*/
{
	/* In SETL 'OVERFLOW' is returned to indicate overflow. In C
	 * the global variable adaval_overflow is set to indicate overflow
	 * Since adaval is recursive, we initialize flag here and then call
	 * adavall to perform actual computation.
	 * Part of the recursive use also involves breaking up the original
	 * string into parts, or slices, so we represent the string as	
	 * both pointers to the first character and companion intger giving length.
	 */

	Const	result;

	adaval_overflow = FALSE;
	result = adavall(mde, number, strlen(number));
	return result;
}

static Const adavall(Symbol mde, char *number, int numberl)		/*;adavall*/
{
	int	n, i, d, tn;
	Const	result, cbse, lncon;
	Rational	rn;
	char	numsign = '+';
	char	*numb, *b, *dc;
	char	*t, *expnt, *wh, *fr;
	int	expntl, whl, frl, bse, p, bl;
	int	numbl, exp_sgn;
	int	*ibse, *ln, *e, *dv;
	static	char *conv = "0123456789ABCDEF";
	char	*tstr;
	int	tstrl;

	if (numberl < 0 || numberl > 1000)chaos("util: adavall ridiculous numberl");

	n = 0;
	/* The setl sequence r = break(s, c) translates into C as follows:
	 *	t = breakc(s, sl, c);
	 *	if (t == (char *)0) { ...no match }
	 *	else {	match
	 *	  r = s; rl = t - s;
	 *	  s = t; sl -= rl;
	 *	}
	 */
	numb = number;
	numbl = numberl;
	if (numb == (char *)0 || numbl == 0) {
		adaval_overflow = TRUE;
		return const_new(CONST_OM);
	}
	numsign = '0';
	if (*numb == '+' || *numb == '-') {
		numsign = *numb;
		if (numbl == 1){ /* if only sign */
			adaval_overflow = TRUE;
			return const_new(CONST_OM);
		}
		numb++;
	}
	/* see if want integer and no base or exponent; if so, call adavali
	 * to do (much simpler) conversion.
	 */
	/* if want integer and number is all digits and no possibility of
	 * overflow, call adavali to do conversion 
	 */
	if (mde == symbol_integer && numbl > 0 && numbl <= 4
	  && spanc(numb, numbl, "0123456789") == numbl) {
		result = adavali(numb, numbl, numsign);
		return result;
	}
	/* Divide num into bse, num, and expnt:*/

	t = breakc(numb, numbl, '#');
	if (t == (char *)0) {	/* Not a based number.*/
		bse   = 10;
		expnt = numb; 
		expntl = numbl;
		t   = breakc(expnt, expntl, 'E');
		if (t == (char*)0) {	/* No exponent.*/
			numb   = expnt;
			numbl   = expntl;
			expnt = (char *)0;
		}
		else {			/* Exponent.*/
			b = expnt; 
			bl = t - expnt;
			numb = b; 
			numbl = bl;  /* do we need both ??  (gs 18-feb-85) */
			expnt = t;
			expntl -= bl;
			expnt++; 
			expntl--;
		}
	}
	else {		/* Based number.*/
		b = numb; 
		bl = t - numb;
		numb = t; 
		numbl -= bl;
		cbse   = adavali( b, bl, '+');
		bse = cbse->const_value.const_int;
		if (numbl > 0) {
			expnt = numb+1; 
			expntl = numbl-1;
		}
		else {
			expnt = (char *)0;
		}
		t   = breakc(expnt, expntl, '#'); /* strip off right base delimiter. */
		if (t != (char *)0) {
			numb = expnt; 
			numbl = t - expnt;
			expnt = t; 
			expntl -= numbl;
		}
		if (expntl == 1	 && *expnt == 'E') {	/* No exponent. */
			expnt = (char *)0;
		}
		else {			/* Exponent. */
			if (expntl > 2) {
				expnt += 2; 
				expntl -= 2;
			}
			else {
				expnt = (char *)0;
			}
		}
	}

	/* Compute exponent and bse ** expnt */

	ibse = int_fri(bse);
	if (expnt != (char *)0) {
		exp_sgn = 1;
		if (*expnt == '+') {
			if (expntl > 1) {
				expnt += 1; 
				expntl--;
			}
			else {
				expnt = (char *)0;
			}
		}
		else if (*expnt == '-') {
			if (expntl > 1) {
				expnt += 1; 
				expntl--;
			}
			else {
				expnt = (char *)0;
			}
			exp_sgn = -1;
		}
		result = adavall(symbol_universal_integer, expnt, expntl);
		e = int_exp(ibse, result->const_value.const_uint);
	}
	else {
		e = int_fri(1);
		exp_sgn = 0;
	}

	/* Now find the value of the number with base bse. */

	if (mde == symbol_integer || mde == symbol_universal_integer) {

		/* First convert body of integer: */

		ln	  = int_fri(0);
		for (i = 0; i < numbl; i++) {
			dc = breakc(conv, 16, numb[i]);
			if (dc == (char *)0) {
				adaval_overflow = TRUE;
				return (mde == symbol_integer ? int_const(0)
				  : uint_const(int_con(0)));
			}
			d = dc - conv;
			if (d > bse) {
				adaval_overflow = TRUE;
				return (mde == symbol_integer ? int_const(0)
				  : uint_const(int_con(0)));
			}
			arith_overflow = FALSE;
			ln = int_add(int_mul(ln, ibse), int_fri(d));
			if (arith_overflow) {
				adaval_overflow = TRUE;
				arith_overflow = 0;
				return (mde == symbol_integer ? int_const(0)
				  : uint_const(int_con(0)));
			}
		}

		/* Apply exponent:	 (n := n * e) */

		if (exp_sgn == 1) {
			ln = int_mul(ln, e);
			if (arith_overflow) {
				adaval_overflow = TRUE;
				arith_overflow = FALSE; /* reset */
				return (mde == symbol_integer ? int_const(0)
				  : uint_const(int_con(0)));
			}
		}

		/* If regular integer, then convert. */

		if (mde == symbol_integer) {
			n = int_toi (ln);
			if (arith_overflow) {
				adaval_overflow = TRUE;
				arith_overflow = FALSE; /* reset */
				return (mde == symbol_integer ? int_const(0)
				  : uint_const(int_con(0)));
			}
			if (numsign == '-') n = -n;
			result = int_const(n);
		}
		else {
			result = uint_const(ln);
		}

	}
	else if (mde == symbol_float || mde == symbol_dfixed
	  || mde == symbol_universal_real) {

		/* To obtain the numerator of the rational number,
		 * concatenate whole part with fractional part and convert
		 * the whole thing as an integer.  Then the denominator is
		 * just the base raised to a power determined by the
		 * length of the fractional part.
		 */
		tn = spanc(numb, numbl, "0123456789ABCDEFEabcdef");
		if (tn > 0) {
			wh = numb; 
			whl = tn;
			numb += tn; 
			numbl -= tn;
		}
		else {
			wh = (char *)0; 
			whl = 0;
		}
		if (*numb == '.' ) {
			if (numbl > 1) {
				numb++; 
				numbl--;
			}
			else {
				numb = (char *)0;
			}

			tn   = spanc(numb, numbl, "0123456789ABCDEFabcdef");
			if (tn == 0) {
				fr = (char *)0; 
				frl = 0;
			}
			else {
				fr = numb; 
				frl = tn;
				numb += tn; 
				numbl -= tn;
			}
			p    = frl;
			/*wh = strjoin(wh, fr);*/
			if (whl == 0 && frl == 0) {
				wh = "";
			}
			else if (whl == 0) { /* result is fr */
				wh = substr(fr, 1, frl);
			}
			else if (frl == 0) { /* result is wh */
				wh = substr(wh, 1, whl);
			}
			else { /* result is concaenation */
				wh = strjoin(substr(wh, 1, whl), substr(fr, 1, frl));
			}
			whl += frl;
			/* TBSL: need to free up intermediate storge */
		}
		else {
			p    = 0;
		}
		tstrl = 2 + 1 + whl + 1;
#ifdef SMALLOC
		tstr = smalloc((unsigned)tstrl+1);
#else
		tstr = emalloc((unsigned)tstrl+1);
#endif
		sprintf(tstr, "%2d#%s#", bse, wh);
		lncon = adavall (symbol_universal_integer, tstr, tstrl);
#ifndef SMALLOC
		efree(tstr);
#endif
		dv = int_exp(ibse, int_fri(p));
		if (lncon->const_kind == CONST_UINT) {
			rn = rat_fri(lncon->const_value.const_uint, dv);
		}
		else if (lncon->const_kind == CONST_INT) {
			rn = rat_fri(int_fri(lncon->const_value.const_int), dv);
		}
		else {
			chaos("adavall: lncon wrong type");
		}

		/* Apply exponent:	 (n := n * e) */

		if (exp_sgn == 1) {
			rn= rat_mul(rn, rat_fri(e, int_fri(1)));
		}
		else if (exp_sgn == -1) {
			rn= rat_mul(rn, rat_fri(int_fri(1), e));
		}

		/* If regular real, then convert. */

		if (mde == symbol_float) {
			result = real_const(rat_tor (rn, ADA_REAL_DIGITS));
		}
		else {
			result = rat_const(rn);
		}
	}
	return result;
}

static char *breakc(char *s, int sl, char c)						/*;breakc*/
{
	/* look for instance of break character in search string. return
	 * null pointer if no instance, else pointer to first instance of
	 * break character.
	 */

	while (sl--) {
		if (*s == c) return s;
		s++;
	}
	return (char *)0;
}

static int spanc(char *string, int length, char *span_string)		/*;spanc*/
{
	/* return number of initial characters in s which are also in ss */

	int		i, res = 0, ssl;
	char	c;

	ssl = strlen(span_string);
	for (i = 0; i < length; i++) {
		c = string[i];
		if (breakc(span_string, ssl, c) == (char *)0)
			return i;
		else res++;
	}
	return res;
}

static Const adavali(char *number, int numberl, char numsign)		/*;adavali*/
{
	/* process conversion when ordinary integer wanted and no base or
	 * exponent, and NO possibility of overflow during conversion.
	 */

	Const	result;
	int	i;
	char	s[120]; /*TBSL: const. 120 should be prog param*/

	for (i = 0; i < numberl; i++)
		s[i] = number[i];
	s[numberl] = '\0';
	i = atoi(s);
	if (numsign == '-') i = -i;
	result = int_const(i);
	return result;
}
