/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* Translation of module ada - arith to C */
/* David Shields  CIMS	11 Nov 83 */

/* translation of arith and multi-precision package to C.
 *
 */
#ifndef _arith_h
#define _arith_h
#include <math.h>

/*
  Some of the procedures want to signal overflow by returning the
  string 'OVERFLOW'. In C we do this by setting global arith_overflow
  to non-zero if overflow occurs, zero otherwise
 */
extern int arith_overflow ;


#define ABS(x) ((x)<0 ? -(x) : (x))
#define SIGN(x) ((x)<0 ? -1 : (x)==0 ? 0 : 1)

/* Constants for use by arithmetic packages: */

typedef struct Rational_s
{
	int	*rnum;	/* numerator */
	int	*rden;	/* denominator */
} Rational_s;
typedef Rational_s *Rational;

/* Macros for access to rational numbers: */

#define num(x) x->rnum
#define den(x) x->rden


extern Rational RAT_TWO;
extern	Rational ADA_MAX_FLOAT;

#endif
