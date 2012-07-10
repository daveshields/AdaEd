/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#include "ada.h"

#define NAMEMAPSIZE 1021	/* temporary values */
/* define with suffix L as long constant for PC */
#ifdef IBM_PC
#define NAMEMAPSIZE_L 1021L	/* temporary values */
#endif
#define NAMELISTSIZE 324	/* temporary values */

#define ISDELIMITER(c) strchr("()&*:-=/+;><,.|![]",c)

#define IS_STRING_CHAR(x)  ( x != '"' && ( isprint(x) || x == ' ') )
