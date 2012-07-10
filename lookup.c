/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* This file has procedures formerly in closerms.c, inprefor.c, clocand.c,
 * errmsgsy.c and tokval.c
 * These procedures in general corresond to various table lookups.
 *	D. Shields	4-2-85
 */

/* Automatically Generated */
/* Must be re-generated if */
/* LALR grammar is changed */

/*
 *	closer_candidates[opener] := {CLOSER_SYMS(j) | j in CLOSER_MAP_SYMS(opener)}
 *
 *	So, for each opener, there is a list of tuples of closer candidates. Some
 *	may have only one set of these candidates, and the maximum number of tuples
 *	is three. Each set has between 1 and 5 elements.
 *
 *  As and example, for the opener whose symbol is 56, there are two tuples
 *	of closer candidates, viz [80, 21, 80, 37, 10] and [80, 21].
 *
 *	This structure is used by the scope_recovery procedure to generate and
 *	insert possible sequences of closers into the token sequence.
 *
 */

#include <string.h>
#include "lookupprots.h"

char closer_candidates[13][3][5] = {
	{  { 
		80, 21, 80, 37, 10},
		{ 80, 21	} 
	},
	{  { 
		80, 33, 21	} 
	},
	{  { 
		80, 21, 80, 37, 10},
		{ 80, 21	} 
	},
	{  { 
		80, 21	} 
	},
	{  { 
		72},
		{ 80, 72	} 
	},
	{  { 
		38},
		{ 65, 38	} 
	},
	{  { 
		80, 12, 21},
		{ 31},
		{ 61, 31	} 
	},
	{  { 
		80, 48, 21	} 
	},
	{  { 
		80, 29, 21	} 
	},
	{  { 
		80, 53, 21	} 
	},
	{  { 
		80, 29, 21	} 
	},
	{  { 
		80, 21, 80, 37, 10},
		{ 80, 21	} 
	},
	{  { 
		80, 29, 21	} 
	},
};

/* Automatically Generated */
/* Must be re-generated if */
/* LALR grammar is changed */
/* ERROR_MSG_SYMS */
char   *err_msg_syms (int n)							/*;err_msg_syms*/
{
	switch (n) {
	case 0:
		return ("Bad compilation");
	case 191:
		return ("Bad component declaration");
	case 256:
		return ("Bad parameter declaration");
	case 99:
		return ("Bad term");
	case 323:
		return ("Bad exception handler");
	case 167:
		return ("Bad discriminant declaration");
	case 298:
		return ("Bad exception choice");
	case 171:
		return ("Bad choice");
	case 108:
		return ("Bad compilation");
	case 268:
		return ("Bad entry declaration");
	case 173:
		return ("Bad declaration");
	case 204:
		return ("Bad factor");
	case 238:
		return ("Bad condition in if statement");
	case 301:
		return ("Bad generic formal");
	case 242:
		return ("Bad case alternative");
	case 278:
		return ("Bad select alternative");
	case 217:
		return ("Bad statement");
	case 156:
		return ("Bad index specification");
	default :
		return("") ;
	}
}
int in_beacon(int n)										/*;in_beacon*/
{
	/* macro in_BEACON_SYMS, formerly in recover.h,is now a procedure
 * this simplifies files for PC and avoids problems with -cram option
 * of HIC when run with reduced memory
 *	ds	30-mar-85
 */
	/* BEACON_SYMS */
	/* the procedure is now in_beacon*/
	return
	    ((n == 10) || (n == 18) || (n == 19) || (n == 20) || (n == 21)
	    || (n == 25) || (n == 26) || (n == 29) || (n == 31) || (n == 33)
	    || (n == 42) || (n == 45) || (n == 51) || (n == 56) || (n == 58)
	    || (n == 62) || (n == 80)) ;
}

/*			PREFERRED_FOR_SYMS				*/

/*
 * returns true if u is in the set of PREFERRED_FOR_SYMS of v
 *
 */
int in_PREFERRED_FOR_SYMS (int u, int v)		/*;in_PREFERRED_FOR_SYMS*/
{
	switch(u)	{
	case 66 : 
		return(v == 65) ;
	case 65 : 
		return(v == 45) ;
	case 38 : 
		return(v == 31) ;
	case 77 : 
		return(v == 86) ;
	case 82 : 
		return(v == 88) ;
	case 80 : 
		return(v == 33) ;
	case 18 : 
		return(v == 33) ;
	case 25 : 
		return(v == 33) ;
	case 88 : 
		return((v == 82) || (v == 31)) ;
	case 55 : 
		return(v == 59) ;
	case 31 : 
		return((v == 38) || (v == 88)) ;
	case 59 : 
		return(v == 55) ;
	default : 
		return(0) ;
	}
} /* End PREFERRED_FOR_SYMS */

int is_opener(int t)										/*;is_opener*/
/* The macro in_OPENER_SYMS, formerly in recover.h,
 * is now part of this procedure.
 *		ds 3-30-85
 */
{
	return
	    (((t)==8)
	    || ((t)==10)
	    || ((t)==12)
	    || ((t)==19)
	    || ((t)==20)
	    || ((t)==29)
	    || ((t)==33)
	    || ((t)==42)
	    || ((t)==48)
	    || ((t)==53)
	    || ((t)==56)
	    || ((t)==71)
	    || ((t)==251)
	    );
}

int	open_index (int n)									/*;open_index*/
/*
 *	This function maps the value of an opener to a number in the
 *  range 0 to 12 for use as an array index.
 */
{
	switch (n) {
	case 251:
		return (0);
	case 33:
		return (1);
	case 42:
		return (2);
	case 10:
		return (3);
	case 71:
		return (4);
	case 8:
		return (5);
	case 12:
		return (6);
	case 48:
		return (7);
	case 19:
		return (8);
	case 53:
		return (9);
	case 20:
		return (10);
	case 56:
		return (11);
	case 29:
		return (12);
	}				/* case */
	return (0); /* shouldn't reach here, this for lint's sake */
}

char * token_val_des(char *t) 							/*;token_val_des*/
{
	if (!strcmp("identifier",t) )
		return ("any_id")  ;
	if (!strcmp("numeric_literal",t) )
		return ("0")  ;
	if (!strcmp("character_literal", t))
		return ("'?'")	;
	if (!strcmp("string_literal", t) )
		return ("") ;
	return (t) ;
}
/* CLOSER_MESSAGE_SYMS */
char   *CLOSER_MESSAGE_SYMS (int n)			/*;CLOSER_MESSAGE_SYMS*/
{
	/* The value of n is an encoding of the tuple */
	/* generated merely by adding their values */
	switch (n) {
	case 38 /* [ 38 ] */ :
		return ("\"OF\" inserted to match \"ARRAY\"");
	case 152 /* [ 80 72 ] */ :
		return ("\");\" inserted to match \"(\"");
	case 72 /* [ 72 ] */ :
		return ("\")\" inserted to match \"(\"");
	case 113 /* [ 80 12 21 ] */ :
		return (" \"END CASE;\" inserted to match \"CASE\"");
	case 103 /* [ 65 38 ] */ :
		return ("\"OF IDENTIFIER\" inserted to match \"ARRAY\"");
	case 130 /* [ 80 29 21 ] */ :
		return (" \"END IF;\" inserted to match \"IF\"");
	case 149 /* [ 80 48 21 ] */ :
		return (" \"END RECORD;\" inserted to match \"RECORD\"");
	case 134 /* [ 80 33 21 ] */ :
		return (" \"END LOOP;\" inserted to match \"LOOP\"");
	case 228 /* [ 80 21 80 37 10 ] */ :
		return ("statement part missing for unit starting");
	case 154 /* [ 80 53 21 ] */ :
		return (" \"END SELECT;\" inserted to match \"SELECT\"");
	case 31 /* [ 31 ] */ :
		return ("\"IS\" inserted to match \"CASE\"");
	case 92 /* [ 61 31 ] */ :
		return ("\"IS WHEN\" inserted to match \"CASE\"");
	case 101 /* [ 80 21 ] */ :
		return ("\"END;\" inserted to match current scope opened");
	}
	/* shouldn't reach here give string for sake of lint */
	return("");
}				/* CLOSER_MESSAGE_SYMS */
