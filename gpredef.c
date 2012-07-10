/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include <stdio.h>
#include "config.h"
#include "miscprots.h"
#include "gpredefprots.h"

/* define procedures:
 *	predef_name(int)   int => string of predef opcode (or null if no such)
 */

char *pretab[] = {
	"",
	/* Operations where a file argument is given */

	"SET_LINE_LENGTH_FILE",
	"SET_PAGE_LENGTH_FILE",
	"LINE_LENGTH_FILE",
	"PAGE_LENGTH_FILE",
	"NEW_LINE_FILE",
	"SKIP_LINE_FILE",
	"END_OF_LINE_FILE",
	"NEW_PAGE_FILE",
	"SKIP_PAGE_FILE",
	"END_OF_PAGE_FILE",
	"TIO_END_OF_FILE_FILE",
	"SET_COL_FILE",
	"SET_LINE_FILE",
	"COL_FILE",
	"LINE_FILE",
	"PAGE_FILE",
	"GET_CHAR_FILE_ITEM",
	"PUT_CHAR_FILE_ITEM",
	"GET_STRING_FILE_ITEM",
	"PUT_STRING_FILE_ITEM",
	"GET_LINE_FILE",
	"PUT_LINE_FILE",
	"GET_INTEGER_FILE_ITEM",
	"PUT_INTEGER_FILE_ITEM",
	"PUT_INTEGER_STRING",
	"GET_FLOAT_FILE_ITEM",
	"PUT_FLOAT_FILE_ITEM",
	"GET_FIXED_FILE_ITEM",
	"PUT_FIXED_FILE_ITEM",
	"GET_ENUM_FILE_ITEM",
	"PUT_ENUM_FILE_ITEM",

	/* Operations using default input file */

	"GET_CHAR_ITEM",
	"GET_STRING_ITEM",
	"GET_LINE",
	"GET_INTEGER_ITEM",
	"GET_INTEGER_STRING",
	"GET_FLOAT_ITEM",
	"GET_FLOAT_STRING",
	"GET_FIXED_ITEM",
	"GET_FIXED_STRING",
	"GET_ENUM_ITEM",
	"GET_ENUM_STRING",
	"SKIP_LINE",
	"END_OF_LINE",
	"SKIP_PAGE",
	"END_OF_PAGE",
	"TIO_END_OF_FILE",

	/* Operations using default output file */

	"SET_LINE_LENGTH",
	"SET_PAGE_LENGTH",
	"LINE_LENGTH",
	"PAGE_LENGTH",
	"NEW_LINE",
	"NEW_PAGE",
	"SET_COL",
	"SET_LINE",
	"COL",
	"LINE",
	"PAGE",
	"PUT_CHAR_ITEM",
	"PUT_STRING_ITEM",
	"PUT_LINE",
	"PUT_INTEGER_ITEM",
	"PUT_FLOAT_ITEM",
	"PUT_FLOAT_STRING",
	"PUT_FIXED_ITEM",
	"PUT_FIXED_STRING",
	"PUT_ENUM_ITEM",
	"PUT_ENUM_STRING",

	/* Other operations */

	"TIO_CREATE",
	"TIO_OPEN",
	"TIO_CLOSE",
	"TIO_DELETE",
	"TIO_RESET",
	"TIO_RESET_MODE",
	"TIO_MODE",
	"TIO_NAME",
	"TIO_FORM",
	"TIO_IS_OPEN",
	"SET_INPUT",
	"SET_OUTPUT",
	"STANDARD_INPUT",
	"STANDARD_OUTPUT",
	"CURRENT_INPUT",
	"CURRENT_OUTPUT",
	"SIO_CREATE",
	"SIO_OPEN",
	"SIO_CLOSE",
	"SIO_DELETE",
	"SIO_RESET",
	"SIO_RESET_MODE",
	"SIO_MODE",
	"SIO_NAME",
	"SIO_FORM",
	"SIO_IS_OPEN",
	"SIO_READ",
	"SIO_WRITE",
	"SIO_END_OF_FILE",
	"DIO_CREATE",
	"DIO_OPEN",
	"DIO_CLOSE",
	"DIO_DELETE",
	"DIO_RESET",
	"DIO_RESET_MODE",
	"DIO_MODE",
	"DIO_NAME",
	"DIO_FORM",
	"DIO_IS_OPEN",
	"DIO_READ",
	"DIO_READ_FROM",
	"DIO_WRITE",
	"DIO_WRITE_TO",
	"DIO_SET_INDEX",
	"DIO_INDEX",
	"DIO_SIZE",
	"DIO_END_OF_FILE",
	"CLOCK",
	"YEAR",
	"MONTH",
	"DAY",
	"SECONDS",
	"SPLIT",
	"TIME_OF",
	"ADD_TIME_DUR",
	"ADD_DUR_TIME",
	"SUB_TIME_DUR",
	"SUB_TIME_TIME",
	"LT_TIME",
	"LE_TIME",
	"GT_TIME",
	"GE_TIME"
};

char *predef_name(int op)										/*;predef_name*/
{
	/* return name given predef opcode */
	if (op < 1 || op > 130 ) chaos("predef_name failed");
	return pretab[op];
}
