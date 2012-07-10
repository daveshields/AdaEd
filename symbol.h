/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#ifndef _symbol_h
#define _symbol_h
#include "set.h"

typedef struct Symbol_s *Symbol;

typedef struct Symbol_s
{
	short		nature;		/* one of na_ codes */
	short		s_seq;	/* sequence number within unit */
	short		s_unit; /* unit number */
	short		type_attr;	/* miscellaneous type attributes */
	Symbol		type_of;	/* type */	
	Symbol		scope_of;	/* scope: symbol table pointer */
	Tuple		signature;	/* pointer to tuple, varies by NATURE */
	Set		overloads;
	Declaredmap	declared;
	Symbol		alias;
	char		*orig_name;
	char		*misc;
    /* remaining fields used only by generator */
    /* we use short intending 16 bits */
	short		type_kind;
	short		type_size;
	Symbol		init_proc;
	Tuple		associated_symbols;  /* for _type, etc */
	short		s_segment; /* REFERENCE_MAP segment */
	short		s_offset; /* REFERENCE_MAP offset */
	Tuple       rcinfo;
	Tuple       repr;
	short       forced;

} Symbol_s;

/* s_offset was originally unsigned. However, processing of variant
 * records currently requires that it be signed. Also, since currently
 * using words as basic storage unit,there is no great loss in making it
 * signed.	ds	11-18-85
 */
/*
The nature field gives the kind of the entry, i.e., it serves as a
discriminant. The type_of field is a pointer to a symbol entry giving
the type. 
In the SETL source, the field names correspond to maps and are
often referenced in form
	NATURE(x)   TYPE_OF(x)	 etc
We require that such usage use upper case and define macros to
avoid the need to translate all such instances. Note however that
instances of lower-case names for fields will have to be translated
	nature(x) -> NATURE(x)
*/

#define NATURE(x)	((x)->nature)
#define TYPE_OF(x)	((x)->type_of)
#define ALIAS(x)	((x)->alias)
#define SIGNATURE(x)	((x)->signature)
#define SCOPE_OF(x)	((x)->scope_of)
#define OVERLOADS(x)	((x)->overloads)
#define DECLARED(x)	((x)->declared)
#define ORIG_NAME(x)	((x)->orig_name)
#define S_SEQ(x)	((x)->s_seq)
#define S_UNIT(x)	((x)->s_unit)
#define TYPE_ATTR(x)	((x)->type_attr)
#define MISC(x)		((x)->misc)
#define TYPE_KIND(x)	((x)->type_kind)
#define TYPE_SIZE(x)	((x)->type_size)
#define INIT_PROC(x)	((x)->init_proc)
#define ASSOCIATED_SYMBOLS(x) ((x)->associated_symbols)
#define S_SEGMENT(x) ((x)->s_segment)
#define S_OFFSET(x) ((x)->s_offset)
#define RCINFO(x) ((x)->rcinfo)
#define FORCED(x) ((x)->forced)
#define REPR(x) ((x)->repr)

#endif
