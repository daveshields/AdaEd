/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#define GEN

#include "hdr.h"
#include "vars.h"
#include "segment.h"
#include "gvars.h"
#include "setprots.h"
#include "segmentprots.h"
#include "dbxprots.h"
#include "miscprots.h"
#include "gmiscprots.h"
#include "smiscprots.h"
#include "gutilprots.h"

static short nature_root_type(Symbol);

extern Tuple segment_map_new(), segment_map_put();
extern Segment segment_map_get();
extern Segment	CODE_SEGMENT, DATA_SEGMENT, DATA_SEGMENT_MAIN;

/* create dummy entry for p (np is string with name of p)
 * and call chaos if p is called
 */
#define undone(p, np) p() { chaos(strjoin(np, " not implemented")); }

int ada_bool(int x)												/*;ada_bool*/
{
	return (x != 0 ? 1 : 0) ;
}

int assoc_symbol_exists(Symbol sym, int aname)			/*;assoc_symbol_exists*/
{
	/* return TRUE if assoc_symbol_get would succeed, FALSE otherwise */

	Tuple	tup;

	tup = ASSOCIATED_SYMBOLS(sym);
	if (tup == (Tuple)0)
		return FALSE;
	else
		return (tup[aname] != (char *)0);
}

Symbol assoc_symbol_get(Symbol sym, int aname)			/*;assoc_symbol_get*/
{
	/* Enter asym as associated symbol of symbol sym. Aname is code
	 * definining position in tuple of associated symbols. The tuple
	 * is allocated if not already defined 
	 */

	Tuple	tup;

	tup = ASSOCIATED_SYMBOLS(sym);
	if (tup == (Tuple)0)	/* if not allocated*/
		chaos("assoc_symbol_get: tuple not allocated");
	if (tup_size(tup)<aname)
		chaos("associate_symbol_get: index out of range");
	if (tup[aname] == (char *)0)
		chaos("assoc_symbol_get: symbol not present");
	return (Symbol) tup[aname];
}

void assoc_symbol_put(Symbol sym, int aname, Symbol asym) /*;assoc_symbol_put*/
{
	/* Enter asym as associated symbol of symbol sym. Aname is code
	 * definining position in tuple of associated symbols. The tuple
	 * is allocated if not already defined 
	 */

	Tuple	tup;

	tup = ASSOCIATED_SYMBOLS(sym);
	if (tup == (Tuple)0) { /* if need new tuple */
		/* allocate three entries for now, should allocate proper count later */
		tup = tup_new(3);
		tup[1] = (char *)0;
		tup[2] = (char *)0;
		tup[3] = (char *)0;
	}
	if (tup_size(tup) < aname)
		chaos("associate_symbol_put: index out of range");
	tup[aname] = (char *) asym;
	ASSOCIATED_SYMBOLS(sym) = tup;
}

#ifdef DEBUG
/* Calls to COMPILER_ERROR in SETL are translated to calls to
 * commpiler_error in C. Where the SETL version builds up a string
 * the C version adds a suffix to indicate argument type. For example
 * compiler_error_n(s, n) to pass node. The case compiler_error_k is
 * used to pass node for which the SETL version has
 *	COMPILER_ERROR(s  + str N_KIND(node)
 * This is written in C as
 *	compiler_error_k(s, node)
 * These are defined for DEBUG (base) version only. In the export version,
 * they are redefined as macros (in ghdr.c) to call procedure
 * exit_internal_error().
 */

void compiler_error_k(char *s, Node node) 				/*;compiler_error_k*/
{
	printf("compiler error: %s\n", s); 
	zpnod(node);
	errors++;
	chaos("compiler_error_k");
}

void compiler_error_c(char *s, Tuple t)					/*;compiler_error_c*/
{
	/* second arg is tuple corresponding to constraint*/
	printf("compiler_error_c: %s\n", s);
	errors++;
	chaos("compile_error_c");
}

void compiler_error_s(char *s, Symbol sym)				/*;compiler_error_s*/
{
	/* second argument is symbol */
	printf("compiler_error_s: %s\n", s); 
	zpsym(sym);
	errors++;
	chaos("compiler_error_s");
}
#endif

Tuple discriminant_list_get(Symbol record)			/*;discriminant_list_get*/
{
	/* DISCRIMINANT_LIST(record); SIGNATURE(root_type(record))(2)  */
	Tuple	tup;
	tup = SIGNATURE(root_type(record));
	return (Tuple) tup[3];
}

/* The SETL map EMAP is accessed in C by the following procedures:
 *	 emap_get(symbol)
 *	emap_put(symbol, value)
 *  Note that emap_get returns TRUE if EMAP defined for the argument,
 *  and sets EMAP_VALUE to the value, or returns FALSE if the value
 *  not defined.
 *  The SETL sequence
 *	EMAP(s) = OM;
 *  is translated as
 *	emap_undef(s);
 */

int emap_get(Symbol sym)									/*;emap_get*/
{
	int	i, n;
	n = tup_size(EMAP);
	for (i = 1; i <= n; i += 2) {
		if (EMAP[i] == (char *) sym) {
			EMAP_VALUE = (Tuple) EMAP[i+1];
			return TRUE;
		}
	}
	return FALSE;
}

void emap_put(Symbol sym, char *val)			/*;emap_put*/
{
	int		i, n;
	n = tup_size(EMAP);
	for (i = 1; i <= n; i += 2) {
		if (EMAP[i] == (char *) sym) {
			EMAP[i+1] = val;
			return;
		}
	}
	EMAP = tup_with(EMAP, (char *) sym); /* add as new entry */
	EMAP = tup_with(EMAP, (char *) val); /* add new value */
}

void emap_undef(Symbol s)									/*;emap_undef*/
{
	int	i, n, j;

	n = tup_size(EMAP);
	for (i = 1; i <= n; i += 2) {
		if (EMAP[i] == (char *) s) {
			/* if defined here, move down later entries*/
			for (j = i; j < n - 1; j ++) {
				EMAP[j] = EMAP[j+2];
			}
		}
	}
}

void generate_object(Symbol s)							/*;generate_object*/
{
	if (!tup_mem((char *)s, GENERATED_OBJECTS))
		GENERATED_OBJECTS = tup_with(GENERATED_OBJECTS, (char *) s);
}

Tuple get_constraint(Symbol type_name)					/*;get_constraint*/
{
	/* constraints on access types are now also tuples in the C version.*/
	if (is_array(type_name) || NATURE(base_type(type_name)) == na_subtype) {
		Tuple tup; /* TBSL: make this a static constant */
		tup = tup_new(5);
		tup[1] = (char *)co_index;
		tup[2] = (char *)OPT_NODE;
		tup[3] = (char *)OPT_NODE;
		return tup;
	}
	else {
		return SIGNATURE(type_name);
	}
}

Symbol get_type(Node node)										/*;get_type*/
{
	int	nk;
	Symbol	sym;

	nk = N_KIND(node);
	if (nk == as_simple_name || nk == as_subtype_indic) {
		sym = N_UNQ(node);
		if (sym == (Symbol)0) {
#ifdef DEBUG
			zpnod(node);
#endif
			chaos("get_type: N_UNQ not defined for node");
		}
		else {
			sym =  TYPE_OF(sym);
		}
	}
	else {
		sym = N_TYPE(node);
	}
	return sym;
}

int has_discriminant(Symbol typ)						/*;has_discriminant*/
{
	/* Note that has_discriminant is adasem macro that is NOT same as
	 * discriminant_list macro defined in adagen. Calls of the latter must
	 * be translated as discriminant_list_get.
	 */
	Tuple	tup;
	tup = discriminant_list_get(typ);
	if (tup == (Tuple)0) return FALSE;
	return tup_size(tup) > 0;
}

int has_static_size(Symbol typ)							/*;has_static_size*/
{
	return size_of(typ) >= 0;
}

int is_access_type(Symbol typ)							/*;is_access_type*/
{
	return nature_root_type(typ) == na_access;
}

int is_aggregate(Node node)									/*;is_aggregate*/
{
	register int	nk;
	nk = N_KIND(node);
	return nk == as_array_aggregate || nk == as_array_ivalue
	  ||  nk == as_record_aggregate || nk == as_record_ivalue;
}

int is_array_type(Symbol typ)							/*;is_array_type*/
{
	return nature_root_type(typ) == na_array;
}

int is_entry_type(Symbol typ)								/*;is_entry_type*/
{
	return NATURE(typ) == na_entry_former;
}

int is_enumeration_type(Symbol typ)						/*;is_enumeration_type*/
{
	return NATURE(root_type(typ)) == na_enum;
}

int is_float_type(Symbol typ)								/*;is_float_type*/
{
	Tuple	tup;
	tup = SIGNATURE(typ);
	return (int)tup[1] == co_digits;
}

int is_formal_parameter(Symbol sym)					/*;is_formal_parameter*/
{
	register int	na;
	int                 s_n, found;
	Symbol              same_sym, sym_scope;
	Fortup              ft1;

	na = NATURE(sym);
	return ((na == na_in || na == na_inout || na == na_out)
			&& assoc_symbol_exists(sym,FORMAL_TEMPLATE) );
}

int is_global(Symbol sym)										/*;is_global*/
{
	return sym->s_segment != -1;
}

int is_integer_type(Symbol typ)								/*;is_integer_type*/
{
	return root_type(typ) == symbol_integer;
}

int is_ivalue(Node node)										/*;is_ivalue*/
{
	int	nk = N_KIND(node);
	return nk == as_ivalue || nk == as_int_literal || nk == as_string_ivalue
	  || nk == as_real_literal || nk == as_array_ivalue
	  || nk == as_record_ivalue;
}

int is_object(Node node)										/*;is_object*/
{
	int	nk = N_KIND(node);
	return nk == as_simple_name || nk == as_null || nk == as_name
	  || nk == as_slice || nk == as_index || nk == as_selector;
}

int is_record_subtype(Symbol typ)						/*;is_record_subtype*/
{
	return is_record_type(typ) && NATURE(typ) == na_subtype;
}

int is_record_type(Symbol typ)								/*;is_record_type*/
{
	return nature_root_type(typ) == na_record;
}

int is_renaming(Symbol sym)									/*;is_renaming*/
{
	return ALIAS(sym) != (Symbol)0;
}

int is_simple_name(Node node)								/*;is_simple_name*/
{
	int nk = N_KIND(node);
	return nk == as_simple_name || nk == as_null || nk == as_name;
}

int is_simple_type(Symbol typ)								/*;is_simple_type*/
{
	return nature_root_type(typ) != na_array
	  && nature_root_type(typ) != na_record;
}

int is_static_type(Symbol typ)								/*;is_static_type*/
{
	return is_global(typ) && has_static_size(typ);
}

int local_reference_map_defined(Symbol sym)		/*;local_reference_map_defined*/
{
	/* return TRUE if local_reference_map defined for sym, else FALSE */
	int		i, n;
	n = tup_size(LOCAL_REFERENCE_MAP);
	for (i = 1; i <= n; i += 2) {
		if (LOCAL_REFERENCE_MAP[i] == (char *) sym)
			return TRUE;
	}
	return FALSE;
}

Tuple local_reference_map_new()					/*;local_reference_map_new*/
{
	return tup_new(0);
}

unsigned int local_reference_map_get(Symbol sym)	/*;local_reference_map_get*/
{
	int		i, n;
	n = tup_size(LOCAL_REFERENCE_MAP);
	for (i = 1; i <= n; i += 2) {
		if (LOCAL_REFERENCE_MAP[i] == (char *) sym)
			return (unsigned int) LOCAL_REFERENCE_MAP[i+1];
	}
	chaos("local_reference_map_get unable to find value "); 
	return 0;
}

void local_reference_map_put(Symbol sym, int off)	/*;local_reference_map_put*/
{
	int		i, n;
	n = tup_size(LOCAL_REFERENCE_MAP);
	for (i = 1; i <= n; i += 2) {
		if (LOCAL_REFERENCE_MAP[i] == (char *)sym) {
			LOCAL_REFERENCE_MAP[i+1] = (char *) off;
			return;
		}
	}
	LOCAL_REFERENCE_MAP = tup_exp(LOCAL_REFERENCE_MAP, n+2);
	LOCAL_REFERENCE_MAP[n+1] = (char *) sym;
	LOCAL_REFERENCE_MAP[n+2] = (char *) off;
}

int mu_size(int mutyp)											/*;mu_size*/
{
	/* This procedure returns the number of storage units required for
	 * the memory type given by mutyp, one of the mu_ codes.
	 */
#ifdef WORDSIZE16
	switch (mutyp) {
	case(mu_byte):
	case(mu_word):
		return 1;
	case(mu_addr):
	case(mu_long):
	case(mu_xlng): /* check that mu_xlng value right */
		return 2; /* check desired size */
	case(mu_dble):
		return 4;
	default:
		chaos("mu_size: bad argument"); 
		return 0;
	}
#else
	switch (mutyp) {
	case(mu_byte):
	case(mu_word):
	case(mu_long):
		return 1;
	case(mu_addr):
	case(mu_xlng): /* check that mu_xlng value right */
		return 2; /* check desired size */
	case(mu_dble):
		return 4;
	default:
		chaos("mu_size: bad argument"); 
		return 0;
	}
#endif
}

int su_size(int ktyp)												/*;su_size*/
{
	/* This procedure returns the number of storage units required for
	 * the memory type given by ktyp, one of the TK_ codes.
	 */
#ifdef WORDSIZE16
	switch (ktyp) {
	case TK_BYTE:
	case TK_WORD: 
		return 1;
	case TK_LONG:
	case TK_XLNG:
	case TK_ADDR: 
		return 2;
	case TK_DBLE: 
		return 4;
	default:
		chaos("su_size: bad argument");
		return 0; /* for the sake of lint */
	}
#else
	switch (ktyp) {
	case TK_BYTE:
	case TK_LONG:
	case TK_WORD: 
		return 1;
	case TK_XLNG:
	case TK_ADDR: 
		return 2;
	case TK_DBLE: 
		return 4;/* dble is double address, not C double */
	default:
		chaos("su_size: bad argument");
		return 0; /* for the sake of lint */
	}
#endif
}

void next_local_reference(Symbol name)				/*;next_local_reference*/
{
	LAST_OFFSET		    -= mu_size(mu_addr);
	local_reference_map_put(name, LAST_OFFSET);
}

void next_global_reference_def(Symbol name)		/*;next_global_reference_def*/
{
	/* begin definition of initial data for specified symbol at end
	 * of currrent data segment.
	 */

#ifdef MACHINE_CODE
	Gref	gref;
#endif
	S_SEGMENT(name) = CURRENT_DATA_SEGMENT;
	S_OFFSET(name) = DATA_SEGMENT->seg_maxpos;
	/*REFERENCE_MAP(name) = [CURRENT_DATA_SEGMENT, #DATA_SEGMENT+1];*/
#ifdef MACHINE_CODE
	if (list_code) { /* save for printout */
		gref = (Gref) emalloct(sizeof(Gref_s), "gref");
		gref->gref_sym = name;
		gref->gref_seg = CURRENT_DATA_SEGMENT;
		gref->gref_off = DATA_SEGMENT->seg_maxpos;
		/*n = tup_size(global_reference_tuple);*/
		global_reference_tuple = tup_with(global_reference_tuple, (char *)gref);
	}
#endif
}

void next_global_reference_r(Symbol sym, int seg, unsigned int off)
													/*;next_global_reference_r*/
{
	/* need to extend DATA_SEGMENT with seg and off */

	next_global_reference_def(sym);
	segment_put_word(DATA_SEGMENT, seg);
	segment_put_word(DATA_SEGMENT, off);

}

void next_global_reference_segment(Symbol sym, Segment seg)
											/*;next_global_reference_segment*/
{
	/* install segment seg as next global reference */

	next_global_reference_def(sym);
	segment_append(DATA_SEGMENT, seg);
}

void next_global_reference_template(Symbol sym, Segment seg)
											/*;next_global_reference_template*/
{
	next_global_reference_segment(sym, seg);
}

void next_global_reference_z(Symbol sym)			/*;next_global_reference_z*/
{
	/* This corresponds to SETL case next_global_reference(sym, [0, 0]);]
	 * which we translate to next_global_reference_r for now, though
	 * the correctness of this translation needs to be checked
	 */

	next_global_reference_def(sym);
	segment_put_word(DATA_SEGMENT, 0);
	segment_put_word(DATA_SEGMENT, 0);
}

void next_global_reference_word(Symbol sym, int w)
												/*;next_global_reference_word*/
{
	/* This corresponds to SETL case of adding value [n] where n is assumed
	 * to take only a word.
	 */

	next_global_reference_def(sym);
	segment_put_word(DATA_SEGMENT, w);
}

Symbol new_unique_name(char *s)							/*;new_unique_name*/
{
	/* TBSL: see if this is right translation?  ds  3-12-85 */
	/* If list_code on, then create ORIG_NAME from argument by appending
	 * sequence number
	 */
#ifdef MACHINE_CODE
	Symbol	sym;
	char	seq[10];

	sym = sym_new(na_void);
	sprintf(seq, "#%d", S_SEQ(sym));
	ORIG_NAME(sym) = (s != (char *)0) ? strjoin(s, seq) : strjoin(seq, "");
	return sym;
#else
	return sym_new(na_void);
#endif
}

static short nature_root_type(Symbol typ)				/*;nature_root_type*/
{
	Symbol sym;

	if (typ == (Symbol)0)
		chaos("gutil.c : nature_root_type argument null");

	sym = root_type(typ);

	if (sym == (Symbol)0)
		chaos("gutil.c : nature_root_type, root_type of arg null");

	return NATURE(sym);
}

Segment segment_map_get(Tuple tup, int sn)				/*;segment_map_get*/
{
	/* tup is segment map, sn is segment number */

	int		i, n;

	n = tup_size(tup);
	for (i = 1; i<n; i += 2) {
		if ((int) tup[i] == sn)
			return (Segment) tup[i+1];
	}
	return (Segment) 0;
}

Tuple segment_map_put(Tuple tup, int sn, Segment seg)		/*;segment_map_put*/
{
	/* tup is segment map, sn is segment number */

	int		i, n;

	n = tup_size(tup);
	for (i = 1; i<n; i += 2) {
		if ((int) tup[i] == sn) {
			tup[i+1] = (char *) seg;
			return tup;
		}
	}
	/* here if no entry, make new one, possible reallocating tuple */
	tup = tup_exp(tup, n+2);
	tup[n+1] = (char *) sn;
	tup[n+2] = (char *) seg;
	return tup;
}

Const	small_of(Symbol typ)									/*;small_of*/
{
	/* It returns const, that should always be rational and so
	 * perhaps should insert check here that this holds	ds 7-1-85*/
	Tuple tup = SIGNATURE(typ);
	return get_ivalue((Node)tup[5]);
}
