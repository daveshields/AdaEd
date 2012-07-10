/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* gmisc - translation of setl misc.c */

#define GEN

#include "hdr.h"
#include "vars.h"
#include "segment.h"
#include "gvars.h"
#include "ops.h"
#include "slot.h"
#include "dbxprots.h"
#include "exprprots.h"
#include "setprots.h"
#include "genprots.h"
#include "gmainprots.h"
#include "segmentprots.h"
#include "arithprots.h"
#include "libprots.h"
#include "gutilprots.h"
#include "initprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "gmiscprots.h"

static void relay_set_add(Symbol);
static int in_slot_map(Tuple, Symbol);
static Tuple labelmap_def(Symbol);

extern Segment	CODE_SEGMENT, DATA_SEGMENT, DATA_SEGMENT_MAIN;

unsigned int subprog_patch_get(Symbol sym)				/*;subprog_patch_get*/
{
	int	i, n;

	/* search tuple SUBPROG_PATCH for symbol, return*/
	n = tup_size(SUBPROG_PATCH);
	for (i = 1; i <= n; i += 2) {
		if ((Symbol) SUBPROG_PATCH[i] == sym)
			return (unsigned int) SUBPROG_PATCH[i+1];
	}
	return 0; /* is this right or should there be error return?*/
}

void subprog_patch_put(Symbol sym, int off)			/*;subprog_patch_put*/
{
	int	i, n;

	n = tup_size(SUBPROG_PATCH);
	for (i = 1; i <= n; i += 2) {
		if ((Symbol) SUBPROG_PATCH[i] == sym ) {
			SUBPROG_PATCH[i+1] = (char *) off;
			return;
		}
	}
	/* here if need new element */
	SUBPROG_PATCH = tup_exp(SUBPROG_PATCH, n+2);
	SUBPROG_PATCH[n+1] = (char *) sym;
	SUBPROG_PATCH[n+2] = (char *) off;
	/* SUBPROG_PATCH is map as tuple: domain elements are symbols, vales
	 * are integers
	 */
}

void subprog_patch_undef(Symbol sym)		/*;subprog_patch_undef*/
{
	int i, n, j;
	n = tup_size(SUBPROG_PATCH);
	for (i = 1; i <= n; i += 2) {
		if ((Symbol) SUBPROG_PATCH[i] == sym) {
			for (j = i+2; j <= n; j++) 
				SUBPROG_PATCH[j-2] = SUBPROG_PATCH[j];
			SUBPROG_PATCH[0] = (char *) n-2; /* adjust size */
			break;
		}
	}
}

/* Miscelleanous utilities on types */

Symbol base_type(Symbol name)				/*;base_type*/
{
	/*
	 * The base-type of a type-mark is itself, unless the type-mark denotes
	 * a subtype.
	 */

	while (NATURE(name) == na_subtype && TYPE_OF(name) != name)
		name = TYPE_OF(name);
	return name;
}

int is_discrete_type(Symbol name)						/*;is_discrete_type*/
{
	Symbol	btype;

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC :  is_discrete_type") ;

	if (TYPE_OF(name) != (Symbol)0) btype = root_type(name);
	else return FALSE;
	if (btype == symbol_integer
	  || btype == symbol_universal_integer
	  || btype == symbol_discrete_type
	  || btype == symbol_any) return TRUE;
	if (NATURE(btype) == na_enum ) return TRUE;
	return FALSE;
}

int is_unconstrained(Symbol typ)						/*;is_unconstrained*/
{
	Symbol	parent_type;

	switch( NATURE(typ)) {
	case(na_array):
		return TRUE;
	case(na_record):
		return has_discriminant(typ);
	case(na_type):
		parent_type = TYPE_OF(typ);
		if (parent_type == typ)
			return FALSE;
		else
			return is_unconstrained(parent_type);
	default:
		return FALSE;
	}
}

int not_included(Symbol small_type, Symbol large_type)		/*;not_included*/
{
	/*
	 * Checks if the bounds of small_type are (statically) out of those of
	 * large_type.
	 */

	Node	small_low_def, small_high_def, large_low_def, large_high_def;
	Tuple	tup;
	Const	small_low, small_high, large_low, large_high;

	if (large_type == base_type(small_type))
		return FALSE;	 /* even if not static in that case */

	tup = SIGNATURE(small_type);
	small_low_def = (Node) tup[2];
	small_high_def = (Node) tup[3];
	tup = SIGNATURE(large_type);
	large_low_def = (Node) tup[2];
	large_high_def = (Node) tup[3];
	small_low = get_ivalue(small_low_def);
	small_high = get_ivalue(small_high_def);
	large_low = get_ivalue(large_low_def);
	large_high = get_ivalue(large_high_def);
	if (small_low->const_kind == CONST_OM
	  || small_high->const_kind == CONST_OM
	  || large_low->const_kind == CONST_OM
	  || large_high->const_kind == CONST_OM) {
		return TRUE;
	}
	else if (is_fixed_type(large_type) || is_float_type(large_type)) {
		return const_lt(small_low, small_high)
		  && (const_lt(small_low, large_low)
		  || const_gt(small_high, large_high));
	}
	else {
		return const_lt(small_low , small_high)
		  && (const_lt(small_low , large_low)
		  || const_gt(small_high , large_high));
	}
}

#ifndef BINDER
void optional_qual(Symbol source_type, Symbol target_type)	/*;optional_qual*/
{
	Symbol	source_obj_type, target_obj_type;

	/* Generates a qual if necessary. The value is already on top of stack. */
	if (target_type == base_type(source_type))
		;    /* qual never necessary here */
	else if (is_access_type(target_type)) {
		source_obj_type = (Symbol) designated_type(source_type);
		target_obj_type = (Symbol) designated_type(target_type);
		if (target_obj_type != source_obj_type 
		  && target_obj_type != base_type(source_obj_type)) {
			if (is_array_type(target_obj_type)) {
				gen_access_qual(as_qual_index, target_obj_type);
			}
			else if (is_record_type(target_obj_type)) {
				gen_access_qual(as_qual_discr, target_obj_type);
			}
			else {	 /* simple type */
				;  /* No need to qual range */
			}
		}

	}
	else if (is_simple_type(target_type) &&
	    not_included(source_type, target_type)) {
		gen_s(I_QUAL_RANGE, target_type);
	}
}
#endif

int kind_of(Symbol type_name)									/*;kind_of*/
{
	/*
	 * Determines the memory unit addressing mode for the given type.
	 * NOTE: This procedure is the point where the code generator bombs whenever
	 *	 there is something wrong with a type declaration....
	 */

	int		nat, tsiz;

	type_name = root_type(type_name);

#ifdef TRACE
	if (debug_flag)
		gen_trace_symbol("KIND_OF", type_name);
#endif

	nat = NATURE(type_name);
	if (nat == na_array) {
		return mu_dble;
	}
	else if (nat == na_record || nat == na_access) {
		return mu_addr;
	}
	else if (nat == na_package) {
		return mu_byte;
	}
	else if (nat == na_enum) {
		return mu_word;
	}
	else {
		tsiz = TYPE_KIND(type_name);
		if (tsiz == TK_BYTE) {
			return mu_byte;
		}
		else if (tsiz == TK_WORD) {
			return mu_word;
		}
		else if (tsiz == TK_ADDR){
			return mu_addr;
		}
		else if (tsiz == TK_LONG) {
			return mu_long;
		}
		else if (tsiz == TK_XLNG) {
			return mu_xlng;
		}
		else {
			compiler_error_s("Kind_of returning omega. Type name is ",
			  type_name);
			return mu_word; /* mu_word bogus value so can proceed */
		}
	}
}

int length_of(Symbol type_name)						/*;length_of*/
{
	/* gives the number of item in the type, assumed to be a discrete type */

	Node	low, high;
	Tuple	tup;
	Const	low_const, high_const;
	int         bs, bi;
	tup = SIGNATURE(type_name);
	low = (Node) tup[2];
	high = (Node) tup[3];

	low_const = get_ivalue(low);
	high_const = get_ivalue(high);
	if	(low_const->const_kind != CONST_OM
	  && high_const->const_kind != CONST_OM) {
		/*   return  get_ivalue_int(high)-get_ivalue_int(low)+1; */
		bi = get_ivalue_int (low);
		bs = get_ivalue_int (high);
		if (bi > bs)
			return 0;
		else
			return bs - bi + 1;
	}
	else {
		return -1;
	}
}

/* On symbol table */

void new_symbol(Symbol new_name, int new_nature, Symbol new_type,
  Tuple new_signature, Symbol new_alias)				/*;new_symbol*/
{
	NATURE(new_name)	= new_nature;
	TYPE_OF(new_name)	= new_type;
	SIGNATURE(new_name) = new_signature;
	ALIAS(new_name)	= new_alias;
}

/* On addresses */

void reference_of(Symbol name)							/*;reference_of*/
{
	/* The C version returns result in two globals; ref_seg?? and ref_off ?? */

	int	lrmval;

#ifdef SKIP
	REFERENCE_OFFSET = 0; 
	REFERENCE_SEGMENT = 0; /* for initial checkout*/
	return;
#endif

	if (tup_mem((char *) name , PARAMETER_SET)) {
		if (!tup_mem((char *) PC(), CODE_PATCH_SET)) {
			CODE_PATCH_SET = tup_with(CODE_PATCH_SET, (char *)PC());
		}
		/* Parameters always referenced */
		/* from assemble, peep-hole OK. */
		REFERENCE_SEGMENT = 0;
		REFERENCE_OFFSET = local_reference_map_get(name);
	}
	else if (local_reference_map_defined(name)) {
		REFERENCE_SEGMENT = 0;
		REFERENCE_OFFSET = local_reference_map_get(name);
	}
	else if (S_SEGMENT(name) != -1) {
		REFERENCE_SEGMENT = S_SEGMENT(name);
		REFERENCE_OFFSET = S_OFFSET(name);
	}
	else {
		lrmval  =  mu_size(mu_addr) * tup_size(RELAY_SET);
		local_reference_map_put(name, lrmval);
		relay_set_add(name);
		REFERENCE_SEGMENT  = 0;
		REFERENCE_OFFSET = lrmval;
	}
}

static void relay_set_add(Symbol name)					/*;relay_set_add*/
{
	if (!tup_mem((char *) name, RELAY_SET))
		RELAY_SET = tup_with(RELAY_SET, (char *) name);
}

int is_defined(Symbol name)									/*;is_defined*/
{
	if (!local_reference_map_defined(name)) {
		if (S_SEGMENT(name) == -1)
			return FALSE;
	}
	return TRUE;
}

/* next_local_reference and next_global_reference in util.c */

Symbol get_constant_name(Segment item)					/*;get_constant_name*/
{
	/* CONSTANT_MAP is used to detect duplicate instances of constant
	 * For now we disable this check and always generate new reference
	 */

	Symbol	name;

#ifdef TBSN
	if (NO(name :
	== CONSTANT_MAP(item))) {
		name = new_unique_name("constant");
		next_global_reference_segment(name, item);
		CONSTANT_MAP(item) = name;
	}
	return name;
#endif
	name = new_unique_name("constant");
	next_global_reference_segment(name, item);
	return name;
}

void assign_same_reference(Symbol new_name, Symbol old_name)
													/*;assign_same_reference*/
{
	if (tup_mem((char *)old_name , PARAMETER_SET)) {
		PARAMETER_SET	= tup_with(PARAMETER_SET, (char *) new_name);
		ASSOCIATED_SYMBOLS(new_name) = ASSOCIATED_SYMBOLS(old_name);
		local_reference_map_put(new_name, local_reference_map_get(old_name));
	}
	else if (local_reference_map_defined(old_name)) {
		local_reference_map_put(new_name, local_reference_map_get(old_name));
	}
	else if (S_SEGMENT(old_name) != -1) {
		S_SEGMENT(new_name) = S_SEGMENT(old_name);
		S_OFFSET(new_name) = S_OFFSET(old_name);
	}
	else {
		local_reference_map_put(old_name,  mu_size(mu_addr)
		    * tup_size(RELAY_SET));
		relay_set_add(old_name);
		local_reference_map_put(new_name, local_reference_map_get(old_name));
	}
}

/* Slots management */

int select_entry(int a_map_code , Symbol an_item, int a_map_name)
															/*;select_entry*/
{
	/*
	 * finds the entry corresponding to an_item into the slot map a_map.
	 * creates it if not found, and updates OWNED_SLOTS.
	 */

	int indx, isin, nmap, j;
	Tuple	a_map;
	Tuple	utup, stup;
	Slot		slot;

	switch (a_map_code) {
	case SELECT_CODE: 
		a_map = CODE_SLOTS; 
		break;
	case SELECT_DATA: 
		a_map = DATA_SLOTS; 
		break;
	case SELECT_EXCEPTIONS: 
		a_map = EXCEPTION_SLOTS; 
		break;
	default:
#ifdef DEBUG
		printf("a_map_code: %d\n", a_map_code);
#endif
		chaos("select entry bad a_map_code");
	}
	indx = in_slot_map(a_map, an_item);
	if (indx != 0) {
		;
	}
	else if (a_map_name == SLOTS_DATA_BORROWED 
	  || a_map_name == SLOTS_CODE_BORROWED) {
#ifdef ERRMSG
		compiler_error(a_map_name +' slot not present for '+ str an_item);
#endif
		compiler_error("select_entry: slot not present ");
		return 0;
	}
	else {
		nmap  = tup_size(a_map);
		for (indx = init_slots(a_map_name);;) {
			indx += 1;
			isin = FALSE;
			for (j = 1; j <= nmap; j++) {
				slot = (Slot) a_map[j];
				if (slot->slot_number == indx) {
					isin = TRUE;
					break;
				}
			}
			if (isin == FALSE) break;
		}

		slot = slot_new(an_item, indx);
		a_map  = tup_with(a_map, (char *)slot);
		switch (a_map_code) {
		case SELECT_CODE: 
			CODE_SLOTS = a_map; 
			break;
		case SELECT_DATA: 
			DATA_SLOTS = a_map; 
			break;
		case SELECT_EXCEPTIONS: 
			EXCEPTION_SLOTS = a_map; 
			break;
		}

		if (indx > max_index(a_map_name)) {
			if (a_map_name == SLOTS_DATA) {
				compiler_error("Too many compilation units");
			}
			else if(a_map_name == SLOTS_CODE) {
				compiler_error("Too many program units");
			}
			else if (a_map_name == SLOTS_EXCEPTION) {
				compiler_error("Too many exceptions");
			}
			return 0;
		}
	}

	/* In case of a recompilation of an unit, OWNED_SLOTS may not be */
	/* initialized even if index was found in the map. */
	utup = unit_slots_get(unit_number_now);
	stup = (Tuple) utup[a_map_name];
	stup = tup_with(stup, (char *) indx);
	utup[a_map_name] = (char *) stup;
	unit_slots_put(unit_number_now, utup);

	return indx;
}

static int in_slot_map(Tuple tup, Symbol item)				/*;in_slot_map*/
{
	int		i, n;
	int		seq, unt;
	Slot	s;

	n = tup_size(tup);
	unt = S_UNIT(item); 
	seq = S_SEQ(item);
	for (i = 1; i <= n; i++) {
		s = (Slot) tup[i];
		if (unt == s->slot_unit && seq == s->slot_seq)
			return s->slot_number;
	}
	return 0;
}

/* Code selection */

void optional_deref(Symbol type_name)					/*;optional_deref*/
{
	if (is_simple_type(type_name))
		gen_k(I_DEREF, kind_of(type_name));
}

/* On ivalues */

Const get_ivalue(Node node)									/*;get_ivalue*/
{
	/*
	 * returns a scalar ivalue extracted from the expression.
	 * In the case of a rational ivalue, returns the rational representation.
	 * In the case of a real ivalue, returns the integer representation
	 */

	Const	v;
	if (! is_ivalue(node))
		return const_new(CONST_OM);
	v = (Const) N_VAL(node);
	return v;
}

int get_ivalue_int(Node node)								/*;get_ivalue_int*/
{
	/*
	 * returns a scalar ivalue extracted from the expression.
	 * The ivalue must be  one of the following:
	 * 1) integer
	 * 2) universal integer that can be converted to integer.
	 * Otherwise, chaos is noted.
	 * This is used when we suspect an int is always wanted and
	 * want to raise an error if this is not the case.
	 */

	Const	v;
	int n;
	if (! is_ivalue(node)  )
		chaos("get_ivalue_int: arg not ivalue");
	v = (Const) N_VAL(node);
	n = get_const_int(v);
	return n;
}

int get_const_int(Const v)							/*;get_const_int*/
{
	int n = 0;

	/* return value of const if integer, chaos otherwise */
	if (v->const_kind == CONST_INT)
		n = INTV(v);
	else if (v->const_kind == CONST_UINT) {
		/* uint ok if can convert to integer*/
		n = int_toi(UINTV(v));
		if (!arith_overflow)
			 return n;
		chaos("get_ivalue_int: cannot convert uint");
	}
	else
		chaos("get_ivalue: const not int");
	return n;
}

/* Formatted_name */

char *formatted_name(char *unit)					/*;formatted_name*/
{
	char *kind, *unit_kind;

	kind = unit_name_type(unit);
	if (is_subunit(unit))	    unit_kind = "proper body ";
	else if (streq(kind, "sp"))  unit_kind = "package spec ";
	else if (streq(kind, "bo"))  unit_kind = "package body ";
	else if (streq(kind, "ss"))  unit_kind = "subprogram spec ";
	else if (streq(kind, "su"))  unit_kind = "subprogram ";
	else if (streq(kind, "ma"))  unit_kind = "binding unit ";
	else unit_kind = "unit ";
	return strjoin(unit_kind, unit_name_name(unit));
}

/* On expressions */

int size_entry(Symbol entry_name)						/*;size_entry*/
{
	/* Computes the size reserved on the stack for parameters of the entry */

	Tuple	formals;
	Symbol	fname, ftype;
	int		fmode;
	int		addr_size, size;
	Fortup	ft1;

	formals   = SIGNATURE(entry_name);
	addr_size = su_size(TK_ADDR);
	size	     = 0;
	FORTUP(fname = (Symbol), formals, ft1) ;
		fmode = NATURE(fname);
		ftype = TYPE_OF(fname);
		size += addr_size;

		/* scalar out and in out parameters takes 2 stacks locations */
		/* one for returned na_out value, the other for temporary na_in; */
		/* Array addresses are mu_dble. */
		if    ((is_simple_type(ftype) && (fmode != na_in))
	      || is_array_type(ftype)) {
			size += addr_size;
		}
	ENDFORTUP(ft1);

	return size;
}

int is_generated_label(Symbol label_name) 				/*;is_generated_label*/
{
	/*
	 * This procedure look at the first character of the name of a 
	 * label to check if it as been generated by the parser.
	 * Note: This is called only once from expand, and it should be
	 * acceptable to always return FALSE.
	 */

	return *(char *)ORIG_NAME(label_name) == '#';
}

/* Patch_code */

void patch_code(unsigned int location, unsigned int value)		/*;patch_code*/
{
	/*CODE_SEGMENT(location+1) = value;*/
	/* Patch specified location (following one specified) and restore
	 * segment position to end
	 */

	/* move to patch location*/
	segment_set_pos(CODE_SEGMENT, (unsigned) location+1, 0);
	segment_put_word(CODE_SEGMENT, value);
	segment_set_pos(CODE_SEGMENT, 0, 2); /* move to end */
}

void patch_code_byte(int location, int value)			/*;patch_code_byte*/
{
	/* The SETL code to patch a full address takes the form
	 *	CODE_SEGMENT(patch_addr) = base; -- where base is segment number
	 *	patch_code(patch_addr, off); -- where off is offset part of address
	 * Note that patch_code patches after specified location.
	 * patch_code_byte is defined to correspond to first line in above sequence
	 * and patches at the specified location.
	 */

	segment_set_pos(CODE_SEGMENT, location, 0); /* move to location*/
	segment_put_byte(CODE_SEGMENT, value);
	segment_set_pos(CODE_SEGMENT, 0, 2); /* move to end */
}
/* Update_code */

void update_code(int location, int value)					/*;update_code*/
{
	int oval;		/* TBSL: is this unsigned??*/
	/*CODE_SEGMENT(location+1) -= value;*/
	oval = segment_get_off(CODE_SEGMENT, location+1);
	segment_put_off(CODE_SEGMENT, location+1, oval - value);
	segment_set_pos(CODE_SEGMENT, 0, 2); /* move to end */
}

/* Compiler_error */

#ifdef DEBUG
void compiler_error(char *reason)							/*;compiler_error*/
{
	errors++;
	list_hdr(ERR_COMPILER);
	fprintf(MSGFILE, "  %s\n", reason);
	/*PRINTA(GENfile, ERR_COMPILER, ada_line, 0, ada_line, 0, '	'+reason);*/
	if (debug_flag)
		printf("--> %s\n", reason);
	chaos("compiler errror");
}
#endif

/* the following included for compatibility with sem sources */
void errmsg(char *msg, char *lrm, Node node)					/*;errmsg */
{
	user_error(msg);
}

#ifdef TRACE

/* use gen_trace for one with with trace string. If more than one
 * arg, use suffix to indicte argyment type.
 * _node for node
 * _nodes for tuple of nodes
 * _symbol for symbol
 * _symbols for tuple of symbols
 * _relay for tuple of symbols
 * _i for integer (NOT SUED)
 * _c for comment (string constant) (NOT USED)
 */

void gen_trace(char *caller)									/*;gen_trace*/
{
	printf("TRACE %s\n", caller);
}

void gen_trace_node(char *caller, Node node)				/*;gen_trace_node*/
{
	printf("TRACE %s ", caller);
	zpnod(node);
}

void gen_trace_nodes(char *caller, Tuple nodes)			/*;gen_trace_nodes*/
{

	Node	n;
	Fortup	ft1;

	gen_trace(caller);
	FORTUP(n = (Node), nodes, ft1);
		zpnod(n);
	ENDFORTUP(ft1);
}

void gen_trace_symbol(char *caller, Symbol symbol)		/*;gen_trace_symbol*/
{
	printf("TRACE %s ", caller);
	zpsym(symbol);
}

void gen_trace_symbols(char *caller, Tuple symbols)		/*;gen_trace_symbols*/
{

	Symbol	n;
	Fortup	ft1;

	gen_trace(caller);
	FORTUP(n = (Symbol), symbols, ft1);
		zpsym(n);
	ENDFORTUP(ft1);
}

void gen_trace_string(char *caller, char *s)			/*;gen_trace_string*/
{
	printf("TRACE %s %s\n", caller, s);
}

void gen_trace_strings(char *caller, Tuple strings)		/*;gen_trace_strings*/
{
	char	*s;
	Fortup	ft1;

	gen_trace(caller);
	FORTUP(s = (char *), strings, ft1);
		printf("%s\n", s);
	ENDFORTUP(ft1);
}

void gen_trace_units(char *caller, Set uset)				/*;gen_trace_units*/
{
	/* uset is set of unit numbers. print their names */
	Forset fs1;
	int unum;

	gen_trace(caller);
	FORSET(unum = (int), uset, fs1);
		printf("  %s\n", pUnits[unum]->name);
	ENDFORSET(fs1);
}
#endif

void labelmap_put(Symbol sym, int comp, char *val)			/*;labelmap_put*/
{
	Tuple	tup;

	/* set label map value for symbol sym, component comp (one of LABEL_STATIC,
	 * ...), to value val.
	 * using EMAP for labelmap
	 */

	if (!emap_get(sym))
		tup = labelmap_def(sym);
	else
		tup = EMAP_VALUE;
	if (comp<1 || comp>LABEL_SIZE)
		chaos("labelmap_put label code out of range");
	tup[comp] = val;
}

static Tuple labelmap_def(Symbol sym)						/*;labelmap_def*/
{
	Tuple tup;

	tup = tup_new(LABEL_SIZE);
	tup[LABEL_STATIC_DEPTH] = (char *) 0;
	tup[LABEL_POSITION] = (char *) 0;
	tup[LABEL_PATCHES] = (char *) tup_new(0);
	tup[LABEL_EQUAL] = (char *) tup_new(0);
	emap_put(sym, (char *) tup);
	return tup;
}

Tuple labelmap_get(Symbol sym)								/*;labelmap_put*/
{
	/* get label map value for symbol sym, */

	Tuple	tup;

	if (!emap_get(sym)) { /* creat empty entry if not yet defined */
		tup = labelmap_def(sym);
	}
	else {
		tup = EMAP_VALUE;
	}
	if (tup == (Tuple)0) {
#ifdef DEBUG
		zpsym(sym);
#endif
		chaos("labelmap_get label map is null tuple ");
	}
	return tup;
}

Tuple unit_slots_get(int unum)							/*;unit_slots_get*/
{
	int		n;

	n = tup_size(unit_slots);
	if (unum > n)
		chaos("unit_slots_get unit number out of range");
	return (Tuple) unit_slots[unum];
}

void unit_slots_put(int unum, Tuple tup)				/*;unit_slots_put*/
{
	int		n, j, k;
	Tuple	ntup;

	if (unit_slots == (Tuple)0) { /* if never initialized */
		unit_slots = tup_new(0);
	}
	n = tup_size(unit_slots);
	if (unum>n) { /* if need to allocate new slots */
		unit_slots = tup_exp(unit_slots, unum);
		for (j = n + 1; j <= unum; j++) {
			ntup = tup_new(5);
			for (k = 1; k <= 5; k++)
				ntup[k] = (char *) tup_new(0);
			unit_slots[j] = (char *) ntup;
		}
	}
	unit_slots[unum] = (char *) tup;
}

void user_warning(char *s1, char *s2)						/*;user_warning*/
{
	list_hdr(ERR_WARNING);
	fprintf(MSGFILE, "%s %s\n", s1, s2);
}

int is_generic(char *na)									/*;is_generic*/
{
	return tup_memstr(na, late_instances);
}

int is_ancestor(char *na)									/*;is_ancestor*/
{
	return streq(unit_name_names(na), stub_ancestor(unit_name));
}

/* TO_GEN procedures */

void list_hdr(int typ)											/*;list_hdr*/
{
	fprintf(MSGFILE, "%d %d %d %d %d\t", typ, ada_line, 0, ada_line, 0);
}

#ifdef MACHINE_CODE
void to_gen(char *s)											/*;to_gen*/
{
	list_hdr(INFORMATION);
	fprintf(MSGFILE, "%s\n", s);
}

void to_gen_int(char *s, int n)								/*;to_gen_int*/
{
	list_hdr(INFORMATION);
	fprintf(MSGFILE, "%s %d\n", s, n);
}

void to_gen_unam(char *s1, char *name, char *s2)				/*;to_gen_unam*/
{
	/* corresponds to SETL case of two strings with unit_name between them */
	char	s[250];
	sprintf(s, "%s%s%s", s1, name, s2);
	to_gen(s);
}
#endif

void to_list(char *str)											/*;to_list*/
{
	fprintf(MSGFILE, "%d 9999 0 9999 0\t", INFORMATION);
	fprintf(MSGFILE, "%s\n", str);
}
