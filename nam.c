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
#include "gvars.h"
#include "ops.h"
#include "segment.h"
#include "setprots.h"
#include "genprots.h"
#include "smiscprots.h"
#include "exprprots.h"
#include "maincaseprots.h"
#include "gmiscprots.h"
#include "gutilprots.h"
#include "namprots.h"

/* changes
 * 13-mar-85	shields
 * change 'index_type' to 'indx_type' since index_type is macro in sem.
 */

/*
 *T+ Chapter 4: Names and Expressions
 *  Object expressions (used for left-hand sides) is processed
 *  by GEN_ADDRESS, value expressions (used as "right-hand sides")
 *  are processed by GEN_VALUE.
 *
 *   At run-time, the stack contains addresses of objects, but values
 *   are represented either by the actual value for simple types, or
 *   by pointers to data-segments for composite types.
 *
 *   The addresses (or pointers) are usually a pair of unsigned
 *   integers: ( data_segment number, offset in that segment), except
 *   for array objects and values, for which an address consists of
 *   two such pairs,  ( address of array, address of descriptor ).
 *
 *  The format of objects on the stack at run-time are one of the
 *  following (this will be called the "kind" of an object).
 *
 *   mu_byte : for boolean, short_integer, enumeration,
 *             record field number, task
 *
 *   mu_word : for integer, or for an offset
 *
 *   mu_addr : for an absolute address (seg. number + offset)
 *
 *   mu_long : for long_integer and floating-point real numbers
 *
 *   mu_dble : for a double address (array reference)
 *
 *   mu_xlng : for long_float and fixed points requiring a large
 *            mantissa
 *
 *
 *  The function size_of(type) returns the size (in bytes) occupied
 *  by one value of the type 'type'. The function kind_of(type) returns
 *  the kind of stack reference of an object (i.e. mu_byte, mu_word,
 *  mu_dble or mu_addr if the object is not a simple one (or an access).
 */

/* Object evaluation */
void gen_address(Node node)										/*;gen_address*/
{
	/*
	 *  This procedure generates code for the o_expressions
	 *  or, in other words, the left-handsides.
	 */

	Node   pre_node, array_node, range_node, lbd_node, ubd_node, record_node,
	  field_node, id_node;
	Symbol	node_name, type_name, record_name, record_type,
	  field_name, comp_type, proc_name, return_type;
	int		f_off, bse, off, nk;
	Fortup	ft1;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("GEN_ADDRESS", node);
#endif

	while (N_KIND(node) == as_insert) {
		FORTUP(pre_node=(Node), N_LIST(node), ft1);
			compile(pre_node);
		ENDFORTUP(ft1);
		node = N_AST1(node);
	}

	node_name = N_UNQ(node);
	if (is_simple_name(node)) {
		type_name = get_type(node);
		if (is_renaming(node_name))
			gen_ks(I_PUSH, mu_addr, node_name);
		else
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, node_name);

		/* Arrays are treated in a different manner, depending on their */
		/* nature: parameters, constants, variables... */
		if (is_array_type(type_name)) {
			if (is_formal_parameter(node_name)) {
				type_name = assoc_symbol_get(node_name, FORMAL_TEMPLATE);
			}
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
		}

	}
	else {
		switch (nk = N_KIND(node)) {
		case as_raise:
			compile(node);
			break;

		case as_index:
			gen_subscript(node);
			break;

		case as_slice:
			array_node = N_AST1(node);
			range_node = N_AST2(node);
			/*range_name = N_UNQ(range_node); -- never used   ds 7-8-85 */

			/* Note: case of type simple name changed into range attribute */
			/* by expander */
			if (N_KIND(range_node) == as_attribute) {
				gen_attribute(range_node);
			}
			else { /* range */
				lbd_node = N_AST1(range_node);
				ubd_node = N_AST2(range_node);
				gen_value(lbd_node);
				gen_value(ubd_node);
			}
			if (N_KIND(array_node) == as_attribute) {
				gen_attribute(array_node);
			}
			else {
				gen_address(array_node);
			}
			gen(I_ARRAY_SLICE);
			break;

		case as_selector:
			record_node = N_AST1(node);
			field_node = N_AST2(node);
			record_name = N_UNQ(record_node);
			record_type = get_type(record_node);
			field_name = N_UNQ(field_node);
			f_off = FIELD_OFFSET(field_name);
			if (f_off >= 0 &&
			  ((! has_discriminant(record_type))
			  || NATURE(field_name) == na_discriminant)){
				if (is_simple_name(record_node)
				  && !(is_renaming(record_name)) && is_global(record_name)) {
					reference_of(record_name);
					bse = REFERENCE_SEGMENT;
					off = REFERENCE_OFFSET;
					/* The SETL version has generate(I_PUSH_IMMEDIATE, mu_addr,
					 *  ref, field_name);
					 * which we translate as (I_PUSH_EFFECTIVE_ADDRESS ...
					 * ref       = [bse, off+f_off];
					 * Replace use of explicit ref by PUSH_IMMEDIATE
					 */
					/*  gen_rc(I_PUSH_IMMEDIATE, explicit_ref_new(bse,
					 *   off+f_off), "");
					 */
					gen_kv(I_PUSH_IMMEDIATE, mu_word, int_const(bse));
					gen_kv(I_PUSH_IMMEDIATE, mu_word, int_const(off+f_off));
				}
				else {
					gen_address(record_node);
					if (f_off != 0 ) {
						gen_ki(I_ADD_IMMEDIATE, mu_word, f_off);
					}
				}
				if (is_array_type(comp_type=TYPE_OF(field_name))) {
					gen_s(I_PUSH_EFFECTIVE_ADDRESS, comp_type);
				}
			}
			else {
				gen_address(record_node);
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, record_type);
				/* translating following assuming field_name is comment part of
				 *-- instruction		ds	7-5-86
				 * 		gen_i(I_SELECT, FIELD_NUMBER(field_name), field_name);
				 */
				gen_i(I_SELECT, (int) FIELD_NUMBER(field_name));
			}
			break;

		case as_all:
			id_node = N_AST1(node);
			gen_value(id_node);
			if (is_array_type(N_TYPE(node)))
				gen_k(I_DEREF, mu_dble);
			break;

		case as_call:
			id_node   = N_AST1(node);
			proc_name   = N_UNQ(id_node);
			return_type = TYPE_OF(proc_name);
			gen_kc(I_DUPLICATE, kind_of(return_type), "place holder");
			compile(node);  	 /* processed from now as a procedure call */
			break;

		case as_un_op:
			gen_unary(node);
			break;

		case as_op:
			gen_binary(node);
			break;

		case as_string_ivalue:
			gen_value(node);
			break;

		default:
			compiler_error_k("GEN_ADDRESS called with kind ", node);
		}
	}
}

/* 4.1.1: subscripting */

void gen_subscript(Node node)								/*;gen_subscript*/
{
	Symbol	comp_type;
	Node	index_name, array_node;
	Node	index_list_node, subscript;
	Tuple	index_type_list, subscripts, tup;
	Symbol	array_name, array_type;
	int		optimized;
	int		index, seg, offset;
	Fortup	ft1;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("GEN_SUBSCRIPT", node);
#endif

	array_node = N_AST1(node);
	index_list_node = N_AST2(node);
	array_name = N_UNQ(array_node);
	array_type = get_type(array_node);
	tup = SIGNATURE(array_type);
	index_type_list = (Tuple) tup[1];
	comp_type = (Symbol) tup[2];
	/* need tup_copy since subscripts used in tup_fromb below */
	subscripts = tup_copy(N_LIST(index_list_node));

	/*
	 *  Before applying the brute force method of the 'do-it-all' instruction
	 *  "subscript", which can solve any case, some optimizations will be
	 *  attempted.
	 *
	 *  First, we try to compute the address of the indexed element directly,
	 *  when subscripts are immediate values and the index check can be done
	 *  at compile time:
	 */

	if ((Symbol)index_type_list[1] == symbol_none) {
		optimized = FALSE;
	}
	else if (!(is_unconstrained(array_type))) {
		index     = compute_index(subscripts, index_type_list);
		optimized = index != -1;
		if (optimized) {
			if (has_static_size(comp_type)) {
				index = index * size_of(comp_type);
				if (is_simple_name(array_node) && !is_renaming(array_name) ) {
					if (is_global(array_name)) {
						reference_of(array_name);
						seg = REFERENCE_SEGMENT;
						offset = REFERENCE_OFFSET;
						/*gen_todo(I_PUSH_EFFECTIVE_ADDRESS,[seg, offset+index],
						 *   array_name + '(" + str(get_ivalue(subscripts(1)))
						 *      +/ [', '+str(get_ivalue(subscripts(i))):
						 *                  i in [2..#subscripts] ]
						 *      + ")' );
						 */
						gen_rc(I_PUSH_EFFECTIVE_ADDRESS, explicit_ref_new(seg,
						  offset+index), "");
					}
					else {
						gen_s(I_PUSH_EFFECTIVE_ADDRESS, array_name);
						if (index != 0)
							gen_kic(I_ADD_IMMEDIATE, mu_word, index, "offset");
					}
				}
				else {
					gen_address(array_node);
					gen_ks(I_DISCARD_ADDR, 1, array_type);
					if (index != 0)
						gen_ki(I_ADD_IMMEDIATE, mu_word, index);
				}
			}
			else {
				optimized = FALSE;
			}
		}
	}
	else {
		optimized = FALSE;
	}

	/*
	 *  Nothing worked, we are left with the worse case, solved by the
	 *  "subscript" instruction
	 */

	if (!optimized) {
		FORTUP( index_name=(Node), index_type_list, ft1);
			subscript = (Node) tup_fromb(subscripts);
			gen_value(subscript) ;
		ENDFORTUP(ft1);
		gen_address(array_node);
		gen(I_SUBSCRIPT);
	}

	if (is_array_type(comp_type)) {
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, comp_type);
	}
}

int compute_index(Tuple subscript_list_arg, Tuple index_list_arg)
															/*;compute_index*/
{
	/* Evaluate mono-dimensional offset from the given subscripts */

	Node	subscript, low_node, high_node;
	Symbol	indx_type;
	int		ndex, delta; /* use ndex for index, index is builtin */
	int         sb_val, lw_val, hg_val;
	Tuple	tup;
	Const	lw, hg, sb;
	Tuple	subscript_list, index_list;

	/* copy arguments - needed since they are used desctructively in
     * tup_frome calls below
     */
	subscript_list = tup_copy(subscript_list_arg);
	index_list = tup_copy(index_list_arg);
	ndex = 0;
	delta = 1;
	while (tup_size(index_list)) {
		indx_type = (Symbol) tup_frome(index_list);
		subscript  = (Node) tup_frome(subscript_list);
		tup = SIGNATURE(indx_type);
		low_node = (Node) tup[2];
		high_node = (Node) tup[3];
		lw = get_ivalue(low_node);
		hg = get_ivalue(high_node);
		sb = get_ivalue(subscript);
		if (!( lw->const_kind != CONST_OM   && hg->const_kind != CONST_OM
		  && sb->const_kind != CONST_OM)) {
			tup_free(subscript_list); 
			tup_free(index_list);
			return -1;
		}
		sb_val = INTV(sb);
		lw_val = INTV(lw);
		hg_val = INTV(hg);
		if (sb_val<lw_val ||  sb_val>hg_val) {
			/* here, raise constraint_error */
			gen_s(I_LOAD_EXCEPTION_REGISTER, symbol_constraint_error);
			gen(I_RAISE);
			tup_free(subscript_list); 
			tup_free(index_list);
			return -1;
		}
		ndex += delta*(sb_val-lw_val);
		delta *= (hg_val-lw_val+1);
	}
	tup_free(subscript_list); 
	tup_free(index_list);
	return ndex;
}
