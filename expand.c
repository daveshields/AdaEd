/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#define GEN

#include "hdr.h"
#include "libhdr.h"
#include "vars.h"
#include "gvars.h"
#include "attr.h"
#include "slot.h"
#include "segment.h"
#include "setprots.h"
#include "langprots.h"
#include "initprots.h"
#include "initobjprots.h"
#include "dbxprots.h"
#include "miscprots.h"
#include "utilprots.h"
#include "glibprots.h"
#include "readprots.h"
#include "libprots.h"
#include "arithprots.h"
#include "librprots.h"
#include "gnodesprots.h"
#include "gmiscprots.h"
#include "gutilprots.h"
#include "aggrprots.h"
#include "chapprots.h"
#include "smiscprots.h"
#include "gmainprots.h"
#include "expandprots.h"

void expand(Node node)												/*;expand*/
{
	/*
	 * Expander
	 * Performs a set of semantic transformations on the tree
	 * in order to simplify the job for the code generator.
	 * Some semantic optimizations are performed too.
	 * IMPORTANT: 
	 *    expand must not be called twice on the same structure, as
	 *    for some kinds of nodes, the format before expand is
	 *    different from the format after expand. A special problem
	 *    arises for aggregates, where already expanded structures
	 *    (subaggregates) are part of a not yet expanded structure
	 *    (assignment to enclosing structure) that must be expanded.
	 *    a special node, as_expanded, is used to block double
	 *    expansion in that case.
	 */

	Fortup      ft1, ft2;
	Tuple       tup, tup1, tup2;
	Symbolmap   instance_map, type_map;
	Node        node1, node2, node3, node4;
	Symbol      sym1, sym2, sym3, sym4;
	int         nk, cboolean;
	Const       lv;
	Unitdecl    ud;

	/* TBSL remove the following declarations */
	Const       lbd_1, ubd_1, lbd_2, ubd_2;
	int         ubd_1_val, ubd_2_val, lbd_1_val, lbd_2_val;

	Tuple  instantiation_code, ntup ;
#ifdef TRACE
	if (debug_flag)
		gen_trace_node("EXPAND", node);
#endif

#ifdef DEBUG
	if (trapns>0 && N_SEQ(node)== trapns && N_UNIT(node) == trapnu) trapn(node);
#endif
	switch N_KIND(node) {

	case(as_insert):
		N_SIDE(node) = FALSE;
		FORTUP(node1 = (Node), N_LIST(node), ft1);
			expand(node1);
			N_SIDE(node) |= N_SIDE(node1);
		ENDFORTUP(ft1);
		node1 = N_AST1(node);
		expand(node1);
		N_SIDE(node) |= N_SIDE(node1);
		break;

	/* Chapter 3. Declarations and types*/
	/*
	 *-----------------
	 * 3.1 Declarations
	 */
	case(as_declarations):
		N_SIDE(node) = FALSE;
		if (N_LIST(node) == (Tuple)0)
			chaos("expand.c: as_declarations N_LIST null");
		FORTUP(node1 = (Node), N_LIST(node), ft1);
			expand(node1);
			N_SIDE(node) |= N_SIDE(node1);
		ENDFORTUP(ft1);
		break;

	/*
	 *------------------------------
	 * 3.2 Objects and named numbers
	 */

	case(as_obj_decl):
	case(as_const_decl):
		expand_decl(node);
		break;

	/*
	 *-----------------------
	 * 3.3 Types and subtypes
	 * 3.3.1
	 */
	case(as_type_decl):
		expand_type(node);
		break;

	/* 3.3.2 */
	case(as_subtype_decl):
	expand_subtype(node);
		break;

	case(as_delayed_type):
		sym1 = N_UNQ(N_AST1(node)); /* type name */
		sym2 = N_UNQ(N_AST2(node)); /* parent name */
		node1 = copy_node(node);    /* delayed node */
		if (NATURE(sym1) == na_subtype)
			N_KIND(node1) = as_subtype_decl;
		else
			N_KIND(node1) = as_type_decl;
		nk = emap_get(sym2); 
		tup = EMAP_VALUE;
		if (!nk)  /* emap_defined */
			tup = tup_new1((char *) node1);
		else
			tup = tup_with(tup, (char *)node1);
		/* EMAP(sym2) = (EMAP(sym2)?[]) with node1;*/
		emap_put(sym2, (char *) tup);
		delete_node(node);
		break;

	case(as_subtype_indic):
		sym1 = N_UNQ(N_AST1(node)); /* type name */
		N_SIDE(node) = (unsigned)CONTAINS_TASK(sym1);
		node2 = N_AST2(node); /* expression */
		expand(node2);
		N_SIDE(node) |= N_SIDE(node2);
		break;
	/*
	 *-----------------
	 * 3.5 Scalar types
	 */
	case(as_digits):
		expand(N_AST1(node)); /* precision node */
		node2 = N_AST2(node); /* range node */
		expand(node2);
		N_SIDE(node) = N_SIDE(node2);
		break;

	case(as_delta):
		expand(N_AST1(node)); /* precision node */
		node2 = N_AST2(node); /* range node */
		expand(node2);
		N_SIDE(node) = N_SIDE(node2);
		break;

	case(as_subtype):
		node2 = N_AST2(node);
		expand(node2);
		N_SIDE(node) = N_SIDE(node2);

		/* Transmit tasks_declared: */
		sym1 = N_UNQ(N_AST1(node)); /* type name */
		/* N_TYPE(node) is parent type */
		CONTAINS_TASK(sym1) = CONTAINS_TASK(N_TYPE(node));
		break;

	case(as_component_list):
		node1 = N_AST1(node); /* invariant node */
		FORTUP(node2 = (Node), N_LIST(node1), ft1);
			expand(node2);     /* field node */
		ENDFORTUP(ft1);
		expand(N_AST2(node)); /* variant node */
		N_SIDE(node) = FALSE;
		break;

	case(as_simple_choice):
		node1 = N_AST1(node); /* expression */
		expand(node1);
		N_SIDE(node) = N_SIDE(node1);
		break;

	case(as_incomplete_decl):
		sym1 = N_UNQ(N_AST1(node)); /* type name */
		CONTAINS_TASK(sym1) = (char *) TRUE; /* May be. Future will tell */
		delete_node(node);
		break;

	/*
	 * Chapter 4. Names and expressions
	 *
	 *----------
	 * 4.1 Names
	 */
	case(as_range_choice):
		node1 = N_AST1(node);
		if (N_KIND(node1) == as_attribute) {
			/* must be range. */
			sym1 = N_TYPE(node1);
			nk = (int)attribute_kind(node1) - ATTR_RANGE;   /* 'T' or 'O'*/
			attribute_kind(node1) = (char *) (nk + ATTR_FIRST);
			N_AST2(node) = new_attribute_node(nk + ATTR_LAST,
			  N_AST2(node1), N_AST3(node1), sym1);
			N_KIND(node) = as_range;
			N_TYPE(node) = sym1;
			expand(node);
		}
		else {
			node2 = N_AST2(node1);
			expand(node2);
			N_SIDE(node) = N_SIDE(node2);
		}
		break;

	case(as_range):
		node1 = N_AST1(node); /* expression */
		node2 = N_AST2(node); /* expression */
		expand(node1);
		expand(node2);
		N_SIDE(node) = N_SIDE(node1) | N_SIDE(node2);
		break;

	case(as_constraint):
		N_SIDE(node) = FALSE;
		FORTUP(node1 = (Node), N_LIST(node), ft1);
			if (N_KIND(node1) == as_choice_list) {
				/* named discriminant constraints. Only need expression. */
				node1 = N_AST2(node1) ;
			}
			expand(node1);
			N_SIDE(node) |= N_SIDE(node1);
		ENDFORTUP(ft1);
		break;

	case(as_index):
		node1 = N_AST1(node) ; /* array node */
		expand(node1);
		N_SIDE(node) = N_SIDE(node1);
		/* N_AST2(node) is a list of indices */
		FORTUP(node2 = (Node), N_LIST(N_AST2(node)), ft1);
			expand(node2); /* index */
			N_SIDE(node) |=  N_SIDE(node2);
		ENDFORTUP(ft1);
		break;

	/*
	 * 4.1.2
	 */
	case(as_slice):
		node2 = N_AST2(node) ; /* range node */

		if (N_KIND(node2) == as_subtype) {
			/* remove subtype */
			node1 = N_AST2(node2); /* id node */
			copy_attributes(node1, node2);
		}

		if (is_simple_name(node2)) {
			/* type name replaced by range attribute */
			/* SETL has OPT_NODE as third arg in next call. This is
	 		 * wrong - want to indicate first dimension.
	 		 *  ds	9-8-85
	 		 */
			node2 = new_attribute_node(ATTR_T_RANGE, node2,
			  new_ivalue_node(int_const(1), symbol_integer), N_UNQ(node2));
			N_AST2(node) = node2 ;
		}
		node1 = N_AST1(node) ; /* array node */
		expand(node1);
		N_SIDE(node) = N_SIDE(node1);
		expand(node2);         /* range node */
		N_SIDE(node) |= N_SIDE(node2);
		break;

	case(as_field):
		node2 = N_AST2(node) ; /* expression */
		expand(node2);
		N_SIDE(node) = N_SIDE(node2);
		break;

	case(as_selector):
	case(as_all):
		node1 = N_AST1(node) ; /* expression */
		expand(node1);
		N_SIDE(node) = N_SIDE(node1);
		break;

	/*
	 * 4.1.4
	 */
	case(as_attribute):
	case(as_range_attribute):
		expand_attr(node);
		break;

	/*
	 *-------------
	 * 4.2 Literals
	 */
	case(as_string_ivalue):
		expand_string(node);
		break;

	case(as_int_literal):
		/* TBSL(JC) This is a kludge */
		N_KIND(node) = as_ivalue;
		lv = adaval(symbol_integer, N_VAL(node));
		if (adaval_overflow)
			chaos("unable to convert integer literal");
		else
			N_VAL(node) = (char *) lv;
		N_SIDE(node) = FALSE;
		break;

	/*
	 *---------------
	 * 4.3 Aggregates
	 */
	case(as_array_aggregate):
#ifdef DEFER
		/* N_LIST assignmentnot needed in packed version  DS 3-86 */
		N_LIST(node) = (Tuple)0;    /* Useless information removed */
#endif
		expand_array_aggregate(node) ;
		N_SIDE(node) = N_KIND(node) != as_array_ivalue;
		/* TBSL better N_SIDE */
		break;

	case(as_row):
		node1 = N_AST1(node); /* expression */
		if (is_ivalue(node1) && root_type(N_TYPE(node1)) == symbol_character) {
			/* Transform into string litteral */
			/* Clear current AST_3 and AST_4 only if defined, thus preserving
	 		 * any N_UNQ and N_TYPE values if these are defined for the node.
	 		 */
			if (N_AST3_DEFINED(N_KIND(node))) N_AST3(node) = (Node) 0;
			if (N_AST4_DEFINED(N_KIND(node))) N_AST4(node) = (Node) 0;
			N_KIND(node) = as_string_ivalue;
			N_AST1(node) = (Node)0;
			N_AST2(node) = (Node)0;
			/* TBSL: check translation of following carefully */
			N_VAL(node) = (char *) tup_new1((char *) get_ivalue_int(node1));
		}
		else {
			/* Transform into an aggregate */
			N_KIND(node) = as_array_aggregate;
			/* positionnal */
			node3 = node_new(as_aggregate_list);
			node2         = node_new(as_list); /* positionnal */
			N_LIST(node2) = tup_new1((char *) node1);
			N_AST1(node3)  = node2 ;
			/* named */
			node2         = node_new(as_list); /* named */
			N_LIST(node2) = tup_new(0);
			N_AST2(node3)  = node2 ;
			N_AST1(node) = node3;

			N_AST2(node)  = OPT_NODE ;
			N_UNQ (node)  = new_unique_name("row");
		}
		expand(node);
		break;

	case(as_record_aggregate):
		expand_record_aggregate(node);
		N_SIDE(node) = N_KIND(node) != as_record_ivalue;
		/* TBSL better N_SIDE */
		break;

	/*
	 *----------------
	 * 4.4 Expressions
	 */

	/*
	 *----------------------------------------
 	* 4.5 Operators and expression evaluation
	 */
	case(as_op):
		expand_op(node);
		break;

	case(as_un_op):
		node2 = N_AST2(node) ; /* arguments */
		node1 = (Node) ((Tuple) N_LIST(node2)[1]);
		expand(node1);
		N_SIDE(node) = N_SIDE(node1);
		break;

	/*
	 *---------------------
	 * 4.6 Type conversions
	 */
	case(as_qual_range):
	case(as_qual_discr):
	case(as_qual_sub):
		node1 = N_AST1(node) ; /* expression */
		expand(node1);

		/* Note: must expand before checking types, as actual subtype of */
		/* aggregates may be determined by expansion. */
		sym1 = N_TYPE(node); /* qualification type */
		if (sym1 == get_type(node1) || is_unconstrained(sym1)) {
			/* remove qual */
			copy_attributes(node1, node);
		}
		else {
			N_SIDE(node) = N_SIDE(node1);
		}
		break;

	case(as_qual_index):
		node1 = N_AST1(node); /* expression */
		expand(node1);
		sym1 = N_TYPE(node); /* qualification type */
		sym2 = get_type(node1);
		if (sym1 == sym2 || is_unconstrained(sym1)) {
			/* remove qual */
			copy_attributes(node1, node);
		}
		else {
			/* tup_copy needed since index_types tuple used here
	 		 * destructiely  ds 6-25-85
	 		 */
			/* TBSL (JC) no copy needed. use FORTUPI */
			tup1 = tup_copy(index_types(sym1));
			tup2 = tup_copy(index_types(sym2));
			cboolean = TRUE;
			while (tup_size(tup1)) {
				sym3 = (Symbol) tup_fromb(tup1);
				sym4 = (Symbol) tup_fromb(tup2);
				node2 = (Node) ((Tuple) SIGNATURE(sym3)[2]); /* lower bound */
				node3 = (Node) ((Tuple) SIGNATURE(sym3)[3]); /* upper bound */
				lbd_1 = get_ivalue(node2);
				ubd_1 = get_ivalue(node3);
				node2 = (Node) ((Tuple) SIGNATURE(sym4)[2]); /* lower bound */
				node3 = (Node) ((Tuple) SIGNATURE(sym4)[3]); /* upper bound */
				lbd_2 = get_ivalue(node2);
				ubd_2 = get_ivalue(node3);
				if (N_KIND(node1) != as_slice && !is_unconstrained(sym2)
				  && lbd_1->const_kind != CONST_OM
				  && ubd_1->const_kind != CONST_OM
				  && lbd_2->const_kind != CONST_OM
				  && ubd_2->const_kind != CONST_OM) {
					lbd_1_val = INTV(lbd_1); 
					ubd_1_val = INTV(ubd_1);
					lbd_2_val = INTV(lbd_2); 
					ubd_2_val = INTV(ubd_2);
					if ((ubd_1_val - lbd_1_val) != (ubd_2_val - lbd_2_val)) {
						make_raise_node(node, symbol_constraint_error);
						USER_WARNING("Evaluation of expression will raise",
						  " CONSTRAINT_ERROR");
						cboolean = FALSE;
						break;
					}
					if ((ubd_1_val != ubd_2_val) || (lbd_1_val != lbd_2_val)) {
						cboolean = FALSE;
						break;
					}
				}
				else { /* non static */
					cboolean = FALSE;
					break;
				}
			} /* end loop */
			if (cboolean) {
				/* qual_index can be removed */
				copy_attributes(node1, node);
				N_TYPE(node) = sym1;
				if (is_aggregate(node))  {
					node2 = N_AST2(node); /* object node */
					TYPE_OF(N_UNQ(node2)) = sym1;
				}
				else if (N_KIND(node)==as_insert && is_aggregate(N_AST1(node))){
					node2 = N_AST2(N_AST1(node)); /* object node */
					TYPE_OF(N_UNQ(node2)) = sym1;
				}
			}
			else {
				N_SIDE(node) = N_SIDE(node1);
			}
		}
		break;

	case(as_qual_aindex):
	case(as_qual_alength):
	case(as_qual_adiscr):
		node1 = N_AST1(node) ; /* expression */
		expand(node1);
		if (N_KIND(node1) == as_null) {
			/* remove qual */
			copy_attributes(node1, node);
		}
		else {
			N_SIDE(node) = N_SIDE(node1);
		}
		break;

	case(as_convert):
		/* The target type of the conversion is the type of the node */
		/* The source type is the type of the expression itself. */
		node2 = N_AST2(node) ; /* expression */

		/* Special case: convert of a fixed point * or / */
		if (N_KIND(node2) == as_op && (op_kind(node2) == symbol_mulfx
		  || op_kind(node2) == symbol_divfx)) {

			/* Bind result type to the operation and remove node */
			N_TYPE(node2) = N_TYPE(node);
			copy_attributes(node2, node);
			expand(node);
		}
		else {
			expand(node2);
			N_SIDE(node) = N_SIDE(node2);

			/* Remove unnecessary conversion */
			if ((base_type(get_type(node2)) == base_type(N_TYPE(node))
			  && !is_unconstrained(base_type(N_TYPE(node))))
			  || ((root_type(get_type(node2)) == root_type(N_TYPE(node)))
			  && (is_discrete_type (root_type (get_type (node2)))))) {
				/*copy_attributes(node2, node); */
				N_KIND (node) = as_qual_range;
				N_AST1 (node) = N_AST2 (node);
			}
		}
		break;

	case(as_arg_convert):
		/*    The target type of the conversion is the type of the node
		 *    The source type is the type of the expression itself.
		 *    src_type    = get_type(node2) ;
		 *    target_type = N_TYPE(node);
		 */
		node2 = N_AST2(node) ; /* expression */
		expand(node2);
		N_SIDE(node) = N_SIDE(node2);
		break;

	/*
	 *---------------
	 * 4.8 Allocators
	 */
	case(as_new):
		node1 = N_AST1(node) ; /* id node */
		node2 = N_AST2(node) ; /* expression */
		sym1  = N_UNQ(node1) ; /* allocated type */
		/* N_TYPE(node) is the type of the context */
		sym2 = (Symbol) designated_type(N_TYPE(node)); /* accessed type */

		if (is_task_type(sym2)) {
			node2 = new_create_task_node(sym2);
			N_AST2(node) = node2 ;
		}
		else if ( is_access_type(sym2) && node2 == OPT_NODE) {
			node2 = node_new(as_null);
			N_AST2(node) = node2 ;
		}

		expand(node2);

		if (!is_simple_name(node1)) {
			/* There is a subtype to emit */
			expand(node1);
			make_insert_node(node, tup_new1((char *) node1), copy_node(node));
			node = N_AST1(node);
		}
		else if ( is_unconstrained(sym1)) {
			/* Establish proper subtype */
			if (is_array_type(sym1)) {
				/* Take constraint from initial value (always present in */
				/* this case) */
				sym1 = get_type(node2);
				N_UNQ(node1) = sym1;
			}
			else if (node2 == OPT_NODE) {  /* record */
				/* Create a subtype, constrained by default values. (Default
				 * values always present in that case). 
				 */
				sym1 = new_unique_name("constrained_type");
				N_UNQ(node1) = sym1;
				tup1 = constraint_new(co_discr);
				tup = tup_new(0);
				FORTUP(sym4 = (Symbol), discriminant_list_get(sym2), ft1);
					/* An allocator is always constrained. Set the constrained
					* bit accordingly
					*/
					if (sym4 == symbol_constrained)
						tup = discr_map_put(tup, sym4, 
					      new_ivalue_node(int_const(TRUE), symbol_boolean));
					else
						tup = discr_map_put(tup, sym4, 
					      copy_tree((Node) default_expr(sym4)));
				ENDFORTUP(ft1);
				tup1[2] = (char *) tup;
				new_symbol(sym1, na_subtype, sym2, tup1,
				  root_type(sym2));
				node1 = new_subtype_decl_node(sym1);
				expand(node1);
				make_insert_node(node,tup_new1((char *)node1), copy_node(node));
				node = N_AST1(node);
			}
			else if ( !is_unconstrained(get_type(node2))) {
				/* Use expression subtype for allocated object */
				sym3 = get_type(node2);
				N_UNQ(node1) = sym3;
			}
			else {
				/* Worst case: new REC'(F), where REC is unconstrained, and F
				 * returns REC. The subtype must be elaborated from the value
				 * of discriminants of the expression.
				 */
				sym3 = get_type(node2);
				sym1 = new_unique_name("constrained_type");
				N_UNQ(node1) = sym1;
				/* tup1 = [co_discr, {} ];*/
				tup1 = constraint_new(co_discr);
				tup1[2] = (char *) tup_new(0);
				new_symbol(sym1, na_subtype, sym2, tup1,
				  root_type(sym2));
				CONTAINS_TASK(sym1) = CONTAINS_TASK(sym2);

				node3         = node_new(as_type_and_value);
				N_AST1(node3) = new_name_node(sym1) ;
				N_AST2(node3) = node2 ;
				N_TYPE(node3) = sym3;
				N_AST1(node)  = node1 ;
				N_AST2(node)  = node3 ;
				if (N_AST3_DEFINED(N_KIND(node))) N_AST3(node) = (Node) 0;
				if (N_AST4_DEFINED(N_KIND(node))) N_AST4(node) = (Node) 0;
			}
		}
		sym3 = INIT_PROC(base_type(sym2));
		if (node2 == OPT_NODE && sym3 != (Symbol)0) {
			node2 = build_init_call(OPT_NODE, sym3, sym1, OPT_NODE);
			expand(node2);
			N_AST1(node) = node1 ;
			N_AST2(node) = node2;
			if (N_AST3_DEFINED(N_KIND(node))) N_AST3(node) = (Node) 0;
			if (N_AST4_DEFINED(N_KIND(node))) N_AST4(node) = (Node) 0;
		}
		N_SIDE(node) = TRUE;
		break;

		/** Chapter 5. Statements */

	case(as_null_s):
		break;

	case(as_line_no):
		ada_line     = (int) N_VAL(node);
		N_SIDE(node) = FALSE;
#ifdef TRACE
		if (debug_line>0 && ada_line >= debug_line) {
			expand_line();
		}
#endif
		break;
	
	/*
	 *-----------------------------------
	 * 5.1 Simple and compound statements
	 */
	case(as_statement):
		/* This node is used only for labelled statements, in front */
		/* of which labels are emitted. */
		expand(N_AST2(node)) ;
		break;

	case(as_statements):
		node1 = N_AST1(node) ; /* statements node */
		/* Note that if cboolean is true, the statement is not reachable 
		 * and therefore can be removed. TBSL: remove it from the list.
		 */
		cboolean = FALSE; /* first statement is always reachable */
		FORTUP(node2 = (Node), N_LIST(node1), ft1);
			if (N_KIND(node2) == as_statement)
				cboolean = FALSE;
			if (cboolean)
				delete_node(node2);
			else
				expand(node2);
			if (  N_KIND(node2) == as_raise 
		      || N_KIND(node2) == as_goto
		      || N_KIND(node2) == as_return 
		      || N_KIND(node2) == as_end
		      || N_KIND(node2) == as_terminate)
			cboolean = TRUE;
		ENDFORTUP(ft1);
		break;

	/*
	 *-------------------------
	 * 5.2 Assignment statement
 	*/
	case(as_assignment):
		expand(N_AST1(node)) ; /* variable node */
		expand(N_AST2(node)) ; /* expression */
		break;

	/*
	 *------------------
	 *  5.3 If statement
	 */
	case(as_if):
		node1 = N_AST1(node) ; /* if list node */
		node2 = N_AST2(node) ; /* else part */

		/* Remove branches guarded by static expressions */
		/* (conditional compilation) */
		tup = tup_new(0);
		FORTUP(node3 = (Node), N_LIST(node1), ft1);
			node4 = N_AST1(node3) ; /* condition */
			expand(node4);

			if (is_ivalue(node4)) {
				if (get_ivalue_int(node4) == TRUE) {
					/* This branch is guarded by TRUE: becomes the else part.
	      			 * All others branches are no longer reachable and
	       			 * may therefore be discarded.
	       			 */
					node2 = N_AST2(node3);
					break;
				}
				/* else FALSE: skip this node */
			}
			else {
				expand(N_AST2(node3));
				tup = tup_with(tup, (char *) node3);
			}
		ENDFORTUP(ft1);

		expand(node2); /* else part */

		if (tup_size(tup) == 0) {
			if (node2 == OPT_NODE)
				delete_node(node);
			else
				copy_attributes(node2, node);
		}
		else {
			N_LIST(node1) = tup;
			N_AST1(node)  = node1 ;
			N_AST2(node)  = node2 ;
		}
		break;

	/*
	 *--------------------
	 * 5.4 Case statements
	 */

	case(as_case):
	case(as_variant_decl):
		expand(N_AST1(node)) ; /* expression */
		tup1 = tup_copy(N_LIST(N_AST2(node))) ;
		/* tup_copy needed since tup1 used destructively
		 * in tup_fromb below  ds 6-25-85 
		 */
		if (tup_size(tup1) == 1) {
			/* Only one case... suppress case statement */
			node1 = (Node) tup_fromb(tup1); /* case branch */
			/* N_AST2(node1) is the list of statements for that branch */
			copy_attributes(N_AST2(node1), node);
			expand(node);
		}
		else {
			FORTUP(node1 = (Node), tup1, ft1);
				/* node1 is case node */
				node2 = N_AST1(node1) ; /* list of choices */
				expand(N_AST2(node1)) ; /* statements node */
				FORTUP(node1 = (Node), N_LIST(node2), ft2);
					/* in the inner loop node1 is choice node */
					nk = N_KIND(node1);
					if (nk == as_range_choice) {
						node3 = N_AST1(node1); /* id node */
						node4 = N_AST2(node3); /* range node */
						N_AST1(node1) = N_AST1(node4);
						N_AST2(node1) = N_AST2(node4);
						N_AST3(node1) = N_AST3(node4);
						N_AST4(node1) = N_AST4(node4);
						N_KIND(node1) = as_range;
					}
					else if (nk == as_simple_name) {
						sym1 = N_UNQ(node1); /* type name */
						tup = (Tuple) get_constraint(sym1);
						N_AST1(node1) = (Node) tup[2] ; /* lower bound */
						N_AST2(node1) = (Node) tup[3] ; /* upper bound */
						N_KIND(node1) = as_range;
					}
					else if (nk == as_simple_choice) {
						node3 = N_AST1(node1); /* lower bound */
						N_AST1(node1) = node3 ;
						N_AST2(node1) = node3 ;
						N_KIND(node1) = as_range;
					}
					else if (nk == as_others_choice || nk == as_range) {
						;
					}
					else {
						compiler_error_k(
						  "Unexpected choice in case statement: ", node1);
					}
				ENDFORTUP(ft2);
			ENDFORTUP(ft1);
		}
		break;

	/*
	 *--------------------
	 * 5.5 Loop statements
	 */

	case(as_loop):
		node1 = N_AST1(node) ; /* id node */
		node2 = N_AST2(node) ; /* iteration scheme */
		if (node2 != OPT_NODE) {
			expand(node2) ;
			if (N_KIND(node2) == as_insert) {
				propagate_insert(node2, node);
				node = N_AST1(node);
			}
		}
		nk = N_KIND(node2);
		if (nk == as_deleted)
			delete_node(node);
		else if (nk == as_raise)
			copy_attributes(node2, node);
		else { /* normal case */
			if (node1 != OPT_NODE) {
				sym1 = N_UNQ(node1); /* loop name */
				SIGNATURE(sym1) = (Tuple) FALSE;
			}
			expand(N_AST3(node)); /* statements */
			if (node1 != OPT_NODE) {
				/* Remove id node if not used */
				sym1 = N_UNQ(node1);
				if (is_generated_label(sym1) &&
				    SIGNATURE(sym1) == (Tuple) FALSE) {
					N_AST1(node) = OPT_NODE ;
				}
			}
		}
		break;

	case(as_while):
		expand(N_AST1(node)); /* condition node */
		break;

	case(as_for):
	case(as_forrev):
		expand_for(node);
		break;
	
	/*
	 *---------------------
	 * 5.6 Block statements
	 */

	case(as_block):
		node1 = N_AST1(node) ; /* id node */
		/* N_AST2(node) declaration node */
		/* N_AST3(node) statements node */
		/* N_AST4(node) handler node */
		if (is_simple_name(node1) && (N_UNQ(node1) == symbol_task_block)) {
			node2 = node_new(as_terminate); /* terminal node */
			tup = tup_new(2); 
			tup[1] = 0; 
			tup[2] = 0;
			N_VAL(node2) = (char *) tup;
		}
		else {
			node2 = node_new(as_end);       /* terminal node */
		}
		expand_block(N_AST2(node), N_AST3(node), N_AST4(node), node2);
		break;

	case(as_end):
		break;

	/*
	 *--------------------
	 * 5.7 Exit statements
	 */

	case(as_exit):
		expand(N_AST2(node)); /* condition node */
		sym1 = N_UNQ(node); /* loop name */
		SIGNATURE(sym1) = (Tuple) TRUE;
		break;

	/*
	 *----------------------
	 * 5.8 Return statements
	 */

	case(as_return):
		node1 = N_AST1(node) ; /* expression */
		if (node1 != OPT_NODE)
			expand(node1);
		break;

	/*
	 *--------------------
	 * 5.9 Goto statements
 	*/
	case(as_goto):
		break;

	/* Chapter 6. Subprograms */
	/*
	 *---------------------------
	 * 6.0 Predefined subprograms
	 */

	case(as_predef):
		sym1 = N_UNQ(node);     /* procedure name */
		sym2 = N_TYPE(node);    /* type name */
		tup = tup_new(2);
		tup[1] = (char *) N_VAL(node);
		/* integer mapped to the marker name */
		tup[2] = (char *) sym2;
		MISC(sym1) = (char *) tup;
		N_SIDE(node) = FALSE;
		break;

	case(as_interfaced):
		sym1 = N_UNQ(node);     /* procedure name */
		node1 = N_AST1(node);
		tup = tup_new(2);
		tup[1] = (char *) interface_counter++;  /* integer mapped to the
		                                               interfaced subprogram */
		/* the tuple interfaced_procedures consists of unit numbers of
		 * interfaced procedures followed by a string which contains
		 * the call to this interfaced procedure
		 */
		interfaced_procedures = tup_with(interfaced_procedures,
		  (char *) unit_number_now);
		if (streq(N_VAL(node1), "C")) {
			interfaced_procedures = tup_with(interfaced_procedures,
			  c_interface(sym1, (int) tup[1]));
		}
		else {
			interfaced_procedures = tup_with(interfaced_procedures,
			  fortran_interface(sym1, (int) tup[1]));
		}
		MISC(sym1) = (char *) tup;
		N_SIDE(node) = FALSE;
		break;

	/*
	 *----------------------
	 * 6.3 Subprogram bodies
	 */

	case(as_subprogram_tr):
		/* N_AST1(node) statements */
		/* N_AST2(node) declarations */
		/* N_AST4(node) handler */
		/* unique name of subprogram is now in the N_UNQ field of node. */
		sym1 = N_UNQ(node) ; /* subprogram name */

		if (NATURE(sym1) == na_procedure || NATURE(sym1) == na_procedure_spec) {
			/* Terminal node = return; */
			node2 = node_new(as_return);
			N_AST1(node2) = OPT_NODE ;
			N_AST2(node2) = new_name_node(sym1) ;
			N_AST3(node2) = new_number_node(0); /* depth */
		}
		else if (NATURE(sym1) == na_function
		  || NATURE(sym1) == na_function_spec) {
			/* Terminal node = raise PROGRAM_ERROR */
			node2 = new_raise_node(symbol_program_error);
		}
		else {     /* Task */
			node2 = node_new(as_terminate);
			tup = tup_new(2); 
			tup[1] = 0; 
			tup[2] = 0;
			N_VAL(node2) = (char *) tup;
		}

		/* The statement node is now in the N_AST1 field of node instead
		 * of N_AST3 field as it was when the node was as_subprogram
		 */
		expand_block(N_AST2(node), N_AST1(node), N_AST4(node), node2) ;
		N_SIDE(node) = TRUE;
		break;

	/*
	 *---------------------
	 * 6.4 Subprogram calls
	 */

	case(as_call):
	case(as_init_call):
		node1 = N_AST1(node) ; /* procedure id */
		node2 = N_AST2(node) ; /* list of arguments */
		sym1  = N_UNQ(node1) ; /* prcedure name */
		/* The following if statement is not in SETL source but was added
		 * to C version to fix renaming problem	ds 7-9-85
		 */
		if (ALIAS(sym1) != (Symbol)0) {
			sym1 = ALIAS(sym1);
			N_UNQ(node1) = sym1;
		}
		if (in_bin_ops(sym1)) {
			N_KIND(node) = as_op;
			expand(node);
		}
		else if (in_un_ops(sym1)) {
			N_KIND(node) = as_un_op;
			expand(node);
		}
		else {
			FORTUP(node1 = (Node), N_LIST(node2), ft1);
			expand(node1);
			ENDFORTUP(ft1);
			N_SIDE(node) = TRUE;
		}
		break;

	/*
	 * Chapter 7. Packages
	 *--------------------------------------------
	 * 7.2 Package specifications and declarations
	 */

	case(as_package_spec):
		/*Swap in symbol table private declarations with full declarations */
		sym1  = N_UNQ(N_AST1(node)) ; /* package name */
		private_install(sym1);

		node2 = N_AST2(node) ; /* declarations node */
		node3 = N_AST3(node) ; /* private declarations */
		expand(node2);
		expand(node3);

		N_SIDE(node) = N_SIDE(node2) | N_SIDE(node3);
		break;

	/*
	 *-------------------
	 * 7.3 Package bodies
	 */

	case(as_package_body):
		/* N_AST2(node) declarations */
		/* N_AST3(node) statements */
		/* N_AST4(node) handler */
		sym1 = N_UNQ(N_AST1(node)); /* package name */

		ud = unit_decl_get(unit_name);
		sym2 = ud->ud_unam; /* unit package */
		if (sym2 == sym1) { /* library unit */

			node4 = node_new(as_return);
			N_AST1(node4) = OPT_NODE;
			N_AST2(node4) = N_AST1(node);
			N_AST3(node4) = new_number_node(0); /* depth */
		}
		else {
			node4 = node_new(as_end);
		}

		if (N_AST3(node) == OPT_NODE) { /* statements */
			N_AST3(node) = new_statements_node(tup_new(0));
		}

		expand_block(N_AST2(node), N_AST3(node), N_AST4(node), node4);
		N_SIDE(node) = N_SIDE(N_AST2(node));
		break;

	/*
	 *----------------------------------------------------
	 * 7.4 Private type and deferred constant declarations
	 */

	case(as_use):
		delete_node(node);
		break;

	/*
	 * Chapter 8. Visibility rules
	 *--------------------------
	 * 8.5 Renaming declarations
	 */
	case(as_rename_obj):
		node1 = N_AST3(node) ; /* object node */
		expand(node1);
		N_SIDE(node) = N_SIDE(node1);
		break;

	case(as_rename_sub_tr):
		node2 = N_AST2(node) ; /* definition node */
		sym1  = N_UNQ(node) ; /* procedure name */
		tup1  = tup_copy(SIGNATURE(sym1));
		/* tup_copy needed since tup1 used in tup_fromb below */

		nk = N_KIND(node2);
		if (nk == as_attribute) {
			node2 = copy_node(node2); /* attribute node */
			sym3 = (Symbol) tup_fromb(tup1);
			N_AST2(node2) = new_name_node(TYPE_OF(sym3)) ;
			N_AST3(node2) = new_name_node(sym3) ;
			N_TYPE(node2) = TYPE_OF(sym1);
			node3 = node_new(as_return); /* return node */
			N_AST1(node3) = node2 ;
			N_AST2(node3) = new_name_node(sym1) ;
			N_AST3(node3) = new_number_node(0); /* depth */
			make_subprog_node(node, sym1, OPT_NODE,
			  new_statements_node(tup_new1((char *)node3)), OPT_NODE);
			expand(node);
		}
		else if (nk == as_entry_name) {
			node3 = node_new(as_ecall);       /* entry call */
			N_AST1(node3) = copy_node(node2); /* entry node */
			node2 = node_new(as_list);        /* arguments node */
			tup = tup_new(tup_size(tup1));
			FORTUPI(sym4 = (Symbol), tup1, nk, ft1);
				tup[nk] = (char *) new_name_node(sym4);
			ENDFORTUP(ft1);
			N_LIST(node2) = tup;
			N_AST2(node3) = node2;
			make_subprog_node(node, sym1, OPT_NODE,
			  new_statements_node(tup_new1((char *)node3)), OPT_NODE);
			expand(node);
		}
		else if (nk == as_simple_name) {
			/* handled fully by front-end. */
			delete_node(node);
		}
		else {
			compiler_error_k("Unknown kind in subprogram renaming: ", node2);
		}
		break;

	/*
	 * Chapter 9. Tasks
	 *----------------------------------------
	 * 9.1 Task specifications and task bodies
	 */

	case(as_task_spec):
		/* Separate declaration of the object from declaration of the type */
		sym1 = N_TYPE(node);   /* task type */
		sym2 = N_UNQ(node);    /* task name */
		node1 = copy_node(node); /* id node */
		N_KIND(node1) = as_task_type_spec;
		make_insert_node(node, tup_new1((char *) node1),
		  new_var_node(sym2, sym1, OPT_NODE));
		new_symbol(sym2, na_obj, sym1, (Tuple)0, (Symbol)0);
		expand(node);
		break;

	case(as_task_type_spec):
		/* Add the subprogram spec declaration in front
		 * and transform into type node.
		 */
		node2 = N_AST2(node); /* entries node */
		sym1 = N_TYPE(node); /* task type */
		sym2 = new_unique_name("task_init_proc"); /* associated procedure */
		assoc_symbol_put(sym1, TASK_INIT_PROC, sym2);
		CONTAINS_TASK(sym1) = (char *) TRUE;
		FORTUP(node1 = (Node), N_LIST(node2), ft1);
			expand(node1); /* entry node */
		ENDFORTUP(ft1);
		NATURE   (sym2) = na_task_body;
		TYPE_OF  (sym2) = symbol_none;
		SIGNATURE(sym2) = tup_new(0);
		generate_object(sym2); /* associated procedure */
		SIGNATURE(sym1) = N_LIST(node2);

		node2 = node_new(as_subprogram_decl_tr); /* subprogram node */
		N_UNQ(node2) = sym2;
		expand(node2);
		N_KIND(node) = as_type_decl;
		N_AST1(node) = new_name_node(sym1);
		N_AST2(node) = N_AST3(node) = (Node) 0;
		if (N_AST4_DEFINED(as_type_decl)) N_AST4(node) = (Node)0;
		N_SIDE(node) = FALSE;
		make_insert_node(node, tup_new1((char *)node2), copy_node(node));
		break;

	/*
	 *--------------------------------
	 * 9.2 Task types and task objects
	 */
	case(as_task):
		/* Transform it to procedure with modified statements */
		node1 = N_AST1(node); /* id node */
		/* N_AST2(node) declarations */
		/* N_AST3(node) statements */
		/* N_AST4(node) handler */
		/* N_UNQ(node1) task name */
		/* TYPE_OF(N_UNQ(node1)) type name */
		/* get associated procedure name */
		N_UNQ(node1) = assoc_symbol_get(TYPE_OF(N_UNQ(node1)), TASK_INIT_PROC);

		tup = tup_new(2);
		tup[1] = (char *) N_AST2(node); /* declaration node */
		node3 = node_new(as_end_activation);
		N_VAL(node3) = (char *) 1;      /* end activation OK */
		tup[2] = (char *) node3;
		N_KIND(node) = as_subprogram_tr;

		N_AST1(node) = new_statements_node(tup_new1((char *) new_block_node(
		  new_name_node(symbol_task_block), tup, tup_new1((char *)N_AST3(node)),
		  N_AST4(node))));
		N_AST2(node) = OPT_NODE;
		N_UNQ(node) = N_UNQ(node1);
		node2 = node_new(as_terminate); /* terminate node */
		tup = tup_new(2);
		tup[1] = (char *) 0;
		tup[2] = (char *) 2;
		N_VAL(node2) = (char *) tup;
		tup = tup_new(2);
		tup[2] = (char *) node2;        /* terminate node */
		node2 = node_new(as_end_activation);
		N_VAL(node2) = (char *) 0;   /* activation failed */
		tup[1] = (char *) node2;
		N_AST4(node) = new_statements_node( tup );
		expand(node);
		break;

	/*
	 *------------------------------------------------
	 * 9.3 Task Execution - Task Activation
	 */

	case(as_activate_spec):
		break;

	case(as_end_activation):
	case(as_create_task):
		N_SIDE(node) = TRUE;
		break;

	case(as_current_task):
		sym1 = N_UNQ(node); /* task name */
		N_SIDE(node) = FALSE;
#ifdef SHORT
		/* enable this code when and if support short integers */
		N_TYPE(node) = symbol_short_integer;
		new_symbol(sym1, na_obj, symbol_short_integer, (Tuple)0, (Symbol)0);
		make_const_node(node, sym1, symbol_short_integer, copy_node(node));
#else
		N_TYPE(node) = symbol_integer;
		new_symbol(sym1, na_obj, symbol_integer, (Tuple)0, (Symbol)0);
		make_const_node(node, sym1, symbol_integer, copy_node(node));
#endif
		break;

	case(as_entry_name):
		expand(N_AST1(node)); /*  task node */
		/* N_AST2(node)          entry node */
		node1 = N_AST3(node); /* index node */
		if (node1 != OPT_NODE) {
			node2 = copy_node(node1);
			/* Since N_AST3 and N_UNQ overlaid, clear N_AST3 field if 
			 * currently defined.
			 */
			if (N_AST3_DEFINED(N_KIND(node1)))
				N_AST3(node1) = (Node)0;
			N_KIND(node1) = as_convert;
#ifdef SHORT
			N_AST1(node1) = new_name_node(symbol_short_integer);
#else
			N_AST1(node1) = new_name_node(symbol_integer);
#endif
			N_LIST(node1) = (Tuple)0;
			N_AST2(node1) = node2 ;
#ifdef SHORT
			N_TYPE(node1) = symbol_short_integer;
#else
			N_TYPE(node1) = symbol_integer;
#endif
			expand(node1);
		}
		break;

	/*
	 *------------------------------------------------
	 * 9.4 Task Dependance - Termination of Tasks
	 */
	case(as_terminate):
		break;

	case(as_terminate_alt):
		break;

	/*
	 *------------------------------------------------
	 * 9.5 Entries, entry calls, and accept statements
	 */
	case(as_ecall):
		expand(N_AST1(node)) ; /* object node */
		node2 = N_AST2(node) ; /* arguments list */
		FORTUP(node1 = (Node), N_LIST(node2), ft1);
			expand(node1); /* argument node */
		ENDFORTUP(ft1);
		break;

	case(as_conditional_entry_call):
		/* Transform into timed entry call with delay 0 */
		/* N_AST1(node) call statement node */
		/* N_AST2(node) statements node */
		/* N_AST3(node) else part */
		node1 = node_new(as_delay_alt); /* delay alternative */
		node2 = node_new(as_delay);     /* delay expression  */
		N_AST1(node2) = new_ivalue_node(
		  rat_const(rat_fri(int_fri(0), int_fri(1))), symbol_duration);
		N_AST1(node1) = node2 ;
		N_AST2(node1) = N_AST3(node) ; /* else part */
		N_KIND(node) = as_timed_entry_call;
		N_AST3(node) = node1 ;
		expand(node);
		break;

	case(as_timed_entry_call):
		expand(N_AST1(node)) ; /* call node */
		expand(N_AST2(node)) ; /* stmt node */
		node1 = N_AST3(node) ; /* delay alternative */
		expand(N_AST1(node1)); /* delay expression  */
		expand(N_AST2(node1)); /* else part */
		break;

	case(as_accept):
		/* Replace [id_node, index_node] by an entry_name node */
		node1 = node_new(as_entry_name); /* entry name */
		N_AST1(node1) = OPT_NODE ;
		N_AST2(node1) = N_AST1(node); /* id node */
		N_AST3(node1) = N_AST2(node); /* index node */
		N_AST1(node) = node1 ;        /* entry name */
		N_AST2(node) = N_AST3(node);
		N_AST3(node) = node2 = N_AST4(node);
		N_AST4(node) = (Node) 0;
		expand(node1);

		if (node2 != OPT_NODE) {      /* body node */
			node1 = new_block_node(OPT_NODE, tup_new(0), 
			  tup_new1((char *)node2), node_new(as_exception_accept));
			expand(node1);
			N_AST3(node) = node1 ;
		}
		break;

	case(as_accept_alt):
		expand(N_AST1(node)); /* accept statement node */
		expand(N_AST2(node)); /* statements node */
		break;

	/*
	 *----------------------------------------
	 * 9.6 Delay statements, duration and time
	 */
	case(as_delay):
		expand(N_AST1(node)); /* expression */
		break;

	/*
	 *----------------------
	 * 9.7 Select statements
 	*/

	case(as_selective_wait):
		node1 = N_AST1(node); /* list of alternatives */
		FORTUP(node2 = (Node), N_LIST(node1), ft1);
			expand(node2);      /* alternative */
		ENDFORTUP(ft1);
		node2 = N_AST2(node); /* else part */
		if (node2 != OPT_NODE) {
			expand(node2); /* else part */
			node3 = node_new(as_delay_alt) ; /* delay alternative */
			N_AST2(node3) = node2 ;          /* else part */
			node2 = node_new(as_delay);
			N_AST1(node2) = new_ivalue_node(
			  rat_const(rat_fri(int_fri(0), int_fri(1))), symbol_duration);
			N_AST1(node3) = node2 ;          /* delay expression */
			N_LIST(node1) = tup_with(N_LIST(node1), (char *) node3);
		}
		break;

	case(as_guard):
		expand(N_AST1(node)); /* condition node */
		expand(N_AST2(node)); /* alternative node */
		break;

	case(as_delay_alt):
		expand(N_AST1(node)); /* expression */
		expand(N_AST2(node)); /* statements */
		break;

	/*
	 *---------------------
	 * 9.9 Abort statements
 	*/

	case(as_abort):
		FORTUP(node1 = (Node), N_LIST(node), ft1);
			expand(node1); /* id of the task to be aborted */
		ENDFORTUP(ft1);
		break;

	/*
	 * Chapter 10. Program structure and compilation issues
	 *---------------------------------------
	 * 10.1 Compilation units - Library units
	 */

	case(as_unit):
		expand(N_AST2(node)); /* unit root node */
		break;

	/*
	 *------------------------------------
	 * 10.2 Subunits of compilations units
	 */
	case(as_subprogram_stub_tr):
	case(as_package_stub):
	case(as_task_stub):
		lib_stub_put(N_VAL(node), AISFILENAME); /* N_VAL(node) is stub_name */
		stub_parent_put(N_VAL(node), unit_name);
		/* generate a slot for a fake proper body which is considered obsolete.
		 * This is due to handling of generic stubs.
		 */
		pUnits[unit_number(N_VAL(node))]->libInfo.obsolete = string_ds;/*"$D$"*/
		N_SIDE(node) = FALSE;
		break;

	case(as_separate):
		expand(N_AST2(node)); /* unit root node */
		break;

	/*
	 * Chapter 11. Exceptions
	 */
	/*
	 *------------------------
	 * 11.2 Exception handlers
	 */

	case(as_handler):
		/* Transform the handler into a "elsif test_exception or
		 * test_exception ... then statements".
		 * when others is expanded as an "elsif TRUE then statements"
		 * Do not expand statements, as they will be expanded when the if
		 * statement is.
		 */
		node1 = N_AST1(node) ; /* list of exceptions */
		tup  = N_LIST(node1) ; /* list of exception nodes */
		node1 = (Node) tup[1]; /* name of first exception */
		if (N_KIND(node1) == as_others)
			node2 = new_ivalue_node(int_const(TRUE), symbol_boolean);
		else {
			node2 = node_new(as_test_exception);     /* root of if */
			N_AST1(node2) = node1;      /* name of first exception */
			N_TYPE(node2) = symbol_boolean;
			for (nk = 2; nk <= tup_size(tup); nk++) {
				node1 = node_new(as_test_exception); /* running condition */
				N_AST1(node1) = (Node) tup[nk];      /* name of exception */
				N_TYPE(node1) = symbol_boolean;
				node2 = new_binop_node(symbol_or, node2, node1, symbol_boolean);
			}
		}

		node1 = N_AST2(node) ; /* statements */
		node3 = N_AST1(node1); /* list of statements */
		/* N_AST3(node) terminal statements node */
		N_LIST(node3) = tup_with(N_LIST(node3), (char *) N_AST3(node));

		N_KIND(node) = as_cond_statements;
		N_AST1(node) = node2 ; /* if list */
		N_AST3(node) = N_AST4(node) = (Node) 0;
		break;

	case(as_exception):
		/* Transform the handler into an if statement.
		 * Add an else part to that if: else raise.
		 * Note: if the user has provided a "when others" clause, this will
		 *       be expanded as an "elsif TRUE" branch, and optimization of
		 *       the if statement will remove the (now superfluous) else.
		 */
		node1 = N_AST1(node); /* terminal statement */
		FORTUP(node2 = (Node), N_LIST(node), ft1);
			N_AST3(node2) = copy_tree(node1);
			expand(node2); /* handler node */
		ENDFORTUP(ft1);

		tup = N_LIST(node);
		make_if_node(node, tup, new_raise_node(OPT_NAME));
		expand(node);   /* other transformations possible in this new form */
		break;

	/*
	 *-------------------------------------------------
	 * 11.5 Exceptions raised during task communication
	 */

	case(as_exception_accept):
		break;

	/*
	 * Chapter 12. Generics units
	 */
    case(as_generic_package):
      /*
       * Added here to traverse decls list to catch presence of stubs.
       * This is necessary to allocate a unit number for it to enable
       *  subsequent unit numbers to be correct.
       */
#ifdef TBSL
       expand(N_AST2(node));
#endif
       N_SIDE(node) = FALSE;
       break;
	/*
	 *---------------------------
	 * 12.3 Generic instanciation
	 */
	case(as_package_instance):
		/* This  node  indicates  a late  instantiation, i.e.  a  package
		 * instantiation  that  precedes  the  compilation of the generic
		 * package body. If the package has been seen, the instantiation is
		 * now completed. If none is needed, an empty package is created.
		 * Otherwise the missing body is treated as a stub.
		 */
		sym1 = N_UNQ(N_AST1(node)) ; /* package name */
		sym2 = N_UNQ(N_AST2(node)) ; /* generic name */
		retrieve_generic_body(sym2);
		tup = (Tuple) N_VAL(N_AST4(node));
		instance_map = (Symbolmap) tup[1];
		cboolean = (int) tup[2];
		tup = SIGNATURE(sym2);
		/* (Node) tup[2] declarations */
		/* (Node) tup[3] private part */
		node1 = (Node) tup[4];       /* body node */
		tup2 = (Tuple) tup[5]; 	   /* must_constrain generic types */

		/* check to see if this is a case where the body is a stub. */
		if (node1 == OPT_NODE) {
			char	 *stub_nam;
			tup = stubs(unit_name);
			FORTUP(stub_nam = (char *), tup, ft1);
				if (streq(unit_name_name(stub_nam), ORIG_NAME(sym2))) {
					if (!read_ais(AISFILENAME, TRUE, stub_nam, 0, TRUE)) break;
					tup  = SIGNATURE(sym2);
					node1 = (Node) tup[4];     /* body node */
					tup2 = (Tuple) tup[5];     /* must_constrain generic types*/
					break;
				}
			ENDFORTUP(ft1);
		}
		/*$TBSL retrieve_old_tree(node1); */
		retrieve_generic_tree(node1, (Node)0);
		if (node1 != OPT_NODE) {	   /* Instantiate body. */
			/* Instantiate all entities local to  the package body.
			 * Instance_map marks the entities defined in the spec, 
			 * and already instantiated.
			 */
			tup = instantiate_symbtab(sym2, sym1, instance_map);
			instance_map = (Symbolmap) tup[1];
			/* instantiate the AST itself, and complete the 
			 * instantiation of the symbol table.
			 */
			node_map = nodemap_new() ;		/* global object. */

			node2 = instantiate_tree(node1, instance_map) ; /* new body */
			N_KIND(node2) = as_package_body ;
			copy_attributes(node2, node);
			/* Node references in the symbol table 
			 * must point to the instantiated tree.
			 */
			tup1 = (Tuple) tup[3];
			update_symbtab_nodes(instance_map, tup1) ;
			tup1 = (Tuple) tup[2];
			check_priv_instance(tup2, instance_map) ;
			/* The full declarations of private entities must be updated as
			 * well, for the generic package and all inner packages.
			 */
			/*  loop for sym3 in tup1 do
			 *      private_decls(instance_map(sym3)) =
			 *	     update_private_decls(sym3, instance_map) ;
			 *  end loop ;
			 */
			FORTUP(sym3 = (Symbol), tup1, ft1);
				sym4 = symbolmap_get(instance_map, sym3);
				private_decls(sym4) =
				  (Set)update_private_decls(sym3, instance_map);
			ENDFORTUP(ft1);
			N_KIND(node) = as_package_body ;
			mint(node);
			expand(node) ;
		}
		else if ( ! cboolean) {
			/* assume that none will be seen, and build empty package body.*/
			N_KIND(node) = as_package_body ;
			N_AST1(node) = new_name_node(sym1) ;
			N_AST2(node) = OPT_NODE;
			N_AST3(node) = OPT_NODE;
			N_AST4(node) = OPT_NODE;
			expand(node) ;
		}
		else
			user_error("Separately compiled generics not supported ") ;
		break;

	case(as_function_instance):
	case(as_procedure_instance):
		/* Same as previous one, for subrograms. Here the body is always
		 * needed.
		 */
		/* Unpack instantiation information, attached to N_VAL of node. */
		tup = (Tuple)N_VAL(N_AST4(node));
		type_map = (Symbolmap)tup[1];
		sym1 = N_UNQ(N_AST2(node)) ; /* generic name */
		retrieve_generic_body(sym1);
		tup  = SIGNATURE(sym1);
		node1 = (Node) tup[3];       /* body node */
		tup1 = (Tuple) tup[4];	   /* must_constrain */

		/* check to see if this is a case where the body is a stub. */
		if (node1 == OPT_NODE) {
			char	 *stub_nam;
			tup = stubs(unit_name);
			FORTUP(stub_nam = (char *), tup, ft1);
				if (streq(unit_name_name(stub_nam), ORIG_NAME(sym1))) {
					if (!read_ais(AISFILENAME, TRUE, stub_nam, 0, TRUE)) break;
					tup = SIGNATURE(sym1);
					node1 = (Node) tup[3];       /* body node */
					tup1 = (Tuple) tup[4];	     /* must_constrain */
					break;
				}
			ENDFORTUP(ft1);
		}

		if (node1 != OPT_NODE) {
			/*$TBSL retrieve_old_tree(node1); */
			retrieve_generic_tree(node1, (Node)0);
			instantiation_code = N_LIST(N_AST3(node)) ;
			instantiate_subprog_tree(node, type_map) ;
			/* Take the subprogram created by the instantiation and reformat
			 * the spec node to be of a form as_procedure_tr (as_function_tr) 
			 * with the formal part detached from the tree. Move up the id_node
			 * (subprogram name) info to the specfication node.
			 */
			node2 = N_AST1(node);
			node3 = N_AST1(node2);
			N_KIND(node) = as_subprogram_tr;
			N_AST1(node) = N_AST3(node);
			N_UNQ(node) = N_UNQ(node3);
			/* add instantiation code to declarative part of subprogram.
	  		 * this is not strictly correct, as bounds checks should be
	  		 * elaborated outside of the subprogram body. To be cleaned up
	  		 * later.
	  		 */
			ntup = tup_add(instantiation_code, N_LIST(N_AST2(node))) ;
			tup_free(instantiation_code) ;
			N_LIST(N_AST2(node)) = ntup ;

			check_priv_instance(tup1, instance_map) ;
			mint(node);
			expand(node) ;
		}
		else
			user_error("Separately compiled generics not supported ") ;
		break;

	case(as_check_bounds):
		sym1 = N_UNQ(N_AST1(node)) ; /* generic type */
		sym2 = N_UNQ(N_AST2(node)) ; /* actual type */
		if (is_discrete_type (sym2)) {
			node1 = new_attribute_node(ATTR_T_FIRST, new_name_node(sym1),
			  OPT_NODE, sym1);
			node2 = new_attribute_node(ATTR_T_LAST, new_name_node(sym1),
			  OPT_NODE, sym1);
			node3 = new_attribute_node(ATTR_T_FIRST, new_name_node(sym2),
			  OPT_NODE, sym2);
			node4 = new_attribute_node(ATTR_T_LAST, new_name_node(sym2),
			  OPT_NODE, sym2);
			/*$ TBSL: some constant folding. */
			make_if_node(node,
			  tup_new1((char *) new_cond_stmts_node(
			  new_binop_node(symbol_or,
			  new_binop_node(symbol_ne,
			  node1,
			  node3,
			  symbol_boolean),
			  new_binop_node(symbol_ne,
			  node2,
			  node4,
			  symbol_boolean),
			  symbol_boolean),
			  new_raise_node(symbol_constraint_error)  )
			  ),
			  OPT_NODE);
		}
		else if (is_fixed_type (sym2)) {

			/* conversion of fixed is possible if they have the same accuracy */
			if (rat_neq ( RATV (get_ivalue
			  (((Node) numeric_constraint_delta (get_constraint(sym1))))),
			  RATV (get_ivalue
			  (((Node) numeric_constraint_delta (get_constraint(sym2))))))) {
				make_raise_node(node, symbol_constraint_error);
				USER_WARNING(
	"Due to difference in fixed point accuracy, conversion of array will raise",
				  " CONSTRAINT_ERROR"); 
			}
		}
		else if (is_float_type (sym2)) {

			/* conversion of float is possible if they have the same floating
			 * point accuracy
			 */
			if ( INTV (get_ivalue (((Node) numeric_constraint_delta
			  (get_constraint(sym1))))) != INTV (get_ivalue
			  (((Node) numeric_constraint_delta (get_constraint(sym2)))))) {
				make_raise_node(node, symbol_constraint_error);
				USER_WARNING(
"Due to difference in floating point accuracy, conversion of array will raise",
				  " CONSTRAINT_ERROR"); 
			}
		}
		expand(node);
		N_SIDE(node) = FALSE;
		break;

	case(as_check_discr):
		node1 = N_AST1(node) ;
		sym1  = N_UNQ(N_AST2(node)) ; /* type name */
		sym2  = N_UNQ(N_AST3(node)) ; /* dscriminant name */
		make_if_node(node,
		  tup_new1((char *) new_cond_stmts_node(
		  new_binop_node(symbol_ne,
		  node1,
		  new_discr_ref_node(sym2, sym1),
		  symbol_boolean),
		  new_raise_node(symbol_constraint_error)  )
		  ),
		  OPT_NODE);
		expand(node);
		N_SIDE(node) = FALSE;
		break;

	case(as_expanded):
		/* This node removed, WITHOUT expanding its descendant! */
		node1 = N_AST1(node); /* son node */
		copy_attributes(node1, node);
		break;

	/*
	 * Chapter 13. Representation clauses
	 *--------------------
	 * 13.2 Length clauses
	 */

	case(as_length_clause):
	case(as_enum_rep_clause):
	case(as_rec_rep_clause):
		delete_node(node);
		N_SIDE(node) = FALSE;
		break;

	case(as_opt):
		break;

	case(as_pragma):
	case(as_arg):
	case(as_enum):
	case(as_num_decl):
	case(as_int_type):
	case(as_float_type):
	case(as_fixed_type):
	case(as_array_type):
	case(as_record):
	case(as_discr_ref):
	case(as_simple_name):
	case(as_labels):
	case(as_ivalue):
	case(as_null):
	case(as_subprogram_decl_tr):
	case(as_private_decl):
	case(as_rename_ex):
	case(as_rename_pack):
	case(as_entry):
	case(as_entry_family):
	case(as_except_decl):
	case(as_raise):
	case(as_test_exception):
	case(as_generic_function):
	case(as_generic_procedure):
	case(as_generic_formals):
		N_SIDE(node) = FALSE;
		break;

	default:
		compiler_error_k( "Illegal kind of node in expand: ", node);
	}
}
