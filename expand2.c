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
#include "gmainprots.h"
#include "setprots.h"
#include "miscprots.h"
#include "gnodesprots.h"
#include "gutilprots.h"
#include "gmiscprots.h"
#include "initobjprots.h"
#include "arithprots.h"
#include "chapprots.h"
#include "smiscprots.h"
#include "expandprots.h"

static Tuple constrained_type(Symbol, Node, Node);
static int array_nelem(Node);
static void replace_name(Node, Symbol, Symbol);

static int array_nelem_defined; /* set if array_nelem undefined */

void expand_line()											/*;expand_line*/
{
	/* called when expander reaches line debug_line if debug_line is not
	 * zero. This is meant to provide useful trapping point for
	 * interactive debugging.		ds 7-19-85
	 */
}


int in_bin_ops(Symbol op)									/*;in_bin_ops*/
{
	/*	 bin_ops = {'and',  'or',  'xor', '&', '&ac', '&ca', &cc'
	 *	 '=',    '/=',  '<=',  '>',    '>=',   '<',     
	 *	 '+i',   '-i',   '*i',  '/i',  '**i',  'remi', 'modi', 
	 *	 '+fl',   '-fl',  '*fl', '/fl', '**fl', 
	 *	 '+fx',   '-fx',  '*fx', '/fx', '*fix', '*fxi', '/fxi'},
	 */
	return op == symbol_and || op == symbol_or || op == symbol_xor 
	  || op == symbol_cat || op == symbol_cat_cc || op == symbol_cat_ca
	  || op == symbol_cat_ac || op == symbol_eq || op == symbol_ne
	  || op == symbol_le || op == symbol_gt || op == symbol_ge
	  || op == symbol_lt || op == symbol_addi || op == symbol_subi
	  || op == symbol_muli || op == symbol_divi || op == symbol_expi 
	  || op == symbol_remi || op == symbol_modi || op == symbol_addfl
	  ||op == symbol_subfl || op == symbol_mulfl || op == symbol_divfl
	  || op == symbol_expfl || op == symbol_addfx || op == symbol_subfx
	  || op == symbol_mulfx || op == symbol_divfx || op == symbol_mulfix
	  || op == symbol_mulfxi || op == symbol_divfxi;
}

int in_un_ops(Symbol op)									/*;in_un_ops*/
{
	/*	un_ops =  {'not', '-ui',  '+ui',  'absi', '-ufl', '+ufl', 'absfl',
	 *	'-ufx', '+ufx', 'absfx'  };
	 */

	return op == symbol_not || op == symbol_subui || op == symbol_addui
	  || op == symbol_absi || op == symbol_subufl || op == symbol_addufl
	  || op == symbol_absfl || op == symbol_subufx || op == symbol_addufx
	  || op == symbol_absfx;
}

void expand_block(Node decl_node, Node stmt_node, Node exc_node, Node term_node)
															/*;expand_block*/
{
	Node	stmt_list_node;

	if (decl_node != OPT_NODE)
		expand(decl_node);

	stmt_list_node = N_AST1(stmt_node);
	N_LIST(stmt_list_node) = tup_with(N_LIST(stmt_list_node),
	  (char *) copy_tree(term_node));
	expand(stmt_node);

	if (exc_node != OPT_NODE) {
		/* Note: exc node may be a sequence of statements */
		if (N_KIND(exc_node) == as_exception) {
			N_AST1(exc_node) = term_node;
			if (N_AST2_DEFINED(as_exception)) N_AST2(exc_node) = (Node) 0;
			if (N_AST3_DEFINED(as_exception)) N_AST3(exc_node) = (Node) 0;
			if (N_AST4_DEFINED(as_exception)) N_AST4(exc_node) = (Node) 0;
		}
		expand(exc_node);
	}
}

static Tuple constrained_type(Symbol array_type, Node lbd_node, Node ubd_node)
														/*;constrained_type*/
{
	/*
	 * Given an unconstrained array type, constructs a constrained subtype
	 * with the given bounds.
	 * returns [type_name, decls] where type_name is the name of the
	 * constrained array subtype, and decls a list (tuple) of nodes necessary
	 * to elaborate the type.
	 */

	Symbol   bt, index_name, array_name, comp_type;
	Node	range_node, indic_node, ix_name_node, index_node, ar_name_node,
	  array_node;
	Tuple	tup, dtup;

	bt = base_type(N_TYPE(lbd_node));

	/* 1- Create range node */
	range_node        = node_new(as_range);
	N_AST1(range_node) = lbd_node;
	N_AST2(range_node) = ubd_node;
	indic_node        = node_new(as_subtype_indic);
	N_AST1(indic_node) = new_name_node(bt);
	N_AST2(indic_node) = range_node;

	/* 2- Create index subtype */
	index_name         = new_unique_name("index");
	ix_name_node       = new_name_node(index_name);
	index_node         = node_new(as_subtype_decl);
	N_AST1(index_node) = ix_name_node;
	N_AST2(index_node) = indic_node;
	tup = constraint_new(co_range);
	tup[2] = (char *) lbd_node;
	tup[3] = (char *) ubd_node;
	new_symbol(index_name, na_subtype, bt, tup, ALIAS(bt));
	CONTAINS_TASK(index_name) = FALSE;

	/* 3- Create constrained array subtype */
	indic_node         = node_new(as_constraint);
	N_LIST(indic_node) = tup_new1( (char *) new_name_node(index_name));
	array_name         = new_unique_name("array");
	ar_name_node       = new_name_node(array_name);
	array_node         = node_new(as_subtype_decl);
	N_AST1(array_node)  = ar_name_node;
	N_AST2(array_node)  = indic_node;
	comp_type = (Symbol) (SIGNATURE(array_type))[2];
	tup = tup_new(2);
	tup[1] = (char *) tup_new1( (char *) index_name);
	tup[2] = (char *) comp_type;
	new_symbol(array_name, na_subtype, array_type,
	  tup, ALIAS(array_type));
	CONTAINS_TASK(array_name) = CONTAINS_TASK(array_type);
	dtup = tup_new(2);
	dtup[1] = (char *) index_node;
	dtup[2] = (char *) array_node;
	tup = tup_new(2);
	tup[1] = (char *) array_name;
	tup[2] = (char *) dtup;
	return tup;
}

static int array_nelem(Node node)							/*;array_nelem*/
{
	/*
	 * Given a node that is appropriate for an array type, determines the
	 * number of elements if known statically, returns OM otherwise.
	 */

	Symbol   node_name, type_name, index_sym;
	Tuple 	index_list, tup;
	int		size, nk;
	Node		nod2, lbd_node, ubd_node;
	Fortup	ft1;
	Const	lbd, ubd;

	/* the global (to this module) variable array_nelem_defined is set to
	 * FALSE if the SETL version of this procedure returns OM, TRUE otherwise
	 */
	array_nelem_defined = TRUE; /* assume defined */
	nk = N_KIND(node);
	if (nk == as_subtype_indic) {
		nk = (int) N_KIND((N_AST2(node) == OPT_NODE) ?
		  N_AST1(node) : N_AST2(node));
		nod2 = N_AST2(node);
	}
	if (nk == as_string_ivalue) {
		return tup_size((Tuple) N_VAL(node));
	}
	else if (nk == as_simple_name) {
		node_name = N_UNQ(node);
		if (NATURE(node_name) == na_type) {
			array_nelem_defined = FALSE;
			return 0;	/* always unconstrained */
		}
		else if ( NATURE(node_name) == na_subtype) {
			type_name = node_name;
		}
		else { /* object */
			type_name = N_TYPE(node);
		}
		tup        = SIGNATURE(type_name);
		index_list = (Tuple) tup[1];
		size       = 1;
		FORTUP(index_sym  = (Symbol), index_list, ft1);
			tup = SIGNATURE(index_sym);
			lbd_node = (Node) tup[2];
			ubd_node = (Node) tup[3];
			lbd = get_ivalue(lbd_node);
			ubd = get_ivalue(ubd_node);
			if (lbd->const_kind != CONST_OM  && ubd->const_kind != CONST_OM) {
				if (get_ivalue_int(ubd_node) < get_ivalue_int(lbd_node))
					return 0;
				else
					size *= get_ivalue_int(ubd_node)-get_ivalue_int(lbd_node)+1;
			}
			else{
				array_nelem_defined = FALSE;
				return 0;
			}
		ENDFORTUP(ft1);
		return size;
	}
#ifdef TBSL
	/* Wrong because the type_name is the base_type*/
	else if (nk == as_array_aggregate || nk == as_array_ivalue)  {
		type_name  = N_TYPE(node);
		tup        = SIGNATURE(type_name);
		index_list = (Tuple) tup[1];
		size       = 1;
		FORTUP(index_sym  = (Symbol), index_list, ft1);
		tup = SIGNATURE(index_sym);
		lbd_node = (Node) tup[2];
		ubd_node = (Node) tup[3];
		lbd = get_ivalue(lbd_node);
		ubd = get_ivalue(ubd_node);
		if (lbd->const_kind != CONST_OM  &&
		    ubd->const_kind != CONST_OM) {
			if (get_ivalue_int(ubd_node) < get_ivalue_int(lbd_node)) {
				return 0;
			}
			else {
				size *= get_ivalue_int(ubd_node) - get_ivalue_int(lbd_node) +1;
			}
		}
		else{
			array_nelem_defined = FALSE;
			return 0;
		}
		ENDFORTUP(ft1);
		return size;
	}
#endif
	else if (nk == as_range) {
		lbd_node = N_AST1(nod2);
		ubd_node = N_AST2(nod2);
		size     = 1;
		lbd = get_ivalue(lbd_node);
		ubd = get_ivalue(ubd_node);
		if (lbd->const_kind != CONST_OM  && ubd->const_kind != CONST_OM) {
			if (get_ivalue_int(ubd_node) < get_ivalue_int(lbd_node))
				return 0;
			else
				size *= get_ivalue_int(ubd_node) - get_ivalue_int(lbd_node) +1;
		}
		else{
			array_nelem_defined = FALSE;
			return 0;
		}
		return size;
	}
	else {
		/*compiler_error_k("Array_nelem: kind = ", node);*/
		/*TBSL : does not make the test for a slice, 
		 *a convert, a call, an op.              
		 */
		array_nelem_defined = FALSE;
		return 0;
	}
}

Symbol op_kind(Node node)										/*;op_kind*/
{
	/* Given a as_op node, returns the unique name of the operator */

	Node	id_node;

	id_node = N_AST1(node);
	return N_UNQ(id_node);
}

static void replace_name(Node node, Symbol old_name, Symbol new_name)
															/*;replace_name*/
{
	/* Replaces all occurences of old_name by new_name in the tree rooted at
	 * node.
	 */

	Node	subnode;
	Fortup	ft1;
	int	nk;

	if (node == (Node)0)
		chaos("replace_name called on null node");
	if (N_UNQ(node) == old_name )
		N_UNQ(node) = new_name;

	nk = N_KIND(node);
	if (N_AST1_DEFINED(nk) && N_AST1(node) != (Node)0)
		replace_name(N_AST1(node), old_name, new_name);
	if (N_AST2_DEFINED(nk) && N_AST2(node) != (Node)0)
		replace_name(N_AST2(node), old_name, new_name);
	if (N_AST3_DEFINED(nk) && N_AST3(node) != (Node)0)
		replace_name(N_AST3(node), old_name, new_name);
	if (N_AST4_DEFINED(nk) && N_AST4(node) != (Node)0)
		replace_name(N_AST4(node), old_name, new_name);
	if (N_LIST_DEFINED(nk) && N_LIST(node) != (Tuple)0) {
		FORTUP(subnode = (Node), N_LIST(node), ft1);
			replace_name(subnode, old_name, new_name);
		ENDFORTUP(ft1);
	}
}

void mint(Node node)											/*;mint*/
{
	/* Deletes all occurences of :
	 * 	as_qualify, as_name, as_conditon, as_parenthesis
	 * in the tree rooted at node.
	 */

	register int	i, nk;
	Tuple	tup;

	nk= N_KIND(node);
	if (N_AST1_DEFINED(nk)  && N_AST1(node) != (Node)0) mint(N_AST1(node));
	if (N_AST2_DEFINED(nk)  && N_AST2(node) != (Node)0) mint(N_AST2(node));
	if (N_AST3_DEFINED(nk)  && N_AST3(node) != (Node)0) mint(N_AST3(node));
	if (N_AST4_DEFINED(nk)  && N_AST4(node) != (Node)0) mint(N_AST4(node));
	if (N_LIST_DEFINED(nk) && N_LIST(node) != (Tuple)0) {
		tup = N_LIST(node);
		for (i = (int)*tup++; i > 0; i--)
			mint((Node)*tup++);
	}

	if (nk == as_name || nk == as_parenthesis || nk == as_condition)
		copy_attributes(N_AST1(node), node);
	else if (nk == as_qualify)
		copy_attributes(N_AST2(node), node);
}

void check_priv_instance(Tuple must_constrain, Symbolmap instance_map)
														/*;check_priv_instance*/
{
	/*
	 * For a late instantiation, verify that a private generic type that is
	 * used to declare an object has been instantiated with a constrained
	 * type.
	 */

	Fortup	ft1;
	Symbol	g_name, new_type;

	FORTUP(g_name = (Symbol), must_constrain, ft1);
		if (tup_mem((char *)g_name, must_constrain) ) {
			new_type = symbolmap_get(instance_map, g_name);
			if ( NATURE(new_type) == na_array
			  || (NATURE(new_type) == na_record && has_discriminants(new_type)
			  && (Node) default_expr((Symbol)discriminant_list(new_type)[2])
			  /* this is 1st discrim, as 'constrained' is added by expander */
			  == OPT_NODE )) {
				user_error(
 "usage of generic private type requires instantiation with constrained type");
			}
		}
	ENDFORTUP(ft1);
}

void expand_decl(Node node)									/*;expand_decl*/
{
	Fortup  ft1;
	Node    id_list_node, type_indic_node, init_node, first_obj_node,
	  const_val_node, decl_node, id_node, constrained_node;
	Symbol  init_type_name, first_obj_name, type_name, p;
	Tuple   tup;
	int     is_var_decl, init_len, init_len_defined,
	const_len, const_len_defined, is_agg;

	/*       Note: const decl are always single declarations (split by FE).
	 *       otherwise, the case of deferred constants would be more
	 *       difficult.
	 */
	id_list_node = N_AST1(node);
	type_indic_node = N_AST2(node);
	init_node = N_AST3(node);
	init_type_name = N_TYPE(init_node);
	is_var_decl    = N_KIND(node) == as_obj_decl;
	first_obj_node = (Node) ((Tuple) N_LIST(id_list_node))[1];
	first_obj_name = N_UNQ(first_obj_node);
	type_name      = TYPE_OF(first_obj_name);

	if (!is_var_decl && init_node == OPT_NODE) {
		/*
		 *      Deferred constant: transform into variable, as it has no
		 *      initialization and cannot be unconstrained (LRM 7.4.1(3))
		 *      Defer elaboration of this "variable" after elaboration of the
		 *      type, but before elaboration of any delayed type depending on
		 *      the same type.
		 */
		N_KIND(node) = as_obj_decl;
		emap_put(first_obj_name , (char *) TRUE);
#ifdef TBSN
		emap_defined = emap_get(type_name); 
		etup = EMAP_VALUE;
		if (!emap_defined || tup_size(etup) == 0) {
			ntup = tup_new1((char *) copy_node(node));
		}
		else {
			ntup = tup_new(tup_size(etup)+1);
			ntup[1] = (char *)copy_node(node);
			for (tupi = 1; tupi <= tup_size(etup); tupi++) {
				ntup[tupi+1] = etup[tupi];
			}
		}
		emap_put(type_name, (char *) ntup);
		delete_node(node);
#endif
	}
	else if (!is_var_decl && emap_get(first_obj_name)) {
		/* 
		 * Full declaration of a deferred constant, 
		 * transform into assignment.
		 */
		if (is_simple_type(type_name)) {
			make_assign_node(node, first_obj_node, init_node);
			expand(node);
			N_SIDE(node) = N_SIDE(init_node);
		}
		else {
			if (init_node == OPT_NODE) {
				/* record type */
				N_SIDE(node) = FALSE;
			}
			else {
				N_AST3(node) = OPT_NODE;
				expand(init_node);
				N_SIDE(node) = N_SIDE(init_node);
				make_insert_node(node, tup_new1((char *)copy_node(node)),
				  new_assign_node(first_obj_node, init_node));
			}
		}
		return;
	}

	/*
	 * Normal declaration.
	 * Remark: following tests are always FALSE for constants
	 */
	if (is_task_type(type_name)) {
		/* Initial value for task objects is create_task */
		init_node   = (Node) new_create_task_node(type_name);
		N_AST1(node) = id_list_node;
		N_AST2(node) = type_indic_node;
		N_AST3(node) = init_node;
	}
	else if (is_access_type(type_name) && init_node == OPT_NODE) {
		/* Initial value for (uninitialized) access objects is null*/
		init_node   = (Node) new_null_node(type_name);
		N_AST1(node) = id_list_node;
		N_AST2(node) = type_indic_node;
		N_AST3(node) = init_node;
	}

	/* 
	 * Remark: type_name always constrained for variables 
	 */
	if (is_array_type(type_name) && init_node != OPT_NODE) {
		/* Try to propagate constraints statically */
		if (!is_unconstrained(type_name) && is_unconstrained(init_type_name)) {
			init_len  = array_nelem(init_node);
			init_len_defined = array_nelem_defined;
			const_len = array_nelem(type_indic_node);
			const_len_defined = array_nelem_defined;
			if (init_len_defined && const_len_defined) {
				if (init_len == const_len) {
					N_TYPE(init_node) = type_name;
				}
				else {
					make_raise_node(init_node, symbol_constraint_error);
					USER_WARNING("Mismatched length will raise",
					  " CONSTRAINT_ERROR");
				}
			}
		}
		else if (is_unconstrained(type_name) && 
		  !is_unconstrained(init_type_name)) {
			N_UNQ(type_indic_node) = init_type_name;
			FORTUP(id_node = (Node), N_LIST(id_list_node), ft1);
				TYPE_OF(N_UNQ(id_node)) = init_type_name;
			ENDFORTUP(ft1);
		}
	}

	expand(type_indic_node);
	N_SIDE(node) = N_SIDE(type_indic_node);
	p = INIT_PROC((Symbol) base_type(type_name));
	if (init_node == OPT_NODE  && p != (Symbol)0) {
		init_node = build_init_call(first_obj_node, p, type_name, OPT_NODE);
		expand(init_node);
		N_AST1(node) = id_list_node;
		N_AST2(node) = type_indic_node;
		N_AST3(node) = init_node;
		decl_node   = node;
	}
	else if (init_node != OPT_NODE ) {
		is_agg = is_aggregate(init_node); /* may become an insert */
		expand(init_node);
		init_type_name = N_TYPE(init_node);
		if (is_agg) {
			replace_name(init_node, N_UNQ(init_node), first_obj_name);
		}
		if (is_agg && is_record_type(type_name) && is_unconstrained(type_name)){
			if (N_KIND(node) == as_obj_decl) {
				/* Correct bit constrained in aggregate if unconstrained var */
				if (N_KIND(init_node) == as_insert ) {
					tup = N_LIST(N_AST1(N_AST1(N_AST1(init_node))));
				}
				else if ( N_KIND(init_node) == as_record_ivalue
				  || N_KIND(init_node) == as_record_aggregate) {
					tup = N_LIST(N_AST1(N_AST1(init_node)));
				}
				else
					chaos("not so impossible expand2 problem");
				constrained_node = (Node) tup[1];
				const_val_node = N_AST2(constrained_node);
				N_VAL(const_val_node) = (char *) int_const(FALSE);
			}
			else if (NATURE(type_name) == na_record
			  && N_KIND(node) == as_const_decl) {
				/* Propagate type of aggregate to constant */
				TYPE_OF(first_obj_name) = init_type_name;
				N_UNQ(type_indic_node) = init_type_name;
			}
		}
		/* Propagate possible pre-statements in front of this node*/
		if (N_KIND(init_node) == as_insert) {
			propagate_insert(init_node, node);
			decl_node = N_AST1(node);
		}
		else {
			decl_node = node;
		}
		N_SIDE(node) |= N_SIDE(init_node);
		if (is_array_type(type_name)
		  && is_unconstrained(type_name) && !is_unconstrained(init_type_name)) {
			/*
			 * Lucky! expand of init_node has been able to determine
			 * the constraints...
			 */
			N_UNQ(type_indic_node) = init_type_name;
			FORTUP(id_node  = (Node), N_LIST(id_list_node), ft1);
				TYPE_OF(N_UNQ(id_node)) = init_type_name;
			ENDFORTUP(ft1);
		}
	}
	else {
		decl_node = node;
	}

	/* If side-effect, replace by a list of single object decl.*/
	if (N_SIDE(decl_node))
		make_single_decl_list(node, decl_node);
}

void expand_type(Node node)									/*;expand_type*/
{
	Fortup   ft1;
	Node     id_node, small_node, proc_init_node, invariant_node,
	  variant_node, comp_node, delayed_node;
	Node     cases_node, case_node;
	Symbol   type_name, parent_type, comp_name, dummy;
	Tuple    sig, tup, discr_list;
	int      nat;

	/* Generate complete declaration if simple derivation is not enough*/
	id_node   = N_AST1(node);
	type_name    = N_UNQ(id_node);

	N_SIDE(node) = FALSE;
	CONTAINS_TASK(type_name) = FALSE;

	if (TYPE_OF(type_name) == symbol_incomplete) {
		/* case of an incomplete type in the private part of a package,
		 * whose  complete type declaration has appeared in the body,
		 * and saved in a dummy symbol. Retrieve, and update the entry
		 * for the type.
		 */
		dummy = N_TYPE(node);
		NATURE(type_name)    = NATURE(dummy);
		TYPE_OF(type_name)   = TYPE_OF(dummy);
		SIGNATURE(type_name) = SIGNATURE(dummy);
		OVERLOADS(type_name) = OVERLOADS(dummy);
		root_type(type_name) = root_type(dummy);
	}
	parent_type  = TYPE_OF(type_name);
	nat = NATURE(type_name);
	if (nat == na_type) {
		/* Derived or predefined type*/
		if (is_fixed_type(type_name)) {
			/* Provide small if no representation clause*/
			sig = SIGNATURE(type_name);
			small_node = (Node) sig[5];
			if (small_node == OPT_NODE) {
				/* Processing formerly done here now down by new_fixed_type()
				 * in adasem, so it is an error to reach here.
				 */
				chaos("fixed with small OPT_NODE");
			}
			CONTAINS_TASK(type_name) = (char *) FALSE;
		}
		else if (CONTAINS_TASK(parent_type)  /* derived access on task*/
		  && is_access_type(parent_type)) { /* needs own template*/
			NATURE(type_name)        = na_access;
			SIGNATURE(type_name)     = SIGNATURE(parent_type);
			CONTAINS_TASK(type_name) = (char *) TRUE;
		}
		else {
			CONTAINS_TASK(type_name) = CONTAINS_TASK(parent_type);
			SIGNATURE(type_name)     = SIGNATURE(parent_type);
			INIT_PROC(type_name)     = INIT_PROC(parent_type);
		}
	}
	else if (nat == na_array) {
		comp_name                = (Symbol) ((Tuple) SIGNATURE(type_name))[2];
		CONTAINS_TASK(type_name) = CONTAINS_TASK(comp_name);
		proc_init_node           = build_proc_init_ara(type_name);
		if (proc_init_node != OPT_NODE) {
			expand(proc_init_node);
			make_insert_node(node, tup_new1((char *) copy_node(node)),
			  proc_init_node);
		}
	}
	else if (nat == na_record) {
		/* review following code: only altering 2nd part of SIGNATURE */
		sig = SIGNATURE(type_name);
		discr_list = (Tuple) sig[3];
		invariant_node = (Node) sig[1];
		variant_node = (Node) sig[2];

		FORTUP(comp_node= (Node), N_LIST(invariant_node), ft1);
			expand(comp_node);
			N_SIDE(node) |= N_SIDE(comp_node);
		ENDFORTUP(ft1);
		/* In case of a variant part of the type:
		 *      case disc is
		 *        when a..b => null;
		 *      end case;
		 * the record type is said to have no variant part.
		 */
		if (variant_node != OPT_NODE)  {
			cases_node = N_AST2(variant_node);
			tup = tup_copy(N_LIST(cases_node));
			case_node = (Node) tup_fromb(tup);
			comp_node = N_AST2(case_node);
			if (tup_size(tup) == 0 
			  && N_AST1(comp_node) == OPT_NODE
			  && N_AST2(comp_node) == OPT_NODE)  {
				variant_node = OPT_NODE;
				SIGNATURE(type_name)[2] = (char *) variant_node;
			}
		}
		expand(variant_node);

		proc_init_node  = build_proc_init_rec(type_name);
		if (proc_init_node != OPT_NODE) {
			expand(proc_init_node);
			make_insert_node(node, tup_new1((char *) copy_node(node)),
			  proc_init_node);
		}
	}
	else if (nat == na_subtype) {
		N_AST3(node) = (Node)0;
		N_KIND(node) = as_subtype_decl;
		expand(node);
	}
	else if (nat == na_task_type) {
		parent_type              = TYPE_OF(type_name);
		SIGNATURE(type_name)     = SIGNATURE(parent_type);
		CONTAINS_TASK(type_name) = (char *) TRUE;
	}

	if (emap_get(type_name)) {
		delayed_node = node_new(as_declarations);
		if (emap_get(type_name))
			N_LIST(delayed_node) = EMAP_VALUE;
		expand(delayed_node);
		N_SIDE(node) |= N_SIDE(delayed_node);
		make_insert_node(node, tup_new1((char *)copy_node(node)), delayed_node);
		emap_undef(type_name);
	}
}

void expand_subtype(Node node)								/*;expand_subtype*/
{
	Node   id_node, lbd_node, ubd_node, de_node, delayed_node;
	Symbol type_name, parent_type;
	Tuple  field_list, constraint;
	int    co_kind, i;

	id_node   = N_AST1(node);
	type_name   = N_UNQ(id_node);
	parent_type = TYPE_OF(type_name);

	constraint = (Tuple) get_constraint(type_name);
	co_kind = (int) constraint[1];
	if (co_kind == co_access) {
		N_SIDE(node) = FALSE;
	}
	else if (co_kind == co_range) {
		lbd_node = (Node) constraint[2];
		ubd_node = (Node) constraint[3];
		mint(lbd_node);
		mint(ubd_node);
		expand(lbd_node);
		expand(ubd_node);
		N_SIDE(node) = N_SIDE(lbd_node) | N_SIDE(ubd_node);
	}
	else if (co_kind == co_digits) {
		lbd_node = (Node) constraint[2];
		ubd_node= (Node) constraint[3];
		expand(lbd_node);
		expand(ubd_node);
		N_SIDE(node) = N_SIDE(lbd_node) | N_SIDE(ubd_node);
	}
	else if (co_kind == co_delta) {
		lbd_node = (Node) constraint[2];
		ubd_node = (Node) constraint[3];
		expand(lbd_node);
		expand(ubd_node);
		N_SIDE(node) = N_SIDE(lbd_node) | N_SIDE(ubd_node);
	}
	else if (co_kind == co_discr) {
		field_list = (Tuple) constraint[2];
		N_SIDE(node) = FALSE;
		/* In C, field_list is tuple with successive domain symbol
		 * and range node values.
		 */
		for (i = 1; i <= tup_size(field_list); i += 2) {
			de_node = (Node) field_list[i+1];
			expand(de_node);
			N_SIDE(node) |= N_SIDE(de_node);
		}
	}
	else if (co_kind == co_index) {
		N_SIDE(node) = FALSE;
	}
	else
		compiler_error_c("Unknown constraint in subtype decl: ", constraint);

	/*       Transmit tasks_declared: */
	CONTAINS_TASK(type_name) = CONTAINS_TASK(parent_type);

	if (emap_get(type_name)) {
		delayed_node         = node_new(as_declarations);
		N_LIST(delayed_node) = EMAP_VALUE;
		expand(delayed_node);
		N_SIDE(node) |= N_SIDE(delayed_node);
		make_insert_node(node, tup_new1((char *)copy_node(node)), delayed_node);
		emap_undef(type_name);
	}
}

void expand_attr(Node node)									/*;expand_attr*/
{
	Node   precision, arg1, arg2, low_node, high_node;
	Symbol type_name, index_name, obj_name;
	Tuple  index_t, tup;
	Rational    delta, fx_low, fx_high, fx_ma;
	int    attr, dim, discr_dep, result, i;
	int    *rat_n, *rat_d; /* Multi-precision integers */

	Const   low_const, high_const;

	arg1 = N_AST2(node);
	arg2 = N_AST3(node);
	attr = (int) attribute_kind(node);

	/* BASE attribute is evaluated to a type mark.  */
	if (attr == ATTR_BASE) {
		make_name_node(node, base_type(N_UNQ(arg2)));
	}
	else {
		expand(arg1);
	}

	if ((arg2 != (Node)0 ? arg2: OPT_NODE) != OPT_NODE)
		expand(arg2);

	/* Transformations on attributes */
	switch (attr) {
	case(ATTR_O_RANGE):
	case(ATTR_O_FIRST):
	case(ATTR_O_LAST):
	case(ATTR_O_LENGTH):

		/* if the first parameter is a simple name, if its type is
		 * constrained and, if it is an array, its bounds must no depend on
		 * discriminant, then we can make a
		 * conversion to an attribute to its type. This will be very useful
		 * since the expansion of the T_attribute may produce some constant
		 */

		discr_dep = FALSE;
		type_name = get_type(arg1);
		if (is_array_type(type_name)) {
			index_t = index_types(type_name);
			dim = get_ivalue_int(arg2);
			index_name   = (Symbol) index_t[dim];
			tup = SIGNATURE(index_name);
			low_node = (Node) tup[2];
			high_node = (Node) tup[3];
			discr_dep = is_discr_ref(low_node) || is_discr_ref(high_node);
		}
		if (is_simple_name (arg1) && !is_unconstrained (get_type(arg1))
		  && !discr_dep) {
			N_AST2 (node) = new_name_node (get_type (arg1));
			/* convert from O_ to T_ attribute by adding one */
			attribute_kind(node) = (char *) ((int)attribute_kind(node) + 1);
			expand (node); 
		}

#ifdef TBSL

	/* In case of an aggregate, the object itself declares its type and this
	* transformation leads to a RELAY_SET problem. 
	*/

		/* Transform into T_xxx of type if possible */
		type_name = get_type(arg1);
		if (is_array_type(type_name)) {
			index_t = index_types(type_name);
			dim = get_ivalue_int(arg2);
			index_name   = (Symbol) index_t[dim];
			tup = SIGNATURE(index_name);
			low_node = (Node) tup[2];
			high_node = (Node) tup[3];
			discr_dep = is_discr_ref(low_node) || is_discr_ref(high_node);
		}
		else {
			discr_dep = FALSE;
		}
		if (! (discr_dep || is_unconstrained(type_name))) {
			N_KIND(arg1) = as_simple_name;
			N_AST1(arg1) = (Node)0;
			N_AST2(arg1) = (Node)0;
			N_AST3(arg1) = (Node)0;
			N_AST3(arg1) = (Node)0;
			N_UNQ(arg1)  = type_name;
			N_TYPE(arg1) = type_name;
			/* convert from O_ to T_ attribute by adding one */
			attribute_kind(node) = (char *) ((int)attribute_kind(node) + 1);
			expand(node);
		}
#endif
		break;
	case(ATTR_T_FIRST):
		type_name = N_UNQ(arg1);
		if (is_array_type(type_name)) {
			index_t = index_types(type_name);
			dim = get_ivalue_int(arg2);
			type_name = (Symbol) index_t[dim];
		}
		tup = SIGNATURE(type_name);
		low_node = (Node) tup[2];
		if (is_ivalue(low_node)) {
			copy_attributes(low_node, node);
		}
		break;

	case(ATTR_T_LAST):
		type_name = N_UNQ(arg1);
		if (is_array_type(type_name)) {
			index_t = index_types(type_name);
			dim = get_ivalue_int(arg2);
			type_name = (Symbol) index_t[dim];
		}
		tup = SIGNATURE(type_name);
		high_node = (Node) tup[3];
		if (is_ivalue(high_node)) {
			copy_attributes(high_node, node);
		}
		break;

	case(ATTR_O_CONSTRAINED):
		for (;;) {
			if (N_KIND(arg1) == as_index || N_KIND(arg1) == as_selector) {
				break;
				/* constant_folding TBSL */
			}
			else if (N_KIND(arg1) == as_all) {
				/* Allocated objects always constrained */
				make_ivalue_node(node, int_const(TRUE), symbol_boolean);
				break;
			}
			else if (N_KIND(arg1) == as_simple_name) {
				obj_name = N_UNQ(arg1);
				if (NATURE(obj_name) == na_constant
				  || NATURE(obj_name) == na_in
				  || ! is_unconstrained(TYPE_OF(obj_name))) {
					make_ivalue_node(node, int_const(TRUE), symbol_boolean);
				}
				break;
			}
			else {
				compiler_error("Illegal prefix for attribute");
			}
		}
		break;

	case(ATTR_POS):
		/* Transform into convert */
		/* Since N_AST3 and N_UNQ overlaid, clear N_AST3 field if 
		 * currently defined.
		 */
		if (N_AST3_DEFINED(N_KIND(node))) {
			N_AST3(node) = (Node)0;
		}
		N_KIND(node) = as_convert;
		N_AST1(node) = arg1;
		N_AST2(node) = arg2;
		break;

	case(ATTR_COUNT):
		/*This attribute is only allowed within the body of T (9.9(5)) */
		N_AST1(arg1) = OPT_NODE;
		break;

	case(ATTR_O_SIZE):
		/* apply it to type of prefix. */
		/* type_name = get_type(arg1);
 	 	 * make_name_node(arg1, type_name);
	 	 * attribute_kind(node) = (char *) ATTR_T_SIZE;
		 */
		break;

	case(ATTR_WIDTH):

		type_name = N_UNQ(arg1);
		if (is_static_type(type_name)) {
			int low_int, high_int, ivalue_int;
			tup = SIGNATURE(type_name);
			low_node = (Node) tup[2];
			high_node = (Node) tup[3];
			low_const = get_ivalue (low_node);
			high_const = get_ivalue (high_node);

			/* this following test has been added because the bounds of the
			 * range may be not static. In the previous version there was an
			 * error during the get_ivalue_int.  Some optimizations can still
			 * be performed since we just generate the WIDTH attribute
			 */

			if (low_const->const_kind != CONST_OM
			  && high_const->const_kind != CONST_OM) {
				low_int   = get_ivalue_int(low_node);
				high_int  = get_ivalue_int(high_node);
				if (is_integer_type(type_name)) {
					if (low_int > high_int)
						result = 0;
					else {
						char *val_str = emalloct(10, "expand-attr-wid-1");
						low_int =  abs (low_int);
						high_int = abs (high_int);
						ivalue_int = (low_int > high_int ? low_int : high_int);
						sprintf(val_str, " %d", ivalue_int);
						ivalue_int = strlen(val_str);
						efreet(val_str, "expand-attr-wid-2");
						result = ivalue_int;
					}
				}
				else {	 /* Enumeration types */
					int len, v;
					tup = (Tuple) literal_map(root_type(type_name));
					ivalue_int = 0;
					for (i = 1; i <= tup_size(tup); i += 2) {
						len = strlen(tup[i]);
						v = (int) tup[i+1];
						if (len > ivalue_int && (v >= low_int && v  <=high_int))
							ivalue_int = len;
					}
					result = ivalue_int;
				}
				make_ivalue_node(node, int_const(result), symbol_integer);
			} 
		}
		break;

	/* The minimum number of characters needed for the integer
	 *  part of the decimal representation (including sign).
	 */
	case(ATTR_FORE):
		tup = SIGNATURE(N_UNQ(arg1));
		low_node = (Node) tup[2];
		high_node = (Node) tup[3];
		if (is_ivalue(low_node) && is_ivalue(high_node)) {
			fx_low = RATV((Const)N_VAL(low_node));
			fx_high = RATV((Const) N_VAL(high_node));
			if (rat_geq(rat_abs(fx_high), rat_abs(fx_low)))
				fx_ma = rat_abs(fx_high);
			else 
				fx_ma = rat_abs(fx_low);
			rat_n = num(fx_ma);
			rat_d = den(fx_ma);
			result = 2;
			while (int_geq(int_quo(rat_n , rat_d) , ivalue_10)) {
				rat_d = int_mul(rat_d, ivalue_10);
				result += 1;
			}
			make_ivalue_node(node, int_const(result), symbol_integer);
		}
		break;

	/*      The number of decimal digits needed after the decimal point
	 *		= smallest n such that (10**N)*FX'DELTA >= 1.0
	 */
	case(ATTR_AFT):
		tup = SIGNATURE(N_UNQ(arg1));
		low_node = (Node) tup[2];
		high_node = (Node) tup[3];
		precision = (Node) tup[4];
		delta = RATV((Const) N_VAL(precision));
		fx_low = RATV((Const)N_VAL(low_node));
		fx_high = RATV((Const) N_VAL(high_node));
		result = 1;
		while (rat_lss(delta, rat_fri(int_fri(1), int_fri(10)) )){
			delta = rat_mul(delta, rat_fri(int_fri(10), int_fri(1)));
			result += 1;
		}
		make_ivalue_node(node, int_const(result), symbol_integer);
		break;

	case(ATTR_SAFE_LARGE):
		/* Equal to 'large of base type. */
		N_UNQ(arg1) = base_type(N_UNQ(arg1));
		attribute_kind(node) = (char *)ATTR_LARGE;
		break;

	case(ATTR_SAFE_SMALL):
		/* Equal to 'small of base type. */
		N_UNQ(arg1) = base_type(N_UNQ(arg1));
		attribute_kind(node) = (char *)ATTR_SMALL;
		break;
	}

	N_SIDE(node) = FALSE;
}

void expand_string(Node node)								/*;expand_string*/
{
	Node   lbd_node, ubd_node, check_node, range_lbd_node, range_ubd_node,
	  base_lbd_node;
	Symbol str_type, comp_type, new_type, indx_type, base_index_type;
	Tuple  ntup, stmts_list, tup, decls;
	int    str_len, lowest_char, highest_char, n, ubd_val_int, lbd, ubd, i;
	Const  hg_val, lw_val;

	str_type = N_TYPE(node);
	str_len  = tup_size((Tuple) N_VAL(node));
	if (str_len != 0) {
		/* SETL has lowest_char=MAX/...highest_char = MIN ... !! - we fix this*/
		ntup = (Tuple) N_VAL(node);
		lowest_char = (int) ntup[1];
		highest_char = (int) ntup[1];
		n = tup_size(ntup);
		for (i = 2; i <= n; i++) {
			if ((int)ntup[i] < lowest_char) lowest_char = (int) ntup[i];
			if ((int)ntup[i] > highest_char) highest_char = (int) ntup[i];
		}
		/*lowest_char  = max/N_VAL(node); !!*/
		/*highest_char = min/N_VAL(node); !!*/
		comp_type    = (Symbol) component_type(str_type);
		stmts_list   = tup_new(0);
		tup = SIGNATURE(comp_type);
		lbd_node = (Node) tup[2];
		ubd_node = (Node) tup[3];

		lw_val = get_ivalue(lbd_node);
		if (lw_val->const_kind != CONST_OM) {
			if (lowest_char <  get_ivalue_int(lbd_node)) {
				make_raise_node(node, symbol_constraint_error);
				USER_WARNING("Character in string will raise ",
				  " CONSTRAINT_ERROR");
			}
		}
		else {
			check_node        = node_new(as_discard);
			N_AST1(check_node) = new_qual_range_node( new_ivalue_node(
			  int_const(lowest_char), symbol_character), comp_type);
			N_TYPE(check_node) = comp_type;
			N_SIDE(check_node) = FALSE;
			stmts_list = tup_new1((char *) check_node);
		}
		hg_val = get_ivalue(ubd_node);
		if (hg_val->const_kind != CONST_OM) {
			if (highest_char >  get_ivalue_int(ubd_node)) {
				make_raise_node(node, symbol_constraint_error);
				USER_WARNING("Character in string will raise ",
				  "CONSTRAINT_ERROR");
			}
		}
		else {
			check_node        = node_new(as_discard);
			N_AST1(check_node) = new_qual_range_node( new_ivalue_node(
			  int_const(highest_char), symbol_character), comp_type);
			N_TYPE(check_node) = comp_type;
			N_SIDE(check_node) = FALSE;
			stmts_list = tup_with(stmts_list, (char *) check_node);
		}
		if (tup_size(stmts_list) != 0) {
			make_insert_node(node, stmts_list, copy_node(node));
			node       = N_AST1(node);
			N_SIDE(node) = FALSE;
		}
	}

	/* construct subtype */

	tup = index_types(str_type);
	indx_type = (Symbol) tup[1];
	tup = SIGNATURE(indx_type);
	lbd_node = (Node) tup[2];
	ubd_node = (Node) tup[3];
	if (is_ivalue(lbd_node)) {
		lbd = get_ivalue_int(lbd_node);
		base_index_type = base_type(indx_type);
		tup = SIGNATURE(base_index_type);
		base_lbd_node = (Node) tup[2];
		if (str_len == 0
		  && const_eq(get_ivalue(lbd_node), get_ivalue(base_lbd_node))) {
			/* LRM 4.2(3) */
			make_raise_node(node, symbol_constraint_error);
			USER_WARNING("Null string will raise CONSTRAINT_ERROR",
			  " (LRM 4.2(3))" );
		}
		else {
			ubd_val_int    = lbd + str_len - 1;
			if (is_ivalue(ubd_node)) {
				ubd = get_ivalue_int(ubd_node);
				if (!is_unconstrained(str_type)) {
					if ((str_len != 0 && ubd_val_int != ubd)
					  || (str_len == 0 && ubd >= lbd)) {
						make_raise_node(node, symbol_constraint_error);
						USER_WARNING("String literal will raise ",
						  "CONSTRAINT_ERROR");
					}
					else return;	/* static bounds ok. */
				}
				else {	/* unconstrained context. Length may be too big. */
					if (ubd_val_int > ubd) {
						make_raise_node(node, symbol_constraint_error);
						USER_WARNING("String literal will raise ",
						  "CONSTRAINT_ERROR");
					}
				}
			}
			/* else gen_subtype will emit a qual sub */
		}
		range_lbd_node = copy_node(lbd_node);
		range_ubd_node = new_ivalue_node(int_const(ubd_val_int),
		  N_TYPE(range_lbd_node));
	}
	else { /* lbd_node is not an ivalue */
		/* write range_lbd_node  as an attribute node */
		range_lbd_node = new_attribute_node(ATTR_T_FIRST,
		  new_name_node(indx_type), OPT_NODE, indx_type);
		range_ubd_node = new_binop_node(symbol_addi, range_lbd_node,
		  new_ivalue_node(int_const(str_len-1), base_type(indx_type)),
		  base_type(indx_type));
		/* gen_subtype will emit a qual sub on the index type */
	}

	if (N_KIND(node) != as_raise) {
		tup = constrained_type(str_type, range_lbd_node, range_ubd_node);
		new_type = (Symbol) tup[1];
		decls = (Tuple) tup[2];
		N_TYPE(node) = new_type;
		N_SIDE(node) = FALSE;
		make_insert_node(node, decls, copy_node(node));
	}
	N_SIDE(node) = FALSE;
}

void expand_op(Node node)										/*;expand_op*/
{
	Node   op_node, args_node, arg1, arg2, conv_node, to_type_node, type_node,
	  lbd_node, ubd_node, constraint_node, lbd_node1, ubd_node1;
	Symbol op_name, range_name, type_name;
	Symbol indx_t, str1_type;
	Tuple  tup, constraint;
	Node   comp;

	op_node = N_AST1(node);
	args_node = N_AST2(node);
	op_name = N_UNQ(op_node);
	arg1 = (Node) ((Tuple)N_LIST(args_node) [1]);
	arg2 = (Node) ((Tuple)N_LIST(args_node) [2]);

	/* Constant folding: concatenation of two non-null string which index_type
	 * is static.
	 */
	if (op_name == symbol_cat && N_KIND(arg1) == as_string_ivalue
	  && N_KIND(arg2) == as_string_ivalue ) {
		str1_type = N_TYPE(arg1);
		indx_t = (Symbol) index_types(str1_type)[1];
		tup = SIGNATURE(indx_t);
		lbd_node1 = (Node) tup[2];
		ubd_node1 = (Node) tup[3];
		/* if the index_type is static and the length of both the strings
		 * is not null, then we transform the node into a string_ivalue
		 * which is the concatenation of the two strings.
		 */
		if (N_KIND(lbd_node1) == as_ivalue && N_KIND(ubd_node1) == as_ivalue
		  && tup_size((Tuple) N_VAL(arg1)) &&tup_size((Tuple) N_VAL(arg2))) {
			N_KIND(node) = as_string_ivalue;
			N_AST1(node) = N_AST2(node) = N_AST3(node) = N_AST4(node) = (Node)0;
			N_VAL(node) = (char *) tup_add((Tuple)N_VAL(arg1),
			  (Tuple)N_VAL(arg2));
			N_TYPE(node) = str1_type;
			expand(node);	/* and generate subtype, etc. */
		}
	}

	/* case of the new catenation instructions */

	else if  (op_name == symbol_cat_ca) {
		comp = copy_node (arg1);
		N_KIND (arg1) = as_row;
		N_AST1 (arg1) = comp;
		N_AST2 (arg1) = (Node) 0;
		N_TYPE (arg1) = N_TYPE (node);
		N_UNQ (N_AST1(node)) = symbol_cat;
	}
	else if  (op_name == symbol_cat_ac) {
		comp = copy_node (arg2);
		N_KIND (arg2) = as_row;
		N_AST1 (arg2) = comp;
		N_AST2 (arg2) = (Node) 0;
		N_TYPE (arg2) = N_TYPE (node);
		N_UNQ (N_AST1(node)) = symbol_cat;
	}
	else if  (op_name == symbol_cat_cc) {
		comp = copy_node (arg2);
		N_KIND (arg2) = as_row;
		N_AST1 (arg2) = comp;
		N_AST2 (arg2) = (Node) 0;
		N_TYPE (arg2) = N_TYPE (node);

		comp = copy_node (arg1);
		N_KIND (arg1) = as_row;
		N_AST1 (arg1) = comp;
		N_AST2 (arg1) = (Node) 0;
		N_TYPE (arg1) = N_TYPE (node);

		N_UNQ (N_AST1(node)) = symbol_cat;
	}
	/* Transform some operations: */
	else if (op_name == symbol_mulfli || op_name == symbol_divfli) {
		conv_node           = node_new(as_convert);
		to_type_node        = new_name_node(symbol_universal_real);
		N_AST1(conv_node)   = to_type_node;
		N_AST2(conv_node)   = arg2;
		N_TYPE(conv_node)   = symbol_universal_real;
		arg2                = conv_node;
		tup  = tup_new(2);
		tup[1] = (char *) arg1; 
		tup[2] = (char *) arg2;
		N_LIST(args_node)   = tup;
		N_UNQ(op_node) = (op_name == symbol_mulfli) ? symbol_mulfl 
		  : symbol_divfl;
	}
	else if (op_name == symbol_mulifx) {
		tup = tup_new(2);
		tup[1] = (char *) arg2; 
		tup[2] = (char *) arg1;
		N_LIST(args_node)   = tup;
		N_UNQ(op_node)      = symbol_mulfxi;
	}
	else if (op_name == symbol_in || op_name == symbol_notin) {
		if (!is_simple_name(arg2)) {
			/* Add subtype declaration */
			range_name = new_unique_name("range");
			type_name  = N_TYPE(arg2);
			if (N_KIND(arg2) == as_attribute) {
				lbd_node        = copy_node(arg2);
				ubd_node        = copy_tree(arg2);
				/*lbd_attr_node = N_AST1(lbd_node); -- not needed in C version*/
				/*ubd_attr_node = N_AST1(ubd_node); -- not needed in C version*/
				if ((int) attribute_kind(lbd_node) == ATTR_T_RANGE) {
					attribute_kind(lbd_node) = (char *) ATTR_T_FIRST;
					attribute_kind(ubd_node) = (char *)ATTR_T_LAST;
				}
				else {  /* 'O_RANGE' */
					attribute_kind(lbd_node) = (char *) ATTR_O_FIRST;
					attribute_kind(ubd_node) = (char *) ATTR_O_LAST;
				}
				constraint = constraint_new(co_range);
				constraint[2] = (char *) lbd_node;
				constraint[3] = (char *) ubd_node;
			}
			else { /* as_subtype */
				Tuple t;

				constraint_node      = N_AST2(arg2);
				lbd_node = N_AST1(constraint_node);
				ubd_node = N_AST2(constraint_node);

				t = SIGNATURE(type_name);
				constraint = constraint_new((int)numeric_constraint_kind(t));
				numeric_constraint_low(constraint)  = (char *) lbd_node;
				numeric_constraint_high(constraint) = (char *) ubd_node;

				/* inherit precision of real subtype from parent type */
				if (numeric_constraint_kind(t) == (char *)co_digits) {
					numeric_constraint_digits(constraint) =
					  numeric_constraint_digits(t);
				}
				else if (numeric_constraint_kind(t) == (char *)co_delta) {
					numeric_constraint_delta(constraint) =
					  numeric_constraint_delta(t);
					numeric_constraint_small(constraint) =
					  numeric_constraint_small(t);
				}
			}
			NATURE(range_name) = na_subtype;
			TYPE_OF(range_name) = base_type(type_name);
			SIGNATURE(range_name) = constraint;
			ALIAS(range_name) = ALIAS(type_name);
			type_node             = node_new(as_subtype_decl);
			N_AST1(type_node)      = new_name_node(range_name);
			make_insert_node(node,tup_new1((char *)type_node), copy_node(node));
			make_name_node(arg2, range_name);
		}
	}

	expand(arg1);
	expand(arg2);
	N_SIDE(node) = N_SIDE(arg1) | N_SIDE(arg2);
}

void expand_for(Node node)										/*;expand_for*/
{
	Node   id_node, range_node, low_node, high_node, ubd_node, lbd_node,
	  arg1, arg2, type_node, new_range_node, decl_node;
	Symbol type_name, type_mark;
	Const  lbd, ubd, low_const, high_const;
	Tuple  tup;
	int    nk, attr_prefix;

	id_node = N_AST1(node);
	range_node = N_AST2(node);
	nk = N_KIND(range_node);
	if (nk == as_subtype){
		type_node = N_AST1(range_node);
		type_mark = N_UNQ(type_node);
		new_range_node    = N_AST2(range_node);
		low_node = N_AST1(new_range_node);
		high_node = N_AST2(new_range_node);
		type_name = new_unique_name("loop_type");
		tup = constraint_new(co_range);
		tup[2] = (char *) low_node;
		tup[3] = (char *) high_node;
		new_symbol(type_name, na_subtype, type_mark, tup, ALIAS(type_mark));
		if (not_included(type_name, type_mark) ) {
			decl_node = new_subtype_decl_node(type_name);
			expand(decl_node);
			make_insert_node(node,tup_new1((char *)decl_node), copy_node(node));
			node = N_AST1(node);
			type_node = new_name_node(type_name);
			low_node  = new_attribute_node(ATTR_T_FIRST, type_node, OPT_NODE,
			  type_name);
			high_node = new_attribute_node(ATTR_T_LAST, type_node, OPT_NODE,
			  type_name);
		}
		else {
			/* we don't need type_name*/
			new_symbol(type_name, na_void, (Symbol)0, (Tuple)0, (Symbol)0);
		}
	}
	else if (nk == as_range) {
		low_node = N_AST1(range_node);
		high_node = N_AST2(range_node);
	}
	else if (nk == as_name) {
		range_node = N_AST1(range_node);
		type_name = N_UNQ(range_node);
		tup  = get_constraint(type_name);
		low_node = (Node) tup[2];
		high_node = (Node) tup[3];
		if (!is_ivalue(low_node) || !is_ivalue(high_node)) {
			low_node = new_attribute_node(ATTR_T_FIRST,
			  copy_node(range_node), OPT_NODE, type_name);
			high_node= new_attribute_node(ATTR_T_LAST,
			  copy_node(range_node), OPT_NODE, type_name);
		}
	}
	else if (nk == as_simple_name) {
		type_name = N_UNQ(range_node);
		tup = get_constraint(type_name);
		low_node = (Node) tup[2];
		high_node = (Node) tup[3];
		if (!is_ivalue(low_node) || !is_ivalue(high_node)) {
			low_node = new_attribute_node(ATTR_T_FIRST,
			  copy_node(range_node), OPT_NODE, type_name);
			high_node= new_attribute_node(ATTR_T_LAST,
			  copy_node(range_node), OPT_NODE, type_name);
		}
	}
	else if (nk == as_attribute) {
		/*att_node = N_AST1(range_node);*/
		arg1 = N_AST2(range_node);
		arg2 = N_AST3(range_node);
		attr_prefix = (int)attribute_kind(range_node)-ATTR_RANGE;
		/* 'T' or 'O'*/
		attribute_kind(range_node) = (char *) ((int)attr_prefix + ATTR_FIRST);
		low_node = range_node;
		high_node = new_attribute_node(attr_prefix + ATTR_LAST,
		  copy_node(arg1), copy_node(arg2), get_type(range_node));
	}
	else {
		compiler_error_k("Unexpected range in for: ", range_node );
		low_node = high_node = OPT_NODE;
	}
	expand(low_node);
	expand(high_node);
	low_const = get_ivalue(low_node);
	high_const = get_ivalue(high_node);
	tup = get_constraint(get_type(range_node));
	lbd_node = (Node) tup[2];
	ubd_node = (Node)tup[3];
	if (low_const->const_kind != CONST_OM
	  && high_const->const_kind != CONST_OM
	  && get_ivalue_int(high_node) < get_ivalue_int(low_node) ) {
		/* static null range */
		delete_node(node);
	}
	else {
		lbd = get_ivalue(lbd_node);
		ubd = get_ivalue(ubd_node);
		if (low_const->const_kind != CONST_OM
		  && high_const->const_kind != CONST_OM
		  && lbd->const_kind != CONST_OM
		  && ubd->const_kind != CONST_OM
		  && (get_ivalue_int(lbd_node) > get_ivalue_int(low_node)
		  || get_ivalue_int(ubd_node) < get_ivalue_int(high_node))) {
			/* static violation of constraints */
			make_raise_node(node, symbol_constraint_error);
			USER_WARNING("Evaluation of range will raise",
			  " CONSTRAINT_ERROR");
		}
		else {
			N_AST1(node) = id_node;
			N_AST2(node) = low_node;
			N_AST3(node) = high_node;
		}
	}
}
