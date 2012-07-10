/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* aggr.c : translation of aggr.stl */

#define GEN
#include "hdr.h"
#include "vars.h"
#include "gvars.h"
#include "attr.h"
#include "miscprots.h"
#include "setprots.h"
#include "gutilprots.h"
#include "gnodesprots.h"
#include "gmiscprots.h"
#include "smiscprots.h"
#include "initobjprots.h"
#include "expandprots.h"
#include "aggrprots.h"

static int tup_eq(Tuple, Tuple);
static Tuple aggr_choice(Node, Tuple, Symbol);
static int needs_subtype(Node, Node, Symbol);
static Node new_type_choice(Node, Symbol, Tuple);
static Tuple aggr_type(Node, Tuple);
static Tuple same_bounds_check(Symbol, Tuple, Tuple);
static Tuple in_bounds_check(Tuple, Tuple, int *);
static Tuple aggr_eval(Node, Tuple, Tuple, Node, Symbol, int);
static Node new_index_bound_node(Const, int, Symbol);

/* changes
 * 13-mar-85	shields
 * change 'index_type' to 'indx_type' since index_type is macro in sem.
 *
 * 18-6-86	ACD
 * changed final loop over checks in 'same_bounds_check' to improve
 * efficiency
 *
 * 19-6-86	 ACD
 * changed 'exists' to 'static_index' in 'aggr_eval' to improve clarity
 *
 * 22-6-86	 ACD
 * changed aggr_eval to allow for optimization of static and semi-static
 * aggregates.  If the aggregate is static and associations and components
 * are static then the aggregate is 'optable'.  A data segment will
 * be created with the aggregate values in the data stack and will be
 * assigned to the array at run time.  The creation of the stack is done
 * by array_ivalue in expr.c.  aggr_eval unwinds the aggregate and changes
 * it into a positional aggregate passing the correct information to 
 * array_ivalue.  Array_ivalue uses the static_nodes to create the segment
 * and appends additional assignment statements for any non-static components
 * If there is an others clause,
 * then it is used to 'fill-in' the missing associations.
 *
 * 24-6-86	 ACD
 * Added code to detect the following flags: static_assoc, array_size,
 * static_component to be used in deciding whether to optimize or not.
 * These are set in aggr_choice, in_bounds_check and check_static_comp
 * (new routine) respectively.  From this information the flag:
 * optable are set.  Ths is passed to aggr_eval
 * to decide the level to optimize in attempt to evalaute a time-space
 */

void expand_array_aggregate(Node node)			/*;expand_array_aggregate*/
{
	/*
	 *
	 *  This procedure normalizes the format of an array aggregate, and
	 *  constructs the tree for the multiple range checks that may have
	 *  to be performed before constructing the aggregate proper.
	 *  The aggregate has the format : [positional_list, named_list, others]
	 *
	 *  On exit from this procedure, the named_list has been expanded into
	 *  code to perform range checks, and code to initialize the array
	 *  components. The rules of the language require that this code be in
	 *  fact elaborated first, that is to say before the elaboration of any
	 *  components (including the positional ones).
	 *  The positional part has been expanded to collect static components
	 *  and give explicit indication of the index positions.
	 *  The following takes place in sequence:
	 *
	 *	a) expand code to evaluate named choices.
	 *	b) obtain all index types.
	 *	c) For multidimensional aggregates, verify that bounds of all
	 *	   subaggregates are the same.
	 *	d) Verify that the aggregate bounds are compatible with type of
	 *	   indices.
	 *	e) expand code to evaluate components. For named associations
	 *	   that are static, it is tempting to elaborate the array here,
	 *	   in full. This is probably impractical for large arrays. The
	 *	   current solution is to emit a case statement that assigns to
	 *	   individual components according to the choices.
	 *	   In the case of a single named component, a loop is emitted.
	 *	   The same holds for 'others' choice when present.
	 *	   This scheme clearly contains much room for optimization.
	 *
	 */

	Symbol	type_name;
	Tuple	index_type_list, base_index_type_list, tup, decl_code, ntup;
	Symbol	comp_type, bt, al, obj_name;
	Tuple	new_subtypes;
	Tuple	index_type_sets;
	Tuple	init_code, new_pos, new_index_type_list, new_nam;
	Node	obj_node, pos_node, nam_node, comp_node, n, lnode;
	Fortup	ft1;
 
	int	  optable;
	int	  array_size;

#ifdef TRACE    
	if (debug_flag)
		gen_trace_node("ARRAY_AGGREGATE", node);
#endif


	/*
	 *  STEP 1
	 *     Initialize variables etc.
	 */

	type_name	    = N_TYPE(node);
	index_type_list = index_types(type_name);
	tup = SIGNATURE((Symbol) base_type(type_name));
	base_index_type_list = (Tuple) tup[1];
	comp_type = (Symbol)tup[2];

	/*
	 * STEP 2
	 *    Evaluate all choices first, including choices in subaggregates 
	 *    declaring anon subtypes when necessary.  A tuple containing 
	 *    these declarations is returned.	 
	 */
	decl_code = aggr_choice(node, index_type_list, comp_type);

	/*
	 * STEP 3
	 *    Then gather all index subtypes for all dimensions.  Add the
	 *    code for the new subtypes created to tuple of declarations
	 */
	tup = aggr_type(node, index_type_list);

	new_subtypes = (Tuple) tup[1];
	index_type_sets = (Tuple) tup[2];

	tup_free(tup); ntup = tup_add(decl_code, new_subtypes);
	tup_free(decl_code); decl_code = ntup; 
	tup_free(new_subtypes); /* free after last use */

	/* 
	 * STEP 4
	 *    Now check that all bounds for each dimension are the same.  If bounds
	 *    are dynamic, then a set of run-time checks are returned
	 */
	tup = same_bounds_check(type_name, index_type_list, index_type_sets);
	init_code = (Tuple) tup[1];
	new_index_type_list = (Tuple) tup[2];

	/*
	 * STEP 5
	 *   Is unconstrained or indices computed in same_bounds_check differ from
	 *   those computed in  aggr_type, then set the type of the aggregate to
	 *   the index_types to created in same_bounds_check
	 */
	if (!tup_eq(index_type_list , new_index_type_list)
	  || is_unconstrained(type_name))  {
		bt = base_type(type_name);
		al = ALIAS(type_name);
		type_name = new_unique_name("type");
		NATURE(type_name) = na_subtype;
		TYPE_OF(type_name) = bt;
		tup = tup_new(2);
		tup[1] = (char *) new_index_type_list;
		tup[2] = (char *) comp_type;
		SIGNATURE(type_name) = tup;
		ALIAS(type_name) = al;
		decl_code=tup_with(decl_code, (char *)new_subtype_decl_node(type_name));
		index_type_list	   = new_index_type_list;
		N_TYPE(node)	   = type_name;
	}

	/*
	 * STEP 6
	 *    Now test that the index_types computed belong to the base_index_types.
	 *    If bounds are dynamic, then run_time checks are performed
	 */
	array_size = 1;
	tup = in_bounds_check(index_type_list, base_index_type_list, &array_size);
	ntup = tup_add(init_code, tup);
	tup_free(init_code);
	init_code  = ntup;
	tup_free(tup);

	/*
	 * STEP 7
	 *   Finally, expand assignments to individual components. 
	 *   Add to aggregate node the name of the object assigned to it. The 
	 *   variable, constant, or temporary to which the aggregate is 
	 *   assigned, will be bound to this name subsequently. This name has 
	 *   been put in the N_UNQ of the node by the FE. In the case of an 
	 *   aggregate appearing as the initial value of an object declaration, 
	 *   the name has been changed to the first name of the identifier list.
	 */
	obj_name   = N_UNQ(node);
	obj_node   = new_name_node(obj_name);
	if (NATURE(obj_name) == na_void) {
		new_symbol(obj_name, na_obj, N_TYPE(node), (Tuple)0, (Symbol)0);
		/* else another copy of the aggregate was already expanded.
		 * this is the case if the aggregate is a default expression used
		 * in several calls.
		 */
	}

	optable = (array_size > 0 && array_size < MAX_STATIC_SIZE
	  && !(is_unconstrained(comp_type)));

	ntup = tup_add(init_code, aggr_eval(node, new_index_type_list, tup_new(0),
	  obj_node, comp_type, optable));
	tup_free(init_code);
	init_code = ntup;

	/*
	 * STEP 8
	 *   Sort the nodes that initialize components into those that are pure- 
	 *   ly static and those that require emission of assignment statements.
	 */
	new_pos = tup_new(0);
	new_nam = tup_new(0);
	FORTUP(comp_node = (Node), init_code, ft1);
		if (N_KIND(comp_node) == as_static_comp) 
			new_pos = tup_with(new_pos, (char *) comp_node);
		else
			new_nam = tup_with(new_nam, (char *) comp_node);
	ENDFORTUP(ft1);

	lnode = N_AST1(node);
	pos_node = N_AST1(lnode);
	nam_node = N_AST2(lnode);

	N_LIST(pos_node)	   = new_pos;
	N_AST1(pos_node)	   = (Node) 0;
	if (N_AST2_DEFINED(N_KIND(pos_node))) N_AST2(pos_node)= (Node) 0;
	if (N_AST3_DEFINED(N_KIND(pos_node))) N_AST3(pos_node)= (Node) 0;
	if (N_AST4_DEFINED(N_KIND(pos_node))) N_AST4(pos_node)= (Node) 0;

	N_SIDE(node) = FALSE;
	FORTUP(n = (Node), decl_code, ft1);
		expand(n);
		N_SIDE(node) |= N_SIDE(n);
	ENDFORTUP(ft1);

	if (tup_size(new_nam) == 0) {
		N_AST1(lnode) = pos_node;
		N_AST2(lnode) = OPT_NODE;
		N_AST1(node) = lnode;
		N_AST2(node) = obj_node;
		/*N_AST4(node) = (Node) 0; -- need to preserve N_TYPE if defined */
		N_KIND(node) = as_array_ivalue;
	}
	else {
		make_statements_node(nam_node, new_nam);
		expand(nam_node);
		/* insert test below to make sure tree reformatting proper */
		if (! is_aggregate(node)) {/* this check may be redundant */
			printf("aggr: test node_kind %d\n", N_KIND(node));/*DEBUG DS*/
			chaos("aggr bad kind");
		}
		N_AST1(lnode) = pos_node;
		N_AST2(lnode) = nam_node;
		N_AST1(node) = lnode;
		N_AST2(node) = obj_node;
		/* suppress next as need to preserve N_TYPE */
		/*if (N_AST4_DEFINED(N_KIND(node))) N_AST4(node) = (Node) 0;*/

	}
	if (tup_size(decl_code) != 0) {
		make_insert_node(node, decl_code, copy_node(node));
	}
}

static int tup_eq(Tuple ta, Tuple tb)								/*;tup_eq*/
{
/* compare two tuples for equality */
	int	i, n;
	n = tup_size(ta);
	if (ta == (Tuple)0 && tb == (Tuple)0) return TRUE;
	if (n != tup_size(tb)) return FALSE;
	for (i = 1; i <= n; i++)
		if (ta[i] != tb[i]) return FALSE;
	return TRUE;
}

static Tuple aggr_choice(Node node, Tuple index_type_list_arg, Symbol comp_type)
																/*;aggr_choice*/
{
	/*
	 * First step of array_aggregate evaluation: evaluate all choices, and
	 * normalize their format. Create anonymous ranges if dynamic bounds,
	 * and emit their declarations.
	 *
	 * Note: if a subtype is emitted, its elaboration will automatically
	 *	 check for compatibility with index subtype. If bounds are
	 *	 static, no subtype is emitted, and check is done here.
	 *
	 * Node is supposed to be an array aggregate. It may happen to be a
	 * string literal, in the case of a multidimensional array type of
	 * character component (not an array of strings). In this case, it is
	 * transformed into an aggregate.
	 */

	Tuple	anon_decls, tup, comp_list, index_type_list; /* check that local */
	Symbol	index_t, temp;
	int		nk, c;
	Tuple	str_val;  /* check type of this */
	Node	pos_node, lbd_node, ubd_node, choice, ch_node, comp_ch, v_expr, t;
	Node	nam_node, tnod, choice_node, subtype_node, lnode;
	Const	lbd_val, ubd_val;
	Tuple	pos, nam, constraint, ntup;
	Node	range_node, constraint_node, val_node, comp, assoc;
	Fortup	ft1;
	int		lbd_int, ubd_int;

#ifdef TRACE
	if (debug_flag) {
		gen_trace_node("AGGR_CHOICE", node);
		gen_trace_symbols("AGGR_CHOICE arguments", index_type_list_arg);
	}
#endif
	anon_decls = tup_new(0);
	index_type_list = tup_copy(index_type_list_arg); 
	/* since tup_fromb destructive*/
	index_t = (Symbol) tup_fromb(index_type_list);
	nk = N_KIND(node);

	/*
	 * Case: string_ivalue
	 */
	if (nk == as_string_ivalue) {
		str_val = (Tuple) N_VAL(node);
		N_KIND(node) = as_array_aggregate;
		N_VAL (node) = (char *)0;
		if (tup_size(str_val) == 0) {
			/* Must make a named association, because of 4.2(3) */
			pos_node = new_node(as_list);
			N_LIST(pos_node) = tup_new(0);
			lbd_node = new_attribute_node(ATTR_T_FIRST, new_name_node(index_t),
			  OPT_NODE, index_t);
			ubd_node = new_attribute_node(ATTR_PRED,
			  new_name_node(base_type(index_t)), copy_tree(lbd_node),
			  base_type(index_t));
			choice = new_node(as_range);
			N_AST1(choice)	  = lbd_node;
			N_AST2(choice)	  = ubd_node;
			ch_node	  = new_node(as_list);
			N_LIST(ch_node)  = tup_new1((char *) choice);
			v_expr	= new_ivalue_node(int_const(0), comp_type);  /* Why not.. */
			comp_ch	  = new_node(as_choice_list);
			N_AST1(comp_ch)	  = ch_node;
			N_AST2(comp_ch)	  = v_expr;
			nam_node	  = new_node(as_list);
			N_LIST(nam_node) = tup_new1((char *) comp_ch);
		}
		else {
			pos_node		= new_node(as_list);
			comp_list		= tup_new(0);
			tup = SIGNATURE(comp_type);
			lbd_node = (Node) tup[2];
			ubd_node = (Node) tup[3];
			lbd_val		= get_ivalue(lbd_node);
			ubd_val		= get_ivalue(ubd_node);
			if (lbd_val->const_kind != CONST_OM) 
				lbd_int = get_ivalue_int(lbd_node);
			if (ubd_val->const_kind != CONST_OM) 
				ubd_int = get_ivalue_int(ubd_node);
			FORTUP(c = (int), str_val, ft1);
				if ((lbd_val->const_kind != CONST_OM 
				  && ubd_val->const_kind != CONST_OM)
				  && c >= lbd_int && c <= ubd_int) {
					comp_list  = tup_with(comp_list, 
					  (char *) new_ivalue_node(int_const(c), comp_type));
				}
				else {
					comp_list = tup_with(comp_list,
					  (char *) new_qual_range_node(new_ivalue_node(int_const(c),
					   symbol_character), comp_type));
				}
			ENDFORTUP(ft1);
			N_LIST(pos_node) = comp_list;
			nam_node	  = new_node(as_list);
			N_LIST(nam_node) = tup_new(0);
		}
		lnode = node_new(as_aggregate_list);
		N_AST1(lnode) = pos_node;
		N_AST2(lnode) = nam_node;
		N_AST1(node) = lnode;
		N_AST2(node) = OPT_NODE;
	}
	else if (!(nk == as_array_aggregate) && !(nk == as_array_ivalue)) {
		chaos("compiler error");
		compiler_error_k("Illegal array aggregate subcomponent: ", node );
	}

	/*
	 * STEP 2.
	 *    Process the aggregate choices
	 */
	pos_node = N_AST1(N_AST1(node));
	nam_node = N_AST2(N_AST1(node));
	pos	    = N_LIST(pos_node);
	nam	    = N_LIST(nam_node);

	if (tup_size(pos) == 0  && tup_size(nam) == 1) {
		/*
		 * Case: single named association
		 *	  only case that can be non-static. 
		 *	  Possible error: #choice_list may be > 1. Front-end must unfold. 
		 */
		tnod = (Node) nam[1];
		choice_node = N_AST1(tnod);
		v_expr = N_AST2(tnod);
		tup = N_LIST(choice_node);
		choice = (Node) tup[1];

		expand(choice);
		N_SIDE(node) = N_SIDE(choice);

		nk = N_KIND(choice);
		/*
		 * Subcase: as_range for single named choice
		 */
		if (nk == as_range) {
			lbd_node = N_AST1(choice);
			ubd_node = N_AST2(choice);
	  		if (needs_subtype(lbd_node, ubd_node, index_t)) {
				/* Build anonymous subtype for choice described by non- */
				/* static range. */
				constraint = constraint_new(co_range);
				constraint[2] = (char *) lbd_node;
				constraint[3] = (char *) ubd_node;
				t = new_type_choice(choice, index_t, constraint);
				anon_decls = tup_with(anon_decls, (char *)  t);
			}
		}

		/*
		 * Subcase: as_range_choice for single named choice
		 */
		else if (nk == as_range_choice) {
			subtype_node = N_AST1(choice);
			range_node = N_AST2(subtype_node);
			lbd_node = N_AST1(range_node);
			ubd_node = N_AST2(range_node);

			if (needs_subtype(lbd_node, ubd_node, index_t)) {
				/* Build anon subtype for choice described by non-sttc range.*/
				constraint = constraint_new(co_range);
				constraint[2] = (char *) lbd_node;
				constraint[3] = (char *) ubd_node;
				t = new_type_choice(choice, index_t, constraint);
				anon_decls = tup_with(anon_decls, (char *)  t);
			}
			else {
				copy_attributes(range_node, choice);
			}
		}
		/*
		 * Subcase: as_subtype for single named choice
		 */
		else if (nk == as_subtype) {
			/* promote to anonymous subtype also */
			/*bt = (Node) N_AST2(choice);*/
			constraint_node = (Node) N_AST2(choice);
			lbd_node = N_AST1(constraint_node);
			ubd_node = N_AST2(constraint_node);
			/*	constraint = [N_UNQ(constraint_node), lbd_node, ubd_node];
			 * The above line from SETL version is wrong as first component
			 * of tuple should be constraint kind. For now we issue warning
			 * and make in co_range.		ds  7-10-85
			 */
#ifdef DEBUG
			printf("warning - review constraint settingin aggr.c\n");
#endif
			constraint = constraint_new(co_range);
			/*constraint[1] = (char *) N_UNQ(constraint_node);*/
			constraint[2] = (char *) lbd_node;
			constraint[3] = (char *) ubd_node;
			t = new_type_choice(choice, index_t, constraint);
			anon_decls = tup_with(anon_decls, (char *) t);
		} 
		/*
		 * Subcase: as_simple_choice for single named choice
		 *     if it is a non-static single choice given by an expression then
		 *     transform into a range of size 1.  If it has a side-effect
		 *     (e.g. f(x) => 3) then introduce anon subtype to prevent double
		 *     eval.
		 */
		else if (nk == as_simple_choice) {
			val_node = N_AST1(choice);
			if (!is_ivalue(val_node)) {
				if (!N_SIDE(choice)) {
					constraint = constraint_new(co_range);
					constraint[2] = (char *) choice;
					constraint[3] = (char *) choice;
				}
				else {
					temp = new_unique_name("single");
					new_symbol(temp, na_obj, index_t, (Tuple)0, (Symbol)0);
					anon_decls = tup_with(anon_decls, 
					  (char *) new_var_node(temp, index_t, val_node));
					tup = constraint_new(co_range);
					tup[2] = (char *) new_name_node(temp);
					tup[3] = (char *) new_name_node(temp);
					constraint    = tup;
				}
				t = new_type_choice(choice, index_t, constraint);
				anon_decls = tup_with(anon_decls, (char *)  t);
			}
		}
		/*
		 * Subcase: error case for single named choice
		 */
		else if (nk != as_simple_name) {
			chaos("compiler error -unknown choice in array aggr.");
			compiler_error_k("Unknown choice in array aggregate: ", choice);
		}
	}
	/*
	 * Case:  Anything other that a single named association
	 */
	else {
		N_SIDE(node) = FALSE;
	}

	/*
	 * STEP 3.
	 *   process remaining dimensions by recursing on remaining indices. Each 
	 *   vexpr is an aggregate.  Iterate over position and named list  
	 *   concatenating the anon type declaration
	 */
	if (tup_size(index_type_list) != 0) {
		FORTUP(comp = (Node), pos, ft1);
			tup = aggr_choice(comp, index_type_list, comp_type);
	  		ntup = tup_add(anon_decls, tup);
			tup_free(anon_decls); anon_decls = ntup; tup_free(tup);
			N_SIDE(node) |= N_SIDE(comp);
		ENDFORTUP(ft1);

		FORTUP(assoc = (Node), nam, ft1);
			v_expr = N_AST2(assoc);
			tup = aggr_choice(v_expr, index_type_list, comp_type);
	  		ntup = tup_add(anon_decls, tup);
			tup_free(anon_decls); anon_decls = ntup; tup_free(tup);
		ENDFORTUP(ft1);
	}
	return anon_decls;
}

static int needs_subtype(Node lbd_node, Node ubd_node, Symbol index_t)
															/*;needs_subtype*/
{
	Tuple	tup;
	Const	lbd_val, ubd_val;
	Node	 typ_lbd, typ_ubd;

	if ((!is_ivalue(lbd_node)) || (!is_ivalue(ubd_node))
	  || (!is_static_type(index_t))) {
		return TRUE;
	}
	else {
		/* May need to force CONSTRAINT_ERROR if bnds statically out of bnds */

		lbd_val = get_ivalue(lbd_node);
		ubd_val = get_ivalue(ubd_node);
		if (INTV(lbd_val) <= INTV(ubd_val)) { /* No qual on null ranges */
			tup = SIGNATURE(index_t);
			typ_lbd = (Node) tup[2];
			typ_ubd = (Node) tup[3];
	
			/* TBSL: may need to check these values are integers */

			if (get_ivalue_int(lbd_node) < get_ivalue_int(typ_lbd)
			  || get_ivalue_int(ubd_node) > get_ivalue_int(typ_ubd)) {
	  			USER_WARNING("Choice in aggregate will raise ",
				  "CONSTRAINT_ERROR");
				return TRUE;
			}
		}
 	}
	return FALSE;
}

static Node new_type_choice(Node choice_node, Symbol index_t, Tuple constraint)
														/*;new_type_choice*/
{
	/*
	 * create anonymous subtype for dynamic range in choice, and return code
	 * for creation of this anonymous subtype. Update the choice to carry
	 * a type name.
	 * Note: parent type must be the base type in order to avoid checking for
	 * constraint_error now (must be done after ALL choices are elaborated).
	 */

	Symbol	temp;

	temp = new_unique_name("choice");
	new_symbol(temp, na_subtype, base_type(index_t),constraint, ALIAS(index_t));
	make_name_node(choice_node, temp);
	return new_subtype_decl_node(temp);
}

static Tuple aggr_type(Node node, Tuple index_type_list_arg)	/*;aggr_type*/
{
	/*
	 * Collect the index types given in the aggregate itself. These are used
	 * to build the actual aggregate  subtype in the case  where the context
	 * type is unconstrained.
	 * The result is a pair; the first component is a tuple, the second
	 * is  a tuple of sets of symbols.
	 */

	Tuple	index_type_list;
	Node	pos_node, nam_node, others_node, assoc, choice_list_node;
	Tuple	all_choices, all_vexpr, nam, pos, choice_list, code;
	Fortup	ft1;
	Node	vexpr, choice, lbd_node, ubd_node, first_node;
	int		err, static_bounds, nk, lw_val, hg_val;
	int		high_bound, low_bound, i;
	Symbol	t, actual_index, assumed_index;
	Tuple	tup, sig, other_indices, down_subt, down_indices, ntup;
	Const	low, hi, lw, hg;
	int		low_bound_defined = FALSE, high_bound_defined = FALSE;
	int		low_int, hi_int;
	Set		aset, tset;

	/* index_type_list in SETL version becomes index_type_list_arg in
	 * C version to permit copy here to avoid problems that would
	 * result from destructive use made of index_type_list later on.
	 */
	/*
	 * STEP 1.
	 *   Initialize variables 
	 */
	index_type_list = tup_copy(index_type_list_arg);
	sig = (Tuple) 0;
#ifdef TRACE
	if (debug_flag) {
		gen_trace_node("AGGR_TYPE AST1 (pos)", N_AST1(N_AST1(node)));
		gen_trace_node("AGGR_TYPE AST2 (nam)", N_AST2(N_AST1(node)));
		gen_trace_node("AGGR_TYPE AST3 (others)", N_AST2(node));
		gen_trace_symbols("AGGR_TYPE", index_type_list);
	}
#endif

	assumed_index = (Symbol) tup_fromb(index_type_list);

	pos_node = N_AST1(N_AST1(node));
	nam_node = N_AST2(N_AST1(node));
	others_node = N_AST2(node);
	all_choices = tup_new(0);
	all_vexpr   = tup_new(0);
	nam		= N_LIST(nam_node);
	pos		= N_LIST(pos_node);

	/*
	 * STEP 2.
	 *   Process aggregate to get actual index.  In addition, collect a
	 *   tuple of the v_expressions
	 */

	/* Case 1:  others choice present    */
	/*      can only be present if type is constrained. */

	if (others_node != OPT_NODE) {
		all_vexpr = tup_with(all_vexpr, (char *) others_node);
		actual_index = assumed_index;
	}
	/*
	 * Case 2:  named associations and not others  
	 *    - Collect all ranges present in named associations. 
	 *    - Iterate over all bounds on this dimension, finding smallest and
	 *    - largest
	 */
	else if (tup_size(nam) != 0) {
		FORTUP(assoc = (Node), nam, ft1);
			choice_list_node = N_AST1(assoc);
			vexpr = N_AST2(assoc);
			choice_list = N_LIST(choice_list_node);
			if (vexpr != (Node)0) {	  /* absent if static null aggregate */
				all_vexpr = tup_with(all_vexpr, (char *)  vexpr);
			}
			ntup = tup_add(all_choices, choice_list);
			tup_free(all_choices); all_choices = ntup;
		ENDFORTUP(ft1);

		static_bounds = TRUE;
		err = FALSE;
		FORTUP(choice = (Node), all_choices, ft1);
			nk = N_KIND(choice);
			if (nk == as_simple_name) {
				t = N_UNQ(choice);
				if (NATURE(t) == na_type
				  || NATURE(t) == na_subtype || NATURE(t) == na_enum) {
					tup = SIGNATURE(t);
					lbd_node = (Node) tup[2];
					ubd_node = (Node) tup[3];

					lw = get_ivalue(lbd_node); 
					hg = get_ivalue(ubd_node);
					if  (lw->const_kind != CONST_OM
					  && hg->const_kind != CONST_OM) {
						lw_val = get_ivalue_int(lbd_node);
						hg_val = get_ivalue_int(ubd_node);
					}
					else {
		  				actual_index	= N_UNQ(choice);
		  				static_bounds = FALSE;
					}
				}
				else {
					err = TRUE;
					compiler_error("Simple name not type in aggr. choice");
				}
			}
			else if (nk == as_range) {
				/* We know from previous pass that it is static. */
				lbd_node = N_AST1(choice);
				ubd_node = N_AST2(choice);
				lw_val = get_ivalue_int(lbd_node);
				hg_val = get_ivalue_int(ubd_node);
			}
			else if(nk == as_simple_choice) {
				lbd_node = N_AST1(choice);
				lw_val = get_ivalue_int(lbd_node);
				hg_val = lw_val;
	  		}
			else if (nk == as_ivalue || nk == as_int_literal) {
				lw_val = get_ivalue_int(choice);
				hg_val = lw_val;
			}
			else {
				err = TRUE;
				compiler_error_k("Unknown choice in aggr_type: ", choice);
	  		}

	  		if (!err && static_bounds) {
				if (!low_bound_defined) {
					low_bound_defined = TRUE;
					low_bound = lw_val;
 	    		}
				if (low_bound > lw_val) low_bound = lw_val;
				if (!high_bound_defined) {
					high_bound_defined = TRUE;
					high_bound = hg_val;
				}
				if (high_bound < hg_val) high_bound = hg_val;
			}
		ENDFORTUP(ft1);

		if (static_bounds) {
			sig = constraint_new(co_range);
			sig[2] = (char *) new_ivalue_node(int_const(low_bound),  
			  assumed_index);
			sig [3] = (char *)new_ivalue_node(int_const(high_bound), 
			  assumed_index);
		}
	}

	/* Case 3:  positional associations and no others  */

	else	{	 /* nam = [], positional associations, no others. */
		ntup = tup_add(all_vexpr, pos); 
		tup_free(all_vexpr); all_vexpr = ntup;
		tup = SIGNATURE(assumed_index);
		lbd_node = (Node) tup[2];
		ubd_node = (Node) tup[3];

		low = get_ivalue(lbd_node); 
		if (low->const_kind != CONST_OM) {
	  		low_int = get_ivalue_int(lbd_node);
			hi = get_ivalue(ubd_node);
			if (hi->const_kind != CONST_OM)
				hi_int = get_ivalue_int(ubd_node);
			if (hi->const_kind != CONST_OM 
			  && (tup_size(pos) == hi_int - low_int + 1)) {
				/* actual bounds match index subtype. */
				actual_index = assumed_index;
			}
			else { /* Upper bound determined from number of components. */
				sig = constraint_new(co_range);
				sig[2] = (char *) lbd_node;
				sig[3] =
				   (char *)new_ivalue_node(int_const(tup_size(pos)-1 + low_int),
				   assumed_index);
			}
		}
		else {  /* Non-static low bound. */
			first_node = new_attribute_node(ATTR_T_FIRST,
			  new_name_node(assumed_index), OPT_NODE, assumed_index);
			sig = constraint_new(co_range);
			sig[2] = (char *) first_node;
			sig[3] = (char *) new_binop_node(symbol_addi,
		     new_ivalue_node(int_const(tup_size(pos) - 1), assumed_index),
		     copy_tree(first_node), assumed_index);
		}
	}
	/* 
	 * STEP 3
	 *     Build an anonymous subtype with bounds if one has been detected
	 */
	if (sig != (Tuple)0) {
		actual_index = new_unique_name("choice");
		new_symbol(actual_index, na_subtype, base_type(assumed_index),
		  sig, ALIAS(assumed_index));
		code = tup_new1((char *) new_subtype_decl_node(actual_index));
	}
	else {
		code = tup_new(0);
	}

	/*
	 * STEP 4.
	 *    In the multidimensional case,  recurse over inner aggregates. For 
	 *    each, collect the set of bounds that it provides on each dimension.
	 */

	if (tup_size(index_type_list) == 0) { /* reached last level */
		tup = tup_new(2);
		tup[1] = (char *) code;
		tup[2] = (char *) tup_new1((char *) set_new1((char *) actual_index));
		tup_free(index_type_list);
		return tup;
	}
	else {
		other_indices = tup_new(tup_size(index_type_list));
		for (i = 1; i <= tup_size(index_type_list); i++)
			other_indices[i] = (char *) set_new(0);
		FORTUP(vexpr = (Node), all_vexpr, ft1);
			tup =  aggr_type(vexpr, index_type_list);
	  		down_subt = (Tuple) tup[1];
			down_indices = (Tuple) tup[2];
			tup_free(tup);
			ntup = tup_add(code, down_subt);
			tup_free(code); code = ntup; 
			for (i = 1; i <= tup_size(index_type_list); i++) {
				tset = (Set) other_indices[i];
				other_indices[i]=(char *) set_union(tset, (Set)down_indices[i]);
				set_free(tset);
  			}
		ENDFORTUP(ft1);

		/* TBSL (after acvc): some dead sets can probably be freed here */
		tup = tup_new(2);
		tup[1] = (char *) code;
		aset = set_new(1);
		aset = set_with(aset, (char *) actual_index);
		tup[2] = (char *) tup_add(tup_new1((char *) aset), other_indices);
		tup_free(index_type_list);
		return tup;
		/*      return [code, [{actual_index}] + other_indices];*/
	}
}

static Tuple same_bounds_check(Symbol type_name, Tuple index_type_list,
  Tuple index_type_sets)								/*;same_bounds_check*/
{
	/*  This function checks that the set of index_types computed for each
	 *  dimension.  It compares these to an 'assumed_type' - either the
	 *  index-type for that dimension or if it this type is not a member
	 *  of the set of index_types derived, then it selects an arbitrary
	 *  element in the set.
	 */

	Tuple	new_index_type_list, check_list, tup, code;
	int		i;
	Symbol	assumed_type, indx_type;
	Node	low, high, l1, l2, h1, h2, cond, cond_list, high2, low2;
	Forset	fs1;
	Fortup	ft1;
	Const	lw, hg, hg2, lw2;
	Set		index_set;


	new_index_type_list = tup_new(0);
	check_list		 = tup_new(0);
	code		 = tup_new(0);

	/*
	 * STEP 1
	 *  Process the bounds for each dimension
	 */
	for (i = 1; i <= tup_size(index_type_list); i++) {
		/*
		 * STEP 1a
		 *    Set of bounds suggested by subaggregates on this dimension.
		 *    This set is produced by 'aggr_type'.  An assumed_type is
		 *    selected: if it is a constrained array: use given index otherwise
		 *    pick arbitrary index from actual bounds. 
		 */
		index_set = (Set) index_type_sets[i];
		if (set_mem(index_type_list[i], index_set)) {
			assumed_type  = (Symbol) index_type_list[i];
	  		index_set = set_less(index_set , (char *) assumed_type);
		}
		else assumed_type = (Symbol) set_from(index_set);

		new_index_type_list = tup_with(new_index_type_list,
		  (char *) assumed_type);
		tup = SIGNATURE(assumed_type);
		low = (Node) tup[2];
		high = (Node) tup[3];
		lw = get_ivalue(low);
		hg = get_ivalue(high);

		/*
		 * STEP 1b
		 *   Compare the bounds of the assumed type to the index_type and
		 *   generate dynamic checks if necessary
		 */

		FORSET(indx_type = (Symbol), index_set, fs1);
			tup = SIGNATURE(indx_type);
			low2 = (Node) tup[2];
			high2 = (Node) tup[3];
			lw2 = get_ivalue(low2);
			hg2 = get_ivalue(high2);

			if (lw->const_kind != CONST_OM && lw2->const_kind != CONST_OM) {
				if (const_ne(lw, lw2)) {
					code = tup_with(code, (char *)
					  new_raise_node(symbol_constraint_error));
					USER_WARNING("Evaluation of aggregate will raise",
					  " CONSTRAINT_ERROR");
				}
	  		}
			else { /* code to check dynamically the equality of lower bounds. */
				l1 = new_index_bound_node(lw,  ATTR_T_FIRST, assumed_type);
				l2 = new_index_bound_node(lw2, ATTR_T_FIRST, indx_type);
				check_list = tup_with(check_list,
				  (char *) new_binop_node(symbol_ne, l1, l2, symbol_boolean));
			}

			if (hg->const_kind != CONST_OM && hg2->const_kind != CONST_OM) {
				if (const_ne(hg , hg2)) {
					code = tup_with(code, (char *)
					  new_raise_node(symbol_constraint_error));
					USER_WARNING("Evaluation of aggregate will raise",
					  " CONSTRAINT_ERROR");
				}
	  		}
			else { /* code to check dynamically the equality of upper bounds. */
				h1 = new_index_bound_node(hg,  ATTR_T_LAST, assumed_type);
				h2 = new_index_bound_node(hg2, ATTR_T_LAST, indx_type);
				check_list = tup_with(check_list, (char *)
				  new_binop_node(symbol_ne, h1, h2, symbol_boolean));
			}
		ENDFORSET(fs1); /* end loop */
	}
 
	/*
	 * STEP 2
	 *   Create an expression to perform all of dynamic checks at run time
	 *   for all dimensions at one time
	 */
	if (tup_size(check_list) != 0) {
		cond_list = (Node) tup_frome(check_list);
		FORTUP(cond = (Node), check_list, ft1); 
			cond_list = new_binop_node(symbol_orelse, cond, cond_list,
			  symbol_boolean);
		ENDFORTUP(ft1); 
		tup_free(check_list);
		code = tup_with(code, (char *)  new_simple_if_node(cond_list,
		  new_raise_node(symbol_constraint_error), OPT_NODE));
	}
	tup = tup_new(2);
	tup[1] = (char *) code;
	tup[2] = (char *) new_index_type_list;
	return tup;
}

static Tuple in_bounds_check(Tuple index_type_list, Tuple base_index_type_list,
  int *array_size)										/*;in_bounds_check*/
{
	/* Emit code to check that bounds of aggregate belong to the index
	 * subtypes.  This compares the index types to the base index types
	 * Note: NO check is made that the aggregate is not (globally) null
	 *	 (according to LMC decision).
	 *TBSL: Simpler code could be generated by using qual_sub on index types.
	 */

	Tuple	code, tup;
	int		i;
	Symbol	index_t, base_index_t;
	Node	lw, hg, bl, bh;
	Const	bl_val, bh_val, lw_val, hg_val;
	code = tup_new(0);

	for (i = 1; i <= tup_size(base_index_type_list); i++) {
		index_t	   = (Symbol) index_type_list[i];
		base_index_t = (Symbol) base_index_type_list[i];
		tup = SIGNATURE(index_t);
		lw = (Node) tup[2]; 
		hg = (Node) tup[3];
		tup = SIGNATURE(base_index_t);
		bl = (Node) tup[2]; bh = (Node) tup[3];
		lw_val = get_ivalue(lw); hg_val = get_ivalue(hg);
		bl_val = get_ivalue(bl); bh_val = get_ivalue(bh);
		if  (bl_val->const_kind != CONST_OM
		  && bh_val->const_kind != CONST_OM
		  && lw_val->const_kind != CONST_OM
		  && hg_val->const_kind != CONST_OM ) {
			if ((get_ivalue_int(bl) < get_ivalue_int(bh)
			  && get_ivalue_int(lw) < get_ivalue_int(hg))) { /*Non null ranges*/
				if  (((get_ivalue_int(bl) > get_ivalue_int(lw)) 
				  ||  (get_ivalue_int(bh) < get_ivalue_int(hg)))) {
					/* Bounds outside of index type. */
		   			code = tup_with(code, (char *) 
					new_raise_node(symbol_constraint_error));
					USER_WARNING("Incompatible bounds in aggregate will raise",
					  " CONSTRAINT_ERROR");
					*array_size = 0;
		   			break;		  /* No need to check the rest... */
				}
				else
					*array_size *= (get_ivalue_int(hg)-get_ivalue_int(lw)) + 1;
			}
			else *array_size = 0;
		}
		else *array_size = 0;
	}
	return code;
}

static Tuple aggr_eval(Node aggr, Tuple index_type_list_arg,
  Tuple subscript_list, Node obj_node, Symbol comp_type, int optable)
																/*;aggr_eval*/
{
	/*
	 * Expand code to assign to each component of the aggregate.
	 * A special format is used to mark components whose index positions
	 * are static. A case statement is used for the rest.
	 */

	Tuple	code, pos, nam, tup, comp_list, expr_list, case_list, ncode, stup;
	int		save_side_value, static_index, index, lw_int, hg_int;
	Node	post_expr, s, stat_node, dyn_node, nam_node, new_case, lhs;
	Node	init_node, pos_node, others_node, low, high, low_node, subscript;
	Node	 v_expr_save, choice, lbd_node, ubd_node, static_node; 
	Fortup	ft1, ft2;
	Symbol	temp, p, index_t, loop_var, loop_range;
	Const	lw;
	Node	v_expr, hg, loop_var_node, range_node, iter, iter_node;
	Node	choice_list_node, assoc, body_node, var_node, list_node;
	Node	cases, case_body, case_expr;
	Tuple	index_type_list;
	int	  lbd_index_t, ubd_index_t, i, nk, lw_val, hg_val;
	
#ifdef TRACE
	if (debug_flag) 
		gen_trace_symbols("AGGR_EVAL", index_type_list_arg);
#endif

	if (tup_size(index_type_list_arg) == 0) {
		/*
		 * CASE 1: component level
		 *     using index_type_list_arg  we decide we have reached the
		 *     component level (and can therfore produce the final code).
		 *     Assign to the given index position.  Expand component and merge
		 *     pre-statements (in order to diagnose more ivalues)
		 */
		expand(aggr);
		static_index = TRUE;
		code = tup_new(0);
		save_side_value = N_SIDE(aggr);
		while (N_KIND(aggr) == as_insert) {
			/* static_index = FALSE; */
			static_index = FALSE;
			ncode = tup_add(code, N_LIST(aggr));
			tup_free(code); code = ncode;
			post_expr = N_AST1(aggr);
			copy_attributes(post_expr, aggr);
		}
		N_SIDE(aggr) = save_side_value;

		/*
		 * STEP 1
		 *  See if the indices are all static 
		 */
		FORTUP(s = (Node), subscript_list, ft1);
			if (!is_ivalue(s)) {
				static_index = FALSE;
				break;
			}
		ENDFORTUP(ft1);

		/* 
		 * STEP 2
		 *   propogate indexing of components.  This consists of three cases
		 *	1.  static indices and an aggregate component
		 *	2.  static indices and a static conponent
		 *	3.  non-static indices -or- non-static component
		 */

		nk = N_KIND(aggr);
		if (static_index && is_aggregate(aggr)) {
			stat_node = N_AST1(N_AST1(aggr));
			dyn_node = N_AST2(N_AST1(aggr));
			nam_node = N_AST2(aggr);
			make_index_node(nam_node, obj_node, subscript_list, comp_type);
			ncode = tup_add(code, N_LIST(stat_node));
			tup_free(code);
			code = ncode;
			code = tup_with(code, (char *)  new_expanded_node(dyn_node));
		}

		/*   Static component and indices. Special assignment format.  */

		else if (optable && static_index
		  && (nk == as_string_ivalue || nk == as_ivalue
		  ||  nk == as_int_literal   || nk == as_real_literal )) {
			static_node = new_node(as_static_comp);
			N_AST1(static_node) =
			  new_index_node(obj_node, subscript_list, comp_type);
			N_AST2(static_node) = aggr;
			N_TYPE(static_node) = comp_type;
			code = tup_with(code, (char *) static_node); 
		} 

		/* Non-static case. Note that must initialize on some cases   */

		else {
			lhs  = new_index_node(obj_node, subscript_list, comp_type);
			p = INIT_PROC(base_type(comp_type));
			if (is_record_type(comp_type) && p != (Symbol)0) {
				init_node = build_init_call(lhs, p, comp_type, obj_node);
				code = tup_with(code, (char *) init_node);
			}
			code = tup_with(code, (char *)
			new_assign_node(lhs, new_expanded_node(aggr)));
		}
		return code;
	}

	/*
	 * CASE 2:   Non-component level
	 *   We are not at the last level of indexing and have more dimensions
	 *   to process
	 */
	code = tup_new(0);
	index_type_list = tup_copy(index_type_list_arg); 
	index_t = (Symbol) tup_fromb(index_type_list);
	pos_node = N_AST1(N_AST1(aggr));
	nam_node = N_AST2(N_AST1(aggr));
	others_node = N_AST2(aggr);
	pos = N_LIST(pos_node);
	nam = N_LIST(nam_node);
	N_SIDE(aggr) = FALSE;    /* Just an assumption */

	/*
	 * STEP 1    
	 *    Process the associations.  This consists on three subcases:
	 *      1.  Positional associations
	 *      2.  A single named association
	 *      3.  Named associtions
	 *    Note that in all cases there is room for possible optimizations
	 */

	if (tup_size(pos) != 0) {
		/*
		 *  SubCase 1:  positional part 
		 */

		 /*
		  * STEP 1
		  *    Find the lower bound of the aggregate and create a subscript node
		  */
		tup = SIGNATURE(index_t);
		low = (Node) tup[2];
		high = (Node) tup[3];
		lw = get_ivalue(low);
		if (lw->const_kind != CONST_OM) {
			subscript = low;
			lw_int = get_ivalue_int(low);
			index = lw_int;
		}
		else {
			/* dynamic expression for lower bound. */
			low_node = new_attribute_node(ATTR_T_FIRST, new_name_node(index_t),
			  OPT_NODE, index_t);
			subscript = low_node;
			index	   = 0;
		}

		 /*
		  * STEP 2
		  *    Process the positional associations 
		  */

		FORTUP(v_expr = (Node), pos, ft1);
			stup = tup_copy(subscript_list);
			stup = tup_with(stup, (char *) subscript);
			ncode = tup_add(code, aggr_eval(v_expr, index_type_list, stup,
			  obj_node, comp_type, optable));
			tup_free(code); code = ncode;
			N_SIDE(aggr) |= N_SIDE(v_expr);

			index += 1;
			if (lw->const_kind != CONST_OM) 
				subscript = new_ivalue_node(int_const(index), index_t);
			else
				subscript = new_binop_node(symbol_addi, low_node,
				  new_ivalue_node(int_const(index), index_t), index_t);
		ENDFORTUP(ft1);

		 /*
		  * STEP 3
		  *  Process an others node if exists concurrent the positional assocs 
		  */

		if ((others_node != OPT_NODE) && optable) {
			/* If it is optimization, then loop over the remaining indices and
			 * create  the additional associations at this time.
			 */ 
			hg_int = get_ivalue_int(high);
			pos = tup_exp(pos, (hg_int - lw_int) + 1);
			v_expr = others_node;
			for (i = index; i <= (hg_int); i++) {
				stup = tup_copy(subscript_list);
				stup = tup_with(stup, (char *) subscript);
				v_expr_save = copy_tree((Node) v_expr);
				ncode = tup_add(code, aggr_eval(v_expr, index_type_list,
				  stup, obj_node, comp_type, optable));
				tup_free(code); code = ncode;
				v_expr = v_expr_save;
				subscript = new_ivalue_node(int_const(i + 1), index_t);
				pos[(i - lw_int) + 1] = (char *) v_expr; 
				if (i == hg_int) break;
			}
			N_SIDE(aggr) |= N_SIDE(others_node);
		}   /* end of optimized others node */
	
		else if (others_node != OPT_NODE) {

			/*  If it is not optimization, then create a run-time loop over the
			 * remaining index positions
			 */

			hg = new_index_bound_node(get_ivalue(high), ATTR_T_LAST, index_t);
			loop_var	   = new_unique_name("index");
			TYPE_OF(loop_var) = index_t;
			loop_var_node	   = new_name_node(loop_var);
			stup = tup_copy(subscript_list);
			stup = tup_with(stup, (char *)loop_var_node);
			expr_list = aggr_eval(others_node, index_type_list, stup, obj_node,
			  comp_type, optable);
			N_SIDE(aggr) |= N_SIDE(others_node);

			loop_range = new_unique_name("range");
			tup = constraint_new(co_range);
			tup[2] = (char *) subscript;
			tup[3] = (char *) hg;
			new_symbol(loop_range, na_subtype, index_t, tup, (Symbol)0);
			range_node	    = new_node(as_range);
			N_AST1(range_node) = subscript;
			N_AST2(range_node) = hg;
			iter		    = new_node(as_subtype);
			N_AST1(iter)	    = new_name_node(loop_range);
			N_AST2(iter)	    = range_node;
			N_TYPE(iter)	    = index_t;
			iter_node	    = new_node(as_for);
			N_AST1(iter_node)  = loop_var_node;
			N_AST2(iter_node)  = iter;
			code  = tup_with(code, (char *) new_loop_node(OPT_NODE, iter_node,
			  expr_list));
		}
	}

	else if (tup_size(nam) == 1 && tup_size(N_LIST(N_AST1((Node) nam[1]))) == 1
	  && others_node == OPT_NODE ) {

		/*
		 * CASE 2: Single named assoiation
		 */
		/*  If all is optable, loop over the indices and create entries for a
		 *  data segment at this time changing it into a positional association
		 */

		if (optable) {
			tup = SIGNATURE(index_t);
			low = (Node) tup[2];
			high = (Node) tup[3];
			lw_int = get_ivalue_int(low);
			hg_int = get_ivalue_int(high);
			pos = tup_new(hg_int + 1 - lw_int);
			assoc = (Node) nam[1];
			v_expr = N_AST2(assoc);
			for (i = lw_int; i <= (hg_int); i++) {
				subscript = new_ivalue_node(int_const(i), index_t);
				stup = tup_copy(subscript_list);
				stup = tup_with(stup, (char *) subscript);
				v_expr_save = copy_tree((Node) v_expr);
				comp_list = aggr_eval(v_expr, index_type_list,
				  stup, obj_node, comp_type, optable);
				v_expr = v_expr_save;
				ncode = tup_add(code, comp_list);
				tup_free(code); code = ncode;
				pos[(i - lw_int) + 1] = (char *) v_expr; 
				if (i == hg_int) break;
			}

			N_SIDE(aggr) = N_SIDE(v_expr);
			N_LIST(nam_node) = tup_new(0);
			N_LIST(pos_node) = pos;
		}   /* end of optimized others node */
	
		else {
			/*   if non-optable then create a run_time loop over the indices */

			assoc = (Node) nam[1];
			choice_list_node = N_AST1(assoc);
			v_expr = N_AST2(assoc);
			tup = N_LIST(choice_list_node);
			range_node = (Node) tup[1];
			if (N_KIND(range_node) == as_simple_choice) {
				stup = tup_copy(subscript_list);
				stup = tup_with(stup, (char *) N_AST1(range_node));
				comp_list = aggr_eval(v_expr, index_type_list, stup, obj_node,
				  comp_type, optable);
				N_SIDE(aggr) = N_SIDE(v_expr);
				ncode = tup_add(code, comp_list);
				tup_free(code); code = ncode;
			}
			else {
				loop_var	  = new_unique_name("index_t");
				TYPE_OF(loop_var)= index_t;
				loop_var_node	  = new_name_node(loop_var);
				stup = tup_copy(subscript_list);
				stup = tup_with(stup, (char *) loop_var_node);
				comp_list  = aggr_eval(v_expr, index_type_list, stup, obj_node,
				  comp_type, optable);
				N_SIDE(aggr) |= N_SIDE(v_expr);
				body_node	= new_statements_node(comp_list);

				/* Finally we build a loop over the choice range, whose body */
				/* is the initialisation of the sub aggregate */
				var_node	    = new_name_node(loop_var);
				iter_node	    = new_node(as_for);
				N_TYPE(range_node) = index_t;
				N_AST1(iter_node)   = var_node;
				N_AST2(iter_node)   = range_node;
				code = tup_with(code, (char *) new_loop_node(OPT_NODE,
				  iter_node, tup_new1((char *) body_node)));
			}
		}
	}  /* of a single named association   */

	/*
	 *  CASE 3:  Named Association
	 */

	else if (optable) {
		/*  If the aggregate is optable, then change each choice
		 *  into a series on positional association.  If there is an others
		 *  clause then use this to 'fill-in' any missing associations
		 */ 
		tup = SIGNATURE(index_t);
		lbd_node = (Node) tup[2];
		ubd_node = (Node) tup[3];
		lbd_index_t = get_ivalue_int(lbd_node);
		ubd_index_t = get_ivalue_int(ubd_node);
		pos = tup_new(ubd_index_t - lbd_index_t + 1);
		for (i = 1; i <= tup_size(pos); i++)
			pos[i] = (char *) 0; 

		FORTUP(assoc = (Node), nam, ft1);
			choice_list_node = N_AST1(assoc);
			v_expr = N_AST2(assoc);
			FORTUP(choice = (Node), N_LIST(choice_list_node), ft2);
				nk = N_KIND(choice);
				if (nk == as_simple_name) {
					temp = N_UNQ(choice);
					tup = SIGNATURE(temp);
					lbd_node = (Node) tup[2];
					ubd_node = (Node) tup[3];
					lw_val = get_ivalue_int(lbd_node);
					hg_val = get_ivalue_int(ubd_node);
				}
				else if (nk == as_range) {
					/* We know from previous pass that it is static. */
					lbd_node = N_AST1(choice);
					ubd_node = N_AST2(choice);
					lw_val = get_ivalue_int(lbd_node);
					hg_val = get_ivalue_int(ubd_node);
				}
				else if(nk == as_simple_choice) {
					lbd_node = N_AST1(choice);
					lw_val = get_ivalue_int(lbd_node);
					hg_val = lw_val;
				}
				else if (nk == as_ivalue || nk == as_int_literal) {
					lw_val = get_ivalue_int(choice);
					hg_val = lw_val;
				}
				else {
					compiler_error_k("Unknown choice in aggr_type: ", choice);
				}

				for (i = lw_val; i <= hg_val; i++) {
					subscript = new_ivalue_node(int_const(i), index_t);
					stup = tup_copy(subscript_list);
					stup = tup_with(stup, (char *) subscript);
					v_expr_save = copy_tree((Node) v_expr);
					ncode = tup_add(code, aggr_eval(v_expr, index_type_list,
					  stup, obj_node, comp_type, optable));
					tup_free(code); code = ncode;
					v_expr = v_expr_save;
					pos[(i - lbd_index_t) + 1] = (char *) v_expr;
					if (i == hg_val) break;
				}
			ENDFORTUP(ft2);
			N_SIDE(aggr)  |= N_SIDE(v_expr);
		ENDFORTUP(ft1);

		if (others_node != OPT_NODE) {
			v_expr = others_node;
			for (i = 1; i <= (tup_size(pos)); i++) {
				if (pos[i] == (char *) 0) {
					subscript = new_ivalue_node(int_const((lbd_index_t + i)-1),
					  index_t);
					stup = tup_copy(subscript_list);
					stup = tup_with(stup, (char *) subscript);
					v_expr_save = copy_tree((Node) v_expr);
					ncode = tup_add(code, aggr_eval(v_expr, index_type_list,
					  stup, obj_node, comp_type, optable));
					tup_free(code); code = ncode;
					v_expr = v_expr_save;
				}
			}
			N_SIDE(aggr)	 |= N_SIDE(others_node);
		}
	
		N_LIST(nam_node) = tup_new(0);
		N_LIST(pos_node) = pos;
	}

	else {   /* array is too big to expand at compile time  */
		/*
		 *     If the aggregate is not optimizable then
		 *     the code emitted is a run-time case statement  within 
		 *     a loop with variable which ranges over the index type.
		 */

		loop_var		= new_unique_name("index_t");
		TYPE_OF(loop_var)= index_t;
		loop_var_node    = new_name_node(loop_var);
		case_list		= tup_new(0);

		FORTUP(assoc = (Node), nam, ft1);
			choice_list_node = N_AST1(assoc);
			v_expr = N_AST2(assoc);
			stup = tup_copy(subscript_list);
			stup = tup_with(stup, (char *) loop_var_node);
			comp_list = aggr_eval(v_expr, index_type_list, stup, obj_node,
			  comp_type, optable);
			N_SIDE(aggr)  |= N_SIDE(v_expr);
			new_case	 = new_node(as_case_statements);
			N_AST1(new_case) = choice_list_node;
			N_AST2(new_case) = new_statements_node(comp_list);
			case_list  = tup_with(case_list, (char *) new_case);
		ENDFORTUP(ft1);

		if (others_node != OPT_NODE) {
			stup = tup_copy(subscript_list);
			stup = tup_with(stup, (char *) loop_var_node);
			comp_list   = aggr_eval(others_node, index_type_list, stup,
			  obj_node, comp_type, optable);
			N_SIDE(aggr)	 |= N_SIDE(others_node);
			list_node	   = new_node(as_list);
			N_LIST(list_node) = tup_new1((char *) new_node(as_others_choice));
			new_case	   = new_node(as_case_statements);
			N_AST1(new_case)   = list_node;
			N_AST2(new_case)   = new_statements_node(comp_list);
			case_list     = tup_with(case_list, (char *) new_case);
		}

		cases		= new_node(as_list);
		N_LIST(cases)    = case_list;
		case_body		= new_node(as_case);
		case_expr		= new_name_node(loop_var);
		N_AST1(case_body) = case_expr;
		N_AST2(case_body) = cases;

		/* Finally we build a loop over the index range, whose body is */
		/* the case statement assigning to various components. */
		var_node		= new_name_node(loop_var);
		iter_node		= new_node(as_for);
		N_AST1(iter_node) = var_node;
		N_AST2(iter_node) = new_name_node(index_t);
		code = tup_with(code, (char *) new_loop_node(OPT_NODE, iter_node, 
		  tup_new1((char *) case_body)));
	}
	return code;
}

static Node new_index_bound_node(Const v, int attribute, Symbol type_name)
													/*;new_index_bound_node*/
{
	Node	node;

	if (v->const_kind != CONST_OM) 
		node = new_ivalue_node(v, type_name);
	else
		node = new_attribute_node(attribute, new_name_node(type_name),
		  new_ivalue_node(int_const(1), symbol_integer), type_name);
	return node;
}

void expand_record_aggregate(Node node)			/*;expand_record_aggregate*/
{
	/*
	 * Normalize the format of a record aggregate. The component associations
	 * are separated into a list of static components, and a list of indivi-
	 * dual assignments to selected components of the object.
	 * A dummy name node is emitted, which is eventually bound to the entity
	 * that receives the aggregate.
	 */

	Symbol	type_name, some_discr, discr_name, subtype, obj_name;
	Symbol	comp_type, p, field_name;
	Tuple	comp_list, d_l, field_list, dyn_list, tup, ntup, discr_map;
	Node	comp_assoc, lhs;
	int		i, static_check, mismat_disc_err;
	Fortup	ft1, ft2;
	Node	e_node, n_node, static_comps, obj_node, stat_node, dyn_node;
	Node	aggr_node, nam_node, init_node, n, n_d, stmts_node, d_node, lnode;
	Symbol      index, c_t, a_t, field_type;
	Tuple	new_decls;
	int	  qualified;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("RECORD_AGGREGATE", node);
#endif
	/*
	 * STEP 1:
	 *    Initialize variables
	 */
	type_name = N_TYPE(node);
	comp_list = N_LIST(N_AST1(N_AST1(node)));
	new_decls = tup_new(0);
	field_list= tup_new(0);
	subtype   = type_name;
	/*
	 * STEP 2 
	 *     Collect discriminants to emit constrained array  subtypes for
	 *     components that may depend on discriminants. If type is unconstrained
	 *     the object takes its constraints from the aggregate itself and a
	 *     subtype is created for it here.
	 */
	if (has_discriminant(type_name)) {
		d_l = discriminant_list_get(type_name);
		some_discr = (Symbol)d_l[2];
		if (is_unconstrained(type_name)
		  && (Node)default_expr(some_discr) == OPT_NODE) { 
			subtype= new_unique_name("agg_type");
		}
		for (i = 1; i <= tup_size(d_l); i++) {
			comp_assoc	     = (Node) comp_list[i];
			n_node = N_AST1(comp_assoc);
			e_node = N_AST2(comp_assoc);
			discr_name	     = N_UNQ(n_node);
			expand(e_node);
			field_list = discr_map_put(field_list,discr_name,copy_node(e_node));
#ifdef TBSN
			if (!is_ivalue(e_node)) {
				/* this should be done when building the object and not the
				 * subtype value need not be static if there is no variant part
				 */
				make_discr_ref_node(e_node, discr_name, subtype);
			}
#endif
		} /* end loop */
	}

	/* 
	 * STEP 3
	 *    If the subtype is not a type_name then build a symbol table entry
	 */
	if (subtype != type_name) {	
		NATURE (subtype) = na_subtype;
		TYPE_OF(subtype) = base_type(type_name);
		tup = constraint_new(co_discr);
		tup[2] = (char *) field_list;
		SIGNATURE(subtype) = tup;
		ALIAS	  (subtype) = ALIAS(type_name);
		CONTAINS_TASK(subtype) = CONTAINS_TASK(type_name);
		type_name	    = subtype;
		N_TYPE(node)	    = type_name;
		new_decls = (Tuple)tup_new1((char *)new_subtype_decl_node(type_name));
	}

	mismat_disc_err = FALSE;
	static_check  = TRUE;
	/* 
	 * STEP 4
	 *    If it is constrained an has a discriminant then check the discriminant
	 *    against the expected subtype
	 */
	if (has_discriminant(type_name) && (!is_unconstrained(type_name)) ) {
		tup = SIGNATURE(type_name);
		discr_map = (Tuple) tup[2];
		for (i = 1; i <= tup_size(d_l); i++) {
			comp_assoc	  = (Node) comp_list[i];
			n_node = N_AST1(comp_assoc);
			e_node = N_AST2(comp_assoc);
			discr_name	  = N_UNQ(n_node);
			d_node		  = discr_map_get(discr_map, discr_name);
			if (is_ivalue(e_node) && is_ivalue(d_node)) {
				if (INTV(get_ivalue(e_node)) != INTV(get_ivalue(d_node))) {
					mismat_disc_err = TRUE;
					break;
				}
			}
			else {
				static_check = FALSE;
				break;
			}
		}
	}

	/*
	 * STEP 6
	 *    process each of the components of the record aggregate
	 */
	static_comps		= new_node(as_list);
	N_LIST(static_comps) = tup_new(0);
	dyn_list		= tup_new(0);
	obj_name		= N_UNQ(node);
	obj_node		= new_name_node(obj_name);
	new_symbol(obj_name, na_obj, N_TYPE(node), (Tuple)0, (Symbol)0);

	FORTUP(comp_assoc = (Node), comp_list, ft1);
		n_node = N_AST1(comp_assoc);
		e_node = N_AST2(comp_assoc);
		field_name = N_UNQ(n_node);
		comp_type  = TYPE_OF(field_name);

		field_type = N_TYPE(e_node); 
		if (field_type != comp_type) {
			/* the front-end recomputes the subtypes of components that
			 * depend on discriminants, using the values for these that
			 * appear in the aggregate itself. emit declarations for these
			 * subtypes in front of the aggregate.
			 */
			if (is_access(field_type))   {
				a_t = (Symbol)designated_type(field_type);
				c_t = (Symbol)designated_type(comp_type);
			}
			else  {
				a_t = field_type;
				c_t = comp_type;
			}
			if (is_array(a_t)) {
				FORTUPI(index = (Symbol), index_types(a_t), i, ft2)
					if (index_types(c_t)[i] != (char *)index) {
						new_decls = tup_with(new_decls,
						  (char *)new_subtype_decl_node(index));
					}
				ENDFORTUP(ft2);
			}
			else {
				/* TBSL: record, and access to record, components.*/
				;
			}
			n_d = new_subtype_decl_node(a_t);
			expand(n_d);
			new_decls = tup_with(new_decls, (char *)n_d);

			if (is_access(field_type)) {
				n_d = new_subtype_decl_node(field_type);
				new_decls = tup_with(new_decls, (char *)n_d);
			}
			N_TYPE(e_node) = field_type;
		}

		if (is_array_type(comp_type)) {
			expand(e_node);
			if (N_KIND(e_node) == as_qual_index) {
				qualified = TRUE;
				aggr_node = N_AST1(e_node);
			}
			else {
				qualified = FALSE;
				aggr_node = e_node;
			}

			if (N_KIND(aggr_node) == as_insert) {
				/* emit anonymous subtypes in front, and get aggregate */
				ntup = tup_add(new_decls, N_LIST(aggr_node));
				tup_free(new_decls);
				new_decls = ntup;
				aggr_node = N_AST1(aggr_node);
			}

			if (is_ivalue(aggr_node)
			  && (N_KIND(aggr_node) != as_array_ivalue && !qualified)) {
				lhs = new_selector_node(obj_node, field_name);
				N_KIND(comp_assoc)	     = as_static_comp;
				N_AST1(comp_assoc)	     = lhs;
				N_LIST(comp_assoc)	     = (Tuple)0;
				N_AST2(comp_assoc)	     = aggr_node;
				tup = N_LIST(static_comps);
				tup = tup_with(tup, (char *) comp_assoc);
				N_LIST(static_comps) = tup;
			}
			else if (is_aggregate(aggr_node) && !qualified) {
				stat_node = N_AST1(N_AST1(aggr_node));
				dyn_node  = N_AST2(N_AST1(aggr_node));
				nam_node  = N_AST2(aggr_node);
				make_selector_node(nam_node, obj_node, field_name);
				ntup = tup_add(N_LIST(static_comps), N_LIST(stat_node));
				tup_free(N_LIST(static_comps)); N_LIST(static_comps) = ntup;
				dyn_list = tup_with(dyn_list, (char *) dyn_node);
			}
			else {			/* variable, possibly with constraints */
				lhs = new_selector_node(obj_node, field_name);
				n = new_assign_node(lhs, e_node);
				dyn_list = tup_with(dyn_list, (char *) n);
			}
		}
		else { /* Discriminants were expanded above. */
			if (NATURE(field_name) != na_discriminant)
				expand(e_node);
			/* Emit an assigment to a selected component of the object. */
			if (is_aggregate(e_node)) {
				stat_node = N_AST1(N_AST1(e_node));
				dyn_node  = N_AST2(N_AST1(e_node));
				nam_node  = N_AST2(e_node);
				make_selector_node(nam_node, obj_node, field_name);
				ntup = tup_add(N_LIST(static_comps), N_LIST(stat_node));
				tup_free(N_LIST(static_comps));
				N_LIST(static_comps) = ntup;
				dyn_list = tup_with(dyn_list, (char *) dyn_node);
			}
			else  {
				lhs = new_selector_node(obj_node, field_name);
				if (is_ivalue(e_node)) {
					N_KIND(comp_assoc)	     = as_static_comp;
					N_AST1(comp_assoc)	     = lhs;
					N_LIST(comp_assoc)	     = (Tuple)0;
					N_AST2(comp_assoc)	     = e_node;
					tup = N_LIST(static_comps);
					tup = tup_with(tup, (char *) comp_assoc);
					N_LIST(static_comps) = tup;
				}
				else {
					p = INIT_PROC((Symbol) base_type(comp_type));
					if (is_record_type(comp_type) && p != (Symbol)0) {
			  			/* Assignment cannot be performed unless lhs */
			  			/* correctly initialized. */
			  			init_node = build_init_call(lhs, p, comp_type,obj_node);
			  			dyn_list = tup_with(dyn_list, (char *)  init_node);
					}
					n = new_assign_node(lhs, e_node);
					dyn_list = tup_with(dyn_list, (char *) n);
				}
			}
		} /*end*/
	ENDFORTUP(ft1);

	if (tup_size(dyn_list) == 0 && !qualified) { /* fully static aggregate. */
		N_KIND(node) = as_record_ivalue;
		lnode = node_new(as_aggregate_list);
		N_AST1(lnode) = static_comps;
		N_AST2(lnode) = OPT_NODE;
		N_AST1(node) = lnode;
		N_AST2(node) = obj_node;
	}
	else {
		stmts_node   = new_statements_node(dyn_list);
		if (!is_aggregate(node)) { /* this check may be redundant DS */
			printf("aggr dyn_list kind %d\n", N_KIND(node)); /*DEBUG DS */
			chaos("aggr - not aggregate node");
		}
		lnode = node_new(as_aggregate_list);
		N_AST1(lnode) = static_comps;
		N_AST2(lnode) = stmts_node;
		N_AST1(node) = lnode;
		N_AST2(node) = obj_node;
	}

	if (!static_check) { /* Add qual_discr */
		subtype      = N_TYPE(node);
		N_AST4(node) = (Node)0;
		N_TYPE(node) = base_type(type_name);	/* Only thing we know... */
		N_AST1(node) = copy_node(node);
		N_AST2(node) = N_AST3(node) = (Node) 0;
		N_KIND(node) = as_qual_discr;
		N_TYPE(node) = subtype;
	}
	else if (mismat_disc_err) {  
		/* make_insert_node needs to be done here, at the end of the
		 * expansion, while the test needs to be done at the beginning.
		 * This is when the discriminant announced does not match with
		 * the one in the aggregate.
		 */
		make_insert_node(node, (Tuple) tup_new1((char *) new_raise_node(
		  symbol_constraint_error)), copy_node(node));
		USER_WARNING("Mismatched discriminants will raise"," CONSTRAINT_ERROR");
	}

	if (tup_size(new_decls) != 0) {
		/* add declarations of constrained array types in front */
		make_insert_node(node, new_decls, copy_node(node));
	}
}
