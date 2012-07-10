/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#include "4.h"
#include "attr.h"
#include "setprots.h"
#include "libprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "errmsgprots.h"
#include "nodesprots.h"
#include "dclmapprots.h"
#include "evalprots.h"
#include "chapprots.h"

static int prev_error_message;
static Triplet *is_partition(Tuple, int, int);
static Tuple sort_case(Tuple);
static int tcompar(Triplet **, Triplet **);
static int abs_val(int);
static void complete_a_aggregate(Tuple, Tuple, Symbol, int, Node);
static void complete_component(Tuple, Tuple, Symbol, int, Node);
static Node new_comp_assoc(Symbol, Node);
static void resolve_r_component(Node, Symbol, Tuple);
static Symbol check_discriminant_dependence(Symbol, Tuple);
static int in_gen_types(Symbol);
static int in_multiple_types(Symbol);
static int is_integer_type(Symbol);
static Triplet *triplet_new();

int can_constrain(Symbol d_type)						  /*;can_constrain*/
{
	/* Determine whether an object, actual parameter,  type def, etc.  can
	 * receive a constraint.The predicate -is_unconstrained- used in decla-
	 * rations is too weak here, because it returns false on discriminated
 	* records with default values.
	 */

	if ((NATURE(d_type) == na_array)
	  || (is_record(d_type) && NATURE(d_type) != na_subtype
	  && has_discriminants(d_type)))
		return TRUE;
	else
		return FALSE;
}

Set valid_array_expn(Node expn)							 /*;valid_array_expn*/
{
	/* Called to validate indexing and slicing operations. The array name may
	 * be overloaded, and may also be an access to an array type. 
	 */

	Node	a_expn, i_node;
	Set array_types, types, rset;
	Tuple	index_list;
	Node	index;
	Symbol	n, a_t, t;
	int		i, exists, forall;
	Symbol	i_t;
	Forset	fs1, fs2;
	Fortup	ft1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  valid_array_expn");

	a_expn = N_AST1(expn);
	i_node = N_AST2(expn);
	resolve1(a_expn);
	types = N_PTYPES(a_expn);
	index_list = N_LIST(i_node);
	array_types = set_new(0);	/* To collect valid types*/
	FORTUP(index = (Node), index_list, ft1);
		n = N_UNQ(index);
		if (N_KIND(index) == as_simple_name && n != (Symbol)0 && is_type(n))
			/* In the case of a slice, */
			N_PTYPES(index) = set_new1((char *)TYPE_OF(n));
			/* may be a type mark.*/
		else
			resolve1(index);
	ENDFORTUP(ft1);
#ifdef TBSN
	if (cdebug2 > 3) TO_ERRFILE('index_list ' + str index_list);
#endif
	/* Now select those array types that are compatible with given indices.*/
	FORSET(a_t = (Symbol), types, fs1);
		t = a_t;
		if (is_access(t)) {
			if (is_fully_private(t)) {
				/* Cannot dereference an access to fully private type.*/
				if (set_size(array_types) == 1) {
					premature_access(t, a_expn);
					return set_new(0);
				}
				else
					continue;
			}
			else t = (Symbol) designated_type(t);
		}
#ifdef TBSN
		if (cdebug2 > 3) {
			TO_ERRFILE('type ' + str t);
			TO_ERRFILE('# dims t ' + str no_dimensions(t));
		}
#endif
		/* Discard incompatible array types */
		if (!is_array(t) || no_dimensions(t) != tup_size(index_list))
			continue;

		/* Now verify all indices in turn.*/
		forall = TRUE;
		FORTUPI(index = (Node), index_list, i, ft1);
			exists = FALSE;
			FORSET(i_t = (Symbol), N_PTYPES(index), fs2);
				if (compatible_types(i_t, (Symbol) index_types(t)[i])) {
					exists = TRUE;
					break;
				}
			ENDFORSET(fs2);
			if (exists == FALSE) {
				forall = FALSE;
				break;
			}
		ENDFORTUP(ft1);
		if (forall)
			/* a valid array type*/
			array_types = set_with(array_types, (char *)a_t);
	ENDFORSET(fs1);
#ifdef TBSN
	if (cdebug2 > 3) TO_ERRFILE('valid_array_expn ' + str array_types);
#endif

	N_PTYPES(a_expn) = array_types;
	rset = set_new(0);
	FORSET(a_t = (Symbol), array_types, fs1);
		if (is_access(a_t))
			rset = set_with(rset, (char *) designated_type(a_t));
		else
			rset = set_with(rset, (char *) a_t);
	ENDFORSET(fs1);
	return rset;
}

Symbol complete_array_expn(Node expn, Symbol c_type)  /*;complete_array_expn*/
{
	/* Called to complete the validation of an index or slice expression. The
	 * context type is the element	type for indexing, and the array type for
	 * slicing . The array expression may yield an access type, in which case
	 * a dereference operation is emitted now.
	 */

	Node	a_expn, index_list, a_node;
	Set		array_types;
	Symbol	array_type, a_t, t, c, access_type;
	Forset	fs1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : complete_array_expn");

	a_expn = N_AST1(expn);
	index_list = N_AST2(expn);
	array_types = N_PTYPES(a_expn);
	array_type = (Symbol)0;

	/* Iterate over array types to find unique one satisfying context.*/

	FORSET(a_t = (Symbol), array_types, fs1);
		t = (is_access(a_t)) ? (Symbol)designated_type(a_t): a_t;
		c = (N_KIND(expn) == as_slice) ? t: (Symbol) (component_type(t));
		if (compatible_types(c_type, c)) {
			if (array_type == (Symbol)0) {	/* One match found.*/
				array_type = t;
				access_type = a_t; /* Maybe an access.*/
			}
			else {
				/* If it is ambiguous, then it must an overloaded function*/
				/* that returns (an access to) an array.*/
				array_type = symbol_any;
			}
		}
	ENDFORSET(fs1);
	if (array_type == symbol_any) {
		remove_conversions(a_expn);		/* last chance. */
		if (set_size(N_PTYPES(a_expn)) == 1) {
			array_type = (Symbol) set_arb(N_PTYPES(expn));
			access_type = array_type;
			if (is_access(array_type))
				array_type = (Symbol) designated_type(access_type);
		}
		else {		/* still ambiguous */
			/* SETL sends {'indexing'}, in C, send {'any'} */
			type_error(set_new1((char *) symbol_any), c_type, 
			  set_size(N_PTYPES(a_expn)), expn);
		}
	}
	if (array_type == (Symbol)0) {
		/* SETL sends {'indexing'}, in C, send {'any'} */
		type_error(set_new1((char *) symbol_any), c_type, 
		  set_size(N_PTYPES(a_expn)), expn);
		array_type = symbol_any;
	}

	if (array_type != access_type) {	       /* Insert dereference. */
		a_node = copy_node(a_expn);
		N_KIND(a_expn) = as_all;
		N_AST1(a_expn) = a_node;
		N_AST2(a_expn) = N_AST3(a_expn) = N_AST4(a_expn) = (Node) 0;
		N_PTYPES(a_expn) = set_new1((char *) array_type);
	}
	resolve2(a_expn, array_type);			/* and resolve. */

	return array_type;
}

void valid_selected_expn(Node expn) /*;valid_selected_expn*/
{
	/* Use the name of the selector to determine the possible types of obj,
	 * which may be a function returning (an access to) a record or task type
	 * The possible types of the expression are those of the selected comps.
	 */

	Node	obj, s_node;
	Set types1, valid_t;
	Symbol	o_t, t, comp;
	char	*selector;
	Forset	fs1;
	Declaredmap	decls;

	obj = N_AST1(expn);
	s_node = N_AST2(expn);
	selector = N_VAL(s_node);
	resolve1(obj);
	types1 = N_PTYPES(obj);
	valid_t = set_new(0);

	FORSET( o_t = (Symbol), types1, fs1);
		t = o_t;
		if (is_access(o_t))t = (Symbol) designated_type(o_t);
		if (is_record(t))
			decls = (Declaredmap) (declared_components(base_type(t)));
		else if (is_task_type(t))
			decls = DECLARED(t);
		else continue;

		comp = dcl_get(decls, selector);
		if (comp != (Symbol)0) {
			if (is_access(o_t) && is_fully_private(o_t)
		      && NATURE(comp) != na_discriminant) { /*$ Can't dereference.*/
				if (set_size(types1) == 1) {
					premature_access(o_t, obj);
					return;
				}
				else continue;
			}
			else
				valid_t = set_with(valid_t, (char *) TYPE_OF(comp));
		}
	ENDFORSET(fs1);

	if (set_size(valid_t) == 0)
		pass1_error("invalid selector name", "4.1.3", s_node);
	N_PTYPES(expn) = valid_t;
}

Symbol complete_selected_expn(Node expn, Symbol c_type)
													/*;complete_selected_expn*/
{
	/* Complete the resolution of a selected component  expression, by
	 * choosing the one that yields the context_type. If the type of the
	 * object selected from is an access type, emit a dereference.
	 */

	Node	obj, s_node, acc_obj;
	Set types1;
	Symbol	comp_t, o_t, t, comp, obj_t, c;
	int		out_c;
	Forset	fs1;
	char	*selector;
	Declaredmap	decls;

	obj = N_AST1(expn);
	s_node = N_AST2(expn);
	selector = N_VAL(s_node);
	types1 = N_PTYPES(obj);
	comp_t = (Symbol)0;

	FORSET( o_t = (Symbol), types1, fs1);
		t = (is_access(o_t)) ? (Symbol) designated_type(o_t): o_t;
	
		if (is_record(t))
			decls = (Declaredmap) declared_components(base_type(t));
		else if (is_task_type(t))
			decls = DECLARED(t);

		c = dcl_get(decls, selector);
		if (c != (Symbol)0 && compatible_types(TYPE_OF(c), c_type)) {
			comp = c;
			if (comp_t == (Symbol)0) {
				comp_t = TYPE_OF(comp);		/* Found a match*/
				N_UNQ(s_node) = comp;
				obj_t = o_t;
			}
			else 			/* ambiguous call to some*/
				obj_t = symbol_any;
		}

	ENDFORSET(fs1); 

	if (obj_t == symbol_any) {
		remove_conversions(obj);			/* last hope. */
		if (set_size(N_PTYPES(obj)) != 1) {
#ifdef TBSL
			type_error(set_new1(symbol_selection), (Symbol)0, 
			  set_size(N_PTYPES(obj)), expn);
#endif
			return (Symbol)0;
		}
		else
			obj_t = (Symbol) set_arb(N_PTYPES(obj));
	}

	out_c = out_context;
	/* This is a valid context for the use of an out parameter, if 
	 * it is an assigment to a component of it, or if it is a reading
	 * of a discriminant.
	 */
	out_context = (out_c || NATURE(comp) == na_discriminant) ? TRUE:FALSE;

	if (is_access(obj_t)) {
		obj_t = (Symbol) designated_type(obj_t);
		/* Introduce explicit dereference. */
		acc_obj = copy_node(obj);
		N_KIND(obj) = as_all;
		N_AST2(obj) = N_AST3(obj) = N_AST4(obj) = (Node) 0;
		N_AST1(obj) = acc_obj;
		N_PTYPES(obj) = set_new1((char *)obj_t);
	}

	resolve2(obj, obj_t);
	out_context = out_c;

	return comp_t;
}

static Triplet *is_partition(Tuple choice_tuple, int choice_tuple_size,
  int exist_other_choice)									 /*;is_partition*/
{

	/* Checks if the ranges of the choice_nodes in a named array aggregate form 
	 * a partition.
	 * For example: (1|2|4 =>2, 5..10 =>3, 3 =>2, NUM => 4) where you can find
	 * simple_choices, a range_choice and a choice_unresolved. This will be a
	 * partition if the type_mark NUM is disjoint with {1..10} assuming that 
	 * the bounds of the array are (1..NUM'LAST).  A range such as 7..4 is a
	 * null range. It is permitted only if alone in the array aggregate.
	 * This function returns a pointer to a Triplet. This Triplet gives the
	 * final range of the aggregate. Complete_a_aggregate checks after whether
	 * the range of the aggregate is the same than the range of the array. It
	 * uses the system call 'qsort' to sort the ranges by their lower bound
	 * and then uses this sorted list to verify that it is a partition.
	 */

	int        lbd, ubd = 0, ubd_save;
	Triplet    *i_trip;
	Node       choice;
	int        i;

	if (choice_tuple_size != 0) {

		/*  1.  sort the set of choices giving a tuple  */

		choice_tuple = sort_case(choice_tuple);

		/*  2.  pass over choice_tuple checking that:
		 *        - there are only legal null ranges
		 *        - there are no overlapping ranges
		 *        - if the array aggregate does not have an others
		 *          then there are no missing associations
		 */

		for (i = 1; (i <= choice_tuple_size); i++) {
			ubd_save = ubd;
			lbd = ((Triplet *) choice_tuple[i])->inf;
			ubd = ((Triplet *) choice_tuple[i])->sup;
			choice = ((Triplet *) choice_tuple[i])->choice_node;

			/*  1.  Check for a null range. */
			if ((lbd > ubd) && (choice_tuple_size > 1 || exist_other_choice)) {
				errmsg(
				  "A null range in array aggregate must be the only choice",
				  "4.3.2.(3)", choice);
				prev_error_message = 1;
				return (Triplet *)0;
			}

			/*  2.  Check that the ranges do not overlap  */

			else if ((lbd <= ubd_save) && (i > 1)) {
				errmsg(
				  "Component is not allowed to be specified more than once",
				  "4.3.(6)", choice);
				prev_error_message = 1;
				return (Triplet *)0;
			}

			/*  3.  Check that the intersection between the ranges is not null*/

			else if ((i > 1) && (!exist_other_choice) && (lbd != ubd_save+1)) {
				errmsg("Missing association in array aggregate", "4.3.(6)",
				  choice);
				prev_error_message = 1;
				return (Triplet *)0;
			}
		}

		i_trip = triplet_new();
		i_trip->inf = ((Triplet *) choice_tuple[1])->inf;
		i_trip->sup = ((Triplet *) choice_tuple[choice_tuple_size])->sup;
		return (i_trip);
	}
}

static Tuple sort_case(Tuple tuple_to_sort)						/*;sort_case*/
{
	/*  This function sorts a tuple of triples based on the value of the
	 *  first element
	 */

	qsort((char *) &tuple_to_sort[1], tup_size(tuple_to_sort), sizeof (char *),
	  (int (*)(const void *, const void *))tcompar);
	return tuple_to_sort;
}

static int tcompar(Triplet **ptup1, Triplet **ptup2)			/*;tcompar*/
{
	Triplet  *tup1, *tup2;
	int   n1, n2;

	tup1 = *ptup1;                 
	tup2 = *ptup2;
	n1 = (int) (tup1->inf);    
	n2 = (int) (tup2->inf);
	if (n1 == n2) return 0;
	else if (n1 < n2) return -1;
	else return 1;
}

static int abs_val(int x)						             /*;abs_val*/
{
	return (x >= 0) ? x : -x;
}

void complete_aggregate(Symbol agg_type, Node expn)		 /*;complete_aggregate*/
{
	/* Given the context type, resolve the aggregate components. For an array
	 * type we  pass index	and component  types separately	 to the recursive
	 * routine complete_a_aggregate.  For record types  only the base type is
	 * needed here. Any required constraints are imposed in resolve2.
	 */

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : complete_aggregate");

	if (is_limited_type(agg_type)) {
		errmsg_id("aggregates not available for limited type %", agg_type,
		  "7.4.4", expn);
	}

	if (is_array(agg_type)) {
		/* if the context allows sliding, the bounds of the aggregate need
		 * only be verified against the unconstrained type.              
		 */
		if (full_others)
			complete_a_aggregate(index_types(agg_type), index_types(agg_type),
			  component_type(agg_type), can_constrain(agg_type), expn);
		else
			complete_a_aggregate(index_types(agg_type),
			  index_types(TYPE_OF(agg_type)), component_type(agg_type),
			  can_constrain(agg_type), expn);
	}
	else if (is_record(agg_type))
		complete_r_aggregate(base_type(agg_type), expn);
	else {
		errmsg("Invalid context for aggregate", "none", expn);
	}
}

static void complete_a_aggregate(Tuple indices, Tuple base_indices,
  Symbol comp_type, int is_unc, Node expn)			/*;complete_a_aggregate*/
{
	/* Complete processing of an array aggregate. The tree is normalized as
	 * follows:
	 *     N_KIND = as_array_aggregate
	 *     N_AST = [list_node, others_node]
	 * where list_node has two entries:
	 *     N_AST = [pos_list, nam_list]
	 * The first two are list nodes. The elements of N_LIST(nam_list) are
	 * pairs [choice_list, expression].  The N_KIND of choice nodes are 
	 * as_simple_choice and as_range_choice.  A simple_choice includes a 
	 * type name specifiying a range.
	 */

	Tuple	arg_list, pos_list, nam_list, tup, b_itup, itup;
	Node	others_node, last_arg, choice_list, c_expr, lexpn;
	Node	arg, i_expr, range_constraint, choice, pos_node, nam_node;
	Symbol	type_mark, indxt, b_indxt;
	Fortup	ft1, ft2;
	int	i, n, nn;
	int     c_ind, exist_other_choice, lbd, ubd, lbd_val, ubd_val;
	int     static_test, choice_tuple_size;
	int	raises;
	Tuple   choice_tuple;
	Triplet    *aggr_range;
	Node    lw_bd, hg_bd, lo_bd, up_bd, simple_expr1, simple_expr2;
	char	*nchoice;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : complete_a_aggregate");

	arg_list = N_LIST(expn);
	b_indxt = (Symbol) base_indices[1];
	indxt = (Symbol) indices[1];
	others_node = OPT_NODE;
	pos_list = tup_new(0);
	nam_list = tup_new(0);
	choice_tuple_size = 0;
	static_test = 1;
	c_ind = 1;
	exist_other_choice = 0;
	prev_error_message = 0;
	raises = FALSE;

	/* STEP 1.
	 *   Remove the OTHERS choice from the arggregate list if it is the last
	 *   component and place in -others_choice-. Otherwise if it appears
	 *   elsewhere in the aggregate it will be noted as a error later.
	 */

	last_arg = (Node) arg_list[tup_size(arg_list)];
	if (N_KIND(last_arg) == as_choice_list) {
		choice_list = N_AST1(last_arg);
		c_expr = N_AST2(last_arg);
		tup = N_LIST(choice_list);
		choice = (Node) tup[1];

		if (N_KIND(choice) == as_others_choice) {
			exist_other_choice = 1;
			others_node = c_expr;

			if (is_unc || (!is_static_subtype(indxt) && tup_size(arg_list)>1)) {
				errmsg("OTHERS choice not allowed in this context", "4.3.2",
				  last_arg);
			}	/* process anyway*/

			tup_frome(arg_list);
			resolve1(c_expr);
			n = tup_size(base_indices);
			nn = tup_size(indices);
			if (nn > 0 && n > 0) {
				b_itup = tup_new(n-1);
				itup = tup_new(n-1);
				for (i = 1; i < n; i++)
					b_itup[i] = base_indices[i+1];
				for (i = 1; i < nn; i++)
					itup[i] = indices[i+1];
				complete_component(itup, b_itup, comp_type, is_unc, c_expr);
				raises = raises || (N_KIND(c_expr) == as_raise);
			}
		}
	}

	/* STEP 2.
	 *   After any others clause has been processed, process the named and
	 *   positional associations
	 */

	FORTUP(arg = (Node), arg_list, ft1);
		if (N_KIND(arg) == as_choice_list) {
			/* STEP 2a.
			 *   Process named association choice list 
			 */
			choice_list = N_AST1(arg);
			c_expr = N_AST2(arg);
			resolve1(c_expr);
			n = tup_size(base_indices);
			nn = tup_size(indices);
			if (nn > 0 && n > 0) {
				b_itup = tup_new(n-1);
				itup = tup_new(n-1);
				for (i = 1; i < n; i++)
					b_itup[i] = base_indices[i+1];
				for (i = 1; i < nn; i++)
					itup[i] = indices[i+1];
				complete_component(itup, b_itup, comp_type, is_unc, c_expr);
				raises = raises || (N_KIND(c_expr) == as_raise);
			}
			else
				chaos("complete_a_aggregate - indices null");
			/* STEP 2b.
			 *   Process each choice in the choice list
			 */
			FORTUP(choice = (Node), N_LIST(choice_list), ft2);
				n = -1;
				if (N_KIND(choice) == as_choice_unresolved) {
					/* Case:  choice_unresolved:
					 *     If the index expression is an identifier, it must be
					 *     a type name or an object.
					 */
					i_expr = N_AST1(choice);
					find_old(i_expr);
					type_mark = N_UNQ(i_expr);
					if (is_type(type_mark)) {
						/* Subcase: type type_mark of choice_unresolved
						 *   check that it is either the only choice -or- is
						 *   static...
						 *     set the N_KIND to a as_simple_name
						 *     check that the type_mark is compatible with
						 *     the base index type 
						 */
						tup = SIGNATURE(type_mark);
						lo_bd = (Node) tup[2];
						up_bd = (Node) tup[3];
						if ((!is_static_expr(lo_bd))||(!is_static_expr(up_bd))){
							if ((tup_size(arg_list)>1) || exist_other_choice) {
								errmsg(
	"Non static choice in array aggregate must be the only choice",
	"4.3.2.(3)", choice); 
							}
							static_test = 0;
						}
						else {
							lbd_val = INTV((Const) N_VAL(lo_bd));
							ubd_val = INTV((Const) N_VAL(up_bd));
						}
						N_KIND(choice) = as_simple_name;
						nchoice = N_VAL(choice); /* preserve N_VAL */
						N_AST1(choice) = (Node)0;
						N_AST2(choice) = (Node)0;
						N_AST3(choice) = (Node)0;
						N_AST4(choice) = (Node)0;
						N_UNQ(choice) = type_mark;
						N_VAL(choice) = nchoice; /* preserve N_VAL */
						if (!compatible_types(type_mark, b_indxt)) {
							errmsg("invalid type mark in array aggregate",
							  "4.3", choice);
							return;
						}
					}
					else { /* single association*/
						/* Subcase: simple_choice of choice_unresolved
						 *     this is a single association
						 *     set the N_KIND to a as_simple_name check that
						 *     it is either the only choice -or- is static...
						 */
						N_KIND(choice) = as_simple_choice;
						i_expr = N_AST1(choice);
						check_type(base_type(b_indxt), i_expr);
						if (N_TYPE(i_expr) == symbol_any)
							static_test = 0;
						else if (!is_static_expr(i_expr)) {
							if ((tup_size(arg_list)>1) || exist_other_choice) {
								errmsg(
	"Non static choice in array aggregate must be the only choice", "4.3.2.(3)",
	choice);
							}
							static_test = 0;
						}
						else {
							lbd_val = INTV((Const) N_VAL(i_expr));
							ubd_val = INTV((Const) N_VAL(i_expr));
						}
					}
				}
				/* Case: as_simple_choice
				 *   The association is known to be a simple expression.
				 *     check that the type of the expression 
				 *     check that it is either the only choice -or- is static...
				 */
				else if (N_KIND(choice) == as_simple_choice) {
					i_expr = N_AST1(choice);
					adasem(i_expr);
					check_type(base_type(b_indxt), i_expr);
					if (N_TYPE(i_expr) == symbol_any)
						static_test = 0;
					else if (!is_static_expr(i_expr)) {
						if ((tup_size(arg_list) > 1) || exist_other_choice)   {
							errmsg(
	"Non static choice in array aggregate must be the only choice",
	"4.3.2.(3)", choice);
						}
						static_test = 0;
					}
					else {
						lbd_val = INTV((Const) N_VAL(i_expr));
						ubd_val = INTV((Const) N_VAL(i_expr));
					}
				}
				/* Case: range_choice
				 */
				else if (N_KIND(choice) == as_range_choice) {
					i_expr = N_AST1(choice);
					check_type(b_indxt, i_expr);
					if (N_KIND(i_expr) == as_subtype) {
						/* Subcase: expression is subtype in range_choice
						 *   Extract the constraint itself is static, reformat
						 *   choice as range else check that it is the only
						 *   choice
						 */
						range_constraint = N_AST2(i_expr);
						copy_attributes(range_constraint, choice);
						simple_expr1 = N_AST1(range_constraint);
						simple_expr2 = N_AST2(range_constraint);
						if (N_TYPE(i_expr) == symbol_any)
							static_test = 0;
						else if ((!is_static_expr(simple_expr1))
		    			  || (!is_static_expr(simple_expr2))) {
							if ((tup_size(arg_list) > 1) || exist_other_choice){
								errmsg(
	"Non static choice in array aggregate must be the only choice",
	"4.3.2.(3)", choice);
							}
							static_test = 0;
						}
						else {
							lbd_val = INTV((Const) N_VAL(simple_expr1));
							ubd_val = INTV((Const) N_VAL(simple_expr2));
						}
					}
					else { /*attribute RANGE.*/
						/* Subcase: attribute range subtype in range_choice
						 *        this means that it is an attrtibute range
						 */
						static_test = 0;
					}
				}
				/* Case: others choice (illegal at this point)
				 */

				else if (N_KIND(choice) == as_others_choice)  {
					errmsg("OTHERS must be the last aggregate component",
					  "4.3", choice);
					return;

				}
				/* STEP 2c.
				 *   After processing the choice if it is static then add to
				 *   choice list to be tested with is_partition
				 */
				if (static_test) {
					aggr_range = triplet_new();
					aggr_range->inf = lbd_val;  /*bounds and node of the curr */
					aggr_range->sup = ubd_val;  /*choice_node for is_partition*/
					aggr_range->choice_node = choice;
					if (c_ind == 1)
						choice_tuple = tup_new1((char *) aggr_range);
					else
						choice_tuple =tup_with(choice_tuple,(char *)aggr_range);
				}
				c_ind++;
			ENDFORTUP(ft2);   /* choice within a named choice list */

			/* STEP 2d.
			 *    Add the choice list to the tuple of named associations
			 */
			nam_list = tup_with(nam_list, (char *) arg);
		}

		/* STEP 3.
		 *   Process positional components...
		 */
		else { /* Positional component. */
			resolve1(arg);
			n = tup_size(base_indices);
			nn = tup_size(indices);
			if (nn > 0 && n > 0) {
				b_itup = tup_new(n-1);
				itup = tup_new(n-1);
				for (i = 1; i < n; i++)
					b_itup[i] = base_indices[i+1];
				for (i = 1; i < nn; i++)
					itup[i] = indices[i+1];
				complete_component(itup, b_itup, comp_type, is_unc, arg);
				raises = raises || (N_KIND(arg) == as_raise);
			}
			else chaos("complete_a_aggregate - indices null");
			pos_list = tup_with(pos_list, (char *) arg);
		}
	ENDFORTUP(ft1); /* end of processing the choice lists  */

	/* STEP 4.
	 *   Perform the final checks.  
	 *     A. Check that either the name list or the position list is null
	 *     B. Check for valid context for Others choice
	 */
	if (tup_size(pos_list) > 0 && tup_size(nam_list) > 0) {
		errmsg_l("In a positional aggregate only named association ",
		  "allowed is OTHERS", "4.3.2", expn);
		return;
	}
	else if (others_node != OPT_NODE && !full_others && tup_size(nam_list) !=0){
		errmsg("Invalid context for OTHERS and named associations",
		  "4.3.2(6)", others_node);
		return;
	}

	tup = SIGNATURE(indxt);   /*range of the array.*/
	lw_bd = (Node) tup[2];
	hg_bd = (Node) tup[3];
	/* STEP 5.
	 *   Perform check is it is static and named
	 *   If it is a partition then check:
	 *     A.  If the range is out of bounds (base index) considering sliding
	 *     B.  if the size of the choice range is less than the index range
	 *     C.  if the size of the choice range is greater that the index range
	 *     D.  if the choice range is null and the index range is not
	 */
	if (n == -1 && static_test)   {
		choice_tuple_size = tup_size(choice_tuple);
		aggr_range = is_partition(choice_tuple, choice_tuple_size,
		  exist_other_choice);

		if (!prev_error_message && !exist_other_choice)  {
			lbd = aggr_range->inf;
			ubd = aggr_range->sup;
			tup = SIGNATURE(b_indxt); /*range of the indices.*/
			lo_bd = (Node) tup[2];
			up_bd = (Node) tup[3];
			if ((is_static_expr(lo_bd)) && (is_static_expr(up_bd)))  {
				lbd_val = INTV((Const) N_VAL(lo_bd));
				ubd_val = INTV((Const) N_VAL(up_bd));

				/* Check A */
				if ((lbd_val > lbd || ubd_val < ubd)
				  && (ubd_val > lbd_val && ubd > lbd)   /*Non-null range*/
				  && full_others)   {
					/* Does not check anything if the subtype_range or the
					 * aggregate_range is null, according to test c43206a.
					 */
					raises = TRUE;
				}
			}
			if (!is_unc) {
				if ((is_static_expr(lw_bd)) && (is_static_expr(hg_bd)))  {
					lbd_val = INTV((Const) N_VAL(lw_bd));
					ubd_val = INTV((Const) N_VAL(hg_bd));
					/* TBSL : ubd_val-lbd_val may be superior to INTEGER'LAST.
					 * Use multiprecision.
					 */
					/* Check B */
					if ((ubd_val > lbd_val && ubd > lbd)   /*Non-null range*/
					  && (abs_val(ubd_val - lbd_val) < abs_val(ubd - lbd)))
						raises = TRUE;
					/* TBSL : ubd_val-lbd_val may be superior to INTEGER'LAST.
					 * Use multiprecision.
					 */
					/* Check C */
					else if ((ubd_val > lbd_val && ubd > lbd) /*Non-null range*/
					  && (abs_val(ubd_val - lbd_val) > abs_val(ubd - lbd))) {
						/* CONSTRAINT_ERROR may be raised according to test
						 * c48009f instead of:
                      	 * 	errmsg("Missing association in array aggregate",
						 * 	  "4.3.(6)", expn);
						 */
						raises = TRUE;
					}
					/* Check D */
					else if (ubd_val < lbd_val && ubd > lbd) {
						raises = TRUE;
					}
				}
			}
		}
	}
	/* STEP 6.
	 *   Perform check is it is position, not others and unconstrained
	 */
	if (n != -1 && !is_unc && !exist_other_choice) { /*Positional components*/
		if ((is_static_expr(lw_bd)) && (is_static_expr(hg_bd)))  {
			lbd_val = INTV((Const) N_VAL(lw_bd));
			ubd_val = INTV((Const) N_VAL(hg_bd));
			/* TBSL : ubd_val-lbd_val may be superior to INTEGER'LAST.
			 * Use multiprecision.
			 */
			if (tup_size(pos_list) != abs_val(ubd_val-lbd_val) + 1) {
				raises = TRUE;
			}
		}
	}

	/* STEP 7. 
	 *   Proccess an others choice by itself by converted into a named
	 *   association
	 */
	if (tup_size(pos_list) == 0 && tup_size(nam_list) == 0) {
		if ((N_KIND(lw_bd) == as_ivalue || N_KIND(lw_bd) == as_discr_ref)
		  &&  (N_KIND(hg_bd) == as_ivalue || N_KIND(hg_bd) == as_discr_ref)) {
			choice = node_new(as_range);
			N_AST1(choice) = copy_tree(lw_bd);
			N_AST2(choice) = copy_tree(hg_bd);
			arg = node_new(as_choice_list);
			N_AST1(arg) = node_new(as_list);
			N_LIST(N_AST1(arg)) = tup_new1( (char *)choice);
			N_AST2(arg) = others_node;
			nam_list = tup_new1( (char *)arg);
			others_node = OPT_NODE;
		}
	}

	/* If any component or subaggregate raises constraint error, replace the
	 * whole aggregate by a raise node.
	 */
	if (raises) {
		create_raise(expn, symbol_constraint_error);
		return;
	}
	/* STEP 8. 
	 *   Create the pos and name lists nodes
	 */
	pos_node = node_new(as_list);
	nam_node = node_new(as_list);
	N_LIST(pos_node) = pos_list;
	N_LIST(nam_node) = nam_list;

	N_KIND(expn) = as_array_aggregate;
	N_UNQ(expn) = sym_new(na_void);
	N_LIST(expn) = tup_new(0);	/* no further need for it.*/
	lexpn = node_new(as_aggregate_list);
	N_AST1(lexpn) = pos_node;
	N_AST2(lexpn) = nam_node;
	N_AST1(expn) = lexpn;
	N_AST2(expn) = others_node;
	N_AST4(expn) = (Node) 0;
}

static void complete_component(Tuple indices, Tuple b_indices, Symbol comp_type,
   int is_unc, Node expn)								/*;complete_component*/
{
	/* Complete the	 resolution of a component of  an array aggregate. If it
	 * is a multidimensional aggregate, the component itself is an array and
	 * a recursive	call is made with the remaining indices. String literals
	 * are handled in their own routine.
	 */

	Node	expn2;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC complete_component");

	if (tup_size(b_indices) == 0)
		res2_check(expn, comp_type);
	else if (N_KIND(expn) == as_aggregate)
		complete_a_aggregate(indices, b_indices, comp_type, is_unc, expn);
	else if (N_KIND(expn) == as_string_literal) {
		if (tup_size(b_indices) != 1) {
			errmsg("Invalid use of literal in aggregate", "4.3.2", expn);
			return;
		}
		complete_string_literal(expn, comp_type);
		N_TYPE(expn) = (Symbol) 0; /* clear as no type defined here */
	}
	else if (N_KIND(expn) == as_parenthesis) {
		/* Context of subaggregate is unconstrained, "others" choice is not*/
		/* allowed.*/
		expn2 = N_AST1(expn);
		complete_component(indices, b_indices, comp_type, TRUE, expn2);
	}
	else {
		errmsg("Expect aggregate for component of multidimensional aggregate",
		  "4.3.2", expn);
	}
}

void complete_string_literal(Node node, Symbol comp)
												/*;complete_string_literal*/
{
	/* String literals can appear as aggregates for arrays of character type.
	 * We have to verify that each character in the string is an  enumeration
	 * literal for that type.
	 */

	char	*strg, c, *lit;
	Tuple	arr, lit_map;
	Node	lo, hi;
	Symbol	sc;
	int		i, strglen, istr, ilitmap, v, exists, found;

	strg = N_VAL(node);
	sc = SCOPE_OF(comp);
	if (!tup_mem((char *)sc, open_scopes) && !tup_mem((char *)sc, used_mods)) {
		errmsg("characters in a string literal must be directly visible",
		 "4.2(3)", node);
	}

	if (comp == symbol_character || comp == symbol_any) {
		/*arr := [abs c: c in strg];*/
		strglen = strlen(strg);
		arr = tup_new(strglen);
		for (i = 1; i <= strglen; i++)
			arr[i] = (char *) strg[i-1];
		N_VAL(node) = (char *) arr;
		N_KIND(node) = as_string_ivalue;
	}
	else {/* Some enumeration type. Use its literal map.*/
		if (NATURE(base_type(comp)) != na_enum) {
			errmsg("Component type of context is not a character type",
			  "4.2", node);
			return;
		}
		lit_map = (Tuple) literal_map(base_type(comp));
		if (lit_map == (Tuple)0) lit_map = tup_new(0);
		/* arr := [lit_map('''' + c + '''') : c in strg]; */
		strglen = strlen(strg);
		arr = tup_new(strglen);
		lit = emalloct(4, "complete-string-literal");
		exists = FALSE;
		for (istr = 0; c = strg[istr]; istr++) {
			lit[0] = lit[2] = '\'';
			lit[1] = c;
			lit[3] = '\0';
			found = FALSE;
			for (ilitmap = 1; ilitmap < tup_size(lit_map); ilitmap += 2) {
				if (streq(lit, lit_map[ilitmap])) {
					arr[istr+1] = lit_map[ilitmap+1];
					found = TRUE;
					break;
				}
			}
			if (!found)
				exists = TRUE;
		}
		/* if exists c = strg(i) | arr(i) = om then */
		/*  Some characters are not in the component type. */
		if (exists) {
			create_raise(node, symbol_constraint_error);
			return;
		}
		else {
			/* The individual characters must be bounds-checked as any other
			 * array component.
			 */
			N_VAL(node) = (char *)arr;
			N_KIND(node) = as_string_ivalue;
			if (NATURE(comp) == na_subtype) {
				lo = (Node) (SIGNATURE(comp))[2];
				hi = (Node) (SIGNATURE(comp))[3];
				if (is_static_expr(lo) && is_static_expr(hi)) {
					/* and exists v in arr | v<N_VAL(lo) or v>N_VAL(hi) then */
					for (istr = 1; istr <= strglen; istr++) {
						v = (int) arr[istr];
						if (v < ((Const)N_VAL(lo))->const_value.const_int
						  || v > ((Const)N_VAL(hi))->const_value.const_int) {
							create_raise(node, symbol_constraint_error);
							return;
						}
					}
				}
			}
		}
	}
}

void complete_r_aggregate(Symbol aggregate_type, Node expn)
													/*;complete_r_aggregate*/
{
	/* Perform resolution of components in a record aggregate. If the
	 * record type has discriminants, we must first resolve the discriminant
	 * components, in order to determine the variant parts to which the rest
	 * of the aggregate must conform.
	 */

	Tuple	arg_list, ttup, btup;
	Tuple	discr_list;
	int		first_named, exists, ctupi, num_discr;
	Tuple	positional_args;
	Tuple	named_args;
	int		discri;
	Node	comp_assoc, choice_list, choice_node, e, c_expr, others_expr;
	Tuple	discr_map, all_component_names;
	int i1, found_discr_val;
	char	*sel;
	Node	simple_name, others_comp_list, lnode;
	Symbol	discr, bs, ctupd, btype;
	Node	invariant_node, variant_node, ctupn;
	Declaredmap	sel_names;
	Tuple	leftovers;
	Node	discr_id, variant_list, alt;
	int		discr_value, lo, hi;
	Tuple	case_list;
	Node	case_node, component_list, list_node;
	Tuple	comp_assoc_list;
	int		comp_pos, i, j, k;
	Tuple	choices, components_seen;
	/*    sel				: IDENTIFIER;*/
	Symbol	selector;
	Fortup	ft1, ft2;
	int	found_discr_value;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : complete_r_aggregate:");

	/* In SETL, components_seen is a set of symbols. Here we keep it as
	 * tuple. Since it is a local variable, we allocate it here and free
	 * it before every return from this procedure.
	 */
	components_seen = tup_new(0);
	arg_list = N_LIST(expn);
	discr_list = (Tuple) discriminant_list(aggregate_type);
	num_discr = tup_size(discr_list);
	/* Components can be given by named choices. Divide argument list
	 * into positional and named components .
	 */
	exists = FALSE;
	FORTUPI(comp_assoc = (Node), arg_list, i, ft1);
		if (N_KIND(comp_assoc) == as_choice_list) {
			exists = TRUE;
			break;
		}
	ENDFORTUP(ft1);
	if (exists)
		first_named = i;
	else
		first_named = tup_size(arg_list) + 1;

	/* TBSL: positional_args and named_args may not have to be built
	 * as separate tuples; if they are, should free on return
	 * Also check that don't get into nasty boundary cases here
	 * (building tuple of length -1, etc.
	 */
	positional_args = tup_new(first_named-1);
	for (j = 1; j <= first_named-1; j++)
		positional_args[j] = arg_list[j];
	/*named_args = arg_list(first_named..);*/
	named_args = tup_new(tup_size(arg_list)-first_named+1);
	k = 1;
	for (j = first_named; j <= tup_size(arg_list); j++)
		named_args[k++] = arg_list[j];
	others_expr = (Node) 0;
	FORTUP(comp_assoc = (Node), named_args, ft1);
		choice_list = N_AST1(comp_assoc);
		c_expr = N_AST2(comp_assoc);
		exists = FALSE;
		FORTUP(choice_node = (Node), N_LIST(choice_list), ft2);
			if (N_KIND(choice_node) == as_others_choice) {
				exists = TRUE;
				break;
			}
		ENDFORTUP(ft2);
		if (exists) {
			if (tup_size( N_LIST(choice_list)) != 1
	    	  || (comp_assoc != (Node)named_args[tup_size(named_args)])) {
				errmsg("OTHERS must appear alone and last in a choice list",
				  "4.3", choice_node);
				tup_free(components_seen);
				return;
			}
			else {
				others_expr = c_expr;
				break;
			}
		}
	ENDFORTUP(ft1);

	discr_map = tup_new(0);
	if (num_discr > 0) {
		/* add value for 'constrained' bit, and do not check for it later.*/
		e = new_ivalue_node(int_const(TRUE), symbol_boolean);
		copy_span((Node)arg_list[1], e);
		discr_map = discr_map_put(discr_map, symbol_constrained, e);
	}
	/* Map the discriminants into the (hopefully) static expressions
	 * given for them. Omit constrained bit from consideration.
	 */
	i1 = num_discr == 0 ? 0:
	  (num_discr -1 < tup_size(positional_args) ? num_discr -1 : 
	  tup_size(positional_args));
	/* collect the positional discriminants first. */
	for (i = 1; i <= i1; i++) {
		comp_assoc = (Node) positional_args[i];
		discr_map =
		  discr_map_put(discr_map, (Symbol) discr_list[i+1], comp_assoc);
	}
	/* Now look for named discriminants among named components.*/

	for (i = i1 + 2; i <= num_discr; i++) {
		discr = (Symbol) (discr_list[i]);

		found_discr_val = FALSE;
		FORTUP(comp_assoc = (Node), named_args, ft1);
			choice_list = N_AST1(comp_assoc);
			c_expr = N_AST2(comp_assoc);
			FORTUP(choice_node = (Node), N_LIST(choice_list), ft2);
				if (N_KIND(choice_node) == as_choice_unresolved) {
					simple_name = N_AST1(choice_node);
					if (streq(N_VAL(simple_name), original_name(discr))) {
						found_discr_val = TRUE;
						goto endforcomp;
					}
				}
			ENDFORTUP(ft2);
		ENDFORTUP(ft1);
endforcomp:
		if (found_discr_val)
			discr_map = discr_map_put(discr_map, discr, c_expr);
		else if (others_expr != (Node)0)
			discr_map = discr_map_put(discr_map, discr,
			  copy_tree(others_expr));
		else {
			errmsg_id("No value supplied for discriminant %", discr,
			  "4.3.1", expn);
			tup_free(components_seen);
			return;
		}
	}
	/* perform type resolution on the associations for discriminants */
	for (discri = 1; discri <= tup_size(discr_map); discri += 2) {
		discr = (Symbol) discr_map[discri];
		c_expr = (Node) discr_map[discri+1];
		if (N_TYPE(c_expr) == (Symbol)0)
			check_type(TYPE_OF(discr), c_expr);
	}
	invariant_node = (Node) invariant_part(aggregate_type);
	variant_node = (Node)(variant_part(aggregate_type));
	sel_names = (Declaredmap) declared_components(aggregate_type);
	/* Now assemble the list of selector names. Each component declara-
	 * tion declares a list of selectors with the same type.
	 */
	all_component_names = build_comp_names(invariant_node);
	/* Scan the variant part of the record declaration, and collect the
	 * types corresponding to the given discriminants.
	 */
	while (variant_node != OPT_NODE) {
		found_discr_value = FALSE;
		discr_id = N_AST1(variant_node);
		variant_list = N_AST2(variant_node);
		c_expr = discr_map_get(discr_map, N_UNQ(discr_id));
		/* Verify that a discriminant which governs a variant part*/
		/* is static.*/
		if (!is_static_expr(c_expr)) {
			errmsg_nval("Value for discriminant % must be static", discr_id,
			  "4.3.1", c_expr);
			/* TBSL: this was N_UNQ, but probably should be N_VAL (gs Sep 20)*/
			tup_free(components_seen);
			return;
		}

		discr_value = INTV((Const)N_VAL(c_expr));
		case_list = N_LIST(variant_list);
		case_node = (Node)case_list[tup_size(case_list)];
		if (N_KIND(case_node) == as_others_choice)
			others_comp_list = N_AST2(case_node);
		else
			others_comp_list = (Node)0;
		FORTUP(case_node = (Node), case_list, ft1);
			choice_list = N_AST1(case_node);
			component_list = N_AST2(case_node);
			exists = FALSE;
			if (N_KIND(case_node) == as_others_choice) continue;

			FORTUP(alt = (Node), N_LIST(choice_list), ft2);
				/* find the variant selected by given value of discriminant.
	       		 * all choices are now discrete ranges.
	        	 */
				lo = INTV((Const)N_VAL(N_AST1(alt)));
				hi = INTV((Const)N_VAL(N_AST2(alt)));
				if (lo <= discr_value && discr_value <= hi) {
					exists = TRUE;
					break;
				}
			ENDFORTUP(ft2);
			if (exists) {
				/* Variants may be nested.*/
				invariant_node = N_AST1(component_list);
				variant_node = N_AST2(component_list);
				/*all_component_names +:= build_comp_names(invariant_node);*/
				btup = build_comp_names(invariant_node);
				FORTUP(bs = (Symbol), btup, ft1);
					all_component_names = tup_with(all_component_names,
			    	  (char *) bs);
				ENDFORTUP(ft1);
				tup_free(btup);
				found_discr_value = TRUE;
				break /*quit forall case_node*/;
			}
		ENDFORTUP(ft1);

		if (!found_discr_value) {
			if (others_comp_list != (Node)0) {
				invariant_node = N_AST1(others_comp_list);
				variant_node = N_AST2(others_comp_list);
				btup = build_comp_names(invariant_node);
				FORTUP(bs = (Symbol), btup, ft1);
					all_component_names = tup_with(all_component_names,
				      (char *)bs);
				ENDFORTUP(ft1);
				tup_free(btup);
				/*all_component_names +:=build_comp_names(invariant_node);*/
			}
			else {
				create_raise(expn, symbol_constraint_error);
				tup_free(components_seen);
				return;
			}
		}
	}

	comp_pos = 1;	   /* Index into list of selector assignments.*/

	/*components_seen = tup_new(0);  now allocated at start of proc*/

	if (cdebug2 > 0) {
		TO_ERRFILE("record fields are: ");
	}
	/* The list of component asssociations is built with pairs name -> expr
	 * for all components present, including discriminants.
	 */
	/*comp_assoc_list := [new_comp_assoc(d, v) : [d, v] in discr_map];*/
	comp_assoc_list = tup_new(tup_size(discr_map)/2);
	for (ctupi = 1; ctupi <= tup_size(discr_map); ctupi += 2) {
		ctupd = (Symbol) discr_map[ctupi];
		ctupn = (Node) discr_map[ctupi+1];
		comp_assoc_list[(ctupi+1)/2] = (char *) new_comp_assoc(ctupd, ctupn);
	}
	/* Perform resolution of all components following the positional
	 * discriminants. Skip over named associations which are discriminants
	 * since these have already been resolved.
	 */
	for(i = i1+1; i <= tup_size(arg_list); i++) {
		comp_assoc = (Node) arg_list[i];
		if (N_KIND(comp_assoc) == as_choice_list) {
			choice_list = N_AST1(comp_assoc);
			c_expr = N_AST2(comp_assoc);
			choices = tup_new(0);

			FORTUP(choice_node = (Node), N_LIST(choice_list), ft1);
				if (N_KIND(choice_node) == as_choice_unresolved) {
					simple_name = N_AST1(choice_node);
					sel = N_VAL(simple_name);
					current_node = simple_name;
					check_void(sel);
					selector = dcl_get(sel_names, sel);
					if (selector == (Symbol)0) {
						errmsg("Undefined component name","4.3.1", simple_name);
						tup_free(components_seen);
						return;
					}
					choices = tup_with(choices, (char *) selector);
					if (tup_mem((char *)selector, components_seen)) {
						errmsg("Duplicate value for component in aggregate",
						  "4.3.1", simple_name);
						tup_free(components_seen);
						return;
					}
					else {
						if (!tup_mem((char *)selector, components_seen))
							components_seen =
							  tup_with(components_seen, (char *)selector);
						if (NATURE(selector) != na_discriminant) {
							if (tup_size(N_LIST(choice_list))> 1)
								/* copy expression node for each choice.*/
								e = copy_tree(c_expr);
							else
								e = c_expr;
							resolve_r_component(e, selector, discr_map);
							comp_assoc_list = tup_with(comp_assoc_list,
						      (char *)new_comp_assoc(selector, e));
						}
						comp_pos += 1;
					}
				}

				else if (N_KIND(choice_node) == as_simple_choice) {
					errmsg("choice in record aggregate must be selector name",
					  "4.3.1", choice_node);
					tup_free(components_seen);
					return;
				}
				else if (N_KIND(choice_node) == as_range_choice) {
					errmsg("Range choice not allowed in record aggregate",
					  "4.3.1", choice_node);
					tup_free(components_seen);
					return;
				}
				else if (N_KIND(choice_node) == as_others_choice) {
					leftovers = tup_new(0);
					FORTUP(selector = (Symbol), all_component_names, ft2);
						if (!tup_mem((char *)selector, components_seen)) {
							if (!tup_mem((char *) selector, leftovers))
								leftovers=tup_with(leftovers, (char *)selector);
						}
					ENDFORTUP(ft2);

					if (tup_size( leftovers) == 0) {
						errmsg_l("OTHERS choice must represent at least ",
						  "one component", "4.3.1", choice_node);
						tup_free(components_seen);
						return;
					}
					else {
						FORTUP(selector = (Symbol), leftovers, ft2);
							if(! tup_mem((char *)selector, components_seen))
								components_seen = tup_with(components_seen, 
						    	  (char *) selector);
							if (NATURE(selector) != na_discriminant) {
								if (tup_size(leftovers)> 1) {
									/* copy expression node.*/
									e = copy_tree(c_expr);
								}
								else {
									e = c_expr;
								}
								resolve_r_component(e, selector, discr_map);
								if (N_TYPE(c_expr) == symbol_any) {
									errmsg_id(
									  "OTHERS expression incompatible with %",
									  selector, "4.3.1", choice_node);
									tup_free(components_seen);
									return;
								}
								comp_assoc_list = tup_with(comp_assoc_list,
						    	  (char *)new_comp_assoc(selector, e));
							}
							choices = tup_with(choices, (char *) selector);
						ENDFORTUP(ft2);
					}
				}
			ENDFORTUP(ft1);

			ttup= tup_new(0);
			FORTUP(selector = (Symbol), choices, ft2);
				btype = base_type(TYPE_OF(selector));
				if (!tup_mem((char *) btype, ttup))
					ttup = tup_with(ttup, (char *) btype);
			ENDFORTUP(ft2);
			if (tup_size(ttup) > 1) {
				errmsg("components on a choice list must have same type",
				  "4.3.1", choice_list);
			}
			tup_free(ttup);
		}
		else {	/* Positional record aggregate. */
			if (comp_pos > tup_size(all_component_names)) {
				errmsg("Too many components for record aggregate","none", expn);
				tup_free(components_seen);
				return;
			}
			selector = (Symbol) all_component_names[comp_pos];
			resolve_r_component(comp_assoc, selector, discr_map);
			comp_pos += 1;
			if (!tup_mem((char *) selector, components_seen))
				components_seen = tup_with(components_seen, (char *) selector);
			comp_assoc_list = tup_with(comp_assoc_list,
			  (char *) new_comp_assoc(selector, comp_assoc));
		}
	}

	exists = FALSE;
	FORTUP(selector = (Symbol), all_component_names, ft1);
		if (!tup_mem((char *) selector, components_seen)) {
			exists = TRUE;
			break;
		}
	ENDFORTUP(ft1);
	if (exists)  {
		errmsg_id("No value supplied for component %", selector, "4.3.1",
		  current_node);
		tup_free(components_seen);
		return;
	}
	for (i = 1; i <= tup_size(comp_assoc_list); i++) {
		if (N_KIND(N_AST2((Node)comp_assoc_list[i])) == as_raise) {
			create_raise(expn, symbol_constraint_error);
			return;
		}
	}
	N_UNQ(expn) = sym_new(na_void);
	N_KIND(expn) = as_record_aggregate;
	N_LIST(expn) = (Tuple)0; /* clear out n_list */
	list_node = node_new(as_list);
	N_LIST(list_node) = comp_assoc_list;
	lnode = node_new(as_aggregate_list);
	N_AST1(lnode) = list_node;
	N_AST2(lnode) = OPT_NODE;
	N_AST1(expn) = lnode;
	N_AST2(expn) = OPT_NODE;
}

static Node new_comp_assoc(Symbol selector, Node expn)		 /*;new_comp_assoc*/
{
	/* Used to normalize the representation of record aggregates: associate
	 * a selector name with the expression given for it in the aggregate.
	 */

	Node	c_node;

	c_node = node_new(as_record_choice);
	N_AST1(c_node) = new_name_node(selector);
	N_AST2(c_node) = expn;
	copy_span(expn, N_AST1(c_node));
	return c_node;
}

Tuple build_comp_names(Node invariant_node)	/*;build_comp_names*/
{
	/* Collect names of record components in the invariant part of the
	 * record. Skip nodes generated for internal anonymous types.
	 */

	Tuple	all_component_names;
	Node	node, id_list_node, id_node;
	Fortup	ft1, ft2;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  build_comp_names");

	all_component_names = tup_new(0);
	FORTUP(node = (Node), N_LIST(invariant_node), ft1);
		if (N_KIND(node) == as_subtype_decl || N_KIND(node) == as_delayed_type)
			continue;
		id_list_node = N_AST1(node);
		FORTUP(id_node = (Node), N_LIST(id_list_node), ft2);
		/* test against 0 needed since in SETL om added at end of tuple
		 * has no effect!	ds 14 aug
		 * Skip over 'constrained' bit added by code generator (case of a
		 * separately compiled record type definition.
		 */
		if (N_UNQ(id_node) != (Symbol)0)
			all_component_names = tup_with(all_component_names,
			  (char *) N_UNQ(id_node));
		ENDFORTUP(ft2);
	ENDFORTUP(ft1);
	return all_component_names;
}

static void resolve_r_component(Node e, Symbol selector, Tuple discr_map)
													/*;resolve_r_component.*/
{  
	Symbol comp_type;

	resolve1(e);
	if (!noop_error) {
		comp_type = TYPE_OF(selector);
		/* if its bounds depend on discriminants, we emit subtypes with
		 * the actual values of the discriminants given in the aggr. 
		 */
		comp_type = check_discriminant_dependence(comp_type, discr_map);
		res2_check(e, comp_type);
	}
}

static Symbol check_discriminant_dependence(Symbol comp_type, Tuple discr_map)
											/*;check_discriminant_dependence*/
{
	/* if the subtype indication of a record component depends on a
	 * discriminant, then the expression in a record aggregate that corresponds
	 * to this component is given a subtype that is constrained by the values
	 * of the discriminants that appear in the aggregate itself.
	 */

	Tuple   constraint, new_constraint, tup, new_indices;
	Node    ubd, lbd, e;
	Symbol  d, type_name, index, new_index, new_type, new_acc;
	Tuple   comp_discr_map, new_discr_map;
	int     i, newi, new_t;
	Fortup  ft1;

	if (tup_size(discr_map) == 0) return comp_type;

	type_name = (is_access(comp_type)) ? (Symbol)designated_type(comp_type):
	  comp_type;

	if (is_array(type_name)) {
		tup = index_types(type_name);
		new_indices = tup_new(0);
		FORTUP(index = (Symbol), tup, ft1)
		    constraint = SIGNATURE(index);
			lbd = (Node)constraint[2];
			ubd = (Node)constraint[3];
			newi = FALSE;
			if (N_KIND(lbd) == as_discr_ref) {
				lbd = discr_map_get(discr_map, N_UNQ(lbd));
				newi = TRUE;
			}
			if (N_KIND(ubd) == as_discr_ref) {
				ubd = discr_map_get(discr_map, N_UNQ(ubd));
				newi = TRUE;
			}
			if (newi) {
				new_index = sym_new(na_subtype);
				dcl_put(DECLARED(scope_name), str_newat(), new_index);
				new_constraint = constraint_new(CONSTRAINT_RANGE);
				new_constraint[2]    = (char *)lbd;
				new_constraint[3]    = (char *)ubd;
				TYPE_OF(new_index)   = TYPE_OF(index);
				SIGNATURE(new_index) = new_constraint;
				SCOPE_OF(new_index)  = scope_name;
				ALIAS	  (new_index) = ALIAS(index);
				new_indices = tup_with(new_indices, (char *)new_index);
				new_t = TRUE;
			}
			else new_indices = tup_with(new_indices, (char *)index);
		ENDFORTUP(ft1);
		if (new_t) {
			/* create new subtype of array type, using new index types, and
			 * label aggregate with this new array subtype.
			 */
			new_type = sym_new(na_subtype);
			dcl_put(DECLARED(scope_name), str_newat(), new_type);
			TYPE_OF(new_type)      = base_type(type_name);
			SIGNATURE(new_type)    = tup_new(2);
			SIGNATURE(new_type)[1] = (char *)new_indices;
			SIGNATURE(new_type)[2] = (char *)component_type(type_name);
			SCOPE_OF(new_type)     = scope_name;
			ALIAS(new_type)        = ALIAS(type_name);
		}
		else {
			tup_free(new_indices);
			return comp_type;
		}
	}
	else if (NATURE(type_name) == na_subtype && is_record(type_name)) {
		/* see if any discriminant constraint is itself given by a discrimi-
		 * nant (which must be a discriminant of the enclosing record.
		 */
		comp_discr_map = (Tuple)numeric_constraint_discr(SIGNATURE(type_name));
		new_discr_map = tup_new(0);
		newi = FALSE;
		for (i = 1; i <= tup_size(comp_discr_map); i += 2) {
			d = (Symbol)comp_discr_map[i];
			e = (Node)  comp_discr_map[i+1];
			if (N_KIND(e) == as_discr_ref) {
				/* replace discriminant reference with value given in enclosing
				 * aggregate.
				 */
				newi = TRUE;
				new_discr_map = discr_map_put(new_discr_map, d,
				  copy_tree(discr_map_get(discr_map, N_UNQ(e))));
			}
			else
				new_discr_map = discr_map_put(new_discr_map, d, e);
		}
		if (newi) {
			new_type = sym_new(na_subtype);
			dcl_put(DECLARED(scope_name), str_newat(), new_type);
			tup = constraint_new(CONSTRAINT_DISCR);
			numeric_constraint_discr(tup) = (char *)new_discr_map;
			TYPE_OF(new_type)      = TYPE_OF(type_name);
			SIGNATURE(new_type)    = tup;
			OVERLOADS(new_type)    = OVERLOADS(type_name);
			SCOPE_OF(new_type)     = scope_name;
			ALIAS(new_type)        = ALIAS(type_name);
		}
		else {
			tup_free(new_discr_map);
			return comp_type;
		}
	}
	else {
		/* cannot be a discriminant constraint.*/
		return comp_type;
	}
	if (is_access(comp_type)) {
		/* create access type to new constrained array type.*/
		new_acc = sym_new(na_subtype);
		dcl_put(DECLARED(scope_name), str_newat(), new_acc);
		TYPE_OF(new_acc)      = TYPE_OF(comp_type);
		SIGNATURE(new_acc)    = constraint_new(CONSTRAINT_ACCESS);
		SIGNATURE(new_acc)[2] = (char *)new_type;	/*designated type*/
		SCOPE_OF(new_acc)     = scope_name;
		ALIAS(new_acc)        = ALIAS(comp_type);
		return new_acc;
	}
	else
		return new_type;
}

void valid_task_name(Node task_name)					 /*;valid_task_name*/
{
	/* First pass over an expression that must yield a task type: called to
	 * resolve entry names.
	 */

	Set	task_types;
	Forset	fs1;
	Symbol	t;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : valid_task_name");

	resolve1(task_name);
	task_types = set_new(0);
	FORSET(t = (Symbol), N_PTYPES(task_name), fs1);
		if (is_task_type(t)
	      || (is_access(t) && is_task_type(designated_type(t))))
			task_types = set_with(task_types, (char *) t);
	ENDFORSET(fs1);

	if (set_size(task_types) == 0) {
		errmsg("expect task name ", "9.5", task_name);
	}

	N_PTYPES(task_name) = task_types;
}

void complete_task_name(Node task1, Symbol context_typ)  /*;complete_task_name*/
{
	/* Complete resolution of task name used in an entry name.The context_typ
	 * is obtained from the	scope of  the resolved	entry name. Derived task
	 * types have the same entries as their root type, and the unique type of
	 * the task name is thus the one whose root type is the context type.
	 */

	Node	a_task;
	Set	types;
	Symbol	t, tmp;
	int	exists;
	Forset	fs1;
	Symbol	t_n;

	if (cdebug2 > 3)  TO_ERRFILE("AT PROC : complete_task_name");

	types = N_PTYPES(task1);
	exists = FALSE;
	FORSET(t = (Symbol), types, fs1);
		if (root_type(t) == context_typ) {
			exists = TRUE;
			break;
		}
	ENDFORSET(fs1);
	if (exists) {
		resolve2(task1, t);
		if (N_KIND(task1) != as_simple_name) eval_static(task1);
	}
	else {
		exists = FALSE;
		FORSET(t = (Symbol), types, fs1);
			tmp =  (Symbol) designated_type(t);
			if (is_access(t) &&
		    	root_type(tmp) == context_typ) {
				exists = TRUE;
				break;
			}
		ENDFORSET(fs1);
		if (exists) {
			resolve2(task1, t);
			if (N_KIND(task1) != as_simple_name) eval_static(task1);
			a_task = copy_node(task1);
			N_KIND(task1) = as_all; /* explicit dereference*/
			N_AST1(task1) = a_task; /* of access to task*/
			N_AST2(task1) = N_AST3(task1) = N_AST4(task1) = (Node) 0;
			N_TYPE(task1) = (Symbol) designated_type(t);
		}
		else { /* previous error.*/
			return;
		}
	}
	/* Within the task body a task type designates the object currently exe-
	 * cuting that task. We replace the task type with  what will be	 its
	 * run-time identity.
	 */
	t_n = N_UNQ(task1);
	if (N_KIND(task1) == as_simple_name && is_task_type(t_n)) {
		if (in_open_scopes(t_n))
			N_UNQ(task1) = dcl_get(DECLARED(t_n), "current_task");
		else {
			/* Use of the task type otherwise is invalid.*/
			errmsg("invalid use of task type outside of its own body", "9.1",
			  task1);
		}
	}
}

void res2_check(Node expn2, Symbol context_type)			/*;res2_check*/
{
	/* Called to impose constraints when needed, on aggregate components
	 * and allocated objects. These are non-sliding contexts for aggregates.
	 */

	int may_others;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  res2_check");

	may_others = full_others;
	full_others = TRUE;
	resolve2(expn2, context_type);

	apply_constraint(expn2, context_type);
	full_others = may_others;
	if (!noop_error)
		eval_static(expn2);
}

Symbol attribute_type(int attribute, Symbol typ, Node arg1, Node arg2)
														/*;attribute_type*/
{
	/* -attribute- is a predefined attribute. arg1 is the first arg,
	 * whose type is typ, and arg2 is the second argument (or a dummy 1).
	 * The result type of an attribute is either a numeric type, or
	 * the type of its first argument (	attributes of enumerations).
	 * FIRST and LAST are more complicated : they return the first
	 * value of the index type of the i'th dimension of their first
	 * argument.
	 * For enumeration types, FIRST and LAST simply return the type
	 * of the first argument.
	 */

	Symbol	n;
	Set		types2;
	int		dim;
	Symbol	a_type, root, t, t2;
	int		type_ok, exists;
	Forset	fs1;
	Unitdecl	ud;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : attribute_type");

	n = N_UNQ(arg2);
	if ((N_KIND(arg2) == as_simple_name) && (n != (Symbol)0))
		N_PTYPES(arg2) = set_new1((char *) TYPE_OF(n));
	else
		resolve1(arg2);		/* Begin resolution of second arg*/

	types2 = N_PTYPES(arg2);
	if (types2 == (Set)0) types2 = set_new(0);
	if (set_size(types2) == 0)	/* Some type error .*/
		return symbol_any;

	if ( attribute == ATTR_O_FIRST || attribute == ATTR_T_FIRST
	  || attribute == ATTR_O_LAST || attribute == ATTR_T_LAST
	  || attribute == ATTR_O_RANGE || attribute == ATTR_T_RANGE
	  || attribute == ATTR_O_LENGTH || attribute == ATTR_T_LENGTH) {
		/* The second argument must be a universal integer, and
		 * and must be static. Complete its resolution now.
 		 */
		if (set_mem((char *) symbol_universal_integer, types2)) {
			resolve2(arg2, symbol_universal_integer);
			specialize(arg2, symbol_integer);
		}
		else
			pass1_error_str("index number of attribute % must be universal",
			  attribute_str(attribute), "Appendix A", arg2);

		if (! is_static_expr(arg2)
		  || N_KIND(arg2) != as_ivalue 
		  || ((Const)N_VAL(arg2))->const_kind != CONST_INT) {
			pass1_error_str("Second argument of % must be static integer", 
			  attribute_str(attribute), "3.6.2", arg2); /* ?? */

			dim = 1;	/* assume 1*/
		}
		else dim = INTV((Const)N_VAL(arg2));

		a_type = typ;
		if (is_array(typ)) {
			if (is_type_node(arg1) && can_constrain(N_UNQ(arg1))) {
				pass1_error_str("Unconstrained array type for attribute %",
				  attribute_str(attribute), "3.6.2", arg1);
				return symbol_any;
			}
			if ( (dim > no_dimensions(typ)) || (dim < 1)) {
				pass1_error_l("Invalid dimension number for array type",
				  " in attribute", "3.6.2", arg1);
				return symbol_any;
			}
			if (attribute == ATTR_O_LENGTH || attribute == ATTR_T_LENGTH)
				a_type = symbol_universal_integer;
			else {
				/* Get type of index for specified dimension.*/
				a_type = (Symbol) index_types(a_type)[dim];
			}
		}
	}
	else if (attribute == ATTR_ADDRESS) {
		ud = unit_decl_get("spSYSTEM");
		if (ud == (Unitdecl)0 || !in_vis_mods(ud->ud_unam)) {
			/* The use of this attribute seems incorrect if its type
			 * cannot be named.
			 */
			errmsg("use of SYSTEM.ADDRESS requires presence of package SYSTEM",
			  "13.7.2, Annex A", arg1);
			a_type = symbol_integer; /* Closest thing we've got.*/
		}
		else {
			/*a_type = ??visible('SYSTEM')('ADDRESS');*/
			a_type = dcl_get_vis(DECLARED(ud->ud_unam), "ADDRESS");
		}
	}
	else if (attribute != ATTR_BASE
	  &&     attribute != ATTR_T_FIRST && attribute != ATTR_O_FIRST
	  &&     attribute != ATTR_O_LAST && attribute != ATTR_T_LAST
	  &&     attribute != ATTR_PRED
	  &&     attribute != ATTR_O_RANGE && attribute != ATTR_T_RANGE
	  &&     attribute != ATTR_SUCC
	  &&     attribute != ATTR_VAL
	  &&     attribute != ATTR_VALUE) {

		/*a_type = TYPE_OF(attribute);*/
		if ( attribute == ATTR_AFT
		  || attribute == ATTR_COUNT
		  || attribute == ATTR_DIGITS 
		  || attribute == ATTR_EMAX 
		  || attribute == ATTR_FIRST_BIT 
		  || attribute == ATTR_FORE 
		  || attribute == ATTR_LAST_BIT 
		  || attribute == ATTR_LAST_BIT 
		  || attribute == ATTR_O_LENGTH || attribute == ATTR_T_LENGTH 
		  || attribute == ATTR_MACHINE_EMAX 
		  || attribute == ATTR_MACHINE_EMIN 
		  || attribute == ATTR_MACHINE_MANTISSA 
		  || attribute == ATTR_MACHINE_RADIX 
		  || attribute == ATTR_MANTISSA 
		  || attribute == ATTR_POS 
		  || attribute == ATTR_POSITION 
		  || attribute == ATTR_SAFE_EMAX 
		  || attribute == ATTR_O_SIZE || attribute == ATTR_T_SIZE 
		  || attribute == ATTR_STORAGE_SIZE 
		  || attribute == ATTR_WIDTH) {
			a_type = symbol_universal_integer;
		}
		else if (attribute == ATTR_DELTA
		  ||     attribute == ATTR_EPSILON	
		  ||     attribute == ATTR_LARGE	
		  ||     attribute == ATTR_SMALL	
		  ||     attribute == ATTR_SAFE_LARGE	
		  ||     attribute == ATTR_SAFE_SMALL) {
			a_type = symbol_universal_real;
		}
		else if (attribute==ATTR_O_CONSTRAINED || attribute==ATTR_T_CONSTRAINED
		  ||     attribute == ATTR_MACHINE_OVERFLOWS	
		  ||     attribute == ATTR_MACHINE_ROUNDS	
		  ||     attribute == ATTR_CALLABLE	
		  ||     attribute == ATTR_TERMINATED) {
			a_type = symbol_boolean;
		}
		else if (attribute == ATTR_IMAGE)
			a_type = symbol_string;
	}
	else if (attribute == ATTR_BASE
	  ||     attribute == ATTR_POS
	  ||     attribute == ATTR_PRED
	  ||     attribute == ATTR_SUCC
	  ||     attribute == ATTR_VAL
	  ||     attribute == ATTR_VALUE) {
		a_type = base_type(typ);
	}
	else {
		a_type = typ;
	}

	root = root_type(typ);

	/* Now verify that the type of the argument is valid for the attribute.*/

	t = N_UNQ(arg1);
	if (t != (Symbol)0 && tup_mem((char *) t, open_scopes)
	  && NATURE(t) == na_record) {
		errmsg_id("Invalid self-reference in definition of %", t, "3.1", arg1);
	 	/* ?? */
		return symbol_any;
	}

	if (attribute == ATTR_ADDRESS)
		type_ok =  !is_type_node(arg1);
	else if (attribute == ATTR_BASE)
		type_ok =	  is_type(root);
	else if (attribute == ATTR_T_FIRST || attribute == ATTR_O_FIRST
	  || attribute == ATTR_O_LAST || attribute == ATTR_T_LAST)
		type_ok =  is_scalar_type(root) || is_array(root);
	else if (attribute == ATTR_VALUE) {
		if (!is_discrete_type(root))
			type_ok = FALSE;
		else {
			exists = FALSE;
			FORSET(t2 = (Symbol), types2, fs1);
				if (compatible_types(symbol_string, t2)) {
					exists = TRUE;
					break;
				}
			ENDFORSET(fs1);
			type_ok = exists;
		}
	}
	else if (attribute == ATTR_IMAGE
	  ||     attribute == ATTR_POS
	  ||     attribute == ATTR_PRED
	  ||     attribute == ATTR_SUCC) {
		if (! is_discrete_type(root))
			type_ok = FALSE;
		else {
			exists = FALSE;
			FORSET(t2 = (Symbol), types2, fs1);
				if (compatible_types(typ, t2)) {
					exists = TRUE;
					break;
				}
			ENDFORSET(fs1);
			type_ok =  exists;
		}
	}
	else if (attribute == ATTR_VAL) {
		if (!is_discrete_type(root))
			type_ok = FALSE;
		else {
			exists = FALSE;
			FORSET(t2 = (Symbol), types2, fs1);
				if (is_integer_type(root_type(t2))) {
					exists = TRUE;
					break;
				}
			ENDFORSET(fs1);
			type_ok =  exists;
		}
	}
	else if (attribute == ATTR_AFT
	  ||     attribute == ATTR_DELTA
	  ||     attribute == ATTR_FORE) {
		type_ok =   is_fixed_type(root);
	}
	else if (attribute == ATTR_DIGITS
	  ||     attribute == ATTR_EMAX
	  ||     attribute == ATTR_EPSILON
	  ||     attribute == ATTR_MACHINE_RADIX
	  ||     attribute == ATTR_MACHINE_MANTISSA
	  ||     attribute == ATTR_MACHINE_EMAX
	  ||     attribute == ATTR_MACHINE_EMIN
	  ||     attribute == ATTR_SAFE_EMAX) {
		type_ok =		root == symbol_float;
	}
	else if (attribute == ATTR_LARGE
	  ||    attribute == ATTR_MACHINE_ROUNDS
	  ||    attribute == ATTR_MACHINE_OVERFLOWS
	  ||    attribute == ATTR_MANTISSA
	  ||    attribute == ATTR_SMALL
	  ||    attribute == ATTR_SAFE_LARGE
	  ||    attribute == ATTR_SAFE_SMALL) {
		if (is_fixed_type(root) || root == symbol_float)
			type_ok = TRUE;
		else
			type_ok = FALSE;
	}
	else if (attribute == ATTR_O_LENGTH || attribute == ATTR_T_LENGTH
	  || attribute == ATTR_O_RANGE || attribute == ATTR_T_RANGE)
		type_ok = is_array(root);
	else if (attribute==ATTR_O_CONSTRAINED || attribute == ATTR_T_CONSTRAINED) {
		if (is_type_node(arg1))
			type_ok = is_private(typ);
		else if ( is_record(root) && has_discriminants(root))
			type_ok = TRUE;
		else
			type_ok = FALSE;
	}
	else if (attribute == ATTR_TERMINATED || attribute == ATTR_CALLABLE) {
		if (is_access(root)) root = (Symbol) designated_type(root);
		type_ok =  is_task_type(root);
	}
	else if (attribute == ATTR_STORAGE_SIZE)
		type_ok =  (is_task_type(root) || is_access(root));
	else if (attribute == ATTR_WIDTH)
		type_ok = is_discrete_type(root);

	else if (attribute == ATTR_COUNT
	  ||    attribute == ATTR_FIRST_BIT
	  ||    attribute == ATTR_LAST_BIT
	  ||    attribute == ATTR_O_SIZE || attribute == ATTR_T_SIZE
	  ||    attribute == ATTR_POSITION) {
		type_ok =  TRUE;
	}

	else {
		errmsg_str("Undefined attribute: %", attribute_str(attribute),
		  "Annex A", arg1);
		a_type = symbol_any;
		type_ok = TRUE;
	}

	if (type_ok) return a_type;
	else {
		pass1_error_str("Invalid argument type for attribute %",
		  attribute_str(attribute), "Annex A", arg1);
		return symbol_any;
	}
}

int compatible_types(Symbol t_out, Symbol t_in) /*;compatible_types*/
{
	/* This procedure verifies that an expression of type -t_in- can appear
	 * in a context requiring type -t_out-. In the case of subtypes this
	 * procedure indicates whether a run-time check will be necessary.
	 * Equality, set and comparison operators carry a special type-marker which
	 * is ignored on the first pass of type resolution, because the type of
	 * the arguments of these operators have no effect on the result type.
	 * On the second pass, these special type-markers are used to indicate
	 * the need for a consistency check among the types of the two actual
	 * parameters themselves.
	 */

	Symbol	r;
	int	n;
	Symbol tmp;

	if (cdebug2 > 0) {
		TO_ERRFILE("check compatible types ");
		printf("  %s %s\n", ((t_out != (Symbol)0) ? ORIG_NAME(t_out): ""),
		  ((t_in != (Symbol) 0)? ORIG_NAME(t_in) : ""));
	}
	if (t_in == (Symbol)0 || t_out == (Symbol)0	/* syntax error*/
	  || (t_in == t_out)	/*compatible types*/
	  || in_multiple_types(t_in) || in_multiple_types(t_out)) {
		return TRUE;
	}
	/* The generic types 'universal_integer', 'universal_real', 'string_type'
	 * and '$FIXED' are used to indicate the type of the corresponding literals.
	 * These types are compatible with specific types of the same family.
	 * On the other hand, the generic 'universal_fixed' is incompatible
	 * with all types, and its presence in any type checking will trigger an
	 * error message, at some point.
	 * To avoid checking for their presence on both sides, we perform the
	 * following normalization :
	 */
	if (!in_gen_types(t_in) && in_gen_types(t_out)) {
		tmp = t_in; 
		t_in = t_out; 
		t_out = tmp;
	}

	if (t_in == symbol_universal_integer)
		return ( root_type(t_out) == symbol_integer);
	else if(t_in == symbol_universal_real)
		return (root_type(t_out) == symbol_float ||
		  (t_out != symbol_universal_fixed && is_fixed_type(root_type(t_out))));
	else if (t_in == symbol_universal_type)
		return in_univ_types(t_out);
	else if (t_in == symbol_dfixed)
		return (t_out == symbol_universal_real || is_fixed_type(t_out));
	else if (t_in == symbol_boolean_type)
		return (root_type(t_out) == symbol_boolean || (is_array(t_out)
		  && root_type((Symbol) component_type(t_out)) == symbol_boolean));
	else if (t_in == symbol_discrete_type)
		return(	    is_discrete_type(t_out));
	else if(t_in == symbol_integer_type)
		return (root_type(t_out) == symbol_integer
		  || t_out == symbol_universal_integer);
	else if (t_in == symbol_real_type) {
		r = root_type(t_out);
		return (r == symbol_float 
		  || (r != symbol_universal_fixed && is_fixed_type(r))
		  || r == symbol_universal_real);
	}
	else if(t_in == symbol_string_type)
		return (is_array(t_out) && no_dimensions(t_out) ==  1
		  && is_character_type(component_type(t_out)));
	else if(t_in == symbol_character_type)
		return(is_character_type(t_out));
	else if (t_in == symbol_array_type)
		return(is_array(t_out));
	else if (t_in == symbol_composite_type) {
		n = NATURE(root_type(t_out));
		return(n == na_array || n == na_record);
	}
	else if(t_in == symbol_universal_fixed)
		return	 FALSE;
	else
		/* name equivalence of base types holds for everything else.*/
		return  (base_type(t_in) == base_type(t_out));
}

static int in_gen_types(Symbol t)						 /*;in_gen_types*/
{
	return (
	    t == symbol_array_type	
	 || t == symbol_boolean_type  
	 || t == symbol_character_type 
	 || t == symbol_composite_type
	 || t == symbol_discrete_type 
	 || t == symbol_dfixed
	 || t == symbol_integer_type   
	 || t == symbol_real_type
	 || t == symbol_string_type     
	 || t == symbol_universal_integer 
	 || t == symbol_universal_real
	 || t == symbol_universal_fixed 
	 || t == symbol_universal_type);
}

static int in_multiple_types(Symbol t)  /*;in_multiple_types*/
{
	return (t == symbol_equal_type
	  ||    t == symbol_order_type
	  ||    t == symbol_any);
}

void type_error(Set op_names, Symbol typ, int num_types, Node node)
																/*;type_error*/
{
	/* Emit error message after a type error was detected during
	 * type resolution.
	 * if num_types > 1, the expression is ambiguous : the operator of
	 * op_names is overloaded, and the argument list is not sufficient to
	 * disambiguate.
	 * If num_types = 0, the argument list is incompatible with the op.
	 */

	Symbol	op_name;
	char	*op_n; /*TBSL: check type of op_n*/
	char	*names;
	int		nat;

	if (cdebug2 > 3) {
		TO_ERRFILE("AT PROC :  type_error");
#ifdef TBSL
		TO_ERRFILE('opname=' + str op_names);
#endif
	}

	/* avoid taking set_arb of empty set	ds 8 aug */
	if (set_size(op_names) == 0)
		op_name = (Symbol)symbol_undef;
		/* this should parallel SETL   gcs 19 feb 
		 * Looks like noop_error should be set (but is not) 
		 */
	else
		op_name = (Symbol) set_arb(op_names);

	op_n = ORIG_NAME(op_name);
	if (N_KIND(node) == as_simple_name)
		N_UNQ(node) = op_name;	/* to avoid cascaded errors */
	if (num_types > 1) {
		nat = NATURE(op_name);

		if (nat == na_procedure || nat == na_function 
		  || nat == na_procedure_spec || nat == na_function_spec) {
#ifdef TBSL
			names :
				= +/[original_name(scope_of(x)) + '.' +
		   		 original_name(x) + ' ' : x in  op_names];
#endif
			names = build_full_names(op_names);
			errmsg_str("Ambiguous call to one of %", names, "6.6, 8.3", node);
		}
		else if (nat == na_op) {
			errmsg_str("Ambiguous operands for %", op_n, "6.7, 8.3", node);
		}
		else if (nat == na_literal) {
			errmsg_str("Ambiguous literal: %", op_n, "3.5.1, 4.7, 8.3", node);
		}

		else {
			errmsg("ambiguous expression", "8.2, 8.3", node);
		}

		/* If the type is ambiguous the expression is of couse invalid.*/

		noop_error = TRUE;
	}
	else {		/* Num_types is zero.*/
		if (noop_error) {
			/* Current expression contained previous error. Do not emit
			 * an aditional one.
			 */
			return;
		}

		noop_error = TRUE; /* For sure.*/

		if (typ == (Symbol) 0) {	/* Operator or subprogram .*/
			if (strcmp(op_n, "GET") == 0 || strcmp(op_n, "PUT") == 0) {
				errmsg("TEXT_IO not instantiated nor defined for type",
				  "8.4, 14.4", node);
			}
			else {
				if (NATURE(op_name) == na_entry
				  || NATURE(op_name) == na_entry_family) {
					op_n = "entry call";
				}
				if (NATURE(op_name) == na_op)
					errmsg_str("invalid types for %", op_n, "none", node);
				else {
					errmsg_str("invalid argument list for %",op_n,"none", node);
				}
			}
		}
		else if (NATURE(op_name) == na_literal) {
			errmsg_id_type("no instance of % has type %", op_name, typ,
			  "3.5.1", node);
		}
		else {
			errmsg_type("Expect expression to yield type %", typ, "none", node);
		}
	}
}

void premature_access(Symbol type_mark, Node node)		 /*;premature_access*/
{
	/* Called when trying to use ( an access to) a fully private type.*/
	pass1_error_id("Premature usage of access, private or incomplete type %",
	  type_mark, "7.4.2", node);
	return;
}

/* variations of this procedure are defined in errmsg.c */
void pass1_error(char *msg1, char *lrm_sec, Node node) /*;pass1_error*/
{
	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  pass1_error");

	/* This procedure is invoked when a type error which requires a special
	 * message is encountered in resolve1.
	 */

	if (!noop_error)
		/* to avoid errmsg prepass */
		errmsg(msg1, lrm_sec, node);
	noop_error = TRUE;	/* To avoid cascaded errors.*/
}

char *full_type_name(Symbol typ)	/*;full_type_name*/
{
	/* Error message procedure. Restore source name of type, or if anonymous
	 * build some approximate description of its ancestry.
	 */
	/* Note that this is only called as part of error message and need ot
	 * be provided until full error messages supported	ds 14 aug
	 */

	char *type_name;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  full_type_name");

	type_name = ORIG_NAME(typ);
	if (type_name == (char *)0 || strlen(type_name) == 0) { /* Anonymous type.*/
		/* TBSL: check above line for anonymous vs. undefined */
		if ( NATURE(typ) == na_subtype)
			type_name = full_type_name(TYPE_OF(typ));
		else if (NATURE(typ) == na_array)
			type_name = strjoin(strjoin("array(",
			  full_type_name((Symbol) index_type(typ))), "...");

		else if (NATURE(typ) == na_type)		/* derived type */
			type_name = strjoin("new ", full_type_name(TYPE_OF(typ)));
		else type_name = strjoin("--anonymous--", "");
	}
	return type_name;
}

int is_type_node(Node node)									/*;is_type_node*/
{
	return (N_KIND(node) == as_simple_name && (is_type(N_UNQ(node))));
}

static int is_integer_type(Symbol sym)					/*;is_integer_type*/
{
	return (sym == symbol_integer || sym == symbol_short_integer
	  || sym == symbol_long_integer || sym == symbol_universal_integer);
}

static Triplet *triplet_new()
{
	return (Triplet *) emalloct(sizeof(Triplet), "triplet-new");
}
