/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* Todo: 

 3-12-86	ds	
 Modify format of as_return node so that new node of type as_number
 put in N_AST3 field to hold depth count formerly kept in N_VAL.

 30-oct-84	ds
 Note that N_VAL for node produced at end of return_statement()
 is different, is now integer giving depth, was tuple of length two.


id is defined in goto_statement but never used

*/

#include "attr.h"
#include "hdr.h"
#include "vars.h"
#include "setprots.h"
#include "dclmapprots.h"
#include "miscprots.h"
#include "errmsgprots.h"
#include "dbxprots.h"
#include "evalprots.h"
#include "nodesprots.h"
#include "smiscprots.h"
#include "chapprots.h"

#define label_unreachable 0
#define label_reachable 1

static void new_symbol(Symbol, int, Symbol, Tuple, Symbol);
static Const get_static_nval(Node);
static void replace_others(Node, Node, int, int);

Symbol slice_type(Node node, int is_renaming)	     /*;slice_type*/
{
	Node   array_node, range_node, low_node, high_node, type_node;
	Node   new_range_node, arg1, arg2, var_node;
	Symbol type_name, type_mark, index_name, i_type;
	Tuple  tup;
	int    attr_prefix, kind;

	/* We must have a subtype for the aggregate to give the bounds */
	if (is_renaming) {
		var_node = N_AST3(node);
	} 
	else
		var_node = N_AST1(node);
	array_node = N_AST1(var_node);
	range_node = N_AST2(var_node);
	kind = N_KIND(range_node);
	if (kind == as_simple_name || kind == as_name)
		type_name = N_UNQ(range_node);
	else {
		if (kind == as_subtype) {
			type_node = N_AST1(range_node);
			new_range_node = N_AST2(range_node);
			low_node  = N_AST1(new_range_node);
			high_node = N_AST2(new_range_node);
		}
		else if (kind == as_range) {
			low_node = N_AST1(range_node);
			high_node = N_AST2(range_node);
		}
		else if (kind == as_attribute) {
			/*att_node = N_AST1(range_node); -- not needed in C */
			arg1 = N_AST2(range_node);
			arg2 = N_AST3(range_node);
			/* subtract code for ATTR_FIRST to get T_ or O_ value */
			/* recall that in C attribute kind kept in range_node*/
			attr_prefix = (int)attribute_kind(range_node)-ATTR_RANGE;
			/* 'T' or 'O' */
			attribute_kind(range_node) = (char *)((int) attr_prefix+ATTR_FIRST);
			low_node = range_node;
			high_node = new_attribute_node(attr_prefix+ATTR_LAST,
			  copy_node(arg1), copy_node(arg2), get_type(range_node));
			eval_static(low_node);
			eval_static(high_node);
		}
		else {
			errmsg("Unexpected range in slice", "", range_node );
			low_node = OPT_NODE;
			high_node = OPT_NODE;
		}
		/* We need the bounds twice, for the slice and for the aggregate
	     * so we build an anonymous subtype to avoid double evaluation
	     */
		if (N_KIND(array_node) == as_simple_name
		  || N_KIND(array_node) == as_name)
			type_mark = TYPE_OF(N_UNQ(array_node));
		else
			type_mark = N_TYPE(array_node);
		type_mark = base_type(type_mark);		/* get base type */
		index_name = named_atom("slice_index_type");
		type_name = named_atom("slice_type");
		i_type= (Symbol) index_type(type_mark);
		tup = constraint_new(0);
		tup[2] = (char *) low_node;
		tup[3] = (char *) high_node;
		new_symbol(index_name, na_subtype, i_type, tup, ALIAS(i_type));
		SCOPE_OF(index_name) = scope_name;

		tup = constraint_new(4);
		tup[1] = (char *) tup_new1((char *) index_name);
		tup[2] = (char *) component_type(type_mark);

		new_symbol(type_name, na_subtype, type_mark, tup, ALIAS(type_mark));
		SCOPE_OF(type_name) = scope_name;
		tup = tup_new(2);
		tup[1] = (char *) new_subtype_decl_node(index_name);
		tup[2] = (char *) new_subtype_decl_node(type_name);
		make_insert_node(node, tup, copy_node(node));
		N_AST1(var_node)  = array_node;
		N_AST2(var_node)  = new_name_node(index_name);
		copy_span(range_node, N_AST2(var_node));
	}
	return type_name;
}

static void new_symbol(Symbol new_name, int new_nature, Symbol new_type,
  Tuple new_signature, Symbol new_alias)						/*;new_symbol*/
{
	NATURE(new_name)	= new_nature;
	TYPE_OF(new_name)	= new_type;
	SIGNATURE(new_name) = new_signature;
	ALIAS(new_name)	= new_alias;
	dcl_put(DECLARED(scope_name), str_newat(), new_name);
}

Symbol get_type(Node node)										/*;get_type*/
{
	/*
	 * GET_TYPE is procedure get_type() in C:
	 * 	macro GET_TYPE(node);
	 *  (if N_KIND(node) in [as_simple_name, as_subtype_indic]
	 *                        then TYPE_OF(N_UNQ(node))
	 *                        }
	 *                        else N_TYPE(node) end )                   endm;
	 */

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
		else
			sym =  TYPE_OF(sym);
	}
	else
		sym = N_TYPE(node);

	return sym;
}

void assign_statement(Node node)  /*;assign_statement*/ 
{
	Node var_node, exp_node;
	Symbol t, t1, t2, ok_sym;
	Set	t_l, t_left, t_right, ok_types, ook_types;
	Forset	tiv, tforl, tforr, fs1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  assign_statement");

	var_node = N_AST1(node);
	exp_node = N_AST2(node);

	noop_error = FALSE;		/* To clear previous type errors */

	adasem(var_node);
	find_old(var_node);			/* left-hand side is a name.*/
	adasem(exp_node);

	resolve1(var_node);
	t_l = N_PTYPES(var_node);
	t_left = set_new(0);
	FORSET(t = (Symbol), t_l, tiv);
		if (! is_limited_type(t)) t_left = set_with(t_left, (char *) t);
	ENDFORSET(tiv);
	resolve1(exp_node);
	t_right = N_PTYPES(exp_node);

	if (noop_error) {	/* previous error. */
		noop_error = FALSE;
		return;
	}

	ok_types = set_new(0);
	FORSET(t1 = (Symbol), t_left, tforl);
		FORSET(t2 = (Symbol), t_right, tforr);
			if (compatible_types(t1, t2) )
				ok_types = set_with(ok_types, (char *) t1);
		ENDFORSET(tforr);
	ENDFORSET(tforl);
	/* For the assignment to be unambiguous, the left-hand and right_hand
	 * sides must have a single compatible interpretation.
	 */
	if (set_size(ok_types) == 0) {
		if (set_size(t_l) == 1 && set_size(t_left) == 0) {
			errmsg("assignment not available on a limited type", "7.4.2",
			  var_node);
			set_free(ok_types);
			return;
		}
		else {
			errmsg("incompatible types for assignment", "5.2", node);
			set_free(ok_types);
			return;
		}
	}
	else if (set_size(ok_types) > 1) {	/* ambiguous left-hand side */
		remove_conversions(var_node);	    /* last chance. */
		ook_types = ok_types;
		ok_types = set_new(0);
		FORSET(ok_sym=(Symbol), N_PTYPES(var_node), fs1);
			if (set_mem((char *) ok_sym, ook_types))
				ok_types = set_with(ok_types, (char *)ok_sym);
		ENDFORSET(fs1);
		set_free(ook_types);
		if (set_size(ok_types) != 1) {
			errmsg("ambiguous types for assigment", "5.2", var_node);
			set_free(ok_types);
			return;
		}
	}
	t1 = (Symbol) set_arb(ok_types);  /* Now unique. */
	set_free(ok_types);
	out_context = TRUE;
	resolve2(var_node, t1);
	out_context = FALSE;
	/*if (N_KIND(var_node) == as_slice && (N_KIND(exp_node) == as_aggregate
        ||N_KIND(exp_node) == as_string_literal)){*/

	/* we don't have to care about the type of the right hand side cf Setl */
	if (N_KIND(var_node) == as_slice) {
		/* context is constrained, even though type of lhs is base type
		 * This means that an OTHERS association is allowed.
		 */
		t1 = slice_type(node,0);
		resolve2 (exp_node, t1);
		return;
	}

	if(NATURE(t1) == na_array && N_UNQ(var_node) != (Symbol)0 &&
	  (NATURE(N_UNQ(var_node))==na_inout || NATURE(N_UNQ(var_node))==na_out))
		replace_others(exp_node, var_node, tup_size(index_types(t1)), 1);

	resolve2(exp_node, t1);

	if (! is_variable(var_node)){
		errmsg("left-hand side in assignment is not a variable", "5.2",
		  var_node);
		return;
	}

	if (is_array(t1) ) {
		/* array assignments are length_checked in the interpreter, and don't
		 * carry a qualification.
		 */
		;
	}
	else if (!in_qualifiers(N_KIND(exp_node))) {
		/* a constraint check on the right hand side may be needed.*/
		N_TYPE(exp_node) = base_type(t1);
		apply_constraint(exp_node, t1);
	}
	eval_static(var_node);
	eval_static(exp_node);

	noop_error = FALSE;		/* clear error flag */
}

static void replace_others(Node agg_node, Node var_node, int max_dim, int dim)
															/*;replace_others*/
{
	/* This function's sole purpose is to replace the OTHERS choice in an
	 *  array aggregate with a RANGE choice, when the OTHERS is the only
	 *  choice and the aggregate is on the right side of an assignment
	 *  statement.  It presumes that the aggregate is properly formed
	 *  since that is checked elsewhere. It must call itself recursively
	 *  to check the higher numbered dimensions.
	 */

	Node association, choice_list, choices, choice;
	Tuple assoc_list;
	Fortup ft1;

	/* Check conditions allowing immediate return */
	if (N_KIND(agg_node) != as_aggregate)
		return;
	if (dim > max_dim)  /* All dimensions have been checked */
		return;
	if ((assoc_list = N_LIST(agg_node)) == (Tuple)0 || tup_size(assoc_list) ==0)
		/* Return if no entries (component associations) in aggregate */
		return;

	/* Recursive call for each association's expression */
	FORTUP(association = (Node), assoc_list, ft1)
		replace_others(N_AST2(association), var_node, max_dim, dim + 1);
	ENDFORTUP(ft1)

	/* Check for OTHERS to be replaced */
	if (tup_size(assoc_list) != 1) return;
	choice_list = (Node)assoc_list[1];
	if (N_KIND(choice_list) != as_choice_list) return;
	choices = N_AST1(choice_list);
	if (N_LIST(choices) == (Tuple)0) return;
	if (tup_size(N_LIST(choices)) != 1) return;
	choice = (Node)N_LIST(choices)[1];
	if (N_KIND(choice) != as_others_choice) return;

	/* Replace */
	N_KIND(choice) = as_range_choice;
	choice = (N_AST1(choice) = node_new(as_attribute));
	N_AST1(choice) = node_new(as_number);
	N_VAL(N_AST1(choice)) = (char *)ATTR_RANGE;
	N_AST2(choice) = copy_node(var_node);
	N_AST3(choice) = OPT_NODE;
}

int is_variable(Node node)  /*;is_variable*/  
{
	/* Verify that an expression is a variable name. This is called for
	 * assignment statements, when validating  -out- and -inout-
	 * parameters in a procedure or entry call, and for generic inout parms.
	 */

	Node array_node, sel_node;
	Node rec_node, exp_node;
	int	nat ;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  is_variable");

	switch (N_KIND(node)) {
	case as_simple_name:
		nat = NATURE(N_UNQ(node));
		return ( nat == na_obj || nat == na_inout || nat == na_out);
	case as_index:
	case as_slice:
		array_node  = N_AST1(node);
		return (is_variable(array_node) );
	case as_selector:
		rec_node = N_AST1(node);
		sel_node= N_AST2(node);
		return (is_variable(rec_node) && NATURE(N_UNQ(sel_node)) == na_obj );
	case as_all:
		/* access_node = N_AST1(node);
		 * return (N_KIND(access_node) == as_simple_name ||
		 *   is_variable(access_node) ||
		 *   N_KIND(access_node) == as_call
		 *   && is_access(N_TYPE(access_node))
		 * 	);
		 */
		return TRUE; /* designated object is always assignable */
	default:
		return FALSE;
	}
}

void statement_list(Node node)  /*;statement_list*/
{
	Node	stmt_list, label_list, l;
	Symbol	ls;
	int	i;
	Fortup	ft1;
	Tuple	labs;
	stmt_list = N_AST1(node);
	label_list = N_AST2(node);

	/* labs := [N_UNQ(l) : l in N_LIST(label_list)]; */
	labs = tup_new(tup_size(N_LIST(label_list)));
	FORTUPI(l = (Node), N_LIST(label_list), i, ft1);
		labs[i] = (char *) N_UNQ(l);
	ENDFORTUP(ft1);
	/* Within the statement list, all labels defined therein are reachable
	 * by goto statements in that list.
	 */
	FORTUP(ls = (Symbol), labs, ft1);
		label_status(ls) = (Tuple) label_reachable;
	ENDFORTUP(ft1);
	FORTUP(l = (Node), N_LIST(stmt_list), ft1);
		if (N_KIND(l) != as_line_no)
			adasem(l);
	ENDFORTUP(ft1);

	/* On exit, these labels become unreachable.*/
	FORTUP(ls = (Symbol), labs, ft1);
		label_status(ls) = (int) label_unreachable;
	ENDFORTUP(ft1);
	tup_free(labs);
}

void if_statement(Node node)							   /*;if_statement*/
{
	Fortup	ft1;
	Node	cond_node, stmt_node, if_list, else_node, tnode;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  if_statement");

	if_list = N_AST1(node);
	else_node = N_AST2(node);

	FORTUP(tnode = (Node), N_LIST(if_list), ft1);
		cond_node = N_AST1(tnode);
		stmt_node = N_AST2(tnode);
		adasem(cond_node);
		adasem(stmt_node);
	ENDFORTUP(ft1);

	adasem(else_node);
}

void case_statement(Node node)							  /*;case_statement*/
{
	Symbol	exptype;
	Node	exp_node, cases;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  case_statement");

	exp_node = N_AST1(node);
	cases = N_AST2(node);

	adasem(exp_node);
	check_type_d(exp_node);
	exptype = N_TYPE(exp_node);

	if (exptype == symbol_any) 		/* Type error. */
		return;
	else
		if (exptype == symbol_universal_integer)
			/*exptype = symbol_integer;*/
			specialize(exp_node, symbol_integer);

	process_case(exptype, cases);
}

void process_case(Symbol exptype, Node cases)  /*;process_case*/
{

	Forset	fs1;
	int invalid_case_type;
	Symbol	exp_base_type;
	Node		exp_lo, exp_hi;
	int	t;
	int		exp_lov, exp_hiv, range_size;
	Tuple	case_list, cs, tup, sig, choice_alt;
	int		is_others_part;
	Set		valset;
	int		numval;
	Node	stmt_list, choice_list, c, ch, choices;
	Node	choice, lo, hi, last_choices, alternative;
	Node	constraint, tmpnode;
	Symbol	choicev;
	int		lov, hiv, is_static;
	Tuple numcon;
	Node	stmts;
	int		range_choice, duplicate_choice, a, b;
	Fortup	ft1, ft2;
	Const	con;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  process_case");

	/* This procedure is given the type of the case expression and
	 * uses this type to resolve the choices appearing in the case_list.
	 * It also checks that the choices are static expressions and
	 * constructs the case statement intermediate code.
	 * It is called both for case statements and for variant parts.
	 *
	 * The case_list has the form
	 *
	 *	case_list ::= [ [choice_list, statement_list] ... ]
	 *
	 * where a choice_list is a sequence of choices,
	 *
	 *	choice_list ::= [choice ...]
	 *
	 * each of the form
	 *
	 *	choice ::= ["simple_choice", simp_expr ]
	 *		  |["range_coice",   discr_range]
	 *		  |["others_choice", OPT_NODE]
	 *
	 *
	 *	case_statement ::= ["case", expr, altlist, others]
	 *
	 * where
	 *	altlist	 ::=  { {choice} -> statement_list}
	 * and
	 *	choice ::=  choiceval | ["range", choiceval, choiceval]
	 *
	 * On exit, the VAL field of each choice list is the set of discrete
	 * values corresponding to the choices in the list.
	 */
	if (cdebug2 > 0) {
#ifdef ERRMSG
		TO_ERRFILE("case evaluation", exptype);
#endif
		TO_ERRFILE("case evaluation");
	}

	/* Check that the case expression is of a discrete type
	 * and that its range is static, and find the length of
	 * the range.
	 *
	 */
	invalid_case_type = FALSE;

	exp_base_type = base_type(exptype);

	if ( !is_discrete_type(exp_base_type)) {
		errmsg("Case expression not of discrete type", "3.7.3, 5.4", cases);
		invalid_case_type = TRUE;	/* Still check the alternatives*/

	}
	else if (is_generic_type(exp_base_type)) {
		errmsg("Case expression cannot be of a generic type", "5.4", cases);
		invalid_case_type = TRUE;
	}

	numcon = (Tuple) SIGNATURE(exptype);
	if (numcon == (Tuple) 0 ) {
		exp_lo = (Node)0;
		exp_hi = (Node)0;
	}
	else {
		exp_lo = (Node) numeric_constraint_low(numcon);
		exp_hi = (Node) numeric_constraint_high(numcon);
	}

	is_static = is_static_subtype(exptype);

	if (! is_static) {
		tup = SIGNATURE(exp_base_type);
		if (tup == (Tuple)0 ) {
			exp_lo = (Node)0;
			exp_hi = (Node)0;
		}
		else {
			exp_lo = (Node) tup[2];
			exp_hi = (Node) tup[3];
		}
		if (! is_static_expr(exp_lo) || !is_static_expr(exp_hi))
			/* This alternative can arise only if the type of the
			 * case expression does not have static bounds.  This
			 * has alreay been caught, so we give no error message here,
			 * but only the choices are type checked and no code put out.
			 */
			invalid_case_type = TRUE;
	}

	if (! invalid_case_type) {
		con = (Const) N_VAL(exp_lo);
		exp_lov = (int) con->const_value.const_int;
		con = (Const) N_VAL(exp_hi);
		exp_hiv = con->const_value.const_int;
		t = (exp_hiv - exp_lov + 1);
		range_size = t > 0 ? t : 0;
	}

	/* Now check each of the case choices against exp_base_type, and ensure
	 * that each is static.
	 */
	case_list = N_LIST(cases);

	FORTUP(c =(Node), case_list, ft1);
		/* Process statements or declarations, and resolve names in*/
		/* choice expressions. */
		choices = N_AST1(c);
		stmts = N_AST2(c);
		sem_list(choices);
		adasem(stmts);
	ENDFORTUP(ft1);

	is_others_part = FALSE;
	valset = set_new(0);
	numval = 0;
	if (tup_size(case_list)) { /* empty case list is allowed */
		tmpnode = (Node) case_list[tup_size(case_list)];
		last_choices = N_AST1(tmpnode);
		cs = N_LIST(last_choices);
		if (tup_size(cs) == 1 && N_KIND((Node)cs[1]) == as_others_choice) {
			is_others_part = TRUE;
			/* label the whole alternative as an OTHERS choice .*/
			N_KIND(tmpnode) = as_others_choice;
		}

		FORTUP(alternative =(Node) , case_list, ft1);
			choice_list = N_AST1(alternative);
			stmt_list   = N_AST2(alternative);
			choice_alt  = tup_new(0);

			FORTUP(ch=(Node), N_LIST(choice_list), ft2);
				if (N_KIND(ch) == as_others_choice) {
					is_others_part = TRUE;
					continue;
				}
				choice = N_AST1(ch);
				/* Type check the choice and  ensure that it is static,
				 * in the range	for the expression  subtype, and  that
				 * it appears no more than once in the list of values.
				 */

				if (N_KIND(ch) == as_choice_unresolved ) {
					find_old(choice);
					choicev = N_UNQ(choice);
					if (is_type (choicev) ) {
						if (! compatible_types(choicev, exp_base_type)) {
							errmsg_id("Choice must have type %", exp_base_type,
							  "5.4", ch);
							continue;
						}
						sig = SIGNATURE(choicev);
						lo = (Node) sig[2];
						hi = (Node) sig[3];
						if (is_static_expr(lo) && is_static_expr(hi) ) {
							eval_static(lo);
							con = (Const) N_VAL(lo);
							lov = con->const_value.const_int;
							eval_static(hi);
							con = (Const) N_VAL(hi);
							hiv = con->const_value.const_int;
						}
						else {
							errmsg("Case choice not static", "3.7.3, 5.4", ch);
							continue;
						}
						/* Reformat node as a simple type name. */
						copy_attributes(choice, ch);
					}
					else		/* expression: resolve below.*/
						N_KIND(ch) = as_simple_choice;
				}
				if (N_KIND(ch) == as_simple_choice) {
					check_type(exp_base_type, choice);

					if (N_TYPE(choice) == symbol_any || invalid_case_type )
						continue;
					else if (is_static_expr(choice)) {
						con = get_static_nval(choice);
						if (con == (Const)0)   /* previous error (?) */
							continue;
						lov = con->const_value.const_int;
						lo = hi = choice;
						hiv = lov;
					}
					else {
						errmsg("Case choice not static", "3.7.3, 5.4", ch);
						continue;
					}
				}
				else if (N_KIND(ch) == as_range_choice) {
					check_type(exp_base_type, choice);
					if (N_TYPE(choice) == symbol_any || invalid_case_type)
						continue;
					else {
						constraint = N_AST2(choice);
						lo = N_AST1(constraint);
						hi = N_AST2(constraint);
						if (is_static_subtype(N_TYPE(choice))
						  && is_static_expr(lo) && is_static_expr(hi)) {
							con = get_static_nval(lo);
							lov = con->const_value.const_int;
							con = get_static_nval(hi);
							hiv = con->const_value.const_int;
						}
						else {
							errmsg("Case choice not static", "3.7.3, 5.4", ch);
							continue;
						}
					}
				}
			/* At this point the choice is known to be static and is expressed
			 * as a range [lov, hiv].
			 */
				if (is_static && (lov<=hiv) && (lov<exp_lov || hiv > exp_hiv)) {
					errmsg_l("choice value(s) not in range of static ",
					  "subtype of case expression", "5.4", ch);
				}
				/* Remove junk values from below*/
				if (lov < exp_lov) lov = exp_lov;
				/* Remove junk values from above*/
				if (hiv > exp_hiv) hiv = exp_hiv;

				/* normalize all nodes to be ranges. */
				N_KIND(ch) = as_range;
				N_AST1(ch) = lo;
				N_AST2(ch) = hi;

				if (lov > hiv )			/* Null range -- ignore it.*/
					continue;

				/* Ensure that range is disjoint from all others. */

				range_choice = hiv > lov;
				duplicate_choice = FALSE;

				FORSET(tup =(Tuple) , valset, fs1);
					if (lov >= (int) tup[1] && lov <= (int)tup[2]) {
						duplicate_choice = TRUE;
						lov = (int)tup[2] + 1;
						break;
					}
				ENDFORSET(fs1);

				if (range_choice) {
					FORSET(tup = (Tuple), valset, fs1);
						a = (int) tup[1]; 
						b = (int) tup[2];
						if (hiv >= a && hiv <= b) {
							duplicate_choice = TRUE;
							hiv = a - 1;
							break;
						}
					ENDFORSET(fs1);
				}
				if (range_choice) {
					FORSET(tup = (Tuple), valset, fs1);
						a = (int) tup[1]; 
						b = (int) tup[2];
						if (lov<a && hiv>b) {
							duplicate_choice = TRUE;
							break;
						}
					ENDFORSET(fs1);
				}
				if (duplicate_choice) {
					errmsg("Duplicate choice value(s)", "3.7.3, 5.4", ch);
				}

				if (lov > hiv)				/*Again check for null range*/
					continue;

				/* Add interval to set of values seen so far, add the number 
		 		 * of choices to the count of values covered. 
		 		 */
				tup = tup_new(2);
				tup[1] = (char *) lov;
				tup[2] = (char *) hiv;
				valset = set_with(valset, (char *)tup);
				numval += (hiv - lov + 1);

				/* finally, normalize all nodes to be discrete ranges. */
				N_KIND(ch) = as_range;
				N_AST1(ch) = lo;
				N_AST2(ch) = hi;
			ENDFORTUP(ft2);
		ENDFORTUP(ft1);
	}
	/* Check that all of the possibilities in the range of the
	 * case expression have been used.
	 */
	if  (! invalid_case_type && ! is_others_part
	  && (numval != range_size || exptype == symbol_universal_integer))
	{
		errmsg("Missing OTHERS choice", "3.7.3, 5.4", cases);
	}
}

int is_static_subtype(Symbol subtype)  /*;is_static_subtype*/
{
	Symbol	bt;
	Node lo, hi;
	Tuple tup;

	bt = TYPE_OF(subtype);
	if (is_generic_type(bt) || in_incp_types(bt) || (! is_scalar_type(bt)))
		/*  RM 4.9 (11) */
		return FALSE;
	else if (bt == subtype)
		return TRUE;
	else {
		tup = (Tuple) SIGNATURE(subtype);
		lo = (Node) tup[2];
		tup = (Tuple) SIGNATURE(subtype);
		hi = (Node) tup[3];
		return (is_static_subtype(bt)
		  && N_KIND(lo) == as_ivalue && N_KIND(hi) == as_ivalue);
	}
}

static Const get_static_nval(Node node)			/*;get_static_nval */
{
	/* a choice may be a qualification, or it may carry a (spurious) constraint
	 * check. Reformat node to be a ivalue, as we know it is in bounds.
	 */

	int kind;

	kind = N_KIND(node);
	if (kind == as_qual_range) {
		copy_attributes(N_AST1(node), node);
		return get_static_nval(node);
	}
	else if (kind == as_qualify || kind == as_convert) {
		copy_attributes(N_AST2(node), node);
		return get_static_nval(node);
	}
	else return (Const)N_VAL(node);
}

void new_block(Node node)								/*;new_block*/
{
	Node	id_node, decl_node, stmt_node, handler_node;
	Symbol	block_name;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  new_block");

	id_node = N_AST1(node);
	decl_node  = N_AST2(node);
	stmt_node = N_AST3(node);
	handler_node = N_AST4(node);

	/* block names are declared when procedure containing them is entered. */
	block_name = N_UNQ(id_node);

	NATURE(block_name) = na_block;
	newscope(block_name);
	adasem(decl_node);
	adasem(stmt_node);
	adasem(handler_node);
	check_incomplete_decls(block_name, decl_node);
	popscope();
    force_all_types();
}

void loop_statement(Node node)						  /*;loop_statement*/
{
	Tuple	t;
	Symbol	loop_name;
	Node	id_node, iter_node, stmt_node;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  loop_statement");

	id_node = N_AST1(node);
	iter_node  = N_AST2(node);
	stmt_node = N_AST3(node);

	/* loop names are declared when procedure containing them is entered.*/

	find_old(id_node);
	loop_name = N_UNQ(id_node);
	NATURE(loop_name) = na_block;
	OVERLOADS(loop_name) = (Set) BLOCK_LOOP;
	t = tup_new(1);
	t[1] = (char *) FALSE;
	SIGNATURE(loop_name) = t;
	/* The loop is the scope of definition of the iteration variable.  */
	newscope(loop_name);
	adasem(iter_node);
	adasem(stmt_node);

	popscope();	/* Exit from loop scope.*/
}

/*?? is return needed */
Symbol iter_var(Node node)  /*;iter_var*/
{
	Node	id_node, range_node, def_node;
	Symbol	loop_var, iter_type, type_def;
	Tuple	t, tt, toptup, it;
	int	n; 
	char *id;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  iter_var");

	id_node = N_AST1(node);
	range_node = N_AST2(node);
	adasem(range_node);
	id = N_VAL(id_node);

	/* Insert loop variable in scope of loop. */
	loop_var = find_new(id);
	N_UNQ(id_node) = loop_var;

	/* If the iteration is given by a discrete range, construct an anonymous
	 * type for it, and save the defining expression. It is	 emitted as part
	 * of the loop header.
	 */
	iter_type = make_index(range_node);  /* $$$ PERHAPS */
	n = tup_size(newtypes);
	toptup = (Tuple) newtypes[n]; /* top newtypes */
	if ((Symbol)toptup[tup_size(toptup)] == iter_type) {
		/* Remove from anonymous types, and save subtype definition. */
		it = (Tuple)tup_frome(toptup);
		type_def = (Symbol) subtype_expr(iter_type);
	}
	else
		type_def = (Symbol) tup_new(0);
	NATURE(loop_var) = na_constant;
	TYPE_OF(loop_var) = iter_type;
	/* create dummy non-static default expression node for this (dummy) const */
	def_node = node_new(as_simple_name);
	N_VAL(def_node) = "";
#ifdef IBM_PC
	N_VAL(def_node) = strjoin("",""); /* copy literal */
#endif
	N_UNQ(def_node) = symbol_undef;
	default_expr(loop_var) = (Tuple) def_node;

	t = tup_new(2);
	t[1] = (char *) iter_type;
	t[2] = (char *) type_def;
	tt = SIGNATURE(scope_name);
	tt = tup_with(tt, (char *) t);
	SIGNATURE(scope_name) = tt;
	return loop_var;
}

void exit_statement(Node node)  /*;exit_statement*/
{
	Node	id_node, cond_node;
	Symbol	scope, sc;
	int	exists;
	Fortup	ft1;
	char	*id;
	Tuple	tup;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  exit_statement");

	id_node = N_AST1(node);
	cond_node = N_AST2(node);

	/* An unqualified exit refers to the innermost enclosing scope.  */
	if (id_node == OPT_NODE) {
		exists = FALSE;

		FORTUP(scope = (Symbol), open_scopes, ft1);
			if ((int)OVERLOADS(scope) == BLOCK_LOOP) {
				/* Indicate that loop label must be emitted. */
				tup = SIGNATURE(scope); 
				tup[1] = (char *)TRUE;
				exists = TRUE;
				break;
			}
		ENDFORTUP(ft1);
		if (! exists) {
			errmsg("EXIT statement not in loop", "5.7", node);
			return;
		}
	}
	else {
		id = N_VAL(id_node);
		/* Verify that loop label exists.*/
		exists = FALSE;
		FORTUP(scope = (Symbol), open_scopes, ft1);
			if (((int)OVERLOADS(scope) == BLOCK_LOOP)
			  && streq(original_name(scope), id)) {
				tup = SIGNATURE(scope);
				tup[1] = (char *) TRUE;
				exists = TRUE;
				break;
			}
		ENDFORTUP(ft1);
		if (! exists) {
			errmsg_str("Invalid loop label in EXIT: %",id, "5.5, 5.7", id_node);
			return;
		}
	}
	N_UNQ(node) = scope;

	/* Now verify that the exit statement does not try to exit from
	 * a procedure, task, package or accept statement. This amounts
	 * to requiring that the scope stack contain only blocks up to the
	 * scope being exited.
	 */
	FORTUP(sc = (Symbol), open_scopes, ft1);
		if (sc == scope) break;
		else if (NATURE(sc) != na_block) {
			errmsg_nat("attempt to exit from %", sc, "5.7", node);
			break;
		}
	ENDFORTUP(ft1);

	adasem(cond_node);
}

void return_statement(Node node)					/*;return_statement*/
{
	Node	exp_node, proc_node;
	int	j, nat, out_depth, certain;
	Symbol	r_type, proc_name, tsym;
	Fortup ft1;
	int	i, blktyp;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  return_statement");

	exp_node = N_AST1(node);

	/* Find subprogram or accept statement which is enclosing scope, and keep
	 * track of the	 number	 of blocks that	 have  to  be exited. This number
	 * is kept in the N_AST3 field for the node.
	 * The N_AST of the node receives an additional
	 * simple node to hold the unique name of the subprogram being exited. 
	 */
	has_return_stk[tup_size(has_return_stk)] = (char *)TRUE;

	certain = FALSE;
	FORTUPI(proc_name = (Symbol), open_scopes, i, ft1);
		nat = NATURE(proc_name);
		if (nat != na_block) {
			certain = TRUE;
			break;
		}
	ENDFORTUP(ft1);
	out_depth = i - 1;

	/* Exception handlers are blocks for syntactic purposes, but not at
	 * run-time. They must be excluded from this count.
	 * The same is true for loops.
	 */
	for (j = 1; j <= i; j++) {
		tsym = (Symbol) open_scopes[j];
		blktyp = (int)OVERLOADS(tsym);
		if (blktyp == BLOCK_HANDLER || blktyp == BLOCK_LOOP) out_depth -= 1;
	}
	if ((nat == na_function || nat == na_procedure 
	  || nat == na_generic_function || nat == na_generic_procedure
	  || nat == na_entry || nat == na_entry_family)) {
		;
	}
	else {
		errmsg("invalid context for RETURN statement", "5.8", node);
		return;
	}
	r_type = nat == na_entry_family ? symbol_none : TYPE_OF(proc_name);
	if (exp_node != OPT_NODE) {
		if (r_type == symbol_none) {
			errmsg("Procedure cannot return value", "5.8", exp_node);
		}
		else {
			/* If the value returned is an aggregate, there is no sliding
			 * for it, and named associations can appear together with 
			 * "others" (see 4.3.2(6)).
			 */
			full_others = TRUE;
			adasem(exp_node);
			check_type(r_type, exp_node);
			full_others = FALSE;
		}
	}
	else if (r_type != symbol_none) {
		errmsg("Function must return value", "5.8", node);
	}

	proc_node = node_new(as_simple_name);
	N_UNQ(proc_node) = proc_name;
	N_AST1(node) =	exp_node;
	N_AST2(node) = proc_node;
	N_AST3(node) = new_number_node(out_depth);
	N_AST4(node) = (Node) 0;
}

void label_decl(Node node)  						/*;label_decl*/
{
	Symbol label;
	Fortup	ft1;
	char	*id;
	Tuple tlabs;
	Node	id_node;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  label_decl");

	FORTUP(id_node = (Node), N_LIST(node), ft1);
		id = N_VAL(id_node);
		label = find_new(id);
		N_UNQ(id_node) = label;
		if (NATURE(label) == na_void
		  && !tup_mem((char *) label , (Tuple) lab_seen[tup_size(lab_seen)])) {
			NATURE(label) = na_label;
			label_status(label) = (int) label_unreachable;

			/* top(lab_seen) with:= label; */
			tlabs = (Tuple) lab_seen[tup_size(lab_seen)];
			tlabs = tup_with(tlabs, (char *) label);
			lab_seen[tup_size(lab_seen)] = (char *) tlabs;
		}
		else {
			errmsg("Duplicate identifier for label", "5.1", id_node);
		}
	ENDFORTUP(ft1);
}

void lab_init()											/*;lab_init*/
{
	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  lab_init ");

	lab_seen = tup_with(lab_seen, (char *) tup_new(0));
}

void lab_end()										  /*;lab_end*/
{
	char	*old_labels;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  lab_end ");
	/* The value of old_labels is irrelevant, as we are just removing
	 * last element from lab_seen
	 */
	old_labels = tup_frome(lab_seen);
}

void goto_statement(Node node)						   /*;goto_statement*/
{
	Node	id_node, id;
	Symbol	label, s;
	Fortup	ft1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  goto_statement");

	id_node = N_AST1(node);
	id = (Node) N_VAL(id_node); /*?? id is never used */

	find_old(id_node);
	label = N_UNQ(id_node);

	if (NATURE(label) != na_label) {
		errmsg("target of goto is not a label", "5.9", id_node);

	}
	else if ((int)label_status(label) == label_unreachable) {
		errmsg("target of goto is not a reachable label", "5.9", id_node);
	}
	else {
		FORTUP(s = (Symbol), open_scopes, ft1);
			if (s == SCOPE_OF(label)) break;
			else if (NATURE(s) != na_block) {
				errmsg_nat("attempt to jump out of %", s, "5.9", node);
			}

		ENDFORTUP(ft1);
	}
}
