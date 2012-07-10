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
#include "evalprots.h"
#include "errmsgprots.h"
#include "dclmapprots.h"
#include "sspansprots.h"
#include "nodesprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "utilprots.h"
#include "chapprots.h"

static int constraint_kind(Symbol);
static void make_constrained_node(Node, Symbol, int);
static void dereference_node(Node, Symbol);
static Symbol resolve2_attr(Node, Symbol);
static int in_univ_attributes(int);
static void check_bounds_in_range(Node, Node, Symbol);
static void check_array_conversion(Node, Symbol, Symbol);
static int reads_prefix(int, Symbol);

int in_type_classes(Symbol sym)							 /*;in_type_classes*/
{
	/* return true if sym in type_classes, as defined in check_type*/
	/* New procedure aqdded for c version */
	return (
	     sym == symbol_boolean_type 
	  || sym == symbol_discrete_type   
	  || sym == symbol_integer_type
	  || sym == symbol_real_type
	  || sym == symbol_universal_type);
}

void check_type_i(Node expn)								 /*;check_type_i*/
{
	/* check_type('integer_type', expn) */
	check_type(symbol_integer_type, expn);
}

void check_type_r(Node expn)								 /*;check_type_r*/
{
	/* check_type('real_type', expn) */
	check_type(symbol_real_type, expn);
}

void check_type_d(Node expn)								 /*;check_type_d*/
{
	/* check_type('discrete_type', expn) */
	check_type(symbol_discrete_type, expn);
}

void check_type_u(Node expn)								/*;check_type_u*/
{
	/* check_type('universal_type', expn) */
	check_type(symbol_universal_type, expn);
}

void check_type(Symbol context_type, Node expn)				/*;check_type*/
{
	/* This procedure performs type checking and operator disambiguation.
	 * -expn- is an expression tree, which must have the type -context_type-.
	 * This procedure is called in all contexts where the type of
	 * an expression is known a priori : assignments, conditionals, etc.
	 * The procedure returns the annotated tree for -expn-, labelling each
	 * node with its unique type, and resolving overloaded constructs where
	 * needed.
	 * Some contexts require that a type belong to a class of types instead
	 * of one  specific type. For example, a condition must be of a boolean
	 * type, not just BOOLEAN.
	 */

	Set types, otypes;
	Symbol t, old_context;
	Forset	fs1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  check_type");

	N_TYPE(expn) = symbol_any;		/*By default.*/
	noop_error = FALSE;

	resolve1(expn);		/* Bottom-up pass.*/

	if (noop_error) {
		noop_error = FALSE;	/* error emitted already*/
		N_TYPE(expn) = symbol_any;
		return;
	}

	types = N_PTYPES(expn);
	old_context = context_type;
	if (in_type_classes(context_type)) {
		/* Keep only those that belong to this class.*/
		otypes = set_copy(types);
		types = set_new(0);
		FORSET(t = (Symbol), otypes, fs1);
			if (compatible_types(t, context_type))
				types = set_with(types, (char *) t);
		ENDFORSET(fs1);
		set_free(otypes);

		if (set_size(types) > 1) {
			/* May be overloaded operator: user_defined one hides predefined.*/
			/* types -:= univ_types */
			otypes = set_copy(types); 
			types = set_new(0);
			FORSET(t = (Symbol), otypes, fs1);
				if (t != symbol_universal_integer && t!= symbol_universal_real)
					types = set_with(types, (char *)t);
			ENDFORSET(fs1);
			set_free(otypes);
		}

		if (set_size(types) == 1) {
			context_type = (Symbol) set_arb (types);
			set_free(types);
		}
		else {
			type_error(set_new1((char *) symbol_any), context_type, 
			  set_size(types), expn);
			N_TYPE(expn) = symbol_any;
			set_free(types);
			return;
		}
	}

	resolve2(expn, context_type);

	if (noop_error) {
		noop_error = FALSE;	/* error emitted already*/
		return;
	}

	/* Now emit a constraint qualification if needed.*/
	if (! in_type_classes(old_context)) apply_constraint(expn, context_type);
	if (! in_univ_types(context_type)) eval_static(expn);
}

static int constraint_kind(Symbol typ)					 /*;constraint_kind*/
{
	Symbol	d;

	if (cdebug2 > 3) {
		TO_ERRFILE("AT PROC :  constraint_kind");
	}
	/* Note that the use of '' in SETL version is translated to zero in
	 * the c version. This use of '' is common only to this routine and
	 * the next following one.
	 */
	if (is_unconstrained(typ) || in_univ_types(typ))  return as_opt;
	if (is_scalar_type(typ)) {
		if (NATURE(typ) == na_enum) return as_opt;
		else return as_qual_range;
	}
	if (is_array(typ))  {
		if (full_others || NATURE(scope_name) == na_record)
			return as_qual_index;
		else return as_opt;
	}
	if (is_record(typ)) {
		if (has_discriminants(typ)) return  as_qual_discr;
		else return as_opt;
	}
	if (is_access(typ)) {
		d = (Symbol) designated_type(typ);
		if (is_scalar_type(d)) return as_opt;
		else if (is_unconstrained(d)) return as_opt;
		else if (is_array(d)) {
			return as_qual_aindex;
		}
		else if (is_record(d)) {
			if (has_discriminants(d)) return as_qual_adiscr;
			else return as_opt;
		}
	}
	return as_opt;
}

void apply_constraint(Node expn, Symbol typ)		  /*;apply_constraint*/
{
	int	k, constraint;

	if (cdebug2 > 3) {
		TO_ERRFILE("AT PROC :  apply constraint");
	}

	constraint = constraint_kind(typ);
	/* test of constraint != 0 corresponds to encoding assigned in previous
	 * procedure
	 */
	k = N_KIND(expn);

	/* If node is insert node, lone descendant is original expression.*/
	if (k == as_insert)  apply_constraint(N_AST1(expn), typ);

	if (k == as_subtype || k == as_parenthesis || constraint == as_opt)
		return;
	/* the two cases have to be distinguished : a'first..a'last and a'b 
	 * in an aggregate, where a qual_range doesn't make any sens.
	 */
	if (k == as_attribute
	  && ((int) attribute_kind(expn) == ATTR_T_RANGE
	  ||  (int) attribute_kind(expn) == ATTR_O_RANGE)
	  && constraint == as_qual_range)
		return;

	if (k == as_ivalue || (N_TYPE(expn) != typ)
	  || (k == as_array_aggregate)
	  || (k == as_new && N_AST2(expn) == OPT_NODE)) {

		/* The two following lines were in the Setl version : We don't have
		 * to keep them since qual_a* is tranformed in qual_* in the code
		 * generator
		 * if (is_access (typ)) {type_const = (Symbol) designated_type (typ); }
		 *    else { type_const = typ; }
		 */
		make_constrained_node(expn, typ, constraint);
	}
}

static void make_constrained_node(Node expn, Symbol typ, int constraint)
													/*;make_constrained_node*/
{
	Node e_node;

	e_node = copy_node(expn);
	N_KIND(expn) = constraint;
	N_AST1(expn) = e_node;
	if (N_AST2_DEFINED(constraint)) N_AST2(expn) = (Node)0;
	if (N_AST3_DEFINED(constraint)) N_AST3(expn) = (Node)0;
	if (N_AST4_DEFINED(constraint)) N_AST4(expn) = (Node)0;
	N_TYPE(expn) = typ;
}

int in_priv_types(Symbol s)									/*;in_priv_types*/
{
	return (s == symbol_private || s == symbol_limited_private);
}

void resolve1(Node expn)										/*;resolve1*/
{
	/* This procedure performs the first, bottom-up pass of the type checking
	 * and	overload resolution. It	 annotates the	expression tree	 with the
	 * attribute N_PTYPES(expn),  corresponding to the possible  types of the
	 * expression.
	 */

	Fortup ft1;
	Forset fs1, fs2;
	unsigned int    op_name;
	int	    exists, i, j, k, tmp1, nat;
	Symbol name, target_type;
	Set names, op_types, array_types;
	Tuple tmp;
	Set tset;
	Node arg, aggregate_node;
	Tuple arg_list;
	Symbol n_t;
	Node lit_name;
	Symbol n;
	Node op_node, args_node;
	Set possible_types;
	Node arg2;
	Symbol nam;
	Node constraint;
	Set ts;
	Symbol t;
	Node ac_expn, type_id;
	Symbol type_mark;
	Symbol desig_type;
	Node c_expr, arg1;
	Node t_node;
	Node e;
	Symbol to_type;
	Set types;
	Node type_node;
	Node low;
	Node high;
	Set t_low, t_high;
	Symbol t1, t2, it, typ;
	Node call_node, index_node;
	Span save_span;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : resolve1 ");

	/*if (noop_error ? false) then return; end if; */
	/* TODO: check why noop_error assumed possible non_boolean in above */
	if (noop_error) {
		N_PTYPES(expn) = set_new1((char *) symbol_any);
		return;
	}

	op_name = N_KIND(expn);

	if (cdebug2 > 3) {
#ifdef IBM_PC
		printf(" resolve1 %p %s\n", expn, kind_str(op_name));
#else
		printf(" resolve1 %ld %s\n", expn, kind_str(op_name));
#endif
	}

	switch (op_name) {
	case as_simple_name:
		name = N_OVERLOADED(expn) ? (Symbol) 0 : N_UNQ(expn);
		if (name != (Symbol)0) {

			n_t = TYPE_OF(name);
			nat = NATURE(name);
			if ( nat == na_obj
			  || nat == na_constant
			  || nat == na_in
			  || nat == na_inout
			  || nat == na_out
			  || nat == na_task_obj
			  || nat == na_task_obj_spec
			  || nat == na_task_type
			  || nat == na_task_type_spec) {
				N_PTYPES(expn) = set_new1((char *) n_t);
			}
			else if (nat == na_type || nat == na_subtype
			  || nat == na_enum || nat == na_record
			  || nat == na_array || nat == na_access) {
				N_PTYPES(expn) = set_new1((char *) symbol_any);
				pass1_error_id("Invalid use of type %", name, "4.4", expn);
			}
			else if (nat == na_discriminant) {
				/* A discriminant reference can only appear within a  */
				/* record definition. The rec.type in noted on the node. */
				save_span = get_left_span(expn);
				N_KIND(expn) = as_discr_ref;
				N_AST1(expn) = new_name_node(SCOPE_OF(name));
				N_AST2(expn) = N_AST4(expn) = (Node) 0;
				set_span(N_AST1(expn), save_span);
				N_PTYPES(expn) = set_new1((char *) n_t);
			}

			else if (nat == na_void) {
				N_PTYPES(expn) = set_new1((char *)symbol_any);
				pass1_error_id("premature use of %", name, "8.3", expn);
				return;
			}
			else {
				N_PTYPES(expn) = set_new1((char *) symbol_any);
				pass1_error_id("Invalid use of identifier %", name, 
				  "4.4", expn);
			}
		}
		else {
			/* The simple name is overloaded: case of a literal or para-*/
			/* meterless function. Reformat with null param. list.*/
			lit_name = copy_node(expn);
			args_node = node_new(as_list);
			N_LIST(args_node) = tup_new(0);
			N_KIND(expn) = as_call;
			N_AST1(expn) = lit_name;
			N_AST2(expn) = args_node;
			resolve1(expn);
		}
		break;
	case as_character_literal:
		N_PTYPES(expn) = set_new(set_size(N_NAMES(expn)));
		FORSET(n = (Symbol), N_NAMES(expn), fs1);
			N_PTYPES(expn) = set_with(N_PTYPES(expn), (char *) TYPE_OF(n));
		ENDFORSET(fs1);
		break;
	case as_op:
	case as_un_op:
	case as_call:
		/* Overloaded constructs. */

		op_node = N_AST1(expn);
		args_node = N_AST2(expn);

		FORTUP(arg = (Node), N_LIST(args_node), ft1);
			resolve1(arg);
			check_range_attribute(arg);   /* a no-no */
		ENDFORTUP(ft1);
		names = N_NAMES(op_node);
		result_types(expn);
		if (noop_error);	/* Previous error. */
		else if (set_size(N_PTYPES(expn)) == 0)
			type_error(names, (Symbol) 0, 0, expn);

		/* All other cases are basic operations on arrays, record, aggregates */
		/* attributes, subtypes, conversions and qualifications. */
		break;
	case as_name:
		find_old(expn);
		resolve1(expn);
		break;
	case as_int_literal:
		N_PTYPES(expn) = set_new1((char *)symbol_universal_integer);
		break;
	case as_real_literal:
		N_PTYPES(expn) = set_new1((char *) symbol_universal_real);
		break;
	case as_string_literal:
		N_PTYPES(expn) = set_new1((char *) symbol_string_type);
		break;
	case as_null:
		N_PTYPES(expn) = find_access_types();
		break;
	case as_aggregate:
		/* Verify that the list	of choices  is properly formatted, and
		 * collect  all possible aggregate  types. The types of the in-
		 * dividual choices are not used to resolve the aggregate type.
		 */
		arg_list = N_LIST(expn);
		exists = FALSE;
		FORTUPI(arg = (Node), arg_list, i, ft1);
			if (N_KIND(arg) == as_choice_list) {
				exists = TRUE;
				break;
			}
		ENDFORTUP(ft1);
		if (exists) {
			exists = FALSE;
			for (j = i + 1; j <= tup_size(arg_list); j++) {
				arg2 = (Node) arg_list[j];
				if (N_KIND(arg2) != as_choice_list) {
					exists = TRUE;
					break;
				}
			}
		}
		/*	if (exists arg = arg_list(i) | N_KIND(arg) = as_choice_list)
		 *    and(exists arg2 in arg_list(i+1..) |
		 *     N_KIND(arg2) /= as_choice_list)
		 */
		if (exists) {
			Tuple t, t1;
			pass1_error(
			  "positional associations must appear first in aggregate", "4.3",
			  arg2);
			t = tup_new(i);
			/* N_LIST(expn) = N_LIST(expn)(1..i); */
			t1 = N_LIST(expn);
			for (j = 1; j <= i; j++)
				t[i] = t1[i];
			N_LIST(expn) = t;
		}
		/* collect all possible aggregate types. */
		N_PTYPES(expn) = find_agg_types();
		break;
	case as_index:
		possible_types = set_new(0);
		{
			Symbol t;
			FORSET(t = (Symbol), valid_array_expn(expn), fs1);
				possible_types = set_with(possible_types, 
				  (char *) component_type(t));
			ENDFORSET(fs1);
		}
		if (set_size(possible_types) == 0)
			pass1_error("type mismatch in indexing", "4.1.1", expn);
		N_PTYPES(expn) = possible_types;
		break;
	case as_slice:
		/* Slicing operations are equivalent to indexing operations,
		 * for type checking purposes. We simply reformat the result
		 * of type checking, so that the result type of the slice is
		 * the base type of the array expression. If this type is an
		 * access type, we must of course dereference it.
		 */
		possible_types = valid_array_expn(expn);

		if (set_size(possible_types) == 0)
			pass1_error("type mismatch in slice", "4.1.2", expn);

		/* N_PTYPES(expn) := {base_type(t)  : t in possible_types}; */
		tset = set_new(0);
		{
			Symbol t;
			FORSET(t = (Symbol), possible_types, fs1);
				tset = set_with(tset, (char *) t);
			ENDFORSET(fs1);
		}
		set_free(possible_types);
		N_PTYPES(expn) = tset;
		break;
	case as_selector:
		valid_selected_expn(expn);
		break;
	case as_in:
	case as_notin:
		/* The second argument of membership operators is a type_mark or */
		/* a range. */
		op_node = N_AST1(expn);
		args_node = N_AST2(expn);
		tmp = N_LIST(args_node);
		arg1 = (Node) tmp[1];
		arg2 = (Node) tmp[2];

		resolve1(arg1);
		if (N_KIND(arg2) == as_range_expression) {
			find_old(arg2);
			k = N_KIND(arg2);
			if (k != as_simple_name && k != as_attribute) {
				pass1_error("invalid argument for membership operator",
				  "4.4", arg2);
				return;
			}
			nam = N_UNQ(arg2);
			t = base_type(nam);
			if (in_priv_types(t)) t = nam;
			N_PTYPES(arg2) = set_new1((char *) t);
			/* Missing: range attribute. */
		}
		else {
			if (N_KIND(arg2) != as_attribute) {
				/* Argument is a range: reformat as subtype of some type. */
				constraint = copy_node(arg2);
				N_KIND(arg2) = as_subtype;
				N_AST1(arg2) = OPT_NODE;
				N_AST2(arg2) = constraint;
			}
			resolve1(arg2);

			/* ts := {t in N_PTYPES(arg2) | is_scalar_type(t)}; */
			ts = set_new(0);
			{
				Symbol t;
				FORSET(t = (Symbol), N_PTYPES(arg2), fs1);
					if (is_scalar_type(t))
						ts = set_with(ts, (char *) t);
				ENDFORSET(fs1);
			}
			if (set_size(ts) == 0) {
				errmsg("bounds of range for membership op must be scalar",
				  "4.4", arg2);
			}
			else N_PTYPES(arg2) = ts;
		}
		/* Now resolve the expression as for any other operator. */

		{
			Set  op_name_set;
			N_KIND(expn) = as_op;
			op_name_set = op_name == as_in ? set_new1((char *)symbol_in)
			  : set_new1((char *)symbol_notin);
			N_NAMES(op_node) = op_name_set;
			result_types(expn);
			if (noop_error);
			else if (set_size(N_PTYPES(expn)) == 0)
				type_error(op_name_set, (Symbol)0, 0, expn);
		}
		break;
	case as_all:
		/* dereference operations must apply  to objects	 of access type.
		 * The type yielded is obtained by dereferencing the type descrip
		 * tor of the access object.
		 */
		ac_expn = N_AST1(expn);

		resolve1(ac_expn);
		/* ??possible_types := {designated_type(t): t in N_PTYPES(ac_expn)
		 *      | is_access(t)};
		 */
		possible_types = set_new(0);
		{
			Symbol t;
			FORSET(t = (Symbol), N_PTYPES(ac_expn), fs1);
				if (is_access(t))
					possible_types = set_with(possible_types,
				      (char *) designated_type(t));
			ENDFORSET(fs1);
		}
		if (set_size(possible_types) == 0) {
			pass1_error("Expect access type for dereference",
			  "3.8", ac_expn);
		}
		N_PTYPES(expn) = possible_types;
		break;
	case as_new:
		/* the elaboration of the subtypes may produce additional
		 * anonymous types. These are emitted later on (see resolve2)
		 * and here are just collected and discarded.
		 */
		newtypes = tup_with(newtypes, (char *)tup_new(0));
		desig_type = make_subtype(expn);
		{
			Tuple junk = (Tuple)tup_frome(newtypes);
			tup_free(junk);
		}
		type_id = N_AST1(expn);
		constraint = N_AST2(expn);

		type_mark = N_UNQ(type_id);
		if ((constraint == OPT_NODE) &&(is_unconstrained(type_mark))) {
			pass1_error_l("Constraint required in allocator when",
			  "initialization is absent", "4.8", expn);
			return;
		}
		else  /* use name of generated subtype to label allocator */
			N_UNQ(type_id) = desig_type;

		check_fully_declared(desig_type);

		/* Rebuild node as having a designated type and no aggregate. */
		if (constraint != OPT_NODE) {
			type_node = copy_node(expn);
			N_UNQ(type_node) = desig_type;
			N_KIND(type_node) = as_subtype_decl;
		}
		else type_node = type_id;
		N_AST1(expn) = type_node;
		N_AST2(expn) = OPT_NODE;

		/* N_PTYPES(expn) := {a in find_access_types() |
		 *    compatible_types(desig_type, designated_type(a))};
		 */
		{
			Set s;
			Symbol a;
			s = set_new(0);
			FORSET(a = (Symbol), find_access_types(), fs1);
				if (compatible_types(desig_type, designated_type(a)))
					s = set_with(s, (char *) a);
			ENDFORSET(fs1);
			N_PTYPES(expn) = s;
		}
		break;
	case as_new_init:
		/* Allocator given by a type mark and an explicit aggregate. */

		type_id = N_AST1(expn);
		aggregate_node = N_AST2(expn);
		find_type(type_id);
		desig_type = N_UNQ(type_id);
		if (!is_type(desig_type)) {
			pass1_error("invalid type mark in allocator", "4.8", type_id);
			return;
		}
		else
			if (is_limited_type(desig_type)) {
				pass1_error_l("initial value not allowed on an ",
				  "allocator for a limited type", "7.4.4", type_id);
				return;
			}
		if (N_KIND(aggregate_node) == as_parenthesis) {
			/*Remove parenthesis which is an artifact of parsing.*/
			aggregate_node = N_AST1(aggregate_node);
			N_AST2(expn) = aggregate_node;
		}
		resolve1(aggregate_node);
		/* ??N_PTYPES(expn) = {a in find_access_types() |
		 *     compatible_types(desig_type, designated_type(a))}; $$ES151
		 */
		{
			Symbol a;
			Set s;
			s = set_new(0);
			FORSET(a = (Symbol), find_access_types(), fs1);
				if (compatible_types(desig_type, designated_type(a)))
					s = set_with(s, (char *) a);
			ENDFORSET(fs1);
			N_PTYPES(expn) = s;
		}
		N_KIND(expn) = as_new; /* for common processing. */
		break;
	case as_choice_list:
		/* This is used only for the arguments to calls and not for */
		/* aggregates which are handled in complete_r_aggregate. */

		c_expr = N_AST2(expn);
		resolve1(c_expr);
#ifdef TBSL
		-- is copy of N_TYPES needed below	ds 8-jan-85
#endif
	    N_PTYPES(expn) = N_PTYPES(c_expr);
		break;
	case as_attribute:
		resolv_attr(expn);
		break;
	case as_qual_range:
		/* When qual_range appears in an expression, the bounds have */
		/* been type-checked. Simple extract the known result type. */
		N_PTYPES(expn) = set_new1((char *) N_TYPE(expn));
		break;
	case as_convert:
		/* The result type is the type mark of the conversion. */

		t_node = N_AST1(expn);
		arg = N_AST2(expn);
		tmp1 = N_KIND(arg);
		target_type = N_UNQ(t_node);
		if (tmp1 == as_null || tmp1 == as_new || tmp1 == as_new_init
		  || tmp1 == as_aggregate || tmp1 == as_string_literal) {
			pass1_error("invalid expression for conversion", 
			  "4.6(3)", arg);
			return;
		}
		else if (is_incomplete_type(target_type)) {
			pass1_error("premature use of private type in expression",
			  "7.4.1(4)", t_node);
		}
		else {
			resolve1(arg);
			N_PTYPES(expn) = set_new1((char *)target_type);
		}
		break;
	case as_qualify:

		t_node = N_AST1(expn);
		arg = N_AST2(expn);
		to_type = N_UNQ(t_node);
		if (!is_type(to_type)) {
			pass1_error("Expect type mark in qualified expression", 
			  "4.7", t_node);
			return;
		}
		else if (in_open_scopes(to_type) && is_task_type(to_type)) {
			pass1_error_id("invalid use of type % within its own body",
			  to_type, "9.1", t_node);
			return;
		}
		else if (is_incomplete_type(to_type)) {
			pass1_error("premature use of private type in expression",
			  "7.4.1(4)", t_node);
			return;
		}
		else N_PTYPES(expn) = set_new1((char *) to_type);

		resolve1(arg);

		if (noop_error) return;
		else types = N_PTYPES(arg);

		exists = FALSE;
		{
			Symbol t;
			FORSET(t = (Symbol), types, fs1);
				if (compatible_types(to_type, t)) {
					exists = TRUE;
					break;
				}
			ENDFORSET(fs1);
		}
		if (!exists) {
			pass1_error("Expression has wrong type for qualification",
			  "4.7", arg);
		}
		break;
	case as_subtype:
		/* For a subtype expression, the bounds expressions  must  be
		 * checked against the specified type, if any, or against the
		 * type required by context.
		 */
		type_node = N_AST1(expn);
		constraint = N_AST2(expn);
		if (N_KIND(constraint) == as_attribute)
			t_low = t_high = N_PTYPES(constraint);
		else {
			low = N_AST1(constraint);
			high = N_AST2(constraint);
			resolve1(low);
			resolve1(high);
			t_low = N_PTYPES(low);
			t_high = N_PTYPES(high);
		}
		if (type_node == OPT_NODE) {
			/* Case of a range expression with no named type. Validate
			 * the bounds against each other, and return the possible types.
			 */
			possible_types = set_new(0);
			FORSET(t1 = (Symbol), t_low, fs1);
				FORSET(t2 = (Symbol), t_high, fs2);
					it = intersect_types(t1, t2);
					if (it != (Symbol)0) 
						possible_types = set_with(possible_types, (char *)it);
				ENDFORSET(fs2);
			ENDFORSET(fs1);
		}
		else {
			int exists1, exists2;
			/* Subtype of a specified type. Validate the bounds against */
			/* it. */
			typ = N_UNQ(type_node);
			possible_types = set_new1((char *) typ);
			/* if (not exists t1 in t_low |compatible_types(typ, t1))
			 *  or (not exists t2 in t_high|compatible_types(typ, t2)) then
			 */
			exists1 = exists2 = FALSE;
			FORSET(t1 = (Symbol), t_low, fs1);
				if (compatible_types(typ, t1)) {
					exists1 = TRUE;
					break;
				}
			ENDFORSET(fs1);
			if (exists1 == TRUE) {
				FORSET(t2 = (Symbol), t_high, fs1);
					if (compatible_types(typ, t2)) {
						exists2 = TRUE;
						break;
					}
				ENDFORSET(fs1);
			}
			if (!exists1 || !exists2) {
				pass1_error("Invalid types in bounds for range",
				  "3.5, 4.1.2", expn);
			}
		}
		N_PTYPES(expn) = possible_types;
		break;
	case as_parenthesis:
		/* A parenthesised  expression carries  a special operator, in
		 * order to distinguish it from a variable.(Thus(X) is not a
		 * valid OUT parameter for a procedure, and(D) is not a valid
		 * use of a discriminant name).
		 */
		e = N_AST1(expn);
		resolve1(e);
		N_PTYPES(expn) = N_PTYPES(e);
		break;
	case as_call_or_index:
		/* A call to a parameterless function that returns an array can
		 * overload a call  to a function  call with arguments. Resolve
		 * each of the trees independently.
		 */
		call_node = N_AST1(expn);
		index_node = N_AST2(expn);
		op_node = N_AST1(call_node);
		args_node = N_AST2(call_node);
		FORTUP(arg = (Node), N_LIST(args_node), ft1);
			resolve1(arg);
		ENDFORTUP(ft1);
		result_types(call_node);
		op_types = N_PTYPES(call_node);
#ifdef TBSN
		if (cdebug2 > 3) TO_ERRFILE('op_types ' + str op_types);
#endif
		array_types = set_new(0);
		FORSET(t = (Symbol), valid_array_expn(index_node), fs1);
			t = (Symbol)component_type(t);
			array_types = set_with(array_types, (char *)t);
		ENDFORSET(fs1);
		N_PTYPES(index_node) = array_types;
#ifdef TBSN
		if (cdebug2 > 3) TO_ERRFILE('array_types ' + str array_types);
#endif
		N_PTYPES(expn) = set_union(op_types, array_types);
		break;
	case as_range:	/* A frequent error. */
		pass1_error("Invalid use of discrete range  in expression",
		  "4.4", expn);
		N_PTYPES(expn) = set_new1((char *) symbol_any);
		break;
	default:
		/* TBSL: in SETL have op_name = om: use 0 for now */
		if (op_name == 0) {
			/* usually a previous error; often an invalid selected */
			/*  component name. */
			noop_error = TRUE;
		}
		else 
			pass1_error("Invalid operator in expression: ", "4.4, 4.5", expn);
		break;
	}
}

void resolv_attr(Node expn)								  /*;resolv_attr*/
{
	Fortup ft1;
	int	    exists, i, j, notexists, nat, attrkind;
	Symbol s1, s;
	Node entry_node;
	Symbol range_typ;
	Node arg2;
	Node  a_node, arg1;
	Symbol type1;
	Node task_node;
	Symbol task, entry_name;
	Set task_types;
	Node index_node;
	static int is_attribute_prefix = FALSE;

	a_node = N_AST1(expn);
	arg1 = N_AST2(expn);
	arg2 = N_AST3(expn);
	if (N_KIND(a_node) == as_simple_name)  /* no attribute if simple name here*/
		attrkind = ATTR_any;
	else
		attrkind = (int) attribute_kind(expn); /* numeric code for attribute */

	/* verify that BASE appears only as the prefix of another attribute */
	if (attrkind == ATTR_BASE && !is_attribute_prefix)
		errmsg("Invalid use of attribute BASE", "Annex A", expn);
	is_attribute_prefix = TRUE;

	/* First - for attributes applying to objects or types, change
	 * attrkind to reflect the type of entity to which the attribute
	 * is being applied.
	 */
	if ( attrkind == ATTR_FIRST || attrkind == ATTR_LAST
	  || attrkind == ATTR_RANGE || attrkind == ATTR_LENGTH
	  || attrkind == ATTR_SIZE || attrkind == ATTR_CONSTRAINED) 
			attrkind = (int)(attribute_kind(expn) +=(is_type_node(arg1) ? 2:1)); 

	/* We find the type of the left argument of the attribute. */
	/* It may be a type name, in which case there is nothing to be */
	/* done. */

	if (is_type_node(arg1)) {
		type1 = N_UNQ(arg1);
		if (is_incomplete_type(type1)) {
			premature_access(type1, arg1);
			N_PTYPES(expn) = set_new1((char *) symbol_any);
			return;
		}
		if (is_task_type(type1)
		  &&(attrkind != ATTR_BASE
		  && attrkind != ATTR_O_SIZE && attrkind != ATTR_T_SIZE
		  && attrkind != ATTR_STORAGE_SIZE)) {
			/* may refer to current task */
			if (in_open_scopes(type1))
				N_UNQ(arg1) = dcl_get(DECLARED(type1), "current_task");
			else
				/* use of the task type otherwise is invalid.*/
				pass1_error("invalid use of task type outside of it own body", 
				  "9.1", arg1);
		}
		N_PTYPES(arg1) = set_new1((char *) type1);
	}
	else if (attrkind == ATTR_COUNT) {
		find_entry_name(arg1);
		task_node = N_AST1(arg1);
		entry_node = N_AST2(arg1);
		task_types = N_PTYPES(task_node);

		if (entry_node == OPT_NODE || set_size(task_types) == 0) {
			/* previous error*/
			noop_error = TRUE; 
			return;
		}

		if (N_KIND(arg1) == as_entry_family_name) {
			entry_name = N_UNQ(entry_node);
			index_node = N_AST3(arg1);
			range_typ = (Symbol) index_type(TYPE_OF(entry_name));
			check_type(range_typ, index_node);
			N_KIND(arg1) = as_entry_name; /* for common processing */
		}
		else {   /* single entry, possibly overloaded */
			if (set_size(N_NAMES(arg1)) > 1) {
				errmsg("ambiguous entry name for attribute", "9.9", entry_node);
				return;
			}
			else {
				entry_name = (Symbol) set_arb(N_NAMES(arg1));
				N_UNQ(entry_node) = entry_name;
				N_AST3(arg1) = OPT_NODE; /* discard N_NAMES */
			}
		}
		complete_task_name(task_node, TYPE_OF(SCOPE_OF(entry_name)));
		task= N_UNQ(task_node);

		/* The COUNT attribute can only be used immediately within*/
		/* the object executing the task body. */
		exists = FALSE;
		if (N_KIND(task_node) != as_simple_name) exists = TRUE;
		if (!exists) {
			/* check that the task is one of the open scopes */
			notexists = TRUE;
			FORTUPI(s = (Symbol), open_scopes, i, ft1);
				s = (Symbol) open_scopes[i];
				if (task == s 
			      || strcmp(original_name(task), "current_task") == 0
			      && SCOPE_OF(task) == s) {
					notexists = FALSE;
					break;
				}
			ENDFORTUP(ft1);
			if (notexists) exists = TRUE; /* not in open scopes */
		}
		if (!exists) {
			/* intervening scopes cannot be subprograms, etc */
			for (j = 1; j <= i-1; j++) {
				s1 = (Symbol) open_scopes[j];
				nat = NATURE(s1);
				if (nat != na_block && nat != na_entry 
				  && nat != na_entry_family) {
					exists = TRUE;
					break;
				}
			}
		}
		if (exists) {
			pass1_error_l( "E\'COUNT can only be used within the body ",
			  "of the task containing E", "9.9", expn);
			return;
		}

		type1 = symbol_none;
		N_PTYPES(arg1) = set_new1((char *) symbol_none);
	}
	else {
		resolve1(arg1);
		if (set_size(N_PTYPES(arg1)) != 1) {
			pass1_error_str("Invalid argument for attribute %",
			  attribute_str(attrkind), "Annex A, 4.1.4", expn);
			return;
		}
		else
			type1 = (Symbol) set_arb(N_PTYPES(arg1));
	}

	is_attribute_prefix = FALSE;   /* clear flag */

	/* Verify that the type has received a full declaration. */
	if (is_incomplete_type(type1)) {
		/* 'SIZE and 'ADDRESS can be applied to a deffered constant,
		 * in the default expression for record components and non-
		 * generic formal parameters. The nature of the current scope
		 * is either na_record or na_void(formal part or discr. part).
		 */
		if (!is_type_node(arg1) &&
		  (attrkind == ATTR_O_SIZE || attrkind == ATTR_T_SIZE
		  || attrkind == ATTR_ADDRESS) &&(NATURE(scope_name) == na_void
		  || NATURE(scope_name) == na_record)) {
			;
		}
		else {
			premature_access(type1, arg1);
			N_PTYPES(expn) = set_new1((char *) symbol_any);
			return;
		}
	}
	/* Verify that attributes have the proper number of arguments. */

	if (is_scalar_type(type1) &&
	  (  attrkind == ATTR_O_FIRST || attrkind == ATTR_T_FIRST
	  || attrkind == ATTR_O_LAST || attrkind == ATTR_T_LAST)) {
		if (arg2 != OPT_NODE) {
			pass1_error_str("Invalid second argument for attribute %",
			  attribute_str(attrkind), "Annex A, 4.1.4", arg2);
		}
		else if ((N_KIND(arg1) == as_simple_name &&(!is_type(N_UNQ(arg1))))
		  || (N_KIND(arg1) == as_attribute
		  && (int) attribute_kind(arg1) != ATTR_BASE)) {
			pass1_error("attribute cannot be applied to scalar object",
			  "Annex A", a_node);
		}
	}
    else if (attrkind == ATTR_LARGE
     || attrkind == ATTR_SMALL) {
		if ((N_KIND(arg1) == as_simple_name &&(!is_type(N_UNQ(arg1)))))
			pass1_error("attribute must be applied to a type",
			            "Annex A", a_node);
    }
	else if (attrkind == ATTR_POS 
	  || attrkind == ATTR_VAL 
	  || attrkind == ATTR_PRED 
	  || attrkind == ATTR_SUCC 
	  || attrkind == ATTR_VALUE 
	  || attrkind == ATTR_IMAGE) {
		if (arg2 == OPT_NODE) {
			pass1_error("Missing second argument for attribute ",
			  "Annex A", a_node);
			return;
		}
		else
			if (!is_type_node(arg1) || (N_KIND(arg1) == as_attribute
			  && (int) attribute_kind(arg1) == ATTR_BASE)) {
				pass1_error_l("First argument of attribute must ",
				  "be a type mark", "Annex A", a_node);
				return;
			}
	}

	/* In the case of array attributes, the argument may be an access */
	/*    object. Dereference it now. */
	if ((attrkind == ATTR_O_FIRST || attrkind == ATTR_T_FIRST 
	  || attrkind == ATTR_O_LAST || attrkind == ATTR_T_LAST 
	  || attrkind == ATTR_O_RANGE || attrkind == ATTR_T_RANGE 
	  || attrkind == ATTR_O_LENGTH || attrkind == ATTR_T_LENGTH)
	  && is_access(type1)
	  && is_array((Symbol)(designated_type(type1)))) {
		if (is_fully_private(type1)) {
			premature_access(type1, arg1);
			N_PTYPES(expn) = set_new1((char *)symbol_any);
			return;
		}
		dereference_node(arg1, type1);
		type1 = (Symbol) designated_type(type1);
	}
	else if ((attrkind == ATTR_CALLABLE || attrkind == ATTR_TERMINATED)
	  && is_access(type1)) {
		dereference_node(arg1, type1);
		type1 = (Symbol) designated_type(type1);
	}

	if (arg2 == OPT_NODE) {
		/* For array attributes, a missing second argument is */
		/* equivalent to a reference to the first dimension. */
		arg2 = node_new(as_int_literal);
		set_span(arg2, get_right_span(N_AST2(expn)));
		N_VAL(arg2) = strjoin("1", "");
		N_AST3(expn) = arg2;
	}

	/* The  procedure  attribute-type  will  resolve  fully arg2 */
	/* in the case of array attributes, to obtain a dimension no. */

	N_PTYPES(expn) =
	  set_new1((char *)attribute_type(attrkind, type1, arg1, arg2));
}

/* Made case as_attribute in resolve2 into separate procedure 
 * resolve2_attr.  Having resolve2_attr return (Symbol)0 in case of pass1_error.
 */

static void dereference_node(Node arg1, Symbol type1)	/*;dereference_node*/
{
	/* the prefix of several attributes must be appropriate for the type,
	 * i.e.  it can be an access to an entity  of the proper kind. This
	 * routine is called to emit an explicit dereference (.all) in such cases.
	 */

	Node acc_arg1;

	if (is_type_node(arg1)) {
		;	/* no op */
	}
	else {	/* Dereference object */
		acc_arg1 = copy_node(arg1);
		N_AST2(arg1) = (Node)0;
		N_AST3(arg1) = (Node)0;
		N_AST4(arg1) = (Node)0;
		N_PTYPES(acc_arg1) = set_new1((char *)type1);
		N_KIND(arg1) = as_all;
		N_AST1(arg1) = acc_arg1;
	}
	N_PTYPES(arg1) = set_new1((char *)designated_type(type1));
}

void resolve2(Node expn, Symbol context_typ)				  /*;resolve2*/
{
	/* This procedure performs the second, top-down pass of the
	 * type validation and overloading resolution.
	 * second argument is the type which the expression must yield.
	 * If the expression is overloaded, only one of its instances must
	 * yield  -context_typ-. Once this is ascertained, the known types of the
	 *formals for the top level operator in expression, are propagated
	 * downwards to the actuals.
	 */

	Fortup ft1;
	Forset fs1;
	int	    exists, nat, nk;
	Set types, a_types, ntypes;
	Set oa_types = (Set) 0;
	Symbol name, type2, c, rtype, target_type, ntype_sym;
	Node op_node, args_node, node;
	Set valid_ops;
	Symbol op_name, atysym, t2;
	Set op_names;
	Tuple tup, indices;
	Symbol target_typ;
	Node array1;
	Symbol array_type;
	int	    out_c;
	Tuple	index_list;
	Node index;
	int	    i, may_others;
	Node discr1, e, ac_expn;
	Symbol access_type;
	Node type_node, expn1, entry_node;
	Symbol alloc_type;
	Symbol accessed_type;
	/*char   *chk;*/
	char	*strvstr;
	Tuple	strvtup;
	int		strvlen, strvi;
	Symbol t;
	Symbol c1, c2;
	Set tu;
	Node t_node, constraint, low, high;
	Symbol b_type;
	int	    kind;
	Node call_node, index_node;
	Const	lv; /*TBSL: check type of lv */
	char	*orignam;
	Tuple	litmaptup;
	int		litmapi;
	Span	save_span;

	if (cdebug2 > 0) {
		TO_ERRFILE("resolve2 ");
#ifdef IBM_PC
		printf(" %p %s context %p %s\n"
		  , expn, kind_str(N_KIND(expn)), context_typ,
		  ((context_typ != (Symbol)0)? ORIG_NAME(context_typ):""));
#else
		printf(" %ld %s context %ld %s\n"
		  , expn, kind_str(N_KIND(expn)), context_typ,
		  ((context_typ != (Symbol)0)? ORIG_NAME(context_typ):""));
#endif
	}
	if (context_typ == (Symbol)0)
		printf("??:resolve2 context_typ null\n");
	if (noop_error) return;

	types = N_PTYPES(expn);

	if (expn == OPT_NODE) return;

	switch (nk = N_KIND(expn)) {
	case as_simple_name:
		name = N_UNQ(expn);
		/* If constant, get its value, and if universal constant,
		 * convert when necessary.
		 */
		type2 = TYPE_OF(name);
		if (!compatible_types(context_typ, type2)) {
			errmsg_id_type("% has incorrect type. Expect %", name, context_typ,
			  "none", expn);
			noop_error = TRUE;
			return;
		}
		else
			if ((NATURE(name) == na_out) &&(!out_context)) {
				errmsg_id("invalid reading of out parameter %", name, "6.2",
				  expn);
			}
		if (NATURE(name) == na_constant) {
			if (in_univ_types(type2)) {
				copy_attributes((Node) SIGNATURE(name), expn);
				specialize(expn, context_typ);
				type2 = base_type(context_typ);
			}
			else if ((Node) SIGNATURE(name) == OPT_NODE
			  && (NATURE(scope_name) != na_void 
			  && NATURE(scope_name) != na_record)) {
				/* Only permissible contexts for a defered constant are
				 * formal parts and component declarations.
				 */
				errmsg_l("premature use of deferred constant before its",
				  "full declaration", "7.4.3", expn);
			}
		}
		else eval_static(expn);
		break;
	case as_character_literal:
		exists = FALSE;
		FORSET(c = (Symbol), N_NAMES(expn), fs1);
			if (compatible_types(context_typ, TYPE_OF(c))) {
				exists = TRUE;
				break;
			}
		ENDFORSET(fs1);
		if (exists) {
			type2 = TYPE_OF(c);
			/*N_VAL(expn) = literal_map(type2)(original_name(c));*/
			/* In the C version, create a Const with this value */
			orignam = ORIG_NAME(c);
			if (orignam == (char *)0) chaos("resolve2 null literal");
			litmaptup = (Tuple) literal_map(type2);
			for (litmapi = 1; litmapi <= tup_size(litmaptup); litmapi += 2) {
				if (streq(orignam, litmaptup[litmapi])) {
					N_VAL(expn) = (char *) int_const((int)litmaptup[litmapi+1]);
					break;
				}
			}
		}
		else {
			char *tmp_msg;

			tmp_msg = strjoin(N_VAL(expn), " has incorrect type. Expect %");
			errmsg_type(tmp_msg, context_typ, "none", expn);
			type2 = symbol_any;
			N_VAL(expn) = (char *) int_const(0);
		}
		N_KIND(expn) = as_ivalue;
		N_OVERLOADED(expn) = FALSE;
		N_PTYPES(expn) = (Set) 0;
		N_NAMES(expn) = (Set) 0;
		break;
	case as_op:
	case as_un_op:
	case as_call:
		op_node = N_AST1(expn);
		args_node = N_AST2(expn);
		op_names = N_NAMES(op_node);

		/* Find instance of operator that yields type imposed by context. */
		valid_ops = set_new(0);
		FORSET(name = (Symbol), op_names, fs1);
			if (compatible_types(context_typ, TYPE_OF(name)))
				valid_ops = set_with(valid_ops, (char *) name);
		ENDFORSET(fs1);

		N_NAMES(op_node) = valid_ops;

		if (set_size(valid_ops) > 1)
			disambiguate(expn, context_typ);

		if (set_size(N_NAMES(op_node)) > 1)
			/* try removing implicit conversions of universal quantities. */
			remove_conversions(expn);

		/* Now there should be only one possiblity left. */
		valid_ops = N_NAMES(op_node);
		if (set_size(valid_ops) != 1) {
			if (cdebug2 > 2) {
#ifdef TBSN
				??(for nam in valid_ops)
					TO_ERRFILE('OVERLOADS ', nam, SYMBTAB(nam));
				end for;
#endif
			}
			type_error(op_names, context_typ, set_size(valid_ops), op_node);
			return;
		}
		else {
			op_name = (Symbol) set_arb(valid_ops);
			type2   = TYPE_OF(op_name);
		}

		N_OVERLOADED(expn) = FALSE; /* DS -check this */
		N_NAMES(expn) = N_PTYPES(expn) = (Set)0;
		/* For a predefined operator, the type imposed by context fixes
		 * the types of the arguments. The signature of a predefined op.
		 * contains only classes of types, and it ignored in this pass.
		 * The resulting type must be that of the context.
		 */
		switch (nat = NATURE(op_name)) {
		case na_op:
			type2 = base_type(context_typ);
			N_UNQ(op_node) = op_name;
			complete_op_expr(expn, type2);
			/* The expression "+"(1, 2) is syntactically a function call. At
			 * this point it recognized as an operator node.
			 */
			if (N_KIND(expn) == as_call)
				N_KIND(expn) = (tup_size(N_LIST(args_node)) == 1) ? as_un_op
				  : as_op;

			/* For a procedure or function, the signature imposes a type on
			 * each actual parameter present, and specifies a default value
			 * for the ones that are absent. If the function is aliased(ie
			 * a renaming or derivation) the parent subprogram is called.
			 */
			break;
		case na_procedure:
		case na_procedure_spec:
		case na_function:
		case na_function_spec:
			complete_arg_list(SIGNATURE(op_name), args_node);
			N_KIND(expn) = as_call;
			N_UNQ(op_node) = op_name;
			TO_XREF(op_name);
			break;
		case na_entry:
		case na_entry_family:
			complete_arg_list(SIGNATURE(op_name), args_node);
			N_KIND(expn) = as_ecall;
			if (N_KIND(op_node) == as_entry_name
			  || N_KIND(op_node) == as_entry_family_name) {
				entry_node = N_AST2(op_node);
				/* Note  the unique name on the entry name node. */
				N_UNQ(entry_node) = op_name;
			}
			else {   /* called from proc_or_entry, no entry name yet */
				N_UNQ(op_node) = op_name;
			}
			TO_XREF(op_name);

			/* Resolved enumeration literals are returned as themselves. */
			break;
		case na_literal:
			save_span = get_left_span(expn);
			N_KIND(expn) = as_simple_name;
			N_UNQ(expn)  = op_name;
			set_span(expn, save_span);
			N_AST2(expn) = (Node)0; /* clear ast */
			N_VAL(expn)  = ORIG_NAME(op_name);
			TO_XREF(op_name);
			break;
		}
		/* Remaining cases are basic operations. */
		break;
	case as_int_literal:
		/* If the context  type is not universal, the literal must be trans-
		 * formed to its short SETL form.
		 */
		target_typ = ((context_typ == symbol_universal_integer)
		  ? symbol_universal_integer : symbol_integer);

		lv = adaval(target_typ, N_VAL(expn));
		if (adaval_overflow)
			create_raise(expn, symbol_numeric_error);
		else {
			ast_clear(expn);
			N_KIND(expn) = as_ivalue;
			N_VAL(expn) = (char *) lv;
		}
		type2 = base_type(context_typ); /* inherited from context */
		if (root_type(type2) != symbol_integer
		  && root_type(type2) != symbol_universal_integer) {
			errmsg("invalid context for integer literal", "4.6(15)", expn);
		}
		break;
	case as_real_literal:
		/* If the context is not universal, or is not a fixed type, then
		 * convert the literal to a floating number.
		 */
		target_typ = (context_typ == symbol_universal_real
		  || is_fixed_type(root_type(context_typ)))
		  ? symbol_universal_real: symbol_float;
		lv = adaval(target_typ, N_VAL(expn));
		if (adaval_overflow)
			create_raise(expn, symbol_constraint_error);
		else {
			ast_clear(expn);
			N_KIND(expn) = as_ivalue;
			N_VAL(expn) = (char *) lv;
		}
		type2 = base_type(context_typ); /* inherited from context */
		if (root_type(type2) != symbol_float 
		  && !is_fixed_type(root_type(type2))
		  && root_type(type2) != symbol_universal_real) {
			errmsg("invalid context for real literal", "4.6(15)", expn);
		}
		break;
	case as_string_literal:
		if (is_array(context_typ)) {
			if (context_typ == symbol_string_type) {
				/* verify that only one string type is visible. */
				context_typ = symbol_string;
			}
			else if (is_fully_private(context_typ))
				premature_access(context_typ, expn);

			if (root_type(context_typ) == symbol_string) {
				/*N_VAL(expn) := [abs c: c in N_VAL(expn)];*/
				strvstr = N_VAL(expn);
				strvlen = strlen(strvstr);
				strvtup = tup_new(strvlen);
				for (strvi = 1; strvi <= strvlen; strvi++)
					strvtup[strvi] = (char *) strvstr[strvi-1];
				ast_clear(expn);
				N_VAL(expn) = (char *) strvtup;
				N_KIND(expn) = as_string_ivalue;
				N_NAMES(expn) = (Set) 0;
			}
			else {
				/* Context is user-defined array of a character type. */
				complete_string_literal(expn, component_type(context_typ));
			}
		}
		else {
			errmsg_type("Incorrect type for string literal. Expect %",
			  context_typ, "none", expn);
		}
		type2 = context_typ;
		break;
	case as_null:
		if (is_access(context_typ)) type2 = context_typ;
		else {
			errmsg("Invalid context for NULL", "3.8.2", expn);
			return;
		}
		break;
	case as_aggregate:
		/* Resolve it using the  context type, and apply constraint if any.
		 * The possible types include all visible composite types, and there
		 * should be one of them compatible with the context.
		 */
		exists = FALSE;
		FORSET(t = (Symbol), types, fs1);
			if (compatible_types(t, context_typ)) {
				exists = TRUE;
				break;
			}
		ENDFORSET(fs1);
		if (!exists) {
			errmsg_id("No aggregate available for type %", context_typ, "4.2",
			  expn);
			return;
		}
		else complete_aggregate(context_typ, expn);

		type2 = context_typ;

		/* in the absence of more precise checks, the type of the
		 * aggregate can only be set to the base type (see end of resolve2
		 */
		context_typ = base_type (context_typ);

		/* For arrays, obtain required index type from type of array
		 * expression, and complete the determination of both.
		 */
		break;
	case as_index:
		array1 = N_AST1(expn);
		index_node = N_AST2(expn);

		array_type = complete_array_expn(expn, context_typ);

		/* Previous error*/
		if (array_type == symbol_any) return;
		/* Complete resolution of each index.
		 * The  index expression is	a context  in which  out parameters
		 * cannot  be  read. This  has to  be  special-cased	 because an
  		 * indexed  expression on  the lhs  of an assignment is a  valid
		 * context for an out parameter, and the global flag out_context
		 * is set accordingly in  processing assignments.
		 */
		out_c = out_context;
		out_context = FALSE;
		index_list = N_LIST(index_node);

		FORTUPI(index = (Node), index_list, i, ft1);
			resolve2(index, (Symbol) (index_types(array_type))[i]);
		ENDFORTUP(ft1);
		out_context = out_c;

		type2 = (Symbol) component_type(array_type);
		break;
	/* For slices, obtain array type, and apply its index type to the
	 * subtype expression for the discrete range.
	 */
	case as_slice:
		array1 = N_AST1(expn);
		index_node = N_AST2(expn);
		array_type = complete_array_expn(expn, context_typ);
		/* Previous error*/
		if (array_type == symbol_any)
			return;
		tup = N_LIST(index_node);
		discr1 = (Node) (tup[1]);
		resolve2(discr1, (Symbol) index_type(array_type));
		/*	Replace index list with its sole element. */
		N_AST2(expn) = discr1;
		N_AST3(expn) = N_AST4(expn) = (Node) 0;
		type2 = base_type(array_type);
		break;
	case as_selector:
		type2 = complete_selected_expn(expn, context_typ);

		/* For a parenthesised expression, resolve the expression, and keep
		 * the parenthesis, to distinguish them from variables. The possible
		 * constraint of the context is not propagated to the expression.
		 * If the context is universal, discard the parenthesis, to enable
		 * full evaluation of universal expressions.
		 */
		break;
	case as_parenthesis:
		e = N_AST1(expn);
		resolve2(e, base_type(context_typ));
		if (in_univ_types(context_typ))
			copy_attributes(e, expn);
		apply_constraint(e, context_typ);
		type2 = context_typ;
		break;
	/* For a dereference operation, we must verify that the access
	 * object points to the right type.
	 */
	case as_all:
		ac_expn = N_AST1(expn);
		{
			Symbol t;

			a_types = set_new(0);
			FORSET(t = (Symbol), N_PTYPES(ac_expn), fs1);
				if (is_access(t)
				  && compatible_types(context_typ, designated_type(t)))
					a_types = set_with(a_types, (char *) t);
			ENDFORSET(fs1);
		}
		/* TBSL: check that t is defined in type_error call dsd 18 aug */
		if (set_size(a_types) != 1) {
			remove_conversions(ac_expn);	/* last chance */
			oa_types = a_types;
			a_types = set_new(0);
			FORSET(atysym = (Symbol), N_PTYPES(ac_expn), fs1);
				if (set_mem((char *)atysym, oa_types))
					a_types = set_with(a_types, (char *) atysym);
			ENDFORSET(fs1);
			if (set_size(a_types) != 1) {
#ifdef TBSL
				]	    type_error(set_new1('@'), t, set_size(a_types), expn);
#endif
				set_free(oa_types); 
				set_free(a_types);
				return;
			}
		}
		access_type = (Symbol) set_arb(a_types);	/* Only one type left. */
		set_free(a_types);
		if (oa_types != (Set)0)
			set_free(oa_types);

		/* We know already that the nature of access type is na_access. */
		type2 = (Symbol) designated_type(access_type);
		/* It is always illegal to dereference an out parameter.*/
		out_c = out_context;
		out_context = FALSE;
		resolve2(ac_expn, access_type);
		out_context = out_c;
		break;
	/* For an allocator, we obtain the type of the access object
	 * by dereferencing the access type. The final expression however
	 * gives the access type, together with the validated access object.
	 */
	case as_new:
		type_node = N_AST1(expn);
		expn1 = N_AST2(expn);
		alloc_type = N_UNQ(type_node);

		if (!is_access(context_typ)) {
			errmsg("Context of allocator must be an access type", "4.8, 3.8",
			  expn);
			return;
		}

		accessed_type = (Symbol) designated_type(context_typ);
		/* Verify that the allocator matches the context.
		 * The(possibly unconstrained)	access type is	the one given by the
		 * context(eg.	declaration). If the allocator provides a constraint
		 * rather than an aggregate, then a subtype has been created, and the
		 * access type is an access to this constrained type. The  constraint
		 * must	 then be  emitted so that it is evaluated at the proper time.
		 *(The subtype is  not an anonymous type, and is introduced  only to
		 * simplify type checking).
		 * The converse may also occur: the  context is	 constrained, but the
		 * allocator  type is  unconstrained. In that  case, use  the context
		 * context type as the type of the expression.
		 * Finally,  the context  may be  an unconstrained  array type, whose
		 * index  type	is   nevertheless   bounded.  When   the allocator is
		 * initialized with an aggregate, the bounds of the aggregate must be
		 * compatible with that index type.
		 */
		if (!compatible_types(accessed_type, alloc_type)) {
			errmsg_type("Invalid type for allocator. Expect %", accessed_type,
			  "3.8, 4.8", type_node);
			return;
		}

		if (expn1 != OPT_NODE) {
			res2_check(expn1, alloc_type);
			if (is_array(accessed_type) && can_constrain(accessed_type)) {
				/* bounds of the aggregate will have to be shown to be 
				 * compatible with the (unconstrained) designated type.
				 */
				make_constrained_node(expn1, accessed_type, as_qual_sub);
			}
			else if (!can_constrain(accessed_type)
			  && accessed_type != alloc_type) {
				/*A further qualification is necessary.*/
				may_others = full_others;
				full_others = TRUE;
				apply_constraint(expn1, accessed_type);
				full_others = may_others;
			}
		}
		else if (is_array(alloc_type) && N_KIND(type_node) == as_subtype_decl) {
			/* the index subtypes of the type will have to be elaborated. */
			indices = tup_new(0);
			{ 
				Symbol i;
				FORTUP(i = (Symbol), index_types(alloc_type), ft1);
					indices =
					  tup_with(indices, (char *) new_subtype_decl_node(i));
				ENDFORTUP(ft1);
			}
			N_TYPE(expn) = context_typ;
			make_insert_node(expn, indices, copy_node(expn));
		}

		else if (is_access(alloc_type) && N_KIND(type_node) == as_subtype_decl){
			/* the designated type is anonymous, and will also be elaborated. */
			indices = tup_new(0);
			{ 
				Symbol i, d;
				d = (Symbol) designated_type(alloc_type);
				if is_array(d) {       /* elaborate indices as well */
					FORTUP(i = (Symbol), index_types(d), ft1);
						indices =
						  tup_with(indices, (char *) new_subtype_decl_node(i));
					ENDFORTUP(ft1);
				}
				indices = tup_with(indices, (char *) new_subtype_decl_node(d));
			}
			N_TYPE(expn) = context_typ;
			make_insert_node(expn, indices, copy_node(expn));
		}
		type2 = context_typ;/* No further constraints */
		break;
	/* For an attribute, we complete the type checking of the right
	 * argument, and if it must be a static expression, we perform
	 * the appropriate check and extract the attribute.
	 */
	case as_attribute:
	case as_range_attribute:
		type2 = resolve2_attr(expn, context_typ);
		/* return immediately if resolve_attr failed due to pass1_error */
		if (type2== (Symbol)0) return;
		break;
	/* A conversion may imply a run-time action, or may be used
	 * between types of the same structure to achieve type consistency.
	 * In the later case, do not emit any conversion.
	 * In both cases however, a range check may be needed.
	 */

	case as_convert:
		t_node = N_AST1(expn);
		expn1 = N_AST2(expn);
		target_type = N_UNQ(t_node);
		type2 = target_type;
		types = N_PTYPES(expn1);
		/* Apply the preference rule to choose a universal meaning for
		 * the expression in case of overloading of operators.
		 */
		/*tu = set_inter(types, univ_types);*/
		tu = set_new(0);
		if (set_mem((char *) symbol_universal_integer, types))
			tu = set_with(tu, (char *) symbol_universal_integer);
		if (set_mem((char *) symbol_universal_real, types))
			tu = set_with(tu, (char *) symbol_universal_real);
		if (set_size(types) > 1 && set_size(tu) == 1)
			types = tu;
		else set_free(tu);

		/* Verify that original expression is unambiguous. */
		if (set_size(types) != 1) {
			errmsg("ambiguous expression for conversion", "4.6", expn1);
			return;
		}
		else {
			t = (Symbol) set_arb(types);
			/*	resolve2(expn1, t);  */
			if (is_numeric(t) && is_numeric(target_type)) {
				/* conversions between any two numeric types are allowed. */
				/* all done */

				resolve2 (expn1, t);
				N_AST2 (expn) = expn1;
				/*        N_AST1 (expn) = new_name_node (t); */
				N_TYPE (expn) = target_type;
			}
			/* conversion of records with discriminant will be valid if
			 *   the discriminants have the same values
			 */
			else if (is_record (target_type) && has_discriminants (target_type)
			  && (root_type (target_type) == root_type (t))) {
				resolve2 (expn1, t);
				N_KIND (expn) = as_qual_discr;
				N_AST1 (expn) = expn1;
				N_AST2 (expn) = (Node) 0;
				N_TYPE (expn) = target_type;
			}
			/* conversion of access values pointing to arrays will be valid
			 * if the indexes of the designated type have the same values
			 */

			else if (is_access (target_type)
			  && is_array (designated_type(target_type))
			  && (root_type (target_type) == root_type (t))) {
				resolve2 (expn1, t);
				N_KIND (expn) = as_qual_aindex;
				N_AST1 (expn) = expn1;
				N_AST2 (expn) = (Node) 0;
				N_TYPE (expn) = target_type;
			}
			/* conversion of access values pointing to records with discriminant
			 * will be valid if the discriminants of the designated type have
			 * the same values
			 */

			else if (is_access (target_type)
			  && is_record (designated_type(target_type))
			  && has_discriminants (designated_type(target_type))
			  && (root_type (target_type) == root_type (t))) {
				resolve2 (expn1, t);
				N_KIND (expn) = as_qual_adiscr;
				N_AST1 (expn) = expn1;
				N_AST2 (expn) = (Node) 0;
				N_TYPE (expn) = target_type;
			}

			else if (root_type(target_type) == root_type(t)) {
				/* conversions among types derived from a common root. In
				 * the absence of representation specifications, this is a
				 * noop, indicated here by having the same type on both sides
				 */
				resolve2 (expn1, t);
				N_AST2 (expn) = expn1;
				/* N_AST1 (expn) = new_name_node (t); */
				N_TYPE (expn) = target_type;
			}
			else if (is_array(target_type)) {
				/* conversion between array types are allowed, if types of
				 * indices are convertible and component types are the same.
				 */
				exists = FALSE;
				if ( is_array(t)
				  && no_dimensions(t) == no_dimensions(target_type))
					exists = TRUE;
				if (exists) {
					for (i = 1; i <= no_dimensions(t); i++) {
						if (root_type((Symbol)index_types(target_type)[i])
						   != root_type((Symbol)index_types(t)[i])) {
							exists = FALSE; 
							break;
						}
					}
				}
				if (exists) {
					if ( base_type((Symbol)component_type(target_type))
					  != base_type((Symbol) component_type(t)))
						exists = FALSE;
				}
				if (exists) { 		 /* convertible */
					/* the following lines have been translated from the Setl
					 * version
					 */

					if (is_access (component_type (t))) {
						c1 = designated_type (component_type (t));
						c2 = designated_type (component_type (target_type));
					}
					else {
						c1 = component_type (t);
						c2 = component_type (target_type);
					}
					if ((can_constrain (c1)) != (can_constrain (c2))) {
						errmsg_l ("component types in array conversion must",
						  " be both constrained or unconstrained", 
						  "4.6 (11)", expn);
						return;
					}
					resolve2 (expn1, t);
					N_AST2 (expn) = expn1;
					N_TYPE (expn) = target_type;

					check_array_conversion(expn, t, target_type);
				}
				else {
					errmsg("Invalid array conversion", "4.6", expn);
					return;
				}
			}
			else {
				errmsg_id("cannot convert to %", target_type, "4.6", expn);
			}
		}
		/* if (N_KIND(expn) == as_insert) expn = N_AST1(expn);
		 *   	 N_TYPE(expn) = base_type(type2);
		 * 	  the result of the conversion must belong to the target subtype.
		 *   	 if (!is_array(t)) {
		 *   	     apply_constraint(expn, type2);
		 */

		apply_constraint (expn, target_type);
		break;
	case as_qualify:

		/* proc resolve2_qualify(expn, context_type);
		 * sem_trace3(3, 'At proc resolve2_qualify ', expn);
		 * [-, to_type, expn1] := expn;
		 * $ No sliding for aggregates here.
		 * may_others := full_others;
		 * full_others := true;
		 * expn2 := eval_static(apply_constraint(resolve2(expn1, to_type),
		 * to_type));
		 * full_others := may_others;                 
		 * return [['qualify', expn2], to_type];
		 */
		t_node = N_AST1(expn);
		expn1 = N_AST2(expn);
		type2 = N_UNQ(t_node);

		/* This is non-sliding context for aggregates. */
		may_others = full_others;
		full_others = TRUE;
		resolve2(expn1, type2);
		eval_static(expn1);

		apply_constraint(expn1, type2);			/* impose checks. */

		full_others = may_others;
		break;
	/* For a subtype, complete the evaluation of the bounds.
	 * If the bounds are literal, the type may be a universal one.
	 * replace it now by the corresponding non-literal type.
	 */
	case as_subtype:
		type_node = N_AST1(expn);
		constraint = N_AST2(expn);
		low = N_AST1(constraint);
		high = N_AST2(constraint);
		/* If the bounds are overloaded, the subtype itself may be an
		 * overloaded expression. Extract the type(s) that are compatible
		 * with context .
		 */
		ntypes = set_new(0);
		FORSET(ntype_sym = (Symbol), types, fs1);
			if (compatible_types(context_typ, ntype_sym))
				ntypes = set_with(ntypes, (char *) ntype_sym);
		ENDFORSET(fs1); 
		set_free(types);
		types = ntypes;
		/* Make sure that only one type is possible. */
		if (set_size(types) > 1) {
			/*types = set_diff(types, univ_types);*/
			ntypes = set_new(0);
			FORSET(ntype_sym = (Symbol), types, fs1);
				if (ntype_sym != symbol_universal_integer
				  && ntype_sym != symbol_universal_real)
					ntypes = set_with(ntypes, (char *) ntype_sym);
			ENDFORSET(fs1); 
			set_free(types); 
			types = ntypes;
		}
		if (set_size(types) != 1) {
			type_error(set_new1((char *)symbol_any), context_typ, 
			  set_size(types), expn);
			N_TYPE(expn) = symbol_any;
			return;
		}
		else
			b_type = base_type((Symbol)set_arb(types));

		/* In the case of a range in a membership op, the type may be a real
		 * one, in which case the precision is inherited from the context .
		 */
		rtype = root_type(context_typ);

		if (rtype == symbol_float || rtype == symbol_universal_real)
			kind = as_digits;
		else if (is_fixed_type(rtype))
			kind = as_delta;
		else
			kind = as_range;/* $ Discrete type. */

		if (type_node != OPT_NODE)
			b_type = N_UNQ(type_node);
		else {
			if (kind == as_range) {
				if (b_type == symbol_universal_integer) {
					b_type = symbol_integer;
					if (context_typ == symbol_universal_integer
					  && (N_KIND(low) == as_op 
					  || N_KIND(low) == as_un_op 
					  || N_KIND(high) == as_op
					  || N_KIND(high) == as_un_op)) {
						/* i.e. discrete range in arr def. or iteration rule.*/
						/* Not a literal, named number, or attribute(3.6.1(2))*/
						errmsg_l("Invalid universal expression in",
						  " discrete range", "3.6.1", expn);
						N_TYPE(expn) = symbol_any;
						return;
					}
				}
			}
			else if (kind == as_delta)
				b_type = context_typ;
			else if (kind == as_digits)
				b_type = symbol_float;
		}
		/* If the type name was not specified, then it is the type
		 * of the bounds.
		 */
		if (type_node == OPT_NODE) {
			type_node = node_new(as_simple_name);
			copy_span(constraint, type_node);
			N_UNQ(type_node) = b_type;
			N_AST1(expn) = type_node;
			N_AST2(expn) = constraint;
			if (N_AST3_DEFINED(N_KIND(expn))) N_AST3(expn) = (Node)0;
			if (N_AST4_DEFINED(N_KIND(expn))) N_AST4(expn) = (Node)0;
		}
		resolve2(low, b_type);
		resolve2(high, b_type);
		/* An index constraint may depend on a discriminant . Verify that
		 * if a discriminant appears, it is by itself, and not as part of
		 * a larger expression. 
		 */
		check_discriminant(low);
		check_discriminant(high);
		eval_static(low);
		eval_static(high);
		if (is_discrete_type(b_type)) check_bounds_in_range(low, high, b_type);

		/* No constraint is imposed on the subtype node itself.*/
		type2 = b_type;
		context_typ = b_type;
		break;
	case as_call_or_index:
		/* Find the tree which has a type compatible with the context, and
		 * resolve it.
 		 */
		call_node = N_AST1(expn);
		index_node = N_AST2(expn);
		exists = FALSE;
		FORSET(t = (Symbol), N_PTYPES(call_node), fs1);
			if (compatible_types(t, context_typ)) {
				exists = TRUE;
				break;
			}
		ENDFORSET(fs1);
		if (exists) {
			node = call_node;
			exists = FALSE;
			FORSET(t2 = (Symbol), N_PTYPES(index_node), fs1);
				if( compatible_types(t2, context_typ)) {
					exists = TRUE;
					break;
				}
			ENDFORSET(fs1);
			if (exists) {
				remove_conversions(call_node);	/* last chance */
				remove_conversions(index_node);
				exists = FALSE;
				FORSET(t = (Symbol), N_PTYPES(call_node), fs1);
					if ( compatible_types(t, context_typ)) {
						exists = TRUE;
						break;
					}
				ENDFORSET(fs1);
				if (exists) {
					node = call_node;
					exists = FALSE;
					FORSET(t2 = (Symbol), N_PTYPES(index_node), fs1);
						if (compatible_types(t2, context_typ)) {
							exists = TRUE;
							break;
						}
					ENDFORSET(fs1);
					if (exists) {
#ifdef TBSL
						type_error(set_new1('call or index'), context_typ, 2,
						  expn);
#endif
					}
				}
				else node = index_node;
			}
		}
		else node = index_node;
		resolve2(node, context_typ);
		copy_attributes(node, expn);
		type2 = N_TYPE(node);
		break;
	default:
		/* Other operators require no propagation */
		type2 = (Symbol) set_arb(types);
		break;
	}

	if (compatible_types(context_typ, type2)) N_TYPE(expn) = type2;
	else {
		errmsg_type("Incorrect type for expression. Expect %", context_typ,
		  "none", expn);
	}
}

static Symbol resolve2_attr(Node expn, Symbol context_typ)	/*;resolve2_attr*/
{
	Forset	fs1;
	Set		types;
	int		attrkind, dim, out_c;
	Symbol	type2;
	Const	con;
	Node	attr_node, arg1, arg2;
	Set		types1, types2;
	Symbol	type1, t2, itype1;

	types = N_PTYPES(expn);
	attr_node = N_AST1(expn);
	arg1 = N_AST2(expn);
	arg2 = N_AST3(expn);
	/*  The type of the right argument is determined by the attribute,
	 *  and has already been evaluated in the case of array attributes.
	 */
	/*attribute = N_VAL(attr_node); -- should be dead  ds 3-13-86*/
	attrkind = (int) attribute_kind(expn);
	types1 = N_PTYPES(arg1);
	types2 = N_PTYPES(arg2);
	type1 = (Symbol) set_arb(types1);

	if (attrkind == ATTR_PRED 
	  ||attrkind == ATTR_SUCC 
	  ||attrkind == ATTR_POS 
	  ||attrkind == ATTR_IMAGE)
		t2 = base_type(type1);
	else if (attrkind == ATTR_VALUE)
		t2 = symbol_string;
	else if (attrkind == ATTR_VAL) {
		Symbol t;
		Set otypes2;
		otypes2 = types2;
		types2 = set_new(0);
		FORSET(t = (Symbol), otypes2, fs1);
			if (compatible_types(t, symbol_integer_type))
				types2 = set_with(types2, (char *) t);
		ENDFORSET(fs1);
		if (set_size(types2) == 0) {
			errmsg("Second argument of VAL must be of some integer type",
			 "Annex A", arg2);
			return (Symbol)0;
		}
		else if (set_size(types2) == 1)
			t2 = (Symbol) set_arb(types2);
		else if (set_mem((char *) symbol_universal_integer, types2))
			t2 = symbol_universal_integer;
		else {
			errmsg("ambiguous argument for attribute VAL", "Annex A", arg2);
			return (Symbol)0;
		}
	}
	else
		t2 = symbol_integer;

	if  (attrkind != ATTR_O_FIRST && attrkind != ATTR_T_FIRST
	  && attrkind != ATTR_O_LAST && attrkind != ATTR_T_LAST
	  && attrkind != ATTR_O_RANGE && attrkind != ATTR_T_RANGE
	  && attrkind != ATTR_O_LENGTH && attrkind != ATTR_T_LENGTH)
		resolve2(arg2, t2);
	if (t2 == symbol_universal_integer)		/* possible for VAL */
		specialize(arg2, symbol_integer);
	if ((attrkind == ATTR_POSITION || attrkind == ATTR_FIRST_BIT
	  || attrkind == ATTR_LAST_BIT) && N_KIND(arg1) != as_selector) {
		errmsg("attribute must apply to selected component", "13.7.2", arg1);
	}
	/*
	 * If the left argument is a type, or if it is a constrained
	 * object, then evaluate the attribute on the type, statically if
	 * possible.
	 */
	/*
	 * All attributes, except those that  are functions,  can be applied
	 * to  an out parameter, because  they do not require reading of the
	 * object, or read  only its bounds. On the other hand, 	 if the pre-
	 * fix is an access type, it cannot be an an out parameter (4.1(4)).
	 */
	out_c = out_context; /* Save current setting*/
	out_context = !reads_prefix(attrkind, type1);
	itype1 = type1;

	if (is_array(type1)
	  && (attrkind == ATTR_O_FIRST || attrkind == ATTR_T_FIRST
	  || attrkind == ATTR_O_LAST || attrkind == ATTR_T_LAST
	  || attrkind == ATTR_O_RANGE || attrkind == ATTR_T_RANGE
	  || attrkind == ATTR_O_LENGTH || attrkind == ATTR_T_LENGTH)) {
		/*	The second argument indicates the dimension whose attribute
		 * is sought. It must be a static integer(this has been checked
		 * already).
		 */
		if (!is_static_expr(arg2))
			dim = 1;	/* By default. */
		else {
			con = (Const) N_VAL(arg2);
			dim = con->const_value.const_int;
		}
		itype1 = (Symbol) (index_types(type1)[dim]);
	}

	if (is_type_node(arg1)) {
		/* This might cause problems in eval_static. */
		/* In at least some cases, N_PTYPES has been set (cf. 4a.c line 1009),
		 * so here we clear N_PTYPES lest it be mistaken for N_TYPE (DS 9-18-86)
		 */
		N_PTYPES(arg1) = (Set) 0;
		N_UNQ(arg1) = itype1;
	}
	else if (attrkind == ATTR_COUNT) {
		/* entry name is fully resolved in first pass. */
		;		/* no op */
	}
	else {
		resolve2(arg1, type1);
	}
	out_context = out_c; /* restore	*/

	if (in_univ_attributes(attrkind)) {
		if (is_static_expr(expn)) {
			/* Specialize value if context is not universal.*/
			eval_static(expn);
			specialize(expn, context_typ);
		}
		/* in nay case indicate desired context type for subsequent conversion*/
		type2 = base_type(context_typ);
	}
	else {				 /*$$$ TBSL: check for FIRST_BIT, LAST_BIT*/
		type2 = (Symbol) set_arb(types);
	}
	return type2;
}

static int in_univ_attributes(int attrkind)				/*;in_univ_attributes*/
{
	/* test if type of attribute is universal type */
	static int attrs[] = {
		ATTR_AFT, ATTR_COUNT, ATTR_DIGITS, ATTR_EMAX, ATTR_FIRST_BIT, ATTR_FORE,
		ATTR_LAST_BIT, ATTR_O_LENGTH, ATTR_T_LENGTH, ATTR_MACHINE_EMAX,
		ATTR_MACHINE_EMIN, ATTR_MACHINE_MANTISSA, ATTR_MACHINE_RADIX,
		ATTR_MANTISSA, ATTR_POS, ATTR_POSITION, ATTR_SAFE_EMAX, ATTR_O_SIZE,
		ATTR_T_SIZE, ATTR_STORAGE_SIZE, ATTR_WIDTH, ATTR_DELTA, ATTR_EPSILON,
		ATTR_LARGE, ATTR_SMALL, ATTR_SAFE_LARGE, ATTR_SAFE_SMALL,
		ATTR_O_CONSTRAINED, ATTR_T_CONSTRAINED, ATTR_MACHINE_OVERFLOWS,
		ATTR_MACHINE_ROUNDS, ATTR_CALLABLE, ATTR_TERMINATED, 999	};
	int i;
	for (i = 0; ; i++) {
		if (attrs[i] == 999) return FALSE;
		if (attrs[i] == attrkind) return TRUE;
	}
}

static void check_bounds_in_range(Node low, Node high, Symbol b_type)
													/*;check_bounds_in_range*/
{
	/* check if the bounds of an array with a subtype_declaration are
	 * in the bounds of the base_type, when static. (When not static,
	 * a qual_range is introduced on as_convert).
	 */

	Node    lbd_range, ubd_range;
	int     low_val, high_val, lbd_val, ubd_val;
	Tuple   b_range_tup;
	Const	  low_const, high_const, lbd_const, ubd_const;

	/* Previous error such as missing declaration for variable*/
	if (b_type == symbol_any) return;
	b_range_tup   = SIGNATURE(b_type);
	lbd_range     = (Node) b_range_tup[2];
	ubd_range     = (Node) b_range_tup[3];
	if (N_KIND(low) == as_qualify) low = N_AST2(low);
	if (N_KIND(high) == as_qualify) high = N_AST2(high);

	if (is_static_expr(low) && is_static_expr(high)
	  && is_static_expr(lbd_range) && is_static_expr(ubd_range))  {
		low_const = (Const) N_VAL(low);
		high_const = (Const) N_VAL(high);
		lbd_const = (Const) N_VAL(lbd_range);
		ubd_const = (Const) N_VAL(ubd_range);
		const_check(low_const, CONST_INT);
		const_check(high_const, CONST_INT);
		const_check(lbd_const, CONST_INT);
		const_check(ubd_const, CONST_INT);
		low_val = INTV(low_const);
		high_val = INTV(high_const);
		lbd_val = INTV(lbd_const);
		ubd_val = INTV(ubd_const);

		if ((lbd_val > ubd_val && low_val <= high_val)
		  || ((low_val <= high_val) && (low_val < lbd_val || low_val > ubd_val
		  || high_val > ubd_val || high_val < lbd_val))) {
			create_raise(low, symbol_constraint_error);
			return;
		}
	}
}

static void check_array_conversion(Node expn, Symbol from_t, Symbol to_t)
												/*;check_array_conversion */
{
	/* verify that in an array conversion, source and target component types
	 * have the same constraints.
	 */

	Symbol from_c, to_c;
	Tuple  checks;
	Tuple from_i, to_i;
	int i;

	checks = tup_new(0);

	from_c = component_type(from_t);
	to_c = component_type(to_t);

	while (is_access (from_c)) {
		from_c = designated_type (from_c);
		to_c = designated_type (to_c); 
	}

	if (from_c == to_c) {
		;
	}
	else if (is_scalar_type(from_c))
		checks = tup_with(checks, (char *) new_check_bounds_node(from_c, to_c));
	else if (is_record (from_c) && has_discriminants (from_c))
		checks = new_check_disc_node (from_c, to_c); 
	else if (is_array(from_c)) {
		/* index subtypes must be equal */
		from_i = index_types(from_c);
		to_i = index_types(to_c);
		for (i = 1; i<= tup_size(from_i); i++) {
			checks = tup_with(checks,
			  (char *) new_check_bounds_node( (Symbol)from_i[i],
			  (Symbol)to_i[i]));
		}
	}
	/* TBSL: check values of discriminants for record types. */

	if (tup_size(checks) > 0) {
		make_insert_node(expn, checks, copy_node(expn));
		/* This line has to be deleted in order to reuse the function
      in case of conversion of array access values 
      N_TYPE(expn) = to_t; */
	}
}

static int reads_prefix(int attrkind, Symbol type1)
															/*;reads_prefix*/
{
	/* Used to determine whether an attribute can apply to an out parameter.
	 * see tests A62006d, B62006c, B85007C.
	 */

	if  (attrkind == ATTR_BASE
	  || attrkind == ATTR_POS
	  || attrkind == ATTR_PRED
	  || attrkind == ATTR_SUCC
	  || attrkind == ATTR_VAL
	  || attrkind == ATTR_VALUE)
		return TRUE;

	if (is_access(type1))  return TRUE;
	return FALSE;
}
