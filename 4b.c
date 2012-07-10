/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#include "4.h"
#include "dbxprots.h"
#include "setprots.h"
#include "arithprots.h"
#include "nodesprots.h"
#include "errmsgprots.h"
#include "evalprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "chapprots.h"

static int exist_compatible_type(Set, Symbol);
static int compatible_op(Symbol, Node, Symbol);
static Tuple valid_op_types(Symbol, Node);
static int in_unary_ops(Symbol);
static int op_suffix(Symbol);
static Symbol op_suffix_gen(Symbol, int);
static int in_numeric_types(Symbol);
static int eq_universal_types(Symbol, Symbol);
static int in_mult_types(Symbol, Symbol);
static int in_mixed_mult_types(Symbol, Symbol);
static int in_mod_types(Symbol, Symbol);
static int in_adding_types(Symbol, Symbol);
static int in_expon_types(Symbol, Symbol);
static Symbol valid_arg_list(Symbol, Node);
static Const check_constant_overflow(Const);
static void literal_expression(Node);
static Tuple order_arg_list(Node, Tuple);
static void bind_arg(Node, Symbol, int, int);
static int in_comparison_ops(Symbol);
static Set find_compatible_type(Set, Set);
static Tuple valid_concatenation_type(Set, Set);

/* we need the following constants in order to make some tests :
 * does a constant belong to its type interval ?
 */

extern int	ADA_MIN_INTEGER;
extern int	ADA_MAX_INTEGER;
extern int    *ADA_MAX_INTEGER_MP;
extern int    *ADA_MIN_INTEGER_MP;
extern long	ADA_MIN_FIXED, ADA_MAX_FIXED;
extern int	*ADA_MIN_FIXED_MP, *ADA_MAX_FIXED_MP;

void result_types(Node expn)							  /*;result_types*/
{
	/* This procedure performs the first pass of type resolution on over-
	 * loadable  constructs :  operators,  subprograms and literals.
	 */

	Fortup	ft1;
	Forset	fs1, fs2;
	Node	op_node;
	Node prefix_node;
	Node	arg_list_node;
	Tuple	tmp;
	Set types;
	Set ops;
	Symbol	opn;
	Set opns;
	Set valid;
	Symbol	sct;
	Symbol	t;
	Set usable, set1;
	Symbol typ;
	int	exists, nat;
	Symbol	package;
	Node	arg;

	if (cdebug2 > 3)  TO_ERRFILE("AT PROC :  result_types");

	/* Check for previous type error.*/

	if (noop_error ) {
		N_PTYPES(expn) = set_new(0);
		return;
	}

	op_node = N_AST1(expn);
	arg_list_node = N_AST2(expn);
	ops = set_new(0);
	types = set_new(0);
	/* The C code differs from SETL code in that set loop only needed for simple
	 * names		ds 8-jan-85
	 * this is not longer the case!! gs apr 1 85
	 */
	set1 = N_NAMES(op_node);
	FORSET(opn =(Symbol), set1, fs1);
		nat = NATURE(opn);
		if (nat == na_un_op || nat == na_op) {
			tmp = valid_op_types(opn, expn);
			opns = (Set) tmp[1];
			valid = (Set) tmp[2];
			if (set_size(valid) == 0)
				opns = set_new(0);
			/* A predefined operator is usable if its resulting types appears
			 * in a lexically open scope, or a used package.
			 */
			usable = set_new(0);
			if (N_KIND(op_node) == as_selector 
			  && SCOPE_OF(opn) == symbol_standard0) {
				/* use of P.'op' for a predefined operator.  Name resolution
	      		 * has already verified that the operator is defined in scope
	      		 * P, or that the scope declares an implicit operator. (see
	      		 * find_selected_comp and has_implicit_operator).
				 */
				prefix_node = N_AST1(op_node);
				package = N_UNQ(prefix_node);
				/* after which it can be treated as a simple name.*/
				N_KIND(op_node) = as_simple_name;
				FORSET(t=(Symbol), valid, fs2);
					usable = set_with(usable, (char *) t);
				ENDFORSET(fs2);
			}
			else {		/* normal infix usage of operator */
				FORSET(t=(Symbol), valid, fs2);
					sct = SCOPE_OF(t);
					if (tup_mem((char *)sct, open_scopes)
					  || tup_mem((char *)sct, used_mods))
						usable = set_with(usable, (char *) t);
				ENDFORSET(fs2);
			}
			/* usable := {t in valid | (sct := SCOPE_OF(t)) in open_scopes
			 * 	or sct in used_mods};
	     	*/
			if (set_size(usable) == 0 && set_size(valid) == 1 
		      && set_size(N_NAMES(op_node)) == 1) {
				pass1_error("operator is not directly visible",
			      "6.6, 8.3, 8.4", op_node);
				return;
			}
			else {
				ops = set_union(ops, opns );
				types = set_union(types, usable);
			}
		}
		else if (nat == na_procedure || nat == na_procedure_spec
	      || nat == na_function || nat == na_function_spec
	      || nat == na_entry || nat == na_entry_family	) {
			typ = valid_arg_list(opn, arg_list_node);
			if (typ != (Symbol)0 ) {
				types = set_with(types, (char *) typ);
				ops = set_with(ops, (char *) opn);
			}
		}
		else if (nat == na_literal)  {
			/* A literal may overload a function. The literal is valid only
			 * if the argument list is empty.
			 */
			if (tup_size(N_LIST(arg_list_node)) == 0) {
				types = set_with(types, (char *) TYPE_OF(opn));
				ops = set_with(ops , (char *) opn);
			}
		}
	ENDFORSET(fs1);

	exists = FALSE;
	FORTUP(arg=(Node), N_LIST(arg_list_node), ft1);
		if (set_mem((char *)symbol_universal_fixed, N_PTYPES(arg))) {
			exists = TRUE;
			break;
		}
	ENDFORTUP(ft1);
	if (set_size(types) == 0 && exists ) {
		errmsg("Missing explicit conversion from universal fixed value",
		  "3.5.9, 4.5.5", op_node);
		noop_error = TRUE;
	}
#ifdef DEBUG
	if (cdebug2 > 0) {
		TO_ERRFILE("resulting types ");
		/* use zpsymset	 from sdbx.c to list set for debugging 
		 * This is temporary measure until new errmsg package installed
		 */
		zppsetsym(types);
	}
#endif
	N_NAMES(op_node) = ops;
	N_OVERLOADED(op_node) = TRUE;
	N_PTYPES(expn) = types;
}

void disambiguate(Node expn, Symbol context_typ)		  /*;disambiguate*/
{
	/* TBSL: check translation of this procedure CAREFULLY!! (ds 22 may)*/

	/* Called from	resolve2, when more than one operator  or  function is
	 * compatible  with the context type.  Apart from true	ambiguity, this
	 * can also happen if both a predefined and a user-defined operator are
	 * visible. This is because all predefined operators in the language have
	 * generic signatures (e.g. universal_integer rather than INTEGER) and as
	 *  result, a user-defined operator does not hide the corresponding
	 * operator(they do not have the same signature). The solution is to
	 * choose in favor of the user-defined op. if it is defined in the same
	 * package as the type, or in an open scope, and in favor of the
	 * defined one otherwise. For comparison  operators which yields the pre-
	 * defined  type BOOLEAN, the  above reasoning applies to the type of its
	 * formals and not to the boolean context.
	 *
	 * On the other hand, a predefined operator of (generic) type o_t may be
	 * compatible with arguments of type a_t and with the context c_t, while
	 * a_t is in fact not compatible with c_t.  To catch that case, we check
	 * valid_op_types again to verify that the result is compatible with the
	 * context.
	 *
	 * A final wrinkle : if the context is universal, as in a number declara-
	 * tion, then the predefined operator is used even if a user-defined one
	 * is in scope.
	 */

	Node	op_node;
	Node	args_node;
	Set valid_ops, ovalid_ops;
	Symbol	nam;
	Symbol	opn;
	Forset	fs1;
	int exists;
	Symbol	sc, scc;
	Tuple tup;
	/*TBSL: there are a number of statements of the form
	 *	valid_ops = {x in valid_ops | c(x) }
	 * In C we translate this as
	 *	ovalid_ops = valid_ops;
	 *	valid_ops = set_new(0);
	 *	FORSET(x=, ovalid_ops, fs1);
	 *		if(c(x)) set_with(valid_ops, x)
	 *	ENDFORSET
	 * Perhaps later we can do this be removing elements from valid_ops.
	 * Also we will eventually want to free dead sets.
	 */

	op_node = N_AST1(expn);
	args_node = N_AST2(expn);
	valid_ops = N_NAMES(op_node);
	if (cdebug2 > 2) {
		TO_ERRFILE("AT PROC: disambiguate");
		FORSET(nam =(Symbol) , valid_ops, fs1);
			TO_ERRFILE("OVERLOADS ");
		ENDFORSET(fs1); 
	}
	ovalid_ops = valid_ops;
	valid_ops = set_new(0);
	FORSET(opn=(Symbol), ovalid_ops, fs1);
		if ( (NATURE(opn) != na_op)
	      || compatible_op(opn, args_node, context_typ))
			valid_ops = set_with(valid_ops, (char *) opn);
	ENDFORSET(fs1);
	/* return statements have been inserted earlier to simplify the logic
	 * of the translation to c (ds 22 may 84) 
	 */
	if (in_univ_types(context_typ)) {
		ovalid_ops = valid_ops;
		valid_ops = set_new(0);
		FORSET(opn=(Symbol), ovalid_ops, fs1);
		if (TYPE_OF(opn) == context_typ)
			valid_ops = set_with(valid_ops, (char *) opn);
		ENDFORSET(fs1);
		N_NAMES(op_node) = valid_ops;
		return;
	}

	exists = FALSE;
	FORSET(nam=(Symbol), valid_ops, fs1);
		sc = SCOPE_OF(nam);
		tup = SIGNATURE(nam);
		if (tup!=(Tuple)0)		/* avoid dereference of null pointer */
			scc = (Symbol) tup[1];
		else
			scc = (Symbol)0;
		if  (NATURE(nam) != na_op && (sc == SCOPE_OF(context_typ)
	      || in_open_scopes(sc)
	      /* maybe a compar op. Check against scope of type of first formal.*/
		  || (TYPE_OF(nam) == symbol_boolean
		  && ( scc!=(Symbol)0 && sc == SCOPE_OF(TYPE_OF(scc)))) ) ) {
			exists = TRUE;
			break;
		}
	ENDFORSET(fs1);
	if (exists) {
		/* user-defined operator(s) hide derived operator.*/
		ovalid_ops = valid_ops;
		valid_ops = set_new(0);
		FORSET(nam=(Symbol), ovalid_ops, fs1);
			if (NATURE(nam) != na_op)
			valid_ops = set_with(valid_ops, (char *) nam);
		ENDFORSET(fs1);
		N_NAMES(op_node) = valid_ops;
		return;
	}

	exists = FALSE;
	FORSET(nam=(Symbol), valid_ops, fs1);
		if (NATURE(nam) == na_op) {
			exists = TRUE;
			break;
		}
	ENDFORSET(fs1);
	if (exists) {
		/* It will have precedence over imported user-defined functions.*/
		ovalid_ops = valid_ops;
		valid_ops = set_new(0);
		FORSET(nam=(Symbol), ovalid_ops, fs1);
			if (NATURE(nam) == na_op)
				valid_ops = set_with(valid_ops, (char *) nam);
		ENDFORSET(fs1);

		if (is_fixed_type(root_type(context_typ))) {
			/* remove mixed floating operators, that yield universal*/
			/* real, but are not compatible with a fixed type context*/
			ovalid_ops = valid_ops;
			valid_ops = set_new(0);
			FORSET(nam=(Symbol), ovalid_ops, fs1);
			if (TYPE_OF(nam) != symbol_universal_real)
				valid_ops = set_with(valid_ops, (char *) nam);
			ENDFORSET(fs1);
		}
	}
	N_NAMES(op_node) = valid_ops;
}

static int exist_compatible_type(Set set1, Symbol context_type)
													/*exist_compatible_type*/
{
	/* retun true if it exists one type of set1 that id compatible 
	 * with context_type
	 */

	Forset fs1;
	Symbol t;

	FORSET(t=(Symbol), set1, fs1);
		if (compatible_types(t, context_type))
			return TRUE;
	ENDFORSET(fs1);
	return FALSE;
}

static int compatible_op(Symbol opn, Node args_node, Symbol context_typ)
															/*;compatible_op*/
{
	Tuple	arg_list;
	Set types1, types2;
	Symbol	t;
	Forset	fs1;

	if (cdebug2 > 2) TO_ERRFILE("AT PROC compatible_op");
	/* In most cases, binary operators are homogenenous: the type of their
	 * arguments is also  the type of the result. We get the types	of the
	 * arguments to perform this test:
	 */
	arg_list = N_LIST(args_node);
	if (tup_size(arg_list) == 0)
		types1 = set_new(0);
	else
		types1 = N_PTYPES(((Node)arg_list[1]));

	if (tup_size(arg_list) == 2 ) types2 = N_PTYPES(((Node) arg_list[2]));

	/* For comparison operators, the types of the operands are known to be
	 * compatible and unrelated to the boolean result. 
	 */

	if (in_comparison_ops(opn)) return TRUE;
	if (opn == symbol_mulifl || opn == symbol_mulifx) {
		FORSET(t=(Symbol), types2, fs1);
			/* For these ops, the second argument yields the result type.*/
			if (compatible_types(t, context_typ))
				return TRUE;
		ENDFORSET(fs1);
		return FALSE;
	}
	if (opn == symbol_cat_ac )
		return ((exist_compatible_type (types1, context_typ)
		  && exist_compatible_type (types2, component_type(context_typ))));
	if (opn == symbol_cat_ca)
		return ((exist_compatible_type (types2, context_typ)
		  && exist_compatible_type (types1, component_type(context_typ))));
	if (opn == symbol_cat_cc)
		return ((exist_compatible_type (types2, component_type(context_typ))
		  && exist_compatible_type (types1, component_type(context_typ))));
	return (exist_compatible_type (types1, context_typ));
}

void remove_conversions(Node expn)  /*;remove_conversions*/
{
	/* If after the previous procedure an expression is still ambiguous, this
	 * may be due to an implicit conversion of a universal quantity. This can
	 * only	 happen in the	presence of user-defined operators.  We therefore
	 * attempt to  resolve the expression  again, after removing user-defined
	 * operators from the  tree, whose  arguments are universal quantities.
	 * A full disambiguation would require that we try to remove these selec-
	 * tively. Here we simply  remove all  of them, and give up if the result
	 * is still ambiguous.
	 */

	Node	args_node, arg, op_node, a_list_node, ts, a_expn;
	Set arg_types, arg_op, tset;
	Symbol	n, t;
	int		exists, nk;
	Fortup	ft1;
	Forset	fs1;

	if (cdebug2 > 2) TO_ERRFILE("AT PROC: remove_conversions");

	nk = N_KIND(expn);
	if (nk == as_call || nk == as_op || nk == as_un_op) {
		args_node = N_AST2(expn);
		FORTUP(arg =(Node), N_LIST(args_node), ft1);
			arg_types = N_PTYPES(arg);
			if (set_size( arg_types) < 2 );	/*$ unambiguous.*/
			else if (N_KIND(arg) != as_aggregate ) {
				op_node = N_AST1(arg);
				a_list_node = N_AST2(arg);
				arg_op = N_NAMES(op_node);
				if (!N_OVERLOADED(op_node) );
				/* Incomplete: could be an indexing on an overloaded call!*/

				else if (
				  !in_op_designators(original_name((Symbol)set_arb(arg_op))))
					/* May be overloaded because some of its arguments are.*/
					remove_conversions(arg);
				else {
					exists = FALSE;
					FORTUP(ts=(Node), N_LIST(a_list_node), ft1);
						if (set_mem((char *) symbol_universal_integer,
						  N_PTYPES(ts)) || set_mem(
						  (char *)symbol_universal_real, N_PTYPES(ts))) {
							exists = TRUE;
							break;
						}
					ENDFORTUP(ft1);
					if (exists) {
						/* Some arg is universal. Resolve as predefined op */
						tset = set_new(0);
						FORSET(n=(Symbol), arg_op, fs1);
							if (NATURE(n) == na_op)
								tset = set_with(tset, (char *) n);
						ENDFORSET(fs1);
						N_NAMES(op_node) = tset;
						result_types(arg);
					}
				}
			}
		ENDFORTUP(ft1);

		/* Use the pruned argument list to resolve again the expression.*/
		result_types(expn);
	}
	else if (nk == as_all) {
		a_expn = N_AST1(expn);
		remove_conversions(a_expn);
		tset = set_new(0);
		FORSET(t=(Symbol), N_PTYPES(a_expn), fs1);
			if (is_access(t))
				tset = set_with(tset, (char *) designated_type(t));
		ENDFORSET(fs1);
		N_PTYPES(expn) = tset;
	}
	else {			/* may be continued: indexing, selection. */
		;
	}
}

static Tuple valid_op_types(Symbol opn, Node expn)		 /*;valid_op_types*/
{
	/* This procedure is invoked during the bottom-up pass of type
	 * resolution. It determines the possible result types of predefined
	 * operators, using the possible types of their arguments.
	 * All arithmetic operators have special rules that apply within literal
	 * expressions. They are all treated in routine valid_arith_ops.
	 * For other operators, the following rule applies:
	 * Binary operators yield the intersection of the types of their two
	 * arguments, provided that they are boolean (For boolean operators),
	 * discrete (for ordering operators) , etc.
	 * The concatenation operator provides an exception : it will
	 * concatenate and array with an object of the component type, either
	 * on the left or right.
	 * The node can be a call ( "+"(a,b) for example) or a qualified name,
	 * in which case the only way to distinguish between unary and binary 
	 * ops. is to look at the  length of the argument list.
	 */

	/* const unary_ops  = ['+', '-', 'abs', 'not']; */
	Node	op_node, arg_list_node, arg1, arg2;
	Set possible_types, opossible_types, typ1, typ2;
	Symbol	t2, t, typ;
	Set		types;
	Tuple	arg_list, tup;
	Forset	fs1, fs2;
	int		exists;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  valid_op_types");

	op_node = N_AST1(expn);
	arg_list_node = N_AST2(expn);

	if (N_KIND(expn) == as_un_op
	  || (tup_size(N_LIST(arg_list_node)) == 1 && in_unary_ops(opn ) ) )
		arg_list = order_arg_list(arg_list_node, unary_sig);
	else
		arg_list = order_arg_list(arg_list_node, binary_sig);
	if (arg_list == (Tuple)0) {
		tup = tup_new(2);
		tup[1] = (char *) set_new(0);
		tup[2] = (char *) set_new(0);
		return tup;
	}

	if (TYPE_OF(opn) == symbol_numeric)
		return valid_arith_types(opn, arg_list);

	if (tup_size(arg_list) == 1) {
		arg1 = (Node) arg_list[1];
		possible_types =set_new(0);
		FORSET(t=(Symbol), N_PTYPES(arg1), fs1);
			possible_types = set_with(possible_types, (char *) base_type(t));
		ENDFORSET(fs1);
	}
	else {
		/*Binary operator.*/
		arg1 = (Node) arg_list[1];
		arg2 = (Node) arg_list[2];
		typ1 = N_PTYPES(arg1);
		typ2 = N_PTYPES(arg2);

		if (opn == symbol_cat)
			/* Both arguments must have the same one-dimensional array type,
			 * or one or both may have the component type of such an array type
			 */
			return (valid_concatenation_type ( typ1, typ2));

		else{
			/* All other binary operators are homogeneous : the arguments
			 * must have compatible types,
			 */
			possible_types = set_new(0);
			FORSET(t=(Symbol), typ1, fs1);
				exists = FALSE;
				FORSET(t2=(Symbol), typ2, fs2);
					if (compatible_types(t, t2) && t != symbol_universal_fixed){
						exists = TRUE;
						break;
					}
				ENDFORSET(fs2);
				if (exists)
					possible_types = set_with(possible_types,
					  (char *) base_type(t));
			ENDFORSET(fs1);
		}
	}
	/* Remove array types with incomplete private components.*/
	opossible_types = possible_types;
	possible_types = set_new(0);
	FORSET(t=(Symbol), opossible_types, fs1);
		/* the aim of this test is to remove array types with incomplete
		 * private components. We think taht the use of the function
		 * "is_fully_private" is indadequate in this case. The new test checks
		 * id the array is incomplete and private
		 */
		/* if(!is_array(t) || ! is_fully_private(t) ) {*/
		if (!is_array(t)
		  || (! ((((int) misc_type_attributes (t)) & TA_INCOMPLETE)
		  && (((int) misc_type_attributes (t))
		  & (TA_PRIVATE | TA_LIMITED_PRIVATE)))))
			possible_types = set_with(possible_types, (char *) t);
	ENDFORSET(fs1);

	typ = TYPE_OF(opn);
	if (typ == symbol_boolean) {
		/* equality and membership operators.*/

		if (opn == symbol_eq || opn == symbol_ne) {
			exists = FALSE;
			FORSET(t=(Symbol), possible_types, fs1);
				if (! is_limited_type(t)) {
					types = set_new1((char *) symbol_boolean);
					exists = TRUE;
					break;
				}
			ENDFORSET(fs1);
			if (! exists) types = set_new(0);
		}
		else {
			if (set_size(possible_types) > 0)
				types = set_new1((char *) symbol_boolean);
			else
				types = set_new(0);
		}
	}
	else if(typ == symbol_boolean_type) {
		/* Boolean and short circuit operators.*/

		if (opn == symbol_andthen || opn == symbol_orelse) {
			types = set_new(0);
			FORSET(t=(Symbol), possible_types, fs1);
				if (root_type(t) == symbol_boolean)
					types = set_with(types, (char *) t);
			ENDFORSET(fs1);
		}
		else {
			types = set_new(0);
			FORSET(t=(Symbol), possible_types, fs1);
				if(root_type(t) == symbol_boolean || is_array(t)
				  && no_dimensions(t) == 1
				  && root_type((Symbol)(component_type(t))) == symbol_boolean)
					types = set_with(types, (char *) t);
			ENDFORSET(fs1);
		}
	}
	else if (typ == symbol_order_type) { /* Comparison operators.*/
		exists = FALSE;
		FORSET(t=(Symbol), possible_types, fs1);
			if (is_scalar_type(t) || is_array(t) && no_dimensions(t) == 1
		      && is_discrete_type((Symbol)component_type(t))) {
				types = set_new1((char *) symbol_boolean);
				exists = TRUE;
				break;
			}
		ENDFORSET(fs1);
		if (!exists) types = set_new(0);
	}
	else if (typ == symbol_any) 	      /* Syntax error*/
		types = set_new1((char *) symbol_any);

	else {
		/* The SETL simply prints the TYPE_OF field, i.e. the unique name
		 * of some entry in the symbol table. In C, this is not enough!
		 */
		char *msg = emalloct(100, "valid-op-types-msg");

		sprintf(msg, "at loc: %d, nature: %s, value: %s",
		  typ, nature_str(NATURE(typ)), ORIG_NAME(typ) );
		errmsg_str("system error: strange op type %", msg, "none", arg1);
		efreet(msg, "valid-op-types-msg");
	}
	tup = tup_new(2);
	tup[1] = (char *) set_new1((char *) opn);
	tup[2] = (char *) types;
	return tup;
}

static int in_unary_ops(Symbol opn)						/*;in_unary_ops*/
{
	/* const unary_ops  = ['+', '-', 'abs', 'not'];
	 * corresponds to opn in unary_ops
	 */
	return (opn == symbol_add || opn == symbol_sub || opn == symbol_abs
	    || opn == symbol_not);
}
/* OP_SUFFIX codes used to represent SETL sfx character string values */

#define OP_SUFFIX_NONE	0
#define OP_SUFFIX_I		1
#define OP_SUFFIX_FL	2
#define OP_SUFFIX_FX	3
#define OP_SUFFIX_FLI	4
#define OP_SUFFIX_FXI	5
#define OP_SUFFIX_IFL	6
#define OP_SUFFIX_IFX	7
#define OP_SUFFIX_U		8
#define OP_SUFFIX_UI	9
#define OP_SUFFIX_UFL	10
#define OP_SUFFIX_UFX	11

Tuple valid_arith_types(Symbol opn, Tuple arg_list)	/*;valid_arith_types*/
{
	/* Bottom-up pass over arithmetic expressions. return the pair:
	 * [possible operators, possible result types] .
	 */
#ifdef TBSN

	macro i;  
	"INTEGER"	       endm;
	macro fl;  
	"FLOAT"	       endm;
	macro fx;  
	"$FIXED"	       endm;
	macro ui; 
	"universal_integer" endm;
	macro ur; 
	"universal_real"    endm;
	macro ufx; 
	"universal_fixed"   endm;

	const numeric_types = {
		i, fl, fx, ui, ur}, 
		    universal_types = {
			ui, ur}, 

			    adding_types = { 
				[i , i ], [fl, fl], [fx, fx], [ui, i],
				    [ui, ui], [ur, ur], [ur, fx], [ur, fl]}, 

				    mult_types	  = { 
					[i , i ], [fl, fl], [fx, fx], [ui, i ],
					    [ui, ui], [ur, ur], [ur, fl]}, 

					    mixed_mult_types = { 
						[fx, i], [fx, ui], [ur, ui], [ur, i]}, 

						    mod_types	  = { 
							[i, i], [ui, i], [i, ui], [ui, ui]}, 

							    expon_types    = { 
								[i , i ], [fl, i ], [ur, i ], [ui, i ],
								    [i , ui], [fl, ui], [ur, ui], [ui, ui]  }, 


								    op_suffix	  = { 
	[i, "i"], [ui, "i"], [fl, "fl"], [ur, "fl"],
	    [fx, "fx"] , [ufx, "fx"]
								};
#endif

	Set possible_types, types, ops, typ1, typ2;
	Symbol	t;
	Symbol	t1, t2, r_type, bt1, bt2;
	int		sfx;
	Forset	fs1, fs2;
	Tuple	tup;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  valid_arith_types");
	if  (tup_size(arg_list) == 1) {		/* Unary ops return the type*/
		/* of their argument.*/
		possible_types = (Set) (N_PTYPES((Node)(arg_list[1])) );

		types = set_new(0);
		FORSET(t=(Symbol), possible_types, fs1);
			if (in_numeric_types(root_type(t)))
				types = set_with(types, (char *) base_type(t));
		ENDFORSET(fs1);

		/*Construct the unary version of the operator name.*/
		if (opn == symbol_add) opn = symbol_addu;
		else if (opn == symbol_sub) opn = symbol_subu;
		/*ops = ??{ opn + op_suffix(root_type(t)): t in types};*/
		ops = set_new(0);
		FORSET(t=(Symbol), types, fs1);
			ops = set_with(ops,
			  (char *)op_suffix_gen(opn, op_suffix(root_type(t))));
		ENDFORSET(fs1);
		tup = tup_new(2);
		tup[1] = (char *) ops;
		tup[2] = (char *) types;
		return tup;
	}
	else {
		typ1 = N_PTYPES((Node)(arg_list[1]));
		typ2 = N_PTYPES((Node)(arg_list[2]));

		ops = set_new(0);
		types =set_new(0);

		FORSET(t1=(Symbol), typ1, fs1);
			FORSET(t2=(Symbol), typ2, fs2);
				sfx =OP_SUFFIX_NONE;/* Suffix to designate type of op.*/
				r_type = (Symbol)0;		/*will indicate type found.*/
				bt1 = root_type(t1);
				bt2 = root_type(t2);

				if (opn == symbol_add || opn == symbol_sub) {
					if (in_adding_types(bt1, bt2)
					  || in_adding_types(bt2, bt1) )
						r_type = intersect_types(t1, t2);
				}
				else if (opn == symbol_mul || opn == symbol_div) {
					if (in_mult_types(bt1, bt2) || in_mult_types(bt2, bt1) ) {
						if (is_fixed_type(bt1)||is_fixed_type(bt2))
							r_type = symbol_universal_fixed;
						else
							r_type = intersect_types(t1, t2);
					}
					else {
						/* Mixed mode operation on fixed types, or
						 * literal expression.
						 */
						if (in_mixed_mult_types(bt1, bt2) ) {
							if (eq_universal_types(bt1, bt2 )) {
								/* Literal expr.*/
								r_type = symbol_universal_real;
								sfx = OP_SUFFIX_FLI;	/* Compile-time op.*/
							}
							else if (base_type(t2) == symbol_integer) {
								/* Mixed mode operation with a fixed type.
								 * If the first argument is universal, the
								 * result is $FIXED, i.e any fixed type.
								 */
								if (t1 == symbol_universal_real )
									r_type = symbol_dfixed;
								else r_type = t1;
								sfx = OP_SUFFIX_FXI;	/* Run-time operation.*/
							}
							else if (bt2 == symbol_universal_integer) {
								/* specific type on left*/
								r_type = t1;
								sfx = OP_SUFFIX_FXI;
							}
						}
						else if (in_mixed_mult_types(bt2, bt1)
			    		  && opn == symbol_mul/* '*'*/) {
							/* Mixed modes are not commutative for division.*/
							if (eq_universal_types(bt1, bt2) ) {
								r_type = symbol_universal_real;
								sfx = OP_SUFFIX_IFL;
							}
							else if (base_type(t1) == symbol_integer) {
								/* $FIXED, or the specific fixed type t2.*/
								if (t2 == symbol_universal_real)
									r_type = symbol_dfixed;
								else r_type = t2;
								sfx = OP_SUFFIX_IFX;
							}
							else if (bt1 == symbol_universal_integer) {
								/* specific type on right*/
								r_type = t2;
								sfx = OP_SUFFIX_IFX;
							}
						}
					}
				}
				else if (opn == symbol_mod || opn == symbol_rem) {
					if (in_mod_types(bt1, bt2) )
						r_type = intersect_types(t1, t2);
				}
				else if(opn == symbol_exp) {
					/* The result of an exponentiation has the type of the
					 * first argument.
					 */
					if (in_expon_types(bt1, bt2)) r_type = t1;
				}

				if (r_type != (Symbol)0) {	/* Pair of matching types found.*/
					/* The result type of an arithmetic operation does not carry
					 * the constraint (if any) of the arguments. Therefore, drop
					 * the constraint on the result if it appears as a subtype.
 					 */
					types = set_with(types, (char *)  base_type(r_type));

					/* Append to the operator name a suffix that specifies the
					 * type of its arguments and the type returned.
 					 */
					if (sfx == OP_SUFFIX_NONE)
						sfx = op_suffix(root_type(r_type));
					ops = set_with(ops, (char *) op_suffix_gen(opn , sfx) );
				}
			ENDFORSET(fs2);
		ENDFORSET(fs1);
	}
	tup = tup_new(2);
	tup[1] = (char *)ops;
	tup[2] = (char *)types;
	return tup;
}

static int op_suffix(Symbol ocode)							  /*;op_suffix*/
{
	/*	Return C analog of op_suffix in SETL version.
	 * op_suffix	  = { [i, 'i'], [ui, 'i'], [fl, 'fl'], [ur, 'fl'],
	 * 		[fx, 'fx'] , [ufx, 'fx']};
	 */
	if (ocode == symbol_integer) return OP_SUFFIX_I;
	if (ocode == symbol_universal_integer) return OP_SUFFIX_I;
	if (ocode == symbol_float) return OP_SUFFIX_FL;
	if (ocode == symbol_universal_real)	return OP_SUFFIX_FL;
	if (is_fixed_type(ocode)) return OP_SUFFIX_FX;
	if (ocode == symbol_universal_fixed) return OP_SUFFIX_FX;
	return OP_SUFFIX_NONE;
}

static Symbol op_suffix_gen(Symbol op, int sfx)				 /*;op_suffix_gen*/
{
	/* Generate symbol correspond to op with suffix code sfx */
	if (sfx == OP_SUFFIX_NONE) return op;
	if (op == symbol_abs) {
		if (sfx == OP_SUFFIX_FL) return symbol_absfl;
		if (sfx == OP_SUFFIX_FX) return symbol_absfx;
		if (sfx == OP_SUFFIX_I) return symbol_absi;
	}
	else if (op == symbol_add) { /* + */
		if (sfx == OP_SUFFIX_FL)		return symbol_addfl;	/* +fl */
		if (sfx == OP_SUFFIX_FX)		return symbol_addfx;	/* +fx */
		if (sfx == OP_SUFFIX_I)		return symbol_addi;	/* +i  */
		if (sfx == OP_SUFFIX_U)		return symbol_addu;	/* +u  */
		if (sfx == OP_SUFFIX_UFL)		return symbol_addufl;	/* +ufl */
		if (sfx == OP_SUFFIX_UFX)		return symbol_addufx;	/* +ufx */
		if (sfx == OP_SUFFIX_UI)		return symbol_addui;	/* +ui */
	}
	else if (op == symbol_addu) { /* +u */
		if (sfx == OP_SUFFIX_FL)		return symbol_addufl;	/* +ufl */
		if (sfx == OP_SUFFIX_FX)		return symbol_addufx;	/* +ufx */
		if (sfx == OP_SUFFIX_I)		return symbol_addui;	/* +ui */
	}
	else if (op == symbol_div) {	/* / */
		if (sfx == OP_SUFFIX_FL)		return symbol_divfl;	/* /fl */
		if (sfx == OP_SUFFIX_FLI)		return symbol_divfli;	/* /fli */
		if (sfx == OP_SUFFIX_FX)		return symbol_divfx;	/* /fx */
		if (sfx == OP_SUFFIX_FXI)		return symbol_divfxi;	/* /fxi */
		if (sfx == OP_SUFFIX_I)		return symbol_divi;	/* /i */
	}
	else if (op == symbol_exp) {
		if (sfx == OP_SUFFIX_I)		return symbol_expi;	/* **i */
		if (sfx == OP_SUFFIX_FL)		return symbol_expfl;	/* **fl */
	}
	else if (op == symbol_mod) {	/* mod */
		if (sfx == OP_SUFFIX_I)		return symbol_modi;	/* modi */
	}
	else if (op == symbol_mul) {	/* * */
		if (sfx == OP_SUFFIX_I)		return symbol_muli;	/* *i  */
		if (sfx == OP_SUFFIX_FL)		return symbol_mulfl;	/* *fl */
		if (sfx == OP_SUFFIX_FLI)		return symbol_mulfli;	/* *fli */
		if (sfx == OP_SUFFIX_FX)		return symbol_mulfx;	/* *fx */
		if (sfx == OP_SUFFIX_FXI)		return symbol_mulfxi;	/* *fxi */
		if (sfx == OP_SUFFIX_IFL)		return symbol_mulifl;	/* *ifl */
		if (sfx == OP_SUFFIX_IFX)		return symbol_mulifx;	/* *ifx */
	}
	else if (op == symbol_rem) {
		if (sfx == OP_SUFFIX_I)		return symbol_remi;	/* remi */
	}
	else if (op == symbol_sub) {		/* - */
		if (sfx == OP_SUFFIX_FL)		return symbol_subfl;	/* -fl */
		if (sfx == OP_SUFFIX_FX)		return symbol_subfx;	/* -fx */
		if (sfx == OP_SUFFIX_I)		return symbol_subi;	/* -i  */
		if (sfx == OP_SUFFIX_U)		return symbol_subu;	/* -u  */
		if (sfx == OP_SUFFIX_UFL)		return symbol_subufl;	/* -ufl */
		if (sfx == OP_SUFFIX_UFX)		return symbol_subufx;	/* -ufx */
		if (sfx == OP_SUFFIX_UI)		return symbol_subui;	/* -ui */
	}
	else if (op == symbol_subu) { /* -u */
		if (sfx == OP_SUFFIX_I)		return symbol_subui;	/* -ui */
		if (sfx == OP_SUFFIX_FL)		return symbol_subufl;	/* -ufl */
		if (sfx == OP_SUFFIX_FX)		return symbol_subufx;	/* -ufx */
	}
#ifdef TBSL
	-- need to handle subui and addui more completely, check
	    -- other unary operators
#endif
#ifdef DEBUG
	printf("unable to match operator\n");
	zpsym(op);
#endif
	chaos("op_suffix_gen(4)");
	return (Symbol)0;
}

#undef OP_SUFFIX_NONE 
#undef OP_SUFFIX_I	
#undef OP_SUFFIX_FL	
#undef OP_SUFFIX_FX	
#undef OP_SUFFIX_FLI	
#undef OP_SUFFIX_FXI	
#undef OP_SUFFIX_IFL	
#undef OP_SUFFIX_IFX	
#undef OP_SUFFIX_U	
#undef OP_SUFFIX_UI	
#undef	OP_SUFFIX_UFL	
#undef OP_SUFFIX_UFX	

Symbol intersect_types(Symbol t1, Symbol t2) /*;intersect_types*/
{
	/* Find the more specific of two numeric types, if they are compatible.
	 * In particular, if  only one of them is  universal, return the other.
	 * Called to validate arithmetic arguments and bounds of subtypes.
	 */

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  intersect_types");

#ifdef TBSN    
	Const universal_types =
	    { 'universal_integer', 'universal_real', '$FIXED' };
#endif
	if (compatible_types(t1, t2)) {
		if (t1 == symbol_universal_integer || t1 == symbol_universal_real
		  || t1 == symbol_dfixed)
			return (t2);
		else if (t2 == symbol_universal_integer || t2 == symbol_universal_real
		  || t2 == symbol_dfixed)
			return (t1);
		else return(t1);
	}
	else return (Symbol)0;
}

static int in_numeric_types(Symbol t)				  /*;in_numeric_types*/
{
	return t == symbol_integer
	  || t == symbol_float
	  || is_fixed_type(t)
	  || t == symbol_universal_integer
	  || t == symbol_universal_real;
}

static int eq_universal_types(Symbol t1, Symbol t2) /*;eq_universal_types*/
{
	return (t1 == symbol_universal_integer && t2 == symbol_universal_real)
	  || (t2 == symbol_universal_integer && t1 == symbol_universal_real);
}

static int in_adding_types(Symbol t1, Symbol t2)		 /*;in_adding_types*/
{
	/* [symbol_integer , symbol_integer ], 
	 * [symbol_float, symbol_float], 
	 * [symbol_dfixed, symbol_dfixed], 
	 * [symbol_universal_real, symbol_universal_real], 
	 * [symbol_universal_integer, symbol_integer],
	 * [symbol_universal_integer, symbol_universal_integer], 
	 * [symbol_universal_real, symbol_dfixed], 
	 * [symbol_universal_real, symbol_float] ,
	 */
	if (t1 == t2) {
		if (t1 == symbol_integer || t1 == symbol_float || is_fixed_type(t1)
	      || t1 == symbol_universal_real) return TRUE;
	}
	if (t1 == symbol_universal_integer)
		return (t2 == symbol_integer|| t2 == symbol_universal_integer);
	if (t1 == symbol_universal_real)
		return (is_fixed_type(t2) || t2 == symbol_float);
	return FALSE;
}

static int in_mult_types(Symbol t1, Symbol t2)			  /*;in_mult_types*/
{
	/* { [symbol_integer , symbol_integer ], 
	 * [symbol_float, symbol_float], 
	 * [symbol_dfixed, symbol_dfixed], 
	 * [symbol_universal_integer, symbol_universal_integer], 

	 * [symbol_universal_integer, symbol_integer ],
	 * [symbol_universal_real, symbol_universal_real], 
	 * [symbol_universal_real, symbol_float], 
	 * }
 	 */
	if (t1 == t2)
		return (t1 == symbol_integer || t1 == symbol_float || is_fixed_type(t1)
	      || t1 == symbol_universal_integer || t1 == symbol_universal_real);
	if (t1 == symbol_universal_integer && t2 == symbol_integer)
		return TRUE;
	if (t1 == symbol_universal_real)
		return (t2 == symbol_float);
	return FALSE;
}

static int in_mixed_mult_types(Symbol t1, Symbol t2)  /*;in_mixed_mult_types*/
{
	/* [symbol_dfixed, symbol_integer],
	 * [symbol_dfixed, symbol_universal_integer], 
	 * [symbol_universal_real, symbol_universal_integer], 
	 * [symbol_universal_real, symbol_integer]
	 */
	if (is_fixed_type(t1))
		return (t2 == symbol_integer || t2 == symbol_universal_integer);
	if (t1 == symbol_universal_real)
		return (t2 == symbol_universal_integer || t2 == symbol_integer);
	return FALSE;
}

static int in_mod_types(Symbol t1, Symbol t2)			  /*;in_mod_types*/
{
	/* [symbol_integer, symbol_integer], 
	 * [symbol_integer, symbol_universal_integer], 
	 * [symbol_universal_integer, symbol_integer], 
	 * [symbol_universal_integer, symbol_universal_integer]
	 */

	if (t1 == symbol_integer)
		return (t2 == symbol_integer || t2 == symbol_universal_integer);
	if (t1 == symbol_universal_integer)
		return (t2 == symbol_integer || t2 == symbol_universal_integer);
	return FALSE;
}

static int in_expon_types(Symbol t1, Symbol t2)			 /*;in_expon_types*/
{
	/* [symbol_integer , symbol_universal_integer], 
	 * [symbol_integer , symbol_integer ], 
	 * [symbol_float, symbol_integer ], 
	 * [symbol_float, symbol_universal_integer], 
	 * [symbol_universal_integer, symbol_universal_integer] 
	 * [symbol_universal_integer, symbol_integer ],
	 * [symbol_universal_real, symbol_integer ],
	 * [symbol_universal_real, symbol_universal_integer],
 	 */
	if (t1 == symbol_integer)
		return (t2 == symbol_integer || t2 == symbol_universal_integer);
	if (t1 == symbol_float)
		return (t2 == symbol_integer || t2 == symbol_universal_integer);
	if (t1 == symbol_universal_integer)
		return (t2 == symbol_integer || t2 == symbol_universal_integer);
	if (t1 == symbol_universal_real)
		return (t2 == symbol_integer || t2 == symbol_universal_integer);
	return FALSE;
}

static Symbol valid_arg_list(Symbol proc_name, Node arg_list_node)
															/*;valid_arg_list*/
{
	Tuple	formals, arg_list;
	Node	actual;
	Set		a_types;
	Symbol	t;
	Forset	fs1;
	Fortup	ft1;
	int		exists, i;
	Symbol	f;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  valid_arg_list");
	/* This procedure is called during the bottom-up phase of overloading
	 * resolution. It checks whether an argument list is compatible with
	 * the formals of a subprogram, and yields the return type of the
	 * subprogram if the answer is affirmative.
 	 * The arguments have already been processed by the first pass.
	 */

	formals = SIGNATURE(proc_name);
	arg_list = order_arg_list(arg_list_node, formals); /*Normalize arguments*/

	if (cdebug2 > 0)  TO_ERRFILE("valid arg list :  formals ");

	if (arg_list == (Tuple)0) return (Symbol)0;	   /* no match, or error*/

	/* Traverse signature and actuals, and verify that types match.*/

	FORTUPI(f=(Symbol), formals, i, ft1);
		actual = (Node) arg_list[i];
		if (actual == OPT_NODE) continue;	/* Default value exists.*/
		else a_types = N_PTYPES(actual);

		exists = FALSE;
		FORSET(t=(Symbol), a_types, fs1);
			if (compatible_types(TYPE_OF(f), t)) {
				exists = TRUE;
				break;
			}
		ENDFORSET(fs1);
		if (exists) 
			continue;
		else
			return (Symbol)0;
	ENDFORTUP(ft1);

	/* All arguments have a match.*/
	return (TYPE_OF(proc_name));
}

void complete_op_expr(Node expn, Symbol ctx_type) /*;complete_op_expr*/
{
	/* Complete the top-down pass of an expression with a predefined
	 * operator.
	 * For predefined operators, the signature of the operator does not
	 * fix the type of the arguments, because it only specifies a class
	 * of types. The precise type to be used is either imposed by context
	 * (this is the argument ctx_type) or is found by requiring consistency
	 * between the possible types of the arguments themselves.
	 */
#ifdef TBSN
	const comparison_ops = {
	'<', '<=', '>', '>=', '=', '/='
	};
#endif

	Node	o, args;
	Symbol	op_name;
	Tuple	arg_list;
	Node	arg1, arg2;
	Set		t_left, t_right, ok_types, univ;
	Symbol	ctx_root, t2, t1, isym, typ;
	Forset	fs1, fs2;


	o = N_AST1(expn);
	args = N_AST2(expn);
	op_name	  = N_UNQ(o);
	arg_list  = N_LIST(args);

	if (cdebug2 > 0) TO_ERRFILE("complete_op_expr:");

	if (tup_size(arg_list) == 1)
		arg_list = order_arg_list(args, unary_sig);
	else
		arg_list = order_arg_list(args, binary_sig);

	if (arg_list == (Tuple)0) return;
	N_LIST(args) = arg_list;      /* Normalize if named parameters. */

	if (tup_size( arg_list) == 2) {		/*Binary operators.*/
		arg1 = (Node) arg_list[1];
		arg2 = (Node) arg_list[2];
		t_left = N_PTYPES(arg1);
		t_right = N_PTYPES(arg2);

		typ = TYPE_OF(op_name);
		if (typ == symbol_universal_integer || typ == symbol_universal_real
	      || typ == symbol_universal_fixed
		  || (typ!=(Symbol)0 && is_fixed_type(typ)))  {
			ctx_root = root_type(ctx_type);

			if (ctx_type == symbol_universal_fixed) {
				/* Must have appeared in a conversion. Each argument must be of
	    		 * some fixed type. 
	    		 */
				t1 = ctx_type;		/* by default */
				FORSET(t1=(Symbol), t_left, fs1);
					if (compatible_types(t1, symbol_dfixed)) break;
				ENDFORSET(fs1);

				t2 = ctx_type;
				FORSET(t2=(Symbol), t_right, fs2);
					if (compatible_types(t2, symbol_dfixed)) break;
				ENDFORSET(fs1);
				/* TBSL: not catching ambiguity in these loops.*/
				resolve2(arg1, t1);
				resolve2(arg2, t2);
			}
			else if (op_name == symbol_mulfxi || op_name == symbol_mulifx
		      || op_name == symbol_divfxi || op_name == symbol_expi
		      || op_name == symbol_expfl) {
				/* For mixed mode fixed operations and  exponentiation,
				 * the  type  from  context  is imposed	on  the	 first
				 * argument. The second one must be INTEGER.
				 */
				if (op_name == symbol_mulifx) { /*permute arguments.*/
					Tuple tup= tup_new(2);
					tup[1] = (char *) arg2;
					tup[2] = (char *) arg1;
					N_LIST(args) = tup;
					arg1 = (Node) tup[1];
					arg2 = (Node) tup[2];
					op_name = symbol_mulfxi;
					N_UNQ(o) = symbol_mulfxi;
				}

				if (ctx_type == symbol_dfixed) {
					/* mixed mode expression in a context that does not
		    		* have an explicit fixed type: comparison or conversion.
		    		*/
					errmsg("invalid context for mixed-mode operation",
			    	  "4.5.5, 4.10", expn);
				}
				if (op_name == symbol_expfl && is_fixed_type(ctx_root)) {
					/* universal expression in fixed context: no ** .*/
					errmsg(
					  "Missing explicit conversion from universal_real value ",
					 	"4.5.6", expn);
				}
				resolve2(arg1, ctx_type);
				resolve2(arg2, symbol_integer);
				/*
				 * The second argument is not universal, yet the whole
				 * may be constant-foldable. Fold arg2, and if static
				 * make universal again.
				 */
				eval_static(arg2);
				if (N_KIND(arg2) == as_ivalue )
					N_TYPE(arg2) = symbol_universal_integer;
#ifdef TBSL
				/* TBSL (In C, will need explicit conversion)*/
#endif
			}
			else if (op_name == symbol_mulfli
			  || op_name == symbol_mulifl
			  || op_name == symbol_divfli) {
				/* These mixed mode operations appear in number declara-
				 * tions, in which case they are universal, or in a fixed
				 * type context.
				 */
				if (op_name == symbol_mulifl) { /* permute arguments.*/
					Tuple tup = tup_new(2);
					tup[1] = (char *) arg2;
					tup[2] = (char *) arg1;
					N_LIST(args) = tup;
					arg1 = (Node) tup[1];
					arg2 = (Node) tup[2];
					op_name = symbol_mulfli;
					N_UNQ(o) = symbol_mulfli;
				}
				if (ctx_root == symbol_universal_real)
					t2 = symbol_universal_integer;
				else if (is_fixed_type(ctx_root))
					/* universal expression in fixed context.*/
					t2 = symbol_integer;
				else {
					errmsg("Invalid context for mixed mode operation",
					  "4.5.5, 4.10", expn);
					N_KIND(expn) = as_opt;
					return;
				}
				resolve2(arg1, ctx_type);
				resolve2(arg2, t2);
			}
			else {
				/* For other  arithmetic operators, propagate  context
			 	 * type to arguments. 
 				 */
				resolve2(arg1, ctx_type);
				resolve2(arg2, ctx_type);
			}
			/* If the context is universal, evaluate the corresponding
			 * literal expression.
			 */
			if (in_univ_types(ctx_type ) || (is_fixed_type(ctx_root)
		      && N_KIND(arg1) == as_ivalue && N_KIND(arg2) == as_ivalue))
				literal_expression(expn);
			if ((op_name == symbol_mulfl || op_name == symbol_divfl)
		      && (is_fixed_type(ctx_root)) && (!is_fixed_type(ctx_type))) {
				/* These floating point operation may appear in some fixed
				 * type context if their constituents are literals. this is
				 * an error because the operation yields a universal_fixed
				 * quantity that must be explicitly converted If a conversion
				 * is present, the context type itself is symbol_dfixed.
				 */
				errmsg_l("Missing explicit conversion from ",
				  "universal_fixed value ", "4.5.5", expn);
			}
		}
		else if (typ == symbol_order_type ||  typ == symbol_discrete_type
		  ||  typ == symbol_boolean) {
			/* Equality, set or comparison  operators. Verify that  there  is
			 * only one possible type choice for both arguments. If both arg.
			 * are universal, we must choose a universal interpretation for
			 * each. Otherwise, the non-universal type is applied to both.
			 */
#ifdef TBSN
			/* it happens to be wrong.*/
		    /* In the case of an array compared to an aggregate, the array is
   	     	 * already constrained as it is an object.
   	     	 */
			need_constr_type = FALSE;
			exists = FALSE;
			if (N_KIND(arg1) == as_simple_name )  {
				arg1_name = N_UNQ(arg1);
				exists = TRUE;
			}
#endif
			ok_types = set_new(0);
			FORSET(t1=(Symbol), t_left, fs1);
				FORSET(t2=(Symbol), t_right, fs2);
					isym = intersect_types(t1, t2);
					if (isym!=(Symbol)0)  {
#ifdef TBSN
						if (N_KIND(arg1) == as_selector) {
							obj = N_AST1(arg1);
							s_node = N_AST2(arg1);
							selector = N_VAL(s_node);
							types1 = N_PTYPES(obj);
							FORSET( o_t =(Symbol), types1, fs1);
								if (is_access(o_t) )
									t = (Symbol) designated_type(o_t);
								else 
									t = o_t;
								if (is_record(t))
									decls = (Declaredmap)
									  declared_components(base_type(t));
								else if (is_task_type(t))
									decls = DECLARED(t);
								arg1_name = dcl_get(decls, selector);
								if(arg1_name != (Symbol)0
								  && compatible_types(TYPE_OF(arg1_name),isym)){
									exists = TRUE;
									break;
								}
							ENDFORSET(fs1); 
						}
						if (exists && NATURE(arg1_name) == na_obj 
			    	  	  && NATURE(base_type(TYPE_OF(arg1_name))) == na_array)
							need_constr_type = TRUE;
						if (need_constr_type)
							ok_types = set_with(ok_types, (char *) isym);
						else
							ok_types =
							  set_with(ok_types, (char *) base_type(isym));
#endif
						ok_types = set_with(ok_types, (char *) base_type(isym));
					}
				ENDFORSET(fs2);
			ENDFORSET(fs1);

			if (set_size( ok_types) ==  1)
				t1 = t2 = (Symbol) set_arb(ok_types);
			else {
				univ = set_new(0);
				FORSET(t1=(Symbol), ok_types, fs1);
					if (in_univ_types(t1))
						univ = set_with(univ, (char *) t1);
				ENDFORSET(fs1);
				if (set_size(univ) == 1)
					t1 = t2 = (Symbol) set_arb(univ);
				else {
					type_error(set_new1((char *)op_name),
				      (Symbol)0, set_size(ok_types), expn);
					return;
				}
			}
			if (is_limited_type(t1)
		      && (op_name !=symbol_in && op_name!=symbol_notin)) {
				errmsg_id("% not available on a limited type", op_name,
				  "7.4.2", o);
				return;
			}
			/* Now resolve each operand independently.*/

			resolve2(arg1, t1);
			/* The membership tests are not static but their arguments 
 			 * may be universal. Convert them to non-universal form for 
 			 * run-time evaluation. Also special case type mark as second arg.
 			 */
			if (op_name == symbol_in || op_name == symbol_notin) {
				if (t2 == symbol_universal_integer)
					specialize(arg1, symbol_integer);
				else if (t2 == symbol_universal_real)
					specialize(arg1, symbol_float);
				if (N_KIND(arg2) != as_simple_name)
					resolve2(arg2, t2);
				else
				/* type mark. Its type is of course its own name. */
				N_TYPE(arg2) = N_UNQ(arg2);
			}
			else			 /* resolve second argument */
				resolve2(arg2, t2);
			/* Comparison operators on  literal expressions are evaluated
			 * separately,  because their arguments are in universal form.
			 */
			if (in_comparison_ops(op_name ) && t1 == t2
		      && in_univ_types(t1))
				literal_expression(expn);
		}
		else if (typ == symbol_array_type) { /* Concatenation operator.*/
			if (op_name == symbol_cat) {
				resolve2 (arg1, ctx_type);
				resolve2 (arg2, ctx_type);
			}
			else {
				if (op_name == symbol_cat_ac) {
					resolve2 (arg1, ctx_type);
					resolve2 (arg2, component_type (ctx_type));
					eval_static(arg2);
				}
				else {
					if (op_name == symbol_cat_ca) {
						resolve2 (arg1, component_type (ctx_type));
						resolve2 (arg2, ctx_type);
						eval_static(arg1);
					}
					else {
						if (op_name == symbol_cat_cc) {
							resolve2 (arg1, component_type (ctx_type));
							eval_static(arg1);
							resolve2 (arg2, component_type (ctx_type));
							eval_static(arg2);
						}
					}
				}
			}
		}
		else {
			/* Other binary operators.*/
			resolve2(arg1, ctx_type);
			resolve2(arg2, ctx_type);
		}
	}
	else {
		/*Unary operator. Type of argument is that imposed by context.*/
		arg1 = (Node)arg_list[1];
		resolve2(arg1, ctx_type);
		/* if the argument to unary minus is universal real, the default
	     * operator is floating negation. If the context is fixed, adjust
		 * accordingly.
		 */
		if (op_name == symbol_subufl && is_fixed_type(ctx_type))
			N_UNQ(N_AST1(expn)) = symbol_subufx;
		if (in_univ_types(ctx_type))
			literal_expression(expn);
	}
}

void specialize(Node u_expr, Symbol ctx_type)  /*;specialize*/
{
	/* Convert a universal numeric into a specific one, if the context impo-
	 * ses a non-universal numeric type.
	 */

	int k;
	Const	v;
	Rational    ra;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  specialize");

	/*$$$$ Test should be more general.*/
	k = N_KIND(u_expr);
	if (k!=as_ivalue && k!=as_int_literal && k!=as_real_literal) return;

	if (!in_univ_types(ctx_type )) {
		v = (Const) N_VAL(u_expr);

		if (is_universal_integer(v)) {
			N_VAL(u_expr) =
			  (char *) int_const(int_toi(v->const_value.const_uint));
			if (arith_overflow)
				/* overflow has occurs during conversion to integer */
				create_raise(u_expr, symbol_constraint_error); 
			else 	 /* From universal to SETL integer*/
				N_TYPE(u_expr) = symbol_integer; 
		}
		else if (is_universal_real(v)) {
			if ( !is_fixed_type(root_type(ctx_type))) {
				/* N_VAL(u_expr)  =
				 *   (char *) real_const(rat_tor(v->const_value.const_rat,
				 *   ADA_REAL_DIGITS));
				 */
				ra  = RATV (v);

				/* the conversion from a rational to a real value will be
				 * correct is the rational value belongs to the real interval
				 */

				if (rat_lss (ra, rat_frr (ADA_MIN_REAL)) || 
	    			rat_gtr (ra, rat_frr (ADA_MAX_REAL))) {
					/* overflow occurs during conversion */
					/*N_VAL (u_expr) = const_new (CONST_OM); */
					create_raise(u_expr, symbol_constraint_error);
				}
				else {
					N_VAL(u_expr) =
					  (char *) real_const(rat_tor(v->const_value.const_rat,
		    		  ADA_REAL_DIGITS));
					N_TYPE(u_expr) = symbol_float; 
				}
			}
			else
				/* label universal constant with the specific fixed type */
				N_TYPE(u_expr) = ctx_type;
		}
		/*$$$ Do something about overflow in conversion.*/
	}
}

static Const check_constant_overflow(Const x)		/*;check_constant_overflow*/
{
	if is_const_om (x) 
		return x;
	else if (is_const_int (x)) {
		if ((INTV (x) < ADA_MIN_INTEGER) || (INTV(x) > ADA_MAX_INTEGER))
			return const_new (CONST_OM);
		else
			return x;
	}
	/* else if (is_const_uint (x)) {
	 * 	if (int_lss(UINTV (x), ADA_MIN_INTEGER_MP) || int_gtr(UINTV(x),
	 *    ADA_MAX_INTEGER_MP))
	 * 		return const_new (CONST_OM);
	 *  else return x;
	 * }
	 * else if (is_const_rat (x)) {
	 * 	if (rat_gtr (RATV (x), ADA_MAX_FLOAT) )
	 * 		return const_new (CONST_OM);
	 * 	else return x; 
	 */
	else if (is_const_fixed (x)) {
		if ((FIXEDV (x) < ADA_MIN_FIXED) || (FIXEDV(x) > ADA_MAX_FIXED))
			return const_new (CONST_OM);
		else
			return x;
	}
	else if (is_const_real (x)) {
		if ((REALV (x) < ADA_MIN_REAL) || (REALV(x) > ADA_MAX_REAL))
			return const_new (CONST_OM);
		else
			return x;
	}
	else 
		return x;
}

/*TBSL: check argument types, esp. in calls, for type_error */
static void literal_expression(Node expn)			  /*;literal_expression*/
{
	/* TBSL: need to always return uint case converting input
	 * cases of CONST_INT to long form - review this  ds 11 sep 84
	 */
	/* Use the arbitrary precision arithmetic package to evaluate an arith-
	 * metic expression whose arguments are literal. This routine is called
	 * in contexts that require a universal value, i.e. constant definitions.
	 * If the constituents are not universal, the expression is returned as
	 * is.
	 * Several attributes deliver a universal value, but are nevertheless
	 * evaluated at run-time. If these attributes are companion operands of
	 * literals, then these literals must be converted to non-universal form,
	 * real or integer depending on the attribute. Note that this conversion is
	 * never to a fixed point type, even for attributes of fixed points.
	 */

	Node	op_node, args_node, e1, e2;
	Tuple arg_list;
	Const op1, op2;
	int is_int;
	Symbol	sym;
	Const	ivalue;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  literal_expression");

	op_node = N_AST1(expn);
	args_node = N_AST2(expn);
	arg_list = N_LIST(args_node);

	if (tup_size( arg_list) == 2 ) {	/* binary operation.*/
		e1 = (Node) arg_list[1];
		e2 = (Node) arg_list[2];

		if (N_KIND(e1) == as_ivalue) {
			op1 = (Const) N_VAL(e1);
			/* extract possible values */
			if (N_KIND(e2) == as_ivalue) {
				op2 = (Const) N_VAL(e2);
				/* In the case of mixed mode operations on fixed types, the
	    		 * second argument is already folded to INTEGER. If a static
	    		 * evaluation is possible, make it into a universal object again
	    		 */
				if (is_const_int(op2)
				  && (is_const_rat(op1) || N_UNQ(op_node) == symbol_expi))
					op2 = uint_const(int_fri(INTV(op2)));
			}
			else {
				/* op2 is attribute expr. If first operand is integer, check
				 * its bounds . If it is a mixed operation, convert the first
				 * operand to the most precise floating type available.
				 */
				if(is_const_int(op1) || is_const_uint(op1))
					specialize(e1, symbol_integer);
				else
					specialize(e1, symbol_float);
				return;
			}
		}
		else {			/* op1 is attribute expr.*/
			if (N_KIND(e2) == as_ivalue) {
				op2 = (Const) N_VAL(e2);
				if(is_const_int(op2) || is_const_uint(op2))
					specialize(e2, symbol_integer);
				else
					specialize(e2, symbol_float);
				return;
			}
			else {			/* They both are.*/
				return;
			}
		}
	}
	else {
		e1 = (Node) arg_list[1];
		if (N_KIND(e1) != as_ivalue) {
			return;
		}
		else {
			op1 = (Const) N_VAL(e1);
		}
	}

	is_int = is_universal_integer(op1);
	if ((! is_int && !(is_const_rat(op1)))
	  || (tup_size(arg_list) == 2 && !(is_const_uint(op2))
	  && !(is_const_rat(op2)))) {
		return;
	}

	sym =N_UNQ(op_node);

	if (sym == symbol_addi) {
		const_check(op1, CONST_UINT);
		const_check(op2, CONST_UINT);
		ivalue = uint_const(int_add(UINTV(op1), UINTV(op2)));
	}
	else if (sym == symbol_addfl || sym == symbol_addfx) {
		const_check(op1, CONST_RAT);
		const_check(op2, CONST_RAT);
		ivalue = rat_const(rat_add(RATV(op1), RATV(op2)));
	}
	else if (sym == symbol_subi) {
	   const_check(op1, CONST_UINT);
	   const_check(op2, CONST_UINT);
	   ivalue = uint_const(int_sub(UINTV(op1), UINTV(op2)));
	}
	else if (sym == symbol_subfl|| sym == symbol_subfx) {
		const_check(op1, CONST_RAT);
		const_check(op2, CONST_RAT);
		ivalue = rat_const(rat_sub(RATV(op1), RATV(op2)));
	}
	else if (sym == symbol_muli) {
		const_check(op1, CONST_UINT);
		const_check(op2, CONST_UINT);
		ivalue = uint_const(int_mul(UINTV(op1), UINTV(op2)));
	}
	else if (sym == symbol_mulfl || sym == symbol_mulfx) {
		const_check(op1, CONST_RAT);
		const_check(op2, CONST_RAT);
		ivalue =  rat_const(rat_mul(RATV(op1), RATV(op2)));
	}
	else if (sym == symbol_mulfxi || sym == symbol_mulfli) {
		const_check(op1, CONST_RAT);
		const_check(op2, CONST_UINT);
		RATV(op1) = RATV(op1);
		ivalue = rat_const(rat_red(int_mul(num(RATV(op1)), UINTV(op2)),
		  den(RATV(op1))));
	}
	else if (sym == symbol_divfxi || sym == symbol_divfli) {
		const_check(op1, CONST_RAT);
		const_check(op2, CONST_UINT);
		if (int_eql(UINTV(op2),int_fri(0)))
			ivalue = const_new(CONST_OM);
		else
	   		ivalue = rat_const(rat_red(num(RATV(op1)), int_mul(den(RATV(op1)), 
			  UINTV(op2))));
	}
	else if (sym == symbol_divi) {
		const_check(op1, CONST_UINT);
		const_check(op2, CONST_UINT);
		ivalue = uint_const(int_quo(UINTV(op1), UINTV(op2)));
	}
	else if (sym == symbol_divfl || sym == symbol_divfx) {
		const_check(op1, CONST_RAT);
		const_check(op2, CONST_RAT);
		ivalue =  rat_const(rat_div(RATV(op1), RATV(op2)));
	}
	else if (sym == symbol_remi) {
		const_check(op2, CONST_UINT);
		if (int_eql(UINTV(op2),int_fri(0)))
			ivalue = const_new(CONST_OM);
		else
	    	ivalue = uint_const(int_rem(UINTV(op1), UINTV(op2)));
	}
	else if (sym == symbol_modi) {
		const_check(op2, CONST_UINT);
		if (int_eql(UINTV(op2),int_fri(0)))
			ivalue = const_new(CONST_OM);
		else {
			const_check(op1, CONST_UINT);
			const_check(op2, CONST_UINT);
			ivalue = uint_const(int_mod(UINTV(op1), UINTV(op2)));
		}
	}
	else if (sym == symbol_expi) {
		const_check(op2, CONST_UINT);
		if (int_lss(UINTV(op2),int_fri(0)))
	    	ivalue = const_new(CONST_OM); 
		else {
			const_check(op1, CONST_UINT);
			const_check(op2, CONST_UINT);
			ivalue = uint_const(int_exp(UINTV(op1), UINTV(op2)));
		}
	}
	else if (sym == symbol_expfl) {
		const_check(op1, CONST_RAT);
		const_check(op2, CONST_UINT);
		ivalue = rat_const(rat_exp(RATV(op1), UINTV(op2)));
	}
	else if (sym == symbol_eq) {
		ivalue = int_const(const_eq(op1, op2));
	}
	else if (sym == symbol_ne) {
		ivalue = int_const(!const_eq(op1, op2));
	}
	else if(sym == symbol_gt) {
		ivalue = int_const(const_gt(op1, op2));
	}
	else if (sym == symbol_lt) {
		ivalue = int_const(const_lt(op1, op2));
	}
	else if (sym == symbol_ge) {
		ivalue= int_const(const_ge(op1, op2));
	}
	else if (sym == symbol_le)  {
		ivalue = int_const(const_le(op1, op2));
	}
	else if (sym == symbol_addui || sym == symbol_addufl || sym==symbol_addufx){
		ivalue = op1;
	}
	else if(sym == symbol_subui) {
		const_check(op1, CONST_UINT);
		ivalue = uint_const(int_umin(UINTV(op1)));
	}
	else if (sym == symbol_subufl || sym == symbol_subufx) {
		const_check(op1, CONST_RAT);
		ivalue = rat_const(rat_umin(RATV(op1)));
	}
	else if (sym == symbol_absi) {
		const_check(op1, CONST_UINT);
		ivalue = uint_const(int_abs(UINTV(op1)));
	}
	else if (sym == symbol_absfl || sym == symbol_absfx) {
		const_check(op1, CONST_RAT);
		ivalue = rat_const(rat_abs(RATV(op1)));
	}
	else {	     /* Error: not a universal operator. */
		ivalue = const_new(CONST_OM); 
	}

	/* the previous calculus may have raised the overflow flag 
	 * if (arith_overflow) {
	 * 	arith_overflow = FALSE;
	 * 	ivalue =  const_new (CONST_OM);}
	 */

	ivalue = check_constant_overflow (ivalue);

	if (ivalue->const_kind == CONST_OM)
		create_raise(expn, symbol_constraint_error);
	else {
		N_KIND(expn) = as_ivalue;
		N_AST1(expn) = N_AST2(expn) = N_AST3(expn) = N_AST4(expn) = (Node)0;
		copy_span(e1, expn);
		N_VAL(expn) = (char *)ivalue;
	}
}

static Tuple order_arg_list(Node arg_list_node, Tuple sig) /*;order_arg_list*/
{
	/* Normalize an argument list (possibly containing named associations)
	 * according to the signature -sig-. Called for subprogram and operators.
	 */

	Tuple	arg_list;
	Node	actual, arg, choice_list, a_expr, choice_node, id_node;
	int		p, actuals_seen, i, first_named;
	Tuple	new_list;
	Tuple	named_args;
	Symbol	f_name;
	int found_name;
	int		exists;
	Fortup	ft1, ft2;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : order_arg_list");

	arg_list = N_LIST(arg_list_node);
	exists = FALSE;
	FORTUPI(actual=(Node), arg_list, p, ft1);
		if (N_KIND(actual) == as_choice_list) {
			exists = TRUE;
			break;
		}
	ENDFORTUP(ft1);
	if (exists) {
		first_named = p;
		exists = FALSE;
		for (i = p+1;i <= tup_size(arg_list); i++) {
			actual = (Node) arg_list[i];
			if (N_KIND(actual) != as_choice_list) {
				exists= TRUE;
				break;
			}
		}
		if (exists) {
			errmsg("No positional arguments can appear after named ones",
			  "6.4", actual);
			return (Tuple)0;
		}
	}
	else
		first_named = tup_size(arg_list) + 1;
	new_list = tup_new(first_named - 1);
	for (i = 1; i < first_named; i++)
		new_list[i] = arg_list[i];
	named_args = tup_new(tup_size(arg_list) - first_named + 1);
	for (i = first_named; i <= tup_size(arg_list); i++)
		named_args[i - first_named + 1] = arg_list[i];
	actuals_seen = first_named - 1;

	FORTUP(arg=(Node), named_args, ft1);
		choice_list = N_AST1(arg);
		a_expr = N_AST2(arg);
		exists = FALSE;
		if (tup_size(N_LIST(choice_list)) != 1) exists = TRUE;
		if (exists == FALSE) {
			FORTUP(choice_node = (Node), N_LIST(choice_list), ft2);
				if (N_KIND(choice_node) != as_choice_unresolved) {
					exists = TRUE;
					break;
				}
			ENDFORTUP(ft2);
		}
		if ( exists ) {
			errmsg("Invalid format for argument association", "6.4",
			  choice_list);
			return (Tuple)0;
		}
	ENDFORTUP(ft1);

	if (cdebug2 > 2) {
	}

	for (i = first_named; i <= tup_size(sig); i++) {
		f_name = (Symbol) sig[i];
		found_name = FALSE;

		FORTUP(arg=(Node), named_args, ft1);
			choice_list = N_AST1(arg);
			a_expr = N_AST2(arg);
			id_node = N_AST1((Node) (N_LIST(choice_list)[1]));
			if (streq(N_VAL(id_node), original_name(f_name))) {
				found_name = TRUE;
				break;
			}
		ENDFORTUP(ft1);

		if (found_name) {
			new_list = tup_with(new_list, (char *) a_expr);
			actuals_seen += 1;
			current_node = id_node;
			check_void(N_VAL(id_node));
		}
		else if ((Node) default_expr(f_name) != OPT_NODE)
			new_list = tup_with(new_list , (char *) OPT_NODE);
			/* Just a marker. Type is correct*/
		else			/* Name not present*/
			return (Tuple)0;
	}

	if (cdebug2 > 2) {
	}

	if (actuals_seen == tup_size(arg_list)		/* all actuals seen.*/
	  && tup_size(new_list) == tup_size(sig))  /* all formals matched */
		return(new_list);
	else return (Tuple)0;
}

void complete_arg_list(Tuple formals, Node arg_list_node) /*;complete_arg_list*/
{
	/* This procedure completes the formatting of the argument list of
	 * a subprogram or entry call. This is done in the second,
	 * top-down pass of overloading resolution. The argument list is
	 * reordered, the names of the formals are removed from the actuals,
	 * and default values are inserted in the place of missing parameters.
	 * Types have already been validated during pass one, and default para-
	 * meters are known to exist where needed.
	 */

	Tuple	arg_list, complete_args;
	int		i;
	Node	actual, default_node, default_copy;
	Fortup	ft1;
	Symbol	f;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : complete_arg_list");

	arg_list = order_arg_list(arg_list_node, formals); /* Normalize arguments*/
	/* if arg_list = om then ?*/

	complete_args = tup_new(0);
	/* Complete type resolution of each actual, and insert default expression
	 * for those that are missing; default expressions are known to exist.
	 */
	FORTUPI(f=(Symbol), formals, i, ft1);
		actual = (Node) arg_list[i];
		/* If no named association, a default value must be present,
		 * unless, there was a previous error.
		 */

		if (actual == OPT_NODE) {
			if (f != symbol_any_id) {
				default_node = (Node) default_expr(f);
				/* we assume all trees read in before use so node should be
				 * available.
				 */
				default_copy = copy_tree(default_node);
				if (fold_context) eval_static(default_copy);
				/* No constant folding in the middle of a conformance check */
				complete_args = tup_with(complete_args, (char *) default_copy);
			}
			else		/* previous error. */
				complete_args = tup_with(complete_args, (char *) OPT_NODE);
		}
		else {
			bind_arg(actual, TYPE_OF(f), NATURE(f), i);
			if (fold_context) eval_static(actual);
			complete_args = tup_with(complete_args, (char *) actual);
		}
	ENDFORTUP(ft1);
	N_LIST(arg_list_node) = complete_args;
}

static void bind_arg(Node actual, Symbol f_type, int f_mode, int i)/*;bind_arg*/
{
	/* Unlike the high-level version of Ada/Ed, the C front-end does not
	 * indicate what constraints, if any, must be applied to actual parameters.
	 * The job is done completely by the code generator, and sequences of
	 * constraint checks on entry and exit are emitted in gen_prelude and
	 * gen_postlude.
	 */

	Set a_types;
	Symbol	a_type;
	int out_c;
	Node	a;
	int		exists, may_others;
	Forset	fs1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  bind_arg");

	a_types = N_PTYPES(actual);

	/* One of its possible types must be compatible with the formal.*/
	exists = FALSE;
	FORSET(a_type=(Symbol), a_types, fs1);
		if(compatible_types(f_type, a_type)) {
			exists = TRUE;
			break;
		}
	ENDFORSET(fs1);
	if (!exists) /* assertion failure */
		chaos("assertion failure bind_arg");
	/* An out parameter may appear as the actual for another out parameter.*/
	out_c = out_context;
	out_context = (f_mode == na_out);
	/*  If the actual is an aggregate, there is no sliding for it, and named
	 *  associations can appear with "others" (cf. 4.3.2(6)).
	 */
	may_others = full_others;
	full_others = TRUE;

	resolve2(actual, f_type);
	apply_constraint (actual, f_type);

	/* verify that inout and out parameters are valid targets
	 * of assignments.
	 */
	if (N_KIND(actual) == as_qual_range || N_KIND(actual) == as_qual_index
	  || N_KIND(actual) == as_qual_discr || N_KIND(actual) == as_qual_aindex 
	  || N_KIND(actual) == as_qual_adiscr)
		a = N_AST1(actual);
	else
		a = actual;

	if (N_KIND(a) == as_insert)   /* case of an array conversion */
		a = N_AST1(a);
	if (f_mode != na_in && 
		/*
		 * check for conversion explicitly here, as is_variable() no
		 * longer allows conversions.
		 */
		!(is_variable(a) || N_KIND(a)==as_convert && is_variable(N_AST2(a)))) {
		errmsg_str_num("% actual parameter no. % in call is not a variable",
		  nature_str(f_mode), i, "6.4.1", actual);
	}

	if (is_scalar_type(f_type)) /* Convert from universal value if need be.*/
		specialize(actual, f_type);
	out_context = out_c;
	full_others = may_others;
}

static int in_comparison_ops(Symbol op)			/*;in_comparison_ops*/
{
	/* test for comparison operator */
	return (
	  op == symbol_eq || op == symbol_ne
	  || op == symbol_lt || op == symbol_gt
	  || op == symbol_le || op == symbol_ge );
}

static Set find_compatible_type(Set typ1, Set typ2) /*; find_compatible_type */
{
	/* return the types of typ1 (t1) such as the component type of t1 is 
	 * compatible with at least one type of typ2
	*/

	Set result;
	Symbol t1, t2;
	Forset fs1, fs2;

	result = set_new (0);

	FORSET (t1 = (Symbol), typ1, fs1);
		FORSET (t2 = (Symbol), typ2, fs2);
		if (compatible_types ((Symbol) component_type (t1), t2))
			result = set_with (result, (char *) base_type (t1)); 
		ENDFORSET (fs2);
	ENDFORSET (fs1);
	return result;
}

static Tuple valid_concatenation_type(Set typ1, Set typ2)
												/*;valid_concatenation_type*/
{
	/* Concatenation is performed by 4 distinct operators, corresponding to
	 * array-array, array-component, component-array, and component-component
	 * cases. If either operand is an aggregate, or if both operands are
	 * components, then the candidate resulting types are a subset of the
	 * one-dimensional array types that are in scope.
	 */

	Set arrays1, arrays2, arrays3, types, new_types;
	Set opns, types1, types2, types3;
	Symbol t1, t2, t3;
	Forset fs1, fs2, fs3;
	Tuple tup;
	int exist_composite_in_typ1, exist_composite_in_typ2;

	arrays1 = set_new (0);
	arrays2 = set_new (0);
	arrays3 = set_new (0);
	types = set_new (0);
	opns = set_new (0);

	FORSET  (t1=(Symbol), typ1, fs1);
		if (is_array (t1) && no_dimensions (t1) == 1)
			arrays1 = set_with (arrays1, (char *) base_type (t1));
	ENDFORSET (fs1);

	FORSET  (t1=(Symbol), typ2, fs1);
		if (is_array (t1) && no_dimensions (t1) == 1)
			arrays2 = set_with (arrays2, (char *) base_type (t1));
	ENDFORSET (fs1);

	FORSET  (t1=(Symbol), find_agg_types (), fs1);
		if (is_array (t1) && no_dimensions (t1) == 1)
			arrays3 = set_with (arrays3, (char *) base_type (t1));
	ENDFORSET (fs1);

	exist_composite_in_typ1 = FALSE;
	FORSET (t1 = (Symbol), typ1, fs1);
		if (NATURE (base_type (t1)) == na_aggregate)
		{ 
			exist_composite_in_typ1 = TRUE; 
			break; 
		}
	ENDFORSET (fs1);

	exist_composite_in_typ2 = FALSE;
	FORSET (t1 = (Symbol), typ2, fs1);
		if (NATURE (base_type (t1)) == na_aggregate)
		{ 
			exist_composite_in_typ2 = TRUE; 
			break; 
		}
	ENDFORSET (fs1);

	/* First we look for compatible arrays to concatenate. */
	if (exist_composite_in_typ1)
		types = arrays2; 
	else
	{
		FORSET (t1 = (Symbol), arrays1, fs1);
			FORSET (t2 = (Symbol), typ2, fs2);
				if (compatible_types (t1, t2))
					types = set_with (types, (char *) base_type (t1));
			ENDFORSET (fs2);
		ENDFORSET (fs1);
	}
	if (set_size (types) != 0)
		opns = set_with (opns, (char *)symbol_cat); 

	/* Next, look for aggregate or array type concatenated with compatible
	 * component.
	 */
	if (exist_composite_in_typ1)
		types1 = find_compatible_type (arrays3, typ2);
	else
		types1 = find_compatible_type (arrays1, typ2);

	if (set_size (types1) != 0)
	{ 
		types = set_union (types, types1);
		opns = set_with (opns, (char *)symbol_cat_ac);
	}

	/* The component-array case is similar. */
	if (exist_composite_in_typ2)
		types2 = find_compatible_type (arrays3, typ1);
	else
		types2 = find_compatible_type (arrays2, typ1);
	if (set_size (types2) != 0)
	{ 
		types = set_union (types, types2);
		opns = set_with (opns, (char *)symbol_cat_ca);
	}

	/* Next, both arguments may be the component type of some one-dimensional 
	 * array type, as in `A` & 'B'. Note that the arguments may still be
	 * arrays, and the result type be a one-dimensional array of arrays.
	 * The candidate resulting types are all array types in scope whose
	 * component types are compatible with both operands.
	 */

	types3 = set_new (0);
	FORSET (t1 = (Symbol), arrays3, fs1);
		FORSET (t2 = (Symbol), typ1, fs2);
			FORSET (t3 = (Symbol), typ2, fs3);
			if (compatible_types ((Symbol) component_type (t1), t2)
			  && compatible_types ((Symbol) component_type (t1), t3))
				types3 = set_with (types3, (char *)base_type (t1)); 
			ENDFORSET (fs3);
		ENDFORSET (fs2);
	ENDFORSET (fs1);

	if (set_size (types3) != 0) { 
		types = set_union (types, types3);
		opns = set_with (opns, (char *)symbol_cat_cc);
	}

	/* Finally, if both arguments are aggregates, the result can be an array
	 * type.
	 */
	if ((exist_composite_in_typ1)  && (exist_composite_in_typ2)) {
		types = set_with (types, (char *)symbol_array_type);
		opns = set_with (opns, (char *)symbol_cat);
	}

	new_types = set_new (0);
	FORSET (t1 = (Symbol), types, fs1);
		if (! is_limited_type (t1))
			new_types = set_with (new_types , (char *) t1);
	ENDFORSET (fs1);

	tup = tup_new (2);
	tup [1] = (char *) opns;
	tup [2] = (char *) new_types;

	return tup;
}
