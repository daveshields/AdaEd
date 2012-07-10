/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "hdr.h"
#include "vars.h"
#include "attr.h"
#include "arithprots.h"
#include "setprots.h"
#include "errmsgprots.h"
#include "nodesprots.h"
#include "machineprots.h"
#include "sspansprots.h"
#include "chapprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "evalprots.h"

/* Define DETAIL to break up some complicated expresssions into
 * several statements to assist debugging using interactive debugger
 */
#define DETAIL

static Const const_val(Symbol);
static Const eval_lit_map(Symbol);
static Const const_fold(Node);
static Const fold_unop(Node);
static Const fold_op(Node);
static Const fold_attr(Node);
static Const fold_convert(Node);
static Const eval_qual_range(Node, Symbol);
static Const eval_real_type_attribute(Node);
static Const check_overflow(Node, Const);
static int  *fl_mantissa(int);
static int *fl_emax(int);
static void insert_and_prune(Node, Const);
static Rational fx_max (Rational, Rational);
static Const test_expr(int);

extern Const int_const(), real_const(), rat_const();
extern ADA_MIN_INTEGER;

/* TBSL:provide proper link to ADA_SMALL_REAL*/
#define ADA_SMALL_REAL 0.1

static Const const_val(Symbol obj)								/*;const_val*/
{
	/* Return the constant value of the object if it has one;
	 * else return om.
	 * The constant value of a user-defined constant is derived from
	 * its SIGNATURE, when this is a constant value.
	 * The constant value of a literal is obtained from the literal map
	 * of its type.
	 */

	Tuple	sig;

	if (cdebug2 > 3) TO_ERRFILE("const_val");

	if (is_literal(obj)) return eval_lit_map(obj);

	sig = SIGNATURE(obj);
	if( is_constant(obj) && is_scalar_type(TYPE_OF(obj))
	  && N_KIND((Node)sig) == as_ivalue) {
		return (Const) N_VAL((Node)sig);
		/* TBSL: could be static but not constant folded yet. */
	}
	else return const_new(CONST_OM);
}

static Const eval_lit_map(Symbol obj)					/*;eval_lit_map*/
{
	Symbol	typ;
	Tuple	tup;
	int	i;

	typ = TYPE_OF(obj);
	tup = (Tuple) literal_map(typ);
	for (i = 1; i <= tup_size(tup); i += 2) {
		if (ORIG_NAME(obj) == (char *)0) continue;
		if (streq(tup[i], ORIG_NAME(obj)))
			return int_const((int)tup[i+1]);
	}
	return const_new(CONST_OM);
	/*(return literal_map(TYPE_OF(obj))(original_name(obj));*/
}

void eval_static(Node node)								/*;eval_static*/
{
	/* Top level evaluation of static expressions and constant folding. The
	 * recursive procedure const_fold is invoked, and a top-level range 
	 * check on numeric results is performed.
	 */
	/* If the node type is set to as_ivalue, the the N_VAL field will
	 * be a Const.
	 */
	Const	result;

	result = const_fold(node);
	if (result->const_kind != CONST_OM)
		check_overflow(node, result);
}

static Const const_fold(Node node)							/*;const_fold*/
{
	/* This recursive procedure evaluates expressions, when static.
	 * If node is static, its actual value	 is returned,  and the	node is
	 * modified to be an ivalue. Otherwise const_fold returns om, and node
	 * is	untouched. If the static  evaluation shows that the  expression
	 * would  raise an exception, a ['raise' exception] value  is produced
	 * and placed on the tree.
	 */

	Fortup ft1;
	Node expn, index_list, index, discr_range;
	Const	result;
	Node	opn;
	Node	n2, op_range;
	Symbol	sym, op_type;

	/* */
#define is_simple_value(t) ((t)->const_kind == CONST_INT \
	|| (t)->const_kind == CONST_UINT || (t)->const_kind == CONST_REAL)

	if (cdebug2 > 3) { }

	switch (N_KIND(node)) {
	case(as_simple_name):
		result = const_val(N_UNQ(node));
		break;
	case(as_ivalue):
		result = (Const) N_VAL(node);
		break;
	case(as_int_literal):
		/* TBSL: assuming int literal already converted check this Const*/
		result = (Const) N_VAL(node);
		break;
	case(as_real_literal):
		/*TBSL: assuming real literal already converted */
		result = (Const) N_VAL(node);
		break;
	case(as_string_ivalue):
		/* Will be static if required type has static low bound.*/
		/*		indx := index_type(N_TYPE(node));
		 *		[-, lo_exp, -] := signature(indx);
		 * * Move this test to the expander, once format of aggregates is known.
		 *		if is_static_expr(lo_exp) then
		 *		   lob := N_VAL(lo_exp);
		 *		   av  := [v : [-, v] in comp_list];
		 *		   result := check_null_aggregate(av, lob, indices, node);
		 *		   result := ['array_ivalue', [v: [-, v] in comp_list], 
		 *					   lob, lob + #comp_list - 1];
		 *		else
		 */
		result = const_new(CONST_OM);
		/*		end if;	*/
		break;
	case(as_character_literal):
		result = const_new(CONST_STR);
		break;
	case(as_un_op):
		result = fold_unop(node);
		break;
	case(as_in):
		opn = N_AST1(node);
		op_range = N_AST2(node);
		result = eval_qual_range(opn, N_TYPE(op_range));
		if (is_const_constraint_error(result))
			result = test_expr(FALSE);
		else if (!is_const_om(result))
			result = test_expr(TRUE);
		break;
	case(as_notin):
		opn = N_AST1(node);
		n2 = N_AST2(node);
		result = eval_qual_range(opn, N_TYPE(n2));
		if (is_const_constraint_error(result))
			result = test_expr(TRUE);
		else if (!is_const_constraint_error(result))
			result = test_expr(FALSE);
		break;
	case(as_op):
		result = fold_op(node);
		break;
	case(as_call):
		{
			int i;
			Tuple arg_list;
			Const arg;

			opn = N_AST1(node);
			result = const_new(CONST_OM);       /* in general not static */
			arg_list = N_LIST(N_AST2(node));    /* but can fold actuals. */
			for (i = 1; i <= tup_size(arg_list); i++)
				arg = const_fold((Node)arg_list[i]);
			if (N_KIND(opn) == as_simple_name) {
				sym = ALIAS(N_UNQ(opn));
				if (sym != (Symbol)0 && is_literal(sym))
					/* replace call by actual value of literal */
					result = eval_lit_map(sym);
			}
		}
		break;
	case(as_parenthesis):
		/* If the parenthesised expression is evaluable, return
		 * its value. Otherwise leave it parenthesised.
		 */
		opn = N_AST1(node);
		result = const_fold(opn);
		break;
	case(as_qual_range):
		opn = N_AST1(node);
		op_type = N_TYPE(node);
		result = eval_qual_range(opn, op_type);
		if (is_const_constraint_error(result)) {
			create_raise(node, symbol_constraint_error);
			result = const_new(CONST_OM);
		}
		break;
	case(as_qual_index):
		eval_static(N_AST1(node));
		result = const_new(CONST_OM);
		break;
	case(as_attribute):
	case(as_range_attribute):
		/* use separate procedure for C */
		result = fold_attr(node);
		break;
	case(as_qualify):
		if (fold_context)
			result = const_fold(N_AST2(node));
		else
			/* in the context of a conformance check, keep qualification.*/
			result = const_new(CONST_OM);
		break;
		/* Type conversion:
		 * /TBSL/ These conversions are not properly checked!
		 */
	case(as_convert):
		/* use separate procedure for C */
		result = fold_convert(node);
		break;
	case(as_array_aggregate):
		/* This is treated in the expander.*/
		result = const_new(CONST_OM);
		break;
	case(as_record_aggregate):
		result = const_new(CONST_OM);
		break;
	case(as_selector): /*TBSL Case for discriminants needed */
		expn = N_AST1(node);
		eval_static(expn);
		return const_new(CONST_OM);
	case(as_slice):
		expn = N_AST1(node);
		discr_range = N_AST2(node);
		eval_static(expn);
		eval_static(discr_range);
		return const_new(CONST_OM);
	case(as_row):	/* Not folded for now.*/
		/* p1 := check_const_val(op1);
		 * if is_value(op1) then
		 *    result := ['array_ivalue', [op1(2)], 1, 1];
		 * else
		 */
		return const_new(CONST_OM);
	case(as_index):
		expn = N_AST1(node);
		index_list = N_AST2(node);
		eval_static(expn);

		FORTUP(index = (Node), N_LIST(index_list), ft1)
		    eval_static(index);
		ENDFORTUP(ft1);
		return const_new(CONST_OM);
	default:
		result = const_new(CONST_OM);
	}
	if (result->const_kind != CONST_OM)
		insert_and_prune(node, result);

	return result;
}

static Const fold_unop(Node node)								/*;fold_unop*/
{
	Node	opn, oplist;
	Const	result, op1;
	int	op1_kind;
	Symbol	sym;

	opn = N_AST1(node);
	oplist = N_AST2(node);
	op1 = const_fold((Node) (N_LIST(oplist))[1]);

	if (is_const_om(op1)) return op1;

	op1_kind = op1->const_kind;

	sym = N_UNQ(opn);
	if (sym == symbol_addui) {
		/*  the "+" can be ignored if it is used as a unary op */
		result = op1;
	}
	else if (sym == symbol_addufl) {
		result = op1;
	}
	else if (sym == symbol_addufx) {
		result = op1;
	}
	else if (sym == symbol_subui ||
	    sym == symbol_subufl || sym == symbol_subufx) {
		if (is_simple_value(op1)) {
			if (sym == symbol_subui) {
				if (is_const_int(op1)) {
					if (INTV(op1) == ADA_MIN_INTEGER) {
						create_raise(node, symbol_constraint_error);
						result = const_new(CONST_OM);
					}
					else {
					   result = int_const(-INTV(op1));
					}
				}
				else if (is_const_uint(op1))
					result = uint_const(int_umin(UINTV(op1)));
				else chaos("eval:subui bad type");
			}
			else if (sym == symbol_subufl) {
				const_check(op1, CONST_REAL);
				result = real_const(-REALV(op1));
			}
		}
		else {
			const_check(op1, CONST_RAT);
			result= rat_const(rat_umin(RATV(op1)));
		}
	}
	else if ( sym == symbol_not) {
		if (is_simple_value (op1)) {
			if (op1_kind == CONST_INT)
				result = int_const(1-INTV(op1)); /*bnot in setl */
			else chaos("fold_unop: bad kind");
		}
		else {		/*TBSL*/
			result = const_new(CONST_OM);
		}
	}
	else if ( sym == symbol_absi ||
	    sym == symbol_absfl || sym == symbol_absfx) {

		if (is_simple_value(op1)) {
			if (sym == symbol_absi) {
				if (op1_kind == CONST_INT) result = int_const(abs(INTV(op1)));
				else if (op1_kind == CONST_UINT)chaos("fold_unit absi in uint");
				else chaos("fold_unop: bad kind");
			}
			else if (sym == symbol_absfl) {
				result = real_const(fabs(REALV(op1)));
			}
		}
		else {
			result= rat_const(rat_abs(RATV(op1)));
		}
	}
	return result;
}

static Const fold_op(Node node)									/*;fold_op*/
{
	Node	opn, arg1, arg2, oplist;
	Const	result, op1, op2, tryc;
	Symbol	sym, op_name;
	int	*uint;
	int	rm;
	Tuple	tup;
	int	res, overflow;

	opn = N_AST1(node);
	oplist = N_AST2(node);
	tup = N_LIST(oplist);
	arg1 = (Node) tup[1];
	arg2 = (Node) tup[2];
	op1 = const_fold(arg1);
	op2 = const_fold(arg2);
	op_name = N_UNQ(opn);

	/* If either operand raises and exception, so does the operation */
	if (N_KIND(arg1) == as_raise) {
		copy_attributes(arg1,  node);
		return const_new(CONST_OM);
	}
	if (N_KIND(arg2) == as_raise 
	  && op_name != symbol_andthen && op_name != symbol_orelse) {
		copy_attributes(arg2,  node);
		return const_new(CONST_OM);
	}

	if (is_const_om(op1) || (is_const_om(op2)
	  && (op_name != symbol_in || op_name != symbol_notin))) {
		return const_new(CONST_OM);
	}

	sym = op_name;

	if ( sym == symbol_addi || sym == symbol_addfl) {
		if (sym == symbol_addi) {
			res = word_add(INTV(op1), INTV(op2), &overflow);
			if (overflow) {
				create_raise(node, symbol_constraint_error);
				result = const_new(CONST_OM);
			}
			else result = int_const(res);
		}
		else
			result = real_const(REALV(op1) + REALV(op2));
	}
	else if ( sym == symbol_addfx) {
		const_check(op1, CONST_RAT);
		const_check(op2, CONST_RAT);
		result= rat_const(rat_add(RATV(op1), RATV(op2)));
	}
	else if ( sym == symbol_subi) {
		if (is_const_int(op1)) {
			if (is_const_int(op2)) {
				res = word_sub(INTV(op1), INTV(op2), &overflow);
				if (overflow) {
					create_raise(node, symbol_constraint_error);
					result = const_new(CONST_OM);
				}
				else result = int_const(res);
			}
			else {
				chaos("fold_op: subi operand types");
			}
		}
	}
	else if (sym == symbol_subfl) {
		result = real_const(REALV(op1) - REALV(op2));
	}
	else if ( sym == symbol_subfx) {
		const_check(op1, CONST_RAT);
		const_check(op2, CONST_RAT);
		result= rat_const(rat_sub(RATV(op1), RATV(op2)));
	}
	else if ( sym == symbol_muli) {
#ifdef TBSL
		-- need to check for overflow and convert result back to int if not
		    -- note that low-level setl is missing calls to check_overflow that
		    -- are present in high-level and should be in low-level as well
		    result = int_mul(int_fri(op1), int_fri(op2));
#endif
		/* until overflow check in */
		const_check(op1, CONST_INT);
		const_check(op2, CONST_INT);
		res = word_mul(INTV(op1), INTV(op2), &overflow);
		if (overflow) {
			create_raise(node, symbol_constraint_error);
			result = const_new(CONST_OM);
		}
		else result = int_const(res);
	}
	else if ( sym == symbol_mulfl) {
		const_check(op1, CONST_REAL);
		const_check(op2, CONST_REAL);
		if ((fabs(REALV(op1)) < ADA_SMALL_REAL)
		  || (fabs(REALV(op2)) < ADA_SMALL_REAL)) {
			result = real_const(0.0);
		}
		else if (log(fabs(REALV(op1))) + 
		    log(fabs(REALV(op2))) > ADA_MAX_REAL) {
			create_raise(node, symbol_constraint_error);
			return const_new(CONST_OM);
		}
		else
			result = real_const(REALV(op1) * REALV(op2));
	}
	else if ( sym == symbol_mulfx) {
		const_check(op1, CONST_RAT);
		const_check(op2, CONST_RAT);
		result = rat_const(rat_mul(RATV(op1), RATV(op2)));
	}
	else if (sym == symbol_mulfxi || sym == symbol_mulfli) {
		const_check(op1, CONST_RAT);
		const_check(op2, CONST_RAT);
		result = rat_const(rat_fri(int_mul(num(RATV(op1)), UINTV(op2)),
		  den(RATV(op1))));
	}
	else if (sym == symbol_mulifx) {
		const_check(op1, CONST_UINT);
		const_check(op2, CONST_RAT);
		result = rat_const(rat_fri(int_mul(UINTV(op1), num(RATV(op2))),
		  den(RATV(op2))));
	}
	else if (sym == symbol_divi) {
		if (INTV(op2)== 0) {
			create_raise(node, symbol_constraint_error);
			return const_new(CONST_OM);
		}
		result = int_const(INTV(op1) / INTV(op2));
	}
	else if (sym == symbol_divfl) {
		const_check(op2, CONST_REAL);
		if (fabs(REALV(op2)) < ADA_SMALL_REAL) {
			create_raise(node, symbol_constraint_error);
			return const_new(CONST_OM);
		}
		else if (fabs(REALV(op1)) < ADA_SMALL_REAL) {
			const_check(op1, CONST_REAL);
			result = real_const(0.0);
		}
		else if (log(fabs(REALV(op1))) -
		  log(fabs(REALV(op2))) >log(ADA_MAX_REAL)) {
			create_raise(node, symbol_constraint_error);
			return const_new(CONST_OM);
		}
		else {
			result = real_const(REALV(op1)
			    / REALV(op2));
		}
	}
	else if (sym == symbol_divfx) {
		/* TBSL: note that rnum(rat2) is in long integer format */
		if (int_eqz(num(RATV(op2)))) {
			create_raise(node, symbol_constraint_error);
			return const_new(CONST_OM);
		}
		result = rat_const(rat_div(RATV(op1), RATV(op2)));
	}
	else if (sym == symbol_divfxi ||  sym == symbol_divfli) {
		const_check(op1, CONST_RAT);
		if (is_const_int(op2)) {
			if (!INTV(op2)) {
				create_raise(node, symbol_constraint_error);
				return const_new(CONST_OM); }
			result = rat_const(rat_fri(num(RATV(op1)), int_mul(den(RATV(op1)),
			  int_fri(INTV(op2))))); }
/* Shouldn't be a rational
		else if (is_const_rat(op2)) {
			if (int_eqz(num(RATV(op2)))) {
				create_raise(node, symbol_constraint_error);
				return const_new(CONST_OM); }
			result = rat_const(rat_div(RATV(op1), RATV(op2))); }
*/
		else {
			const_check(op2, CONST_UINT);
			if (int_eqz(UINTV(op2))) {
				create_raise(node, symbol_constraint_error);
				return const_new(CONST_OM); }
			result = rat_const(rat_fri(num(RATV(op1)), int_mul(den(RATV(op1)),
			  UINTV(op2))));
		}
	}
	else if (sym == symbol_remi) {
		if (INTV(op2) == 0) {
			create_raise(node, symbol_constraint_error);
			return const_new(CONST_OM);
		}
		result = int_const(INTV(op1) - (INTV(op1) / INTV(op2)) * INTV(op2));
	}
	else if (sym == symbol_modi) {
		if (INTV(op2) == 0) {
			create_raise(node, symbol_constraint_error);
			return const_new(CONST_OM);
		}
		rm = INTV(op1) % INTV(op2);
		if ((rm == 0) || (INTV(op2) > 0))
			result = int_const(rm);
		else
			result = int_const(rm + INTV(op2));
	}
	else if (sym == symbol_expi) {
		if (INTV(op2) < 0) {
			create_raise(node, symbol_constraint_error);
			return const_new(CONST_OM);
		}
		else {
			if (is_const_int(op1))
				uint = int_fri(INTV(op1));
			else
				chaos("expi: bad kind");
			const_check(op2, CONST_INT);
			result = int_const(int_toi(int_exp(uint, int_fri(INTV(op2)))));
		}
	}
	else if (sym == symbol_expfl) {
		const_check(op1, CONST_REAL);
		const_check(op2, CONST_INT);
		if ((fabs(REALV(op1)) < ADA_SMALL_REAL)
		  || ((abs(INTV(op2)) * log (fabs( REALV(op1)))) > log(ADA_MAX_REAL))) {
			create_raise(node, symbol_constraint_error);
			return const_new(CONST_OM);
		}
		return const_new(CONST_OM);
#ifdef TBSL
		-- need to find C form for **
		    pow(x, y) is x**y with x an y both double.
		    result = op1 ** op2;
#endif
	}
	else if ((sym == symbol_cat) || (sym == symbol_cat_ca)
	  || (sym == symbol_cat_ac) || (sym == symbol_cat_cc)) {
		/*  /TBSL/ Bounds may not be correct!*/
		/*  [-, agg1, lb1, ub1] := op1;
		 *  [-, agg2, lb2, ub2] := op2;
		 *  agg := agg1 + agg2;
		 *  lb := lb1 min lb2;
		 */
		result = const_new(CONST_OM);
	}
	else if (sym == symbol_and || sym == symbol_or || sym == symbol_xor) {
		if (is_simple_value(op1)) {
			if (N_UNQ(opn) == symbol_and) {
				if (is_const_int(op1))
					result = int_const(INTV(op1)&&INTV(op2));
				else
					chaos("fold_unop: bad kind");
			}
			else if (N_UNQ(opn) == symbol_or) {
				if (is_const_int(op1))
					result = int_const(INTV(op1)||INTV(op2));
				else
					chaos("fold_unop: or bad kind");
			}
			else if (N_UNQ(opn) == symbol_xor) {
				result = test_expr((INTV(op1))!= (INTV(op2)));
			}
			else {
				chaos("ERROR IN ES99");
			}
		}
	}
	else if (sym == symbol_andthen || sym == symbol_orelse) {
		/* not static */
		result = const_new(CONST_OM);
	}
	else if (sym == symbol_eq) {
#ifdef TBSN
		if (is_universal_real(op1) && is_universal_real(op2))
			result = test_expr(rat_eql(op1, op2));
		else
			result = test_expr(op1 == op2);
#endif
		if (const_same_kind(op1, op2))
			return test_expr(const_eq(op1, op2));
		else return int_const(FALSE);
	}
	else if (sym == symbol_ne) {
#ifdef TBSN
		if (is_universal_real(op1) && is_universal_real(op2)) {
			result = test_expr(rat_neq(op1, op2));
		}
		else {
			/*TBSL: do we need two cases here */
			if (is_const_int(op1))
				result = int_const(INTV(op1) != INTV(op2));
			else if (is_const_real(op1))
				result = test_expr((REALV(op1) != REALV(op2)));
			else
				chaos("error in ne case in const_fold");
		}
#endif
		if (const_same_kind(op1, op2))
			return test_expr(const_ne(op1, op2));
		else return int_const(FALSE);
	}
	else if (sym == symbol_lt) {
		if (is_simple_value(op1)) {
#ifdef TBSN
			if (is_const_int(op1)) {
				result = int_const(INTV(op1) < INTV(op2));
			}
			else {
				if (is_const_real(op1)) {
					result = real_const(REALV(op1)
					    < REALV(op2));
				}
				else {
					chaos("fold_unop: lt bad kind ");
				}
			}
#endif
			if (const_same_kind(op1, op2))
				return test_expr(const_lt(op1, op2));
			else return int_const(FALSE);
		}
		/*TBSL	 need array types */
		else if (is_const_rat (op1) && is_const_rat (op2)) {
			result = test_expr(rat_lss (RATV (op1), RATV (op2))); 
		}
		else {
			result = const_new(CONST_OM); 
		}
	}
	else if (sym == symbol_le) {
		if (is_simple_value(op1)) {
#ifdef TBSN
			if (is_const_int(op1)) {
				result = int_const(INTV(op1) <= INTV(op2));
			}
			else if (is_const_real(op1)) {
				result = real_const(REALV(op1) <= REALV(op2));
			}
			else {
				chaos("fold_op: le bad kind");
			}
#endif
			if (const_same_kind(op1, op2))
				return test_expr(const_le(op1, op2));
			else return int_const(FALSE);
		}
		else {	/*TBSL need array types */
			if (is_const_rat (op1) && is_const_rat (op2))
				result = test_expr(rat_leq (RATV (op1), RATV (op2))); 
			else
				result = const_new(CONST_OM); 
		}
	}
	else if (sym == symbol_gt) {
		if (is_simple_value(op1)) {
#ifdef TBSN
			if (is_const_int(op1)) {
				result = int_const(INTV(op1) > INTV(op2));
			}
			else if (is_const_real(op1)) {
				result = real_const(REALV(op1)
				    > REALV(op2));
			}
			else {
				chaos("fold_op: gt bad kind");
			}
#endif
			if (const_same_kind(op1, op2))
				return test_expr(const_gt(op1, op2));
			else return int_const(FALSE);
		}
		else {	/*TBSL need array types */
			if (is_const_rat (op1) && is_const_rat (op2))
				result = test_expr(rat_gtr (RATV (op1), RATV (op2))); 
			result = const_new(CONST_OM);
		}
	}
	else if (sym == symbol_ge) {
		if (is_simple_value(op1)) {
#ifdef TBSN
			if (is_const_int(op1))
				result = int_const(INTV(op1) >= INTV(op2));
			else if (is_const_real(op1))
				result = real_const(REALV(op1) >= REALV(op2));
			else
				chaos("fold op ge bad kind");
#endif
			if (const_same_kind(op1, op2))
				return test_expr(const_ge(op1, op2));
			else
				return int_const(FALSE);
		}
		else {	/*TBSL need array types */
			if (is_const_rat (op1) && is_const_rat (op2))
				result = test_expr(rat_geq (RATV (op1), RATV (op2))); 
			result = const_new(CONST_OM);
		}
	}
	else if (sym == symbol_in || sym == symbol_notin) {
		specialize(arg1, N_TYPE(arg2));	 /* ?? */
		/* check whether this is correct, SETL is TYPE_OF, which is WRONG!!*/
		if (N_KIND(arg2) != as_simple_name) {
			result = const_new(CONST_OM); /* Could do better. */
		}
		else {
			tryc = eval_qual_range(opn, N_UNQ(arg2));
			if (is_const_constraint_error(tryc))
				result = test_expr(op_name == symbol_notin);
			else if (!is_const_om(tryc))
				result= test_expr(op_name == symbol_in);
		}

	}
	else {
		printf("bad operator symbol: %s\n", nature_str(NATURE(sym)));
		chaos("fold_op: bad operator");
	}
	return result;
}

static Const fold_attr(Node node)		/*;fold_attr*/
{
	Node	attr_node, typ_node, arg_node, f_node, l_node, l_n, h_n;
	Symbol	typ1;
	int		attrkind, is_t_n, rv, i, len, max;
	Const	first, last, op1, result, lo, hi;
	Tuple	tsig, sig, l;
	Span	save_span;

	attr_node = N_AST1(node);
	typ_node = N_AST2(node);
	arg_node = N_AST3(node);

	/* Try to fold the prefix of the attribute*/
	eval_static(typ_node);
	/*attr = N_VAL(attr_node);  -- should be dead  3-13-86 ds */
	attrkind = (int) attribute_kind(node);
	if (N_KIND(typ_node) != as_simple_name) {
		/*Not for attribute COUNT. beware!*/
		typ1 = N_TYPE(typ_node);
	}
	else {
		typ1 = N_UNQ(typ_node);
	}
	is_t_n = is_type_node(typ_node);
	/* For array attributes, we establish whether it is being
	 * applied to an object or  to a type. The two operations
	 *  are distinguished in the interpreter by prefix O_ or T_
	 */
	if ((attrkind == ATTR_T_FIRST || attrkind == ATTR_T_LAST
	  || attrkind == ATTR_T_RANGE || attrkind == ATTR_T_LENGTH )
	  && can_constrain(typ1) ) {

			errmsg( "attribute cannot be applied to unconstrained array type",
			  "3.6.2", attr_node);
	}
	else if (attrkind == ATTR_T_SIZE || attrkind == ATTR_O_SIZE) {
        node = size_attribute(node);
        if (N_KIND(node) == as_ivalue) {
            return (Const) N_VAL(node);
		}
        else {
            return const_new(CONST_OM);
		}
	}
	else if (attrkind == ATTR_BASE) {
		save_span = get_left_span(node);
		N_KIND(node) = as_simple_name;
		/* clear attribute code so won't be taken as string*/
		N_VAL(node) = (char *)0;
		N_UNQ(node)	 = base_type(typ1);
		set_span(node, save_span);
		return const_new(CONST_OM);
	}

	if (!is_t_n)return const_new(CONST_OM);
	/* This was needed in the high level, to prevent extra
	 * folding in non-static cases. It may be superfluous here
	 */
	/* Attributes that are functions take the base type */
	if (attrkind == ATTR_BASE || attrkind == ATTR_POS || attrkind == ATTR_PRED
	  ||attrkind == ATTR_SUCC || attrkind == ATTR_VAL
	  || attrkind == ATTR_VALUE) {
		N_UNQ(typ_node) = base_type(typ1);
	}
	if (arg_node != OPT_NODE) {
		op1 = const_fold(arg_node);
		if (is_const_om(op1))return const_new(CONST_OM);
	}
	/* They are evaluable statically only if the subtype typ1
	 * itself is static.
	 */
	if (is_type(typ1) && is_static_subtype(typ1)
	  || is_task_type(TYPE_OF(typ1))
	  || attrkind == ATTR_T_CONSTRAINED || attrkind == ATTR_O_CONSTRAINED) {
		;    /* try to evaluate */
	}
	else {
		return const_new(CONST_OM); /* not static (RM 4.9 (8)*/
	}
	if (is_generic_type(typ1))	return const_new(CONST_OM);

	if (is_static_subtype(typ1)) {
		tsig = SIGNATURE(typ1);
		f_node = (Node) tsig[2];
		l_node = (Node) tsig[3];
		first = const_fold(f_node);
		last = const_fold(l_node);
	}

	/* Attributes of SCALAR types or ARRAY types: */

	if (attrkind == ATTR_O_FIRST || attrkind == ATTR_T_FIRST)
		result = first;
	else if (attrkind == ATTR_O_LAST || attrkind == ATTR_T_LAST)
		result = last;
	else if ( attrkind == ATTR_O_LENGTH || attrkind == ATTR_T_LENGTH
	  || attrkind == ATTR_O_RANGE || attrkind == ATTR_T_RANGE)
		result = const_new(CONST_OM);
	/* Attributes of DISCRETE types: */
	else if (attrkind == ATTR_IMAGE) {
		Symbol btyp1;
		char *image;
		Tuple tup;
		int tsize;

		btyp1 = root_type(typ1);

		image = emalloct(10, "fold-attr");
		if (btyp1 == symbol_integer) {
			const_check(op1, CONST_INT);
			if (INTV(op1) >= 0) sprintf(image, " %d", INTV(op1));
			else sprintf(image, "%d", INTV(op1));
		}
		else {
			/* image := 
			 *   if exists [nam, v] in literal_map(btyp1) | op1 = v
			 *       then nam else '' end;
			 */
			image = "";
			tup = (Tuple) literal_map(btyp1);
			tsize = tup_size(tup);
			for (i = 1; i <= tsize; i += 2) {
				const_check(op1, CONST_INT);
				if ((int)tup[i+1] == INTV(op1)) {
					image = strjoin(tup[i], "");
					break;
				}
			}
		}
		N_KIND(node) = as_string_ivalue;
		/* N_VAL(node)	 = [abs c : c in image]; */
		tsize = strlen(image);
		tup = tup_new(tsize);
		for (i = 1; i <= tsize; i++)
			tup[i] = (char *) image[i-1];

		if (N_AST1_DEFINED(N_KIND(node))) N_AST1(node) = (Node) 0;
		if (N_AST2_DEFINED(N_KIND(node))) N_AST2(node) = (Node) 0;
		if (N_AST3_DEFINED(N_KIND(node))) N_AST3(node) = (Node) 0;
		if (N_AST4_DEFINED(N_KIND(node))) N_AST4(node) = (Node) 0;
		N_VAL(node) = (char *) tup;
		result = const_new(CONST_OM);
	}
	else if (attrkind == ATTR_VALUE) {
		chaos("value attrobute (eval.c)");
	}
	else if (attrkind == ATTR_POS) {
		const_check(op1, CONST_INT);
		result = uint_const(int_fri(INTV(op1)));	/*$ES10*/
		/* result = int_const(int_fri(op1)); */	      /*$ES10*/
	}
	else if (attrkind == ATTR_VAL || attrkind == ATTR_PRED
	  || attrkind == ATTR_SUCC) {
		const_check(op1, CONST_INT);
		rv = INTV(op1);
		sig = SIGNATURE(base_type(typ1));
		if (sig != (Tuple)0) {
			l_n = (Node) sig[2];
			h_n = (Node) sig[3];
		}
		else {
			l_n = (Node) 0;
			h_n = (Node) 0;
		}
		lo = const_fold(l_n);
		hi = const_fold(h_n);
		if (is_const_om(lo) || is_const_om(hi)) {
			return const_new(CONST_OM);
		}
		if (attrkind == ATTR_PRED) {
			const_check(lo, CONST_INT);
			if (rv > INTV(lo)) rv -= 1;
			else {
				create_raise(node, symbol_constraint_error);
				return const_new(CONST_OM);
			}
		}
		else if (attrkind == ATTR_SUCC) {
			const_check(hi, CONST_INT);
			if (rv < INTV(hi)) rv += 1;
			else {
				create_raise(node, symbol_constraint_error);
				return const_new(CONST_OM);
			}
		}
		else if (attrkind == ATTR_VAL) {
			const_check(lo, CONST_INT);
			const_check(hi, CONST_INT);
			if (rv < INTV(lo) || rv > INTV(hi)) {
				create_raise(node, symbol_constraint_error);
				return const_new(CONST_OM);
			}
		}
		result = int_const(rv);
	}
	else if (attrkind == ATTR_WIDTH) {
		int first_val, last_val, max_val;

		if (root_type(typ1) == symbol_integer) {
			if (is_const_om(first) || is_const_om(last))
				chaos("eval WIDTH: unexpected const_kind");
			const_check(first, CONST_INT);
			const_check(last, CONST_INT);
			/* In the case of a null range the Width is defined as 0.
			 * Otherwise it is defined as the maximum IMAGE length for
			 * all values of the subtype.
			 */
			if (INTV(first) > INTV(last))
				result = uint_const(int_fri(0));
			else {
				char *val_str = emalloct(10, "fold-attr-1");
				first_val = abs(INTV(first));
				last_val  = abs(INTV(last));
				max_val = (first_val > last_val ? first_val : last_val);
				sprintf(val_str, " %d", max_val);
				result = uint_const(int_fri(strlen(val_str)));
				efreet(val_str, "eval-fold-rat");
			}
		}
		else {
			/*   Must find longest name in enumeration subtype.  */
			int v;
			l = (Tuple) literal_map(root_type(typ1));
			max = 0;
			first_val = abs(INTV(first));    /* bounds of subtype */
			last_val  = abs(INTV(last));
			for (i = 1; i <= tup_size(l); i += 2) {
				len = strlen(l[i]);
				v = (int)l[i+1];
				if (len > max && v >= first_val && v <= last_val)
					max = len;
			}
			result = uint_const(int_fri(max));
		}
	}

	/* Miscellaneous attributes. */

	/* The following  attributes are  of type universal integer.
	 * The current system ignores them, and passes them to the expander. 
	 */

	else if (attrkind == ATTR_POSITION || attrkind == ATTR_FIRST_BIT
	  || attrkind == ATTR_LAST_BIT || attrkind == ATTR_STORAGE_SIZE) {
		result = const_new(CONST_OM);
	}
	else if (attrkind == ATTR_O_CONSTRAINED || attrkind == ATTR_T_CONSTRAINED) {
		/* Attribute is true on constants and on -in- parameters */
		if ((typ1 != (Symbol) 0) &&
		    NATURE(typ1) == na_constant || NATURE(typ1) == na_in) {
			result = int_const(1);
		}
		else if (!is_generic_type(typ1)) {
			/* it is false for private  types with discriminants.  */
			result = int_const( !(is_record(typ1) && has_discriminants(typ1)
			  && NATURE(typ1) != na_subtype));
		}
		else {		/* run-time check */
			result = const_new(CONST_OM);
		}
	}
	else if (attrkind == ATTR_ADDRESS || attrkind == ATTR_TERMINATED 
	  || attrkind == ATTR_CALLABLE) {
		result = const_new(CONST_OM);
	}
	else {
		/* Attributes of FIXED and FLOATing point types:*/
		result = eval_real_type_attribute(node);
	}
	return result;
}

static Const fold_convert(Node node)						/*;fold_convert*/
{
	Node	typ2_node, opd_node;
	Symbol	typ1, typ2; /* type2 is target type */
	Const	opd, result;

	typ2_node = N_AST1(node);
	opd_node = N_AST2(node);
	typ1 = root_type(N_TYPE(opd_node));
	typ2 = root_type(N_UNQ(typ2_node));
	opd = const_fold(opd_node);
	if (is_const_om(opd)) {
		return const_new(CONST_OM);
	}
	if (typ1 == symbol_integer) {
		if (typ2 == symbol_integer) {
			result = opd;
		}
		else if (typ2 == symbol_float) {
			const_check(opd, CONST_INT);
			result = real_const((float)INTV(opd));
		}
		else if (typ2 == symbol_universal_integer)	{
			const_check(opd, CONST_INT);
			result	= uint_const(int_fri(INTV(opd)));
		}
		else if (typ2 == symbol_universal_real
		  || typ2 == symbol_universal_fixed || typ2 == symbol_dfixed) {
			if (is_const_int(opd)) {
				result = rat_const(rat_fri(int_fri(INTV(opd)), int_fri(1)));
			}
			else if (is_const_uint(opd)) {
				result = rat_const(rat_fri(UINTV(opd), int_fri(1)));
			}
			else
				chaos("const wrong type (eval.c)");
		}
		else
			result = const_new(CONST_OM);
	}
	else if (typ1 == symbol_float) {
		if (typ2 == symbol_integer || typ2 == symbol_universal_integer) {
			Rational z;
			int *x, *y;
			const_check(opd, CONST_REAL);
			z = rat_frr((double)(REALV(opd) + 0.5));
			x = num(z);
			y = den(z);
			result = uint_const(int_quo(x, y));
		}
		else if (typ2 == symbol_float) {
			result = opd;
		}
		else if (typ2 == symbol_dfixed || typ2 == symbol_universal_real
		  || typ2 == symbol_universal_fixed) {
			result = rat_const(rat_frr((double)REALV(opd)));
		}
		else
			result = const_new(CONST_OM);
	}
	else if (typ1 == symbol_universal_integer) {
		if (typ2 == symbol_integer)
/*
			result = opd;
*/
			result = int_const(int_toi(UINTV(opd)));
		else if (typ2 == symbol_float) {
			/* result = [opd, 1]; */
			/*	result = real_const((float) UINTV(opd)); */
			/*result = rat_const(rat_new(UINTV(opd), int_fri(1))); */
			result = const_new (CONST_OM);
		}
		else if (typ2 == symbol_universal_integer) {
			result = opd;
		}
		else if ( typ2 == symbol_universal_real ||
		    typ2 == symbol_universal_fixed ||
		    typ2 == symbol_dfixed) {
			result = rat_const(rat_fri(UINTV(opd), int_fri(1)));
		}
		else
			result = const_new(CONST_OM);
	}
	else if (typ1 == symbol_universal_real || typ1 == symbol_universal_fixed
	  || typ1 == symbol_dfixed) {

		if (typ2 == symbol_float) {
			result = real_const (rat_tor (RATV (opd), ADA_REAL_DIGITS));
			if (arith_overflow) {
				arith_overflow = FALSE;
				create_raise (node, symbol_constraint_error);
				result = const_new (CONST_OM);
			}
		}
		else if (typ2 == symbol_universal_real
		  || typ2 == symbol_universal_fixed || typ2 == symbol_dfixed) {
			result = opd;
		}
		else if (typ2 == symbol_integer) {
			const_check(opd, CONST_RAT);
			result = int_const(rat_toi(RATV(opd)));
		}
		else
			result = const_new(CONST_OM);
	}
	else 
		result = const_new(CONST_OM);

	return result;
}

static Const eval_qual_range(Node op1, Symbol op_type)		/*;eval_qual_range*/
{
	/* This has been separated from the main body of const_fold because
	 * it is used for two differents operators: 'qual_range' proper,
	 * and 'in' and 'notin'
	 *
	 * If the expression is not static it return the former expression expn.
	 * If the expression evaluates to a ['raise', 'CONSTRAINT_ERROR'] because
	 * op1 is not in the range op2, it returns the string 'contraint_error'
	 * without emitting any warning; this is left to the caller
 	* responsibility.
 	*/
	Node	lo, hi;
	Const	op1_val, lo_val, hi_val;
	int		c_error;
	Tuple	numcon;
	Rational	rop1_val;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : eval_qual_range");

	op1_val = const_fold(op1);
	if (op1_val->const_kind == CONST_OM)
		return const_new(CONST_OM);

	/* May just be a type name. */
	if (is_scalar_type(op_type)) {
		numcon = SIGNATURE(op_type);
		if (numcon != (Tuple)0) {
			lo = (Node) numcon[2];
			hi = (Node) numcon[3];
		}
		else {
			lo = (Node) 0;
			hi = (Node) 0;
		}
	}
	else
		return const_new(CONST_OM);

	/* If the argument is universal, convert it to
	 * standard representation. A qual_range indicates
	 * a constrained type, i.e. non-universal.
	 */

	if (is_universal_integer(op1_val)) {
		const_check(op1_val, CONST_UINT);
		op1_val = int_const(int_toi(UINTV(op1_val)));
		if (arith_overflow) {
			arith_overflow = 0;
			return const_new(CONST_CONSTRAINT_ERROR);
		}
	}
	else if (is_universal_real(op1_val)
	  && (!is_fixed_type(root_type(op_type)))) {
		const_check(op1_val, CONST_RAT);
		op1_val = real_const(rat_tor(RATV(op1_val), ADA_REAL_DIGITS));
		if (arith_overflow) {
			arith_overflow = FALSE;
			return const_new(CONST_CONSTRAINT_ERROR);
		}
	}
	if (N_KIND(lo) != as_ivalue || N_KIND(hi) != as_ivalue) {
		return const_new(CONST_OM);
	}
	else {
		lo_val = (Const) N_VAL(lo);
		hi_val = (Const) N_VAL(hi);
	}
	/* The overflow test done here in SETL version is done above after
	 * calls to arith routines in C version 
	 */

	if (op_type == symbol_integer || op_type == symbol_float
	  || op_type == symbol_dfixed || op_type == symbol_character
	  || NATURE(op_type) == na_enum) {
		/*    Predefined types: value is already known to be in range.*/
		return op1_val;
	}
	else {
		/* At this point everything is known to be constant.
		 * If the constraint is obeyed, return the value without
		 * a range qualification. Otherwise emit a constraint
		 * exception.
		 */

		/* c_error =	 ( root_type(op_type) != symbol_dfixed ?
		 * (op1_val < lo_val) || (op1_val > hi_val)
		 */
		if (is_fixed_type(root_type(op_type))) {
			if (op1_val->const_kind == CONST_RAT) {
				const_check(op1_val, CONST_RAT);
				const_check(lo_val, CONST_RAT);
				const_check(hi_val, CONST_RAT);
				c_error = (rat_lss(RATV(op1_val), RATV(lo_val))
				  || rat_gtr(RATV(op1_val), RATV(hi_val)));
			}
			else if (op1_val->const_kind == CONST_REAL) {
				rop1_val = rat_frr(REALV(op1_val));
				const_check(lo_val, CONST_RAT);
				const_check(hi_val, CONST_RAT);
				c_error = (rat_lss(rop1_val, RATV(lo_val))
				  || rat_gtr(rop1_val, RATV(hi_val)));
			}
		}
		else if (op1_val->const_kind == CONST_INT) {
			const_check(op1_val, CONST_INT);
			const_check(lo_val, CONST_INT);
			const_check(hi_val, CONST_INT);
			c_error = (INTV(op1_val) < INTV(lo_val))
			  || (INTV(op1_val) > INTV(hi_val));
		}
		else if (op1_val->const_kind == CONST_REAL) {
			const_check(op1_val, CONST_REAL);
			const_check(lo_val, CONST_REAL);
			const_check(hi_val, CONST_REAL);
			c_error = (REALV(op1_val) < REALV(lo_val))
			  || (REALV(op1_val) > REALV(hi_val));
		}
		if (c_error) {
			return const_new(CONST_CONSTRAINT_ERROR);
		}
		else {
			return op1_val;
		}
	}
}

static Const eval_real_type_attribute(Node node)  /*;eval_real_type_attribute*/
{
	/*
	 *    Static evaluation of real types characteristics
	 *    ===============================================
	 */

	Node	attr_node, arg_node, lo, hi, precision;
	Const	result, precision_const;
	Tuple	sig;
	int		kind, attrkind, static_bounds;
	int		fl_digits;
	Rational	delta, fx_low, fx_high, xdelta, small;
	/* the following are macros in SETL, and should eventually be converted */

#define rat_1 rat_fri(int_fri(1), int_fri(1))
#define rat_2 rat_fri(int_fri(2), int_fri(1))

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : eval_real_type_attribute");

	attr_node = N_AST1(node);
	arg_node = N_AST2(node);
	result = const_new(CONST_OM);
	sig = SIGNATURE(N_UNQ(arg_node));
	kind = (int) sig[1];
	/*
	 *    Part A : FLOATING POINT REAL
	 *
	 *    For a floating point real type FL, we have the following
	 *    basic informations:
	 *	  digits  (SETL_integer)
	 *	  fl_high (SETL_real)
	 *	  fl_low  (SETL_real)
	 */

	if (kind == CONSTRAINT_DIGITS) {
		lo = (Node) sig[2];
		hi = (Node) sig[3];
		precision = (Node) sig[4];
		precision_const = (Const) N_VAL(precision);
		const_check(precision_const, CONST_INT);
		fl_digits = INTV(precision_const);
		attrkind = (int) attribute_kind(node);
		/*
		 *
		 *	 FL'DIGITS    --> universal_integer
		 *
		 *	      The minimum number of significant decimal digits.
		 */
		if (attrkind == ATTR_DIGITS) {
			result = uint_const(int_fri(fl_digits));
		}
		/*
		 *
		 *	 FL'MANTISSA  --> universal_integer
		 *
		 *	      The minimum number of binary digits required for DIGITS:
		 *		    ceil(fl_digits*log(10)/log(2))+1)
		 *
		 */

		else if (attrkind == ATTR_MANTISSA) {
			result = uint_const(fl_mantissa(fl_digits));
		}
		/*
		 *	 FL'EPSILON   --> universal_real
		 *
		 *	      The absolute value of the difference between the nuber 1.0
		 *	      and the next model number above :
		 *		    = 2.0**(1-FL'MANTISSA)
		 */
		else if (attrkind == ATTR_EPSILON) {
			result = rat_const(rat_exp(rat_2, int_sub(int_fri(1),
			  fl_mantissa(fl_digits))));
		}
		/*
		 *	 FL'EMAX      --> universal_integer
		 *
		 *	      The largest exponent value in binary canonical form:
		 *		    = 4*FL'MANTISSA
		 */
		else if (attrkind == ATTR_EMAX || attrkind == ATTR_SAFE_EMAX) {
			result = uint_const(fl_emax(fl_digits));
		}
		/*
		 *	 FL'SMALL     --> universal_real
		 *
		 *	      The smallest positive non-zero number :
		 *		    = 2.0**(- FL'EMAX -1)
		 */
		else if (attrkind == ATTR_SMALL || attrkind == ATTR_SAFE_SMALL) {
			result = rat_const( rat_exp(rat_2, 
	    	  int_umin(int_add(fl_emax(fl_digits), int_fri(1)))));
		}
		/*
		 *	 FL'LARGE     --> universal_integer
		 *
		 *	       The largest positive number:
		 *		     = 2.0**FL'EMAX * (1.0 - 2.0**(-FL'MANTISSA))
		 */
		else if (attrkind == ATTR_LARGE || attrkind == ATTR_SAFE_LARGE) {
			/* TBSL: check types, this looks wrong */
			result = rat_const(rat_mul( rat_exp(rat_2, fl_emax(fl_digits)),
	    	  rat_sub(rat_1, rat_exp(rat_2,int_umin(fl_mantissa(fl_digits))))));
		}
		/*
		 *	 FL'SAFE_EMAX =  FL'BASE'EMAX
		 *	 FL'SAFE_SMALL =  FL'BASE'SMALL
		 *	 FL'SAFE_LARGE =  FL'BASE'LARGE
		 *
		 *	  cf. FL'EMAX, FL'SMALL, FL'LARGE
		 */

		/*
		 *	 FL'MACHINE_ROUNDS --> boolean
		 */
		else if (attrkind == ATTR_MACHINE_ROUNDS) {
			result = test_expr(FALSE);
		}
		/*
		 *	 FL'MACHINE_OVERFLOWS --> boolean
		 */
		else if (attrkind == ATTR_MACHINE_OVERFLOWS) {
			result = test_expr(TRUE);
		}
		/*
		 *	 FL'MACHINE_RADIX     --> universal_integer
		 */
		else if (attrkind == ATTR_MACHINE_RADIX) {
			result = uint_const(int_fri(2));
		}

		/*
		 *	 FL'MACHINE_MANTISSA  --> universal_integer
		 */
		else if (attrkind == ATTR_MACHINE_MANTISSA) {
			result = uint_const(int_fri(24));
		}
		/*
		 *	 FL'MACHINE_EMAX      --> universal_integer
		 */
		else if (attrkind == ATTR_MACHINE_EMAX) {
			result = uint_const(int_fri(127));
		}
		/*
		 *	 FL'MACHINE_EMIN      --> universal_integer
		 */
		/* We have to modified MACHINE_EMIN so that test c45524a de C4dep */
		/* passes */
		else if (attrkind == ATTR_MACHINE_EMIN) {
			result = uint_const(int_fri(-127));
		}
	}
	/*
	 *    Part B : FIXED POINT REAL
	 *
	 *    For a fixed point real type FX, we have the following basic
	 *    informations:
	 *	 delta	  (universal_real)
	 *	 fx_low	  (universal_real)
	 *	 fx_high  (universal_real)
	 *    but the bounds may not be static...
	 */
	else if (kind == CONSTRAINT_DELTA) {
		attrkind = (int) attribute_kind(node);
		if (attrkind == ATTR_SAFE_LARGE || attrkind == ATTR_SAFE_SMALL)
			sig = SIGNATURE(base_type(N_UNQ(arg_node)));
		lo = (Node) sig[2];
		hi = (Node) sig[3];
		precision = (Node) sig[4];
		static_bounds = (is_static_expr(lo) && is_static_expr(hi));
		delta = RATV((Const) N_VAL(precision));
		small = RATV((Const)N_VAL((Node)numeric_constraint_small(sig)));
		if (static_bounds) {
			eval_static(lo);
			eval_static(hi);
			const_check((Const)N_VAL(lo), CONST_RAT);
			const_check((Const)N_VAL(hi), CONST_RAT);
			fx_low = RATV((Const)N_VAL(lo));
			fx_high = RATV((Const) N_VAL(hi));
		}
		/*
		 *	 FX'DELTA     --> universal_real
		 *
		 *	      The absolute value of the error bound.
		 */
		if (attrkind == ATTR_DELTA) {
			result = rat_const(delta);
		}
		/*
		 *	 FX'SMALL     --> universal_real
		 *
		 *	      The largest power of 2 not greater than the delta:
		 *		 = 2.0**floor(log(delta)/log(2.0))
		 */
		else if (attrkind == ATTR_SMALL || attrkind == ATTR_SAFE_SMALL) {
			result = rat_const(small);
		}
		/*
		 *	 FX'MANTISSA  --> universal_integer
		 *
		 *	     The number of binary digits required:
		 *	    = ceil(log(max(abs(fx_high), abs(fx_low))/FX'SMALL)/log(2.0)))
		 */

		else if (attrkind == ATTR_MANTISSA) {
			if (static_bounds) {
				result=uint_const(int_fri(fx_mantissa(fx_high, fx_low, small)));
			}
		}
		/*
		 *	 FX'LARGE     --> universal_real
		 *
		 *	      The largest positive number :
		 *		 = (2.0**FX'MANTISSA - 1) * FX'SMALL
		 */
		else if (attrkind == ATTR_LARGE || attrkind == ATTR_SAFE_LARGE) {
			if (static_bounds) {
				result = rat_const(rat_mul( rat_sub(rat_exp(rat_2,
				  int_fri( fx_mantissa(fx_high, fx_low, small))), rat_1),
		    	  small));
			}
		}
		/*
		 *	 FX'FORE      --> universal_integer
		 *
		 *	      The minimum number of characters needed for the integer
		 *	      part of the decimal representation (including sign).
		 */
		else if (attrkind == ATTR_FORE) {
			if (static_bounds) {
				int *ivalue_10, *rat_n, *rat_d; /* Multi-precision numbers */
				int ivalue_n;
				Rational fx_maximum;

				ivalue_10 = int_fri(10);
				ivalue_n = 2;
				fx_maximum = fx_max(fx_high, fx_low);
				rat_n = num(rat_abs(fx_maximum));
				rat_d = den(rat_abs(fx_maximum));
				while (int_geq(int_quo(rat_n, rat_d), ivalue_10)) {
					rat_d = int_mul(rat_d, ivalue_10);
					ivalue_n += 1;
				}
				result = uint_const(int_fri(ivalue_n));
			}
		}
		/*
		 *	 FX'AFT	      --> universal_integer
		 *
		 *	      The number of decimal digits needed after the decimal point
		 *		= smallest n such that (10**N)*FX'DELTA >= 1.0
		 */
		else if (attrkind == ATTR_AFT) {
			xdelta = delta;
			result = uint_const(int_fri(1));
			while (rat_lss(xdelta, rat_fri(int_fri(1), int_fri(10)))) {
				xdelta = rat_mul(xdelta, rat_fri(int_fri(10), int_fri(1)));
				UINTV(result)= int_add(UINTV(result), int_fri(1));
			}
		}
		/*
		 *	 FX'SAFE_SMALL =  FX'BASE'SMALL
		 *	 FX'SAFE_LARGE =  FX'BASE'LARGE
		 *
		 *	 cf. FX'SMALL and FX'LARGE
		 */

		/*
		 *	 FX'MACHINE_ROUNDS --> boolean
		 */
		else if (attrkind == ATTR_MACHINE_ROUNDS) {
			result = test_expr(TRUE);
		}
		/*
		 *	 FX'MACHINE_OVERFLOWS --> boolean
		 */
		else if (attrkind == ATTR_MACHINE_OVERFLOWS) {
			result = test_expr(TRUE);
		}
	}
	return result;
}

static Const check_overflow(Node node, Const x)				/*check_overflow*/
{
	/*
	 * Check_overflow tests its argument against ADA_MAX_INTEGER or
	 * ADA_MAX_REAL, returning the setl value of the argument or the
	 * raise NUMERIC_ERROR instruction.  Universal integers and reals are
	 * converted to setl values.
	 */

	int	attrkind;
	Const	result;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  check_overflow");

	return const_new(CONST_OM); /*TBSL: for initial chceckout */
#ifdef TBSL
	if (!is_numeric(N_TYPE(node))
	    return;
    else if (x == symbol_overflow) {
		create_raise(node, symbol_constraint_error);
	    result = om;
	}
	else
		attrkind = (int) attribute_kind(node); /*TBSL - check this  ds 14 nov */
	case(type(x)) {
			if (streq(attr, "INTEGER")) {
				/*if (abs(x) > ADA_MAX_INTEGER) { 
             This previous test was wrong due to disymetry */
				if ((x> ADA_MAX_INTEGER) || (x < ADA_MIN_INTEGER)) {
					create_raise(node, symbol_constraint_error);
					    result = om;
				}
				else
					result = x;
			}
			else if (streq(attr, "REAL")) {
				if (abs(x) > ADA_MAX_REAL) {
					create_raise(node, symbol_constraint_error);
					    result = om;
				}
				else
					result = x;
			}
			else if (streq(attr, "TUPLE")) {
				if is_universal_integer(x) {
					if ((res = int_toi(x)) == 'OVERFLOW') {
						create_raise(node, symbol_constraint_error);
						    result = om;
					}
					else
						result = res;
				}
				else
					if ((res = rat_tor(x, ada_real_digits)) == 'OVERFLOW') {
						create_raise(node, symbol_constraint_error);
						    result = om;
					}
					else
						result = res;
		else
			;		/* Not a numeric node */
			}
			return result;
#endif

}

static int  *fl_mantissa(int fl_digits)						/*;fl_mantissa*/
{
	/*
	 *		    ceil(fl_digits*log(10)/log(2))+1)
	 */
	return (int_fri((int)ceil(((double)fl_digits*log(10.0))/log(2.0) + 1.0)));
}

static int *fl_emax(int fl_digits)							/*;fl_emax*/
{
    return	int_mul(int_fri(4), fl_mantissa(fl_digits));
}

int is_universal_integer(Const x)				/*;is_universal_integer*/
{
	return is_const_uint(x);
}

int is_universal_real(Const x)						/*;is_universal_real*/
{
	return  is_const_rat(x);
}

static void insert_and_prune(Node node, Const value)	/*;insert_and_prune*/
{
	/* When an expression tree can be constant-folded, it is reduced to a
	 * formattd value for the interpreter, and its descendants are dis-
	 * carded. The type has been established during type resolution.
	 */
	int nk;
	Span savespan;

    if (cdebug2 > 3) { }

	nk = N_KIND(node);

    savespan = get_left_span(node);
    if (N_AST1_DEFINED(nk)) N_AST1(node) = (Node) 0;
    if (N_AST4_DEFINED(nk)) N_AST4(node) = (Node) 0;
    N_KIND(node) = as_ivalue;
    N_UNQ(node) = (Symbol) 0; /* as_ivalue has no n_unq */
	N_VAL(node) = (char *) value;
    N_SPAN0(node) = savespan->line;
    N_SPAN1(node) = savespan->col;
}

void create_raise(Node node, Symbol exception)				/*;create_raise*/
{
	/* This routine replaces the subtree at node by a -raise- operator
	 * with -exception- as its operand
	 */
	Node	excp_node;
    Node	span_node;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  create_raise");

	warning(strjoin("Evaluation of expression will raise ",
	  ORIG_NAME(exception)), node);

    excp_node = node_new(as_simple_name);
    span_node = node_new(as_simple_name);
    copy_span(node, excp_node);
    copy_span(node, span_node);
    N_UNQ(excp_node) = exception;
    N_KIND(node) = as_raise;
    N_AST1(node) = excp_node;
    N_AST2(node) = span_node;
    N_TYPE(node) = (Symbol)0;

    return;
}

static Rational fx_max (Rational fx_high, Rational fx_low)			/*;fx_max*/
{
	if (rat_geq(rat_abs(fx_high), rat_abs(fx_low)))
		return rat_abs(fx_high);
	else 
		return rat_abs(fx_low);
}

static Const test_expr(int e)								/*;test_expr*/
{
	Const	res;

    res = const_new(CONST_INT);
    INTV(res) = e;
    return res;
}
