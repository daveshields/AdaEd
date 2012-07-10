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
#include "segment.h"
#include "gvars.h"
#include "attr.h"
#include "ops.h"
#include "type.h"
#include "namprots.h"
#include "segmentprots.h"
#include "genprots.h"
#include "miscprots.h"
#include "maincaseprots.h"
#include "setprots.h"
#include "typeprots.h"
#include "gutilprots.h"
#include "arithprots.h"
#include "gmiscprots.h"
#include "smiscprots.h"
#include "chapprots.h"
#include "axqrprots.h"
#include "exprprots.h"

static int rat_convert(Const, int *);
void gen_attribute(Node);
static int float_mantissa(int);
static void gen_type_attr(Symbol, int);
static int code_map(Symbol);

static int code_map_defined; /* set to FALSE if SETL version yields OM */

void gen_value(Node node)										/*;gen_value*/
{
	/*
	 *  This procedure generates code for the v_expressions
	 *  or, in other words, the right-hand-sides.
	 *
	 *  - node is the tree expression for which code is to be generated.
	 */

	int	save_tasks_declared, can_convert, rat_int;
	Node	pre_node, rec_type_node, id_node, static_node, init_node, obj_node,
	  exception_node, expr_node, init_call_node, task_node, entry_node,
	  index_node, value_node, arr_l_bd, arr_h_bd, val_l_bd, val_h_bd;
	Symbol	type_name, node_name, rec_type_name, proc_name, return_type,
	  obj_name, obj_type, model_name, exception_name, from_type, to_type,
	  accessed_type, discr_name;
	Fortup	ft1;
	Symbol	junk_var, comp_name, indx_type, value_type, indx_value_type;
	Tuple	stmts_list;
	Node	list_node, stmt_node, lhs, comp_node, type_node;
	Tuple	d_l, tup, indx_types;
	Const	value;
	int		i, stmts_list_i, size, ivalue;
	long	exprv; /* fixed point value */

#ifdef TRACE
	if (debug_flag) {
		gen_trace_node("GEN_VALUE", node);
	}
#endif

	while (N_KIND(node) == as_insert) {
		FORTUP(pre_node = (Node), N_LIST(node), ft1);
			compile(pre_node);
		ENDFORTUP(ft1);
		node = N_AST1(node);
	}

	type_name = get_type(node);

	if (N_KIND(node) == as_null)
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, symbol_null);
	else if (is_simple_name(node)) {
		node_name = N_UNQ(node);

		if (is_renaming(node_name)) {
			gen_ks(I_PUSH, mu_addr, node_name);
			if (is_array_type(type_name)) {
				/* Note: can't be a renaming of a formal parm (transformed */
				/*       to normal variable). */
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
			}
			optional_deref(type_name);
		}
		else if (is_simple_type(type_name)) {
			gen_ks(I_PUSH, kind_of(type_name), node_name);
		}
		else {
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, node_name);

			/* Arrays are treated in a different manner, depending on their */
			/* nature: parameters, constants, variables... */
			if (is_array_type(type_name)) {
				if (is_formal_parameter(node_name)) {
					/* For a parm, the type template follows the parameter */
					/* in the stack */
					gen_s(I_PUSH_EFFECTIVE_ADDRESS,
					  assoc_symbol_get(node_name, FORMAL_TEMPLATE));
				}
				else {
					/* otherwise, the type template address is pushed on the */
					/* stack */
					gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
				}
			}
		}
	}
	else {

		switch (N_KIND(node) ) {

		case(as_create_task):
			gen_s(I_CREATE_TASK, type_name);
			break;

		case(as_discard):
			expr_node = N_AST1(node);
			junk_var    = new_unique_name("junk");  /* TBSL: Reusing same var */
			next_local_reference(junk_var);
			gen_ks(I_DECLARE, kind_of(N_TYPE(node)), junk_var);

			gen_value(expr_node);
			gen_ksc(I_POP, kind_of(N_TYPE(node)), junk_var,
			  "Used only for check");
			break;

		case(as_ivalue): 
		case(as_real_literal): 
		case(as_int_literal):
			if (is_fixed_type(type_name)) {
				exprv = rat_tof(get_ivalue(node),
				  small_of(base_type(type_name)), size_of(type_name));

				/* the evaluation may have raised the overflow flag. Therefore,
				 * constraint_error has to be raised at execution time
				 */
				if ( ! arith_overflow) {
					gen_kv(I_PUSH_IMMEDIATE, kind_of(type_name),
					  fixed_const(exprv));
				}
				else {
					gen_s(I_LOAD_EXCEPTION_REGISTER, symbol_constraint_error);
					gen(I_RAISE); 
				}
			}
			else if (is_simple_type(type_name)) {
				value = get_ivalue(node);
				if (is_float_type(type_name)) {
					/* gen_(I_PUSH_IMMEDIATE, kind_of(type_name), value,
					 * ' = '+str(I_TO_F(value)));
					 */
					if (is_const_rat(value)) { /* try to cnvrt rtnl to real*/
						chaos("expr.c: rational seen when real expected");
					}
					gen_kv(I_PUSH_IMMEDIATE, kind_of(type_name), value);
				}
				else {
					if (is_const_rat(value)) { /* try to cnvrt rtnl to int */
						rat_int = rat_convert(value, &can_convert);
						if (can_convert) {
							gen_kv(I_PUSH_IMMEDIATE, kind_of(type_name),
							  int_const(rat_int));
						}
						else {
							gen_kv(I_PUSH_IMMEDIATE, kind_of(type_name), value);
						}
					}
					else if (is_const_uint(value)) {
						/* try to convert universal integer to integer */
						ivalue = int_toi(UINTV(value));
						if (!arith_overflow) {/* if can convert to integer */
							gen_kv(I_PUSH_IMMEDIATE, kind_of(type_name),
							  int_const(ivalue));
						}
						else { /* just try again as universal integer */
							gen_s(I_LOAD_EXCEPTION_REGISTER,
							  symbol_constraint_error);
							gen(I_RAISE);
							/* the exceptn has to be raised (overflow on int)
							 * gen_kv(I_PUSH_IMMEDIATE, kind_of(type_name),
							 *    value);
							 */
						}
					}
					else {
						gen_kv(I_PUSH_IMMEDIATE, kind_of(type_name), value);
					}
				}
			}
			else 
				compiler_error("structured ivalue");
			break;

		case(as_string_ivalue):
			/*  This created a segment containing the string literal... */
			/* TBSL: note that array_ivalue returns a Segment */
			obj_name  = get_constant_name(array_ivalue(node));
			type_name = N_TYPE(node);
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, obj_name);
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
			break;

		case(as_index):
			gen_subscript(node);
			optional_deref(type_name);
			break;

		case(as_selector):
			gen_address(node);
			optional_deref(type_name);
			break;

		case(as_discr_ref):
			discr_name      = N_UNQ(node);
			rec_type_node = N_AST1(node);
			rec_type_name   = N_UNQ(rec_type_node);
			gen_sc(I_PUSH_EFFECTIVE_ADDRESS, rec_type_name,
			  "fetch discriminant from template");
			/* SETL version has discr_name as last argument, this is presumably
			 * comment part of instruction. For now ignore this
			 * gen_ki(I_ADD_IMMEDIATE, mu_word,
			 *   TT_C_RECORD_DISCR + FIELD_OFFSET(discr_name)(TARGET),
			 *   discr_name);
			 */
			/* TBSL: review trnsltn of next line VERY carefully  ds 10-2-85 */
			if (TYPE_KIND(rec_type_name) == TT_D_RECORD) {
				gen_ki(I_ADD_IMMEDIATE, mu_word,
				  ((sizeof(struct tt_d_type)/sizeof(int)) + 
				  1 + 2 * FIELD_OFFSET(discr_name)));
			}
			else {
				gen_ki(I_ADD_IMMEDIATE, mu_word,
				  ((sizeof(struct tt_d_type)/sizeof(int))
				  + FIELD_OFFSET(discr_name)));
			}
			gen_k(I_DEREF, kind_of(type_name));
			break;

		case(as_all):
			gen_address(node);
			if (is_simple_type(type_name)) {
				gen_k(I_DEREF, kind_of(type_name));
			}
			else {
				Symbol not_null;
				/* test for null explicitly, because optional_deref is a noop
				 * on an array  or record (which are always  references).
				 */
				gen_k(I_DUPLICATE, mu_addr);
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, symbol_null);
				gen_k(I_COMPARE, mu_addr);
				not_null = new_unique_name("ok_access");
				gen_s(I_JUMP_IF_FALSE, not_null);
				gen_s(I_LOAD_EXCEPTION_REGISTER, symbol_constraint_error);
				gen(I_RAISE);
				gen_s(I_LABEL, not_null);
			}
			break;

		case(as_call):
			id_node   = N_AST1(node);
			proc_name   = N_UNQ(id_node);
			return_type = TYPE_OF(proc_name);
			gen_kc(I_DUPLICATE, kind_of(return_type), "place holder");
			compile(node);  	 /* processed from now as a procedure call */
			break;

		case(as_slice):
			gen_address(node);
			break;

		case(as_raise):
			compile(node);
			break;

		case(as_attribute): 
		case(as_range_attribute):
			gen_attribute(node);
			break;

		case(as_record_aggregate): 
		case(as_record_ivalue):
			static_node = N_AST1(N_AST1(node));
			init_node = N_AST2(N_AST1(node));
			obj_node = N_AST2(node);
			obj_name = N_UNQ(obj_node);
			obj_type = get_type(obj_node);

			if (!has_static_size(obj_type)) {
				next_local_reference(obj_name);
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, obj_type);
				gen(I_CREATE_STRUC);
				gen_s(I_UPDATE_AND_DISCARD, obj_name);
				/* Warning: Discriminants may be static or not, but must be */
				/*          evaluated before other components */
				if (static_node != OPT_NODE) {
					stmts_list = tup_copy(N_LIST(static_node));
					if (init_node != OPT_NODE) {
						/* init_node is an as_statements */
						list_node = N_AST1(init_node);
						d_l       = discriminant_list_get(obj_type);
						FORTUP(stmt_node = (Node), N_LIST(list_node), ft1);
							if (N_KIND(stmt_node) == as_assignment)  {
								/* lhs is as_selector */
								lhs = N_AST1(stmt_node);
								comp_node = N_AST2(lhs);
								comp_name = N_UNQ(comp_node);
								if (tup_mem((char *) comp_name, d_l)) {
									/* This is a discriminant */
									stmts_list = tup_exp(stmts_list,
									  tup_size(stmts_list)+1);
									for (stmts_list_i = tup_size(stmts_list);
									  stmts_list_i > 1; stmts_list_i--) {
										stmts_list[stmts_list_i] =
										  stmts_list[stmts_list_i-1];
									}
									stmts_list[1] = (char *)stmt_node;
								}
								else {
									stmts_list =
									  tup_with(stmts_list, (char *) stmt_node);
								}
							}
							else if (N_KIND(stmt_node) == as_init_call) {
								tup  = N_LIST(N_AST2(stmt_node));
								size = tup_size(tup);
								/* lhs is as_selector */
								lhs  = (Node) tup[size];
								comp_node = N_AST2(lhs);
								comp_name = N_UNQ(comp_node);
								if (tup_mem((char *) comp_name, d_l)) {
									/* This is a discriminant */
									stmts_list = tup_exp(stmts_list,
									  tup_size(stmts_list)+1);
									for (stmts_list_i = tup_size(stmts_list);
									  stmts_list_i > 1; stmts_list_i--) {
										stmts_list[stmts_list_i] =
										  stmts_list[stmts_list_i-1];
									}
									stmts_list[1] = (char *)stmt_node;
								}
								else {
									stmts_list =
									  tup_with(stmts_list, (char *) stmt_node);
								}
							}
							else {
								stmts_list = tup_with(stmts_list,
								  (char *) stmt_node);
							}
						ENDFORTUP(ft1);
					}

					FORTUP(comp_node = (Node), stmts_list, ft1)
					    compile(comp_node);
					ENDFORTUP(ft1);
					init_node = OPT_NODE;    /* all done. */
				}
			}
			else if (is_ivalue(node)) {
				assign_same_reference(obj_name,
				  get_constant_name(record_ivalue(node)) );
			}
			else if (CURRENT_LEVEL == 1) {
				next_global_reference_template(obj_name, record_ivalue(node));
			}
			else if (tup_size(N_LIST(static_node)) == 0) {
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, obj_type);
				gen(I_CREATE_STRUC);
				next_local_reference(obj_name);
				gen_s(I_UPDATE_AND_DISCARD, obj_name);
			}
			else {
				model_name = get_constant_name(record_ivalue(node));
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, model_name);
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, obj_type);
				gen(I_CREATE_COPY_STRUC);
				next_local_reference(obj_name);
				gen_s(I_UPDATE_AND_DISCARD, obj_name);
			}

			compile(init_node);
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, obj_name);
			break;

		case(as_array_aggregate): 
		case(as_array_ivalue):
			static_node = N_AST1(N_AST1(node));
			init_node = N_AST2(N_AST1(node));
			obj_node = N_AST2(node);
			obj_name = N_UNQ(obj_node);
			obj_type = get_type(obj_node);

			/*  Check and see if can create a segment containing the aggregate
			 *  value...
			 */

			if (!has_static_size(obj_type)) {

				/*  CASE 1.  We  cannot create a segment because have anon.
				 *   types decl which are used for type checking at run time
				 */

				next_local_reference(obj_name);
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, obj_type);
				gen(I_CREATE_STRUC);
				if (is_array_type(obj_type)) {
					gen_ks(I_DISCARD_ADDR, 1, obj_type);
				}
				gen_s(I_UPDATE_AND_DISCARD, obj_name);
				FORTUP(comp_node = (Node), N_LIST(static_node), ft1);
					compile(comp_node);
				ENDFORTUP(ft1);
			}
			else if (is_ivalue(node)) {
				/* TBSL: note that array_ivalue returns a Segment */
				/*  CASE 2.  The aggregate is static and some (or all) values
				 * can be put into a segment for that aggregate.
				 */

				assign_same_reference(obj_name,
				  get_constant_name(array_ivalue(node)));
			}
			else if (CURRENT_LEVEL == 1) {
				/*  CASE 3.    */
				next_global_reference_template(obj_name, array_ivalue(node));
			}
			else if (tup_size(N_LIST(static_node)) == 0) {
				/*  CASE 4.  There are no static values for the aggregate.
				 *  Hence, all values are assigned with run-time assignment
				 *  statements...
				 */

				gen_s(I_PUSH_EFFECTIVE_ADDRESS, obj_type);
				gen(I_CREATE_STRUC);
				next_local_reference(obj_name);
				gen_ks(I_DISCARD_ADDR, 1 , obj_type);
				gen_s(I_UPDATE_AND_DISCARD, obj_name);
			}
			else {
				/*  CASE 5.  There are both static values and non-static values
				 *  for the aggregate.  A segment is created with the static
				 *  values, and non-static values are assigned with run-time
				 *  assignment statements...
				 */
				model_name = get_constant_name(array_ivalue(node));
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, model_name);
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, obj_type);
				gen(I_CREATE_COPY_STRUC);
				next_local_reference(obj_name);
				gen_ks(I_DISCARD_ADDR, 1, obj_type);
				gen_s(I_UPDATE_AND_DISCARD, obj_name);
			}

			/* Proces the non-static value and push addresses of the obj_name
			 * and obj_type
			 */
			compile(init_node);
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, obj_name);
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, obj_type);
			break;

		case(as_type_and_value):
			/* Special node: generate a record value and elaborate a record */
			/* subtype, constrained by the value's discriminants */
			type_node = N_AST1(node);
			expr_node = N_AST2(node);
			type_name = N_UNQ(type_node);

			gen_value(expr_node);
			gen_subtype(type_name);
			break;

		case(as_test_exception):
			exception_node = N_AST1(node);
			exception_name   = N_UNQ(exception_node);
			gen_s(I_TEST_EXCEPTION_REGISTER, exception_name);
			break;

		case(as_convert):
			expr_node = N_AST2(node);
			from_type = base_type(get_type(expr_node));
			to_type   = N_TYPE(node);
			gen_value(expr_node);
			gen_convert(from_type, to_type);
			break;

		case(as_qual_discr):
			type_name    = N_TYPE(node);
			value_node = N_AST1(node);
			gen_value(value_node);
			/* A qual_discr on a TT_D_RECORD is meaningless.
			 * Special code may be emitted TBSL.
			 */
			if (type_name != get_type(value_node)
			  && TYPE_KIND(type_name) != TT_D_RECORD
			  && SIGNATURE(type_name) != SIGNATURE(root_type(type_name))) {
				gen_s(I_QUAL_DISCR, type_name);
			}
			break;

		case(as_qual_range):
			type_name  = N_TYPE(node);
			value_node = N_AST1(node);
			gen_value(value_node);
			gen_s(I_QUAL_RANGE, type_name);
			break;

		case(as_qual_index):
			type_name    = N_TYPE(node);
			value_node = N_AST1(node);
			gen_value(value_node);
			value_type = get_type(value_node);
			if (value_type != type_name && TYPE_KIND(type_name) != TT_D_ARRAY) {
				gen_s(I_QUAL_INDEX, type_name);
			}
			/* the bounds of the value and the array itself must be equal. */
			else if (value_type != type_name)  {   /* case of TT_D_ARRAY. */
				indx_types = (Tuple)SIGNATURE(type_name)[1];
				for (i = 1; i <= tup_size(indx_types); i++)  {
					indx_type = (Symbol)indx_types[i];
					arr_l_bd = (Node)SIGNATURE(indx_type)[2];
					arr_h_bd = (Node)SIGNATURE(indx_type)[3];
					indx_value_type =
					  (Symbol)((Tuple)SIGNATURE(value_type)[1])[i];
					val_l_bd = (Node)SIGNATURE(indx_value_type)[2];
					val_h_bd = (Node)SIGNATURE(indx_value_type)[3];
					if (is_ivalue(arr_l_bd) && is_ivalue(val_l_bd) &&
					  INTV(get_ivalue(arr_l_bd)) != INTV(get_ivalue(val_l_bd))){
						gen_s(I_LOAD_EXCEPTION_REGISTER,
						  symbol_constraint_error);
						gen(I_RAISE);
						break;
					}
					if (is_ivalue(arr_h_bd) && is_ivalue(val_h_bd) &&
					  INTV(get_ivalue(arr_h_bd)) != INTV(get_ivalue(val_h_bd))){
						gen_s(I_LOAD_EXCEPTION_REGISTER,
						  symbol_constraint_error);
						gen(I_RAISE);
						break;
					}
				}
			}
			break;

		case(as_qual_sub):
			type_name  = N_TYPE(node);
			value_node = N_AST1(node);
			gen_value(value_node);
			gen_s(I_QUAL_SUB, type_name);
			break;

		case(as_qual_adiscr):
			type_name  = (Symbol)designated_type(N_TYPE(node));
			value_node = N_AST1(node);
			gen_value(value_node);
			gen_access_qual(as_qual_discr, type_name);
			break;

		case(as_qual_aindex):
			type_name  = (Symbol)designated_type(N_TYPE(node));
			value_node = N_AST1(node);
			gen_value(value_node);
			gen_access_qual(as_qual_index, type_name);
			break;

		case(as_new):
			type_node = N_AST1(node);
			expr_node = N_AST2(node);
			type_name = N_TYPE(node);
			accessed_type = N_UNQ(type_node);
			if (N_KIND(expr_node) == as_init_call) {
				init_call_node = expr_node;
				expr_node      = OPT_NODE;
			}
			else {
				init_call_node = OPT_NODE;
			}

			if (CONTAINS_TASK(accessed_type)) {
				save_tasks_declared = TASKS_DECLARED;
				TASKS_DECLARED      = FALSE;
				/* Note, make want to have global corresponding to this const */
				gen_kv(I_PUSH_IMMEDIATE, mu_word, int_const_null_task);
				gen_c(I_LINK_TASKS_DECLARED, "new task frame for allocator");
			}

			if (expr_node != OPT_NODE) {
				gen_value(expr_node);
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
				gen_s(I_ALLOCATE_COPY, accessed_type);
			}
			else {
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, accessed_type);
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
				gen(I_ALLOCATE);
				if (init_call_node != OPT_NODE) {
					if (is_array_type(accessed_type)) {
						gen_k(I_DUPLICATE, mu_addr);
						gen_k(I_DEREF, mu_dble);
					}
					compile(init_call_node);
					if (is_array_type(accessed_type)) {
						gen_ks(I_DISCARD_ADDR, 2, (Symbol) 0);
					}
				}
			}

			if (CONTAINS_TASK(accessed_type)) {
				gen_s(I_ACTIVATE_NEW, type_name);
				TASKS_DECLARED = save_tasks_declared;
			}
			break;

		case(as_entry_name):
			task_node = N_AST1(node);
			entry_node = N_AST2(node);
			index_node = N_AST3(node);
			if (task_node != OPT_NODE)
				gen_value(task_node);

			if (index_node == OPT_NODE) {
				reference_of(N_UNQ(entry_node));
				gen_kv(I_PUSH_IMMEDIATE, mu_byte,
				  int_const((int)REFERENCE_OFFSET));
				gen_kvc(I_PUSH_IMMEDIATE, mu_word, int_const_0, "simple entry");
			}
			else {
				reference_of(N_UNQ(entry_node));
				gen_kvc(I_PUSH_IMMEDIATE, mu_byte,
				  int_const((int) REFERENCE_OFFSET), "family");
				gen_value(index_node);
			}
			break;

		case(as_current_task):
			gen(I_CURRENT_TASK);
			break;

			/* Unary operators */
		case(as_un_op):
			gen_unary(node);
			break;

			/* Binary operators */
		case(as_op):
			gen_binary(node);
			break;

		case(as_deleted):
			;

		default:
			compiler_error("Unknown node at GEN_VALUE");
		}
	}
}

static int rat_convert(Const con, int *can_convert)			/*;rat_convert*/
{
	int rat_int;

	rat_int = rat_toi(RATV(con));
	*can_convert = !arith_overflow;
	return rat_int;
}

void gen_unary(Node node)								/*;gen_unary*/
{
	/* Unary operators */
	Node	op_node, args_node, op1;
	Symbol	opcode, type_name;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("GEN_UNARY", node);
#endif

	op_node = N_AST1(node);
	args_node = N_AST2(node);
	opcode    = N_UNQ(op_node);
	type_name = N_TYPE(node);
	op1 = (Node) N_LIST(args_node)[1];

	gen_value(op1);
	if (opcode == symbol_addui || opcode == symbol_addufl
	  || opcode == symbol_addufx)
		;
	else if (opcode == symbol_subufx || opcode == symbol_subui)
		gen_k(I_NEG, kind_of(type_name));
	else if (opcode == symbol_subufl)
		gen_k(I_FLOAT_NEG, kind_of(type_name));
	else if (opcode == symbol_absi || opcode == symbol_absfx)
		gen_k(I_ABS, kind_of(type_name));
	else if (opcode == symbol_absfl)
		gen_k(I_FLOAT_ABS, kind_of(type_name));
	else if (opcode == symbol_not) {
		if (is_array_type(type_name))
			gen(I_ARRAY_NOT);
		else
			gen(I_NOT);
	}
	else
		compiler_error("Unexpected unary operator");
}

void gen_binary(Node node)										/*;gen_binary*/
{
	/* The SETL constant code_map is realized in the C version by a procedure
	 * code_map().
	 */

	Node	op_node, args_node, op1, op2;
	Symbol	opcode, type_name, andthen, orelse, op1_type, op2_type;
	int		op_instr, aopcode;
#ifdef TRACE
	if (debug_flag)
		gen_trace_node("GEN_BINARY", node);
#endif

	op_node = N_AST1(node);
	args_node = N_AST2(node);
	opcode = N_UNQ(op_node);
	type_name = N_TYPE(node);
	op1 = (Node) N_LIST(args_node)[1];
	op2 = (Node) N_LIST(args_node)[2];

	if (opcode == symbol_and|| opcode == symbol_or || opcode == symbol_xor) {
		gen_value(op1);
		gen_value(op2);
		if (is_array_type(type_name)) {
			if (opcode == symbol_and) aopcode = I_ARRAY_AND;
			else if (opcode == symbol_or) aopcode = I_ARRAY_OR;
			else if (opcode == symbol_xor) aopcode = I_ARRAY_XOR;
			gen(aopcode);
		}
		else {
			gen(code_map(opcode));
		}
	}
	else if (opcode == symbol_andthen) {
		gen_value(op1);
		gen_k(I_DUPLICATE, mu_byte);
		andthen = new_unique_name("andthen");
		gen_s(I_JUMP_IF_FALSE, andthen);
		gen_value(op2);
		gen(I_AND);
		gen_s(I_LABEL, andthen);
	}
	else if(opcode == symbol_orelse) {
		gen_value(op1);
		gen_k(I_DUPLICATE, mu_byte);
		orelse = new_unique_name("orelse");
		gen_s(I_JUMP_IF_TRUE, orelse);
		gen_value(op2);
		gen(I_OR);
		gen_s(I_LABEL, orelse);
	}
	else if (opcode == symbol_in || opcode == symbol_notin) {
		op2_type = N_UNQ(op2);
		if (is_record_type(op2_type) && !has_discriminant(op2_type)) {
			gen_ki(I_PUSH_IMMEDIATE, mu_byte, opcode == symbol_in);
		}
		else {
			if (is_access_type(op2_type)) {
				/* if the acces value is null, it belongs to the subtype.
				 * Otherwise, it is the designated object that must belong
				 * to the designated subtype.
				 */
				Symbol desig_type, end_if, deref;

				end_if = new_unique_name("end_if");
				deref  = new_unique_name("deref");
				desig_type = designated_type(op2_type);

				gen_value(op1);
				gen_k(I_DUPLICATE, kind_of(op2_type));
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, symbol_null);
				gen_k(I_COMPARE, mu_addr);
				gen_s(I_JUMP_IF_FALSE, deref);
				gen_ks(I_DISCARD_ADDR, 1, (Symbol)0);
				gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_boolean),
				  int_const(TRUE));
				gen_s(I_JUMP, end_if);

				gen_s(I_LABEL, deref);
				if (is_simple_type(desig_type) || is_array_type(desig_type))
					gen_k(I_DEREF, kind_of(desig_type));
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, desig_type);   /* Type name */
				gen(I_MEMBERSHIP);
				gen_s(I_LABEL, end_if);
			}
			else {
				gen_value(op1);
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, op2_type);   /* Type name */
				gen(I_MEMBERSHIP);
			}
			if (opcode == symbol_notin)
				gen(I_NOT);
		}
	}
	else if (opcode == symbol_eq || opcode == symbol_ne || opcode == symbol_lt
	  || opcode == symbol_gt || opcode == symbol_le ||opcode == symbol_ge){

		gen_value(op1);
		gen_value(op2);

		op1_type = get_type(op1);
		if (is_simple_type(op1_type)) {
			if (is_float_type(op1_type))
				gen_k(I_FLOAT_COMPARE, kind_of(op1_type));
			else
				gen_k(I_COMPARE, kind_of(op1_type));
		}
		else if (is_array_type(op1_type)) {
			if (opcode == symbol_eq || opcode == symbol_ne)
				gen(I_COMPARE_STRUC);
			else
				gen(I_COMPARE_ARRAYS);
		}
		else if (is_record_type(op1_type)) {
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, op1_type);
			gen(I_COMPARE_STRUC);
		}

		/* Note: the compare operation push a byte on the stack whose two */
		/*       least significant bits mean 'is_equal' and 'is_greater' */

		if(opcode == symbol_ne) {
			gen(I_IS_EQUAL);
			gen(I_NOT);
		}
		else {
			gen(code_map(opcode));
		}
	}
	else if (opcode == symbol_addi) {
		if (is_ivalue(op1)) {
			gen_value(op2);
			gen_ki(I_ADD_IMMEDIATE, kind_of(type_name), get_ivalue_int(op1));
		}
		else if (is_ivalue(op2)) {
			gen_value(op1);
			gen_ki(I_ADD_IMMEDIATE, kind_of(type_name), get_ivalue_int(op2));
		}
		else {
			gen_value(op1);
			gen_value(op2);
			gen_k(code_map(opcode), kind_of(type_name));
		}
	}
	else if (opcode == symbol_subi) {
		if (is_ivalue(op2)) {
			gen_value(op1);
			gen_ki(I_ADD_IMMEDIATE, kind_of(type_name), -get_ivalue_int(op2));
		}
		else {
			gen_value(op1);
			gen_value(op2);
			gen_k(code_map(opcode), kind_of(type_name));
		}
	}
	else if (opcode == symbol_cat) {
		gen_value(op1);
		gen_value(op2);
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, base_type(type_name));
		gen(I_ARRAY_CATENATE);
	}
	else if (opcode == symbol_mulfx || opcode == symbol_divfx) {
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
		gen_value(op1);
		op1_type = get_type(op1);
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, op1_type);
		gen_value(op2);
		op2_type = get_type(op2);
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, op2_type);
		gen(code_map(opcode));
		/* note: a qual_range is done implicitly by the fix_xxx instruction */
	}
	else if (opcode == symbol_mulfxi || opcode == symbol_divfxi) {
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
		gen_value(op1);
		op1_type = get_type(op1);
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, op1_type);
		gen_value(op2);
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, symbol_integer);
		gen_s(I_CONVERT_TO, symbol_dfixed);
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, symbol_dfixed);
		gen(code_map(opcode));
	}
	else if (opcode == symbol_mulfix) {
		gen_value(op2);
		op2_type = get_type(op2);
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, op2_type);
		gen_value(op1);
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, symbol_dfixed);
		gen(code_map(opcode));
	}
	else {
		gen_value(op1);
		gen_value(op2);
		op_instr = code_map(opcode);
		if (code_map_defined) {/*if code_map knows about opcode */
			gen_k(op_instr, kind_of(type_name));
		}
		else
			compiler_error("Unknown operator:");
	}
}

void gen_attribute(Node node)								/*;gen_attribute*/
{
	/*SETL float_mantissa macro is procedure in C following this one.*/
	/* const
	 * internal_map is not needed in  C version.
	 * internal_map = {['T_FIRST',     a_T_FIRST],
	 *   ['T_LAST',       a_T_LAST],
	 *   ['T_LENGTH',   a_T_LENGTH],
	 *   ['T_RANGE',     a_T_RANGE]};
	 */
	Const	old_lbd, old_ubd; 
	Rational rat;

	int		*rat_n, *rat_d, *ivalue_i; /* multi-precision integers*/
	Node	lbd_node, ubd_node, delta_node, low, high;
	int		ivalue_n;
	int		fmantissa, digits_int, ivalue_int, i;
	Tuple	tup;
	Const	type_small, root_small;
	int		l, low_int, high_int;
	Const	low_value, high_value, digits, const_1, const_2, rat_const_v;
	double	fvalue;
	Rational	rvalue, rat_t;
	Node	arg1, arg2, comp_node, digs;
	Symbol	from_type, to_type, type_name, comp_name;
	Symbol	junk_var, field;
	Tuple	index_list;
	int		attribute;
	long	low_long, high_long, rvalue_long;	/* fixed point */
	Tuple	repr_tup, align_info, attribute_list;
	Fortup	ft1;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("GEN_ATTRIBUTE", node);
#endif

	arg1 = N_AST2(node);
	arg2 = N_AST3(node);
	attribute = (int) attribute_kind(node);

#ifdef TRACE
	if (debug_flag)
		gen_trace_string("   ATTRIBUTE:", attribute_str(attribute));
#endif

	/*TBSL(JC): in GEN_ATTRIBUTE type of static attributes of real types */

	switch (attribute) {

	case(ATTR_ADDRESS):
		gen_address(arg1);
		break;

	case(ATTR_AFT):	 /* Computed by the expander? TBSL */
		type_name = N_UNQ(arg1);
		tup = get_constraint(type_name);
		delta_node = (Node) tup[4];
		rat_const_v  = get_ivalue(delta_node);
		if (rat_const_v->const_kind != CONST_RAT)
			chaos("expr: argument not rational");
		rat = rat_const_v->const_value.const_rat;
		ivalue_1 = int_fri(1); 
		ivalue_i = int_fri(1);
		rat_n = num(rat); 
		rat_d = den(rat);
		rat_n     = int_mul(rat_n, int_fri(10));
		while (int_lss(rat_n , rat_d)) {
			ivalue_i = int_add(ivalue_i, ivalue_1);
			rat_n      = int_mul(rat_n, ivalue_10);
		}
		ivalue_n = int_toi(ivalue_i);
		/* TBSL: may need extra check for long case here, though for now
		 * will crash if want long integer value as will get overflow
		 */
		if (arith_overflow)
			chaos("expr.c ATTR_AFT overflow during conversion");
		gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_integer), int_const(ivalue_n));
		break;

		/*  ("BASE): */

	case(ATTR_CALLABLE):
		gen_value(arg1);
		gen_kv(I_ATTRIBUTE, ATTR_CALLABLE, int_const(0));
		break;
		/*  ("T_CONSTRAINED"): */

	case(ATTR_O_CONSTRAINED):
		if (is_record_type(get_type(arg1))) {
			gen_address(arg1);     /* 1st field in record */
			gen_kc(I_DEREF, mu_byte, "constrained flag");
		}
		else {
			gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_boolean), int_const(TRUE));
		}
		break;

	case(ATTR_COUNT):
		gen_value(arg1);
		gen_kv(I_ATTRIBUTE, ATTR_COUNT, int_const(0));
		break;

	case (ATTR_DELTA):
		to_type    = N_TYPE(node);
		type_name  = N_UNQ(arg1);
		tup        = get_constraint(type_name);
		delta_node = (Node)numeric_constraint_delta(tup);
		rat_const_v  = get_ivalue(delta_node);
		/* convert rational value to indicated target type */
		if (is_fixed_type(to_type)) {
			rvalue_long = rat_tof(rat_const_v, small_of(base_type(to_type)),
			  size_of(to_type));
			gen_kv(I_PUSH_IMMEDIATE,kind_of(to_type), fixed_const(rvalue_long));
		}
		else {		/* can only be float */
			fvalue = rat_tor(RATV(rat_const_v), ADA_REAL_DIGITS);
			gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_float), real_const(fvalue));
		}
		break;

	case(ATTR_DIGITS):   /* Folded by FE unless it appears in a generic */
		type_name    = N_UNQ(arg1);
		tup = SIGNATURE(type_name);
		digs = (Node) tup[4];
		digits = get_ivalue(digs);
		gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_integer), digits);
		break;

	case(ATTR_EMAX):     /* Folded by FE unless it appears in a generic */
		type_name    = N_UNQ(arg1);
		tup = SIGNATURE(type_name);
		digs = (Node) tup[4];
		digits_int= get_ivalue_int(digs);
		fmantissa    = float_mantissa(digits_int);
		gen_kv(I_PUSH_IMMEDIATE,kind_of(symbol_integer),int_const(4*fmantissa));
		break;

	case(ATTR_EPSILON):   /* Folded by FE unless it appears in a generic */
		type_name    = N_UNQ(arg1);
		tup = SIGNATURE(type_name);
		digs = (Node) tup[4];
		digits_int       = get_ivalue_int(digs);
		fmantissa    = float_mantissa(digits_int);
		fvalue       = pow(2.0, -(double) (fmantissa-1));
		gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_float), real_const(fvalue));
		break;

	case(ATTR_T_FIRST): 
	case(ATTR_T_LAST):
	case(ATTR_T_LENGTH): 
	case(ATTR_T_RANGE):
		/* Note: cf. GEN_SUBTYPE for some optimizations on 'range */
		type_name = N_UNQ(arg1);
		if (is_array_type(type_name)) {
			tup = SIGNATURE(type_name);
			index_list = (Tuple) tup[1];
			type_name = (Symbol) index_list[get_ivalue_int(arg2)];
		}
		tup = SIGNATURE(type_name);
		low = (Node) tup[2];
		high = (Node) tup[3];
		low_value  = get_ivalue(low); 
		high_value = get_ivalue(high);

		if ((attribute == ATTR_T_RANGE) && (low_value->const_kind != CONST_OM
		  && high_value->const_kind != CONST_OM)) {
			gen_kv(I_PUSH_IMMEDIATE, kind_of(type_name), low_value);
			gen_kv(I_PUSH_IMMEDIATE, kind_of(type_name), high_value);
			return;
		}
		else if((attribute==ATTR_T_FIRST) && low_value->const_kind != CONST_OM){
			if (is_fixed_type(type_name)) {
				low_long= rat_tof(low_value, small_of(base_type(type_name)),
				  size_of(type_name));
				gen_kv(I_PUSH_IMMEDIATE, kind_of(type_name),
				  fixed_const(low_long));
			}
			else {
				gen_kv(I_PUSH_IMMEDIATE, kind_of(type_name), low_value);
			}
			return;
		}
		else if((attribute==ATTR_T_LAST) && high_value->const_kind != CONST_OM){
			if (is_fixed_type(type_name)) {
				high_long= rat_tof(high_value, small_of(base_type(type_name)),
				  size_of(type_name));
				gen_kv(I_PUSH_IMMEDIATE, kind_of(type_name),
				  fixed_const(high_long));
			}
			else {
				gen_kv(I_PUSH_IMMEDIATE, kind_of(type_name), high_value);
			}
			return;
		}
		else if((attribute==ATTR_T_LENGTH) && (l = length_of(type_name)) >= 0) {
			gen_kv(I_PUSH_IMMEDIATE, kind_of(type_name), int_const(l));
			return;

			/* and in case none of the above worked */
		}
		else {
			gen_type_attr(type_name, attribute);
		}
		break;

	case(ATTR_O_FIRST):
		gen_value(arg1);
		gen_kv(I_ATTRIBUTE, ATTR_O_FIRST, get_ivalue(arg2));
		break;

	case(ATTR_FIRST_BIT):
	case(ATTR_LAST_BIT):
	case(ATTR_POSITION):

		comp_node = N_AST2(arg1);
		type_name = TYPE_OF(N_UNQ(N_AST1(arg1)));
		comp_name = N_UNQ(comp_node);
		repr_tup= REPR(type_name);
		align_info = (Tuple) repr_tup[4]; 	  /* alignment_info*/
		attribute_list = (Tuple) align_info[2];
	    FORTUP(tup=(Tuple),attribute_list,ft1);
		  field = (Symbol) tup[1];
          if (comp_name == field) {
        	 if (attribute == ATTR_POSITION) {
	      		 ivalue_int  = (int) tup[2]; /* position */
			 }
        	 else if (attribute == ATTR_FIRST_BIT) {
	      		 ivalue_int  = (int) tup[3]; /* first_bit */
			 }
        	 else {
	      		 ivalue_int  = (int) tup[4]; /* last_bit */
			 }
		  	 gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_integer),
					int_const(ivalue_int));
			 return;
		  }	
		ENDFORTUP(ft1);
		break;

	case(ATTR_FORE):
		type_name = N_UNQ(arg1);
		if (is_static_type(type_name)) {
			tup = get_constraint(type_name);
			lbd_node = (Node) tup[2];
			ubd_node = (Node) tup[3];
			old_lbd = get_ivalue(lbd_node);
			old_ubd = get_ivalue(ubd_node);
			if (rat_gtr(rat_abs(RATV(old_lbd)), rat_abs(RATV(old_ubd))) ) {
				rat_t = rat_abs(RATV(old_lbd));
				rat_n = num(rat_t); 
				rat_d = den(rat_t);
				/*[n, d] = rat_abs(old_lbd);*/
			}
			else {
				/*[n, d] = rat_abs(old_ubd);*/
				rat_t = rat_abs(RATV(old_ubd));
				rat_n = num(rat_t); 
				rat_d = den(rat_t);
			}
			ivalue_n = 2;
			while (int_geq(int_quo(rat_n , rat_d) , ivalue_10)) {
				rat_d = int_mul(rat_d, ivalue_10);
				ivalue_n += 1;
			}
			gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_integer),
			  int_const(ivalue_n));
		}
		else {
			rat_const_v = small_of(base_type(type_name)); 
			rat = RATV(rat_const_v);
			rat_n = num(rat); 
			rat_d = den(rat);
			gen_kv(I_PUSH_IMMEDIATE, mu_word, int_const(int_toi(rat_n)));
			gen_kv(I_PUSH_IMMEDIATE, mu_word, int_const(int_toi(rat_d)));
			gen_type_attr(type_name, ATTR_FORE);
		}
		break;

	case(ATTR_IMAGE):
		type_name = N_UNQ(arg1);
		gen_value(arg2);
		gen_type_attr(type_name, ATTR_IMAGE);
		break;

	case(ATTR_LARGE):
		type_name = N_UNQ(arg1);
		to_type   = N_TYPE(node);
		if (is_fixed_type(type_name)) {
			Rational rt, rb;
			int* small_ratio;
			int* scaled_large;

			rt = RATV(small_of(type_name));
			rb = RATV(small_of(base_type(type_name)));
			rvalue = rat_div(rt, rb);
			small_ratio = int_quo(num(rvalue), den(rvalue));

			if (is_static_type(type_name)) {
				tup = get_constraint(type_name);
				lbd_node = (Node) tup[2];
				ubd_node = (Node) tup[3];
				old_lbd = get_ivalue(lbd_node);
				old_ubd = get_ivalue(ubd_node);

				/* large = (2 ** mantissa -1) * small  
				 * The run-time representation is in units of the base small,
				 * but of course the mantissa is that of the type, not the base.
				 * We scale the result by the ratios of the two smalls.
				 */
				scaled_large  = int_mul(int_sub(int_exp(int_fri(2),
				  int_fri(fx_mantissa(RATV(old_lbd), RATV(old_ubd), rt))),
				  int_fri(1)), small_ratio);

				if (is_fixed_type(to_type)) {
					/* emit as fixed point number, i.e. long value */
					gen_kv(I_PUSH_IMMEDIATE, kind_of(to_type),
					  fixed_const(int_tol(scaled_large)));
				}
				else {   /* convert to floating type */
					Rational rat_val;
					rat_val = rat_new(int_mul(scaled_large, num(rb)), den(rb));
					fvalue = rat_tor(rat_val, ADA_REAL_DIGITS);
					gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_float),
					  real_const(fvalue));
				}
			}
			else {
				/* Compute ratio between subtype's SMALL and base type's */
				/* SMALL and push it (always integer) */
				gen_kv(I_PUSH_IMMEDIATE, mu_word,
				  int_const(int_toi(small_ratio)));
				gen_type_attr(type_name, ATTR_LARGE);
				if(base_type(type_name) != base_type(to_type))
					gen_convert(type_name, to_type);
			}
		}
		else { /*floating points: folded by FE unless it appears in a generic */
			tup = SIGNATURE(type_name);
			digs = (Node) tup[4];
			digits_int   = get_ivalue_int(digs);
			fmantissa    = float_mantissa(digits_int);
			fvalue       = (1.0-(pow(2.0, -(double) fmantissa)))
			  * pow(2.0, (4.0 * fmantissa));
			gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_float), real_const(fvalue));
		}
		break;
		/*  ("T_LAST"):  $ cf 'T_FIRST' */

	case(ATTR_O_LAST):
		gen_value(arg1);
		gen_kv(I_ATTRIBUTE, ATTR_O_LAST, get_ivalue(arg2));
		break;


		/*  ("T_LENGTH"): $ cf 'T_FIRST' */

	case(ATTR_O_LENGTH):
		gen_value(arg1);
		gen_kv(I_ATTRIBUTE, ATTR_O_LENGTH, get_ivalue(arg2));
		break;

	case(ATTR_MACHINE_EMAX):
		gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_integer), int_const(127));
		break;

	case(ATTR_MACHINE_EMIN):
		gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_integer), int_const(-128));
		break;

	case(ATTR_MACHINE_MANTISSA):
		gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_integer), int_const(24));
		break;

	case(ATTR_MACHINE_OVERFLOWS):
		gen_kv(I_PUSH_IMMEDIATE, mu_byte, int_const(TRUE));
		break;

	case(ATTR_MACHINE_RADIX):
		gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_integer), int_const(2));
		break;

	case(ATTR_MACHINE_ROUNDS):
		gen_kv(I_PUSH_IMMEDIATE, mu_byte, int_const(TRUE));
		break;

	case(ATTR_MANTISSA):
		type_name = N_UNQ(arg1);
		if (is_fixed_type(type_name)) {
			if (is_static_type(type_name) ) {
				tup = get_constraint(type_name);
				lbd_node = (Node) tup[2];
				ubd_node = (Node) tup[3];
				old_lbd = get_ivalue(lbd_node);
				old_ubd = get_ivalue(ubd_node);
				ivalue_int  = fx_mantissa(RATV(old_lbd), RATV(old_ubd),
				  RATV(small_of(type_name)));
				gen_kv(I_PUSH_IMMEDIATE, mu_word, int_const(ivalue_int));
			}
			else {
				/* Compute ratio between subtype's SMALL and base type's */
				/* SMALL and push it (always integer) */
				const_1 = small_of(type_name);
				const_2 = small_of(base_type(type_name));
				rvalue = rat_div(RATV(const_1), RATV(const_2));
				gen_kv(I_PUSH_IMMEDIATE, mu_word,
				  int_const(int_toi(int_quo(num(rvalue) , den(rvalue)))));
				gen_type_attr(type_name, ATTR_MANTISSA);
			}
		}
		else { /*floating points: folded by FE unless it appears in a generic */
			tup = SIGNATURE(type_name);
			digs = (Node) tup[4];
			digits_int       = get_ivalue_int(digs);
			ivalue_int       = float_mantissa(digits_int);
			gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_integer),
			  int_const(ivalue_int));
		}
		break;

		/*  ("POS"):      $ Transformed by expander */

	case(ATTR_PRED):
		type_name = N_UNQ(arg1);
		gen_value(arg2);
		gen_type_attr(type_name, ATTR_PRED);
		break;

		/*  ("T_RANGE"):  $ cf 'T_FIRST' */

	case(ATTR_O_RANGE):
		gen_value(arg1);
		gen_kv(I_ATTRIBUTE, ATTR_O_RANGE, get_ivalue(arg2));
		break;

	case(ATTR_SAFE_EMAX):
		gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_integer), int_const(127));
		break;

	case(ATTR_SAFE_LARGE):
		/* chaos("expr.c - untranslated code reached"); */
		gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_float),
		  real_const(ADA_MAX_REAL));
		break;

	case(ATTR_SAFE_SMALL):
		gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_float),
		  real_const(pow(2.0, -129.0)));
		break;

	case(ATTR_T_SIZE):
		type_name = N_UNQ(arg1);
		if (has_static_size(type_name)) {
		     repr_tup = REPR(type_name);
		     if (repr_tup != (Tuple)0) {
			    ivalue_int = (int) repr_tup[2]; 	  /* size */
			    gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_integer),
			  		   int_const(ivalue_int));
			 }
			 else { /* size representation not counted due to some error */
				gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_integer),
              		   int_const(BITS_SU * size_of(type_name)));
			 }
        }
		else {
			gen_type_attr(type_name, ATTR_SIZE);
		}
		break;

	case(ATTR_O_SIZE):

		/* The evaluation of this attribute has to evaluate the object
		 * because this evaluation may raise an exception, for example.
		 * Therefore we have a junk variable that is just used for this
		 * purpose. Since there is no O_SIZE attribute in the Ada machine, the
		 * size of the object is still calculated from T_SIZE
		 */

		type_name = get_type(N_AST2(node));
		if (is_simple_name (N_AST2 (node)) && !is_unconstrained (type_name)) {
			/* this is the simplest case */
			gen_type_attr(type_name, ATTR_SIZE);
		}
		else if ((!is_unconstrained(type_name)) && (!is_array_type(type_name))){
			/* the object has to be evaluated */
			junk_var = new_unique_name("junk");  /*TBSL:Reusing same variable */
			next_local_reference(junk_var);
			gen_ks(I_DECLARE, kind_of(type_name), junk_var);
			gen_value(N_AST2(node));
			gen_ksc(I_POP, kind_of(type_name), junk_var,
			  "Used only for eval. attr. size");
			gen_type_attr(type_name, ATTR_SIZE);
		}
		else {
			gen_value(N_AST2(node));
			gen_kv(I_ATTRIBUTE, ATTR_SIZE, int_const(0));
			if (is_array_type (type_name)) {
				 /* TBSL: Reusing same variable */
				junk_var    = new_unique_name("junk");
				next_local_reference(junk_var);
				gen_ks(I_DECLARE, kind_of(symbol_integer), junk_var);
				gen_ksc(I_POP, kind_of(symbol_integer), junk_var,
				  "Used only for eval. attr. size");
				gen_ks (I_DISCARD_ADDR, 1, (Symbol) 0);
				gen_ks(I_PUSH, kind_of(symbol_integer), junk_var);
			}
		}
		break;

	case(ATTR_SMALL):
		type_name = N_UNQ(arg1);
		to_type   = N_TYPE(node);
		if (is_fixed_type(type_name)) {
			type_small = small_of(type_name);
			root_small = small_of(base_type(type_name));
			if (is_fixed_type(to_type)) {
				rvalue_long = rat_tof(type_small, small_of(base_type(to_type)),
				  size_of(to_type));
				gen_kv(I_PUSH_IMMEDIATE, kind_of(to_type),
				  fixed_const(rvalue_long));
			}
			else {   /* convert to floating type */
				fvalue = rat_tor(RATV(type_small), ADA_REAL_DIGITS);
				gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_float),
				  real_const(fvalue));
			}
		}
		else { /*floating points: folded by FE unless it appears in a generic */
			tup = SIGNATURE(type_name);
			digs = (Node) tup[4];
			digits_int   = get_ivalue_int(digs);
			fmantissa    = float_mantissa(digits_int);
			fvalue       = pow(2.0, (-4.0*fmantissa-1.0));
			gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_float), real_const(fvalue));
		}
		break;

	case(ATTR_STORAGE_SIZE):
	    if (N_KIND(arg1) == as_all) { /* form of Obj.all'STORAGE_SIZE */
			type_name = get_type(N_AST1(arg1));
		}
		else {
			type_name = N_UNQ(arg1);
		}
		/*
		 * Since the collection size information is kept in the access
		 * template only , we must generate a reference to the base type 
		 * in the case of STORAGE_SIZE on a subtype.
	     */	
		if (NATURE(type_name) == na_subtype) {
		    type_name = base_type(type_name);
		}
		gen_type_attr(type_name, ATTR_STORAGE_SIZE);
		break;

	case(ATTR_SUCC):
		type_name = N_UNQ(arg1);
		gen_value(arg2);
		gen_type_attr(type_name, ATTR_SUCC);
		break;

	case(ATTR_TERMINATED):
		gen_value(arg1);
		gen_kv(I_ATTRIBUTE, ATTR_TERMINATED, int_const(0));
		break;

	case(ATTR_VAL):
		from_type = base_type(get_type(arg2));
		to_type   = N_TYPE(node);
		gen_value(arg2);
		gen_convert(from_type, to_type);
		gen_s(I_QUAL_RANGE, to_type);
		break;

	case(ATTR_VALUE):
		type_name = N_UNQ(arg1);
		gen_value(arg2);
		gen_type_attr(type_name, ATTR_VALUE);
		break;

	case(ATTR_WIDTH):
		type_name = N_UNQ(arg1);
		if (is_static_type(type_name)) {
			tup = SIGNATURE(type_name);
			low = (Node) tup[2];
			high = (Node) tup[3];
			low_value = get_ivalue (low);
			high_value = get_ivalue (high);

			/* this following test has been added because the bounds of the
			 * range may be not static. In the previous version there was an
			 * error during the get_ivalue_int
			 */

			if (low_value->const_kind == CONST_OM
			  || high_value->const_kind == CONST_OM)  {
				gen_type_attr(type_name, ATTR_WIDTH); 
			}
			else {
				low_int  = get_ivalue_int(low);
				high_int = get_ivalue_int(high);
				if (is_integer_type(type_name)) {
					if (low_int > high_int)
						gen_kv(I_PUSH_IMMEDIATE, mu_word, int_const(0));
					else {
						char *val_str = emalloct(10, "gen-attr-wid-1");
						low_int =  abs (low_int);
						high_int = abs (high_int);
						ivalue_int = (low_int > high_int ? low_int : high_int);
						sprintf(val_str, " %d", ivalue_int);
						ivalue_int = strlen(val_str);
						efreet(val_str, "gen-attr-wid-2");
						gen_kv(I_PUSH_IMMEDIATE, mu_word,int_const(ivalue_int));
					}
				}
				/* following code does not work for bool and char.
				 * disable for now.
				 */
				else {	 /* Enumeration types */
					int len, v;
					tup = (Tuple) literal_map(root_type(type_name));
					ivalue_int = 0;
					for (i = 1; i <= tup_size(tup); i += 2) {
						len = strlen(tup[i]);
						v = (int) tup[i+1];
						if (len > ivalue_int && (v >= low_int && v <= high_int))
						  ivalue_int = len;
					}
					gen_kv(I_PUSH_IMMEDIATE, mu_word, int_const(ivalue_int));
				}
			} 
		}
		else { /* Not static types */
			gen_type_attr(type_name, ATTR_WIDTH);
		}
		break;

	default:
		compiler_error("Unexpected attribute ");
	}
}

static int float_mantissa(int digits)					/*;float_mantissa*/
{
	return (digits < 4 ? (3 * digits + 2) : (3 * digits + 3) );
}

static void gen_type_attr(Symbol type_name, int a_attribute) /*;gen_type_attr*/
{
	gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
	gen_kv(I_ATTRIBUTE, a_attribute, int_const(0));
}

void gen_convert(Symbol from_type, Symbol to_type)			/*;gen_convert*/
{
	if (is_fixed_type(from_type) && is_integer_type(to_type)) {
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, from_type);
		gen_s(I_CONVERT_TO, symbol_dfixed);
		from_type = symbol_dfixed;
	}
	else if (is_integer_type(from_type) && is_fixed_type(to_type)) {
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, from_type);
		gen_s(I_CONVERT_TO, symbol_dfixed);
		from_type = symbol_dfixed;
	}
	if (!is_array_type(from_type)) {
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, from_type);
	}
	if (is_array_type(to_type) && is_unconstrained(to_type)) {
		gen_s(I_QUAL_SUB, to_type);
	}
	else {
		gen_s(I_CONVERT_TO, to_type);
	}
}

void gen_access_qual(int qualifier, Symbol type_name)		/*;gen_access_qual*/
{
	Symbol	null_access;

	gen_k(I_DUPLICATE, mu_addr);
	gen_s(I_PUSH_EFFECTIVE_ADDRESS, symbol_null);
	gen_k(I_COMPARE, mu_addr);
	null_access = new_unique_name("null_access");
	gen_s(I_JUMP_IF_TRUE, null_access);
	if (qualifier == as_qual_index) {
		gen_k(I_DUPLICATE, mu_addr);
		gen_k(I_DEREF, mu_dble);
		gen_s(I_QUAL_INDEX, type_name);
		gen_ks(I_DISCARD_ADDR, 2, (Symbol)0);
	}
	else if (qualifier == as_qual_discr) {
		/* Note: an access to a record type does not require
		 * any derefencing!
		 */
		gen_s(I_QUAL_DISCR, type_name);
	}
	else
		compiler_error("Illegal access qual");
	gen_s(I_LABEL, null_access);
}

Segment array_ivalue(Node node)							/*;array_ivalue*/
{
	/* Returns the ivalue part of an array object, i.e. a segment having the
	 * size of the object, with all static components initialized
	 * In C, the returned value is a Segment.
	 */

	Node   static_node, selector_node, val_node, static_comp_node,
	  access_node, list_node;
	Symbol	obj_type, comp_type, selector_name;
	Tuple	tup, subscript_list;  /* tuple(integer); */
	int		offset, i, index, comp_size, str_len, nk, n;
	Segment	res, obj_value;
	Tuple	tupstr, index_list;
	Const	exprv;
	Fortup	ft1;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("ARRAY_IVALUE", node);
#endif

	nk = N_KIND(node);
	if (nk == as_string_ivalue) {
		/*  CASE 1.  String
		 *    Create a segment and copy the characters from the string tuple   
		 *    to the data segment
		 */
		tupstr = (Tuple) N_VAL(node);
		n = tup_size(tupstr);
		res = segment_new(SEGMENT_KIND_DATA, n);
		for (i = 1; i <= n; i++)
			segment_put_word(res, (int) tupstr[i]);
		return res;
	}
	else if (nk == as_array_aggregate || nk == as_array_ivalue) {
		/* CASE 2:  arr_aggreagate -or- array_ivalue
		 *  Note: obj_type may be unconstrained in the case where the array 
		 *  subtype is identical to the base type. (not "really" unconstrained).
		 */
		static_node = N_AST1(N_AST1(node)); 
		obj_type = N_TYPE(node);
		if (!has_static_size(obj_type)) {
			compiler_error("Ivalue of not static size array aggr.");
			return segment_new(SEGMENT_KIND_DATA, 0);
		}
		/* Step 1:  Create a segment and initialize it */
		obj_value = segment_new(SEGMENT_KIND_DATA, size_of(obj_type));
		for (i = 0; i < size_of(obj_type); i++)
			segment_put_word(obj_value, 0);
		/* Step 2:  Calculate the offset for each static component */
		FORTUP(static_comp_node = (Node), N_LIST(static_node), ft1);
			offset      = 0;
			access_node = N_AST1(static_comp_node);
			val_node    = N_AST2(static_comp_node);
			while (!is_simple_name(access_node)) {
				if (N_KIND(access_node) == as_index){
					list_node   = N_AST2(access_node);
					access_node = N_AST1(access_node);
					obj_type    = get_type(access_node);
					tup         = SIGNATURE(obj_type);
					index_list  = (Tuple) tup[1];
					comp_type   = (Symbol) tup[2];
					comp_size   = size_of(comp_type);
					subscript_list = N_LIST(list_node);
					index       = compute_index(subscript_list, index_list);
					offset      += index*comp_size;
				}
				else if (N_KIND(access_node) == as_selector) {
					selector_node = N_AST2(access_node);
					access_node   = N_AST1(access_node);
					obj_type      = get_type(access_node);
					selector_name = N_UNQ (selector_node);
					comp_type     = TYPE_OF(selector_name);
					offset       += FIELD_OFFSET(selector_name);
				}
				else {
					compiler_error("Incoherent access list in array agg.");
					break;
				}
			}

			/* Step 3:  Copy the component value into the correct position
			 * in the segment
			 */
			if (N_KIND(val_node) == as_string_ivalue) {
				segment_set_pos(obj_value, (unsigned) offset, 0);
				tup = (Tuple) N_VAL(val_node);
				str_len = tup_size(tup);
				for (i = 1; i <= str_len; i++)
					segment_put_word(obj_value, (int) tup[i]);
			}
			else if (N_KIND(val_node) == as_ivalue
		      || N_KIND(val_node) == as_int_literal
		      || N_KIND(val_node) == as_real_literal) {
				exprv = get_ivalue(val_node);
				comp_type = N_TYPE(val_node);
				if (is_fixed_type(comp_type)) {
					/* we have to take into account if the node val is fixed */
					exprv = fixed_const(rat_tof( exprv,
				   	  small_of(base_type(comp_type)), size_of(comp_type)));
				}
	    		if (is_const_uint(exprv)) {
	  				/* try to convert universal integer to integer */
   					i= int_toi(UINTV(exprv));
     				if (arith_overflow) {/* if cannot convert to integer */
						    chaos("cannot convert uint to int in array_ivalue");
	     			}
					exprv = int_const(i);
	   			}
				segment_set_pos(obj_value, offset, 0);
				segment_put_const(obj_value, exprv);

				/* segment_set_pos(obj_value, (unsigned) offset, 0);
				 * segment_put_const(obj_value, get_ivalue(val_node));
				 */
			}
			else {
				compiler_error("Static comp in array aggregate not ivalue");
			}
		ENDFORTUP(ft1);
	}
	/* there was an error message here */
	return obj_value;
}

Segment record_ivalue(Node node)						/*;record_ivalue*/
{
	/* Returns the ivalue part of a record object, i.e. a tuple having the
	 * size of the object, with all static components initialized
	 * In C, the returned value is a segment.
	 */

	Node	static_node, selector_node, val_node;
	Node	static_comp_node, access_node, list_node;
	Symbol	obj_type, comp_type, selector_name;
	Segment	obj_value;  /* tuple(integer); */
	int		i, index, comp_size, nk;
	Fortup	ft1;
	Segment	sval;
	Const       exprv;
	Tuple	tup, subscript_list, index_list;
	unsigned	offset;
	Segment     tempseg;

	sval = segment_new(SEGMENT_KIND_DATA, 1);
	nk = N_KIND(node);
	if (nk == as_record_aggregate || nk == as_record_ivalue) {
		static_node = N_AST1(N_AST1(node));
		/*init_node = N_AST2(node); -- init_node not used  ds 7-8-85 */
		/*name_node = N_AST3(node); -- name_node not used  ds 7-8-85*/
		obj_type  = N_TYPE(node);

		if (! has_static_size(obj_type)) {
			compiler_error("Ivalue of not static size record aggr.");
			return sval;
		}
		/* TBSL: see that obj_value properly intialized  ds 6-26-85*/
		obj_value = segment_new(SEGMENT_KIND_DATA, size_of(obj_type));
		/* obj_value = [1..size_of(obj_type)];*/

		FORTUP(static_comp_node = (Node), N_LIST(static_node), ft1);
			offset   = 0; /* a segment start at position 0 in c version */
			access_node = N_AST1(static_comp_node);
			val_node = N_AST2(static_comp_node);
			while (! is_simple_name(access_node)) {
				nk = N_KIND(access_node);
				if (nk == as_index) {
					list_node= N_AST2(access_node);
					access_node = N_AST1(access_node);
					obj_type    = get_type(access_node);
					tup = SIGNATURE(obj_type);
					index_list = (Tuple) tup[1];
					comp_type = (Symbol) tup[2];
					comp_size = size_of(comp_type);
					subscript_list = N_LIST(list_node);
					index = compute_index(subscript_list, index_list);
					offset += index*comp_size;
				}
				else if (nk == as_selector) {
					selector_node = N_AST2(access_node);
					access_node = N_AST1(access_node);
					obj_type = get_type(access_node);
					selector_name = N_UNQ(selector_node);
					comp_type = TYPE_OF(selector_name);
					offset += FIELD_OFFSET(selector_name);
				}
				else {
					compiler_error("Incoherent access list in record agg.");
					break;
				}
			}

			/* We have now reached a simple type ivalue */
			nk = N_KIND(val_node);
			if (nk == as_string_ivalue) {
				tup = (Tuple) N_VAL(val_node);
				segment_set_pos(obj_value, offset, 0);
				for (i = 1; i<= tup_size(tup); i++)
					segment_put_int(obj_value, (int) tup[i]);
			}
			else if (nk == as_array_ivalue) {
				tempseg = array_ivalue(val_node);
				segment_set_pos(obj_value, offset, 0);
				for (i = 0; i < segment_get_maxpos(tempseg); i ++) {
					segment_put_int(obj_value,
					  (int) segment_get_int(tempseg, i));
				}
			}
			else if (nk == as_ivalue || nk == as_int_literal
			  || nk == as_real_literal) {
				exprv = get_ivalue(val_node);
				comp_type = N_TYPE(val_node);
				if (is_fixed_type(comp_type)) {
					exprv = fixed_const(rat_tof( exprv,
				      small_of(base_type(comp_type)), size_of(comp_type)));
				}
				segment_set_pos(obj_value, offset, 0);
				segment_put_const(obj_value, exprv);
			}
			else
				compiler_error("Static component in aggregate not ivalue");
		ENDFORTUP(ft1);
	}
	else {
		compiler_error_k("Not implemented : ", val_node);
		compiler_error("record_ivalue - unknown node kind");
	}
	/*
	 * Initialize the rest of the segment with zeros. Note that this value
	 * has to be the same in intb.c - create_struc.
	 * This affects only unconstrained records.
	 */
	segment_set_pos(obj_value, (unsigned) segment_get_maxpos(obj_value), 0);
	for (i = segment_get_pos(obj_value); i < size_of(obj_type); i++) {
		segment_put_int(obj_value, 0);
	}
	return obj_value;
}

static int code_map(Symbol opcode)		/*;code_map*/
{
	code_map_defined = TRUE; /* assume can map to machine instruction */
	if (opcode == symbol_and) return        I_AND;
	else if (opcode == symbol_or) return         I_OR;
	else if (opcode == symbol_xor) return        I_XOR;

	else if (opcode == symbol_eq) return          I_IS_EQUAL;
	else if (opcode == symbol_ne) return         I_NOT;
	else if (opcode == symbol_le) return         I_IS_LESS_OR_EQUAL;
	else if (opcode == symbol_gt) return          I_IS_GREATER;
	else if (opcode == symbol_ge) return         I_IS_GREATER_OR_EQUAL;
	else if (opcode == symbol_lt) return          I_IS_LESS;

	else if (opcode == symbol_addi) return         I_ADD;
	else if (opcode == symbol_subi) return         I_SUB;
	else if (opcode == symbol_addfx) return        I_ADD;
	else if (opcode == symbol_subfx) return        I_SUB;

	else if (opcode == symbol_muli) return         I_MUL;
	else if (opcode == symbol_divi) return         I_DIV;
	else if (opcode == symbol_remi) return       I_REM;
	else if (opcode == symbol_modi) return       I_MOD;
	else if (opcode == symbol_expi) return        I_POW;

	else if (opcode == symbol_addfl) return        I_FLOAT_ADD;
	else if (opcode == symbol_subfl) return        I_FLOAT_SUB;
	else if (opcode == symbol_mulfl) return        I_FLOAT_MUL;
	else if (opcode == symbol_divfl) return        I_FLOAT_DIV;
	else if (opcode == symbol_expfl) return       I_FLOAT_POW;

	else if (opcode == symbol_mulfix) return       I_FIX_MUL;
	else if (opcode == symbol_mulfxi) return       I_FIX_MUL;
	else if (opcode == symbol_mulfx) return        I_FIX_MUL;
	else if (opcode == symbol_divfxi) return       I_FIX_DIV;
	else if (opcode == symbol_divfx) return        I_FIX_DIV;
	else {
		code_map_defined = FALSE;
		return 0;
	}
}
