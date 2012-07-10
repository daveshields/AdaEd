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
#include "dbxprots.h"
#include "namprots.h"
#include "procprots.h"
#include "exprprots.h"
#include "setprots.h"
#include "genprots.h"
#include "statprots.h"
#include "miscprots.h"
#include "gmiscprots.h"
#include "smiscprots.h"
#include "segmentprots.h"
#include "declprots.h"
#include "typeprots.h"
#include "packprots.h"
#include "gutilprots.h"
#include "axqrprots.h"
#include "sepprots.h"
#include "maincaseprots.h"

static void compile_line();

void compile(Node node)											/*;compile*/
{
	/* Generates one TREE statement */

	Node 	expr_node;
	Symbol	junk_var;
	Tuple	case_table;
	Tuple	tup;
	Const	cond_val;
	Tuple	labtup;
	int		lablev;

	Node	
	  pre_node, post_node, decl_node, id_list_node, type_node, init_node,
	  stmt_node, var_node, exp_node, if_list_node, else_node, cond_node,
	  body_node, cases_node, id_node, stmts_node, handler_node, proc_node,
	  args_node, obj_node, package_tasks_node,
	  entry_node, alt_node, acc_node, delay_node, call_node, stmts1_node,
	  stmts2_node, task_node, separate_unit_node, label_node, others_node,
	  n, temp_node;
	Tuple   condition_list, id_list, task_list, select_list, case_bodies;
	Symbol   label_name, type_name, proc_name, new_name, old_name, entry_name,
	  exception_name, package_tasks_name, else_part, dont_exit, end_if,
	  true_guard, end_alt, i_subt;
	Tuple   except_names, predef_tuple;
	Tuple		labs;
	int		nesting_depth, lineno, flag, tag, i;
	int		guarded;
	/* DECL */
	Fortup	ft1;
	int         function_code;
	Const	ival;
	int		ikind;
	Segment	init_val;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("COMPILE", node);
#endif

#ifdef DEBUG
	if (trapns>0 && N_SEQ(node) == trapns && N_UNIT(node) == trapnu)trapn(node);
#endif
	switch(N_KIND(node)) {

	case(as_opt):          /* OPT_NODE */
		break;

	case(as_deleted):      /* Deleted by expander */
		break;

	case(as_insert):       /* Inserted by expander */
		FORTUP(pre_node=(Node), N_LIST(node), ft1);
			compile(pre_node);
		ENDFORTUP(ft1);
		post_node = N_AST1(node);
		compile(post_node);
		break;

	case(as_discard):     /* Some check to evaluate and discard */
		expr_node = N_AST1(node);
		junk_var    = new_unique_name("junk"); /* TBSL: Reusing same variable */
		next_local_reference(junk_var);
		gen_ks(I_DECLARE, kind_of(N_TYPE(node)), junk_var);

		gen_value(expr_node);
		gen_ksc(I_POP, kind_of(N_TYPE(node)), junk_var, "Used only for check");
		break;

	/* Chapter 2. Lexical elements
	 *------------
	 * 2.8 Pragmas
	 */
	case(as_pragma):       /*TBSL(JC)    pragmas */
		break;

	case(as_arg):          /*TBSL(JC)    arguments for pragmas */
		break;

	/* Chapter 3. Declarations and types */
	case(as_labels):
		break;

	/* 3.1 Declarations */
	case(as_declarations):
		FORTUP(decl_node=(Node), N_LIST(node), ft1);
			compile(decl_node);
		ENDFORTUP(ft1);
		break;

	/* 3.2 Objects and named numbers */
	case(as_const_decl):
		id_list_node = N_AST1(node);
		type_node = N_AST2(node);
		init_node = N_AST3(node);

		/* Generate pre-statements */
		while (N_KIND(init_node) == as_insert) {
			FORTUP(pre_node=(Node), N_LIST(init_node), ft1);
				compile(pre_node);
			ENDFORTUP(ft1);
			init_node = N_AST1(init_node);
		}

		id_list   = N_LIST(id_list_node);
		type_name = N_UNQ(type_node);
		create_object(id_list, type_name, init_node, TRUE);

		TASKS_DECLARED |= (int) CONTAINS_TASK(type_name);
		break;

	case(as_obj_decl):
		id_list_node = N_AST1(node);
		type_node = N_AST2(node);
		init_node = N_AST3(node);

		/* Generate pre-statements */
		while (N_KIND(init_node) == as_insert) {
			FORTUP(pre_node=(Node), N_LIST(init_node), ft1);
				compile(pre_node);
			ENDFORTUP(ft1);
			init_node = N_AST1(init_node);
		}

		id_list   = N_LIST(id_list_node);
		type_name = N_UNQ(type_node);
		create_object(id_list, type_name, init_node, FALSE);

		TASKS_DECLARED |= (int)CONTAINS_TASK(type_name);
		break;

	case(as_num_decl):
		break;

	/* 3.3 Types and subtypes */
	case(as_type_decl):
		id_node = N_AST1(node);
		type_name = N_UNQ(id_node);
		gen_type(type_name);
		break;

	case(as_subtype_decl):
		id_node = N_AST1(node);
		type_name = N_UNQ(id_node);
		gen_subtype(type_name);
		break;

	/* Chapter 5. Statements */
	case(as_null_s):
		break;

	case(as_line_no):
		NB_STATEMENTS += 1;
		lineno = (int) N_VAL(node);
		ada_line = lineno;
#ifdef MACHINE_CODE
		if (debug_line > 0 && lineno >= debug_line)
			compile_line();
#endif
		if (line_option)
			gen_i(I_STMT, lineno);
		break;

	/* 5.1 Simple and compound statements */
	case(as_statements):
		stmts_node = N_AST1(node);
		label_node = N_AST2(node);
		labs = tup_new(0);
		FORTUP(n=(Node), N_LIST(label_node), ft1);
			if (!tup_mem((char *) N_UNQ(n), labs))
				labs =tup_with(labs, (char *)N_UNQ(n));
		ENDFORTUP(ft1);
		FORTUP(label_name=(Symbol), labs, ft1);
			labelmap_put(label_name, LABEL_STATIC_DEPTH, (char *)CURRENT_LEVEL);
			next_local_reference(label_name);
			gen_s(I_SAVE_STACK_POINTER, label_name);
		ENDFORTUP(ft1);
		FORTUP(stmt_node=(Node), N_LIST(stmts_node), ft1);
			compile(stmt_node);
		ENDFORTUP(ft1);
		tup_free(labs);
		break;

	case(as_statement):
		label_node = N_AST1(node);
		stmt_node = N_AST2(node);
		labs = tup_new(0);
		FORTUP(n=(Node), N_LIST(label_node), ft1);
			if (!tup_mem((char *) N_UNQ(n), labs))
				labs =tup_with(labs, (char *) N_UNQ(n));
		ENDFORTUP(ft1);
		FORTUP(label_name=(Symbol), labs, ft1);
			gen_s(I_LABEL, label_name);
		ENDFORTUP(ft1);
		compile(stmt_node);
		tup_free(labs);
		break;

	/* 5.2 Assignment statement */
	case(as_assignment): 
	case(as_static_comp):
		var_node = N_AST1(node);
		exp_node = N_AST2(node);
		type_name           = get_type(var_node);
		select_assign(var_node, exp_node, type_name);
		break;

	/*  5.3 If statement */
	case(as_if):
		if_list_node = N_AST1(node);
		else_node = N_AST2(node);
		end_if = new_unique_name("end_if");
		condition_list  = tup_copy(N_LIST(if_list_node));
		/* tup_copy needed since condition_list used in tup_fromb below */
		while (tup_size(condition_list)) {
			n = (Node) tup_fromb(condition_list);
			cond_node = N_AST1(n);
			body_node = N_AST2(n);
			else_part = new_unique_name("else");
			gen_condition(cond_node, else_part, FALSE);
			compile(body_node);
			if ((tup_size(condition_list) != 0) || (else_node != OPT_NODE))
				gen_s(I_JUMP, end_if);
			gen_s(I_LABEL, else_part);
		}

		if (else_node != OPT_NODE)
			compile(else_node);

		gen_s(I_LABEL, end_if);
		break;

	/* 5.4 Case statements */
	case(as_case):
		exp_node = N_AST1(node);
		cases_node = N_AST2(node);
		gen_value(exp_node);
		tup = make_case_table(cases_node);
		case_table = (Tuple) tup[1];
		case_bodies = (Tuple) tup[2];
		others_node = (Node) tup[3];
		gen_case(case_table, case_bodies, others_node,
		  kind_of(get_type(exp_node)));
		break;

	/* 5.5 Loop statements */
	case(as_loop):
		gen_loop(node);
		break;

	/* 5.6 Block statements */
	case(as_block):
		id_node = N_AST1(node);
		decl_node = N_AST2(node);
		stmts_node = N_AST3(node);
		handler_node = N_AST4(node);
		compile_body(decl_node, stmts_node, handler_node, TRUE);
		break;

	case(as_end):
		gen(I_EXIT_BLOCK);
		break;

	/* 5.7 Exit statements */
	case(as_exit):
		cond_node = N_AST2(node);
		label_name     = N_UNQ(node);
		if (cond_node != OPT_NODE) {
			dont_exit = new_unique_name("continue");
			gen_condition(cond_node, dont_exit, FALSE);
		}
		labtup = labelmap_get(label_name);
		if (labtup == (Tuple)0)
			chaos("as_exit label map undefined");
		lablev = (int) labtup[LABEL_STATIC_DEPTH];
		for (i = lablev;i<CURRENT_LEVEL; i++)
			gen(I_EXIT_BLOCK);
		gen_s(I_RESTORE_STACK_POINTER, label_name);
		gen_s(I_JUMP, label_name);
		if (cond_node != OPT_NODE)
			gen_s(I_LABEL, dont_exit);
		break;

	/* 5.8 Return statements */
	case(as_return):
		exp_node = N_AST1(node);
		id_node = N_AST2(node);
		proc_name           = N_UNQ(id_node);
		nesting_depth       = (int) N_VAL(N_AST3(node));

		if (NATURE(proc_name) == na_entry
		  || NATURE(proc_name) == na_entry_family) {
			/* Entry return */
			for (i=1; i<=nesting_depth; i++)
				gen(I_LEAVE_BLOCK);
			/* allocate symbol for return target label if not yet allocated
      		 * (see comments in gen_accept() for details)
      		 */
			if (symbol_accept_return == (Symbol)0)
				symbol_accept_return = new_unique_name("end_handler");
			gen(I_EXIT_BLOCK);
			gen_s(I_JUMP, symbol_accept_return);
		}
		else {
			if ( exp_node != OPT_NODE) {
				if (N_KIND (exp_node) == as_raise) {
					/* the result of the function raises an exception */
					if (N_AST1 (exp_node) != OPT_NODE) {
						gen_s(I_LOAD_EXCEPTION_REGISTER,
						  N_UNQ(N_AST1(exp_node)));
					}
					gen(I_RAISE);
				}
				else {
					/* Function return */
					gen_value(exp_node);
					type_name = N_TYPE(exp_node);
					if (is_simple_type(type_name)) {
						gen_ks(I_RETURN, kind_of(type_name),
						  assoc_symbol_get(proc_name, RETURN_TEMPLATE));
					}
					else {
						if (is_record_type(type_name)) {
							gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
						}
						gen_s(I_RETURN_STRUC,
						    assoc_symbol_get(proc_name, RETURN_TEMPLATE));
					}
				}
			}
			for (i = 0; i <= nesting_depth; i++) {
				gen(I_LEAVE_BLOCK);
			}
		}
		break;

	/* 5.9 Goto statements */
	case(as_goto):
		id_node  = N_AST1(node);
		label_name = N_UNQ(id_node);
		labtup = labelmap_get(label_name);
		if (labtup == (Tuple)0)
			chaos("as_goto label map undefined");
		lablev = (int) labtup[LABEL_STATIC_DEPTH];
		for (i=lablev; i<CURRENT_LEVEL; i++)
			gen(I_EXIT_BLOCK);
		gen_s(I_RESTORE_STACK_POINTER, label_name);
		gen_s(I_JUMP, label_name);
		break;

	/* Chapter 6. Subprograms */
	case(as_predef):
		break;
	case(as_interfaced):
		break;

	/* 6.1 Subprogram declarations */
	case(as_subprogram_decl_tr):
		gen_subprogram_spec(node);
		break;

	/* 6.3 Subprogram bodies */
	case(as_subprogram_tr):
		gen_subprogram(node);
		break;

	/* 6.4 Subprogram calls */
	case(as_call): 
	case(as_init_call):
		proc_node = N_AST1(node);
		args_node = N_AST2(node);
		proc_name              = N_UNQ(proc_node);
		while (is_renaming(proc_name))
			proc_name = ALIAS(proc_name);
		gen_prelude(proc_name, args_node);

		/* we must check that this is a real proc, and not some predef stuff */
		predef_tuple = (Tuple) MISC(proc_name);
		if (predef_tuple!=(Tuple)0) {
			/* predefined operation */
			function_code = (int) predef_tuple[1];
			/* the predefined functions are mapped to integers lesser than 256
      		 * whereas the interfaced procedures are mapped to integers greater
      		 * than 256
			 */
			if (function_code < 255) {
				type_name = (Symbol) predef_tuple[2];
				if (type_name != OPT_NAME) {
					gen_sc(I_PUSH_EFFECTIVE_ADDRESS, type_name,
					  "discarded by predef");
				}
				gen_ic(I_CALL_PREDEF, function_code, "predef");
			}
			else {
				gen_ic(I_CALL_INTERFACE, function_code, "interfaced");
			}
		}
		else {
			gen_s(I_CALL, proc_name);
		}
		gen_postlude(proc_name, args_node);
		break;

	/* Chapter 7. Packages
	 * 7.2 Package specifications and declarations
	 */
	case(as_package_spec):
		gen_package(node);
		break;

	/* 7.3 Package bodies */
	case(as_package_body):
		gen_package_body(node);
		break;

	/* 7.4 Private type and deferred constant declarations */
	case(as_private_decl):
		break;

	/* Chapter 8. Visibility rules */

	/* 8.5 Renaming declarations */
	case(as_rename_obj):
		id_node = N_AST1(node);
		type_node = N_AST2(node);
		obj_node = N_AST3(node);
		new_name = N_UNQ(id_node);

		if (is_ivalue(obj_node) && is_simple_type(N_UNQ(type_node))) {
				ival = get_ivalue(obj_node);
				ikind = ival->const_kind;
				if(ikind == CONST_INT) {
					init_val = segment_new(SEGMENT_KIND_DATA, 1);
					segment_put_word(init_val, ival->const_value.const_int);
				}
				else if(ikind == CONST_REAL) {
					init_val = segment_new(SEGMENT_KIND_DATA, 1);
					segment_put_real(init_val, ival->const_value.const_real);
				}
				else {
#ifdef DEBUG
					printf("const_kind %d\n", ikind);
#endif		
					chaos("as_rename_object:unsupported kind");
				}
				old_name = get_constant_name(init_val);
				assign_same_reference(new_name, old_name);
				if (!is_renaming(old_name)) {
					ALIAS(new_name) = (Symbol) 0; /* not a renaming any more */
				}
		}
		else if (is_simple_name(obj_node)) {
			old_name = N_UNQ(obj_node);
			assign_same_reference(new_name, old_name);
			ASSOCIATED_SYMBOLS(new_name) = ASSOCIATED_SYMBOLS(old_name);
			if (TYPE_OF(new_name) != TYPE_OF(old_name))
				TYPE_OF(new_name) = TYPE_OF(old_name);
			if (!is_renaming(old_name)) {
				ALIAS(new_name) = (Symbol) 0;     /* not a renaming any more */
			}
		}
		else if (CURRENT_LEVEL > 1) {
			next_local_reference(new_name);
			gen_address(obj_node);
			type_name = get_type(id_node);
			if (is_array_type(type_name)) {
				if (N_KIND(obj_node) == as_all) {
					i_subt = new_unique_name("dyn_(sub)type");
					new_symbol(i_subt,NATURE(type_name),TYPE_OF(type_name),
						SIGNATURE(type_name), root_type(type_name));
					gen_type(i_subt);
					type_name = i_subt;
					TYPE_OF(N_UNQ(id_node)) = type_name;
				}
				/* the address of the type is pushed by gen_address */
				if (N_KIND(obj_node) == as_slice || N_KIND(obj_node) == as_all) {
					gen_s(I_UPDATE_AND_DISCARD,type_name);
				}
				else {
					gen_ks(I_DISCARD_ADDR,1,(Symbol)0);
				}
			}
			gen_s(I_UPDATE_AND_DISCARD, new_name);
		}
		else {
			next_global_reference_r(new_name, 0, 0);
			gen_address(obj_node);
			gen_ks(I_POP, mu_addr, new_name);
		}
		break;

	case(as_rename_ex):
		break;

	case(as_rename_pack):
		break;

	/* Chapter 9. Tasks
	 * 9.1 Task specifications and task bodies
	 * Task body transformed into procedure by expander
	 *------------------------------------------------
	 * 9.3 Task Execution - Task Activation
	 */
	case(as_activate_spec):		/* used internally only */
		package_tasks_node = N_AST1(node);
		package_tasks_name   = N_UNQ(package_tasks_node);
		gen_ks(I_PUSH, mu_word, package_tasks_name);
		gen(I_LINK_TASKS_DECLARED);
		gen(I_ACTIVATE);
		break;

	case(as_end_activation):
		tag = (int) N_VAL(node);
		if (tag == 1)
			gen_ic(I_END_ACTIVATION, tag, "Ok");
		else
			gen_ic(I_END_ACTIVATION, tag, "Failed");
		break;

	/* 9.4 Task Dependance - Termination of Tasks */
	case(as_terminate):
		tup = (Tuple) N_VAL(node);
		nesting_depth = (int) tup[1];
		tag = (int) tup[2];
		for (i=1; i<=nesting_depth; i++)
			gen(I_LEAVE_BLOCK);
		gen_i(I_TERMINATE, tag);
		break;

	/* 9.5 Entries, entry calls, and accept statements */
	case(as_ecall):
		entry_node = N_AST1(node);
		args_node = N_AST2(node);
		gen_value(entry_node);
		id_node = N_AST2(entry_node);
		entry_name = N_UNQ(id_node);
		gen_prelude(entry_name, args_node);
		gen_i(I_ENTRY_CALL, TYPE_SIZE(entry_name));
		gen_postlude(entry_name, args_node);
		break;

	case(as_accept):
		entry_node = N_AST1(node);
		body_node = N_AST3(node);
		id_node = N_AST2(entry_node);
		entry_name    = N_UNQ(id_node);
		gen_value(entry_node);
		gen_ic(I_SELECTIVE_WAIT, 0, "simple accept");
		gen_accept(entry_name, body_node, OPT_NODE);
		break;

	/* 9.6 Delay statements, duration and time */
	case(as_delay):
		exp_node = N_AST1(node);
		gen_value(exp_node);
		gen(I_WAIT);
		break;

	/* 9.7 Select statements */
	case(as_selective_wait):
		/* Note: Else part added as a delay 0 in alt_list by expander */
		alt_node = N_AST1(node);
		select_list  = N_LIST(alt_node);

	case_table  = tup_new(0);
	case_bodies = tup_new(0);
		tag = 0;
		FORTUP(stmt_node=(Node), select_list, ft1);
			tag += 1;
			if (N_KIND(stmt_node) == as_guard) {
				cond_node = N_AST1(stmt_node);
				stmt_node = N_AST2(stmt_node);
				gen_value(cond_node);
				guarded = TRUE;
			}
			else {
				gen_kvc(I_PUSH_IMMEDIATE, kind_of(symbol_boolean),
				  int_const(TRUE), "True guard");
				guarded = FALSE;
			}

			if (N_KIND(stmt_node)== as_accept_alt) {
				acc_node = N_AST1(stmt_node);
				body_node = N_AST2(stmt_node);
				entry_node = N_AST1(acc_node);
				id_node = N_AST2(entry_node);
				entry_name = N_UNQ(id_node);

				flag = 1;
				if (guarded) {
					cond_val = get_ivalue(cond_node);
					if (cond_val->const_kind!=CONST_OM  ) {
						if (cond_val->const_value.const_int == ada_bool(TRUE)) {
							gen_value(entry_node);
						}
						else {
							gen_kvc(I_PUSH_IMMEDIATE, mu_byte, int_const_0,
						      "dummy member");
							gen_kvc(I_PUSH_IMMEDIATE, mu_word, int_const_0,
						      "dummy family");
						}
					}
					else {
						gen_k(I_DUPLICATE, kind_of(symbol_boolean));
						true_guard = new_unique_name("true_guard");
						gen_s(I_JUMP_IF_TRUE, true_guard);
						gen_kvc(I_PUSH_IMMEDIATE, mu_byte, int_const_0,
						  "dummy member");
						gen_kvc(I_PUSH_IMMEDIATE, mu_word, int_const_0,
						  "dummy family");
						end_alt = new_unique_name("end_alt");
						gen_s(I_JUMP, end_alt);
						gen_s(I_LABEL, true_guard);
						gen_value(entry_node);
						gen_s(I_LABEL, end_alt);
					}
				}
				else {
					gen_value(entry_node);
				}

			}
			else if (N_KIND(stmt_node) == as_delay_alt) {
				delay_node = N_AST1(stmt_node);
				delay_node = N_AST1(delay_node);
				flag = 2;
				if (guarded) {
					cond_val = get_ivalue(cond_node);
					if (cond_val->const_kind != CONST_OM  ) {
						if (cond_val->const_value.const_int == ada_bool(TRUE)) {
							gen_value(delay_node);
						}
						else {
							gen_kvc(I_PUSH_IMMEDIATE, kind_of(symbol_duration), 
						      int_const_0, "dummy duration");
						}
					}
					else {
						gen_k(I_DUPLICATE, kind_of(symbol_boolean));
						true_guard = new_unique_name("true_guard");
						gen_s(I_JUMP_IF_TRUE, true_guard);
						gen_kvc(I_PUSH_IMMEDIATE, kind_of(symbol_duration), 
					      int_const_0, "dummy duration");
						end_alt = new_unique_name("end_alt");
						gen_s(I_JUMP, end_alt);
						gen_s(I_LABEL, true_guard);
						gen_value(delay_node);
						gen_s(I_LABEL, end_alt);
					}
				}
				else {
					gen_value(delay_node);
				}

			}
			else if (N_KIND(stmt_node) == as_terminate_alt) {
				flag = 3;
			}

			gen_kv(I_PUSH_IMMEDIATE, mu_byte, int_const(flag));
			tup = tup_new(2);
			tup[1] = (char *) tag;
			tup[2] = (char *) tag;
			case_table  =tup_with(case_table, (char *)tup);
			case_bodies = tup_with(case_bodies, (char *) stmt_node);

		ENDFORTUP(ft1);

		gen_i(I_SELECTIVE_WAIT, tup_size(select_list));

		gen_case(case_table, case_bodies, OPT_NODE, mu_byte);
		break;

	case(as_accept_alt):
		acc_node = N_AST1(node) ;
		stmts_node   = N_AST2(node) ;
		entry_node = N_AST1(acc_node);
		body_node = N_AST3(acc_node);
		id_node            = N_AST2(entry_node);
		entry_name               = N_UNQ(id_node);
		gen_accept(entry_name, body_node, stmts_node);
		break;

	case(as_delay_alt):
		body_node = N_AST2(node);
		compile(body_node);
		break;

	case(as_terminate_alt):
		nesting_depth = (int) N_VAL(node);
		for (i = 1; i <= nesting_depth; i++)
			gen(I_LEAVE_BLOCK);
		gen_ic(I_TERMINATE, 1, "terminate alternative");
		break;

	case(as_timed_entry_call):
		/* note: this case includes also conditional entry call */
		call_node = N_AST1(node);
		stmts1_node = N_AST2(node);
		delay_node = N_AST3(node);
		entry_node = N_AST1(call_node);
		args_node              = N_AST2(call_node);
		id_node                        = N_AST2(entry_node);
		entry_name                           = N_UNQ(id_node);
		temp_node = delay_node;
		delay_node = N_AST1(temp_node);
		stmts2_node            = N_AST2(temp_node);
		delay_node                         = N_AST1(delay_node);

		gen_value(entry_node);
		gen_prelude(entry_name, args_node);
		gen_value(delay_node);
		gen_i(I_TIMED_ENTRY_CALL, TYPE_SIZE(entry_name));

		else_part = new_unique_name("else");
		gen_s(I_JUMP_IF_FALSE, else_part);
		gen_postlude(entry_name, args_node);
		compile(stmts1_node);   /* rendezvous occured */
		if (stmts2_node != OPT_NODE) {
			end_if = new_unique_name("end_if");
			gen_s(I_JUMP, end_if);
			gen_s(I_LABEL, else_part);
			compile(stmts2_node); /* rendezvous did not occur */
			gen_s(I_LABEL, end_if);
		}
		else {
			gen_s(I_LABEL, else_part);
		}
		break;

	/*
	 *---------------
	 * 9.8 Priorities
	 *
	 *(as_priority):
	 *   pass;

	 *---------------------
	 * 9.9 Abort statements
	 */
	case(as_abort):
		task_list = N_LIST(node);
		FORTUP(task_node=(Node), task_list, ft1);
			gen_value(task_node);
		ENDFORTUP(ft1);
		gen_i(I_ABORT, tup_size(task_list));
		break;

	/* Chapter 10. Program structure and compilation issues
	 *------------------------------------
	 * 10.2 Subunits of compilations units
	 */
	case(as_subprogram_stub_tr):
		/* Generate spec if not already done: */
		proc_name   = N_UNQ(node);

		/* Avoid processing generic subprogram stubs */
		if (NATURE(proc_name) == na_generic_procedure 
		  || NATURE(proc_name) == na_generic_function) {
		}
		else {
			if (assoc_symbol_exists(proc_name, PROC_TEMPLATE)) {
				if (!is_defined(assoc_symbol_get(proc_name, PROC_TEMPLATE)))
					gen_subprogram_spec(node);
			}
			else {
				gen_subprogram_spec(node);
			}
			gen_stub(node);
		}
		break;

	case(as_package_stub): 
	case(as_task_stub):
		gen_stub(node);
		break;

	case(as_separate):
		separate_unit_node = N_AST2(node);
		compile(separate_unit_node);
		break;

	/* Chapter 11. Exceptions
	 *----------------------------
	 * 11.1 Exception declarations
	 */
	case(as_except_decl):
		except_names = tup_new(0);
		FORTUP(id_node=(Node), N_LIST(node), ft1);
			if (!tup_mem((char *)N_UNQ(id_node), except_names))
				except_names = tup_with(except_names, (char *) N_UNQ(id_node));
		ENDFORTUP(ft1);
		FORTUP(exception_name=(Symbol), except_names, ft1);
			select_entry(SELECT_EXCEPTIONS, exception_name, SLOTS_EXCEPTION);
		ENDFORTUP(ft1);
		tup_free(except_names);
		break;

	/* 11.3 Raise statements */
	case(as_raise):
		id_node = N_AST1(node);
		if (id_node != OPT_NODE)
			gen_s(I_LOAD_EXCEPTION_REGISTER, N_UNQ(id_node));
		gen(I_RAISE);
		break;

	/* 11.5 Exceptions raised during task communication */
	case(as_exception_accept):
		gen(I_RAISE_IN_CALLER);
		gen(I_END_RENDEZVOUS);
		gen(I_RAISE);
		break;

	/* Chapter 12. Generics units */
	case(as_generic_function): 
	case(as_generic_procedure):
	case(as_generic_package):
		break;

	case(as_null):
#ifdef DEBUG
		printf("compile for node kind as_null - skipped\n");
#endif
		break;

	/*--------------------------------------------------- */
	default:
#ifdef DEBUG
		zpnod(node);/* for initial debug - dump node */
		compiler_error_k("Unknown kind of node in compile: ", node );
#endif
		chaos("unknown node kind in compile");
	}
}

static void compile_line()									/*;compile_line*/
{
	/* called when starting to compile line debug_line, used for debugging */
}
