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
#include "setprots.h"
#include "genprots.h"
#include "exprprots.h"
#include "namprots.h"
#include "procprots.h"
#include "maincaseprots.h"
#include "miscprots.h"
#include "gmiscprots.h"
#include "gutilprots.h"
#include "statprots.h"

static void select_move(Node, Symbol);
static Tuple sort_case(Tuple);
static int tcompar(Tuple *, Tuple *);
void compile_body(Node, Node, Node, int);
static int jump_false_code(Symbol);
static int jump_true_code(Symbol);
static Symbol jump_table_get(Tuple, int);
static Tuple jump_table_put(Tuple, int, Symbol);

/* Chapter 5: statements
 * 5.2: Assignment statement
 */

void select_assign(Node var_node, Node expr_node, Symbol type_name)
															/*;select_assign*/
{
	Symbol	var_name, expr_name;

	var_name = N_UNQ(var_node);
	expr_name = N_UNQ(expr_node);
	if (is_simple_type(type_name) && is_simple_name(var_node)
	  && !is_renaming(var_name) ) {
		if ((is_simple_name(expr_node) && N_KIND(expr_node) != as_null
		  && !is_renaming(expr_name))
		  || (N_KIND(expr_node) == as_selector 
		  || N_KIND(expr_node) == as_index 
		  || N_KIND(expr_node) == as_all)) {
			gen_address(expr_node);
			gen_ks(I_INDIRECT_POP, kind_of(type_name), var_name);
		}
		else {
			gen_value(expr_node);
			gen_ks(I_POP, kind_of(type_name), var_name);
		}
	}
	else {
		gen_address(var_node);
		select_move(expr_node, type_name);
	}
}

static void select_move(Node node, Symbol type_name)		/*;select_move*/
{

	if (is_simple_type(type_name)) {
		if ((N_KIND(node) != as_null
		  && is_simple_name(node) && !is_renaming(N_UNQ(node)))
		  || (N_KIND(node) == as_selector || N_KIND(node) == as_index
		  || N_KIND(node) == as_all)) {
			gen_address(node);
			gen_k(I_INDIRECT_MOVE, kind_of(type_name));
		}
		else {
			gen_value(node);
			gen_k(I_MOVE, kind_of(type_name));
		}
	}
	else {
		if (is_array_type(type_name)) {
			gen_value(node);
			gen(I_ARRAY_MOVE);
		}
		else {
			gen_value(node);
			gen_s(I_RECORD_MOVE, type_name);
		}
	}
}

/* 5.4: Case statement */
Tuple make_case_table(Node cases_node) 					/*;make_case_table*/
{
	/* Function : takes a set of alternatives, and produces a linear table
	 *            suitable for jump table, of case ranges sorted in ascending
	 *            order. Some optimisation is done, to merge contiguous
	 *            ranges and to fill missing ranges with "others" case
	 * Input : case_node       ::= {case_statements}
	 *         case_statements ::= [choice_list, body]
	 *         choice_list     ::= { choice }
	 *         choice          ::= simple_choice | range_choice
	 *                                           | others_choice
	 *	  simple_choice   ::= [ value ]
	 *         range_choice    ::= [ subtype ]
	 * Output : [table, bodies, others_body]
	 *          table ::= [ [ lower_bound, index ] ]
	 *            -  an extra pair is added with a "lower_bound" one step
	 *               higher than necessary
	 *            -  "index" is an index in the tuple "bodies", and
	 *               index = 0 means "others"
	 */
	Node	case_statements_node, choice_list_node, body_node, choice_node,
	    lbd_node, ubd_node, others_body;
	Tuple	result, tup, bodies, triplets;
	int		index, a1, a2, a3, b1, b2, b3, lbd_int, ubd_int;
	int		empty;
	Fortup	ft1, ft2;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("MAKE_CASE_TABLE", cases_node);
#endif

	/* 1. build a set of triples [lowerbound, upperbound, index] */

	index       = 0;
	bodies      = tup_new(0);
	triplets    = tup_new(0);
	others_body = OPT_NODE;
	FORTUP(case_statements_node = (Node), N_LIST(cases_node), ft1);
		choice_list_node = N_AST1(case_statements_node);
		body_node = N_AST2(case_statements_node);
		index += 1;
		empty  = TRUE;  /* may be we have an empty branch */
		FORTUP(choice_node = (Node), N_LIST(choice_list_node), ft2);
			switch (N_KIND(choice_node)) {
			case (as_range):
				lbd_node = N_AST1(choice_node);
				ubd_node = N_AST2(choice_node);
				lbd_int = get_ivalue_int(lbd_node);
				ubd_int = get_ivalue_int(ubd_node);
				if (lbd_int <= ubd_int) {
					tup = tup_new(3);
					tup[1] = (char *) lbd_int;
					tup[2] = (char *) ubd_int;
					tup[3] = (char *) index;
					triplets = tup_with(triplets, (char *) tup);
					empty = FALSE;
				}
				break;

			case (as_others_choice):
				others_body = body_node;
				break;

			default:
				compiler_error( "Unknown kind of choice: ");
			}
		ENDFORTUP(ft2);
		if (empty)
			index -= 1;
		else
			bodies  = tup_with(bodies, (char *) body_node);
	ENDFORTUP(ft1);

	result = tup_new(0);

	if (tup_size(triplets) != 0) { /* We may have a completely empty case */

		/* 2. sort the set of triples, giving a tuple */

		triplets = sort_case(triplets);

		/* 3. build the case table, filling gaps and merging adjacent cases */

		tup = (Tuple) tup_fromb(triplets);
		a1 = (int) tup[1]; 
		a2 = (int) tup[2]; 
		a3 = (int) tup[3];
		while(tup_size(triplets) != 0) {
			tup = (Tuple) tup_fromb(triplets);
			b1 = (int) tup[1]; 
			b2 = (int) tup[2]; 
			b3 = (int) tup[3];
			if (a2 != b1-1) {  /* gap */
				tup = tup_new(2);
				tup[1] = (char *) a1;
				tup[2] = (char *) a3;
				result = tup_with(result, (char *) tup);
				tup = tup_new(2);
				tup[1] = (char *) (a2+1);
				tup[2] = (char *) 0;
				result = tup_with(result, (char *) tup);

				a1 = b1; 
				a2 = b2; 
				a3 = b3;
			}
			else if (a3 == b3)  {  /* merge */
				a2 = b2; 
				a3 = b3;
			}
			else {
				tup = tup_new(2);
				tup[1] = (char *) a1;
				tup[2] = (char *) a3;
				result = tup_with(result, (char *) tup);
				a1 = b1; 
				a2 = b2; 
				a3 = b3;
			}
		}
		tup  = tup_new(2);
		tup[1] = (char *) a1;
		tup[2] = (char *) a3;
		result = tup_with(result, (char *) tup);
		tup = tup_new(2);
		if (a2 != MAX_INTEGER) {
			tup[1] = (char *) a2+1;
			tup[2] = (char *) 0;
		}
		else {
			tup[1] = (char *) 0; /* does not really matter */
			tup[2] = (char *) a3;/* merge with the preceeding */
		}
		result = tup_with(result, (char *) tup);
	}

	tup = tup_new(3);
	tup[1] = (char *) result;
	tup[2] = (char *) bodies;
	tup[3] = (char *) others_body;
	return tup;
}

static Tuple sort_case(Tuple tuple_to_sort)						/*;sort_case*/
{
	/*
	 * Takes a set of case triples, and returns a tuple of those triple,
	 * sorted by ascending lower bounds. Quick sort algorithm.
	 * (sorry, this is not efficient, but was very easy to write)
	 */

	qsort((char *) &tuple_to_sort[1], tup_size(tuple_to_sort), sizeof (char *),
	  (int (*)(const void *, const void *))tcompar);
	return tuple_to_sort;
}

static int tcompar(Tuple *ptup1, Tuple *ptup2)					/*;tcompar*/
{
	Tuple	tup1, tup2;
	int		n1, n2;

	tup1 = *ptup1; 
	tup2 = *ptup2;
	/* called from sort_case to compare two elements in the case list */
	n1 = (int) tup1[1];
	n2 = (int) tup2[1];
	if (n1 == n2) return 0;
	else if (n1 < n2) return -1;
	else return 1;
}

void gen_case(Tuple case_table, Tuple bodies_arg, Node others_body,int mem_unit)
																/*;gen_case*/
{
	/* Generates the code to select the right alternative and the bodies */
	int		index, lower_bound, i, n;
	Node	body_node;
	Symbol	end_case, jumpsym;
	Tuple	jump_table, tup;
	Fortup	ft1;
	Tuple	bodies;

	bodies = tup_copy(bodies_arg); /* copy needed since used in tup_fromb */
	end_case = new_unique_name("end_case");
	gen_k(I_CASE, mem_unit);
	/* The SETL jump_table map is represented as a 'tuple map' in C, with
	 * procedures jump_table_get() and jump_table_put() (defined below) used
	 * to retrieve and insert values in this map.
	 */
	jump_table = tup_new(0);
	jump_table = jump_table_put(jump_table, 0, new_unique_name("case"));
	gen_ks(I_CASE_TABLE, tup_size(case_table), jump_table_get(jump_table, 0)  );
	FORTUP(tup = (Tuple), case_table, ft1);
		lower_bound = (int) tup[1];
		index = (int) tup[2];
		jumpsym = jump_table_get(jump_table, index);
		if (jumpsym == (Symbol)0) { /* if no entry yet, make new one */
			jumpsym = new_unique_name("case");
			jump_table = jump_table_put(jump_table, index, jumpsym);
		}
		gen_ks(I_CASE_TABLE, lower_bound, jumpsym);
	ENDFORTUP(ft1);
	index  = 0;
	bodies = tup_exp(bodies, tup_size(bodies) + 1);
	n = tup_size(bodies);
	for (i = n; i > 1; i--) {
		bodies[i] = bodies[i-1];
	}
	bodies[1] = (char *) others_body;
	while (tup_size(bodies) != 0) {
		body_node = (Node) tup_fromb(bodies);
		gen_s(I_LABEL, jump_table_get(jump_table, index));
		compile(body_node);
		if (tup_size(bodies) != 0) { /* to avoid useless "jump $+1" */
			gen_s(I_JUMP, end_case );
		}
		index += 1;
	}
	gen_s(I_LABEL, end_case);
	tup_free(bodies);
}

/* 5.6: block statement (compile_body) */
void compile_body(Node decls_node, Node stmts_node, Node handler_node,
  int is_block_statement)									/*;compile_body*/
{
	int		save_last_offset;
	/* stack frame offset for local variables */
	/* will overlap for blocks at the same nesting level */

	int		save_tasks_declared;
	Symbol	start_handler, end_handler;

	CURRENT_LEVEL       += 1;
	save_last_offset     = LAST_OFFSET;
	save_tasks_declared  = TASKS_DECLARED;
	TASKS_DECLARED       = FALSE;

	gen(I_ENTER_BLOCK);
	compile(decls_node);
	if (handler_node != OPT_NODE) {
		start_handler = new_unique_name("handler");
		gen_s(I_INSTALL_HANDLER, start_handler);
	}
	if (TASKS_DECLARED) {
		gen(I_ACTIVATE);
	}
	compile(stmts_node);
	if (handler_node != OPT_NODE) {
		if (is_block_statement) {
			/* use label allocated if return in accept else allocate
			 * a label for end of block (cf. comments in gen_accept)
			 */
			if (symbol_accept_return != (Symbol)0) {
				end_handler = symbol_accept_return;
			}
			else {
				end_handler = new_unique_name("end_handler");
			}
			gen_s(I_JUMP, end_handler);
			gen_s(I_LABEL, start_handler);
			compile(handler_node);
			gen_s(I_LABEL, end_handler);
		}
		else {
			gen_s(I_LABEL, start_handler);
			compile(handler_node);
		}
	}

	/*MAX_OFFSET  max= abs LAST_OFFSET;*/
	MAX_OFFSET = offset_max(MAX_OFFSET, LAST_OFFSET);
	LAST_OFFSET    = save_last_offset;
	TASKS_DECLARED = save_tasks_declared;
	CURRENT_LEVEL -= 1;
}

void gen_condition(Node node, Symbol destination, int branch_cond)
															/*;gen_condition*/
{
	/* IMPORTANT WARNING: destination is where to go when expression is
	 *                    equal to branch_cond
	 */
	/* These maps are realized in procedures immediately following.
	 *  const
	 * jump_false_code = {
	 *    ['=', I_JUMP_IF_FALSE],
	 *    ['!=', I_JUMP_IF_TRUE],
	 *    ['<', I_JUMP_IF_GREATER_OR_EQUAL],
	 *    ['>', I_JUMP_IF_LESS_OR_EQUAL],
	 *    ['<=', I_JUMP_IF_GREATER],
	 *    ['>=', I_JUMP_IF_LESS] },
	 * 
	 * jump_true_code = {
	 *    ['=', I_JUMP_IF_TRUE],
	 *    ['<', I_JUMP_IF_LESS],
	 *    ['>', I_JUMP_IF_GREATER],
	 *    ['<=', I_JUMP_IF_LESS_OR_EQUAL],
	 *    ['>=', I_JUMP_IF_GREATER_OR_EQUAL] };
	 */

	Tuple	tup;
	Node	opnode, args, op1, op2;
	Symbol	opcode, optype;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("GEN_CONDITION", node);
#endif

	if (N_KIND(node) == as_op) {
		opnode = N_AST1(node);
		args = N_AST2(node);
		opcode  = N_UNQ(opnode);
		if (opcode == symbol_eq || opcode == symbol_ne || opcode == symbol_lt
		  || opcode == symbol_gt || opcode == symbol_le || opcode == symbol_ge){
			tup = N_LIST(args);
			op1 = (Node) tup[1];
			op2     = (Node) tup[2];

			gen_value(op1);
			gen_value(op2);
			optype = get_type(op1);
			if (is_simple_type(optype)) {
				if (is_float_type(optype))
					gen_k(I_FLOAT_COMPARE, kind_of(optype));
				else
					gen_k(I_COMPARE, kind_of(optype));
			}
			else {
				if (is_record_type(optype)) {
					gen_s(I_PUSH_EFFECTIVE_ADDRESS, optype);
				}
				if (is_array_type(optype) && 
				    (opcode != symbol_eq) && (opcode != symbol_ne)) {
					gen(I_COMPARE_ARRAYS);
				}
				else {
					gen(I_COMPARE_STRUC);
				}
			}
		}
		else {
			gen_value(node);
			opcode = symbol_eq;
		}
	}
	else {
		gen_value(node);
		opcode = symbol_eq;
	}

	if (branch_cond)
		gen_s(jump_true_code(opcode), destination);
	else
		gen_s(jump_false_code(opcode), destination);
}

static int jump_false_code(Symbol op)					/*;jump_false_code*/
{
	if (op == symbol_eq) return I_JUMP_IF_FALSE;
	else if (op == symbol_ne) return I_JUMP_IF_TRUE;
	else if (op == symbol_lt) return I_JUMP_IF_GREATER_OR_EQUAL;
	else if (op == symbol_gt) return I_JUMP_IF_LESS_OR_EQUAL;
	else if (op == symbol_le) return I_JUMP_IF_GREATER;
	else if (op == symbol_ge) return I_JUMP_IF_LESS;
	else chaos("jump_false_code bad op");
	return I_JUMP_IF_TRUE; /* return junk value */
}

static int jump_true_code(Symbol op)						/*;jump_true_code*/
{
	if (op == symbol_eq) return I_JUMP_IF_TRUE;
	else if (op == symbol_ne) return I_JUMP_IF_FALSE;
	else if (op == symbol_lt) return I_JUMP_IF_LESS;
	else if (op == symbol_gt) return I_JUMP_IF_GREATER;
	else if (op == symbol_le) return I_JUMP_IF_LESS_OR_EQUAL;
	else if (op == symbol_ge) return I_JUMP_IF_GREATER_OR_EQUAL;
	else chaos("jump_true_code");
	return I_JUMP_IF_TRUE; /* return junk value for lint's sake */
}

void gen_loop(Node node)										/*;gen_loop*/
{
	/* Generate loop stratements */
	Node	id_node, iter_node, stmt_node, while_cond_node, var_node,
	  exp1_node, exp2_node;
	Symbol	label_name, start_loop, start_while, end_while, var_name,
	  end_for, for_body, for_start, void_loop;
	int		end_inst;
	int		kind_var;
	int         needs_check;
	Const	val1, val2;


#ifdef TRACE
	if (debug_flag)
		gen_trace_node("GEN_LOOP", node);
#endif

	id_node = N_AST1(node);
	iter_node = N_AST2(node);
	stmt_node = N_AST3(node);

	if (id_node != OPT_NODE) {
		label_name               = N_UNQ(id_node);
		labelmap_put(label_name, LABEL_STATIC_DEPTH, (char *) CURRENT_LEVEL);
		next_local_reference(label_name);
		gen_s(I_SAVE_STACK_POINTER, label_name);
	}

	if (iter_node == OPT_NODE) { /* simple loop */
		start_loop = new_unique_name("loop");
		gen_s(I_LABEL, start_loop);
		compile(stmt_node);
		gen_s(I_JUMP, start_loop );
		if (id_node != OPT_NODE)
			gen_s(I_LABEL, label_name);
	}
	else if (N_KIND(iter_node) == as_while) {	 /* while loop */
		while_cond_node = N_AST1(iter_node);
		start_while  = new_unique_name("start_while");
		end_while    = new_unique_name("end_while");
		gen_sc(I_JUMP, end_while, "Test better at end of loop");
		gen_s(I_LABEL, start_while);

		compile(stmt_node);
		gen_s(I_LABEL, end_while);
		gen_condition(while_cond_node, start_while, TRUE);

		if (id_node != OPT_NODE)
			gen_s(I_LABEL, label_name);
	}
	else {					 /* for loop */
		var_node = N_AST1(iter_node);
		exp1_node = N_AST2(iter_node);
		exp2_node = N_AST3(iter_node);
		var_name = N_UNQ(var_node);
		next_local_reference(var_name);
		kind_var = kind_of(TYPE_OF(var_name));
		val1     = get_ivalue(exp1_node);
		val2     = get_ivalue(exp2_node);

		end_inst = ((N_KIND(iter_node) == as_for)) ?
		  I_END_FOR_LOOP : I_END_FORREV_LOOP;

		/* Static null range already checked by expander */

		if (val1->const_kind != CONST_OM && val2->const_kind != CONST_OM
		  && get_ivalue_int(exp1_node) == get_ivalue_int(exp2_node)) {
			/* Loop executed only once, remove loop */
			gen_value(exp1_node);
			gen_k(I_CREATE_COPY, kind_var);
			gen_s(I_UPDATE_AND_DISCARD, var_name);

			compile(stmt_node);

			if (id_node != OPT_NODE)
				gen_s(I_LABEL, label_name);
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, var_name);
			gen(I_UNCREATE);
		}
		else {
			needs_check = (val1->const_kind == CONST_OM
			  || val2->const_kind == CONST_OM );

			if (N_KIND(iter_node) == as_for) {
				gen_value(exp2_node);
				if (needs_check) {
					gen_k(I_DUPLICATE, kind_var);
				}
				gen_value(exp1_node);
				if (needs_check) {
					gen_k(I_DUPLICATE, kind_var);
				}
			}
			else {
				gen_value(exp1_node);
				if (needs_check) {
					gen_k(I_DUPLICATE, kind_var);
				}
				gen_value(exp2_node);
				if (needs_check) {
					gen_k(I_DUPLICATE, kind_var);
				}
			}
			for_start = new_unique_name("for_start");
			for_body = new_unique_name("for_body");
			end_for = new_unique_name("end_for");
			if (needs_check) {
				void_loop = new_unique_name("void");
				gen_k(I_CREATE_COPY, kind_var);
				gen_s(I_UPDATE_AND_DISCARD, var_name);
				gen_k(I_COMPARE, kind_var);
				if (N_KIND(iter_node) == as_for) {
					gen_s(I_JUMP_IF_GREATER_OR_EQUAL, for_start);
				}
				else {
					gen_s(I_JUMP_IF_LESS_OR_EQUAL, for_start);
				}
				gen_ks(I_POP, kind_var, var_name);
				gen_s(I_JUMP, void_loop);
				gen_s(I_LABEL, for_start);
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, var_name);
			}
			else
			{  /* loop executed at least once, no need for check */
				gen_k(I_CREATE_COPY, kind_var);
				gen_s(I_UPDATE, var_name);
			}
			gen_s(I_LABEL, for_body);

			compile(stmt_node);

			gen_s(I_LABEL, end_for);
			gen_ks(end_inst, kind_var, for_body );

			if (id_node != OPT_NODE) {
				gen_s(I_LABEL, label_name);
			}

			if (needs_check) {
				gen_s(I_LABEL, void_loop);
			}
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, var_name);
			gen(I_UNCREATE);

		} /* static null loop */
	}
}

static Symbol jump_table_get(Tuple jtab, int ndx)		/*;jump_table_get()*/
{
	int		i, n;

	n = tup_size(jtab);
	for (i = 1; i <= n; i += 2) {
		if ((int) jtab[i] == ndx)
			return (Symbol) jtab[i+1];
	}
	return (Symbol)0;
}

static Tuple jump_table_put(Tuple jtab, int ndx, Symbol sym) /*;jump_table_put*/
{
	/* set value of jump_table jtab for int ndx to be sym. jtab is a map
	 * kept as tuple.
	 */

	int		i, n;

	n = tup_size(jtab);
	for (i = 1; i <= n; i += 2) {
		if ((int) jtab[i] == ndx) {
			jtab[i+1] = (char *) sym;
			return jtab;
		}
	}
	/* here to add new entry */
	jtab = tup_exp(jtab, n+2);
	jtab[n+1] = (char *) ndx;
	jtab[n+2] = (char *) sym;
	return jtab;
}
