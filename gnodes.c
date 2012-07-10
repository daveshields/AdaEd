/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* gnodes.c - translation of gnodes.stl */

#define GEN

#include "hdr.h"
#include "vars.h"
#include "gvars.h"
#include "chapprots.h"
#include "gmiscprots.h"
#include "dbxprots.h"
#include "setprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "chapprots.h"
#include "gutilprots.h"
#include "gnodesprots.h"

/*
 * Tree construction procedures
 *--------------------
 * 2. Lexical elements
 */

Node new_number_node(int value)								/*;new_number_node*/
{
	/* constructs an number node, used to hold small integer values used for
	 * attributes and return statement depth.
	 */

	Node	node;

	node		= node_new(as_number);
	N_VAL (node) = (char *) value;
	return node;
}

Node new_instance_node(Tuple value)						/*;new_instance_node*/
{
	/* constructs an instance node, used to hold tups used for instantiations */
	Node	node;

	node		= node_new(as_instance_tuple);
	N_VAL (node) = (char *) value;
	return node;
}

void make_ivalue_node(Node node, Const value, Symbol typ)  /*;make_ivalue_node*/
{
	/* constructs an ivalue node */

	int nk;

	nk = N_KIND(node);
	if (N_AST1_DEFINED(nk)) N_AST1(node) = (Node) 0;
	if (N_AST2_DEFINED(nk)) N_AST2(node) = (Node) 0;
	if (N_AST3_DEFINED(nk)) N_AST3(node) = (Node) 0;
	if (N_AST4_DEFINED(nk)) N_AST4(node) = (Node) 0;
	if (N_LIST_DEFINED(nk)) N_LIST(node) = (Tuple) 0;
	N_KIND(node) = as_ivalue;
	N_VAL (node) = (char *) value;
	N_TYPE(node) = typ;
}

/*
 *--------------------------
 * 3.2.1 Object declarations
 */

#ifndef BINDER
void make_single_decl_list(Node root, Node decl_node) /*;make_single_decl_list*/
{
	/*
	 * This procedure transforms a declaration with a list of names into a
	 * list of declarations, each with one sigle name. It is called in the
	 * case of declarations with side-effect.
	 * This procedure is ineffective if the original name list has only one
	 * element.
	 * root is the root of the tree to duplicate, while decl_node points to
	 * the actual (original) declaration. The latter is part of the tree, but
	 * not necessarily the root due to possible pre-statements.
	 * The declaration is supposed to be fit for the first element of the
	 * list, so renaming is necessary for all others.
	 */

	Node		id_list_node, first_id, id;
	Tuple	id_list, decl_list;
	Symbol	first_name, first_type, id_name;
	Fortup	ft1;
	Symbolmap   	rename_map;

	id_list_node = N_AST1(decl_node);
	id_list        = tup_copy(N_LIST(id_list_node));
	/* tup_copy needed since id_list used destructively in tup_fromb below*/
	if (tup_size(id_list) == 1)
		return;

	first_id         = (Node) tup_fromb(id_list);
	N_LIST(id_list_node) = tup_new1((char *) first_id);
	first_name           = N_UNQ  (first_id);
	first_type           = TYPE_OF(first_name);
	decl_list            = tup_new1((char *) copy_node(root));
	FORTUP(id=(Node), id_list, ft1);
		id_name       = N_UNQ(id);
		/* RENAME_MAP    = {[first_name, id_name],
      	 *		  [first_type, TYPE_OF(id_name)] };
      	 */
		rename_map = symbolmap_new();
		symbolmap_put(rename_map, first_name, id_name);
		symbolmap_put(rename_map, first_type, TYPE_OF(id_name));
		node_map = nodemap_new();	/* initialize */

		decl_list = tup_with(decl_list,
	      (char *) instantiate_tree(root, rename_map));
	ENDFORTUP(ft1);

	N_KIND(root) = as_declarations;
	N_AST1(root) = (Node)0; 
	N_AST2(root) = (Node)0;
	N_AST3(root) = (Node)0; 
	N_AST4(root) = (Node)0;
	N_LIST(root) = decl_list;
	N_SIDE(root) = TRUE;  /* We are called only in case of side-effect */
}
#endif

void make_const_node(Node node, Symbol const_name, Symbol type_name,
  Node init_node)										/*;make_const_node*/
{
	Node	list_node;

	list_node         = new_node(as_list);
	N_KIND(node)      = as_const_decl;
	N_LIST(list_node) = tup_new1((char *) new_name_node(const_name));
	N_LIST(node)      = (Tuple) 0;
	N_VAL (node)      = (char *) 0;
	N_AST1(node)      = list_node ;
	N_AST2(node)      = new_name_node(type_name) ;
	N_AST3(node)      = init_node ;
}

Node new_var_node(Symbol var_name, Symbol type_name, Node init_node)
															/*;new_var_node*/
{
	Node   list_node, node;

	list_node         = new_node(as_list);
	N_LIST(list_node) = tup_new1((char *) new_name_node(var_name));
	node              = new_node(as_obj_decl);
	N_AST1(node)      = list_node ;
	N_AST2(node)      = new_name_node(type_name) ;
	N_AST3(node)      = init_node ;
	return node;
}

/*
 *---------------------------
 * 3.3.2 Subtype declarations
 */

Node new_subtype_decl_node(Symbol type_name)		/*;new_subtype_decl_node*/
{
	/*
	 * Creates a subtype declaration node. Only type name initialized, as
	 * types are fully processed from the symbol table.
	 */
	Node	node;

	node        = new_node(as_subtype_decl);
	N_AST1(node) = new_name_node(type_name);
	N_AST2(node) = OPT_NODE;
	N_UNQ(node) = type_name;
	return node;
}

/*
 *----------------
 * 3.8 Access type
 */

Node new_null_node(Symbol r_type)							/*;new_null_node*/
{
	Node	node;

	node         = new_node(as_null) ;
	N_TYPE(node) = r_type ;
	return node ;
}

/*
 *----------
 * 4.1 Names
 */

Node new_name_node(Symbol name)								/*;new_name_node*/
{
	/* constructs an as_simple_name node. */
	Node	node;

	if (name == (Symbol)0)
		compiler_error("Name is omega in new_name_node");
	node         = new_node(as_simple_name);
	N_UNQ (node) = name;
	return node;
}

void make_name_node(Node node, Symbol name)				/*;make_name_node*/
{
	/* Transforms node into an as_simple_name node. */

	if (name == (Symbol)0)
		compiler_error("Name is omega in make_name_node");
	N_KIND(node) = as_simple_name;
	N_AST1(node) = (Node)0; 
	N_AST2(node) = (Node) 0;
	N_AST3(node) = (Node)0; 
	N_AST4(node) = (Node) 0;
	N_LIST(node) = (Tuple)0;
	N_TYPE(node) = (Symbol) 0;
	N_VAL (node) = (char *) 0;
	N_UNQ (node) = name;
}

/*
 *--------------------------
 * 4.1.1 Indexed components
 */

Node new_index_node(Node object_node, Tuple index_list, Symbol comp_type)
															/*;new_index_node*/
{
	/* Build an as_index node */
	Node	node, list_node;

	list_node         = new_node(as_list);
	N_LIST(list_node) = index_list;
	node              = new_node(as_index);
	N_AST1(node)      = object_node ;
	N_AST2(node)      = list_node ;
	N_TYPE(node)      = comp_type;
	return node;
}

void make_index_node(Node node, Node object_node, Tuple index_list,
  Symbol comp_type)										/*;make_index_node */
{
	/* Build an as_index node */
	Node	list_node;

	list_node         = new_node(as_list);
	N_LIST(list_node) = index_list;
	N_LIST(node)      = (Tuple) 0;
	N_KIND(node)      = as_index;
	N_AST1(node)      = object_node ;
	N_AST2(node)      = list_node ;
	N_TYPE(node)      = comp_type;
}

/*
 *--------------------------
 * 4.1.3 Selected components
 */

Node new_selector_node(Node object_node, Symbol selector) /*;new_selector_node*/
{
	/*
	 * The selector  is a declared  component name, or the  internal marker
	 * 'constrained' used  to represent the  corresponding attribute.  This
	 * name is used for all records with discriminants. Its type is BOOLEAN.
	 */

	Node	node, sel_node;

	node         = new_node(as_selector) ;
	sel_node     = new_name_node(selector) ;
	N_AST1(node) = object_node ;
	N_AST2(node) = sel_node ;
	N_TYPE(node) = TYPE_OF(selector) ;
	return node ;
}

void make_selector_node(Node node, Node object_node, Symbol selector)
													/*;make_selector_node*/
{
	/*
	 * The selector  is a declared  component name, or the  internal marker
	 * 'constrained' used  to represent the  corresponding attribute.  This
	 * name is used for all records with discriminants. Its type is BOOLEAN.
	 */

	Node	sel_node;

	sel_node     = new_name_node(selector) ;
	N_KIND(node) = as_selector;
	N_LIST(node) = (Tuple) 0;
	N_AST1(node) = object_node ;
	N_AST2(node) = sel_node ;
	N_TYPE(node) = TYPE_OF(selector) ;
}

Node new_discr_ref_node(Symbol d_name, Symbol type_name)	/*;new_discr_ref*/
{
	Node	node;

	node         = new_node(as_discr_ref) ;
	N_AST1(node) = new_name_node(type_name);
	N_UNQ(node) = d_name;
	N_TYPE(node) = TYPE_OF(d_name);
	return node ;
}

void make_discr_ref_node(Node node, Symbol d_name, Symbol type_name)
													/*;make_discr_ref_node*/
{
	N_KIND(node) = as_discr_ref;
	N_AST1(node) = new_name_node(type_name);
	N_LIST(node) = (Tuple) 0;
	N_UNQ (node) = d_name;
	N_TYPE(node) = TYPE_OF(d_name);
}

/*
 *-----------------
 * 4.1.4 Attributes
 */

Node new_attribute_node(int attr, Node arg1, Node arg2, Symbol typ)
														/*;new_attribute_node*/
{
	/* Creates an attribute node. attr is the attribute's name. */

	Node	id_node, attr_node;

	id_node           = new_node(as_number);
	attr_node         = new_node(as_attribute);
	/* attach attribute code to parent node */
	N_AST1(attr_node) = id_node ;
	attribute_kind(attr_node)   = (char *) attr;
	N_AST2(attr_node) = arg1 ;
	N_AST3(attr_node) = arg2 ;
	N_TYPE(attr_node) = typ;
	return attr_node;
}

/*
 *----------------------------------------
 * 4.5 Operators and expression evaluation
 */

Node new_binop_node(Symbol oper, Node arg1, Node arg2, Symbol typ)
															/*;new_binop_node*/
{
	/* Creates a binary operator node. Oper is the operator's name */

	Node	id_node, list_node, node;
	Tuple	tup;

	id_node           = new_name_node(oper);
	list_node         = new_node(as_list);
	tup = tup_new(2);
	tup[1] = (char *) arg1;
	tup[2] = (char *) arg2;
	N_LIST(list_node) = tup;
	node              = new_node(as_op);
	N_AST1(node)      = id_node ;
	N_AST2(node)      = list_node ;
	N_TYPE(node)      = typ;
	return node;
}

/*
 *--------------------
 * 4.6 Type conversion
 */

Node new_qual_range_node(Node expr_node, Symbol type_name)
														/*;new_qual_range_node*/
{
	/* Creates a qual_range node */

	Node	node;

	node = new_node(as_qual_range);
	N_TYPE(node) = type_name;
	N_AST1(node) = expr_node;
	return node;
}

/*
 *------------------------------------------------------------
 * 5.1 Simple and compound statements - Sequence of statements
 */

Node new_statements_node(Tuple stmt_list)			/*;new_statements_node*/
{
	/* Creates an as_statements node, given a list (tuple) of statements */

	Node	stmt_node, list_node;

	stmt_node         = new_node(as_statements);
	list_node         = new_node(as_list);
	N_LIST(list_node) = stmt_list;
	N_AST1(stmt_node) = list_node ;
	N_AST2(stmt_node) = OPT_NODE ;
	return stmt_node;
}

void make_statements_node(Node node, Tuple stmt_list) /*;make_statements_node*/
{
	/* Transforms node into an as_statements node, given a list (tuple)
	 * of statements
	 */

	Node	list_node;

	list_node         = new_node(as_list);
	N_LIST(list_node) = stmt_list;
	N_KIND(node) = as_statements;
	N_LIST(node) = (Tuple) 0;
	N_VAL (node) = (char *) 0;
	N_AST1(node) = list_node ;
	N_AST2(node) = OPT_NODE ;
}

/*
 *-------------------------
 * 5.2 Assignment statement
 */

Node new_assign_node(Node lhs, Node rhs)				/*;new_assign_node*/
{
	/* Creates an assign node */

	Node	node;

	node        = new_node(as_assignment) ;
	N_AST1(node) = lhs ;
	N_AST2(node) = rhs  ;
	return node ;
}

void make_assign_node(Node node, Node lhs, Node rhs)	/*;make_assign_node*/
{
	/* Transforms node into an assign node */

	N_KIND(node) = as_assignment;
	N_LIST(node) = (Tuple) 0;
	N_VAL (node) = (char *) 0;
	N_AST1(node) = lhs ;
	N_AST2(node) = rhs  ;
}

/*
 *-----------------
 * 5.3 If statement
 */

Node new_simple_if_node(Node cond_node, Node then_node, Node else_node)
														/*;new_simple_if_node*/
{
	/* Creates an if node for the case without elsif parts */

	Node	node, cond_stmt_node, if_list_node;

	cond_stmt_node        = new_node(as_cond_statements) ;
	N_AST1(cond_stmt_node) = cond_node;
	N_AST2(cond_stmt_node) = then_node  ;
	if_list_node          = new_node(as_list) ;
	N_LIST(if_list_node)  = tup_new1((char *) cond_stmt_node);
	node                  = new_node(as_if) ;
	N_AST1(node)           = if_list_node ;
	N_AST2(node)           = else_node  ;
	return node;
}

void make_if_node(Node node, Tuple cond_list, Node else_stmt_node)
															/*;make_if_node*/
{
	/*
	 * Transforms node into an if statement.
	 * cond_list is a list (tuple) of conditions node
	 * others_stmt is the node corresponding to the else part
	 */

	Node	list_node;

	list_node         = new_node(as_list);
	N_LIST(list_node) = cond_list;

	N_KIND(node)      = as_if;
	N_LIST(node)      = (Tuple) 0;
	N_VAL(node)      = (char *) 0;
	N_AST1(node)      = list_node ;
	N_AST2(node)      = else_stmt_node ;
}

Node new_cond_stmts_node(Node expr_node, Node stmts_node)
														/*;new_cond_stmts_node*/
{
	/*
	 * Creates a conditional statements node.
	 * Expr is the (boolean) expression, stat the statements
	 */

	Node	cond_node;

	cond_node        = new_node(as_cond_statements);
	N_AST1(cond_node) = expr_node ;
	N_AST2(cond_node) = stmts_node ;
	return cond_node;
}

/*
 *-------------------
 * 5.5 Loop statement
 */

Node new_loop_node(Node label_node, Node iter_node, Tuple stmt_list)
															/*;new_loop_node*/
{
	/* Creates a loop node */

	Node	loop_node, stmt_node;

	loop_node         = new_node(as_loop);
	stmt_node         = new_statements_node(stmt_list);
	N_AST1(loop_node) = label_node ;
	N_AST2(loop_node) = iter_node ;
	N_AST3(loop_node) = stmt_node ;
	return loop_node;
}

/*
 *--------------------
 * 5.6 Block statement
 */

Node new_block_node(Node label_node, Tuple decl_list, Tuple stmt_list,
  Node exc_node)										/*;new_block_node*/
{
	/* Creates a block node */

	Node	block_node, decl_node, stmt_node;

	block_node = new_node(as_block);

	if (tup_size(decl_list) == 0) {
		decl_node = OPT_NODE;
	}
	else {
		decl_node         = new_node(as_declarations);
		N_LIST(decl_node) = decl_list;
	}

	stmt_node = new_statements_node(stmt_list);

	N_AST1(block_node) = label_node ;
	N_AST2(block_node) = decl_node ;
	N_AST3(block_node) = stmt_node ;
	N_AST4(block_node) = exc_node ;
	return block_node;
}

/*
 *---------------------------
 * 6.1 Subprogram declaration
 */

void make_subprog_node(Node node, Symbol type_name, Node decl_node,
  Node stmt_node, Node exc_node)						/*;make_subprog_node*/
{
	/* Note format of as_subprogram_tr node is different than that of 
	 * as_subprogram. This format is much more concise with all unnecessary
	 * tree structure disgarded.
	 */

	N_KIND(node) = as_subprogram_tr;
	N_AST1(node) = stmt_node ;
	N_AST2(node) = decl_node ;
	N_UNQ(node) = type_name ;
	N_AST4(node) = exc_node ;
}

Node new_param_node(char *param_name, Symbol scope_name, Symbol type_name,
  int na_mode)												/*;new_param_node*/
{
	/* This procedure is called from initobj. The actual string passed as
	 * the first argument is not important and is used in SETL version
	 * only for debugging purposes.
	 */

	Node	node;
	Symbol	param_unam;


	param_unam = new_unique_name(param_name) ;
	node       = new_name_node(param_unam) ;

	TYPE_OF(param_unam)  = type_name;
	NATURE (param_unam)  = na_mode;
	SCOPE_OF(param_unam) = scope_name;
	return node ;
}

/*
 *--------------------
 * 6.4 Subprogram call
 */

Node new_call_node(Symbol proc_name, Tuple arg_list, Symbol type_name)
															/*;new_call_node*/
{
	/* Creates a call node. */

	Node	list_node, call_node;

	list_node         = new_node(as_list);
	N_LIST(list_node) = arg_list;
	call_node         = new_node(as_call);
	N_TYPE(call_node) = type_name;
	N_AST1(call_node) = new_name_node(proc_name) ;
	N_AST2(call_node) = list_node ;
	return call_node;
}

/*
 *--------------------------------
 * 9.2 Task types and task objects
 */

Node new_create_task_node(Symbol c_type)			/*;new_create_task_node*/
{
	Node	node;

	node         = new_node(as_create_task) ;
	N_TYPE(node) = c_type ;
	N_SIDE(node) = TRUE;
	return node ;
}

/*
 *---------------------
 * 11.3 Raise statement
 */

Node new_raise_node(Symbol exc_name)					/*;new_raise_node */
{
	/* creates a raise node */

	Node	raise_node;

	raise_node = new_node(as_raise);
	N_AST1(raise_node) = (exc_name == OPT_NAME) ? OPT_NODE :
	  new_name_node(exc_name);
	return raise_node;
}

void make_raise_node(Node node, Symbol exc_name)		/*;make_raise_node*/
{
	/* Transforms node into a raise statement */

	N_KIND(node) = as_raise;
	N_AST1(node) = (exc_name == OPT_NAME) ? OPT_NODE :
	  new_name_node(exc_name);
	N_LIST(node) = (Tuple) 0;
	N_VAL (node) = (char *) 0;
}

/*
 *--------------
 * Miscelleanous
 */

void make_insert_node(Node node, Tuple pre_list, Node post_node)
														/*;make_insert_node*/
{
	/* Transforms node into an insert node */

	if (N_AST3_DEFINED(N_KIND(node))) { /* clear to avoid confusing with N_UNQ*/
		N_AST3(node) = (Node) 0;
	}
	/* warn if n_ast4 and N_type may be confused */
	if (N_AST4_DEFINED(N_KIND(node))) {
#ifdef DEBUG
		zpnod(node);
#endif
		chaos("make_insert_node error: ");
		N_AST4(node) = (Node) 0;
	}
	N_KIND(node) = as_insert;
	N_VAL (node) = (char *) 0;
	N_AST1(node) = post_node;
	N_LIST(node) = pre_list;
	if (N_TYPE_DEFINED(N_KIND(post_node))) {
		N_TYPE(node) = N_TYPE(post_node);
	}
}

void propagate_insert(Node from_node, Node to_node)		/*;propagate_insert*/
{
	/* From node is an insert node that is to be propagated to to_node */

	Node	post_node;
	Tuple	pre_list;

	post_node = N_AST1(from_node);
	pre_list    = N_LIST(from_node);
	copy_attributes(post_node, from_node);
	copy_attributes(to_node, post_node);
	make_insert_node(to_node, pre_list, post_node);
}

Node new_expanded_node(Node exp_node)					/*;new_expanded_node*/
{
	/* Creates an as_expanded node */

	Node	node;

	if (exp_node == OPT_NODE)  return OPT_NODE;
	node        = new_node(as_expanded);
	N_AST1(node) = exp_node;
	return node;
}

/* Node management */
Node copy_node(Node node1)									/*;copy_node*/
{
	Node	node2;

	if (node1 == OPT_NODE) {
		compiler_error("Attempt to copy OPT_NODE");
		return OPT_NODE;
	}
	node2 = node_new(N_KIND(node1));
	copy_attributes(node1, node2) ;
	return node2;
}

void copy_attributes(Node old_node, Node target_node)		/*;copy_attributes*/
{
	int 	nk;

	if (N_KIND(old_node) == as_opt)
		compiler_error("Copying OPT kind");

	nk = N_KIND(old_node);
	N_KIND(target_node) = nk;
	if (N_AST1_DEFINED(nk)) N_AST1(target_node) = N_AST1(old_node);
	if (N_AST2_DEFINED(nk)) N_AST2(target_node) = N_AST2(old_node);
	if (N_AST3_DEFINED(nk)) N_AST3(target_node) = N_AST3(old_node);
	if (N_AST4_DEFINED(nk)) N_AST4(target_node) = N_AST4(old_node);
	if (N_LIST_DEFINED(nk)) N_LIST(target_node) = N_LIST(old_node);
	if (N_VAL_DEFINED(nk)) N_VAL (target_node) = N_VAL (old_node);
	N_UNQ (target_node) = N_UNQ (old_node);
	N_TYPE(target_node) = N_TYPE(old_node);
	N_SIDE(target_node) = N_SIDE(old_node);
#ifdef TBSL
	-- see if any other fields need becopied
#endif
}

Node copy_tree(Node node)										/*;copy_tree*/
{
	/* Create a full copy of the tree rooted at node, and return the new root*/

	Fortup	ft1;
	Tuple	tup;
	Node n, root;
	int i, nk;

	if (node == (Node)0 || node == OPT_NODE)
		return (node);
	root = node_new(N_KIND(node));

	nk = N_KIND(node);
	if (N_VAL_DEFINED(nk)) N_VAL (root) = N_VAL (node) ;
	/* N_UNQ defined only if N_AST3 not defined */
	if (!N_AST3_DEFINED(nk)) N_UNQ (root) = N_UNQ (node) ;
	/* N_TYPE defined only if N_AST4 not defined */
	if (!N_AST4_DEFINED(nk)) N_TYPE(root) = N_TYPE(node) ;
	N_SIDE(root) = N_SIDE(node) ;
	if (N_AST1_DEFINED(nk)) N_AST1(root) = copy_tree(N_AST1(node));
	if (N_AST2_DEFINED(nk)) N_AST2(root) = copy_tree(N_AST2(node));
	if (N_AST3_DEFINED(nk)) N_AST3(root) = copy_tree(N_AST3(node));
	if (N_AST4_DEFINED(nk)) N_AST4(root) = copy_tree(N_AST4(node));

	if (N_LIST_DEFINED(nk) && N_LIST(node) != (Tuple)0) {
		tup = tup_new(tup_size(N_LIST(node)));
		FORTUPI(n=(Node), N_LIST(node), i, ft1);
			tup[i] = (char *) copy_tree(n);
		ENDFORTUP(ft1);
		N_LIST(root) = tup ;
	}
	return root;
}

Node new_node(int kind)											/*;new_node*/
{
	Node	node;

	node = node_new(kind);
	return node;
}

void delete_node(Node node)									/*;delete_node*/
{
#ifdef TRACE
	if (debug_flag)
		gen_trace_node("DELETE", node);
#endif

	N_KIND(node) = as_deleted;
	N_SIDE(node) = FALSE;
	N_VAL (node) = (char *) 0;
	N_LIST(node) = (Tuple) 0;
	N_AST1(node) = N_AST2(node) = N_AST3(node) = N_AST4(node) = (Node) 0;
}

void copy_span(Node old, Node newn)							/*;copy_span */
{
	/* make this a noop in the code generator as spans field is undefined */
	return;
}

int is_terminal_node(short kind)					/*;is_terminal_node */
{
	/* noop in generator as spans field is undefined */
	return 0;
}
