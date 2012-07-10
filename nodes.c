/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* nodes.c: C version of nodes.stl*/
#include "hdr.h"
#include "vars.h"
#include "setprots.h"
#include "nodesprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "sspansprots.h"
#include "chapprots.h"

/*
 * Tree construction procedures
 *--------------------
 * 2. Lexical elements
 */

Node new_instance_node(Tuple value)						/*;new_instance_node*/
{
	/* construct an instance node used to hold tuples used for instantiations */

	Node	node;

	node = node_new(as_instance_tuple);
	N_VAL (node) = (char *) value;
	return node;
}

Node new_number_node(int value)							/*;new_number_node*/
{
	/* constructs an number node, used to hold small integer values used for
	 * attributes and return statement depth.
	 */

	Node	node;

	node = node_new(as_number);
	N_VAL (node) = (char *) value;
	return node;
}

Node new_subtype_decl_node(Symbol type_name)		/*;new_subtype_decl_node*/
{
	Node node;

	node         = node_new(as_subtype_decl);
	N_AST1(node) = new_name_node(type_name);
	N_AST2(node) = OPT_NODE;
	return node;
}

Node new_name_node(Symbol name)								/*;new_name_node*/
{
	/* constructs an as_simple_name node. */

	Node	node;

	node	     = node_new(as_simple_name);
	N_UNQ(node) = name;
	return node;
}

Node new_attribute_node(int attr, Node arg1, Node arg2, Symbol typ)
														/*;new_attribute_node*/
{
	/* Creates an attribute node. attr is the attribute's name.*/

	Node	id_node, attr_node;

	id_node	     = node_new(as_number);
	N_VAL (id_node)   = (char *) attr;
	attr_node	     = node_new(as_attribute);
	N_AST1(attr_node) = id_node;
	N_AST2(attr_node) = arg1;
	N_AST3(attr_node) = arg2;
	N_TYPE(attr_node) = typ;
	return attr_node;
}

/*
 *----------------------------------------
 * 4.5 Operators and expression evaluation
 */

Node new_unop_node(Symbol oper, Node arg1, Symbol typ)		/*;new_unop_node*/
{
	/* Creates a unary operator node. Oper is the operator's name */

	Node	id_node, list_node, node;

	id_node = new_name_node(oper);
	list_node = node_new(as_list);
	N_LIST(list_node) = tup_new1((char *) arg1);
	node = node_new(as_un_op);
	N_AST1(node) = id_node;
	N_AST2(node) = list_node;
	N_TYPE(node) = typ;
	return node;
}

/* this new procedure has the same functionalities as
new_check_bounds. It defines the tests that have to be performed at
execution time. We have been inspired by what has been done in
chapter 12 for the checking of parameters to generic units */

Tuple new_check_disc_node (Symbol type1, Symbol type2) /* new_check_disc_node */
{
	Tuple checks, g_list, a_list, g_discr_map;
	int i;
	Fortup ft;
	Node n, t, d;
	Symbol discr;

	checks = tup_new (0);

	g_list = discriminant_list(base_type(type1));
	a_list = discriminant_list(base_type(type2));
	g_discr_map = (Tuple) SIGNATURE(type1)[2];

	FORTUPI(discr=(Symbol), g_list, i, ft)
		n = node_new(as_check_discr);
		t = new_name_node(type2);
		d = new_name_node((Symbol) a_list[i]);
		N_AST1(n) = discr_map_get(g_discr_map, discr);
		N_AST2(n) = t;
		N_AST3(n) = d;
		checks = tup_with (checks, (char *) n);
	ENDFORTUP(ft);
	return checks;
}

Node new_check_bounds_node(Symbol type1, Symbol type2)
													/*;new_check_bounds_node */
{
	/* used to check that component types of array conversions have the same
	 * bounds. Should also be used in check_actual_constraint (12c)
	 */

	 Node n, t1, t2;

	 n  = node_new(as_check_bounds);
	 t1 = new_name_node(type1);
	 t2 = new_name_node(type2);
	 N_AST1(n) = t1;
	 N_AST2(n) = t2;
	 return n;
}

/*
 *------------------------------------------------------------
 * 5.1 Simple and compound statements - Sequence of statements
 */

Node new_statements_node(Tuple stmt_list)			/*;new_statements_node*/
{
	/* Creates an as_statements node, given a list (tuple) of statements */

	Node	stmt_node, list_node;

	stmt_node	     = node_new(as_statements);
	list_node	     = node_new(as_list);
	N_LIST(list_node) = stmt_list;
	N_AST1(stmt_node) = list_node;
	N_AST2(stmt_node) = OPT_NODE;
	return stmt_node;
}

/*
 *-------------------------
 * 5.2 Assignment statement
 */

Node new_assign_node(Node lhs, Node rhs)				/*;new_assign_node*/
{
	/* Creates an assign node */

	Node	node;

	node	       = node_new(as_assignment);
	N_AST1(node) = lhs;
	N_AST2(node) = rhs;
	return node;
}

/*
 *-----------------
 * 5.3 If statement
 */

Node new_call_node(Symbol proc_name, Tuple arg_list, Symbol type_name)
															/*;new_call_node*/
{
	/* Creates a call node.*/

	Node	list_node, call_node;

	list_node = node_new(as_list);
	N_LIST(list_node) = arg_list;

	call_node = node_new(as_call);
	N_TYPE(call_node) = type_name;
	N_AST1(call_node) = new_name_node(proc_name);
	N_AST2(call_node) = list_node;
	return call_node;
}

void make_insert_node(Node node, Tuple pre_list, Node post_node)
														/*;make_insert_node*/
{
	/* Transforms node into an insert node */

	int nk;

	nk = N_KIND(node);
	N_KIND(node) = as_insert;
	N_AST1(node) = post_node;
	if (N_AST2_DEFINED(nk)) N_AST2(node) = (Node)0;
	if (N_AST3_DEFINED(nk)) N_AST3(node) = (Node)0;
	if (N_AST4_DEFINED(nk))  /* copy ast4 if defined */
	   N_AST4(node) = (Node)0;
	/* or set n_type if post_node has n_type defined */
	else if (N_TYPE_DEFINED(N_KIND(post_node)))
	   N_TYPE(node) = N_TYPE(post_node);
	if (N_VAL_DEFINED(nk)) N_VAL (node) = (char *)0;
	N_LIST(node) = pre_list; /* TBSL: is copy needed  ds 7 nov */
}

Node copy_node(Node node)	/*;copy_node*/
{
	Node node2;

	node2 = node_new(N_KIND(node));
	copy_attributes(node, node2);
	if (is_terminal_node(N_KIND(node)))
	  copy_span(node, node2);/* TBSL: check whether this is always desirable */
	return node2;
}

void copy_attributes(Node old, Node newn)				/*;copy_attributes*/
{
	/*  copy attributes of old to new, preserving sequence and unit of new */

	char	*np, *op;
	Span	save_span;
	short	terminal;
	int i, n, nseq, nunit;

	nseq = N_SEQ(newn);
	nunit = N_UNIT(newn);
	terminal = (is_terminal_node(N_KIND(old)) && is_terminal_node(N_KIND(newn)));
	if (terminal) save_span = get_left_span(newn);
	n = sizeof(Node_s);
	op = (char *)old; np = (char*) newn;
	for (i=1; i <= n; i++) *np++ = *op++;
	N_UNIT(newn) = nunit;
	N_SEQ(newn) = nseq;
	if (terminal) set_span(newn, save_span);
}

void copy_span(Node old, Node newn)							/*;copy_span */
{
	/* retrieve left spans of old node and set spans fields of new node */
	
	Span span;

	span = get_left_span(old);
	N_SPAN0(newn) = span->line;
	N_SPAN1(newn) = span->col;
	efreet((char *) span, "spans");
}

void set_span(Node node, Span span)								/*;set_span */
{
	/* set span of node to the values in span */
	N_SPAN0(node) = span->line;
	N_SPAN1(node) = span->col;
}

Node copy_tree(Node node)										/*;copy_tree*/
{
	/* Create a full copy of the tree rooted at node, and return the new root*/

	Fortup	ft1;
	Tuple	tup;
	Node n, root;
	int i;

	if (node == (Node)0 || node == OPT_NODE) 
	return (node);
	root = node_new(N_KIND(node));
	N_KIND(root) = N_KIND(node); i = N_KIND(node);
	N_OVERLOADED(root) = N_OVERLOADED(node);
	N_VAL(root) = N_VAL(node);
	N_UNQ(root) = N_UNQ(node);
	N_NAMES(root) = N_NAMES(node);
	N_TYPE(root) = N_TYPE(node);
	N_PTYPES(root) = N_PTYPES(node);
	if (N_AST1_DEFINED(i)) N_AST1(root) = copy_tree(N_AST1(node));
	if (N_AST2_DEFINED(i)) N_AST2(root) = copy_tree(N_AST2(node));
	if (N_AST3_DEFINED(i)) N_AST3(root) = copy_tree(N_AST3(node));
	if (N_AST4_DEFINED(i)) N_AST4(root) = copy_tree(N_AST4(node));
	if (is_terminal_node((unsigned) i)) copy_span(node, root);

	if (N_LIST_DEFINED(i) && N_LIST(node) != (Tuple)0) {
	tup = tup_new(tup_size(N_LIST(node)));
	FORTUPI(n=(Node), N_LIST(node), i, ft1);
	    tup[i] = (char *) copy_tree(n);
	ENDFORTUP(ft1);
	N_LIST(root) = tup;
	}
	return root;
}
