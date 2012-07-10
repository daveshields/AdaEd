/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

Node new_number_node(int);
Node new_instance_node(Tuple);
void make_ivalue_node(Node, Const, Symbol);
#ifndef BINDER
void make_single_decl_list(Node, Node);
#endif
void make_const_node(Node, Symbol, Symbol, Node);
Node new_var_node(Symbol, Symbol, Node);
Node new_subtype_decl_node(Symbol);
Node new_null_node(Symbol);
Node new_name_node(Symbol);
void make_name_node(Node, Symbol);
Node new_index_node(Node, Tuple, Symbol);
void make_index_node(Node, Node, Tuple, Symbol);
Node new_selector_node(Node, Symbol);
void make_selector_node(Node, Node, Symbol);
Node new_discr_ref_node(Symbol, Symbol);
void make_discr_ref_node(Node, Symbol, Symbol);
Node new_attribute_node(int, Node arg1, Node, Symbol);
Node new_binop_node(Symbol, Node arg1, Node, Symbol);
Node new_qual_range_node(Node, Symbol);
Node new_statements_node(Tuple);
void make_statements_node(Node, Tuple);
Node new_assign_node(Node, Node);
void make_assign_node(Node, Node, Node);
Node new_simple_if_node(Node, Node, Node);
void make_if_node(Node, Tuple, Node);
Node new_cond_stmts_node(Node, Node);
Node new_loop_node(Node, Node, Tuple);
Node new_block_node(Node, Tuple, Tuple, Node);
void make_subprog_node(Node, Symbol, Node, Node, Node);
Node new_param_node(char *, Symbol, Symbol, int);
Node new_call_node(Symbol, Tuple, Symbol);
Node new_create_task_node(Symbol);
Node new_raise_node(Symbol);
void make_raise_node(Node, Symbol);
void make_insert_node(Node, Tuple, Node);
void propagate_insert(Node, Node);
Node new_expanded_node(Node);
Node copy_node(Node node1);
void copy_attributes(Node, Node);
Node copy_tree(Node);
Node new_node(int);
void delete_node(Node);
void copy_span(Node, Node);
int is_terminal_node(short);
