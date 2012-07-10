/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

Node new_instance_node(Tuple);
Node new_number_node(int);
Node new_subtype_decl_node(Symbol);
Node new_name_node(Symbol);
Node new_attribute_node(int, Node arg1, Node arg2, Symbol);
Node new_unop_node(Symbol, Node arg1, Symbol);
Tuple new_check_disc_node (Symbol type1, Symbol type2);
Node new_check_bounds_node(Symbol type1, Symbol type2);
Node new_statements_node(Tuple);
Node new_assign_node(Node, Node);
Node new_call_node(Symbol, Tuple, Symbol);
void make_insert_node(Node, Tuple, Node);
Node copy_node(Node);
void copy_attributes(Node, Node);
void copy_span(Node, Node);
void set_span(Node, Span);
Node copy_tree(Node);
