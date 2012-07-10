/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/*  expand */
void expand(Node);

/* expand2 */
void expand_line();
int in_bin_ops(Symbol);
int in_un_ops(Symbol);
void expand_block(Node, Node, Node, Node);
Symbol op_kind(Node);
static void replace_name(Node, Symbol, Symbol);
void check_priv_instance(Tuple, Symbolmap);
void expand_decl(Node);
void expand_type(Node);
void expand_subtype(Node);
void expand_attr(Node);
void expand_string(Node);
void expand_op(Node);
void expand_for(Node);
void mint(Node);
