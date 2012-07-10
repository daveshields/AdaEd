/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

void select_assign(Node, Node, Symbol);
Tuple make_case_table(Node);
void gen_case(Tuple, Tuple, Node,int);
void compile_body(Node, Node, Node, int);
void gen_condition(Node, Symbol, int);
void gen_loop(Node);
