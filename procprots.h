/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

void gen_subprogram_spec(Node);
void gen_subprogram(Node);
void unit_subprog_spec(Node);
void unit_subprog(Node);
void gen_prelude(Symbol, Node);
void gen_postlude(Symbol, Node);
void gen_accept(Symbol, Node, Node);
int offset_max(int, int);
