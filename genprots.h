/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "genop.h"

void gen(int);
void gen_c(int, char *);
void gen_i(int, int);
void gen_ic(int, int, char *);
void gen_k(int, int);
void gen_kc(int, int, char *);
void gen_ki(int, int, int);
void gen_kic(int, int, int, char *);
void gen_ks(int, int, Symbol);
void gen_ksc(int, int, Symbol, char *);
void gen_kv(int, int, Const);
void gen_kvc(int, int, Const, char *);
void gen_rc(int, Explicit_ref, char *);
void gen_s(int, Symbol);
void gen_sc(int, Symbol, char *);
void assemble(Op);
Explicit_ref explicit_ref_new(int, int);
void print_ref_map_local();
void print_ref_map_global();
