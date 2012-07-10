/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "segment.h"

unsigned int subprog_patch_get(Symbol);
void subprog_patch_put(Symbol, int);
void subprog_patch_undef(Symbol);
Symbol base_type(Symbol);
int is_discrete_type(Symbol);
int is_unconstrained(Symbol);
int not_included(Symbol, Symbol);
#ifndef BINDER
void optional_qual(Symbol, Symbol);
#endif
int kind_of(Symbol);
int length_of(Symbol);
void new_symbol(Symbol, int, Symbol, Tuple, Symbol);
void reference_of(Symbol);
int is_defined(Symbol);
Symbol get_constant_name(Segment);
void assign_same_reference(Symbol, Symbol);
int select_entry(int a_map_code, Symbol, int);
void optional_deref(Symbol);
Const get_ivalue(Node);
int get_ivalue_int(Node);
int get_const_int(Const);
char *formatted_name(char *);
int size_entry(Symbol);
int is_generated_label(Symbol);
void patch_code(unsigned int, unsigned int);
void patch_code_byte(int, int);
void update_code(int, int);
#ifdef DEBUG
void compiler_error(char *);
#endif
void errmsg(char *, char *, Node);
#ifdef TRACE
void gen_trace(char *);
void gen_trace_node(char *, Node);
void gen_trace_nodes(char *, Tuple);
void gen_trace_symbol(char *, Symbol);
void gen_trace_symbols(char *, Tuple);
void gen_trace_string(char *, char *);
void gen_trace_strings(char *, Tuple);
void gen_trace_units(char *, Set);
#endif
void labelmap_put(Symbol, int, char *);
Tuple labelmap_get(Symbol);
Tuple unit_slots_get(int);
void unit_slots_put(int, Tuple);
void user_warning(char *s1, char *s2);
int is_generic(char *);
int is_ancestor(char *);
void list_hdr(int);
#ifdef MACHINE_CODE
void to_gen(char *);
void to_gen_int(char *, int);
void to_gen_unam(char *, char *, char *s2);
#endif
void to_list(char *);
