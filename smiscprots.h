/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

void ast_clear(Node);
Const const_new(int);
Const int_const(int);
Const fixed_const(long);
Const uint_const(int *);
Const real_const(double);
Const rat_const(Rational);
int const_eq(Const, Const);
int const_ne(Const, Const);
int const_lt(Const, Const);
int const_le(Const, Const);
int const_gt(Const, Const);
int const_ge(Const, Const);
int const_same_kind(Const, Const);
int const_cmp_undef(Const, Const);
Node node_new_noseq(unsigned int);
Node node_new(unsigned int);
int fx_mantissa(Rational, Rational, Rational);
void to_errfile(char *);
int needs_body(Symbol);
char *kind_str(unsigned int);
char *nature_str(int);
int in_open_scopes(Symbol);
char *newat_str();
char *str_newat();
void symtab_copy(Symbol, Symbol);
void sym_copy(Symbol, Symbol);
void SYMBTABcopy(Symbol, Symbol);
Symbol sym_new_noseq(int);
Symbol sym_new(int);
Private_declarations private_decls_new(int);
Symbol private_decls_get(Private_declarations, Symbol);
void private_decls_put(Private_declarations, Symbol);
void private_decls_swap(Symbol, Symbol);
char *attribute_str(int);
int no_dimensions(Symbol);
int in_incp_types(Symbol);
int in_qualifiers(unsigned int);
int in_univ_types(Symbol);
int in_vis_mods(Symbol);
void undone(char *);
int is_type(Symbol);
int is_fixed_type(Symbol);
int is_generic_type(Symbol);
int is_access(Symbol);
int is_scalar_type(Symbol);
int is_numeric_type(Symbol);
int is_record(Symbol);
int is_anonymous_task(Symbol);
int is_task_type(Symbol);
Node discr_map_get(Tuple, Symbol);
Tuple discr_map_put(Tuple, Symbol, Node);
int tup_memsym(Symbol, Tuple);
void const_check(Const, int);
int power_of_2(Const);
Node new_ivalue_node(Const, Symbol);
Tuple constraint_new(int);
