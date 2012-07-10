/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "libhdr.h"
#include "ifile.h"

char *predef_unit_name(int);
int predef_node_count(int);
int predef_symbol_count(int);
int in_aisunits_read(char *);
void unit_nodes_add();
int init_predef();
int retrieve(char *);
int last_comp_index(IFILE *);
int stub_retrieve(char *);
void update_lib_maps(char *, char);
char *unit_name_name(char *);
int stub_parent_get(char *);
void stub_parent_put(char *, char *);
char *unit_name_names(char *);
char *stub_ancestors(char *);
char *stub_ancestor(char *);
int is_subunit(char *);
void unit_nodes_add(Node);
Unitdecl unit_decl_new();
Stubenv stubenv_new();
void unit_decl_put(char *, Unitdecl);
Unitdecl unit_decl_get(char *);
void lib_unit_put(char *, char *);
char *lib_unit_get(char *);
char *lib_stub_get(char *);
int current_level_get(char *);
void lib_stub_put(char *s, char *);
void current_level_put(char *, int);
int stub_number(char *);
int stub_numbered(char *);
int unit_number(char *);
void unit_number_expand(int);
int unit_numbered(char *);
Symbol getsymptr(int, int);
void symtab_restore(Tuple);
Tuple sym_save(Tuple, Symbol, char);
