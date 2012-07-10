/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "segment.h"

int ada_bool(int);
int assoc_symbol_exists(Symbol, int);
Symbol assoc_symbol_get(Symbol, int);
void assoc_symbol_put(Symbol, int, Symbol);
#ifdef DEBUG
void compiler_error_k(char *, Node);
void compiler_error_c(char *, Tuple);
void compiler_error_s(char *, Symbol);
#endif
Tuple discriminant_list_get(Symbol);
int emap_get(Symbol);
void emap_put(Symbol, char *);
void emap_undef(Symbol);
void generate_object(Symbol);
Tuple get_constraint(Symbol);
Symbol get_type(Node);
int has_discriminant(Symbol);
int has_static_size(Symbol);
int is_access_type(Symbol);
int is_aggregate(Node);
int is_array_type(Symbol);
int is_entry_type(Symbol);
int is_enumeration_type(Symbol);
int is_float_type(Symbol);
int is_formal_parameter(Symbol);
int is_global(Symbol);
int is_integer_type(Symbol);
int is_ivalue(Node);
int is_object(Node);
int is_record_subtype(Symbol);
int is_record_type(Symbol);
int is_renaming(Symbol);
int is_simple_name(Node);
int is_simple_type(Symbol);
int is_static_type(Symbol);
int local_reference_map_defined(Symbol);
Tuple local_reference_map_new();
unsigned int local_reference_map_get(Symbol);
void local_reference_map_put(Symbol, int);
int mu_size(int);
int su_size(int);
void next_local_reference(Symbol);
void next_global_reference_def(Symbol);
void next_global_reference_r(Symbol, int, unsigned int);
void next_global_reference_segment(Symbol, Segment);
void next_global_reference_template(Symbol, Segment);
void next_global_reference_z(Symbol);
void next_global_reference_word(Symbol, int);
Symbol new_unique_name(char *);
Segment segment_map_get(Tuple, int);
Tuple segment_map_put(Tuple, int, Segment);
Const	small_of(Symbol);
