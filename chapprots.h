/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/* Only 12b used by adagen*/
#ifndef GEN

/* 0a */
void init_sem();
int in_op_designators(char *);

/* 0b */
void adasem(Node);
void sem_list(Node);

/* 2 */
void process_pragma(Node);

/* 3a */

void obj_decl(Node);
void const_decl(Node);
Symbol check_init(Node, Node);
int is_deferred_constant(Node);
void number_decl(Node);
void type_decl(Node);
Symbol find_type_name(Node);
void check_delayed_type(Node, Symbol);
void subtype_decl(Node);
Symbol make_subtype(Node);
int is_derived_subprogram(Symbol);

/* 3b */
Tuple apply_range(Node);
void array_typedef(Node);
void new_array_type(Symbol, Node);
void new_constrained_array(Symbol, Node);
Symbol anonymous_array(Node);
Symbol constrain_array(Symbol, Node);
Symbol make_index(Node);
void record_decl(Symbol, Node, Node);
void process_discr(Symbol, Node);
void discr_redecl(Symbol, Node);
int same_expn(Node exp1, Node exp2);
void conformance_error(Node);
void comp_decl(Node);
Symbol constrain_record(Symbol, Node);
int check_discriminant(Node);
void variant_decl(Node);
void incomplete_decl(Node);
void check_incomplete(Symbol);
void declarative_part(Node);
Symbol promote_subtype(Symbol);
Tuple subtype_expr(Symbol);
int is_character_type(Symbol);
int is_discrete_type(Symbol);
int is_numeric(Symbol);
int is_incomplete_type(Symbol);
int is_unconstrained(Symbol);
Symbol base_type(Symbol);
Symbol named_type(char *);
Symbol anonymous_type();
Symbol named_atom(char *);
int is_static_expr(Node);

/* 4a */
int in_type_classes(Symbol);
void check_type_i(Node);
void check_type_r(Node);
void check_type_d(Node);
void check_type_u(Node);
void check_type(Symbol, Node);
void apply_constraint(Node, Symbol);
int in_priv_types(Symbol);
void resolve1(Node);
void resolv_attr(Node);
void resolve2(Node, Symbol);

/* 4b */
void result_types(Node);
void disambiguate(Node, Symbol);
void remove_conversions(Node);
Tuple valid_arith_types(Symbol, Tuple);
Symbol intersect_types(Symbol t1, Symbol t2);
void complete_op_expr(Node, Symbol);
void specialize(Node, Symbol);
void complete_arg_list(Tuple, Node);

/* 4c */
int can_constrain(Symbol);
Set valid_array_expn(Node);
Symbol complete_array_expn(Node, Symbol);
void valid_selected_expn(Node);
Symbol complete_selected_expn(Node, Symbol);
void complete_aggregate(Symbol, Node);
void complete_string_literal(Node, Symbol);
void complete_r_aggregate(Symbol, Node);
Tuple build_comp_names(Node);
void valid_task_name(Node);
void complete_task_name(Node task1, Symbol);
void res2_check(Node expn2, Symbol);
Symbol attribute_type(int, Symbol, Node arg1, Node arg2);
int compatible_types(Symbol, Symbol);
void type_error(Set, Symbol, int, Node);
void premature_access(Symbol, Node);
void pass1_error(char *msg1, char *, Node);
char *full_type_name(Symbol);
int is_type_node(Node);

/* 5 */
Symbol slice_type(Node,int);
Symbol get_type(Node);
void assign_statement(Node);
int is_variable(Node);
void statement_list(Node);
void if_statement(Node);
void case_statement(Node);
void process_case(Symbol, Node);
int is_static_subtype(Symbol);
void new_block(Node);
void loop_statement(Node);
Symbol iter_var(Node);
void exit_statement(Node);
void return_statement(Node);
void label_decl(Node);
void lab_init();
void lab_end();
void goto_statement(Node);

/* 6 */
void subprog_decl(Node);
void check_spec(Node);
void check_new_op(Node, Tuple, Symbol);
Tuple get_formals(Node, char *);
void subprog_body(Node);
void process_subprog_body(Node, Symbol);
Node new_not_equals(Symbol, Symbol);
Tuple process_formals(Symbol, Tuple,int);
void reprocess_formals(Symbol, Node);
void normalize(Symbol, Node);
int conform(Node exp1, Node exp2);
void call_statement(Node);
Symbol chain_overloads(char *, int, Symbol, Tuple, Symbol, Node);
int can_overload(Symbol);
int same_signature(Symbol sub1, Symbol sub2);
int same_sig_spec(Symbol, Tuple);
int same_type(Symbol type1, Symbol type2);

/* 7 */
void package_specification(Node);
void new_package(Node, int);
void package_declarations(Node, Node);
void module_body_id(int, Node);
void module_body(int, Node);
void private_decl(Node);
void check_fully_declared(Symbol);
void check_fully_declared2(Symbol);
int is_private(Symbol);
int is_limited_type(Symbol);
void check_out_parameters(Tuple);
int in_private_part(Symbol);
int private_kind(Symbol);
int is_fully_private(Symbol);
void check_priv_decl(int, Symbol);
Symbol private_ancestor(Symbol);
void end_specs(Symbol);
void check_incomplete_decls(Symbol, Node);
Symbol get_specs(char *);

/* 8 */
void find_old(Node);
Symbol find_type(Node);
void check_old(Node);
Set find_agg_types();
Set find_access_types();
Symbol find_new(char *);
void check_void(char *);
void new_agg_or_access_acc(Symbol);
void new_agg_or_access_agg(Symbol);
char *original_name(Symbol);
void rename_ex(Node);
void rename_pack(Node);
void rename_subprogram(Node);
Tuple find_renamed_entity(int, Tuple, Symbol, Node);
void rename_object(Node);
void newscope(Symbol);
void popscope();
void newmod(char *);
void use_clause(Node);

/* 9 */
void task_spec(Node);
void accept_statement(Node);
void entry_decl(Node);
void entry_family_decl(Node);
void entry_call(Node);
void check_entry_call(Node);
void find_entry_name(Node);
void terminate_statement(Node);
void abort_statement(Node);

/* 10 */
void new_compunit(char *, Node);
void compunit(Node);
#ifdef SAVE_TRACE
void save_trace(char *, int, Node);
#endif
void save_trace_init();
Tuple unit_symbtab(Symbol, char);
void save_subprog_info(Symbol);
void save_spec_info(Symbol, Tuple);
void save_body_info(Symbol);
void stub_head(int, Node);
void save_stub(Node);

/* 11 */
void except_decl(Node);
void exception_part(Node);
void exception_handler(Node);
void raise_statement(Node);

/* 12a */
void generic_subprog_spec(Node);
void generic_subprog_body(Symbol, Node);
void generic_pack_spec(Node);
void generic_obj_decl(Node);
void generic_type_decl(Node);
void generic_priv_decl(Node);
void check_generic_usage(Symbol);
void generic_subp_decl(Node);
void subprog_instance(Node);
void package_instance(Node);

#endif
/* 12b */
void instantiate_subprog_tree(Node, Symbolmap);
void instantiate_pack_tree(Node, Symbolmap, Tuple);
Tuple instantiate_symbtab(Symbol, Symbol, Symbolmap);
void update_symbtab_nodes(Symbolmap, Tuple);
Private_declarations update_private_decls(Symbol, Symbolmap);
Node instantiate_tree(Node, Symbolmap);
Symbol replace(Symbol, Symbolmap);
Symbolmap symbolmap_new();
Symbol symbolmap_get(Symbolmap, Symbol);
void symbolmap_put(Symbolmap, Symbol, Symbol);
Nodemap nodemap_new();
#ifndef GEN

/* 12c */
Tuple instantiate_generics(Tuple, Node);
Tuple check_nat_type(Node);
void desig_to_op(Node);
int is_discriminant_dependent(Node);
void linear(Symbol);
Symbol anon_proc_instance(Symbol, Tuple, Symbol);
void is_identifier();
void is_tuple();

/* 13 */
void length_clause(Node);
void enum_rep_clause(Node);
void rec_rep_clause(Node);
void initialize_representation_info(Symbol, int);
void choose_representation(Symbol);
void inherit_representation_info(Symbol, Symbol);
int	 already_forced(Symbol);
void not_chosen_put(Symbol, Symbol);
Node size_attribute(Node);
Node storage_size_attribute(Node);
void force_representation(Symbol);
void force_all_types();
/* 14 */
void check_range_attribute(Node);
#endif
