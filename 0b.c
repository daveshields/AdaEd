/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "hdr.h"
#include "vars.h"
#include "dbxprots.h"
#include "errmsgprots.h"
#include "dclmapprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "chapprots.h"
#include <ctype.h>
/* ctype.h needed for isupper, tolower, etc in 4.2 bsd*/

void adasem(Node node)											/*;adasem*/
{
	/* This is the driver routine for  all semantic processing. It is called
	 * by  the parser  whenever the syntax	tree  for a compilation unit has
	 * been built. The input  to this routine  is an AST node,  on which two
	 * maps are defined : AST, and SPANS. These maps are global to the front
	 * end.
	 */

	Node	n1, n2, n3, n4;
	char	*id, *op_id;
	Fortup	ft1;
	Tuple	tup;
	Node	decl_node, id_node, l;
	Symbol	package, s1;

	if (cdebug2 > 2) {
		/*    TO_ERRFILE("node type ");*/
#ifdef IBM_PC
		printf("node type: %s %d %p\n", kind_str(N_KIND(node)), N_KIND(node),
		  node);
#else
		printf("node type: %s %d %ld\n", kind_str(N_KIND(node)), N_KIND(node),
		  node);
#endif
	}

	/* The current node is placed in a global variable, from which the error
	 * routines can extract its span.
	 */
	current_node = node;

#ifdef DEBUG
	if (trapns>0 && N_SEQ(node) == trapns && N_UNIT(node) == trapnu)trapn(node);
#endif
	switch(N_KIND(node)) {

	/* Chapter 2. Lexical elements*/

	/* pragma  ->  [as_pragma  identifier argument_list]*/
	case(as_pragma):
		process_pragma(node);
		break;

	/* argument_association	 ->  [as_arg  identifier  expression]*/
	case(as_arg):
		break;			/*Unpacked in process_pragmas.*/

	/* Chapter 3. Declarations and types */

	/*  object_declaration ->  [as_obj_decl	identifier_list subtype_indic
	 *							opt_expression]
	 */
	case(as_obj_decl):
		obj_decl(node);
		break;

	/* const_declaration  ->  ['const_decl' identifier_list subtype_indic
	 *							opt_expression]
	 */
	case(as_const_decl):
		const_decl(node);
		break;

	/* num_declaration    ->  ['num_decl'  identifier_list expression]*/
	case(as_num_decl):
		number_decl(node);
		break;

	/* type_decl  ->  ['type_decl' identifier discriminant_list
	 *							type_definition]
	 */
	case(as_type_decl):
		type_decl(node);
		break;

	/* Subtype_decl ->  ['subtype_decl' identifier subtype_indic]*/
	case(as_subtype_decl):
		subtype_decl(node);
		break;

	/* subtype_indication  ->  ['subtype_indic', name opt_constraint]*/
	case(as_subtype_indic):
		/*[name, opt_constraint] := N_AST(node);*/
		adasem(N_AST1(node));
		adasem(N_AST2(node));
		break;

	/* derived_type_definition  -> ['derived_type'	subtype_indication]*/
	case(as_derived_type):
		break;

	/* discrete_range  ->  ['range' expression  expression]*/
	case(as_range):
		/*[expression1, expression2] := N_AST(node);*/
		adasem(N_AST1(node));
		adasem(N_AST2(node));
		break;

	/* range_attribute ->  ['range_attribute' name range]*/
	case(as_range_attribute):
		N_KIND(node) = as_attribute;
		n2 = N_AST3(node);
		find_old(node);
		adasem(n2);
		break;

	/* discrete_range  ->  ['range_expression'  expression]*/
	case(as_range_expression):
		adasem(N_AST1(node));
		break;

	/* constraint  ->  ['constraint'  general_aggregate]*/
	case(as_constraint):
		sem_list(node);
		break;

	/* enumeration_type  -> [as_enum  enumeration_literal_list]*/
	case(as_enum):
		sem_list(node);
		break;

	case(as_int_type):
		break;

	case(as_float_type):
		break;

	case(as_fixed_type):
		break;

	case(as_digits):
	case(as_delta):
		adasem(N_AST1(node));
		adasem(N_AST2(node));
		break;

	/* array_type_definition -> ['array_type' index_list subtype_indication]*/
	case(as_array_type):
		array_typedef(node);
		break;

	/* subtype_definition  ->  ['box'  name]*/
	case(as_box):
		adasem(N_AST1(node));
		break;

	/* discrete_range -> [as_subtype opt_name  range_constraint]
	 * general_component_association ->[as_subtype opt_name range-constraint]
	 */
	case(as_subtype):
		/*[opt_name, range_constraint] := N_AST(node);*/
		n1 = N_AST1(node);
		n2 = N_AST2(node);
		if (n1 != OPT_NODE) {
			adasem(n1);
			find_old(n1);
		}
		if (n2 == OPT_NODE) {	/* possible, if syntax error */
			N_KIND(node) = as_name;
		}
		else adasem(n2);
		break;

	/* record_decl	-> [as_record component_list]*/
	case(as_record):
		adasem(N_AST1(node));
		break;

	/* component_list  -> [ 'component_list'  component_decl_list variant]*/
	case(as_component_list):
		/*[component_decl_list, variant] := N_AST(node);*/
		sem_list(N_AST1(node));
		adasem(N_AST2(node));
		break;

	/* component_declaration -> ['field' identifier_list subtype_indic
	 *							 opt_expression]
	 */
	case(as_field):
		comp_decl(node);
		break;

	/* discr_specification -> ['discr_spec' identifier_list name opt_expr]*/
	case(as_discr_spec):
		/*[id_list_node, name, opt_expr] := N_AST(node);*/
		adasem(N_AST2(node));
		/*  adasem(N_AST3(node));   */
		break;

	/* variant_part -> ['variant_decl' simple_name variant_list]*/
	case(as_variant_decl):
		variant_decl(node);
		break;

	/* component_association -> ['choice_list'  choice_list	 expression]*/
	case(as_choice_list):
		/*[choice_list, expression] := N_AST(node);*/
		sem_list(N_AST1(node));
		adasem(N_AST2(node));
		break;

	case(as_simple_choice):
		adasem(N_AST1(node));
		break;

	case(as_range_choice):
		adasem(N_AST1(node));
		break;

	case(as_others_choice):
		break;

	case(as_choice_unresolved):
		adasem(N_AST1(node));
		break;

	case(as_access_type):
		n1 = N_AST1(node);
		adasem(n1);
		n2 = N_AST1(n1);
		n3 = N_AST2(n1);
		if (n3 == OPT_NODE ) {
			/*Special case: type mark may be an incomplete type.*/
			N_UNQ(n1) = find_type(n2);
		}
		else {	/* elaborate subtype indication*/
			N_UNQ(n1) = promote_subtype(make_subtype(n1));
		}
		break;

	/* incomplete_type_decl -> ['incomplete_decl'  identifier  discriminant]*/
	case(as_incomplete_decl):
		incomplete_decl(node);
		break;

	/* declarations -> ['declarations'  declaration_list]*/
	case(as_declarations):
		declarative_part(node);
		break;

	/* Chapter 4. Names and expressions */

	/* name	 -> ['character_literal'   character]
	 * Character literals also appear as enumeration literals, and as
	 * selectors.
	 */
	case(as_character_literal):
		break;

	/* name	  ->  ['simple_name'  identifier]*/
	case(as_simple_name):
		break;

	/* name	  ->  ['call?'	name  general_aggregate]*/
	case(as_call_unresolved):
		n1 = N_AST1(node);
		n2 = N_AST2(node);

		if (N_KIND(n1) == as_string) {
			/* Operator designator: reduce to lower case.*/
			/*N_VAL(n1) = LOWER_CASE_OF(N_VAL(n1));*/
			id = N_VAL(n1);
			while(*id) {
				if (isupper(*id)) *id = tolower(*id);
				id++;
			}
		}
		adasem(n1);
		FORTUP(n1 = (Node), N_LIST(n2), ft1);
			adasem(n1);
		ENDFORTUP(ft1);
		break;

	/* name ->  ['operator'	 operator_symbol]*/
	case(as_operator):
		N_KIND(node) = as_simple_name;
		break;

	case(as_string):
		N_KIND(node) = as_simple_name;
		break;

	/* name	 ->  ['.' name selector]*/
	case(as_selector):
		adasem(N_AST1(node));
		break;

	case(as_all):
		adasem(N_AST1(node));
		break;

	case(as_attribute):
		adasem(N_AST2(node));
		adasem(N_AST3(node));
		break;

	/* aggregate  ->  [as_aggregate expression_list]*/
	case(as_aggregate):
		sem_list(node);
		break;

	/* parenthesised_expression  ->	 ['()', expression]*/
	case(as_parenthesis):
		adasem(N_AST1(node) );
		break;

	/* expression  ->  [operator_designator	 <expression..>]*/
	case(as_op):
	case(as_un_op):
		/*[op_node, arg_list] := N_AST(node);*/
		n1 = N_AST1(node);
		op_id = N_VAL(n1);
		/* KLUDGE until parser fixed. */
		if (streq(op_id, "NOT")) N_VAL(n1) = strjoin("not", "");
		else if (streq(op_id, "AND")) N_VAL(n1) = strjoin("and", "");
		else if (streq(op_id, "XOR")) N_VAL(n1) = strjoin("xor", "");
		else if (streq(op_id, "REM")) N_VAL(n1) = strjoin("rem", "");
		else if (streq(op_id, "MOD")) N_VAL(n1) = strjoin("mod", "");
		else if (streq(op_id, "OR"))  N_VAL(n1) = strjoin("or", "");
		n2 = N_AST2(node);
		find_old(n1);

		FORTUP(n3 = (Node), N_LIST(n2), ft1);
			adasem(n3);
			/*
	    	 * the call to check_range_attribute is useless, since
	    	 * adasem converts as_range_attribute to as_attribute
	    	 *				(gcs 11 feb)
	    	 */
			/* check_range_attribute(n3); */
		ENDFORTUP(ft1);
		break;

	case(as_in):
	case(as_notin):

		n3 = N_AST2(node);
		tup = N_LIST(n3);
		n1 = (Node) tup[1];
		n2 = (Node) tup[2];
		adasem(n1);
		adasem(n2);
		break;

	case(as_int_literal):
		break;

	case(as_real_literal):
		break;

	case(as_string_literal):
		break;

	case(as_null):
		break;

	case(as_name):
		adasem(N_AST1(node));
		break;

	case(as_qualify):
		find_type(N_AST1(node));
		adasem(N_AST2(node));
		break;

	/* allocator  -> ['new_init' name aggregate]*/
	case(as_new_init):
		n1 = N_AST1(node);
		n2 = N_AST2(node);
		adasem(n1);
		adasem(n2);
		break;

	/* allocator  ->  ['new'  name	constraint_list]*/
	case(as_new):
		n1 = N_AST1(node);
		n2 = N_AST2(node);
		adasem(n1);
		sem_list(n2);
		break;

	/* Chapter 5. Statements*/

	/* sequence_of_statements  ->  ['statements' statement_list, label_list]*/
	case(as_statements):
		statement_list(node);
		break;

	/* statement  ->  ['statement'	label_list  statement]*/
	case(as_statement):
		/*[label_list, stmt] := N_AST(node);*/
		n1= N_AST1(node);
		n2= N_AST2(node);

		FORTUP(l = (Node), N_LIST(n1), ft1);
			find_old(l);
			if (NATURE(N_UNQ(l)) != na_label) {
				errmsg("label hidden by inner declaration", "5.1", l);
			}
		ENDFORTUP(ft1);

		adasem(n2);
		break;

	/* labels_declaration  ->  ['labels'  label_list]*/
	case(as_labels):
		label_decl(node);
		break;

	/* null_statement  -> [null_s']*/
	case(as_null_s):
		break;


	/* assignment  -> [':='	 name  expression ]*/
	case(as_assignment):
		assign_statement(node);
		break;

	/* if_statement	 ->  ['if' if_part_list opt_else]*/
	case(as_if):
		if_statement(node);
		break;

	/* condition  ->  ['condition' expression]*/
	case(as_condition):
		n1 = N_AST1(node);
		adasem(n1);
		check_type(symbol_boolean_type, n1);
		break;

	/* case_statement  ->  ['case' expression alt_list]*/
	case(as_case):
	case_statement(node);
		break;

	/* loop_statement  ->  ['loop'	opt_loop_id iteration_rule statements]*/
	case(as_loop):
		loop_statement(node);
		break;

	/* iteration_rule  ->  ['while'	 condition]*/
	case(as_while):
		adasem(N_AST1(node));
		break;

	/* iteration rule  ->  ['for'	 identifier  discrete_range]*/
	case(as_for):
		iter_var(node);
		break;

	/* iteration_rule  ->  ['forrev' identifier  discrete_range]*/
	case(as_forrev):
		iter_var(node);
		break;

	/* block  ->  [na_block identifier declarations statements exceptions]*/
	case(as_block):
		new_block(node);
		break;

	/* exit_statement ->  ['exit' opt_name opt_expression]*/
	case(as_exit):
		exit_statement(node);
		break;

	/* return_statement  ->	 ['return' opt_expression]*/
	case(as_return):
		return_statement(node);
		break;

	case(as_goto):
		goto_statement(node);
		break;

	/* Chapter 6. Subprograms*/

	/* subprogram_declaration  ->  ['subprogram_decl', subprogram_spec]*/
	case(as_subprogram_decl):
		subprog_decl(node);
		break;

	/* subprogram_specification -> [na_procedure identifier formals_list]
	 *			   -> [na_function  identifier formals_list name]
	 */
	case(as_procedure):
		break;

	case(as_function):
		find_type(N_AST3(node));
		break;

	/* subprogram_body  ->	['subprogram' subprogram_spec  declarations
	 *					   statements opt_exceptions]
	 */
	case(as_subprogram):
		subprog_body(node);
		break;

	/* parameter_specification -> ['formal' id_list mode name opt_expression]*/
	case(as_formal):
		break;

	/* mode	 -> ['mode'  identifier]*/
	case(as_mode):
		break;

	/* call_statement -> ['call' name]*/
	case(as_call):
		call_statement(node);
		break;

	/* Chapter 7. Packages*/

	/* package_specification  ->  [na_package_spec identifier declarations
	 *						      opt_private_part]
	 */
	case(as_package_spec):
		package_specification(node);
		break;

	/* package_body	 ->  ['package_body' identifier declarations
	 *					 opt_statements	 opt_handler]
	 */
	case(as_package_body):
		id_node = N_AST1(node);
		decl_node = N_AST2(node);
		n3 = N_AST3(node);
		n4 = N_AST4(node);
		module_body_id(na_package, id_node);
		adasem(decl_node);
		adasem(n3);
		adasem(n4);
	    force_all_types();
		module_body(na_package, node);
		package = N_UNQ(id_node);
		if (NATURE(package) == na_generic_package)
			N_KIND(node) = as_generic_package;
		break;

	/* private_type_declaration  ->	 ['private_decl' identifier
	 *					  discriminant_list priv_kind]
	 */
	case(as_private_decl):
		private_decl(node);
		break;

	/* Chapter 8. Visibility rules*/

	/* use_clause  -> [use' identifier_list]*/
	case(as_use):
		use_clause(node);
		break;

	/* renaming_declaration -> ['rename_ex' identifier name]*/
	case(as_rename_ex):
		rename_ex(node);
		break;

	/* renaming_declaration	 ->  ['rename_pack' identifier	name]*/
	case(as_rename_pack):
		rename_pack(node);
		break;

	/* renaming_declaration	 ->  ['rename_obj' identifier type_mark name]*/
	case(as_rename_obj):
		rename_object(node);
		break;

	/* renaming declarations  ->  ['rename_sub'  subprogam_spec  name]*/
	case(as_rename_sub):
		rename_subprogram(node);
		break;

	/* Chapter 9. Tasks */

	/* task_specification  ->  [task_kind identifier opt_entry_declaration
	 *							 opt_rep_clause]
	 * task_kind	       ->  'task_spec'
	 *		      ->  na_task_type_spec
	 */
	case(as_task_spec):
	case(as_task_type_spec):
		/* clear N_AST3 as specification not supported now, and
		 * need this field for N_TYPE   DS 9-21-86
		 */
		N_AST3(node) = (Node)0;
		task_spec(node);
		break;

	/* task_body  ->  ['task' identifier declarations statements
	 *							opt_exceptions]
	 */
	case(as_task):
		/*[id_node, decls, stmts, excepts] := N_AST(node);*/
		id_node = N_AST1(node);
		n2 = N_AST2(node);
		n3 = N_AST3(node);
		n4 = N_AST4(node);
		module_body_id(na_task_type, id_node);
		/* clear the private_decls field set in module_body_id as this is */
		/* irrelevant to tasks. */
		private_decls(N_UNQ(id_node)) = (Set)0;
		adasem(n2);
		adasem(n3);
		adasem(n4);
		module_body(na_task_type, node);
		s1 = N_UNQ(id_node);
		check_incomplete_decls(s1, node);
		break;

	/* entry_declaration   ->  [na_entry identifier formals_list]*/
	case(as_entry):
		entry_decl(node);
		break;

	/* * entry_declaration   ->  [na_entry_family identifier discrete_range
	 *							   formals_list]
	 */
	case(as_entry_family):
		entry_family_decl(node);
		break;

	/* accept_statement  ->	 ['accept' name opt_expression opt_formal_part
	 *						      opt_statements]
	 */
	case(as_accept):
		accept_statement(node);
		break;

	/* delay_statement  -> ['delay'	 expression]*/
	case(as_delay):
		n1 = N_AST1(node);
		adasem(n1);
		check_type(symbol_duration, n1);
		break;

	/* selective_wait  ->  ['selective_wait' alternative_list else_part]*/
	case(as_selective_wait):
		n1 = N_AST1(node);
		n2 = N_AST2(node);
		sem_list(n1);
		if (n2 != OPT_NODE)
			adasem(n2);
		break;

	/* select_alternative -> ['guard' condition selective_wait_alternative]*/
	case(as_guard):
		adasem(N_AST1(node));
		adasem(N_AST2(node));
		break;

	/* selective_wait_alternative -> ['accept_alt' accept_statement opt_stats]
	 *			     -> ['delay_alt'  delay_statement  opt_stats]
	 */
	case(as_accept_alt):
		adasem(N_AST1(node));
		adasem(N_AST2(node));
		break;

	case(as_delay_alt):
		adasem(N_AST1(node));
		adasem(N_AST2(node));
		break;

	/* selective_wait_alternative  -> ['terminate_alt' ]*/
	case(as_terminate_alt):
		terminate_statement(node);
		break;

	/* conditional_entry_call -> ['conditional_entry_call' call_statement
	 *						statements else_stat]
	 */
	case(as_conditional_entry_call):
		check_entry_call(N_AST1(node));
		adasem(N_AST2(node));
		adasem(N_AST3(node));
		break;

	/* timed_entry_call -> ['timed_entry_call', call_statement statements
	 *						   delay_alternative]
	 */
	case(as_timed_entry_call):
		check_entry_call(N_AST1(node));
		adasem(N_AST2(node));
		adasem(N_AST3(node));
		break;

	/* abort_statement  -> ['abort'	 task_name_list]*/
	case(as_abort):
		abort_statement(node);
		break;

	/* Chapter 10. Program structure...*/

	/* (as_compilation):
	 * This node is used for pragmas that precede a compilation unit.
	 * TBSL
	 */

	/* unit_declaration  ->	 ['unit' context_clause	 unit_body]*/
	case(as_unit):
		compunit(node);
		break;

	/* context_clause  -> ['with_use_list' [with_or_use...]]
	 * No action is necessary since this is handled in comp_unit
	 * body_stub	->  ['subprogam_stub' subprogram_specification]
	 *	       ->  ['package_stub'  name]
	 *	       ->  ['task_stub'	    name]
	 */

	case(as_subprogram_stub):
		{
			Symbol u_name;
			n1 = N_AST1(node);
			n2 = N_AST1(n1);
			u_name = dcl_get(DECLARED(scope_name), N_VAL(n2));
			/* For generic stubs ignore call to check_spec. 
			 * TBSL: code for checking formals.
			 * Note: if uname is undefined here it indicates that the stub had
			 * no subprog declaration and therefore is certainly not generic.
			 */
			if (u_name != (Symbol)0
			  && (NATURE(u_name) == na_generic_procedure_spec
			  || NATURE(u_name) == na_generic_function_spec)) {
				N_UNQ(n2) = u_name;
				newscope(u_name);
				adasem(n1);
				popscope();
				save_stub(node);
			}
			else {
				adasem(n1);
				check_spec(node);
				u_name = N_UNQ(n2);
				NATURE(u_name) = N_KIND(n1) == as_procedure ? na_procedure_spec
				  : na_function_spec;
				if (in_op_designators(ORIG_NAME(u_name) ) ){
					errmsg_l("Name of separately compiled unit cannot be ",
					  "an operator designator", "10.1", n2);
				}
				else {
					save_stub(node);
				}
			}
		}
		break;

	case(as_package_stub):
		stub_head(na_package, node);
		save_stub(node);
		break;

	case(as_task_stub):
		stub_head(na_task, node);
		save_stub(node);
		break;

	/* subunit  -> ['separate' parent_name unit]*/
	case(as_separate):
		adasem(N_AST2(node));
		break;

	/* Chapter 11. Exceptions*/

	/* Exception_declaration  ->  ['except_decl'  identifier_list]*/
	case(as_except_decl):
		except_decl(node);
		break;

	/* exceptions  -> ['exception' handler_list]*/
	case(as_exception):
		exception_part(node);
		break;

	/* exception_handler  ->  ['handler'  exception_choice_list statements]*/
	case(as_handler):
		exception_handler(node);
		break;

	case(as_others):
		break;

	/* raise_statement -> ['raise  opt_identifier]*/
	case(as_raise):
		raise_statement(node);
		break;

	/* Chapter 12. Generics*/
	case(as_generic_procedure):
	case(as_generic_function):
		generic_subprog_spec(node);
		break;

	case(as_generic_package):
		generic_pack_spec(node);
		break;

	/* Generic part	 ->  ['generic_formals' generic_decl_list]*/
	case(as_generic_formals):
		/*$$$newtypes with:= []; $ Anonymous types may be created (???)*/
		sem_list(node);
		/*$$$ generic_list := []+/sem_list(2);	 and new_type_list*/
		break;

	/* Generic_formal -> ['generic_obj' id_list mode name opt_expression]*/
	case(as_generic_obj):
		generic_obj_decl(node);
		break;

	/* Generic formal  -> ['generic_type' identifier type_def]*/
	case(as_generic_type):
		generic_type_decl(node);
		break;

	/* Generic formal  -> ['gen_priv_type'	private_type_declaration]*/
	case(as_gen_priv_type):
		generic_priv_decl(node);
		break;

	/* Generic_formal   ->	['generic_subp', subprogram_spec  opt_is]*/
	case(as_generic_subp):
		generic_subp_decl(node);
		break;

	/* Generic_type_definition  ->	['generic' identifier]*/
	case(as_generic):
		break;

	/* Package_instance -> ['package_instance' identifier name instance_list]*/
	case(as_package_instance):
		package_instance(node);
		break;

	/* subprogram_instance
	 *	->  ['function_instance'  designator  name  generic_actual_part]
	 *	->  ['procedure_instance' identifier  name  generic_actual_part]
	 */
	case(as_function_instance):
	case(as_procedure_instance):
		subprog_instance(node);
		break;

	/* generic_parameter_association->['instance' opt_identifier expression]*/
	case(as_instance):
		break;

	/* Chapter 13. Representation specs...*/

	/* length_clause -> ['length_clause' attribute simple_expression ]*/
	case(as_length_clause):
		length_clause (node);
		break;

	/*
	 * enumeration_representation_clause -> ['enum_rep_clause'
	 *					   simple_name aggregate ]
	 */
	case(as_enum_rep_clause):
		 enum_rep_clause (node); 
		break;

	/*
	 * record_representation_clause ->
	 *    ['rec_rep_clause' simple_name opt_align_clause comp_clause_list ]
	 */
	case(as_rec_rep_clause):
		rec_rep_clause(node);
		break;

	/* component_clause -> ['compon_clause' name simple_expression range]*/
	case(as_compon_clause):
		adasem(N_AST1(node));
		adasem(N_AST2(node));
		adasem(N_AST3(node));
		break;

	/* address_clause -> ['address_clause' simple_name simple_expression]*/
	case(as_address_clause):
		break;

	case(as_opt): 
		break;

	case(as_line_no):
		break;

	default:
		if (node == (Node)0) return;
		/* above is single line added re OPT_NODE  4 jul*/
		printf("adasem: invalid node %d kind %d\n", node, N_KIND(node));
		errmsg_str("System error: invalid node %", kind_str(N_KIND(node)),
		  "none", node);
	}
}

void sem_list(Node n)										/*;sem_list*/
{
	Fortup ft1;
	Node	ln;

	if (N_LIST(n) == (Tuple)0) return;
	FORTUP(ln = (Node), N_LIST(n), ft1);
		adasem(ln);
	ENDFORTUP(ft1);
}
