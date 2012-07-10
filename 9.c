/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#include "hdr.h"
#include "vars.h"
#include "setprots.h"
#include "errmsgprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "nodesprots.h"
#include "dclmapprots.h"
#include "chapprots.h"

void task_spec(Node task_node)								/*;task_spec*/
{
	Node	entries_node, id_node;
	int		anon;
	Symbol	task_type_name, t_name, old_kind, entry_sym;
	char	*id;
	Declaredmap	entry_list;
	Fordeclared fd1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  task_spec");

	id_node = N_AST1(task_node);
	entries_node = N_AST2(task_node);
#ifdef TBSN
	/* ignore opt_specs_node for now, as N_AST3 used for N_TYPE
	 * DS  9-22-86
	 */
	opt_specs_node = N_AST3(task_node);
#endif
	/*
	 * If this is a task declaration, an anonymous task type is introduced
	 * for it. Entry declarations are always attached to the task type.
	 * TBSL : processing of specifications.
	 */
	anon = (N_KIND(task_node) == as_task_spec);
	id = N_VAL(id_node);
	if (anon)
		task_type_name =
		   find_new(strjoin(strjoin("task_type:", id), newat_str()));
	else
		task_type_name = find_type_name(id_node);

	if (task_type_name == symbol_any) return; /* Illegal redeclaration. */

	if (anon) {
#ifdef TBSN
		XREF lessf:= task_type_name;
#endif
	}
	old_kind = TYPE_OF(task_type_name); /* may have been private */

	NATURE(task_type_name) = na_task_type_spec;
	TYPE_OF(task_type_name) = task_type_name;
	SIGNATURE(task_type_name) = tup_new(0);  /* created by the expander */
	root_type(task_type_name) = task_type_name;
	initialize_representation_info(task_type_name, TAG_TASK);
	/* priv_types is {private, limited_private}; first arg to check_priv_decl
	 * is one of MISC_TYPE_ATTRIBUTES ...
	 */
	if (old_kind == symbol_private)
		check_priv_decl(TA_PRIVATE, task_type_name);
	else if (old_kind == symbol_limited_private)
		check_priv_decl(TA_LIMITED_PRIVATE, task_type_name);
	if (anon) {
		t_name = find_new(id);
		NATURE(t_name) = na_task_obj_spec;
		TYPE_OF(t_name) = task_type_name;
		SIGNATURE(t_name) = (Tuple) 0;
		N_UNQ(task_node) = t_name;
	}

	N_TYPE(task_node) = task_type_name;
	newscope(task_type_name);	/* introduce new scope */
#ifdef TBSN
	prefix := prefix + id + '.';			$ For unique names.
#endif
	    sem_list(entries_node);
#ifdef TBSN
	/* ignore opt_specs_node for now, as N_AST3 used for N_TYPE
	 * DS  9-22-86
	 */
	sem_list(opt_specs_node);
#endif

	entry_list = DECLARED(scope_name);
	popscope();

	if (anon) {
		/* Attach entry declarations for task object as well, and emit a
		 * declaration for the task object itself.
		 */
		SIGNATURE(t_name) = (Tuple) 0;
		DECLARED(t_name) = entry_list;

		FORDECLARED(id, entry_sym, entry_list, fd1)
		    /*(for entry = entry_list(id))*/
			SCOPE_OF(entry_sym) = t_name;
		ENDFORDECLARED(fd1)
	}
	return;
}

void accept_statement(Node accept_node)					/*;accept_statement*/
{

	/* This procedure opens a new scope when an ACCEPT statement is seen.
	 * In the case of an overloaded entry name, it selects the one with
	 * the matching signature.
	 */

	int		certain;
	Symbol	task_name, task_type, real_name, entry_name, ix_t;
	Set		entries;
	Tuple	formals;
	Forset	fs1;
	Node	id_node, indx, body_node;
	Node	formals_node;
	int		exists, nat;
	char	*id, *junk;
	Fortup	ft1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : accept_statement");

	id_node = N_AST1(accept_node);
	indx = N_AST2(accept_node);
	formals_node = N_AST3(accept_node);
	body_node = N_AST4(accept_node);

	id = N_VAL(id_node);
	formals = get_formals(formals_node, id);
	/* Find the task  in which the accept statement occurs. The accept
	 * may of course appear within a block or another accept statement.
	 */

	exists	= FALSE;
	FORTUP(task_name = (Symbol), open_scopes, ft1);
		nat = NATURE(task_name);
		if( nat != na_block && nat != na_entry && nat != na_entry_family) {
			exists = TRUE;
			break;
		}
	ENDFORTUP(ft1);
	certain = exists;
	task_type = TYPE_OF(task_name);

	if (task_type == (Symbol)0 || NATURE(task_type) != na_task_type)  {
		errmsg("Accept statements can only appear in tasks","9.5", accept_node);
		/* following junk line in SETL not needed here	ds 1 nov 84
		 * entry_name = id;
		 */
		return;
	}

	real_name = entry_name = dcl_get(DECLARED(task_name), id);

	if (entry_name == (Symbol)0) {
		errmsg("Undefined entry name in ACCEPT ", "9.5", id_node);
#ifdef TBSL
		-- entry_name is symbol, id is string		ds 2-jan-85
		    entry_name = id; /* For dummy scope. */
#endif
		return; /* to Initialize it . */
	}
	else if (NATURE(entry_name) == na_entry) {
		/* Collect all its overloadings and select the one with the
		 * correct signature.
		 */
		entries = OVERLOADS(entry_name);

		if (indx != OPT_NODE) {
			errmsg("invalid index on entry (not entry family)", "9.5", indx);
		}

		exists = FALSE;
		FORSET(entry_name = (Symbol), entries, fs1);
			if (same_sig_spec(entry_name, formals)) {
				exists = TRUE;
				break;
			}
		ENDFORSET(fs1);
		if (!exists) {
			errmsg("Entry name in ACCEPT statement does not match any entry" ,
			  "9.5", id_node);
			return;
		}
	}
	else if (NATURE(entry_name) == na_entry_family) {
		ix_t = (Symbol) index_type(TYPE_OF(entry_name));

		if (indx == OPT_NODE) {
			errmsg("Missing index for entry family.", "9.5", accept_node);
		}
		else {
			adasem(indx);
			check_type(ix_t, indx);
		}	
	}
	else {
		errmsg("Invalid entry name in ACCEPT", "9.5", id_node);
		return;
	}

	N_UNQ(id_node) = entry_name;
	TO_XREF(entry_name);

	reprocess_formals(entry_name, formals_node);
	if (in_open_scopes(entry_name )) {
		errmsg_l("An accept_statement cannot appear within an ACCEPT for",
		  " the same entry", "9.5", accept_node);
	}
	newscope(entry_name);
	has_return_stk = tup_with(has_return_stk, (char *)FALSE);
	adasem(body_node);
	junk = tup_frome(has_return_stk);
	popscope();
}

void entry_decl(Node entry_node)							/*;entry_decl*/
{
	/* An entry declaration is treated like a procedure specification.
	 * An anonymous type is created for the entry object. This type is
	 * used by the interpreter to build the environment of an entry.
	 */

	Symbol	entry_sym, entry_type;
	Node	id_node, formal_list;
	Tuple	formals;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  entry_decl");

	id_node = N_AST1(entry_node);
	formal_list = N_AST2(entry_node);

	formals = get_formals(formal_list, N_VAL(id_node));

	check_out_parameters(formals);

	/*entry = chain_overloads(N_VAL(id_node), [na_entry, 'none', formals]); */
	entry_sym = chain_overloads(N_VAL(id_node), na_entry, symbol_none,
	  formals, (Symbol)0, formal_list);

	entry_type = anonymous_type();

	/*SYMBTAB(entry_type) := [na_entry_former, scope_name, signature(entry)]; */
	NATURE(entry_type) = na_entry_former;
	TYPE_OF(entry_type) = scope_name;
	SIGNATURE(entry_type) = SIGNATURE(entry_sym);
	root_type(entry_type) = entry_type;

	N_UNQ(id_node)	= entry_sym;
	N_TYPE(entry_node) = entry_type;
}

void entry_family_decl(Node entry_node)					/*;entry_family_decl*/
{
	/* An entry family  is not  an overloadable  object. It	 is  constructed
	 * as an array of entries. An anonymous type is introduced for the entry
	 * former, just	 as for an  entry declaration, and another is introduced
	 * for the array representing the family.
	 */

	Symbol	entry_sym, entry_type, family_type;
	Symbol	opt_range;
	Tuple	formals, f, tup;
	Node	id_node, discrete_range, formal_list;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : entry_family_decl");

	id_node = N_AST1(entry_node);
	discrete_range = N_AST2(entry_node);
	formal_list = N_AST3(entry_node);

	entry_sym = find_new(N_VAL(id_node));

	formals = get_formals(formal_list, N_VAL(id_node));

	check_out_parameters(formals);

	f = process_formals(entry_sym, formals, TRUE);

	entry_type = anonymous_type();

	NATURE(entry_type) = na_entry_former;
	TYPE_OF(entry_type) = scope_name;
	SIGNATURE(entry_type) = f;
	root_type(entry_type) = entry_type;
	adasem(discrete_range);
	opt_range = make_index(discrete_range);
	family_type = anonymous_type();
	/* SYMBTAB(family_type) =
	 *	    [na_array, family_type, [[opt_range], entry_type]];
	 */
	NATURE(family_type) = na_array;
	TYPE_OF(family_type) = family_type;
	tup = tup_new(2);
	tup[1] = (char *) tup_new1((char *) opt_range);
	tup[2] = (char *) entry_type;
	SIGNATURE(family_type) = (Tuple) tup;
	root_type(family_type) = family_type;

	/* SYMBTAB(entry) = [na_entry_family, family_type, f]; */
	NATURE(entry_sym) = na_entry_family;
	TYPE_OF(entry_sym) = family_type;
	SIGNATURE(entry_sym) = f;
	formal_decl_tree(entry_sym) = (Symbol) formal_list;
	N_UNQ(id_node) = entry_sym;
	N_TYPE(entry_node) = family_type;
}

void entry_call(Node node)									/*;entry_call*/
{
	/* process an entry call. obj_node below is the entry name: either a se-
	 * lected or an indexed expression.
	 */

	Symbol	range_typ, entry_sym;
	Node	obj_node, arg_list_node;
	Tuple	arg_list;
	Node	task_node, index_node, entry_node;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  entry_call");

	obj_node = N_AST1(node);
	arg_list_node = N_AST2(node);

	arg_list = N_LIST(arg_list_node);

	find_entry_name(obj_node); /* Normalize entry name*/
	task_node = N_AST1(obj_node);
	entry_node = N_AST2(obj_node);

	if (entry_node == OPT_NODE) return;	/* previous error. */

	if (N_KIND(obj_node) == as_entry_family_name) {
		entry_sym = N_UNQ(entry_node);
		range_typ = (Symbol) index_type(TYPE_OF(entry_sym));
		index_node = N_AST3(obj_node);

		if (index_node == OPT_NODE) {
			/* Case of a call to a parameterless family. The formals list
			 * is actually the index expression. Verify its size.
			 */
			if (tup_size(arg_list) != 1) {
				errmsg("Call to member of entry family requires one index",
				  "9.5, 3.6.1", obj_node);
				return;
			}
			else {
				index_node = (Node) arg_list[1];
				N_AST3(obj_node) = index_node;

				arg_list_node = node_new(as_list);
				N_LIST(arg_list_node) = tup_new(0);

				N_AST2(node) = arg_list_node;
			}
		}

		check_type(range_typ, index_node);

		/* process as usual call.*/
		N_NAMES(obj_node) = set_new1((char *) entry_sym);
		check_type(TYPE_OF(entry_sym), node);
		N_AST3(obj_node) = index_node;     /* restore index */
		N_KIND(obj_node) = as_entry_name;  /* common processing after this */
	}
	else {	/* Simple entry.*/
		check_type(symbol_none, node);	/* as for a procedure call */
		entry_sym = N_UNQ(entry_node);
		N_AST3(obj_node) = OPT_NODE;      /* discard  N_NAMES  */
	}
	/*  Having resolved the call, use the unique entry name to complete the
	 *  resolution of the task name itself.
	 */
	if (entry_sym != (Symbol)0)
		complete_task_name(task_node, TYPE_OF(SCOPE_OF(entry_sym)));

	return;
}

void check_entry_call(Node stat_node)					/*;check_entry_call*/
{
	/* Verify that the call in a timed entry call or a conditional entry call
	 * is indeed a call to an entry, and not to a procedure.
	 */

	adasem(stat_node);

	if (N_KIND(stat_node) == as_call) {
		errmsg("context requires entry name ", "9.7.2, 7.3", stat_node);
	}
}

void find_entry_name(Node obj_node)						/*;find_entry_name*/
{
	/* Find the name of an entry or entry family, given by a qualified and
	 * (in the case of a family) indexed expression. This differs from other
	 * cases of name resolution in that the name of the task containing the
	 * entry can be given by an expression that must also be resolved.
	 * This procedure is also called to validate the argument of the COUNT
	 * attribute; this attribute can only be used within the task body, in
	 * which the entry need not be named as a selected component. An entry
	 * name will then be seen as an overloaded identifier. The task name is
	 * the scope of the entry.
	 * An entry family name is built as a triple [task_node, entry_node, index]
	 * An entry name is built as a pair [task_node, entry_name]. In addition,
	 * the N_NAMES field is defined in the case of entries, which can be over-
	 * loaded.
	 */

	Node	index_list_node, task_node, entry_node, index_node;
	Tuple	index_list;
	Symbol	obj, task_name, t, e, sym;
	Set		entries, task_types, entry_names;
	Forset	fs1, fs2;
	char	*entry_id;
	int exists, is_family;

	if (cdebug2 > 3 ) TO_ERRFILE("AT PROC :  find_entry_name");

	if (N_KIND(obj_node) == as_simple_name) {
		if (N_OVERLOADED(obj_node) ) {
			entries = N_NAMES(obj_node);
			task_name = SCOPE_OF((Symbol)set_arb( entries));

			if (!is_task_type(TYPE_OF(task_name))) {
				errmsg("Invalid entry name", "9.5", obj_node);
				entry_node = OPT_NODE;
			}
			else {
				entry_node = copy_node(obj_node);
			}

			task_node = node_new(as_simple_name);
			N_UNQ(task_node) = task_name;
			N_VAL(task_node) = (char *) original_name(task_name);
			copy_span(obj_node, task_node);

			index_node = OPT_NODE;
		}
		else if (NATURE((obj = N_UNQ(obj_node))) == na_entry_family) {
			/* Member of entry family, with index missing. */
			errmsg("Missing index in name of member of entry family",
			  "9.5", obj_node);
			entry_node = OPT_NODE;
		}
	}
	else if (N_KIND(obj_node) == as_selector) { /* selected_component*/
		task_node = N_AST1(obj_node);
		entry_node = N_AST2(obj_node);
		index_node = OPT_NODE;
	}
	else {	/* case of entry family. */
		entry_node = N_AST1(obj_node);
		index_list_node = N_AST2(obj_node);

		if (N_KIND(entry_node) == as_simple_name) {
			/* Entry family named in task body. Get enclosing task name.*/

			task_node = node_new(as_simple_name);
			task_name = SCOPE_OF(N_UNQ(entry_node));
			N_UNQ(task_node) = task_name;
			N_VAL(task_node) = (char *) original_name(task_name);
			copy_span(obj_node, task_node);
		}
		else {/* Name is selected component. */
			task_node = N_AST1(entry_node);
			entry_node = N_AST2(entry_node);
		}

		index_list = N_LIST(index_list_node);
		if (tup_size(index_list) != 1) {
			errmsg("Member of entry family requires a single index ",
			  "9.5, 3.6.1", obj_node);
			entry_node = OPT_NODE;
		}
		index_node = (Node) index_list[1];/* In any case. */
	}

	if (entry_node != OPT_NODE) {		/* no previous error*/
		valid_task_name(task_node);
		task_types = N_PTYPES(task_node);
		if (set_size(task_types) == 0)		/* prefix is not a task*/
			entry_node = OPT_NODE;
	}
	else {
		task_node = OPT_NODE;
		task_types = set_new(0);
	}

	entry_names = set_new(0);
	entry_id = (char *) N_VAL(entry_node);
	is_family = FALSE;

	FORSET(t = (Symbol), task_types, fs1);
		if (is_access(t)) t = (Symbol) designated_type(t);

		e = dcl_get(DECLARED(t), entry_id);
		if (e != (Symbol)0) {
			if (NATURE(e) == na_entry) {
				FORSET(sym = (Symbol), OVERLOADS(e), fs2);
					entry_names = set_with(entry_names, (char *) sym);
				ENDFORSET(fs2);
			}
			else {	/* name of entry family*/
				entry_names = set_with(entry_names, (char *) e);
				is_family = TRUE;
			}
		}
	ENDFORSET(fs1);

	if (set_size(entry_names) == 0 && entry_node != OPT_NODE ) {
		errmsg("Undefined entry name in task : ", "9.5", obj_node);
		entry_node = OPT_NODE;
	}
	else {
		exists = FALSE;
		if (set_size(entry_names) > 1 ) {
			exists = FALSE;
			FORSET(e = (Symbol), entry_names, fs2);
				if (NATURE(e) == na_entry_family ) {
					exists = TRUE;
					break;
				}
			ENDFORSET(fs2);
		}
		if (exists) {
			errmsg_id("ambiguous entry family name: %", e , "9.5", obj_node);
			/* entry is undefined, this is a guess (gs sep 20) */
			entry_node = OPT_NODE;
		}
		else if (entry_node != OPT_NODE) {
			if (is_family) {
				N_KIND(obj_node)  = as_entry_family_name;
				N_UNQ(entry_node) = (Symbol)set_arb(entry_names);
				N_AST3(obj_node)  = index_node;
			}
			else {
				N_KIND(obj_node)  = as_entry_name;
				N_NAMES(obj_node) = entry_names;
				if (index_node != OPT_NODE ) {
					errmsg_id("invalid index. % is not an entry family", 
					    (Symbol) set_arb(entry_names), "9.5", obj_node);
				}

			}
		}
	}
	N_AST1(obj_node) = task_node;
	N_AST2(obj_node) = entry_node;
}

void terminate_statement(Node node)					/*;terminate_statement*/
{
	/* A terminate alternative is annotated with the nesting level of the
	 * statement, to simplify the retrieval of the task environment.
	 */

	int	certain, exists, i, out_depth, j, blktyp;
	Fortup	ft1;
	Symbol	scope;

	exists = TRUE;
	FORTUPI(scope = (Symbol), open_scopes, i, ft1);
		if (NATURE(scope) == na_task_obj || NATURE(scope) == na_task_type) {
			exists = TRUE;
			break;
		}
	ENDFORTUP(ft1);
	certain = exists;
	if (!certain) {
		errmsg("Invalid context for TERMINATE alternative", "9.7.1", node);
		i = 1;
	}
	/* Loops and handlers are scopes for syntactic purposes, but not at run-
	 * time. Remove them from depth count.
	 */
	out_depth = i - 1;
	for (j = i; j > 0; j--) {
		scope = (Symbol) open_scopes[j];
		blktyp = (int) OVERLOADS(scope);
		if (blktyp == BLOCK_LOOP || blktyp == BLOCK_HANDLER)
			out_depth -= 1;
	}
	N_VAL(node) = (char *) out_depth;
}

void abort_statement(Node node)							/*;abort_statement*/
{
	Node	name_node;
	Fortup	ft1;
	Symbol	task_obj;
	Set	task_types;
	Symbol	t;

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC :  abort_statement");

	FORTUP(name_node = (Node), N_LIST(node), ft1);
		adasem(name_node);
		find_old(name_node);
		valid_task_name(name_node);
		task_types = N_PTYPES(name_node);

		if (set_size(task_types) == 0)		/* Previous error*/
			continue;
		else if (!is_task_type( (t = (Symbol)set_arb (task_types), t) ) ) {
			/* Access type not valid here.*/
			errmsg(" expect task name is ABORT statement", "9.10", name_node);
			continue;
		}
		else
			resolve2(name_node, t);

		if (N_KIND(name_node) == as_simple_name
		  && NATURE(task_obj = N_UNQ(name_node)) == na_task_type ) {
		/* This is a reference to the task currently executing the body.
		 * replace the name of the task type by its run-time identity.
		 */
			if (in_open_scopes(task_obj))
				N_UNQ(name_node) = dcl_get(DECLARED(task_obj), "current_task");
			else {
				errmsg("Invalid task type in ABORT statement", "9.10",
				  name_node);
			}
		}
	ENDFORTUP(ft1);
}
