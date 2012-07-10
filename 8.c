/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#ifndef SEM
#define SEM	1
#endif

#include "hdr.h"
#include "vars.h"
#include "attr.h"
#include "dclmapprots.h"
#include "errmsgprots.h"
#include "sspansprots.h"
#include "nodesprots.h"
#include "setprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "chapprots.h"

/*
 CHECK HANDLING OF NEW_NAME in newmod	ds 30 jul
 Sort out is_identifier usage		ds 26 nov 84
 Bring C version of find_simple_name in closer correspondence to SETL
 version.	ds 7 aug 84

 Note that set imported in collect_imported names is built on every call.
 It is probably dead on return, but I am not copying it when I put in
 in all_imported_names. May be able to do set_free(imported) before
 return from collect_imported_names - look into this later.  ds 2 aug
*/

/*
 * The following global variable is used for error reporting when
 * several instances of an identifier end up hiding each other and
 * the identifier is seen as undeclared or ambiguous.
 */
static Set all_imported_names; /*TBSL: initialize to (Set)0 */


static Set collect_imported_names(char *);
static void name_error(Node);
static void find_simple_name(Node);
static void array_or_call(Node);
static int parameterless_callable(Symbol);
static void index_or_slice(Node);
static void find_selected_comp(Node);
static void find_exp_name(Node, Symbol, char *);
static void all_declarations(Node, Symbol, char *, Symbol);
static int has_implicit_operator(Node, Symbol, char *);
static void make_any_id_node(Node);
static int is_appropriate_for_record(Symbol);
static int is_appropriate_for_task(Symbol);
static Symbol renamed(Node, Tuple, Symbol);
static Symbol op_matches_spec(Symbol, Tuple, Symbol);
static void check_modes(Tuple, Symbol);
static void renamed_entry(Node, Tuple);

void find_old(Node id_node)									/*;find_old*/
{
	/*
	 * Establish unique name of identifier, or of syntactic category name.
	 * Yield error in the case of undefined identifier.
	 * In the case of long and short integers, indicate that they are
	 * unimplemented rather than 'undefined'.
	 */
	Symbol	u_name;
	char	*id;
	char	*newn;
	int		unsupported;

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC :  find_old");

	check_old(id_node);
	if (N_KIND(id_node) != as_simple_name) return; /* added 7 jul */
	u_name = N_OVERLOADED(id_node) ? (Symbol) 0 : N_UNQ(id_node);
	id = N_VAL(id_node);
	if (u_name == symbol_undef) {
		if (streq(id, "LONG_INTEGER") || streq(id, "SHORT_INTEGER")) {
			unsupported = TRUE;
			u_name = symbol_integer; /* new type to use */
		}
		else if (streq(id, "SHORT_FLOAT") || streq(id, "LONG_FLOAT")) {
			unsupported = TRUE;
			u_name = symbol_float; /* new type to use */
		}
		else {
			unsupported = FALSE;
		}

		if (!unsupported) {
			/* The identifier is undefined, or not visible. This is an error.*/
			name_error(id_node);
		}
		else {
			/* The identifier names unsupported type. This is error, so
			 * issue error message and then change type to avoid further
			 * spurious error messages
			 */
			errmsg_str("% is not supported in current implementation",
			  id, "none", id_node);
			N_UNQ(id_node) = u_name;
			return;
		}
		/* insert in current scope, and give it default type.*/
		if (dcl_get(DECLARED(scope_name), id) == (Symbol)0
		  && set_size(all_imported_names) == 0) {
			newn = id;
			u_name = find_new(newn);
			NATURE(u_name)	= na_obj; /* Could be more precise.*/
			N_UNQ(id_node) = u_name;
		}
		TYPE_OF(u_name) = symbol_any;
		ALIAS(u_name) = symbol_any;
	}
}

Symbol find_type(Node node) /*;find_type*/
{
	Symbol	type_mark;

	/* Resolve a name that must yield a type mark.*/
	find_old(node);
	type_mark = N_UNQ(node);
	if (N_OVERLOADED(node) || type_mark == (Symbol)0
	  || !is_type(type_mark) && TYPE_OF(type_mark) != symbol_any) {
		errmsg("Invalid type mark ", "none", node);
		N_UNQ(node) = type_mark = symbol_any;
	}
	return type_mark;
}

static void name_error(Node id_node)  /*;name_error*/
{

	char	*id;
	char	*names;

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC :  name_error");
	/*
	 * Name was not found in environment. This may be because it is undeclared,
	 * or because several imported instances of the name hide each other.
	 * The marker '?' is also returned when a type name is mentioned in
	 * the middle of its own elaboration.
	 */
	id = N_VAL(id_node);
	if (set_size(all_imported_names) == 0) {
		if (dcl_get(DECLARED(scope_name), id) == (Symbol)0) {
			errmsg_str("identifier undeclared or not visible %", id, "3.1", id_node);
		}
		else {
			errmsg_str("Invalid reference to %", id , "3.3", id_node);
		}
	}
	else {
#ifdef TBSL
		names = +/[ original_name(scope_of(x)) + '.' + original_name(x)
			+ ' ':	x in all_imported_names ];
#endif
		names = build_full_names(all_imported_names);
		errmsg_str("Ambiguous identifier. Could be one of: %",
		  names, "8.3, 8.4", id_node);
	}
}

void check_old(Node n_node)  /*;check_old*/
{
	Node	node, attr, arg1, expn;
	int	nk;

	if (cdebug2 > 3) {
		TO_ERRFILE("AT PROC :  check_old");
		printf("  kind %s\n", kind_str(N_KIND(n_node))); /*DEBUG*/
	}
	/*
	 * This procedure performs name resolution for several syntactic
	 * instances of names. These include identifiers, selected components,
	 * array indexing and slicing, function calls and attribute expressions.
	 * If -name- is an identifier and is undeclared, this proc yields
	 * the special marker '?' which is used by error routines.
	 * If -name- is overloaded, the procedure returns the set of overloaded
	 * names which correspond to -name-. This set is constructed by
	 * scanning first the open scopes, and then examining visible packages.
	 * To facilitate the collection of overloaded names, the procedure
	 * chain_overload, which is called when a procedure specification, or
	 * and enumeration type are processed, collects successive overloads of the
	 * same id together, using the -overloads- field of the symbol table.
	 */

	switch (nk = N_KIND(n_node)) {
	  case	as_simple_name:
	  case	as_character_literal:
	  case	as_package_stub:
	  case	as_task_stub:
				find_simple_name(n_node);
				break;
	  case	as_call_unresolved:
				array_or_call(n_node);
				break;
	  case	as_selector:
				find_selected_comp(n_node);
				break;
	  case	as_string:
				N_KIND(n_node) = as_simple_name; /* Treat as simple*/
				find_simple_name(n_node);		    /* name.*/
				break;
	  case	as_name:
	  case	as_range_expression:
				node = N_AST1(n_node);
				find_old(node);
				copy_attributes(node, n_node);
				break;
	  case	as_attribute:
				attr = N_AST1(n_node);
				arg1 = N_AST2(n_node);
				find_old(arg1);
				break;
	  case	as_all:
				expn = N_AST1(n_node);
				find_old(expn);
				break;
	}
}

static void find_simple_name(Node n_node)		/*;find_simple_name*/
{
	char	*id;
	Symbol	sc;
	int		sc_num;
	Symbol	u_name, o, n, u_n;
	Symbol	found, foreign;
	Set		names, names_add, found_set;
	Set imported;
	int		i, exists, found_is_set;
	Forset	fs1, fs2;
	Symbol	sym;

	id = N_VAL(n_node);

	if (cdebug2 > 0) {
		TO_ERRFILE(" looking for id. " );
		printf("  kind %s %s\n", kind_str(N_KIND(n_node)), id); /*DEBUG*/
	}

	exists = FALSE;
	for (sc_num = 1; sc_num <= tup_size(open_scopes); sc_num++) {
		sc = (Symbol)open_scopes[sc_num];
		u_name = dcl_get(DECLARED(sc), id);
		if	 (u_name != (Symbol)0) {
			exists = TRUE;
			break;
		}
	}
	if (exists) {
		if (!can_overload(u_name)) {
			found_is_set = FALSE;
			found = u_name;
			TO_XREF(u_name);
		}
		else {
			names = set_copy(OVERLOADS(u_name));

			/* Scan open scopes for further overloadings.*/
			for (i = sc_num+1; i <= tup_size(open_scopes); i++) {
				u_n = dcl_get(DECLARED(((Symbol)open_scopes[i])), id);
				if (u_n == (Symbol)0) continue;
				else if (!can_overload(u_n)) {
					found_is_set = TRUE;
					found_set = names;
				}
				else {
					names_add = set_new(0);
					FORSET(o=(Symbol), OVERLOADS(u_n), fs1);
						exists = FALSE;
						FORSET(n=(Symbol), names, fs2);
							if (same_type(TYPE_OF(n), TYPE_OF(o)) &&
							  same_signature(n, o)) {
								exists = TRUE;
								break;
							}
						ENDFORSET(fs2);
						if (!exists) names_add = set_with(names_add, (char *)o);
					ENDFORSET(fs1);
					FORSET(o=(Symbol), names_add, fs1);
						names = set_with(names, (char *)o);
					ENDFORSET(fs1);
					set_free(names_add);
				}
			}
			imported = collect_imported_names(id);
			/* Keep only the imported names which are not hidden
			 * by visible names with the same signature.
			 */
			if (set_size(imported)>1 ||
			  (set_size(imported) == 1 &&
			  can_overload((Symbol)set_arb(imported)))) {
				names_add = set_new(0);
				FORSET(foreign=(Symbol), imported, fs1);
					exists = FALSE;
					FORSET(n=(Symbol), names, fs2);
						if (same_type(TYPE_OF(n), TYPE_OF(foreign)) &&
				    		same_signature(n, foreign)) {
							exists = TRUE;
							break;
						}
						ENDFORSET(fs2);
					if (!exists)
						names_add = set_with(names_add, (char *)foreign);
				ENDFORSET(fs1);
				FORSET(n=(Symbol), names_add, fs1);
					names = set_with(names, (char *) n);
				ENDFORSET(fs1);
				set_free(names_add);
			}
			found_is_set = TRUE;
			found_set = names;
		}
	}
	else if ((imported = collect_imported_names(id) , set_size(imported)) != 0){
		if (set_size(imported)>1 || can_overload((Symbol)set_arb(imported))) {
			found_is_set = TRUE;
			found_set = imported;
		}
		else {
			found_is_set = FALSE;
			found = (Symbol) set_arb(imported);
		}
	}
	/* the syntactic error recovery routine sends a '' when it can
	 * recover by token insertion. return it as is, to avoid
	 * subsequent spurious messages.
	 */
	/* #if DEAD */
	/* DEAD (as best we can tell  7 jul */
	else if (streq(id, "any_id")) {
		found_is_set = FALSE;
		found = symbol_any_id;
	}
#ifdef DEAD
	else if (id == (Symbol)0) {
		found_is_set = FALSE;
		found = id;
	}
#endif
	else {
		found_is_set = FALSE;
		found = symbol_undef; /* need to add symbol_undef '?' */
	}
	if (found_is_set) {
		N_OVERLOADED(n_node) = TRUE;
		N_NAMES(n_node) = found_set;
	}
	else {
		N_OVERLOADED(n_node) = FALSE;
		N_UNQ(n_node) = found;
	}
	if (cdebug2 == 0) return; /* rest is debugging trace only*/

	if (cdebug2 > 0) TO_ERRFILE ("found name(s): " );
/* always print found names */
	if (found_is_set) {
		FORSET(sym=(Symbol), found_set, fs1)
#ifdef IBM_PC
	    	printf("%p", sym);
#else
		printf("%ld", sym);
#endif
		if (sym!=(Symbol)0) printf("%s", ORIG_NAME(sym));
		printf("\n");
		ENDFORSET(fs1);
	}
	else {
#ifdef IBM_PC
		printf("found name %p  ", found);
#else
		printf("found name %ld  ", found);
#endif
		/* symbol_undef should not need special handling  ds 17 jul
		if (found == symbol_undef) printf("?\n");
		else
 */
		if (found!=(Symbol)0) printf("%s\n", ORIG_NAME(found));
	}
}

static Set collect_imported_names(char *id)		/*;collect_imported_names*/
{
	Set imported;
	Symbol	used;
	Symbol	s;
	Symbol	foreign;
	Fortup	ft1;
	Forset	fs1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  collect_imported_names");
	/*
	 * This procedure collects the set of all imported names corresponding
	 * to identifier -name-, which appear in currently visible package.
	 * An imported identifier is visible if :
	 * a) It is not an overloadable identifier, and it appears in only
	 * one used package.
	 * b) Or, all of its appearances in used modules are overloadable.
	 */
	imported = set_new(0);
	/*
	 * (forall used in used_mods | (f:= visible(used)) /= om
	 * 				and (foreign := f(id)) /= om )
	 */
	FORTUP(used=(Symbol), used_mods, ft1);
		if (DECLARED(used) == (Declaredmap)0) continue;
		foreign = dcl_get_vis(DECLARED(used), id);
		if (foreign !=(Symbol)0) {
			if (can_overload(foreign)){
				FORSET(s=(Symbol), OVERLOADS(foreign), fs1);
					imported = set_with(imported, (char *)s);
				ENDFORSET(fs1);
			}
			else {
				if (set_size(imported) != 0) {
					/* mutual hiding. Save all for error message.*/
					/* imported dead - no need to copy	ds 2 aug */
					all_imported_names = imported;
					all_imported_names = set_with(all_imported_names,
				  	(char *) foreign);
					return set_new(0);
				}
				else {
					imported = set_new1((char *) foreign);
				}
			}
		}
	ENDFORTUP(ft1);

	if (cdebug2 > 1) TO_ERRFILE("Imported names:");

	/* Save imported names in global variable, for possible error message.*/
	all_imported_names = imported;
	return imported;
#ifdef TBSL
	-- this code seems to be dead  review this with Ed  ds	12-dec-84
	    exists = FALSE;
	FORSET(fgn=(Symbol), imported, fs1);
		if (!can_overload(fgn)) {
			exists = TRUE;
			break;
		}
	ENDFORSET(fs1);
	if (exists) {
		/* If it is the only name found, return it.*/
		if (set_size(imported) == 1) {
			/*set_free(imported);*/
			return set_new1(fgn);
		}
		else {
			/*set_free(imported);*/
			return set_new(0);
			/* various visible names hide each other.*/
		}
	}
	else {
		/* All occurrences are overloadable. Return only those which do*/
		if (cdebug2 > 1) {
			TO_ERRFILE("Names:");
			return imported;
		}
	}
#endif
}

static void array_or_call(Node n_node)	/*;array_or_call*/
{
	/*
	 * This procedure resolves the construct
	 *	name aggregate
	 * The meaning of this construct is one of the following :
	 * a) Indexed expression or slice.
	 * b) function call.
	 * d) Conversion.
	 */

	Node	prefix_node, agg_node, call_node, index_node, p_node;
	Tuple	arg_list;
	Set		f_names, npfs;
	Symbol	f, t;
	Forset	fs1;

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC :  array_or_call");

	prefix_node = N_AST1(n_node);
	agg_node = N_AST2(n_node);
	arg_list = N_LIST(agg_node);

	/* Find unique name of object (procedure, array, etc).*/
	find_old(prefix_node);
	/*  Need different error flag. */
	if (N_UNQ(prefix_node) == (Symbol)symbol_undef)
		/* error message emitted already by find_old.*/
		return;

	if (N_OVERLOADED(prefix_node)) {
		f_names = N_NAMES(prefix_node);
		/* function call.*/
		N_KIND(n_node) = as_call;
		/* The  nature of at least one  of the  overloaded instances	 must be
		 * callable.	 This  is  checked  by the type resolution  routines. An
		 * unpleasant syntactic ambiguity appears if parameterless  functions
		 * that  return an  array type appear  in obj_name. In this	case the
		 * expression must  be reformatted  as an indexing on the result of a
		 * function	call. If  both parameterless  and  parametered functions
		 * are present, then the  tree itself is ambiguous, and both parsings
		 * must be carried, to be resolved by the type resolution routines.
		 */
		npfs = set_new(0);
		FORSET(f=(Symbol), f_names, fs1);
			t = TYPE_OF(f);
			if (parameterless_callable(f) && (is_array(t)
		      || is_access(t) && is_array((Symbol)designated_type(t))))
				npfs = set_with(npfs, (char *)f);
		ENDFORSET(fs1);
		if (set_size(npfs) != 0) {
			index_or_slice(n_node);

			if (N_KIND(n_node) == as_slice) {
				/* no ambiguity: it must be a slice.*/
				; }
			else {
				/* Construct subtrees with both parsings.*/
				call_node  = copy_node(n_node);
				N_KIND(call_node) = as_call;
				index_node = copy_tree(n_node);
				p_node = N_AST1(index_node);
				N_NAMES(p_node) = npfs;
				N_OVERLOADED(p_node)= TRUE;

				N_KIND(n_node) = as_call_or_index;
				N_AST1(n_node)  = call_node;
				N_AST2(n_node)  = index_node;
			}
		}
	}
	else if (is_type(N_UNQ(prefix_node))) {
		/* Case of a conversion.*/
		N_KIND(n_node) = as_convert;
		if (tup_size(arg_list) == 1) {
			/* Conversion of a single expression. $$$ What about a choice?*/
			N_AST1(n_node) = prefix_node;
			N_AST2(n_node) = (Node)arg_list[1];
		}
		else {
			/* Conversion of an aggregate: label it as such.*/
			N_KIND(agg_node) = as_aggregate;
		}
	}
	else{
		index_or_slice(n_node);
	}
}

static int parameterless_callable(Symbol f)   /*;parameterless_callable*/
{
	/*
	 * Assert  that f is  a parameterless function, or  that default values
	 * exist for all its parameters and it can be called without arguments.
	 */

	Symbol	formal;
	Fortup	ft1;

	if (NATURE(f) !=na_function && NATURE(f)!=na_function_spec)
		return FALSE;
	FORTUP(formal=(Symbol), SIGNATURE(f), ft1);
		if ((Node)default_expr(formal) == OPT_NODE ) return FALSE;
	ENDFORTUP(ft1);
	return TRUE;
}

static void index_or_slice(Node n_node)	 /*;index_or_slice*/
{
	/*
	 * A slice is not always recognizable syntactically from an
	 * indexing expression. v(arg) is a slice in 3 cases:
	 * a) arg is a range : L..R
	 * b) arg is of the form V'RANGE
	 * c) arg is a type mark, possibly with a range constraint.
	 */
	Node	prefix_node, index_node, constraint;
	Tuple	index_list;
	int		index_kind;
	Node	index;

	prefix_node = N_AST1(n_node);
	index_node = N_AST2(n_node);
	index_list = N_LIST(index_node);
	N_KIND(n_node) = as_index; /* most likely. */

	if (tup_size(index_list) == 1) {
		index = (Node)index_list[1];
		index_kind = N_KIND(index );
		if (index_kind == as_subtype)
			N_KIND(n_node) = as_slice;
		else if (index_kind == as_range) {
			/* Reformat it as subtype of unknown type.*/
			constraint = copy_node(index);
			N_KIND(index) = as_subtype;
			N_AST1(index) = OPT_NODE;
			N_AST2(index) = constraint;
			N_KIND(n_node) = as_slice;
		}
		else if (index_kind == as_name) {
			find_old(index);
			if (is_type(N_UNQ(index)) || (N_KIND(index) == as_attribute
			  && ((int)attribute_kind(index) == ATTR_RANGE
			  ||  (int)attribute_kind(index) == ATTR_O_RANGE
			  ||  (int)attribute_kind(index) == ATTR_T_RANGE)))
				N_KIND(n_node) = as_slice;
		}
	}
}

static void find_selected_comp(Node n_node) /*;find_selected_comp*/
{
	Node	prefix_node, s_node;
	char	*selector;
	Set		objset;
	Symbol	prefix, prefix_type, u_n;
	Forset	fs1;
	int		prefix_nat;
	Symbol	subp;
	Span	save_span;

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC :  find_selected_comp");

	prefix_node = N_AST1(n_node);
	s_node      = N_AST2(n_node);
	selector    = N_VAL(s_node);
	save_span   = get_left_span(n_node);

	find_old(prefix_node);

	if (NATURE(scope_name) == na_void && streq(ORIG_NAME(scope_name), selector))
		errmsg_str("premature usage of %", selector, "8.3(16)", s_node);

	if (N_KIND(prefix_node) == as_simple_name && !N_OVERLOADED(prefix_node)){
		prefix = N_UNQ(prefix_node);
		prefix_type = TYPE_OF(prefix);
		prefix_nat = NATURE(prefix);
		if (prefix_nat == na_package_spec || prefix_nat == na_package)
			find_exp_name(n_node, prefix, selector);
		else if (is_appropriate_for_record(prefix_type))  {
			/* Type checking will verify that the selector denotes a
			 * discriminant or component of the corresponding record or value.
			 */
			;
		}
		else if (is_appropriate_for_task(prefix_type)
		    /* if the selector is an entry name, return it as as selected
			 * component.  Context is an entry call or the prefix of the
			 * attribute COUNT.
			 */
		  && (is_access(prefix_type)
		  || (((u_n= dcl_get(DECLARED(prefix_type), selector))!= (Symbol)0)
		  && (NATURE(u_n)  == na_entry || NATURE(u_n) == na_entry_family)))) {
			;
		}
		/* other forms of selected components are expanded names. */

		else if (in_open_scopes(prefix) && prefix_nat != na_void) {
			/* prefix denotes an enclosing loop, block, or task, i.e. an
			 * enclosing construct that is not a subprogram or accept statement.
     		 */
			find_exp_name(n_node, prefix, selector);
		}

		else { 			/* various error cases. */
			if (prefix_type == symbol_any) {
				/* Object was undeclared, and error message emitted already.*/
				;
			}
			else if (NATURE(prefix) == na_void) {
				errmsg_id("premature usage of %", prefix, "8.3(16)", n_node);
			}
			else {
				errmsg("Invalid prefix in qualified name", "4.1.3", n_node);
			}
			make_any_id_node(n_node);
		}
		return;
	}
	if (N_KIND(prefix_node) != as_simple_name) {
		/* if the prefix is not a simple name (overloaded or not) it must be
     	 * be an expression whose type is appropriate for a record or access
     	 * type. Its full resolution requires type resolution as well. Nothing
     	 * else is done here.
     	 */
		;
		return;
	}
	objset= N_NAMES(prefix_node);

	/* At this point the prefix is an overloaded name. It can be an enclosing
 	 * subprogram or accept statement. It can also be a call to a parameterless
 	 * function that yields a record value.
 	 */
	FORSET(subp=(Symbol), objset, fs1);
		if (in_open_scopes(subp )) {
			/* TBSL: more than one visible such name. */
			find_exp_name(n_node, subp, selector);
			return;
		}
	ENDFORSET(fs1);

	/* if no interpretation as an expanded name is possible, it must be a
 	 * selected component of a record returned by a function call.
 	 */
	FORSET(subp=(Symbol), objset, fs1);
		if (parameterless_callable(subp))
			return;
	ENDFORSET(fs1);
	/* nothing found.*/
	make_any_id_node(n_node);
	errmsg("Ambiguous name in selected component", "4.1.3", n_node);
}

static void find_exp_name(Node n_node, Symbol prefix, char *selector)
  /*;find_exp_name*/
{
	/* resolve an expanded name whose prefix denotes a package or an enclosing
	 * construct.
	 */

	Symbol	entity;

	if (in_open_scopes(prefix))
		entity = dcl_get(DECLARED(prefix), selector);
	else					/* prefix is package. */
		entity = dcl_get_vis(DECLARED(prefix), selector);
	if (entity !=(Symbol)0)
		/* If the object is overloaded, collect its local occurences.*/
		all_declarations(n_node, prefix, selector, entity);
	else if (has_implicit_operator(n_node, prefix, selector)) {
		/* It can still be an implicitly defined operator obtained by derivation
    	 * of a predefined type within the given construct.
    	 */
		;
	}
	else {
		make_any_id_node(n_node);
		errmsg_str_id("% not declared in %" , selector,
		  prefix, "4.1.3, 8.3", n_node);
	}
}

static void all_declarations(Node n_node, Symbol prefix, char *selector,
  Symbol entity) /*;all_declarations*/
{
	/* collect all declarations that overload an entity that is declared
	 * in a given construct. If the entity is not overloadable it is returned
	 * as is (a simple name). Otherwise the local overloading must also be
	 * collected. This is made complicated by the possible presence of implicit
	 * operators, which are created by the derivation of predefined types, but
	 * are nto inserted explicitly into the symbol table of the declarative
	 * part where they occur.
	 */

	int		forall, ii;
	Symbol	predef_op, subp, f;
	Forset	fs1;
	Tuple	tup;
	Set		nams;
	Span	save_span;

	save_span = get_left_span(n_node);
	N_KIND(n_node) = as_simple_name;	/* most likely case.*/
	N_OVERLOADED(n_node) = FALSE;
	if (can_overload(entity)) {
		nams = set_copy(OVERLOADS(entity));
		if( in_op_designators(selector) && prefix!=symbol_standard0 ){
			/* Include implicitly defined operators, if they are not hidden by
         	 * an explicit declaration in the scope. To determine whether it is
	 		 * hidden, compare it with the signature of the user-defined
			 *operator just as for the resolution of renamings.
         	 */
			predef_op = dcl_get(DECLARED(symbol_standard0), selector);
			forall = TRUE;
			FORSET(subp=(Symbol), nams, fs1);
				tup = tup_new(tup_size(SIGNATURE(subp)));
				for (ii = 1; ii <= tup_size(SIGNATURE(subp)); ii++) {
					f = (Symbol) ((SIGNATURE(subp))[ii]);
					tup[ii] = (char *)TYPE_OF(f);
				}
				if (!(op_matches_spec(predef_op, tup, TYPE_OF(subp))
		 		  == (Symbol)0)) {
					forall = FALSE;
#ifdef TUPFREE
					tup_free(tup);
#endif
					break;
				}
#ifdef TUPFREE
				tup_free(tup);
#endif
			ENDFORSET(fs1);
			if (forall) {
				/* leave as qualified name, for resolution in
				 * procedure result_types.
 				 */
				nams = set_with(nams, (char *)predef_op);
				N_KIND(n_node) = as_selector;
			}
		}
		/* in any case, entity is overloaded.*/
		N_OVERLOADED(n_node) = TRUE;
		N_NAMES(n_node) = nams;
	}
	if (N_KIND(n_node) == as_simple_name) {
		if (!N_OVERLOADED(n_node)) N_UNQ(n_node) = entity;
		N_AST2(n_node) = (Node)0;
		N_VAL(n_node) = selector;
		set_span(n_node, save_span);
		TO_XREF(entity);
	}
}

static int has_implicit_operator(Node n_node, Symbol scope, char *selector)
  /*;has_implicit_operator*/
{
	Fordeclared fd1;
	Symbol	root, typ;
	char	*id;

	if (!in_op_designators(selector))
		return FALSE;
	FORDECLARED(id, typ, DECLARED(scope), fd1);
		if (!is_type(typ)) continue;
		root = root_type (typ);

		if ( !is_limited_type (typ)
	      && (streq(selector, "=") || streq(selector, "/="))) {
			N_OVERLOADED(n_node) = TRUE;
			N_NAMES(n_node) =
			  set_new1((char *)dcl_get(DECLARED(symbol_standard0), selector));
			return TRUE;
		}
		if (((root == symbol_boolean) || (is_array (typ) &&
	      (root_type (component_type (typ)) == symbol_boolean))) &&
	      (streq(selector, "not") || streq(selector, "and")
	      || streq(selector, "or") || streq(selector, "xor"))) {
			N_OVERLOADED(n_node) = TRUE;
			N_NAMES(n_node) =
			  set_new1((char *)dcl_get(DECLARED(symbol_standard0), selector));
			return TRUE;
		}
		if (is_scalar_type (typ) || (is_array (typ) &&
	      is_discrete_type (component_type (typ))) &&
	      (streq(selector, "<") || streq(selector, "<=")
	      || streq(selector, ">") || streq(selector, ">="))) {
			N_OVERLOADED(n_node) = TRUE;
			N_NAMES(n_node) =
			  set_new1((char *)dcl_get(DECLARED(symbol_standard0), selector));
			return TRUE;
		}
		if (is_numeric_type (typ) &&
	      (streq(selector, "+") || streq(selector, "-") ||
	      streq(selector, "*") || streq(selector, "/") ||
	      streq(selector, "**") || streq(selector, "abs") ||
	      streq(selector, "mod") || streq(selector, "rem"))) {
			N_OVERLOADED(n_node) = TRUE;
			N_NAMES(n_node) =
	 		  set_new1((char *)dcl_get(DECLARED(symbol_standard0), selector));
			return TRUE;
		}
		if (is_array (typ) && streq (selector , "&")) {
			N_OVERLOADED(n_node) = TRUE;
			N_NAMES(n_node) =
			  set_new1((char *)dcl_get(DECLARED(symbol_standard0), selector));
			return TRUE;
		}
	ENDFORDECLARED(fd1);
	return FALSE;
}

static void make_any_id_node(Node n_node) /*;make_any_id_node*/
{
	Span	save_span;

	save_span = get_left_span(n_node);
	N_KIND(n_node) = as_simple_name;
	N_AST2(n_node) = (Node)0;
	set_span(n_node, save_span);
	N_UNQ(n_node) = symbol_any_id;
}

static int is_appropriate_for_record(Symbol t) /*;is_appropriate_for_record*/
{
	return (is_record(t)
	    || is_access(t) && is_record(designated_type(t)));
}

static int is_appropriate_for_task(Symbol t)		/*;is_appropriate_for_task*/
{
	return (is_task_type(t)
	    || is_access(t) && is_task_type(designated_type(t)));
}

Set find_agg_types()   /*;find_agg_types*/
{
	/*
	 * The possible types of an aggregate  are all the structured types  that
	 * are	visible, even if  not directly	visible.
	 */

	Symbol	s, agg, p, fgn, ss;
	Set	res;
	Fortup	ft1;
	Forset	fs1;

	/*
	 * return {}  +/[overloads(agg): s in open_scopes
	 * 			  |(agg := declared(s)('aggregate')) /= om]
	 *     +/[overloads(fgn) : p in vis_mods
	 * 			  |(fgn :=  visible(p)('aggregate')) /= om];
	 */
	res = set_new(0);
	FORTUP(s=(Symbol), open_scopes, ft1);
		agg = dcl_get(DECLARED(s), "aggregate");
		if (agg!=(Symbol)0) {
			FORSET(ss=(Symbol), OVERLOADS(agg), fs1);
				res = set_with(res, (char *)ss);
			ENDFORSET(fs1);
		}
	ENDFORTUP(ft1);
	FORTUP(p=(Symbol), vis_mods, ft1);
		fgn =  dcl_get_vis(DECLARED(p), "aggregate");
		if (fgn!=(Symbol)0) {
			FORSET(ss=(Symbol), OVERLOADS(fgn), fs1);
				res = set_with(res, (char *) ss);
			ENDFORSET(fs1);
		}
	ENDFORTUP(ft1);
	return res;
}

Set find_access_types() /*;find_access_types*/
{
	/*
	 * Similarly, the possible types of NULL, and of any allocator, are all
	 * visible access types. To simplify their  retrieval, they are treated
	 * like aggregates,  and  attached to the marker  'access', whenever an
	 * access type definition is processed.
	 */

	Set a_types;
	Symbol	s, fgn, ss, a;
	Fortup	ft1;
	Forset	fs1;

	/*
	 * a_types =
	 * {} +/[overloads(a): s in open_scopes
	 * 			  |(a := declared(s)('access')) /= om]
	 *   +/[overloads(fgn) : p in vis_mods
	 * 			  |(fgn :=  visible(p)('access')) /= om];
	 */
	a_types = set_new(0);
	FORTUP(s = (Symbol), open_scopes, ft1);
		a = dcl_get(DECLARED(s), "access");
		if (a != (Symbol)0) {
			FORSET(ss=(Symbol), OVERLOADS(a), fs1);
				a_types = set_with(a_types, (char *) ss);
			ENDFORSET(fs1);
		}
	ENDFORTUP(ft1);

	FORTUP(fgn = (Symbol), vis_mods, ft1);
		fgn =  dcl_get_vis(DECLARED(fgn), "access");
		if (fgn != (Symbol)0) {
			FORSET(ss=(Symbol), OVERLOADS(fgn), fs1);
				a_types = set_with(a_types, (char *) ss);
			ENDFORSET(fs1);
		}
	ENDFORTUP(ft1);

	if (set_size(a_types) == 0) {
		noop_error = TRUE;
		errmsg("No available access types for allocator", "3.8,4.8",
		    current_node);
	}
	return a_types;
}

Symbol find_new(char *name)  /*;find_new*/
{
	Symbol	unique_nam, old;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  find_new");

	/*
	 * insert new name in symbol table of current scope. Check
	 * against duplications.
	 *
	 * IF error token was seen ('') , return undeclared marker.
	 */

	if (name == (char *)0 || strlen(name) == 0) return	symbol_any_id;

	/* add new name to current scope declarations.
	 * generate a unique identifier for it.
	 */

	unique_nam = (Symbol) 0;

	/* Insert new name in DECLARED table for current scope */
	old = dcl_get(DECLARED(scope_name), name);
	if (old	 != (Symbol)0) {
		/* The name has been seen already. This is acceptable
	     * if it  was inserted after	 some previous	error of
	     * any sort. (in that case it has type 'any').
		 */
		if	(TYPE_OF(old) == symbol_any) return old;
		else {
			errmsg_str("duplicate identifier: %", name , "8.3", current_node);
		}
	}
	else {
		unique_nam = sym_new(na_void);
		/* insert in declared map for scope, and make visible if scope
 	     * is a package specification. ES 9-21-86)
 	     */
		dcl_put_vis(DECLARED(scope_name), name, unique_nam ,
		  (NATURE(scope_name) == na_package_spec));
	}
	/* Initialize symbol table entry.*/
	/* allocate new symbol if not yet allocated */
	if (unique_nam == (Symbol)0) unique_nam = sym_new(na_void);
	NATURE(unique_nam)  = na_void;
	TYPE_OF(unique_nam)  = symbol_none;
	SCOPE_OF(unique_nam) = scope_name;
	ORIG_NAME(unique_nam) = name;
	TO_XREF(unique_nam);
	return unique_nam;
}

void check_void(char *id)  /*;check_void*/
{
	/*
	 * Verify that within a procedure specification no use is made of the
	 * procedure identifier under any guise. This cannot be automatically
	 * caught by the name resolution routines.
	 */
	if (streq(original_name(scope_name), id) && NATURE(scope_name) == na_void){
		errmsg_str("premature usage of %", id, "8.3(16)", current_node);
	}
}

/* new_agg_or_access becomes two procedures:
	new_agg_or_access_acc	marker 'access' implied
	new_agg_or_access_agg	marker 'aggregate' implied
 */

void new_agg_or_access_acc(Symbol type_mark)  /*;new_agg_or_access_acc*/
{
	/*
	 * The possible types of an aggregate are all composite types that are
	 * currently visible. To simplify their use, an entry  with the marker
	 * 'aggregate' is created for each such type definition. Its overloads
	 * set carries all such types  defined in  the current	scope. This is
	 * similar to what is done for other overloadable constructs.
	 * The same is done for access types, using the marker 'access'.
	 */

	Symbol	scope, old_def, new_def, maybe_priv, pr;
	int	nat;
	Private_declarations pd;

	if (cdebug2>3) TO_ERRFILE("AT PROC: new_agg_or_access_acc");

	scope = scope_name;
	nat = na_access	;
	new_def = sym_new(nat);
#ifdef TBSN
	new_def = marker + str newat;
#endif
	SCOPE_OF(new_def) = scope;
	TYPE_OF(new_def)  = type_mark;
	old_def = dcl_get(DECLARED(scope), "access");
	if (old_def == (Symbol)0 ) { 	/* first in scope*/
		dcl_put(DECLARED(scope), "access", new_def );
		OVERLOADS(new_def) = set_new1((char *) type_mark);
	}
	else {
		dcl_put(DECLARED(scope), newat_str(), new_def);
		/* If the current scope is  a private part, make sure the visible
		 * declaration has been saved, before adding new entry to overloads
		 * set for old_def.
		 */
		pd = (Private_declarations) private_decls(scope);
		if (NATURE(scope_name) == na_private_part
		  && private_decls_get(pd, old_def) == (Symbol)0)
			private_decls_put(pd, old_def);
		OVERLOADS(old_def) = set_with(OVERLOADS(old_def), (char *) type_mark);
	}
	/*
	 * If the type has an incomplete private component, (a private ancestor)
	 * list it in the set of private dependents of that ancestor.
	 */
	maybe_priv =  (Symbol) designated_type(type_mark);
	pr = private_ancestor(maybe_priv);
	if ((pr !=(Symbol)0 && in_open_scopes(SCOPE_OF(pr)))
	  || (is_access(type_mark) && is_incomplete_type(pr = maybe_priv)))
		/* ie still incomplete.*/
		if (!private_dependents(pr))
			private_dependents(pr) = set_new1((char *) type_mark);
		else
			private_dependents(pr) =
			  set_with(private_dependents(pr), (char *) type_mark);
    initialize_representation_info(type_mark,TAG_ACCESS);
}

void new_agg_or_access_agg(Symbol type_mark)  /*;new_agg_or_access_agg*/
{
	/*
	 * The possible types of an aggregate are all composite types that are
	 * currently visible. To simplify their use, an entry  with the marker
	 * 'aggregate' is created for each such type definition. Its overloads
	 * set carries all such types  defined in  the current	scope. This is
	 * similar to what is done for other overloadable constructs.
	 * The same is done for access types, using the marker 'access'.
	 */

	Symbol	scope, old_def, new_def, maybe_priv, pr;
	int	nat;
	Private_declarations pd;

	scope = scope_name;
	nat = na_aggregate;
	new_def = sym_new(nat);
#ifdef TBSN
	if (cdebug2>3) TO_ERRFILE("AT PROC: new_agg_or_access_agg");
	new_def = marker + str newat;
#endif
	SCOPE_OF(new_def) = scope;
	TYPE_OF(new_def)  = type_mark;
	old_def = dcl_get(DECLARED(scope), "aggregate");
	if (old_def == (Symbol)0 ) { /* first in scope*/
		dcl_put(DECLARED(scope), "aggregate", new_def );
		OVERLOADS(new_def) = set_new1((char *) type_mark);
	}
	else {
		dcl_put(DECLARED(scope), newat_str(), new_def);
		/* If the current scope is  a private part, make sure the visible
		 * declaration has been saved, before adding new entry to overloads
		 * set for old_def.
		 */
		pd = (Private_declarations) private_decls(scope);
		if (NATURE(scope_name) == na_private_part
		  && private_decls_get(pd, old_def) == (Symbol)0)
			private_decls_put(pd, old_def);
		/*
		 * Make a copy of the overloads set so that if the field is 
		 * changed it will not affect another copy of the symbol which 
		 * points to this set. This might be the case if we have compilation
		 * units for a package spec and body in the same file. The Overloads
		 * field pointed to by the "aggregate" symbol saved in the unitdecl 
		 * of the spec and restored when processing the body is mangled if
		 * the body adds anything to this overloads field.
		 */
		OVERLOADS(old_def) = set_copy(OVERLOADS(old_def));
		OVERLOADS(old_def) = set_with (OVERLOADS(old_def), (char *) type_mark);
	}
	/* If the type has an incomplete private component, (a private ancestor)
	 * list it in the set of private dependents of that ancestor.
	 */
	maybe_priv = type_mark;
	pr = private_ancestor(maybe_priv);
	if ((pr !=(Symbol)0 && in_open_scopes(SCOPE_OF(pr)))
	  || (is_access(type_mark) && is_incomplete_type(pr = maybe_priv)))
		/* ie still incomplete.*/
		if (!private_dependents(pr))
			private_dependents(pr) = set_new1((char *) type_mark);
		else
			private_dependents(pr) =
			  set_with(private_dependents(pr), (char *) type_mark);
}

char *original_name(Symbol unique_nam)	 /*;*original_name*/
{
	/*
	 * This procedure strips the prefix and suffix of a generated name, to
	 * recover the original source name. Is is used when looking for a
	 * compilation stub, and for error messages.
	 */
	return ORIG_NAME(unique_nam);
}

/*
 * Process  RENAMES clauses. If the renamed entity is an identifier, then
 * the renames clause simply creates a synonym : new id shares the symbol
 * table entry of the  entity. If  the entity  is an expression, then the
 * interpreter	will have  to elaborate it, and a  'renames' statement is
 * emitted. In addition, a new symbol table entry  is created for the new
 * id, with the the appropriate type and nature.
 */
void rename_ex(Node node)	  /*;rename_ex*/
{
	/* Rename an exception.*/
	Node	id_node, name_node;
	char	*new_id;
	Symbol	old;

	id_node = N_AST1(node);
	name_node = N_AST2(node);
	new_id = N_VAL(id_node);
	adasem(name_node);
	find_old(name_node);
	old = N_UNQ(name_node);
	if (N_KIND(name_node) != as_simple_name) {
		errmsg("Expect identifier in renaming", "8.5", name_node);
	}
	else if (N_OVERLOADED(name_node) || NATURE(old) != na_exception) {
		errmsg("not an exception", "8.5", name_node);
	}
	else
		dcl_put(DECLARED(scope_name), new_id, old);
}

void rename_pack(Node node)  /*;rename_pack*/
{
	Node	id_node, name_node;
	char	*new_id;
	Symbol	old;

	id_node = N_AST1(node);
	name_node = N_AST2(node);
	new_id = N_VAL(id_node);
	adasem(name_node);
	find_old(name_node);
	old = N_UNQ(name_node);
	if (N_KIND(name_node) != as_simple_name) {
		errmsg("Expect identifier in renaming", "8.5", name_node);
	}
	else if (N_OVERLOADED(name_node)
	  || (NATURE(old) != na_package
	  &&  NATURE(old) != na_package_spec
	  &&  NATURE(old) != na_generic_package
	  &&  NATURE(old) != na_generic_package_spec)) {
		errmsg("not a package", "8.5", name_node);
	}
	else
		dcl_put(DECLARED(scope_name), new_id, old);
}

void rename_subprogram(Node node)					/*;rename_subprogram*/
{
	/*
	 * The subprogram specification is elaborated, and the declared subpro-
	 * gram is inserted in the symbol table.
	 */
	Symbol	ret;
	Node	spec_node, name_node, formal_list;
	int		kind, s_kind, exists, i;
	Node	id_node, ret_node;
	Tuple	formals, ftup, old_types;
	Symbol	old1;
	Set		set;
	Symbol	ne, new_subp, new_ne;
	Forset	fs1;
	Fortup	ft1;
	char	*id;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  rename_subprogram");

	spec_node = N_AST1(node);
	name_node = N_AST2(node);
	adasem(spec_node);
	id_node = N_AST1(spec_node);
	formal_list = N_AST2(spec_node);
	ret_node = N_AST3(spec_node);
	id = N_VAL(id_node);
	formals = get_formals(formal_list, id);

	if (N_KIND(spec_node) == as_procedure ) {
		kind = na_procedure;
		s_kind = na_procedure_spec;
		ret = symbol_none;
		/* Transform into abbreviated as_rename_sub_tr node and reset
		 * N_UNQ(node) in later code below. The spec part of the node
		 * is dropped.
		 */
		N_KIND(node) = as_rename_sub_tr;
	}
	else {
		kind = na_function;
		s_kind = na_function_spec;
		ret = N_UNQ(ret_node);
		N_KIND(node) = as_rename_sub_tr;
		/* reset N_UNQ(node) below */
	}
	adasem(name_node);
	find_old(name_node); /* Name of entity being renamed.*/

	current_node = node;
	old_types = find_renamed_entity(kind, formals, ret, name_node);
	if (tup_size(old_types) != 0) {
		/* the subtypes of the formals are unaffected by the renaming */
		ret = (Symbol) tup_frome(old_types);
		FORTUPI(ftup = (Tuple), formals, i, ft1);
			ftup[3] = (char *)old_types[i];
		ENDFORTUP(ft1);
	}
	else return;		/* previous error. Is this ok ??? */

	if (N_KIND(name_node) == as_simple_name) {
		/* renaming of subprogram or operator. */
		old1 = N_UNQ(name_node);
		if (in_op_designators(id ))  /* check format, if operator spec */
			check_new_op(id_node, formals, ret);

		new_subp = chain_overloads(id, s_kind, ret, formals, old1, OPT_NODE);
		N_UNQ(node) = new_subp;
		/* a renaming is both a specification and body */
		NATURE(new_subp) = kind;
		if (ALIAS(old1) != (Symbol)0)
			ALIAS(new_subp) = ALIAS(old1);
		else
			ALIAS(new_subp) = old1;
		if (streq(id , "=")) {
			if (!streq(original_name(old1) , "=")) {
				errmsg("renaming with = can only rename an equality operator",
				  "6.7", name_node);
			}
			else if (tup_size(formals) != 2 ) {
				;	/* error caught elsewhere*/
			}
			else {
				/* The implicitly defined inequality operator, just introduced,
				 * renames another inequality.  assert exists ne in
				 * overloads(declared(scope_of(old1))('/=')) |
				 *	    same_signature(old1, ne);
				 */
				exists = FALSE;
				set = OVERLOADS(dcl_get(DECLARED(SCOPE_OF(old1)), "/="));
				FORSET(ne=(Symbol), set, fs1);
					if(same_signature(old1, ne)) {
						exists = TRUE;
						break;
					}
				ENDFORSET(fs1);
				if (!exists)
					chaos("assertion failed in rename_subprogram chapter 8");
				/* assert exists new_ne in
				 * overloads(declared(scope_of(new_subp))('/=')) |
				 *      same_signature(new_subp, new_ne);
				 */
				exists = FALSE;
				set = OVERLOADS(dcl_get(DECLARED(SCOPE_OF(new_subp)), "/="));
				FORSET(new_ne=(Symbol), set, fs1);
					if(same_signature(new_subp, new_ne)) {
						exists = TRUE;
						break;
					}
				ENDFORSET(fs1);

				if (!exists)
					chaos("assertion failed in rename_subprogram chapter 8");

				if (ALIAS(ne) != (Symbol) 0)
					ALIAS(new_ne) = ALIAS(ne);
				else
					ALIAS(new_ne) = ne;
			}
		}
	}
	else {
		/* renaming of entry or attribute. */

		new_subp= chain_overloads(id, s_kind, ret, formals, (Symbol)0,OPT_NODE);
		N_UNQ(node) = new_subp;
	}
	/* A renaming declaration provides the subprogram specification and the
	 * body as well.
	 */
	NATURE(new_subp) = kind;
}

Tuple find_renamed_entity(int kind, Tuple formals, Symbol ret, Node name_node)
/*;find_renamed_entity*/
{
	/* When a subprogram  is renamed, the  signature of the entity is that of
	 * the renamed object, and not that of the given subprogram specification
	 * (except if the  renamed entity is an operator, in  which case the base
	 * types of the specification are used).
	 * This procedure finds	the renamed  entity (subprogram, entry or attri-
	 * bute, verifies that it matches  the spec, and returns a tuple with the
	 * types of  the formals	 of the renamed object, together with  its type.
	 */
	Symbol	old1, e_name, typ, typ2, res, ft, i;
	Set		old_sub;
	Node		e_node, attr_node, typ_node;
	int		attr;
	Tuple	tup, ftup;
	Fortup	ft1;
	Span		save_span;

	if (N_OVERLOADED(name_node)) {
		old_sub = N_NAMES(name_node);		/* Most likely overloadable. */
		/* find the one that matches the new specification. */
		old1 = renamed(name_node, formals, ret);
#ifdef TBSL
		-- check old1='' in next line
#endif
		if (old1 == (Symbol) 0) return tup_new(0);	/* No match found. */
		else {
			/* suprogram name renames subprogram name. Mark as simple */
			/* renaming. */
			save_span = get_left_span(name_node);
			ast_clear(name_node);
			N_KIND(name_node) = as_simple_name;
			set_span(name_node, save_span);
			N_UNQ(name_node)  = old1;
			tup = tup_new(0);
			if (NATURE(old1) != na_op) {
				FORTUP(i=(Symbol), SIGNATURE(old1), ft1);
					tup = tup_with(tup, (char *) TYPE_OF(i));
				ENDFORTUP(ft1);
				tup = tup_with(tup, (char *) TYPE_OF(old1));
			}
			else {
				FORTUP(ftup=(Tuple), formals, ft1);
					tup = tup_with(tup, (char *) base_type((Symbol) ftup[3]));
				ENDFORTUP(ft1);
				tup = tup_with(tup, (char *) base_type(ret));
			}
			return tup;
		}
	}
	else if (kind == na_procedure &&
	  (N_KIND(name_node) == as_selector || N_KIND(name_node)== as_index)) {
		/* Procedure renames a entry given by a qualified name. Find */
		/* the full entry (and task) name. */
		renamed_entry(name_node, formals);
		e_node = N_AST2(name_node);
		if (e_node != OPT_NODE) {
			e_name = N_UNQ(e_node);
#ifdef TBSL
			return [type_of(i): i in signature(e_name)] with 'none';
#endif
			tup = tup_new(0);
			FORTUP(i=(Symbol), SIGNATURE(e_name), ft1)
			    tup = tup_with(tup, (char *) TYPE_OF(i));
			ENDFORTUP(ft1)
		    tup = tup_with(tup, (char *) symbol_none);
		}
		else {
			return tup_new(0);
		}
	}
	else	{
		/* The name can be an attribute, renaming a function. */
		/* Verify that signatures match. */
		if (kind != na_function || N_KIND(name_node) != as_attribute) {
			errmsg("invalid renaming", "8.5", name_node);
			return tup_new(0);
		}
		else if (tup_size(formals) != 1) {
			errmsg("function spec. does not match attribute", "8.5,12.3.6",
			  current_node);
			return tup_new(0);
		}

		attr_node = N_AST1(name_node);
		typ_node = N_AST2(name_node);
		attr = (int) N_VAL(attr_node);
		typ	 = N_UNQ(typ_node);
		tup	 = (Tuple) formals[1];	 /* verify that this is correct  */
		ft   = (Symbol)tup[3];
		/* Find type returned by the attribute, and the required type of its
    	 * second argument.
		 */

		if (attr == ATTR_SUCC || attr == ATTR_PRED) {
			typ2 = base_type(typ);
			res = base_type(typ);
		}
		else if (attr == ATTR_IMAGE) {
			typ2 = base_type(typ);
			res = symbol_string;
		}
		else if (attr == ATTR_VALUE) {
			typ2 = symbol_string;
			res = base_type(typ);
		}
		else {
			errmsg("attribute cannot be renamed as function", "8.5,12.3.6",
			  attr_node);
			return tup_new(0);
		}
		if (!compatible_types(ret, res) ||
		  !compatible_types(typ2, ft)) {
			errmsg("function spec. does not match attribute", "8.5,12.3.6",
			  current_node);
			return tup_new(0);
		}
		else {
			tup = tup_new(2);
			tup[1] = (char *) typ2;
			tup[2] = (char *) res;
			return tup;
		}
	}
}

void rename_object(Node node)  /*;rename_object*/
{
	Node	id_node, type_node, expr_node;
	char	*new_id;
	Symbol	typ, new_obj, obj_typ;
	Node	old_expr = (Node) 0; /* see note below */
	int	nat;
	Tuple	tup;

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC :  rename_object");

	id_node = N_AST1(node);
	type_node = N_AST2(node);
	expr_node = N_AST3(node);
	new_id = N_VAL(id_node);
	adasem(type_node);
	adasem(expr_node);
	find_old(expr_node);
	typ = find_type(type_node);

	out_context = TRUE; /* Subcomponents of out parameters*/
	check_type(typ, expr_node);
	out_context = FALSE; /* are certainly renamable.*/

	if (in_qualifiers(N_KIND(expr_node))) {
		/* Constraints implied by the type mark of the clause are ignored*/
		expr_node = N_AST1(expr_node);
		N_AST1(node) = id_node;
		N_AST2(node) = type_node;
		N_AST3(node) = expr_node;
	}
	/* It is tempting to say that if a simple object is being renamed, the
	 * new one has the same unique name. This simple optimization must
	 * however be delayed until after conformance checks have been done.
	 */
	/* TBSL - old_expr is never initialized. However
	 * is_discriminant_dependent(12) currently always returns FALSE, so we
	 * just declare old_expr.		ds 3 aug
	 * old_expr is initialized to (Node) 0 to keep lint quite  ds 23-feb-87
	 */
	if (is_discriminant_dependent( old_expr )) {
		errmsg_str("existence of object % depends on a discriminant ", new_id,
		  "8.5", (Node)0);
	}
	else {
		new_obj = find_new(new_id);
		N_UNQ(id_node) = new_obj;
		tup = check_nat_type(expr_node);
		nat = (int) tup[1];
		obj_typ = (Symbol) tup[2];
		if (N_KIND(expr_node) == as_slice) {
			obj_typ = slice_type(node,1);
		}
		NATURE(new_obj)  = nat;
		SIGNATURE(new_obj) = (Tuple)expr_node;
		TYPE_OF(new_obj) = typ;
		if (N_KIND(expr_node) != as_ivalue) {
 	    	/* object sharing at run-time. The type is inherited from the
 	    	 * object (the declared type may be unconstrained).
			 */
			TYPE_OF(new_obj) = obj_typ;
		/* In the C version constants are allocated and this is handled
		 * during the code generation phase.
		 */
		}
	}
}

static Symbol renamed(Node name_node, Tuple formals, Symbol ret)	/*;renamed*/
{
	Node	arg_list_node, subp_node, arg, expn;
	Set		sfound, types, nset, tset, subprogs;
	Symbol	subp, n, t, found;
	Tuple	arg_list, ftup;
	Fortup	ft1;
	Forset	fs1;
	int		exists;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  renamed");

	/* Find the subprogram in the overloaded set -subprog- which matches
	 * the specification given in a renames clause or in a generic instantia-
	 * tion.
	 * If subprogs includes operators, then the matching is analogous to the
	 * type-checking of an expression. We construct a skeletal argument list
	 * out of the formals, and use result-types(q.v) to find the specific
	 * operator being renamed.
	 */
	if (cdebug2 > 0) TO_ERRFILE("Renaming prog with signature " );

	subp_node = copy_tree(name_node);
	subprogs  = set_new(0);

	/* The renamed subprogram and the given specification must have the same
	 * parameter and result profile. This requires that signatures have the
	 * same length, and that the types match. Type matching is verified by
	 * constructing a call to the renamed entity. Length checking is done first.
	 */
	FORSET(subp=(Symbol), N_NAMES(subp_node), fs1)
	    if (NATURE(subp) == na_op
	      || tup_size(SIGNATURE(subp)) == tup_size(formals))
			subprogs = set_with(subprogs, (char *)subp);
	ENDFORSET(fs1);
	N_NAMES(subp_node) = subprogs;

	arg_list_node = node_new(as_list);
	arg_list = tup_new(0);
	FORTUP(ftup=(Tuple), formals, ft1);
		t = (Symbol) ftup[3];
		arg = node_new(as_simple_name);
		N_PTYPES(arg) = set_new1((char *) t);
		arg_list = tup_with(arg_list, (char *) arg);
	ENDFORTUP(ft1);
	N_LIST(arg_list_node) = arg_list;

	/* Build call node with these arguments, and resolve. */
	expn = node_new(as_call);
	N_AST1(expn) = subp_node;
	N_AST2(expn) = arg_list_node;
	result_types(expn);
	types = N_PTYPES(expn);
	N_PTYPES(expn) = (Set) 0; /* clear */
	if (types == (Set)0)  types = set_new(0);
	sfound = set_new(0);
	if (N_OVERLOADED(subp_node))
		nset = N_NAMES(subp_node);
	else
		nset = (Set) 0;
	if (nset!=(Set)0) {
		FORSET(n=(Symbol), nset, fs1);
			if (compatible_types(TYPE_OF(n), ret))
				sfound = set_with(sfound, (char *) n);
		ENDFORSET(fs1);
	}
	/* This may require a stronger test.*/
	if (set_size(sfound) > 1) {
		/* user-defined subprogram defined in enclosing scope hides predefined
     	 * operator, and is chosen first.
     	 */
		exists = FALSE;
		FORSET(subp=(Symbol), sfound, fs1);
			if (NATURE(subp) != na_op
		      && tup_mem((char *) SCOPE_OF(subp) , open_scopes)) {
				exists = TRUE;
				break;
			}
		ENDFORSET(fs1);
		if (exists) {
			tset = set_new(0);
			FORSET(subp=(Symbol), sfound, fs1);
				if (NATURE(subp) != na_op)
					tset = set_with(tset, (char *) subp);
			ENDFORSET(fs1);
			set_free(sfound);
			sfound = tset;
		}
		else {
			FORSET(subp=(Symbol), sfound, fs1);
				if ( NATURE(subp) == na_op) {
					sfound = set_new1((char *) subp);
					break;
				}
			ENDFORSET(fs1);
		}
	}
	if (set_size(sfound) == 1 ) {
		found = (Symbol) set_arb( sfound);
		check_modes(formals, found);

		if (cdebug2 > 0) TO_ERRFILE("renaming successful with ...");

		return found;
	}
	else if (set_size(sfound) > 1 ) {
		errmsg_id("ambiguous subprogram name: %", (Symbol) set_arb(subprogs),
		  "8.5,12.3.6", current_node);
	}
	else {
		errmsg("No match for subprogam specification ", "8.5,12.3.6",
		  current_node);
	}
	return (Symbol)0;
}

static Symbol op_matches_spec(Symbol op_nam, Tuple f_types, Symbol ret)
/*;op_matches_spec*/
{
	/* Determine whether a predefined operator matches a given subprogram
	 * specification. Called for renamings and for name resolution of
	 * selected components whose selector is an operator designator.
	 * The matching is analogous to the type-checking of an expression. We
	 * construct a skeletal argument list out of the type of formals, and
	 * use result-types(q.v) to find the specific operator being renamed.
	 */
	Node	op_node, arg_list_node, expn;
	Tuple	arg_list;
	Symbol	t;
	Fortup	ft1;
	Forset  fs1;
	Set	ops, types;
	Node	arg;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : op_matches_spec");

	if (tup_size(f_types) < 1 || tup_size(f_types)> 2 )
		return (Symbol)0;
	else {
		op_node = node_new(as_op);
		N_NAMES(op_node) = set_new1((char *) op_nam);
		N_OVERLOADED(op_node) = TRUE;

		arg_list_node = node_new(as_list);
		arg_list = tup_new(0);
		FORTUP(t=(Symbol), f_types, ft1);
			arg = node_new(as_simple_name);
			N_PTYPES(arg) = set_new1((char *) t);
			arg_list = tup_with(arg_list, (char *) arg);
		ENDFORTUP(ft1);
		N_LIST(arg_list_node) = arg_list;

		expn = node_new(as_call);
		N_AST1(expn) = op_node;
		N_AST2(expn) = arg_list_node;
		result_types(expn);
		ops =  (N_OVERLOADED(op_node)) ? N_NAMES(op_node): (Set)0;
		types = N_PTYPES(expn);
		N_PTYPES(expn) = (Set)0; /* clear */

		if (ops == (Set)0) return (Symbol) 0;
		if (set_size(ops) != 1) return (Symbol) 0;
		FORSET(t=(Symbol), types, fs1);
			if (compatible_types(t, ret)) return (Symbol) set_arb(ops);
		ENDFORSET(fs1);
		return (Symbol) 0;
	}
}

static void check_modes(Tuple formals, Symbol subp)	  /*;check_modes*/
{
	/* Verify that the modes of the formals in a renaming spec match the modes
	 * of the renamed subprogram (operator, entry).
	 */

	int		i, md;
	Fortup	ft1;
	Tuple	tup, sig;

	sig = SIGNATURE(subp);
	FORTUPI(tup=(Tuple), formals, i, ft1);
		md = (int) tup[2];
		if ((NATURE(subp) == na_op && md == na_in)
		  || md == NATURE((Symbol)sig[i]))
			;
		else {
			errmsg("parameter modes do not match", "8.5(8)", current_node);
		}
	ENDFORTUP(ft1);
}

static void renamed_entry(Node entry_expr, Tuple formals)	 /*;renamed_entry*/
{
	/* A procedure is being renamed with an expression. This can only be the
	 * renaming of an entry or a member of an entry family.
	 */

	Symbol	e, new_typ, i_type;
	Set entries, found	;
	Tuple	tup;
	Symbol	e_name;
	Node	task_node, entry_node, index_node;
	Fortup	ft1;
	Forset	fs1;
	Tuple	sig;
	int	i, nk;
	Symbol	f;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  renamed_entry");

	find_entry_name(entry_expr);
	task_node  = N_AST1(entry_expr);
	entry_node = N_AST2(entry_expr);

	if (entry_node == OPT_NODE)  /* Invalid entry name or expression*/
		return;
	else if (N_KIND(entry_expr) == as_entry_name) {
		/* possibly  overloaded; disambiguate with signature. */
		entries = N_NAMES(entry_expr);
		N_AST3(entry_expr) = OPT_NODE;   /* discard N_NAMES */
	}
	else { /* case of entry family member. Type check the index */
		e_name     = N_UNQ(entry_node);
		entries    = set_new1((char *) e_name);
		index_node = N_AST3(entry_expr);
		i_type     = (Symbol) index_type(TYPE_OF(e_name));
		check_type(i_type, index_node);
		N_KIND(entry_expr) = as_entry_name; /* common processing after this*/
	}
	found = set_new(0);

	FORSET(e=(Symbol), entries, fs1);
		sig = SIGNATURE(e);
		if (tup_size( sig) != tup_size(formals)) continue;

		FORTUPI(f =(Symbol), sig, i, ft1);
			tup = (Tuple) formals[i];
			new_typ = (Symbol) tup[3];
			if (!same_type(TYPE_OF(f), new_typ)) goto continue_forall_e;
		ENDFORTUP(ft1);

		found = set_with(found, (char *) e);
continue_forall_e:
		;
	ENDFORSET(fs1);


	if (set_size(found) != 1 ) {
		errmsg("ambiguous or invalid entry name in renaming", "8.5", current_node);
		N_AST1(entry_expr) = OPT_NODE;
		N_AST2(entry_expr) = OPT_NODE;
		N_AST3(entry_expr) = OPT_NODE;
		nk = N_KIND(entry_expr);
		if (N_AST4_DEFINED(nk)) N_AST4(entry_expr) = (Node)0;
	}
	else {
		/* use entry name to complete resolution of task name*/
		e_name = (Symbol) set_arb(found);
		N_UNQ(entry_node) = e_name;
		complete_task_name(task_node, TYPE_OF(SCOPE_OF(e_name)));
		check_modes(formals, e_name);
	}
}

Tuple check_nat_type(Node expr_node)	 /*;check_nat_type*/
{
	/* Obtain the nature and the actual type of of a renamed  expression,
	 * and verify that it designates an object.
	 */

	Symbol	expn;
	int		nat, nk;
	Symbol	t, s;
	Node	exp1, exp2;
	int		nrec, nfield;
	Tuple	tup;

	if (N_KIND(expr_node) == as_simple_name) {
		expn = N_UNQ(expr_node);
		nat = NATURE(expn);
		t = TYPE_OF(expn);
		if (nat !=na_constant
		  && nat!= na_in
		  && nat!= na_inout
		  && nat!= na_out
		  && nat!= na_obj) {
			errmsg("Renamed entity must be an object", "8.5", expr_node);
		}
		tup = tup_new(2);
		tup[1] = (char *) nat;
		tup[2] = (char *) t;
		return tup;
	}
	else {
		/* Predefined operation, or call.*/
		exp1 = N_AST1(expr_node);
		exp2 = N_AST2(expr_node);

		nk = N_KIND(expr_node);

		if (nk == as_index) {
			/* The nature of an indexed component is the same as the
			 * nature of the array object itself.
			 */
			tup = check_nat_type(exp1);
			t = (Symbol) tup[2];
			tup[2] = (char *) component_type(t);
			return tup;
		}
		else if (nk == as_slice) {
			/* The nature of the slice is that of the array object.*/
			return check_nat_type(exp1);
		}
		else if (nk == as_selector) {
			tup = check_nat_type(exp1);
			nrec = (int) tup[1];
			s = N_UNQ(exp2);
			nfield = NATURE(s);
			t = TYPE_OF(s); /* attrs. of selector */
			/* IF selector is a discriminant, the new entity must be
			 * treated as such.  Otherwise the  nature of the record
			 * object (constant, formal, etc.) determines that of the
			 * new entity.
			 */
			nat = (nfield == na_discriminant) ? na_constant : nrec;
			tup = tup_new(2);
			tup[1] = (char *) nat;
			tup[2] = (char *) t;
			return tup;
		}
		else if (nk == as_all) {
			/* A dereferenced pointer always yields an object.*/
			tup = check_nat_type(exp1);
			nat = (int) tup[1];
			t = (Symbol)tup[2];
			/*tup_free(tup); may be possible here */
			tup = tup_new(2);
			tup[1] = (char *)na_obj;
			tup[2] =(char *) designated_type(t);
			return tup;
		}
		else if (nk == as_call) {
			/* The function being called must yield an access type.*/
			t = N_TYPE(expr_node);
			if (!is_access(t)) {
				errmsg("Renamed entity must be an object", "8.5", expr_node);
			}
			tup = tup_new(2);
			tup[1] = (char *) na_obj;
			tup[2] = (char *) t;
			return tup;
		}
		else if (nk == as_ivalue) {
			tup = tup_new(2);
			tup[1] = (char *) na_constant;
			tup[2] = (char *) symbol_any;
			return tup;
		}
		else {
			/*error somewhere.*/
			tup = tup_new(2);
			tup[1] = (char *) na_obj;
			tup[2] = (char *) symbol_any;
			return tup;
		}
	}
}

void newscope(Symbol new_name)  /*;newscope*/
{
	Tuple	tup;
	int	old_size;
	int	i;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  newscope");
	/*
	 * This procedure is invoked when a new lexical scope is entered.
	 * Lexical scopes include package specifications, package bodies ,
	 * subprogram bodies and entry bodies (ACCEPT statements) . In addition
	 * record and task declarations and private parts are treated as scopes.
	 * In each case, the environment of the previous scope is stacked
	 * and the symbol table for the new scope is initialized.
	 */
	if (cdebug2 > 0)
		if (ORIG_NAME(new_name) != (char *) 0)
			printf("new scope %s\n", ORIG_NAME(new_name));

	tup = tup_new(4);
	tup[1] = (char *) scope_name;
	tup[2] = (char *) tup_copy(open_scopes);
	tup[3] = (char *) tup_copy(used_mods);
	tup[4] = (char *) tup_copy(vis_mods);
	scope_st = tup_with(scope_st, (char *) tup);
	scope_name = new_name;

	if (DECLARED(scope_name) == (Declaredmap)0) 
		DECLARED(scope_name) = dcl_new(0);

	/* save scope_name if new scope	  ds 1 aug */

	/*open_scopes := [scope_name] + open_scopes;*/
	old_size = tup_size(open_scopes);
	open_scopes = tup_exp(open_scopes, (unsigned) old_size+1);
	for (i = old_size; i >= 1; i--)
		open_scopes[i+1] = (char *) open_scopes[i];
	open_scopes[1] = (char *) scope_name;
#ifdef TBSN
suffix :
	= str newat;
	$ For the formation of unique names
#endif
}

void popscope()   /*;popscope*/
{
	Tuple	tup;

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC :  popscope");
	/*
	 * Ths procedure is called on exit from a completed lexical scope.
	 * Eventually , it should contain various housekeeping functions
	 * relating to symbol table statistics and space recovery. For now
	 * it simply restores the environment of the enclosing scope.
	 *
	 * As each scope is closed, a symbol table dump may be done, controled
	 * by the value of cdebug2:
	 *
	 *     cdebug2 = 2  :  show entries for current scope without signature
	 *     cdebug2 > 2  :  show entries for current scope with signature
	 *     cdebug2 > 6  :  show entries for all user defined scopes
	 *     cdebug2 = 9  :  show entries for all declared scopes
	 */
	if (cdebug2 > 1) {
#ifdef TBSLN
		loop forall scop in
		    if cdebug2 = 9 then domain declared
		elseif cdebug2 > 6 then domain(declared) -
		    ({
			'STANDARD#0', 'UNMENTIONABLE#0', 'ASCII'		}
		+
		    {
			x(2) :
			x in PREDEF_UNITS		}
		)
else {
	scope_name}
end
do
sig_flag :
	= (cdebug2 > 2) and
	    exists [item, u_name] in DECLARED(scop) |
	    SIGNATURE(u_name) /= om;
errstr "--- Symbol table entries for declared("+scop+"):";
TO_ERRFILE(errstr );
errstr = rpad("Id", 15) + rpad("Unique name", 25) +
rpad("Nature", 15) + rpad("Type", 24) +
if sig_flag then " Signature" else "" end;
TO_ERRFILE(errstr );
(forall [item, u_name] in DECLARED(scop))
line :
= rpad(item ? "", 14);
line := rpad(line + " " + u_name ? "", 39);
line := rpad(line + " " + nature(u_name) ? "", 54);
line := rpad(line + " " +
if is_string(type_of(u_name)) then type_of(u_name)
else str type_of(u_name) end, 79);
if sig_flag and signature(u_name) /= om then
line +:
= " " + str signature(u_name);
end if;
TO_ERRFILE(line);
line :
=  str (overloads(u_name)) + " "
+ str scope_of(u_name)    + " "
+ str alias(u_name);
TO_ERRFILE(line);

end forall;
end loop;
#endif
	}
	tup = (Tuple) tup_frome(scope_st);
	scope_name = (Symbol) tup[1];
	open_scopes = (Tuple) tup[2];
	used_mods = (Tuple) tup[3];
	vis_mods = (Tuple) tup[4];
	if (cdebug2 > 0) TO_ERRFILE("return to scope: " );
}

void newmod(char *name)   /*;newmod*/
{
	Symbol	new_name;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  newmod");

	/* Update this comment*/

#ifdef SKIPTHIS
	-- I think all we need is find_new call
	    if (IS_COMP_UNIT){
		/* TBSN- SETL has new_name := name. But in C, name is string, and
   new_name is symbol table pointer. Try replacing with find_new
    new_name = name;
 */
		new_name = find_new(name);
		/* Enter module name in STANDARD*/
		if (dcl_get(DECLARED(scope_name), name) == (Symbol)0) {
			dcl_put(DECLARED(scope_name), name, new_name);
			SCOPE_OF(new_name) = scope_name;
			TO_XREF(new_name);
		}
		else {
			errmsg_str("Duplicate declaration of %", name , "8.3", current_node);
		}
	}
	else {
		new_name = find_new(name);
	}
#endif
	new_name = find_new(name);
	ORIG_NAME(new_name) = strjoin(name, "");
	/* Initialize its symbol table and enter scope.  */
	DECLARED(new_name) = dcl_new(0);
	/*declared(new_name) := visible(new_name) := {};*/
	newscope(new_name);
	/* and update prefix of names with current module name. */
#ifdef TBSN
	prefix = prefix + name + '.';
#endif
}

void use_clause(Node node)					/*;use_clause*/
{
	/* If the use clause appears within a package specification, it constitutes
	 * a declarative item that is visible in the corresponding body, and must
	 * be saved in the declared map of the package.
	 */

	Node	id_node;
	char	*id;
	Symbol	rnam, uds, un;
	Fortup	ft1;
	Fordeclared fd;
	int 	nat;

	nat = NATURE(scope_name);
	if (nat == na_package_spec || nat == na_generic_package_spec
	  || nat == na_private_part)
		/*use_declarations(scope_name) +:= used;*/
		uds = dcl_get(DECLARED(scope_name), "$used");
	else uds = (Symbol)0;

	FORTUP(id_node =(Node), N_LIST(node), ft1);
		id = N_VAL(id_node);
		check_old(id_node);
		rnam = N_UNQ(id_node);
		if (rnam == symbol_undef) {
			errmsg_str("undeclared package name %", id, "8.4, 10.1", id_node);
		}
		else if (N_OVERLOADED(id_node) ||
		  NATURE(rnam)!=na_package && NATURE(rnam) !=na_package_spec){
			errmsg_str("% is not the name of a USEable package", id,
			  "8.4", id_node);
		}
		else {
			if (!tup_mem((char *) rnam, used_mods))
				used_mods = tup_with(used_mods, (char *) rnam);
			/* inner packages defined in a 'used' package can now be used to
 	 		 * qualify their inner entities
 	 		 */
			if (DECLARED(rnam) != (Declaredmap)0) { /* in case of error */
				FORDECLARED(id, un, DECLARED(rnam), fd);
					if (IS_VISIBLE(fd) && (NATURE(un) == na_package
					  || NATURE(un) == na_package_spec))
						vis_mods = tup_with(vis_mods, (char *) un);
				ENDFORDECLARED(fd);
			}
			if (uds != (Symbol)0)
				SIGNATURE(uds) = tup_with(SIGNATURE(uds), (char *)rnam);
		}
	ENDFORTUP(ft1);
}
