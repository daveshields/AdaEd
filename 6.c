/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "hdr.h"
#include "libhdr.h"
#include "vars.h"
#include "setprots.h"
#include "dclmapprots.h"
#include "errmsgprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "nodesprots.h"
#include "utilprots.h"
#include "chapprots.h"
#include "libprots.h"

static void invisible_designator(Node, char *);
static Tuple derived_formals(Symbol, Tuple);
static void proc_or_entry(Node);
static void new_over_spec(Symbol, int, Symbol, Tuple, Symbol, Node);

void subprog_decl(Node node)  /*;subprog_decl*/
{
	Node	spec_node, id_node, neq_node, eq_node;
	Symbol	subp_name, neq;
	int		exists;
	Forset	fs1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  subprog_decl");

	spec_node = N_AST1(node);
	id_node = N_AST1(spec_node);
	new_compunit("ss", id_node);
	adasem(spec_node);
	check_spec(node);

	subp_name = N_UNQ(id_node);
	save_subprog_info(subp_name);

	/* Modify the node kind for subprogram declarations to be 
	 * as_subprogram_decl_tr so that their specification part need not be 
	 * saved in the tree automatically. The formal part will be saved by 
	 * collect_unit_nodes only in the case of a subprogram specification 
	 * that is not in the same unit as the body as it is then needed for 
	 * conformance checks. In addition the node as_procedure (as_function)
	 * is no longer needed in the tree since this info is obtained from
	 * the symbol table.
	 * Since the spec  part is now dropped we now move the id_node info 
	 * (name of the subprogram) to the N_UNQ filed of the as_subprogram_decl_tr
	 * node directly.
	 */

	N_KIND(node) = as_subprogram_decl_tr;
	N_UNQ(node) = N_UNQ(id_node);
	if (streq(N_VAL(id_node) , "=") &&  tup_size(SIGNATURE(subp_name)) == 2) {
		/* build tree for declaration of inequality that was just introduced 
		 * (in the current scope, or the enclosing one, if now in private part).
		 */
		exists = FALSE;
		FORSET(neq = (Symbol), OVERLOADS(dcl_get(DECLARED(SCOPE_OF(subp_name)),
		  "/=")), fs1);
			if ( same_signature(neq, subp_name) ) {
				exists = TRUE;
				break;
			}
		ENDFORSET(fs1);
		if (exists) {
			neq_node = copy_tree(node);	      /* a valid subprogram decl*/
			N_UNQ(neq_node) = neq;
			eq_node = copy_node(node);
			make_insert_node(node, tup_new1((char *) eq_node), neq_node);
		}
	}
}

void check_spec(Node node) /*;check_spec*/
{
	/* If the subprogram name is an	 operator designator, verify that it has
	 * the proper type and number of arguments.
	 */

	int		proc_nat;
	Node	spec_node, id_node, formal_node, ret_node;
	char	*proc_id;
	Tuple	formals;
	Symbol	ret;
	Symbol	prog_name;
	int		spec_kind, node_kind;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  check_spec ");

	spec_node = N_AST1(node);
	id_node = N_AST1(spec_node);
	formal_node = N_AST2(spec_node);
	ret_node = N_AST3(spec_node);
	proc_id = N_VAL(id_node);

	spec_kind = N_KIND(spec_node);
	if (spec_kind == as_procedure)
		ret = symbol_none;
	else
		ret = N_UNQ(ret_node);

	switch (node_kind = N_KIND(node)) {
	  case	as_subprogram_decl:
				if (spec_kind == as_procedure)
					proc_nat = na_procedure_spec;
				else
					proc_nat = na_function_spec;
				break;
	  case	as_subprogram:
	  case	as_subprogram_stub:
	  case	as_generic_subp:
				if (spec_kind == as_procedure)
					proc_nat = na_procedure;
				else
					proc_nat = na_function;
				break;
	}

	formals = get_formals(formal_node, proc_id);

	check_out_parameters(formals);

	if (in_op_designators(proc_id ))
		check_new_op(id_node, formals, ret);

	prog_name = chain_overloads(proc_id, proc_nat, ret, formals, (Symbol)0,
	  formal_node);
	N_UNQ(id_node) = prog_name;
}

void check_new_op(Node id_node, Tuple formals, Symbol ret)	/*;check_new_op */
{
	/* apply special checks for definition of operators */
	char *proc_id;
	Tuple tup;
	Fortup ft1;
	Node  initv;
	int  exists;
	Symbol typ1;

	proc_id = N_VAL(id_node);

	if ((strcmp(proc_id , "+") == 0 || strcmp(proc_id, "-") == 0)
	  && tup_size(formals) == 1)
		;	/* Unary operators.*/
	else if ( (strcmp(proc_id , "not") == 0 || strcmp(proc_id, "abs") == 0)
	  ? tup_size(formals) == 1 : tup_size(formals) == 2 )
		;
	else {
		errmsg_str("Incorrect no. of arguments for operator %" , proc_id,
		  "6.7", id_node);
	}

	exists = FALSE;
	FORTUP(tup = (Tuple), formals, ft1);
		initv = (Node)tup[4];
		if (initv != OPT_NODE) {
			exists = TRUE;
			break;
		}
	ENDFORTUP(ft1);
	if (exists) {
		errmsg("Initializations not allowed for operators", "6.7", initv);
	}
	/* Apply the special checks on redefinitions of equality.*/
	else if (streq(proc_id , "=")) {
		typ1 = (Symbol) ((Tuple)formals[1])[3];	/* type of formal*/
		if (tup_size(formals) != 2
		  || typ1 != (Symbol) ((Tuple)formals[2])[3] 
		  || ret != symbol_boolean) {
			errmsg("Invalid argument profile for \"=\"", "6.7", id_node);
		}
	}
	else if (strcmp(proc_id , "/=") == 0) {
		errmsg(" /=	 cannot be given an explicit definition", "6.7", id_node);
	}
} /* end check_new_op */

Tuple get_formals(Node formal_list, char *proc_id) 			/*;get_formals*/
{
	/* Utility to format the formals of a subprogram specification, in the
	 * internal form kept in  the subprogram's signature.
	 */

	Node	formal_node, id_list, m_node, type_node, exp_node, id_node;
	Tuple	formals, tup;
	Fortup	ft1, ft2;
	int		formal_index, f_mode;
	Symbol 	type_mark;

	formal_index = 0;
	FORTUP(formal_node = (Node), N_LIST(formal_list), ft1);
		id_list = N_AST1(formal_node);
		FORTUP(id_node = (Node), N_LIST(id_list), ft2);
			formal_index++;
		ENDFORTUP(ft2);
	ENDFORTUP(ft1);
	formals = tup_new(formal_index);
	formal_index = 0;

	FORTUP(formal_node = (Node), N_LIST(formal_list), ft1);
		id_list = N_AST1(formal_node);
		m_node = N_AST2(formal_node);
		type_node = N_AST3(formal_node);
		invisible_designator(type_node, proc_id);
		exp_node = N_AST4(formal_node);
		invisible_designator(exp_node, proc_id);
		f_mode = (int) N_VAL(m_node);
		if (f_mode == 0) f_mode = na_in; /* note using 0 for '' f_mode case */
		type_mark = find_type(copy_tree(type_node)); /* for conformance check */
		FORTUP(id_node = (Node), N_LIST(id_list), ft2);
			formal_index++;
			tup = tup_new(4);
			tup[1] = (char *)N_VAL(id_node);
			tup[2] = (char *) f_mode;
			tup[3] = (char *) type_mark;
			tup[4] = (char *) copy_tree(exp_node);
			formals[formal_index] = (char *) tup;
		ENDFORTUP(ft2);
	ENDFORTUP(ft1);

	return (formals);
}

static void invisible_designator(Node tree_node, char *proc_id)
/*;invisible_designator*/
{
	/*
	 * check for premature use of formals
	 */

	int		nk;
	Node	n;
	Fortup	ft1;

	/* The designator of a subprogram is not visible within its specification.*/

	nk = N_KIND(tree_node);
	if (N_KIND(tree_node) == as_simple_name)  {
		if (streq(N_VAL(tree_node), proc_id))
			errmsg_str("premature usage of %", proc_id, "8.3(16)", tree_node);
	}
	else {
		if (N_AST1_DEFINED(nk)) invisible_designator(N_AST1(tree_node),proc_id);
		if (N_AST2_DEFINED(nk)) invisible_designator(N_AST2(tree_node),proc_id);
		if (N_AST3_DEFINED(nk)) invisible_designator(N_AST3(tree_node),proc_id);
		if (N_AST4_DEFINED(nk)) invisible_designator(N_AST4(tree_node),proc_id);

		if (N_LIST_DEFINED(nk) && N_LIST(tree_node) != (Tuple)0) {
			FORTUP(n = (Node), N_LIST(tree_node), ft1);
				invisible_designator(n, proc_id);
			ENDFORTUP(ft1);
		}
	}
}

void subprog_body(Node node)		/*;subprog_body*/
{
	Node	specs_node, id_node, stats_node;
	Node	eq_node, neq_node;
	char	*spec_name, *prog_id;
	Symbol	unname, prog_name, neq, scope;
	int		i;
	Forset	fs1;
	Fortup	ft1;
	int		exists;
	Tuple	decscopes, decmaps, s_info;
	/* s_info may not be needed	 ds 30 jul*/
	Unitdecl	ud;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : subprog_body");

	specs_node  = N_AST1(node);

	id_node = N_AST1(specs_node);
	adasem(id_node);
	prog_id = N_VAL(id_node);

	if (IS_COMP_UNIT) {
		new_compunit("su", id_node);
		/* If the specification of the unit was itself a compilation unit, we
		 * will verify that the two specs are conforming. If this is the
		 * body to a generic comp. unit, will have to access and update the
		 * spec. In both cases see if the spec. is available.
		 */
		spec_name = strjoin("ss", prog_id);	/* Already retrieved*/
		ud = unit_decl_get(spec_name);
		if (ud != (Unitdecl)0) {
			/* Unpack declarations and install symbol table of unit.
			 * [unname, s_info, decmap] := UNIT_DECL(spec_name);
			 */
			unname = ud->ud_unam;
			s_info = ud->ud_symbols;
			decscopes = ud->ud_decscopes;
			decmaps = ud->ud_decmaps;
			/* Must look before putting because name could have been 'with'ed */
			if (dcl_get(DECLARED(symbol_standard0), prog_id) != unname)
				dcl_put(DECLARED(symbol_standard0), prog_id, unname);

			/* (for decls = decmap(scope)) declared(scope) := decls; end; */
			FORTUPI(scope = (Symbol), decscopes, i, ft1);
				if (decmaps[i] != (char *)0)
					DECLARED(scope) = dcl_copy((Declaredmap) decmaps[i]);
			ENDFORTUP(ft1);

			/* TBSL does s_info need to be retored ?? */
			symtab_restore(s_info);
		}
	}
	check_old(id_node);
	prog_name = N_UNQ(id_node);
	if (prog_name != (Symbol)0 
	  &&(NATURE(prog_name) == na_generic_procedure_spec 
	  || NATURE(prog_name) == na_generic_function_spec)) {
		generic_subprog_body(prog_name, node);
		return;
	}
	else {
		/* (Re)process subprogram specification.*/
		adasem(specs_node);
		check_spec(node);
		prog_name = N_UNQ(id_node);
		if (NATURE(prog_name) !=na_procedure && NATURE(prog_name) !=na_function)
			/* illegal subprogram name or redeclaration */
			return;

		if (IS_COMP_UNIT && ud != (Unitdecl)0 && prog_name != unname) {
			/* Spec. does not match its previous occurrence, or several
			 * subprograms with same name are present.
			 */
			errmsg("library subprograms cannot be overloaded",
			  "10.1(10)", id_node);
			return;
		}
	}
	if (!streq(original_name(prog_name), unit_name_name(unit_name))) {
 	   /*
	    * All types in the current declarative part must be forced before
        * entering a nested scope.
	    */
	    force_all_types();
	}
	newscope(prog_name);
	process_subprog_body(node, prog_name);
	force_all_types();
	popscope();
	save_subprog_info(prog_name);
	/* Modify the node kind for subprogram bodies to be as_subprogram_tr 
	 * so that their specfication part need not be saved in the tree 
	 * automatically. The formal part need not be saved for the bodies
	 * since all the info is in the symbol table and the conformance checks
	 * are done against the formal part saved for the specification if any
	 * was given.
	 * In addition the node as_procedure (as_function) is no longer needed 
	 * in the tree since this info is obtained from the symbol table.
	 * Since the spec part is now dropped we now move the id_node info 
	 * (name of the subprogram) to the N_UNQ filed of the as_subprogram_tr
	 * node directly. In order to put the unique name info in the 
	 * as_subprogram_tr node we must shift the stats_node (statement part) 
	 * from being N_AST3 to N_AST1 so that we can use the N_UNQ field.
	 */
	N_KIND(node) = as_subprogram_tr;
	stats_node = N_AST3(node);
	N_AST1(node) = stats_node;
	N_UNQ(node) = N_UNQ(id_node);

	if (streq(prog_id , "=")) {
		exists = FALSE;
		FORSET(neq = (Symbol), OVERLOADS(dcl_get(DECLARED(SCOPE_OF(prog_name))
		  , "/=")), fs1);
			if (same_signature(neq, prog_name) ) {
				exists = TRUE;
				break;
			}
		ENDFORSET(fs1);
		if (exists) {
			/* create body of corresponding inequality, whose implicit spec.
			 * was introduced with the spec. of equality.
			 */
			neq_node = new_not_equals(neq, prog_name);
			eq_node  = copy_node(node);
			make_insert_node(node, tup_new1((char *) eq_node), neq_node);
		}
	}
}

void process_subprog_body(Node node, Symbol prog_name) /*;process_subprog_body*/
{
	Node    decl_node, stats_node, handler_node;
	int	  has_return;

	has_return_stk = tup_with(has_return_stk, (char *)FALSE);

	decl_node  = N_AST2(node);
	stats_node = N_AST3(node);
	handler_node = N_AST4(node);

	lab_init();
	adasem(decl_node);
	adasem(stats_node);
	adasem(handler_node);
	lab_end();			/* Validate goto statements in subprogram*/

	has_return = (int) tup_frome(has_return_stk);

	if (NATURE(prog_name) == na_function && !has_return)
		errmsg("Missing RETURN statement in function body", "6.5", node);

	check_incomplete_decls(prog_name, node);
}

Node new_not_equals(Symbol neq, Symbol eq)				/*;new_not_equals*/
{
	/* Build the tree for the body of an implicitly defined inequality op.
	 * This is a prime candidate for on-line expansion later on.
	 */

	Node	node, id_node, arg1, arg2, a1, a2;
	Node	call_node, not_node, ret_node, stat_node;
	Tuple	sig, tup;

	node = node_new(as_subprogram_tr);
	sig = SIGNATURE(neq);
	arg1 = (Node) sig[1];
	arg2 = (Node) sig[2];
	a1 = (Node) new_name_node((Symbol) arg1);
	a2 = (Node) new_name_node((Symbol) arg2);
	tup = tup_new(2);
	tup[1] = (char *) a1;
	tup[2] = (char *) a2;
	call_node = new_call_node(eq, tup, symbol_boolean);
	not_node = new_unop_node(symbol_not, call_node, symbol_boolean);
	id_node = new_name_node(neq);
	ret_node = node_new(as_return);
	N_AST1(ret_node) = not_node;	/* return not(arg1 = arg2)*/
	N_AST2(ret_node) = id_node;
	N_AST3(ret_node) = new_number_node(0);		/* from top level */
	/*
 * Note that stat_node is N_AST1 so is because the node is as_subprogram_tr
 * which has the stat_node is N_AST1 instead of N_AST3 as it is for
 * as_subprogram.
 */
	stat_node = new_statements_node(tup_new1((char *) ret_node));
	N_AST1(node) = stat_node;
	N_AST2(node) = OPT_NODE;
	N_UNQ(node) = neq;		/* ignore formals, etc .*/
	N_AST4(node) = OPT_NODE;

	return node;
}

Tuple process_formals(Symbol scope, Tuple form_list,int newi)
														/*;process_formals*/
{
	/* This	 is called to process  formal parameters of a procedure spec. or
	 * entry spec.
	 * The flag -newi- indicates whether this is the first time the object is
	 * seen. For  an entry or  subprogram declaration,  newi is true; for an
	 * accept  statement it is  false. For a  subprogram body it  depends on
	 * whether a separate specification was provided.
	 */

	Tuple	new_form_list, t, tup;
	int		in_out, nat;
	Node	opt_init;
	Symbol	type_mark, form_name, f_nam;
	char	*form_id;
	int		i;
	Fortup	ft1, ft2;
	char	*id;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : process_formals");

	new_form_list = tup_new(0);

	/* Initialize -declared- map for new scope. */

	if (DECLARED(scope) == (Declaredmap)0)
		DECLARED(scope) = dcl_new(0);
	newscope(scope);
	nat = NATURE(scope);
	NATURE(scope) = na_void;
	FORTUP(t = (Tuple), form_list, ft1);
		form_id = t[1];
		in_out = (int) t[2];
		type_mark = (Symbol)t[3];
		opt_init = (Node) t[4];

		form_name = find_new(form_id);
		/* formals parameters cannot have an incomplete type. They can
	 	* have an incomplete private type however.
	 	*/
		if (TYPE_OF(type_mark) == symbol_incomplete) {
			errmsg_id("Invalid use of incomplete type %", type_mark,
			  "3.8.1", current_node);
		}
		TYPE_OF(form_name) = type_mark;
		default_expr(form_name)  = (Tuple) opt_init;
		if (opt_init != OPT_NODE) {
			adasem(opt_init);
			normalize(type_mark, opt_init);
		}
		ORIG_NAME(form_name) = form_id;

		if (opt_init != OPT_NODE && newi && in_out != na_in) {
			errmsg("default initialization only allowed for IN parameters",
			  "6.1", current_node);
			opt_init = OPT_NODE;
		}

		/* Assignable parameters must not appear in functions.*/
		if ( in_out != na_in && (nat==na_function || nat==na_function_spec )) {
			errmsg_str("functions cannot have % parameters ",
			  nature_str(in_out), "6.5", current_node);
		}

		TO_XREF(form_name);
		new_form_list = tup_with(new_form_list, (char *) form_name);
	ENDFORTUP(ft1);
	FORTUPI(t = (Tuple), form_list, i, ft1);
		/* at end of formal part, set mode of formal parameters */
		form_id = t[1];
		in_out = (int) t[2];
		form_name = (Symbol) new_form_list[i];
		NATURE(form_name) = in_out;
	ENDFORTUP(ft1);

	NATURE(scope) = nat;
	popscope();
	if (newi)
		return new_form_list;
	else {		/* Verify that redeclaration matches. */
		FORTUPI(tup = (Tuple), form_list, i, ft2);
			id= tup[1];
			in_out = (int) tup[2];
			type_mark = (Symbol) tup[3];
			opt_init = (Node) tup[4];
			f_nam = (Symbol) (SIGNATURE(scope))[i];
			if (
#ifdef TBSN
		    -- skip this failed since original_name null even though had right
		    symbol	 ds 1 aug
		    strcmp(id, original_name(f_nam)) != 0  ||
#endif
		    in_out != NATURE(f_nam) || type_mark != TYPE_OF(f_nam) ) {
				/* missing conformance on init. */
				errmsg("Declaration does not match previous specification",
				  "6.3.1", current_node);
			}
		ENDFORTUP(ft2);
		return SIGNATURE(scope);
	}
}

static Tuple derived_formals(Symbol scope, Tuple form_list) /*;derived_formals*/
{
	/* build list of formals for derived subprograms.
	 * No semantic checks necessary
	 */

	Tuple new_form_list, t;
	Symbol form_name, type_mark;
	char *form_id;
	int  in_out;
	Node opt_init;
	Fortup ft1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : derived_formals");

	new_form_list = tup_new(0);

	/* Initialize -declared- map for new scope. */
	DECLARED(scope) = dcl_new(0);

	newscope(scope);

	FORTUP(t = (Tuple), form_list, ft1);
		form_id = t[1];
		in_out = (int) t[2];
		type_mark = (Symbol)t[3];
		opt_init = (Node) t[4];

		form_name = find_new(form_id);

		NATURE(form_name) = in_out;
		TYPE_OF(form_name) = type_mark;
		default_expr(form_name)  = (Tuple) opt_init;
		ORIG_NAME(form_name) = form_id;

		new_form_list = tup_with(new_form_list, (char *)form_name);
	ENDFORTUP(ft1);
	popscope();

	return(new_form_list);
}

void reprocess_formals(Symbol name, Node formals_node)	/*;reprocess_formals */
{
	/* check conformance of subprogram specifications given in spec and body.*/

	Node 	old_formals_node, old_node, new_node, old_id_list, type_node,
	    init_node;
	Symbol 	formal, type_mark;
	Tuple	old_list, new_list;
	char	*id;
	int		i;

	old_formals_node = (Node) formal_decl_tree(name);
	if (!conform(formals_node, old_formals_node)) {
		conformance_error(formals_node);
		return;
	}

	old_list = N_LIST(old_formals_node);
	new_list = N_LIST(formals_node);
	for (i = 1; i <= tup_size(old_list); i++) {
		old_node = (Node) old_list[i];
		new_node = (Node) new_list[i];
		old_id_list = N_AST1(old_node);
		type_node = N_AST3(new_node);
		type_mark = find_type(type_node);
		init_node = N_AST4(new_node);
		id = N_VAL((Node)N_LIST(old_id_list)[1]);
		formal = dcl_get(DECLARED(name), id);
		if (type_mark != TYPE_OF(formal)) {
			conformance_error(type_node);
			return;
		}
		if (init_node != OPT_NODE) {
			adasem(init_node);
			normalize(type_mark, init_node);
		}
		if (!same_expn(init_node, (Node)default_expr(formal))) {
			conformance_error(init_node);
			return;
		}
	}
}

void normalize(Symbol context_type, Node expn)				/*;normalize*/
{
	/* This procedure performs type resolution (as in check_type), without
	 * constant folding.
	 */

	Set types, otypes;
	Symbol t, old_context;
	Forset	fs1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  normalize");

	N_TYPE(expn) = symbol_any;		/*By default.*/
	fold_context = FALSE; /* to inhibit constant folding elsewhere.*/
	noop_error = FALSE;

	resolve1(expn);		/* Bottom-up pass.*/

	if (noop_error) {
		noop_error = FALSE;	/* error emitted already*/
		return;
	}

	types = N_PTYPES(expn);
	old_context = context_type;
	if (in_type_classes(context_type)) {
		/* Keep only those that belong to this class.*/
		otypes = set_copy(types);
		types = set_new(0);
		FORSET(t = (Symbol), otypes, fs1);
			if (compatible_types(t, context_type))
				types = set_with(types, (char *) t);
		ENDFORSET(fs1);
		set_free(otypes);

		if (set_size(types) > 1) {
			/* May be overloaded operator: user_defined one hides predefined.*/
			/* types -:= univ_types */
			otypes = set_copy(types); 
			types = set_new(0);
			FORSET(t = (Symbol), otypes, fs1);
				if (t != symbol_universal_integer && t != symbol_universal_real)
					types = set_with(types, (char *)t);
			ENDFORSET(fs1);
			set_free(otypes);
		}

		if (set_size(types) == 1) {
			context_type = (Symbol) set_arb (types );
			set_free(types);
		}
		else {
			type_error(set_new1((char *) symbol_any), context_type, 
			    set_size(types), expn);
			N_TYPE(expn) = symbol_any;
			set_free(types);
			fold_context = TRUE;
			return;
		}
	}
	resolve2(expn, context_type);
	fold_context = TRUE;

	if (noop_error) {
		noop_error = FALSE;	/* error emitted already*/
		return;
	}
	/* Now emit a constraint qualification if needed.*/
	if (! in_type_classes(old_context) ) {
		apply_constraint(expn, context_type);
	}
}

int conform(Node exp1, Node exp2)					/*;conform*/
{
	/* Verify that two trees corresponding to two expressions are conformant,
	 * according to 6.2.1. This procedure is called after ascertaining that
	 * the trees denote the same entities. We now verify that their lexical
	 * structure is conformant.
	 */

	Tuple	l1, l2;
	Node   sel_node, pfx1, pfx2, sel1, sel2;
	int	i, nk;
	char  * id1;

	switch (N_KIND(exp1)) {
	case (as_simple_name):
		if (N_KIND(exp2) == as_simple_name)
			return streq(N_VAL(exp1), N_VAL(exp2));
		else if (N_KIND(exp2) == as_selector) {
			sel_node = N_AST2(exp2);
			id1 = N_VAL(exp1);
			return !in_op_designators(id1) && streq(id1, N_VAL(sel_node));
		}
		else if (N_KIND(exp2) == as_qual_range) {
			/* possible if first occurrence had private type.*/
			return conform(exp1, N_AST1(exp2));
		}
		else
			return FALSE;
	case (as_mode):
		return(N_VAL(exp1) == N_VAL(exp2));   /* mode is integer in C version */
	case (as_int_literal):
		return (N_KIND(exp2) == as_int_literal
		  && const_eq(adaval(symbol_universal_integer, N_VAL(exp1)),
		  adaval(symbol_universal_integer, N_VAL(exp2)) ));
	case (as_real_literal):
		return (N_KIND(exp2) == as_real_literal
		  && const_eq(adaval(symbol_universal_real, N_VAL(exp1)),
		  adaval(symbol_universal_real, N_VAL(exp2)) ) );
	case (as_string_literal):
		return(N_KIND(exp2) == as_string_literal
		  && streq(N_VAL(exp1), N_VAL(exp2)));
	case (as_selector):
		pfx1 = N_AST1(exp1);
		sel1 = N_AST2(exp1);
		if (N_KIND(exp2) == as_simple_name )
			return (conform(exp2, exp1));
		else if (N_KIND(exp2) == as_selector ) {
			pfx2  = N_AST1(exp2);
			sel2  = N_AST2(exp2);
			return (conform(pfx1, pfx2) && streq(N_VAL(sel1), N_VAL(sel2)));
		}
		else
			return FALSE;
		break;
	default:
		if (N_KIND(exp1) != N_KIND(exp2) )
			return FALSE;
		else {
			/* if is_tuple(a1 := N_AST(exp1)) then 
	  		 *    (for i in [1..#a1])
 	  		 *  	  if not conform(a1(i), a2(i)) then return FALSE; end;
	  		 *    end for;
	  		 */
			nk = N_KIND(exp1);
			if (N_AST1_DEFINED(nk) && N_AST1(exp1) != (Node)0) {
				if (!conform(N_AST1(exp1), N_AST1(exp2)))
					return FALSE;
				if (N_AST2_DEFINED(nk) && N_AST2(exp1) != (Node)0) {
					if (!conform(N_AST2(exp1), N_AST2(exp2)))
						return FALSE;
					if (N_AST3_DEFINED(nk) && N_AST3(exp1) != (Node)0) {
						if (!conform(N_AST3(exp1), N_AST3(exp2)))
							return FALSE;
						if (N_AST4_DEFINED(nk) &&N_AST4(exp1) != (Node)0) {
							if (!conform(N_AST4(exp1), N_AST4(exp2)))
								return FALSE;
						}
					}
				}
			}
			/* if is_tuple(l1 := N_LIST(exp1)) then
	  		 *	if #l1 != #(l2 := N_LIST(exp2) ? [])) then 
	  		 *		return FALSE;
	  		 *     else
	  		 *	   (for i in [1..#l1]))
	  		 *	      if not conform(l1(i), l2(i)) then
	  		 *		return FALSE;
	  		 *	      end if;
	  		 *	end if;
          	 * end if;
  	  		 */
			if (N_LIST_DEFINED(nk))
				l1 = N_LIST(exp1);
			else
				l1 = (Tuple) 0;
			if (l1 != (Tuple)0) {
				if (N_LIST_DEFINED(N_KIND(exp2)))
					l2 = N_LIST(exp2);
				else
					l2 = (Tuple) 0;
				if (l2 == (Tuple)0 || tup_size(l1) != tup_size(l2) )
					return FALSE;
				for (i = 1; i <= tup_size(l1); i++) {
					if (!conform((Node)l1[i], (Node)l2[i]))
						return FALSE;
				}
			}
			return TRUE;  /* AST and LIST match. */
		}
	} /* end switch */
}

void call_statement(Node node) /*;call_statement*/
{
	/* This procedure resolves call statements. Syntactically the node is
	 * a name, possibly selected and indexed.
	 * These statements can have one of the following meanings :
	 * a) Procedure call.
	 * b) entry call .

	 * Procedure and entry calls are handled by first resolving the name, and
	 * then type-checking the  argument list. Complications arise for parame-
	 * terless procedures and entries, and for parameterless entries in entry
	 * entry  families. In those  cases, this procedure reformats the name by
	 * appending an empty argument list.
	 */

	Node	c_node, arg_list;
	int		nk;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : call_statement");

	c_node = N_AST1(node);
	if (N_KIND(c_node) == as_call_unresolved) {
		/* Rebuild call node: proc name, arg_list. */
		/* Next, do N_AST(node) = N_AST(c_node) */
		nk = N_KIND(node);
		if (N_AST1_DEFINED(nk)) N_AST1(node) = N_AST1(c_node);
		if (N_AST2_DEFINED(nk)) N_AST2(node) = N_AST2(c_node);
		if (N_AST3_DEFINED(nk)) N_AST3(node) = N_AST3(c_node);
		if (N_AST4_DEFINED(nk)) N_AST4(node) = N_AST4(c_node);
	}
	else if (N_KIND(c_node) == as_simple_name || N_KIND(c_node)==as_selector) {
		/* Parameterless procedure, */
		/* qualified name of entry.  */
		arg_list = node_new(as_list); /* add empty argument list. */
		N_LIST(arg_list) = tup_new(0);
		N_AST1(node) = c_node;
		N_AST2(node) = arg_list;
	}
	else {
		errmsg("Invalid statement: not procedure or entry call", "5.1", node);
		return;
	}
	proc_or_entry(node);
}

static void proc_or_entry(Node node)					/*;proc_or_entry*/
{
	/* Process procedure calls, entry calls, and calls to members of
	 * entry families.
	 * The statement :	       name(args);
	 * can have 3 meanings :
	 * a) It can be a procedure call.
	 * b) It can be an entry call.
	 * c) -name- can be the name of an entry family, and -args- an index
	 * into that family. This is recognized by the fact that the type of
	 * -name- is an array type.
	 * In the first two cases, we must type-check and format the argument
	 * list. In the last one, we must emit a parameterless entry call.

	 * If the statement has the format :	name(arg)(args);

	 * then it can only be a call  with parameters to an element of an
	 * entry family.
	 */

	Node	obj_node, arg_list, a_node;
	Symbol	obj_name, entr;
	Fortup	ft1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  proc_or_entry");

	obj_node = N_AST1(node);
	arg_list = N_AST2(node);

	adasem(obj_node);
	/* Perform name resolution on argument list.*/
	FORTUP(a_node = (Node), N_LIST(arg_list), ft1);
		adasem(a_node);
	ENDFORTUP(ft1);

	if (N_KIND(obj_node) == as_simple_name || N_KIND(obj_node) == as_selector) {
		find_old(obj_node);
		obj_name = N_UNQ(obj_node);

		/* Probably indicated in a different way */
		if (N_KIND(obj_node) != as_simple_name) {
			entry_call(node);
		}
		else if (obj_name != (Symbol)0  && NATURE(obj_name) == na_entry_family)
			/* entry family called within task body, without qualified name.*/
			entry_call(node);
		else if (N_OVERLOADED(obj_node)) {
			check_type(symbol_none, node);

			entr = N_UNQ(obj_node);
			if (entr != (Symbol)0 && NATURE(entr) == na_entry) {
				Symbol task_name;
				task_name = SCOPE_OF(entr);
				if (is_task_type(task_name))
					task_name = dcl_get(DECLARED(task_name), "current_task");
				N_KIND(obj_node) = as_entry_name;
				N_AST1(obj_node) = new_name_node(task_name);
				N_AST2(obj_node) = new_name_node(entr);
				N_AST3(obj_node) = OPT_NODE;
			}
			if (N_KIND(node) != as_call && N_KIND(node) != as_ecall) {
				errmsg("Invalid procedure or entry call", "6.5, 9.5", node);
			}

		}
		else {
		/* If the name was undeclared, an error message was emitted
		 * already. We can detect this case by the fact that the identifier
		 * has type -any-.
		 */
			if (TYPE_OF(obj_name) != symbol_any ) {
				errmsg("Invalid statement", "5.1", node);
			}
			else {
			/* Make up a dummy symbol table entry, so that subsequent uses
			 * of it have a chance of looking plausible.
			 */
				NATURE(obj_name) = na_procedure;
				{	
					int i, n; 
					Tuple tup;
					n = tup_size(N_LIST(arg_list));
					tup = tup_new(n);
					for (i = 1; i <= n; i++)
						tup[i] = (char *) symbol_any_id;
					SIGNATURE(obj_name) = tup;
				}
				TYPE_OF(obj_name) = symbol_none;
				OVERLOADS(obj_name) = set_new1((char *) obj_name);
			}
		}
	}
	else {
		/* Case of an entry family call with parameters. */
		find_old(obj_node);
		if (N_TYPE(obj_node) == symbol_any || N_KIND(obj_node) != as_index ) {
			errmsg("Invalid call", "9.5", node);
		}
		else entry_call(node);
	}
}


Symbol chain_overloads(char *id, int new_nat, Symbol new_typ, Tuple new_sig,
  Symbol parent_subp, Node formals_node) /*;chain_overloads*/
{
	/* Insert procedure, function, or enumeration literal into the current
	 * symbol table. Because these names can be overloaded, each set of
	 * overloaded names visible in the current scope is held in the
	 * -overload- attribute of the corresponding identifier.
	 * If there is no actual overload, the unique name is generated as for
	 * any other identifier. Otherwise, successive overloads in the same
	 * scope are given an additional arbitrary suffix to distinguish them
	 * one from the other.
	 * The overloaded name in inserted in the current scope.
	 */

	int		old_nat, n;
	Symbol	new_name, seen, name;
	Set		current_overload;
	Forset	fs1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  chain_overloads");

	new_name = sym_new(new_nat);

	seen = dcl_get(DECLARED(scope_name), id);
	if (seen== (Symbol)0) {
		/* First occurrence in this scope. Define therein, and make visible
		 * if scope is visible part of package specification.
		 */
		dcl_put_vis(DECLARED(scope_name), id, new_name,
		  NATURE(scope_name) == na_package_spec);
		ORIG_NAME(new_name) = id;
		new_over_spec(new_name, new_nat, new_typ, new_sig,
		  parent_subp, formals_node);
	}
	else {
		/* Name already appears in current scope. One of the following
		 * may be the case :
		 * a) It is a redeclaration, either because a non-overloaded
		 * instance of that id exists, or because an object with the
		 * same signature has already been declared : indicate error.
		 * b) It is the body of a function or procedure, whose specs
		 * have already been seen. Update the corresponding entry.
		 * c) It is a new object. Generate a new name, and make entry
		 * for it.
		 * d) It is a redeclaration of a derived subprogram. in that case
		 * the derived subprogram becomes inaccessible.
		 * e) If it is a derived subprogram, and there is an explicit user
		 * defined one already, the derived one is discarded. 
		 */
		if (!can_overload(seen)) {
			errmsg_str("Redeclaration of identifier %", id, "8.3, 8.4",
			  current_node);
			return seen;
		}
		else {
			current_overload =  set_copy(OVERLOADS(seen));
			/* If the current scope is a private part, make sure the visible
			 * declaration has been saved, before any modification of overloads
			 * set.
        	 */
			if ((scope_name != symbol_standard0) &&
			  (NATURE(scope_name) == na_private_part ||
			  NATURE(scope_name) == na_package) &&
			  private_decls_get((Private_declarations)
              private_decls(scope_name), seen) == (Symbol)0 ) {
				private_decls_put((Private_declarations)
				  private_decls(scope_name), seen);
			}
		}
		FORSET(name = (Symbol), current_overload, fs1);
			if  (same_sig_spec(name, new_sig)
			  && same_type(TYPE_OF(name), new_typ) ) {
				/* A homograph of  the current declaration exists in the
				 * scope. This is  permissible only if  one or  both are
				 * implicit declarations of derived subprogram or prede-
				 * fined operation. The latter  do not appear in Ada/Ed,
				 * and we only need to consider derived subprograms.
				 */
				if (is_derived_subprogram(name) ) {
					/* An explicit declaration redefines an implicitly
					 * derived subprogram. Make the later unreachable.
					 */
					OVERLOADS(seen) = set_less(OVERLOADS(seen), (char *) name);
					/* next line incorrect: code gen. needs to know parent */
					/* ALIAS(name) = (Symbol) 0; */
				}
				else if (parent_subp != (Symbol)0 
				  && streq(id, ORIG_NAME(parent_subp) )) {
					/* New declaration is derived subprogram.*/
					new_name = named_atom(id);
					if (new_nat != na_literal) {
						/* A derived subprogram is hidden by any other homograph
		    			 * but may itself be further derived. Insert in symbol
		    			 * table as new entity, which is only retrievable when
		    			 * iterating over declared map. A derived literal is
						 * also hidden by other declarations, but still exists
						 * as a literal of the type. It is inserted in symbol
						 * table but not in declared. 
 		    			 */
						dcl_put(DECLARED(scope_name), strjoin(id, newat_str()),
				 		  new_name);
					}
					new_over_spec(new_name, new_nat, new_typ, new_sig,
					  parent_subp, formals_node);
					ORIG_NAME(new_name) = id;
					return new_name;
				}
				else {
					n = NATURE(name);
					if ((n == na_procedure_spec
					  && new_nat == na_procedure)
					  || (n == na_function_spec && new_nat == na_function)) {
						/* Subprogram body whose spec was already seen.*/
						NATURE(name) = new_nat;
						/* Verify conformance of formal param declarations.*/
						reprocess_formals(name, formals_node);
						return name;
					}
					else {
						errmsg_str("invalid declaration of homograph %",
						  id, "8.3(17)", current_node);
						return name;
					}
				}
			}
		ENDFORSET(fs1);
		/* If we fall through, this is a new entity. Build its symbol table
		 * entry, and add it to the overload set already seen. 
		 * As declared(scope)(id) is already defined, we enter the entity in
		 * the declared map using an arbitrary string. The new entity  will
		 * always be retrieved through overload(seen).
		 * The name of the subprogram becomes hidden until the end of the spec.
		 * In particular, it cannot be used inside the formal part. 
		 */
		/* add identifier name to result of newat_str to create a unique
		 * anonymous entity which will not conflict with names generated
		 * by anonymous_type
		 */
		new_name = named_atom(id);
		dcl_put_vis(DECLARED(scope_name), strjoin(id, newat_str()), new_name,
		  NATURE(scope_name) == na_package_spec);
		old_nat = NATURE(seen);
		NATURE(seen) = na_void;
		new_over_spec(new_name, new_nat, new_typ, new_sig,
		  parent_subp, formals_node);
		NATURE(seen) = old_nat;
		OVERLOADS(seen) = set_with(OVERLOADS(seen) , (char *) new_name);
		ORIG_NAME(new_name) = id;
	}
	return new_name;
}

int can_overload(Symbol name)  /*;can_overload*/
{
	int n;
	n = NATURE(name);
	return (n == na_procedure_spec || n == na_function_spec || n == na_op
	  || n == na_function || n == na_procedure || n == na_entry
	  || n == na_literal);
}

static void new_over_spec(Symbol name, int nat, Symbol typ, Tuple sig,
  Symbol parent_subp, Node formals_node) /*;new_over_spec*/
{
	/* Place in symbol table maps the specification of a new overloadable
	 * object .
	 */

	Symbol	arg_type;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  new_over_spec");

	/* Apply the special checks on redefinitions of equality.*/

	NATURE(name) = nat;
	TYPE_OF(name) = typ;
	SCOPE_OF(name) = scope_name;
	OVERLOADS(name) = set_new1((char *) name);
	if (nat == na_literal)	SIGNATURE(name) = tup_new(0);

	/* If the subprograms have the same name but the signatures have different 
	 * types or the subprograms have differing types it is a derived subprogram 
	 * otherwise it is a renaming of a subprogram.
	 */
	else if (parent_subp != (Symbol) 0 && 
	  streq(ORIG_NAME(name), ORIG_NAME(parent_subp)) &&
	  (!same_sig_spec(parent_subp, sig) || 
	  TYPE_OF(name) != TYPE_OF(parent_subp)))
		SIGNATURE(name) = derived_formals(name, sig);
	else {
		SIGNATURE(name) = process_formals(name, sig, TRUE);
		formal_decl_tree(name) = (Symbol) formals_node;
	}
	if (streq(original_name(name) , "=")) {
		/* introduce the implicit "/=" as well.*/
		chain_overloads("/=", na_function, typ, sig, (Symbol)0, OPT_NODE);
		arg_type = TYPE_OF((Symbol)SIGNATURE(name)[1]);
		if (!is_limited_type(arg_type) && parent_subp == (Symbol)0) {
			/* an equality operator can only be defined on limited types
			 * unless it is introduced by a renaming declaration or derivation
			 */
			errmsg("= can only be defined for limited types", "6.7",
			  current_node);
		}
	}
	TO_XREF(name);
}

int same_signature(Symbol sub1, Symbol sub2) /*;same_signature*/
{
	/* Compare the signatures of two subprograms to determine whether
	 * they hide each other. Two signatures are considered identical if
	 * they have the same length, and the formals match in name and type.
	 */

	int		i;
	Symbol	type1, type2;
	Tuple	old, newi;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  same_signature");

	old = SIGNATURE(sub1);
	newi = SIGNATURE(sub2);
	if (old == newi) return TRUE;
#ifdef TBSN
	== how to translate is_tuple ?? ds 8 jun
else if (! is_tuple(old) ||  ! is_tuple(newi) ) {
	return FALSE;
}
#endif
	else if (tup_size(old) != tup_size(newi)) return FALSE;
	else {
		for (i = 1; i <= tup_size(old); i++) {
			type1 = (Symbol) old[i]; 
			type2 = (Symbol) newi[i];
			if (! same_type(TYPE_OF(type1), TYPE_OF(type2)) ) return FALSE;
		}
		return TRUE;
	}
}

int same_sig_spec(Symbol subp, Tuple spec) /*;same_sig_spec*/
{
	/* Compare the signature of a subprogram with the formals list of a
	 * new subprogram specification.
	 */

	Tuple	sig;
	Tuple	tup;
	int	i;
	Symbol	new_typ;
	Symbol	sym;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  same_sig_spec");

	sig = SIGNATURE(subp);

	if (tup_size(sig) != tup_size(spec)) return FALSE;
	else {
		for (i = 1; i <= tup_size(sig); i++) {
			tup = (Tuple) spec[i];
			new_typ = (Symbol)tup[3];
			sym = (Symbol)(sig[i]);
			if (!same_type(TYPE_OF(sym), new_typ)) return FALSE;
		}
		return TRUE;
	}
}

int same_type(Symbol type1, Symbol type2) /*;same_type*/
{
	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  same_type");

	return (base_type(type1) == base_type(type2) );
}
