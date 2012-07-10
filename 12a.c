/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/* chapter 12 - part a*/
#include "hdr.h"
#include "vars.h"
#include "libhdr.h"
#include "attr.h"
#include "unitsprots.h"
#include "errmsgprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "setprots.h"
#include "libprots.h"
#include "dclmapprots.h"
#include "nodesprots.h"
#include "chapprots.h"

static Tuple collect_generic_formals(Node);
static void add_implicit_neq(Tuple, Node, Symbol);
static void bind_names(Node);

void generic_subprog_spec(Node node)	 /*;generic_subprog_spec*/
{
	int		nat, kind, i;
	Node	id_node, generic_part_node, ret_node, formals_list;
	int		f_mode, body_number;
	char	*obj_id;
	Symbol	gen_name, form_name, scope;
	Tuple	gen_list, form_list;
	Tuple	tup;
	Node	formal_node, id_list, m_node, type_node, exp_node, init_node;
	Symbol	type_mark;
	Tuple	f_ids;
	char	*id;
	Fortup	ft1, ft2;

	/*
	 * Build specifications	 of a  generic subprogram. We create  a scope for
	 * it, and  define within the  names of generics and  formal  parameters.
	 * The signature of the generic subprogram includes the generic parameter
	 * list and the formals. These two are unpacked during instantiation.
	 */
	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC :  generic_subprog_spec ");

	id_node = N_AST1(node);
	generic_part_node = N_AST2(node);
	formals_list = N_AST3(node);
	ret_node = N_AST4(node);
	kind = N_KIND(node);

	obj_id = N_VAL(id_node);
	new_compunit("ss", id_node);

	if (IS_COMP_UNIT) {
		/* allocate unit number for body, and mark it obsolete */
		body_number = unit_number(strjoin("su", obj_id));
		pUnits[body_number]->libInfo.obsolete = string_ds; /*"$D$"*/
	}

	gen_name = find_new(obj_id);
	N_UNQ(id_node) = gen_name;
	DECLARED(gen_name) = dcl_new(0);
	NATURE(gen_name) = na_generic_part;
	formal_decl_tree(gen_name) = (Symbol) formals_list;
	newscope(gen_name);

	adasem(generic_part_node);
	gen_list = collect_generic_formals(generic_part_node);
	/*
	 * Now declared(gen_name) contains  the generic parameters: types,
	 * objects and	subprograms.
	 *
	 * For the formal parameters, we simply must recognize their names
	 * and	types. Type  checking on  initialization  is  repeated	on
	 * instantiation.
	 */
	NATURE(gen_name) = na_void;		/* To catch premature usage. */
	form_list = tup_new(0);

	FORTUP(formal_node =(Node), N_LIST(formals_list), ft1);
		id_list = N_AST1(formal_node);
		m_node = N_AST2(formal_node);
		type_node = N_AST3(formal_node);
		exp_node = N_AST4(formal_node);
		type_mark = find_type(copy_tree(type_node));

		if (exp_node != OPT_NODE) {
			adasem(exp_node);
			init_node = copy_tree(exp_node);
			normalize(type_mark, init_node);
		}
		else init_node = OPT_NODE;
		current_node = formal_node;
		f_ids = tup_new(tup_size(N_LIST(id_list)));
		FORTUPI(id_node=(Node), N_LIST(id_list), i, ft2);
			f_ids[i] = N_VAL(id_node);
		ENDFORTUP(ft2);
		f_mode = (int) N_VAL(m_node);
		if (f_mode == 0 ) f_mode = na_in;

		FORTUP(id=, f_ids, ft2);
			form_name = find_new(id);
			NATURE(form_name)  = f_mode;
			TYPE_OF(form_name) = type_mark;
			default_expr(form_name) = (Tuple) copy_tree(init_node);
			form_list = tup_with(form_list, (char *) form_name);
		ENDFORTUP(ft2);

		if (f_mode != na_in && kind == as_generic_function) {
			errmsg_l(nature_str(f_mode),
			  " parameter not allowed for functions", "6.5", formal_node);
		}
		/*  enforce restrictions on usage of out formal parameters given in
     	 *  LRM 7.4.4
     	*/
		scope = SCOPE_OF(type_mark);
		nat = NATURE(scope);
		if (f_mode != na_out || is_access(type_mark))
			continue;
		else if (TYPE_OF(type_mark) == symbol_limited_private
	    	&& (nat == na_package_spec || nat == na_generic_package_spec 
	    	|| nat == na_generic_part )
	    	&& !in_private_part(scope)
	    	&& tup_mem((char *)scope, open_scopes) ) {
			/* We	are in the visible  part of  the package that declares
	    	 * the type. Its  full  decl. will  have to be  given with an
	    	 * assignable type.
 			 */
			misc_type_attributes(type_mark) =  
		    (misc_type_attributes(type_mark)) | TA_OUT;
		}
		else if (is_limited_type(type_mark)) {
			errmsg_id("Invalid use of limited type % for out parameter ",
			  type_mark, "7.4.4", formal_node);
		}
	ENDFORTUP(ft1);
	/*
	 * Save signature of generic object, in the format which the
	 * instantiation procedure requires.
	 */
	NATURE(gen_name) =
	    (kind == as_generic_procedure) ? na_generic_procedure_spec
	    : na_generic_function_spec;
	tup = tup_new(4);
	tup[1] = (char *) gen_list;
	tup[2] = (char *) form_list;
	tup[3] = (char *) OPT_NODE;
	tup[4] = (char *) tup_new(0);
	SIGNATURE(gen_name) = tup;
	if (kind == as_generic_function) {
		find_old(ret_node);
		TYPE_OF(gen_name) = N_UNQ(ret_node);
	}
	else {
		TYPE_OF(gen_name) = symbol_none;
	}
	popscope();

	save_subprog_info(gen_name);
}

void generic_subprog_body(Symbol prog_name, Node node) /*;generic_subprog_body*/
{
	/*
	 * Within  its body,  the generic  subprogram  name behaves  as a regular
	 * (i.e. non-generic) subprogram. In  particular, it  can be  called (and
	 * it cannot be instantiated). Its nature must be set accordingly,  prior
	 * to compilation of the body.
	 */
	int		new_nat, nat, i;
	Tuple	sig, must_constrain;
	Node	specs_node, decl_node, formals_node;
	char	*spec_name;
	char 	*junk;
	Tuple	specs, tup, gen_list, form_list, decscopes, decmaps, body_specs;
	Symbol	generic_sym, g_name;
	Unitdecl	ud;
	Fortup	ft;

	/* if module is a generic subprogram body verify that the generic spec 
	 * appeared in the same file.
	 */
	if (IS_COMP_UNIT) {
		spec_name = strjoin("ss", unit_name_name(unit_name));
		if (!streq(lib_unit_get(spec_name), AISFILENAME))
		errmsg("Separately compiled generics not supported", "none", node);
	}

	if (NATURE(prog_name) == na_generic_procedure_spec) {
		new_nat = na_procedure;
		nat = na_generic_procedure; /* Save till end of body. */
	}
	else {
		new_nat = na_function;
		nat = na_generic_function;
	}

	/*
	 * save and stack the generic symbol for this subprogram to allow the
	 * detection of recursive instantiations within the generic body
	 */
	generic_sym = sym_new_noseq(na_void);
	sym_copy(generic_sym, prog_name);
	NATURE(generic_sym) = nat;
	current_instances = tup_with(current_instances, (char *)  generic_sym);

	NATURE(prog_name) = new_nat;
	/*
	 * The signature of a  generic object includes	the generic  part. During
	 * compilation of the body, set the signature to contain only the formals
	 */
	sig = SIGNATURE(prog_name);
	gen_list = (Tuple) sig[1];
	form_list = (Tuple) sig[2];
	SIGNATURE(prog_name) = (Tuple) form_list;
	OVERLOADS(prog_name) = set_new1((char *) prog_name);

	specs_node   = N_AST1(node);
	formals_node = N_AST2(specs_node);
	decl_node    = N_AST2(node);
	newscope(prog_name);
	reprocess_formals(prog_name, formals_node);
	process_subprog_body(node, prog_name);
    force_all_types();
	popscope();
	/*
	 * If a generic subprogram parameter is an equality operator, we must
	 * construct the body for the corresponding implicitly defined inequality
	 */
	add_implicit_neq(gen_list, decl_node, prog_name);

	/* Outside of its body, the object is generic again.*/
	NATURE(prog_name) = nat;
	junk = tup_frome(current_instances);

	/* collect all generic types whose '$constrain' attribute is set into the
	 * tuple must_constrain and save it in the signature of the body
	 */

	must_constrain = tup_new(0);
	FORTUP(tup=(Tuple), gen_list, ft)
	    g_name = (Symbol)tup[1];
		if ((int)misc_type_attributes(g_name) & TA_CONSTRAIN)
			must_constrain = tup_with(must_constrain, (char *)g_name);
	ENDFORTUP(ft)

	sig= tup_new(4);
	sig[1] = (char *) gen_list;
	sig[2] = (char *) form_list;
	sig[3] = (char *) node;
	sig[4] = (char *) must_constrain;
	SIGNATURE(prog_name) = sig; /* for instantiation */
	OVERLOADS(prog_name) = (Set) 0;	/* Not a callable object. */

	/*
	 * If the  corresponding spec was defined in another compilation unit, it
	 * must	 be updated  accordingly. If the generic is not itself a compila-
	 * tion unit, we  find the unit in which it appears, and update the info.
	 * Currently this is done only if both units are in the same compilation.
	 */

	if (IS_COMP_UNIT) {
		pUnits[unit_number(unit_name)]->libInfo.obsolete = string_ok;
		/*save it as any subprogram body. */
		save_subprog_info(prog_name);
	}
	else if (streq(unit_name_type(unit_name), "bo") &&
	  streq(unit_name_name(unit_name), unit_name_names(unit_name)) ) {
		spec_name = strjoin("sp", unit_name_name(unit_name));
		ud = unit_decl_get(spec_name);
		if (streq(lib_unit_get(spec_name), AISFILENAME) && (ud!=(Unitdecl)0)) {
			/* i.e. current compilation, and separate unit, already seen.
	 		 * update symbol table information for all entities in body.
	 		 * Probably incomplete on unit_nodes, declared, etc.
			 */
			/* [n, specs, decmap, o, v, c, nodes] := UNIT_DECL(spec_name); */
			specs = ud->ud_symbols;
			body_specs = unit_symbtab(prog_name, 'u');

			/* (for [nam, info] in body_specs)
			 *   specs(nam) := info;
			 * end for;
			 */
	 		for (i = 1; i <= tup_size(body_specs); i++)
				specs = sym_save(specs, (Symbol)body_specs[i], 'u');

	 		/* decmap(prog_name) := declared(prog_name); */
			decscopes = ud->ud_decscopes;
			decmaps   = ud->ud_decmaps;
			for (i = 1; i<= tup_size(decscopes); i++)
				if (prog_name == (Symbol)(decscopes[i]))
					break;
			decmaps[i] = (char *)dcl_copy(DECLARED(prog_name));
			/* is copy necessary ? */

			/* UNIT_DECL(spec_name):= [n, specs, decmap, o, v, c, 
 	  		 *			   		nodes + UNIT_NODES];
	  		 */
			ud->ud_symbols = specs;
			for (i = 1; i <= tup_size(unit_nodes); i++)
				ud->ud_nodes = tup_with(ud->ud_nodes, unit_nodes[i]);
		}
	}
	else {
		/* If it is a subunit of a subprogram unit, it is only visible within
		 * this unit, and no update is needed.
		 */
#ifdef TBSL
		unit_kind : = om;
#endif
	}

	N_KIND(node) = (nat == na_generic_procedure) ? as_generic_procedure
	    : as_generic_function;
}

static void add_implicit_neq(Tuple gen_list, Node decl_node, Symbol prog_name)
/*;add_implicit_neq*/
{
	/*
	 * if a generic subprogram parameter is an equality operator, an implicit
	 * inequality is thus defined, and a symbol table entry for it has been
	 * constructed at the same time as that for the equality. We place a 
	 * declaration for its body in the declarative	part of the generic unit.
	 * It  will thus  be instantiated in the same way as other local entity.
	 */
	Fortup	ft1;
	Forset	fs1;
	Tuple	tup;
	Symbol	g_name, neq;
	int		exists;
	Node	neq_node;
	Set		oset;

	FORTUP(tup=(Tuple), gen_list, ft1);
		g_name = (Symbol) tup[1];

		if (NATURE(g_name) != na_function) continue;
		if (streq(original_name(g_name), "=") == FALSE) continue;
		exists = FALSE;
		oset = (Set)OVERLOADS(dcl_get(DECLARED(prog_name), "/="));
		FORSET(neq=(Symbol), oset, fs1);
			if (same_signature(g_name, neq)) {
				exists = TRUE;
				break;
			}
		ENDFORSET(fs1);
		if (!exists) continue;
		neq_node = new_not_equals(neq, g_name);
#ifdef TBSL
		N_LIST(decl_node) :
		= [neq_node] + N_LIST(decl_node);
#endif
		N_LIST(decl_node) = tup_with(N_LIST(decl_node), (char *)neq_node);
	ENDFORTUP(ft1);
}

void generic_pack_spec(Node node)	 /*;generic_pack_spec*/
{
	Node	id_node, generic_part_node, decl_node, priv_node;
	Tuple	tup, gen_list;

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC :  generic_pack_spec");

	id_node = N_AST1(node);
	generic_part_node = N_AST2(node);
	decl_node = N_AST3(node);
	priv_node = N_AST4(node);

	new_package(id_node, na_generic_part);

	/*
	 * Process generic parameters. Their definition will appear in
	 * the scope of the generic package. The list of them is also
	 * preserved in the signature of the package, for instantiation.
	 * The signature of the generic package as the format:
	 *
	 *  [[generic_type_list, visible_decls, private_part, body, must_constrain]
	 *
	 * The body will be seen later, its place kept by a null node.
	 * Must_constrain is the list of generic types that must be constrained upon
	 * instantiation. It is created by module_body after processing the generic
	 * package body.
	 */
	adasem(generic_part_node);
	tup = tup_new(5);
	gen_list = collect_generic_formals(generic_part_node);
	tup[1] = (char *) gen_list;
	tup[2] = (char *) decl_node;
	tup[3] = (char *) priv_node;
	tup[4] = (char *) OPT_NODE;
	tup[5] = (char *) tup_new(0);

	SIGNATURE(scope_name) = tup;
	NATURE(scope_name)    = na_generic_package_spec;

	/* The rest of the package is processed as in a non-generic case.*/
	package_declarations(decl_node, priv_node);
	add_implicit_neq(gen_list, decl_node, scope_name);
	end_specs(scope_name);
}

void generic_obj_decl(Node node) /*;generic_obj_decl*/
{
	Node	id_list_node, in_out_node, type_node, init_node, id_node;
	Tuple	id_nodes;
	int		kind;
	Symbol	type_mark, name;
	Tuple	nam_list;
	Fortup	ft1;
	int		i;

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC :  generic_obj_decl");

	id_list_node = N_AST1(node);
	in_out_node = N_AST2(node);
	type_node = N_AST3(node);
	init_node = N_AST4(node);

	id_nodes = N_LIST(id_list_node);
	nam_list = tup_new(tup_size(id_nodes));
	FORTUPI(id_node=(Node), id_nodes, i, ft1);
		nam_list[i] = (char *) find_new(N_VAL(id_node));
	ENDFORTUP(ft1);
	for (i = 1; i <= tup_size(id_nodes); i++)
		N_UNQ((Node)id_nodes[i]) = (Symbol) nam_list[i];

	kind = (int) N_VAL(in_out_node);
	if (kind == 0 ) kind = na_in;
	find_type(type_node);
	type_mark = N_UNQ(type_node);
	if (is_incomplete_type(type_mark))
		errmsg_id("Premature use of incomplete or private type %",
    	  type_mark, "7.4.1", type_node);
	adasem(init_node);

	if (kind == na_in) {
		if (is_limited_type(type_mark)) {
			errmsg_l("Type of a generic formal object of mode IN must not",
			  " be a limited type", "12.1.1", type_node);
		}

		if (init_node != OPT_NODE) {
			/* Type check  default value. */
			bind_names(init_node);
			check_type(type_mark, init_node);
			if (is_deferred_constant(init_node) ) {
				errmsg_l("Deferred constant cannot be default expression",
				  " for a generic parameter", "7.4.3", init_node);
			}
		}
	}
	else if (kind == na_inout) {
		/* No constraints apply to generic inout formals.*/
		type_mark = base_type(type_mark);

		if (init_node != OPT_NODE) {
			errmsg("Initialization not allowed for IN OUT generic parameters",
			  "12.1.1", init_node);
		}
	}
	else if (kind == na_out) {
		errmsg("OUT generic formals objects not allowed",
		  "12.1.1", in_out_node);
	}

	FORTUP(name=(Symbol), nam_list, ft1);
		if (kind == na_in) NATURE(name) =  na_in;
		else NATURE(name)= na_inout;
		TYPE_OF(name)   = type_mark;
		SIGNATURE(name) = (Tuple) init_node;
	ENDFORTUP(ft1);
}

void generic_type_decl(Node node) /*;generic_type_decl*/
{
	Node	id_node, def_node, range_node, opt_disc;
	char	*id, *root_id;
	Symbol	root;
	/*char	*attr;*/
	Symbol	type_name, anon_type, generic_base, t;
	Node	lo, hi, attr_node, precision, type_node;
	Tuple	ncon, bounds;
	int		kind;

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC :  generic_type_decl");

	id_node = N_AST1(node);
	opt_disc = N_AST2(node);
	def_node = N_AST3(node);
	id = N_VAL(id_node);
	/*
	 * In the case of generic array types, anonymous parent array may be
	 * introduced. They are not generic in themselves, and play no role in
	 * the instantiated code; they are collected here and  discarded.
	 */
	newtypes = tup_with(newtypes , (char *) tup_new(0));
	if (N_KIND(def_node) == as_generic) {	/*scalar type*/
		type_name = find_new(id);
		N_UNQ(id_node) = type_name;
		root_id = N_VAL(def_node);
		if (streq(root_id, "INTEGER")) root = symbol_integer;
		else if (streq(root_id, "discrete_type")) root = symbol_discrete_type;
		else if (streq(root_id, "FLOAT")) root = symbol_float;
		else if (streq(root_id, "$FIXED")) root = symbol_dfixed;
		else chaos("generic_type_decl(12) bad generic type");

		/* A generic signature must be constructed for these types, in
		 * order to verify bounds  in instantiations,  subtypes,  etc.
		 * These bounds must expressed by means of attributes.
		 */
		if (root == symbol_integer || root == symbol_discrete_type) {
			type_node = new_name_node(type_name);
			lo = new_attribute_node(ATTR_T_FIRST,type_node,OPT_NODE, type_name);
			type_node = new_name_node(type_name);
			hi = new_attribute_node(ATTR_T_LAST, type_node,OPT_NODE, type_name);
			/*bounds := ['range', lo, hi];*/
			bounds = constraint_new(CONSTRAINT_RANGE);
			numeric_constraint_low(bounds) = (char *)lo;
			numeric_constraint_high(bounds) = (char *)hi;
			range_node = node_new(as_range);
			N_AST1(range_node) = lo;
			N_AST2(range_node) = hi;
			N_AST1(def_node) = range_node;
		}
		else {
			ncon = (Tuple) SIGNATURE(root);
			kind = (int)numeric_constraint_kind(ncon);
			lo = (Node) numeric_constraint_low(ncon);
			hi = (Node) numeric_constraint_high(ncon);
			/*[kind, lo, hi, precision] := signature(root);*/
			attr_node = node_new(as_number);
			/* proper attr code filled in below */
			if (kind == CONSTRAINT_DIGITS) {
				N_VAL(attr_node) = (char *) ATTR_DIGITS;
			}
			else {
				N_VAL(attr_node) = (char *) ATTR_DELTA;
				/* N_VAL(attr_node) = if kind = 'digits' then 'DIGITS' 
	     		 *	else 'DELTA' end;
	     		 */
			}
			precision = node_new(as_attribute);
			type_node = new_name_node(type_name);
			N_AST1(precision) = attr_node;
			N_AST2(precision) = type_node;
			N_AST3(precision) = OPT_NODE;
#ifdef TBSL
			-- check this out, SETL seems wrong
			    N_AST(def_node)  :
			= precision;
#endif
			/*bounds = [kind, lo, hi, precision];*/
			bounds = constraint_new(kind);
			numeric_constraint_low(bounds) = (char *)lo;
			numeric_constraint_high(bounds) = (char *)hi;
			numeric_constraint_digits(bounds) = (char *)precision;
		}
		/* The base type of a generic type is the base of its actual. In
		 * order to be able to refer to the base type of a generic within
		 * the object, we introduce an anonymous type that will be instan
		 * tiated with the base type of the actual.
		 */
		generic_base = anonymous_type();
		NATURE(generic_base) = na_type;
		TYPE_OF(generic_base) = root;
		SIGNATURE(generic_base) = (Tuple) bounds;
		root_type(generic_base) = root_type(root);
		misc_type_attributes(generic_base) = TA_GENERIC;

		/*SYMBTAB(type_name) := [na_subtype, generic_base, bounds];*/
		NATURE(type_name) = na_subtype;
		TYPE_OF(type_name) = generic_base;
		SIGNATURE(type_name) = bounds;
		root_type(type_name) = root_type(root);
	}
	else {	/* array type or access type.*/
		type_decl(node);
		type_name = N_UNQ(id_node);
		if (is_access(type_name))
			t = (Symbol) designated_type(type_name);
		else t = (Symbol) component_type(type_name);
		/* note that a generic type defintion is not a type declaration and
		 * therefore, the component or designated type of a generic type
		 * cannot be an incomplete private type.
		 */
		if (private_ancestor(t) != (Symbol)0 )
		errmsg_id("Premature usage of type % before its full declaration",
		  t, "7.4.1", node);
	}

	misc_type_attributes(type_name) =
	  misc_type_attributes(type_name) | TA_GENERIC;

	anon_type = (Symbol)tup_frome( newtypes);
}

void generic_priv_decl(Node node)	 /*;generic_priv_decl*/
{
	Node	id_node;
	Symbol	type_name, discr;
	Fortup	ft;

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC :  generic_priv_decl");

	private_decl(node);

	id_node = N_AST1(node);
	type_name = N_UNQ(id_node);
	if (type_name == symbol_any)   /* previous error */
		return;
	misc_type_attributes(type_name) = TA_GENERIC;

	FORTUP(discr=(Symbol), discriminant_list(type_name), ft)
	    if (discr == symbol_constrained) continue;
		if ((Node)default_expr(discr) != OPT_NODE) {
			errmsg(
			  "generic private type cannot have defaults for discriminants",
			  "12.1.2", (Node)default_expr(discr) );
			return;
		}
	ENDFORTUP(ft)
}

void check_generic_usage(Symbol type_mark)	/*;check_generic_usage*/
{
	/*
	 * if a private generic type, or a subtype or derived type of it, is used
	 * in an object declaration, component declaration, or allocator, indicate
	 * that it must be instantiated with a constrained type.
	 */
	Symbol	t;

	t = root_type(type_mark);

	if (in_priv_types(TYPE_OF(t)) && is_generic_type(t)
	  && (can_constrain(type_mark) || ! has_discriminants(type_mark)) )
		misc_type_attributes(t) = misc_type_attributes(t) | TA_CONSTRAIN;
}

void generic_subp_decl(Node node)	 /*;generic_subp_decl*/
{
	Node	spec_node, opt_is_node, id_node, formal_list, ret_node;
	char	*id;
	Tuple	formals;
	Symbol	ret, name, anon_subp;
	int 	kind;

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC :  generic_subp_decl");

	spec_node = N_AST1(node) ;
	opt_is_node = N_AST2(node) ;
	adasem(spec_node);
	id_node = N_AST1(spec_node);
	formal_list = N_AST2(spec_node);
	ret_node = N_AST3(spec_node);
	id = N_VAL(id_node);
	formals = get_formals(formal_list, id);
	if (N_KIND(spec_node) == as_procedure ) {
		kind = na_procedure;
		ret = symbol_none;
	}
	else {
		kind = na_function;
		ret = N_UNQ(ret_node);
	}
	if (in_op_designators(id ))		/* check format, if operator spec */
		check_new_op(id_node, formals, ret);
	name = chain_overloads(id, kind, ret, formals, (Symbol)0, OPT_NODE);
	N_UNQ(id_node) = name;

	/* a generic subprogram parameter is treated as a renaming of some
	 * unspecified subprogram whose actual name will be supplied at
	 * the point of instantiation
	 */
	anon_subp = sym_new(kind);
	TYPE_OF(anon_subp) = TYPE_OF(name);
	SIGNATURE(anon_subp) = SIGNATURE(name);
	SCOPE_OF(anon_subp) = scope_name;
	dcl_put(DECLARED(scope_name), newat_str(), anon_subp);
	ALIAS(name) = anon_subp;

	if (N_KIND(opt_is_node) == as_string) /* Default val is an operator name.*/
		desig_to_op(opt_is_node);
	else
		adasem(opt_is_node) ;

	if (opt_is_node != OPT_NODE) {
		if (N_KIND(opt_is_node) == as_simple_name
		    /* had 'box' in next line TBSL check type */
		&& streq(N_VAL(opt_is_node) , "box")) {
			;
		}
		else {
			find_old(opt_is_node);
			/* verify that the default has a matching signature */
			current_node = opt_is_node;
			if (tup_size(find_renamed_entity(kind,
			  formals, ret, opt_is_node)) == 0)
				N_AST2(node) = OPT_NODE; /* renaming error */
			if (name == N_UNQ(opt_is_node))
			errmsg_str("invalid reference to %", id, "8.3(16)", opt_is_node);
		}
	}
}

static void bind_names(Node node)		/*;bind_names*/
{
	Node	name, sel, arg_list, arg1, arg2, arg;
	Fortup	ft1;
	int	nk;

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC :  bind_names");
	/*
	 * Perform name resolution for default initializations for generic IN
	 * parameters and for discriminant specifications.
	 */
	switch (nk = N_KIND(node)) {
	  case	as_name:
				find_old(node);
				bind_names(node);
				break;
	  case	as_selector:
				name = N_AST1(node);
				sel = N_AST2(node);
				bind_names(name);
				break;
	  case	as_call_unresolved:
	  case	as_op:
	  case	as_un_op:
				name = N_AST1(node);
				arg_list = N_AST2(node);
				find_old(name);
				FORTUP(arg =(Node), N_LIST(arg_list), ft1);
					bind_names(arg);
				ENDFORTUP(ft1);
				break;
	  case	as_attribute:
				arg1 = N_AST2(node);
				arg2 = N_AST3(node);
				bind_names(arg1);
				bind_names(arg2);
				break;
	} /* End switch */
}

static Tuple collect_generic_formals(Node generic_part_node)
/*;collect_generic_formals*/
{
	Tuple	gen_list;
	Node	n, id_list_node, init_node, id_node, spec_node;
	int		nk;
	Fortup	ft1, ft2;
	Tuple	tup;
	/*
	 * Collect names of generic parameters, and defaults when present.
	 * Return a list of pairs [unique_name, default], which is attached to
	 * the generic object to simplify instantiation.
	 */

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC: collect_generic_formals");
	gen_list = tup_new(0);

	FORTUP(n =(Node), N_LIST(generic_part_node), ft1);
		nk = N_KIND(n);
		if (nk == as_generic_obj) {
			id_list_node = N_AST1(n);
			init_node = N_AST4(n);
			FORTUP(id_node=(Node), N_LIST(id_list_node), ft2);
				tup = tup_new(2);
				tup[1] = (char *) N_UNQ(id_node);
				tup[2] = (char *) init_node;
				gen_list = tup_with(gen_list, (char *) tup);
			ENDFORTUP(ft2);
		}
		else if (nk == as_generic_subp) {
			spec_node = N_AST1(n);
			init_node = N_AST2(n);
			id_node = N_AST1(spec_node);
			tup = tup_new(2);
			tup[1] = (char *) N_UNQ(id_node);
			tup[2] = (char *) init_node;
			gen_list = tup_with(gen_list, (char *) tup);
		}
		else {	/*Generic type definition*/
			id_node = N_AST1(n);
			tup = tup_new(2);
			tup[1] = (char *) N_UNQ(id_node);
			tup[2] = (char *) OPT_NODE;
			gen_list = tup_with(gen_list, (char *) tup);
		}
	ENDFORTUP(ft1);
	return gen_list;
}

void subprog_instance(Node node) /*;subprog_instance*/
{
	Node	id_node, gen_node, spec_node, instance_node, body_node,stmt_node;
	char	*new_id, *body_name;
	Symbol	gen_name;
	int		kind;
	Tuple	generics, instance_list;
	Tuple	formals;
	Symbol	return_type;
	Tuple	new_info;
	Symbol	new_return;
	Tuple	new_specs;
	Symbol	proc_name;
	Tuple	tup;
	Fortup	ft1;
	Symbol	new_f, f;
	Tuple	new_formals;
	Symbolmap	type_map;
	int		ii, body_num, s ;
	int		has_default = FALSE;
	Tuple	newtup;
    Set		body_precomp;
	Forset	fs1;

	/*
	 * Create an instantiation of a generic procedure.
	 *
	 * To construct	 the new instance, we  first process the instantiation of
	 * the	generics. This yields a series	of renames  statements, which map
	 * the generic parameters  into	  actual types and  subprograms. This map
	 * is used to rename all generic entities within the spec and body of the
	 * generic object, to yield the AST and SYMBTAB for the instantiated one.
	 */
	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC : subprog_instance");

	id_node	 = N_AST1(node);
	gen_node = N_AST2(node);
	instance_node = N_AST3(node);
	/* instantiate_generics adds to list - don't want to modify OPT_NODE */
	if (instance_node == OPT_NODE) {
		instance_node = node_new(as_list);
		N_LIST(instance_node) = tup_new(0);
		N_AST3(node) = instance_node;
	}
	new_id = N_VAL(id_node);
	new_compunit("su", id_node);
	find_old(gen_node);
	gen_name = N_UNQ(gen_node);
	if (gen_name == (Symbol)0) gen_name = symbol_any_id;
	/*
	 * In the case where the instantiation is a compilation unit, the context
	 * of the generic body needs to be transferred to the instatiation. This
	 * is done by adding the body of the generic (if it has been seen) to the
	 * all_vis insuring that the body is loaded and all that it references
	 * is loaded (transitivly) in INIT_GEN.
	 * In the case where the generic spec and body are not in the same unit,
	 * it is also necessary to bring in the context of the body for 
	 * instantiation. This is accomplished by adding the PRECOMP of the body
	 * to the PRECOMP (all_vis) of the unit containing the instantiation.
	 */
	body_name = strjoin("su", ORIG_NAME(gen_name));
	body_num = unitNumberFromLibUnit(body_name);
	if (IS_COMP_UNIT) {
		if (body_num)
			all_vis = tup_with(all_vis, body_name);
	}
	if (!body_num) { 	/* generic is not a library unit, but nested somewhere */
		if (S_UNIT(gen_name) != unit_number_now &&
            streq(unit_name_type(pUnits[S_UNIT(gen_name)]->name),"sp")) {
            body_name = strjoin("bo",
                        unit_name_name(pUnits[S_UNIT(gen_name)]->name));
			retrieve(body_name);
			body_num = unit_numbered(body_name);
		}
	}
	if (body_num != 0 && pUnits[body_num]->aisInfo.preComp != (char *)0) {
		/* check for previous errors */
		body_precomp = (Set) pUnits[body_num]->aisInfo.preComp;
    	FORSET( s=(int), body_precomp, fs1 );
			all_vis = tup_with(all_vis,pUnits[s]->name);
		ENDFORSET(fs1);
	}
	kind = ( N_KIND(node) == as_procedure_instance ) ? na_procedure
	    : na_function;

	if ((kind == na_procedure && 
	  (NATURE(gen_name) != na_generic_procedure
	  && NATURE(gen_name) != na_generic_procedure_spec))
	  || (kind == na_function && (NATURE(gen_name) != na_generic_function
	  && NATURE(gen_name) != na_generic_function_spec))) {
		errmsg_l("not a generic ", nature_str(kind), "12.1, 12.3", gen_node);
		return;
	}
#ifdef XREF
	TO_XREF(gen_name);
#endif
	tup = SIGNATURE(gen_name);
	generics = (Tuple) tup[1];
	formals = (Tuple) tup[2];
	body_node = (Node) tup[3];
	return_type = TYPE_OF(gen_name);

	/* Now match generic specification with instantiation.*/

	node_map = nodemap_new();   /* initialize */
	tup = instantiate_generics(generics, instance_node);
	instance_list = (Tuple) tup[1];
	type_map= (Symbolmap) tup[2];
	/*
	 * Use the instantiated generic types to obtain the actual signature and
	 * return type of the new procedure.
	 * Set default expression nodes temporarily to opt_node for the 
	 * call to chain_overloads (so that we avoid reprocessing them
	 * in process_formals). 
	 * Due to this kludge, we also test here (explicitly) that default 
	 * parameters are not specified for operator symbols.
	 * They are instantiated upon return from chain_overloads.
	 */
	new_info = tup_new(tup_size(formals));
	FORTUPI(f=(Symbol), formals, ii, ft1);
		newtup = tup_new(4);
		newtup[1] = (char *)ORIG_NAME(f);
		newtup[2] = (char *)NATURE(f);
		newtup[3] = (char *)replace(TYPE_OF(f), type_map);
		newtup[4] = (char *)OPT_NODE;  	/* temporarily */
		new_info[ii] = (char *) newtup;
		if ((Node)default_expr(f) != OPT_NODE)
			has_default = TRUE;
	ENDFORTUP(ft1);
	new_return = replace(return_type, type_map);

	new_specs = tup_new(3);
	new_specs[1] = (char *) kind;
	new_specs[2] = (char *) new_return;
	new_specs[3]= (char *) new_info;

	if (in_op_designators(new_id )) { /* check format, if operator spec */
		check_new_op(id_node, new_info, new_return);
		if (has_default)
		errmsg("Initializations not allowed for operators", "6.7", instance_node);
	}
	/* Create new overloadable object with these specs.*/

	proc_name = chain_overloads(new_id, kind, new_return, new_info, (Symbol)0,
	  OPT_NODE);
	/*
	 * in the body of the procedure, replace the generic name with the
	 * instantiated name. (it appears on the return statement, and of
	 * course in any recursive call).
	 * Also, map the names of the formals parameters into the names they
	 * have in the instantiated procedure (the actual formals ?)
	 * Instantiate default expressions for formals.
	 */
	/* map the formals of the generic into the formals of the instantiation.*/

	new_formals = SIGNATURE(proc_name);
	FORTUPI(new_f=(Symbol), new_formals, ii, ft1);
		symbolmap_put(type_map, (Symbol) formals[ii], new_f);
		default_expr(new_f) = (Tuple) instantiate_tree(
		  (Node) default_expr((Symbol)formals[ii]), type_map);
	ENDFORTUP(ft1);
	/* in the body of the subprogram, the generic name is replaced by the
	 * instantiated name. (it appears  on the  return  statement,  and of
	 * course in any recursive call). 
 	*/
	symbolmap_put(type_map, gen_name, proc_name);
	N_UNQ(id_node) = proc_name;

	if (body_node == OPT_NODE) {
		/* Attach type_map to node for subsequent instantiation (expander).
    	 * For visibility purposes, only the formals of the subprogram are
    	 * needed; the symbol table instantiation  will  also take place in
    	 * the binder.
		 */
		/* We must call instantiate_sybmtab here in order to have instantiated
		 * items placed in appropriate declared maps
		 */
		newtup = instantiate_symbtab(gen_name, proc_name, type_map);
		type_map = (Symbolmap) newtup[1];
		newtup = tup_new(2);
		newtup[1] = (char *) type_map;
		newtup[2] = (char *) TRUE;
		N_AST4(node) = new_instance_node(newtup);
		/* original instance node not needed further */
		if (instance_node != OPT_NODE)
			N_KIND(N_AST3(node)) = as_list;
		else N_AST3(node) = node_new(as_list);
		/* to be included with decls in body */
		N_LIST(N_AST3(node)) = instance_list;
	}
	else {
		instantiate_subprog_tree(node, type_map);
		/*
     	 * Take the subprogram created by the instantiation and reformat
     	 * the subprogram node to be of a form as_subprogram_tr with the
     	 * specifcation part detached from the tree. Move up the id_node
     	 * (subprogram name) info to the subprogram node. The stmt_node 
     	 * needs to be moved to N_AST1 so that N_UNQ field can be used
     	 * to store unique name of subprogram.
     	 */
		spec_node = N_AST1(node);
		stmt_node = N_AST3(node);
		id_node = N_AST1(spec_node);
		N_KIND(node) = as_subprogram_tr;
		N_AST1(node) = stmt_node;
		N_UNQ(node) = N_UNQ(id_node);
		/* 
     	 * Emit the code that instantiates the generic parameters in front of  
     	 * the subprogram.
     	 */
		if (tup_size(instance_list) > 0)
			make_insert_node(node, instance_list, copy_node(node));
	}

	save_subprog_info(proc_name);
}

void package_instance(Node node)	/*;package_instance*/
{
	Node	id_node, gen_node, instance_node;
	Symbol	package, gen_name;
	Tuple	instance_list;
	Symbolmap	type_map;
	Node	package_node;
	Tuple	tup, gen_list;
	char 	*body_name;
	int		is_comp, body_num, s;
	Set		body_precomp;
	Forset	fs1;

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC : package_instance");
	/*
	 * Create  an  instantiation of a generic  package. The renaming and
	 * instantiation of local objects is done as for subprograms.
	 */
	is_comp = IS_COMP_UNIT;
	id_node = N_AST1(node);
	gen_node= N_AST2(node);
	instance_node = N_AST3(node);
	/* instantiate_generics adds to list - don't want to modify OPT_NODE */
	if (instance_node == OPT_NODE) {
		instance_node = node_new(as_list);
		N_LIST(instance_node) = tup_new(0);
		N_AST3(node) = instance_node;
	}
	new_package(id_node, na_package_spec);
	package = scope_name;

	find_old(gen_node);
	gen_name = N_UNQ(gen_node);
	if (gen_name == (Symbol)0) gen_name =  symbol_any_id;
	/* TBSL: the context of the generic needs to be transferred to the
	 * instantiation in the case of a compilation unit. (see mod in
	 * subprogram instance).
	 */
	body_name = strjoin("bo", ORIG_NAME(gen_name));
    body_num = unitNumberFromLibUnit(body_name);
	if (is_comp) {
		if (body_num)
			all_vis = tup_with(all_vis, body_name);
	}
	if (body_num) {
    	body_precomp = (Set) pUnits[body_num]->aisInfo.preComp;
    	FORSET( s=(int), body_precomp, fs1 );
        	all_vis = tup_with(all_vis,pUnits[s]->name);
    	ENDFORSET(fs1);
	}

	/*
	 * new_compunit will have already been called under the asssumption
	 * that the current compilation unit is a non-generic package.	This
	 * may be inefficient, but the second calls to new_compunit and
	 * establish_context will act correctly.
	 * Build temporary node "package_node" to call new_compunit.
	 */
	package_node = node_new(as_simple_name);
	copy_span(id_node, package_node);
	N_VAL(package_node) = N_VAL(id_node);
	/* TBSL - SETL has 'spec instance' - I am doing as 'spec'  ds 30 jul */
	new_compunit("sp", package_node);
	if (
	    /* !is_identifier(gen_name) ||  */
		/* is_identifier will always be true because was set above */
	  (NATURE(gen_name) !=na_generic_package
	  && NATURE(gen_name) !=na_generic_package_spec) ) {
		errmsg("not a generic package", "12.1", gen_node);
		popscope();
		return;
	}
	else if (in_open_scopes(gen_name)) {
		errmsg("Recursive instantiation not allowed", "12.3", gen_node);
		popscope();
		return;
	}
#ifdef XREF
	TO_XREF(gen_name);
#endif
	tup = SIGNATURE(gen_name);
	gen_list = (Tuple) tup[1];
	node_map = nodemap_new();   /* initialize */
	tup = instantiate_generics(gen_list, instance_node);
	instance_list = (Tuple) tup[1];
	type_map = (Symbolmap) tup[2];
	symbolmap_put(type_map, gen_name, package);
	instantiate_pack_tree(node, type_map, instance_list);
	end_specs(package);
	/*
	 * The instantiated object is a package, although it appears syntact-
	 * ically as a package spec. 
	 */
	NATURE(package) = na_package;
}
