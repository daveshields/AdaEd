/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* chapter 12, part b */

#include "hdr.h"
#include "vars.h"
#include "libprots.h"
#include "librprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "dclmapprots.h"
#include "sspansprots.h"
#include "errmsgprots.h"
#include "nodesprots.h"
#include "setprots.h"
#include "chapprots.h"

static void update_one_entry(Symbol, Symbol, Symbolmap);
static void update_scalar_signature(Symbol, Symbol);
static void update_record_entry(Symbol, Symbol, Symbolmap);
static void update_array_entry(Symbol, Symbol, Symbolmap);
static Node update_new_node(Node);
static Symbol update_new_name(Symbolmap, Symbol);
static void instantiate_derived_types(Node, Symbolmap);
static Set update_overloads(Set, Symbolmap);
static int check_recursive_instance(Node);
static int scan_instance(Node);
static void nodemap_free(Nodemap);
static Node nodemap_get(Nodemap, Node);
static void nodemap_put(Nodemap, Node, Node);

void instantiate_subprog_tree(Node node, Symbolmap type_map)
  /*;instantiate_subprog_tree*/
{
	/* Build  the tree  for the instantiated object,  and the corresponding
	 * symbol table entries, some of which	may contain pointers to new tree.
	 */

	Node	id_node, gen_node, b_node, specs_node;
	Symbol	prog_name, gen_name, g_p, new_p;
	/* Nodemap	node_map; */
	Tuple	sig, itup, packs;
	Node	stmts_node, decl_node, handler_node;
	Symbolmap	rename_map;
	Tuple	truly_renamed;
	Fortup      ft1;

	id_node   = N_AST1(node);
	gen_node  = N_AST2(node);
	prog_name = N_UNQ(id_node);
	gen_name  = N_UNQ(gen_node);
	/* instantiate all entities local to the subprogram. The type map is aug-
	 * mented with the mapping of local generic entities into their instances
	 */

	itup = instantiate_symbtab(gen_name, prog_name, type_map);
	rename_map = (Symbolmap) itup[1];
	packs = (Tuple)itup[2];
	truly_renamed = (Tuple) itup[3];
	/* Now use this mapping to instantiate the AST itself. */
	node_map = nodemap_new();		/* global object. */
	current_node = node;

	sig = SIGNATURE(gen_name);
	b_node = (Node) sig[3];

	retrieve_generic_tree(b_node, (Node)0);	/* if in another file. */
	/* Instantiate body and transform into subprogram node*/
	specs_node   = N_AST1(b_node);
	decl_node    = N_AST2(b_node);
	stmts_node   = N_AST3(b_node);
	handler_node = N_AST4(b_node);

	N_KIND(node) = as_subprogram;
	N_AST1(node) = instantiate_tree(specs_node,   rename_map);
	N_AST2(node) = instantiate_tree(decl_node,    rename_map);
	N_AST3(node) = instantiate_tree(stmts_node,   rename_map);
	N_AST4(node) = instantiate_tree(handler_node, rename_map);
	/* Finally, complete the instantiation of the  symbol table. The later
	 * happens after  tree instantiation, to insure that symbtab instances 
	 * point to the instantiated nodes. The entry for the instance has been
	 * constructed by chain_overloads, and is not updated further.
	 */
	truly_renamed = tup_with(truly_renamed, (char *) gen_name);
	update_symbtab_nodes(rename_map, truly_renamed);

	/* Update the private declarations of enclosed packages */
	FORTUP(g_p=(Symbol), packs, ft1);
		new_p = symbolmap_get(rename_map, g_p);
		private_decls(new_p) = (Set) update_private_decls(g_p, rename_map);
	ENDFORTUP(ft1);
	instantiate_derived_types(decl_node, rename_map);

	/*TBSL: should we free old node_map???	ds 7nov */
	nodemap_free(node_map);		/* free current allocation */
	node_map = nodemap_new();	/* discard after use. */
}

void instantiate_pack_tree(Node node, Symbolmap type_map,
  Tuple instance_list) /*;instantiate_pack_tree*/
{
	/* Build tree for  instantiated object, and symbol table entries for all
	 * its local entities. In the case of a forward instantiation, visibility
	 * rules  require that the symbol  table  of the visible  part	be  fully
	 * instantiated. The expander then instantiates the  symbol table for the
	 * body, together with the corresponding tree.
	 */
	Node	id_node, gen_node;
	Symbol	package, gen_name, g_p, new_p, new_f, sym, gen_formal, over;
	/* Nodemap	node_map; */
	Tuple	sig;
	Node	priv_node, decl_node, b_node, spec_node, new_decl_node;
	Node	new_priv_node;
	Node	new_b_node;
	Symbolmap	rename_map;
	Tuple	ltup, itup, truly_renamed;
	Tuple	packs, gen_tup, gen_list;
	Fortup	ft1, ft2;
	Forset	fs1, fs2;
	Set  	overloadables;
	id_node = N_AST1(node);
	gen_node = N_AST2(node);
	package	 = N_UNQ(id_node);
	gen_name = N_UNQ(gen_node);

	/* Instantiate all entities local to the package. */
	itup = instantiate_symbtab(gen_name, package, type_map);
	rename_map = (Symbolmap)itup[1];
	packs = (Tuple)itup[2];
	truly_renamed = (Tuple) itup[3];
	tup_free(itup); /* itup just used to pass result*/
	/* Now instantiate the AST itself, and complete the instantiation of the
	 * symbol table. 
	 */
	node_map = nodemap_new();			/* global object.*/
	current_node = node;
	sig = SIGNATURE(gen_name);
	decl_node = (Node) sig[2];
	priv_node = (Node) sig[3];
	retrieve_generic_tree(decl_node, priv_node);
	b_node = (Node) sig[4];
	spec_node = node_new(as_package_spec);
	new_decl_node = instantiate_tree(decl_node, rename_map);
	new_priv_node = instantiate_tree(priv_node, rename_map);
	/* N_LIST(new_decl_node) = instance_list + N_LIST(new_decl_node); */
	N_LIST(new_decl_node) = tup_add(instance_list, N_LIST(new_decl_node));
	N_AST1(spec_node) = id_node;
	N_AST2(spec_node) = new_decl_node;
	N_AST3(spec_node) = new_priv_node;
	if (b_node != OPT_NODE) { /* Instantiate body as well */
		retrieve_generic_tree(b_node, (Node)0);
		new_b_node = instantiate_tree(b_node, rename_map);
		N_KIND(new_b_node) = as_package_body;
	}
	else {
		new_b_node = copy_node(node);
		/* Attach tpe_map to node for eventual code emission */
		ltup = tup_new(2);
		ltup[1] = (char *) rename_map;
		ltup[2] = (char *) needs_body(gen_name);
		N_AST4(new_b_node) = new_instance_node(ltup);
	}
	/* In any case, emit the spec node before the body */
	make_insert_node(node, tup_new1((char *) spec_node), new_b_node);

	/* Node references in the symbol table must point to the instantiated
	 * tree.
 	*/
	update_symbtab_nodes(rename_map, truly_renamed);

	/* Complete construction of visibility information for inner packages.	*/
	FORTUP(g_p=(Symbol), packs, ft1);
		new_p = symbolmap_get(rename_map, g_p);
		/* construct visible map for it, so that the proper instantiated
		 * entities within new package become accessible.
		 */
		/* TBSL: review translation of next line */
		/* 
		 *  visible(new_p) := { [id, symbolmap_get(rename_map, old_n) ? old_n] : 
		 *	     [id, old_n] in  visible(g_p)};
		 */

		/*    
		 * Nested packages (which are not generic) are now visible: their
		 * local entities are nameable using qualified names.
		 */
		if (NATURE(g_p) != na_generic_package
	    	&& NATURE(g_p) != na_generic_package_spec) {
			vis_mods = tup_with(vis_mods, (char *) new_p);
		}
		/*
		 *The top level package is added to vis_mods in end_specs, called
		 * at the end of package_instance.
		 */
		/* Finally, apply renamings to the private declarations. */
		private_decls(new_p) = (Set) update_private_decls(g_p, rename_map);
	ENDFORTUP(ft1);

	instantiate_derived_types(decl_node, rename_map);
	/* The instantiation does not include a copy of the generic part. RM 12.3(5)
	 * Thus, the instantiation of the generic parameters themselves, is not
	 * visible. If, however, a generic subprogram parameter has an overload in
	 * the visible part of the package, that overload itself must remain
	 * accessible; so we just remove the name of the instantiated generic
	 * subprogram parameter from its own overloads set.
	 */
	overloadables = set_new(0);
	gen_list = (Tuple) SIGNATURE(gen_name)[1];
	FORTUP(gen_tup = (Tuple), gen_list, ft2);
		gen_formal = (Symbol) gen_tup[1];
		new_f = symbolmap_get(rename_map, gen_formal);
		if (new_f == (Symbol) 0) 	/* error in instantiation */
			/* TBSL: can we just return here ? */
			continue;
		if (NATURE(gen_formal)==na_procedure || NATURE(gen_formal)==na_function)
			overloadables = set_with(overloadables, (char *) new_f);
	ENDFORTUP(ft2);

	FORSET(sym=(Symbol), overloadables, fs1);
		FORSET(over = (Symbol), overloadables, fs2);
			if (set_mem((char *) over, OVERLOADS(sym)))
				OVERLOADS(sym) = set_del(OVERLOADS(sym), (char *) over);
		ENDFORSET(fs2);
	ENDFORSET(fs1);
}

Tuple instantiate_symbtab(Symbol gen_name, Symbol new_n, Symbolmap rename_map)
  /*;instantiate_symbtab*/
{
	/* This	 procedure constructs  the symbol  table for instantiated  units.
	 * This involves the  instantiation of local entities. Constructing their
	 * symbol table	 entries is akin  to assigning "locations" for them. Such
	 * locations also have	to be created  for  instantiated 'in' parameters.
	 * but not for types, or inout parameters, which are  simply renamings.
	 * On the other hand, generic subprogram parameters are already defined as
	 * renamings and the instantiation provides the name of the entity which
	 * they actually rename.  Finally, thediscriminants of generic
	 * private  types are  mapped into  the discriminants  of the  actuals by
	 * renaming also, and are not otherwise instantiated.
	 * The mapping rename_map is expanded by this  procedure, and used at the
	 * point of call to complete instantiation of the bodies.
	 */

	Tuple	gen_list, rtup;
	Symbol	n;
	Tuple	renamed_params, packs;
	Symbol	gen_d;
	Tuple	instantiated_scopes;
	Symbol	g_n;
	Symbol	new_pn;
	Declaredmap old_decls, new_decls;
	char	*id;
	Symbol	old_n;
	int		nat;
	Fordeclared fd1;
	Tuple	workpile, tup;
	Forsymbol	fsym;
	Fortup	ft1;


	tup = SIGNATURE(gen_name);
	gen_list= (Tuple) tup[1];

	/*renamed_params := { n : [n, -] in gen_list | NATURE(n) != na_in} +
	 * {gen_d : [gen_d, -] in rename_map | nature(gen_d) = na_discriminant};
 	*/
	renamed_params = tup_new1((char *) new_n);
	FORTUP(tup=(Tuple), gen_list, ft1);
		n = (Symbol) tup[1];
		nat = NATURE(n);
		if (nat != na_in && nat != na_procedure && nat != na_function) {
			if (!tup_mem((char *) n, renamed_params))
				renamed_params = tup_with(renamed_params, (char *) n);
		}
	ENDFORTUP(ft1);
	FORSYMBOL(gen_d, n, rename_map, fsym);
		nat = NATURE(gen_d);
		if (nat == na_discriminant) {
			if (!tup_mem( (char *) gen_d, renamed_params))
				renamed_params = tup_with(renamed_params, (char *) gen_d);
		}
		else if (nat == na_in || nat == na_function || nat == na_procedure) {
			/* set scope of instantiated parameters to the instantiated unit */
			SCOPE_OF(n) = new_n;
		}
	ENDFORSYMBOL(fsym);
	/* Create the proper prefix for the unique names of instantiated entities */
#ifdef TBSN
o_pref :
	= prefix;
prefix :
	= original_name(new_n) + '.';
#endif
	/* An additional complication has to do with nested declarations(records,
	 * other packages) within the  generic object.	For these  we  must  also
	 * create  instances of	 their symbol  tables, so that type  checking of
	 * their  uses can  be performed.  We therefore	 traverse recursively all
	 * nested declarations within the generic object, to collect every object
	 * whose symbol	 table field  must be  instantiated.  This may be done at
	 * generic definition  time, and  will	be more efficient  than here. For
	 * procedures and  functions, only  their signature is needed  to perform
	 * type-checking, but their  symbol  tables are instantiated as well, for
	 * completeness and for use by the code generator.
	*/

	packs = tup_new(0); /* to collect names of nested packages. */
	instantiated_scopes = tup_new(0);  /* All of which have declared maps.*/
	tup = tup_new(2);
	tup[1] = (char *) gen_name;
	tup[2] = (char *) new_n;
	workpile = tup_new1((char *) tup);
	while (tup_size(workpile)) {
		tup = (Tuple) tup_frome(workpile);
		g_n = (Symbol) tup[1];
		new_pn = (Symbol) tup[2];
		tup_free(tup);
		if (!tup_mem((char *) g_n, instantiated_scopes)) {
			instantiated_scopes =tup_with(instantiated_scopes, (char *) g_n);
		}
		if (cdebug2 > 3) TO_ERRFILE("Instantiating scope " );

		/* Iterate over all items declared in g_n, the generic object (or any
   		 * object nested within and which has declarations : package, record,
   		 * subprogram, task) and collect declarations for instantiated items.
   		 */

		old_decls = DECLARED(g_n);
		new_decls = dcl_new(0);

		FORDECLARED(id, old_n, old_decls, fd1);
			if (cdebug2 > 0) TO_ERRFILE("     Instantiating item ");

			if (tup_mem((char *)old_n, renamed_params)){
				/*
	  			 * generic parameter which was renamed already. 
	  			 */
				n = symbolmap_get(rename_map, old_n);
				if (n != (Symbol)0)
					/* will be Symbol 0 ONLY if there was an error, in which
					 * case we do not put it in the declared map !
					 */
					dcl_put_vis(new_decls, id, n, IS_VISIBLE(fd1));
				    if (REPR(n) != (Tuple)0) {
					   REPR(old_n) = REPR(n);
					}
			}
			else if ((new_n = symbolmap_get(rename_map, old_n)) != (Symbol)0)
				/* id renames an object which has been instantiated already.
	  			 * The instantiation of id will point to the instantiation of
	  			 * that object.
	  			 */
				dcl_put_vis(new_decls, id, new_n, IS_VISIBLE(fd1));
			else if (SCOPE_OF(old_n) != g_n) {
				/* old_n is a renaming of some other entity, generic or other-
	  			 * wise, which is defined in some outer scope. The instantia-
	  			 * tion of old_n must rename the same entity.
	  			 */
				if ((new_n = symbolmap_get(rename_map, old_n)) == (Symbol)0){
					symbolmap_put(rename_map, old_n, old_n);
					new_n = old_n;
					/*new_n = rename_map(old_n) := old_n;*/
				}
				if (!tup_mem((char *) old_n, renamed_params))
					renamed_params = tup_with(renamed_params, (char *) old_n);
				dcl_put_vis(new_decls, id, new_n, IS_VISIBLE(fd1));
			}
			else if (NATURE(old_n) != na_void) {
				new_n = sym_new(na_void);
				/* map generic to actual. */
				symbolmap_put(rename_map, old_n, new_n);
				/* Create entry in declared for instantiated item. Other symb
	   			 * table fields are set in update_symbtab_info below.
	   			 */
				NATURE(new_n) = NATURE(old_n);
				SCOPE_OF(new_n) = new_pn;
				if (REPR(old_n) != (Tuple)0) {
					REPR(new_n) = tup_copy(REPR(old_n));
				}
				dcl_put_vis(new_decls, id, new_n, IS_VISIBLE(fd1));
				if (SCOPE_OF(old_n) != old_n
				   &&  DECLARED(old_n) != (Declaredmap)0
			  	  /* an anonymous task type has a declared map, which is
				   * instantiated when the corresponding single task object
				   * is. That map should not be instantiated twice.
	    		   */
				  && !is_anonymous_task(old_n)){
					/* Nested record, package, subprogram, or task.
					 * Put on workpile with appropriate prefix for new names.
					 */
					tup = tup_new(2);
					tup[1] = (char *) old_n;
					tup[2] = (char *) new_n;
					workpile = tup_with(workpile, (char *) tup);
				}
			}
		ENDFORDECLARED(fd1);

		/* Assign new declarations to package, record or task entity. */

		DECLARED(new_pn) = new_decls;
		nat = NATURE(g_n);

		if (nat  == na_package || nat == na_package_spec
		  || nat == na_generic_package
		  || nat == na_generic_package_spec){
			if (!tup_mem((char *) g_n, packs))
				packs = tup_with(packs , (char *) g_n);
		}
	}

#ifdef TBSN
	prefix = o_pref;			    
	$ Restore naming environment
#endif
	rtup = tup_new(3);
	rtup[1] = (char *) rename_map;
	rtup[2] = (char *) packs;
	rtup[3] = (char *) renamed_params;
	return rtup;
}

void update_symbtab_nodes(Symbolmap rename_map, Tuple truly_renamed)
  /*;update_symbtab_nodes*/
{
	/*
	 * The rename_map  contains  the generic  items and the names of their
	 * instantiations. We  must  now complete the symbol table entries for
	 * the later,  to insure  that	type information  is correct. 
	 *
	 * Entities that are true renamings (generic types, inout parameters, or 
	 * actual renamings  within the generic	 object)  have	no symbol  table 
	 * entry in it, and are skipped in what follows.
	 */

	Symbol	old_n, new_n;
	Forsymbol	fsym;

	FORSYMBOL(old_n, new_n, rename_map, fsym);
		if (!tup_mem((char *)old_n, truly_renamed) && TYPE_OF(new_n)==(Symbol)0)
			update_one_entry(old_n, new_n, rename_map);
	ENDFORSYMBOL(fsym);
}

static void update_one_entry(Symbol old_n, Symbol new_n, Symbolmap rename_map)
  /*;update_one_entry*/
{
	/* Update the symbol  table entry of one entity in an instantiated unit.
	 * The scope of the new entry has already been established. The node_map 
	 * (global) takes generic nodes into their instances.
	 */

	int		nat, ii, nn;
	Tuple	tup, gen_list, form_list, new_gen_list, new_form_list, otup, ntup;
	Node	body_node, decl_node, opt_priv_node, node, n, d;
	Fortup	ft1;
	Tuple	discr_map, newdiscr_map, newsig, constrain_list, new_constrain_list;

	/* SETL macros new_node and new_name are done using procedures 
	 * update_new_node and update_new_name, respectively.
	 */
	TYPE_OF(new_n) = update_new_name(rename_map, TYPE_OF(old_n));
	if (ALIAS(old_n) == symbol_discrete_type)
		/* not in the rename map ! */
		ALIAS(new_n) = root_type(TYPE_OF(new_n));
	else 
		ALIAS(new_n) = update_new_name(rename_map, ALIAS(old_n));

	ORIG_NAME(new_n) = ORIG_NAME(old_n);
	/* The signature of  entities may  contain tree nodes (constraints, 
	 * initial values, etc). The instantiated entries must point to the
	 * corresponding instantiated node.
	 */
	switch (nat = NATURE(old_n)) {
	case na_constant:
	case na_discriminant:
	case na_in:
	case na_obj:
		d = (Node) default_expr(old_n);
		if (d != (Node)0) {
			if (nat == na_in || nat == na_discriminant)
				/* default expression is not attached to generic tree, and
				 * must be instantiated separately.
	 			 */
				default_expr(new_n) = (Tuple)instantiate_tree(d, rename_map);
			else
				default_expr(new_n) = (Tuple)update_new_node(d);
		}
		break;
	case na_out:
	case na_inout:
		default_expr(new_n) = (Tuple)OPT_NODE;
		break;
	case na_type:
		if (is_scalar_type(old_n))
			update_scalar_signature(old_n, new_n);
		else if (in_incp_types(TYPE_OF(root_type(old_n)) )) {
			update_record_entry(old_n, new_n, rename_map);
			misc_type_attributes(new_n) = misc_type_attributes(old_n);
		}
		break;
	case na_subtype:
		if (is_scalar_type(old_n))
			update_scalar_signature(old_n, new_n);
		else if (is_array(old_n))
			update_array_entry(old_n, new_n, rename_map);
		else if (is_record(old_n)) {
			tup = SIGNATURE(old_n);
			discr_map = (Tuple) numeric_constraint_discr(tup);
			newsig = tup_new(2);
			numeric_constraint_kind(newsig) = (char *) CONSTRAINT_DISCR;
			nn = tup_size(discr_map);
			newdiscr_map = tup_new(nn);
			for (ii = 1; ii <= nn; ii+=2) {
				newdiscr_map[ii] = (char *) update_new_name(rename_map,
				  (Symbol) discr_map[ii]);
				newdiscr_map[ii+1] = 
				  (char *) update_new_node((Node)discr_map[ii+1]);
			}
			numeric_constraint_discr(newsig) = (char *) newdiscr_map;
			SIGNATURE(new_n) = newsig;
#ifdef TBSL
			-- status of this is undecided
			    misc_type_attributes(new_n) = misc_type_attributes(old_n);
#endif
		}
		else if (is_access(old_n)) {
			newsig = constraint_new(CONSTRAINT_ACCESS);
			newsig[2] = 
			  (char *)update_new_name(rename_map, designated_type(old_n));
			SIGNATURE(new_n) = newsig;
		}
		break;
	case na_enum:
		update_scalar_signature(old_n, new_n);
		/*(literal_map(new_n) := {[new_name(l), i]:
		 * [l, i] in literal_map(old_n)};
		 */
		otup = (Tuple) literal_map(old_n);
		if (otup != (Tuple)0) {
			nn = tup_size(otup);
			ntup = tup_new(nn);
			for (ii = 1; ii <= nn; ii+=2) {
				ntup[ii] = (char *)update_new_name(rename_map,(Symbol)otup[ii]);
				ntup[ii+1] = otup[ii+1];
			}
		}
		else {
			ntup = otup;
		}
		literal_map(new_n) = (Set) ntup;
		break;
	case na_record:
		update_record_entry(old_n, new_n, rename_map);
		break;
	case na_array:
		update_array_entry(old_n, new_n, rename_map);
		break;
	case na_procedure:
	case na_procedure_spec:
	case na_function:
	case na_function_spec:
	case na_literal:
	case na_entry:
		/*signature(new_n) := [new_name(f): f in signature(old_n)];*/
		otup = SIGNATURE(old_n);
		if (otup != (Tuple)0) {
			nn =tup_size(otup);
			ntup = tup_new(nn);
			for (ii = 1; ii <= nn; ii++)
				ntup[ii] = (char *)update_new_name(rename_map,(Symbol)otup[ii]);
			SIGNATURE(new_n) = ntup;
		}
		OVERLOADS(new_n) = update_overloads(OVERLOADS(old_n), rename_map);
		break;
	case na_entry_former:
	case na_entry_family:
		otup = SIGNATURE(old_n);
		if (otup != (Tuple)0) {
			nn = tup_size(otup);
			ntup = tup_new(nn);
			for (ii = 1; ii <= nn; ii++)
				ntup[ii] = (char *)update_new_name(rename_map,(Symbol)otup[ii]);
			SIGNATURE(new_n) = ntup;
		}
		break;
	case na_generic_procedure:
	case na_generic_procedure_spec:
	case na_generic_function:
	case na_generic_function_spec:
		tup = SIGNATURE(old_n);
		gen_list = (Tuple) tup[1];
		form_list = (Tuple) tup[2];
		body_node = (Node) tup[3];
		constrain_list = (Tuple) tup[4];
		/* new_gen_list := [[update_new_name(rename_map, n), 
		 *		     update_new_node(node_map, node)]
		 *		: [n, node] in gen_list];
		 */
		nn = tup_size(gen_list);
		new_gen_list = tup_new(nn);
		FORTUPI(tup=(Tuple), gen_list, ii, ft1);
			n = (Node) tup[1]; 
			node = (Node) tup[2];
			tup =tup_new(2);
			tup[1]= (char *) update_new_name(rename_map, (Symbol) n);
			tup[2] = (char *) update_new_node(node);
			new_gen_list[ii] = (char *) tup;
		ENDFORTUP(ft1);
		/*new_form_list := [replace(n, rename_map): n in form_list];*/
		nn = tup_size(form_list);
		new_form_list = tup_new(nn);
		for (ii = 1; ii <= nn; ii++)
			new_form_list[ii] = 
			  (char *) replace((Symbol) form_list[ii], rename_map);
		/*new_constrain_list := [replace(n, rename_map): n in constrain_list];*/
		nn = tup_size(constrain_list);
		new_constrain_list = tup_new(nn);
		for (ii = 1; ii <= nn; ii++)
			new_form_list[ii] = 
			  (char *) replace((Symbol) constrain_list[ii], rename_map);
		tup = tup_new(4);
		tup[1] = (char *) new_gen_list;
		tup[2] = (char *) new_form_list;
		tup[3] = (char *) update_new_node(body_node);
		tup[4] = (char *) new_constrain_list;
		SIGNATURE(new_n) = tup;
		break;
	case na_task_obj:
	case na_task_obj_spec:
		/* declared map (entry names) is shared with anonymous task type.*/
		DECLARED(TYPE_OF(new_n)) = DECLARED(new_n);
		break;
	case na_generic_package:
	case na_generic_package_spec:
		tup = SIGNATURE(old_n);
		gen_list = (Tuple) tup[1];
		decl_node = (Node) tup[2];
		opt_priv_node = (Node) tup[3];
		body_node = (Node) tup[4];
		constrain_list = (Tuple) tup[5];
		/* new_gen_list := [[update_new_name(rename_map, n), 
		 *		     update_new_node(node_map, node)]
		 *		: [n, node] in gen_list];
		 */
		nn = tup_size(gen_list);
		new_gen_list = tup_new(nn);
		FORTUPI(tup=(Tuple), gen_list, ii, ft1);
			n = (Node) tup[1]; 
			node = (Node) tup[2];
			tup =tup_new(2);
			tup[1]= (char *) update_new_name(rename_map, (Symbol) n);
			tup[2] = (char *) update_new_node(node);
			new_gen_list[ii] = (char *) tup;
		ENDFORTUP(ft1);
		/*new_constrain_list := [replace(n, rename_map): n in constrain_list];*/
		nn = tup_size(constrain_list);
		new_constrain_list = tup_new(nn);
		for (ii = 1; ii <= nn; ii++)
			new_form_list[ii] = 
			  (char *) replace((Symbol) constrain_list[ii], rename_map);
		tup = tup_new(5);
		tup[1] = (char *) new_gen_list;
		tup[2]= (char *) update_new_node(decl_node);
		tup[3] = (char *) update_new_node(opt_priv_node);
		tup[4] = (char *) update_new_node(body_node);
		tup[5] = (char *) new_constrain_list;
		SIGNATURE(new_n) = tup;
		break;
	case na_aggregate:
		OVERLOADS(new_n) = update_overloads(OVERLOADS(old_n), rename_map);
		break;
	case na_access:
		/* update designated type */
		SIGNATURE(new_n) = 
		  (Tuple) update_new_name(rename_map, designated_type(old_n));
		OVERLOADS(new_n) = update_overloads(OVERLOADS(old_n), rename_map);
		break;
	}
	/* verify all uses of signature and overloads are covered*/
}

static void update_scalar_signature(Symbol old_n, Symbol new_n)
  /*update_scalar_signature*/
{
	Tuple  otup,  ntup;
	Symbol old_base, new_base;

	old_base = base_type(old_n);
	new_base = TYPE_OF(new_n);
	otup = SIGNATURE(old_n);
	if (otup != (Tuple)0) {
		ntup = tup_new(tup_size(otup));
		numeric_constraint_kind(ntup) = numeric_constraint_kind(otup);
		numeric_constraint_low(ntup)  = (char *) update_new_node
		  ((Node)numeric_constraint_low(otup));
		numeric_constraint_high(ntup) = (char *) update_new_node
		  ((Node)numeric_constraint_high(otup));

		if ((int)numeric_constraint_kind(otup) == CONSTRAINT_DIGITS) {
			if (is_generic_type(old_base)
			  && N_KIND((Node)numeric_constraint_digits(otup)) != as_ivalue)
				/* inherit digits from generic actual */
				numeric_constraint_digits(ntup) = 
				  numeric_constraint_digits(SIGNATURE(new_base));
			else
				numeric_constraint_digits(ntup)=numeric_constraint_digits(otup);
		}
		else if ((int)numeric_constraint_kind(otup) == CONSTRAINT_DELTA) {
			if (is_generic_type(old_base)
			  && N_KIND((Node)numeric_constraint_delta(otup)) != as_ivalue) {
				/* inherit  generic and small from actual */
				numeric_constraint_delta(ntup) = 
				  numeric_constraint_delta(SIGNATURE(new_base));
				numeric_constraint_small(ntup) = 
				  numeric_constraint_small(SIGNATURE(new_base));
			}
			else {
				numeric_constraint_delta(ntup) = numeric_constraint_delta(otup);
				numeric_constraint_small(ntup) = numeric_constraint_small(otup);
			}
		}
		SIGNATURE(new_n) = ntup;
	}
}

static void update_record_entry(Symbol old_n, Symbol new_n,Symbolmap rename_map)
  /*;update_record_entry*/
{
	Node i_node , v_node;
	Tuple sig, old_disc_list, new_disc_list;
	int  i, disc_size;

	sig = record_declarations(new_n) = tup_new(5);
	i_node = (Node) invariant_part(old_n);
	v_node = (Node) variant_part(old_n);
	sig[1] = (char *) update_new_node(i_node);   /* invariant_part */
	sig[2] = (char *) update_new_node(v_node);   /* variant_part */
	sig[4] = (char *) DECLARED(new_n);           /* declared_components */
	old_disc_list = (Tuple) discriminant_list(old_n);
	disc_size = tup_size(old_disc_list);
	new_disc_list = tup_new(disc_size);
	sig[3] = (char *) new_disc_list;	      /* discriminant_list */
	for (i = 1; i <= disc_size; i++)
		new_disc_list[i] = 
		  (char *) update_new_name(rename_map, (Symbol)old_disc_list[i]);
#ifdef TBSL
	misc_type_attributes(new_n) = misc_type_attributes(old_n);
#endif
}

static void update_array_entry(Symbol old_n, Symbol new_n, Symbolmap rename_map)
  /*;update_array_entry */
{
	Tuple newsig, tup;
	Symbol si;
	int i;
	Fortup  ft;

	/*index_types(new_n) := [new_name(i) : i in index_types(old_n)];*/
	SIGNATURE(new_n) = newsig = tup_new(2);
		tup = tup_new(tup_size(index_types(old_n)));
	FORTUPI(si=(Symbol), (Tuple)index_types(old_n), i, ft);
		tup[i] = (char *) update_new_name(rename_map, si);
	ENDFORTUP(ft);
	newsig[1] = (char *) tup;   			  /* index_types */
	newsig[2] = (char *) update_new_name(rename_map,
	  component_type(old_n));  /* component_type */
#ifdef TBSL
	misc_type_attributes(new_n) = misc_type_attributes(old_n);
#endif
}

static Node update_new_node(Node n)		/*;update_new_node*/
{
	/* transcription of macro new_node in update_one_entry */
	Node	t;

	t = nodemap_get(node_map, n);
	if (t == (Node)0) t = n;
	return t;
}

static Symbol update_new_name(Symbolmap nmap, Symbol s)		/*;update_new_name*/
{
	/* transcription of macro new_name in update_one_entry */
	Symbol	t;

	t = symbolmap_get(nmap, s);
	if (t == (Symbol)0) t = s;
	return t;
}

static void instantiate_derived_types(Node decl_node, Symbolmap rename_map)
  /*;instantiate_derived_types*/
{
	/* derived type declarations whose parent type is a generic type must be
	 * reprocessed, in order to complete the derivation of subprograms from
	 * the instance of the generic formal (AI 398).
	 */

	Symbol gen_p, gen_d, act_p, act_d, act_dt;
	Node   n1, n2;
	Fortup ft1;

	FORTUP(n1=(Node), N_LIST(decl_node), ft1)
	    if (N_KIND(n1) == as_type_decl) n2 = N_AST3(n1);
		else if (N_KIND(n1) == as_subtype_decl) n2 = N_AST2(n1);
		else continue;

		if (N_KIND(n2) == as_derived_type) {
			gen_d = N_UNQ(N_AST1(n1));         /* derived type in template */
			gen_p = N_UNQ(N_AST1(N_AST1(n2))); /* parent  type in template */
			if (is_generic_type(gen_p) && SCOPE_OF(gen_d) == SCOPE_OF(gen_p))
			{
				act_d = update_new_name(rename_map, gen_d);
				act_p = update_new_name(rename_map, gen_p);

				if (NATURE(gen_d) == na_type && NATURE(act_p) == na_subtype) {
					/* if formal has no constraint, but actual is a subtype,
					 * must first derive anonymous type, of which the
					 * instantiation of the name appearing in the type
					 * declaration is a subtype.
 		 			 */
					act_dt = sym_new(na_void);	/*anonymous derived type */
					dcl_put_vis(DECLARED(scope_name),newat_str(), act_dt, TRUE);
					NATURE(act_d)  = na_subtype;
					TYPE_OF(act_d) = act_dt;
				}
				else
					act_dt = base_type(act_d);
				ALIAS(act_d)	 = ALIAS(act_p);
				SIGNATURE(act_d)  = SIGNATURE(act_p);
				SIGNATURE(act_dt) = SIGNATURE(act_p);
				/* For now do not create derived programs. */
				/*  build_derived_type(act_p, act_dt, current_node); */
			}
		}
	ENDFORTUP(ft1);
}

static Set update_overloads(Set oset, Symbolmap rename_map)
  /*;update_overloads*/
{
	Set nset;
	Forset fs1;
	Symbol si;

	nset = (Set)0;
	if (oset != (Set)0) {
		nset = set_new(set_size(oset));
		FORSET(si=(Symbol), oset, fs1);
			nset = set_with(nset, (char *) update_new_name(rename_map, si));
		ENDFORSET(fs1);
	}
	return nset;
}

Private_declarations update_private_decls(Symbol pack_name,
  Symbolmap rename_map)							 /*;update_private_decls*/
{
	/* Complete the instantiation of the private declarations of a package.
	 * The	same renaming rules apply as  for visible symbol table entries.
	 * We install each private declaration in the  symbol table, update the
	 * information, and swap back.
	 */

	Private_declarations  old_decls, new_decls;
	Forprivate_decls	fp;
	Symbol	old_n, info, new_n, save_new;

	new_decls = private_decls_new(0);
	/* TBSL:
	 * -- this involves more than swapping, need to copy entries as appropiate
	 * -- ds  9 nov 84
	*/

	/*(forall [old_n, info] in private_decls(pack_name))*/
	old_decls = (Private_declarations) private_decls(pack_name);
	FORPRIVATE_DECLS(old_n, info, old_decls, fp);
		new_n = symbolmap_get(rename_map, old_n);
		if (new_n == (Symbol)0)  continue;	/* some error. */

#ifdef TBSN
[save_old, save_new] :
	= [SYMBTABF(old_n), SYMBTABF(new_n)];
	SYMBTABF(old_n) :
	= info;
#endif
		save_new = sym_new_noseq(na_void);
		sym_copy(save_new, new_n);
		update_one_entry(info, new_n, rename_map);
		NATURE(new_n) = NATURE(info);  /* maybe different from visible decl */
		SCOPE_OF(new_n)  = symbolmap_get(rename_map, pack_name);
#ifdef TBSN
	new_decls(new_n) :
	= SYMBTABF(new_n);
[SYMBTABF(old_n), SYMBTABF(new_n)] :
	= [save_old, save_new];
#endif
		private_decls_put(new_decls, new_n);
		sym_copy(new_n, save_new);
	ENDFORPRIVATE_DECLS(fp);
	return new_decls;
}

Node instantiate_tree(Node node, Symbolmap rename_map) /*;instantiate_tree*/
{
	/*
	 * Makes a copy of the tree rooted at node, while replacing occurences
	 * of names in domain rename_map by corresponding values. If the
	 * instantiation contains an inner forward instantiation, the renaming 
	 * map of the inner one must be combined with the outer one. 
	 */

	Node	root;
	Symbol	dnode, rnode;
	Tuple	tup, ltup, ntup;
	Symbolmap	new_r_map, r_map;
	Forsymbol	fsym;
	int		i, ni, n;
	unsigned int nkind;
	Node	anode, nnode;
	Fortup	ft1;
	Symbol	old_n, new_n;

	if (node == OPT_NODE ) return OPT_NODE;
	nkind = N_KIND(node);
	root = node_new(nkind);
	/*N_VAL(root) = N_VAL(node);  very delicate code - 3-20-86  DS */
	if (N_VAL_DEFINED(nkind)) N_VAL (root) = N_VAL (node);
	if (is_terminal_node(nkind) && current_node != OPT_NODE)
		copy_span(current_node, root);

	if (nkind == as_function_instance 
	  || nkind == as_procedure_instance 
	  || nkind == as_package_instance) {
		/* Update the instantiation information.*/
		tup = tup_copy((Tuple) N_VAL(N_AST4(node)));
		r_map = (Symbolmap) tup[1];
		/* TBSL: should set better size for new_r_map on init. alloc.*/
		/*
		 * new_r_map := { [old_n, rename_map(new_n) ? new_n]:
		 *				[old_n, new_n] in r_map};
		 */
		new_r_map = symbolmap_new();
		FORSYMBOL(old_n, new_n, r_map, fsym);
			symbolmap_put(new_r_map, old_n, replace(new_n, rename_map));
		ENDFORSYMBOL(fsym);
		/*N_VAL(root)  := [new_r_map, flag]; */
		tup[1] = (char *) new_r_map;
		N_AST4(root) = new_instance_node(tup);

		/* And check that no recursive instantiations are implied by
		 *  the current inner one.
		 */
		check_recursive_instance(node);
	}
	/*N_UNQ (root) = symbolmap_get(rename_map, N_UNQ(node))  ? N_UNQ(node);*/
	dnode = N_UNQ(node);
	rnode = symbolmap_get(rename_map, dnode);
	if (rnode == (Symbol)0) rnode = dnode;
	if (nkind == as_array_aggregate || nkind == as_record_aggregate) {
		/* the internally generated name of the aggregate is not in the
		 * symbol table, for delicate separate compilation reasons. Each
		 * aggregate instance must nevertheless have a distinct name
		 */
		rnode = sym_new(na_void);
	}
	if (N_UNQ_DEFINED(N_KIND(root)))
		N_UNQ(root) = rnode;
	/*N_TYPE(root) := symbolmap_get(rename_map, N_TYPE(node)) ? N_TYPE(node);*/
	dnode= N_TYPE(node);
	rnode = symbolmap_get(rename_map, dnode);
	if (rnode == (Symbol)0) rnode = dnode;
	if (N_TYPE_DEFINED(N_KIND(root)))
		N_TYPE(root) = rnode;
	N_SIDE(root) = N_SIDE(node);
	/* N_AST (root) := [instantiate_tree(n, rename_map): 
	 * 	n in N_AST(node)  ? []];
	 */
	for (ni = 1; ni <= 4; ni++) {
		anode = (Node)0;
		if (ni == 1 && N_AST1_DEFINED(nkind)) anode =N_AST1(node);
		else if (ni == 2 && N_AST2_DEFINED(nkind)) anode = N_AST2(node);
		else if (ni == 3 && N_AST3_DEFINED(nkind)) anode = N_AST3(node);
		else if (ni == 4 && N_AST4_DEFINED(nkind)) {
			anode = N_AST4(node);
			if (N_KIND(anode) == as_instance_tuple) continue;
			/* treated above as special case in instance nodes */
		}
		if (anode == (Node)0) continue;
		nnode = instantiate_tree(anode, rename_map);
		if (anode != (Node)0) {
			if (ni == 1) N_AST1(root) = nnode;
			else if (ni == 2) N_AST2(root) = nnode;
			else if (ni == 3) N_AST3(root) = nnode;
			else if (ni == 4) N_AST4(root) = nnode;
		}
	}
	if (N_LIST_DEFINED(nkind))
		ltup = N_LIST(node);
	else
		ltup = (Tuple)0;
	if (ltup != (Tuple)0) {
		/* N_LIST(root) := [instantiate_tree(n, rename_map): 
		 * 	n in N_LIST(node) ? []];
		 */
		n = tup_size(ltup);
		ntup = tup_new(n);
		FORTUPI(nnode=(Node), ltup, i, ft1);
			ntup[i] = (char *)instantiate_tree(nnode, rename_map);
		ENDFORTUP(ft1);
		N_LIST(root) = ntup;
	}
/*
 * In the case of a slice, the procedure slice_type reformats the as_slice node.
 * The lower and upper bounds nodes of the as_range are incorporated into
 * an anonymous subtype (slice_index_type). The N_AST2 of the as_slice node 
 * points to a new name node with this slice_index_type as its N_UNQ. As a
 * conseqeunce of this reformatting the bounds nodes are no longer connected
 * to the tree rooted by the as_slice node and are left out when tranversing
 * the tree in instantiate_tree. Threfore, a special check is made in this
 * case to instantiate the bound nodes as well.
 */
	if ((nkind == as_slice) && (N_KIND(N_AST2(node)) == as_simple_name)) {
		tup = SIGNATURE(N_UNQ(N_AST2(node)));
		nnode = instantiate_tree((Node)numeric_constraint_low(tup),rename_map);
		nnode = instantiate_tree((Node)numeric_constraint_high(tup),rename_map);
	}
	nodemap_put(node_map, node, root);
	return root;
}

static int check_recursive_instance(Node node)	/*;check_recursive_instance*/
{
	/* Verify that an instance appearing in the current instantiation does
	 * not include an  instantiation of the	 unit being instantiated. we
	 * use current_instances to keep track of units already seen.
	 */

	Node	specs_node, priv_node, body_node;
	Node	gen_node;
	Symbol	nam;
	int		nat;
	Tuple	sig;
	Node	body;

	gen_node = N_AST2(node);
	nam = N_UNQ(gen_node);
	if (tup_memsym(nam, current_instances)) {
		errmsg("Invalid recursive instantiation", "12.3", current_node);
		return TRUE;
	}
	else {
		current_instances = tup_with(current_instances, (char *) nam );
		nat = NATURE(nam);
		if (nat == na_generic_procedure || nat == na_generic_function) {
			sig = SIGNATURE(nam);
			body = (Node) sig[3];
			if (scan_instance(body)) return TRUE;
		}
		else if (nat == na_generic_package_spec) {
			sig = SIGNATURE(nam);
			specs_node = (Node)sig[2];
			priv_node = (Node) sig[3];
			if (scan_instance(specs_node)) return TRUE;
			if (scan_instance(priv_node)) return TRUE;
		}
		else if (nat == na_generic_package) {
			sig = SIGNATURE(nam);
			specs_node = (Node) sig[2];
			priv_node = (Node) sig[3];
			body_node = (Node) sig[4];
			if (scan_instance(specs_node)) return TRUE;
			if (scan_instance(priv_node)) return TRUE;
			if (scan_instance(body_node)) return TRUE;
		}
		nam = (Symbol) tup_frome(current_instances );
	}
	return FALSE;
}

static int scan_instance(Node node) 					/*;scan_instance */
{
	/* Subsidiary procedure to  the above:	search the specs or body of a
	 * generic  object, for the presence  of forward instantiations, i.e.
	 * instantiations that preceded the body of the	 generic. Non-trivial
	 * recursive instantiations  can only  occur in the presence of such.
	 */

	int	i, nkind;
	Fortup	ft1;
	Node	inode;

	if ( N_KIND(node) == as_function_instance
	  || N_KIND(node) == as_procedure_instance 
	  || N_KIND(node) == as_package_instance)
		if (check_recursive_instance(node)) return TRUE;
	else {
		nkind = N_KIND(node);
		for (i = 1; i <= 4; i++) {
			inode = (Node)0;
			if (i == 1 && N_AST1_DEFINED(nkind)) inode = N_AST1(node);
			else if (i == 2 && N_AST2_DEFINED(nkind)) inode = N_AST2(node);
			else if (i == 3 && N_AST3_DEFINED(nkind)) inode = N_AST3(node);
			else if (i == 4 && N_AST4_DEFINED(nkind)) inode = N_AST4(node);
			if (inode != (Node)0)
				if (scan_instance(inode)) return TRUE;
		}
		if (N_LIST_DEFINED(nkind) && N_LIST(node) != (Tuple)0) {
			FORTUP(inode=(Node), N_LIST(node), ft1);
				if (scan_instance(inode)) return TRUE;
			ENDFORTUP(ft1);
		}
	}
	return FALSE;
}

Symbol replace(Symbol expn, Symbolmap mapping)		/*;replace*/
{
	Symbol sym;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  replace");

	sym = symbolmap_get(mapping, expn);
	if (sym != (Symbol)0)
		return sym;
	else return expn;
}

Symbolmap symbolmap_new()		/*;symbolmap_new*/
{
	/* initialize symbolmap for n entries */

	Symbolmap	smap;

	smap = (Symbolmap) emalloct(sizeof(struct Symbolmap_s), "symbolmap-new");
	smap->symbolmap_tuple = tup_new(0);
	return smap;
}

Symbol symbolmap_get(Symbolmap type_map, Symbol sym)	/*;symbolmap_get*/
{
	int	i, n;
	Tuple	tup;

	tup = type_map->symbolmap_tuple;
	n = tup_size(tup);
	for (i = 1; i <= n; i+=2)
		if (tup[i] == (char *)sym)
			return (Symbol) tup[i+1];
	/* symbolmap_get returns (Symbol)0 if map undefined */
	return (Symbol) 0;
}

void symbolmap_put(Symbolmap type_map, Symbol symd, Symbol symv)
  /*;symbolmap_put*/
{
	int	i, n;
	Tuple	tup;

	tup = type_map->symbolmap_tuple;
	n = tup_size(tup);
	for (i = 1; i <= n; i+=2) {
		if (tup[i] == (char *)symd) {
			tup[i+1] = (char *)symv;
			return;
		}
	}
	/* here if need to extend map. */
	tup = tup_exp(tup, (unsigned) (n+2));
	type_map->symbolmap_tuple = tup;
	tup[n+1] = (char *)symd;
	tup[n+2] = (char *)symv;
	return;
}

Nodemap nodemap_new()									/*;nodemap_new*/
{
	/* initialize nodemap for n entries */

	Nodemap	nmap;

	nmap = (Nodemap) emalloct(sizeof(struct Nodemap_s), "nodemap-new");
	nmap->nodemap_tuple = tup_new(0);
	return nmap;
}

static void nodemap_free(Nodemap smap)		/*;nodemap_free*/
{
	tup_free(smap->nodemap_tuple);
	efreet((char *) smap, "node-map-free");
}

static Node nodemap_get(Nodemap node_map, Node sym)	/*;nodemap_get*/
{
	int	i, n;
	Tuple	tup;

	tup = node_map->nodemap_tuple;
	n = tup_size(tup);
	for (i = 1; i <= n; i+=2)
		if (tup[i] == (char *)sym)
			return (Node) tup[i+1];
	return (Node)0;
}

static void nodemap_put(Nodemap node_map, Node symd, Node symv) /*;nodemap_put*/
{
	int	i, n;
	Tuple	tup;

	tup = node_map->nodemap_tuple;
	n = tup_size(tup);
	for (i = 1; i <= n; i+=2) {
		if (tup[i] == (char *)symd) {
			tup[i+1] = (char *)symv;
			return;
		}
	}
	/* here if need to extend map. */
	tup = tup_exp(tup, (unsigned) n+2);
	node_map->nodemap_tuple = tup;
	tup[n+1] = (char *)symd;
	tup[n+2] = (char *)symv;
	return;
}
