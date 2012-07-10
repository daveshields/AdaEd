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
#include "errmsgprots.h"
#include "dclmapprots.h"
#include "libprots.h"
#include "miscprots.h"
#include "unitsprots.h"
#include "nodesprots.h"
#include "smiscprots.h"
#include "chapprots.h"
/* TBSL: check that check_priv_decl always called with first
	argument (kind) as integer, corresponding to MISC_TYPE_ATTRIBUTE...
 */

static int in_relevant_scopes(int);
static Symbol trace_ancestor(Symbol, Tuple);
static void private_part(Node);

void package_specification(Node node)	/*; package specification */
{
	Node	id_node, decl_node, priv_node;

	id_node   = N_AST1(node);
	decl_node = N_AST2(node);
	priv_node = N_AST3(node);
	new_package(id_node, na_package_spec);
	package_declarations(decl_node, priv_node);
	end_specs(N_UNQ(id_node));
}

void new_package(Node id_node, int nat)	/*;new_package*/
{
	/* Process a  package specification: install scope, initialize  mappings. */

	char	*id;
	Symbol	ud;
	int		body_number;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  new_package");

	id = N_VAL(id_node);
	new_compunit("sp", id_node);
	if (nat==na_generic_part && IS_COMP_UNIT) {
			/* allocate unit number for body, and mark it obsolete */
			body_number = unit_number(strjoin("bo", id));
			pUnits[body_number]->libInfo.obsolete = string_ds; /*"$D$"*/
	}
	newmod(id);

	N_UNQ(id_node) = scope_name;
	NATURE(scope_name)  = nat;
	TYPE_OF(scope_name) = symbol_none;
	/* Create dummy entry to hold use clauses, which are declarative items.*/
	find_new("$used");
	/* use_declarations in SETL is signature(declared(scope_name), '$used') */
	ud = dcl_get(DECLARED(scope_name), "$used");
	SIGNATURE(ud) = tup_new(0);
	private_decls(scope_name) = (Set) private_decls_new(0);
}

void package_declarations(Node decl_node, Node priv_node)
													/*;package_declarations */
{
	char	*str;
	Symbol	s1, u_name;
	Fordeclared dcliv;

	adasem(decl_node);
	/* The declarations so far constitute the visible part of the package*/
	/* save current declarations */
	/*    visible(scope_name) = declared(scope_name); */
	FORDECLARED(str, s1, DECLARED(scope_name), dcliv);
		IS_VISIBLE(dcliv) = TRUE;
	ENDFORDECLARED(dcliv);

	FORDECLARED(str, u_name, DECLARED(scope_name), dcliv)
	    if (TYPE_OF(u_name) == symbol_incomplete) {
		errmsg_id("missing full declaration for %", u_name, "3.8.1", decl_node);
		}
	ENDFORDECLARED(dcliv);
	/* Now process private part of package.*/
	private_part(priv_node);
}

void module_body_id(int mod_nature, Node name_node)  /*;module_body_id*/
{
	/* This procedure is invoked when the name of a module body has been
	 * seen. It opens the new scope, and if necessary retrieves from the
	 * library the specifications for the module.
	 */

	Symbol	mod_name, c, real_t;
	char	*spec_name;
	int	nat, mattr, mark;
	char	*id;
	Symbol	s1, s2, t;
	Fordeclared	fd1;
	Forprivate_decls	fp1;
	Private_declarations	pd;
	Tuple	ud;
	Symbol	uds; /* check tupe of this	ds 4 aug */
	Fortup	ft1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  module_body_id");

	new_compunit("bo", name_node);

	find_old(name_node);
	mod_name = N_UNQ(name_node);
	if (!IS_COMP_UNIT && SCOPE_OF(mod_name) != scope_name) {
		errmsg("Specification and body are in different scopes" , "7.1, 9.1",
		  name_node);
	}

	/* Nature of specification must match that of current body*/

	/*
	 * const specs_of = { 
	 * 	[na_package, {na_package_spec, na_generic_package_spec}],
	 * 	[na_task_type, {na_task_type_spec, na_task_obj_spec}] };
	 * if (NATURE(mod_name) in specs_of(mod_nature) ) {
     * 	rmatch(nature(mod_name), '_spec');		$ not a spec any longer 
	 * }
	 */
	nat = NATURE(mod_name);
	if (mod_nature == na_package
	  && (nat == na_package_spec || nat == na_generic_package_spec)
	  || (mod_nature == na_task_type && (nat == na_task_type_spec
	  || nat == na_task_obj_spec 
	  || (nat == na_obj && NATURE(TYPE_OF(mod_name)) == na_task_type_spec)))) {
		/* if the task appeared in a previously (separately) compiled unit,
 		 * the expander has already changed its nature to na_obj
	 	 */
		if (nat == na_package_spec) nat = na_package;
		else if (nat == na_generic_package_spec)
			nat = na_generic_package;
		else if (nat == na_task_type_spec)
			nat = na_task_type;
		else if (nat == na_task_obj_spec)
			nat = na_task_obj;
		else if (nat == na_obj)
			NATURE(TYPE_OF(mod_name)) = na_task_type;

		NATURE(mod_name) = nat;
	}
	else {
		errmsg_nval("Matching specification not found for body %", name_node,
		  "7.1, 9.1", name_node);
	}

	/* if module is a generic package body and the current unit is a package
	 * body, verify that the generic spec appeared in the same file.
	 */
	if (NATURE(mod_name) == na_generic_package 
	  && streq(unit_name_type(unit_name), "bo")) {
		if (is_subunit(unit_name))
			spec_name = pUnits[stub_parent_get(unit_name)]->name;
		else
			spec_name = strjoin("sp", unit_name_name(unit_name));
		if (!streq(lib_unit_get(spec_name), AISFILENAME))
			errmsg("Separately compiled generics not supported", "none",
			  name_node);
	}

	newscope (mod_name);	/* added to match SETL	gcs 23 jan */
	if (private_decls(mod_name) == (Set)0)
		private_decls(mod_name) = (Set) private_decls_new(0);
	/* For safe processing of body.*/
	if (DECLARED(mod_name) == (Declaredmap)0)
		DECLARED(mod_name) = dcl_new(0);

	if (NATURE(mod_name) == na_task_type ) {
		/* Within the body of a task type, the name of the task can be used 
		 * to designate the task currently executing the body. We create an 
		 * alias to be elaborated at run-time, under the name 'current_task'.
		 */
		c = find_new(strjoin("", "current_task"));
		TYPE_OF(c) = mod_name;
		NATURE(c) = na_obj;
	}
	else if (NATURE(mod_name) == na_task_obj ) {
		/* remove -spec marker from its anonymous task type as well.*/
		NATURE(TYPE_OF(mod_name)) = na_task_type;
	}
	else if (mod_nature == na_package ) {
		/* Within a package body, declarations from the private part of the
		 * specification are	 visible. Swap	visible and  private versions.
		 */
		pd = (Private_declarations) private_decls(mod_name);
		FORPRIVATE_DECLS(s1, s2, pd, fp1);
			private_decls_swap(s1, s2);
		ENDFORPRIVATE_DECLS(fp1);
		/* (forall [item, pdecl] in private_decls(mod_name))
		 * [SYMBTABF(item), private_decls(mod_name)(item)] :=
		 * [pdecl, SYMBTABF(item)];	
		 * end forall;
		 */
		/* Furthermore, composite types that depend on (outer) private types
		 * may now be fully useable if the latter received full declarations,
		 * (as long as they do not depend in external private types...)
		 */
		FORDECLARED(id, t, DECLARED(mod_name), fd1);
			if (NATURE(t) == na_package_spec && !tup_mem((char *) t, vis_mods) )
				vis_mods = tup_with(vis_mods, (char *) t);
			else if (! is_type(t)) continue;
			mattr = (int) misc_type_attributes(t);
			mark = 0;
			if (mattr & TA_PRIVATE)
				mark = TA_PRIVATE;
			else if (mattr & TA_LIMITED_PRIVATE)
				mark = TA_LIMITED_PRIVATE;
			/* exclude the mark 'limited' from this test (gs apr 1 85) */
			/* else if (mattr & TA_LIMITED)
			 * mark = TA_LIMITED;
			 */
			else if (mattr & TA_INCOMPLETE)
				mark = TA_INCOMPLETE;
			if (mark == 0) continue;
			if (is_access(t)) real_t = (Symbol) designated_type(t);
			else real_t = t;

			if (!is_private(real_t) ) {
				/* full declaration  of private ancestor(s) has been seen.
				 * save visible declaration before updating.
				 */
				private_decls_put((Private_declarations)
				  private_decls(mod_name), t);
				misc_type_attributes(t) = (misc_type_attributes(t) & ~mark );
			}
		ENDFORDECLARED(fd1);
		/* and install the use clauses that were encountered in the
		 * specification.
		 */
		uds = dcl_get(DECLARED(mod_name), "$used");
		if ( uds != (Symbol)0 ) {
			ud = SIGNATURE(uds);
			FORTUP(uds=(Symbol), ud, ft1);
				used_mods = tup_with(used_mods, (char *) uds);
			ENDFORTUP(ft1);
		}
		/* Else the body was not found. Error was emitted already.*/
	}

	/* Initialize the stacks used for label processing.*/
	lab_init();
}

void module_body(int nat, Node block_node)	/*;module_body*/
{

	Symbol	mod_name, scope;
	char	*spec_name;
	Tuple		specs, nodes, context;
	Node	decls, stats, except, id_node;
	Symbol	u_name;
	Tuple	tup;
	int	i;
	Symbol	s1, s2;
	Forprivate_decls	fp1;
	Private_declarations	pd;
	Fordeclared		fd1;
	Fortup			ft1;
	Tuple		scopes, must_constrain;
	Unitdecl	ud;
	char	*utnam;
	char	*did;
	Symbol	t_name, unit_unam;
	Tuple	old_vis;
	int	scopei;
	Tuple	decmaps, decscopes, gen_list;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  module_body");

	mod_name = scope_name;
	decls = N_AST2(block_node);
	stats = N_AST3(block_node);
	except = N_AST4(block_node);
	/* Each task type can refer to an instance of itself; dynamically,
	 * such an instance is constructed under the name 'current_task'. We
	 * introduce a declaration for a dummy task object with taht name.
	 */
	if (NATURE(mod_name) == na_task_type) {
		id_node = node_new(as_simple_name);
		N_VAL(id_node) = strjoin("", "current_task");
		find_old(id_node);
		N_KIND(id_node) = as_current_task;
		copy_span(N_AST1(block_node), id_node);
#ifdef TBSN
		SPANS(id_node)	= [left_span(decls)];
#endif
		/*N_LIST(decls) := [id_node] + N_LIST(decls) */
		tup = N_LIST(decls);
		tup = tup_exp(tup, (unsigned) tup_size(tup)+1);
		for (i=tup_size(tup);i>1;i--)
			tup[i] = tup[i-1];
		tup[1] = (char *) id_node;
		N_LIST(decls) = tup;
	}

	lab_end();
	check_incomplete_decls(mod_name, block_node);
	popscope()	;
	/* Having finished the module body, we now restore the visible
	 * declarations saved in module_body_id (If it is a package).
	 */
	if (nat == na_package  || nat == na_generic_package) {
		pd = (Private_declarations) private_decls(mod_name);
		FORPRIVATE_DECLS(s1, s2, pd, fp1);
			private_decls_swap(s1, s2);
		ENDFORPRIVATE_DECLS(fp1);
	}

	if (NATURE(mod_name) == na_generic_package) {
		/* We must update the declarations for the current unit, to
		 * include  the generic body. This  can be  done  omly if the
		 * generic  specification appears in the current compilation,
		 * which is a restriction on the current  implementation that
		 * will be lifted some day.
		 * For purposes of generic instantiation, we must save not only
		 * the visible part of the package, but all declarations in the
		 * body as well, including declarations	 for nested non-generic
		 * objects. This parallels what is done at the point of instan-
		 * tiation. 
		 *
		 * Replace the opt_node that marks the place of the body in the 
		 * generic spec, with the body node.
		 * Set fifth component of signature to tuple of generic private types
		 * that must be constrained upon instantiation.
		 */

		SIGNATURE(mod_name)[4] = (char *) block_node;
		gen_list = (Tuple) SIGNATURE(mod_name)[1];
		must_constrain = tup_new(0);
		FORTUP(tup=(Tuple), gen_list, ft1)
		    t_name = (Symbol)tup[1];
			if ((int)misc_type_attributes(t_name) & TA_CONSTRAIN)
				must_constrain=tup_with(must_constrain, (char *)t_name);
		ENDFORTUP(ft1);
		SIGNATURE(mod_name)[5] = (char *) must_constrain;

		utnam = unit_name_type(unit_name);
		if (IS_COMP_UNIT) {
			pUnits[unit_number(unit_name)]->libInfo.obsolete = string_ok;
#ifdef IBM_PC
			pUnits[unit_number(unit_name)]->libInfo.obsolete = strjoin("ok", "");
#endif
		}
		if (streq(utnam, "bo") || streq(utnam, "su")
		  && streq(unit_name_name(unit_name), unit_name_names(unit_name)) ){
			spec_name = strjoin("sp", unit_name_name (unit_name));
			if (lib_unit_get(spec_name) != (char *)0
			  && streq(lib_unit_get(spec_name) , AISFILENAME)
			  && unit_decl_get(spec_name)!=(Unitdecl)0 ) {
				/* Unpack unit specification.*/
				ud = unit_decl_get(spec_name);
				unit_unam = ud->ud_unam;
				/*specs = utup[5];*/
				specs = ud->ud_symbols;
				decscopes = ud->ud_decscopes;
				old_vis = ud->ud_oldvis;
				decmaps = ud->ud_decmaps;
				scopes = tup_new1((char *) mod_name);
				nodes = ud->ud_nodes;
				context =ud->ud_context;

				/*  Update the specs of generic types, that may carry the
				 * marker "$constrain', because of usage in body.
				 */
				FORDECLARED(did, t_name, DECLARED(mod_name), fd1);
					if( is_generic_type(t_name))
						/*specs(t_name) := SYMBTABF(t_name);*/
						specs = sym_save(specs, t_name, 'u');
				ENDFORDECLARED(fd1);
				while (tup_size(scopes) >0) {
					scope =(Symbol) tup_frome(scopes);

					/*specs(scope)  = SYMBTABF(scope);*/
					specs = sym_save(specs, scope, 'u');
					scopei = tup_memi((char *) scope, decscopes);
					if (scopei == 0) {
						decscopes = tup_exp(decscopes,
						  (unsigned) tup_size(decscopes)+1);
						decmaps = tup_exp(decmaps,
						  (unsigned) tup_size(decmaps)+1);
						scopei = tup_size(decscopes);
						decscopes[scopei] = (char *) scope;
					}
					decmaps[scopei] = (char *) dcl_copy(DECLARED(scope));
					/* body_decls	  = declared(scope) -
					 *   (visible(scope) ? {});
					 * notvis(scope) = body_decls;
					 */
					/* TBSL: Review following when do generics	ds 1 aug */
					/*(forall [-, u_name] in body_decls)*/
					FORDECLARED(did, u_name, DECLARED(scope), fd1);
						if (IS_VISIBLE(fd1)) continue;
						/*specs(u_name) := SYMBTABF(u_name);*/
						specs = sym_save(specs, u_name, 'u');

						if (DECLARED(u_name) != (Declaredmap)0
					      && ! can_overload(u_name)
					      && NATURE(u_name) != na_generic_package)
							/* Contains further collectible decls.*/
							if (!tup_mem((char *) u_name, scopes))
								scopes = tup_with(scopes, (char *) u_name);
					ENDFORDECLARED(fd1);
				}
				/*specs(mod_name) := SYMBTABF(mod_name);*/
				specs = sym_save(specs, mod_name, 'u');
				/* Repackage the unit's information.*/
				/* UNIT_DECL(spec_name) :=
				 * [unit_unam, specs, decmap, old_vis, notvis, context,
				 * nodes with block_node];
				 */
				ud = unit_decl_get(spec_name);
				if (ud == (Unitdecl)0) ud = unit_decl_new();
				/* TBSL see if tup_copy's needed before saving tuples in utup */
				ud->ud_unam = unit_unam;
				ud->ud_useq = S_SEQ(unit_unam);
				ud->ud_unit = S_UNIT(unit_unam);
				ud->ud_symbols = specs;
				ud->ud_decscopes = decscopes;
				ud->ud_oldvis = old_vis;
				ud->ud_decmaps = decmaps;
				ud->ud_context = tup_copy(context);
				ud->ud_nodes = tup_with(nodes, (char *) block_node);
				unit_decl_put(spec_name, ud);
			}
			else if (IS_COMP_UNIT) {
				/* Repackage as a specification. */

				newscope(mod_name);	/* For end_specs*/
				end_specs(mod_name);
			}
		}
	} /* end if na_generic_package() */

	if (nat != na_task) save_body_info(mod_name);
}

void private_decl(Node node)	/*;private_decl*/
{
	char	*id, *priv_kind_str;
	Symbol	name, priv_kind;
	Node	id_node, opt_discr, priv_kind_node;
	int	nat;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  private_decl");

	id_node = N_AST1(node);
	opt_discr = N_AST2(node);
	priv_kind_node = N_AST3(node);

	id = N_VAL(id_node);
	sem_list(opt_discr);
	priv_kind_str = N_VAL(priv_kind_node);
	if (streq(priv_kind_str, "private"))
		priv_kind = symbol_private;
	else if (streq(priv_kind_str, "limited_private"))
		priv_kind = symbol_limited_private;
	else {
		printf("private_decl: invalid priv_kind_str %s\n",
		    priv_kind_str);
		chaos("bad priv_kind_str");
	}

	if (dcl_get(DECLARED(scope_name), id) == (Symbol)0) {
		name = find_new(id);
		TYPE_OF(name) = priv_kind;
		root_type(name) = name;
		newscope(name);
		process_discr(name, opt_discr);
		NATURE(name) = na_type;
        /*initialize_representation_info(name, TAG_RECORD);*/
		/* This should be private_dependents (in SETL, it is the same as 
		 *   misc_type_attributes)
		 *   misc_type_attributes(name) = 0; 
		 */
		private_dependents(name) = set_new(0);
		popscope();

		nat = NATURE(scope_name);
		if (nat!=na_package_spec && nat !=na_generic_package_spec
		  && nat!=na_generic_part) {
			errmsg("Invalid context for private declaration", "7.4, 12.1.2",
			  node);
		}
	}
	else{
		errmsg("Invalid redeclaration ", "8.2", id_node);
		name = symbol_any;
	}

	N_UNQ(id_node) = name;
}

void check_fully_declared(Symbol type_mark)			/*;check_fully_declared*/
{
	/* Called from object and constant declarations, to ensure that a
	 * private or incomplete type is not used in a declaration before its
	 * full declaration has been seen.
	 */

	Symbol	t;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  check_fully_declared");

	t = base_type(type_mark);

	if (TYPE_OF(t) == symbol_incomplete || private_ancestor(t) != (Symbol)0) {
		errmsg_id("invalid use of type % before its full declaration",
		  type_mark, "3.8.1, 7.4.1", current_node);
	}
	/* If the type is a generic private type, and is used as an unconstrained
	 * subtype indication, note that its instantiations will have to be
	 * with a constrained type.
	 */
	check_generic_usage(type_mark);
}

void check_fully_declared2(Symbol type_mark)		/*;check_fully_declared2*/
{
	/* Called from array element and component declarations, to ensure that
	 * an incomplete type is not used in a declaration before its
	 * full declaration has been seen.
	 */

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  check_fully_declared2");

	check_incomplete(type_mark);
	check_generic_usage(type_mark);
}

int is_private(Symbol type_mark)							/*;is_private*/
{
	/* Determine whether a type has a private subcomponent. This differs
	 * from what is done in private_ancestor, where only incomplete priv.
	 * subcomponents are of interest.
	 */

	Fordeclared	fd1;
	char		*id;
	Symbol		comp;

	if (in_priv_types(TYPE_OF(base_type(type_mark))) ) return TRUE;
	if (in_priv_types(TYPE_OF(root_type(type_mark))) ) return TRUE;
	if (is_array(type_mark) && is_private(component_type(type_mark)))
		return TRUE;

	if (is_record(type_mark)) {
		FORDECLARED(id, comp ,
		  (Declaredmap) declared_components(base_type(type_mark)), fd1)
		    if (is_private(TYPE_OF(comp)) ) return TRUE;
		ENDFORDECLARED(fd1);
		return FALSE;
	}
}

int is_limited_type(Symbol type_mark)	/*;is_limited_type*/
{
	/* A type is limited if its root type is a limited private type or a task
	 * type, or if it is a composite type some of whose components are limit-
	 * ted. The attributes 'limited' and 'limited private' are attached to
	 * such composite types when they are created by a definition, derivation
	 * or subtype declaration.
	 */

	Fordeclared	fd1;
	int	mt;
	char	*id;
	Symbol	comp;

	if (TYPE_OF(base_type(type_mark)) == symbol_limited_private) return TRUE;
	if (TYPE_OF(root_type(type_mark)) == symbol_limited_private) return TRUE;
	if (is_task_type(type_mark)) return TRUE;

	mt = (int) misc_type_attributes(type_mark);

	if ((mt & TA_LIMITED) && (! is_access(type_mark))) return TRUE;

	if ((mt & TA_LIMITED_PRIVATE) == 0)	 return FALSE;
	if (! in_open_scopes(SCOPE_OF(type_mark) ) && ! is_access(type_mark))
		return TRUE;
	if (is_array(type_mark) &&	is_limited_type(component_type(type_mark)))
		return TRUE;
	if (is_record(type_mark) == FALSE) return FALSE;
	FORDECLARED(id, comp, 
	  (Declaredmap)declared_components(base_type(type_mark)), fd1)
	    if (is_limited_type(TYPE_OF(comp)) )  return TRUE;
	ENDFORDECLARED(fd1)
	return FALSE;
}

void check_out_parameters(Tuple formals) 			/*;check_out_parameters */
{
	/*  enforce restrictions on usage of out formal parameters given in
	 *  LRM 7.4.4
	 */

	Symbol type_mark, scope;
	Fortup ft;
	int  nat, mode;
	Tuple tup;

	FORTUP(tup=(Tuple), formals, ft);
		mode = (int)tup[2];
		type_mark = (Symbol)tup[3];
		scope = SCOPE_OF(type_mark);
		nat = NATURE(scope);
		if (mode != na_out || is_access(type_mark))
			continue;
		else if (TYPE_OF(type_mark) == symbol_limited_private
		  && (nat == na_package_spec || nat == na_generic_package_spec 
		  || nat == na_generic_part )
		  && !in_private_part(scope) && tup_mem((char *)scope, open_scopes) ) {
			/* We	are in the visible  part of  the package that declares
			 * the type. Its  full  decl. will  have to be  given with an
			 * assignable type.
			 */
			misc_type_attributes(type_mark) =  
		      (misc_type_attributes(type_mark)) | TA_OUT;
		}
		else if (is_limited_type(type_mark)) {
			errmsg_id("Invalid use of limited type % for out parameter ",
			  type_mark, "7.4.4", current_node);
		}
	ENDFORTUP(ft);
}

int in_private_part(Symbol scope)					/*;in_private_part */
{
	Fortup ft;
	Symbol sym;

	FORTUP(sym=(Symbol), open_scopes, ft);
		if (NATURE(sym) == na_private_part 
	      && streq(ORIG_NAME(sym), ORIG_NAME(scope)))
			return TRUE;
	ENDFORTUP(ft);
	return FALSE;
}

int private_kind(Symbol type_mark)						/*;private_kind*/
{
	/* We must distinguish between fully limited types, such as task types,
	 * and	limited private types, which  are not limited  in the  defining
	 * package body. Limited private types become limited when used outside
	 * of their scope  of definition, and so  do composite	types with such
	 * components, or derived  types of them. This procedure is used to set
	 * the corresponding attribute in a type definition.
	 *   Generic  limited types  and composites of them are always limited.
	 * These attribtues are also used to detect premature access to composite
	 * types that have incomplete subcomponents. If a subcomponent is a generic
	 * private type, there is no question of premature access (e.g. it is legal
	 * to have aggregates of this composite type).
	 */
	/* This procedure is only used to return one of the attributes maintained
	 * is misc_type_attributes, and hence returns one of the values
	 * TA_...
	 */

	Symbol	r, t;
	int	kind, tattr;

	r = root_type(type_mark);
	kind=0;
	do {
		if (is_scalar_type(type_mark))  {
			kind = 0;
			break;
		}

		t = TYPE_OF(r);
		if (t == symbol_private) {
			kind = TA_PRIVATE;
			break;
		}
		if (t == symbol_limited_private) {
			kind = TA_LIMITED_PRIVATE;
			break;
		}

		tattr = (int)misc_type_attributes(type_mark);
		if (tattr &TA_PRIVATE) {
			kind = TA_PRIVATE;
			break;
		}
		if (tattr & TA_LIMITED_PRIVATE) {
			kind = TA_LIMITED_PRIVATE;
			break;
		}
		if (tattr & TA_LIMITED) {
			kind = TA_LIMITED;
			break;
		}
		if (tattr & TA_INCOMPLETE) {
			kind = TA_INCOMPLETE;
			break;
		}
		if (is_task_type(type_mark)) {
			kind =	TA_LIMITED;
			break;
		}

		if (is_access(type_mark)) {
			t = TYPE_OF((Symbol)base_type((Symbol) designated_type(type_mark)));
			if (t == symbol_private)
				kind = TA_PRIVATE;
			else if (t == symbol_limited_private)
				kind = TA_LIMITED_PRIVATE;
			else if (t == symbol_limited)
				kind = TA_LIMITED;
			else if (t == symbol_incomplete)
				kind = TA_INCOMPLETE;
		}
	} while (0);

	if (kind == TA_LIMITED_PRIVATE
	  && (is_generic_type(type_mark) || ! in_open_scopes(SCOPE_OF(r))))
		kind = TA_LIMITED;
	if (kind == TA_PRIVATE && is_generic_type(type_mark)) kind = 0;
	return (kind);
}

int is_fully_private(Symbol type_mark)		/*;is_fully_private*/
{
	/* Check whether a composite type has an 'incomplete' private component.*/

	int	a;

#ifdef TBSN
	const f_types = ['private', 'limited_private', 'incomplete'];

	return	is_set (a :
		= misc_type_attributes(type_mark))
	    	and exists kind in f_types | kind in a;
#endif
	a = (int) misc_type_attributes(base_type(type_mark));
	return a & (TA_PRIVATE | TA_LIMITED_PRIVATE | TA_INCOMPLETE);
}

void check_priv_decl(int kind, Symbol type_name)	/*;check_priv_decl*/
{
	/* Verify that the full declaration of a private type satisfies the
	 * restrictions stated in 7.4.1., 7.4.4.
	 */

	Tuple	disc_list;
	Symbol	package_name, ps, t;
	Set	attributes;
	int	typeattr;
	Forset	fs1;

	package_name = SCOPE_OF(type_name);
	if (kind == TA_PRIVATE && is_limited_type(TYPE_OF(type_name)) ) {
		errmsg("Private type requires full declaration with non limited type",
		  "7.4.1", current_node);
		return;
	}
	else if (NATURE(type_name) == na_array) {
		errmsg_l("Private type cannot be fully declared as an unconstrained",
		  " array type", "7.4.1", current_node);
		return;
	}
	else {
		/* If the private type is not declared with discriminants, it cannot
		 * be instantiated with a type with discriminants. Retrieve the pri-
		 * vate declaration to find if discriminant list was present.
		 */
		/* [-, -, [-, disc_list], attributes ] :=
		 *   private_decls(package_name)(type_name);
		 */
		ps = private_decls_get(
		  (Private_declarations) private_decls(package_name), type_name);
		disc_list = (Tuple) (SIGNATURE(ps))[3]; /*is 3rd comp. in C */
		attributes = private_dependents(ps);
		typeattr = misc_type_attributes(ps);

		if (can_constrain(type_name) && tup_size(disc_list) == 0) {
			errmsg_l("Private type without discriminants cannot be given ",
			  "full declaration with discriminants", "7.4.1", current_node);
			/* and viceversa.*/
		}
		else if (tup_size(disc_list) != 0 && NATURE(type_name) !=na_record ) {
		    /* TBSL - see why following line commented out	ds 2 aug */
			/*|| !has_discriminants(type_name)*/
				errmsg_l("A private type with discriminants must be given ",
				  "full declaration with a discriminated type", "7.4.1",
				  current_node);
			/*    else if ('out' in_attributes ? {} {*/
		}
		else if ( (typeattr & TA_OUT) && is_limited_type(type_name) ) {
			errmsg_l("Use of type for an OUT parameter requires full ",
			  "declaration  with non limited type", "7.4.4", current_node);
		}
	}
	/* Composite types defined in the package and which include a component
	 * whose type is type_name are now usable in full (if type_name itself is
	 * not limited). They  may be defined in the visible part of the package,
	 * or in the (current) private part.
	 * The private dependents are part of the attributes of the private type.
	 */
	if (!is_limited_type(type_name)) {
		if (attributes != (Set)0) {
			FORSET(t=(Symbol), attributes, fs1);
				if (SCOPE_OF(t) == package_name || SCOPE_OF(t) == scope_name)  {
					/* Save visible definition before updating.*/
					private_decls_put((Private_declarations)
					  private_decls(package_name), t);
					/* private_decls(package_name)(t) := SYMBTABF(t); */
					/*    set_less(misc_type_attributes(t) , kind);*/
					misc_type_attributes(t) =
					  ((int)misc_type_attributes(t) & ~kind);
				}
			ENDFORSET(fs1)
		}
	}
	check_generic_usage(type_name);
}

static int in_relevant_scopes(int n)				/*;in_relevant_scopes*/
{
	/* called from private_ancestor to test membership in 
     * SETL constant tuple relevant_scopes
	 */

	return (n== na_package_spec || n == na_generic_package_spec
	  || n == na_private_part || n == na_generic_part);
}

Symbol private_ancestor(Symbol type_name)	/*;private_ancestor*/
{
	/* A type name has  a private ancestor	if it  is a subtype of, or has a
	 * component which is a subtype of, a private type whose full definition
	 * has not been seen yet. If the private ancestor of  t is defined, then
	 * t cannot  appear in	a type derivation,  and its  elaboration must be
	 * performed after that of the ancestor.
	 */

	if (in_relevant_scopes(NATURE(scope_name))
	  || ((NATURE(scope_name) == na_record || NATURE(scope_name) == na_void)
	  && in_relevant_scopes(NATURE(SCOPE_OF(scope_name)))))
		return trace_ancestor(type_name, tup_new(0));
	else
		return (Symbol)0;
}

static Symbol trace_ancestor(Symbol type_name, Tuple seen_prev)
															/*;trace_ancestor*/
{
	Fordeclared	fd1;
	char		*id;
	Symbol		comp, pr;
	int		nat;
	Tuple		seen;

#ifdef TBSL
	-- note that seen is declared as set in SETL 
#endif
	/* Insertion of type names to the tuple seen must remain local to current
	 * invocation of this recursive procedure and not affect the calling one.
	 * Thus, a local copy of the tuple is created upon each entry to this
	 * procedure.
	 * the parameter name seen has been changed to seen_prev.
	 */
	seen = tup_copy(seen_prev);

	/* Recursive procedure to find the private components of a composite
	 * type. this procedure uses a collection variable in order to detect 
	 * (invalid) recursive type definitions of private types.
 	 */
	if (tup_mem((char *) type_name, seen)) {
		errmsg_id("recursive definition of private type %", type_name,
		  "7.2", current_node);
		return type_name;
	}
	else
		seen = tup_with(seen, (char *) type_name);

	if (is_scalar_type(type_name)) return (Symbol)0;
	else if (in_priv_types(TYPE_OF(type_name))
	  && in_open_scopes(SCOPE_OF(type_name))) {
		if (!is_generic_type(type_name))
			return type_name;
		else 	      /* A generic type is never seen by the interpreter */
			return (Symbol)0;
	}
	else {
		nat = NATURE(type_name);
		if (nat == na_subtype)
			return trace_ancestor(base_type(type_name), seen);
		else if (nat == na_array)
			return trace_ancestor((Symbol) component_type(type_name), seen);
		else if (nat == na_record) {
			FORDECLARED(id, comp,
			    (Declaredmap)declared_components(base_type(type_name)), fd1);
				/* anonymous subtypes are generated for subtype indications in
				 * component declarations, and appear in the declared map of 
				 * records, but need not be examined here. 
				 */
				if (NATURE(comp) == na_subtype) continue;
				pr = trace_ancestor(TYPE_OF(comp), seen);
				if (pr!=(Symbol)0) return pr;
			ENDFORDECLARED(fd1);
		}
		else if (nat == na_access)
			/* Access types need not be deferred.*/
			return (Symbol)0;
	}
	return (Symbol)0; /* If none of the above.*/
}

static void private_part(Node priv_node)					/*;private_part*/
{
	char *nam;
	Symbol	u_name;
	Fordeclared	fd1;
	Private_declarations	pd;
	Forprivate_decls	fp1;
	Symbol	vis_decl;
	int	nat;
	Node	save_current_node;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  private_part");

	nat = NATURE(scope_name);			/* save */
	NATURE(scope_name) = na_private_part;
	save_current_node = current_node;	/* will be changed by adasem */
	adasem(priv_node);
    force_all_types();
	NATURE(scope_name) = nat;			/* restore */
	current_node = (priv_node != OPT_NODE ? priv_node : save_current_node);
	/* Check that private types and deferred constants received
	 * full declarations.
	 */

	FORDECLARED(nam, u_name, DECLARED(scope_name), fd1 );
		if (IS_VISIBLE(fd1)) { 
		  if ((in_priv_types(TYPE_OF(u_name)) 
				&& SCOPE_OF(u_name) == scope_name
		  		&& !is_generic_type(u_name)) 
			|| (NATURE(u_name) == na_constant 
				&& (Node)SIGNATURE(u_name) == OPT_NODE)) {
			/* Private object did not get private description.*/
				errmsg_str("Missing full declaration in private part for %",
			  			nam, "7.4.1", current_node);
		   }
		}
	ENDFORDECLARED(fd1);
	/* Now exchange contents of private_decls and symbol table. In this
	 * fashion the declarations that were visible in the private part of
	 * the package, and that will be visible in the package body, become
	 * inaccessible outside of the package specification.
	 */
	pd = (Private_declarations) private_decls(scope_name);
	FORPRIVATE_DECLS(u_name, vis_decl, pd, fp1);
		private_decls_swap(u_name, vis_decl);
	ENDFORPRIVATE_DECLS(fp1);
}

void end_specs(Symbol nam)		/*;end_specs*/
{
	/* This procedure is invoked at the end of a module specification.
	 * If this spec. is a compilation unit, then we save in UNIT_DECL
	 * all the declarations processed for the module. These declarations
	 * are retrieved (by procedure get_specs) when the separate compilation
	 * facility is used.
	 * In the case of generic modules, we must we must save the
	 * specs of the generic object in its signature, to simplify its instan-
	 * tiation. In order to insure that a separately compiled generic object
	 * is properly saved, we make the object name accessible within its own
	 * scope. This insures that its symbol table entry is correctly saved.
	 */

	int	kind;
	Tuple	old_vis, vis_units;
	Fortup	ft1;
	Symbol	v;
	char	*v_spec_name;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : end_specs(nam) ");

	kind = NATURE(nam);

	/* save visible mods for this scope.*/
	old_vis = tup_new(0);
	FORTUP(v=(Symbol), vis_mods, ft1);
		if (v!=symbol_ascii)
			old_vis = tup_with(old_vis, (char *) v);
		/*old_vis = [v in vis_mods | v /= 'ASCII'];*/
	ENDFORTUP(ft1);

	popscope();

	vis_units = tup_new(0);
	FORTUP(v=(Symbol), old_vis, ft1);
		v_spec_name = strjoin("sp", original_name(v));
		if (unitNumberFromName(v_spec_name))
			vis_units = tup_with(vis_units, original_name(v));
	ENDFORTUP(ft1);

	if (IS_COMP_UNIT)
		save_spec_info(nam, vis_units);
	else {
		/* If the module is a sub-unit, make sure that it is visible in
		 * its enclosing scope (except if it is a generic package).
		 */
		FORTUP(v=(Symbol), old_vis, ft1);
			if (! tup_mem((char *) v, vis_mods))
				vis_mods = tup_with(vis_mods, (char *) v);
		ENDFORTUP(ft1);
		/*vis_mods +:= [v in old_vis | v notin vis_mods];*/
		if (kind != na_generic_package_spec)
			vis_mods =  tup_with(vis_mods, (char *) nam);
	}
}

void check_incomplete_decls(Symbol scope, Node msg_node)
													/*;check_incomplete_decls*/
{
	/* At the end of a block, verify that entities that need a body received
	 * one.
	 */

	Fordeclared	fd1;
	Fortup	ft1;
	char	*id, *stub;
	Symbol	name;
	int	exists;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : check_incomplete_decls");

	if (DECLARED(scope) != (Declaredmap)0) {
		FORDECLARED(id, name, DECLARED(scope), fd1);
                        /* Limit the check to only entities declared in this
                         * scope to avoid checking packages that are renamings
                         * of things in other scopes.
                         */
			if ((SCOPE_OF(name) == scope) &&
                            needs_body(name) && !is_anonymous_task(name)) {
				exists = FALSE;
				FORTUP(stub=(char *), lib_stub, ft1);
					if (streq(unit_name_name(stub), original_name(name)))
						exists = TRUE;
				ENDFORTUP(ft1);
				if (!exists)  {
					errmsg_nat_id_str("Missing body for % %.%", name, scope,
					  id, "7.3", msg_node);
					continue;
				}
			}
			if (TYPE_OF(name) == symbol_incomplete) {
				errmsg_str(
				  "Missing full type declaration for incomplete type %",
				  id, "3.8.1", msg_node);
			}
		ENDFORDECLARED(fd1);
	}
}

Symbol get_specs(char *name)		/*;get_specs*/
{
	/* Install the specification for a package. This is done in two cases :
	 * a) When we process the WITH clause of a new compilation unit.
	 * b) When we compile the body of a package. The corresponding
	 * package specification must have been compiled already, an must be
	 * available. 
	 */

	char	*spec_name, *u;
	int	i, notin;
	Tuple	decscopes, decmaps, vis_units, specs;
	Symbol	v, sn;
	Fortup	ft1, ft2;
	Symbol	unit_unam, uname, maybe_decl;
	Unitdecl ud;

	if (cdebug2 > 3) {
		TO_ERRFILE("AT PROC :  get_specs");
		printf("get_specs for %s\n", name);
	}

	spec_name = strjoin("sp", name);
	if (!retrieve(spec_name)) {
		errmsg_str("Cannot find package specification for %", name, "10.1",
		  current_node);
		return (Symbol)0;
	}
	/* Read in the unique names and the declared types of all visible
	 * names in the module specification.
	 */
	/*[unit_unam, specs, decmap, old_vis, notvis] := UNIT_DECL(spec_name);*/
	ud = unit_decl_get(spec_name);
	if (ud == (Unitdecl) 0) chaos("get_specs, unit_decl_get returned 0 - exit");
	unit_unam = ud->ud_unam;
	specs = ud->ud_symbols;
	decscopes = ud->ud_decscopes;
	vis_units = ud->ud_oldvis;
	decmaps = ud->ud_decmaps;

	/* SYMTAB restore */
	symtab_restore(specs);

	/* (for dec = decmap(sn))
	 * declared(sn) := dec;
	 * if notvis(sn) /= om then   $ only defined for non-generic packages.
	 * visible(sn) :=	dec - notvis(sn);
	 * end if;
	 * end for;
	 */
	FORTUPI(sn=(Symbol), decscopes, i, ft1);
		/* TBSL - see if need do dcl_copy when restore, as did copy when saved*/
#ifdef TBSL
	-- translate if notvis(sn)... test above to C	ds 2-jan-85 
	    -- need loop over declared map to see if any entries not visible.
#endif
	    if (decmaps[i]!=(char *)0)
			DECLARED(sn) = dcl_copy((Declaredmap) decmaps[i]);
	ENDFORTUP(ft1);
	/*
	 * Predefined unit that are mentioned in a WITH clauses are not saved in
	 * UNIT_LIB, for storage reasons. Their contents must be brought in ex-
	 * plicitly, but their direct visibility must not be modified.
	 */
	/* (for u in vis_units | u notin vis_mods) */
	FORTUP(u=(char *), vis_units, ft1);
		notin = TRUE;
		FORTUP(v=(Symbol), vis_mods, ft2);
			if (streq(u, original_name(v))) notin = FALSE;
		ENDFORTUP(ft2);
		if (notin) {
			maybe_decl = dcl_get(DECLARED(symbol_standard0), u);
			uname = get_specs(u);
			/*
			 * dcl_put(DECLARED(symbol_standard0),u,maybe_decl);
			 *   this line raises chaos for duplicate entry in dcl_put,
			 *   so we explicitly undefine and then restore previous value
			 */
			dcl_undef(DECLARED(symbol_standard0),u);
			if (maybe_decl !=(Symbol)0)
				dcl_put(DECLARED(symbol_standard0),u,maybe_decl);
			vis_mods = tup_with(vis_mods, (char *)  uname);
		}
	ENDFORTUP(ft1);
	if (dcl_get(DECLARED(symbol_standard0), name) == (Symbol)0)
		dcl_put(DECLARED(symbol_standard0), name, unit_unam);
	return unit_unam;
}
