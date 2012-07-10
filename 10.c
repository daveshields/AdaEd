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
#include "ifile.h"
#include "chapprots.h"
#include "setprots.h"
#include "smiscprots.h"
#include "miscprots.h"
#include "libprots.h"
#include "libwprots.h"
#include "dclmapprots.h"
#include "dbxprots.h"
#include "errmsgprots.h"

int save_trace_opt = 0;
/* chapter 10 */

static Tuple context;

static void init_compunit();
static void save_comp_info(Node);
static void save_tree(Node, int);
static void renumber_nodes(char *);
static void collect_unit_nodes(Symbol);
static void generic_declarations(Symbol, Unitdecl);
static void save_proper_body_info(Node);
static void save_package_instance_unit(Node);
static void save_subprogram_instance_unit(Node);
static void establish_context(Node);
static void with_clause(Tuple, Node);
static void elaborate_pragma(Node);
static Tuple check_separate(Node);
static Stubenv retrieve_env(Node, Node);
static void remove_obsolete_stubs(char *);
static char *get_unit(char *);
static void new_unit_numbers(Node, unsigned);

/*TBSL: need to review calls to sasve_subprog_info now that
 * it has an argument	ds 31 oct
 */

extern IFILE *TREFILE, *AISFILE, *LIBFILE;
static Tuple  elab_pragmas;

/* all_vis is tuple of unit-names */

static void init_compunit()						/*;init_compunit*/
{
	int	i;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  init_compunit;");

	/* Initialize tree nodes to unit number of the new compilation unit.*/
	unit_number_now = unit_number(unit_name);
	for (i = 1; i <= seq_node_n; i++)
		N_UNIT((Node)seq_node[i]) = unit_number_now;
}

void new_compunit(char *typ, Node name_node)	/*;new_compunit*/
{
	char	*name;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  new_compunit");

	name = N_VAL(name_node);

	/* Establish global name and library name for new compilation unit. */
	if (IS_COMP_UNIT){
		remove_obsolete_stubs(name);
		seq_symbol_n = 0;	 /* reset symbol count */
		unit_name = strjoin(typ, name);
		init_compunit();
	}
}

/* chapter 10, part b*/
void compunit(Node node)							/*;compunit*/
{
	Node	unit_body;
	Tuple	added_names;
	char	*id;
	Fortup	ft1;
	Symbol	sym;
	Fordeclared fd;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  compunit;");

	elab_pragmas = tup_new(0);
	stubs_to_write = set_new(0);
	all_vis = tup_new(0);
	/*context_node = N_AST1(node);*/
	unit_body = N_AST2(node);
	establish_context(node);
	/* process unit only if there were no problems in processing context */
	if (context != (Tuple)0)
		adasem(unit_body);
	if (errors == 0) {
		/* If there are no errors in any comp unit in the file, collect global
		 * maps and library information after completion of this a compilation
		 * unit.
		 */
		if (N_KIND(unit_body) == as_separate)
			/* collect symbol table information for body (it is not a unit, 
			 * and must be saved explicitly here).
			 */
			save_proper_body_info(unit_body);

		tup_frome(newtypes);

		if (N_KIND(unit_body) == as_insert) {
			if (N_KIND(N_AST1(unit_body)) == as_subprogram_tr)
				/* for a subprogram instance, we place renaming code in the body
				 * of the subprogram. If there is some additional instantiation 
				 * code (bounds checks, etc.) it must be placed in a separate
				 * unit on which the instantiation depends.
				 */
				save_subprogram_instance_unit(node);
			else
				/* Produce two units, one for spec instance and one for body. */
				save_package_instance_unit(node);
		}
		else {		/* any other kind of compilation unit.*/
			save_comp_info(node);
		}
	}
	/* Reinitialize compilation environment. */

	unit_name = strjoin("","");
	newtypes = tup_with(newtypes, (char *) tup_new(0));
	/*   DECLARED := BASE_DECLARED;
	 * Delete symbols placed in standard0 by previous compilation,
	 * restoring standard0 to its initial state. added_names is a tuple
	 * of identifiers added in prior compilation.
	 */
	added_names = tup_new(0); /* build tuple of added identifiers */
	FORDECLARED(id, sym, DECLARED(symbol_standard0), fd);
		if (sym != (Symbol)0 && S_UNIT(sym))
			added_names = tup_with(added_names, id);
	ENDFORDECLARED(fd);
	FORTUP(id=(char *), added_names, ft1);
		dcl_undef(DECLARED(symbol_standard0), id);
	ENDFORTUP(ft1);
	tup_free(added_names);

	DECLARED(symbol_unmentionable) = base_declared[1];
	DECLARED(symbol_standard) = base_declared[2];
	DECLARED(symbol_ascii) = base_declared[3];
	FORDECLARED(id, sym, DECLARED(symbol_ascii), fd);
		IS_VISIBLE(fd) = TRUE;
	ENDFORDECLARED(fd);
	scope_name = symbol_standard0;
	open_scopes = tup_new(2);
	open_scopes[1] = (char *)symbol_standard0;
	open_scopes[2] = (char *)symbol_unmentionable;
	used_mods = tup_new(0);
	vis_mods = tup_new1((char *) symbol_ascii);
	scope_st = tup_new(0);
	return;
}

static void save_comp_info(Node node)					/*;save_comp_info*/
{
	/* Subsidiary to the previous procedure. In the case of a unit which is
	 * a package instantiation, the current procedure is called twice, to
	 * produce separate units for the instance spec and the instance body.
	 */

	Unitdecl	ud;
	char	*v;
	Tuple	tup;
	Set		vis_units;
	int		uindex, i, si;
	struct unit *pUnit;
	Fortup	ft1;
	Forset	fs1;
	Stubenv	ev;
	char	*stub_name;

	vis_units = set_new(tup_size(all_vis));

	uindex = unit_number(unit_name);
	pUnit = pUnits[uindex];
	/*PRE_COMP(unit_name) := vis_units;*/
	FORTUP(v=(char *), all_vis, ft1);
		vis_units = set_with(vis_units, (char *) unit_numbered(v));
	ENDFORTUP(ft1);
	pUnit->aisInfo.preComp = (char *)vis_units;
	pUnit->aisInfo.pragmaElab = (char *) tup_copy(elab_pragmas);

	/* Before writing out any info, set unit of all symbols allocated
	 * while compiling this unit to current unit number
	 */
	for (i = 1; i <= seq_symbol_n; i++)
		S_UNIT((Symbol)seq_symbol[i]) = uindex;

	save_tree(node, uindex);
	update_lib_maps(unit_name, 'u');
	pUnit->aisInfo.compDate = (char *) tup_new(0);

	/*UNIT_DECL(unit_name) +:= [CONTEXT, UNIT_NODES];	*/
	ud = unit_decl_get(unit_name);
	if (ud == (Unitdecl)0)
		chaos("save_comp_info: unit decl missing");
	ud->ud_context = tup_copy(context);
	ud->ud_nodes = tup_copy(unit_nodes);
	unit_decl_put(unit_name, ud);
	if (!errors) {
		/* Stub environment info is now written after the tree nodes
		 * are renumbered in save_tree. Also in case of erros Stub info
		 * is not written to st1 file.
		 */
		FORSET(si=(int), stubs_to_write, fs1)
		    stub_name = lib_stub[si];
			tup = (Tuple) stub_info[si];
			ev = (Stubenv) tup[2];
			write_stub(ev, stub_name, "st1");
		ENDFORSET(fs1);
	}
	if (!errors) write_ais(uindex);
}

static void new_unit_numbers(Node root, unsigned newUnitNumber)
														/*;new_unit_number*/
{
	unsigned nodeKind;
	Node listNode;
	Fortup ft1;
	Tuple listTuple;

	if (root == (Node)0 || root == OPT_NODE) return;
	N_UNIT(root) = newUnitNumber;

	nodeKind = N_KIND(root);
	if (N_AST1_DEFINED(nodeKind)) new_unit_numbers(N_AST1(root), newUnitNumber);
	if (N_AST2_DEFINED(nodeKind)) new_unit_numbers(N_AST2(root), newUnitNumber);
	if (N_AST3_DEFINED(nodeKind)) new_unit_numbers(N_AST3(root), newUnitNumber);
	if (N_AST4_DEFINED(nodeKind)) new_unit_numbers(N_AST4(root), newUnitNumber);

	if (! N_LIST_DEFINED(nodeKind)) return;

	listTuple = N_LIST(root);
	FORTUP(listNode=(Node), listTuple, ft1);
		new_unit_numbers(listNode, newUnitNumber);
	ENDFORTUP(ft1);
}

static void save_tree(Node root, int uindex)		/*;save_tree*/
{
	/* This procedure builds a sequential list of all the nodes in the
	 * abstract syntax tree while performing a preorder scan of the tree.
	 * For a given node, all its components are  placed in a flat tuple
	 * "tree_node".	 This tuple is then added to the list.
	 *
	 * For the C version, we need to traverse the tree to find the reachable
	 * nodes, which are built up in a string reach such that reach[i] is
	 * 1 if node with sequence number i is reachable, 0 otherwise.
	 * We then call write_tree (lib.c)  to actually write the tree.
	 */

	int	stack_max, stack_now, na, i, unit_now, nk;
	Tuple	stack, a;
	Node	nodes[5], n, nod;
	char	*reach;
#define STACK_INC 50

	if (TREFILE == (IFILE *)0) return;
	reach = emalloct((unsigned) ( seq_node_n+2) , "reach");
	reach[seq_node_n+1] = '\0'; /* mark end of string */
	for (i=0; i <= seq_node_n; i++) reach[i] = '0';
	stack_max = tup_size(unit_nodes) + STACK_INC;
	stack = tup_new(stack_max);
	for (i = 1; i <= tup_size(unit_nodes); i++){
		stack[i] = unit_nodes[i];
#ifdef SAVE_TRACE
		save_trace("init_stack", i, (Node) stack[i]);
#endif
	}
	stack_now = tup_size(unit_nodes);
	/* NOTE: must have STACK_INC > size of init_nodes.
	 * We do not write nodes for predefined entities in C version.
	 */
	unit_now = N_UNIT(root);
	stack_now++;
	stack[stack_now] = (char *) root;
#ifdef SAVE_TRACE
	save_trace("init_root", stack_now, (Node) stack[stack_now]);
#endif

	while (stack_now) {
		/*n frome stack;*/
		n = (Node) stack[stack_now];
#ifdef DEBUG
		if (trapns>0 && N_SEQ(n) == trapns && N_UNIT(n) == trapnu) trapn(n);
#endif
		/* define SAVE_TRACE for exhaustive trace as write tree */
#ifdef SAVE_TRACE
		save_trace("process", stack_now, (Node) n);
#endif
		if (N_UNIT(n) == unit_now)  reach[(int)N_SEQ(n)] = '1';
		stack_now--;
		if (n == OPT_NODE) continue;
		/*tree_node := [n, N_KIND(n)];*/
		nk = N_KIND(n);
		nodes[1] = nodes[2] = nodes[3] = nodes[4] = (Node)0;
		if (N_AST1_DEFINED(nk)) nodes[1] = N_AST1(n);
		if (N_AST2_DEFINED(nk)) nodes[2] = N_AST2(n);
		if (N_AST3_DEFINED(nk)) nodes[3] = N_AST3(n);
		if (N_AST4_DEFINED(nk)) nodes[4] = N_AST4(n);
		for (i = 1; i <= 4; i++) {
			nod = nodes[i];
			/*tree_node with:= #a;*/
			if (nod == (Node)0) continue;
			/*if (tree_node /=OPT_NODE) stack with:= a(#a-i+1);*/
			if (nod == OPT_NODE) continue;
			if (stack_now == stack_max) { /* expand stack */
				stack[0] = (char *) stack_now;
				stack = tup_exp(stack, (unsigned) (stack_now+STACK_INC));
				stack[0] = (char *) stack_now;
				stack_max += STACK_INC;
			}
			/* add node to stack */
			/*tree_node with:= a(i);*/
			stack[++stack_now] = (char *) nod;
#ifdef SAVE_TRACE
			save_trace("stack_ast", stack_now, nod);
#endif
		}
		if (N_LIST_DEFINED(nk))
			a = N_LIST(n);
		else
			a = (Tuple)0;
		if (a != (Tuple)0 ) {
			/*tree_node with:= #a;*/
			na = tup_size(a);
			/*(for i in [1..#a])*/
			for (i = 1; i <= na; i++) {
				/*tree_node with:= a(i);*/
				nod = (Node) a[i]; 
				if (N_UNIT(nod) == unit_now) reach[(int)N_SEQ(nod)] = '1';
				/*stack with:= a(#a-i+1);*/
				if (stack_now == stack_max) {
					stack[0] = (char *) stack_now;
					stack = tup_exp(stack, (unsigned) stack_now+STACK_INC);
					stack[0] = (char *) stack_now;
					stack_max += STACK_INC;
				}
				stack[++stack_now] = (char *) nod;
#ifdef SAVE_TRACE
				save_trace("stack_list", stack_now, nod);
#endif
			}
		}
	}
	renumber_nodes(reach);
	write_tre(uindex, N_SEQ(root), reach);
	efreet(reach, "reach");
	tup_free(stack);
}

static void renumber_nodes(char *reach)			/*;renumber_nodes*/
{
	/* This procedure renumbers the nodes so that the nodes which are live
	 * (not dead) and need to be written out in the tree (trc) file are 
	 * contigous and the seq_node array is therefore dense. This reduces 
	 * the size of seq_node necessary for separate compilation and in the 
	 * code generator phase. In addition the offset table written in the trc 
	 * file will also be reduced with this compressed version. The scheme 
	 * is relatively simple in that all nodes that are unreachable are 
	 * exchanged with positions that are reachable which appear later in 
	 * the list (tuple). Only one pass over the nodes is necessary using this
	 * method, so it is quite efficient.  
	 * Note that seq_node_n is changed in this procedure.
	 */

	int 	i, j;
	int		reachable_node_found;
	Node	nod, unreachable_node;

	j = seq_node_n;
	for (i = 1; i <= j; i++) {
		/* First search rightward for a node which is unreachable (where reach 
		 * is 0 for that element). This will then be exchanged with a node 
		 * which is reachable which is found by searching the list leftward.
		 * Ultimately the left and right pointers (i & j) will converge.
		 */
		if (reach[i] == '1') continue;
		reachable_node_found = 0;

		/* Search for reachable node from the right */
		for (; j > i; j--) {
			if (reach[j] == '1') {
				reachable_node_found = 1;
				break;
			}
		}
		/* If there is no reachable node found any more we are done with the
		 * compression.
		 */
		if (!reachable_node_found)  break;
		nod = (Node) seq_node[j];
		unreachable_node = (Node) seq_node[i];
		/* Exchange positions of the two nodes and set their seqeunce number 
		 * to the respective new position numbers.
		 * Currently the node in seq_node[i] cannot be wiped out since it is
		 * still needed because of save_package_instance.
		 */
		seq_node[i] = (char *) nod;
		seq_node[j] = (char *) unreachable_node;
		N_SEQ(nod) = i;
		N_SEQ(unreachable_node) = j;
		reach[i] = '1';
		reach[j] = '0';
	}
	seq_node_n = i - 1;
}

#ifdef SAVE_TRACE
void save_trace(char *s, int n, Node nod)
{
	if (save_trace_opt == 0) return;
	printf("%11s %d\n", s, n);
	zpnod(nod);
}
#endif
void save_trace_init()
{
	save_trace_opt++;
}

Tuple unit_symbtab(Symbol unit_unam, char unit_typ)			/*;unit_symbtab*/
{
	/* Collect symbol table entries for all entities declared in a compila-
	 * tion	 unit, including inner units  and blocks. We iterate  over  the
	 * symbol table, and save all objects that are declared in the unit and
	 * in inner scopes.  For non-generic package bodies, we omit the  decla-
	 * rations that	 appear in the visible part, and are already saved with 
	 * the package spec.
	 */

	Tuple	symb_map;
	Tuple	ignore;
	Set		scopes, seen;
	Symbol	u_name, sc, sym;
	char	*id;
	Fordeclared fd1;
	Forprivate_decls fp1;
	Private_declarations pd;
	int		ignore_n;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : unit_symbtab:");

	unit_nodes = tup_new(0);
	if (errors) return unit_nodes;

	symb_map = tup_new(0);
	ignore = tup_new(0); 
	ignore_n = 0;
	if (NATURE(unit_unam) == na_package && unit_typ == 'u') {
		ignore = tup_exp(ignore, 10);
		ignore_n = 0;
		FORDECLARED(id, u_name, DECLARED(unit_unam), fd1);
			if (IS_VISIBLE(fd1)) {
				if (tup_mem((char *) u_name, ignore)) continue;
				if (ignore_n>=tup_size(ignore)) {
					ignore = tup_exp(ignore, (unsigned) (ignore_n+10));
				}
				ignore_n += 1;
				ignore[ignore_n] = (char *) u_name;
			}
		ENDFORDECLARED(fd1);
	}

	/* first, collect the nodes referenced in the current unit Symbtab record.
	 * then, iterate through it's declared map to get declarations in inner
	 * scopes.
	 */
	collect_unit_nodes(unit_unam);

	ignore[0] = (char *) ignore_n;
	seen = set_new1((char *) unit_unam);
	scopes = set_copy(seen);

	while (set_size(scopes) != 0) {
		sc = (Symbol) set_from(scopes);
		FORDECLARED(id, u_name, DECLARED(sc), fd1);
			if (! tup_mem((char *)u_name, ignore) ) {	/* save its info. */
				/* Collect the AST nodes that appear in SYMBTAB, and may thus*/
				/* be needed for separate compilation and code generation.*/
				collect_unit_nodes(u_name);
				/*symb_map(u_name) := SYMBTABF(u_name);*/
				symb_map = sym_save(symb_map, u_name, unit_typ);
			}
			/* note that na_enum symbols have their literal map stored in the
			 * DECLARED field and so should be skipped in next test
			 * IS THIS STILL TRUE???? 
			 */
			if (NATURE(u_name) == na_enum) continue;

			if (DECLARED(u_name) != (Declaredmap)0 
			  && (!set_mem((char *)u_name, seen ) )){
				/* collect local declarations of inner scope.*/
				scopes = set_with(scopes, (char *) u_name);
				seen = set_with(seen, (char *) u_name);
			}
		ENDFORDECLARED(fd1);

		if (NATURE(sc) == na_package || NATURE(sc) == na_package_spec
		  || NATURE(sc) == na_generic_package
		  || NATURE(sc) == na_generic_package_spec) {
			/* Collect and save nodes attatched to private_decls field */
			pd = (Private_declarations) private_decls(sc);
			FORPRIVATE_DECLS(sym, u_name, pd, fp1);
				collect_unit_nodes(u_name);
			ENDFORPRIVATE_DECLS(fp1);
		}
	}
	/* We include in symb_map the information for the unit itself, which is
	 * declared in STANDARD.
	 */
	/* TBSL: get rid of this KLUDGE
	 * for generic subprograms, save symbol regardless of unit, so that the
	 * unit name of body is retrievable after being overwritten by spec
	 */
	if (NATURE(unit_unam) == na_generic_procedure
	  || NATURE(unit_unam) == na_generic_function 
	  || NATURE(unit_unam) == na_generic_package)
		symb_map = sym_save(symb_map, unit_unam, 's');
	else 
		symb_map = sym_save(symb_map, unit_unam, unit_typ);
	set_free(seen); 
	set_free(scopes);
	/* replace symbol pointers to copy of symbol table entries */
	tup_free(ignore);
	return symb_map;
}

static void collect_unit_nodes(Symbol u_name)			/*;collect_unit_nodes*/
{
	/* Collect the AST nodes that appear in SYMBTAB, and may thus*/
	/* be needed for separate compilation and code generation.*/

	int 	nat, i, size;
	Symbol 	typ;
	Tuple	sig, discr_map, gen_list, tup;
	Fortup 	ft1;

	typ = TYPE_OF(u_name);
	nat = NATURE(u_name);
	if (typ == symbol_incomplete || typ == symbol_private 
	  || typ == symbol_limited_private)
		nat = na_record; /* signature has form of record signature */

	switch (nat) {
	case na_constant:
	case na_discriminant:
	case na_in:
		unit_nodes_add((Node) default_expr(u_name));
		break;
	case na_type:
		sig = SIGNATURE(u_name);
		if (sig == (Tuple)0)
			chaos("unit_symbtab subtype - no signature");
		if ((int) sig[1] == CONSTRAINT_DELTA) {
			unit_nodes_add((Node) numeric_constraint_low(sig));
			unit_nodes_add((Node) numeric_constraint_high(sig));
			unit_nodes_add((Node) numeric_constraint_delta(sig));
			unit_nodes_add((Node) numeric_constraint_small(sig));
		}
		break;
	case na_subtype:
		sig = SIGNATURE(u_name);
		if (sig == (Tuple)0)
			chaos("unit_symbtab subtype - no signature");
		if (is_scalar_type(u_name))	 {
			unit_nodes_add((Node) numeric_constraint_low(sig));
			unit_nodes_add((Node) numeric_constraint_high(sig));
			if ((int) sig[1] == CONSTRAINT_DELTA) {
				unit_nodes_add( (Node) numeric_constraint_delta(sig));
				unit_nodes_add( (Node) numeric_constraint_small(sig));
			}
			else if ((int) sig[1] == CONSTRAINT_DIGITS) {
				unit_nodes_add( (Node) numeric_constraint_digits(sig));
			}
		}
		else if (is_record(u_name)) {
			discr_map = (Tuple) sig[2];
			size = tup_size(discr_map);
			for (i = 1; i <= size; i+=2)
				unit_nodes_add((Node) discr_map[i+1]);
		}
		break;
	case na_enum:
		sig = SIGNATURE(u_name);
		if (sig == (Tuple)0) chaos("unit_symbtab enum - no signature");
		unit_nodes_add((Node) numeric_constraint_low(sig));
		unit_nodes_add((Node) numeric_constraint_high(sig));
		break;
	case na_record:
		unit_nodes_add((Node) invariant_part(u_name));
		unit_nodes_add((Node) variant_part(u_name));
		unit_nodes_add((Node) discr_decl_tree(u_name));
		break;
	case na_procedure_spec:
	case na_function_spec:
	case na_entry:
	case na_entry_family:
	case na_generic_procedure_spec:
	case na_generic_function_spec:
		unit_nodes_add((Node) formal_decl_tree(u_name));
		break;
		/* 
		 * Clear out the formal_decl_tree fields of procedure or 
		 * function symbols since these are not needed for 
		 * conformance checks (only na_procedure_spec or 
		 * na_function_spec symbols need this entry).
		 */
	case na_procedure:
	case na_function:
		formal_decl_tree(u_name) = (Symbol)0;
		break;
		/*
		 * the nodes of generic packages(specs and bodies) or nodes of generic
		 * subprograms bodies are not automatically read in. They are brought 
		 * in explicitly upon instantiation. Default values for generic para-
		 * meters however must be read in for instantiation. The generic_list
		 * is a tuple of pairs [name, initial value] which we unpack here.
		 */
	case na_generic_package_spec:
	case na_generic_package:
	case na_generic_function:
	case na_generic_procedure:
		sig = SIGNATURE(u_name);
		gen_list = (Tuple)sig[1];
		FORTUP(tup=(Tuple), gen_list, ft1)
	    	unit_nodes_add((Node)tup[2]);
		ENDFORTUP(ft1);
		break;
	}
}

void save_subprog_info(Symbol unit_unam)				/*;save_subprog_info*/
{
	/* Save declarations for a subprogram specification or body which is a
	 * compilation unit.
	 */

	int	uindex;
	Unitdecl ud;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  save_subprog_info");

	if (IS_COMP_UNIT){
		if (unit_unam == (Symbol)0) {
			errmsg("Invalid compilation unit", "none", (Node)0);
			return;
		}
		/* get unit number (assign new one if needed) */
		uindex = unit_number(unit_name);

		/* For subprograms, UNIT_DECL has 4 fields:
		 *	1.  unique name of subprogram
		 *	2.  symbol table entries
		 *	3.  declared maps for subprogram's scope
		 *	  ( for possible late instantiations)
		 *	4.  context (supplied in compunit)
		 *
		 * case nature(unit_unam) of
		 *  (na_procedure_spec, na_function_spec,
		 *  na_generic_procedure_spec, na_generic_function_spec):
		 *   decmap := {[unit_unam, declared(unit_unam)]};
		 *
		 *  TBSL for generics
		 *  (na_generic_procedure, na_generic_function):
		 *  decmap := generic_declarations();
		 *  decmap(unit_unam) := declared(unit_unam);
		 *
		 * else
		 *  TBSL for generics
		 *  decmap := generic_declarations();
		 * end case;
		 *
		 * UNIT_DECL(unit_name) :=
		 *   [unit_unam, unit_symbtab(unit_unam), decmap, [], {}];
		 */
		ud = unit_decl_get(unit_name);
		if (ud == (Unitdecl)0) ud = unit_decl_new();
		ud->ud_unam = unit_unam;
		ud->ud_useq =  S_SEQ(unit_unam);
		ud->ud_unit =  S_UNIT(unit_unam);
		ud->ud_symbols = unit_symbtab(unit_unam, 'u');
		if (DECLARED(unit_unam) == (Declaredmap)0) {
			ud->ud_decscopes = (Tuple) 0;
			ud->ud_decmaps	 = (Tuple) 0;
		}
		else {
			ud->ud_decscopes = tup_new1((char *) unit_unam);
			ud->ud_decmaps = tup_new1(
			  (char *) dcl_copy(DECLARED(unit_unam)));
		}
		unit_decl_put(unit_name, ud);
	}
}

static void generic_declarations(Symbol unit_unam, Unitdecl ud)
													/*;generic_declarations*/
{
	/* This procedure collects the contents of declared maps within generic
	 *  subunits, for possible subsequent late instantiations.
	 */

	Tuple	decscopes, decmaps;
	Set	decl_scopes, scopes, seen;
	Symbol u_name, sc;
	char	*id;
	Fordeclared fd1;
	decscopes = tup_new(0);
	decmaps = tup_new(0);

	if (NATURE(unit_unam) == na_generic_package)
		decl_scopes = tup_new1((char *) unit_unam);
	else
		decl_scopes = tup_new(0);

	/* In SETL want to iterate over declared - i.e., we need to  know domain
	 * of declared. We take this by looking at all symbols defined in current
	 * unit for which declared field defined. This includes some extra symbols,
	 * I think due to private decls, but these extra maps seem harmless.
	 */
	scopes = set_new1((char *)unit_unam);
	seen = set_new(0);
	while (set_size(scopes) != 0) {
		sc = (Symbol) set_from(scopes);
		seen = set_with(seen, (char *)sc);
		if (DECLARED(sc) != (Declaredmap)0) {
			FORDECLARED(id, u_name, DECLARED(sc), fd1);
			if (DECLARED(u_name) != (Declaredmap)0 
			  &&(!set_mem((char *)u_name, seen))) {
				/* collect local declarations of inner scope.*/
				if (NATURE(u_name) == na_generic_procedure
				  || NATURE(u_name) == na_generic_function
				  || NATURE(u_name) == na_generic_package)
					decl_scopes = set_with(decl_scopes, (char *)u_name);
				else if (NATURE(u_name) == na_package)
					scopes = set_with(scopes, (char *) u_name);
			}
			ENDFORDECLARED(fd1);
		}
	}

	seen = set_new(0);

	while (set_size(decl_scopes) != 0) {
		sc = (Symbol) set_from(decl_scopes);
		seen = set_with(seen, (char *)sc);
		decscopes = tup_with(decscopes, (char *) sc);
		decmaps = tup_with(decmaps, (char *) dcl_copy(DECLARED(sc)));
		FORDECLARED(id, u_name, DECLARED(sc), fd1);
			if (DECLARED(u_name) != (Declaredmap)0 
			  &&(!set_mem((char *)u_name, seen)))
				/* collect local declarations of inner scope.*/
				decl_scopes = set_with(decl_scopes, (char *) u_name);
		ENDFORDECLARED(fd1);
	}

	ud->ud_decscopes = decscopes;
	ud->ud_decmaps = decmaps;
	set_free(seen); 
	set_free(scopes);
}

void save_spec_info(Symbol unit_unam, Tuple old_vis)		/*;save_spec_info*/
{
	/* Build UNIT_DECL for a package spec. that is a compilation unit.*/

	Symbol	sn;
	int	i, uindex;
	Tuple	decscopes, decmaps, decl_scopes;
	Unitdecl ud;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : save_spec_info");

	/* This was here as early as 1983, and now not only seems useless, but
	 * is WRONG !!!
	 * At end of module_body, we iterate over all inner scopes, and the presence
	 * of generic inside scope of instance results in looping.
	if (NATURE(unit_unam) == na_generic_package_spec) {
	 * save name within its own declarations, to simplify retrieval at
	 * instantiation time.
		dcl_put(DECLARED(unit_unam), original_name(unit_unam), unit_unam);
	}
	 */
	/*
	 * For package specifications, UNIT_DECL has 6 fields.
	 *	1. unique name of compilation unit
	 *	2. symbol table entries
	 *	3. declared maps for program defined scopes
	 *	4. vis_mods
	 *	5. difference between declared and visible
	 *	6. context (supplied in comp_unit)
	 */
	decscopes = tup_new(0);
	decmaps = tup_new(0);
	/* In SETL want to iterate over declared - i.e., we need to  know domain
	 * of declared. We take this by looking at all symbols defined in current
	 * unit for which declared field defined. This includes some extra symbols,
	 * I think due to private decls, but these extra maps seem harmless.
	 */
	decl_scopes = tup_new(0);
	for (i = 1; i <= seq_symbol_n; i++)
		if (DECLARED((Symbol)seq_symbol[i]) != (Declaredmap)0)
			decl_scopes = tup_with(decl_scopes, seq_symbol[i]);
	for (i = 1; i <= tup_size(decl_scopes); i++){
		sn = (Symbol) decl_scopes[i];
		decscopes = tup_with(decscopes, (char *) sn);
		decmaps = tup_with(decmaps, (char *) dcl_copy(DECLARED(sn)));
	}
	/*decmap := {[sn, dsn] : dsn = declared(sn) | sn notin p_s};
	 *
	 * Notvis keeps track of things declared but not visible
	 */
#ifdef TBSL
-- note change in def of notvis 5-jan-85:
	only define notvis
	    -- is vis is not om.
notvis :
	    = {
	};
	(for [sn, dsn] in decmap | visible(sn) /= om)
		notvis(sn) :
		= {
dec: 
			dec in dsn | dec notin visible(sn)		};
	end for;
	notvis = tup_new(0);
#endif
	/* UNIT_DECL(unit_name) :=
	 *   [unit_unam, unit_symbtab(unit_unam), decmap, old_vis, notvis];
	 * In C version have different format .
	 */

	if (!unit_numbered(unit_name)) uindex = unit_number(unit_name);
	ud = unit_decl_get(unit_name);
	if (ud == (Unitdecl)0) ud = unit_decl_new();
	ud->ud_unam =	unit_unam;
	ud->ud_useq = S_SEQ(unit_unam);
	ud->ud_unit = S_UNIT(unit_unam);
	ud->ud_symbols = unit_symbtab(unit_unam, 'u');
	ud->ud_decscopes = decscopes;
	ud->ud_oldvis = tup_copy(old_vis);
	ud->ud_decmaps = decmaps;
	unit_decl_put(unit_name, ud);
}

void save_body_info(Symbol nam)					/*;save_body_info*/
{
	/* For a package body, only the symbol table information needs to be
	 * saved, for purposes of generic instantiation. Visibility information
	 * is not kept.
	 */

	int		uindex;
	Unitdecl	ud;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC: save_body_info");

	if (IS_COMP_UNIT) {
		/*
		 * UNIT_DECL(unit_name) := [nam, unit_symbtab(nam), 
		 *				generic_declarations(), [], {}];
		 */
		uindex = unit_number(unit_name);
		ud = unit_decl_get(unit_name);
		if (ud == (Unitdecl)0) ud = unit_decl_new();
		ud->ud_unam =  nam;
		ud->ud_useq =  S_SEQ(nam);
		ud->ud_unit =  S_UNIT(nam);
		ud->ud_symbols  =  unit_symbtab(nam, 'u');
		generic_declarations(nam, ud);
		unit_decl_put(unit_name, ud);
	}
}

static void save_proper_body_info(Node node)		/*;save_proper_body_info*/
{
	Node	proper_node, spec, name_node;
	Symbol	unit_unam;
	Unitdecl	ud;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  save_proper_body_info");

	proper_node = N_AST2(node);
	if (N_KIND(proper_node) == as_generic_procedure
	  || N_KIND(proper_node) == as_generic_function) {
		spec = N_AST1(proper_node);
		name_node = N_AST1(spec);
	}
	/* For subprogram proper bodies the unique name is stored in the
	 * proper_node itself.
	 */
	else if (N_KIND(proper_node) == as_subprogram_tr) {
		name_node = proper_node;
	}
	else 
		name_node = N_AST1(proper_node);

	unit_unam = N_UNQ(name_node);

	/* UNIT_DECL(unit_name) :=
	 *	[unit_unam, unit_symbtab(unit_unam), generic_declarations(), [], {}];
	 */

	ud = unit_decl_get(unit_name);
	if (ud == (Unitdecl)0) ud = unit_decl_new();
	ud->ud_unam = unit_unam;
	ud->ud_useq = S_SEQ(unit_unam);
	ud->ud_unit = S_UNIT(unit_unam);
	ud->ud_symbols = unit_symbtab(unit_unam, 'u');

#ifdef TBSL
	handle generic_declarations
#endif

    unit_decl_put(unit_name, ud);
}

static void save_package_instance_unit(Node node)/*;save_package_instance_unit*/
{
	/* If a unit is a package instance, it is necessary to construct two 
	 * units, one for the spec and one for the body of the instance.
	 */

	Node	context_node, unit_body, spec_node, body_node, id_node, b_node;
	char	*nam;
	Symbol	unam;
	Tuple	tup;
	Unitdecl	ud;
	int		saved_seq_node_n, i;

	context_node = N_AST1(node);
	unit_body = N_AST2(node);

	/* The unit body is an insert node; unpack spec and body of instance.*/
	tup = N_LIST(unit_body);
	spec_node = (Node) tup[1];
	id_node = N_AST1(spec_node);
	body_node = N_AST1( unit_body);

	N_AST1(node) = context_node;
	N_AST2(node) = spec_node;
	unit_name[0] = 's'; /* set to spec */
	unit_name[1] = 'p';

	/* Build a node for the package instance, and rebuild compilation info.
	 * for it. Its UNIT_DECL need not contain symbol table info, which is
	 * emitted with the spec, and always retrieved at the same time.
	 * TBSL: what if this is a delayed instance?
	 */
	nam = unit_name_name(unit_name);
	b_node = node_new(as_unit);
	N_AST1(b_node) = context_node;
	N_AST2(b_node) = body_node;

	/* Since nodes for the spec and body were created at the same time they
	 * both have the same unit number. 
	 * After the spec is written change the unit field of all the body nodes 
	 * to reflect its unit.
	 */
	unam = N_UNQ(id_node);
	/* Set the nature of the symbol to be as a package spec so that the private 
	 * declarations (OVERLOADS field) is set upon reading the spec of the 
	 * instantiated package. Reset to package after the unit is written.
	 */
	NATURE(unam) = na_package_spec;
	/* Save the old value of seq_node_n since this will be changed when
	 * renumber_nodes is called by save_tree and sets seq_node_n to the 
	 * number of live and useful nodes. However all the nodes in seq_node need
	 * to be accessable for working with the package body nodes, so we will
	 * have to reset seq_node_n to the saved value. This is basically due to
	 * the artifact of how instantiated package body are handled.
	 */
	saved_seq_node_n = seq_node_n;
	save_comp_info(node);
	seq_node_n = saved_seq_node_n;
    OVERLOADS(unam) = 0;
	NATURE(unam) = na_package;

	all_vis = tup_with(all_vis, unit_name);		/* body depends on spec.*/
	unit_name = strjoin("bo", nam);
	unit_number_now = unit_number(unit_name);
	new_unit_numbers(b_node, unit_number_now);
	/* Set the number of symbols to be 0 so that the unit number of the symbol
	 * for the package is not reset to be the unit number for the body.
	 */
	seq_symbol_n = 0;
	unit_nodes = tup_new(0);
	unam = N_UNQ(id_node);
	ud = unit_decl_new();
	ud->ud_unam = unam;
	ud->ud_useq = S_SEQ(unam);
	ud->ud_unit = S_UNIT(unam);
	ud->ud_symbols = tup_new(0);
	unit_decl_put(unit_name, ud);

	/*UNIT_DECL(unit_name) := [nam, {}, {}, [], {}];*/
	/* TBSL: note that now setting five components	ds 7 dec 84 */

	save_comp_info(b_node);
}

static void save_subprogram_instance_unit(Node node)
  /*; save_subprogram_instance_unit */
{
	/* The instantiation code (renamings of formals by actuals, bounds checks)
	 * are elaborated before the body of the instance. If the instance is a
	 * unit, the instantiation code must in fact be placed in a anonymous unit
	 * on which the instantiation depends.
	 * For now, we place the renamings in the dclarative part of the procedure,
	 * which is inefficient but harmless. 
	 * TBSL: construction of anonymous unit with the rest
	 */
 
	Tuple  i_code , i_decls, i_checks, ntup;
	Node   instance, decl_node, n, ins_node, context_node, b_node;
	int    i, k;

	context_node = N_AST1(node);
	ins_node = N_AST2(node);			/* insert node */
	i_code = N_LIST(ins_node);			/* instantiation code */
	instance = N_AST1(ins_node);		/* subprogram instance*/
	N_AST2(node) = instance;
	decl_node = N_AST2(instance);
	i_decls = tup_new(0);
	i_checks = tup_new(0);
	for ( i = 1; i <= tup_size(i_code); i++) {
		n = (Node)tup_fromb(i_code);
		k = N_KIND(n);
		if (k == as_raise || k == as_check_bounds || k == as_check_discr)
			i_checks = tup_with(i_checks, (char *) n);
		else
			i_decls  = tup_with(i_decls, (char *) n);
	}

	ntup = tup_add(i_decls, N_LIST(decl_node));
	tup_free(N_LIST(decl_node));
	N_LIST(decl_node) = ntup;

	b_node = node_new(as_unit);
	N_AST1(b_node) = context_node;
	N_AST2(b_node) = instance;
	save_comp_info(b_node);

	if (tup_size(i_checks) > 0) 
		chaos("subprogram_instance_unit: checks left over");
}

static void establish_context(Node node)	/*;establish_context*/
{
	char	*name, *nam;
	Fortup	ft1, ft2, ft3;
	Node	un_node, clause_node, uw_node, unit_node;
	Node	context_node, spec, name_node;
	int	kind, i, nk;
	Tuple	tupn, tup, use_nodes, with_tup;
	char	*spec_name;
	Tuple	elaborate_list, with_list, nam_list, inherited_context = (Tuple)0;
	Unitdecl spec_decl;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  establish_context(name);");

	context_node = N_AST1(node);
	unit_node = N_AST2(node);

	/* Flatten with- and use-clauses from context node.*/

	context = tup_new(0);
	with_list = N_LIST(context_node);
	elaborate_list = tup_new(0);
	/* NOTE that ELABORATE pragmas can only appear immediately after a
	 * context_clause.  The necessary checks to insure that this condition
	 * is met have not been made.
	 */
	use_nodes = tup_new(0);
	with_tup = tup_new(0);
	FORTUP(clause_node=(Node), with_list, ft1);
		FORTUP(uw_node=(Node), N_LIST(clause_node), ft2);
			kind = N_KIND(uw_node);
			if (kind == as_with || kind == as_use) {
				tupn = tup_new(tup_size(N_LIST(uw_node)));
				FORTUPI(un_node=(Node), N_LIST(uw_node), i, ft3);
					tupn[i] = N_VAL(un_node);
				ENDFORTUP(ft3);
				tup = tup_new(2);
				tup[1] = (char *) kind;
				tup[2] = (char *) tupn;
				context = tup_with(context, (char *) tup);
				if (kind == as_use) {
					/* save nodes for subsequent call to resolve_use_clause */
					use_nodes = tup_with(use_nodes, (char *)uw_node);
					/* check that it appears in a previous with clause */
					FORTUP(name = (char *), tupn, ft3);
						if (!tup_memstr(name, with_tup))
						errmsg_str("% does not appear in previous with clause",
						  name, "10.1.1", uw_node);
					ENDFORTUP(ft3);
				}
				else {
					with_tup = tup_add(with_tup, tupn);
				}
			}
			else {
				elaborate_list = tup_with(elaborate_list, (char *) uw_node);
			}
		ENDFORTUP(ft2);
	ENDFORTUP(ft1);

	/* For bodies and proper bodies, collect any context specification
	 * inherited from parent unit or from spec.
	 */
	nk = N_KIND(unit_node);
	if (nk == as_separate) {
		inherited_context = check_separate(unit_node);
		if (inherited_context == (Tuple)0) {
			context = (Tuple) 0; /* indicates error */
			return;
		}
	}
	else if (nk == as_package_body) {
		name_node = N_AST1(unit_node);
		name = N_VAL(name_node);
		current_node = name_node;
		get_specs(name);
		all_vis = tup_with(all_vis, strjoin("sp", name));
		/* all_vis with:= ['spec', name]; */
		spec_decl = unit_decl_get(strjoin("sp", name));
		if (spec_decl != (Unitdecl)0)
			inherited_context = spec_decl->ud_context;
	}
	else if (nk == as_subprogram) {
		/* may have been subprogram spec.*/
		spec = N_AST1(unit_node);
		name_node = N_AST1(spec);
		name = N_VAL(name_node);
		spec_name = strjoin("ss", name);
		if (retrieve(spec_name) )
			all_vis = tup_with(all_vis, spec_name);

		spec_decl  = unit_decl_get(spec_name);
		if (spec_decl != (Unitdecl)0)
			inherited_context =  spec_decl->ud_context;
	}

	if (inherited_context == (Tuple) 0)
		/* this may occur if there were errors in previous units */
		inherited_context = tup_new(0);

	/* process inherited context specification */
	FORTUP(tup=(Tuple), inherited_context, ft1);
		kind = (int) tup[1];
		nam_list = (Tuple) tup[2];

		if (kind == as_with)
			with_clause(nam_list, current_node);
		else if (kind == as_use) {
			/* rebuild list of name nodes for use_clause */
			un_node = node_new(as_use);
			N_LIST(un_node) = tup_new(tup_size(nam_list));
			FORTUPI(nam = (char *), nam_list, i, ft2);
				name_node = node_new(as_simple_name);
				N_VAL(name_node) = nam;
				N_LIST(un_node)[i] = (char *)name_node;
			ENDFORTUP(ft2);
			use_clause(un_node);
		}
	ENDFORTUP(ft1);

	/* Process the given context specification. */
	FORTUP(tup=(Tuple), context, ft1);
		kind = (int) tup[1];
		nam_list = (Tuple) tup[2];

		if (kind == as_with)
			with_clause(nam_list, context_node);
	ENDFORTUP(ft1);

	FORTUP(un_node=(Node), use_nodes, ft1);
		use_clause(un_node);
	ENDFORTUP(ft1);
	tup_free(use_nodes);

	FORTUP(name_node=(Node), elaborate_list, ft1);
		elaborate_pragma(name_node);
	ENDFORTUP(ft1);

	context = tup_add(inherited_context, context);
}

static void with_clause(Tuple nam_list, Node context_node)	/*;with_clause */
{
	char *nam, *unit;
	Fortup ft;

	FORTUP(nam=(char *), nam_list, ft);
		unit = get_unit(nam);
		if (strlen(unit) >0 )
			all_vis = tup_with(all_vis, unit);
		else {
			errmsg_str("Unknown unit in with clause: %", nam, "10.1.1",
			  context_node);
			all_vis = tup_with(all_vis, strjoin("sp", nam));
		}
	ENDFORTUP(ft);
}

static char *get_unit(char *nam)				/*;get_unit*/
{
	int	exists, i;
	char	*unit, *unit1, *unit2, *su, *body_name;
	Fortup	ft1;
	Node	id_node;
	Symbol	namsym, unit_unam, scope;
	Tuple	s_info, decscopes, decmaps;
	Unitdecl ud;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  get_unit");

	exists = FALSE;
	for(i = 1; i <= unit_numbers; i++) {
		unit = pUnits[i]->libUnit;
		unit2 = unit_name_name(unit);
		unit1 = unit_name_type(unit);
		if (streq(unit2, nam)
		  && (streq(unit1, "ss") || streq(unit1, "sp"))) {
			exists = TRUE;
			break;
		}
	}
	if (exists == FALSE) {
		su = strjoin("su", nam);
		for(i = 1; i <= unit_numbers; i++) {
			unit = pUnits[i]->libUnit;
			if (streq(su, unit)) {
				exists = TRUE;
				break;
			}
		}
	}

	if (exists) {
		if (cdebug2 > 3) TO_ERRFILE(strjoin("unit ", unit));

		if (streq(unit_name_type(unit), "sp")) {
			/* puts created symbol in standard0 scope*/
			unit_unam = get_specs(nam);

			namsym = dcl_get(DECLARED(symbol_standard0), nam);
			if (NATURE(unit_unam) != na_generic_package
			  && NATURE(unit_unam) != na_generic_package_spec)
				vis_mods =tup_with(vis_mods, (char *) namsym);
		}
		else {	/* unit is a subprogram */
			if (retrieve(unit) ) {
				/*	[unit_unam, s_info, decmap] := UNIT_DECL(unit); */
				ud = unit_decl_get(unit);
				unit_unam  = ud->ud_unam;
				s_info     = ud->ud_symbols;
				decscopes  = ud->ud_decscopes;
				decmaps    = ud->ud_decmaps;

				/* Restore symbol table entries.*/
				symtab_restore(s_info);

				/* (for decls = decmap(scope)) 
				 *	declared(scope) := decls; 
				 * end; 
				 */
				FORTUPI(scope=(Symbol), decscopes, i, ft1);
					DECLARED(scope) = dcl_copy((Declaredmap) decmaps[i]);
				ENDFORTUP(ft1);
			}
			dcl_undef(DECLARED(symbol_standard0), nam);
			dcl_put(DECLARED(symbol_standard0), nam, unit_unam);
		}
		/* for generic specs retrieve body info */
		if (NATURE(unit_unam) == na_generic_package_spec) {
			body_name = strjoin("bo", nam);
			if (retrieve(body_name)) {
				ud = unit_decl_get(body_name);
				unit_unam = ud->ud_unam;
				s_info = ud->ud_symbols;
				decscopes = ud->ud_decscopes;
				decmaps = ud->ud_decmaps;

				/* SYMTAB restore */
				symtab_restore(s_info);

				FORTUPI(scope=(Symbol), decscopes, i, ft1);
					if (decmaps[i] != (char *)0)
						DECLARED(scope) = dcl_copy((Declaredmap) decmaps[i]);
				ENDFORTUP(ft1);
			}
		}
		else if (NATURE(unit_unam) == na_generic_procedure_spec
		  || NATURE(unit_unam) == na_generic_function_spec) {
			body_name = strjoin("su", nam);
			/* CHECK HOW MUCH OF THIS IS NECESSARY !!! */
			if (retrieve(body_name)) {
				ud = unit_decl_get(body_name);
				unit_unam  = ud->ud_unam;
				s_info     = ud->ud_symbols;
				decscopes  = ud->ud_decscopes;
				decmaps    = ud->ud_decmaps;

				/* Restore symbol table entries.*/
				symtab_restore(s_info);

				/* (for decls = decmap(scope)) 
				 *	declared(scope) := decls; 
				 * end; 
				 */
				FORTUPI(scope=(Symbol), decscopes, i, ft1);
					DECLARED(scope) = dcl_copy((Declaredmap) decmaps[i]);
				ENDFORTUP(ft1);
			}
			dcl_undef(DECLARED(symbol_standard0), nam);
			dcl_put(DECLARED(symbol_standard0), nam, unit_unam);
		}
		return unit;
	}
	else {	     /* Unit is not in library*/
		id_node = node_new(as_simple_name);
		N_VAL(id_node) = (char *) nam;
		check_old(id_node);
		if (N_UNQ(id_node) == symbol_undef) {     /* safe to add it, */
			namsym = find_new(N_VAL(id_node));    /* To avoid error */
			N_UNQ(id_node) = namsym;
#ifdef TBSL
			visible(nam) :
			= {
			}; 		     
			$ in subsequent USE
#endif
		}
		return strjoin("","");
	}
}

static void elaborate_pragma(Node node)					/*;elaborate_pragma*/
{
	Node	arg_list_node;
	Node	i_node, e_node, name_node, arg_node;
	Tuple	arg_list;
	Fortup	ft1;
	char	*nam;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : elaborate_pragma");

	arg_list_node = N_AST2(node);
	arg_list = N_LIST(arg_list_node);
	FORTUP(arg_node=(Node), arg_list, ft1);
		i_node	= N_AST1(arg_node);
		e_node = N_AST2(arg_node);
		/*For now, disregard named associations.*/
		if (cdebug2 > 3) TO_ERRFILE("all_vis : ");
		name_node = N_AST1(e_node);	   /* extract simple_name node.*/
		nam = N_VAL(name_node);
		if (tup_memstr(strjoin("sp", nam), all_vis)) {
			/*if ['spec', nam] in all_vis then*/
			elab_pragmas =tup_with(elab_pragmas, strjoin("bo", nam));
			/* package body needed.*/
		}
		else if (tup_memstr(strjoin("ss", nam), all_vis)) {
			elab_pragmas =tup_with(elab_pragmas, strjoin("su", nam));
			/* subprogram body needed.*/
		}
		else if (tup_memstr(strjoin("su", nam), all_vis)) {
			;	/* already listed.*/
		}
		else {
			warning(strjoin(strjoin(
		   	  "Unknown unit name in ELABORATE pragma ", nam),
		      "10.5"), name_node);
		}
	ENDFORTUP(ft1);
}

void stub_head(int nat, Node id_node)						/*;stub_head*/
{
	/* Find unique name of package or task stub, and verify that it occurs
	 * in the proper scope.
	 */

	char	*id;
	Symbol	stub_name;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  stub_head");

	find_old(id_node);
	id = N_VAL(id_node);
	stub_name = N_UNQ(id_node);

	if (SCOPE_OF(stub_name) != scope_name ) {
		errmsg_str("specification and stub for % are in different scopes", id,
		  "7.1, 9.1", id_node);
	}

	/* Nature of specification must match that of stub.*/

	if ((nat == na_package && (NATURE(stub_name) != na_package_spec
	  && NATURE(stub_name) != na_generic_package_spec))
	  || (nat == na_task && (NATURE(stub_name) != na_task_type_spec
	  && NATURE(stub_name) != na_task_obj_spec)) ) {
		errmsg_str("Matching specification not found for stub %", id,
		  "7.1, 9.1", id_node);
		if (DECLARED(stub_name) == (Declaredmap)0) 
			DECLARED(stub_name) = dcl_new(0);
	}
}

void save_stub(Node node)							/*;save_stub*/
{
	char	*kind, *stub_name;
	char	*other_unit;
	Symbol	name, unit_unam;
	Node	spec_node, id_node, stmt_node;
	Tuple	env_scope_st, tup;
	Fortup	ft1;
	int	i, si;
	Stubenv ev;

	if (N_KIND(node) ==  as_subprogram_stub) {
		spec_node = N_AST1(node);
		stmt_node = N_AST3(node);
		id_node = N_AST1(spec_node);
		kind = "su";
		/* Transform the node to as_subprogram_stub_tr nearby dropping off the
		 * specification part which contains unnecessary conformance info (in
		 * the formal part). Also the node as_procedure (as_function) is 
		 * unnecessary since this can be determined from the symbol table. Now 
		 * we move the id_node info (name of the subprogram) to the 
		 * as_subprogram_stub_tr node directly and move the statments node to
		 * the N_AST1 field so that the N_UNQ field (N_AST3) can be used.
		 */
		N_KIND(node) = as_subprogram_stub_tr;
		N_AST1(node) = stmt_node;
		N_UNQ(node) = N_UNQ(id_node);
	}
	else {			/* package or task stub */
		id_node = node;
		kind  = "bo";
	}

	/* Save current state of compilation : scope stack and related declared
	 * maps, for a subprogram or module stub.
	 */
	name = N_UNQ(id_node);

	if (cdebug2 > 3) TO_ERRFILE(strjoin("save_stub: ", original_name(name)));

	/* In order to uniquely identify the stub, we create for it a name which
	 * includes the names of all surrounding scopes, with the exception of
	 * the ever-present standard environment and its enclosing scope.
	 */
	stub_name = strjoin(kind, original_name(name));
	i = tup_size(open_scopes)-2;
	stub_name = strjoin(stub_name, ".");
	stub_name = strjoin(stub_name, original_name((Symbol) open_scopes[1]));
	if (i != 1) {
		stub_name = strjoin(stub_name, ".");
		stub_name = strjoin(stub_name, original_name((Symbol) open_scopes[i]));
	}
	/* Ada requires that the identifiers of all subunits of a given library
	 * unit (as well as the name of the library unit itself) be unique.
	 * Check to see of there exists another sub_unit that has the same
	 * identifier a different parent but the same eldest ancestor.
	 */
	FORTUP(other_unit=(char *), lib_stub, ft1);
		if (streq(unit_name_name(other_unit), unit_name_name(stub_name))
		  && streq(stub_ancestor(other_unit), stub_ancestor(stub_name)))
		errmsg("Subunit identifier not unique", "10.2", id_node);
	ENDFORTUP(ft1);

	/* Verify that the stub appears immediately within a compilation unit.*/
	if (!streq(original_name(scope_name), unit_name_name(unit_name)))
		errmsg_l("stubs can only appear in the outermost scope of a " ,
		  "compilation unit", "10.2", id_node);

	/* Install the new stub into the library. */
	update_lib_maps(stub_name, 's');

	/* Save stub environment. 
	 * Perhaps some optimization can be done by have a pointer to the symbol 
	 * table of the parent instead of a complete copy for each stub.
	 *
	 * open_decls := {};
	 * (forall decl = declared(os))
	 *    open_decls(os) := {[nam, decl(nam), SYMBTABF(decl(nam))] :
	 *			nam in domain decl};
	 * end forall;
	 */

	/*unit_unam := declared('STANDARD#0')(stub_name(#stub_name)); */
	unit_unam = dcl_get(DECLARED(symbol_standard0), stub_ancestor(stub_name));

	env_scope_st = tup_new(0);
	FORTUP(tup=(Tuple), scope_st, ft1);
		env_scope_st = tup_with(env_scope_st, (char *) tup_copy(tup));
	ENDFORTUP(ft1);
	tup = tup_new(4);
	tup[1] = (char *) scope_name;
	tup[2] = (char *) tup_copy(open_scopes);
	tup[3] = (char *) tup_copy(used_mods);
	tup[4] = (char *) tup_copy(vis_mods);
	env_scope_st = tup_with(env_scope_st, (char *) tup);
	/* STUB_ENV(stub_name) :=
	 * [ (scope_st + [scope_info]),
	 *   open_decls,
	 *   {[vm, visible(vm)] : vm in vis_mods | vm notin ignore},
	 *   unit_unam,
	 *   SYMBTABF(unit_unam),
	 *   CONTEXT
	 *  ];
	 */
	ev = (Stubenv) stubenv_new();
	ev->ev_scope_st = env_scope_st;
	ev->ev_open_decls = unit_symbtab(unit_unam, 's');
	ev->ev_nodes = tup_copy(unit_nodes);
	ev->ev_unit_unam = unit_unam;
	ev->ev_decmap = dcl_copy(DECLARED(unit_unam));
	ev->ev_context = tup_copy(context);

	if (NATURE(name) == na_task_obj_spec)
		/* Task object. The stub applies to the task type, not the object. */
		N_UNQ(id_node) = TYPE_OF(name);

	N_VAL(node) = stub_name;
	/* Install pointer to saved stub environment */
	si = stub_numbered(stub_name);
	tup = (Tuple) stub_info[si];
	tup[2] = (char *) ev;
	stub_parent_put(stub_name, unit_name);
	stubs_to_write = set_with(stubs_to_write, (char *) si);

	/* allocate a fake proper body for the stub. Needed for handling of
	 * generic stubs.
	 */
	si = unit_number(stub_name);
	pUnits[si]->libInfo.obsolete = string_ds; /*"$D$"*/
}

static Tuple check_separate(Node unit_node)				/*;check_separate*/
{
	/* This procedure restores the environment saved for a stub,
	 * including the original scope stack.
	 */

	Node	a_node, proper_node, spec, name_node;
	char	*name, *parent_unit, *outer_most;
	int	parent_num;
	Symbol	unit_unam;
	Stubenv ev;

	a_node	= N_AST1(unit_node);
	proper_node = N_AST2(unit_node);

	/*  Find identifier of subunit. */
	if (N_KIND(proper_node) == as_subprogram) {
		spec = N_AST1(proper_node);
		name_node = N_AST1(spec);
	}
	else 	/* package body.*/
		name_node = N_AST1(proper_node);
	name = N_VAL(name_node);

	if (cdebug2 > 3) TO_ERRFILE(strjoin("checking separate: ", name));

	ev = (Stubenv) retrieve_env(a_node, name_node);
	if (ev != (Stubenv)0) {
		scope_st = ev->ev_scope_st;
		unit_unam = ev->ev_unit_unam;
		parent_num = stub_parent_get(unit_name);
		parent_unit = pUnits[parent_num]->name;
		all_vis = tup_with(all_vis, (char *)parent_unit);
		/* put name of outer-most scope in standard*/
		outer_most = stub_ancestor(unit_name);
		dcl_undef(DECLARED(symbol_standard0), outer_most);
		dcl_put(DECLARED(symbol_standard0), outer_most, unit_unam);

		/* Reestablish scope of the parent unit, in which compilation of the
		 * subunit will take place.
		 */
		popscope();
#ifdef TBSL
		/* Initialize visibility info. */
		(forall vis_vm = vis(vm))
		    visible(vm) :
		= vis_vm;
		declared(vm) :
		= vis_vm;
		end forall;
#endif
		DECLARED(unit_unam) = dcl_copy(ev->ev_decmap);
		symtab_restore(ev->ev_open_decls);
		return ev->ev_context;
	}
	else return (Tuple)0; /* to indicate error */
}

static Stubenv retrieve_env(Node a_node, Node name_node)	/*;retrieve_env*/
{
	/* Obtain the sequence of parent units of the  subunit. It may be an
	 * expanded name listing all ancestors.
	 */

	Node	id_node;
	char	*name, *expd_name, *stub_nam, *stub_name;
	Fortup	ft1;
	Tuple	tup;
	int	si, stub_err;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  retrieve_env");

	name = N_VAL(name_node);
	expd_name = strjoin(name, "");
	if (N_KIND(a_node) != as_simple_name) {
		id_node = N_AST2(a_node);
		expd_name = strjoin(expd_name, ".");
		expd_name = strjoin(expd_name, N_VAL(id_node));
	}
	while (N_KIND(a_node) != as_simple_name) a_node = N_AST1(a_node);
	expd_name = strjoin(expd_name, ".");
	expd_name = strjoin(expd_name, N_VAL(a_node));
	/* retrieve from library the environment in which a stub was
	 * first seen.
	 */

	stub_err = FALSE;
	stub_name = (char *) 0;
	FORTUP(stub_nam=(char *), lib_stub, ft1);
		if (streq(unit_name_names(stub_nam), expd_name)) {
			if (stub_name == (char *)0) stub_name = stub_nam;
			else if (!streq(stub_name, stub_nam)) stub_err = TRUE;
		}
	ENDFORTUP(ft1);

	if (stub_name == (char *) 0) stub_err = TRUE;

	if (stub_err || !stub_retrieve(stub_name)) {
		errmsg_str("cannot find stub for subunit %", name, "10.2" , name_node);
		unit_name = strjoin("","");
		return (Stubenv)0;
	}
	remove_obsolete_stubs(expd_name);
	unit_name = strjoin(stub_name, "");
	seq_symbol_n = 0;
	init_compunit();
	si = stub_number(stub_name);
	tup = (Tuple) stub_info[si];
	return (Stubenv) tup[2];
}

static void remove_obsolete_stubs(char *name) /*;remove_obsolete_stubs*/
{
	/* If this unit was previously compiled remove possible obsolete stubs 
	 * of it from library.
	 */

	char 	*stub;
	Fortup  ft1;

	FORTUP(stub=(char *), lib_stub, ft1);
		if (streq(stub_ancestors(stub), name))
			lib_stub_put(stub, (char *)0);
	ENDFORTUP(ft1);
}
