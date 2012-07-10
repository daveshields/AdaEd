/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* pack.c: translation of pack.stl */

#define GEN

#include "hdr.h"
#include "libhdr.h"
#include "vars.h"
#include "segment.h"
#include "gvars.h"
#include "ops.h"
#include "type.h"
#include "setprots.h"
#include "statprots.h"
#include "procprots.h"
#include "miscprots.h"
#include "maincaseprots.h"
#include "genprots.h"
#include "gutilprots.h"
#include "gmiscprots.h"
#include "libprots.h"
#include "segmentprots.h"
#include "smiscprots.h"
#include "packprots.h"

extern Segment	CODE_SEGMENT, DATA_SEGMENT, DATA_SEGMENT_MAIN;


/*
 * Chapter 7: Packages
 *  The only problem with packages is the possible presence of tasks
 *  objects in the specification part and the point of their activation
 *  as defined by the RM: on the 'begin' of the package body, if it
 *  exists.
 */

void gen_package(Node pack_node)							/*;gen_package*/
{
	Tuple	tup;
	Node	id_node, decl_node, private_node;
	int 	save_tasks_declared;
	Tuple	save_subprog_specs;
	Symbol	package_name;

	save_tasks_declared = TASKS_DECLARED;
	TASKS_DECLARED      = FALSE;
	save_subprog_specs  = SUBPROG_SPECS;
	SUBPROG_SPECS       = tup_new(0);

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("GEN_PACKAGE", pack_node);
#endif

	id_node = N_AST1(pack_node);
	decl_node = N_AST2(pack_node);
	private_node = N_AST3(pack_node);
	package_name = N_UNQ(id_node);

	next_local_reference(package_name);

	gen_kv(I_PUSH_IMMEDIATE, mu_word, int_const_null_task);
	if (save_tasks_declared) {
		gen_c(I_LINK_TASKS_DECLARED, "save current tasks_declared");
		gen_ks(I_DECLARE, mu_word, package_name);
	}
	else {
		gen_ks(I_DECLARE, mu_word, package_name);
		/* mu_word? */
		gen_ksc(I_POP, mu_word, package_name, "initialize tasks declared");
	}

	compile(decl_node);
	compile(private_node);

	if (TASKS_DECLARED || save_tasks_declared)
		gen_s(I_POP_TASKS_DECLARED, package_name);

	/* needs body already checked by FE */
	tup = tup_new(3);
	tup[1] = (char *) TASKS_DECLARED;
	tup[2] = (char *) 0;
	tup[3] = (char *) tup_copy(SUBPROG_SPECS);
	MISC(package_name) = (char *) tup;
	/* insert warning check in case symbol not package  ds 9-8-85*/
	if (!(NATURE(package_name) == na_package
	  || NATURE(package_name)==na_package_spec)) {
		chaos("pack.c: genpack - setting MISC for symbol ");
	}

	TASKS_DECLARED = save_tasks_declared;
	SUBPROG_SPECS  = save_subprog_specs;

}

void gen_package_body(Node body_node)					/*;gen_package_body*/
{
	/* Process package body that is not a library unit */

	Tuple	tup;
	Symbol	package_name;
	int save_tasks_declared;
	Tuple	save_subprog_specs;
	Node	id_node, decl_node, stmts_node, handler_node;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("GEN_PACKAGE_BODY", body_node);
#endif

	id_node = N_AST1(body_node);
	decl_node = N_AST2(body_node);
	stmts_node = N_AST3(body_node);
	handler_node = N_AST4(body_node);
	package_name = N_UNQ(id_node);

	save_tasks_declared = TASKS_DECLARED;
	tup = (Tuple) MISC(package_name);
	TASKS_DECLARED = (tup != (Tuple)0) ? (int) tup[1] : FALSE;

	save_subprog_specs  = SUBPROG_SPECS;
	/* Note that SUBPROG_SPECS now stored in 3rd MISC entry   ds 7-9-85*/
	SUBPROG_SPECS = (tup != (Tuple)0) ? tup_copy((Tuple) tup[3]) : tup_new(0);

	/* trivial case: this is a dummy package body and no task declared in */
	/*		     the specification part. */
	/*
	 *   if blk=[] and not TASKS_DECLARED then
	 *	TASKS_DECLARED := save_tasks_declared;
	 *	return;
	 *   end if;
	 */

	if (TASKS_DECLARED || save_tasks_declared) {
		gen_ksc(I_PUSH, mu_word, package_name, "retrieve tasks_declared");
		gen(I_LINK_TASKS_DECLARED);
	}

	/*
	 *   if blk = [] then	$ dummy body, TASKS_DECLARED always TRUE
	 *	generate(I_ACTIVATE);
	 *   else
	 */
	compile(decl_node);
	if (TASKS_DECLARED) {
		gen(I_ACTIVATE);
	}
	else if (save_tasks_declared) {
		gen_sc(I_POP_TASKS_DECLARED, package_name, "discard one level");
	}

	compile_body(OPT_NODE, stmts_node, handler_node, TRUE);
	/*   end if; */

	TASKS_DECLARED = save_tasks_declared;
	SUBPROG_SPECS  = save_subprog_specs;
}

void unit_package_spec(Node pack_node)					/*;unit_package_spec*/
{
	/*
	 * Compilation of a library package spec.
	 * As it is a compilation unit, there is no task link to be preserved
	 */

	Node	id_node, decl_node, private_node;
	Symbol	package_name, package_proc;
	Tuple	tup;
	Tuple	local_reference_map_new();
	Symbol package_tasks;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("UNIT_PACKAGE_SPEC", pack_node);
#endif

	id_node = N_AST1(pack_node);
	decl_node = N_AST2(pack_node);
	private_node = N_AST3(pack_node);
	package_name = N_UNQ(id_node);

	TASKS_DECLARED = FALSE;
	CURRENT_LEVEL  = 1;
	LAST_OFFSET	  = -SFP_SIZE;
	MAX_OFFSET	  = 0;
	/* TBSL: see if can free current local reference map before allocating
	 * new one	ds 23-may 
	 */
	LOCAL_REFERENCE_MAP = local_reference_map_new();

	/* Create associated name for initialization proc for spec. */
	/*package_proc		   = package_name+'_spec';*/
	package_proc = sym_new(na_procedure);
	assoc_symbol_put(package_name, INIT_SPEC, package_proc);
	new_symbol(package_proc, na_procedure, symbol_none, tup_new(0), (Symbol)0);
	ORIG_NAME(package_proc) = ORIG_NAME(package_name);
	generate_object(package_proc);
	CURRENT_DATA_SEGMENT = select_entry(SELECT_DATA, package_proc, SLOTS_DATA);
	CURRENT_CODE_SEGMENT = select_entry(SELECT_CODE, package_proc, SLOTS_CODE);
#ifdef MACHINE_CODE
	if (list_code) {
		to_gen_int("	   data slot #", CURRENT_DATA_SEGMENT);
		to_gen_int("	   code slot #", CURRENT_CODE_SEGMENT);
		to_gen(" ");
	}
#endif
	next_global_reference_r(package_proc, CURRENT_CODE_SEGMENT, 0);

	/* Create associated name for initialization of inner tasks.*/
	/*package_tasks	    = package_name+'_tasks';*/
	package_tasks = sym_new(na_obj);
	assoc_symbol_put(package_name, INIT_TASKS, package_tasks);
	/* SETL version gives package_tasks signature with null tuple.
    * This does not correspond to usual form of signature
    * for na_obj, namely a node. Hence in C we set it to
    * null pointer.
    */
	new_symbol(package_tasks, na_obj, symbol_none, (Tuple)0, 
	  (Symbol)package_tasks);
	generate_object(package_tasks);
	/* TBSL: see if byte is appropriate: 
     * next_global_reference_word(package_tasks, [0]);
     */
	next_global_reference_word(package_tasks, 0);

	gen(I_LEAVE_BLOCK);
	gen(I_RAISE);

	compile(decl_node);
	compile(private_node);

	if (TASKS_DECLARED)
		gen_s(I_POP_TASKS_DECLARED, package_tasks);
	gen(I_ENTER_BLOCK);
	gen(I_LEAVE_BLOCK);
	MAX_OFFSET = offset_max(MAX_OFFSET, LAST_OFFSET);
	/* calculate the size of local objects and don't assume it is zero 
    * because it is a package spec. It will not be zero in the case of 
    * nested packages.
    */
	gen_ic(I_DATA, MAX_OFFSET-SFP_SIZE, "Local variables");/*GBSL*/
	gen(I_END);

	tup = tup_new(3);
	tup[1] = (char *) TASKS_DECLARED;
	tup[2] = (char *) SPECS_DECLARED;
	tup[3] = (char *) SUBPROG_SPECS; /* note 3rd comp was formerly signature*/
	MISC(package_name)	   = (char *) tup;
	CODE_SEGMENT_MAP = segment_map_put(CODE_SEGMENT_MAP, CURRENT_CODE_SEGMENT,
	  CODE_SEGMENT);
}

void unit_package_body(Node body_node)					/*;unit_package_body*/
{
	/*
	 * Compilation of a library package body.
	 * As it is a compilation unit, there is no task link to be preserved
	 */

	Node	id_node, decl_node, stmts_node, handler_node;
	Symbol	package_name, package_proc, name, temp_name;
	Tuple	tup, stub_tup;
	int		si;
	Segment	stemplate;
	struct	tt_subprog *tptr;
	int		i, n, stub_cs; 
	unsigned int patch_addr;
	Stubenv	ev;
	Tuple	local_reference_map_new();

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("UNIT_PACKAGE_BODY", body_node);
#endif

	id_node = N_AST1(body_node);
	decl_node = N_AST2(body_node);
	stmts_node = N_AST3(body_node);
	handler_node = N_AST4(body_node);
	package_name = N_UNQ(id_node);
	tup = (Tuple) MISC(package_name);
	TASKS_DECLARED = (tup != (Tuple)0) ? (int) tup[1] : FALSE;

	SUBPROG_SPECS = (tup != (Tuple)0) ? tup_copy((Tuple) tup[3]) : tup_new(0);

	/* trivial case: this is a dummy package body and no task declared in */
	/* the specification part. If it is a subunit, we must generate it */
	/* anyhow, as the corresponding call has been generated. */
	/*
	 *   if blk=[] and not TASKS_DECLARED and not is_subunit(unit_name) then
	 *	return;
	 *   end if;
	 */

	/* Create associated name for proc. to elaborate body. */
	/* package_proc		   = package_name+'_body';*/
	/* Only add the package_proc to GENERATED_OBJECTS if it is not
     * a subunit because in the case of a subunit it already exists
     * in the unit which contained the stub.
     */
	if (is_subunit(unit_name)) {
		package_proc = assoc_symbol_get(package_name, INIT_BODY);
	}
	else {
		package_proc = sym_new(na_procedure);
		assoc_symbol_put(package_name, INIT_BODY, package_proc);
		generate_object(package_proc);
	}
	NATURE   (package_proc) = na_procedure;
	TYPE_OF  (package_proc) = symbol_none;
	SIGNATURE(package_proc) = tup_new(0);
	ORIG_NAME(package_proc) = ORIG_NAME(package_name);
	CURRENT_DATA_SEGMENT = select_entry(SELECT_DATA, package_proc, SLOTS_DATA);
	if (is_subunit(unit_name)) {
		si = stub_numbered(unit_name);
		stub_tup = (Tuple) stub_info[si];
		ev = (Stubenv) stub_tup[2];
		/*CURRENT_LEVEL	 = STUB_ENV(unit_name)(10);*/
		/* CURRENT_LEVEL = ev->ev_current_level; */
		CURRENT_LEVEL = current_level_get(unit_name);
		CURRENT_CODE_SEGMENT = select_entry(SELECT_CODE, package_proc,
		  SLOTS_CODE_BORROWED);
		/* package_procedure object and template already generated */
	}
	else {
		CURRENT_LEVEL	   = 1;
		CURRENT_CODE_SEGMENT = select_entry(SELECT_CODE, package_proc,
		  SLOTS_CODE);
		next_global_reference_r(package_proc, CURRENT_CODE_SEGMENT, 0);
	}
	LAST_OFFSET	       = -SFP_SIZE;
	MAX_OFFSET	       = 0;
	/* TBSL: see if can free prior value of local reference map DS 23-may*/
	LOCAL_REFERENCE_MAP = local_reference_map_new();
	/* TBSL: see if can free current value of relay set */
	RELAY_SET	       = tup_new(0);
#ifdef MACHINE_CODE
	if (list_code) {
		to_gen_int("	   data slot # ", CURRENT_DATA_SEGMENT);
		to_gen_int("	   code slot # ", CURRENT_CODE_SEGMENT);
		to_gen(" ");
	}
#endif
	gen(I_LEAVE_BLOCK);
	gen(I_RAISE);

	if (TASKS_DECLARED) {
		gen_ks(I_PUSH, mu_word, assoc_symbol_get(package_name, INIT_TASKS));
		gen(I_LINK_TASKS_DECLARED);
	}

	compile(decl_node);
	if (TASKS_DECLARED)
		gen(I_ACTIVATE);

	compile_body(OPT_NODE, stmts_node, handler_node, FALSE);

	/*MAX_OFFSET max= abs LAST_OFFSET;*/
	MAX_OFFSET = offset_max(MAX_OFFSET, LAST_OFFSET);
	/* GBSL: check that MAX_OFFSET and SFP_SIZE in bytes, else need to adjust*/
	gen_ic(I_DATA, MAX_OFFSET-SFP_SIZE, "size of local objects");/*GBSL*/
	gen(I_END);

	/* This subprogram has no parameters... */

	if (is_subunit(unit_name)) {
		si = stub_numbered(unit_name); /* get stub index */
		stub_tup = (Tuple) stub_info[si];
		ev = (Stubenv) stub_tup[2];
		ev->ev_relay_set = RELAY_SET; /* see if copy needed below*/
		/*STUB_ENV(unit_name)(8) = RELAY_SET;*/
		/*STUB_ENV(unit_name)(9) = DANGLING_RELAY_SETS;*/
		ev->ev_dangling_relay_set  = DANGLING_RELAY_SETS;
	}
	else if (tup_size(RELAY_SET) != 0 || tup_size(DANGLING_RELAY_SETS) != 0) {
		chaos("Relay set at level 1");
	}

	/* Remaining elements in SUBPROG_PATCH are procedures declared in a */
	/* package spec whose body is separate. Generate corresponding */
	/* procedure templates. Those templates must be declared as */
	/* generated objects, as they will be referenced by other units. */
	/* Information in symbol tables is irrelevant, and left as OM. */

	n = tup_size(SUBPROG_PATCH);
	/*loop forall patch_addr = SUBPROG_PATCH(name) do*/
	for (i = 1; i <= n; i+=2) {
		name = (Symbol) SUBPROG_PATCH[i];
		patch_addr = (unsigned int) SUBPROG_PATCH[i+1];
		temp_name = new_unique_name("proc_template"); /* associated name */
		assoc_symbol_put(name, PROC_TEMPLATE, temp_name);
		generate_object(temp_name);
		stub_cs = select_entry(SELECT_CODE, name, SLOTS_CODE_BORROWED);
		stemplate = template_new(TT_SUBPROG, -1, WORDS_SUBPROG, (int **)&tptr);
		tptr->cs = stub_cs;
		tptr->relay_slot = stub_cs; /* relay_slot */
		next_global_reference_template(temp_name, stemplate);
		segment_free(stemplate);
		reference_of(temp_name);
		segment_set_pos(CODE_SEGMENT, patch_addr, 0);
		segment_put_ref(CODE_SEGMENT, REFERENCE_SEGMENT, (int)REFERENCE_OFFSET);
		segment_set_pos(CODE_SEGMENT, 0, 2); /* reposition to end */
	}

	CODE_SEGMENT_MAP = segment_map_put(CODE_SEGMENT_MAP, CURRENT_CODE_SEGMENT,
	  CODE_SEGMENT);

#ifdef MACHINE_CODE
	if (list_code) {
		to_gen(" ");
		to_gen(" --- Local reference map :");
		to_gen_int("	   Parameter offset = ", MAX_OFFSET);
		print_ref_map_local();
	}
#endif
}
