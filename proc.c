/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#define GEN

#include "hdr.h"
#include "libhdr.h"
#include "vars.h"
#include "segment.h"
#include "gvars.h"
#include "ops.h"
#include "type.h"
#include "axqrprots.h"
#include "namprots.h"
#include "maincaseprots.h"
#include "exprprots.h"
#include "dbxprots.h"
#include "miscprots.h"
#include "libprots.h"
#include "statprots.h"
#include "setprots.h"
#include "genprots.h"
#include "segmentprots.h"
#include "gmiscprots.h"
#include "smiscprots.h"
#include "gutilprots.h"
#include "procprots.h"

extern Segment	CODE_SEGMENT, DATA_SEGMENT, DATA_SEGMENT_MAIN;


void gen_subprogram_spec(Node proc_node)				/*;gen_subprogram_spec*/
{
	/* subprogram spec.
	 * Just reserve a code slot, and GENERATE the procedure object.
	 * If the spec occurs elsewhere than immediately in the declarative part
	 * of a compilation unit, it may need a relay set, but we don't know it
	 * yet. So, we must prepare for a dynamically elaborated procedure.
	 */

	int	 save_current_code_segment;
	Symbol	proc_name;
	Tuple	predef_tuple;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("GEN_SUBPROGRAM_SPEC", proc_node);
#endif

	proc_name   = N_UNQ(proc_node);
	/*tag         = NATURE(proc_name);*/

	predef_tuple = (Tuple) MISC(proc_name);
	if (predef_tuple != (Tuple)0) { /*predef */
	}
	else {
		save_current_code_segment = CURRENT_CODE_SEGMENT;
		CURRENT_CODE_SEGMENT = select_entry(SELECT_CODE, proc_name, SLOTS_CODE);
#ifdef TRACE
		if (list_code) {
			to_gen(" ");
			to_gen_unam("--------------------------------------",
			    ORIG_NAME(proc_name), "--------------");
			to_gen_int("     code slot # ", CURRENT_CODE_SEGMENT);
			to_gen(" ");
		}
#endif

		if (CURRENT_LEVEL == 1) { /* No relay set needed */
			next_global_reference_r(proc_name, CURRENT_CODE_SEGMENT, 0);
		}
		else {
			next_local_reference(proc_name);
		}
		/* Empty segment */
		CODE_SEGMENT_MAP = segment_map_put(CODE_SEGMENT_MAP,
		  CURRENT_CODE_SEGMENT, segment_new(SEGMENT_KIND_CODE, 0));
		SPECS_DECLARED += 1;
		if (!tup_mem((char *) proc_name, SUBPROG_SPECS)) {
			SUBPROG_SPECS = tup_with(SUBPROG_SPECS, (char *) proc_name);
		}
#ifdef MACHINE_CODE
		if (list_code) {
			to_gen_unam("-------- end  ", ORIG_NAME(proc_name), 
			    " -----------");
		}
#endif
		CURRENT_CODE_SEGMENT = save_current_code_segment;
		if (CURRENT_LEVEL != 1) {
			gen(I_END);          /* Purge peep-hole */
			subprog_patch_put(proc_name, PC() + 1);
			gen_rc(I_PUSH_EFFECTIVE_ADDRESS, explicit_ref_0,
			  "subprog. template");
			gen(I_CREATE_STRUC);
			gen_s(I_UPDATE_AND_DISCARD, proc_name);
		}
	} /* PREDEF */
}

/* Procedure elaboration */

void gen_subprogram(Node proc_node)						/*;gen_subprogram*/
{
	/*
	 *   To generate code there are several delicate steps to perform, as
	 *   the output of that is not only the proper code to elaborate the
	 *   subprogram (which may even be reduced to nothing), but to produce
	 *   a new code statement, adding some information to the previous
	 *   code generation environment, and preserving the previous
	 *   environment by "burying" it in local variables.
	 *
	 *   Here is a summary of the steps for this procedure:
	 *
	 *   1) Assign a code slot number to the new procedure/function.
	 *      Note: if the corresponding subprogram spec has been compiled, the
	 *            code slot is already defined.
	 *
	 *   2) The relay set must be build. The current relay set is preserved,
	 *      and a variable is put into the relay set when it cannot be found
	 *      neither in the global nor the local reference map.
	 *
	 *   3) Compute offsets for the parameters, including offset for the
	 *      types of arrays, and for the value returned by a function.
	 *      The parameters are located below the stack frame pointer, but
	 *      room shall be left for the return informations
	 *
	 *   4) After preserving the previous environment, generate code for
	 *      the procedure/function in a new clean segment, starting with
	 *      the "catch-all" exception handler.
	 *
	 *   5) generate code to elaborate the procedure/function (if not
	 *      static)
	 *
	 *   6) restore previous environment
	 */

	Node 	decl_node, stmt_node, handler_node;
	Symbol	proc_name, fname, ftype, t_name, temp_name, name;
	int		tag, fmode, save_current_code_segment;
	int		simple_recursive_proc, has_separate_spec;
	int		const_addr_size, parameter_offset;
	unsigned int	location; /*OFFSET */
	Fortup	ft1;
	int		proc_code_segment, patch_addr;
	Tuple	save_local_reference_map, save_relay_set, save_subprog_specs;
	unsigned int	save_last_offset, save_max_offset;
	Tuple	save_parameter_set, save_code_patch_set, save_data_patch_set;
	Tuple	temp_relay_set, relay_table;
	Segment	tseg, save_code_segment;
	unsigned int roff;
	int		i, dn, rn;
	struct tt_subprog *tptr;

	const_addr_size = mu_size(mu_addr);
	gen(I_END);  /* purge peep-hole buffer */

	/*
	 *-----
	 *  1.
	 */
	stmt_node = N_AST1(proc_node);
	decl_node = N_AST2(proc_node);
	proc_name = N_UNQ(proc_node);
	handler_node = N_AST4(proc_node);
	tag         = NATURE(proc_name);

#ifdef TRACE
	if (debug_flag)
		gen_trace_symbol("GEN_SUBPROGRAM", proc_name);
#endif

	/*
	 *-----
	 *  2.
	 */

	save_relay_set           = RELAY_SET;
	save_local_reference_map = LOCAL_REFERENCE_MAP;
	save_subprog_specs       = SUBPROG_SPECS;
	save_last_offset         = LAST_OFFSET;
	save_max_offset          = MAX_OFFSET;
	save_parameter_set       = PARAMETER_SET;
	save_code_patch_set      = CODE_PATCH_SET;
	save_data_patch_set      = DATA_PATCH_SET;
	save_code_segment        = CODE_SEGMENT;
	save_current_code_segment= CURRENT_CODE_SEGMENT;

	RELAY_SET           = tup_new(0);
	LOCAL_REFERENCE_MAP = tup_new(0);
	SUBPROG_SPECS       = tup_new(0);
	LAST_OFFSET         = -SFP_SIZE;
	MAX_OFFSET          = 0;
	PARAMETER_SET       = tup_new(0);
	CODE_PATCH_SET      = tup_new(0);
	DATA_PATCH_SET      = tup_new(0);
	CODE_SEGMENT        = segment_new(SEGMENT_KIND_CODE, 0);
	if (is_defined(proc_name)) { /* exists separate subprog spec */
		CURRENT_CODE_SEGMENT = select_entry(SELECT_CODE, proc_name,
		  SLOTS_CODE_BORROWED);
	}
	else {
		CURRENT_CODE_SEGMENT = select_entry(SELECT_CODE, proc_name, SLOTS_CODE);
	}

	parameter_offset = -const_addr_size;
	FORTUP(fname = (Symbol), SIGNATURE(proc_name), ft1);
		fmode = NATURE(fname);
		ftype = TYPE_OF(fname);
		if (!tup_mem((char *)fname, PARAMETER_SET)) {
			PARAMETER_SET = tup_with(PARAMETER_SET, (char *) fname);
		}
		if (is_array_type(ftype)) {
			/* Array addresses are mu_dble */
			/*t_name= fname+'_type'; $ associate name*/
			t_name= new_unique_name("fname_type");
			assoc_symbol_put(fname, FORMAL_TEMPLATE, t_name);
			local_reference_map_put(t_name, parameter_offset);
			parameter_offset           -= const_addr_size;
			if (!tup_mem((char *) t_name, PARAMETER_SET)) {
				PARAMETER_SET = tup_with(PARAMETER_SET, (char *) t_name);
			}
		}
		local_reference_map_put(fname, (int) parameter_offset);
		parameter_offset          -= const_addr_size;
		if ((is_simple_type(ftype) &&  (fmode != na_in))) {
			/* scalar out and in out parameters takes 2 stacks locations */
			/* one for returned na_out value, the other for temporary na_in */
			parameter_offset -= const_addr_size;
		}
	ENDFORTUP(ft1);

	if (tag == na_function ||
	  tag == na_function_spec  ) { /* temporary kludge */
		parameter_offset = parameter_offset + const_addr_size
		  - mu_size(kind_of(TYPE_OF(proc_name)));
		t_name = new_unique_name("return_temp");
		/* associated name */
		assoc_symbol_put(proc_name, RETURN_TEMPLATE, t_name);
		generate_object(t_name);
		if (!tup_mem((char *)t_name, PARAMETER_SET)) {
			PARAMETER_SET  = tup_with(PARAMETER_SET, (char *) t_name);
		}
		local_reference_map_put(t_name, (int) parameter_offset);
	}

#ifdef MACHINE_CODE
	if (list_code) {
#ifdef TBSN
		f_name = formatted_name([tag, proc_name]);
#endif
		to_gen(" ");
		to_gen_unam("-----------------------------",
		    ORIG_NAME(proc_name), "-------------------");
		to_gen_int("     code slot # ", CURRENT_CODE_SEGMENT);
		to_gen(" ");
	}
#endif
	/* "catch-all exception handler" */
	gen(I_LEAVE_BLOCK);
	gen(I_RAISE);
	if (tag == na_task_body) {
		/* task trap */
		gen_ic(I_TERMINATE, 2, "task trap");
	}

	compile_body(decl_node, stmt_node, handler_node, FALSE);

	MAX_OFFSET = offset_max(MAX_OFFSET, LAST_OFFSET);
	/* GBSL: see if offset in next op in bytes or needs adjustment */
	gen_ic(I_DATA, MAX_OFFSET-SFP_SIZE, "size of local objects");/*GBSL*/
	gen(I_END);

#ifdef MACHINE_CODE
	if (list_code) {
		to_gen(" ");
		to_gen(" --- Local reference map :");
		to_gen_int("    Parameter offset = ", MAX_OFFSET);
		print_ref_map_local();
		/*TO_GEN("-------- end of '+f_name+' -----------");*/
		to_gen("-------- end -----------");
	}
#endif

	/*
	 *  The set of local variables for the compiled subprogram is now
	 *  complete, therefore we can patch the addresses of the parameters.
	 */

	FORTUP(location = (unsigned), CODE_PATCH_SET, ft1);
		update_code((int) location, MAX_OFFSET);
	ENDFORTUP(ft1);
	FORTUP(location = (unsigned), DATA_PATCH_SET, ft1);
		segment_put_off(DATA_SEGMENT, location, 
	      segment_get_off(DATA_SEGMENT, (int) location) - MAX_OFFSET);
	ENDFORTUP(ft1);
	/* Note: as this subprogram is not a compilation unit, it cannot */
	/* contain stubs. The following serves only for the printout of */
	/* LOCAL_REFERENCE_MAP: */
	FORTUP(name = (Symbol), PARAMETER_SET, ft1);
		local_reference_map_put(name, local_reference_map_get(name)-MAX_OFFSET);
	ENDFORTUP(ft1);
	CODE_SEGMENT_MAP = segment_map_put(CODE_SEGMENT_MAP, CURRENT_CODE_SEGMENT,
	  CODE_SEGMENT);
	temp_relay_set       = RELAY_SET;
	CODE_SEGMENT         = save_code_segment;
	proc_code_segment    = CURRENT_CODE_SEGMENT;
	CURRENT_CODE_SEGMENT = save_current_code_segment;
	CODE_PATCH_SET       = save_code_patch_set;
	DATA_PATCH_SET       = save_data_patch_set;
	PARAMETER_SET        = save_parameter_set;
	LOCAL_REFERENCE_MAP  = save_local_reference_map;
	LAST_OFFSET          = save_last_offset;
	SUBPROG_SPECS        = save_subprog_specs;
	RELAY_SET            = save_relay_set;
	MAX_OFFSET           = save_max_offset;

	/*
	 * Now, considering the content of the relay-set, plus the fact that we
	 * may have already decided that the subprogram object is local, we
	 * can proceed to the elaboration of the subprogram.
	 */

	simple_recursive_proc =
	  (tup_size(temp_relay_set) == 1 && proc_name == (Symbol)temp_relay_set[1]);
	has_separate_spec = tup_mem((char *) proc_name,  SUBPROG_SPECS);
	if ((tup_size(temp_relay_set) == 0 || simple_recursive_proc)
	  && ! has_separate_spec) {
		/* next_global_reference(proc_name,
		 *  [proc_code_segment,
		 *  simple_recursive_proc ? 1 : 0]);
		 */
		tseg = segment_new(SEGMENT_KIND_DATA, 2);
		segment_set_pos(tseg, 0, 0); /* reposition to start */
		segment_put_word(tseg, proc_code_segment);
		segment_put_word(tseg, simple_recursive_proc != 0 ? 1 : 0 );
		next_global_reference_segment(proc_name, tseg);
		segment_free(tseg);
		if (simple_recursive_proc) {
			reference_of(proc_name);
			segment_put_int(DATA_SEGMENT, REFERENCE_SEGMENT);
			segment_put_int(DATA_SEGMENT, (int) REFERENCE_OFFSET);
			/*DATA_SEGMENT += reference_of(proc_name);*/
		}
	}
	else if (CURRENT_LEVEL == 1) {
		if (tup_size(temp_relay_set) != 0 || simple_recursive_proc) {
#ifdef DEBUG
			FORTUP(name = (Symbol), temp_relay_set, ft1);
				zpsym(name);
			ENDFORTUP(ft1);
#endif
			chaos("Relay set at level 1");
#ifdef TRACE
			if (debug_flag)
				gen_trace_symbols("GEN_SUBPROGRAM", temp_relay_set);
#endif
			return;
		}
	}
	else {
		if (! has_separate_spec) {
			next_local_reference(proc_name);
			gen(I_END);          /* Purge peep-hole */
			subprog_patch_put(proc_name, PC() + 1);
			gen_rc(I_PUSH_EFFECTIVE_ADDRESS, explicit_ref_0,
			  "subprogram template");
			gen(I_CREATE_STRUC);
			gen_s(I_UPDATE_AND_DISCARD, proc_name);
		}

		/* Build subprogram template. The call to reference_of will */
		/* automatically add to the current relay set objects in */
		/* temp_relay_set not already in it. If current parameters are */
		/* referred, care must be taken to patch the address in the data */
		/* segment and not at the current position in the code segment. */

		/* Use PROC_TEMPLATE if defined (as can be the case for stubs),
		 * otherwise, create PROC_TEMPLATE symbol.
		 */
		if (assoc_symbol_exists(proc_name, PROC_TEMPLATE)) {
			temp_name = assoc_symbol_get(proc_name, PROC_TEMPLATE);
		}
		else { /* otherwise create new symbol and use it for template */
			temp_name = new_unique_name(":proc_template");
			assoc_symbol_put(proc_name, PROC_TEMPLATE, temp_name);
			generate_object(temp_name);
		}
		relay_table = tup_new(0);
		FORTUP(name = (Symbol), temp_relay_set, ft1);
			if (tup_mem((char *) name, PARAMETER_SET)) {
				relay_table  =  tup_with(relay_table, (char *)
			    local_reference_map_get(name));
				/*DATA_PATCH_SET with= #DATA_SEGMENT + 4 + #relay_table;*/
#ifdef TBSN
				DATA_PATCH_SET = tup_with(DATA_PATCH_SET, (char *)
			    DATA_SEGMENT->seg_maxpos-1);
				/* TBSL
				 * Review that 4 is right - it is some sort of offset in data
				 * segment review that getting lastp position in DATA SEGMENT
				 * properly
				 */
				DATA_PATCH_SET = tup_with(DATA_PATCH_SET, (char *) 4);
				DATA_PATCH_SET = tup_with(DATA_PATCH_SET,
				  (char *) tup_size(relay_table));
#endif
				DATA_PATCH_SET = tup_with(DATA_PATCH_SET, (char *)
			    (DATA_SEGMENT->seg_maxpos - 1 + 4 + tup_size(relay_table)) );
			}
			else {
				reference_of(name);
				relay_table = tup_with(relay_table, (char *) REFERENCE_OFFSET);
			}
		ENDFORTUP(ft1);

		if (is_defined(temp_name)) {
			/* Subprogram template already generated => this a body of a */
			/* proc whose spec has been declared in the visible part of a */
			/* package whose body is separate (the so called HA-HA! case). */
			/*DANGLING_RELAY_SETS += [proc_code_segment, #relay_table] +
	 		 *	relay_table;
	 		 */
			DANGLING_RELAY_SETS = tup_with(DANGLING_RELAY_SETS, (char *)
			  proc_code_segment);
			DANGLING_RELAY_SETS = tup_with(DANGLING_RELAY_SETS, 
			  (char *) tup_size(relay_table));
			dn = tup_size(DANGLING_RELAY_SETS);
			rn = tup_size(relay_table);
			if (rn != 0) { /* if relay table to append */
				DANGLING_RELAY_SETS = tup_exp(DANGLING_RELAY_SETS, dn+rn);
				for (i = 1; i <= rn; i++) {
					DANGLING_RELAY_SETS[dn+i] = relay_table[i];
				}
			}
		}
		else {
			/* next_global_reference(temp_name,
	 		 *	      [tt_subprog, #relay_table, proc_code_segment, 0]
	 		 *	     + relay_table);
	 		 */
			tseg = template_new(TT_SUBPROG, tup_size(relay_table),
			  WORDS_SUBPROG, (int **)&tptr);
			tptr->cs = proc_code_segment;
			tptr->relay_slot = 0;
			FORTUP(roff = (unsigned int), relay_table, ft1);
				segment_put_word(tseg, (int) roff);
			ENDFORTUP(ft1);
			next_global_reference_template(temp_name, tseg);
			segment_free(tseg);
			patch_addr                 = subprog_patch_get(proc_name);
			subprog_patch_undef(proc_name); 		 /* No more needed */
			gen(I_END); /* flush peep-hole stack before patching */
			reference_of(temp_name);
			/*CODE_SEGMENT(patch_addr)   = REFERENCE_SEGMENT;*/
			patch_code_byte(patch_addr, REFERENCE_SEGMENT);
			patch_code(patch_addr, (int)REFERENCE_OFFSET);
		}
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, temp_name);
		gen_s(I_SUBPROGRAM, proc_name);
	}
}

void unit_subprog_spec(Node proc_node)						/*;subprog_spec*/
{
	/*
	 * separatly compiled subprogram spec.
	 * Just reserve a code slot and a data slot.
	 * The procedure object will be generated by compilation of the body, in
	 * order to save one data segment.
	 */

	Symbol	proc_name;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("UNIT_SUBPROG_SPEC", proc_node);
#endif

	proc_name   = N_UNQ(proc_node);
	/*tag         = NATURE(proc_name);*/

	CURRENT_DATA_SEGMENT  = select_entry(SELECT_DATA, proc_name, SLOTS_DATA);
	CURRENT_CODE_SEGMENT  = select_entry(SELECT_CODE, proc_name, SLOTS_CODE);
#ifdef MACHINE_CODE
	if (list_code) {
		to_gen_int("     data slot # ", CURRENT_DATA_SEGMENT);
		to_gen_int("     code slot # ", CURRENT_CODE_SEGMENT);
		to_gen(" ");
	}
#endif

	next_global_reference_def(proc_name); /* just enter the reference into */
	/* reference table (no relay set) */
	/* Empty segment */
	CODE_SEGMENT_MAP = segment_map_put(CODE_SEGMENT_MAP, CURRENT_CODE_SEGMENT,
	  CODE_SEGMENT);
}

void unit_subprog(Node proc_node)							/*;unit_subprog*/
{
	/*
	 * Roughly similar to GEN_SUBPROGRAM, but for a compilation unit
	 * Beware: if the procedure spec has been separately compiled, the
	 *         procedure object has NOT been generated.
	 * It may be a task body in the case of a subunit
	 */

	Node	decl_node, stmt_node, handler_node;
	Symbol	proc_name, fname, ftype, t_name, temp_name, name;
	int		tag, fmode;
	int		stub_cs;
	Fortup	ft1;
	int		parameter_offset, const_addr_size, i, patch_addr, si;
	unsigned int	location;
	Segment	tseg;
	Tuple	local_reference_map_new(), stubtup;
	Stubenv	ev;
	struct tt_subprog *tptr;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("UNIT_SUBPROG", proc_node);
#endif
	const_addr_size = mu_size(mu_addr);
	stmt_node = N_AST1(proc_node);
	decl_node = N_AST2(proc_node);
	proc_name = N_UNQ(proc_node);
	handler_node = N_AST4(proc_node);
	tag         = NATURE(proc_name);

	if (is_subunit(unit_name)) {
		CURRENT_LEVEL = current_level_get(unit_name);
	}
	else {
		CURRENT_LEVEL = 1;
		/* set is_main flag for this unit if it is parameterless. 
		 * it is already known that it is a subprogram which is not a subunit
		 */
		pUnits[unit_number_now]->isMain = (tup_size(SIGNATURE(proc_name)) == 0
		  && NATURE(proc_name) == na_procedure);
	}
	LAST_OFFSET         = -SFP_SIZE;
	MAX_OFFSET          = 0;
	RELAY_SET           = tup_new(0);
	CODE_PATCH_SET      = tup_new(0);
	DATA_PATCH_SET      = tup_new(0);
	LOCAL_REFERENCE_MAP = local_reference_map_new();

	if (is_subunit(unit_name)) {
		CURRENT_CODE_SEGMENT = select_entry(SELECT_CODE, proc_name,
		  SLOTS_CODE_BORROWED);
		CURRENT_DATA_SEGMENT = select_entry(SELECT_DATA, proc_name,
		  SLOTS_DATA);
	}
	else if (is_defined(proc_name)) {	 /* separately compiled spec */
		CURRENT_CODE_SEGMENT = select_entry(SELECT_CODE, proc_name,
		  SLOTS_CODE_BORROWED);
		CURRENT_DATA_SEGMENT = select_entry(SELECT_DATA, proc_name,
		  SLOTS_DATA_BORROWED);
	}
	else {
		CURRENT_CODE_SEGMENT = select_entry(SELECT_CODE, proc_name, SLOTS_CODE);
		CURRENT_DATA_SEGMENT = select_entry(SELECT_DATA, proc_name, SLOTS_DATA);
	}
	if (! is_subunit(unit_name)) { /* procedure object and template */
		/* already generated for stubs */
		next_global_reference_r(proc_name, CURRENT_CODE_SEGMENT, 0);
	}
#ifdef MACHINE_CODE
	if (list_code) {
		to_gen_int("     data slot # ", CURRENT_DATA_SEGMENT);
		to_gen_int("     code slot # ", CURRENT_CODE_SEGMENT);
		to_gen(" ");
	}
#endif
	parameter_offset = -const_addr_size;
	FORTUP( fname = (Symbol), SIGNATURE(proc_name), ft1);
		fmode = NATURE(fname);
		ftype = TYPE_OF(fname);
		if (is_array_type(ftype)) {
			/* Array addresses are mu_dble */
			t_name = new_unique_name("formal_temp"); /* associated_name */
			assoc_symbol_put(fname, FORMAL_TEMPLATE, t_name);
			local_reference_map_put(t_name, parameter_offset);
			parameter_offset -= const_addr_size;
			if (!tup_mem((char *)t_name, PARAMETER_SET)) {
				PARAMETER_SET = tup_with(PARAMETER_SET, (char *) t_name);
			}
		}
		local_reference_map_put(fname, parameter_offset);
		if (!tup_mem((char *) fname, PARAMETER_SET)) {
			PARAMETER_SET = tup_with(PARAMETER_SET, (char *) fname);
		}
		parameter_offset -= const_addr_size;
		if ((is_simple_type(ftype) && (fmode != na_in))) {
			/* scalar out and in out parameters takes 2 stacks locations */
			/* one for returned na_out value, the other for temporary na_in */
			parameter_offset -= const_addr_size;
		}
	ENDFORTUP(ft1);
	if (tag == na_function
	  || tag == na_function_spec ) {/* to be removed when tag ok for stubs */
		parameter_offset = parameter_offset+const_addr_size
		  - mu_size(kind_of(TYPE_OF(proc_name)));
		t_name = new_unique_name("return_temp");
		/* associated name*/
		assoc_symbol_put(proc_name, RETURN_TEMPLATE, t_name);
		generate_object(t_name);
		if (!tup_mem((char *)t_name, PARAMETER_SET))
			PARAMETER_SET = tup_with(PARAMETER_SET, (char *) t_name);
		local_reference_map_put(t_name, parameter_offset);
	}

	gen(I_LEAVE_BLOCK);
	gen(I_RAISE);
	if (tag == na_task_body) {
		/* task trap */
		gen_ic(I_TERMINATE, 2, "task trap");
	}
	compile_body(decl_node, stmt_node, handler_node, FALSE);

	/* MAX_OFFSET max= abs LAST_OFFSET;*/
	MAX_OFFSET = offset_max(MAX_OFFSET, LAST_OFFSET);
	/* GBSL see if 2nd arg in next op in bytes or if needs adjustment */
	gen_ic(I_DATA, MAX_OFFSET-SFP_SIZE, "size of local objects");/*GBSL*/
	gen(I_END);

	/*  The set of local variables for the compiled subprogram is now
	 *  complete, therefore we can patch the addresses of the parameters.
	 *  we must update local_reference_map also as it will be reused by
	 *  the subunits.
	 */
	FORTUP(location = (unsigned), CODE_PATCH_SET, ft1);
		update_code((int) location, MAX_OFFSET);
	ENDFORTUP(ft1);
	FORTUP(location = (unsigned), DATA_PATCH_SET, ft1);
		segment_put_off(DATA_SEGMENT, location, 
	      segment_get_off(DATA_SEGMENT, location) - MAX_OFFSET);
	ENDFORTUP(ft1);
	FORTUP(name = (Symbol), PARAMETER_SET, ft1);
		local_reference_map_put(name, local_reference_map_get(name)-MAX_OFFSET);
	ENDFORTUP(ft1);

	if (is_subunit(unit_name)) {
		si = stub_numbered(unit_name);
		stubtup = (Tuple) stub_info[si];
		ev = (Stubenv) stubtup[2];
		ev->ev_relay_set = RELAY_SET; /* TBSL - is copy needed ? */
		ev->ev_dangling_relay_set = tup_new(0);
		if (tup_size(DANGLING_RELAY_SETS) != 0) {
			/* should happen only with packages */
			compiler_error("Dangling relay set at level 1");
#ifdef TRACE
			if (debug_flag)
				gen_trace_symbols("UNIT_SUBPROG", DANGLING_RELAY_SETS);
#endif
		}
	}
	else if (tup_size(RELAY_SET) != 0 || tup_size(DANGLING_RELAY_SETS) != 0) {
#ifdef DEBUG
		printf("relay set\n");
		FORTUP(name = (Symbol), RELAY_SET, ft1);
			zpsym(name);
		ENDFORTUP(ft1);
		printf("dangling relay sets\n");
		zptup(DANGLING_RELAY_SETS);
#endif
		chaos("Relay set at level 1");
#ifdef TRACE
		if (debug_flag) {
			gen_trace_symbols("UNIT_SUBPROG (RELAY SET)", RELAY_SET );
			gen_trace_symbols("UNIT_SUBPROG (DANGLING_RELAY_SETS)" ,
			  DANGLING_RELAY_SETS);
		}
#endif
	}

	/* Remaining elements in SUBPROG_PATCH are procedures declared in a */
	/* package spec whose body is separate. Generate corresponding */
	/* procedure templates. Those templates must be declared as */
	/* generated objects, as they will be referenced by other units. */
	/* Information in symbol tables is irrelevant, and left as OM. */
	gen(I_END); /* flush peep-hole stack before patching */
	for (i = 1; i <= tup_size(SUBPROG_PATCH); i += 2) {
		name = (Symbol) SUBPROG_PATCH[i];
		patch_addr = (int) SUBPROG_PATCH[i+1];
		temp_name = new_unique_name("proc_temp");
		/* associated name */
		assoc_symbol_put(name, PROC_TEMPLATE, temp_name);
		generate_object(temp_name);
		stub_cs = select_entry(SELECT_CODE, name, SLOTS_CODE_BORROWED);
		/* next_global_reference(temp_name, [tt_subprog,
		 *					-1,
		 *					stub_cs,
		 *				stub_cs]);  
		 */
		tseg = template_new(TT_SUBPROG, -1, WORDS_SUBPROG, (int **)&tptr);
		tptr->cs = stub_cs;
		tptr->relay_slot =  stub_cs; /* relay slot */
		next_global_reference_segment(temp_name, tseg);
		segment_free(tseg);
		reference_of(temp_name);
		patch_code_byte(patch_addr, REFERENCE_SEGMENT);
		patch_code(patch_addr, REFERENCE_OFFSET);
	}
	/* TBSL: JPR indicated SUBPROG_PATCH dead after above loop
	 * check this		ds 3-5-85
	 */

	CODE_SEGMENT_MAP = segment_map_put(CODE_SEGMENT_MAP, CURRENT_CODE_SEGMENT,
	  CODE_SEGMENT);

#ifdef MACHINE_CODE
	if (list_code) {
		to_gen(" ");
		to_gen(" --- Local reference map :");
		to_gen_int("    Parameter offset = ", MAX_OFFSET);
		print_ref_map_local();
	}
#endif
}

/* Parameter passing (Prelude) */

void gen_prelude(Symbol proc_name, Node args_node)			/*;gen_prelude*/
{
	Tuple	formals, actuals;
	Node	arg_node, pre_node, addr_node;
	Symbol	fname, ftype, arg_name, arg_type, qual_arg_type, addr_type;
	Symbol	a_temp, f_temp;
	int		fmode, nk;
	Fortup	ft1;

#ifdef TRACE
	if (debug_flag) {
		gen_trace_symbol("GEN_PRELUDE_P", proc_name);
		gen_trace_node("GEN_PRELUDE_A", args_node);
	}
#endif

	formals   = tup_copy(SIGNATURE(proc_name));
	actuals   = tup_copy(N_LIST(args_node));
	/* tup_copy above needed due to use of tup_frome below */
	while (tup_size(formals)) {
		fname = (Symbol) tup_frome(formals);
		fmode = NATURE(fname);
		ftype = TYPE_OF(fname);
		arg_node = (Node) tup_frome(actuals);

		while (N_KIND(arg_node) == as_insert) {
			FORTUP(pre_node = (Node), N_LIST(arg_node), ft1);
				compile(pre_node);
			ENDFORTUP(ft1);
			arg_node = N_AST1(arg_node);
		}

		if ((arg_node == OPT_NODE) || (N_KIND (arg_node) == as_raise)) {
			/* Special case: address of arg already on tos. Used for the */
			/* call to the initialization proc of an allocated object. */
			/* the test of raise has been added since the static
             evaluation of the effective parameter may have been 
             transformed as an exception */
			if (N_KIND (arg_node) == as_raise)
				compile (arg_node); 
			continue;
		}

		nk = N_KIND(arg_node);
		qual_arg_type = get_type(arg_node);

		/* the qual* must not be removed since they may result from a
		 * constraint imposed by the semantic analyser: this is valid for in 
		 * parameters
		 */

		/* To be removed when FE does not emit qual */
		if ((fmode != na_in) && (nk == as_qual_aindex || nk == as_qual_alength
		  || nk == as_qual_adiscr || nk == as_qual_range
		  || nk == as_qual_index || nk == as_qual_discr || nk == as_qual_sub)) {
			arg_node = N_AST1(arg_node);
		}

		arg_name = N_UNQ(arg_node);
		arg_type = get_type(arg_node);

		if (is_simple_type(ftype)) {
			/* Scalar, access, or task types. */
			/* For those types, Ada requires that parameter passing is done */
			/* by copy => create a temporary to hold the value. */

			if (fmode == na_in) {
#ifdef TBSN
				if (is_ivalue(arg_node) && !not_included(arg_type, ftype)) {
					value = get_ivalue(arg_node);
					/* the argument to get_constant_name must be a Segment, so
					 * must turn result of get_ivalue into a segment ds 6-7-85
					 */
					seg = segment_new(SEGMENT_KIND_DATA, 1);
					segment_put_const(seg, value);
					/*arg_name = get_constant_name(value);*/
					arg_name = get_constant_name(seg);
					segment_free(seg);
					/* useful only for gen_postlude: */
					N_UNQ(arg_node) = arg_name;
					/* generate(I_PUSH_EFFECTIVE_ADDRESS, arg_name,
					 *   ' = ' + str value);
					 */
					gen_s(I_PUSH_EFFECTIVE_ADDRESS, arg_name);
				}
#endif
				if (is_simple_name(arg_node) && arg_name != (Symbol)0
				  && NATURE(arg_name) == na_constant && !is_renaming(arg_name)
				  && ! not_included(arg_type, ftype)) {
					gen_s(I_PUSH_EFFECTIVE_ADDRESS, arg_name);
				}
				else {
					gen_value(arg_node);
					optional_qual(arg_type, ftype);
					gen_k(I_CREATE_COPY, kind_of(ftype));
				}
			}
			else if (fmode == na_inout) {
				/* a) address and value of the actual */
				if (N_KIND(arg_node) == as_convert) {
					addr_node = N_AST2(arg_node);
					addr_type = get_type(addr_node);
					gen_address(addr_node);
					gen_k(I_DUPLICATE, mu_addr);
					if (is_access_type(ftype)) {
						/* apply constraint check before (dummy) conversion */
						gen_k(I_DEREF, kind_of(addr_type));
						optional_qual(addr_type, ftype);
						gen_convert(addr_type, ftype) ;
					}
					else {
						/* for numeric types, convert first, then constrain */
						gen_k(I_DEREF, kind_of(addr_type));
						gen_convert(addr_type, ftype) ;
						optional_qual(arg_type, ftype) ;
					}
				}
				else {
					gen_address(arg_node);
					gen_k(I_DUPLICATE, mu_addr);
					gen_k(I_DEREF, kind_of(arg_type));
					optional_qual(arg_type, ftype);
				}

				a_temp = new_unique_name("inout_tempo");
				assoc_symbol_put(fname, ACTUAL_TEMPLATE, a_temp);
				next_local_reference(a_temp);

				/* c) create a temporary with this value */
				gen_k(I_CREATE_COPY, kind_of(ftype));
				gen_s(I_UPDATE, a_temp);
			}
			else if (fmode == na_out) {
				/* a) address of the actual */
				if (N_KIND(arg_node) == as_convert) {
					addr_node = N_AST2(arg_node);
					gen_address(addr_node);
				}
				else {
					gen_address(arg_node);
				}

				/* b) create an empty temporary */
				gen_k(I_CREATE, kind_of(ftype));
			}

			/* Structured types */
		}
		else if (is_array_type(ftype)) {
			gen_value(arg_node);
			if (!is_unconstrained(ftype) && ftype != arg_type)
				gen_s(I_QUAL_INDEX, ftype);
		}
		else if (is_record_type(ftype)) {
			gen_value(arg_node);

			if (ftype == arg_type || is_unconstrained(ftype)) {
				;
			}
			else if (!is_unconstrained(arg_type)) {
				if (has_discriminant(arg_type))
					gen_s(I_QUAL_DISCR, ftype);
			}
			else {
				/*  there are discriminants */
				/*  the formal is constrained, */
				/*  the actual is unconstrained */
				/*      parameter passing by copy ! */
				gen_s(I_QUAL_DISCR, ftype);
				if (fmode == na_inout || fmode == na_out) {
					if (!assoc_symbol_exists(fname, ACTUAL_TEMPLATE)) {
						/* Create temporary variables if not done by previous */
						/* call. */
						a_temp = new_unique_name("fname_actual");
						f_temp = new_unique_name("fname_formal");
						next_local_reference(a_temp);
						next_local_reference(f_temp);
						assoc_symbol_put(fname, ACTUAL_TEMPLATE, a_temp);
						assoc_symbol_put(fname, FORMAL_TEMPLATE, f_temp);
					}
					gen_s(I_UPDATE, assoc_symbol_get(fname, ACTUAL_TEMPLATE));
				}
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, ftype);
				gen(I_CREATE_COPY_STRUC);
				if (fmode != na_out) {
					/* set constrained bit */
					gen_k(I_DUPLICATE, mu_addr);
					gen_kv(I_PUSH_IMMEDIATE, kind_of(symbol_boolean),
					  int_const(TRUE));
					gen_k(I_MOVE, kind_of(symbol_boolean));
				}
			}
		}
		else {
			compiler_error_s("Prelude, ftype =", ftype);
		}
	}
	tup_free(formals); 
	tup_free(actuals);
}

/* Parameter passing (Postlude) */

void gen_postlude(Symbol proc_name, Node args_node)			/*;gen_postlude*/
{
	Tuple	formals;
	Tuple	actuals;
	Node	arg_node, addr_node;
	Symbol	fname, ftype, arg_type, addr_type, formal_obj_type,
	    actual_obj_type, arg_name;
	int		fmode, nk;

#ifdef TRACE
	if (debug_flag) {
		gen_trace_symbol("GEN_POSTLUDE_P", proc_name);
		gen_trace_node("GEN_POSTLUDE_A", args_node);
	}
#endif

	formals   = tup_copy(SIGNATURE(proc_name));
	actuals   = tup_copy(N_LIST(args_node));
	/* tup_copy needed above due to use of tup_fromb below */
	while (tup_size(formals)) {
		fname  = (Symbol) tup_fromb(formals);
		fmode   = NATURE (fname);
		ftype   = TYPE_OF(fname);
		arg_node = (Node) tup_fromb(actuals);

		while (N_KIND(arg_node) == as_insert)
			arg_node = N_AST1(arg_node);

		if (arg_node == OPT_NODE) {
			/* Special case: address was on tos, must stay there. Used for */
			/* the call to the initialization proc of an allocated object. */
			continue;
		}
		nk = N_KIND(arg_node);
		if (nk == as_qual_aindex || nk == as_qual_alength
		  || nk == as_qual_adiscr || nk == as_qual_range
		  || nk == as_qual_index || nk == as_qual_discr || nk == as_qual_sub) {
			arg_node = N_AST1(arg_node);
		}

		arg_type = get_type(arg_node);

		/* Scalar or access (or task) types.
		 * For those types, ada requires that parameter passing is done by copy,
		 * thus for out and inout parameters we must copy-out the result.
		 * NB: tasks can be only of mode na_in
		 */

		if (is_simple_type(ftype)) {

			if (fmode == na_in) {
				/* If possible, retrieve name of argument for the peep-hole */
				arg_name = N_UNQ(arg_node);
#ifdef TBSL
				if (is_ivalue(arg_node)) {
					arg_name = N_UNQ(arg_node);
					gen_ks(I_DISCARD_ADDR, 1, arg_name);
				}
#endif
				if (is_simple_name(arg_node) && arg_name != (Symbol)0
				  && NATURE(arg_name) == na_constant && !is_renaming(arg_name)
				  && ! not_included(arg_type, ftype)) {
					gen_ks(I_DISCARD_ADDR, 1, arg_name);
				}
				else {
					gen(I_UNCREATE);
				}
			}
			else if (fmode == na_inout || fmode == na_out) {
				gen_k(I_DEREF, kind_of(ftype));
				if (N_KIND(arg_node) == as_convert) {
					addr_node = N_AST2(arg_node);
					addr_type = get_type(addr_node);
					/* On exit, the target type of the conversion is the type
					 * of the actual, not that of the formal (used below). 
					 */
					arg_type = addr_type ;
					gen_convert(ftype, arg_type);
					if (!is_access_type(ftype))
						gen_s(I_QUAL_RANGE, addr_type);
				}

				if (is_access_type(ftype) ) {
					formal_obj_type = (Symbol) designated_type(ftype);
					actual_obj_type = (Symbol) designated_type(arg_type);
					if (formal_obj_type != actual_obj_type
					  && !is_unconstrained(actual_obj_type)) {
						if (is_array_type(actual_obj_type) ) {
							gen_access_qual(as_qual_index, actual_obj_type);
						}
						else if (is_record_type(actual_obj_type)) {
							gen_access_qual(as_qual_discr, actual_obj_type);
						}
						else {	 /* simple type */
							;  /* No need to qual range */
						}
					}
				}
				else if (N_KIND(arg_node) != as_convert
				  && not_included(ftype, arg_type) ) {
					/* never the case for convert */
					gen_s(I_QUAL_RANGE, arg_type);
				}
				gen_k(I_MOVE, kind_of(ftype));
				if(fmode == na_inout) {
					gen_s(I_PUSH_EFFECTIVE_ADDRESS,
					  assoc_symbol_get(fname, ACTUAL_TEMPLATE));
					gen(I_UNCREATE);
				}
			}

			/* Structured types */
		}
		else if (is_array_type(ftype)) {
			gen_ks(I_DISCARD_ADDR, 1, arg_type);
			if (is_simple_name(arg_node) ) {
				gen_ks(I_DISCARD_ADDR, 1, N_UNQ(arg_node));
			}
			else if (is_ivalue(arg_node)) {
				arg_name = get_constant_name(array_ivalue(arg_node));
				gen_ks(I_DISCARD_ADDR, 1, arg_name);
			}
			else {
				gen_ks(I_DISCARD_ADDR, 1, (Symbol)0);
			}
		}
		else if (is_record_type(ftype)) {
			if (is_unconstrained(ftype) || !is_unconstrained(arg_type)
			  || fmode == na_in ) {
				if (is_simple_name(arg_node) ) {
					gen_ks(I_DISCARD_ADDR, 1, N_UNQ(arg_node));
				}
				else if (is_ivalue(arg_node)) {
					/* note that record_ivalue returns a segment */
					arg_name = get_constant_name(record_ivalue(arg_node));
					gen_ks(I_DISCARD_ADDR, 1, arg_name);
				}
				else {
					gen_ks(I_DISCARD_ADDR, 1, (Symbol)0);
				}
			}
			else {
				/*  there are discriminants */
				/*  the mode is na_out or na_inout */
				/*  the formal is constrained, */
				/*  the actual is unconstrained */
				/*      parameter passing by copy ! */
				gen_s(I_UPDATE_AND_DISCARD,
				  assoc_symbol_get(fname, FORMAL_TEMPLATE));
				gen_s(I_PUSH_EFFECTIVE_ADDRESS,
				  assoc_symbol_get(fname, ACTUAL_TEMPLATE));
				gen_s(I_PUSH_EFFECTIVE_ADDRESS,
				  assoc_symbol_get(fname, FORMAL_TEMPLATE));
				gen_s(I_RECORD_MOVE, arg_type);
			}
		}
		else {
			compiler_error_s("Postlude, ftype =", ftype);
		}
	}
	tup_free(formals); 
	tup_free(actuals);
}

void gen_accept(Symbol entry_name, Node body_node, Node after_node)
																/*;gen_accept*/
{
	Tuple	formals;
	Symbol	fname, ftype, t_name;
	int		fmode;
	Fortup	ft1;
	int		save_last_offset;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("GEN_ACCEPT", body_node);
#endif

	formals          = SIGNATURE(entry_name);
	save_last_offset = LAST_OFFSET;

	/* preserve caller: */
	FORTUP(fname = (Symbol), formals, ft1);
		fmode = NATURE(fname);
		ftype = TYPE_OF(fname);
		if (is_array_type(ftype)) {
			/* Array addresses are mu_dble */
			t_name= new_unique_name("fname_type");
			assoc_symbol_put(fname, FORMAL_TEMPLATE, t_name);
			next_local_reference(t_name);
			gen_s(I_UPDATE_AND_DISCARD, t_name);
		}
		next_local_reference(fname);
		gen_s(I_UPDATE_AND_DISCARD, fname);
		if ((is_simple_type(ftype) && (fmode != na_in))) {
			/* scalar out and in out parameters take 2 stacks locations */
			/* one for returned na_out value, the other for temporary na_in */
			gen_ks(I_DISCARD_ADDR, 1, (Symbol)0);
		}
	ENDFORTUP(ft1);

	/* The body of the accept may contain a return statement, which should
	 * be translated as an exit block followed by a jump to the end of
	 * of the block. We set symbol_accept_return to the null case as an
	 * initialization; this symbol will be set non-null if the accept
	 * body contains a return, in which case we use it as the label
	 * corresponding to the end of the body.
	 */
	symbol_accept_return = (Symbol) 0; /* in case return within accept */
	if (body_node != OPT_NODE) {
		compile(body_node);
	}

	gen(I_END_RENDEZVOUS);
	symbol_accept_return = (Symbol) 0; /* reset */

	if (after_node != OPT_NODE) {
		compile(after_node);
	}
	/*MAX_OFFSET max= abs LAST_OFFSET;*/
	MAX_OFFSET = offset_max(MAX_OFFSET, LAST_OFFSET);
	LAST_OFFSET   = save_last_offset;
}

int offset_max(int m, int l)									/*;offset_max*/
{
	/* used to translate MAX_OFFSET max:= abs(LAST_OFFSET) */
	if (l < 0) l = -l;
	if (m < l) m = l;
	return m;
}
