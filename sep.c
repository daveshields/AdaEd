/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#define GEN

#include "hdr.h"
#include "ifile.h"
#include "slot.h"
#include "libhdr.h"
#include "vars.h"
#include "gvars.h"
#include "ops.h"
#include "type.h"
#include "segment.h"
#include "setprots.h"
#include "axqrprots.h"
#include "genprots.h"
#include "gutilprots.h"
#include "segmentprots.h"
#include "readprots.h"
#include "gmiscprots.h"
#include "libprots.h"
#include "sepprots.h"

extern Segment	CODE_SEGMENT, DATA_SEGMENT, DATA_SEGMENT_MAIN;

/* Chapter 10: Separate compilation
 * Stubs
 */

void gen_stub(Node stub_node)									/*;gen_stub*/
{
	/* This procedure generate the code to elaborate the proper body of the
	 * body stub, at the place of the corresponding stub.
	 * In any case, a spec corresponding to the stub has been elaborated.
	 * A data slot is assigned to the subunit (the code segment has already
	 * been assigned by the spec declaration, in the case of a subprogram).
	 */

	Segment	stemplate;
	int		tag, stub_cs, si;
	char	*u_nam;
	Symbol	name, temp_name, package_proc;
	unsigned int patch_addr;
	struct tt_subprog *tptr;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("GEN_STUB", stub_node);
#endif

	STUBS_IN_UNIT = TRUE;

	u_nam = N_VAL(stub_node);
	read_stub_short(lib_stub_get(u_nam), u_nam, "st1");
	si = stub_numbered(u_nam);
	collect_stub_node_units(si);

	tag   = N_KIND(stub_node);
	if (tag == as_subprogram_stub_tr) {
		name	 = N_UNQ(stub_node);
	}
	else {
		name	 = N_UNQ(stub_node);
		if (NATURE(name) == na_generic_package) return;
	}
	/* In the case where the stub is nested in a package body the current level
	 * is set wrong, since it will be incremented after the call to gen_stub
	 * and will be off by one in the stub field. However no correct fix is
	 * known at this time. (BB  2-27-86)
	 */
	current_level_put(u_nam, CURRENT_LEVEL);

	lib_stub_put(u_nam, AISFILENAME);

	switch (tag) {

	case(as_subprogram_stub_tr): 
	case(as_task_stub):
		if (tag == as_task_stub) {
			name = assoc_symbol_get(name, TASK_INIT_PROC);
		}
		stub_cs = select_entry(SELECT_CODE, name, SLOTS_CODE_BORROWED);

		if (CURRENT_LEVEL > 1) { /* may need relay set */
			temp_name = (assoc_symbol_exists(name, PROC_TEMPLATE)) ?
			  assoc_symbol_get(name, PROC_TEMPLATE) : (Symbol)0;

			/* The template is already generated in the case of a subprogram */
			/* declared in the spec of a package whose body is separate */
			if (temp_name ==(Symbol)0 || !is_defined(temp_name)) {
				temp_name = new_unique_name("proc_template"); /* assoc. name */
				assoc_symbol_put(name, PROC_TEMPLATE, temp_name);
				generate_object(temp_name);
				stemplate = template_new(TT_SUBPROG, -1, WORDS_SUBPROG,
				  (int **)&tptr);
				tptr->cs =  stub_cs;
				tptr->relay_slot =  stub_cs; /* relay slot */
				next_global_reference_template(temp_name, stemplate);
				segment_free(stemplate);
				patch_addr = subprog_patch_get(name);
				subprog_patch_undef(name); /* No more needed */
				gen(I_END); /* flush peep-hole stack before patching */
				reference_of(temp_name);
				segment_set_pos(CODE_SEGMENT, patch_addr, 0);
				segment_put_ref(CODE_SEGMENT, REFERENCE_SEGMENT,
				  REFERENCE_OFFSET);
				segment_set_pos(CODE_SEGMENT, 0, 2); /* position at end */
			}
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, temp_name);
			gen_s(I_SUBPROGRAM, name);
		}
		break;

	case(as_package_stub):
		/* We must preserve the signature of this package (and of its */
		/* sub-packages) in its stub_environment, as long as the FE doesn't */
		/* generate the signature of packages. The following may preserve */
		/* too much, but it doesn't hurt: */
#ifdef TBSL
		/* ev already retrieved above */
		 *
		 * STUB_ENV(u_nam)(11) = { [pack, SIGNATURE(pack)]:
		 *			nat=NATURE(pack) | nat = na_package_spec		};
		 */
#endif
	    package_proc = new_unique_name("proc_template"); /* assoc. name */
		temp_name	= new_unique_name("pack_proc_template");
		assoc_symbol_put(name, INIT_BODY, package_proc);
		assoc_symbol_put(package_proc, PROC_TEMPLATE, temp_name);
		generate_object(package_proc);
		generate_object(temp_name);
		stub_cs	= select_entry(SELECT_CODE, package_proc, SLOTS_CODE);
		/*CODE_SEGMENT_MAP(stub_cs) := [];*/
		/* Is this freeing a code seg or allocating a new one ?? ds 6-12-85*/
		CODE_SEGMENT_MAP = segment_map_put(CODE_SEGMENT_MAP,
		  stub_cs, segment_new(SEGMENT_KIND_CODE, 0));
		next_local_reference(package_proc);
		stemplate = template_new(TT_SUBPROG, -1, WORDS_SUBPROG,
		  (int **)&tptr);
		tptr->cs =  stub_cs;
		tptr->relay_slot =  stub_cs; /* relay slot */
		next_global_reference_template(temp_name, stemplate);
		segment_free(stemplate);
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, temp_name);
		gen(I_CREATE_STRUC);
		gen_s(I_UPDATE_AND_DISCARD, package_proc);
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, temp_name);
		gen_s(I_SUBPROGRAM, package_proc);
		gen_s(I_CALL, package_proc);

	default: 		 /* Stub as the body of a generic unit.... */
		;

	}
	stubs_to_write = set_with(stubs_to_write, (char *) si);
}
