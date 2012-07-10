/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#define GEN

/* dbg - debugger interface for adagen */
#include "hdr.h"
#include "vars.h"
#include "segment.h"
#include "gvars.h"
#include "type.h"
#include "dbgprots.h"

static Segment zseg;

void zpds(Segment seg)											/*;zpds*/
{
	/* dump data segment, including initial data */

	int i, *data;

	printf("Segment %d x%x ", (int)seg, seg);
	if (seg->seg_kind == SEGMENT_KIND_CODE) printf(" code");
	else printf(" data");
	printf(" size %d pos %d max_pos %d dim %d ext %d\n", seg->seg_size,
	  seg->seg_pos, seg->seg_maxpos, seg->seg_dim, seg->seg_extend);
	if (seg->seg_kind == SEGMENT_KIND_CODE) return;
	data = (int *) seg->seg_data;
	for (i = 0; i < seg->seg_maxpos && i < 10; i++)
		printf(" %d_%u", i, data[i]);
	printf("\n");
}

void zpttd()													/*;zpttd*/
{
	if (zseg != (Segment) 0)
		zptt(zseg);
}

void zptt(Segment seg)											/*;zptt*/
{
	/* segment dump to terminal */

	struct tt_i_range  *tti;
	int    *data;

	if (seg == (Segment) 0) {
		printf("null segment\n");
		return;
	}
	data = (int *) seg->seg_data;
	tti = I_RANGE(data);
	switch(tti->ttype) {

	case TT_I_RANGE:
		printf("tt_i_range %d ilow %d ihigh %d\n", tti->object_size, 
		  tti->ilow,
		  tti->ihigh);
		break;

	case TT_FL_RANGE: /* Floating point template */
		printf("tt_fl_range %d %g fllow %g flhigh %g\n",
		   FL_RANGE(tti)->object_size,
		   FL_RANGE(tti)->fllow,
		   FL_RANGE(tti)->flhigh);
		break;

	case TT_ENUM:
		/* Enumeration(sub)type template
		 * For tt_enum case, literal values immediately follow, one for each
		 * case in the range. Each literal value consists of word giving length
		 * of value followed by that number of further words(with one character
		 * per word) giving the characters of the literal.
		 */

		printf("tt_enum%d elow %d ehigh %d \n",
		  tti->object_size,
		  E_RANGE(tti)->elow, E_RANGE(tti)->ehigh);

		break;

	case TT_E_RANGE:
		printf("tt_enum%d elow %d ehigh %u ebase %u eoff %d\n",
		  tti->object_size,
		  E_RANGE(tti)->elow, E_RANGE(tti)->ehigh);
		break;

	case TT_FX_RANGE: 	/* Fixed point template */

		printf("tt_fx_range %d small_exp_2 %d small_exp_5\n",
		  tti->object_size,
		  FX_RANGE(tti)->small_exp_2,
		  FX_RANGE(tti)->small_exp_5);
		printf(" %d fxlow %ld %ld fxhigh\n",
		  FX_RANGE(tti)->fxlow,
		  FX_RANGE(tti)->fxhigh);
		break;

	case TT_ACCESS: 	/* Access template */

		printf("tt_access %d master_task %d \n",
		  tti->object_size,
		  ACCESS(tti)->master_task);
		break;

	case TT_U_ARRAY: /* Unconstrained or constrained array template */

		break;

	case TT_C_ARRAY: /* Unconstrained or constrained array template */

		printf("tt_u_array %d dim %d component_base %d component_offset %u \n",
		  tti->object_size,
		  ARRAY(tti)->component_base,
		  ARRAY(tti)->component_offset);
		printf(" index1_base %u index1_offset %u \n",
		  ARRAY(tti)->component_base,
		  ARRAY(tti)->component_offset);
		break;

	case TT_S_ARRAY: 	/* Simple array template */

		printf("tt_s_array %d component_size %d index_size %d \n",
		  tti->object_size,
		  S_ARRAY(tti)->component_size,
		  S_ARRAY(tti)->index_size);
		printf("salow %d sahigh %d\n",
		  S_ARRAY(tti)->salow,
		  S_ARRAY(tti)->sahigh);
		break;

	case TT_D_ARRAY: /* Template for types depending on discriminants */

		printf("tt_d_array %d dbase %u doff %u nb_discr_d %d\n",
		  tti->object_size,
		  D_TYPE(tti)->dbase, D_TYPE(tti)->doff, D_TYPE(tti)->nb_discr_d);
		break;

	case TT_RECORD: 	/* Template for simple record */


		printf("tt_record %d nb_field %d \n", tti->object_size, 
		  RECORD(tti)->nb_field);
		break;

	case TT_U_RECORD: 	/* Template for unconstrained record */

		printf("tt_u_record %d nb_field_u %d nb_discr_u %d nb_fixed_u \n",
		  tti->object_size, U_RECORD(tti)->nb_field_u,
		  U_RECORD(tti)->nb_discr_u,
		  U_RECORD(tti)->nb_fixed_u);
		printf(" variant %d first_case %d\n",
		  U_RECORD(tti)->variant,
		  U_RECORD(tti)->first_case);
		/* field table follows here */

		break;

	case TT_V_RECORD:
		printf("tt_v_record %d nb_field_u %d nb_discr_u %d nb_fixed_u \n",
		  tti->object_size, U_RECORD(tti)->nb_field_u,
		  U_RECORD(tti)->nb_discr_u,
		  U_RECORD(tti)->nb_fixed_u);
		printf(" variant %d first_case %d\n",
		  U_RECORD(tti)->variant,
		  U_RECORD(tti)->first_case);
		break;

	case TT_C_RECORD: 	/* Template for constrained record */

		printf("tt_c_record %d cbase %d coff %d nb_discr_c \n",
		  C_RECORD(tti)->object_size,
		  C_RECORD(tti)->cbase,
		  C_RECORD(tti)->coff,
		  C_RECORD(tti)->nb_discr_c);
		break;

	case TT_D_RECORD: /* Template for types depending on discriminants */

		printf("tt_d_record %d dbase %d doff %d nb_discr_d \n",
		  D_TYPE(tti)->object_size,
		  D_TYPE(tti)->dbase,
		  D_TYPE(tti)->doff,
		  D_TYPE(tti)->nb_discr_d);
		/* entries for discriminants follow here */

		break;

	case TT_TASK: 		/* Task type template */

		printf("tt_task %d priority %u body_base %u body_off %u \n",
		  tti->object_size,
		  TASK(tti)->priority,
		  TASK(tti)->body_base,
		  TASK(tti)->body_off);
		printf("nb_entries %d nb_families %u\n",
		  TASK(tti)->nb_entries,
		  TASK(tti)->nb_families);
		/* entry table follows here */
		break;

	case TT_SUBPROG: 	/* Subprogram template */
		printf("tt_subprog %d cs %u relay_slot %u\n",
		  tti->object_size,
		  SUBPROG(tti)->cs,
		  SUBPROG(tti)->relay_slot);
		break;

	default:
		printf("unknown kind %d\n", tti->ttype);
	}
}
