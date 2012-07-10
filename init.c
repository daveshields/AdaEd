/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#define GEN

#include "hdr.h"
#include "vars.h"
#include "gvars.h"
#include "libhdr.h"
#include "segment.h"
#include "slot.h"
#include "ifile.h"
#include "readprots.h"
#include "setprots.h"
#include "genprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "arithprots.h"
#include "axqrprots.h"
#include "initprots.h"

static Tuple precedes_map_new();
static void init_predef_exceptions();
static void init_predef_exception(int, int, int, char *);

/* These are defined here since type Segment not known in gvars.[ch] */
Segment	CODE_SEGMENT, DATA_SEGMENT, DATA_SEGMENT_MAIN;
Segment FIELD_TABLE, VARIANT_TABLE;
Tuple units_in_compilation;

/* INITALIZATIONS AND FINALIZATION
 * General initialization
 */

void initialize_1()											/*;initialize_1*/
{
	/*
	 * Initializes global variables that are to be kept between the two
	 * phases of generation.
	 */

	int	i;

	/* initialize FIELD_TABLE and VARIANT_TABLE. These are data segments
	 * that are reset to be empty but are not reallocated for each unit
	 */
	FIELD_TABLE = segment_new(SEGMENT_KIND_DATA, 0);
	VARIANT_TABLE = segment_new(SEGMENT_KIND_DATA, 0);
	/* tree maps */
	ivalue_1 = int_fri(1); 
	ivalue_10 = int_fri(10);
	int_const_0 = int_const(0);
	rat_value_10 = rat_fri(ivalue_1, ivalue_10);

	int_const_null_task = int_const(-1);

	/*initializations of variables used only by generator */
	/* explicit_ref_0 is used to pass addresses to be filled in later, and
	 * corresponds to [0, 0] case in SETL version.
	 */
	explicit_ref_0 = explicit_ref_new(0, 0);
	global_reference_tuple = tup_new(0);

	N_SIDE(OPT_NODE) = FALSE;

	/* AXQ maps: */
	CODE_SEGMENT_MAP = tup_new(0);
	DATA_SEGMENT_MAP = tup_new(0);
	/* Global variables */
	EMAP = tup_new(0);
#ifdef TBSN
	PREDEF_UNITS	   = [[], {}];
	/* These are handled using EMAP in C version */
	STATIC_DEPTH	   = {
	};
	POSITION	   = {
	};
	PATCHES	   = {
	};
	EQUAL	   = {
	};
#endif
	CODE_PATCH_SET  = tup_new(0);
	DATA_PATCH_SET  = tup_new(0);
	PARAMETER_SET   = tup_new(0);
	RELAY_SET	   = tup_new(0);
#ifdef TBSN
	axqfiles_read   = {
		'_MEMORY'	};
	instruction_stack	= [];
	deleted_instructions = 0;
	BTIME		= 0;
	optimizable_codes	= domain automat0 +/{
		{x, y	}
:
	[x, y] in domain(automat1)+domain(automat2)};
#endif
	/*	Slots initialization */
	/* INIT_SLOTS and MAX_INDEX are procedures in C version, defined at
	 * the end of this file
	 */
	DATA_SLOTS = tup_new(0);
	CODE_SLOTS = tup_new(0);
	/*
	 * EXCEPTION_SLOTS = { ['CONSTRAINT_ERROR', 1],
	 *			['NUMERIC_ERROR',    2],
	 *			['PROGRAM_ERROR',    3],
	 *			['STORAGE_ERROR',    4],
	 *			['TASKING_ERROR',    5]
	 *			['SYSTEM_ERROR',    6]
	 *			};
	 */
	EXCEPTION_SLOTS = tup_new(5);
	EXCEPTION_SLOTS[1] = (char *) slot_new(symbol_constraint_error, 1);
	EXCEPTION_SLOTS[2] = (char *) slot_new(symbol_numeric_error, 2);
	EXCEPTION_SLOTS[3] = (char *) slot_new(symbol_program_error, 3);
	EXCEPTION_SLOTS[4] = (char *) slot_new(symbol_storage_error, 4);
	EXCEPTION_SLOTS[5] = (char *) slot_new(symbol_tasking_error, 5);
	if (!compiling_predef)  {
		/* if not compiling predef, make room for predef slots */
		EXCEPTION_SLOTS = tup_exp(EXCEPTION_SLOTS, 15);
		init_predef_exceptions();
	}

	PRECEDES_MAP = precedes_map_new();

	compilation_table = tup_new(num_predef_units);
	for (i = 1; i <= num_predef_units; i++) compilation_table[i] = (char *) i;
	late_instances    = tup_new(8);
	late_instances[1] = strjoin("spSEQUENTIAL_IO", "");
	late_instances[2] = strjoin("boSEQUENTIAL_IO", "");
	late_instances[3] = strjoin("spDIRECT_IO", "");
	late_instances[4] = strjoin("boDIRECT_IO", "");
	late_instances[5] = strjoin("ssUNCHECKED_DEALLOCATION", "");
	late_instances[6] = strjoin("suUNCHECKED_DEALLOCATION", "");
	late_instances[7] = strjoin("ssUNCHECKED_CONVERSION", "");
	late_instances[8] = strjoin("suUNCHECKED_CONVERSION", "");

	stubs_to_write = set_new(0);
	units_in_compilation = tup_new(0);
	/* integer arithmetic */
	/* ADA_MIN_INTEGER and ADA_MAX_INTEGER are defined in adasem vars.c */

	/* 'standard' symbol table
	 * Warning : values are given for SETL only 
	 * IN CASE OF CHANGES IN THESE VALUES REPORT CHANGE INTO THE 
	 * BINDER (Initialization of idle_task data segment). 
	 */
}

void initialize_2()											/*;initialize_2*/
{
	/*
	 * Initializations of file, of variables depending on the option string,
	 * and of variables that are to be reset between the two phases
	 */

	Axq	axq;
	/* Variables */

#ifdef TBSL
	STIME	   = time;
#endif
	ada_line	   = 0;
	NB_INSTRUCTIONS = 0;
	NB_STATEMENTS   = 0;

	/* tree map */

	if (!new_library) {
		axq = (Axq) emalloct(sizeof(Axq_s), "axq");
		load_library(axq);
	}
}

/* print_data_segment moved to segment.c */

/* TBSL: Note that INIT_SLOTS should be a procedure, as it is a read-only
 * set
 * It is referenced only by select_entry once initialized, as is the case
 * also with MAX_INDEX.
 */
int init_slots(int kind)								/*;init_slots*/
{
	int n;
	if (compiling_predef) {
		if (kind == SLOTS_DATA) n =  2;
		else if (kind == SLOTS_CODE) n =  3;
		else if (kind == SLOTS_EXCEPTION)  n = 5;
		else chaos("init_slots bad kind");
	}
	else {
		if (kind == SLOTS_DATA)
		n = 8;
		else if (kind == SLOTS_CODE)
		n = 11;
		else if (kind == SLOTS_EXCEPTION)  n =  15;
		else chaos("init_slots bad kind");
	}
	return n;
}

int max_index(int kind)											/*;max_index*/
{
	if (kind == SLOTS_DATA) return 255;
	else if (kind == SLOTS_CODE) return 32767;
	else if (kind == SLOTS_EXCEPTION) return 255;
	chaos("max_slots bad kind");
	return 0;
}

static Tuple precedes_map_new()							/*;precedes_map_new*/
{
	return (tup_new(0));
}

Slot slot_new(Symbol sym, int number)							/*;slot_new*/
{
	Slot s;
	char	*sname;

	s = (Slot) emalloct(sizeof(Slot_s), "slot-new");
	s->slot_seq = S_SEQ(sym);
	s->slot_unit = S_UNIT(sym);
	sname = ORIG_NAME(sym);
	/* Make copy */
	s->slot_name = (sname == (char *)0) ? (char *)0 : strjoin(sname, "");
	s->slot_number = number;
	return s;
}

static void init_predef_exceptions()				/*;init_predef_exceptions*/
{
	/* the body of this procedure is obtained by examining the standard
	 * output when compiling predef!  Hopefully a more rational scheme
	 * of initialization will be provided in the future (after validation).
	 *	shields  11-5-85
	 */

	init_predef_exception(26, 1, 6, "SYSTEM_ERROR");
	init_predef_exception(3, 2, 7, "STATUS_ERROR");
	init_predef_exception(4, 2, 8, "MODE_ERROR");
	init_predef_exception(5, 2, 9, "NAME_ERROR");
	init_predef_exception(6, 2, 10, "USE_ERROR");
	init_predef_exception(7, 2, 11, "DEVICE_ERROR");
	init_predef_exception(8, 2, 12, "END_ERROR");
	init_predef_exception(9, 2, 13, "DATA_ERROR");
	init_predef_exception(10, 2, 14, "LAYOUT_ERROR");
	init_predef_exception(58, 9, 15, "TIME_ERROR");
}

static void init_predef_exception(int seq, int unt, int number, char *name)
													/*;init_predef_exception*/
{
	/* seq - sequence of symbol for exception 
	 * number - exception number assigned 
	 * name - exception name 
	 */

	Slot s;
	s = (Slot) emalloct(sizeof(Slot_s), "init-predef-exception-slot");
	s->slot_seq = seq;
	s->slot_unit = unt;
	s->slot_name = (name == (char *)0) ? (char *)0 : strjoin(name, "");
	s->slot_number = number;
	EXCEPTION_SLOTS[number] = (char *) s;
}

void remove_slots(Tuple tup, int unit)						/*;remove_slots*/
{
	int		i, n;
	Slot	s;
	/* go through the tuple (CODE_SLOTS or DATA_SLOTS) and remove slots that are
	 * attached to the obsolete unit.
	 */
	n = tup_size(tup);
	i = 1;
	while (i <= n) {
		s = (Slot) tup[i];
		if (unit == s->slot_unit) {
			tup[i] = tup[n];
			n -= 1;
		}
		else {
			i++;
		}
	}
	tup[0] = (char *)n;
}

void remove_interface(Tuple tup, int unit)				/*;remove_interface*/
{
	int		i, n;
	int         unit_nbr;
	/* go through the tuple interfaced_procedures and remove strings that are
	 * attached to the obsolete unit.
	 */
	n = tup_size(tup);
	i = 1;
	while (i <= n) {
		unit_nbr = (int) tup[i];
		if (unit == unit_nbr) {
			tup[i+1] = tup[n];
			tup[i] = tup[n-1];
			n -= 2;
		}
		else {
			i += 2;
		}
	}
	tup[0] = (char *)n;
}

void private_exchange(Symbol package_name)				/*;private_exchange*/ 
{
	Fordeclared 	fd1;
	Forprivate_decls	fp1;
	Private_declarations  pd;
	Symbol s1, s2, sym;
	char 	*id;

	if (NATURE(package_name) == na_package_spec
	  || NATURE(package_name) == na_package) {
		pd = (Private_declarations) private_decls(package_name);
		FORPRIVATE_DECLS(s1, s2, pd, fp1);
			private_decls_swap(s1, s2);
		ENDFORPRIVATE_DECLS(fp1);

		/* And apply same to inner package specs.*/

		FORDECLARED(id, sym, DECLARED(package_name), fd1);
			if (S_UNIT(sym) == S_UNIT(package_name)
		      && SCOPE_OF(sym) == package_name) {
				private_exchange(sym);
			}
		ENDFORDECLARED(fd1);
	}
}

void private_install(Symbol package_name) 					/*;private_install*/
{
	Fordeclared	fd1;
	Forprivate_decls fp1;
	Private_declarations  pd;
	Symbol s1, s2;
	int exists;
	char 	*id;

	/* Install full declarations for unit in context clause. To see if needed,
	 * scan priv part to see if currently visible entries contain private types.
	 */
	if (NATURE(package_name) == na_package_spec
	  || NATURE(package_name) == na_package) {
		pd = (Private_declarations) private_decls(package_name);
		if (pd == (Private_declarations)0) return; /* Not assigned yet.*/

		exists = FALSE;
		FORPRIVATE_DECLS(s1, s2, pd, fp1);
			if (TYPE_OF(s1) == symbol_private 
		      || TYPE_OF(s1) == symbol_limited_private) {
				exists = TRUE;
				break;
			}
		ENDFORPRIVATE_DECLS(fp1);
		if (exists) private_exchange(package_name);
		/* else { */
		/* Check recursively in inner packages. (The outer one may have no
          * private part.
          */
		FORDECLARED(id, s1, DECLARED(package_name), fd1);
			if (s1 != package_name)
				private_install(s1);
		ENDFORDECLARED(fd1);
		/*} */
	}
}
