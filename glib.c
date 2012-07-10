/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* glib.c: translation of lib.stl for code generator */
#define GEN

#include "hdr.h"
#include "libhdr.h"
#include "vars.h"
#include "segment.h"
#include "gvars.h"
#include "ops.h"
#include "type.h"
#include "ifile.h"
#include "segmentprots.h"
#include "gutilprots.h"
#include "setprots.h"
#include "axqrprots.h"
#include "libprots.h"
#include "libfprots.h"
#include "miscprots.h"
#include "glibprots.h"

static Set remove_dependent(int);

extern int ADA_MIN_INTEGER, ADA_MAX_INTEGER;
extern long ADA_MIN_FIXED, ADA_MAX_FIXED;
extern Tuple segment_map_new(), segment_map_put();
extern Segment segment_new();
extern Segment	CODE_SEGMENT, DATA_SEGMENT, DATA_SEGMENT_MAIN;


/*
 * Librarian and binder
 *
 * bind renamed binder to avoid conflict with c library routine of same name 
 */


Segment main_data_segment() 						/*;main_data_segment*/
{
	/* Initialize the main data segment needed for all programs. This consists
	 * mainly of the type templates for the standard types. As the templates
	 * are defined, the segment offset of the associated symbols is set
	 * correctly. In the SETL version index 81 is the first free position
	 * after templates are allocated and is used as the value of the macro
	 * relay_tables in the interpreter. We improve on this by setting the first
	 * word in the segment to contain the offset of the start of the relay
	 * sets.
	 */

	/* Template pointers */

	struct tt_i_range  *tt_for_integer;
	struct tt_e_range  *boolean_tt;
	struct tt_i_range  *positive_tt;
	struct tt_array *string_tt;
	struct tt_i_range  *null_index_tt;
	struct tt_s_array  *null_string_tt;
	struct tt_e_range  *character_tt;
	struct tt_task *main_task_type_tt;
	struct tt_i_range  *natural_tt;
	struct tt_fx_range *duration_tt;
	struct tt_fx_range *integer_fixed_tt;
	struct tt_fl_range *float_tt;

	int    *ds, di, i, off_for_main_task_body;
	Segment seg;

	/* SETL text used to define initial data segment:
	 * DATA_SEGMENT =
	 *	[tt_access, 2]			      1 : $ACCESS
	 *    + [tt_i_range, 1, -(2**30)+1, 2**30-1]     3 : integer
	 *    + [tt_enum, 1, 0, 1,			      7 : boolean
	 *	    5, 70, 65, 76, 83, 69,
	 *	    4, 84, 82, 85, 69]
	 *    + [tt_i_range, 1, 1, 2**30-1]	      22 : positive
	 *    + [tt_u_array, 2**30-1, 1, 1, 23, 1, 22]      26 : string
	 *    + [tt_i_range, 1, 1, 0]		      33 : null index
	 *    + [tt_s_array, 0, 1, 2, 1, 0]		      37 : null string
	 *    + [tt_enum, 1, 0, 127]		      43 : character
	 *    + [tt_task, 1, 6, 1, 54, 0, 0]		      47 : main_task_type
	 *    + [main_cs, 0, 0]			      54 : main_task_body
	 *    + [tt_i_range, 1, 0, 2**30-1]	      57 : natural
	 *    + [tt_fixed, 1, -3, -3, -(2**30)+1,
	 *			    2**30-1]	      61 : duration
	 *    + [tt_fixed, 1, 0, 0, -(2**30)+1, 2**30-1]   67 : integer_fixed
	 *    + [tt_f_range, 1, F_TO_I(ada_min_real),
	 *		    F_TO_I(ada_max_real)]     73 : FLOAT
	 *    + [tt_i_range, 1, -(2**15)+1, 2**15-1]     77 : SHORT_INTEGER
	 *					      81 : relay sets
	 *	[tt_access, 2]			     : $ACCESS
	 */

	ds = (int *) ecalloct(150, sizeof(int), "main-data-segment");
	/* di[0] used to store offset of relay tables(see below) */
	di = 1;			/* initial offset */

	S_OFFSET(symbol_daccess) = di;

	/* first two words are not template */
	ds[di++] = TT_ACCESS;
	ds[di++] = 2;

	/* tt_i_range, 1, -(2**30)+1, 2**30-1]    : integer */

	S_OFFSET(symbol_integer) = di;
	S_OFFSET(symbol_universal_integer) = di;

	tt_for_integer = I_RANGE((ds + di));
	tt_for_integer->ttype = TT_I_RANGE;
	tt_for_integer->object_size = 1;
	tt_for_integer->ilow = ADA_MIN_INTEGER;/* check this and next line */
	tt_for_integer->ihigh = ADA_MAX_INTEGER;
	S_OFFSET(symbol_integer) = di;
	di += WORDS_I_RANGE;

	/* [tt_enum, 1, 0, 1,		    : boolean * 5, 70, 65, 76, 83, 69, *
    4, 84, 82, 85, 69] */

	S_OFFSET(symbol_boolean) = di;

	boolean_tt = E_RANGE((ds + di));
	boolean_tt->ttype = TT_ENUM;
	boolean_tt->object_size = 1;
	boolean_tt->elow = 0;
	boolean_tt->ehigh = 1;
	di += WORDS_E_RANGE;
	/* put enumeration values */
	ds[di++] = 5;		/* length of FALSE */
	ds[di++] = 'F';
	ds[di++] = 'A';
	ds[di++] = 'L';
	ds[di++] = 'S';
	ds[di++] = 'E';
	ds[di++] = 4;		/* length of TRUE */
	ds[di++] = 'T';
	ds[di++] = 'R';
	ds[di++] = 'U';
	ds[di++] = 'E';

	/* [tt_i_range, 1, 1, 2**30-1]	      : positive */

	S_OFFSET(symbol_positive) = di;

	positive_tt = I_RANGE((ds + di));
	positive_tt->ttype = TT_I_RANGE;
	positive_tt->object_size = 1;
	positive_tt->ilow = 1;
	positive_tt->ihigh = ADA_MAX_INTEGER;/* check this */
	di += WORDS_I_RANGE;

	/* [tt_u_array, 2**30-1, 1, 1, 23, 1, 22]     : string */

	S_OFFSET(symbol_string_type) = di;
	S_OFFSET(symbol_string) = di;

	string_tt = ARRAY((di + ds));
	string_tt->ttype = TT_U_ARRAY;
	string_tt->object_size = ADA_MAX_INTEGER;
	string_tt->dim = 1;
	string_tt->component_base = 1;
	/* string_tt->component_offset is set below when character defined */
	string_tt->index1_base = 1;
	string_tt->index1_offset = S_OFFSET(symbol_positive);
	di += WORDS_ARRAY;

	/* [tt_i_range, 1, 1, 0]		      : null index */

	null_index_tt = I_RANGE((ds + di));
	null_index_tt->ttype = TT_I_RANGE;
	null_index_tt->object_size = 1;
	null_index_tt->ilow = 1;
	null_index_tt->ihigh = 0;
	di += WORDS_I_RANGE;

	/* [tt_s_array, 0, 1, 2, 1, 0]		      : null string */

	null_string_tt = S_ARRAY((di + ds));
	null_string_tt->ttype = TT_S_ARRAY;
	null_string_tt->object_size = 0;
	;
	null_string_tt->component_size = 1;
	null_string_tt->index_size = 2;
	null_string_tt->salow = 1;
	null_string_tt->sahigh = 0;
	di += WORDS_S_ARRAY;

	/* [tt_enum, 1, 0, 127]		      : character */

	S_OFFSET(symbol_character) = di;
	S_OFFSET(symbol_character_type) = di;

	/* Can set component_offset for string now */
	string_tt->component_offset = di;

	character_tt = E_RANGE((di + ds));
	character_tt->ttype = TT_ENUM;
	character_tt->object_size = 1;
	;
	character_tt->elow = 0;
	character_tt->ehigh = 127;
	di += WORDS_E_RANGE;
	ds[di++] = -1;              /* no list of images */

	/* [tt_task, 1, 6, 1, 54, 0, 0]		      : main_task_type */

	S_OFFSET(symbol_main_task_type) = di;

	main_task_type_tt = TASK((di + ds));
	main_task_type_tt->ttype = TT_TASK;
	main_task_type_tt->object_size = 1;
	main_task_type_tt->priority = MAX_PRIO-1; /* TBSL: priority of main */
	main_task_type_tt->body_base = 1;/* segment number */
	/* body_off filled in later */
	main_task_type_tt->collection_size = 1000;
	main_task_type_tt->collection_avail = 1000;
	main_task_type_tt->nb_entries = 0;
	main_task_type_tt->nb_families = 0;
	di += WORDS_TASK;

	/* [main_cs, 0, 0]			      : main_task_body */

	off_for_main_task_body = di;
	ds[di++] = MAIN_CS;
	ds[di++] = 0;
	ds[di++] = 0;
	main_task_type_tt->body_off = off_for_main_task_body;

	/* [tt_i_range, 1, 0, 2**30-1]	      : natural */

	S_OFFSET(symbol_natural) = di;

	natural_tt = I_RANGE((ds + di));
	natural_tt->ttype = TT_I_RANGE;
	natural_tt->object_size = 1;
	;
	natural_tt->ilow = 0;
	natural_tt->ihigh = ADA_MAX_INTEGER;/* check this */
	di += WORDS_I_RANGE;

	/* [tt_fixed, 1, -3, -3, -(2**30)+1, 2**30-1]	     : duration */

	S_OFFSET(symbol_duration) = di;

	duration_tt = FX_RANGE((ds + di));
	duration_tt->ttype = TT_FX_RANGE;
	duration_tt->object_size = 1;
	duration_tt->small_exp_2 = -3;
	duration_tt->small_exp_5 = -3;
	duration_tt->fxlow = 0 ;
	duration_tt->fxhigh = 86400000L;
	di += WORDS_FX_RANGE;

	/* [tt_fixed, 1, 0, 0, -(2**30)+1, 2**30-1]   : integer_fixed */

	S_OFFSET(symbol_dfixed) = di;

	integer_fixed_tt = FX_RANGE((ds + di));
	integer_fixed_tt->ttype = TT_FX_RANGE ;
	integer_fixed_tt->object_size = 1 ;
	integer_fixed_tt->small_exp_2 = 0;
	integer_fixed_tt->small_exp_5 = 0;
	integer_fixed_tt->fxlow = -ADA_MAX_FIXED;
	integer_fixed_tt->fxhigh = ADA_MAX_FIXED;
	di += WORDS_FX_RANGE;

	/* [tt_f_range, 1, F_TO_I(ada_min_real), F_TO_I(ada_max_real)]   : FLOAT */

	S_OFFSET(symbol_float) = di;
	S_OFFSET(symbol_universal_real) = di;

	float_tt = FL_RANGE((ds + di));
	float_tt->ttype = TT_FL_RANGE;
	float_tt->object_size = sizeof(long)/sizeof(int) ;
	float_tt->fllow = ADA_MIN_REAL;
	float_tt->flhigh = ADA_MAX_REAL;
	di += WORDS_FL_RANGE;

#ifdef TBSL
	-- short integer not supported yet
	    + [tt_i_range, 1, -(2**15)+1, 2**15-1]    /* 77 : SHORT_INTEGER */
	S_OFFSET(symbol_short_integer) = di;
#endif
	/* The interpreter needs to know where the relay sets. We store this
	 * offset in the first word of the data segment
	 */
	ds[0] = di;			/* 81? : relay sets */

	seg = segment_new(SEGMENT_KIND_DATA, di);
	for (i = 0; i < di; i++) {
		segment_put_int(seg, ds[i]);
	}
	/* ds dead now that contents copied into segment */
	efreet((char *) ds, "main-data-segment");
	return seg;
}

Set precedes_map_get(char *name)						/*;precedes_map_get*/
{
	int		unum, i, n;
	unum = unit_numbered(name);
	n = tup_size(PRECEDES_MAP);
	for (i=1; i<=n; i+=2) {
		if (PRECEDES_MAP[i] == (char *)unum)
			return (Set) PRECEDES_MAP[i+1];
	}
	return set_new(0);
}

void precedes_map_put(char *name, Set nset)				/*;precedes_map_put*/
{
	int		unum, i, n;
	unum = unit_numbered(name);
	n = tup_size(PRECEDES_MAP);
	for (i=1; i<=n; i+=2) {
		if (PRECEDES_MAP[i] == (char *) unum) {
			PRECEDES_MAP[i+1] = (char *) nset;
			return;
		}
	}
	PRECEDES_MAP = tup_exp(PRECEDES_MAP, n+2);
	PRECEDES_MAP[n+1] = (char *) unum;
	PRECEDES_MAP[n+2] = (char *) nset;
}

Tuple stubs(char *lib_name)										/*;stubs*/
{
	char	*name;
	Fortup	ft1;
	Tuple	stublist;
	int		parent;
	stublist = tup_new(0);
	if (!streq(unit_name_type(lib_name), "sp")) {
		/* stublist = {n : n in domain STUB_ENV | n(3..) = lib_name(2..)}; */
		parent = unit_numbered(lib_name);
		FORTUP(name=(char *), lib_stub, ft1);
			if (stub_parent_get(name) == parent)
				stublist = tup_with(stublist, name);
		ENDFORTUP(ft1);
	}
	return stublist;
}

Set remove_same_name(char *name)				/*;remove_same_name */
{
	/*
	 * remove references in library maps to previously compiled units with
	 * the same name, except for specs if name is the corresponding body.
	 * returns the set of deleted names.
	 */

	Set		same_name, dependent, obsolete;
	char	*to_keep, *unam;
	int		i, unum;
	Forset	fs1;
	Fortup	ft1;

	same_name = set_new(0);
	if (streq(unit_name_type(name), "bo"))
		to_keep = "sp";
	else if (streq(unit_name_type(name), "su"))
		to_keep = "ss";
	else
		to_keep = "";

	/* loop forall u_data = LIB_UNIT(unam) | unam(2..) = name(2..) and
     *			unam(1)  != to_keep
     * do
     *  same_name with:= unam;
     * end loop;
     */

	for (i = 1; i <= unit_numbers; i++) {
		unam = pUnits[i]->libUnit;
		if (streq(unit_name_names(unam), unit_name_names(name))
		  && !streq(unit_name_type(unam), to_keep)) {
			same_name = set_with(same_name, (char *) unit_numbered(unam));
		}
	}

	same_name = set_with(same_name, (char *) unit_numbered(name));
	dependent = set_new(0);

	/* Remove all units which depend on either units with the same identifier
	 * as "name" or that depend on "name" itself.
	 */
	FORSET(unum=(int), same_name, fs1);
		dependent = set_union(dependent, remove_dependent(unum));
	ENDFORSET(fs1);

	/* remove "name" from the set of units that have the same id */
	same_name = set_less(same_name, (char *) unit_numbered(name));

	obsolete = set_union(same_name, dependent);

	FORTUP(unam=(char *), lib_stub, ft1);
		if (set_mem((char *) stub_parent_get(unam), obsolete))
			lib_stub_put(unam, (char *)0);
	ENDFORTUP(ft1);

	return obsolete;
}

static Set remove_dependent(int unit_num)				/*;remove_dependent */
{
	/*
	 * remove references in library maps to units depending directly or
	 * indirectly on the give unit.
	 * returns the set of deleted names.
	 */

	char	*mname, *name, *unam;
	int		i, unum, nameFound;
	Set		dependent, new_dep, precedes;
	Forset	fs1;

	name = pUnits[unit_num]->name;
	nameFound = FALSE;
	mname = strjoin("ss", unit_name_names(name));
	for (i = 1; i <= unit_numbers; i++) {
		if (streq(mname, pUnits[i]->libUnit)) {
			nameFound = TRUE;
			break; }
	}
	dependent = set_new(0);
	if (streq(unit_name_type(name), "bo") || (streq(unit_name_type(name), "su")
	  && nameFound)) {
		/* Package body and subprog body with separate spec. Only subunits
         * may depend on such things, plus units naming them in pragma 
         * elaborate. Only subunits must be deleted. 
		 */

		/* dependent= {unam: unam in domain LIB_UNIT
		 *		| IS_SUBUNIT(unam) and name in precedes{unam}  };
		 */
		for (i = 1; i <= unit_numbers; i++) {
			unam = pUnits[i]->libUnit;
			if (is_subunit(unam)) {
				precedes = precedes_map_get(unam);
				if (set_mem((char *) unit_numbered(name), precedes))
					dependent = set_with(dependent,(char *)unit_numbered(unam));
			}
		}
	}
	else {
		/* dependent= {unam: unam in domain LIB_UNIT
		 * 		| name in precedes{unam}};
		 */
		for (i = 1; i <= unit_numbers; i++) {
			unam = pUnits[i]->libUnit;
			precedes = precedes_map_get(unam);
			if (set_mem((char *) unit_numbered(name), precedes))
				dependent = set_with(dependent, (char *) unit_numbered(unam));
		}
	}
	new_dep = set_new(0);

	FORSET(unum=(int), dependent, fs1);
		new_dep = set_union(new_dep, remove_dependent(unum));
	ENDFORSET(fs1);

	return set_union(dependent, new_dep);
}

int lib_package_with_tasks(Symbol unit_unam)	    /*;lib_package_with_tasks */
{
	Tuple   tup;
	tup = (Tuple) MISC(unit_unam);
	return ((int)tup[1]);
}

#ifdef DEBUG
Tuple read_predef_axq(Tuple axq_needed)					/*;read_predef_axq*/
{
	IFILE *axq_file;
	Segment	newseg, fakseg;
	int		snum, nsegs;
	char	*funame;
	long	genpos, rec;
	int     name_num, n, skip_it;
	Tuple       predef_data_segments;
	Tuple       predef_code_segments;
	Tuple       data_n_code;
	Fortup	ft1;


	fakseg = segment_new(SEGMENT_KIND_CODE, 0);
	segment_put_byte(fakseg, I_LEAVE_BLOCK);
	segment_put_byte(fakseg, I_RAISE);
	segment_put_byte(fakseg, I_ENTER_BLOCK);
	segment_put_byte(fakseg, I_LEAVE_BLOCK);
	segment_put_int (fakseg, 0); /* size of local objects */

	predef_data_segments = tup_new(0);
	predef_code_segments = tup_new(0);

	axq_file = ifopen(PREDEFNAME, ".axq", "r", 0);
	for (rec=read_init(axq_file); rec != 0; rec=read_next(axq_file, rec)) {
		funame = getstr(axq_file, "axq-unit-name");
		name_num = getnum(axq_file, "axq-unit-number");
		skip_it = TRUE;
		FORTUP(n=(int), axq_needed, ft1)
		    if (n == name_num) {
				skip_it = FALSE;
				break;
			}
		ENDFORTUP(ft1)
		if (skip_it) continue;
		genpos = getlong(axq_file, "axq-gen-pos");
		/* position to start of slots info */
		ifseek(axq_file, "gen-pos", genpos, 0);
		/* data segments */
		nsegs = getnum(axq_file, "number-segments");
		if(nsegs != 1) chaos("read_predef_axq data segment number invalid");
		snum = getnum(axq_file, "axq-segment-num");
		predef_data_segments = tup_with(predef_data_segments, (char *) snum);
		newseg = segment_read(axq_file);
		DATA_SEGMENT_MAP = segment_map_put(DATA_SEGMENT_MAP, snum, newseg);
		/* fake code segment */
		snum = *((int *)newseg->seg_data);
		predef_code_segments = tup_with(predef_code_segments, (char *) snum);
		CODE_SEGMENT_MAP = segment_map_put(CODE_SEGMENT_MAP, snum, fakseg);
	}
	ifclose(axq_file);
	data_n_code = tup_new(2);
	data_n_code[1] = (char *)predef_data_segments;
	data_n_code[2] = (char *)predef_code_segments;
	return data_n_code;
}
#endif
