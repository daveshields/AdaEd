/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/* load.c - procedures to load to libraries and axq files */

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "config.h"
#include "int.h"
#include "segment.h"
#include "slot.h"
#include "ivars.h"
#include "ifile.h"
#include "miscprots.h"
#include "libfprots.h"
#include "axqrprots.h"
#include "loadprots.h"

static void init_predef();
static void init_library(IFILE *, char *);
static char *unit_name_name(char *);
static int *unit_list_new();
static void unit_list_copy(int *, int *);
static int unit_list_next(int *);
static int in_loaded(char *);

/* Various sets and maps in the SETL version are represented using
 * strings in the C version. This is possible since they all have as
 * their domain unit_numbers, and the total number of unit_numbers is
 * known before these are needed. The initial values of these items
 * are set by 
 *	s = unit_list_new(). 
 * Once defined, s[i] is YES if unit i is in the set, NO otherwise.
 * These sets are kept as a vector of (short) integers, with the
 * first (zeroth) element giving the number of elements, in much the
 * way is tuples are represented in the other parts of the compiler.
 */
#define YES 1
#define NO 0

static char  **file_number;
static int  **PRECEDES_MAP;
static char  **unit_names;
static int     unit_count;
static int   interfaced_unit = 0;
static int   obsolete_error = FALSE;

/* The following struct is used main a list of the units actually loaded. */
struct axq_loaded {
	struct axq_loaded  *loaded_next;
	char   *loaded_name;
};
static struct axq_loaded  *ll_head; /* pointer to head of list */

static void init_predef()										/*;init_predef*/
{
	int     i;
	static char *predef_units[] = {
		"spSYSTEM", "spIO_EXCEPTIONS", "spSEQUENTIAL_IO",
		"boSEQUENTIAL_IO", "spDIRECT_IO", "boDIRECT_IO",
		"spTEXT_IO", "boTEXT_IO", "spCALENDAR", "boCALENDAR",
		"ssUNCHECKED_DEALLOCATION", "suUNCHECKED_DEALLOCATION",
		"ssUNCHECKED_CONVERSION", "suUNCHECKED_CONVERSION"
	};

	/* Set values for unit_names, file_number and PRECEDES information for
	 * predefined compilation units, since they do not appear in any library
	 */
	/* allocate unit names - recalling it is ones origin */
	unit_count = 14;
	unit_names = (char **) emalloct((unit_count + 1) * sizeof(char *),
	  "unit_names");
	PRECEDES_MAP = (int **) emalloct(sizeof(char **) *(unit_count + 1),
	  "precedes_map");
	PRECEDES_MAP[0] =  (int *) unit_count;
	file_number = (char **) emalloct(sizeof(char **) *(unit_count + 1),
	  "file_number");
	for (i = 1; i <= unit_count; i++) {
		unit_names[i] = predef_units[i - 1];
		file_number[i] = "0";
		PRECEDES_MAP[i] = unit_list_new();
	}
}

void load_lib(char *filename, IFILE *libfile, Axq axq, char *main_unit,
  char **argv)													/*;load_lib*/
{
	/* This procedure looks for the main unit
	 * and loads it, together with all units on which it depends directly
	 * or indirectly. Dependences are taken from map precedes.
	 */

	struct axq_loaded  *ll_new;
	int   *main_units, *bound_units, *new_main_units, *to_read, *precedes;
	int	   unitn;
	int     i, name, pi;
	int     is_predef_unit;
	int     nmain_units;
	char   *idle_task_name, *unit_file;
	IFILE * axqfile;
	char    exename[100];
	char   *PREDEFNAME;
	char   *file_name, *l_name, *t_name;

	ll_head = (struct axq_loaded   *) 0; /* Initially, no files loaded */
	init_library(libfile,main_unit);
	main_units = unit_list_new();
	bound_units = unit_list_new();
	for (i = 1; i <= unit_count; i++) {
		if (streq(unit_name_type(unit_names[i]), "ma"))
			main_units[i] = YES;
	}
	if (main_unit != (char *) 0) {
		/* main_units := {[x,y]: [x,y] in main_units 
    	 *		| y = '_'+MAINUNIT+'_idle_task'}; 
    	 */
		idle_task_name = strjoin(main_unit, "_idle_task");
		for (name = 1; name <= unit_count; name++) {
			if (main_units[name] == NO)
				continue;
			if (streq(idle_task_name, unit_names[name]+2))
				bound_units[name] = YES;
		}
		unit_list_copy(main_units, bound_units);
	}
	nmain_units = 0;
	for (i = 1; i <= main_units[0]; i++)
		if (main_units[i]) nmain_units++;
	if (nmain_units == 0) {
		printf("*** Unbound library, execution not allowed\n");
		exit(RC_ERRORS);
	}
	else if (nmain_units > 1) {
		printf("*** More than one main program in library\n");
		printf("    Use option: -m(one of the following)\n");
		for (name = 1; name <= unit_count; name++) {
			if (main_units[name] == NO)
				continue;
			unit_names[name][strlen(unit_names[name])-10] = '\0';
			/* name of the form _xxx_idle_task, print only xxx */
			printf("    %s\n", unit_names[name]+2);
		}
		exit(RC_ERRORS);
	}
	else {
#ifndef INTERFACE
#ifdef SUPPORT_PRAGMA_INTERFACE
		/* at this point, if the main binding unit is interfaced, we run
         * the executable which has been built with the procedure interface
         */
		if (interfaced_unit != 0) {
			sprintf(exename,"%s%s%s.exe",filename,DIR_DELIMITER,
			  file_number[interfaced_unit]);
			execvp(exename,argv);
		}
#endif
#endif
		if (obsolete_error) {
			printf(
			  "*** Main binding unit obsolete, please recompile or rebind \n");
			exit(RC_ERRORS);
		}
		to_read = unit_list_new();
		while(unit_list_next(main_units)) {
			for (name = 1; name <= unit_count; name++) {
				if (main_units[name] == NO)
					continue;
				to_read[name] = YES;
			}
			/* main_units := {} +/{ precedes{u} : u in main_units}; */
			new_main_units = unit_list_new();
			/* for name in main_units */
			for (name = 1; name <= unit_count; name++) {
				if (main_units[name] == NO)
					continue;
				precedes = PRECEDES_MAP[name];
				for (pi = 1; pi <= unit_count; pi++) {
					if (precedes[pi] == NO)
						continue;
					new_main_units[pi] = YES;
				}
			}
			unit_list_copy(main_units, new_main_units);
		}
		while((unitn = unit_list_next(to_read))) {
			to_read[unitn]  = NO;		/* remove from set */
			if (unitn == 0) {
				/* junk unit number - binder shouldn't be putting this out */
				printf("load.c: skipping 0 case\n");
				continue;
			}
			if (unitn <= unit_count	/* false if "ghost package body" */
			&&(!in_loaded(file_number[unitn]))) {
				unit_file = (char *) file_number[unitn];
				file_name = unit_file;
				is_predef_unit =  streq(unit_file,"0");
				if (is_predef_unit) {
					PREDEFNAME = predef_env();
					l_name = libset(PREDEFNAME); /* use predef library */
					file_name = "predef";
				}
				axqfile = ifopen(file_name, "axq", "r", 0);
				read_axq(axqfile, axq);
				ifclose(axqfile);
				if (is_predef_unit)
					t_name = libset(l_name); /* restore user library */
				if (!in_loaded(unit_file))
					ll_new = (struct axq_loaded *)
					  smalloc(sizeof(struct axq_loaded));
				ll_new->loaded_next = ll_head;
				ll_new->loaded_name = unit_file;
				ll_head = ll_new;
			}
		}			/* while */
	}
}

static void init_library(IFILE *ifile, char *main_unit)		/*;init_library*/
{
	/*
	 * retrieve information from ifile
	 */

	int     i, j, n, m, unumber,cur_level;
	int	    ignore;
	int     punit;
	char   *uname, *aisname;
	int    *precedes;
	char   *main_binding_unit = (char *)0;
	int    units_lib;
	int    is_interfaced,comp_status;

	init_predef();
	ll_head = (struct axq_loaded   *) 0;
	if (ifile == (IFILE *) 0) {
		printf("*** library is empty\n");
		exit(RC_ERRORS);
	}
	units_lib = getnum(ifile, "lib-unit-count");
	unit_count = getnum(ifile, "lib-unit_num");
	getnum(ifile, "lib-empty-slots"); /* ignore */
	getstr(ifile, "lib-tmp-str");     /* ignore */
	unit_names = (char **) erealloct((char *)unit_names,
	  (unit_count+1) * sizeof(char **), "unit_names-re");

	file_number = (char **) erealloct((char *)file_number,
	    sizeof(char **) *(unit_count+1),"file_number-re");
#ifndef INTERFACE
	if (main_unit != (char *)0) {
		/* a main unit was specified */
		main_binding_unit = strjoin("ma",main_unit);
		main_binding_unit = strjoin(main_binding_unit,"_idle_task");
	}
#endif
	for (i = 1; i <= units_lib; i++) {
		uname = getstr(ifile, "lib-unit-name");
		unumber = getnum(ifile, "lib-unit-number");
		aisname = getstr(ifile, "lib-ais-name");
		getstr(ifile, "comp-date");   /* ignore */
		getnum(ifile, "lib-symbols"); /* ignore */
		getnum(ifile, "lib-nodes");   /* ignore */
		is_interfaced = getnum(ifile, "lib-is-main");
#ifdef SUPPORT_PRAGMA_INTERFACE
#ifndef INTERFACE
		if (main_binding_unit != (char *) 0) {
			/* check is_main (interfaced flag) only for binding unit 
			 * corresponding to specified main unit
			 */
			if (streq(uname,main_binding_unit) && is_interfaced)
				interfaced_unit = unumber;
		}
		else {
			/* look at is_main (interfaced flag) for any main binding unit.
			 * if there is more that one of these, we will report an error
			 * later !!
			 */
			if (streq(unit_name_type(uname),"ma") && is_interfaced)
				interfaced_unit = unumber;
		}
#endif
#endif
		comp_status = getnum(ifile, "lib-status");
		/* verify that main binding unit status is not obsolete */
		/* ignore this field for all other units */
		if (main_binding_unit != (char *) 0) {
			/* check comp_status only for specified main binding unit */
			if (streq(uname,main_binding_unit) && !comp_status)
				obsolete_error = TRUE;
		}
		else {
			/* if none specified, check for any main binding unit */
			if (streq(unit_name_type(uname),"ma") && !comp_status)
				obsolete_error = TRUE;
		}
		unit_names[unumber] = strjoin(uname, "");
		file_number[unumber] = strjoin(aisname, "");
	}
	/* read but ignore stub info */
	n = getnum(ifile, "lib-n");
	for (i = 1; i <= n; i++) {
		uname = getstr(ifile, "lib-unit-name");
		aisname = getstr(ifile, "lib-ais-name");
		ignore = getnum(ifile, "lib-parent");
		cur_level = getnum(ifile, "lib-cur_level");
		m = getnum(ifile, "stub-file-size");
		for (j = 1; j <= m; j++)
			ignore = getnum(ifile, "stub-file");
	}

	PRECEDES_MAP = (int **) emalloct(sizeof(char **) *(unit_count + 1),
	  "precedes_map");
	for (i = 1; i <= unit_count; i++)
		PRECEDES_MAP[i] = unit_list_new();
	n = getnum(ifile, "precedes-map-size");
	for (i = 1; i <= n; i += 2) {
		unumber = getnum(ifile, "precedes-map-ent");
		m = getnum(ifile, "precedes-map-set-size");
		precedes = unit_list_new();
		for (j = 1; j <= m; j++) {
			punit = getnum(ifile, "precedes-map-ent");
			precedes[punit] = YES;
		}
		if (unumber==0) chaos("unit number zero");
		PRECEDES_MAP[unumber] = precedes;
	}
	return;
}

static char *unit_name_name(char *u)						/*;unit_name_name*/
{
	int     n;
	char   *s1, *s2;

	n = strlen(u);
	if (n <= 2)
		return (char *) 0;

	s1 = u + 2;			/* point to start of name */
	s2 = strchr(s1, '.');	/* look for dot after first name */
	if (s2 == (char *) 0)	/* if no dot take rest of string */
		s2 = u + n;		/* find end */
	n = s2 - s1;
	s2 = smalloc((unsigned) n + 1);
	strncpy(s2, s1, n);
	s2[n] = '\0';		/* terminate result */
	return (s2);
}

long load_slots(char *fname, IFILE **ifile, Axq axq)			/*;load_slots*/
{
	IFILE  *AXQFILE;
	Slot slot;
	int     i;
	long    cde_pos;

	AXQFILE = ifopen(LIBFILENAME, "", "r", 0);
	cde_pos = get_cde_slots(AXQFILE, axq);
	*ifile = AXQFILE;		/* store file pointer */

	code_slots_dim = axq->axq_code_segments_dim;
	data_slots_dim = axq->axq_data_segments_dim;
	exception_slots_dim = axq->axq_exception_slots_dim;
	code_slots = (char **) ecalloct(code_slots_dim, sizeof(char *),
	  "code_slots");
	data_slots = (char **) ecalloct(data_slots_dim, sizeof(char *),
	  "data_slots");
	exception_slots = (char **) ecalloct(exception_slots_dim, sizeof(char *),
	  "exception_slots");
	/* now get names from list and put in proper place */
	for (i = 1; i < axq->axq_code_slots_dim; i++) {
		slot = axq->axq_code_slots[i];
		if (slot == (Slot) 0)
			continue;
		if (slot->slot_number == 0)
			continue;
		code_slots[slot->slot_number] = slot->slot_name;
	}
	for (i = 1; i < axq->axq_data_slots_dim; i++) {
		slot = axq->axq_data_slots[i];
		if (slot == (Slot) 0)
			continue;
		if (slot->slot_number == 0)
			continue;
		data_slots[slot->slot_number] = slot->slot_name;
	}
	for (i = 1; i < axq->axq_exception_slots_dim; i++) {
		slot = axq->axq_exception_slots[i];
		if (slot == (Slot) 0)
			continue;
		if (slot->slot_number == 0)
			continue;
		exception_slots[slot->slot_number] = slot->slot_name;
	}
	code_segments_dim = axq->axq_code_segments_dim;
	code_segments = (char **) ecalloct(axq->axq_code_segments_dim, 
	  sizeof(char *),"code_segments");
	code_seglen = (int *) ecalloct(axq->axq_code_segments_dim, sizeof(int),
	  "code_seglen");
	axq->axq_code_segments = code_segments;
	axq->axq_code_seglen = code_seglen;
	data_segments_dim = axq->axq_data_segments_dim;
	data_segments = (int **) ecalloct(axq->axq_data_segments_dim, 
	  sizeof(char *),"data_segments");
	data_seglen = (int *) ecalloct(axq->axq_data_segments_dim, sizeof(int),
	  "data_seglen");
	axq->axq_data_segments = data_segments;
	axq->axq_data_seglen = data_seglen;

	return cde_pos;
}

static int *unit_list_new() 								/*;unit_list_new*/
{
	int    *u;

	u = (int *) smalloc(sizeof(int) * (unit_count + 1));
	u[0] = unit_count;
	for (i = 1; i <= unit_count; i++)
		u[i] = NO;
	return u;
}

static void unit_list_copy(int *u1, int *u2) 			/*;unit_list_copy*/
{
	int n,i;

	n = u1[0];
	if (n != u2[0])
		chaos("unit_copy sizes differ");
	for (i = 1; i <= n; i++)
		u1[i] = u2[i];
}

static int unit_list_next(int *u1)						/*;unit_list_next*/
{
	int i,n;

	n = u1[0];
	for (i = 1; i <= n; i++)
		if (u1[i]) return i;
	return 0;
}

static int in_loaded(char *str)								/*;in_loaded*/
{
	/* test to see if named file has been loaded */
	struct axq_loaded  *p;

	for (p = ll_head; p != (struct axq_loaded  *) 0; p = p->loaded_next)
		if (streq(str, p->loaded_name))
			return TRUE;

	return FALSE;
}
