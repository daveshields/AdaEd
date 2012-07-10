/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/* liblist.c: translation of code generator read.stl*/

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "config.h"
#include "segment.h"
#include "slot.h"
#include "ifile.h"
#include "miscprots.h"
#include "libfprots.h"

static void load_library();
static void get_local_ref_maps(IFILE *, int);
static long get_cde_slots(IFILE *, Axq);
static void get_slot(IFILE *, char *);
static char *convert_date(char *);
static char *unit_name_name(char *);
static int is_subunit(char *);
static char *formatted_name(char *);
static char *formatted_stub(char *);

IFILE *LIBFILE;
#ifdef IBM_PC
/* on the PC, a chdir must be undone before program completes.
 * changed_dir is set when directory changed.
 */
#endif

void main(int argc, char **argv)
{
        int  c;
        int  lib_opt = FALSE;
        int  errflg = 0;

        extern int  optind;
        extern char *optarg;
	char *libname,*fname;
	char *t_name;

#ifdef IBM_PC
	fprintf(stderr, "NYU Ada/Ed Librarian Version 1.11.2\n");
	fprintf(stderr, "Copyright (C) 1985-1992 by New York University.\n");
#endif

#ifndef IBM_PC
        while((c = getopt(argc,argv,"l:"))!=EOF) {
#else
        while((c = getopt(argc,argv,"L:l:"))!=EOF) {
                if (isupper(c)) c = tolower(c);
#endif
                switch(c) {
                case 'l': /* specify library name */
                        lib_opt = TRUE;
                        libname = strjoin(optarg,"");
                        break;
                case '?':
                        errflg++;
                }        
        }

	fname = (char *)0;
	if (optind < argc) fname = argv[optind];
        if (!lib_opt && fname == (char *)0) {
		fname = getenv("ADALIB");
		if (fname!= (char *)0) {
#ifdef IBM_PC
			fprintf(stderr, "L");
#else
			fprintf(stderr, "l");
#endif
			fprintf(stderr,"ibrary defined by ADALIB: %s\n", fname);
		}
	}
	if ((!lib_opt && fname == (char *)0) || errflg) {
	    fprintf(stderr, "Usage: adalib [-l library]\n");
	    exit(1);
	}
        if (!lib_opt) {
           libname = emalloc(strlen(fname) + 1);
           strcpy(libname, fname);
        }

	t_name = libset(libname);
	LIBFILE = ifopen(LIBFILENAME, "", "r", 0);

	load_library();
	exit(0);
}

static void load_library()								/*;load_library*/
{
	/*
	 * retrieve information from LIBFILE
	 * Called only if lib_option and not newlib.
	 */

	int		i, j, n, m, unumber, nodes, symbols;
	int		comp_status, unit_count, cur_level;
	char	*comp_date, *status_str, *uname, *aisname, *tmp_str;
	char	*main_string;
	int		is_main, empty_unit_slots, parent;
	int		ignore;


	unit_count = getnum(LIBFILE, "lib-unit-count");
	n = getnum(LIBFILE, "lib-n");
	empty_unit_slots = getnum(LIBFILE, "lib-empty-slots");
	tmp_str = getstr(LIBFILE, "lib-tmp-str");
	for (i = 1; i <= unit_count; i++) {
		uname = getstr(LIBFILE, "lib-unit-name");
		unumber = getnum(LIBFILE, "lib-unit-number");
		aisname = getstr(LIBFILE, "lib-ais-name");
		comp_date = getstr(LIBFILE, "unit-date");
		symbols = getnum(LIBFILE, "lib-symbols");
		nodes = getnum(LIBFILE, "lib-nodes");
		is_main = getnum(LIBFILE, "lib-is-main");
		if (is_main) {
			if (streq(unit_name_type(uname), "ma"))
				main_string = "(Interface)";
			else
				main_string = "  (Main)   ";
		}
		else {
			main_string = "";
		}
		comp_status = getnum(LIBFILE, "lib-status");
		status_str = (comp_status) ? "active  " : "obsolete";
		printf("%8s %11s %-15s %s\n",
		    status_str, main_string, convert_date(comp_date),
		    formatted_name(uname));
	}
	printf("\n");
	n = getnum(LIBFILE, "lib-n");
	if (n) {
		printf("stubs \n\n");
		for (i = 1; i <= n; i++) {
			uname = getstr(LIBFILE, "lib-unit-name");
			aisname = getstr(LIBFILE, "lib-ais-name");
			parent = getnum(LIBFILE, "lib-parent");
			cur_level = getnum(LIBFILE, "lib-cur-level");
			m = getnum(LIBFILE, "stub-file-size");
			for (j = 1; j <= m; j++)
				ignore = getnum(LIBFILE, "stub-file");
			printf("%s\n", formatted_stub(uname));
		}
		printf("\n");
	}
	ifclose(LIBFILE);
	return;
#ifdef TBSL
	n = getnum(LIBFILE, "precedes-map-size");
	printf("precedes map\n");
	for (i = 1; i <= n; i += 2) {
		dom = getnum(LIBFILE, "precedes-map-dom");
		m = getnum(LIBFILE, "precedes-map-nelt");
		printf("  %4d:", dom);
		for (j = 1; j <= m; j++) {
			range = getnum(LIBFILE, "precedes-map-ent");
			printf(" %4d", range);
		}
		printf("\n");
	}
	n = getnum(LIBFILE, "compilation_table_size");
	if (n) {
		printf("\ncompilation table\n");
		for (i = 1; i <= n; i++) {
			unum = (int) getnum(LIBFILE, "compilation-table-ent");
			printf("  %d\n", unum);
		}
		printf("\n");
	}
	/* late_instances */
	n = getnum(LIBFILE, "late-instances-size");
	if (n) {
		printf("late instances\n");
		for (i = 1; i <= n; i++) {
			str = (char *) getstr(LIBFILE, "late-instances-str");
			printf("  %s\n", str);
		}
	}
	/* current code segment */
	n = getnum(LIBFILE, "unit-size");
	printf("\ncurrent code segments\n");
	printf("  unit cs\n");
	for (i = 1; i <= n; i++) {
		cs = getnum(LIBFILE, "current-code-segment");
		if (cs) printf("   %d: %d\n", i, cs);
	}
	/* local reference maps */
	n = getnum(LIBFILE, "unit-size");
	get_local_ref_maps(LIBFILE, n);
	cde_pos = get_cde_slots(LIBFILE, axq);


	/* could free axq_data_slots, etc., but keep for now */
	/* read out LIB_STUB map (always empty for now) */
	ifclose(LIBFILE);
	return;
#endif
}

static void get_local_ref_maps(IFILE *ifile, int units)	/*;get_local_ref_map*/
{
	int		unit, defined, i, off, n;
	int		sym_seq, sym_unit;

	printf("\nlocal reference maps\n");
	for (unit = 1; unit <= units; unit++) {
		/* ignore empty ref maps (predef units) and obselete units */
		defined = getnum(ifile, "local-ref-map-defined");
		if (!defined) continue;
		printf("%d: ", unit);
		n = getnum(ifile, "local-ref-map-size");
		n = n/2;
		for (i = 1; i <= n; i++) {
			sym_seq = getnum(ifile, "local-ref-map-sym-seq");
			sym_unit = getnum(ifile, "local-ref-map-sym-unit");
			off = getnum(ifile, "local-ref-map-off");
			/* if all three values are zero ignore this entry. It is a fake
			 * entry created by put_local_ref_map. see comment there.
			 */
			if (sym_seq == 0 && sym_unit == 0 && off == 0) continue;
			printf("%d %d %d ", sym_seq, sym_unit, off);
		}
		printf("\n");
	}
	printf("\n");
}

static long get_cde_slots(IFILE *file, Axq axq)				/*;get_cde_slots*/
{
	long	dpos;
	int		n_code, n_data, n_exception;


	dpos = file->fh_slots;
	/* position to start of slot info */
	ifseek(file, "get-cde-slots-start", dpos, 0);
	n_code = getnum(file, "n-code");
	n_data = getnum(file, "n-data");
	n_exception = getnum(file, "n-exception");
	get_slot(file, "code");
	get_slot(file, "data");
	get_slot(file, "exceptions");
	return dpos; /* return offset of start of slot info */
}

static void get_slot(IFILE *file, char *name)					/*;get_slot*/
{
	/* This procedure reads in the SLOTS information. 
	 * Entries are Slots structures. nmax is guess at needed dimension,
	 * dim is set to dimension actually found.
	 */

	int i, n, exists;
	int	slot_seq, slot_unit, slot_number;
	char *slot_name;

	n = getnum(file, "slot-entries");
	printf("%s slots \n", name);
	printf("  num seq unit  name\n");

	for (i = 1; i <= n; i++) {
		exists = getnum(LIBFILE, "slot-exists");
		if (exists) {
			slot_seq = getnum(LIBFILE, "slot-seq");
			slot_unit = getnum(LIBFILE, "slot-unit");
			slot_number = getnum(LIBFILE, "slot-number");
			slot_name = getstr(LIBFILE, "slot_name");
			printf("  %3d %3d %4d  %s\n",
			    slot_number, slot_seq, slot_unit, slot_name);
		}
	}
	printf("\n");
}

static char *convert_date(char *comp_date)					/*;convert_date*/
{
	static char new_date[15];
	int	i;

	if (comp_date == (char *)0)
		return(" ");
	comp_date++;
	comp_date++;
	for (i = 6; i < 8; i++)
		new_date[i] = *comp_date++;
	comp_date++;
	for (i = 0; i < 2; i++)
		new_date[i] = *comp_date++;
	new_date[2] = '/';
	comp_date++;
	for (i = 3; i < 5; i++)
		new_date[i] = *comp_date++;
	new_date[5] = '/';
	new_date[8] = ' ';
	comp_date++;
	for (i = 9; i < 14; i++)
		new_date[i] = *comp_date++;
	new_date[11] = ':';

	new_date[14] = '\0';
	return new_date;
}

static char *unit_name_name(char *u)						/*;unit_name_name*/
{
	int	n;
	char	*s1, *s2;

	n = strlen(u);
	if (n <= 2)
		return (char *)0;

	s1 = u+2; 				/* point to start of name*/
	s2 = strchr(s1, '.'); 	/* look for dot after first name */
	if (s2 == (char *)0) 	/* if no dot take rest of string */
		s2 = u + n; 		/* find end */
	n = s2 - s1;
	s2 = emalloc((unsigned) n+1);
	strncpy(s2, s1, n);
	s2[n] = '\0'; /* terminate result */
	return (s2);
}

static int is_subunit(char *u)									/*;is_subunit*/
{
	/* In C, IS_SUBUNIT is procedure is_subunit():
	 *	IS_SUBUNIT(na);           (#na > 2)                          endm;
	 */

	int	n;
	char	*s1, *s2;

	if (u == (char *)0)
		chaos("is_subunit: null pointer");
	n = strlen(u);
	if (n <= 2)
		return FALSE;
	s1 = u + 2; /* point to start of name*/
	s2 = strchr(s1, '.'); /* look for dot after first name */
	if (s2 == (char *)0) /* if no dot take rest of string */
		return FALSE;
	return TRUE; /* if subunit*/
}

static char *formatted_name(char *unit)					/*;formatted_name*/
{
	char *kind, *unit_kind;

	kind = unit_name_type(unit);
	if (is_subunit(unit))	    unit_kind = "proper body ";
	else if (streq(kind, "sp"))  unit_kind = "package spec ";
	else if (streq(kind, "bo"))  unit_kind = "package body ";
	else if (streq(kind, "ss"))  unit_kind = "subprogram spec ";
	else if (streq(kind, "su"))  unit_kind = "subprogram ";
	else if (streq(kind, "ma"))  unit_kind = "binding unit ";
	else unit_kind = "unit ";
	return strjoin(unit_kind, unit_name_name(unit));
}

static char *formatted_stub(char *unit)						/*;formatted_stub*/
{
	char *kind, *unit_kind;

	kind = unit_name_type(unit);
	if (streq(kind, "bo"))  unit_kind = "package (task) stub ";
	else if (streq(kind, "su"))  unit_kind = "subprogram stub ";
	else unit_kind = "stub ";
	return strjoin(unit_kind, unit_name_name(unit));
}
