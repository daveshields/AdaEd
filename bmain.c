/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#define GEN

#include <stdio.h>
#include <ctype.h>
#include "hdr.h"
#include "vars.h"
#include "gvars.h"
#include "libhdr.h"
#include "segment.h"
#include "ifile.h"
#include "slot.h"
#include "arithprots.h"
#include "dclmapprots.h"
#include "readprots.h"
#include "dbxprots.h"
#include "initprots.h"
#include "blibprots.h"
#include "libprots.h"
#include "glibprots.h"
#include "libfprots.h"
#include "librprots.h"
#include "libwprots.h"
#include "g0aprots.h"
#include "setprots.h"
#include "miscprots.h"
#include "gmiscprots.h"
#include "bmainprots.h"

static void fold_upper(char *);
static void bpreface();
static void exitf(int);

/* Driver routine for ada gen */
char *argname;

IFILE	*AISFILE, *AXQFILE, *STUBFILE, *LIBFILE, *TREFILE;
int list_unit_0 = 0; /* set by '0' option to list unit 0 structure */
int peep_option = 1; /* on for peep_hole optimization */
int adacomp_option = 0; /* set if called from adacomp */

extern Segment	CODE_SEGMENT, DATA_SEGMENT, DATA_SEGMENT_MAIN;
extern Segment   VARIANT_TABLE, FIELD_TABLE ;
char *lib_name;
#ifdef DEBUG
extern int zpadr_opt; /* not for EXPORT */
#endif

void main(int argc, char **argv)
{
	int		c, i, n;
	int		errflg = 0, nobuffer = 0, mflag = 0;
        int    lib_opt = FALSE;
	extern int  optind;
	extern char *optarg;
	char	*t_name;
	char	*fname, *tfname, *source_name;

	AISFILE = (IFILE *)0;
	AXQFILE = (IFILE *)0;
	LIBFILE = (IFILE *)0;
	STUBFILE = (IFILE *)0;
	TREFILE = (IFILE *)0;

	MAINunit = "";
	interface_files = "";

#ifdef IBM_PC
	while ((c = getopt (argc, argv, "C:c:G:g:M:m:i:l:L:")) != EOF) {
#else
	while ((c = getopt (argc, argv, "c:g:m:i:l:")) != EOF) {
#endif
		/*
		 *    user:
		 *	c	set if called from adacomp (errors in msg format).
		 *	g	debugging, followed by list of options:
		 *		0	show structure of unit 0
		 *		b	do not buffer standard output
		 *		e	flag signalling errors in the parsing phase
		 *		g	list generated code
		 *		l	show line numbers in generated code
		 *		z	call trapini to initialize traps
		 *      i   to specify object files and libraries for pragma interface
		 *  	l	using library
		 *	m	main unit name
		 */
#ifdef IBM_PC
		if (isupper(c)) c = tolower(c);
#endif
		switch (c) {
		case 'c': 
			adacomp_option++;
			source_name = malloc(strlen(optarg)+1);
			strcpy(source_name, optarg);
			break;
		case 'i':
			interface_files = strjoin(interface_files, optarg);
			interface_files = strjoin(interface_files, " ");
			break;
		case 'l': /* using existing library */
                        lib_opt = TRUE;
                        lib_name = emalloc(strlen(optarg) + 1);
			strcpy(lib_name, optarg);
			break;
		case 'm': /* specify main unit name */
			MAINunit = malloc(strlen(optarg)+1);
			strcpy(MAINunit, optarg);
			fold_upper(MAINunit);
			break;
		case 'g': /* gen debug options */
			n = strlen(optarg);
			for (i = 0; i < n; i++) {
#ifdef IBM_PC
		                fold_lower(optarg);
#endif
				switch((int)optarg[i]) {
#ifdef DEBUG
				case 'a':
					zpadr_opt = 0; /* do not print addresses in zpadr */
					break;
#endif
				case 'g':
					list_code++;
					break;
				case 'l':
					line_option++;
					break;
#ifdef DEBUG
				case 'b': /* do not buffer output */
					nobuffer++;
					break;
				case 'd': /* force debugging output */
					debug_flag++;
					break;
				case 'e':
					errors = TRUE;
					break;
				case 'o': /* disable optimization (peep) */
					peep_option = 0;
					break;
				case '0': /* read trace including unit 0 */
					list_unit_0++;
					break;
				case 'z': 
					trapini();
					break;
#endif
				}
			}
			break;
		case '?':
			errflg++;
		}
        }
#ifdef IBM_PC
	if (!adacomp_option) {
		fprintf(stderr, "NYU Binder Version 1.11.2,");
		fprintf(stderr, " Copyright (C) 1985-1992 by New York University\n");
	}
#endif
	fname = (char *)0;
	if (optind < argc)
		fname = argv[optind];
	/* if fname not given, get from environment. */
	if (!errflg && !lib_opt && fname == (char *)0) {
		fname = getenv("ADALIB");
		if (fname!= (char *)0 && !adacomp_option) {
#ifdef IBM_PC
			fprintf(stderr, "L");
#else
			fprintf(stderr, "l");
#endif
			fprintf(stderr, "ibrary defined by ADALIB: %s\n", fname);
		}
	}
	if ((!lib_opt && fname == (char *)0) || errflg) {
	       fprintf (stderr, "Usage: adabind [-m main_unit] [-l library]\n");
	       exitp(RC_ABORT);
	}
	if (!lib_opt) {
           lib_name = emalloc(strlen(fname) + 1);
	   strcpy(lib_name, fname);
        }
	t_name = libset(lib_name); /* set library */
	gen_option = FALSE; /* bind only */

	tup_init(); /* initialize set and tuple procedures */
	FILENAME = (fname != (char *)0) ? strjoin(fname, "") : lib_name;

	PREDEFNAME = predef_env();
	if (nobuffer) {
		setbuf (stdout, (char *) 0);	/* do not buffer output (for debug) */
	}
	rat_init(); /* initialize arithmetic and rational package*/
	dstrings_init(2048, 256); /* initialize dstrings package */
	init_sem();
	DATA_SEGMENT_MAIN = main_data_segment();
	aisunits_read = tup_new(0);
	init_symbols = tup_exp(init_symbols, seq_symbol_n);
	for (i = 1; i <= seq_symbol_n; i++)
		init_symbols[i] = seq_symbol[i];

	num_predef_units = init_predef();
	/*
	 * When the separate compilation facility is being used all references to
	 * AIS files will be made via the directory in LIBFILE. AISFILENAME is set
	 * to a number.
	 */
	if (new_library) 
		AISFILENAME = "1";
	else
		AISFILENAME = lib_aisname(); /* retrieve name from library */
	/* open the appropriate files using the suffix .axq for axq files and
	 * .trc for tree file. 
	 *
	 * Open MESSAGEFILE with suffixe ".msg" if a file name specified;
	 * otherwise, if a file name not required, and one is not given,
	 * used stderr.
	 */
	AXQFILE  = ifopen(AISFILENAME, "axq", "w", 0);
	if (adacomp_option) {
		MSGFILE  = efopenl(source_name, "msg", "a", "t");
		/* unbuffer output for debugging purposes */
		setbuf(MSGFILE, (char *) 0);
	}
	else {
		MSGFILE = stdout;
	}
	bpreface();

	/* Code formerly procedure finit() in init.c is now put here directly */
	if (!errors) {
		write_glib();
		cleanup_files();
	}

	exitf(RC_SUCCESS);
}

static void fold_upper(char *s)								/*;fold_upper*/
{
	register char c;

	while (c = *s) {
		if (islower(c)) *s = toupper(c);
		s++;
	}
}

void fold_lower(char *s)										/*;fold_lower*/
{
	register char c;

	while (c = *s) {
		if (isupper(c)) *s = tolower(c);
		s++;
	}
}

static void bpreface()											/*;bpreface*/
{
	/* bpreface is version of preface for use with binder */

	int	i;
	Tuple	aisread_tup;

	aisread_tup = tup_new(0);
	initialize_1();
	/* 1- Load PREDEF */

	TASKS_DECLARED = FALSE;
	/* 2- Generate user program */

	initialize_2();

	ada_line = 9998;
	/* if binding, make ais_read tupe correspond to library */
	aisread_tup = tup_new(0);
	for (i = 11; i <= unit_numbers; i++)
		aisread_tup = tup_with(aisread_tup, pUnits[i]->name);

#ifdef EXPORT
	list_code = 0;
#endif
	if (binder(aisread_tup))
		store_axq(AXQFILE, unit_number_now);
	ifclose(AXQFILE);
	if (errors) {
#ifdef DEBUG
		user_info("Binding stopped");
#endif
		exitf(RC_ERRORS);
	}
}

static void exitf(int status)										/*;exitf*/
{
	/* exit after closing any open files */
	ifoclose(AXQFILE);
	ifoclose(LIBFILE);
	ifoclose(STUBFILE);
	exitp(status);
}

void user_error(char *reason)									/*;user_error*/
{
	errors++;
	if (adacomp_option) {
		list_hdr(ERR_SEMANTIC);
		fprintf(MSGFILE, " %s\n", reason);
	}
	else
		printf(" %s\n", reason);
}

void user_info(char *line)										/*;user_info*/
{
	/* In SETL USER_INFO macro is defined to be
     * PRINTA(GENfile, INFORMATION, ada_line, 0, ada_line, 0, '	'+line)    endm;
	 * where the argument is always a unit_name passed to formatted name
	 * In C, we call user_info and fill in needed info
	 */

	if (adacomp_option) {
		list_hdr(INFORMATION);
		fprintf(MSGFILE, "%s\n", line);
	}
	else {
		printf("%s\n", line);
	}
}
