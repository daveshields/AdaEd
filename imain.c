/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include <string.h>
#include "config.h"
#include "ivars.h"
#include "slot.h"
#include "ifile.h"
#include "intaprots.h"
#include "loadprots.h"
#include "miscprots.h"
#include "libfprots.h"

#ifdef DEBUG
int heap_store_offset = 0;
#endif

static void fold_lower(char *);
static void fold_upper(char *);

/* global variable needed for imain.c, derived from generator */
FILE *efopen();

main(int argc, char **argv)											/*;main*/
{
	int         c, i, n, status;
	int         errflg = 0, nobuffer = 0;
	char        *FILENAME;
	IFILE       *ifile;
	extern int  optind;
	extern char *optarg;
        int         lib_opt = FALSE;
	char        *library_name, *fname;
	char	*t_name;
	Axq		axq;
	char	*main_unit = (char *)0;
	char 	*tname;

	rr_flag = FALSE;
	max_mem = MAX_MEM;
#ifdef IBM_PC
	new_task_size = 2048;
	main_task_size = 4096;
#else
	main_task_size = 10000;
	new_task_size = 10000;
#endif
#ifdef IBM_PC
	while((c = getopt(argc,argv,"BbH:h:L:l:M:m:p:P:s:S:t:T:w:R:r:"))!=EOF){
#else
	while((c = getopt(argc,argv,"bh:l:m:p:s:t:w:r:"))!=EOF){
#endif
		/*    user:
		 *      h       heap size in kilobytes
		 *	l	library name
		 *	m	main unit name
		 *	p	main program task stack size
		 *	r	nb max consecutive stmts for the same task 
                 *              (round-robin)
		 *	s	task stack size
		 *	t	tracing, followed by list of options:
		 *                a	Ada lines
		 *                c	calls 
		 *                e	exceptions
		 *                r	rendezvous
		 *                s	context-switches
		 *                t	tasks
		 *    debug (only):
		 *                d	debug
		 *		  i 	instruction
		 *	b	do not buffer standard output
		 *	w	off	trace stores at specified offset in heap
		 */
#ifdef IBM_PC
                if (isupper(c)) c = tolower(c);
#endif
		switch(c) {
#ifdef DEBUG
		case 'b':	/* do not buffer standard output (for debugging) */
			nobuffer++;
			break;
		case 'w':	/* storage write trace */
			heap_store_offset = atoi(optarg);
			break;
#endif
		case 'h': /* heap size in kilo bytes */
#ifndef IBM_PC
			max_mem = 1000*atoi(optarg);
#else
			{
				int optval; /* avoid too large value */
				optval = atoi(optarg);
				if (optval > 0 && optval < MAX_MEM/1000) 
					max_mem = 1000*optval;
			}
#endif
			break;
		case 'l': /* specify library name */
                        lib_opt = TRUE;
			library_name = strjoin(optarg,"");
			break;
		case 'm': /* specify main unit name */
			main_unit = strjoin(optarg,"");
			fold_upper(main_unit);
			break;
		case 'p': /* main task stack size */
			i = atoi(optarg);
			if (i > 0 && i < 31)	 /* small value gives kilowords */
				main_task_size = i * 1024;
			else if (i > 31)
				main_task_size = i;
			break;
		case 's': /* task stack size */
			i = atoi(optarg);
			if (i > 0 && i < 31)	/* small value gives kilowords */
				new_task_size = i * 1024;
			else if (i > 31)
				new_task_size = i;
			break;
		case 'r': /* nb max consecutive stmts (round-robin) */
			i = atoi(optarg);
			if (i > 0) {
				rr_nb_max_stmts = i;
				rr_flag = TRUE;
			}
			else
	                        errflg++;
			break;
		case 't': /* interpreter trace arguments */
			n = strlen(optarg);
			for (i = 0; i < n; i++) {
#ifdef IBM_PC
				if (isupper(optarg[i]))
                                   optarg[i] = tolower(optarg[i]);
#endif
				switch(optarg[i]) {
				case 'c': /* calls */
					call_trace++;
					break;
				case 'e': /* exceptions */
					exception_trace++;
					break;
				case 'a': /* Ada lines */
					line_trace++;
					break;
				case 'r': /* rendezvous */
					rendezvous_trace++;
					break;
				case 't': /* tasks */
					tasking_trace++;
					break;
				case 's': /* context-switches */
					context_sw_trace++;
					break;
#ifdef DEBUG
				case 'd': /* debug */
					debug_trace++;
					break;
				case 'i': /* instructions */
					instruction_trace++;
					break;
#endif
				default:
					errflg++;
					break;
				}
			}
			break;
		case '?':
			errflg++;
		}
	}
#ifdef DEBUG
	if (debug_trace)
		printf("program, new task stack sizes %d %d\n",
		  main_task_size, new_task_size);
#endif
        fname = (char *)0;
	if (optind < argc) fname = argv[optind];
        if (!lib_opt && fname == (char *)0) { 
		fname = getenv("ADALIB");
	}
	if ((!lib_opt && fname == (char *)0) || errflg) {
 	   fprintf(stderr,
		  "Usage: adaexec -m main_unit -h size -r nb_stmts -t[acerst] [-l library]\n");
		exit(RC_ABORT);
	}
        if (!lib_opt) {
           library_name = emalloc(strlen(fname) + 1);
           strcpy(library_name, fname);
        }
#ifdef DEBUG
	if (nobuffer)
		setbuf(stdout,(char *) 0);/* do not buffer output(for debug) */
#endif
	FILENAME = library_name;
	t_name = libset(library_name);

	/* AXQFILE is opened by load_axq or library read (TBSL);*/
	axq = (Axq) emalloc((unsigned) sizeof(Axq_s));
	load_slots(FILENAME, &ifile, axq);
	/* second arg to load_lib and load_axq is non-null if file open */
	load_lib(FILENAME, ifile, axq, main_unit, argv);

	status = int_main();
	exit(status);
}

static void fold_upper(char *s)					/*;fold_upper*/
{
	char c;

	while (*s) {
		c = *s;
		if (islower(c)) *s = toupper(c);
		s++;
	}
}
