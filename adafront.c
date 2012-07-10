/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "hdr.h"
#include "ada.h"
#include "ifile.h"
#include "miscprots.h"
#include "libfprots.h"
#include "actionprots.h"
#include "adaredprots.h"
#include "prsutilprots.h"
#include "prserrprots.h"
#include "adalexprots.h"
#include "adaprsprots.h"

#include "vars.h"
#include "libhdr.h"
#include "libprots.h"
#include "librprots.h"
#include "libwprots.h"
#include "setprots.h"
#include "dbxprots.h"
#include "arithprots.h"
#include "smiscprots.h"
#include "chapprots.h"
#include "dclmapprots.h"
#include "sspansprots.h"


static void lrparse();
static void errorinit(struct two_pool **, struct two_pool **, int *);
static void exitf(int);

/* Global variables */

struct prsstack *prs_stack = NULL,	/* Stack containing symbols */
*curtok,		/* Current input token */
*PREVTOK = NULL;	/* Previous input token */
struct two_pool *sta_stack;		/* The state stack */
/* not used by parser */
FILE  *adafile,				/* File pointer for ada source file */
*msgfile,				/* File pointer for msgs file */
*errfile;				/* File pointer for error & debug info*/

Node any_node;	/* Special nodes to indicate
					   optional elements in the ada
					   syntax, or a node to be filled in */
int redopt = 0;				/* Flag for printing rules */
int erropt = 0;				/* Flag for printing debugging info */
int termopt = 0;			/* Flag for terminal display */
int debugopt = 0;			/* True if any debugging options on */
int trcopt = 0;				/* True if erropt or redopt set */
extern int optind;			/* global option index */

int n_sta_stack;		    /* The size of the state stack */
int n_prs;
struct prsstack **tokens = NULL;    /* Token stack */
int tokind = -1;
int toksiz = 1;	    /* Size of array used for token stack */
int tokbottom = 0;

extern int optind;
extern char *optarg;

IFILE *LIBFILE;
IFILE *STUBFILE;
IFILE *AISFILE;
IFILE *TREFILE;

int main(int argc, char **argv)				/*;main*/
{
	/* Variables for reading command line and figuring out names
       of files, etc. */
	char *adafilename = NULL;
	char *sourcefilename;
	char *errfilename = NULL;
	char *lib_name;
	char *t_name;
	int  c, n, i;
	int  lib_option = FALSE;
	int  new_library = FALSE;
	int unbufflag = 0;
	int  prefix_len, base_len, suffix_len;
	char *basep;

	Node nod;
	int		compiling_predef = 0;

	/* The parser bombs on VAX if no arguments, so for now fail and
     * also modify usage message to indicate that filename required
     */

	/*  ***** Many options were stripped out during merge of adaprs */
	/*  ***** and adasem.  Relevant ones could be returned.			*/
	/*  ***** Mostly debugging stuff.								*/

	/* Figure out what the command line means */
	while ((c = getopt(argc, argv, "l:np:s:")) != EOF)
	{
		switch (c) {
		case 'l': /* using existing library */
			lib_option = TRUE;
			lib_name = emalloc(strlen(optarg) + 1);
			strcpy(lib_name, optarg);
			break;
		case 'n': /* indicates new library */
			new_library = TRUE;
			lib_option = TRUE;
			break;
		case 'p': /* parser sub options */
			n = strlen(optarg);
			for (i = 0; i < n; i++) {
				switch (optarg[i]) {
				case 'b' :  /* unbuffer output */
					unbufflag = 1;
					break;
				case 'e' :
					erropt = 1 ;
					break ;
				case 'r' : /* display of reductions + source */
					redopt = 1;
					break;
					/* terminal display of source + error messages */
				case 't':
					termopt = 1;
					break;
				}
			}
			break;
		case 's':
			n = strlen(optarg);
			for (i=0; i <= n; i++) {
				switch(optarg[i]) {
				case 'p': /* compiling predef units */
					compiling_predef++;
					break;
				}
			}
			break;
		default:
			exitp(RC_ABORT);
		}
	}
	if (optind < argc) {
		adafilename = argv[optind];
		basep = parsefile(adafilename, &prefix_len, &base_len, &suffix_len);
		FILENAME = emalloc(base_len + 1);
		strncpy(FILENAME, basep, base_len);
		if (suffix_len == 0) { /* if suffix .ada implied */
			sourcefilename = emalloc(strlen(adafilename) + 4 + 1);
			strcpy(sourcefilename, adafilename);
			strcat(sourcefilename, ".ada");
		}
		else {
			sourcefilename = adafilename;
		}
		adafile = efopen(sourcefilename, "r", "t");
	}
	else {
		fprintf(stderr, "Bad usage: no adafile specified.\n");
		exitp(RC_ABORT);
	}
	t_name = libset(lib_name);
	trcopt = redopt || erropt ;
	debugopt = termopt || redopt || erropt ;
	msgfile = efopenl(FILENAME, "msg", "w", "t");
	if (trcopt) {
#ifndef IBM_PC
		errfile = efopenl(FILENAME, "err", "w", "t");
#else
		/* write to stdout on PC */
		errfile = stdout;
#endif
	}
	else {
		errfilename = NULLFILENAME ;
		errfile = (FILE *)0;
	}

	if (unbufflag)
	{
		if (trcopt)
			setbuf(errfile, (char *)0);
		setbuf(msgfile, (char *)0);
	}


/* SEM STUFF */
	STUBFILE= (IFILE *)0;
	AISFILE = (IFILE *)0;
	tup_init(); /* initialize tuple package */

	PREDEFNAME = predef_env();
	dstrings_init(2048, 512); /* initialize dstrings package */

	rat_init(); /* initialize arithmetic and rational package*/
	init_sem();
	seq_node_n = 0;
	any_node = node_new(as_opt);

	aisunits_read = tup_new(0);
	init_symbols = tup_exp(init_symbols, (unsigned)  seq_symbol_n);
	for (i=1; i<= seq_symbol_n; i++)
		init_symbols[i] = seq_symbol[i];

	if (!compiling_predef) init_predef();
	/* When the separate compilation facility is being used all references to
	 * AIS files will be made via the directory in LIBFILE. AISFILENAME is set
	 * to a number if the library is used, otherwise it is the FILENAME.  
	 */
	if (lib_option) {
		if (compiling_predef)
			AISFILENAME = "0";
		else if (new_library) 
			AISFILENAME = "1";
		else {
			/* here to get AIS name from lib. Note the library is left open*/
			AISFILENAME = lib_aisname();
			read_lib();
		}
	}
	else {
		AISFILENAME = FILENAME;
	}
	/* open the appropriate files using the suffix  .aic for ais files and
     * .trc for tree file. 
     */
	AISFILE  = ifopen(AISFILENAME, "aic", "w", 0);
	TREFILE  = ifopen(AISFILENAME, "trc", "w", 0);
	/* delete any existing stubfile for current AISFILENAME */
	ifdelete(strjoin(AISFILENAME, ".st1"));
	lrparse();
	if (debugopt && errors)
		printf("%d parse error(s) found.\n", errors);
	fclose(adafile);
	if (trcopt)
		fclose(errfile);

	exitf(errors ? RC_ERRORS : RC_SUCCESS);
}

/* 
 *			Lrparse: Parser driver. 
 * Gettok() is called to return the next token.
 *  Action is called to compute the next action to be taken given the
 *  state and current token. If the action is a reduction, the reduction
 *  of the state stack is performed, the reduction of the parse stack
 *  is deferred until the next shift by putting onto the queue marked by
 *  topred and lastred, and the new state is computed with another call to
 *  action acting as a GOTO. If the action is a shift, all deferred reductions
 *  are performed, the current token is added to the parse stack, and
 *  the new state is equal to the value returned by action(). When the action
 *  is shift and is equal to NUM_STATES, this is an accept action, and we 
 *  return. 
 */

/* 
 *	A stack of tokens is kept so as to conform with the addition of an 
 *  error recovery routine. Tokens is the variable which is used as an
 *  array to store the tokens. Tokind is the index into this array indicating
 *  the next token to be returned, or -1 if there are no stored tokens.
 *  The macro NEXTTOK is designed for use with this scheme. Toksiz represents
 *  the size of the array being used for the token stack at any given time.
 *  If we need more space, we call realloc() to give us more storage, and
 *  change toksiz to reflect this change. 
 */

/*
  *	Changes made for error recovery		(12/28/83-NG)
  *
  *  Before the call to prserr(), some manipulation of the state and
  *  parse stacks must be performed. A "common point" between these
  *  two stacks must be kept. Before the call to prserr(), the state
  *  stack from the common point must be freed, and then increased to a 
  *  size equal that of the parse stack. This is done by computing
  *  states from the current top of the state stack and the corresponding
  *  position in the parse stack, putting the new state on top and then
  *  using it to compute the next state in the same manner.
  *  This common point is implemented as follows :
  *  The variable sta_com_pt is a pointer to the element of the state
  *  stack which corresponds to the common point. The variable 
  *  prs_com_pt_ct is an integer telling how many elements, from the top
  *  of the parse stack, are needed to reach that element of the parse
  *  stack corresponding to the element in the state stack pointed to
  *  by sta_com_pt (in terms of the sizes of the stacks below these
  *  elements). After performing a shift, sta_com_pt is NULL, and 
  *  prs_com_pt_ct is 0. This is because all deferred reductions will
  *  have been performed, putting the two stacks in alignment. The NULL
  *  indicates that the common point is above (the top of) the state
  *  stack. When there is a reduction, the sta_com_pt may shift down in
  *  the stack or remain the same. If it shifts downwards, then
  *  prs_com_pt_ct is shifted also by the number of elements sta_com_pt
  *  was shifted. (When this first happens sta_com_pt becomes non-NULL)
  *	 Just before the call to prserr(), first free the elements of the 
  *  state stack using the pointer we have to the last element we wish
  *  freed. Then copy prs_com_pt_ct elements from the top of the parse
  *  stack into an array. We then compute the states from the state on top
  *  of the state stack and the next element of the parse stack (from the 
  *  array).
  *
  */



static void lrparse()				/*;lrparse*/
{
	struct two_pool *topred = NULL,	/* Top of reduction queue */
	*lastred = NULL;	/* Bottom of reduction queue */
	int act;				/* Pending action */
	struct two_pool *tmp, *top;		/* Temps */
	int n,		/* Number of symbols being reduced */
	red;		/* Reduction to be performed */
	struct two_pool *sta_com_pt = NULL; /* Common point stuff */
	int i;
	int prs_com_pt_ct = 0;
	int prs_ct_flag;

	sta_stack = TALLOC();
	sta_stack->val.state = 1;
	sta_stack->link = NULL;
	curtok = NEXTTOK;

	while (1)			/* Main parse loop */
	{
		/*	Determine action */

#ifdef DEBUG1
		if (trcopt) {
			fprintf(errfile, "action(%d, %d) = ", sta_stack->val.state, curtok->symbol);
		}
#endif
		act = action(sta_stack->val.state, curtok->symbol);
#ifdef DEBUG1
		if (trcopt)
			fprintf(errfile, "%d \n", act) ;
#endif

		if (!act)		/* ERROR */
		{
			if (topred != NULL)
				errorinit(&sta_stack, &sta_com_pt, &prs_com_pt_ct) ;

			prserr(curtok);		/* THIS IS IT : PRSERR */

			curtok = NEXTTOK ;

#ifdef DEBUG
			/* print debugging information */
			if (trcopt) {
				fprintf(errfile, "RECOVERED\n");
				fprintf(errfile, "STATE STACK:\n");
				dump_stack(sta_stack);
				fprintf(errfile, "PARSE STACK:\n");
				dump_prsstack(prs_stack);
				fprintf(errfile, "NEXT TOKEN: %s\n", TOKSTR(curtok->symbol));
			}
#endif

			/* 
			 * Free any pending reductions 
			 */
			if (topred != NULL) {
				TFREE(topred, lastred) ;
				topred = lastred = NULL ;
			}
		}

		else if (act <= NUM_STATES) /* Shift */
		{
			/* Perform deferred reductions on prs_stack */

			if (topred != NULL) {

				tmp = topred;
				while (topred != NULL) {
					reduce((int)topred->val.reduction);
					topred = topred->link;
				}
				TFREE(tmp, lastred);
				lastred = NULL;
			}
			tmp = TALLOC();
			tmp->val.state = act;
			tmp->link = sta_stack;
			sta_stack = tmp ;
			n_sta_stack ++ ;
			curtok->prev = prs_stack;
			prs_stack = curtok;
			PREVTOK = copytoken(curtok) ;
			curtok = NEXTTOK;
			n_prs ++ ; /* Increment the size of the parse stack */

			sta_com_pt = NULL;		/* Initialize comm pt stuff */
			prs_com_pt_ct = 0;

			if (act == NUM_STATES)	/* Accept */
				return;
		}
		else /* Reduce */
		{
			red = act - NUM_STATES - 1;
			n = rhslen[red];
			tmp = TALLOC();
			tmp->val.reduction = red;
			tmp->link = NULL;
			prs_ct_flag = 0;
			if (lastred == NULL)
				topred = lastred = tmp;
			else {
				lastred->link = tmp;
				lastred = tmp;
			}
			if (!n) {
				tmp = TALLOC();
				tmp->link = sta_stack;
				sta_stack = tmp;
			}
			else if (n > 1) {
				top = sta_stack;
				n_sta_stack = n_sta_stack - n + 1 ;
				for (i = n - 2; i--; ) {
					if (sta_com_pt == sta_stack)   /* The common point */
					{				   /* might be freed here */
						sta_com_pt = NULL;
						prs_ct_flag = 1;
						prs_com_pt_ct += 2;
					}
					else if (prs_ct_flag)    /* Keep count of no. of places */
						prs_com_pt_ct++;	/* common point will move */
					sta_stack = sta_stack->link;
				}
				if (sta_com_pt == sta_stack) {
					sta_com_pt = NULL;
					prs_com_pt_ct ++ ;
				}
				tmp = sta_stack;
				sta_stack = sta_stack->link;
				TFREE(top, tmp);
			}

			/* Set sta_com_pt if needed, and set prs_com_pt_ct to
	       point to right part of prs_stack in the case in which 
	       this is the first reduction after a shift. */
			if (sta_com_pt == NULL) {
				sta_com_pt = sta_stack;
				if (!prs_com_pt_ct)
					prs_com_pt_ct = n ;
			}

			sta_stack->val.state = 
			    action((int)sta_stack->link->val.state, lhs[red]);
		}
	}
}

static void errorinit(struct two_pool **psta_stack,
  struct two_pool **psta_com_pt, int *pprs_com_pt_ct)	/*;errorinit*/
{
	struct two_pool *tmp;
	struct prsstack **tmp_prs_array;
	struct prsstack *prs_temp;
	int i;

	if (*psta_com_pt == NULL)
		return;
	tmp = (*psta_com_pt)->link;
	TFREE(*psta_stack, *psta_com_pt);
	*psta_stack = tmp;
	*psta_com_pt = NULL;
	if (!*pprs_com_pt_ct)
		return;
	tmp_prs_array = (struct prsstack **)malloc((unsigned)(*pprs_com_pt_ct * 
	  (sizeof(struct prsstack *))));
	for (i = 0, prs_temp = prs_stack; i < *pprs_com_pt_ct; i++,
	  prs_temp = prs_temp->prev)
		tmp_prs_array[i] = prs_temp;
	for (i = *pprs_com_pt_ct - 1; i >= 0; i--) {
		tmp = TALLOC();
		tmp->link = *psta_stack;
		tmp->val.state = action((int)(*psta_stack)->val.state,
		  tmp_prs_array[i]->symbol);
		*psta_stack = tmp;
	}
	free((char *)tmp_prs_array);
	*pprs_com_pt_ct = 0;
}

struct prsstack *tokfromlist()			/*;tokfromlist*/
{
	int tmp = tokind;

	tokind = (tokind - 1 + toksiz) % toksiz;
	return(tokens[tmp]);
}

static void exitf(int status)										/*;exitf*/
{
	/* exit after closing any unclosed files */

	ifoclose(AISFILE);
	ifoclose(STUBFILE);
	ifoclose(TREFILE);
	exitp(status);
}

