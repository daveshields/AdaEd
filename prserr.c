/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/********************************************************************
 *								    
 *			  *****************			   
 *			  *  P R S E R R  
 *			  *****************			 
 *								
 *			     Written by			       
 *			   Brian Siritzky		      
 *				1983			     
 *							    
 ********************************************************************/

/********************************************************************/

/********************************************************************/

#include "hdr.h"
#include "ada.h"
#include "adalexprots.h"
#include "actionprots.h"
#include "pspansprots.h"
#include "errsprots.h"
#include "lookupprots.h"
#include "prsutilprots.h"
#include "recoverprots.h"
#include "makecorrprots.h"
#include "prserrprots.h"

static void get_poss_tok();
static void get_next(int);

/*	
 * Variables needed for scope and secondary recoveries
 */

struct two_pool *closer_toksyms ;
struct two_pool *closer_bottom ;

struct two_pool *POSS_TOK;
/* struct prsstack **tokens; deleted on Sam's suggestion 12-11-84 */
int	TOKSYMS[S_TOKSYMS], n_TOKSYMS;
int	BACKUPTOKS = 0;
int	MAX_CHECK = MIN_LEN ;

PCAND next_c, y, next_cand, CANDIDATES[C_BOUND];
static PCAND tmp_cand,temp_cand;
int	n_CANDIDATES[C_BOUND] ;
int nps;
int n_open_seq;
int *open_seq;
int n_closer_toksyms;

void prserr(struct prsstack *curtok)							/*;prserr*/
{

	/********************************************************************
	 *
	 * This routine is the syntactic error	recovery  routine.   It	 at-
	 * tempts  to  correct	simple errors and when that is not possible,
	 * deletes tokens possibly to the left and to the right of the error
	 * point until the parse can safely resume.  The process is thus di-
	 * vided naturally into two  parts,  called  primary  and  secondary
	 * recovery.  Both primary and secondary recovery include efforts at
	 * "scope recovery": i.e.  the	closing	 of  lexically	open  scopes
	 * through the insertion of one or more closer token sequences.	 Ex-
	 * amples of such sequences are right parentheses, "END ;", and "END
	 * IF;".
	 * 
	 * Primary recovery consists of the simple corrections - merging to-
	 * kens,  substituting	a  token  (including a reserved word that is
	 * misspelled as an identifier), inserting a token, and	 deleting  a
	 * token - along with scope recovery.
	 * 
	 * An attempt at simple correction at either the error token  or  at
	 * some parse stack element is called a trial.
	 * 
	 * For the first trial simple corrections are attempted at the token
	 * at which the error was detected (the error token), with the parse
	 * in the configuration obtaining just after  the  shifting  of	 the
	 * previous  token. In order to back up to the succeeding trial, the
	 * top elements are peeled from the state and parse stacks, with the
	 * top element of the parse stack appended to the front of the input
	 * token sequence. Again attempts at simple correction are made. The
	 * process  is	repeated  until	 the determined extent of the backup
	 * move has been accomplished.
	 * 
	 * The criterion by which the effectiveness of a  simple  correction
	 * candidate is measured is the distance it allows the parse to pro-
	 * gress into the forward context (up to  MAX_LOOK_AHEAD  =  25	 to-
	 * kens).   During  the	 simple correction trials we gather together
	 * the CANDIDATES that allow the parse	to  progress  the  furthest,
	 * provided  that  an  advance of at least MIN_CHECK is accomplished
	 * (if not, then CANDIDATES is empty and simple	 correction  fails).
	 * If  CANDIDATES is not empty, it is pruned in accordance with cer-
	 * tain restrictions described below, and then one of them is chosen
	 * as the appropriate correction provided that a condition described
	 * below is satisfied.
	 * 
	 * No attempt is made to delete or substitute for a nonterminal.
	 * 
	 * If no simple correction is chosen, scope recovery is attempted at
	 * each	 point	at  which  simple  recovery was attempted. The scope
	 * recovery procedure determines whether the insertion of a sequence
	 * of  scope  closers  allows the parse to progress MIN_LEN distance
	 * into the forward context.  If  so,  this  multiple  insertion  is
	 * chosen as the correction candidate.
	 * 
	 * If scope recovery also fails, then secondary recovery is invoked.
	 * The	parse  is  restored  to the configuration obtaining upon en-
	 * trance to PRSERR, and each parse stack element is tested - in se-
	 * quence from the top - to see whether parsing can resume from that
	 * point, perhaps with the inclusion of one or more closer token se-
	 * quences.  The  extent  of  the  advance required in order for the
	 * parse to be regarded as successfully	 resumed  depends  upon	 the
	 * current token, but is at least MIN_LEN.
	 * 
	 * If secondary recovery at the current token does not	succeed,  it
	 * is  ignored	and  the next one obtained and the same check is re-
	 * peated. Eventually, there must be an input for  which  the  parse
	 * can	continue, because the end of file token, EOFT, is compatible
	 * with a state on the state stack.
	 * 
	 * When the recovery point is found,  control  is  returned  to	 the
	 * parser.  It is assured that parsing can continue beyond the error
	 * token.
	 * 
	 ********************************************************************/

	/* PARSE STACK and BINARY TUPLE STRUCTURES */
	typedef struct two_pool *TUPLE;


	struct prsstack *ERROR_TOKEN;
	struct prsstack *oldprevtok;/* Saved for scope and secondary recovery */
	struct prsstack *tmp_ps;

	TUPLE STATE_STACK = NULL;
	TUPLE prs_toks = NULL;	/* Used to determine the no of */
	TUPLE tmp_tp;			/* trials to be performed */
	/* Used for freeing storage */
	TUPLE prs_stack_syms = NULL;

	int pb;			/* Used as a flag to check for a parse block */
	int threshold,		/* Used to prune candidates */
	exists;		/* Flag used in list searching */

	short trials,		/* Number of trials performed	*/
	  j, r, trial,
	  i,			/* Loop and auxilliary		*/
	  bk, cc, x, si ;

	int n_PARSE_STACK;
	int save_n_TOKSYMS ;
	struct two_pool *states;

	int	    n_single_cand_modes, total_CANDIDATES;
	int	    n_STATE_STACK, n_sta_stack;

	ERROR_TOKEN = copytoken (curtok);
	MAX_CHECK = MIN_LEN;

	/* ERR_MSGS = NULL ; CLOSER_TOKSYMS = NULL ; */

	copystack (sta_stack, &STATE_STACK, &n_sta_stack);
	/* save for scope and secondary recovery */
	if (PREVTOK != NULL)
		oldprevtok = copytoken (PREVTOK);

	n_STATE_STACK = n_sta_stack;

	BACKUPTOKS = 0;

	get_next (MAX_LOOK_AHEAD);

	/* prs_stack_syms := [r(1) : r in PRS_STACK];		    
	 * Loop over PRS_STACK, collecting the symbols in a list  
	 * headed by prs_stack_syms. While doing this, count up the 
	 * number of elements in the parse stack, keeping this in  
	 * n_PARSE_STACK and nps				   
	 */

	n_PARSE_STACK = 0;

	if ((tmp_ps= prs_stack) == NULL)/* Check for empty stacks */
		prs_stack_syms = NULL;
	else {				/* otherwise copy the list */
		/* Treat the first element as a special case */
		tmp_tp = prs_stack_syms = TALLOC ();
		tmp_tp -> link = NULL;
		tmp_tp -> val.state = tmp_ps -> symbol;
		n_PARSE_STACK = 1;
		/* Loop over the rest of the stack */
		while (tmp_ps -> prev != NULL) {
			tmp_tp -> link = TALLOC ();
			tmp_tp = tmp_tp -> link;
			tmp_ps = tmp_ps -> prev;
			tmp_tp -> val.state = tmp_ps -> symbol;
			n_PARSE_STACK++;
		}			/* while */
		tmp_tp -> link = NULL;
	}				/* else */
	nps = n_PARSE_STACK;

	/* * TOKSYMS := [t(1) : t in TOKENS];			 
	 * Loop over TOKENS, collecting the symbols in a list	
	 * The integer tokind is a count of the number of     
	 * elements in the array tokens.		      
	 *
	 * Note that tokens[tokind] is the next token, so we must
	 * reverse the order of TOKSYMS							
	 */

	/* Put the current token at the top of the token stack */
	tokens[tokind = (tokind + 1) % toksiz] = curtok;
	i = 0;
	j = tokbottom;

	for (;;) {
		TOKSYMS[i] = tokens[j]->symbol;
		if (j == tokind)
			break;
		j = (j + 1) % toksiz;
		i++;
	}

	save_n_TOKSYMS	= n_TOKSYMS = (toksiz + tokind - tokbottom) % toksiz;
	/*
    for (i = 0; i <= tokind; i++)
	TOKSYMS[i] = tokens[i] -> symbol;

    n_TOKSYMS = tokind;
	*/
	dump_toksyms ("At creation");

	/******************************************************************* 
	 *
	 *					S I M P L E    R E C O V E R Y		    
	 *	       
	 *******************************************************************/

	/*	Simple Recovery begins here	 */

	/* Determine number of trials to be performed.  */
	prs_toks = TALLOC ();
	prs_toks -> val.state = curtok -> symbol;
	prs_toks -> link = NULL;

	/* trials = (nps>0) ? nps : 1 ; */
	trials = (n_sta_stack>0) ? n_sta_stack : 1 ;

	states = TALLOC ();
	states -> link = NULL;

	/* for (j = nps; j >= 1; j--) */
	for (j = n_sta_stack; j >= 2; j--) {
		int	jj;
		/* prs_stack_syms(j) is at position (nps - j)  in the linked list.
		 * For this reason we need to follow the links this many times
		 */
		/* jj = nps - j + 1; */
		jj = n_sta_stack - j + 1;
		tmp_tp = prs_stack_syms;
		while (jj-- > 1)
			tmp_tp = tmp_tp -> link;

		r = tmp_tp -> val.state;	/* r := prs_stack_syms(j) */

#ifdef DEBUG
		if (trcopt) {
			fprintf(errfile,"j = %d	 n_sta_stack = %d  r = %d\n",
			  j,n_sta_stack,r);
		}
#endif
		/* dump_stack(prs_toks); */

		/* Check whether it is possible to parse past symbol
		 *	and through the error token.			
		 *
		 *	if forall s in SHIFT_STATES(r) | prs_block(s, prs_toks)
		 *	then
		 *	    trials := nps - j + (if is_terminal(r) then 2 else 1 end);
		 *	    quit;
		 *	end if;
		 */
		pb = TRUE;		/* Assume that the parse will block */
		/* Loop through SHIFT_STATES(r). This is the array SHIFT_STATES from
		 * position SHIFT_STATE_INDEX(r-1) to SHIFT_STATE_INDEX(r) - 1
		 * Each time check if the parse blocks, pb. If it does not then end the
		 * testing.
		 */
		for (si = SHIFT_STATE_INDEX[r - 1];
		  ((si <= (SHIFT_STATE_INDEX[r] - 1)) && pb);
		  si++)
		{
			states -> val.state = SHIFT_STATE[si];
			pb = pb && prs_block (states, prs_toks);

#ifdef DEBUG
			if (trcopt)
				fprintf(errfile,"state: %d	 prsblock: %d\n",
				  states->val.state, prs_block(states,prs_toks) );
#endif
		}

		if (pb) {			/*  If the parse blocks then terminate	*/
			/*trials = 1 + nps - j + (is_terminal (r - 1) ? 2 : 1);*/
			trials = 1 + n_sta_stack - j + (is_terminal (r) ? 2 : 1);
			break;		/* Outer loop */
		}

		tmp_tp = TALLOC ();
		tmp_tp -> link = prs_toks;
		tmp_tp -> val.state = r;
		prs_toks = tmp_tp;

	}				/* end for */

	if (nps == 0)
		trials = 1;	/* To deal with empty parse stacks */
#ifdef DEBUG
	if (trcopt)
		fprintf(errfile,"trials = %d\n",trials);
#endif

	for (trial = 1; trial <= trials; trial++) {
		/*	Attempt simple recovery at token backed up to.	 */
#ifdef DEBUG
		if (trcopt) {
			fprintf(errfile,"Backup Recovery, trial number is: %d\n",trial);
			fprintf(errfile,"STATE STACK:\n");
			dump_stack(sta_stack);
			fprintf(errfile,"PARSE STACK:\n");
			dump_prssyms(prs_stack_syms);
			fprintf(errfile,"TOKENS:\n");
			dump_toksyms("");
		}
#endif

		/* Form set of candidates for insertion and substitution. */

		get_poss_tok ();

		/* Make insertion test.   */

		try_insertion ();

		/* Attempt substitution for current token */

		try_substitution ();

		/* Try merging tokens. */

		if (trial == 1)
			try_merge (curtok, nexttok);
		else
			if (trial == 2)
				try_merge (PREVTOK, curtok);

		/* Check whether parsing can resume with the next token. */

		try_deletion ();

		/* Now we peel off the top state and try again.		   
		 * Put the "token" (terminal or nonterminal) for previous state on 
		 * the list of tokens, and increase backuptoks accordingly.	   
		 */

		tmp_tp = sta_stack;
		sta_stack = sta_stack -> link;
		n_sta_stack--;

		tmp_tp = prs_stack_syms;
		if (prs_stack != NULL) {
			TOKSYMS[++n_TOKSYMS] = prs_stack_syms -> val.state;
			prs_stack_syms = prs_stack_syms -> link;
		}
		BACKUPTOKS++;

	}				/* for */


	/* Form misspelling candidates by applying string distance test in cases
	 *   where a reserved word to be substituted for an identifier.	 
	 */

	if (0 && CANDIDATES[SUBST] != NULL) {
#ifdef DEBUG
		if (trcopt)
			fprintf (errfile, "CANDIDATES[SUBST] != NULL, (#=%d)\n",
			    n_CANDIDATES[SUBST]);
#endif
		/*  spell_substs := {[u, v, w] in CANDIDATES(SUBST) |
		 *	     is_reserved(u) and v = ID_SYM 
		 *	    and spell(namelist(u), namelist(
		 *	     (w = 0 ? curtok : PRS_STACK(nps - w + 1) )(2)))};
		 *
		 *   Note : u == token_sym, v == backup_toks, w == t3
		 *
		 *   Loop over the list headed by CANDIDATES[SUBST], selecting
		 *  all those elements which satisfy the above conditions
		 *
		 *	The spell function used here is a less accurate measure than the
		 *  SETL version. It returns an integer value in the range [0,3],
		 *  where 0, 1 & 2 imply misspellings.
		 */
		nps = stack_count(prs_stack) ;
		next_c = CANDIDATES[SUBST];
		while (next_c != NULL) {
			short   symb;	/* Utility variable */
			PCAND	follow_c ;

			follow_c = next_c-> next ;

			/* Calculate the word to be compared to according to
			 *		symb = (w==0)?curtok : prs_stack(nps -w + 1)
			 */

			if (next_c -> backup_toks == 0)
				symb = curtok -> symbol;
			else {			/* PRSSTACK[nps-w-1].symbol */
				int kk = nps - next_c->backup_toks ;

				tmp_ps = prs_stack;
				while(--kk)
					tmp_ps = tmp_ps -> prev;
				symb = tmp_ps -> symbol;
			}

			if ( (is_reserved (next_c -> token_sym))
			  && (next_c -> t3 == ID_SYM)
			  && ((spell (TOKSTR (next_c -> token_sym), TOKSTR (symb))) < 3 ) )
			{
				/* Add it to the list of SPELL_SUBSTs. */

				next_c-> next = CANDIDATES[SPELL_SUBST] ;
				CANDIDATES[SPELL_SUBST] = next_c ;
				n_CANDIDATES[SPELL_SUBST]++;
				n_CANDIDATES[SUBST]--;
			}

			next_c = follow_c ;
		}

	}
#ifdef DEBUG
	if (trcopt) {
		fprintf(errfile,"Candidates BEFORE pruning\n");
		dump_cand();
	}
#endif

	/* The correction candidates now include only those that have checked
	 * the furthest distance into the forward context.
	 * Prune this set by applying the preferences and restrictions relevant 
	 * in each case.
	 */

	/* If a long parse check has been achieved, set threshold to true.  */

	threshold = (MAX_CHECK >= (MIN_LEN + 3));

	/*  (for y = CANDIDATES(x)) */

	for (x = DELETE; x <= SPELL_SUBST; x++)
	{
		y = CANDIDATES[x];

		if (y == NULL)		/* Check for null candidate list */
			continue;

		switch (x) {

		case DELETE:

			/* Remove all reserved word deletions if another deletion exists
	    	 * and all such deletions if below the threshold		    
	    	 */

			next_cand = CANDIDATES[DELETE];
			exists = FALSE;
			while ((next_cand != NULL) && (!exists)) {
				exists = exists && (next_cand -> token_sym > RESERVED_SYMS);
				next_cand = next_cand -> next;
			}

			if ((!threshold) || exists) {
				/*  y -:= {[token_sym,-,-] in y | is_reserved(token_sym) }
				 *  This is achieved by looping over the list headed by y
				 *  and deleting those elements which satisfy the condition 
				 */
				next_cand = CANDIDATES[x];
				n_CANDIDATES[x] = 0;
				CANDIDATES[x] = NULL;
				while (next_cand != NULL) {
					/* there are more candidates */
					tmp_cand = next_cand -> next;
					if (!is_reserved (next_cand -> token_sym)) {
						/* Add it to the front of the list  */
						n_CANDIDATES[x]++;
						next_cand -> next = CANDIDATES[x];
						CANDIDATES[x] = next_cand;
					}
					next_cand = tmp_cand;
				}
			}

			/* Prefer deletion closest to error token.	*/

			if (y != NULL) {
				/* bk := min/{t(2) : t in y}; */
				next_cand = y;
				bk = next_cand -> backup_toks;
				next_cand = next_cand -> next;
				while (next_cand != NULL) {
					bk = MIN (bk, next_cand -> backup_toks);
					next_cand = next_cand -> next;
				}

				n_CANDIDATES[x] = 0;
				next_cand = CANDIDATES[x];
				CANDIDATES[x] = NULL;
				while (next_cand != NULL) {
					/* there are more candidates */
					tmp_cand = next_cand -> next;
					if (next_cand -> backup_toks == bk) {
						next_cand -> next = CANDIDATES[x];
						CANDIDATES[x] = next_cand;
						n_CANDIDATES[x]++;
					}

					next_cand = tmp_cand;
				}
			}
			break;

		case INSERT:

			/* Remove all insertions of reserved words if below threshold */

			if (!threshold) {
				/* y -:= {[token_sym,-,-] in y | is_reserved(token_sym) }     
				 * This is achieved by looping over the list headed by y   
				 * and deleting those elements which satisfy the condition 
				 */
				n_CANDIDATES[x] = 0;
				next_cand = CANDIDATES[x];
				CANDIDATES[x] = NULL;
				while (next_cand != NULL) {
					/* there are more candidates */
					tmp_cand = next_cand -> next;
					if (!is_reserved (next_cand -> token_sym)) {
						next_cand -> next = CANDIDATES[x];
						CANDIDATES[x] = next_cand;
						n_CANDIDATES[x]++;
					}
					next_cand = tmp_cand;
				}
			}

			/* Prefer insertions closest to error token. */

			if (CANDIDATES[x] != NULL) {
				/* bk := min/{t(3) : t in y}; */
				next_cand = y;
				bk = next_cand -> backup_toks;
				next_cand = next_cand -> next;
				while (next_cand != NULL) {
					bk = MIN (bk, next_cand -> backup_toks);
					next_cand = next_cand -> next;
				}
				/* y := {[-,backup_toks,-] in y | backup_toks = bk) }	   
				 *
				 * This is achieved by looping over the list headed by y   
				 * and deleting those elements which satisfy the condition
				 * While doing this, check if there are any elements  that 
				 * satisfy the condition		    
				 *		(token_sym in ALWAYS_PREFERRED_SYMS) 
				 * If there are any they can be used to further prune the  
				 * list. A flag 'exists' will be used for this purpose.
				 */

				n_CANDIDATES[x] = 0;
				next_cand = CANDIDATES[x];
				CANDIDATES[x] = NULL;
				exists = FALSE;
				/* Assume none in ALWAYS_PREFERRED_SYMS */
				while (next_cand != NULL) {
					/* there are more candidates */
					tmp_cand = next_cand -> next;
					if (next_cand -> backup_toks == bk) {
						exists = exists
						  || in_ALWAYS_PREFERRED_SYMS (next_cand -> token_sym);
						next_cand -> next = CANDIDATES[x];
						CANDIDATES[x] = next_cand;
						n_CANDIDATES[x]++;
					}
					next_cand = tmp_cand;
				}
			}

			/* 	Apply preferred insertions (if any exist)
	    	 *
	    	 *	pi := {[u, v, w] in y | u in ALWAYS_PREFERRED_SYMS};
	    	 *	if (pi != {}) y = pi;
	    	 */

			if (exists) {		/* then prune the list accordingly */
				/* y := {[token_sym,-,-] in y | token_sym in		      
				 *	    ALWAYS_PREFERRED_SYMS }			   
				 * This is achieved by looping over the list headed by y    
				 * and deleting those elements which satisfy the condition  
				 */

				n_CANDIDATES[x] = 0;
				next_cand = CANDIDATES[x];
				CANDIDATES[x] = NULL;
				while (next_cand != NULL) {
					/* there are more candidates */
					tmp_cand = next_cand -> next;
					if (in_ALWAYS_PREFERRED_SYMS (next_cand -> token_sym)) {
						next_cand -> next = CANDIDATES[x];
						CANDIDATES[x] = next_cand;
						n_CANDIDATES[x]++;
					}
					next_cand = tmp_cand;
				}
			}
			break;

		case SUBST:

			/* 		Apply preferred substitutions 
	    	 * 
	    	 *	Check to see whether there are any elements which satisfy   
	    	 *	either of the conditions	    
	    	 *			token_sym in PREFERRED_FOR_SYMS{v}
	    	 *		   or	token_sym = ID_SYM and is_reserved(v) 
	    	 *	If at least one is found then set y to be ps, where ps is   
	    	 *
	    	 *	    ps := {[u, v, w] in y | u in PREFERRED_FOR_SYMS{v}	
	    	 *				or (u = ID_SYM and is_reserved(v))};	    
	    	 *
	    	 *	This is achieved by looping over the list headed by y	
	    	 *	and deleting those elements which satisfy the condition
	    	 */

			/* check for existence */

			next_cand = CANDIDATES[x];
			exists = FALSE; /* Assume none */
			while ((next_cand != NULL) && (!exists)) {
				/* there are more candidates */
				exists = exists
				  || in_PREFERRED_FOR_SYMS( next_cand -> t3,
				   next_cand -> token_sym)
				  || ((next_cand -> token_sym == ID_SYM)
				  && (is_reserved (next_cand -> t3)));
				next_cand = next_cand -> next;
			}

			/* If some exist then y is set to be those only */

			if (exists) {
				n_CANDIDATES[x] = 0;
				next_cand = CANDIDATES[x];
				CANDIDATES[x] = NULL;
				while (next_cand != NULL) {
					/* there are more candidates */
					temp_cand = next_cand -> next;
					if ( in_PREFERRED_FOR_SYMS( next_cand -> t3,
					  next_cand -> token_sym )
					  || ((next_cand -> token_sym == ID_SYM)
					  && is_reserved (next_cand -> t3)))
					{
						next_cand -> next = CANDIDATES[x];
						CANDIDATES[x] = next_cand;
						n_CANDIDATES[x]++;
					}
					next_cand = temp_cand;
				}
			}
			else if (!threshold) {		/* None exist */
				/* Remove all substitutions involving reserved words if below	
				 * the threshold.						
				 */
				/* y -:= {[u, v, w] in y |	
		   	 	 *			 is_reserved(u) or is_reserved(v)};  
		    	 */

				n_CANDIDATES[x] = 0;
				next_cand = CANDIDATES[x];
				CANDIDATES[x] = NULL;
				while (next_cand != NULL) {
					temp_cand = next_cand -> next;
					if (!((is_reserved (next_cand -> t3))
					  || (is_reserved (next_cand -> token_sym))) )
					{
						next_cand -> next = CANDIDATES[x];
						CANDIDATES[x] = next_cand;
						n_CANDIDATES[x]++;
					}
					next_cand = temp_cand;
				}
			}

			/* Prefer substitutions closest to error token. */

			if (CANDIDATES[x] != NULL) {
				/* bk := min/{t(3) : t in y}; */
				next_cand = y;
				bk = next_cand -> backup_toks;
				next_cand = next_cand -> next;
				while (next_cand != NULL) {
					bk = MIN (bk, next_cand -> backup_toks);
					next_cand = next_cand -> next;
				}

				n_CANDIDATES[x] = 0;
				next_cand = CANDIDATES[x];
				CANDIDATES[x] = NULL;
				while (next_cand != NULL) {
					/* there are more candidates */
					temp_cand = next_cand -> next;
					if (next_cand -> backup_toks == bk) {
						next_cand -> next = CANDIDATES[x];
						CANDIDATES[x] = next_cand;
						n_CANDIDATES[x]++;
					}
					next_cand = temp_cand;
				}
			}
			break;

		case SPELL_SUBST:

			/* Prefer closest to error token. */

			/* bk := min/{t(3) : t in y}; */

			next_cand = y;
			bk = next_cand -> backup_toks;
			next_cand = next_cand -> next;
			while (next_cand != NULL) {
				bk = MIN (bk, next_cand -> backup_toks);
				next_cand = next_cand -> next;
			}

			/* 		y := {[-,-,t3] in y | t3=bk }			
	    	 * This is achieved by looping over the list headed by y   
	    	 * and deleting those elements which satisfy the condition 
	    	 */

			if (CANDIDATES[x] != NULL) {
				n_CANDIDATES[x] = 0;
				next_cand = CANDIDATES[x];
				CANDIDATES[x] = NULL;
				while (next_cand != NULL) {
					/* there are more candidates */
					temp_cand = next_cand -> next;
					if (next_cand -> backup_toks == bk) {
						next_cand -> next = CANDIDATES[x];
						CANDIDATES[x] = next_cand;
						n_CANDIDATES[x]--;
					}
					next_cand = temp_cand;
				}
			}
			break;

		case MERGE:

			break;

		}			/* switch */

	}				/* for */
#ifdef DEBUG
	if (trcopt) {
		fprintf(errfile,"Candidates AFTER pruning:\n");
		dump_cand();
	}
#endif


	/* For each mode - merge, spelling, insertion, substitution, deletion -
	 * there are zero or more correction candidates.  
	 * If one or mode has exactly one correction candidate, then one of those
	 * candidates is chosen.
	 * 
	 * If no mode has a single candidate, then a simple correction candidate 
	 * is only chosen if the long check distance has been achieved 
	 *		    (MAX_CHECK >= MIN_LEN + 3).
	 * 
	 * The preference order among the correction modes is : merge, spelling,
	 * insertion, deletion, substitution.
	 */

	/* Calculate the number of single_cand_modes	 */
	/* and the total number of CANDIDATES		 */

	n_single_cand_modes = 0;
	total_CANDIDATES = 0;

	for (cc = DELETE; cc <= SPELL_SUBST; cc++) {
		if (n_CANDIDATES[cc] == 1)
			n_single_cand_modes++;
		total_CANDIDATES += n_CANDIDATES[cc];
	}

	if (n_single_cand_modes > 0) {
		/* Apply one final preference rule where there remains a single 
    	 *	deletion and a single insertion candidate - prefer deletion of 
    	 *	operator or punctuation symbol to insertion of such a symbol.  
    	 */
		if ((n_CANDIDATES[DELETE] == 1)
		  && ((n_CANDIDATES[INSERT]) == 1)
		  && is_operator (CANDIDATES[DELETE] -> token_sym)
		  && is_operator (CANDIDATES[INSERT] -> token_sym))
		{
			/* Set CANDIDATES[INSERT] to NULL and dispose of the list */
			CANDIDATES[INSERT] = NULL;
			n_CANDIDATES[INSERT] = 0;
			n_single_cand_modes--;
			total_CANDIDATES--;
		}

		/* Set all CANDIDATES which have more than 1 element to NULL	
    	 * and dispose of their lists						
    	 */

		for (cc = DELETE; cc <= SPELL_SUBST; cc++)
			if (n_CANDIDATES[cc] > 1) {
				CANDIDATES[cc] = NULL;
				n_CANDIDATES[cc] = 0;
			}

	}				/* if */

	if ((n_single_cand_modes > 0) || ((total_CANDIDATES > 0) && threshold)) {
		make_correction (STATE_STACK);
		return;
	}

	/*  Primary recovery has failed if we reach this point. 
	 *  Reset parse configuration for scope recovery.	
	 */

	copystack (STATE_STACK, &sta_stack, &n_STATE_STACK);
	/*  TOKSYMS(n_TOKENS + 1 .. ) := []; */
	n_TOKSYMS = save_n_TOKSYMS ;
	BACKUPTOKS = 0;

	/************************************************************************
	 *								      
	 *	    E N D     O F     P R I M A R Y    R E C O V E R Y	       
	 *									
	************************************************************************/

	/************************************************************************
	 *								      
	 *					Scope recovery 
	 *									
	************************************************************************/

	/* SCOPE */
	{

		int	 j;
		struct prsstack *prstmp;
		struct two_pool *tuptmp;
		struct two_pool *statmp;
		Span_s *prev_tok_loc;
		/* struct tok_loc *prev_tok_loc = &PREVTOK->ptr.token->span; */

		if (PREVTOK != NULL)
			prev_tok_loc = &PREVTOK->ptr.token->span;

		/*	Allocate an array the size of the parse stack */
		open_seq = (int *)malloc((unsigned) (nps * sizeof(int)));

#ifdef DEBUG
		if (trcopt)
			fprintf(errfile,"SCOPE OPENERS = \n");
#endif
		for (n_open_seq = 0,j = nps, prstmp = prs_stack; prstmp != NULL;
		  prstmp = prstmp->prev, j--) {
			if (is_opener(prstmp->symbol)) {
				open_seq[n_open_seq++] = j;
#ifdef DEBUG
				if (trcopt)
					fprintf(errfile,"[ %s %d ] ",TOKSTR(prstmp->symbol),j);
#endif
			}
		}
#ifdef DEBUG
		if (trcopt)
			fprintf(errfile,"\n");
#endif

		/* for debugging purposes try one less trial */
		trials-- ;


		closer_toksyms = NULL;
		closer_bottom = NULL;

		for (trial = 1 ; trial <= trials ; trial ++ ) {
#ifdef DEBUG
			if (trcopt)
				fprintf(errfile,"Scope Recovery Trial = %d\n",trial);
#endif
			if (scope_recovery(n_STATE_STACK,0,open_seq)) {
				for (tuptmp = closer_toksyms; tuptmp != NULL;
				  tuptmp = tuptmp->link)
				{
					prstmp = PRSALLOC();
					prstmp->ptr.token = TOKALLOC();
					prstmp->symbol =prstmp->ptr.token->index =tuptmp->val.state;
					prstmp->ptr.token->span.line = prev_tok_loc->line;
					prstmp->ptr.token->span.col = prev_tok_loc->col;
					add_to_top(prstmp);
				}
				/* if (closer_toksyms != NULL)
				 * TFREE(closer_toksyms,closer_bottom);
				 */
				n_closer_toksyms = 0 ;
				return;
			}
			/* if (closer_toksyms != NULL)
			 *    TFREE(closer_toksyms,closer_bottom);
			 */
			n_closer_toksyms = 0 ;
			/*	Back up for the next trial */

			if (trial == trials)
				break;

			statmp = sta_stack;
			sta_stack = sta_stack->link;
			TFREE(statmp,statmp);
			n_STATE_STACK -- ;

			prstmp = prs_stack;
			prs_stack = prs_stack->prev;
			nps-- ;

			add_to_top(prstmp);

			TOKSYMS[++n_TOKSYMS] = prstmp->symbol;

			BACKUPTOKS++;

			prev_tok_loc = RLOC(prs_stack);
		}

		/*	To get here scope recovery has failed, try other recoveries */

		/*  First restore the parse configuration for secondary recovery */
		copystack(STATE_STACK,&sta_stack,&n_sta_stack) ;

		for (trial = 1 ; trial < trials ; trial ++) {
			struct prsstack *tmp_ps ;

			tmp_ps = tokens[tokind];
			n_TOKSYMS -- ;
			TOKMINUS ;
			tmp_ps->prev = prs_stack ;
			prs_stack = tmp_ps ;
			nps ++ ;
		}

		PREVTOK = oldprevtok ;
		BACKUPTOKS = 0 ;
	}

	/************************************************************************
	 *								      
	 *					Secondary recovery 
	 *									
	 ************************************************************************/
	/*SEC*/

	/* Now try secondary recoveries.	
	 * First try deleting the error token and some sequence of tokens in the 
	 * forward context - stop at a beacon symbol.	
	 */
	{
#define sec_check	MIN_LEN

		char    tmp_str[500],
		err_msgs[500];
		int	    equal;
		int	    nst;
		int	    n_stack_del_syms;
		int	    t, kk, j, k;
		int	   *stack_delete_syms;
		Span_s  leftt,
		rightt;

		err_msgs[0] = '\0' ; /* initialize to null string */

		for (k = 1; k <= MAX_LOOK_AHEAD - (MIN_LEN + 3); k++) {

			t = TOKSYMS[n_TOKSYMS--];
#ifdef DEBUG
			if (trcopt)
				fprintf (errfile, "take token off TOKSYMS (%s)\n", TOKSTR (t));
#endif

			if((kk=prs_check(sta_stack, TOKSYMS, n_TOKSYMS)) >= (MIN_LEN + 3)) {
				/* changed +2 to +3, gcs */
				/* delete k tokens */

				/*	rightt := TOKENS(n_TOKENS - k + 1);
				 *  TOKENS(n_TOKENS - k + 1 ..) := [];
				 */
				for (i = 1; i < k; i++)
					TOKMINUS;

				rightt = r_span (tokens[tokind]);
				TOKMINUS;

				syntax_err (LLOC (ERROR_TOKEN), &rightt, "Unexpected input");

				return;
			}

			/* For now, ignore to conform with SETL (BEACON_SYMS is empty) 
			 *	if (in_BEACON_SYMS (t))
	 		 *   break;
			 */
		}

		/* Try to resume the parse - perhaps with the inclusion of a sequence of
		 * scope closers-  from some state on the state stack.	
		 * After each attempt the current token is deleted.
		 * To succeed on arbitrary input, some state must accept EOFT.
		 */

#ifdef DEBUG
		if (trcopt)
			fprintf(errfile,"********** SECONDARY RECOVERY **********\n");
#endif

		nst = stack_size (sta_stack);

		while (1) {
			struct two_pool *sta_stack_copy;

			get_next(sec_check + 2);	 /* ensure that there are ample */

			/*	TOKSYMS := [t(1) : t in TOKENS]; */

			i = 0;
			j = tokbottom;

			for (;;) {
				TOKSYMS[i] = tokens[j] -> symbol;
				if (j == tokind)
					break;
				j = (j + 1) % toksiz;
				i++;
			}

			n_TOKSYMS = (toksiz + tokind - tokbottom) % toksiz;

			curtok = tokens[tokind];

#ifdef DEBUG
			if (trcopt) {
				fprintf(errfile,"TRYING: %s\n",TOKSTR(TOKSYMS[n_TOKSYMS]) );
				fprintf(errfile,
				  "\ttoksize = %d  tokbottom = %d  tokind = %d  curtok = %s\n",
				  toksiz,tokbottom,tokind,find_name(curtok) );
			}
#endif

			copystack (sta_stack, &sta_stack_copy, &nst);

			for (k = nst; k >= 1; k--) {

				/* Try peeling stacks. */

				/* Strip n_sta_stack - k - 1 elements off the state stack */

				kk = stack_size (sta_stack_copy) - k;

				/* while (--kk > 0)
				 *  sta_stack_copy = sta_stack_copy -> link;
				 */

				if ( (kk=prs_check (sta_stack_copy, TOKSYMS, n_TOKSYMS)) >=
				  (sec_check + 2)) { /* (sec_check + 1)) */
					/* Form the error message and quit the outer loop */
					sprintf (err_msgs, "%s", err_message (k,curtok));
#ifdef DEBUG
					if (trcopt)
						fprintf(errfile,"prs_check succeeded for k = %d\n",k);
#endif
					goto quit_loop_do;
				}

				/* Try closer recovery. */

				/* Make a copy of the state stack for later restoration */

				if (scope_recovery (k, 0, open_seq)) {
					/* Form the error message and quit the outer loop */
					sprintf (tmp_str, "%s", err_msgs);
					sprintf (err_msgs, "%s -- %s", err_message(k,curtok),
					  tmp_str);
#ifdef DEBUG
					if (trcopt)
						fprintf(errfile,
						  "scope_recovery succeeded for k = %d\n",k);
#endif

					goto quit_loop_do;
				}
				/* pop element of the state stack  */
				sta_stack_copy = sta_stack_copy -> link;

				closer_toksyms = NULL;
			}

			/* Get next token */

#ifdef IGNORE
			PREVTOK = tokens[tokind];
			/* This is a fix proposed by Sam Chin for cases when the entire
			 * text is garbage. If there are tokens on the list of lookahead
			 * tokens then take the token, otherwise, if not then take it from
			 * the input stream. If while deleting the tokens an end of file
			 * is reached, output the appropriate message and quit the
			 * secondary recovery
			 */
			curtok = NEXTTOK ;
#ifdef DEBUG
			if (trcopt)
				fprintf(errfile,"curtok = %s\n",find_name(curtok));
#endif
			if (curtok->symbol == EOFT_SYM) {
				sprintf(err_msgs,"End-of-file reached while trying to recover");
				goto quit_loop_do ;
			}

			if (tokind >= MAX_LOOK_AHEAD) {
				curtok = copytoken(tokens[tokind]) ;
#ifdef DEBUG
				if (trcopt)
					fprintf(errfile,"curtok updated to  %s\n",
					  find_name(curtok));
#endif
			}
#endif

			/* implement next_token macro (correctly), as done in SETL */
			PREVTOK = curtok;
			TOKMINUS;
			if ((toksiz + tokind - tokbottom + 1) % toksiz == 0)
				tokens[tokbottom=(toksiz+tokbottom-1)%toksiz] = gettok();

			/* NEXTTOK; */

			/* copytoken (curtok, tokens[tokind]); */

		}

quit_loop_do: 
		;			/* LABEL for goto */


		/* At this point we have recovered.	
		 * Locate the range of the error.	
		 */


		n_stack_del_syms = 0;
		if (nst > k	 &&  k > 0  &&	prs_stack != NULL) {
			/* check for empty parse stack and k not zero (i.e. end of file) */

			/* stack_delete_syms :=
				[PRS_STACK(t)(1) : t in [nps, nps - 1 .. k + 1]]; */

			/* nps = stack_count (prs_stack); */
			tmp_ps = prs_stack;
			stack_delete_syms =
			  (int *) malloc ((unsigned) ((nst - k ) * sizeof (int)));
			/* stack_delete_syms = (int *) malloc ((k + 1) * sizeof (int)); */
			for (t = nst; t >= k + 1; t--) {
				stack_delete_syms[n_stack_del_syms++] = tmp_ps -> symbol;
				tmp_ps = tmp_ps -> prev;
			}

			leftt = l_span (tmp_ps);

			/* 		PRS_STACK(k + 1 .. ) := [];
    		 *				STA_STACK(k + 1 .. ) := [];	
    		 */

			kk = stack_size (sta_stack) - k;
			while ( kk-- > 0) {
				sta_stack = sta_stack -> link;
				prs_stack = prs_stack -> prev;
			}
		}
		else
			leftt = l_span (ERROR_TOKEN);


		/* Form error location. */

		/*
		 *	Check whether 
		 *		stack_delete_syms = 
		 *			TOKSYMS(#TOKSYMS - #stack_del_syms + 1 ..  #stack_del_syms)
		 *
		 *	Assume equal and check element by element
		 */

		equal = 1;
		for (j = n_stack_del_syms - 1 , k = n_TOKSYMS ;
		  ((j >= 0) && (equal)) ; k--, j--)
			equal = equal && (stack_delete_syms[j] == TOKSYMS[k]);

		if ((n_stack_del_syms != 0) && (n_stack_del_syms <= n_TOKSYMS) && equal)
		{
			/* PRSERR_LOC = loc_range(LLOC(ERROR_TOKEN), LLOC(TOKENS[(tokind -
       		 * n_stack_del_syms + 1) % toksiz] ), RLOC(ERROR_TOKEN));
			 * for now just print the spans
			 */
			syntax_err (LLOC (ERROR_TOKEN), RLOC (ERROR_TOKEN), err_msgs);
		}
		else {
			/* PRSERR_LOC = 
     		 *  loc_range(LLOC(leftt), LLOC(PREVTOK), RLOC(ERROR_TOKEN));
     		 *  for now just print the spans
			 */
			syntax_err (&leftt, RLOC (ERROR_TOKEN), err_msgs);
		}

		/* If the secondary recovery involves a scope recovery, insert the
		 * closer tokens.	
		 */

		if (closer_toksyms != NULL) {
			/* TOKENS +:= [[t, t, top(PREVTOK)] : t in CLOSER_TOKSYMS]; */
			for(tmp_tp =closer_toksyms; tmp_tp != NULL; tmp_tp = tmp_tp -> link)
			{
				add_to_top (PRSALLOC());
				tokens[tokind] -> symbol = tmp_tp -> val.state;
				tokens[tokind] -> ptr.token = TOKALLOC ();
				tokens[tokind] -> ptr.token -> index = tmp_tp -> val.state;
				tokens[tokind] -> ptr.token -> span = PREVTOK -> ptr.token ->span;
			}
		}

		return;
	}
}				/* End of Procedure prserr */

static void get_poss_tok()					/*;get_poss_tok*/
{
	struct two_pool *temp_sta_stack; /* Points to saved copy of state stack	*/
	struct two_pool *act_sta = NULL ; /* Stored list of acceptable actions	*/
	int	ss = sta_stack->val.state ;	/* The top of the state stack			*/
	struct two_pool *tmp_tp ;			/* utility variables			*/
	struct two_pool *tmp ;
	short	red,dr ;
	int	n ,n_temp_sta_stack ;

	/* Get the tokens that are acceptable to the top state on the stack.  */

	copystack(sta_stack,&temp_sta_stack,&n_temp_sta_stack);

	while ((dr = def_action[ss - 1]) != 0) {
		tmp = TALLOC() ;		/* act_sta with := ss	*/
		tmp->val.state = ss ;
		tmp->link = act_sta ;
		act_sta = tmp ;

		red = dr - NUM_STATES - 1 ;

		/*	Strip "rhslen[red]" elements from the temp_sta_stack */
		n = rhslen[red] ;
		if(!n) {
			tmp = TALLOC() ;
			tmp->link = temp_sta_stack ;
			temp_sta_stack = tmp ;
		}
		else if( n > 1 ) {
			while( --n > 1 )
				temp_sta_stack = temp_sta_stack->link ;
			tmp = temp_sta_stack ;
			temp_sta_stack = temp_sta_stack->link ;
		}
		else if (n < 0)
			break ;
		temp_sta_stack->val.state =	
		  action((int)(temp_sta_stack->link->val.state),lhs[red]);
		ss = temp_sta_stack->val.state ;
	}

	tmp = TALLOC() ;
	tmp->val.state = ss ;
	tmp->link = act_sta ;
	act_sta = tmp ;


	/* 
	 * POSS_TOK := +/{ACTION_TOKENS(s) : s in act_sta};				
	 * Since ACTION_TOKENS(s) is a set of numbers, for each s we must
	 * loop over the set, adding the values to the list POSS_TOK
	 */
	POSS_TOK = NULL ;
	while (act_sta != NULL) {
		int a ;

		for(a = ACTION_TOKENS_INDEX[(int)(act_sta->val.state) - 1] ;
		  a <= (ACTION_TOKENS_INDEX[(int)(act_sta->val.state)] - 1) ; a ++ )
		{
			/* Add ACTION_TOKENS(a) to the list */
			tmp_tp = TALLOC() ;
			tmp_tp->link = POSS_TOK ;
			tmp_tp->val.state = ACTION_TOKENS[a] ;
			POSS_TOK = tmp_tp ;
		}
		act_sta = act_sta->link ;
	}
}

static void get_next(int k)				/*;get_next*/
{
	/* This procedure ensures that tokens contains at least k tokens.  
	 * Note that tokind always points to the next token, so that the
	 * array must be read in in reverse order
	 */

	int i;

	/* First check if this is the first time, and if so allocate space for
	 * tokens.
	 */

	if (tokind == -1) {
		tokens =
		  (struct prsstack **)malloc((unsigned)(2*k*sizeof(struct prsstack *)));
		toksiz = 2 * k;
	}

	/* for now only put in k-1 tokens, since the current token has to be
	 * inserted.
	 */
	for (i = k - ((toksiz + (tokind - tokbottom + 1)) % toksiz); i>0 ; i--) {
		tokbottom = (toksiz + tokbottom - 1) % toksiz;
		tokens[tokbottom] = gettok();
	}
	if (tokind == -1)
		tokind = toksiz - 1;
}

add_to_top(struct prsstack *tok)						/* ;add_to_top */
{
	/* this procedure replaces the old ADDTOTOP macro, which assumed there
	 * was room in tokens and did not check for a full queue before adding
	 * a new token
	 * We now check at each insertion, and expand the queue as necessary
	 */
  short siz;

	siz = (tokind - tokbottom + 1 ) % toksiz;
	if (siz == toksiz - 1) 	/* queue is full */
	{						/* reallocate and enlarge ! */
		toksiz = toksiz + 50;
		tokens = (struct prsstack **) erealloc(tokens, (unsigned) (toksiz * 
						sizeof(struct prsstack *)));
	}
	tokens[tokind = (tokind +1) % toksiz] = tok;
}
