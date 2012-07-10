/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "hdr.h"
#include "ada.h"
#include "miscprots.h"
#include "prsutilprots.h"
#include "followprots.h"
#include "actionprots.h"
#include "lookupprots.h"
#include "pspansprots.h"
#include "adalexprots.h"
#include "errsprots.h"
#include "recoverprots.h"

/*	Variables needed for scope and secondary recoveries */

extern int *open_seq;
/* struct two_pool *closer_toksyms;
 struct two_pool *closer_bottom; */
extern int n_open_seq;
extern int n_closer_toksyms;
extern int nps;

extern struct two_pool *closer_toksyms;
extern char *CLOSER_MESSAGE_SYMS();
extern char closer_candidates[13][3][5];

#define EQ(s, t) (strcmp(s, t) == 0)

char *err_message(int k, struct prsstack *curtok)		/*;err_message*/
{
	/*	Form error message for secondary recovery
	 *  The parameter 'k' indicates the point in the parse and state stacks
	 *  at which the recovery is being made
	 */

	char *e_m_s,
	*err_mess;
	/* k is index into state stack (not parse stack because it is off by 1) */
	int pp = stack_size(sta_stack) - k;
	struct prsstack *prs_stack_k = prs_stack;

	if (k == 1)
		/* this is case where there is 1 element on the state stack and 
     	 * the parse stack is empty (i.e. all input is rejected)
     	 */
		return ("Unexpected input");

	while (--pp >= 0)
		prs_stack_k = prs_stack_k-> prev;

	if (EQ((err_mess = err_msg_syms(prs_stack_k->symbol)) , "")) {
		int act;
		struct two_pool *sta_stack_k = sta_stack;
		int kk = stack_size(sta_stack) - k;

		while (--kk >= 0)
			sta_stack_k = sta_stack_k -> link;

		act = action((int)(sta_stack_k->val.state), curtok->symbol);

		if (act > NUM_STATES) {
			e_m_s = err_msg_syms(lhs[act - NUM_STATES - 1]);
			return(EQ(e_m_s , "") ? "Unexpected input" : e_m_s);
		}
		else
			return ("Unexpected input");

	}
	else
		return (err_mess);
}


int prs_block(struct two_pool *states, struct two_pool *toks)	/*;prs_block*/
{
	/* This parse checker returns true if the parse blocks and false  if
	 * it  does  not  or  if it cannot be determined that it will block.
	 * The sequence of states need not be complete, so  it	is  possible
	 * for	a  reduction  to use up all the states.	 This makes the goto
	 * undetermined.  In such a case the FOLLOW set for  the  left	hand
	 * side	 is  used.  If the next token is not in the follow set, then
	 * surely the parse must block eventually, but if it is not, we have
	 * to conclude that not blocking is possible.  The value returned is
	 * the predicate 'the parse must block if the state  stack  contains
	 * states as a suffix and the token sequence contains toks as a pre-
	 * fix'.
	 */
	int act, red, nolh, n;
	int ts;
	struct two_pool *top_tp;
	struct two_pool *tmp_tp;
	int	cs;
	short	n_states = 1;

	ts = toks->val.state;		/* ts frome toks */
	toks = toks->link;

	cs = states->val.state;	/* cs = top(states) */

	while(1) {	/* while true */

		act = action(cs, ts);

		if (act == 0)
			return 1;						    /* parse error */
		else if (act < NUM_STATES) {		/* shift action */
			if (toks == (struct two_pool *)0)
				return 0;

			/* tmp_tp = toks; destroys prs_toks!! */	/* for re-use */
			ts = toks->val.state;		/* next token */
			toks = toks->link;

			tmp_tp = TALLOC();
			tmp_tp->link = states;
			tmp_tp->val.state = (cs = act);	/* update stateseq */
			states = tmp_tp;
			n_states ++;
		}
		else if ((red = (act - NUM_STATES )) == 0)	/* accept action */
			return 0;
		else {	/* reduce action */
			int nn;
			red --;		/* Adjust for 0 offset arrays */
			nolh = lhs[red];
			n = n_states - rhslen[red] + 1;
			nn = rhslen[red];
			if (n <= 1)
				return (is_terminal(ts) && !in_FOLLOW(nolh, ts) );
			/* replace rhs states with lhs	
			 * states[n] = (cs = action(states(n - 1), nolh));	
			 */

			if (nn == 0) {
				tmp_tp = TALLOC();
				tmp_tp->link = states;
				states = tmp_tp;
			}
			else if (nn > 1 ) {
				top_tp = states;
				while (--nn > 1)
					states = states->link;
				tmp_tp = states;
				states = states->link;
				TFREE(top_tp, tmp_tp);
			}
			states->val.state = 
			  (cs = action((int)(states->link->val.state), nolh));
			/* n_states -= nn; */
			n_states -= rhslen[red] - 1;
		}
	}
}

int prs_check(struct two_pool *stateseq, int *tokseq, int n_tokseq)
															/*;prs_check*/
{
	int ts;
	int cs;
	struct two_pool *top_tp;
	struct two_pool *tmp_tp;
	struct two_pool *temp_stateseq;
	int n_temp_stateseq;
	int nsh;
	int red, act;

	/* This is just a parser that operates from the token sequence, tokseq.
	 * It returns when an error occurrs, an accept occurs, or the sequence
	 * of tokens is exhausted.
	 */

	/* n_tokseq is actually the size of tokseq - 1. It is used as an offset 
	 * into tokseq (which starts at zero). However, when the size of tokseq
	 * is desired, we use (n_tokseq + 1) 
	 */

	copystack(stateseq, &temp_stateseq, &n_temp_stateseq);

	nsh = 0;				/* Number of tokens shifted */

	ts = tokseq[n_tokseq];			/* Top of tokseq	*/
	cs = temp_stateseq->val.state;		/* Top of stateseq	*/

	while(1)	/* while true */
	{
		act = action(cs, ts);

		if (act == 0)
			return nsh;			/* parse error */
		else if (act < NUM_STATES)	/* Shift action */
		{
			if ( (++nsh ) >= (n_tokseq + 1))	/*  up shift count */
				return nsh;	/*  gone far enough */

			ts = tokseq[n_tokseq - nsh];	/* next token */

			tmp_tp = TALLOC();	/* Update stateseq */
			tmp_tp->val.state = ( cs = act);
			tmp_tp->link = temp_stateseq;
			temp_stateseq = tmp_tp;
		}
		else if ((red = (act - NUM_STATES )) == 0  ) /* accept action */
			return	((ts == EOFT_SYM) ? (n_tokseq + 1) : nsh);
		else {					/* reduce action */
			int nn;
			red --;		/* adjust for 0 offset arrays */
			nn = rhslen[red];

			/* 	replace rhs states with lhs
			 *
			 *	stateseq(nn..) := [cs := ACTION(stateseq(nn-1), nolh)];		
			 *
			 *  Since the top element will be replaced, we strip off nn - 1
			 *  elements and then replace the top one.
			 *  There are 3 cases : 
			 *	nn == 0 :	allocate a new top element
			 *			for the state stack
			 *	nn == 1 :	Leave the top element for
			 *			replacement
			 *	nn >  1 :	Strip nn - 1 off the stack.
			 *			leaving the top element for
			 *			replacement
			 */

			if ( nn == 0 ) {
				tmp_tp = TALLOC();
				tmp_tp->link = temp_stateseq;
				temp_stateseq =	 tmp_tp;
			}
			else if (nn > 1) {
				top_tp = temp_stateseq;
				while (--nn > 1)
					temp_stateseq = temp_stateseq->link;
				tmp_tp = temp_stateseq;
				temp_stateseq = temp_stateseq->link;
				TFREE(top_tp, tmp_tp);
			}

			/* Replace the top element with the GOTO	*/

			temp_stateseq->val.state = 
			  (cs = action((int)(temp_stateseq->link->val.state), lhs[red]));
		}
	}
}

int scope_recovery(int k, int index, int *open_seq)		/*;scope_recovery*/
{
	int exists = 0;
	int open_loc;
	struct prsstack *prstmp;
	int opener;
	struct two_pool *tmp_tp, *saved_tail, *closer_head, *closer_tail;
	struct two_pool *STA_STACK;
	int closer;
	int i, closer_index;
	int kk = k;
	int ind;
	int *tmp_toksyms;
	int n_tmp_toksyms;
	int prs_distance;
	int check_dist;
	int n_closer;

	/* The parameter 'k' indicates the portion of the state stack with
	 * which the parse check is to be performed. The parameter 
	 * 'index' indicates the portion of the parse stack to be used when
	 * looking for the next opener to be closed.
	 */

	/*
     * if not exists ind in [index .. n_open_seq] 
     *			    | k >= open_seq(ind) then
     *					    return false;
     * end if;
     *
     *	    Assume that no such ind exists. Loop through, looking for
     *	    one.
     */
#ifdef EDEBUG
	if (trcopt)
		fprintf(errfile, "AT PROC: scope_recovery(%d, %d, %d)\n", k, index,
		  *open_seq);
#endif

	for ( ind = index; ind < n_open_seq; ind++ )
		if ( k - 1 >= open_seq[ind]) {
			/* adjust to k-1 because in C version (only), size of
			 * parse stack is 1 less than size of state stack
			 */
			exists = 1;
			break;
		}

	if (!exists)
		return 0;

	open_loc = nps - open_seq[ind];


	for (prstmp = prs_stack; open_loc--; prstmp = prstmp->prev);
	opener = prstmp->symbol;
	/* Keep prstmp for the error message */


	/* Map opener into an array index */
	opener = open_index(opener);
	/*
     *	closer_candidates := 
     *			{ CLOSER_SYMS(j) :
     *					j in CLOSER_MAP_SYMS(opener)};
	 */

	/*	(for closer in closer_candidates) */

	for (closer = 0	; closer_candidates[opener][closer][0] != 0; closer++ )
	{
#ifdef EDEBUG
		if (trcopt)
			fprintf(errfile, "opener %d  closer %d  cand: %c\n", opener, closer,
			  closer_candidates[opener][closer][0]);
#endif
		/*	
		 *   closer_toksyms := closer + closer_toksyms; 
		 *
		 *	These are then appended onto the end of TOKSYMS.
		 *	This will be represented as a linked list of values.
		 */

		/* First set up the list for closer */
		closer_head = closer_tail = TALLOC();
		closer_head->link = (struct two_pool *)0;
		closer_head->val.state = closer_candidates[opener][closer][0];
		for(i = 1, n_closer = 1; 
		  ((closer_candidates[opener][closer][i] != 0) && (i <= 4)); 
		  n_closer++, i ++ ) {
			tmp_tp = TALLOC();
			tmp_tp->link = (struct two_pool *)0;
			tmp_tp->val.state = closer_candidates[opener][closer][i];
			closer_tail->link = tmp_tp;
			closer_tail = tmp_tp;
		}

		saved_tail = closer_tail;
		closer_tail->link = closer_toksyms;
		closer_toksyms = closer_head;
		n_closer_toksyms += n_closer;

		/*	Set tmp_toksyms = TOKSYMS + closer_toksyms */

		tmp_toksyms = (int *)emalloc((1 + n_TOKSYMS + n_closer_toksyms)
		    * sizeof(int) );
		for (i = 0; i <= n_TOKSYMS; i++)
			tmp_toksyms[i] = TOKSYMS[i];
		n_tmp_toksyms = n_TOKSYMS;
		for (tmp_tp = closer_toksyms; tmp_tp != (struct two_pool *)0;
		  tmp_tp=tmp_tp->link )
			tmp_toksyms[++n_tmp_toksyms] = tmp_tp->val.state;



		/* Take the top n_sta_stack - k elements off the state stack, 
		 * keeping them so as to be able to restore the stack after the call.
		 */

		STA_STACK = sta_stack;

		kk = (n_sta_stack = stack_size(STA_STACK)) - k;
		while(--kk > 0)
			STA_STACK = STA_STACK->link;

		/* prs_distance = 
		 *	prs_check(STA_STACK(1 .. k), TOKSYMS + closer_toksyms);
		 */

		prs_distance = prs_check(STA_STACK, tmp_toksyms, n_tmp_toksyms);

		check_dist = n_closer_toksyms;

		if ((prs_distance >= (check_dist + MIN_LEN + 1 + BACKUPTOKS))
		  || ((prs_distance >= check_dist)
		  && (scope_recovery(k, ind + 1, open_seq))) ) {
			Span_s location;
			char	msg[200];

			/* opl := PRS_STACK(open_loc);
	    	 * opl := l_span(opl);
	    	 * opl := top(opl);
			 */
#ifdef DEBUG
			if (trcopt)
				fprintf(errfile, "Successful scope recovery\n");
#endif
			location = l_span(prstmp);
			/* CLOSER_MESSAGE_SYMS is indexed by the sum of the values in
			 * each closer, where closer is an element of 
			 * closer_candidates[opener]. 
			 * I.e.	 +/closer_candidates[opener][closer]
			 */


			for (i = 0 , closer_index = 0;
			  ((i <= 4) && (closer_candidates[opener][closer][i] != 0)); i++)
				closer_index += closer_candidates[opener][closer][i];

			/* ERR_MSGS := [ CLOSER_MESSAGE_SYMS(closer) 
			 *   + ' on line ' + str (opl(1)) ] + ERR_MSGS;
			 */
			sprintf(msg, "%s on line %d",
			  CLOSER_MESSAGE_SYMS(closer_index), location.line );
			syntax_err( LLOC(curtok), RLOC(curtok), msg);

			return 1;
		}
		else {
			/*	closer_toksyms(1 .. n_closer) := []; 
			 *
			 *	Since we saved the head and tail pointers of the list closer,
			 *  this can be done by setting closer_toksyms to point to the 
			 *  tail's link.
			 */

			closer_toksyms = saved_tail->link;
			n_closer_toksyms -= n_closer;
		}
	}

#ifdef EDEBUG
	if (trcopt)
		fprintf(errfile, "recursive call #2\n");
#endif
	return scope_recovery(k, ind + 1, open_seq);

}


int stack_size(struct two_pool *s)							/*;stack_size*/
{
	int size = 0;
	struct two_pool *tmp_tp = s;

	while (tmp_tp != (struct two_pool *)0) {
		tmp_tp = tmp_tp->link;
		size ++;
	}
	return (size);
}

int spell(char *s, char *t)										/*;spell*/
{
	/*	spell : return distance between two names	*/
	/*  See Kernighan & Pike */
	/*
	 *  very rough spelling metric :
	 *	0 if strings are identical
	 *	1 if two chars are transposed
	 *	2 if one char wrong, added or deleted
	 *	3 otherwise
	 */
	while (*s++ == *t)
		if (*t++ == '\0')
			return 0;		/* exact match */
	if (*--s)	{
		if (*t)		{
			if (s[1] && t[1] && *s == t[1]
			  && *t == s[1] && EQ(s + 2, t + 2))
				return 1;	/* transposition */
			if (EQ(s + 1, t + 1))
				return 2;	/* 1 char mismatch */
		}
		if (EQ(s + 1, t))
			return 2;  /* extra character */
	}
	if(*t && EQ(s, t + 1))
		return 2;	/* missing character */
	return 3;
}

#undef EQ

void try_deletion()											/*;try_deletion*/
{
	int	u;
	int ct;
	struct cand	*candidate;

#ifdef DEBUG
	if (trcopt)
		fprintf(errfile, "Try_deletion called\n");
#endif

	if (TOKSYMS[n_TOKSYMS] >= EOFT_SYM) /* do not delete a nonterminal */
		return;

	ct = TOKSYMS[n_TOKSYMS--];

	u = prs_check(sta_stack, TOKSYMS, n_TOKSYMS) - BACKUPTOKS;
#ifdef DEBUG
	if (trcopt)
		fprintf(errfile, "prs_check returned %d\n", u);
#endif

	if (u > MAX_CHECK ) {
		candidate = CANDALLOC();
		candidate->token_sym = ct;
		candidate->backup_toks = BACKUPTOKS;
		candidate->next = (struct cand *)0;
		MAX_CHECK = u;
		cand_clear();
		CANDIDATES[DELETE] = candidate;
		n_CANDIDATES[DELETE] = 1;
#ifdef DEBUG
		if (trcopt)
			fprintf(errfile, "[ %s %d ] ", TOKSTR(ct), u);
#endif
	}
	else if (u == MAX_CHECK ) {
		candidate = CANDALLOC();
		candidate->token_sym = ct;
		candidate->backup_toks = BACKUPTOKS;
		candidate->next = CANDIDATES[DELETE];
		CANDIDATES[DELETE] = candidate;
		n_CANDIDATES[DELETE] ++;
#ifdef DEBUG
		if (trcopt)
			fprintf(errfile, "[ %s %d ] ", TOKSTR(ct), u);
#endif
	}

#ifdef DEBUG
	if (trcopt)
		fprintf(errfile, "\n");
#endif
	TOKSYMS[++n_TOKSYMS] =	ct;

}

void try_insertion()									/*;try_insertion*/
{
	int		u;
	short	ct;
	struct cand * candidate;
	struct two_pool *tmp_tp;

#ifdef DEBUG
	if (trcopt) {
		fprintf(errfile, "Try Insertion called\n");
		fprintf(errfile, "MAX_CHECK = %d\n", MAX_CHECK);
	}
#endif
	ct = TOKSYMS[n_TOKSYMS];

	TOKSYMS[++n_TOKSYMS] = 0;


	/* (for t in POSS_TOK) */
#ifdef DEBUG
	if (trcopt)
		fprintf(errfile, "Possible inserts : ");
#endif
	tmp_tp = POSS_TOK;
	while(tmp_tp != (struct two_pool *)0) {
		TOKSYMS[n_TOKSYMS] = tmp_tp->val.state;

		u = prs_check(sta_stack, TOKSYMS, n_TOKSYMS) - (BACKUPTOKS + 2);

#ifdef DEBUG
		if (trcopt)
			fprintf(errfile, " [ %s,%d,%d ] ",
			  namelist((int)(tmp_tp->val.state)), u, BACKUPTOKS);
#endif

		if (u > MAX_CHECK) {
			MAX_CHECK = u;
			candidate = CANDALLOC();
			candidate->token_sym = tmp_tp->val.state;
			candidate->t3 = ct;
			candidate->backup_toks = BACKUPTOKS;
			candidate->next = (struct cand *)0;
			cand_clear();
			CANDIDATES[INSERT] = candidate;
			n_CANDIDATES[INSERT] = 1;
		}
		else if (u == MAX_CHECK) {
			candidate = CANDALLOC();
			candidate->token_sym = tmp_tp->val.state;
			candidate->t3 = ct;
			candidate->backup_toks = BACKUPTOKS;
			candidate->next = CANDIDATES[INSERT];
			CANDIDATES[INSERT] = candidate;
			n_CANDIDATES [INSERT] ++;
		}

		tmp_tp = tmp_tp->link;
	}
#ifdef DEBUG
	if (trcopt)
		fprintf(errfile, "\n");
#endif

	n_TOKSYMS--;
#ifdef DEBUG
	if (trcopt)
		fprintf(errfile, "At end, MAX_CHECK = %d\n", MAX_CHECK);
#endif

}

void try_merge(struct prsstack *tok1, struct prsstack *tok2)	/*;try_merge*/
{
	int	ct, nt;
	int j, u;
	int	new_tok_sym;
	char  *tok1v;
	char  *tok2v;
	char  *newtok;
	struct cand *candidate;

#ifdef DEBUG
	if (trcopt)
		fprintf(errfile, "Try_merge called\n");
#endif

	ct = TOKSYMS[n_TOKSYMS--];
	nt = TOKSYMS[n_TOKSYMS--];

	tok1v = find_name(tok1);
	tok2v = find_name(tok2);

	/* Allocate space for the newtok */
	newtok = malloc((unsigned)(strlen(tok1v) + strlen(tok2v) + 2));
	strcpy(newtok, tok1v);
	strcat(newtok, tok2v);

#ifdef DEBUG
	if (trcopt) {
		fprintf(errfile, "Trying to merge <%s> and <%s> into <%s>\n",
		  tok1v, tok2v, newtok);
		fprintf(errfile, "The new symbol %s in the symbol table\n",
		  (name_map(newtok)?"IS":"IS NOT") );
	}
#endif
	if (name_map(newtok))
		new_tok_sym = namemap(newtok, strlen(newtok));
	else
		new_tok_sym = EOFT_SYM;

	if (new_tok_sym < EOFT_SYM ) {

		TOKSYMS[++n_TOKSYMS] = new_tok_sym;

		u = prs_check(sta_stack, TOKSYMS, n_TOKSYMS) - BACKUPTOKS;
#ifdef DEBUG
		if (trcopt)
			fprintf(errfile, " PRS_CHECK returns %d\n", u);
#endif

		if (u > MAX_CHECK) {
			candidate = CANDALLOC();
			candidate->token_sym = new_tok_sym;
			candidate->backup_toks = BACKUPTOKS;
			candidate->next = (struct cand *)0;
			MAX_CHECK = u;
			cand_clear();
			CANDIDATES[MERGE] = candidate;
			n_CANDIDATES [MERGE] = 1;
		}
		else if (u == MAX_CHECK ) {
			candidate = CANDALLOC();
			candidate->token_sym = new_tok_sym;
			candidate->backup_toks = BACKUPTOKS;
			candidate->next = CANDIDATES[MERGE];
			CANDIDATES[MERGE] = candidate;
			n_CANDIDATES [MERGE] ++;
		}

		j = TOKSYMS[n_TOKSYMS--]; /* dummy j */
	}

	TOKSYMS[++n_TOKSYMS]  = nt;
	TOKSYMS[++n_TOKSYMS]  = ct;
}

void try_substitution()								/*;try_substitution*/
{
	int	u;
	short	ct;
	struct two_pool *tmp_tp;
	struct cand *candidate;

#ifdef DEBUG
	if (trcopt)
		fprintf(errfile, "try_substitution called\n");
#endif

	if (TOKSYMS[n_TOKSYMS]  >= EOFT_SYM) /* do not delete a nonterminal*/
		return;

	ct = TOKSYMS[n_TOKSYMS];

	/* poss_substs = {}; */

#ifdef DEBUG
	if (trcopt)
		fprintf(errfile, "Poss_substs : ");
#endif
	/*(for t in POSS_TOK)	*/
	tmp_tp = POSS_TOK;
	while (tmp_tp != (struct two_pool *)0) {
		TOKSYMS[n_TOKSYMS] = tmp_tp->val.state;
		u = prs_check(sta_stack, TOKSYMS, n_TOKSYMS) - (BACKUPTOKS + 1);

#ifdef DEBUG
		if (trcopt)
			fprintf(errfile, " [ %s, %d ] ",
			  namelist((int)(tmp_tp->val.state)), u);
#endif
		if (u > MAX_CHECK ) {
			candidate = CANDALLOC();
			candidate->token_sym = tmp_tp->val.state;
			candidate->backup_toks = BACKUPTOKS;
			candidate->t3 = ct;
			candidate->next = (struct cand *)0;
			MAX_CHECK = u;
			cand_clear();
			CANDIDATES[SUBST] = candidate;
			n_CANDIDATES[SUBST] = 1	;
		}
		else if (u == MAX_CHECK ) {
			candidate = CANDALLOC();
			candidate->token_sym = tmp_tp->val.state;
			candidate->backup_toks = BACKUPTOKS;
			candidate->t3 = ct;
			candidate->next = CANDIDATES[SUBST];
			CANDIDATES[SUBST] = candidate;
			n_CANDIDATES [SUBST] ++;
		}
		tmp_tp = tmp_tp->link;
	}
#ifdef DEBUG
	if (trcopt)
		fprintf(errfile, "\n");
#endif

	TOKSYMS[n_TOKSYMS] = ct;
}

