/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#include "hdr.h"
#include "ada.h"
#include "adalexprots.h"
#include "pspansprots.h"
#include "prsutilprots.h"
#include "errsprots.h"
#include "lookupprots.h"
#include "recoverprots.h"
#include "makecorrprots.h"

static void reset_cands();

Span_s PRSERR_LOC ;


void make_correction(struct two_pool *STATE_STACK)		/*;make_correction*/
{
	/* Choose a correction by trying the modes in the order: merge, spelling,
	 * insertion, deletion, substitution.  
	 * Generate appropriate error message.
	 * Apply corrective action to token sequence, and restore state and parse
	 * stacks to correction point.
	 */
	struct	prsstack *ct,*nt,*r,*tokmod,*curtoken ;
	struct	two_pool *tmp_tp ;
	int	i ;
	char	*tv,*ctv,*ntv ;
	int		intok,subtk,bk ;
	int		n_STATE_STACK ;
	char	msg[200];
	int	delete_flag = 0;

	/************************** M E R G E *********************************/

    if ( CANDIDATES[MERGE] != NULL ) {

		/* [subtk, bk] := arb CANDIDATES[MERGE];							
		 * This will be achieved by taking the first element of the list	
		 */

		tv = namelist( subtk = CANDIDATES[MERGE]->token_sym ) ;

		/*	ct = bk == 0 ? curtok : PREVTOK ; */

		if((bk = CANDIDATES[MERGE]->backup_toks) == 0)
			ct = copytoken(curtok) ;
		else
			ct = copytoken(PREVTOK) ;

		/* 	nt =  bk == 0 ? nexttok : curtok ; */
		if(bk == 0)
			nt = copytoken(nexttok) ;
		else
			nt = copytoken(curtok) ;

		ctv = namelist(ct->ptr.token->index);
		ntv = namelist(nt->ptr.token->index);

		/* PRSERR_LOC = position(ct); */
		PRSERR_LOC = ct->ptr.token->span ;
		sprintf(msg,"\"%s\" expected instead of \"%s\" \"%s\"",
		  tv,ctv,ntv) ;
		syntax_err(LLOC(ct),RLOC(nt),msg);

		for (i = 1 ; i <= bk ; i++) {
			r = prs_stack ;
			prs_stack = prs_stack->prev ;
			add_to_top(r) ;
		} 

		/*
		 * tokens[tokind - 1 ] = [[subtk, namemap(token_value_des(tv) ? tv),
	     *						top(ct)]];
		 */
		 TOKMINUS ;
		 tokens[tokind]->symbol = subtk ;
		 tokens[tokind]->ptr.token->index = namemap(tv,strlen(tv));
		 tokens[tokind]->ptr.token->span = ct->ptr.token->span ;


		/*	
		 *	STA_STACK +:= STATE_STACK(n_STA_STACK + 1 ..
	     *									n_STATE_STACK - bk);
		 */


		/*	Strip bk elements off the top off STATE_STACK	*/

		while( bk-- > 0)
			STATE_STACK = STATE_STACK->link ;

		/* Count the size of STATE_STACK */

		n_STATE_STACK = 0 ;
		tmp_tp = STATE_STACK ;
		while (tmp_tp != NULL) {
			n_STATE_STACK ++ ;
			tmp_tp = tmp_tp->link ;
		}

		/* Count the size of STATE_STACK */

		n_sta_stack = 0 ;
		tmp_tp = sta_stack ;
		while (tmp_tp != NULL) {
			n_sta_stack ++ ;
			tmp_tp = tmp_tp->link ;
		}

		/*	Put the top (n_STATE_STACK - n_sta_stack) elements of STATE_STACK
		 *  on the end of sta_stack
		 */
	 	i = n_STATE_STACK - n_sta_stack ;
	 	tmp_tp = STATE_STACK ;
	 	while (--i > 0 )
			tmp_tp = tmp_tp->link ;
	 	tmp_tp->link = sta_stack ;
	 	sta_stack = STATE_STACK ;

		reset_cands() ;
		return;
	}	/* if */

	/************************** S P E L L   S U B S T *********************/

    else if (CANDIDATES[SPELL_SUBST] != NULL ) {


		/* [subtk, -, bk] := CANDIDATES[SPELL_SUBST]; */

		tv = namelist((subtk = CANDIDATES[SPELL_SUBST]->token_sym ));

		/* ct = bk == 0 ? curtok : prs_stack(n_prs_stack - bk + 1) ; */
	
		if ((bk = CANDIDATES[SPELL_SUBST]->backup_toks) == 0) {
			ct = copytoken(curtok) ;
		}
		else {
			/* ct := prs_stack(n_prs_stack - bk + 1) */ 
			int	bktmp = bk ;
			ct = prs_stack ;
			while(--bktmp)
				ct = ct->prev ;
			ct->prev = NULL ;
		}
		/* PRSERR_LOC := position(ct); */
		PRSERR_LOC = ct->ptr.token->span ;

		/* tokmod := [[subtk, tv, top(ct)]]; */
		tokmod = ct ;
		tokmod->prev = NULL ;
		tokmod->symbol = subtk ;
		/* tokmod->ptr.token->index = tv ; */
		tokmod->ptr.token->span = ct->ptr.token->span ; 

		sprintf(msg , "Reserved word \"%s\" misspelled", tv ) ;
		syntax_err(LLOC(ct),RLOC(ct),msg);
	}

	/***************************** I N S E R T *******************************/

    else if (CANDIDATES[INSERT] != NULL ) {
		
		Span_s pt,ct ;
		struct  prsstack *pt_token;
		short		tmp_symbol ;


		/* [intok, -, bk] := arb CANDIDATES[INSERT]; */

		tv = namelist((intok = CANDIDATES[INSERT]->token_sym));

		/* curtoken := bk == 0 ? curtok : prs_stack(n_prs_stack - bk + 1) ; */

		if ((bk = CANDIDATES[INSERT]->backup_toks) == 0) {
			curtoken = copytoken(curtok) ;
		}
		else {
			/* curtoken := prs_stack(n_prs_stack - bk + 1) */ 
			int	bktmp = bk ;

			struct prsstack *tmp_ps = prs_stack ;

			while(--bktmp)
				tmp_ps = tmp_ps->prev ;

			pt =  r_span(tmp_ps->prev) ;
			tmp_symbol = tmp_ps->prev->symbol ;
			/* copytoken(curtoken,tmp_ps) ; */
			curtoken = tmp_ps;
			pt_token = curtoken->prev;
		}

		if (bk == 0) {
			/* pt =	 r_span(prs_stack) ; */
			/* if parse stack is empty (error on first token),
			   use location of current token  */
			/* Metaware HIC does not like next line - so expand it manually 
				pt = (prs_stack != (struct prsstack *)0
			      ? r_span(prs_stack)
				: l_span(curtoken) ) ;
			 */
			if (prs_stack != (struct prsstack *)0) {
			    pt = r_span(prs_stack);
			    pt_token = prs_stack;
			}
			else {
			    pt = l_span(curtoken);
			    pt_token = curtoken;
			}
			tmp_symbol = prs_stack->symbol ;
		}

		ct = l_span(curtoken) ;

		for (i = 1 ; i <= bk; i++ ) {
			r = prs_stack;
			prs_stack = prs_stack->prev ;
			add_to_top(r) ;
		} 
		/* 
		 *	tokmod := [curtoken, [intok, get_name(token_value_des(tv) 
	     *					? tv), top(pt)]];							 
		 */

		/* curtoken->prev = TALLOC() ; */
		/* curtoken->prev->ptr->index = namemap(tv) ; */
		/* curtoken->prev->ptr.token->span = pt->ptr->span ; */
		tokens[tokind] = curtoken ;

		add_to_top(PRSALLOC()) ;
		tokens[tokind]->symbol = intok ;
		tokens[tokind]->ptr.token = TOKALLOC() ;
		tokens[tokind]->ptr.token->index = namemap((char *)token_val_des(tv),
											strlen((char *)token_val_des(tv))) ;
		tokens[tokind]->ptr.token->span = pt ;
		tokmod = NULL;		


		if (n_CANDIDATES[INSERT] == 1) {

			if (( tmp_symbol == SEMI_SYM  )
			  || (prs_stack == NULL) /* if parse stack empty */
			  || ( tmp_symbol > EOFT_SYM ) ) {
				/*
				* This kludge is to take
				* care of nonterminals
				*/
				sprintf(msg,"\"%s\" expected before this token",tv);
				/*
				syntax_err(&PREVTOK->ptr.token->span,
				  &PREVTOK->ptr.token->span,msg);
				*/
				syntax_err(LLOC(curtoken),RLOC(curtoken),msg) ;
				PRSERR_LOC = ct ;
			}
			else {
				PRSERR_LOC = pt ;
				sprintf(msg,"\"%s\" expected after this token",tv);
				syntax_err(LLOC(pt_token),RLOC(pt_token),msg) ;
				/*
				syntax_err(&PREVTOK->ptr.token->span,
				  &PREVTOK->ptr.token->span,msg);
				syntax_err(&curtok->ptr.token->span,&curtok->ptr.token->span,msg);
				*/
			}
		}
		else {
			PCAND	next_cand ;
			char *tmp = msg;
			/* 
			 * errfile := [
		     *	 '{' +/[' ' + NAME_LIST(x(1)) : x in inserts] 
			 *		    + ' } expected after this token'];
			 */

			sprintf(tmp,"One of { ");
			tmp += strlen(tmp);
			next_cand = CANDIDATES[INSERT] ;
			while(next_cand != NULL) {	
				sprintf(tmp,"%s ",namelist(next_cand->token_sym) ) ;
				tmp += strlen(tmp);
				next_cand = next_cand->next ;
			}

			sprintf(tmp," } expected after this token");
			PRSERR_LOC = pt ;
			syntax_err(LLOC(pt_token),RLOC(pt_token),msg);
		}

    	/* 
		 * STA_STACK +:= STATE_STACK(n_STA_STACK + 1 .. n_STATE_STACK - bk) ; 
		 */

		/*	Strip bk elements off the top off STATE_STACK	*/

		while(bk--)
			STATE_STACK = STATE_STACK->link ;

		/* Count the size of STATE_STACK */

		n_STATE_STACK = 0 ;
		tmp_tp = STATE_STACK ;
		while (tmp_tp != NULL) {
			n_STATE_STACK ++ ;
			tmp_tp = tmp_tp->link ;
		}

		/* Count the size of STATE_STACK */

		n_sta_stack = 0 ;
		tmp_tp = sta_stack ;
		while (tmp_tp != NULL) {
			n_sta_stack ++ ;
			tmp_tp = tmp_tp->link ;
		}

		/*	Put the top (n_STATE_STACK - n_sta_stack) elements of STATE_STACK
		 *  on the end of sta_stack
		 */
	 	i = n_STATE_STACK - n_sta_stack ;
	 	tmp_tp = STATE_STACK ;
	 	while (--i > 0 )
			tmp_tp = tmp_tp->link ;
	 	tmp_tp->link = sta_stack ;
	 	sta_stack = STATE_STACK ;

		reset_cands() ;
		return ;

	} /* if */

	/**************************** D E L E T E *********************************/

    else if (CANDIDATES[DELETE] != NULL ) {

		/* [-, bk] := arb CANDIDATES[DELETE];						 */
		/* ct = bk == 0 ? curtok : prs_stack(n_prs_stack - bk + 1) ; */

		if ((bk = CANDIDATES[DELETE]->backup_toks) == 0)
			ct = copytoken(curtok) ;
		else {
			/* ct := prs_stack(n_prs_stack - bk + 1) ;*/ 
			int	bktmp = bk ;
			struct prsstack *tmp_ps = prs_stack ;

			while(--bktmp)
				tmp_ps = tmp_ps->prev ;

			ct = copytoken(tmp_ps) ;
		}

		sprintf(msg, "Unexpected \"%s\" ignored", find_name(ct) ) ;
		PRSERR_LOC = ct->ptr.token->span ;
		syntax_err(LLOC(ct),RLOC(ct),msg);

		tokmod = NULL ;
		delete_flag = 1;
	} /* if */

	/************************** S U B S T ************************************/

    else if (CANDIDATES[SUBST] != NULL) {

		/* [subtk, -, bk] := arb substs; */

		tv = namelist((subtk = CANDIDATES[SUBST]->token_sym));

		/* ct = bk == 0 ? curtok : prs_stack(n_prs_stack - bk + 1) ; */

		if ((bk = CANDIDATES[SUBST]->backup_toks) == 0)
			ct = copytoken(curtok) ;
		else {
			/* ct := prs_stack(n_prs_stack - bk + 1) */
			int	bktmp = bk ;
			struct prsstack *tmp_ps = prs_stack ;

			while(--bktmp)
				tmp_ps = tmp_ps->prev ;

			ct = copytoken(tmp_ps) ;
		}

		PRSERR_LOC = ct->ptr.token->span ;

		/* 
		 * tokmod := [[subtk, get_name(token_value_des(tv) ? tv), top(ct)]];
		 */
		tokmod = copytoken(ct) ;
		tokmod->prev = NULL ;
		tokmod->symbol = subtk ;
		tokmod->ptr.token->index = namemap(token_val_des(tv),
		  strlen(token_val_des(tv))) ; 

		if (n_CANDIDATES[SUBST] == 1) {
			if ( (is_reserved(CANDIDATES[SUBST]->token_sym) )
			  && (ct->symbol == ID_SYM) && (spell(tv,find_name(ct) ) < 3) )
				sprintf(msg,"Reserved word \"%s\" misspelled", tv) ;
			else
		    	sprintf(msg,"\"%s\" expected instead of \"%s\"",
		    	  tv,find_name(ct) ) ;

		    syntax_err(LLOC(ct),RLOC(ct),msg);
		}
		else {
			char	*tmp = msg;
			PCAND	next_cand ;
			/*
			 * errfile := ['{' +/[' ' + NAME_LIST(x(1)) : x in substs]
			 *				+ ' } expected instead of ' + '"' +
			 *				find_name(ct) + '"'];
			 */
			sprintf(tmp,"One of { ");
			tmp += strlen(tmp);
			next_cand = CANDIDATES[SUBST] ;
			while(next_cand != NULL) {	
				sprintf(tmp,"%s ",namelist(next_cand->token_sym) ) ;
				tmp += strlen(tmp);
				next_cand = next_cand->next ;
			}
			sprintf(tmp," } expected instead of \"%s\"",find_name(ct)) ;
			syntax_err(LLOC(ct),RLOC(ct),msg);
		}
    } 

	/*
	 * Alter token sequence in accordance with corrective action.
	 * Restore state and parse stacks to correction point.
	 */

    for (i = 1 ; i<=bk; i++ ) {
		r = prs_stack;
		prs_stack = prs_stack->prev ;
		r->prev = NULL ;
		add_to_top(r) ;
    } 

	if (tokmod != NULL) 
		tokens[tokind] = tokmod ;
	else if (delete_flag)
	    TOKMINUS;
    /* 
	 * STA_STACK +:= STATE_STACK(n_STA_STACK + 1 .. n_STATE_STACK - bk) ; 
	 */

	/*	Strip bk elements off the top off STATE_STACK	*/

	while (bk--)
	    STATE_STACK = STATE_STACK->link ;

	/* Count the size of STATE_STACK */

	n_STATE_STACK = 0 ;
	tmp_tp = STATE_STACK ;
	while (tmp_tp != NULL) {
		n_STATE_STACK ++ ;
		tmp_tp = tmp_tp->link ;
	}

	/* Count the size of STATE_STACK */

	n_sta_stack = 0 ;
	tmp_tp = sta_stack ;
	while (tmp_tp != NULL) {
		n_sta_stack ++ ;
		tmp_tp = tmp_tp->link ;
	}

	/*
	 *	Put the top (n_STATE_STACK - n_sta_stack) elements of STATE_STACK
	 *  on the end of sta_stack
	 */
	 i = n_STATE_STACK - n_sta_stack ;
	 tmp_tp = STATE_STACK ;
	 while (--i > 0 )
		tmp_tp = tmp_tp->link ;
	 tmp_tp->link = sta_stack ;
	 sta_stack = STATE_STACK ;

	 reset_cands() ;

}	/* end procedure make_correction; */

static void reset_cands()									/*;reset_cands*/
{
	int i ;
	/* 
	 * Reset the sets of candidates to empty for future errors 
	 */
	 for (i = DELETE ; i <= SPELL_SUBST ; i ++ ) 
	 {
		n_CANDIDATES[i] = 0 ;
		CANDIDATES[i] = NULL ;
	 }
}
