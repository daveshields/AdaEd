/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "hdr.h"
#include "ada.h"
#include "stdlib.h"
#include "adalexprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "prsutilprots.h"

int	stack_count(struct prsstack *ps)						/*;stack_count*/
{
	int size = 0;

	while( ps != (struct prsstack *)0) {
		ps = ps->prev;
		size++;
	}

	return (size);
}

void copystack(struct two_pool *s, struct two_pool **head, int *size)
															/*;copystack*/
{
	/*	This procedure copies the stack s represented by a singly linked list
	 *  It returns a pointer to the head (top) of the new stack, as well as a
	 *  count of the size of the stack, returned in size
	 *  Note : lists in the front-end are circular, so the link of the last node
	 *	   points to the head of the list.
	 */

	struct two_pool *next,
	*tmp_tp;

	*size = 1;
	/*	Copy head node	 */
	tmp_tp = *head = TALLOC ();
	tmp_tp -> link = NULL;
	tmp_tp -> val.state = s -> val.state;
	/*  Copy rest of list	 */
	next = s -> link;
	while (next != NULL) {
		tmp_tp -> link = TALLOC ();
		tmp_tp = tmp_tp -> link;
		tmp_tp -> link = NULL;
		tmp_tp -> val.state = next -> val.state;
		next = next -> link;
		(*size)++;
	}
}

void dump_stack(struct two_pool *s)						/*;dump_stack*/
{
	int	    count = 0;
#ifdef DEBUG
	if (trcopt) {
		while (s != (struct two_pool *)0) {
			count++;
			fprintf (errfile, "%d %s", s -> val.state,
			  ( ((count%10) == 0) ? "\n":",") );
			s = s -> link;
		}
		fprintf (errfile, " ======>size = %d<====== \n",count);
	}
#endif
}

void dump_prssyms(struct two_pool *s)					/*;dump_prssyms*/
{
	int	    count = 0;
#ifdef DEBUG
	if (trcopt) {
		while (s != (struct two_pool *)0) {
			count++;
			fprintf (errfile, "%s %s", TOKSTR(s -> val.state),
			  ( ((count%5) == 0) ? "\n":",") );
			s = s -> link;
		}
		fprintf (errfile, " ======>size = %d<====== \n",count);
	}
#endif
}

void dump_prsstack(struct prsstack *p)					/*;dump_prsstack*/ 
{
	/* dump symbols of parse stack */
	int count = 0;
#ifdef DEBUG
	if (trcopt) {
		while (p!=(struct prsstack *)0) {
			count++;
			fprintf(errfile,"%s %c",TOKSTR(p->symbol),
			  ( (count%5 == 0) ? '\n' : ' ') );
			p = p->prev;
		}
		fprintf(errfile,"	 size = %d\n",count);
	}
#endif
}

void dump_toksyms(char *s)							/*;dump_toksyms*/
{
	int	    t;

#ifdef DEBUG
	if (trcopt) {
		fprintf (errfile, "Dump of TOKSYMS [%s]\n", s);
		for (t = n_TOKSYMS; t >= 0; t--) {
			fprintf (errfile, "%s%s", TOKSTR(TOKSYMS[t]),
			  ((t % 15) == 14 ? "\n" : " "));
		}
		fprintf (errfile, "\n	< ===== >\n");
	}
#endif
}


void convtolower(char *s)								/*;convtolower*/
{
	/* Convtolower: convert an entire string to lowercase. */
	while (*s) {
		if (isupper(*s))
			*s = tolower(*s);
		s++;
	}
}

void cand_clear()										/*;cand_clear*/
{
	/* cand_clear :	 clear (reinitialize) all candidate sets to empty */
	short x;

	for (x = DELETE; x <= SPELL_SUBST; x++) {
		/* TBSL: free current candidates */
		CANDIDATES[x] = NULL;
		n_CANDIDATES[x] = 0;
	}
}

void dump_cand()										/*;dump_cand*/
{
	/* dump_cand :	dump contents of the candidates map to errfile */
	short x,i;
	struct cand *c;
	char *sub;

#ifdef DEBUG
	if (trcopt) {
		for (x = DELETE; x <= SPELL_SUBST; x++) {
			switch (x) {
			case DELETE:
			case MERGE:
				if (n_CANDIDATES[x] == 0)
					break;
				fprintf(errfile,"%s :\n",(x == DELETE ? "delete" : "merge"));
				c = CANDIDATES[x];
				i=0;
				while (c != (struct cand *)0) {
					fprintf(errfile,"[ %s %d ] %c",TOKSTR(c->token_sym),
					  c->backup_toks+1,((++i % 5) == 0 ? '\n' : ' ') );
					c = c->next;
				}  /* end while */
				if (i%5 != 0) fprintf(errfile,"\n");
				break;
			case INSERT:
			case SUBST:
			case SPELL_SUBST:
				if (n_CANDIDATES[x] == 0)
					break;
				if (x == INSERT) sub = "insert";
				else if (x == SUBST) sub = "subst";
				else sub = "spell_subst";

				fprintf(errfile,"%s :\n",sub);
				c = CANDIDATES[x];
				i=0;
				while (c != (struct cand *)0) {
					fprintf(errfile,"[ %s %s %d ] %c",TOKSTR(c->token_sym),
					  TOKSTR(c->t3),
					  c->backup_toks+1,((++i % 4) == 0 ? '\n' : ' ') );
					c = c->next;
				}
				if (i%4 != 0) fprintf(errfile,"\n");
				break;
			} /* end switch */
		} /* end for */
	}
#endif
}

struct prsstack *copytoken(struct prsstack *b)				/*;copytoken*/
{
	struct prsstack *a;
	char *oldp, *newp;
	int i;

	/* First get space for a */
	a = PRSALLOC();
	a->symbol = b->symbol;
	a->prev = NULL;
	if ( ISTOKEN(b) ) { /* copy token structure */

		a->ptr.token = TOKALLOC();
		a->ptr.token->index = b->ptr.token->index;
		a->ptr.token->span = b->ptr.token->span;
	}
	else {  /* copy ast structure */

		a->ptr.ast = node_new(N_KIND(b->ptr.ast));
		oldp = (char *)(b->ptr.ast); 
		newp = (char *)(a->ptr.ast);
		for (i = 0; i < sizeof(Node_s); i++)
			*newp++ = *oldp++;
	}
	/* end of macro definition */
	return a;
}

/* start allocation routines */

/* This file contains the allocation and freeing routines for various
   structures */
/* replace EMalloc by emalloc (misc.c)
 * char *EMalloc(n)
 */


static struct prsstack *deadprsstack = (struct prsstack *)0;
static void prsfree1(struct prsstack *, struct prsstack *);
static void prsfree2(struct prsstack *, struct prsstack *);
static struct prsstack * prsfakealloc();
struct prsstack *(*prsalloc)(unsigned) =(struct prsstack *(*)(unsigned))emalloc;
void (*prsfree)(struct prsstack *, struct prsstack *) = prsfree1;

static struct prsstack *prsfakealloc()					/*;prsfakealloc*/
{
	struct prsstack *tmp;

	if (deadprsstack != (struct prsstack *)0) {
		tmp = deadprsstack;
		deadprsstack = deadprsstack->prev;
		return(tmp);
	}
	prsalloc = (struct prsstack *(*)(unsigned)) emalloc;
	prsfree = prsfree1;
	return((struct prsstack *)emalloc(sizeof(struct prsstack)));
}

static void prsfree1(struct prsstack *p, struct prsstack *q)	/*;prsfree1*/
{
	prsfree = prsfree2;
	prsalloc = (struct prsstack *(*)(unsigned)) prsfakealloc;
	q->prev = deadprsstack;
	deadprsstack = p;
}

static void prsfree2(struct prsstack *p, struct prsstack *q)	/*;prsfree2*/
{
	q->prev = deadprsstack;
	deadprsstack = p;
}

static struct two_pool *deadtwostack = (struct two_pool *)0;
static void tfree1(struct two_pool *, struct two_pool *);
static void tfree2(struct two_pool *, struct two_pool *);
static struct two_pool *tfakealloc();
struct two_pool *(*talloc)(unsigned) = (struct two_pool *(*)(unsigned)) emalloc;
void (*tfree)(struct two_pool *, struct two_pool *) = tfree1;

static struct two_pool *tfakealloc()
{
	struct two_pool *tmp;

	if (deadtwostack != (struct two_pool *)0) {
		tmp = deadtwostack;
		deadtwostack = deadtwostack->link;
		return(tmp);
	}
	talloc = (struct two_pool *(*)(unsigned)) emalloc;
	tfree = tfree1;
	return((struct two_pool *)emalloc(sizeof(struct two_pool)));
}

static void tfree1(struct two_pool *p, struct two_pool *q)		/*;tfree1*/
{
	tfree = tfree2;
	talloc = (struct two_pool *(*)(unsigned)) tfakealloc;
	q->link = deadtwostack;
	deadtwostack = p;
}

static void tfree2(struct two_pool *p, struct two_pool *q)		/*;tfree2*/
{
	q->link = deadtwostack;
	deadtwostack = p;
}

static struct token *deadtokstack = (struct token *)0;
static void tokfree1(struct token *);						/*;tokfree1*/
static void tokfree2(struct token *);						/*;tokfree1*/
static struct token *tokfakealloc();
struct token *(*tokalloc)(unsigned) = (struct token *(*)(unsigned)) emalloc;
void (*tokfree)(struct token *) = tokfree1;

static struct token *tokfakealloc()						/*;tokfakealloc*/
{
	struct token *tmp;

	if (deadtokstack == (struct token *)0) {
		tokalloc = (struct token *(*)(unsigned)) emalloc;
		tokfree = tokfree1;
		return((struct token *)emalloc(sizeof(struct token)));
	}
	tmp = deadtokstack;
	deadtokstack = ((struct tmptok *)deadtokstack)->link;
	return(tmp);
}

static void tokfree1(struct token *p)						/*;tokfree1*/
{
	((struct tmptok *)p)->link = deadtokstack;
	deadtokstack = p;
	tokalloc = (struct token *(*)(unsigned)) tokfakealloc;
	tokfree = tokfree2;
}

static void tokfree2(struct token *p)						/*;tokfree2*/
{
	((struct tmptok *)p)->link = deadtokstack;
	deadtokstack = p;
}

/*
static Node deadnodestack = (Node)0;
*/

void nodefree(Node p)								/*;nodefree*/
{
#ifdef gargar
	if (p != OPT_NODE && p != any_node && N_KIND(p) != as_free) {
		((struct tmpnode *)p)->link = deadnodestack;
		((struct tmpnode *)p)->kind = as_free;
		deadnodestack = p;
	}
#endif
}

#ifdef gargar
static Node *deadaststack = (struct ast **)0;

void astfree(struct ast **p)									/*;astfree*/
{
	((struct tmpast *)p)->link = deadaststack;
	deadaststack = p;
}
#endif

/* Cand stuff is for error recovery */

struct cand *(*candalloc)(unsigned) = (struct cand *(*)(unsigned)) emalloc;

char *find_name(struct prsstack *x)								/*;find_name*/
{
	if  (ISTOKEN(x)) return TOKSTR(x->ptr.token->index);
	return namelist(x->symbol);
}

void attrnum(Node node)										/*;attrnum*/
{
	/* convert attribute string to internal attribute code */
	int		i;
	char	*s, *name;
	static char *attrnames[] = {
		"ADDRESS",
		"AFT",
		"BASE",
		"CALLABLE",
		"CONSTRAINED",
		"O_CONSTRAINED",
		"T_CONSTRAINED",
		"COUNT",
		"DELTA",
		"DIGITS",
		"EMAX",
		"EPSILON",
		"FIRST",
		"O_FIRST",
		"T_FIRST",
		"FIRST_BIT",
		"FORE",
		"IMAGE",
		"LARGE",
		"LAST",
		"O_LAST",
		"T_LAST",
		"LAST_BIT",
		"LENGTH",
		"O_LENGTH",
		"T_LENGTH",
		"MACHINE_EMAX",
		"MACHINE_EMIN",
		"MACHINE_MANTISSA",
		"MACHINE_OVERFLOWS",
		"MACHINE_RADIX",
		"MACHINE_ROUNDS",
		"MANTISSA",
		"POS",
		"POSITION",
		"PRED",
		"RANGE",
		"O_RANGE",
		"T_RANGE",
		"SAFE_EMAX",
		"SAFE_LARGE",
		"SAFE_SMALL",
		"SIZE",
		"O_SIZE",
		"T_SIZE",
		"SMALL",
		"STORAGE_SIZE",
		"SUCC",
		"TERMINATED",
		"VAL",
		"VALUE",
		"WIDTH",
		0	};

	s = N_VAL(N_AST1(node));
	for (i = 0;; i++) {
		name = attrnames[i];
		if (name == (char *)0) break;
		if (streq(name, s)) {
			/* on match, change ast1 node to hold number, not str*/
			N_KIND(N_AST1(node)) = as_number;
			N_VAL(N_AST1(node)) = (char *) i;
			break;
		}
	}
#ifdef IGNORE
	printf("attribute %s\n", s);
	chaos("unable to match attribute name");
#endif
}
