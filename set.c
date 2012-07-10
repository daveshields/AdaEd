/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "config.h"
#include "set.h"
#include "miscprots.h"
#include "setprots.h"

/* body of small integer set package  */
/* represent sets using tuples */

static Tuple NULL_TUPLE;
static char *FREE_TUPLE = (char *)0;/* list of free (singleton) tuples */

char *set_arb(Set sp)											/*;set_arb*/
{
	/* pick arbitrary element from set */

	if ((int) sp[0] == 0) chaos("set_arb - set already empty");
	return sp[1];
}

Set set_copy(Set sp) 											/*;set_copy*/
{
	/* make copy of set */

	return (Set) tup_copy((Tuple) sp);
}

Set set_del(Set sp, char *n) 									/*;set_del*/
{
	/* remove n from small set */

	int	    i;
	int	    j, cur;

	if (tup_mem(n, (Tuple) sp) == FALSE) return (sp);		/* if not member */
	cur = (int) sp[0];
	for (i = 1; i <= cur; i++) {
		/* here to remove, element known to be present */
		if (sp[i] == n) {
	    	for (j = i + 1; j <= cur; j++) {
				sp[i] = sp[j];
				i++;
	    	}
	    	sp[0] = (char *) --cur;
		}
	}
	return (sp);
}

void set_free(Set sp)											/*;set_free*/
{
	/* free set */
	tup_free(sp);
}

char   *set_from(Set sp)										/*;set_from*/
{
	int n;

	if (sp[0] == 0) chaos("set_from null_set");
	n = (int) sp[0];
	sp[0] = (char *) (n-1);
	return sp[n];
}

Set set_less(Set s, char *n)									/*;set_less*/
{
	int	i, j, cur;

	if (!tup_mem(n, s)) return s;
	cur = (int) s[0];
	for (i = 1; i <= cur; i++) {
		if (s[i] == n) { /* move down remaining elements */
	    	for (j = i+1; j <= cur; j++)
				s[j-1] = s[j];
	    	s[0] = (char *) (--cur);  /* adjust count */
	    	return s;
		}
	}
}

Set set_new(int n)												/*;set_new*/
{
	/* allocate new set with room for n elements */

	Set sp;

	sp = tup_new(n);
	sp[0] = (char *)0;
	return sp;
}

Set set_new1(char *n)											/*;set_new1*/
{
	Set sp;

	sp = set_new(1);
	sp = set_with(sp, n);
	return sp;
}


int	set_mem(char *n, Set sp)									/*;set_mem*/
{
	/* test if n in small set sp */
	return tup_mem(n, sp);
}

#ifndef EXPORT
int	set_size(Set sp)											/*;set_size*/
{
	/* return number of elements in small set */
	return (int) sp[0];
}
#endif

int set_subset(Set sp1, Set sp2)								/*;set_subset*/
{
	/* test for subset by just seeing if each element in first set is
	 * contained in the second. A better algorithm would exploit the
	 * ordering of the elements.
	 */
    Forset	fs1;
    char	*elem;
    FORSET(elem=(char *), sp1, fs1);
		if (!set_mem(elem, sp2)) return FALSE;
    ENDFORSET(fs1);
    return TRUE;
}

Set set_union(Set sp1, Set sp2)									/*;set_union*/
{
	/* union of two small sets */

	Set t;
	Set spr;
	int	    i, cur, n1, n2;

	/* arrange so sp1 points to larger set */
	n1 = (int) sp1[0];
	n2 = (int) sp2[0];
	if (n2 > n1) {
		/* second is larger, swap pointers */
		t = sp1;
		sp1 = sp2;
		sp2 = t;
	}
	spr = set_copy(sp1);
	cur = (int) sp2[0];
	for (i = 1; i <= cur; i++)
		spr = set_with(spr, sp2[i]);
	return spr;
}

Set set_with(Set sp, char *n)									/*;set_with*/
{
	/* insert n into set sp */

	unsigned cur;

	if (tup_mem(n, sp) == TRUE) return sp;		/* if already present */
	cur = (unsigned) sp[0];
	sp = tup_exp(sp, (unsigned)  (cur+1));
	/* insert new value at end */
	sp[++cur] = n;
	sp[0] = (char *) cur;
	return sp;
}

/* Tuple operations */

void tup_init()												/*;tup_init*/
{
	/* initialize NULL_TUPLE, the (unique) null tuple */
	NULL_TUPLE = (Tuple) emalloct(sizeof(char *), "null-tuple");
	*NULL_TUPLE = (char *)0; /* set null length */
}

Tuple tup_add(Tuple tpa, Tuple tpb)				/*;tup_add*/
{
	/* concatenate two tuples */

	Tuple trp;
	int	    i, ni = 1;

	if (tpa == (Tuple)0 ) chaos(" tup_add: first tuple null");
	if (tpb == (Tuple)0 ) chaos(" tup_add: second tuple null");

	trp = tup_new(tup_size(tpa) + tup_size(tpb));
	for (i = 1; i <= (int) tpa[0]; i++)
		trp[ni++] = tpa[i];
	for (i = 1; i <= (int) tpb[0]; i++)
		trp[ni++] = tpb[i];
	return trp;
}

Tuple tup_copy(Tuple tp)										/*;tup_copy*/
{
	/* return copy of tuple */

	Tuple  tnp;
	int	    i;

	if (tp == NULL_TUPLE) return NULL_TUPLE; /* copy of null tuple is itself*/
	tnp = tup_new(tup_size(tp));

	for (i = 1; i <= (int) tp[0]; i++)
		tnp[i] = tp[i];
	return tnp;
}

Tuple tup_exp(Tuple tp, unsigned int n)							/*;tup_exp*/
{
	/* expand tuple so can hold n elements */

	unsigned int oldn;
	Tuple oldtp;

#ifdef CHAOS
	if (n == 0 || n>99999) chaos("tup_exp: new length > 99999");
#endif
#ifdef SKIP
	if ((int)tp[0]>n) {
		/* adjust length */
		tp[0] = (char *) n;
		return tp;
	}
#endif
	/* if expanding null tuple, allocate real tuple */
	if (tp == NULL_TUPLE)
		tp = tup_new((int)n); 
	/* if expanding smalloc singleton */
	else if (is_smalloc_block((char *)tp)) { 
		oldtp = tp;
		tp = (Tuple) ecalloct(sizeof(char *), (unsigned) n+1,
		  "tup-new-smalloc-exp");
		tp[0] = (char *)n;
		tp[1] = oldtp[1];
		oldtp[0] = FREE_TUPLE; /* add smalloc block to free list */
		FREE_TUPLE = (char *) oldtp;
	}
	else {
		if ((unsigned)tp[0] >= n) return tp;
		oldn = (unsigned)tp[0]+1;
		tp[0] = (char *)n;
		tp = (Tuple) erealloct((char *) tp, sizeof(char **) *((unsigned) n + 1),
		  "tup-exp");
		for (; oldn <= n; oldn++)
			tp[oldn] = (char *) 0;
	}
	return tp;
}

void tup_free(Tuple tp)										/*;tup_free*/
{
	if (tp == NULL_TUPLE) return;
#ifndef SMALLOC
	efreet((char *) tp, "tup-free");
#else
	/* if tuple is allocated in smalloc area add to free list, otherwise
	 * free in usual way */
	if (is_smalloc_block((char *) tp)) {
		tp[0] = FREE_TUPLE;
		FREE_TUPLE = (char *) tp;
	}
	else {
		if (tp == NULL_TUPLE) return;
		efreet((char *) tp, "tup-free");
	}
#endif
}

char   *tup_frome(Tuple tp)									/*;tup_frome*/
{
	/* remove element from end */

	if ((int) tp[0] == 0) chaos("tup_frome: tuple already empty");
	tp[0] -= 1;
	return (tp[((int) tp[0]) + 1]);
}

char   *tup_fromb(Tuple tp)									/*;tup_fromb*/
{
	/* remove element from front */

	int	    n, i;
	char   *elt;

	n = (int) tp[0];
	if (n == 0) return 0;
	elt = tp[1];
	for (i = 2; i <= n; i++) 
		tp[i - 1] = tp[i];
	tp[0] = (char *) n-1; /* decrement length */
	return elt;
}

int   tup_mem(char *n, Tuple tp)								/*;tup_mem*/
{
	int i;
	int sz;

	if (tp == (Tuple)0) chaos("tup_mem: tuple not defined");

	sz = tup_size(tp);
	if (sz<0 || sz >9999) chaos("tup_mem: ridiculous tuple element count");

	for (i = 1; i <= sz; i++) 
		if (tp[i]== n) return TRUE;
	return FALSE;
}

int	tup_memi(char *n, Tuple tp)								/*;tup_memi*/
{
	/* like tup_mem but returns index where n present, else 0 if n not present*/

	int	i, sz;

	sz = tup_size(tp);
	for (i = 1; i <= sz; i++) 
		if (tp[i] == n) return i;
	return 0;
}

int   tup_memstr(char *n, Tuple tp)							/*;tup_memstr*/
{
	/* like tup_mem, but n is string, so use streq to check for equality*/

	int i;
	int sz;

	sz = tup_size(tp);
	for (i = 1; i <= sz; i++) 
		if (strcmp(tp[i], n) == 0) return TRUE;
	return FALSE;
}

Tuple tup_new(int n)											/*;tup_new*/
{
	/* allocate new tuple with room for n elements */

	Tuple tp;

	if(n == 0) return NULL_TUPLE;
#ifndef SMALLOC
	tp = (Tuple) ecalloct( (unsigned) n + 1, sizeof(char **), "tup-new");
#else
	/* allocate via smalloc if length one */
	if (n == 1) {
		if (FREE_TUPLE != (char *)0) { /* if can take from free list */
	    	tp = (Tuple) FREE_TUPLE;
	    	FREE_TUPLE = (char *) tp[0];
		}
		else
	    	tp= (Tuple) smalloc(2*sizeof(char *));
		tp[1] = (char *)0; /* clear value */
	}
	else
		tp = (Tuple) ecalloct( (unsigned) n + 1, sizeof(char **), "tup-new");
#endif
	tp[0] = (char *)n;
	return tp;
}

Tuple tup_new1(char *a)											/*;tup_new1*/
{
	Tuple tp;

	tp = tup_new(1);
	tp[1] = a;
	return (tp);
}

Tuple tup_new2(char *a, char *b)								/*;tup_new2*/
{
	Tuple tp;

	tp = tup_new(2);
	tp[1] = a;
	tp[2] = b;
	return (tp);
}

#ifndef EXPORT
int	tup_size(Tuple tp)											/*;tup_size*/
{
#ifdef CHAOS
	int n;

	if (tp == (Tuple)0) chaos("tup_size argument null pointer");

	n = (int)tp[0];
	if (n < 0 || n > 99999) chaos("tup_size: size out of range");
#endif
	return (int) tp[0];
}
#endif

Tuple tup_with(Tuple tp, char *val)								/*;tup_with*/
{
	/* add val at end of tuple, return pointer to result */

	unsigned    n;

	n = (unsigned) tp[0] + 1;
	tp = tup_exp(tp, n);
	tp[n] = (char *) val;
	return tp;
}

Set set_diff(Set sp1, Set sp2)									/*;set_diff*/
{
	/* return set of elements from sp1 that are not in sp2 */
    Forset fs;
    char *item;
    Set spr;

    spr=set_new(0);
    FORSET(item=(char *), sp1, fs);
    	if (!set_mem(item, sp2))
			spr = set_with(spr, item);
    ENDFORSET(fs);
    return spr;
}

#ifdef DEBUG
void set_print(Set sp)											/*;set_print*/
{
	int	    i, cur;

	cur = (int) sp[0];
	for (i = 1; i <= cur; i++)
		printf("%d%c", sp[i], (i ) % 10 ? ' ' : '\n');
	if ((i ) % 10)
		printf("\n");
}

void tup_print(Tuple tp)										/*;tup_print*/
{
	/* print tuple on standard output */

	int	    i;

	for (i = 1; i <= (int) tp[0]; i++)
		printf("%d ", tp[i]);
	printf("\n");
}
#endif
