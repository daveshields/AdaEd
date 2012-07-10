/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#ifndef _set_h
#define _set_h
/*		Set and Tuple procedures
		    David Shields
		      27 Jan 84
 */
	
typedef char **Tuple;

/*
Tuples are represented as an array of pointers to the element values.
Tuples of small integers can be maintained using casts to store
integers instead of pointers in the array. The first element of the
array gives the number of components.

  tup_add(tia,tib) concatenate two tuples
  tup_copy(ti)	return copy of small tuple
  tup_exp(ti,n) expand tuple to length n
  tup_free(ti)	free tiace allocated for tuple
  tup_frome(ti) remove element at end
  tup_fromb(ti) remove element from front
  tup_mem(n,tp) test for membership in tuple
  tup_memi(n,tp) test for membership return index if found, else 0
  tup_new(n)	make new tuple with length zero, no elements
  tup_new1(a)	make new tuple with one component a (singleton)
  tup_new2(a,b) make new tuple with two components: a and b (pair)
  tup_print(ti) print small tuple on standard outiut (debug assist)
  tup_size(ti)	return current size of small tuple
  tup_with(ti,n) add element to end of tuple

*/


/* to iterate over Tuple, (Setl (for var in tup)use
  SETL	(for var in tup) becomes:

  Fortup fort;
  ...
  FORTUP(var,tup, fort)
   ...
  ENDFORTUP(fort)

  FORTUPI is variant corresponding to SETL  (for var = tup(i))
*/
/* Note that tup only evaluated once in FORTUP */
#define FORTUP(var,tup,iv) \
    iv.fortup_val = tup;\
    if(iv.fortup_count = (int) iv.fortup_val[0]) {\
    do { var *++iv.fortup_val;
#define FORTUPI(var,tup,ndx,iv) \
    iv.fortup_val = tup;\
    if(iv.fortup_count = (int) iv.fortup_val[0]) {\
    ndx = 0;\
    do { ndx++; var *++iv.fortup_val; 
#define ENDFORTUP(iv) }	  while(--iv.fortup_count); } 

/* for iteration over tuples */
typedef struct Fortup {
  int	 fortup_count;
  char	** fortup_val;
} Fortup;

typedef char **Set;

/* apr 86 - modify to use tuples to represent sets */
/* This package provides the following procedures:

 set_arb(sp)	pick arbitrary element from set
 set_copy(sp)	return copy of small set
 set_del(sp,n)	delete n from small set sp,return pointer to result
 set_get(sp,n)	return n-th element of set
 set_free(sp)	free space allocated for set
 set_from(sp)	pick arbitrary element from set and remove it
 set_init(n)	set up initial set space for n sets
 set_less(sp1,n) remove element n from set sp1
 set_new(n)	allocate new small set with room for n elements
 set_new1(e)	allocate new small set with single element e
 set_mem(n,sp)	see if n member of small set sp
 set_print(sp)	print small set on standard output (debug assist)
 set_size(sp)	return current size of small set
 set_union(sp1,sp2) union of two small sets
 set_with(sp,n) insert n in small set sp, return pointer to result
 
 to iterate over set, (Setl (for var in tup)use
  SETL	(for var in tup) becomes:

  Forset fors;
  ...
  FORSET(var,tup, fors)
   ...
  ENDFORSET(fors)

*/

/* variables used to control iteration over sets have types Forset */


#define FORSET(var,tup,iv) \
    iv.fortup_val = tup;\
    if(iv.fortup_count = (int) iv.fortup_val[0]) {\
    do { var *++iv.fortup_val;
#define ENDFORSET(iv) }	  while(--iv.fortup_count); } 

/* for iteration over sets (as tuples) */
typedef struct Forset {
  int	 fortup_count;
  char	** fortup_val;
} Forset;

#ifdef EXPORT
#define tup_size(t)	(*(int *)(t))
#define set_size(s)	(*(int *)(s))
#endif
#endif

