/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* action.c - temporarily pulled out from adaprs.c */

#include "hdr.h"
#include "ada.h"
#include "miscprots.h"
#include "actionprots.h"


/* Action: Return an action corresponding to a given state and input 
   symbol. Given a state and input symbol, we get a unique value uniquevalue,
   which we use to get a hash value hashvalue. We use hashvalue as an index
   into act_tab1. If the entry is 0, we return the default action for the
   state. If the table entry is < NUM_ACTIONS, then we return either
   the table entry if act_tab2 gives uniquenum at location hashvalue, or
   the default reduction if not. Otherwise we go through act_tab2 starting
   at index uniquevalue until we find uniquevalue or 0, and return what
   is found in act_tab1 at this location or the default reduction,
   respectively. A shift is indicated by the new state to go to after the
   shift, and a reduction is indicated by the rule number + NUM_STATES. */


int action(int state, int sym)									/*;action*/
{
	long uniquenum;
	int hashvalue;
	int i;
	int aval;
#ifdef DEBUGACT
	printf("action state %d sym %d\n", state, sym); /*DEBUG*/
#endif
	if (state < 0) {
#ifdef DEBUG
		printf("action: fatal error state negative %d\n", state);
#endif
		exitp(RC_INTERNAL_ERROR);
	}
	if (sym < 0) {
#ifdef DEBUG
		printf("action: fatal error sym negative %d\n", sym);
#endif
		exitp(RC_INTERNAL_ERROR);
	}
#ifdef DEBUGACT
	uniquenum = state;
	printf("uniq = state %ld\n", uniquenum);
	uniquenum *= NUM_INPUTS;
	printf("uniq = NUM_INT %ld\n", uniquenum);
	uniquenum += sym;
	printf("uniq += sym %ld\n", uniquenum);
	hashvalue = uniquenum % TABLE_SIZE;
	printf("action hash long %ld becomes %d\n", uniquenum, hashvalue);
	aval = act_tab1[hashvalue];
	printf("initial act_tab1 value for %d is %d\n", hashvalue, aval);
	if (act_tab1[hashvalue] == 0) {
		aval = def_action[state - 1];
		printf("action 1st case %d\n", aval);
		return(aval);
	}
	if (act_tab1[hashvalue] < NUM_ACTIONS) {
		if (act_tab2[hashvalue]== uniquenum) {
			aval = act_tab1[hashvalue];
			printf("action 2nd case %d\n", aval);
			return aval;
		}
		else {
			aval = def_action[state-1];
			printf("acton 3rd case %d\n", aval);
			return aval;
		}
	}
	for (i = act_tab1[hashvalue] - NUM_ACTIONS; act_tab2[i] != 0; i++) {
		if (act_tab2[i] == uniquenum) {
			aval = act_tab1[i];
			printf("action 4th case %d %d\n", i, aval);
			return aval;
		}
	}
	aval = def_action[state-1];
	printf("action 5th case %d\n", aval);
	return(aval);
#else
	uniquenum = (long) state * NUM_INPUTS + sym;
	hashvalue = (int)uniquenum % TABLE_SIZE;
	aval = act_tab1[hashvalue];
	if (aval == 0)
		return(def_action[state - 1]);
	if (aval < NUM_ACTIONS)
		return((act_tab2[hashvalue] == uniquenum) ? aval : def_action[state-1]);
	for (i = act_tab1[hashvalue] - NUM_ACTIONS; act_tab2[i] != 0; i++)
		if (act_tab2[i] == uniquenum)
			return(act_tab1[i]);
	return(def_action[state - 1]);
#endif
}
