/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#define FAA(i, j)	(((i) = (i)+(j)) - (j))
#define FAS(i, j)	(fetch_and_store((int *) i, (int) j))
#define FAS_Q(i,j)	((struct q_item *)pointer_fetch_and_store(         \
 				(char **)i,(char *)j ))
#define FAS_RTS(i,j)	((struct rts_item *) pointer_fetch_and_store(       \
 				(char **)i,(char *)j ))
#define TAS(i)		(((i)>=1) ? ((i)=1) :(((i) = 1) ? 0 : 0))
#define TAR(i)		(((i)>=1) ? ((i)=1) :(((i) = 1) ? 0 : 0))

#define INC(i)		(FAA((i), 1))
#define DEC(i)		(FAA((i),-1))
#define INCC(i)		(increment(&(i)))
#define DECC(i)		(decrement(&(i)))
