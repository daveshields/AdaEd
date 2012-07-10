/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#ifndef DBLE_MUL
void dble_mul();
#endif
#ifndef DBLE_RDIV
void dble_rdiv();
#endif
#ifndef WORD_ADD
extern int word_add(int, int, int *);
#endif
#ifndef WORD_MUL
int word_mul(int, int, int *);
#endif
#ifndef WORD_SUB
extern int word_sub(int, int, int *);
#endif
#ifndef LONG_ADD
long long_add(long, long, int *);
#endif
#ifndef LONG_MUL
long long_mul(long, long, int *);
#endif
#ifndef LONG_SUB
long long_sub(long, long, int *);
#endif
#ifndef MOVE_MEM
void move_mem(int *, int *, int);
#endif
