/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

int int_main();
#ifdef ALIGN_WORD
int get_int(int *);
long get_long(long *);
#endif
int allocate_new_heap();
