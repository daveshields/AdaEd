/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

char *set_arb(Set);
Set set_copy(Set);
Set set_del(Set, char *);
void set_free(Set);
char *set_from(Set);
Set set_less(Set, char *);
Set set_new(int);
Set set_new1(char *);
int set_mem(char *, Set);
int set_size(Set);
int set_subset(Set, Set);
Set set_union(Set, Set);
Set set_with(Set, char *);
void tup_init();
Tuple tup_add(Tuple, Tuple);
Tuple tup_copy(Tuple);
Tuple tup_exp(Tuple, unsigned int);
void tup_free(Tuple);
char *tup_frome(Tuple);
char *tup_fromb(Tuple);
int tup_mem(char *, Tuple);
int tup_memi(char *, Tuple);
int tup_memstr(char *, Tuple);
Tuple tup_new(int);
Tuple tup_new1(char *);
Tuple tup_new2(char *, char *);
int tup_size(Tuple);
Tuple tup_with(Tuple, char *);
Set set_diff(Set, Set);
