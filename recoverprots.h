/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

*/

char *err_message(int, struct prsstack *);
int prs_block(struct two_pool *, struct two_pool *);
int prs_check(struct two_pool *, int *, int);
int scope_recovery(int, int, int *);
int stack_size(struct two_pool *);
int spell(char *, char *);
void try_deletion();
void try_insertion();
void try_merge(struct prsstack *, struct prsstack *);
void try_substitution();

