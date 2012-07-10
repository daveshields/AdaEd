/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

int *int_abs(int *);
int *int_add(int *, int *);
int int_eql(int *, int *);
int *int_exp(int *, int *);
int *int_fri(int);
int *int_frs(char *);
int int_geq(int *, int *);
int int_gtr(int *, int *);
int int_len(int *);
int int_leq(int *, int *);
int int_lss(int *, int *);
int *int_mod(int *, int *);
int *int_mul(int *, int *);
int int_neq(int *, int *);
int *int_quo(int *, int *);
int *int_rem(int *, int *);
int *int_sub(int *, int *);
int int_toi(int *);
#ifdef MAX_INTEGER_LONG
long int_tol(int *);
#else
long int_tol(int *);
#endif
char *int_tos(int *);
int *int_umin(int *);
int value(char *);
int *int_con(int);
int *int_copy(int *);
int int_eqz(int *);
int int_nez(int *);
#ifdef DEBUG
void int_print(int *);
#endif
void rat_init();
Rational rat_new(int *, int *);
#ifdef DEBUG
void rat_print(Rational);
#endif
Rational rat_abs(Rational);
Rational rat_add(Rational, Rational);
Rational rat_div(Rational, Rational);
int rat_eql(Rational, Rational);
Rational rat_exp(Rational, int *);
Rational rat_fri(int *, int *);
Rational rat_frr(double);
Rational rat_frs(char *);
int rat_geq(Rational, Rational);
int rat_gtr(Rational, Rational);
int rat_leq(Rational, Rational);
int rat_lss(Rational, Rational);
Rational rat_mul(Rational, Rational);
int rat_neq(Rational, Rational);
Rational rat_rec(Rational);
Rational rat_red(int *, int *);
Rational rat_sub(Rational, Rational);
double rat_tor (Rational, int);
int rat_toi(Rational);
long rat_tol(Rational);
Rational rat_umin(Rational);
