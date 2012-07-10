/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "ifile.h"

char *smalloc(unsigned);
#ifdef DEBUG
void smalloc_list();
#endif
int is_smalloc_block(char *);
void capacity(char *);
#ifdef CHAOS
void chaos(char *);
#else
void exit_internal_error();
#endif
void exitp(int);
char *ecalloc(unsigned, unsigned);
char *emalloc(unsigned);
char *erealloc(char *, unsigned);
char *strjoin(char *, char *s2);
int streq(char *, char *);
char *substr(char *, int, int);
#ifdef nogetopt
int getopt(int, char **, char *);
#endif
char *greentime(int);
FILE *efopenl(char *, char *, char *, char *);
FILE *efopen(char *, char *, char *);
void efree(char *);
int strhash(char *);
char *unit_name_type(char *);
#ifdef BSD
char *strchr(const char *, int);
char *strrchr(const char *, int);
#endif
char *libset(char *);
char *ifname(char *, char *);
IFILE *ifopen(char *, char *, char *, int);
static void openerr(char *, char *);
void ifclose(IFILE *);
void ifoclose(IFILE *);
long ifseek(IFILE *, char *, long, int);
long iftell(IFILE *);
char *emalloct(unsigned, char *);
#ifndef EXPORT
char *malloct(unsigned, char *);
char *ecalloct(unsigned, unsigned, char *);
char *erealloct(char *, unsigned, char *);
void efreet(char *, char *);
#endif
char *predef_env();
char *get_libdir();
char *parsefile(char *, int *, int *, int *);
