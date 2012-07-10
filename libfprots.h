/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

int getint(IFILE *, char *);
int getnum(IFILE *, char *);
int getchr(IFILE *, char *);
long getlong(IFILE *, char *);
char *getstr(IFILE *, char *);
long read_init(IFILE *);
long read_next(IFILE *, long);
void putnum(IFILE *, char *, int);
void putpos(IFILE *, char *, int);
void putstr(IFILE *, char *, char *);
void putchr(IFILE *, char *, int);
