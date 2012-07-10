/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

void putsymref(IFILE *, char *, Symbol);
long write_ais(int);
void write_stub(Stubenv, char *, char *);
void write_tre(int, int, char *);
void write_end(IFILE *, long);
void cleanup_files();
void ifdelete(char *);
