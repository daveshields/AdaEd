/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

Declaredmap getdcl(IFILE *);
Symbol getsym(IFILE *, char *);
Node getnodptr(int, int);
Node getnodref(IFILE *, char *);
char *read_ais(char *, int, char *, int, int);
int read_stub(char *, char *, char *);
int read_lib();
void load_tre(IFILE *, int);
Symbol getsymref(IFILE *, char *);
void retrieve_generic_tree(Node, Node);
char *lib_aisname();
void get_unit_unam(IFILE *, Symbol);
