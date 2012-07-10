/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

void display_node(Node, int);
void explorast (Node);
void display_node_list (Tuple, int);
void display_symbol_list (Tuple, int);
void display_value (Node);
void display_signature (Symbol);
void give_node_reference (Node);
void give_symbol_reference (Symbol);
void zpadr(char *, char *);
void zpstr(char *);
void zpcon(Const);
void zprat(Rational);
void zpnod(Node);
void zpnods(int, int);
void zpn(int, int);
void zpdnod();
void zpnodrefa(char *, Node);
void zpdset();
void zpset(Set);
void zpdsetsym();
void zpsetsym(Set);
void zpsigs(int, int);
void zpsig(Symbol);
void zpsigt();
void zptup(Tuple);
void zpdtup();
void zpsym(Symbol);
void zpsymrefa(char *, Symbol);
void zpsyms(int, int);
void zpdsym();
void zpdcl(Declaredmap);
void zpddcl();
void zppdcl(Private_declarations);
void zppsetsym(Set);
void zptupsym(Tuple);
void zptupnod(Tuple);
void zpsmap(Symbolmap);
void zpdmap(Nodemap);
void trapn(Node);
void traps(Symbol);
void trapini();
void trapset(int, int, int, int);
Node zgetnodptr(int, int);
Symbol zgetsymptr(int, int);
void zpsymref(Symbol);
void zpnodref(Node);
void zpunit(int);
void zpint(int);
