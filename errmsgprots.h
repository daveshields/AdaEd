/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

void errmsg_id(char *, Symbol, char *, Node);
void errmsg_str(char *, char *, char *, Node);
void errmsg_nat(char *, Symbol, char *, Node);
void errmsg_type(char *, Symbol, char *, Node);
void errmsg_nval(char *, Node, char *, Node);
void errmsg_id_id(char *, Symbol name1, Symbol name2, char *, Node);
void errmsg_id_type(char *, Symbol, Symbol, char *, Node);
void errmsg_nat_id_str(char *, Symbol, Symbol, char *, char *, Node);
void errmsg_str_id(char *, char *, Symbol, char *, Node);
void errmsg_str_num(char *, char *, int, char *, Node);
void pass1_error_id(char *, Symbol, char *, Node);
void pass1_error_str(char *, char *, char *, Node);
void pass1_error_l(char *msg1, char *msg2, char *, Node);
char *build_full_names(Set);
void errmsg(char *, char *, Node);
void warning(char *, Node);
