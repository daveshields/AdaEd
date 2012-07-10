/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

*/

void free_everything(Node);
struct two_pool *initlist(Node);
void append(Node, Node);
void prepend(Node, Node);
Node binary_operator(Node, Node, Node);
Node unary_operator(Node, Node);
int check_expanded_name(Node);
void check_discrete_range(Node);
void pragmalist_warning(Node);
void check_pragmas(Node, int (*allowed_test)(int));
int isoverloadable_op(char *);
int immediate_decl_pragmas(int );
int compilation_pragmas(int );
int after_libunit_pragmas(int );
int task_pragmas(int );
int task_repr_pragmas(int );
int context_pragmas(int );
int null_pragmas(int);
void check_choices(Node, char *);
Tuple remove_duplicate_labels(Tuple);
void ins_as_line_no(Node);
void end_as_line_no(Node, struct prsstack *);
unsigned long labelshash(Node);
void newlabels(Node, Tuple);
Tuple getlabels(Node);
void erase_labels(Node);
void free_labels();
#ifdef DEBUG
void dump_labels(Node);
#endif 
void insert_1child(Node, Node);
void insert_2child(Node, Node, Node);
void insert_3child(Node, Node, Node, Node);
void insert_4child(Node, Node, Node, Node, Node);
