/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* This file contains various functions needed for reduce actions */

#include "hdr.h"
#include "ada.h"
#include "adared.h"
#include "setprots.h"
#include "smiscprots.h"
#include "prsutilprots.h"
#include "errsprots.h"
#include "adalexprots.h"
#include "pspansprots.h"
#include "reduceprots.h"

static void pragma_warning(Node);
static int in_label_set(Node, Tuple);
static int is_pragma(int);

void free_everything(Node n)
{
}

struct two_pool *initlist(Node node)				/*;initlist*/
{
	/* Allocate a single list structure (struct two_pool), set its data to
	 * be a pointer to the node given, and set its link field to point
	 * to itself, since tree node lists are circular.
	 */
	struct two_pool *tmp;

	tmp = TALLOC();
	tmp->val.node = node;
	tmp->link = tmp;
	return(tmp);
}

void append(Node orignode, Node node)			/*;append*/
{
	/* Append node to list within orignode */

	if (N_LIST(orignode) == (Tuple)0) 
		N_LIST(orignode) = tup_new1((char *)node);
	else
		N_LIST(orignode) = tup_with(N_LIST(orignode), (char *)node);
}

void prepend(Node node, Node orignode)		/*;prepend*/
{
	/* Prepends list within orignode with node */

	Tuple beglist = tup_new1((char *)node);

	if (N_LIST(orignode) == (Tuple)0)
		N_LIST(orignode) = beglist;
	else
		N_LIST(orignode) = tup_add(beglist, N_LIST(orignode));
}

Node binary_operator(Node optr, Node expr1, Node expr2)		/*;binary_operator*/
{
	/* Set up the AST node for a binary operator. */

	Node node, arg_list_node;

	node = node_new(as_op);
	arg_list_node = node_new(as_list);
	N_LIST(arg_list_node) = tup_new2((char *)expr1, (char *)expr2);
	insert_2child(node, optr, arg_list_node);
	return(node);
}

Node unary_operator(Node optr, Node expr)				/*;unary_operator*/
{
	/* Set up the AST node for a unary operator. */
	Node node, arg_list_node;

	node = node_new(as_un_op);
	arg_list_node = node_new(as_list);
	N_LIST(arg_list_node) = tup_new1((char *)expr);
	insert_2child(node, optr, arg_list_node);
	return(node);
}

int check_expanded_name(Node name)			/*;check_expanded_name*/
{
	/* Make sure an expanded name node is valid. */

#define sub_expanded_name (N_AST1(name))
	return((N_KIND(name) == as_selector) ? 
	  check_expanded_name(sub_expanded_name) : (N_KIND(name)== as_simple_name));
#undef sub_expanded_name
}

void check_discrete_range(Node discrete_range) /*;check_discrete_range*/
{
	/* Check whether a discrete range node is valid. */

	switch (N_KIND(discrete_range))
	{
	case as_range_expression :
#define name (N_AST1(discrete_range))
		if (!check_expanded_name(name))
			syntax_err(SPAN(discrete_range),
			  "Invalid discrete_range specification");
		else
			N_KIND(discrete_range) = as_name;
		break;
#undef name
	case as_range_attribute :
	case as_subtype :
		break;
	default :
		syntax_err(SPAN(discrete_range),
		  "Invalid discrete_range specification");
	}
}

static void pragma_warning(Node pragma_node)			/*;pragma_warning*/
{
	/* Give a warning that a pragma is ignored. */

	char msg[MAXLINE + 30];

#define id (N_AST1(pragma_node))
	sprintf(msg,"Pragma %s is ignored", namelist(N_ID(id)));
	prs_warning(SPAN(pragma_node),msg);
#undef id
}

void pragmalist_warning(Node list_node)		/*;pragmalist_warning*/
{
	/* For all nodes in the list of list_node give a warning the the pragma
	 * is invalid.
	 */

	Node tmp_node;
	Fortup ft1;

	if (N_LIST(list_node) != (Tuple)0) {
		FORTUP(tmp_node = (Node), N_LIST(list_node), ft1);
	    	pragma_warning(tmp_node);
		ENDFORTUP(ft1);
	}
}

void check_pragmas(Node pragma_node, int (*allowed_test)(int))
													/*;check_pragmas*/
{
	/* Check that a pragma is valid. */

	Tuple new_list = tup_new(0);
	Node tmp_node;
	Fortup ft1;
	int id;

	if (N_LIST(pragma_node) != (Tuple)0) {
		FORTUP(tmp_node = (Node), N_LIST(pragma_node), ft1);
			id = N_ID(N_AST1(tmp_node));
			if (is_pragma(id) && (*allowed_test)(id - MIN_PRAGMA)) {
				if (strcmp(namelist(id),"PRIORITY")
				  && strcmp(namelist(id),"ELABORATE")
				  && strcmp(namelist(id),"INTERFACE")) {
					pragma_warning(tmp_node);
				}
				else
					new_list = tup_with(new_list, (char *)tmp_node);
			}
			else if (is_pragma(id) && ispredef_pragma[id - MIN_PRAGMA]) {
				char msg[200];

				sprintf(msg,"Pragma %s is not valid in this context",
				  namelist(id));
				prs_warning(SPAN(tmp_node),msg);
			}
			else if (!(is_pragma(id) && isimpldef_pragma[id - MIN_PRAGMA])
			  && strcmp(namelist(id),"OPTIMIZE")) {
				pragma_warning(tmp_node);
			}
			else
				new_list = tup_with(new_list, (char *)tmp_node);
		ENDFORTUP(ft1);
		N_LIST(pragma_node) = new_list;
	}
}

int isoverloadable_op(char *str)				/*;isoverloadable_op*/
{
	/* Check whether a string represnts an overloadable operator by
	 * comparing against all overloadable operators.
	 */

	char tmp[MAXLINE + 1];
	int i;

	strcpy(tmp, str);
	convtolower(tmp);
	for (i = 0; i < NUMOVERLOADOPS; i++)
		if (!strcmp(tmp, overloadable_operators[i]))
			return(1);
	return(0);
}

/* The following functions are for passing to check_pragmas */

int immediate_decl_pragmas(int p)				/*;immediate_decl_pragmas*/
{
	return(isimmediate_decl_pragma[p]);
}

int compilation_pragmas(int p)					/*;compilation_pragmas*/
{
	return(iscompilation_pragma[p]);
}

int after_libunit_pragmas(int p)				/*;after_libunit_pragmas*/
{
	return(isafter_libunit_pragma[p]);
}

int task_pragmas(int p)							/*;task_pragmas*/
{
	return(istask_pragma[p]);
}

int task_repr_pragmas(int p)					/*;task_repr_pragmas*/
{
	return(istask_pragma[p] || isrepr_pragma[p]);
}

int context_pragmas(int p)						/*;context_pragmas*/
{
	return(iscontext_pragma[p]);
}

int null_pragmas(int i)									/*;null_pragmas*/
{
	return(i = 0);
}

void check_choices(Node alt_node, char *source)	/*;check_choices*/
{
	Tuple choice_list, others_indices = tup_new(0);
	Node tmp_node, tmp_node2, last_alt = (Node) 0;
	Fortup ft1, ft2;
	int choice_flag = 0;

	FORTUP(tmp_node = (Node), N_LIST(alt_node), ft1);
	    if (N_KIND(tmp_node) != as_pragma) {
			choice_list = N_LIST(N_AST1(tmp_node));
			if (tup_size(choice_list) > 1) {
				FORTUP(tmp_node2 = (Node), choice_list, ft2);
					if (N_KIND(tmp_node2) == as_others
					  || N_KIND(tmp_node2) == as_others_choice) {
						char msg[90];

						sprintf(msg,"The choice OTHERS must appear alone in %s",
						  source);
						syntax_err(SPAN(tmp_node2),msg);
						choice_flag = 1;
						break;
					}
				ENDFORTUP(ft2);
			}
		   	if (!choice_flag) {
				if (N_KIND((Node)choice_list[1]) == as_others
				  || N_KIND((Node)choice_list[1]) == as_others_choice)
					others_indices = tup_with(others_indices, (char *)tmp_node);
			}
			else
				choice_flag = 0;
			last_alt = tmp_node;
		}
	ENDFORTUP(ft1);

	FORTUP(tmp_node = (Node), others_indices, ft1); {
		Node choice;
		char msg[90];

		if (tmp_node == last_alt)
			continue;
		choice = (Node)N_LIST(N_AST1(tmp_node))[1];
		sprintf(msg,"The choice OTHERS must appear last in %s",source);
		syntax_err(SPAN(choice),msg);
	} ENDFORTUP(ft1);
/*
	if (others_indices != (struct two_pool *)0 )
		TFREE(others_indices->link,others_indices);
*/
}

Tuple remove_duplicate_labels(Tuple label_list)
											/*;remove_duplicate_labels*/
{
	Tuple new_label_list = tup_new(0), label_id_set = tup_new(0);
	Fortup ft1, ft2;
	Node tmp_node, tmp_node2, node, label;

	FORTUP(tmp_node = (Node), label_list, ft1);
	    if (N_KIND((node = tmp_node)) == as_simple_name) {
			if (in_label_set(node, label_id_set))
				syntax_err(SPAN(node),"Duplicate label name");
			else {
				/* new_label_list = concatl(new_label_list,initlist(node)); */
				label_id_set = tup_with(label_id_set, (char *)node);
			}
			new_label_list = tup_with(new_label_list, (char *)node);
		}
		else {
			FORTUP(tmp_node2 = (Node), N_LIST(node), ft2);
		    	label = tmp_node2;
				if (in_label_set(label,label_id_set))
					syntax_err(SPAN(label),"Duplicate label name");
				else
					label_id_set = tup_with(label_id_set, (char *)label);
			ENDFORTUP(ft2);
		}
	ENDFORTUP(ft1)
/*
	if (label_id_set != (struct two_pool *)0)
		TFREE(label_id_set->link,label_id_set);
	if (label_list != (struct two_pool *)0)
		TFREE(label_list->link,label_list);
*/
	return(new_label_list);
}

static int in_label_set(Node label, Tuple label_set)
														/*;in_label_set*/
{
	int val = N_ID(label);
	Node tmp_node;
	Fortup ft1;

	FORTUP(tmp_node = (Node), label_set, ft1);
		if (N_ID(tmp_node) == val)
			return(1);
	ENDFORTUP(ft1);
	return(0);
}

void ins_as_line_no(Node node)				/*;ins_as_line_no*/
{
	/* insert as_line_no nodes before each item in declarative/stmt list */

	Tuple new_list = tup_new(0);
	Node tmp_node;
	Fortup ft1;
	Node line_node;
	Span line_node_span;


	FORTUP(tmp_node = (Node), N_LIST(node), ft1);
		line_node = node_new (as_line_no);
		line_node_span = get_left_span_p(tmp_node);
		N_ID(line_node) = line_node_span->line;
		set_span(line_node,line_node_span);
		/* Insert a new node with the as_line_no between dec_list and its 
				predecessor */
		new_list = tup_with(new_list, (char *)line_node);
		new_list = tup_with(new_list, (char *)tmp_node);
	ENDFORTUP(ft1);
	N_LIST(node) = new_list;
}

void end_as_line_no(Node list_node, struct prsstack *next_token)
													/*;end_as_line_no*/
{
	/* add an as_line_no node to end of statement list this is the line
	 * number of the token following the sequence of statements
	 */

	Node  line_node;

	if (N_LIST(list_node) != (Tuple)0) {
		line_node = node_new (as_line_no);
		N_ID(line_node) = next_token->ptr.token->span.line ;
		set_span(line_node, make_span(N_ID(line_node),
		  next_token->ptr.token->span.col));
		N_LIST(list_node) = tup_with(N_LIST(list_node), (char *)line_node);
	}
}

#define LABELSMAPSIZE 50

struct labelsmap {
	Node node;
	Tuple list;
	struct labelsmap *link;
};

struct labelsmap *nodetolabelstable[LABELSMAPSIZE]; /* Table for Labels map */
/* List of free label structures */
static struct labelsmap *deadlabels = (struct labelsmap *)0;

unsigned long labelshash(Node node)			/*;labelshash*/
{
	/* The hash function from nodes to integers */
	return( ((unsigned long) node) % LABELSMAPSIZE);
}

void newlabels(Node node, Tuple list)		/*;newlabels*/
{
	/* Add node to the map, and initialize its labels list to list.
	 * Storage allocation is done using malloc/free structure list.
	 */

	int pos;
	struct labelsmap *labelnode;

	pos = (int)labelshash(node);
	if (deadlabels == (struct labelsmap *)0)
		labelnode = (struct labelsmap *)malloc(sizeof(struct labelsmap));
	else {
		labelnode = deadlabels;
		deadlabels = deadlabels->link;
	}
	labelnode->link = nodetolabelstable[pos];
	nodetolabelstable[pos] = labelnode;
	labelnode->node = node;
	labelnode->list = list;
}

Tuple getlabels(Node node)				/*;getlabels*/
{
	/* Return the list of labels corresponding to a given node. If
	 * The map is not defined for a node, NULL is returned.
	 */

	struct labelsmap *tmp;

	for (tmp = nodetolabelstable[labelshash(node)];
	  tmp != (struct labelsmap *)0 && tmp->node != node; tmp = tmp->link);
	return((tmp == (struct labelsmap *)0) ? tup_new(0) : tmp->list);
}

void erase_labels(Node node)						/*;erase_labels*/
{
	/* Remove a node from the labels map, freeing the structure used for
	 * that node's labels.
	 */

	struct labelsmap *tmp, *last;
	int pos;

	pos = (int)labelshash(node);
	for (tmp = nodetolabelstable[pos], last = (struct labelsmap *)0; 
	  tmp != (struct labelsmap *)0 && tmp->node != node;
	  last = tmp, tmp = tmp->link);
	if (tmp == (struct labelsmap *)0)
		return;
	if (last == (struct labelsmap *)0)
		nodetolabelstable[pos] = tmp->link;
	else
		last->link = tmp->link;
	tmp->link = deadlabels;
	deadlabels = tmp;
/*
	if (tmp->list != (struct two_pool *)0)
		TFREE(tmp->list->link,tmp->list);
*/
}

void free_labels()											/*;free_labels*/
{
	/* Remove all entries in the labels map. */
	int i;
	struct labelsmap *curr;

	for (i = 0; i < LABELSMAPSIZE; i++)
		if (nodetolabelstable[i] != (struct labelsmap *)0) {
			for (curr = nodetolabelstable[i]; curr->link!=NULL; curr=curr->link)
				if (curr->list != NULL)
					;/*TFREE(curr->list->link,curr->list);*/
			curr->link = deadlabels;
			deadlabels = nodetolabelstable[i];
			nodetolabelstable[i] = NULL;
		}
}

static int is_pragma(int n)				 				/*;is_pragma*/
{
	/* Metaware miscompiles if:
	return (MIN_PRAGMA <= (n) && (n) <= MAX_PRAGMA);
     * so reorder first test until MetaWare compiler bug fixed
     */
	return ((n)>=MIN_PRAGMA  && (n) <= MAX_PRAGMA);
}

void insert_1child(Node into, Node a1)
{
	N_AST1(into) = a1;
}
void insert_2child(Node into, Node a1, Node a2)
{
	N_AST1(into) = a1;
	N_AST2(into) = a2;
}
void insert_3child(Node into, Node a1, Node a2, Node a3)
{
	N_AST1(into) = a1;
	N_AST2(into) = a2;
	N_AST3(into) = a3;
}
void insert_4child(Node into, Node a1, Node a2, Node a3, Node a4)
{
	N_AST1(into) = a1;
	N_AST2(into) = a2;
	N_AST3(into) = a3;
	N_AST4(into) = a4;
}
