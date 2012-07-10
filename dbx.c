/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* interface to dbx for sem debugging */
/* interface to dbx for sem debugging */
#include "hdr.h"
#include "libhdr.h"
#include "vars.h"
#include "ifile.h"
#include "setprots.h"
#include "arithprots.h"
#include "sspansprots.h"
#include "chapprots.h"
#include "librprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "dbxprots.h"

#ifndef EXPORT

typedef struct explored
{
	short genre;    /* discriminant : is explored a node or a symbol ? */

	union {
		Node   n;
		Symbol s;
	} addr;
} explored;

#define UNDEFINED_STEP 99
#define EXIT_STEP 100
#define NODE_GENRE 0
#define SYMBOL_GENRE 1



int zpadr_opt = 1;
Symbol zsym;
Set	zset;
Node	znod;
Declaredmap	zdcl;
Tuple ztup;
void give_node_reference(Node);
void give_symbol_reference(Symbol);
void zpnodrefa(char *, Node);
void zpset(Set);
void zpsig(Symbol);
void zpsigt();
void zptup(Tuple);
void zpsetsym(Set);
void zpsym(Symbol);
void zpsymrefa(char *, Symbol);
void zpsymref(Symbol);
void zpnodref(Node);
int analyze(char *, explored, int *, int *);

static int adrflag = 1; /* non zero to print address values */
static int stack_ptr = 0;
static explored stack[ 100 ];
static void push(explored);
static explored pop();
static void display_symbol(Symbol);
static void zpcon1(Const);
static void zprat1(Rational);


/*
 * The purpose of this program is to provide the one who is not familiar
 * with the structure of the AST with a tool which permits him to travel
 * from one node to his eventual father or son (we assume that the
 * beginning of the exploration will take place at the root of the AST .)
 * and focus on the nodes he wants to examine more precisely in a readable
 * way . 
 */


static void push (explored site)				/*;push*/
{
	stack [ stack_ptr++ ] = site;
}

static explored pop ()					/*;pop*/
{
	return (stack [ --stack_ptr ]);
}

static void display_symbol(Symbol symbol_explored)		/*;display_symbol*/
{
	short nature;

	system ("clear");

	if (symbol_explored == (Symbol)0)
		printf ("(Symbol)0\n");
	else {
		printf("NATURE %s        %d \n\n",
		  nature_str (NATURE (symbol_explored)), symbol_explored);
		printf("TYPE_OF %s   %d\n",
		  nature_str(NATURE(TYPE_OF(symbol_explored))),
		  TYPE_OF(symbol_explored));
		printf("ALIAS   %s   %d\n",
		  nature_str(NATURE(ALIAS(symbol_explored))), ALIAS(symbol_explored));
		printf("SIGNATURE :\n");
	
		if (SIGNATURE (symbol_explored) != ((Tuple)0))
			zptup(SIGNATURE (symbol_explored));
		else
			printf("empty_tuple\n");

		if (SCOPE_OF(symbol_explored))
			printf("SCOPE_OF %s   %d\n",
			  nature_str(NATURE(SCOPE_OF(symbol_explored))),
			  SCOPE_OF(symbol_explored));
		else
			printf("No scope.\n");

		printf("OVERLOADS :\n");
		if (OVERLOADS (symbol_explored) != ((Tuple)0)) {
			nature = NATURE(symbol_explored);
			if (nature == na_enum)
				printf(" literal map %d\n", OVERLOADS(symbol_explored));
			else if (nature == na_package || nature == na_package_spec
			  || nature == na_generic_package_spec
			  || nature == na_generic_package || nature == na_task_type
			  || nature == na_task_obj)
				printf(" private declarations %d\n",
				    OVERLOADS(symbol_explored));
			else 
				display_symbol_list  (OVERLOADS (symbol_explored), 1);
		}
		else
			printf ("empty_set\n");
		printf("DECLARED %d\n", DECLARED (symbol_explored));
		if (ORIG_NAME (symbol_explored) != (char *)0)
			printf("ORIG_NAME %s\n", ORIG_NAME (symbol_explored));
		printf("SEQ %d\n", S_SEQ (symbol_explored));
		printf("UNIT %d\n", S_UNIT (symbol_explored));
		printf("TYPE_ATTR %d\n", TYPE_ATTR (symbol_explored));
		if (MISC (symbol_explored) != (char *)0)
			printf("MISC %s\n", MISC (symbol_explored));
		printf("TYPE_KIND %d\n", TYPE_KIND (symbol_explored));
		printf("TYPE_SIZE %d\n", TYPE_SIZE (symbol_explored));

		if (INIT_PROC(symbol_explored))
			printf("INIT_PROC %s   %d\n",
			  nature_str(NATURE(INIT_PROC(symbol_explored))),
			  INIT_PROC(symbol_explored));
		else printf("INIT_PROC = 0\n");

		printf("ASSOCIATED_SYMBOLS :\n");
		if (ASSOCIATED_SYMBOLS (symbol_explored) != ((Tuple)0))
			display_symbol_list (ASSOCIATED_SYMBOLS (symbol_explored), 1);
		else
			printf ("empty_tuple\n");
		printf("SEGMENT %d\n", S_SEGMENT (symbol_explored));
		printf("OFFSET %d\n", S_OFFSET (symbol_explored));
		printf("\n");
	}
}

void display_node(Node node_explored, int list_begin)	/*;display_node*/
{
	int kind_explored;

	system ("clear");

	if (node_explored == (Node)0)
		printf ("(Node)0\n");
	else {
		kind_explored = N_KIND (node_explored);

		printf ("kind -> %s  ", kind_str (kind_explored));
		printf ("unit -> %d  ", N_UNIT (node_explored));
		printf ("side -> %d  ", N_SIDE (node_explored));
		printf ("overloaded -> %d  ", N_OVERLOADED (node_explored));
		printf ("sequence -> %d ", N_SEQ (node_explored));
		printf ("\n");
		printf ("%d", kind_explored);

		printf ("\n");
		printf ("\n");

		/*****************/
		/* nu1 component */
		/*****************/
		printf (" nu1 :  ");

		if (N_AST1_DEFINED (kind_explored)) {
			if (N_AST1(node_explored) != (Node)0)
				printf ("AST1 %s \n", kind_str(N_KIND(N_AST1(node_explored))));
			else
				printf ("AST1 (Node)0 \n");
		}
		else 
			printf ("SPAN %d %d \n", N_SPAN0 (node_explored),
			  N_SPAN1 (node_explored));

		printf ("\n");

		/*****************/
		/* nu2 component */
		/*****************/
		printf (" nu2 :  ");

		if (N_AST2_DEFINED (kind_explored)) {
			if (N_AST2(node_explored) != (Node)0)
				printf ("AST2 %s \n",
				    kind_str(N_KIND(N_AST2(node_explored))));
			else
				printf ("AST2 (Node)0 \n");
		}
		else if (N_LIST_DEFINED (kind_explored)) {
			printf ("LIST ");
			if (N_LIST (node_explored) != ((Tuple)0))
				display_node_list (N_LIST (node_explored), list_begin);
			else 
				printf ("empty_tuple\n");
		}
		else { /* (N_VAL_DEFINED (kind_explored) */
			display_value (node_explored);
			printf ("\n");
		}

		printf ("\n");

		/*****************/
		/* nu3 component */
		/*****************/
		printf (" nu3 :  ");

		if (N_AST3_DEFINED (kind_explored)) {
			if (N_AST3(node_explored) != (Node)0)
				printf ("AST3 %s \n", kind_str(N_KIND(N_AST3(node_explored))));
			else
				printf ("AST3 (Node)0 \n");
		}
		else if (N_UNQ_DEFINED (kind_explored))
			printf ("Symbol unq --> %s \n",
			  nature_str(NATURE(N_UNQ(node_explored))));
		else {
			printf ("N_NAMES ");
			if (N_NAMES (node_explored) != ((Set)0))
				display_node_list((Tuple)N_NAMES(node_explored), list_begin);
			else 
				printf ("empty_set\n");
		}

		printf ("\n");

		/*****************/
		/* nu4 component */
		/*****************/
		printf (" nu4 :  ");

		if (N_AST4_DEFINED (kind_explored)) {
			if (N_AST4(node_explored) != (Node)0)
				printf ("AST4 %s \n", kind_str(N_KIND(N_AST4(node_explored))));
			else
				printf ("AST4 (Node)0 \n");
		}
		else if (N_TYPE_DEFINED (kind_explored))
			printf ("Symbol type --> %s \n",
			  nature_str(NATURE(N_TYPE(node_explored))));
		else {
			printf ("N_PTYPES ");
			if (N_PTYPES (node_explored) != ((Set)0))
				display_node_list((Tuple)N_PTYPES(node_explored), list_begin);
			else 
				printf ("empty_set\n");
		}
		printf ("\n");
	}
}

void explorast (Node root)					/*;explorast*/
{
	explored current;
	int      next_step;
	int      list_node;
	int      list_low;
	char     answer[10];

	current.genre = NODE_GENRE;
	current.addr.n = root;
	list_low = 1;

	do {
		if (current.genre == NODE_GENRE)
			display_node   (current.addr.n, list_low);
		else 
			display_symbol (current.addr.s);

		next_step = UNDEFINED_STEP;
		list_node = 0;

		while (next_step == UNDEFINED_STEP) {
			printf (" what shall be the next step  ?  ");
			scanf ("%10s", answer);
			next_step = analyze (answer, current, &list_node, &list_low);
		}

		switch (next_step) {
		case 0 :
			current = pop ();
			break;
		case 11:
			push (current);
			current.genre  = NODE_GENRE;
			current.addr.n = N_AST1 (current.addr.n);
			break;
		case 21:
			push (current);
			current.genre  = NODE_GENRE;
			current.addr.n = N_AST2 (current.addr.n);
			break;
		case 22:
			push (current);
			current.genre  = NODE_GENRE;
			current.addr.n = (Node)((N_LIST(current.addr.n))[list_node]);
			break;
		case 31:
			push (current);
			current.genre  = NODE_GENRE;
			current.addr.n = N_AST3 (current.addr.n);
			break;
		case 33:
			push (current);
			current.genre  = SYMBOL_GENRE;
			current.addr.s = N_UNQ (current.addr.n);
			break;
		case 41:
			push (current);
			current.genre  = NODE_GENRE;
			current.addr.n = N_AST4 (current.addr.n);
			break;
		case 43:
			push (current);
			current.genre  = SYMBOL_GENRE;
			current.addr.s = N_TYPE (current.addr.n);
			break;
		case 91:
			push (current);
			current.genre  = SYMBOL_GENRE;
			current.addr.s = TYPE_OF (current.addr.s);
			break;
		case 92:
			push (current);
			current.genre  = SYMBOL_GENRE;
			current.addr.s = SCOPE_OF (current.addr.s);
			break;
		case 93:
			push (current);
			current.genre  = SYMBOL_GENRE;
			current.addr.s = ALIAS (current.addr.s);
			break;
		case 94:
			push (current);
			current.genre  = SYMBOL_GENRE;
			current.addr.s = INIT_PROC (current.addr.s);
			break;
		case 999:
			break;
		}
	} while (next_step != EXIT_STEP);
}

int analyze (char *way, explored current, int *p_list_num, int *p_list_low)
																	/*;analyze*/
{
	Node   current_node;
	int    current_kind;
	Symbol current_symbol;
	int    current_nature;

	if (current.genre == NODE_GENRE) {
		current_node = current.addr.n;

		if (current_node != (Node)0)
			current_kind = N_KIND (current_node);

		switch (way [0]) {
		case 'f' : 
			if (stack_ptr == 0) {
				printf (" Illegal step : You are at the ROOT\n");
				return (UNDEFINED_STEP);
			}
			else
				return (0);
		case '1' : 
			if ((current_node != (Node)0) && (N_AST1_DEFINED (current_kind)))
				return (11);
			else {
				printf (" Illegal step : AST1 undefined\n");
				return (UNDEFINED_STEP);
			}
		case '2' : 
			if ((current_node != (Node)0) && (N_AST2_DEFINED (current_kind)))
				return (21);
			else {
				printf (" Illegal step : AST2 undefined\n");
				return (UNDEFINED_STEP);
			}
		case '3' : 
			if ((current_node != (Node)0) && (N_AST3_DEFINED (current_kind)))
				return (31);
			else {
				printf (" Illegal step : AST3 undefined\n");
				return (UNDEFINED_STEP);
			}
		case '4' : 
			if ((current_node != (Node)0) && (N_AST4_DEFINED (current_kind)))
				return (41);
			else {
				printf (" Illegal step : AST4 undefined\n");
				return (UNDEFINED_STEP);
			}
		case 'l' : 
			if ((current_node != (Node)0) && (N_LIST_DEFINED (current_kind))) {
				if (atoi (way + 1) > 0
				  && atoi (way + 1) <= tup_size(N_LIST(current_node))) {
					*p_list_num = atoi (way + 1);
					return (22);
				}
				else {
					printf (" Illegal list number\n");
					return (UNDEFINED_STEP);
				}
			}
			else {
				printf (" Illegal step : LIST undefined\n");
				return (UNDEFINED_STEP);
			}
#ifdef PRETTY
		case 's' : 
			if ((current_node != (Node)0) && (N_LIST_DEFINED (current_kind))) {
				if (atoi (way + 1) > 0
				  && atoi (way + 1) <= tup_size(N_LIST(current_node))) {
					*p_list_num = atoi (way + 1);
					regenerate_source1( N_LIST(current_node)[*p_list_num],
					  stack[stack_ptr - 1].addr.n);
					printf("\n");
					return (UNDEFINED_STEP);
				}
				else {
					printf (" Illegal list number\n");
					return (UNDEFINED_STEP);
				}
			}
			else {
				printf (" Illegal step : LIST undefined\n");
				return (UNDEFINED_STEP);
			}
#endif
		case 'v' : 
			if ((current_node != (Node)0) && (N_LIST_DEFINED (current_kind))) {
				if (atoi (way + 1) <= tup_size(N_LIST(current_node))) {
					*p_list_low = atoi (way + 1);
					return (999);
				}
				else {
					printf (" Illegal list number\n");
					return (UNDEFINED_STEP);
				}
			}
			else {
				printf (" Illegal step : LIST undefined\n");
				return (UNDEFINED_STEP);
			}
		case 'u' : 
			if ((current_node != (Node)0) && (N_UNQ_DEFINED (current_kind)))
				return (33);
			else {
				printf (" Illegal step : UNQ undefined\n");
				return (UNDEFINED_STEP);
			}
		case 't' : 
			if ((current_node != (Node)0) && (N_TYPE_DEFINED (current_kind)))
				return (43);
			else {
				printf (" Illegal step : TYPE undefined\n");
				return (UNDEFINED_STEP);
			}
		case 'q' : 
			stack_ptr = 0;
			return (EXIT_STEP);
		case 'h' : 
			printf (" 1     ==> see AST1            \n");
			printf (" 2     ==> see AST2            \n");
			printf (" 3     ==> see AST3            \n");
			printf (" 4     ==> see AST4            \n");
			printf (" l num ==> see list node num   \n");
			printf (" v num ==> see list begin num  \n");
			printf (" u     ==> see unq             \n");
			printf (" t     ==> see type            \n");
			return (UNDEFINED_STEP);
		default  : 
			printf(" I do not understand where you want to go\n");
			return (UNDEFINED_STEP);
		}
	}
	else {
		current_symbol = current.addr.s;

		if (current_symbol != (Symbol)0)
			current_nature = NATURE (current_symbol);

		switch (way [0]) {
		case 'f' : 
			if (stack_ptr == 0) {
				printf (" Illegal step : You are at the ROOT\n");
				return (UNDEFINED_STEP);
			}
			else
				return (0);
		case 't' : 
			return (91);
		case 's' : 
			return (92);
		case 'a' : 
			return (93);
		case 'i' : 
			return (94);
		case 'q' : 
			stack_ptr = 0;
			return (EXIT_STEP);
		case 'h' : 
			printf (" t ==> see TYPE_OF   \n");
			printf (" s ==> see SCOPE_OF  \n");
			printf (" a ==> see ALIAS     \n");
			printf (" i ==> see INIT_PROC \n");
			return (UNDEFINED_STEP);
		default  : 
			printf(" I do not understand where you want to go\n");
			return (UNDEFINED_STEP);
		}
	}
}

void display_node_list (Tuple tup, int low)				/*;display_node_list*/
{
	int high, i, n;

	n = tup_size(tup);
	printf("size : %d\n", n);
	high = low + 10;
	if (high > n)
		high = n;
	for (i = low; i <= high; i++)
		printf("%d 0x%x %d %s \n", i, (int)tup[i], (int)tup[i],
		  kind_str(N_KIND((Node)tup[i])));
}

void display_symbol_list (Tuple tup, int low)		/*;display_symbol_list*/
{
	int high, i, n;

	n = tup_size(tup);
	printf(" size : %d\n", n);
	high = low + 10;
	if (high > n)
		high = n;
	for (i = low; i <= high; i++) {
		printf(" ");
		give_symbol_reference((Symbol)tup[i]);
		zpsymrefa("type_of", TYPE_OF((Symbol)tup[i]));
		zpsymrefa("scope", SCOPE_OF((Symbol)tup[i]));
		if (ORIG_NAME((Symbol)tup[i]) != (char *)0)
			printf(" :%s", ORIG_NAME((Symbol)tup[i]));
		printf("\n");
	}
}

void display_value (Node node_explored)				/*;display_value*/
{
	int kind_explored, constant_kind;
	Const constant_explored;
	Rational rational_explored;
	Tuple tup;
	int i, n;

	kind_explored = N_KIND (node_explored);

	if (kind_explored == as_simple_name
	  || kind_explored == as_int_literal
	  || kind_explored == as_real_literal
	  || kind_explored == as_string_literal
	  || kind_explored == as_character_literal
	  || kind_explored == as_subprogram_stub_tr
	  || kind_explored == as_package_stub
	  || kind_explored == as_task_stub)
		printf ("%s", N_VAL (node_explored));
	else if (kind_explored == as_line_no
	  || kind_explored == as_number
	  || kind_explored == as_predef)
		printf ("%d", (int) N_VAL (node_explored));
	else if (kind_explored == as_mode)
		printf ("%d", (int) N_VAL (node_explored));
	else if (kind_explored == as_ivalue) {
		constant_explored = (Const) N_VAL (node_explored);
		constant_kind = constant_explored -> const_kind;
		if (NATURE(N_TYPE(node_explored)) == na_enum)
			printf ("%s", OVERLOADS(N_TYPE(node_explored))
			  [2*constant_explored->const_value.const_int+1]);
		else {
			if (constant_kind == CONST_INT)
				printf ("%d",  constant_explored->const_value.const_int);
			else if (constant_kind == CONST_REAL)
				printf ("%f", constant_explored->const_value.const_real);
			else if (constant_kind == CONST_UINT)
				printf ("%d", constant_explored->const_value.const_uint);
			else if (constant_kind == CONST_OM)
				printf ("OM");
			else if (constant_kind == CONST_RAT) {
				rational_explored = constant_explored-> const_value.const_rat;
				printf ("num %d den %d", rational_explored -> rnum,
				  rational_explored -> rden);
			}
			else if (constant_kind == CONST_CONSTRAINT_ERROR)
				printf ("CONSTANT_CONSTRAINT_ERROR");
		}
	}
	else if (kind_explored == as_terminate_alt)
	printf ("%d", (int) N_VAL (node_explored));
	else if (kind_explored == as_string_ivalue) {
		/* N_VAL is a tuple of integer */
		printf ("\"");
		tup = (Tuple) N_VAL (node_explored);
		n = tup_size (tup);
		for (i = 1; i <= n; i++)
			printf ("%c", tup [i]);
		printf ("\"");
	}
	else if (kind_explored == as_null)
		printf ("null");
	else if (kind_explored == as_null_s)
		printf ("null;");
	else if (kind_explored == as_others)
		printf ("others");
	else if (kind_explored == as_generic)
		printf ("(<>)");
	else if (kind_explored == as_instance_tuple)
		printf (" ??????? ");
}

void display_signature (Symbol sym) 				/*;display_signature*/
{
	int nat, i, n, ctyp;
	Tuple	sig, tup, tupent;
	Symbol	s;
	Fortup	ft1;
	static char *constraint_types[] = {
	  "range", "digits", "delta", "discr", "array" };


	/* The signature field is used as follows:
	 * It is a symbol for:
	 *	na_access
	 * It is a node for
	 *	na_constant  na_in  na_inout
	 * It is also a node (always OPT_NODE) for na_out. For now we write this
	 * out even though it is not used. 
	 * It is a pair for na_array.
	 * It is a triple for na_enum.
	 * It is a triple for na_generic_function_spec na_generic_procedure_spec
	 * The first component is a tuple of pairs, each pair consisting of
	 * a symbol and a (default) node.
	 * The second component is a tuple of symbols.
	 * The third component is a node
	 * It is a tuple with four elements for na_generic_package_spec:
	 * the first is a tuple of pairs, with same for as for generic procedure.
	 * the second third, and fourth components are nodes.
	 * It is a 5-tuple for na_record.
	 * It is a constraint for na_subtype and na_type.
	 * It is a node for na_obj.
	 * Otherwise it is the signature for a procedure, namely a tuple
	 * of quadruples.
	 * Note however, that for a private type, the signature has the same
	 * form as for a record.
	 * For a subtype whose root type is an array, the signature has the
	 * same form as for an array.
	 */

	nat = NATURE(sym);
	sig = SIGNATURE(sym);

	/* treat private types way in same way as for records*/

	s = TYPE_OF(sym);
	if (s == symbol_private || s == symbol_limited_private
	  || s == symbol_incomplete)
		nat = na_record;

	switch (nat) {
	case na_access: 
		/* access: signature is designated_type;*/
		(void) give_symbol_reference ((Symbol) sig);
		break;

	case na_array:
	array_case:
		/* array: signature is pair [i_types, comp_type] where
		 * i_type is tuple of type names
		 */
		printf(" array_sig %d\n", tup_size((Tuple) sig[1]));
		FORTUP(s = (Symbol), (Tuple) sig[1], ft1);
			(void) give_symbol_reference (s);
			printf("\n");
		ENDFORTUP(ft1);
		(void) give_symbol_reference ((Symbol) sig[2]);
		printf("\n");
		break;

	case	na_block:
		/* block: miscellaneous information */
		/* This information not needed externally*/
		printf ("signature for block\n");
		break;

	case	na_constant:
	case	na_in:
	case	na_inout:
	case	na_out:
	case	na_discriminant:
		(void) give_node_reference ((Node) sig);
		break;

	case	na_entry:
	case	na_entry_family:
	case	na_entry_former:
		/*  entry: list of symbols */
	case	na_function:
	case	na_function_spec:
	case	na_literal:		/* is this for literals too? */
	case	na_op:
	case	na_procedure:
	case	na_procedure_spec:
		printf(" symbol_list  %d\n", tup_size(sig));
		FORTUP(s = (Symbol), sig, ft1);
			(void) give_symbol_reference(s); 
			printf("\n");
		ENDFORTUP(ft1);
		break;

	case na_enum : 
		/* enum: tuple in form ['range', lo, hi]*/
		/* we write this as two node references*/
		(void) give_node_reference ((Node) sig[2]);
		(void) give_node_reference ((Node) sig[3]);
		printf ("\n");
		break;

	case na_type: 
	case na_subtype:
		if (nat == na_subtype && is_access(TYPE_OF(sym)))
		/* subtype of access type, signature is anonymous type */
			(void) give_symbol_reference ((Symbol)sig);
		else {
			n = tup_size(sig);
			if (is_array (sym)) {
				printf(" constrained_array \n");
				goto array_case;
			}
			ctyp = (int) sig[1];
			if (ctyp >= 0 && ctyp <= 4)
				printf(" co_%s", constraint_types[ctyp]);
			else
				printf(" unknown constraint type %d", ctyp);
			if (ctyp == CONSTRAINT_DISCR) {
				/* discriminant map */
				tup = (Tuple) numeric_constraint_discr(sig);
				n = tup_size(tup);
				for (i = 1; i <= n; i += 2) {
					printf(" %d", (i+1)/2);
					(void) give_symbol_reference ((Symbol) sig[i]);
					(void) give_node_reference ((Node) sig[i+1]);
				}
			}
			else {
				for (i = 2; i <= n; i++) {
					printf(" %d", i);
					(void) give_node_reference ((Node) sig[i]);
				}
			}
		}
		printf("\n");
		break;

	case	na_generic_function:
	case	na_generic_procedure:
	case	na_generic_function_spec:
	case	na_generic_procedure_spec:
		if (tup_size(sig) != 3)
			printf ("bad signature for na_generic_procedure_spec\n");
		/* tuple count known to be three, just put elements */
		tup = (Tuple) sig[1];
		/* the first component is a tuple of pairs, just write count
		 * and the values of the successive pairs 
		 */
		n = tup_size(tup);
		printf(" %d\n", n);
		for (i = 1; i <= n; i++) {
			tupent = (Tuple) tup[i];
			(void) give_symbol_reference((Symbol) tupent[1]);
			(void) give_node_reference ((Node) tupent[2]);
			printf("\n");
		}
		tup = (Tuple) sig[2];
		n = tup_size(tup); /* symbol list */
		printf(" symbol_list %d\n", n);
		for (i = 1; i <= n; i++) {
			(void) give_symbol_reference ((Symbol) tup[i]); 
			printf("\n");
		}
		printf(" node ");
		(void) give_node_reference((Node) sig[3]);
		printf("\n");
		break;

	case	na_generic_package_spec:
	case	na_generic_package:
		/* signature is tuple with three elements */
		if (tup_size(sig) != 4)
			printf ("bad signature for na_generic_package_spec\n");
		tup = (Tuple) sig[1];
		/* the first component is a tuple of pairs, just write count
		 * and the values of the successive pairs 
		 */
		n = tup_size(tup);
		printf(" n %d\n", n);
		for (i = 1; i <= n; i++) {
			tupent = (Tuple) tup[i];
			(void) give_symbol_reference ((Symbol) tupent[1]);
			(void) give_node_reference ((Node) tupent[2]);
			printf("\n");
		}
		/* the second third, and fourth components are just nodes */
		(void) give_node_reference ((Node) sig[2]);
		(void) give_node_reference ((Node) sig[3]);
		(void) give_node_reference ((Node) sig[4]);
		printf("\n");
		break;

	case	na_record:
		/* the signature is tuple with five components:
		 * [node, node, tuple of symbols, declaredmap, node]
		 * NOTE: we do not write component count - 5 assumed 
		 */
		printf(" record (skip details)\n"); 
		break;
/*
		(void) give_node_reference ((Node) sig[1]);
		(void) give_node_reference ((Node) sig[2]);
		tup = (Tuple) sig[3];
		n = tup_size(tup);
		for (i = 1; i <= n; i++)
			zpsymref((Symbol) tup[i]);

		(void) give_node_reference ((Node) sig[5]);
		break;
*/

	case	na_void:
		/* special case assume entry for $used, in which case is tuple
		 * of symbols
		 */
		if (streq(ORIG_NAME(sym), "$used")) {
			n = tup_size(sig);
			printf(" symbol_list %d\n", n);
			for (i = 1; i <= n; i++) {
				(void) give_symbol_reference ((Symbol) sig[i]); 
				printf("\n");
			}
		}
		else {
			(void) give_symbol_reference(sym);
			printf ("na_void, not $used\n");
		}
		break;

	case na_obj:
		(void) give_node_reference ((Node) sig); 
		printf("\n");
		break;

	default:
		printf("display_signature : default error\n");
	}
}

void give_node_reference (Node node)			/*;give_node_reference*/
{
	if (node == (Node)0)
		printf (" (Node)0 \n");
	else
		printf(" n%du%d %d%s", N_SEQ (node), N_UNIT (node), node,
		  kind_str (N_KIND (node)));
}

void give_symbol_reference (Symbol symbol)		/*;give_symbol_reference*/
{
	if (symbol == (Symbol)0)
		printf (" (Symbol)0 \n");
	else
		printf(" s%du%d %d%s", S_SEQ (symbol), S_UNIT (symbol), symbol,
		  nature_str (NATURE (symbol)));
}

void zpadr(char *s, char *p)			/*;zpadr*/
{
	/* print argument as address */
	if (zpadr_opt == 0) return; /* quit if disabled */
	if (p == (char *)0) return; /* don't print if null pointer */
	if (!adrflag) return;
	if (s != (char *)0) {
#ifdef IBM_PC
		printf(" %s %p", s, p);
#else
		printf(" %s %ld", s, p);
#endif
	}
	else {
#ifdef IBM_PC
		printf(" %p", p);
#else
		printf(" %ld", p);
#endif
	}
}

void zpstr(char *str)											/*;zpstr*/
{
	printf("%s\n", str);
}

void zpcon(Const con)											/*;zpcon*/
{
	zpcon1(con);
	printf("\n");
}

static void zpcon1(Const con)									/*;zpcon1*/
{
	int	k;
	char	*s;

	k = con->const_kind;
	if (k == CONST_OM) s = "om";
	else if (k== CONST_INT) s = "int";
	else if (k == CONST_REAL) s = "real";
	else if (k == CONST_STR) s = "str";
	else if (k == CONST_RAT) s = "rat";
	else if (k == CONST_CONSTRAINT_ERROR) s = "constraint_error";
	else if (k == CONST_UINT) s = "uint";
	else if (k == CONST_FIXED) s = "fixed";
	else s = "INVALID";
	printf(" %s", s);
	if (k == CONST_INT) printf(" %d", con->const_value.const_int);
	else if (k == CONST_UINT)printf(" %s",int_tos(con->const_value.const_uint));
	else if (k == CONST_REAL) printf(" %12.3g", con->const_value.const_real);
	else if (k == CONST_STR) printf(" %s", con->const_value.const_str);
	else if (k == CONST_RAT) zprat1(RATV(con));
	else if (k == CONST_FIXED) printf("%ld", con->const_value.const_fixed);
}

static void zprat1(Rational rat)					/*;zprat1*/
{
	char	*s1, *s2;

	s1 = int_tos(rat->rnum);
	s2 = int_tos(rat->rden);
	printf(" %s/%s", s1, s2);
	efreet(s1, "zprat1-num"); 
	efreet(s2, "zprat1-den");
}

void zprat(Rational rat)					/*;zprat*/
{
	zprat1(rat);
	printf("\n");
}

void zpnod(Node nod)					/*;zpnod*/
{
	int	i, seq, unit, has_spans;
	unsigned int nk;
	Symbol	sym;

	if (nod == (Node)0) {
		printf("(Node)0\n");
		return;
	}
	printf("=n%du%d", N_SEQ(nod), N_UNIT(nod));
	zpadr((char *)0, (char *) nod);
	nk = N_KIND(nod);
	printf(" %s", kind_str(nk));
	if (N_LIST_DEFINED(nk)) zpadr("n_list", (char *) N_LIST(nod));
	has_spans = is_terminal_node(nk);
	if (has_spans) {
		printf(" n_span %d", N_SPAN0(nod));
		printf(".%d", N_SPAN1(nod));
	}
	sym = (Symbol) 0;
	/* indicate if overloaded */
	if (N_OVERLOADED(nod)) printf(" OV ");
	/* N_UNQ defined only if N_AST3 not defined */
	if (!N_AST3_DEFINED(nk)) sym = N_UNQ(nod);
	if (sym != (Symbol)0) { /* only do N_UNQ if not overloaded */
		if (!N_OVERLOADED(nod)) {
			seq = S_SEQ(sym); 
			unit = S_UNIT(sym);
			zpsymrefa("n_unq", N_UNQ(nod));
		}
	}
	if (!N_AST3_DEFINED(nk)) { /* N_AST3 and N_NAMES overlap */
		if (N_OVERLOADED(nod)) zpadr("n_names", (char *) N_NAMES(nod));
	}

	sym = (Symbol)0;
	/* N_TYPE defined only if N_AST4 not defined */
	if (!N_AST4_DEFINED(nk)) sym = N_TYPE(nod);
	if (!N_OVERLOADED(nod) && sym != (Symbol)0)
		zpsymrefa("n_type", N_TYPE(nod));
	if (!N_AST4_DEFINED(nk)) { /* N_PTYPES overlaps N_AST4 */
		if (N_OVERLOADED(nod)) zpadr("n_ptypes", (char *) N_PTYPES(nod));
	}

	if (N_KIND(nod) == as_line_no || N_KIND(nod) == as_number)
		printf(" %d", (int)N_VAL(nod));
	else if (N_KIND(nod) == as_ivalue) {
		printf(" ");
		zpcon1((Const) N_VAL(nod));
	}
	else {
		if (N_VAL_DEFINED(nk)) zpadr("n_val",  N_VAL(nod));
		if (N_LIST_DEFINED(nk)) zpadr("n_list",  (char *) N_LIST(nod));
	}
	if (N_KIND(nod) == as_simple_name) printf(" %s", N_VAL(nod));
	printf("\n");
	if (N_AST1(nod) != (Node) 0 || N_AST2(nod) != (Node) 0
	  || N_AST3(nod) != (Node) 0 || N_AST4(nod) != (Node) 0) {
		i = 0; /* set if any subnodes found, to see if newline needed*/
		if (N_AST1_DEFINED(nk) && N_AST1(nod) != (Node) 0)  {
			zpnodrefa("1", N_AST1(nod));
			i = 1;
		}
		if (N_AST2_DEFINED(nk) &&  N_AST2(nod) != (Node) 0)  {
			zpnodrefa("2", N_AST2(nod));
			i = 1;
		}
		if (N_AST3_DEFINED(nk) && N_AST3(nod) != (Node) 0)  {
			zpnodrefa("3", N_AST3(nod));
			i = 1;
		}
		if (N_AST4_DEFINED(nk) && N_AST4(nod) != (Node) 0) {
			zpnodrefa("4", N_AST4(nod));
			i = 1;
		}
		if (i) printf("\n");
	}
#ifdef AMIABLE
	zpoperand(nod);
#endif
}

void zpnods(int seq, int unit)			/*;zpnods*/
{
	/* node dump by sequence and unit number */
	Node node;

	node = zgetnodptr(seq, unit);
	zpnod(node);
}

void zpn(int seq, int unit)					/*;zpn*/
{
	/* short name for zpnods */
	zpnods(seq, unit);
}


void zpdnod() /*;zpdnod*/
{
	zpnod(znod);
}

void zpnodrefa(char *s, Node nod)					/*;zpnodrefa*/
{
	printf(" %s", s); 
	zpnodref(nod);
	/*zpadr((char *)0, nod);*/
}

void zpdset()	/*;zpdset*/
{
	zpset(zset);
}

void zpset(Set s)	/*;zpset*/
{
	zptup(s);
}

void zpdsetsym()	/*;zpdsetsym*/
{
	zpsetsym(zset);
}

void zpsetsym(Set s)	/*zpsetsym*/
{
	Symbol	sym;
	int n;
	Forset	fs1;

	n = set_size(s);
	printf("setsym %d {", n);
	if (n>10) n = 10;
	FORSET(sym = (Symbol), s, fs1);
		zpsym(sym);
	ENDFORSET(fs1);
	printf(" }\n");
}

void zpsigs(int seq, int unit)			/*;zpsigs*/
{
	/* signature dump by sequence and unit number */
	Symbol sym;
	sym = zgetsymptr(seq, unit);
	zpsig(sym);
}

void zpsig(Symbol sym)				/*;zpsig*/
{
	int nat, i, n, ctyp;
	Tuple	sig, tup, tupent;
	Symbol	s;
	Fortup	ft1;
	static char *constraint_types[] = { 
		"range", "digits", "delta", "discr", "array" };


	/* The signature field is used as follows:
	 * It is a symbol for:
	 *	na_access
	 * It is a node for
	 *	na_constant  na_in  na_inout
	 * It is also a node (always OPT_NODE) for na_out. For now we write this
	 * out even though it is not used. 
	 * It is a pair for na_array.
	 * It is a triple for na_enum.
	 * It is a triple for na_generic_function_spec na_generic_procedure_spec
	 * The first component is a tuple of pairs, each pair consisting of
	 * a symbol and a (default) node.
	 * The second component is a tuple of symbols.
	 * The third component is a node
	 * It is a tuple with four elements for na_generic_package_spec:
	 * the first is a tuple of pairs, with same for as for generic procedure.
	 * the second third, and fourth components are nodes.
	 * It is a 5-tuple for na_record.
	 * It is a constraint for na_subtype and na_type.
	 * It is a node for na_obj.
	 * Otherwise it is the signature for a procedure, namely a tuple
	 * of quadruples.
	 * Note however, that for a private type, the signature has the same
	 * form as for a record.
	 * For a subtype whose root type is an array, the signature has the
	 * same form as for an array.
	 */

	nat = NATURE(sym);
	sig = SIGNATURE(sym);
	/* treat private types way in same way as for records*/
	s = TYPE_OF(sym);
	if (s == symbol_private || s == symbol_limited_private
	  || s== symbol_incomplete) {
		nat = na_record;
	}
	switch (nat) {
	case na_access:
		/* access: signature is designated_type;*/
		zpsymref((Symbol) sig);
		break;

	case	na_array:
		/* array: signature is pair [i_types, comp_type] where
		 * i_type is tuple of type names
		 */
array_case:
		printf(" array_sig %d\n", tup_size((Tuple) sig[1]));
		FORTUP(s = (Symbol), (Tuple) sig[1], ft1);
			zpsymref(s);
			printf("\n");
		ENDFORTUP(ft1);
		zpsymref((Symbol) sig[2]);
		printf("\n");
		break;

	case	na_block:
		/* block: miscellaneous information */
		/* This information not needed externally*/
		chaos("zpsig: signature for block");
		break;

	case	na_constant:
	case	na_in:
	case	na_inout:
	case	na_out:
	case	na_discriminant:
		zpnodref((Node) sig);
		break;

	case	na_entry:
	case	na_entry_family:
	case	na_entry_former:
		/* entry: list of symbols */
	case	na_function:
	case	na_function_spec:
	case	na_literal:		/* is this for literals too? */
	case	na_op:
	case	na_procedure:
	case	na_procedure_spec:
		printf(" symbol_list  %d\n", tup_size(sig));
		FORTUP(s = (Symbol), sig, ft1);
			zpsymref(s); 
			printf("\n");
		ENDFORTUP(ft1);
		break;

	case	na_enum:
		/* enum: tuple in form ['range', lo, hi]*/
		/* we write this as two node references*/
		zpnodref((Node) sig[2]);
		zpnodref((Node) sig[3]);
		printf("\n");
		break;

	case	na_type: 
	case na_subtype:
		if (nat == na_subtype && is_access(TYPE_OF(sym))) {
			/* subtype of access type, signature is anonymous type */
			zpsymref((Symbol)sig);
		}
		else {
			n = tup_size(sig);
			if (is_array(sym)) { /* if constrained array */
				printf(" constrained_array \n");
				goto array_case;
			}
			ctyp = (int) sig[1];
			if (ctyp >= 0 && ctyp <= 4)
				printf(" co_%s", constraint_types[ctyp]);
			else
				printf(" unknown constraint type %d", ctyp);
			if (ctyp == CONSTRAINT_DISCR) {
				/* discriminant map */
				tup = (Tuple) numeric_constraint_discr(sig);
				n = tup_size(tup);
				for (i = 1; i <= n; i += 2) {
					printf(" %d", (i+1)/2);
					zpsymref((Symbol) sig[i]);
					zpnodref((Node) sig[i+1]);
				}
			}
			else {
				for (i = 2; i <= n; i++) {
					printf(" %d", i);
					zpnodref((Node) sig[i]);
				}
			}
		}
		printf("\n");
		break;

	case	na_generic_function:
	case	na_generic_procedure:
	case	na_generic_function_spec:
	case	na_generic_procedure_spec:
		if (tup_size(sig) != 3)
			chaos("zpsig: bad signature for na_generic_procedure_spec");
		/* tuple count known to be three, just put elements */
		tup = (Tuple) sig[1];
		/* the first component is a tuple of pairs, just write count
		 * and the values of the successive pairs 
		 */
		n = tup_size(tup);
		printf(" %d\n", n);
		for (i = 1; i <= n; i++) {
			tupent = (Tuple) tup[i];
			zpsymref((Symbol) tupent[1]);
			zpnodref((Node) tupent[2]);
			printf("\n");
		}
		tup = (Tuple) sig[2];
		n = tup_size(tup); /* symbol list */
		printf(" symbol_list %d\n", n);
		for (i = 1; i <= n; i++) {
			zpsymref((Symbol) tup[i]); 
			printf("\n");
		}
		printf(" node ");
		zpnodref((Node) sig[3]);
		printf("\n");
		break;

	case	na_generic_package_spec:
	case	na_generic_package:
		/* signature is tuple with three elements */
		if (tup_size(sig) != 4)
			chaos("zpsig: bad signature for na_generic_package_spec");
		tup = (Tuple) sig[1];
		/* the first component is a tuple of pairs, just write count
		 * and the values of the successive pairs 
		 */
		n = tup_size(tup);
		printf(" n %d\n", n);
		for (i = 1; i <= n; i++) {
			tupent = (Tuple) tup[i];
			zpsymref((Symbol) tupent[1]);
			zpnodref((Node) tupent[2]);
			printf("\n");
		}
		/* the second third, and fourth components are just nodes */
		zpnodref((Node) sig[2]);
		zpnodref((Node) sig[3]);
		zpnodref((Node) sig[4]);
		printf("\n");
		break;

	case	na_record:
		/* the signature is tuple with five components:
		 * [node, node, tuple of symbols, declaredmap, node]
		 * NOTE: we do not write component count - 5 assumed 
		 */
		printf(" record (skip details)\n"); 
		break;
/*
		zpnodref((Node) sig[1]);
		zpnodref((Node) sig[2]);
		tup = (Tuple) sig[3];
		n = tup_size(tup);
		for (i = 1; i <= n; i++)
			zpsymref((Symbol) tup[i]);
		zpnodref((Node) sig[5]);
		break;
*/

	case	na_void:
		/* special case assume entry for $used, in which case is tuple
		 * of symbols
		 */
		if (streq(ORIG_NAME(sym), "$used")) {
			n = tup_size(sig);
			printf(" symbol_list %d\n", n);
			for (i = 1; i <= n; i++) {
				zpsymref((Symbol) sig[i]); 
				printf("\n");
			}
		}
		else {
			zpsym(sym);
			chaos("zpsig: na_void, not $used");
		}
		break;

	case	na_obj:
		zpnodref((Node) sig); 
		printf("\n");
		break;

	default:
		printf("zpsig: default error\n");
		zpsigt();
	}
}

void zpsigt()
{
}

void zptup(Tuple tup) /*;zptup*/
{
	int i, n;
	n = tup_size(tup);
	printf("size : %d\n", n);
	if (n>10) n = 10;
	for (i = 1; i <= n; i++)
		printf("%d 0x%x %d \n", i, (int)tup[i], (int)tup[i]);
}

void zpdtup()
{
	zptup(ztup);
}

void zpsym(Symbol sym)			/*;zpsym*/
{
	/* kind_char gives character for TYPE_KIND - B for byte, etc. */
	static char kind_char[] = {
		'U', 'B', 'W', 'A', 'L', 'D', 'X' };

	if (sym == (Symbol)0) {
		printf("(Symbol)0\n");
		return;
	}
	printf("=s%du%d", S_SEQ(sym), S_UNIT(sym));
	zpadr((char *)0, (char *) sym);
	/*printf(" %d %s ", (int)NATURE(sym), nature_str(NATURE(sym)));*/
	printf(" %s", nature_str(NATURE(sym)));
	zpsymrefa("type_of", TYPE_OF(sym));
	zpsymrefa("scope", SCOPE_OF(sym));
	zpadr("sig", (char *) SIGNATURE(sym));
	printf(" %c%d", kind_char[TYPE_KIND(sym)], TYPE_SIZE(sym));
	/* end line if giving full addresses */
	if (adrflag) printf("\n");
	zpadr("overloads", (char *) OVERLOADS(sym));
	zpadr("dcl", (char *) DECLARED(sym));
	zpsymrefa("alias", ALIAS(sym));
	if (TYPE_ATTR(sym)) printf(" type_attr %d", TYPE_ATTR(sym));
	/* list original name if available, putting : in front to mark it */
	if (ORIG_NAME(sym) != (char *)0)
		printf(" :%s", ORIG_NAME(sym));
	printf("\n");
}

void zpsymrefa(char *s, Symbol sym)			/*;zpsymrefa*/
{
	if (sym == (Symbol) 0) return;
	printf(" %s", s);
	zpsymref(sym);
}

void zpsyms(int seq, int unit)			/*;zpsyms*/
{
	/* symbol dump by sequence and unit number */
	Symbol sym;
	sym = zgetsymptr(seq, unit);
	zpsym(sym);
}

void zpdsym()	/*;zpdsym*/
{
	zpsym(zsym);
}

void zpdcl(Declaredmap dcl) /*;zpdcl*/
{
	Fordeclared	div;
	char	*str;
	Symbol	sym;

#ifdef IBM_PC
	printf("declared map %p\n", dcl);
#else
	printf("declared map %ld\n", dcl);
#endif

	FORDECLARED(str, sym, dcl, div)
#ifdef IBM_PC
	    printf("\"%s\" %p %d\n", str, sym, IS_VISIBLE(div));
#else
		printf("\"%s\" %ld %d\n", str, sym, IS_VISIBLE(div));
#endif
	ENDFORDECLARED(div)
}

void zpddcl() /*;zpddcl*/
{
	zpdcl(zdcl);
}

void zppdcl(Private_declarations pdcl)				/*;zppdcl*/
{
	/* print private declarations */
	Forprivate_decls	fp;
	Symbol	s1, s2;
	int		i = 0;

	printf("private declared map %d\n", (int)pdcl);

	FORPRIVATE_DECLS(s1, s2, pdcl, fp)
	    printf("priv decl entry %d \n", ++i);
		zpsym(s1); 
		zpsym(s2);
		printf("\n");
	ENDFORPRIVATE_DECLS(fp)
}

void zppsetsym(Set s)/*;zppsetsym*/
{
	zpsetsym(s);
}

void zptupsym(Tuple t)/*;zptupsym*/
{
	/* print tuple of symbols */

	int		i, n;

	n = tup_size(t);
	if (n == 0) return;
	printf("%d symbols\n", n);
	for (i = 1; i <= n; i++) {
		printf("%d\n", i);
		zpsym((Symbol) t[i]);
	}
}

void zptupnod(Tuple t)/*;zptupnod*/
{
	/* print tuple of nodes */

	int		i, n;

	n = tup_size(t);
	if (n == 0) return;
	printf("%d nodes\n", n);
	for (i = 1; i <= n; i++) {
		printf("%d\n", i);
		zpnod((Node) t[i]);
	}
}

void zpsmap(Symbolmap smap)					/*;zpsmap */
{
	int i, n;
	Tuple tup;
	tup = smap->symbolmap_tuple;
	n = tup_size(tup);
	printf("%d entries\n", n/2);
	for (i = 1; i<n; i += 2) {
		printf("%d:\n", (i/2)+1);
		zpsym((Symbol) tup[i]);
		zpsym((Symbol) tup[i+1]);
	}
}

void zpdmap(Nodemap dmap)					/*;zpdmap */
{
	int i, n;
	Tuple tup;

	tup = dmap->nodemap_tuple;
	n = tup_size(tup);
	printf("%d entries\n", n/2);
	for (i = 1; i<n; i += 2) {
		printf("%d:\n", (i/2)+1);
		zpnod((Node) tup[i]);
		zpnod((Node) tup[i+1]);
	}
}

void trapn(Node node)					/*;trapn*/
{
	/* called on reference to trapped node */
	zpnod(node);
}

void traps(Symbol sym)					/*;traps*/
{
	/* called on reference to trapped symbol */
	zpsym(sym);
}

void trapini()					/*;trapini*/
{
	FILE	*tfile;

	trapns = trapnu = trapss = trapsu = 0;
	tfile = efopen("trapf", "r", "t");
	if (tfile == (FILE *)0) return;
	fscanf(tfile, "%d%d%d%d", &trapss, &trapsu, &trapns, &trapnu);
	if (trapns | trapnu | trapss | trapsu) {
		printf("trap set ss %d su %d ns %d nu %d\n", trapss, trapsu,
		  trapns, trapnu);
	}
	fclose(tfile);
}

void trapset(int ns, int nu, int ss, int su)				/*;trapset*/
{
	printf("trapset ns %d nu %d ss %d su %d\n", ns, nu, ss, su);
	trapns = ns; 
	trapnu = nu; 
	trapss = ss; 
	trapsu = su;
}

Node zgetnodptr(int seq, int unit)		/*;zgetnodptr*/
{
	/* here to convert seq and unit to pointer to symbol.
	 * we require that the symbol has already been allocated
	 * This is variant of getnodptr; however it does not raise chaos
	 * if node not found, but just prints error message
	 */

	Tuple	nodptr;
	Node	node;

	/* TBSL: need to get SEQPTR table for unit, and return address
	 */
	if (unit == 0) {
		if (seq == 1) return OPT_NODE;
		if (seq == 0) return (Node)0;
		if (seq>0 && seq <= tup_size(init_nodes)) {
			node = (Node) init_nodes[seq];
			return node;
		}
		else {
			printf(" zgetnodptr - node s%du%d not found \n", seq, unit);
			return (Node) 0;
		}
	}
	if (unit <= unit_numbers) {
		nodptr = (Tuple) pUnits[unit]->treInfo.tableAllocated;
		if (seq == 0) {
			printf(" zgetnodptr - node s%du%d not found \n", seq, unit);
			return (Node) 0;
		}
		if (seq <= tup_size(nodptr)) {
			node = (Node) nodptr[seq];
			if (node == (Node)0) {/* here to allocate node on first reference */
				node = node_new_noseq(as_unread);
				N_SEQ(node) = seq;
				N_UNIT(node) = unit;
				nodptr[seq] = (char *) node;
			}
			return node;
		}
	}
	printf(" zgetnodptr - node s%du%d not found \n", seq, unit);
	return (Node) 0;
}

Symbol zgetsymptr(int seq, int unit)		/*;getsymptr*/
{
	/* here to convert seq and unit to pointer to symbol.
	 * we require that the symbol has already been allocated
	 * this is variant of getsymptr; it does not raise chaos if
	 * symbol cannot be found, but just prints error message
	 */

	Tuple	symptr;
	Symbol	sym;
	int	items;

	/* TBSL: need to get SEQPTR table for unit, and return address
	 */
	if (unit == 0) {
		if (seq == 0) return (Symbol)0;
		if (seq>0 && seq <= tup_size(init_symbols)) {
			sym = (Symbol) init_symbols[seq];
			return sym;
		}
		else {
			chaos("unit 0 error getsymptr");
		}
	}
	if (unit <= unit_numbers) {
		struct unit *pUnit = pUnits[unit];
		symptr = (Tuple) pUnit->aisInfo.symbols;
		if (symptr == (Tuple)0) {
			items = pUnit->aisInfo.numberSymbols;
			symptr = tup_new(items);
			pUnit->aisInfo.symbols = (char *) symptr;
		}
		if (seq <= tup_size(symptr)) {
			sym = (Symbol) symptr[seq];
			if (sym == (Symbol)0) {
				sym = sym_new_noseq(na_void);
				symptr[seq] = (char *) sym;
				S_SEQ(sym) = seq;
				S_UNIT(sym) = unit;
			}
			if (trapss>0 && seq == trapss && unit == trapsu) traps(sym);
			return sym; /* return newly allocated symbol */
		}
		else {
			printf(" zgetsymptr: symbol not found, return 0\n");
			return (Symbol) 0;
		}
	}
	printf(" zgetsymptr: symbol not found, return 0\n");
	return (Symbol) 0;
}

void zpsymref(Symbol sym)				/*;zpsymref*/
{
	/* print symbol sequence and unit */

	int	seq, unit;

	if (sym != (Symbol)0) {
		seq = S_SEQ(sym);
		unit = S_UNIT(sym);
	}
	else {
		seq = 0; 
		unit = 0;
	}
	printf(" s%du%d", seq, unit);
}

void zpnodref(Node nod)				/*;zpnodref*/
{
	/* print node sequence and unit */

	int	seq, unit;

	if (nod != (Node)0) {
		seq = N_SEQ(nod);
		unit = N_UNIT(nod);
	}
	else {
		seq = 0; 
		unit = 0;
	}
	printf(" n%du%d", seq, unit);
}

void zpunit(int unum)				/*;zpunit*/
{
	/* print information for nodes and symbols in specified  unit */

	Tuple stup, ntup, sig;
	int	nodes, symbols, i, rootseq, j, n;
	Node	first_node, unit_node, nod;
	Symbol	sym;
	struct unit *pUnit;

	/* disable address printing */
	adrflag = FALSE;
	if (unum > 0) {
		pUnit = pUnits[unum];
		nodes = pUnit->treInfo.nodeCount;
		ntup = (Tuple) pUnit->treInfo.tableAllocated;
		symbols = pUnit->aisInfo.numberSymbols;
		stup = (Tuple) pUnit->aisInfo.symbols;
		printf("unit dump for unit %d %s\n", unum, pUnit->name);
		/* rootseq doesn't seem used - bp */
		rootseq = 0;
		first_node = (Node) getnodptr(rootseq, unit_number_now);
		unit_node = N_AST2(first_node);
	}
	else { /* if dumping unit 0 */
		nodes = seq_node_n;
		ntup = tup_copy(seq_node);
		ntup[0] = (char *) seq_node_n;
		symbols = seq_symbol_n;
		stup = tup_copy(seq_symbol);
		stup[0] = (char *) seq_symbol_n;
		printf("unit dump for unit 0\n");
	}
	for (i = 1; i <= symbols; i++) {
		sym = (Symbol) stup[i];
		if (sym != (Symbol)0) {
			zpsym(sym);
			sig = SIGNATURE(sym);
			if (sig != (Tuple)0) zpsig(sym);
		}
	}
	for (i = 1; i <= nodes; i++) {
		nod = (Node) ntup[i];
		if (nod != (Node)0) {
			zpnod(nod);
			sig = N_LIST(nod);
			if (sig != (Tuple)0) { /* print N_LIST if present */
				n = tup_size(sig);
				printf(" n_list %d ", tup_size(sig));
				for (j = 1; j <= n; j++)
					zpnodref((Node) sig[j]);
				printf("\n");
			}
		}
	}
	if (unum == 0) { /* free node and symbol tuples for unit 0 */
		tup_free(stup);
		tup_free(ntup);
	}
	adrflag = TRUE; /* restore address print flag */
}

void zpint(int n)			/*;zpint*/
{
	/* print n at int */
	char ch;

	ch = (char) n;
	ch = isascii(ch) && isprint(ch) ? ch : ' ';
	printf(" %d %u %x %c  :duxc\n", n, n, n, ch);
}
#endif
