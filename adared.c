/* Reduce: This is the reduce action for ada. When called, the array
   rh is created which contains pointers to the structures on the
   top of the parse stack (prs_stack). To do this we traverse the 
   stack. As this is happening, when we find a terminal on the stack,
   we free the token structure for this terminal. After the traversal,
   we then free all the structures on the top of the stack as indicated
   by the length of the right hand side of the rule except one, which is
   kept for reuse for the non-terminal being formed by the current reduction.
   When we free the stack structures and the token structures, we have not
   actually released the storage, but have put it back into a free pool
   for reuse. However in this function we never allocate a stack or token
   structure from our pool, so the data held in these structures remains
   intact. A special case is when the right hand side of the rule has zero
   symbols, when we instead allocate a new stack strucure and do not free
   anything. */

#include "hdr.h"
#include "vars.h"
#include "ada.h"
#include "adared.h"
#include "nodesprots.h"
#include "smiscprots.h"
#include "setprots.h"
#include "adalexprots.h"
#include "reduceprots.h"
#include "ppredefprots.h"
#include "pspansprots.h"
#include "prsutilprots.h"
#include "errsprots.h"
#include "adaredprots.h"
#include "miscprots.h"

/* Macros for convenient use of the rh array:
AST(n) represents the node in the nth position of the rh array (non-terminal).
IND(n) repesents the index of the terminal in the nth position of rh.
LOC(n) represents the starting loc of the terminal in the nth pos of rh.
END_LOC(n) represents the ending loc of the terminal in the nth pos of rh.
*/
#define AST(j) (rh[j]->ptr.ast)
#define IND(j) (rh[j]->ptr.token->index)
#define LOC(j) (&rh[j]->ptr.token->span)
#define END_LOC(j) 	\
	make_span(LOC(j)->line,LOC(j)->col+strlen(namelist(IND(j)))-1)

/* FREEAST recursively frees the nth child of node and its children. */
#define FREEAST(node,n) {if ((node->links.subast)[n] != OPT_NODE) \
	free_everything((node->links.subast)[n]);}

static Node make_id(int);
static struct prsstack *rh[MAX_RHS];

void reduce(int red)									/*;reduce*/
{
	Fortup ft1;
    int n = rhslen[red];
    struct prsstack *tmp, *top;
    Node node, id_node, tmp_node;

	/* n is the length (# of grammar symbols) of the right hand side of
	 *  the production.  Set up the array 'rh' to contain the n symbols
	 *  from the top of the parse stack.  These are popped from the stack
	 *  in the process, except for 1 which is left to be overridden by
	 *  the new node created during the reduction (note that when n = 0
	 *  a new postion on the top of the stack has to be created).
	 */

    if (!n) {
        tmp = PRSALLOC();
        tmp->prev = prs_stack;
        prs_stack = tmp;
    }
    else {
        if (n == 1) {
            rh[0] = prs_stack;
        }
        else {
            top = prs_stack;
            while (--n > 1) {
                rh[n] = prs_stack;
                prs_stack = prs_stack->prev;
            }
            rh[1] = tmp = prs_stack;
            rh[0] = prs_stack = prs_stack->prev;
            PRSFREE(top, tmp);
        }
    }

    if (redopt)
        fprintf(errfile, "Rule %d [%d]\n", red + 1, rhslen[red]);
    switch (red + 1) {
 
     break;
 /* pragma ::= PRAGMA identifier [(argument_association{,argument_association */
 case 1 :
{
	Node arg_assoc_list_node = AST(2);
    Tuple arg_assoc_list;
    char *name_id;
    int pragma_type = 0;

    arg_assoc_list = N_LIST(arg_assoc_list_node);
    node = any_node;
    if (!strcmp(namelist(IND(1)), "LIST")) {
        if (tup_size(arg_assoc_list) != 1)
            prs_warning(LOC(0), LOC(3),
              "Pragma LIST takes one argument: ON or OFF");
        else {
            Node arg = (Node) arg_assoc_list[1];
			Node opt_id = N_AST1(arg);
			Node expression = N_AST2(arg);

            if (opt_id != OPT_NODE)
                prs_warning(LOC(0), LOC(3),
                  "Named argument is invalid for pragma LIST");
            else if (N_KIND(expression) != as_name)
                prs_warning(LOC(0), LOC(3),
                  "Argument passed to pragma LIST is invalid");
            else {
                Node name = N_AST1(expression);

                if (N_KIND(name) != as_simple_name)
                    prs_warning(LOC(0), LOC(3),
                      "Name argument passed to pragma LIST is invalid");
                else {
                    name_id = namelist(N_ID(name));
                    if (!strcmp(name_id, "ON"))
                        pragma_type = PRAGMA_LIST_ON;
                    else if (!strcmp(name_id, "OFF"))
                        pragma_type = PRAGMA_LIST_OFF;
                    else {
                        char msg[100];

                        sprintf(msg,
                 "Identifier %s is an invalid argument passed to pragma LIST",
                          name_id);
                        prs_warning(LOC(0), LOC(3), msg);
                    }
                }
            }
        }
        if (!pragma_type)
            write_pragma(PRAGMA_LIST_ERR, LOC(0), LOC(3));
    }
    else if (!strcmp(namelist(IND(1)), "PAGE"))
        pragma_type = PRAGMA_PAGE;
    else {
		Node arg2_node, name_node, simple_name_node;

		if (!strcmp(namelist(IND(1)), "IO_INTERFACE")) {
    	    arg_assoc_list = N_LIST(arg_assoc_list_node);
			/* get second argument of pragma io_interface and change node
		 	* from as_simple_name to as_line_no whose n_val contains
		 	* the internal number of the io routine
		 	* TBSL: this node kind should not be as_line_no, however this
		 	* avoids adding a new node kind for the moment!
		 	* The node we are changing is 2 levels down in the tree!
		 	*/
			arg2_node = (Node) arg_assoc_list[2]; /* 2nd as_arg node*/
			name_node = N_AST2(arg2_node);
			simple_name_node = N_AST1(name_node);
			N_KIND(simple_name_node) = as_line_no;
			N_ID(simple_name_node) =
			  predef_code(namelist(N_ID(simple_name_node)));
		}
        node = node_new(as_pragma);
        id_node = make_id(1);
        insert_2child(node, id_node, arg_assoc_list_node);
    }
    if (pragma_type)
        write_pragma(pragma_type, LOC(0), LOC(3));
}
 
 /* argument_association ::= [argument_identifier=>]expression */
 /* case 2 : */
 
 /* basic_declaration ::= object_declaration */
 /* case 3 : */
 
 /* basic_declaration ::= number_declaration */
 /* case 4 : */
 
 /* basic_declaration ::= type_declaration */
 /* case 5 : */
 
 /* basic_declaration ::= subtype_declaration */
 /* case 6 : */
 
 /* basic_declaration ::= subprogram_declaration */
 /* case 7 : */
 
 /* basic_declaration ::= package_declaration */
 /* case 8 : */
 
 /* basic_declaration ::= task_declaration */
 /* case 9 : */
 
 /* basic_declaration ::= generic_declaration */
 /* case 10 : */
 
 /* basic_declaration ::= exception_declaration */
 /* case 11 : */
 
 /* basic_declaration ::= generic_instantiation */
 /* case 12 : */
 
 /* basic_declaration ::= renaming_declaration */
 /* case 13 : */
 
     break;
 /* object_declaration ::= identifier_list : subtype_indication [:=expression */
 case 14 :
    node = node_new(as_obj_decl);
    insert_3child(node, AST(0), AST(2), AST(3));
 
     break;
 /* object_declaration ::= identifier_list : CONSTANT subtype_indication [:=e */
 case 15 :
    node = node_new(as_const_decl);
    insert_3child(node, AST(0), AST(3), AST(4));
 
     break;
 /* object_declaration ::= identifier_list : [CONSTANT] constrained_array_def */
 case 16 :
    node = node_new((AST(2) == OPT_NODE) ? as_obj_decl : as_const_decl);
    insert_3child(node, AST(0), AST(3), AST(4));
 
     break;
 /* number_declaration ::= identifier_list : CONSTANT := universal_static_exp */
 case 17 :
    node = node_new(as_num_decl);
    insert_2child(node, AST(0), AST(4));
 
     break;
 /* identifier_list ::= identifier {,identifier} */
 case 18 :
    node = AST(1);
    id_node = make_id(0);
    prepend(id_node, node);
 
 /* type_declaration ::= full_type_declaration */
 /* case 19 : */
 
 /* type_declaration ::= incomplete_type_declaration */
 /* case 20 : */
 
 /* type_declaration ::= private_type_declaration */
 /* case 21 : */
 
     break;
 /* full_type_declaration ::= TYPE identifier [discriminant_part]IS type_defi */
 case 22 :
    id_node = make_id(1);
    node = node_new(as_type_decl);
    insert_3child(node, id_node, AST(2), AST(3));
 
 /* type_definition ::= enumeration_type_definition */
 /* case 23 : */
 
 /* type_definition ::= integer_type_definition */
 /* case 24 : */
 
 /* type_definition ::= real_type_definition */
 /* case 25 : */
 
 /* type_definition ::= array_type_definition */
 /* case 26 : */
 
 /* type_definition ::= record_type_definition */
 /* case 27 : */
 
 /* type_definition ::= access_type_definition */
 /* case 28 : */
 
 /* type_definition ::= derived_type_definition */
 /* case 29 : */
 
     break;
 /* subtype_declaration ::= SUBTYPE identifier IS subtype_indication ; */
 case 30 :
    id_node = make_id(1);
    node = node_new(as_subtype_decl);
    insert_2child(node, id_node, AST(3));
 
     break;
 /* subtype_indication ::= type_mark [constraint] */
 case 31 :
    node = node_new(as_subtype_indic);
    insert_2child(node, AST(0), AST(1));
 
 /* constraint ::= range_constraint */
 /* case 32 : */
 
 /* constraint ::= floating_point_constraint */
 /* case 33 : */
 
 /* constraint ::= fixed_point_constraint */
 /* case 34 : */
 
     break;
 /* constraint ::= general_aggregate */
 case 35 :
{
    Node element;
	Tuple new_list;

    node = AST(0);
	new_list = tup_new(0);
    N_KIND(node) = as_constraint;

    /*  "Range" elements of the general_aggregate represent the constraints
         of an indexed-constrained array.  The base types of the constraints
         are left as optional in the AST and have to be resolved semantically
         by looking at the definition of the corresponding type_mark.  See
         the definition of "subtype_indication".
    */
	FORTUP(tmp_node = (Node), N_LIST(node), ft1);
		if (N_KIND(tmp_node) == as_range) {
            element = node_new(as_subtype);
			insert_2child(element, OPT_NODE, tmp_node); }
		else
			element = tmp_node;
		new_list = tup_with(new_list, (char *)element);
	ENDFORTUP(ft1);

	N_LIST(node) = new_list;
}
 
     break;
 /* derived_type_definition ::= NEW subtype_indication */
 case 36 :
    node = node_new(as_derived_type);
    insert_1child(node, AST(1));
 
     break;
 /* range_constraint ::= RANGE range */
 case 37 :
{
    Span save_span;

    node = AST(1);
	if (N_KIND(node) != as_range && N_KIND(node) != as_range_attribute) {
        syntax_err(SPAN(node), "Invalid range specification");
		save_span = get_left_span_p(node);
        node = OPT_NODE;
 		set_span(node, save_span);
    }
}
 
     break;
 /* range ::= range_attribute */
 case 38 :
{
	Node name;
    node = AST(0);
	name = N_AST1(node);
    if (N_KIND(node) == as_name) {
        if (N_KIND(name) == as_attribute) {
            if (N_ID(N_AST1(name)) == RANGE_SYM) {
                Node tmp;

                tmp = name;
/*
                astfree(node->links.subast);
*/
                nodefree(node);
                node = tmp;
                N_KIND(node) = as_range_attribute;
            }
        }
        else
            N_KIND(node) = as_range_expression;
    }
}
 
     break;
 /* range ::= simple_expression .. simple_expression */
 case 39 :
    node = node_new(as_range);
    insert_2child(node, AST(0), AST(2));
 
     break;
 /* enumeration_type_definition ::= ( enumeration_literal_specification {,enu */
 case 40 :
    node = AST(2);
    prepend(AST(1), node);
    N_KIND(node) = as_enum;
 
 /* enumeration_literal_specification ::= enumeration_literal */
 /* case 41 : */
 
     break;
 /* enumeration_literal ::= identifier */
 case 42 :
    node = node_new(as_simple_name);
    N_ID(node) = IND(0);
    set_span(node, LOC(0));
 
     break;
 /* enumeration_literal ::= character_literal */
 case 43 :
    node = node_new(as_character_literal);
    N_ID(node) = IND(0);
    set_span(node, LOC(0));
 
     break;
 /* integer_type_definition ::= range_constraint */
 case 44 :
    node = node_new(as_int_type);
    insert_1child(node, AST(0));
 
     break;
 /* real_type_definition ::= floating_point_constraint */
 case 45 :
    node = node_new(as_float_type);
    insert_1child(node, AST(0));
 
     break;
 /* real_type_definition ::= fixed_point_constraint */
 case 46 :
    node = node_new(as_fixed_type);
    insert_1child(node, AST(0));
 
     break;
 /* floating_point_constraint ::= floating_accuracy_definition [range_constra */
 case 47 :
    node = AST(0);
	N_AST2(node) = AST(1);
 
     break;
 /* floating_accuracy_definition ::= DIGITS static_simple_expression */
 case 48 :
    node = node_new(as_digits);
    insert_2child(node, AST(1), any_node);
 
     break;
 /* fixed_point_constraint ::= fixed_accuracy_definition [range_constraint] */
 case 49 :
    node = AST(0);
	N_AST2(node) = AST(1);
 
     break;
 /* fixed_accuracy_definition ::= DELTA static_simple_expression */
 case 50 :
    node = node_new(as_delta);
    insert_2child(node, AST(1), any_node);
 
 /* array_type_definition ::= unconstrained_array_definition */
 /* case 51 : */
 
 /* array_type_definition ::= constrained_array_definition */
 /* case 52 : */
 
     break;
 /* unconstrained_array_definition ::= ARRAY ( index_subtype_definition {,ind */
 case 53 :
    prepend(AST(2), AST(3));
    node = node_new(as_array_type);
    insert_2child(node, AST(3), AST(6));
 
     break;
 /* constrained_array_definition ::= ARRAY index_constraint OF component_subt */
 case 54 :
    node = node_new(as_array_type);
    insert_2child(node, AST(1), AST(3));
 
     break;
 /* index_subtype_definition ::= name RANGE <> */
 case 55 :
    if (!check_expanded_name(AST(0)))
        syntax_err(SPAN(AST(0)),
            "Invalid type_mark used in index_subtype_definition");
    node = node_new(as_box);
    insert_1child(node, AST(0));
 
     break;
 /* index_constraint ::= ( discrete_range {,discrete_range} ) */
 case 56 :
    node = AST(2);
    prepend(AST(1), node);
	FORTUP(tmp_node = (Node), N_LIST(node), ft1);
        check_discrete_range(tmp_node);
	ENDFORTUP(ft1);
 
     break;
 /* discrete_range ::= name range_constraint */
 case 57 :
    if (!check_expanded_name(AST(0)))
        syntax_err(SPAN(AST(0)),
            "Discrete_subtype_indication must be a type_mark");
    node = node_new(as_subtype);
    insert_2child(node, AST(0), AST(1));
 
     break;
 /* discrete_range ::= range */
 case 58 :
    if (N_KIND(AST(0)) == as_range) {
        node = node_new(as_subtype);
        insert_2child(node, OPT_NODE, AST(0));
    }
    else
        node = AST(0);
 
     break;
 /* record_type_definition ::= RECORD component_list END RECORD */
 case 59 :
    node = node_new(as_record);
    insert_1child(node, AST(1));
 
     break;
 /* component_list ::= {pragma} {component_declaration} component_declaration */
 case 60 :
    check_pragmas(AST(0), null_pragmas);
    check_pragmas(AST(3), null_pragmas);
	N_LIST(AST(1)) = tup_with(tup_add(N_LIST(AST(0)),
	   N_LIST(AST(1))), (char *)AST(2));
    node = node_new(as_component_list);
    insert_3child(node, AST(1), OPT_NODE, AST(3));
    nodefree(AST(0));
 
     break;
 /* component_list ::= {pragma} {component_declaration} variant_part {pragma} */
 case 61 :
    check_pragmas(AST(0), null_pragmas);
    check_pragmas(AST(3), null_pragmas);
	N_LIST(AST(1)) = tup_add(N_LIST(AST(0)),
	  N_LIST(AST(1)));
    node = node_new(as_component_list);
    insert_3child(node, AST(1), AST(2), AST(3));
    nodefree(AST(0));
 
     break;
 /* component_list ::= {pragma} NULL ; {pragma} */
 case 62 :
	N_LIST(AST(0)) = tup_add(N_LIST(AST(0)), N_LIST(AST(3)));
    check_pragmas(AST(0), null_pragmas);
    node = node_new(as_component_list);
    insert_3child(node, OPT_NODE, OPT_NODE, AST(0));
    nodefree(AST(3));
 
     break;
 /* component_declaration ::= identifier_list : component_subtype_definition  */
 case 63 :
    node = node_new(as_field);
    insert_3child(node, AST(0), AST(2), AST(3));
 
     break;
 /* discriminant_part ::= ( discriminant_specification {;discriminant_specifi */
 case 64 :
    node = AST(2);
    prepend(AST(1), node);
 
     break;
 /* discriminant_specification ::= identifier_list : type_mark [:=expression] */
 case 65 :
    node = node_new(as_discr_spec);
    insert_3child(node, AST(0), AST(2), AST(3));
 
     break;
 /* variant_part ::= CASE discriminant_simple_name IS {pragma} variant {varia */
 case 66 :
    check_pragmas(AST(3), null_pragmas);
	N_LIST(AST(5)) = tup_add(tup_with(N_LIST(AST(3)),
	  (char *)AST(4)), N_LIST(AST(5)));
    check_choices(AST(5), "a variant_part");
    node = node_new(as_variant_decl);
    insert_2child(node, AST(1), AST(5));
    nodefree(AST(3));
 
     break;
 /* variant ::= WHEN choice {|choice} => component_list */
 case 67 :
    prepend(AST(1), AST(2));
    node = node_new(as_variant_choices);
    insert_2child(node, AST(2), AST(4));
 
     break;
 /* choice ::= discrete_range */
 case 68 :
    switch(N_KIND(AST(0))) {
        case as_subtype :
        case as_range_attribute :
            node = node_new(as_range_choice);
            insert_1child(node, AST(0));
            break;
        case as_range_expression :
            node = AST(0);
            N_KIND(node) = as_choice_unresolved;
            break;
        default :
            node = node_new(as_simple_choice);
            insert_1child(node, AST(0));
            break;
    }
 
     break;
 /* choice ::= OTHERS */
 case 69 :
{
    Node span_node;

    node = node_new(as_others_choice);
    span_node = node_new(as_simple_name);
    N_ID(span_node) = IND(0);
    set_span(span_node, LOC(0));
    insert_3child(node, OPT_NODE, OPT_NODE, span_node);
}
 
     break;
 /* access_type_definition ::= ACCESS subtype_indication */
 case 70 :
    node = node_new(as_access_type);
    insert_1child(node, AST(1));
 
     break;
 /* incomplete_type_declaration ::= TYPE identifier [discriminant_part]; */
 case 71 :
    id_node = make_id(1);
    node = node_new(as_incomplete_decl);
    insert_2child(node, id_node, AST(2));
 
     break;
 /* declarative_part ::= {basic_declarative_item} */
 case 72 :
{
	Tuple decl_list, new_decl_list;
	Node line_node;
	int i, list_length;
	Span line_node_span;

	node = AST (0);
	if (N_LIST(node) != (Tuple)0) {
		decl_list = N_LIST(node);
		list_length = tup_size(decl_list);
		new_decl_list = tup_new(0);

		for (i = 1; i <= list_length; i++) {
			Node element = (Node)tup_fromb(decl_list);

			if (isbody_node[N_KIND(element)]) {
				new_decl_list = tup_with(new_decl_list, (char *)element);
				i++;
				break;
			}
			/* Create and insert as_line_no */
			line_node = node_new (as_line_no);
			line_node_span = get_left_span_p(element);
			N_ID(line_node) = line_node_span->line;
			set_span(line_node, line_node_span);
			new_decl_list = tup_with(new_decl_list, (char *)line_node);
			new_decl_list = tup_with(new_decl_list, (char *)element);
		}
		for ( ; i <= list_length; i++) {
			Node element = (Node)tup_fromb(decl_list);

			if (!islater_declarative_node[N_KIND(element)])
				syntax_err (SPAN (element),
				  "Misplaced basic_declarative_item");

			new_decl_list = tup_with(new_decl_list, (char *)element);
		}
		N_LIST(node) = new_decl_list;
	}
	N_KIND(node) = as_declarations;
}
 
 /* basic_declarative_item ::= basic_declaration */
 /* case 73 : */
 
 /* basic_declarative_item ::= representation_clause */
 /* case 74 : */
 
 /* basic_declarative_item ::= use_clause */
 /* case 75 : */
 
 /* basic_declarative_item ::= body */
 /* case 76 : */
 
 /* body ::= proper_body */
 /* case 77 : */
 
 /* body ::= body_stub */
 /* case 78 : */
 
 /* proper_body ::= subprogram_body */
 /* case 79 : */
 
 /* proper_body ::= package_body */
 /* case 80 : */
 
 /* proper_body ::= task_body */
 /* case 81 : */
 
 /* name ::= simple_name */
 /* case 82 : */
 
     break;
 /* name ::= character_literal */
 case 83 :
    node = node_new(as_character_literal);
    N_ID(node) = IND(0);
    set_span(node, LOC(0));
 
     break;
 /* name ::= operator_symbol */
 case 84 :
    node = AST(0);
    N_KIND(node) = as_string;
 
 /* name ::= indexed_component */
 /* case 85 : */
 
 /* name ::= selected_component */
 /* case 86 : */
 
 /* name ::= attribute */
 /* case 87 : */
 
     break;
 /* simple_name ::= identifier */
 case 88 :
    node = node_new(as_simple_name);
    N_ID(node) = IND(0);
    set_span(node, LOC(0));
 
     break;
 /* indexed_component ::= prefix general_aggregate */
 case 89 :
{
    int kind;
	Node arg2 = N_AST3(AST(0));

    if (N_KIND(AST(0)) == as_attribute && arg2 == OPT_NODE) {
        /* do the following checks only if have not yet processed the node */
		Node general_component;
		Tuple component_list;

        node = AST(0);
		kind = as_opt;
		if (N_LIST(AST(1))&&tup_size(N_LIST(AST(1)))== 1){
			general_component = (Node) N_LIST(AST(1))[1];
			component_list = N_LIST(general_component);
			kind = N_KIND(general_component);
		}
		if (kind == as_opt || kind == as_choice_list || kind == as_range
		  || kind == as_subtype) {
            syntax_err(SPAN(AST(1)),
              "Illegal expression for argument of attribute");
			N_AST3(node) = OPT_NODE;
            free_everything(AST(1));
        }
        else {
            N_AST3(node) = general_component;
            nodefree(AST(1));
        }
		N_AST4(node) = NULL;
    }
    else {
        if (N_KIND(AST(0)) == as_string
		  && !isoverloadable_op(namelist(N_ID(AST(0))))) {
            char msg[200];
            
            sprintf(msg, "\"%s\" is not a valid operator_symbol",
                namelist(N_ID(AST(0))));
            syntax_err(SPAN(AST(0)), msg);
        }
        node = node_new(as_call_unresolved);
        insert_2child(node, AST(0), AST(1));
    }
}
 
     break;
 /* selected_component ::= prefix . selector */
 case 90 :
    if (N_KIND(AST(2)) == as_all) {
        node = AST(2);
        insert_1child(node, AST(0));
    }
    else {
        node = node_new(as_selector);
        insert_2child(node, AST(0), AST(2));
    }
 
 /* selector ::= simple_name */
 /* case 91 : */
 
     break;
 /* selector ::= character_literal */
 case 92 :
    node = node_new(as_character_literal);
    N_ID(node) = IND(0);
    set_span(node, LOC(0));
 
     break;
 /* selector ::= operator_symbol */
 case 93 :
{
    char tmp[200];

    node = AST(0);
    strcpy(tmp, namelist(N_ID(node)));
    convtolower(tmp);
    if (!isoverloadable_op(tmp)) {
        char msg[300];
        
        sprintf(msg, "\"%s\" is not a valid operator_symbol", tmp);
        syntax_err(get_left_span_p(node), get_right_span_p(node), msg);
    }
    N_ID(node) = namemap(tmp, strlen(tmp));
}
 
     break;
 /* selector ::= ALL */
 case 94 :
    node = node_new(as_all);
 
     break;
 /* attribute ::= prefix ' attribute_designator */
 case 95 :
    node = node_new(as_attribute);
    insert_3child(node, AST(2), AST(0), OPT_NODE);
 
 /* attribute_designator ::= simple_name */
 /* case 96 : */
 
     break;
 /* attribute_designator ::= DIGITS */
 case 97 :
 
 /* attribute_designator ::= DELTA */
 case 98 :
 
 /* attribute_designator ::= RANGE */
 case 99 :
    node = node_new(as_simple_name);
    N_ID(node) = IND(0);
    set_span(node, LOC(0));
 
     break;
 /* aggregate ::= ( component_association {,component_association} ) */
 case 100 :
    if( !tup_size(N_LIST(AST(2)))
	  && N_KIND(AST(1)) != as_choice_list){
        node = node_new(as_parenthesis);
        insert_1child(node, AST(1));
        nodefree(AST(2));
    }
    else {
        node = AST(2);
        prepend(AST(1), node);
        N_KIND(node) = as_aggregate;
    }
 
 /* component_association ::= [choice{|choice}=>]expression */
 /* case 101 : */
 
     break;
 /* general_aggregate ::= ( general_component_association {,general_component */
 case 102 :
    node = AST(2);
    prepend(AST(1), node);
 
 /* general_component_association ::= component_association */
 /* case 103 : */
 
     break;
 /* general_component_association ::= simple_expression .. simple_expression */
 case 104 :
    node = node_new(as_range);
    insert_2child(node, AST(0), AST(2));
 
     break;
 /* general_component_association ::= name range_constraint */
 case 105 :
    if (!check_expanded_name(AST(0)))
        syntax_err(SPAN(AST(0)), "subtype_indicaiton must be a type_mark");
    node = node_new(as_subtype);
    insert_2child(node, AST(0), AST(1));
 
 /* expression ::= relation */
 /* case 106 : */
 
 /* expression ::= relation{AND__relation} */
 /* case 107 : */
 
 /* expression ::= relation{OR__relation} */
 /* case 108 : */
 
 /* expression ::= relation{XOR__relation} */
 /* case 109 : */
 
 /* expression ::= relation{AND__THEN__relation} */
 /* case 110 : */
 
 /* expression ::= relation{OR__ELSE__relation} */
 /* case 111 : */
 
     break;
 /* relation ::= simple_expression [relational_operator__simple_expression] */
 case 112 :
    if ((node = AST(1)) == OPT_NODE)
        node = AST(0);
    else {
		Node arg_list_node = N_AST2(node);
		N_LIST(arg_list_node)[1] = (char *) AST(0);
	}
 
     break;
 /* relation ::= simple_expression [NOT] IN range */
 case 113 :
{
    int kind, op_name;
    Node arg_list_node, simple_name;
    Span old_span;

    if (AST(1) != OPT_NODE) {
        kind = as_notin;
        op_name = namemap("notin", 5);
    }
    else if (!strcmp(namelist(IND(2)), "any_op"))
        kind = as_any_op;
    else {
        kind = as_in;
        op_name = namemap("in", 2);
    }
    switch (N_KIND(AST(3))) {
        case as_range_expression :
            if (!check_expanded_name(N_AST1(AST(3))))
                syntax_err(SPAN(AST(3)),
                    "Invalid expression used as range specification");
            break;
        case as_range :
        case as_range_attribute :
            break;
        default :
            syntax_err(SPAN(AST(3)), "Invalid range specification");
            /* fix up to satisfy adasem */
			old_span = LOC(3);
            AST(3) = node_new(as_range_expression);
			insert_1child(AST(3), node_new(as_simple_name));
			N_ID(N_AST1(AST(3))) = namemap("any_id", 6);
			set_span(N_AST1(AST(3)), old_span);
    }
    node = node_new(kind);
    simple_name = node_new(as_simple_name);
    set_span(simple_name, (AST(1) != OPT_NODE ? N_SPAN(AST(1)) : LOC(2)));
    N_ID(simple_name) = op_name;
    arg_list_node = node_new(as_list);
	N_LIST(arg_list_node) = tup_new(2);
	N_LIST(arg_list_node)[1] = (char *)AST(0);
	N_LIST(arg_list_node)[2] = (char *)AST(3);
    insert_2child(node, simple_name, arg_list_node);
}
 
 /* simple_expression ::= [unary_adding_operator]term{binary_adding_operator_ */
 /* case 114 : */
 
 /* term ::= factor{multiplying_operator__factor} */
 /* case 115 : */
 
     break;
 /* factor ::= primary [**__primary] */
 case 116 :
    if ((node = AST(1)) == OPT_NODE)
        node = AST(0);
    else {
		N_LIST(N_AST2(node))[1] = (char *)AST(0);
    }
 
     break;
 /* factor ::= ABS primary */
 case 117 :
{
    Node optr_node;

    optr_node = node_new(as_simple_name);
    N_ID(optr_node) = namemap("abs", 3);
    set_span(optr_node, LOC(0));
    node = unary_operator(optr_node, AST(1));
}
 
     break;
 /* factor ::= NOT primary */
 case 118 :
{
    Node optr_node;

    optr_node = node_new(as_simple_name);
    N_ID(optr_node) = namemap("not", 3);
    set_span(optr_node, LOC(0));
    node = unary_operator(optr_node, AST(1));
}
 
     break;
 /* primary ::= numeric_literal */
 case 119 :
    node = node_new((strchr(namelist(IND(0)), '.')) ? as_real_literal :
        as_int_literal);
    N_ID(node) = IND(0);
    set_span(node, LOC(0));
 
     break;
 /* primary ::= NULL */
 case 120 :
	node = node_new(as_null);
	set_span(node, LOC(0));
 
 /* primary ::= aggregate */
 /* case 121 : */
 
     break;
 /* primary ::= name */
 case 122 :
    if (N_KIND(AST(0)) == as_string) {
        node = AST(0);
        N_KIND(node) = as_string_literal;
    }
    else {
        node = node_new(as_name);
        insert_1child(node, AST(0));
    }
 
 /* primary ::= allocator */
 /* case 123 : */
 
 /* primary ::= qualified_expression */
 /* case 124 : */
 
     break;
 /* relational_operator ::= = */
 case 125 :
 
 /* relational_operator ::= /= */
 case 126 :
 
 /* relational_operator ::= < */
 case 127 :
 
 /* relational_operator ::= <= */
 case 128 :
 
 /* relational_operator ::= > */
 case 129 :
 
 /* relational_operator ::= >= */
 case 130 :
 
 /* binary_adding_operator ::= + */
 case 131 :
 
 /* binary_adding_operator ::= - */
 case 132 :
 
 /* binary_adding_operator ::= & */
 case 133 :
    node = node_new(as_simple_name);
    N_ID(node) = IND(0);
    set_span(node, LOC(0));
 
     break;
 /* unary_adding_operator ::= + */
 case 134 :
 
 /* unary_adding_operator ::= - */
 case 135 :
{
    char str[6];

    node = node_new(as_simple_name);
    sprintf(str, "%s", namelist(IND(0)));
    N_ID(node) = namemap(str, 1);
    set_span(node, LOC(0));
}
 
     break;
 /* multiplying_operator ::= * */
 case 136 :
 
 /* multiplying_operator ::= / */
 case 137 :
    node = node_new(as_simple_name);
    N_ID(node) = IND(0);
    set_span(node, LOC(0));
 
     break;
 /* multiplying_operator ::= MOD */
 case 138 :
    node = node_new(as_simple_name);
    N_ID(node) = namemap("mod", 3);
    set_span(node, LOC(0));
 
     break;
 /* multiplying_operator ::= REM */
 case 139 :
    node = node_new(as_simple_name);
    N_ID(node) =  namemap("rem", 3);
    set_span(node, LOC(0));
 
     break;
 /* qualified_expression ::= name ' aggregate */
 case 140 :
    if (!check_expanded_name(AST(0)))
        syntax_err(SPAN(AST(0)),
              "Invalid type_mark found in qualified_expression");
    if (N_KIND(AST(2)) == as_parenthesis) { /* remove parentheses */
        AST(2) = N_AST1(AST(2));
    }
    node = node_new(as_qualify);
    insert_2child(node, AST(0), AST(2));
 
     break;
 /* allocator ::= NEW type_mark */
 case 141 :
    node = node_new(as_new);
    insert_2child(node, AST(1), OPT_NODE);
 
     break;
 /* allocator ::= NEW type_mark general_aggregate */
 case 142 :
    node = node_new(as_new);
    insert_2child(node, AST(1), AST(2));
 
     break;
 /* allocator ::= NEW type_mark ' aggregate */
 case 143 :
    node = node_new(as_new_init);
    insert_2child(node, AST(1), AST(3));
 
     break;
 /* sequence_of_statements ::= {pragma} statement {statement} */
 case 144 :
{
	Node label_list_node,  line_node;
	Tuple nodelabels = tup_new(0);
	Tuple lablistlabels = tup_new(0);
	Tuple new_statement_list, tmp_list;
	Span line_node_span;

	check_pragmas(AST(0), null_pragmas);
	node = node_new(as_statements);
    new_statement_list = tup_new1((char *)AST(1));
	if (N_LIST(AST(0)) != (Tuple)0)
		new_statement_list = tup_add(N_LIST(AST(0)), new_statement_list);
	if (N_LIST(AST(2)) == (Tuple)0)
		N_LIST(AST(2)) = new_statement_list;
	else
        N_LIST(AST(2)) = tup_add(new_statement_list, N_LIST(AST(2)));
	label_list_node = node_new(as_list);
	new_statement_list = tup_new(0);
	FORTUP (tmp_node = (Node), N_LIST(AST(2)), ft1);
		if (tmp_list = getlabels(tmp_node))
			nodelabels = tup_add(nodelabels, tmp_list);
		if (N_KIND(tmp_node) == as_statement)
			if (tmp_list = N_LIST(N_AST1(tmp_node)))
				lablistlabels = tup_add(lablistlabels, tmp_list);
		if(N_KIND(tmp_node) != as_pragma) {
			/* insert as_line_no node before the current node (tmp_node) */
		    line_node = node_new(as_line_no);
			line_node_span = get_left_span_p(tmp_node);
		    N_ID(line_node) = line_node_span->line;
			set_span(line_node, line_node_span);
			new_statement_list = tup_with(new_statement_list,(char *)line_node);
		}
		new_statement_list = tup_with(new_statement_list, (char *)tmp_node);
	ENDFORTUP(ft1);
	N_LIST(AST(2)) = new_statement_list;
	/* add as_line_no node for next token (curtok) to end of stmt_list */
	end_as_line_no(AST(2), curtok);
	newlabels(node, nodelabels);
	N_LIST(label_list_node) = lablistlabels;
	if (!(tup_size(lablistlabels)))
		set_span(label_list_node, &curtok->ptr.token->span);
	insert_2child(node, AST(2), label_list_node);
	nodefree(AST(0));
}
 
     break;
 /* statement ::= {label} simple_statement */
 case 145 :
    if (tup_size(N_LIST(AST(0)))) {
        node = node_new(as_statement);
        insert_2child(node, AST(0), AST(1));
        newlabels(node, tup_copy(N_LIST(AST(0))));
    }
    else {
        node = AST(1);
        nodefree(AST(0));
    }
 
     break;
 /* statement ::= {label} compound_statement */
 case 146 :
    if (tup_size(N_LIST(AST(0)))) {
        node = node_new(as_statement);
        insert_2child(node, AST(0), AST(1));
        newlabels(node, tup_add(N_LIST(AST(0)), getlabels(AST(1))));
    }
    else {
        node = AST(1);
        nodefree(AST(0));
    }
 
 /* simple_statement ::= null_statement */
 /* case 147 : */
 
 /* simple_statement ::= assignment_statement */
 /* case 148 : */
 
 /* simple_statement ::= exit_statement */
 /* case 149 : */
 
 /* simple_statement ::= return_statement */
 /* case 150 : */
 
 /* simple_statement ::= goto_statement */
 /* case 151 : */
 
 /* simple_statement ::= delay_statement */
 /* case 152 : */
 
 /* simple_statement ::= abort_statement */
 /* case 153 : */
 
 /* simple_statement ::= raise_statement */
 /* case 154 : */
 
 /* simple_statement ::= code_statement */
 /* case 155 : */
 
 /* simple_statement ::= call_statement */
 /* case 156 : */
 
 /* compound_statement ::= if_statement */
 /* case 157 : */
 
 /* compound_statement ::= case_statement */
 /* case 158 : */
 
 /* compound_statement ::= loop_statement */
 /* case 159 : */
 
 /* compound_statement ::= block_statement */
 /* case 160 : */
 
 /* compound_statement ::= accept_statement */
 /* case 161 : */
 
 /* compound_statement ::= select_statement */
 /* case 162 : */
 
     break;
 /* label ::= << label_simple_name >> */
 case 163 :
    node = AST(1);
 
     break;
 /* null_statement ::= NULL ; */
 case 164 :
    node = node_new(as_null_s);
    set_span(node, LOC(0));
 
     break;
 /* assignment_statement ::= variable_name := expression ; */
 case 165 :
	node = node_new(as_assignment);
	insert_2child(node, AST(0), AST(2));
 
     break;
 /* if_statement ::= IF condition THEN sequence_of_statements {ELSIF__conditi */
 case 166 :
{
	Node if_node;
	Tuple nodelabels = tup_new(0);
    
	node = node_new(as_if);
	if_node = node_new(as_cond_statements);
	insert_2child(if_node, AST(1), AST(3));
	prepend(if_node, AST(4));
	FORTUP(tmp_node = (Node), N_LIST(AST(4)), ft1);
		nodelabels = tup_add(nodelabels, getlabels(N_AST2(tmp_node)));
	ENDFORTUP(ft1);
	if (AST(5) != OPT_NODE)
		nodelabels = tup_add(nodelabels, getlabels(AST(5)));
	newlabels(node, nodelabels);
	insert_2child(node, AST(4), AST(5));
}
 
     break;
 /* condition ::= boolean_expression */
 case 167 :
	node = node_new(as_condition);
	insert_1child(node, AST(0));
 
     break;
 /* case_statement ::= CASE expression IS {pragma} case_statement_alternative */
 case 168 :
{
	Tuple nodelabels = tup_new(0);

	node = node_new(as_case);
	check_pragmas(AST(3), null_pragmas);
	N_LIST(AST(5)) = tup_add(tup_with(N_LIST(AST(3)), (char *)AST(4)),
	  N_LIST(AST(5)));
	check_choices(AST(5), "a case_statement");
	nodefree(AST(3));
	FORTUP(tmp_node = (Node), N_LIST(AST(5)), ft1);
		nodelabels = tup_add(nodelabels, getlabels(N_AST2(tmp_node)));
	ENDFORTUP(ft1);
	newlabels(node, nodelabels);
	insert_2child(node, AST(1), AST(5));
}
 
     break;
 /* case_statement_alternative ::= WHEN choice {|choice} => sequence_of_state */
 case 169 :
	prepend(AST(1), AST(2));
	node = node_new(as_case_statements);
	insert_2child(node, AST(2), AST(4));
 
     break;
 /* loop_statement ::= [loop_simple_name:] [iteration_scheme] LOOP sequence_o */
 case 170 :
{
	Node simple_name1;
	Span left_span, right_span ;

	simple_name1 = AST(0);
	if (simple_name1 != OPT_NODE)
	left_span = get_left_span_p(simple_name1);
	else if (AST(1) != OPT_NODE)
	left_span = get_left_span_p(AST(1));
	else left_span = LOC(2);
	if (AST(6) != OPT_NODE)
	right_span = get_right_span_p(AST(6));
	else right_span = END_LOC(5);
	node = node_new(as_loop);
	if (simple_name1 != OPT_NODE) {
	    if (AST(6) != OPT_NODE) {
	        if (N_ID(simple_name1) != N_ID(AST(6)))
	            match_error(N_ID(simple_name1), N_ID(AST(6)),
	              "loop_statement", left_span, right_span);
	    }
	    else {
	        char msg[200];

           sprintf(msg,
"%s at beginning of loop_statement does not match non-existent \
\"loop_simple_name\" at END LOOP", namelist(N_ID(simple_name1)));
           syntax_err(left_span, right_span, msg);
       }
	}
	else {
        char newlabel[15];

        if (AST(6) != OPT_NODE) {
            char msg[200];
        
            sprintf(msg,
"Non existent \"loop_simple_name:\" at beginning of loop_statement does \
not match %s", namelist(N_ID(AST(6))));
            syntax_err(left_span, right_span, msg);
        }
        simple_name1 = node_new(as_simple_name);
        sprintf(newlabel, "#%x", simple_name1);
        N_ID(simple_name1) = namemap(newlabel, strlen(newlabel));
 	set_span(simple_name1, left_span);
    }
    newlabels(node, tup_add(tup_new1((char *)simple_name1),
        getlabels(AST(3))));
    insert_3child(node, simple_name1, AST(1), AST(3));

    nodefree(AST(6));
}
 
     break;
 /* iteration_scheme ::= WHILE condition */
 case 171 :
    node = node_new(as_while);
    insert_1child(node, AST(1));
 
     break;
 /* iteration_scheme ::= FOR loop_parameter_specification */
 case 172 :
    node = AST(1);
 
     break;
 /* loop_parameter_specification ::= identifier IN [REVERSE] discrete_range */
 case 173 :
    check_discrete_range(AST(3));
    node = node_new((AST(2) == OPT_NODE) ? as_for : as_forrev);
    id_node = make_id(0);
    insert_2child(node, id_node, AST(3));
 
     break;
 /* block_statement ::= [block_simple_name:] [DECLARE__declarative_part] BEGI */
 case 174 :
{
    Node simple_name1, labs_node;
    Span left_span, right_span ;

    simple_name1 = AST(0);
    if (simple_name1 != OPT_NODE)
	left_span = get_left_span_p(simple_name1);
    else if (AST(1) != OPT_NODE)
	left_span = get_left_span_p(AST(1));
    else left_span = LOC(2);
    if (AST(6) != OPT_NODE)
	right_span = get_right_span_p(AST(6));
    else right_span = END_LOC(5);
    
    node = node_new(as_block);
    if (simple_name1 != OPT_NODE) {
        if (AST(6) != OPT_NODE) {
            if (N_ID(simple_name1) != N_ID(AST(6)))
                match_error(N_ID(simple_name1), N_ID(AST(6)),
                  "block_statement", left_span, right_span);
        }
        else {
            char msg[200];
            
            sprintf(msg,
"%s at beginning of block_statement does not match non-existent \
\"block_simple_name\" at end of block", namelist(N_ID(simple_name1)));
            syntax_err(left_span, right_span, msg);
        }
    }
    else {
        char newlabel[15];

        if (AST(6) != OPT_NODE) {
            char msg[200];
        
            sprintf(msg,
"Non-existent \"block_simple_name:\" at beginning of block_statement does \
not match %s", namelist(N_ID(AST(6))));
            syntax_err(get_left_span_p(AST(6)),
			get_right_span_p(AST(6)), msg);
        }
        simple_name1 = node_new(as_simple_name);
        sprintf(newlabel, "#%x", simple_name1);
        N_ID(simple_name1) = namemap(newlabel, strlen(newlabel));
 		set_span(simple_name1, left_span);
    }

    /* The labels declared within a block are grouped together under a single
       node : labs_node.  This node is then passed upwards to help prevent
       duplicate declaration of labels within a program unit.
       (see remove_duplicate_labels)
    */

    labs_node = node_new(as_labels);
    N_LIST(labs_node) = remove_duplicate_labels(tup_add(getlabels(AST(3)),
      ((AST(4)==OPT_NODE) ? tup_new(0):(getlabels(AST(4))))));
    newlabels(node, tup_new2((char *)simple_name1, (char *)labs_node));
    append(AST(1), labs_node);
    insert_4child(node, simple_name1, AST(1), AST(3), AST(4));
    nodefree(AST(6));
}
 
     break;
 /* exit_statement ::= EXIT [loop_name] [WHEN__condition] ; */
 case 175 :
{
    Node span_node;

    node = node_new(as_exit);
    span_node = node_new(as_simple_name);
    N_ID(span_node) = IND(0);
    set_span(span_node, LOC(0));
    insert_4child(node, AST(1), AST(2), OPT_NODE, span_node);
}
 
     break;
 /* return_statement ::= RETURN [expression] ; */
 case 176 :
{
    Node span_node;

    node = node_new(as_return);
    span_node = node_new(as_simple_name);
    N_ID(span_node) = IND(0);
    set_span(span_node, LOC(0));
    insert_4child(node, AST(1), OPT_NODE, OPT_NODE, span_node);
}
 
     break;
 /* goto_statement ::= GOTO label_name ; */
 case 177 :
    node = node_new(as_goto);
    insert_1child(node, AST(1));
 
     break;
 /* subprogram_declaration ::= subprogram_specification ; */
 case 178 :
    node = node_new(as_subprogram_decl);
    insert_1child(node, AST(0));
 
     break;
 /* subprogram_specification ::= PROCEDURE identifier [formal_part] */
 case 179 :
    id_node = make_id(1);
    node = node_new(as_procedure);
    insert_3child(node, id_node, AST(2), OPT_NODE);
 
     break;
 /* subprogram_specification ::= FUNCTION designator [formal_part] RETURN typ */
 case 180 :
    node = node_new(as_function);
    insert_3child(node, AST(1), AST(2), AST(4));
 
     break;
 /* designator ::= identifier */
 case 181 :
    node = node_new(as_simple_name);
    N_ID(node) = IND(0);
    set_span(node, LOC(0));
 
     break;
 /* designator ::= operator_symbol */
 case 182 :
{
    char tmp[200];

    node = AST(0);
    strcpy(tmp, namelist(N_ID(node)));
    convtolower(tmp);
    if (!isoverloadable_op(tmp)) {
        char msg[300];
        
        sprintf(msg, "\"%s\" is not a valid operator_symbol", tmp);
        syntax_err(get_left_span_p(node), get_right_span_p(node), msg);
    }
    N_ID(node) = namemap(tmp, strlen(tmp));
}
 
     break;
 /* operator_symbol ::= string_literal */
 case 183 :
    node = node_new(as_operator);
    N_ID(node) = IND(0);
    set_span(node, LOC(0));
 
     break;
 /* formal_part ::= ( parameter_specification {;parameter_specification} ) */
 case 184 :
    node = AST(2);
    prepend(AST(1), node);
 
     break;
 /* parameter_specification ::= identifier_list : mode type_mark [:=expressio */
 case 185 :
    node = node_new(as_formal);
    insert_4child(node, AST(0), AST(2), AST(3), AST(4));
 
 /* mode ::= [IN] */
 /* case 186 : */
 
     break;
 /* mode ::= IN OUT */
 case 187 :
    node = node_new(as_mode);
    N_ID(node) = namemap("inout", 5);
    set_span(node, LOC(0));
 
     break;
 /* mode ::= OUT */
 case 188 :
    node = node_new(as_mode);
    N_ID(node) = namemap("out", 3);
    set_span(node, LOC(0));
 
     break;
 /* subprogram_body ::= subprogram_specification IS declarative_part BEGIN se */
 case 189 :
{
    Node labs_node;

    if (AST(7) != OPT_NODE && N_ID(N_AST1(AST(0))) != N_ID(AST(7)))
        match_error(N_ID(N_AST1(AST(0))), N_ID(AST(7)), "subprogram_body",
		get_left_span_p(AST(0)), get_right_span_p(AST(7)));
    nodefree(AST(7));
    labs_node = node_new(as_labels);
    N_LIST(labs_node) = remove_duplicate_labels(tup_add(getlabels(AST(4)),
      ((AST(5)==OPT_NODE) ? tup_new(0) : getlabels(AST(5)))));
    append(AST(2), labs_node);
    node = node_new(as_subprogram);
    insert_4child(node, AST(0), AST(2), AST(4), AST(5));
}
 
     break;
 /* call_statement ::= name ; */
 case 190 :
    node = node_new(as_call);
    insert_1child(node, AST(0));
 
     break;
 /* package_declaration ::= package_specification ; */
 case 191 :
    node = AST(0);
 
     break;
 /* package_specification ::= PACKAGE identifier IS {basic_declarative_item}  */
 case 192 :
    if (AST(6) != OPT_NODE && IND(1) != N_ID(AST(6)))
        match_error(IND(1), N_ID(AST(6)), "package_specification",
		  get_left_span_p(AST(6)), get_right_span_p(AST(6)));
    id_node = make_id(1);
	FORTUP(tmp_node = (Node), N_LIST(AST(3)), ft1);
        if (isbody_node[N_KIND(tmp_node)])
            syntax_err(SPAN(tmp_node),
                "Body declaration not allowed in package_specification");
    ENDFORTUP(ft1);
    N_KIND(AST(3)) = as_declarations;
    ins_as_line_no(AST(3));
    node = node_new(as_package_spec);
    insert_3child(node, id_node, AST(3), AST(4));
    nodefree(AST(6));
 
     break;
 /* package_body ::= PACKAGE BODY package_simple_name IS declarative_part END */
 case 193 :
    if (AST(6) != OPT_NODE
	  && N_ID(AST(2)) != N_ID(AST(6)))
        match_error(N_ID(AST(2)), N_ID(AST(6)),
    	  "package_body", get_left_span_p(AST(6)),
		  get_right_span_p(AST(6)));
    node = node_new(as_package_body);
    insert_4child(node, AST(2), AST(4), OPT_NODE, OPT_NODE);
    nodefree(AST(6));
 
     break;
 /* package_body ::= PACKAGE BODY package_simple_name IS declarative_part BEG */
 case 194 :
{
    Node labs_node;
    
    if (AST(9) != OPT_NODE
	  && N_ID(AST(2)) != N_ID(AST(9)))
        match_error(N_ID(AST(2)), N_ID(AST(9)),
          "package_body", get_left_span_p(AST(9)),
		  get_right_span_p(AST(9)));
    labs_node = node_new(as_labels);
    N_LIST(labs_node) = remove_duplicate_labels( tup_add(getlabels(AST(6)),
      ((AST(7)==OPT_NODE) ? tup_new(0) : getlabels(AST(7)))));
    append(AST(4), labs_node);
    node = node_new(as_package_body);
    insert_4child(node, AST(2), AST(4), AST(6), AST(7));
    nodefree(AST(9));
}
 
     break;
 /* private_type_declaration ::= TYPE identifier [discriminant_part]IS [LIMIT */
 case 195 :
{
    Node kind_node;
    
    id_node = make_id(1);
    kind_node = node_new(as_simple_name);
    N_ID(kind_node) = (AST(3) == OPT_NODE) ? namemap("private", 7) :
        namemap("limited_private", 15);
	set_span(kind_node,(AST(3)==OPT_NODE ? LOC(4) : N_SPAN(AST(3))));
    node = node_new(as_private_decl);
    insert_3child(node, id_node, AST(2), kind_node);
}
 
     break;
 /* use_clause ::= USE package_name {,package_name} ; */
 case 196 :
    node = AST(2);
    prepend(AST(1), node);
    N_KIND(node) = as_use;
 
     break;
 /* renaming_declaration ::= identifier:type_mark RENAMES object_name ; */
 case 197 :
    node = AST(0);
    N_AST3(node) = AST(2);
 
     break;
 /* renaming_declaration ::= identifier:EXCEPTION RENAMES exception_name ; */
 case 198 :
    node = AST(0);
    N_AST2(node) = AST(2);
 
     break;
 /* renaming_declaration ::= PACKAGE identifier RENAMES package_name ; */
 case 199 :
    id_node = make_id(1);
    node = node_new(as_rename_pack);
    insert_2child(node, id_node, AST(3));
 
     break;
 /* renaming_declaration ::= subprogram_specification RENAMES subprogram_or_e */
 case 200 :
    node = node_new(as_rename_sub);
    insert_2child(node, AST(0), AST(2));
 
     break;
 /* task_declaration ::= task_specification ; */
 case 201 :
    node = AST(0);
 
     break;
 /* task_specification ::= TASK [TYPE] identifier */
 case 202 :
{
    Node entry_decl_list, repr_clause_list;

    id_node = make_id(2);
    node = node_new((AST(1) == OPT_NODE) ? as_task_spec : as_task_type_spec);
    entry_decl_list = node_new(as_list);
    repr_clause_list = node_new(as_list);
    N_LIST(entry_decl_list) = tup_new(0);
    N_LIST(repr_clause_list) = tup_new(0);
    set_span(entry_decl_list, &curtok->ptr.token->span);
    set_span(repr_clause_list, &curtok->ptr.token->span);
    insert_3child(node, id_node, entry_decl_list, repr_clause_list);
}
 
     break;
 /* task_specification ::= TASK [TYPE] identifier IS {entry_declaration} {rep */
 case 203 :
    if (AST(7) != OPT_NODE && N_ID(AST(7)) != IND(2))
        match_error(IND(2), N_ID(AST(7)), "task_specification",
          get_left_span_p(AST(7)), get_right_span_p(AST(7)));
    id_node = make_id(2);
    node = node_new((AST(1) == OPT_NODE) ? as_task_spec : as_task_type_spec);
    insert_3child(node, id_node, AST(4), AST(5));
    ins_as_line_no(AST(4));
    nodefree(AST(7));
 
     break;
 /* task_body ::= TASK BODY task_simple_name IS declarative_part BEGIN sequen */
 case 204 :
{
    Node labs_node;

    if (AST(9) != OPT_NODE
	  && N_ID(AST(2)) != N_ID(AST(9)))
        match_error(N_ID(AST(2)), N_ID(AST(9)),
          "task_body", get_left_span_p(AST(9)),
		  get_right_span_p(AST(9)));
    labs_node = node_new(as_labels);
    N_LIST(labs_node) = remove_duplicate_labels( tup_add(getlabels(AST(6)),
      ((AST(7)==OPT_NODE) ? tup_new(0) : getlabels(AST(7)))));
    append(AST(4), labs_node);
    node = node_new(as_task);
    insert_4child(node, AST(2), AST(4), AST(6), AST(7));
    nodefree(AST(9));
}
 
     break;
 /* entry_declaration ::= ENTRY identifier [(discrete_range)][formal_part] ; */
 case 205 :
    node = AST(2);
    id_node = make_id(1);
    N_AST1(node) = id_node;
 
     break;
 /* accept_statement ::= ACCEPT entry_simple_name [(entry_index)][formal_part */
 case 206 :
    node = AST(2);
    erase_labels(node);
    N_AST1(node) = AST(1);
    N_AST4(node) = OPT_NODE;
 
     break;
 /* accept_statement ::= ACCEPT entry_simple_name [(entry_index)][formal_part */
 case 207 :
    node = AST(2);
    if (AST(6) != OPT_NODE
	  && N_ID(AST(1)) != N_ID(AST(6)))
        match_error(N_ID(AST(1)), N_ID(AST(6)),
          "accept_statement", get_left_span_p(AST(6)),
		  get_right_span_p(AST(6)));
    newlabels(node, tup_copy(getlabels(AST(4))));
    N_AST1(node) = AST(1);
    N_AST4(node) = AST(4);
    nodefree(AST(6));
 
 /* entry_index ::= expression */
 /* case 208 : */
 
     break;
 /* delay_statement ::= DELAY simple_expression ; */
 case 209 :
    node = node_new(as_delay);
    insert_1child(node, AST(1));
 
 /* select_statement ::= selective_wait */
 /* case 210 : */
 
 /* select_statement ::= conditional_entry_call */
 /* case 211 : */
 
 /* select_statement ::= timed_entry_call */
 /* case 212 : */
 
     break;
 /* selective_wait ::= SELECT {pragma} select_alternative {OR__select_alterna */
 case 213 :
{
	Tuple nodelabels = tup_new(0);
    int delay_index = 0, terminate_index = 0, has_accept = 0, i = 0;
    int terminate_ct = 0;
    Node delay_ptr = NULL, terminate_ptr = NULL, tmp_alt;

    node = node_new(as_selective_wait);
    check_pragmas(AST(1), null_pragmas);
    N_LIST(AST(3)) = tup_add(tup_with(N_LIST(AST(1)), (char *)AST(2)),
      N_LIST(AST(3)));
	FORTUP(tmp_node = (Node), N_LIST(AST(3)), ft1);
      nodelabels = tup_add(nodelabels, getlabels(tmp_node));
	ENDFORTUP(ft1);
    if (AST(4) != OPT_NODE)
        nodelabels = tup_add(nodelabels, getlabels(AST(4)));
    newlabels(node, nodelabels);
    insert_2child(node, AST(3), AST(4));
    nodefree(AST(1));

	FORTUP(tmp_node = (Node), N_LIST(AST(3)), ft1);
        i++;
        if (N_KIND(tmp_alt = tmp_node) == as_guard)
            tmp_alt = N_AST2(tmp_alt);
        if (N_KIND(tmp_alt) == as_delay_alt) {
            delay_index = i;
            delay_ptr = tmp_alt;
        }
        else if (N_KIND(tmp_alt) == as_terminate_alt) {
            terminate_index = i;
            terminate_ptr = tmp_alt;
            if (++terminate_ct > 1)
                syntax_err(SPAN(terminate_ptr),
     "Only one terminate alternative can appear in a SELECT statement");
        }
        else
            has_accept = 1;
	ENDFORTUP(ft1);
    if (delay_index && terminate_index) {
        tmp_alt = (delay_index > terminate_index) ? delay_ptr : 
          terminate_ptr;
        syntax_err(SPAN(tmp_alt),
"Delay and terminate alternatives cannot appear in the same SELECT statement");
    }
    if ((delay_index || terminate_index) && AST(4) != OPT_NODE)
        syntax_err(SPAN(AST(4)),
          "ELSE part cannot appear in SELECT statement if delay or terminate \
alternatives are present");

    /* A selective_wait must contain at least one accept_alternative */
    if (!has_accept)
        syntax_err(LOC(0), END_LOC(6),
          "SELECT statement must have at least one ACCEPT alternative");
}
 
     break;
 /* select_alternative ::= [WHEN__condition=>] selective_wait_alternative */
 case 214 :
    if (AST(0) == OPT_NODE)
        node = AST(1);
    else {
        node = node_new(as_guard);
        newlabels(node, tup_copy(getlabels(AST(1))));
        insert_2child(node, AST(0), AST(1));
    }
 
 /* selective_wait_alternative ::= accept_alternative */
 /* case 215 : */
 
 /* selective_wait_alternative ::= delay_alternative */
 /* case 216 : */
 
 /* selective_wait_alternative ::= terminate_alternative */
 /* case 217 : */
 
     break;
 /* accept_alternative ::= accept_statement [sequence_of_statements] */
 case 218 :
    node = node_new(as_accept_alt);
    if (AST(1)!=OPT_NODE) {
        newlabels(node, tup_add(getlabels(AST(0)), getlabels(AST(1))));
    }
    else {
        newlabels(node, tup_copy(getlabels(AST(0))));
    }
    insert_2child(node, AST(0), AST(1));
 
     break;
 /* delay_alternative ::= delay_statement [sequence_of_statements] */
 case 219 :
    node = node_new(as_delay_alt);
    if (AST(1) != OPT_NODE)
        newlabels(node, tup_copy(getlabels(AST(1))));
    insert_2child(node, AST(0), AST(1));
 
     break;
 /* terminate_alternative ::= TERMINATE ; {pragma} */
 case 220 :
    node = AST(2);
    check_pragmas(node, null_pragmas);
    erase_labels(node);
    N_KIND(node) = as_terminate_alt;
 
     break;
 /* conditional_entry_call ::= SELECT {pragma} call_statement [sequence_of_st */
 case 221 :
    node = node_new(as_conditional_entry_call);
    check_pragmas(AST(1), null_pragmas);
    pragmalist_warning(AST(1));
    newlabels(node,  tup_add(((AST(3) == OPT_NODE) ? tup_new(0) : 
        getlabels(AST(3))), getlabels(AST(5))));
    insert_3child(node, AST(2), AST(3), AST(5));
    free_everything(AST(1));
 
     break;
 /* timed_entry_call ::= SELECT {pragma} call_statement [sequence_of_statemen */
 case 222 :
    node = node_new(as_timed_entry_call);
    check_pragmas(AST(1), null_pragmas);
    check_pragmas(AST(5), null_pragmas);
    pragmalist_warning(AST(1));
    pragmalist_warning(AST(5));
    newlabels(node, tup_add(((AST(3) == OPT_NODE) ? tup_new(0) :
        getlabels(AST(3))), getlabels(AST(6))));
    free_everything(AST(1));
    free_everything(AST(5));
    insert_3child(node, AST(2), AST(3), AST(6));
 
     break;
 /* abort_statement ::= ABORT task_name {,task_name} ; */
 case 223 :
    node = AST(2);
    prepend(AST(1), node);
    N_KIND(node) = as_abort;
 
 /* compilation ::= {compilation_unit} */
 /* case 224 : */
 
     break;
 /* compilation_unit ::= context_clause library_unit */
 case 225 :
    node = node_new(as_unit);
    insert_2child(node, AST(0), AST(1));
 
     break;
 /* compilation_unit ::= context_clause secondary_unit */
 case 226 :
    node = node_new(as_unit);
    insert_2child(node, AST(0), AST(1));
 
 /* library_unit ::= subprogram_declaration */
 /* case 227 : */
 
 /* library_unit ::= package_declaration */
 /* case 228 : */
 
 /* library_unit ::= generic_declaration */
 /* case 229 : */
 
 /* library_unit ::= generic_instantiation */
 /* case 230 : */
 
 /* library_unit ::= subprogram_body */
 /* case 231 : */
 
 /* secondary_unit ::= library_unit_body */
 /* case 232 : */
 
 /* secondary_unit ::= subunit */
 /* case 233 : */
 
 /* library_unit_body ::= package_body */
 /* case 234 : */
 
 /* context_clause ::= {with_clause{use_clause}} */
 /* case 235 : */
 
     break;
 /* with_clause ::= WITH unit_simple_name {,unit_simple_name} ; */
 case 236 :
    node = AST(2);
    prepend(AST(1), node);
    N_KIND(node) = as_with;
 
     break;
 /* body_stub ::= subprogram_specification IS SEPARATE ; */
 case 237 :
    node = node_new(as_subprogram_stub);
    insert_1child(node, AST(0));
 
     break;
 /* body_stub ::= PACKAGE BODY package_simple_name IS SEPARATE ; */
 case 238 :
    node = AST(2);
    N_KIND(node) = as_package_stub;
 
     break;
 /* body_stub ::= TASK BODY task_simple_name IS SEPARATE ; */
 case 239 :
    node = AST(2);
    N_KIND(node) = as_task_stub;
 
     break;
 /* subunit ::= SEPARATE ( parent_unit_name ) proper_body */
 case 240 :
    node = node_new(as_separate);
    insert_2child(node, AST(2), AST(4));
 
     break;
 /* exception_declaration ::= identifier_list : EXCEPTION ; */
 case 241 :
    node = AST(0);
    N_KIND(node) = as_except_decl;
 
     break;
 /* exception_handler ::= WHEN exception_choice {|exception_choice} => sequen */
 case 242 :
    node = node_new(as_handler);
    prepend(AST(1), AST(2));
    newlabels(node, tup_copy(getlabels(AST(4))));
    insert_2child(node, AST(2), AST(4));
 
 /* exception_choice ::= exception_name */
 /* case 243 : */
 
     break;
 /* exception_choice ::= OTHERS */
 case 244 :
    node = node_new(as_others);
    set_span(node, LOC(0));
 
     break;
 /* raise_statement ::= RAISE [exception_name] ; */
 case 245 :
{
    Node span_node;

    node = node_new(as_raise);
    span_node = node_new(as_simple_name);
    N_ID(span_node) = IND(0);
    set_span(span_node, LOC(0));
    insert_2child(node, AST(1), span_node);
}
 
     break;
 /* generic_declaration ::= generic_specification ; */
 case 246 :
    node = AST(0);
 
     break;
 /* generic_specification ::= generic_formal_part subprogram_specification */
 case 247 :
    if (N_KIND(AST(1)) == as_function) {
        if (N_KIND(N_AST1(AST(1))) == as_operator)
            syntax_err(SPAN(N_AST1(AST(1))),
              "Operator symbol invalid in Generic specification");
        node = node_new(as_generic_function);
        insert_4child(node,  N_AST1(AST(1)), AST(0), N_AST2(AST(1)),
		  N_AST3(AST(1)));
    }
    else {
        node = node_new(as_generic_procedure);
        insert_4child(node, N_AST1(AST(1)), AST(0), N_AST2(AST(1)), OPT_NODE);
    }
/*
    astfree(sub_spec->links.subast);
*/
    nodefree(AST(1));
 
     break;
 /* generic_specification ::= generic_formal_part package_specification */
 case 248 :
    node = node_new(as_generic_package);
    insert_4child(node, N_AST1(AST(1)), AST(0), N_AST2(AST(1)), N_AST3(AST(1)));
/*
    astfree(pack_spec->links.subast);
*/
    nodefree(AST(1));
 
     break;
 /* generic_formal_part ::= GENERIC {generic_parameter_declaration} */
 case 249 :
    node = AST(1);
    N_KIND(node) = as_generic_formals;
 
     break;
 /* generic_parameter_declaration ::= identifier_list : [IN[OUT]] type_mark [ */
 case 250 :
    node = node_new(as_generic_obj);
    insert_4child(node, AST(0), AST(2), AST(3), AST(4));
 
     break;
 /* generic_parameter_declaration ::= TYPE identifier IS generic_type_definit */
 case 251 :
    id_node = make_id(1);
    node = node_new(as_generic_type);
    insert_3child(node, id_node, OPT_NODE, AST(3));
 
     break;
 /* generic_parameter_declaration ::= private_type_declaration */
 case 252 :
    node = AST(0);
    N_KIND(node) = as_gen_priv_type;
 
     break;
 /* generic_parameter_declaration ::= WITH subprogram_specification [IS__name */
 case 253 :
    node = node_new(as_generic_subp);
    insert_2child(node, AST(1), AST(2));
 
     break;
 /* generic_type_definition ::= ( <> ) */
 case 254 :
    node = node_new(as_generic);
    N_ID(node) = namemap("discrete_type", 13);
    set_span(node, LOC(0));
 
     break;
 /* generic_type_definition ::= RANGE <> */
 case 255 :
    node = node_new(as_generic);
    N_ID(node) = namemap("INTEGER", 7);
    set_span(node, LOC(0));
 
     break;
 /* generic_type_definition ::= DIGITS <> */
 case 256 :
    node = node_new(as_generic);
    N_ID(node) = namemap("FLOAT", 5);
    set_span(node, LOC(0));
 
     break;
 /* generic_type_definition ::= DELTA <> */
 case 257 :
    node = node_new(as_generic);
    N_ID(node) = namemap("$FIXED", 6);
    set_span(node, LOC(0));
 
 /* generic_type_definition ::= array_type_definition */
 /* case 258 : */
 
 /* generic_type_definition ::= access_type_definition */
 /* case 259 : */
 
     break;
 /* generic_instantiation ::= PACKAGE identifier IS NEW generic_package_name  */
 case 260 :
    id_node = make_id(1);
    node = node_new(as_package_instance);
    insert_3child(node, id_node, AST(4), AST(5));
 
     break;
 /* generic_instantiation ::= FUNCTION designator IS NEW generic_function_nam */
 case 261 :
    node = node_new(as_function_instance);
    insert_3child(node, AST(1), AST(4), AST(5));
 
     break;
 /* generic_instantiation ::= subprogram_specification IS NEW generic_procedu */
 case 262 :
    if (N_KIND(AST(0)) != as_procedure)
        syntax_err(SPAN(AST(0)), "Bad generic procedure instantiation");
    if (N_AST2(AST(0)) != OPT_NODE)
        syntax_err(SPAN(AST(0)),
            "formal_part not allowed in procedure instantiation");
    node = node_new(as_procedure_instance);
    insert_3child(node, N_AST1(AST(0)), AST(3), AST(4));
/*
    FREEAST(sub_spec, 1);
    astfree(sub_spec->links.subast);
*/
    nodefree(AST(0));
 
     break;
 /* generic_actual_part ::= ( generic_association {,generic_association} ) */
 case 263 :
    node = AST(2);
    prepend(AST(1), node);
 
 /* generic_association ::= [generic_formal_parameter=>]generic_actual_parame */
 /* case 264 : */
 
 /* generic_formal_parameter ::= parameter_simple_name */
 /* case 265 : */
 
     break;
 /* generic_formal_parameter ::= operator_symbol */
 case 266 :
{
    char tmp[MAXLINE + 1];

    node = AST(0);
    strcpy(tmp, namelist(N_ID(node)));
    convtolower(tmp);
    if (!isoverloadable_op(tmp)) {
        char msg[MAXLINE + 30];

        sprintf(msg, "\"%s\" is not a valid operator_symbol", tmp);
        syntax_err(get_left_span_p(node), get_right_span_p(node), msg);
    }
    N_ID(node) = namemap(tmp, strlen(tmp));
}
 
 /* generic_actual_parameter ::= expression */
 /* case 267 : */
 
     break;
 /* representation_clause ::= type_representation_clause */
 case 268 :
    node = AST(0);
 
     break;
 /* representation_clause ::= address_clause */
 case 269 :
    node = AST(0);
    syntax_err(SPAN(node), "address_clause not supported");
 
 /* type_representation_clause ::= length_clause */
 /* case 270 : */
 
 /* type_representation_clause ::= enumeration_representation_clause */
 /* case 271 : */
 
 /* type_representation_clause ::= record_representation_clause */
 /* case 272 : */
 
     break;
 /* length_clause ::= FOR attribute USE simple_expression ; */
 case 273 :
    node = node_new(as_length_clause);
    insert_2child(node, AST(1), AST(3));
 
     break;
 /* enumeration_representation_clause ::= FOR type_simple_name USE aggregate  */
 case 274 :
    node = node_new(as_enum_rep_clause);
    insert_2child(node, AST(1), AST(3));
 
     break;
 /* record_representation_clause ::= FOR type_simple_name USE RECORD [alignme */
 case 275 :
    node = node_new(as_rec_rep_clause);
    insert_3child(node, AST(1), AST(4), AST(5));
 
     break;
 /* alignment_clause ::= AT MOD static_simple_expression ; */
 case 276 :
    node = AST(2);    
 
     break;
 /* component_clause ::= component_name AT static_simple_expression RANGE sta */
 case 277 :
    node = node_new(as_compon_clause);
    if (N_KIND(AST(4)) != as_range && N_KIND(AST(4))!= as_range_attribute)
        syntax_err(SPAN(AST(4)), "Invalid range specification");
    insert_3child(node, AST(0), AST(2), AST(4));
 
     break;
 /* address_clause ::= FOR simple_name USE AT simple_expression ; */
 case 278 :
    node = node_new(as_address_clause);
    insert_2child(node, AST(1), AST(4));
 
     break;
 /* code_statement ::= name ' record_aggregate ; */
 case 279 :
    if (!check_expanded_name(AST(0)))
        syntax_err(SPAN(AST(0)), "Invalid type_mark in code statement");
    node = node_new(as_code);
    insert_2child(node, AST(0), AST(2));
 
 
     break;
 /* {PRAGMA} ::= empty */
 case 280 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {PRAGMA} ::= {pragma} pragma */
 case 281 :
    node = AST(0);
    if (AST(1) != any_node)
        append(node, AST(1));
 
 
     break;
 /* [(argument_association{,argument_association})] ::= empty */
 case 282 :
 node = OPT_NODE;
 
     break;
 /* [(argument_association{,argument_association})] ::= ( argument_associatio */
 case 283 :
    node = AST(1);
 
     break;
 /* argument_association_list ::= argument_association */
 case 284 :
    node = node_new(as_arg_assoc_list);
    N_LIST(node) = tup_new1((char *)AST(0));
 
     break;
 /* argument_association_list ::= argument_association_list , argument_associ */
 case 285 :
    node = AST(0);
    append(node, AST(2));
 
     break;
 /* [argument_identifier=>]expression ::= expression */
 case 286 :
    node = node_new(as_arg);
    insert_2child(node, OPT_NODE, AST(0));
 
     break;
 /* [argument_identifier=>]expression ::= argument_identifier => expression */
 case 287 :
 
    id_node = make_id(0);
    node = node_new(as_arg);
    insert_2child(node, id_node, AST(2));
 
 
     break;
 /* [:=expression] ::= empty */
 case 288 :
 node = OPT_NODE;
 
     break;
 /* [:=expression] ::= := expression */
 case 289 :
    node = AST(1);
 
 
     break;
 /* [CONSTANT] ::= empty */
 case 290 :
 node = OPT_NODE;
 
     break;
 /* [CONSTANT] ::= CONSTANT */
 case 291 :
    node = any_node;
 
 
     break;
 /* {,identifier} ::= empty */
 case 292 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {,identifier} ::= {,identifier} , identifier */
 case 293 :
    node = AST(0);
    id_node = make_id(2);
    append(node, id_node);
 
 
     break;
 /* [discriminant_part]IS ::= IS */
 case 294 :
 node = OPT_NODE;
 
     break;
 /* [discriminant_part]IS ::= discriminant_part IS */
 case 295 :
    node = AST(0);
 
 
     break;
 /* [constraint] ::= empty */
 case 296 :
 node = OPT_NODE;
 
 /* [constraint] ::= constraint */
 /* case 297 : */
 
     break;
 /* expanded_name ::= identifier */
 case 298 :
    node = node_new(as_simple_name);
    N_ID(node) = IND(0);
    set_span(node, LOC(0));
 
     break;
 /* expanded_name ::= expanded_name . identifier */
 case 299 :
    id_node = make_id(2);
    node = node_new(as_selector);
    insert_2child(node, AST(0), id_node);
 
 
     break;
 /* {,enumeration_literal_specification} ::= empty */
 case 300 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {,enumeration_literal_specification} ::= {,enumeration_literal_specificat */
 case 301 :
    node = AST(0);
    append(node, AST(2));
 
 
     break;
 /* [range_constraint] ::= empty */
 case 302 :
 node = OPT_NODE;
 
 /* [range_constraint] ::= range_constraint */
 /* case 303 : */
 
 
     break;
 /* {,index_subtype_definition} ::= empty */
 case 304 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {,index_subtype_definition} ::= {,index_subtype_definition} , index_subty */
 case 305 :
    node = AST(0);
    append(node, AST(2));
 
 
     break;
 /* {,discrete_range} ::= empty */
 case 306 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {,discrete_range} ::= {,discrete_range} , discrete_range */
 case 307 :
    node = AST(0);
    append(node, AST(2));
 
 
     break;
 /* {component_declaration} ::= empty */
 case 308 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {component_declaration} ::= {component_declaration} component_declaration */
 case 309 :
    node = AST(0);
    check_pragmas(AST(2), null_pragmas);
    N_LIST(node) = tup_add(tup_with(N_LIST(node), (char *)AST(1)),
      N_LIST(AST(2)));
    nodefree(AST(2));
 
 
     break;
 /* {;discriminant_specification} ::= empty */
 case 310 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {;discriminant_specification} ::= {;discriminant_specification} ; discrim */
 case 311 :
    node = AST(0);
    append(node, AST(2));
 
 
     break;
 /* {variant} ::= empty */
 case 312 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {variant} ::= {variant} variant */
 case 313 :
    node = AST(0);
    append(node, AST(1));
 
 
     break;
 /* {|choice} ::= empty */
 case 314 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {|choice} ::= {|choice} '|' choice */
 case 315 :
    node = AST(0);
    append(node, AST(2));
 
 
     break;
 /* [discriminant_part]; ::= ; */
 case 316 :
 node = OPT_NODE;
 
     break;
 /* [discriminant_part]; ::= discriminant_part ; */
 case 317 :
    node  = AST(0);
 
     break;
 /* {basic_declarative_item} ::= {pragma} */
 case 318 :
    check_pragmas(AST(0), immediate_decl_pragmas);
    node = AST(0);
 
     break;
 /* {basic_declarative_item} ::= {basic_declarative_item} basic_declarative_i */
 case 319 :
    node = AST(0);
    check_pragmas(AST(2), immediate_decl_pragmas);
    N_LIST(node) = tup_add(tup_with(N_LIST(node), (char *)AST(1)),
      N_LIST(AST(2)));
    nodefree(AST(2));
 
 
     break;
 /* {,component_association} ::= empty */
 case 320 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {,component_association} ::= {,component_association} , component_associa */
 case 321 :
    node = AST(0);
    append(node, AST(2));
 
 /* [choice{|choice}=>]expression ::= expression */
 /* case 322 : */
 
     break;
 /* [choice{|choice}=>]expression ::= choice {|choice} => expression */
 case 323 :
    prepend(AST(0), AST(1));
    node = node_new(as_choice_list);
    insert_2child(node, AST(1), AST(3));
 
 
     break;
 /* {,general_component_association} ::= empty */
 case 324 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {,general_component_association} ::= {,general_component_association} , g */
 case 325 :
    node = AST(0);
    append(node, AST(2));
 
     break;
 /* relation{AND__relation} ::= relation AND relation */
 case 326 :
 
 /* relation{AND__relation} ::= relation{AND__relation} AND relation */
 case 327 :
 
 /* relation{OR__relation} ::= relation OR relation */
 case 328 :
 
 /* relation{OR__relation} ::= relation{OR__relation} OR relation */
 case 329 :
 
 /* relation{XOR__relation} ::= relation XOR relation */
 case 330 :
 
 /* relation{XOR__relation} ::= relation{XOR__relation} XOR relation */
 case 331 :
    id_node = make_id(1);
    node = binary_operator(id_node, AST(0), AST(2));
 
     break;
 /* relation{AND__THEN__relation} ::= relation AND THEN relation */
 case 332 :
 
 /* relation{AND__THEN__relation} ::= relation{AND__THEN__relation} AND THEN  */
 case 333 :
{
    Node optr_node;

    optr_node = node_new(as_simple_name);
    N_ID(optr_node) = namemap("andthen", 7);
    set_span(optr_node, LOC(1));
    node = binary_operator(optr_node, AST(0), AST(3));
}
 
     break;
 /* relation{OR__ELSE__relation} ::= relation OR ELSE relation */
 case 334 :
 
 /* relation{OR__ELSE__relation} ::= relation{OR__ELSE__relation} OR ELSE rel */
 case 335 :
{
    Node optr_node;

    optr_node = node_new(as_simple_name);
    N_ID(optr_node) = namemap("orelse", 6);
    set_span(optr_node, LOC(1));
    node = binary_operator(optr_node, AST(0), AST(3));
}
 
 
     break;
 /* [relational_operator__simple_expression] ::= empty */
 case 336 :
 node = OPT_NODE;
 
     break;
 /* [relational_operator__simple_expression] ::= relational_operator simple_e */
 case 337 :
    node = binary_operator(AST(0), any_node, AST(1));
 
 
     break;
 /* [NOT] ::= empty */
 case 338 :
 node = OPT_NODE;
 
     break;
 /* [NOT] ::= NOT */
 case 339 :
    node = any_node;
 
 /* [unary_adding_operator]term{binary_adding_operator__term} ::= term */
 /* case 340 : */
 
     break;
 /* [unary_adding_operator]term{binary_adding_operator__term} ::= unary_addin */
 case 341 :
    node = unary_operator(AST(0), AST(1));
 
     break;
 /* [unary_adding_operator]term{binary_adding_operator__term} ::= [unary_addi */
 case 342 :
    node = binary_operator(AST(1), AST(0), AST(2));
 
 /* factor{multiplying_operator__factor} ::= factor */
 /* case 343 : */
 
     break;
 /* factor{multiplying_operator__factor} ::= factor{multiplying_operator__fac */
 case 344 :
    node = binary_operator(AST(1), AST(0), AST(2));
 
 
     break;
 /* [**__primary] ::= empty */
 case 345 :
 node = OPT_NODE;
 
     break;
 /* [**__primary] ::= ** primary */
 case 346 :
    id_node = make_id(0);
    node = binary_operator(id_node, any_node, AST(1));
 
     break;
 /* {statement} ::= {pragma} */
 case 347 :
    check_pragmas(AST(0), null_pragmas);
    node = AST(0);
 
     break;
 /* {statement} ::= {statement} statement {pragma} */
 case 348 :
    node = AST(0);
    check_pragmas(AST(2), null_pragmas);
    N_LIST(node) = tup_add(tup_with(N_LIST(node), (char *)AST(1)),
	  N_LIST(AST(2)));
    nodefree(AST(2));
 
 
     break;
 /* {label} ::= empty */
 case 349 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {label} ::= {label} label */
 case 350 :
    node = AST(0);
    append(node, AST(1));
 
 
     break;
 /* {ELSIF__condition__THEN__sequence_of_statements} ::= empty */
 case 351 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {ELSIF__condition__THEN__sequence_of_statements} ::= {ELSIF__condition__T */
 case 352 :
{
    Node if_node;
    
    node = AST(0);
    if_node = node_new(as_cond_statements);
	insert_2child(if_node, AST(2), AST(4));
    append(node, if_node);
}
 
 
     break;
 /* [ELSE__sequence_of_statements] ::= empty */
 case 353 :
 node = OPT_NODE;
 
     break;
 /* [ELSE__sequence_of_statements] ::= ELSE sequence_of_statements */
 case 354 :
    node = AST(1);
 
 
     break;
 /* {case_statement_alternative} ::= empty */
 case 355 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {case_statement_alternative} ::= {case_statement_alternative} case_statem */
 case 356 :
    node = AST(0);
    append(node, AST(1));
 
 
     break;
 /* [simple_name:] ::= empty */
 case 357 :
 node = OPT_NODE;
 
     break;
 /* [simple_name:] ::= simple_name : */
 case 358 :
    node = AST(0);
 
 
     break;
 /* [simple_name] ::= empty */
 case 359 :
 node = OPT_NODE;
 
 /* [simple_name] ::= simple_name */
 /* case 360 : */
 
 
     break;
 /* [iteration_scheme] ::= empty */
 case 361 :
 node = OPT_NODE;
 
 /* [iteration_scheme] ::= iteration_scheme */
 /* case 362 : */
 
 
     break;
 /* [REVERSE] ::= empty */
 case 363 :
 node = OPT_NODE;
 
     break;
 /* [REVERSE] ::= REVERSE */
 case 364 :
    node = any_node;
 
     break;
 /* [DECLARE__declarative_part] ::= empty */
 case 365 :
    node = node_new(as_declarations);
    N_LIST(node) = tup_new(0);
 
     break;
 /* [DECLARE__declarative_part] ::= DECLARE declarative_part */
 case 366 :
    node = AST(1);
 
 
     break;
 /* [EXCEPTION__exception_handler{exception_handler}] ::= empty */
 case 367 :
 node = OPT_NODE;
 
     break;
 /* [EXCEPTION__exception_handler{exception_handler}] ::= EXCEPTION {pragma}  */
 case 368 :
{
	Tuple nodelabels = tup_new(0);

    node = AST(2);
    check_pragmas(AST(1), null_pragmas);
	FORTUP(tmp_node = (Node), N_LIST(node), ft1);
        nodelabels = tup_add(nodelabels, getlabels(tmp_node));
	ENDFORTUP(ft1);
    newlabels(node, nodelabels);
    N_KIND(node) = as_exception;
    N_LIST(node) = tup_add(N_LIST(AST(1)), N_LIST(node));
    check_choices(node, "an exception_handler list");
    nodefree(AST(1));
}
 
     break;
 /* exception_handler_list ::= exception_handler */
 case 369 :
    node = node_new(as_list);
    N_LIST(node) = tup_new1((char *)AST(0));
 
     break;
 /* exception_handler_list ::= exception_handler_list exception_handler */
 case 370 :
    node = AST(0);
    append(node, AST(1));
 
 
     break;
 /* [expanded_name] ::= empty */
 case 371 :
 node = OPT_NODE;
 
 /* [expanded_name] ::= expanded_name */
 /* case 372 : */
 
 
     break;
 /* [WHEN__condition] ::= empty */
 case 373 :
 node = OPT_NODE;
 
     break;
 /* [WHEN__condition] ::= WHEN condition */
 case 374 :
    node = AST(1);
 
 
     break;
 /* [expression] ::= empty */
 case 375 :
 node = OPT_NODE;
 
 /* [expression] ::= expression */
 /* case 376 : */
 
 
     break;
 /* [formal_part] ::= empty */
 case 377 :
 node = OPT_NODE;
 
 /* [formal_part] ::= formal_part */
 /* case 378 : */
 
 
     break;
 /* {;parameter_specification} ::= empty */
 case 379 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {;parameter_specification} ::= {;parameter_specification} ; parameter_spe */
 case 380 :
    node = AST(0);
    append(node, AST(2));
 
     break;
 /* [IN] ::= empty */
 case 381 :
    node = node_new(as_mode);
    N_ID(node) = namemap("", 0);
    set_span(node, &curtok->ptr.token->span);
 
     break;
 /* [IN] ::= IN */
 case 382 :
    node = node_new(as_mode);
    N_ID(node) = namemap("in", 2);
    set_span(node, LOC(0));
 
 
     break;
 /* [designator] ::= empty */
 case 383 :
 node = OPT_NODE;
 
 /* [designator] ::= designator */
 /* case 384 : */
 
 
     break;
 /* [PRIVATE{basic_declarative_item}] ::= empty */
 case 385 :
 node = OPT_NODE;
 
     break;
 /* [PRIVATE{basic_declarative_item}] ::= PRIVATE {basic_declarative_item} */
 case 386 :
    node = AST(1);
	FORTUP(tmp_node = (Node), N_LIST(node), ft1);
        if (isbody_node[N_KIND(tmp_node)])
            syntax_err(SPAN(tmp_node),
     "Body declaration not allowed in private part of package_specification");
    ENDFORTUP(ft1);
    N_KIND(node) = as_declarations;
    ins_as_line_no(node);
 
 
     break;
 /* [LIMITED] ::= empty */
 case 387 :
 node = OPT_NODE;
 
     break;
 /* [LIMITED] ::= LIMITED */
 case 388 :
    node = any_node;
    set_span(node, LOC(0));
 
 
     break;
 /* {,package_name} ::= empty */
 case 389 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {,package_name} ::= {,package_name} , package_name */
 case 390 :
    node = AST(0);
    append(node, AST(2));
 
     break;
 /* identifier:type_mark ::= identifier_list : type_mark */
 case 391 :
{
	id_node = (Node) N_LIST(AST(0))[1];
	if(tup_size(N_LIST(AST(0))) != 1) {
        syntax_err(get_left_span_p(AST(0)), get_right_span_p(AST(2)),
          "Only one identifier is allowed in this context");
		tup_fromb(N_LIST(AST(0)));
    }
    else
        N_LIST(AST(0)) = tup_new(0);
/* HMMMM????? - AST(0) free-ed andyway
    TFREE(tmp, tmp);
*/
    free_everything(AST(0));
    node = node_new(as_rename_obj);
    insert_3child(node, id_node, AST(2), any_node);
}
 
     break;
 /* identifier:EXCEPTION ::= identifier_list : EXCEPTION */
 case 392 :
{
	id_node = (Node) N_LIST(AST(0))[1];
	if(tup_size(N_LIST(AST(0))) != 1) {
        syntax_err(get_left_span_p(AST(0)), END_LOC(2),
          "Only one identifier is allowed in this context");
		tup_fromb(N_LIST(AST(0)));
    }
    else
        N_LIST(AST(0)) = tup_new(0);
/* ???? see above
    TFREE(tmp, tmp);
*/
    free_everything(AST(0));
    node = node_new(as_rename_ex);
    insert_2child(node, id_node, any_node);
}
 
 
     break;
 /* [TYPE] ::= empty */
 case 393 :
 node = OPT_NODE;
 
     break;
 /* [TYPE] ::= TYPE */
 case 394 :
    node = any_node;
 
     break;
 /* {entry_declaration} ::= {pragma} */
 case 395 :
    node = AST(0);
    check_pragmas(node, task_pragmas);
 
     break;
 /* {entry_declaration} ::= {entry_declaration} entry_declaration {pragma} */
 case 396 :
    node = AST(0);
    check_pragmas(AST(2), task_pragmas);
    N_LIST(node) = tup_add(tup_with(N_LIST(node), (char *)AST(1)),
      N_LIST(AST(2)));
    nodefree(AST(2));
 
 
     break;
 /* {representation_clause} ::= empty */
 case 397 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {representation_clause} ::= {representation_clause} representation_clause */
 case 398 :
    node = AST(0);
    check_pragmas(AST(2), task_repr_pragmas);
    N_LIST(node) = tup_add(tup_with(N_LIST(node), (char *)AST(1)),
      N_LIST(AST(2)));
    nodefree(AST(2));
 
     break;
 /* [(discrete_range)][formal_part] ::= [formal_part] */
 case 399 :
    node = node_new(as_entry);
    insert_2child(node, any_node, AST(0));
    set_span(any_node, get_left_span_p(AST(0))); /* kludge for errors */
 
     break;
 /* [(discrete_range)][formal_part] ::= ( discrete_range ) [formal_part] */
 case 400 :
    check_discrete_range(AST(1));
    node = node_new(as_entry_family);
    insert_3child(node, any_node, AST(1), AST(3));
 
     break;
 /* [(entry_index)][formal_part] ::= [formal_part] */
 case 401 :
    node = node_new(as_accept);
    insert_4child(node, any_node, OPT_NODE, AST(0), any_node);
 
     break;
 /* [(entry_index)][formal_part] ::= ( entry_index ) [formal_part] */
 case 402 :
    node = node_new(as_accept);
    insert_4child(node, any_node, AST(1), AST(3), any_node);
 
 
     break;
 /* {OR__select_alternative} ::= empty */
 case 403 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {OR__select_alternative} ::= {OR__select_alternative} OR {pragma} select_ */
 case 404 :
    node = AST(0);
    check_pragmas(AST(2), null_pragmas);
    N_LIST(node) = tup_with(tup_add(N_LIST(node), N_LIST(AST(2))),
     (char *) AST(3));
    nodefree(AST(2));
 
 
     break;
 /* [WHEN__condition=>] ::= empty */
 case 405 :
 node = OPT_NODE;
 
     break;
 /* [WHEN__condition=>] ::= WHEN condition => {pragma} */
 case 406 :
    node = AST(1);
    check_pragmas(AST(3), null_pragmas);
    pragmalist_warning(AST(3));
    free_everything(AST(3));
 
     break;
 /* [sequence_of_statements] ::= {pragma} */
 case 407 :
    check_pragmas(AST(0), null_pragmas);
    if (tup_size(N_LIST(AST(0)))) {
        Node label_list_node;

        node = node_new(as_statements);
        label_list_node = node_new(as_list);
        N_LIST(label_list_node) = tup_new(0);
		set_span(label_list_node, &curtok->ptr.token->span);
        insert_2child(node, AST(0), label_list_node);
    }
    else
        node = OPT_NODE;
 	set_span(node, &curtok->ptr.token->span);
 
 /* [sequence_of_statements] ::= sequence_of_statements */
 /* case 408 : */
 
 
     break;
 /* {,task_name} ::= empty */
 case 409 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {,task_name} ::= {,task_name} , task_name */
 case 410 :
    node = AST(0);
    append(node, AST(2));
 
     break;
 /* {compilation_unit} ::= {pragma} */
 case 411 :
    check_pragmas(AST(0), compilation_pragmas);
/* This seems to be never used
		if (astopt)
			print_tree(AST(0));
*/
    if (curtok->symbol != EOFT_SYM) {
        free_everything(AST(0));
        free_labels();
    }
    prs_stack->symbol = lhs[red];
    return;
 
     break;
 /* {compilation_unit} ::= {compilation_unit} compilation_unit {pragma} */
 case 412 :
{
	extern int unit_number_now, unit_numbers, seq_node_n;
	extern char** seq_node;
	Node snode;
	int i;

    node = AST(0);
    check_pragmas(AST(2), after_libunit_pragmas);
    pragmalist_warning(AST(2));
	unit_number_now = unit_numbers + 1;
/*
	snode = cvt_tree(AST(1));
	adasem(seq_node[seq_node_n]);
*/
	for (i = 1; i <= seq_node_n; i++) {
		Node tmp_node = (Node) seq_node[i];
		if (!tmp_node) continue;
		if (N_KIND(tmp_node) == as_line_no) continue;
/*
		if (N_AST1(tmp_node) == (Node)0) N_AST1(tmp_node) = OPT_NODE;
		if (N_AST2(tmp_node) == (Node)0) N_AST2(tmp_node) = OPT_NODE;
		if (N_AST3(tmp_node) == (Node)0) N_AST3(tmp_node) = OPT_NODE;
		if (N_AST4(tmp_node) == (Node)0) N_AST4(tmp_node) = OPT_NODE;
*/
		if (N_KIND(tmp_node) == as_attribute
		  || N_KIND(tmp_node) == as_range_attribute) attrnum(tmp_node);
		/* Write the val (N_VAL) */
		if (isval_node[N_KIND(tmp_node)]) {
			if (N_KIND(tmp_node) == as_mode) {
				switch(strlen(namelist(N_ID(tmp_node)))) {
				case 0:
					N_VAL(tmp_node) = (char *)0;
					break;
				case 2:
					N_VAL(tmp_node) = (char *)na_in;
					break;
				case 3:
					N_VAL(tmp_node) = (char *)na_out;
					break;
				case 5:
					N_VAL(tmp_node) = (char *)na_inout;
					break;
				default:
					printf("node type as_mode invalid argument type %s\n",
					  namelist(N_ID(tmp_node)));
					/*** Something more clever ***/
				}
			}
			else
			   N_VAL(tmp_node)=strjoin(namelist(N_ID(tmp_node)),"");
		}
	}
	adasem(AST(1));
	seq_node_n = 0;
    if (curtok->symbol != EOFT_SYM) {
        free_everything(AST(1));
        free_everything(AST(2));
        free_labels();
    }
}
 
 
     break;
 /* {with_clause{use_clause}} ::= empty */
 case 413 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {with_clause{use_clause}} ::= {with_clause{use_clause}} with_clause use_c */
 case 414 :
    node = AST(0);
    N_KIND(AST(2)) = as_with_use_list;
    prepend(AST(1), AST(2));
    append(node, AST(2));
 
     break;
 /* use_clause_list ::= {pragma} */
 case 415 :
    node = AST(0);
    check_pragmas(node, context_pragmas);
 
     break;
 /* use_clause_list ::= use_clause_list use_clause {pragma} */
 case 416 :
    node = AST(0);
    check_pragmas(AST(2), context_pragmas);
    N_LIST(node) = tup_add(tup_with(N_LIST(node), (char *)AST(1)),
      N_LIST(AST(2)));
    nodefree(AST(2));
 
 
     break;
 /* {,unit_simple_name} ::= empty */
 case 417 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {,unit_simple_name} ::= {,unit_simple_name} , unit_simple_name */
 case 418 :
    node = AST(0);
    append(node, AST(2));
 
 
     break;
 /* {|exception_choice} ::= empty */
 case 419 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {|exception_choice} ::= {|exception_choice} '|' exception_choice */
 case 420 :
    node = AST(0);
    append(node, AST(2));
 
 
     break;
 /* {generic_parameter_declaration} ::= empty */
 case 421 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {generic_parameter_declaration} ::= {generic_parameter_declaration} gener */
 case 422 :
    node = AST(0);
    append(node, AST(1));
 
 /* [IN[OUT]] ::= [IN] */
 /* case 423 : */
 
     break;
 /* [IN[OUT]] ::= IN OUT */
 case 424 :
    node = node_new(as_mode);
    N_ID(node) = namemap("inout", 5);
    set_span(node, LOC(0));
 
 
     break;
 /* [IS__name__or__<>] ::= empty */
 case 425 :
 node = OPT_NODE;
 
     break;
 /* [IS__name__or__<>] ::= IS name */
 case 426 :
    node = AST(1);
 
     break;
 /* [IS__name__or__<>] ::= IS <> */
 case 427 :
    node = node_new(as_simple_name);
    N_ID(node) = namemap("box", 3);
    set_span(node, LOC(1));
 
 
     break;
 /* [generic_actual_part] ::= empty */
 case 428 :
 node = OPT_NODE;
 
 /* [generic_actual_part] ::= generic_actual_part */
 /* case 429 : */
 
 
     break;
 /* {,generic_association} ::= empty */
 case 430 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {,generic_association} ::= {,generic_association} , generic_association */
 case 431 :
    node = AST(0);
    append(node, AST(2));
 
     break;
 /* [generic_formal_parameter=>]generic_actual_parameter ::= generic_actual_p */
 case 432 :
    node = node_new(as_instance);
    insert_2child(node, OPT_NODE, AST(0));
 
     break;
 /* [generic_formal_parameter=>]generic_actual_parameter ::= generic_formal_p */
 case 433 :
    node = node_new(as_instance);
    insert_2child(node, AST(0), AST(2));
 
     break;
 /* [alignment_clause] ::= {pragma} */
 case 434 :
    check_pragmas(AST(0), null_pragmas);
    pragmalist_warning(AST(0));
    node = OPT_NODE;
    set_span(node, &curtok->ptr.token->span);
    free_everything(AST(0));
 
     break;
 /* [alignment_clause] ::= {pragma} alignment_clause {pragma} */
 case 435 :
    node = AST(1);
    check_pragmas(AST(0), null_pragmas);
    check_pragmas(AST(2), null_pragmas);
    pragmalist_warning(AST(0));
    pragmalist_warning(AST(2));
    free_everything(AST(0));
    free_everything(AST(2));
 
 
     break;
 /* {component_clause} ::= empty */
 case 436 :
 node = node_new(as_list);
 N_LIST(node) = tup_new(0);
 set_span(node, &curtok->ptr.token->span);
 
     break;
 /* {component_clause} ::= {component_clause} component_clause {pragma} */
 case 437 :
    node = AST(0);
    check_pragmas(AST(2), null_pragmas);
    pragmalist_warning(AST(2));
    append(node, AST(1));
    free_everything(AST(2));
     break;
    default :
        prs_stack->symbol = lhs[red];
        return;
    }
    prs_stack->symbol = lhs[red];
    prs_stack->ptr.ast = node;
    for (n = rhslen[red]; n--;)
        if (ISTOKEN(rh[n]))
            TOKFREE(rh[n]->ptr.token);
}

static Node make_id(int n)										/*;make_id*/
{
	/* Allocate a node for a simple name whose value and span are* known by
	 * looking at the nth symbol in the right hand side of the reduction,
	 * and set these fields.
	 */
	Node node = node_new(as_simple_name);
	N_ID(node) = IND(n);
	set_span(node, LOC(n));
	return node;
}

