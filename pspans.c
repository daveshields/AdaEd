/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "hdr.h"
#include "vars.h"
#include "ada.h"
#include "miscprots.h"
#include "adalexprots.h"
#include "pspansprots.h"

extern char *emalloc();

int is_terminal_node_p(short node_kind)					/*;is_terminal_node_p*/
{
	return (
	    node_kind == as_string ||
	    node_kind == as_string_literal ||
	    node_kind == as_character_literal ||
	    node_kind == as_int_literal ||
	    node_kind == as_real_literal ||
	    node_kind == as_simple_name ||
	    node_kind == as_operator ||
	    node_kind == as_mode ||
	    node_kind == as_package_stub ||
	    node_kind == as_task_stub ||
	    node_kind == as_null ||
	    node_kind == as_null_s ||
	    node_kind == as_others ||
	    node_kind == as_generic ||
	    node_kind == as_line_no 
	    );
}

Span get_left_span_p(Node node)			/*;get_left_span_p*/
{
	short nkind,first;
	Node firstelem;

	nkind = N_KIND(node);
	if (is_terminal_node_p(nkind))
		return N_SPAN(node);
	else if (nkind == as_opt)
		return N_SPAN(node);
	else if (nkind == as_exit) {
		return get_left_span_p(N_AST4(node));
	}
	else if (nkind == as_return) {
		return get_left_span_p(N_AST4(node));
	}
	else if (nkind == as_raise) {
		return get_left_span_p(N_AST2(node));
	}
	else if (nkind == as_others_choice) {
		return get_left_span_p(N_AST3(node));
	}
	else if (islist_node[nkind]) {
		if (!tup_size(N_LIST(node))) /* only for parser */
			return N_SPAN(node);
		else {
			firstelem = (Node)N_LIST(node)[1];/* first list element */
			if (firstelem == OPT_NODE)
				chaos("get_left_span_p: list element OPT_NODE");
			return get_left_span_p(firstelem);
		}
	}
	else if (isast_node[nkind]) {
		firstelem = (Node)0;
		if (N_AST1(node) != OPT_NODE && N_AST1(node) != (Node )0)
			firstelem = N_AST1(node);
		else if (N_AST2_DEFINED(nkind)) {
			if (N_AST2(node) != OPT_NODE && N_AST2(node) != (Node )0)
				firstelem = N_AST2(node);
			else if (N_AST3_DEFINED(nkind)) {
				if (N_AST3(node) != OPT_NODE && N_AST3(node) != (Node )0)
					firstelem = N_AST3(node);
				else if (N_AST4_DEFINED(nkind)) {
					if (N_AST4(node) != OPT_NODE && N_AST4(node) != (Node )0)
						firstelem = N_AST4(node);
				}
			}
		}
		if (firstelem)
			return get_left_span_p(firstelem);
		else {
			printf("node kind %d\n",nkind);
			chaos("get_left_span_p: all ast's are OPT_NODE");
		}
	}
	else printf("get_left_span_p: bad node kind %d\n",nkind);
	chaos("get_left_span_p");
	return (Span)0;
}

Span get_right_span_p(Node node)		/*;get_right_span_p*/
{
	short nkind,last,length=1;
	Node lastelem;

	nkind = N_KIND(node);
	if (is_terminal_node_p(nkind)) {
		if (isval_node[nkind])
			/* as_null, as_null_s, as_others, as_others_choice
			 * have no N_VAL field defined
			 */
			length = strlen(namelist(N_ID(node)));
		return (make_span(N_SPAN0(node), N_SPAN1(node)+length-1));
	}
	else if (nkind == as_opt)
		return N_SPAN(node);
	else if (nkind == as_exit) {
		if (N_AST2(node) != OPT_NODE)
			return get_right_span_p(N_AST2(node));
		else if (N_AST1(node) != OPT_NODE)
			return get_right_span_p(N_AST1(node));
		else return get_right_span_p(N_AST4(node));
	}
	else if (nkind == as_return) {
		if (N_AST1(node) != OPT_NODE)
			return get_right_span_p(N_AST1(node));
		else return get_right_span_p(N_AST4(node));
	}
	else if (nkind == as_raise) {
		if (N_AST1(node) != OPT_NODE)
			return get_right_span_p(N_AST1(node));
		else return get_right_span_p(N_AST2(node));
	}
	else if (nkind == as_others_choice) {
		if (N_AST2(node) != OPT_NODE)
			return get_right_span_p(N_AST2(node));
		else if (N_AST1(node) != OPT_NODE)
			return get_right_span_p(N_AST1(node));
		else return get_right_span_p(N_AST3(node));
	}
	else if (islist_node[nkind]) {
		if (!tup_size(N_LIST(node))) /* only for parser */
			return N_SPAN(node);
		else {
			lastelem = (Node)N_LIST(node)[tup_size(N_LIST(node))];
#ifdef TODO
			-- this finds next element in list. we need to search backwards !!!
			    while ((lastelem)->val.node == OPT_NODE) {
				lastelem = lastelem->link; /* last list element */
				if (lastelem == node->links.list)
					chaos("get_right_span_p: all list elements OPT_NODE");
			}
#endif
			if (lastelem == OPT_NODE)
				chaos("get_right_span_p: list element OPT_NODE");
			return get_right_span_p(lastelem);
		}
	}
	else if (isast_node[nkind]) {
		if (N_AST4_DEFINED(nkind) && N_AST4(node) != OPT_NODE 
		    && N_AST4(node) != (Node )0)
			lastelem = N_AST4(node);
		else if (N_AST3_DEFINED(nkind) && 
		    N_AST3(node) != OPT_NODE && N_AST3(node) != (Node )0)
			lastelem = N_AST3(node);
		else if (N_AST2_DEFINED(nkind) && 
		    N_AST2(node) != OPT_NODE && N_AST2(node) != (Node )0)
			lastelem = N_AST2(node);
		else if (N_AST1(node) == OPT_NODE && N_AST1(node) == (Node )0)
			chaos("get_right_span_p: all ast's are OPT_NODE");
		else lastelem = N_AST1(node);
		return get_right_span_p(lastelem);
	}
	else printf("get_right_span_p: bad node kind %d\n",nkind);
	chaos("get_right_span_p");
	return (Span)0;
}

Span make_span(short line, short col)			/*;make_span*/
{
	Span tok;

	tok = (Span) emalloc(sizeof(Span_s));
	tok->line = line;
	tok->col  = col;
	return (tok);
}
