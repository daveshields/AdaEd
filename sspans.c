/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#include "hdr.h"
#include "vars.h"
#include "miscprots.h"
#include "setprots.h"
#include "smiscprots.h"
#include "sspansprots.h"

static Span retrieve_l_span(Node);
static Span retrieve_r_span(Node);
static Span make_span(short, short);

int is_terminal_node(short node_kind)			/*;is_terminal_node*/
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
	  node_kind == as_line_no ||
	  /* these are added in the semantics */
	  node_kind == as_ivalue ||
	  node_kind == as_string_ivalue ||
	  node_kind == as_current_task ||
	  node_kind == as_number);
}

Span get_right_span(Node node)			/*;get_right_span */
{
	Span rspan;

	rspan = retrieve_r_span(node);
	if (rspan == (Span)0  && node != current_node)
		rspan = retrieve_r_span(current_node);
	if (rspan == (Span)0)
		chaos("get_right_span: cannot find spans");
	return rspan;
}

Span get_left_span(Node node)			/*;get_left_span */
{
	Span lspan;

	lspan = retrieve_l_span(node);
	if (lspan == (Span)0  && node != current_node)
		lspan = retrieve_l_span(current_node);
	if (lspan == (Span)0)
		chaos("get_left_span: cannot find spans");
	return lspan;
}

static Span retrieve_l_span(Node node) 			/*;retrieve_l_span */
{
	int i,listsize;
	unsigned int nkind;
	Span lspan = (Span)0 ;

	if (node == (Node)0 || node == OPT_NODE) return (Span)0;
	nkind = N_KIND(node);
	if (is_terminal_node(nkind)) return make_span(N_SPAN0(node),N_SPAN1(node));
	if (nkind == as_exit) return retrieve_l_span(N_AST4(node));
	if (nkind == as_return) return retrieve_l_span(N_AST4(node));
	if (nkind == as_raise) return retrieve_l_span(N_AST2(node));
	if (nkind == as_others_choice) return retrieve_l_span(N_AST3(node));
	if (nkind == as_op)
		/* N_AST1 is the operator. Really want first argument! */
		if ((lspan=retrieve_l_span(N_AST2(node))) != (Span)0)
			return lspan;
	if (nkind == as_attribute)
		/* N_AST1 is the attribute. Really want first argument! */
		if ((lspan=retrieve_l_span(N_AST2(node))) != (Span)0)
			return lspan;
	if (N_LIST_DEFINED(nkind)) {
		listsize = tup_size(N_LIST(node));
		if (listsize == 0)
			return (Span)0;
		for (i=1; i <= listsize; i++) {
			lspan = retrieve_l_span((Node)N_LIST(node)[i]);
			if (lspan != (Span)0)
				return lspan;
		}
		return (Span)0;
	}
	if (N_AST1_DEFINED(nkind))
		lspan = retrieve_l_span(N_AST1(node));
	if (N_AST2_DEFINED(nkind) && lspan == (Span)0 )
		lspan = retrieve_l_span(N_AST2(node));
	if (N_AST3_DEFINED(nkind) && lspan == (Span)0 )
		lspan = retrieve_l_span(N_AST3(node));
	if (N_AST4_DEFINED(nkind) && lspan == (Span)0 )
		lspan = retrieve_l_span(N_AST4(node));
	return lspan;
}

static Span retrieve_r_span(Node node) 				/*;retrieve_r_span */
{
	int i,listsize,length=1;
	unsigned int nkind;
	Span rspan = (Span)0 ;
	Node attr_node;

	if (node == (Node)0 || node == OPT_NODE) return (Span)0;
	nkind = N_KIND(node);
	if (is_terminal_node(nkind)) {
		if (N_VAL_DEFINED(nkind))
			/* as_null, as_null_s, as_others, 
			 * have no N_VAL field defined
			 */
			if (nkind != as_number && nkind != as_ivalue 
			  && nkind != as_line_no && N_VAL(node) != (char *)0)
				length = strlen(N_VAL(node));
		return (make_span(N_SPAN0(node), N_SPAN1(node)+length-1));
	}
	if (nkind == as_exit) {
		if (N_AST2(node) != OPT_NODE) return retrieve_r_span(N_AST2(node));
		if (N_AST1(node) != OPT_NODE) return retrieve_r_span(N_AST1(node));
		return retrieve_r_span(N_AST4(node));
	}
	if (nkind == as_return) {
		if (N_AST1(node) != OPT_NODE) return retrieve_r_span(N_AST1(node));
		return retrieve_r_span(N_AST4(node));
	}
	if (nkind == as_raise) {
		if (N_AST1(node) != OPT_NODE) return retrieve_r_span(N_AST1(node));
		return retrieve_r_span(N_AST2(node));
	}
	if (nkind == as_others_choice) {
		if (N_AST2(node) != OPT_NODE) return retrieve_r_span(N_AST2(node));
		if (N_AST1(node) != OPT_NODE) return retrieve_r_span(N_AST1(node));
		return retrieve_r_span(N_AST3(node));
	}
	if (nkind == as_attribute) {
		/* N_AST1 is number node representing attribute */
		attr_node = N_AST1(node);
		if (N_KIND(attr_node) == as_number)
			/* due to errors, this is not necessarily the case */
			length = strlen(attribute_str((int) N_VAL(attr_node)));
		rspan = make_span(N_SPAN0(attr_node),
		  N_SPAN1(attr_node) + length - 1 );
		return rspan;
	}
	if (nkind == as_entry_name || nkind == as_entry_family_name) {
		/* N_AST3 gets temporarily overwritten with N_NAMES, 
		 * so ignore it 
		 */
		return retrieve_r_span(N_AST1(node));
	}
	if (N_LIST_DEFINED(nkind)) {
		listsize = tup_size(N_LIST(node));
		if (listsize == 0)
			return (Span)0;
		for (i=listsize; i > 0; i--) {
			rspan = retrieve_r_span((Node)N_LIST(node)[i]);
			if (rspan != (Span)0)
				return rspan;
		}
		return (Span)0;
	}
	if (N_AST4_DEFINED(nkind))
		rspan = retrieve_r_span(N_AST4(node));
	if (N_AST3_DEFINED(nkind) && rspan == (Span)0 )
		rspan = retrieve_r_span(N_AST3(node));
	if (N_AST2_DEFINED(nkind) && rspan == (Span)0 )
		rspan = retrieve_r_span(N_AST2(node));
	if (N_AST1_DEFINED(nkind) && rspan == (Span)0 )
		rspan = retrieve_r_span(N_AST1(node));
	return rspan;
}

static Span make_span(short line, short col)				/*;make_span */
{
	Span tok;

	tok = (Span) emalloct(sizeof(Span_s),"spans");
	tok->line = line;
	tok->col  = col;
	return (tok);
}

