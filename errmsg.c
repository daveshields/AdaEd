/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "hdr.h"
#include "ada.h"
#include "hdr.h"
#include "vars.h"
#include "miscprots.h"
#include "chapprots.h"
#include "smiscprots.h"
#include "sspansprots.h"
#include "errmsgprots.h"

static char *strings[5];

static char *insert(char *, int);

void errmsg(char *msg, char *lrm_sec, Node node)				/*;errmsg*/
{
	/* Semantic errors */

	int begline, begcol, endline, endcol;
	Span lspan, rspan;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : errmsg(msg, lrm_sec, node); ");

	if (node == OPT_NODE) node = current_node;
	if (node != (Node)0) {
		lspan = get_left_span(node);
		rspan = get_right_span(node);
		begline = lspan->line;
		begcol	= lspan->col;
		endline = rspan->line;
		endcol	= rspan->col;
	}
	else 
		/* this is in case rcv null node - put message at beginning of file*/
		/* only temp-eventually, all calls to errmsg should have valid node */
		begline = begcol = endline = endcol = 1;

	fprintf(msgfile, "%d %d %d %d %d\t%s", ERR_SEMANTIC, begline, begcol,
	  endline, endcol, msg);
	if (!streq(lrm_sec, "none"))
		fprintf(msgfile, " (RM %s)", lrm_sec);
	fprintf(msgfile, "\n");
	errors = TRUE;
}

void warning(char *msg, Node node)								/*;warning*/
{
	int begline, begcol, endline, endcol;
	Span lspan, rspan;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : warning(msg);");

	if (node == OPT_NODE) node = current_node;
	if (node != (Node)0) {
		lspan = get_left_span(node);
		rspan = get_right_span(node);
		begline = lspan->line;
		begcol	= lspan->col;
		endline = rspan->line;
		endcol	= rspan->col;
	}
	else 
		/* this is in case rcv null node - put message at beginning of file*/
		/* only temp-eventually, all calls to errmsg should have valid node */
		begline = begcol = endline = endcol = 1;

	fprintf(msgfile, "%d %d %d %d %d\t%s", ERR_WARNING, begline, begcol,
	  endline, endcol, msg);
	fprintf(msgfile, "\n");
}


void errmsg_id(char *msg, Symbol name, char *lrm, Node node)	/*;errmsg_id*/
{
	strings[0] = ORIG_NAME(name);
	errmsg(insert(msg, 1), lrm, node);
}

void errmsg_str(char *msg, char *str, char *lrm, Node node)		/*;errmsg_str*/
{
	strings[0] = str;
	errmsg(insert(msg, 1), lrm, node);
}

void errmsg_nat(char *msg, Symbol sym, char *lrm, Node node)	/*;errmsg_nat*/
{
	strings[0] = nature_str(NATURE(sym));
	errmsg(insert(msg, 1), lrm, node);
}

void errmsg_type(char *msg, Symbol type, char *lrm, Node node)	/*;errmsg_type*/
{
	strings[0] = full_type_name(type);
	errmsg(insert(msg, 1), lrm, node);
}

void errmsg_nval(char *msg, Node name, char *lrm, Node node)	/*;errmsg_nval*/
{
	strings[0] = N_VAL(name);
	errmsg(insert(msg, 1), lrm, node);
}

void errmsg_id_id(char *msg, Symbol name1, Symbol name2, char *lrm, Node node)
															/*;errmsg_id_id*/
{
	strings[0]     = ORIG_NAME(name1);
	strings[1] = ORIG_NAME(name2);
	errmsg(insert(msg, 2), lrm, node);
}

void errmsg_id_type(char *msg, Symbol name, Symbol type, char *lrm, Node node)
															/*;errmsg_id_type*/
{
	strings[0]     = ORIG_NAME(name);
	strings[1] = full_type_name(type);
	errmsg(insert(msg, 2), lrm, node);
}

void errmsg_nat_id_str(char *msg, Symbol sym, Symbol name, char *str, char *lrm,
  Node node)											/*;errmsg_nat_id_str*/
{
	char *name_str;

	strings[0] = nature_str(NATURE(sym));
	name_str = ORIG_NAME(name);
	if (name_str[0] == '#') name_str = "#BLOCK";
	strings[1] = name_str;
	strings[2] = str;

	errmsg(insert(msg, 3), lrm, node);
}

void errmsg_str_id(char *msg, char *str, Symbol name, char *lrm, Node node)
															/*;errmsg_str_id*/
{
	strings[0]     = str;
	strings[1] = ORIG_NAME(name);
	errmsg(insert(msg, 2), lrm, node);
}

void errmsg_str_num(char *msg, char *str, int i, char *lrm, Node node)
														/*;errmsg_str_num*/
{
	char numstr[5];

	strings[0] = str;
	sprintf(numstr, "%d", i);
	strings[1] = numstr;

	errmsg(insert(msg, 2), lrm, node);
}

static char *insert(char *in_format, int nstrings)				/*;insert*/
{
	/*  -in_format- is a character string containing an error message, and 1 or
	 *  more "substitution" (%) characters to be replaced by the character
	 *  strings pointed to by the array -strings-
	 *  -tmp_format- is a working copy to be used by this procedure (to avoid
	 *  "clobbering" string constants).
	 */

	char *msg, *p;
	char *tmp_format;
	int	i;

	/* copy input format string */
	tmp_format = emalloct((unsigned) strlen(in_format)+1, "errmsg-tmp");
	strcpy(tmp_format, in_format);

	/* initialize msg to empty string */
	msg = emalloct(1, "errmsg-1"); 
	*msg = '\0';

	for (i = 0; i < nstrings; i++) {
		p = strchr(tmp_format, '%');
		if (p == 0) break;
		*p = '\0';
		if (p != tmp_format)
			msg = strjoin(msg, tmp_format);
		msg = strjoin(msg, strings[i]);
		tmp_format = ++p;
	}
	if (tmp_format != '\0' )
		msg = strjoin(msg, tmp_format);
	if (p == 0) {
		printf("error in proc insert, too few %c's\n", '%');
	}
	return(msg);
}

/*
 * Following are variations of pass1_error that call the appropriate
 * errmsg_ routine.
 * The original (simple case) pass1_error is still in 4c.c
 */

void pass1_error_id(char *msg, Symbol name, char *lrm_sec, Node node)
														/*;pass1_error_id */
{
	/* This procedure is invoked when a type error which requires a special
	 * message is encountered in resolve1.
	 */

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  pass1_error_id");

	if (!noop_error) errmsg_id(msg, name, lrm_sec, node);
	noop_error = TRUE;	/* To avoid cascaded errors.*/
}

void pass1_error_str(char *msg, char *str, char *lrm_sec, Node node)
														/*;pass1_error_str */
{
	/* This procedure is invoked when a type error which requires a special
	 * message is encountered in resolve1.
	 */

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  pass1_error");

	if (!noop_error) errmsg_str(msg, str, lrm_sec, node);
	noop_error = TRUE;	/* To avoid cascaded errors.*/
}

void pass1_error_l(char *msg1, char *msg2, char *lrm_sec, Node node)
														/*;pass1_error_l */
{
	/* This procedure is invoked when a type error which requires a special
	 * message is encountered in resolve1.
	 */

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  pass1_error_l");

	if (!noop_error) errmsg_l(msg1, msg2, lrm_sec, node);
	noop_error = TRUE;	/* To avoid cascaded errors.*/
}

char *build_full_names(Set symbols)					/*;build_full_names */
{
	/* builds a string containing the full names (scope.name) of all Symbols
	 * in the set 'symbols`
	 */

	Symbol sym;
	Forset fs;
	char   *name, *name_string;

	/* TBSL: this should be improved to free extra storage !! */

	name_string = strjoin("","");
	if (symbols == (Set)0) return(name_string);
	FORSET(sym = (Symbol), symbols, fs);
		name = ORIG_NAME(SCOPE_OF(sym));
		/* skip internally generated block names */
		if (name[0] == '#')
			name = "#BLOCK.";
		else
			name = strjoin(name, ".");
		name = strjoin(name, ORIG_NAME(sym));
		name = strjoin(name, " ");
		name_string = strjoin(name_string, name);
	ENDFORSET(fs);
	return(name_string);
}
