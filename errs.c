/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#include "hdr.h"
#include "ada.h"
#include "vars.h"
#include "ifile.h"
#include "libfprots.h"
#include "pspansprots.h"
#include "adalexprots.h"
#include "errsprots.h"

static void printerr(Span, Span, char *);
static void err_display(char *);
static void write_error(int, char *, Span, Span);

/* This file contains functions for printing error messages.
   To print an error message given the complete message and spans,
   printerr is used. To print a syntax error, syntax_err is
   used.
 */


/* Printerr: print error message to the terminal 
 * this should be called only in case some debugging option is set (-ert)
 * Error message is printed to stdout if termopt set, to errfile if redopt or
 * erropt set 
 * If the error is not on the most recently printed source line, print the line
 * (or last line if it spans multiple lines) first, followed by an underlining
 * or pointer to error location.
 */


static void printerr(Span lspan, Span rspan, char *msg)
															/*;printerr*/
{
	int i;
	char tmp_str[150];

	if (lspan->line==rspan->line || lineno - rspan->line < NUM_LINES)
	{
		/* print source line (or last line ) */
		if (rspan->line != lineno   &&  /* error at current line */
		!(feof(adafile) && lspan->line==lineno-1 &&colno==1) ) {
			/* error is at last line in source */
			sprintf(tmp_str, "%5d:  %s\n", rspan->line, source_buf[
			  (src_index + NUM_LINES - (lineno - rspan->line)) % NUM_LINES]);
			err_display(tmp_str);
		}
		/* underline */
		if (lspan->line != rspan->line) {
			err_display(". . . . ");
			for (i = rspan->col; --i;)
				err_display("-");
			err_display(">\n");
		}
		else { /* error spans more than one line */
			for (i = lspan->col + 8; --i;)
				err_display(" ");
			if (rspan->col - lspan->col <= 1)
				err_display("^");
			else {
				err_display("<");
				for (i = rspan->col - lspan->col - 1; i--;)
					err_display("-");
				err_display(">");
			}
			err_display("\n");
		}
	}
	else {
		sprintf(tmp_str, "-- Between line %d column %d and line %d column %d\n",
		  lspan->line, lspan->col, rspan->line, rspan->col);
		err_display(tmp_str);
	}
	err_display(msg);
	err_display("\n\n");
}

static void err_display(char *str)							/*;err_display*/
{
	if (termopt)
		printf("%s", str);
#ifdef DEBUG
	if (trcopt)
		fprintf(errfile, "%s", str);
#endif
}


/* Syntax_err: Report an error detected during parsing actions */

void syntax_err(Span lspan, Span rspan, char *msg)
															/*;syntax_err*/
{
	char newmsg[300];

	errors++;
	write_error(ERR_SYNTAX, msg, lspan, rspan);
	sprintf(newmsg, "*** Syntax error: %s", msg);
	if (debugopt)
		printerr(lspan, rspan, newmsg);
}


void match_error(int id1, int id2, char *construct, Span lspan,
  Span rspan)									/*;match_error*/
{
	/* Match_error: Report an error in matching two identifiers */
	char msg[200];

	sprintf(msg, "%s at beginning of %s does not match %s",
	  namelist(id1), construct, namelist(id2));
	syntax_err(lspan, rspan, msg);
}

void prs_warning(Span lspan, Span rspan,  char *msg)
															/*;prs_warning*/
{
	/* Prs_warning: Report a warning message */
	char newmsg[200];

	write_error(ERR_WARNING, msg, lspan, rspan);
	sprintf(newmsg, "*** Warning: %s", msg);
	if (debugopt)
		printerr(lspan, rspan, newmsg);
}


void lexerr(int line, int col1, int col2, char *msg)			/*;lexerr*/
{
	/* Lexerr: Report an error detected by the lexical scanner */
	char nmsg[300];
	Span_s span1, span2;

	errors++;
	span1.line = span2.line = line;
	span1.col = col1;
	span2.col = col2;
	write_error(ERR_LEXICAL, msg, &span1, &span2);
	sprintf(nmsg, "*** Lexical Error: %s", msg);
	if (debugopt)
		printerr(&span1, &span2, nmsg);
}

/* This file contains functions dealing with files that need to be
   written so other programs can read them.
*/


/* So that the error messages can be merged with the listing of the
   source file, and so that the pragmas LIST and PAGE are taken into
   consideration properly, msgfile is written with information about
   occurrances of the above. The format is as follows

   error_or_pragma_type lspan rspan
   error_mssage

   where lspan and rspan are each two integers, error_or_pragma_type
   is the type of error or pragma (defined in msgs.h), and error_message
   is the error message in the case of an error. There is no error
   message for pragmas (though there may be a seperate set of lines
   for an error message which is there because of the pragma
*/


void write_pragma(int pragma_type, Span lspan, Span rspan)
															/*;write_pragma*/
{
	/* Write_pragma: Writes data about pragma LIST and PAGE to the msgfile */
	fprintf(msgfile, "%d %d %d %d %d\n", pragma_type, lspan->line,
	  lspan->col, rspan->line, rspan->col);
}

static void write_error(int error_type, char *msg, Span lspan,
  Span rspan)									/*;write_error*/
{
	/* Write_error: Write data about errors to msgfile */
	fprintf(msgfile, "%d %d %d %d %d\t%s\n", error_type, lspan->line,
	  lspan->col, rspan->line, rspan->col, msg);
}
