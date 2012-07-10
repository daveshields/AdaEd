/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

*/

void syntax_err(Span, Span, char *);
void match_error(int, int, char *, Span, Span);
void prs_warning(Span, Span,  char *);
void lexerr(int, int, int, char *);
void write_pragma(int, Span, Span);
