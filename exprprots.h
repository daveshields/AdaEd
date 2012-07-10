/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

void gen_value(Node);
void gen_unary(Node);
void gen_binary(Node);
void gen_attribute(Node);
void gen_convert(Symbol, Symbol);
void gen_access_qual(int, Symbol);
Segment array_ivalue(Node);
Segment record_ivalue(Node);
static int code_map(Symbol);
