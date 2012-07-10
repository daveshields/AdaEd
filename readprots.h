/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

int load_unit(char *, int);
void load_library(Axq);
void store_axq(IFILE *, int);
void write_glib();
void update_stub(Stubenv);
void overwrite_unit_name(char *);
int read_stub_short(char *, char *, char *);
void retrieve_generic_body(Symbol);
void collect_stub_node_units(int);
