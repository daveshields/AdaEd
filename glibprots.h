/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

Segment main_data_segment();
Set precedes_map_get(char *);
void precedes_map_put(char *, Set);
Tuple stubs(char *);
Set remove_same_name(char *);
int lib_package_with_tasks(Symbol);
#ifdef DEBUG
Tuple read_predef_axq(Tuple);
#endif
