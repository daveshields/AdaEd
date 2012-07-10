/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

*/

struct prsstack *gettok();
char *namelist(int num);
int namemap(char *str, int len);
int name_map(char *str);
#ifdef IBM_PC
void lexinit();
#endif
