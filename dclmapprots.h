/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

void dstrings_init(unsigned int, unsigned int);
static unsigned short dcl_lookup(char *);
Declaredmap dcl_new(int);
Symbol dcl_get_vis(Declaredmap, char *);
Symbol dcl_get(Declaredmap, char *);
static Symbol dcl_getp(Declaredmap, char *, int);
void dcl_put_vis(Declaredmap, char *, Symbol, int);
void dcl_put(Declaredmap, char *, Symbol);
void dcl_undef(Declaredmap, char *);
Declaredmap dcl_copy(Declaredmap);
#ifdef DEBUG_DCL
dstrings_dump();
dmap_chk(Declaredmap, char *);
int dcl_dump(D);
#endif
