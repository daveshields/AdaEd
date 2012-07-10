/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/*TODO:
 need to add na_generic_package_spec to na_list
 define new_agg_or_access_acc ,..._agg to indicate markers 'access' 'agg'


 add symtab_copy to copy SYMTAB fields: 
  SYMTAB(a) = SYMTAB(b) => symtab_copy(a,b)
 TBSL: review handling of second arg to chain_overloads : want to avoid
	building explicit tuple for second arg.
 review handling of result from chain_overloads, is it really Symbol
*/
#ifndef _3_h
#define _3_h

#include "hdr.h"
#include "vars.h"
#endif
