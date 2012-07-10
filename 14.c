/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#include "hdr.h"
#include "vars.h"
#include "attr.h"
#include "errmsgprots.h"
#include "chapprots.h"

void check_range_attribute(Node node)				/*;check_range_attribute*/
{
	if (N_KIND(node) == as_attribute
	  && ((int)attribute_kind(node) == ATTR_O_RANGE
	  ||  (int)attribute_kind(node) == ATTR_T_RANGE)) {
		errmsg("invalid use of 'RANGE in expression", "none", node) ;
	}
}

#ifdef TBSN
int is_value(char *x)										/*;is_value*/
{
	TO_ERRFILE("is_value (ch 14) not implemented");
	return	   (is_tuple(x) and x(1) = 'ivalue') ;
}
#endif
