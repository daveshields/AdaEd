/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include <stdlib.h>
#include "ipar.h"
#include "int.h"
#include "iparprots.h"

int fetch_and_store(int *i, int j)						/*;fetch_and_store*/
{
	int temp = *i;
	*i = j;
	return temp;
}

char *pointer_fetch_and_store(char **i, char *j)	/*;pointer_fetch_and_store*/
{
	/* fetch_and_store rewritten to accept pointer arguments */

	char *temp = *i;
	*i = j;
	return temp;
}
