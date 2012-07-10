/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "hdr.h"
#include "vars.h"
#include "unitsprots.h"

int unitNumberFromName(char *name)			/*;unitNumberFromName*/
{
	int i;
	if (!name) return 0;
	for (i = 1; i <= unit_numbers; i++)
		if (pUnits[i]->name && !strcmp(name, pUnits[i]->name))
			return i;
	return 0;
}
int unitNumberFromLibUnit(char *name)			/*;unitNumberFromLibUnit*/
{
	int i;
	if (!name) return 0;
	for (i = 1; i <= unit_numbers; i++)
		if (pUnits[i]->libUnit && !strcmp(name, pUnits[i]->libUnit))
			return i;
	return 0;
}
