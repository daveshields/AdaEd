/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "ifile.h"
#include "slot.h"

Segment segment_new(int, int);
Segment segment_read(IFILE *);
void read_axq(IFILE *, Axq);
long get_cde_slots(IFILE *, Axq);
