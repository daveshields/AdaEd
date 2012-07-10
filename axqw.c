/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* axqw.c - axq output procedures */

#define GEN

#include "hdr.h"
#include "vars.h"
#include "segment.h"
#include "gvars.h"
#include "slot.h"
#include "ifile.h"
#include "setprots.h"
#include "libfprots.h"
#include "miscprots.h"
#include "segmentprots.h"
#include "axqwprots.h"

static void put_slot(IFILE *, Tuple);

void segment_write(IFILE *file, Segment seg)				/*;segment_write*/
{
	short	dim;

	seg_check(seg);
	putnum(file, "segment-kind", seg->seg_kind);
	dim = seg->seg_maxpos + 1;
	putnum(file, "segment-dim", dim);
	fwrite(seg->seg_data, seg->seg_size, dim, file->fh_file);
}

void put_cde_slots(IFILE *file, int ifaxq)					/*;put_cde_slots*/
{
	long	dpos;

	dpos = iftell(file); /* get current position */
	putnum(file, "n-code_slots", tup_size(CODE_SLOTS));
	putnum(file, "n-data-slots", tup_size(DATA_SLOTS));
	putnum(file, "n-exception-slots", tup_size(EXCEPTION_SLOTS));
	put_slot(file, CODE_SLOTS);
	put_slot(file, DATA_SLOTS);
	put_slot(file, EXCEPTION_SLOTS);
	/* now replace word at start of  file with long giving offset to 
	 *start of information just written.
	 */
	file->fh_slots = dpos;
	ifclose(file);
}

static void put_slot(IFILE *file, Tuple tup)					/*;put_slot*/
{
	/* This procedure writes out the SLOTS information. These are maps from
	 * symbols to unit names. The interpreter needs only to know the names
	 * of the symbols so we write their names if available, else
	 * an empty string.
	 */

	int i, n;
	Slot slot;

	n = tup_size(tup);
	putnum(file, "slot-entries", n);
	for (i = 1; i <= n; i++) {
		slot = (Slot) tup[i];
		if (slot == (Slot)0) {
			if (compiling_predef)
				chaos("undefined slot compiling predef");
			putnum(file, "slot-exists", 0);
		}
		else {
			putnum(file, "slot-exists", 1);
			putnum(file, "slot-seq", slot->slot_seq);
			putnum(file, "slot-unit", slot->slot_unit);
			putnum(file, "slot-number", slot->slot_number);
			putstr(file, "slot-name", slot->slot_name);
		}
	}
}

void predef_exceptions(Tuple tup)					/*;predef_exceptions*/
{
	/* This procedure writes out the SLOTS information.
	 * This variant of put_slot writes out definitions of predefined exceptions
	 * when compiling predef, in a form suitable for inclusion as the body
	 * of init_predef_exceptions (cf. init.c).
	 */

	int i, n;
	Slot slot;

	n = tup_size(tup);
	printf("exception slots\n");
	/* first five exceptions defined in standard */
	for (i = 6; i <= n; i++) {
		slot = (Slot) tup[i];
		if (slot == (Slot)0) {
			if (compiling_predef)
				chaos("undefined slot compiling predef");
		}
		else {
			printf("    init_predef_exception(%d, %d, %d, \"%s\");\n",
			  slot->slot_seq, slot->slot_unit, slot->slot_number,
			  slot->slot_name);
		}
	}
}
