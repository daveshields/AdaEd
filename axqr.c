/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/* procedures for reading axq files.
 * Since these are used by the interpreter, it is ESSENTIAL that
 * neither hdr.h or ghdr.h be required for their compilation.
 */

#include "config.h"
#include <stdio.h>
#include "ifile.h"
#include "segment.h"
#include "slot.h"
#include "stdlib.h"
#include "libfprots.h"
#include "miscprots.h"
#include "axqrprots.h"

static Slot *get_slot(IFILE *, int, int *);

Segment segment_new(int kind, int initdim)		/*;segment_new*/
{
	Segment	s;

	s = (Segment) emalloct(sizeof(Segment_s), "segment-new");
	s->seg_kind = kind;
	s->seg_ptr = (int **) 0;
	if (kind==SEGMENT_KIND_CODE) {
		s->seg_size = sizeof(char);
		if (initdim==0) initdim = 128;
		s->seg_dim = initdim;
		s->seg_extend = 128;
	}
	else {
		s->seg_size = sizeof(int);
		if (initdim==0) initdim = 32; /* initial dimension */
		s->seg_dim = initdim;
		s->seg_extend = 8;
	}
	s->seg_pos = 0;
	s->seg_maxpos = 0;
	s->seg_data = emalloct(s->seg_dim * s->seg_size, "segment-data");
	s->seg_id = SEG_ID;		/* insert value to check segment validity*/
	return s;
}

Segment segment_read(IFILE *file)				/*;segment_read*/
{
    Segment	seg;
	short	dim;
	int		kind;
	kind = getnum(file,"segment-kind");
	dim = getnum(file,"segment-dim");
	seg = segment_new(kind, dim);
	fread(seg->seg_data,seg->seg_size,dim,file->fh_file);
	seg->seg_maxpos = dim - 1;
	return seg;
}

void read_axq(IFILE *axq_file, Axq axq)							/*;read_axq*/
{
	/* axq has been set with loads an AXQ */

	Segment	newseg,segment_get();
	int		si,snum,nsegs,sj;
	char	**get_axq_slots();
	char	*funame,*u_type;
	long	genpos,rec;

#ifdef TBSL
	if (debug_trace) {
		TO_ERRFILE("reading axq ",  axq_file_name) ;
	}
	efclose(axq_file);
#endif
	for (rec=read_init(axq_file); rec != 0; rec=read_next(axq_file,rec)) {
		funame = getstr(axq_file,"axq-unit-name");
		getnum(axq_file,"axq-num");
		u_type = unit_name_type(funame);
		/* In the C version, DATA_SLOTS CODE_SLOTS and EXCEPTION_SLOTS are at
		 * the end of the file, and are read below
		 */
		/* load subprogram bodies, package specs and bodies and main unit */
		if (!(streq(u_type,"su") || streq(u_type,"sp") || streq(u_type,"bo")
		  || streq(u_type,"ma"))) {
			continue; /* skip other units */
		}
		genpos = getlong(axq_file,"axq-gen-pos");
		/* position to start of generator info */
		ifseek(axq_file, "axq-gen_info", genpos, 0);
		for (si=0;si<4;si++) {
			nsegs = getnum(axq_file,"number-segments");
			for (sj=1;sj<=nsegs;sj++) {
				snum = getnum(axq_file,"axq-segment-num");
				newseg = segment_read(axq_file);
				if (newseg->seg_kind==SEGMENT_KIND_CODE) {
					if (snum>=axq->axq_code_segments_dim)  {
						chaos("code_segment_number error");
					}
					axq->axq_code_segments[snum] = newseg->seg_data;
					axq->axq_code_seglen[snum] = newseg->seg_dim;
				}
				if (newseg->seg_kind==SEGMENT_KIND_DATA) {
					if (snum>=axq->axq_data_segments_dim)  {
						chaos("data_segment number too big");
					}
					axq->axq_data_segments[snum] = (int *) newseg->seg_data;
					axq->axq_data_seglen[snum] = newseg->seg_dim;
				}
			}
		}
	}
#ifdef TBSL
else {
	TO_LIST("*** Unable to read AXQfile ",axq_file_name);
	stop;
}
#endif
}

long get_cde_slots(IFILE *file, Axq axq)					/*;get_cde_slots*/
{
	/* get slots info from file. The offset within the file is not changed */

	long	dpos,start_pos;
	int		n_code,n_data,n_exception,dim;

	start_pos = iftell(file); /* save pos so can restore after reading slots*/
	dpos = file->fh_slots;/* get offset for slots */
	if (dpos==0l)
		chaos("get_cde_slots: slot offset zero");
	ifseek(file,"slots-start",dpos,0);/* position to start of slot info */
	n_code = getnum(file,"n-code");
	n_data = getnum(file,"n-data");
	n_exception = getnum(file,"n-exception");
	axq->axq_code_slots_dim = n_code + 1;
	axq->axq_code_slots = get_slot(file,n_code,&dim);
	axq->axq_code_segments_dim = dim;
	axq->axq_data_slots_dim = n_data + 1;
	axq->axq_data_slots = get_slot(file,n_data,&dim);
	axq->axq_data_segments_dim = dim;
	axq->axq_exception_slots_dim = n_exception + 1;
	axq->axq_exception_slots = get_slot(file,n_exception,&dim);
	axq->axq_exception_slots_dim = dim;
	ifseek(file,"slots-reset",start_pos,0);/* restore position */
	return dpos; /* return offset of start of slot info */
}

static Slot *get_slot(IFILE *file, int nmax, int *dim)			/*;get_slot*/
{
	/* This procedure reads in the SLOTS information. 
	 * Entries are Slots structures. nmax is guess at needed dimension,
	 * dim is set to dimension actually found.
	 */

	int i,n,exists;
	Slot	*tup;
	Slot	slot;

	*dim = nmax+1;
	tup = (Slot *) emalloct((unsigned)*dim * sizeof(Slot), "get-slot");
	n  = getnum(file,"slot-entries");
	for (i = 1; i <= n; i++) {
		exists = getnum(file,"slot-exists");
		if (exists) {
			slot = (Slot) emalloct(sizeof(Slot_s), "get-slot-1");
			slot->slot_seq = getnum(file,"slot-seq");
			slot->slot_unit = getnum(file,"slot-unit");
			slot->slot_number = getnum(file,"slot-number");
			slot->slot_name = getstr(file,"slot_name");
			if (slot->slot_number >= *dim) {
				*dim = slot->slot_number + 1;
			}
			tup[i] =  slot;
		}
		else {
			tup[i] = (Slot)0;
		}
	}
	return tup;
}
