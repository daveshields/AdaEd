/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#define GEN

#include "hdr.h"
#include "vars.h"
#include "gvars.h"
#include "type.h"
#include "segment.h"
#include "miscprots.h"
#include "dbxprots.h"
#include "axqrprots.h"
#include "gmiscprots.h"
#include "segmentprots.h"

static void segment_put_n(Segment, int, int, char *);
static void segment_realloc(Segment, unsigned);

extern Segment	CODE_SEGMENT, DATA_SEGMENT, DATA_SEGMENT_MAIN;

#ifdef MACHINE_CODE
void print_data_segment()								/*;print_data_segment*/
{
	Segment	seg;
	char		line[250], c;
	int		i, w, *sp;

	seg = DATA_SEGMENT; 
	sp = (int *) seg->seg_data;
	to_gen(" ");
	to_gen_int("--- Global data segment # ", CURRENT_DATA_SEGMENT);
	for (i = 0; i < seg->seg_maxpos; i++) {
		w = *sp++;
		if (w >= ' ' && w <= '~') c = w; 
		else c = ' ';
		sprintf(line, "     %5d  %8x %c %d", i, w, c, w);
		to_gen(line);
	}
}
#endif

void segment_append(Segment s, Segment sa)					/*;segment_append*/
{
	/* append segment sa at end of segment s */

	int	i, la;

	seg_check(s);
	if (s->seg_kind != SEGMENT_KIND_DATA)
		chaos("segment_append not appending a data segment");
	s->seg_pos = s->seg_maxpos;
	la = sa->seg_maxpos;
	for (i = 0; i < la; i++) {
		segment_put_int(s, ((int *)(sa->seg_data))[i]);
	}
}

void seg_check(Segment seg)										/*;seg_check*/
{
	if (seg->seg_id != SEG_ID)
		chaos("invalid segment - check word invalid ");
}

void segment_empty(Segment s)								/*;segment_empty*/
{
	/* seg segment to empty state, but do no reallocate it */
	seg_check(s);
	s->seg_pos = 0;
	s->seg_maxpos = 0;
}

void segment_free(Segment s)								/*;segment_free*/
{
	seg_check(s);
	efreet(s->seg_data, "segment-data");
	efreet((char *) s, "segment");
}

int segment_get_int(Segment s, int i)					/*;segment_get_int*/
{
	/* get value of word from location i in segment seg. */

	int	*resp;

	seg_check(s);
	if (i >= s->seg_maxpos) {
		chaos("segment.c: get_int retrieving from undefined location\n");
		return 0;
	}
	if (s->seg_kind == SEGMENT_KIND_DATA) {
		resp = (int *) s->seg_data + i;
		return *resp;
	}
	else {
#ifdef ALIGN_WORD
		/* retrieve byte by byte to avoid alignment problems */
		register int j;
		int v;
		register char *sp, *tp;

		resp = (int *) (s->seg_data + i);
		sp = (char *) resp;
		tp = (char *) &v;
		for (j = 0; j < sizeof(int); j++) *tp++ = *sp++;
		return v;
#else
		resp = (int *) (s->seg_data + i);
		return *resp;
#endif
	}
}

unsigned int segment_get_pos(Segment seg)				/*;segment_get_pos*/
{
	seg_check(seg);
	return seg->seg_pos;
}

unsigned int segment_get_maxpos(Segment seg)			/*;segment_get_maxpos*/
{
	seg_check(seg);
	return seg->seg_maxpos;
}

int segment_get_off(Segment s, int i)						/*;segment_get_off*/
{
	return segment_get_int(s, i);
}

void segment_put_byte(Segment s, int v)					/*;segment_put_byte*/
{
	unsigned	newpos, pos;

	seg_check(s);

	if (s->seg_kind != SEGMENT_KIND_CODE)
		chaos("segment.c: segment_put_byte called on data segment");

	pos = s->seg_pos;
	newpos = pos + 1;
	if (newpos >= s->seg_dim) {
		segment_realloc(s, newpos);
	}
	s->seg_data[pos] = (char) v;
	s->seg_pos = newpos;
	if (s->seg_maxpos < newpos) s->seg_maxpos = newpos;
}

void segment_put_const(Segment seg, Const con)			/*;segment_put_const*/
{
	if (con->const_kind == CONST_INT) {
		/* can safely put integers - defer others for later */
		segment_put_word(seg, INTV(con));
	}
	else if(con->const_kind == CONST_REAL) {
		segment_put_real(seg, REALV(con));
	}
	else if(con->const_kind == CONST_FIXED) {
		segment_put_long(seg, FIXEDV(con));
	}
	else {
#ifdef DEBUG
		zpcon(con);
#endif
		chaos("segment.c - meaningless kind of literal");
	}
}

void segment_put_int(Segment s, int v)						/*;segment_put_int*/
{
	unsigned	newpos, pos;
	int		*d;

	seg_check(s);
	pos = s->seg_pos;
	if (s->seg_kind == SEGMENT_KIND_DATA) {
		newpos = pos + 1;
		if (newpos >= s->seg_dim)
			segment_realloc(s, newpos);
		d = (int *) s->seg_data;
		d[pos] = v;
	}
	else { /* if code segment */
		newpos = pos + sizeof(int);
		if (newpos >= s->seg_dim)
			segment_realloc(s, newpos);
#ifdef ALIGN_WORD
		/* if must worry about alignment, do byte by byte */
		{
			int iv;
			iv = v;
			(void) segment_put_n(s, s->seg_pos, sizeof(int), (char *) &iv);
		}
#else
		d = (int *) (s->seg_data + pos);
		*d = v;
#endif
	}
	s->seg_pos = newpos;
	if (s->seg_maxpos < newpos) s->seg_maxpos = newpos;
}

void segment_put_long(Segment s, long v)				/*;segment_put_long*/
{
	long	lv = v;
	segment_put_n(s, s->seg_pos, sizeof(long), (char *) &lv);
}

static void segment_put_n(Segment s, int i, int n, char *p)	/*;segment_put_n*/
{
	/* put n bytes from p at location i in segment seg, extending
	 * segment if necessary 
	 */

	unsigned	newpos, pos;
	int		*d;
	char	*dc;

	seg_check(s);
	segment_set_pos(s, (unsigned) i, 0);
	pos = s->seg_pos;
	if (s->seg_size == 1) { /* if code segment */
		newpos = pos + n;
		if (newpos >= s->seg_dim)
			segment_realloc(s, newpos);
		dc = s->seg_data + pos;
		while (n--)
			*dc++ = *p++;
	}
	else { /* assume word size */
		newpos = pos + n/sizeof(int);
		if (newpos >= s->seg_dim)
			segment_realloc(s, newpos);
		d = (int *)( s->seg_data) + pos;
		dc = (char *) d;
		while (n--)
			*dc++ = (unsigned char) *p++;
	}
	s->seg_pos = newpos;
	if (s->seg_maxpos < newpos) s->seg_maxpos = newpos;
}

void segment_put_off(Segment s, int i, int v)				/*;segment_put_off*/
{
	/* put value of v, interpreted as offset (16 bits) at location i
	 * in segment seg.
	 * We assume this is used to overwrite a previously defined location
	 * and raise chaos if this is not the case.
	 */

	unsigned	pos, oldpos;
	int		*d;

	seg_check(s);

	if (i >= s->seg_maxpos)
		chaos("segment.c: segment_put_off of undefined location");

	pos = i;
	if (s->seg_kind == SEGMENT_KIND_DATA) {
		d = (int *) s->seg_data;
		d[pos] = v;
	}
	else {
#ifdef ALIGN_WORD
		{  
			int iv; 
			iv = v;
			oldpos = s->seg_pos; /* save pos since segment_put_n may alter it */
			segment_put_n(s, i, sizeof(int), (char *)&iv);
			s->seg_pos = oldpos;
		}
#else
		d = (int *) (s->seg_data + pos);
		*d = v;
#endif
	}
}

void segment_put_real(Segment s, double db)				/*;segment_put_real*/
{
	float	r = db;
	segment_put_n(s, s->seg_pos, sizeof(float), (char *) &r);
}

void segment_put_ref(Segment seg, int segnum, int off)		/*;segment_put_ref*/
{
	if (seg->seg_kind == SEGMENT_KIND_DATA) {
		segment_put_int(seg, segnum);
		segment_put_int(seg, off);
	}
	else {
		segment_put_byte(seg, segnum);
		segment_put_int(seg, off);
	}
}

void segment_put_word(Segment s, int v)					/*;segment_put_word*/
{
	segment_put_int(s, v);
}

void segment_set_pos(Segment s, unsigned pos, unsigned offtyp)
														/*;segment_set_pos*/
{
	/* set position of segment to offset pos. offtyp is type of offset,
	 * interpreted similarly to lseek(2); i.e., offtyp is 0 for offset
	 * from start of segment, 1 for offset from current position, and 2
	 * for offset from end of segment. Only the cases 0 and 2 are supported now.
	 */

	seg_check(s);
	if (offtyp == 2) { /* to position at end ignore pos */
		s->seg_pos = s->seg_maxpos;
		return;
	}
	if (offtyp != 0)
		chaos("segment_set_pos bad offset type");
	s->seg_pos = pos;
}

static void segment_realloc(Segment s, unsigned newdim)		/*;segment_realloc*/
{
	/* extend dimension field if necessary to it is at least as large
	 * as newdim
	 */

	unsigned	incr, dim;

	seg_check(s);
	dim = s->seg_dim;
	if (dim >= newdim) return;
	incr = newdim - dim;
	if (incr < s->seg_extend) incr = s->seg_extend;
	s->seg_dim += incr;
	s->seg_data = erealloct(s->seg_data, s->seg_dim * s->seg_size,
	  "segment-realloc");
	/* update ptr to data if one is being kept */
	if (s->seg_ptr != (int **) 0) {
		*(s->seg_ptr) = (int *) s->seg_data;
	}
}

Segment template_new(int t_kind, int t_size, int words, int **ptr)
															/*;template_new*/
{
	Segment	s;

	s = segment_new(SEGMENT_KIND_DATA, words);
	s->seg_ptr = ptr; /* save address of pointer to be updated */
	/* return pointer to start of segment */
	*(s->seg_ptr) = (int *) s->seg_data;
	segment_put_word(s, t_kind);
	segment_put_word(s, t_size);
	/* assume user will fill in rest direcly so point to end */
	s->seg_pos = s->seg_maxpos = words;
	return s;
}

unsigned int PC()														/*;PC*/
{
	/* corresponds to macro PC in SETL version */

	seg_check(CODE_SEGMENT);
	return CODE_SEGMENT->seg_maxpos;
}

#ifdef DEBUG
void zpseg(Segment seg)												/*;zpseg*/
{
	printf("Segment %d x%x ", (int)seg, seg);
	if (seg->seg_kind == SEGMENT_KIND_CODE) printf(" code");
	else printf(" data");
	printf(" size %d pos %d max_pos %d dim %d ext %d\n", seg->seg_size,
	    seg->seg_pos, seg->seg_maxpos, seg->seg_dim, seg->seg_extend);
	/* should print part of data here */
}
#endif
