/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "hdr.h"
#include "vars.h"
#include "miscprots.h"
#include "dclmapprots.h"

/* These procedures maintain dstrings, a set of strings and associated
 * hash table used to assign a short integer uniquely identifiying each
 * identifier occurring in a declared map. Each string is preceded by a
 * short integer giving the offset of the next string in the hash chain.
 */

/* number of hash blocks, must be power of two (cf. dcl_lookup) */
#define DSTRINGS_HASH	64

/* DSTRINGS_MAXLEN gives the maximum length of the dstrings block. The
 * current value reflects the use of a 15 bit value for the idnum in the
 * layout of the Dment block used for a declared map entry.
 */
#define DSTRINGS_MAXLEN		32760

static unsigned short dcl_lookup(char *);
static Symbol dcl_getp(Declaredmap, char *, int);

char   *dstrings;		/* data block  - used in FORDECLARED */

static unsigned short dstrings_expand; /* amount to extend when block full */
static unsigned short dstrings_curlen;/* current length in bytes */
static unsigned short dstrings_maxlen;/* allocated length in bytes */
static unsigned short dhashtable[DSTRINGS_HASH];

void dstrings_init(unsigned int init_length, unsigned int expand_count)
/*;dstrings_init*/
{
	int     i;

	for (i = 0; i < DSTRINGS_HASH; i++)
		dhashtable[i] = 0;
	dstrings = (char *) emalloct((unsigned) init_length, "dclmap-dstrings");
	dstrings_curlen = sizeof(short);
	dstrings_maxlen = init_length;
	dstrings_expand = expand_count;
}

static unsigned short dcl_lookup(char *s)			/*;dcl_lookup*/
{
	/* locate string in dstrings block, adding if not yet present */

	unsigned short  hash, i, n;
	unsigned short *dp;

	hash = strhash(s) & (DSTRINGS_HASH-1);
	for (i = dhashtable[hash]; i != 0; i = *((unsigned short *)(dstrings + i)))
		if (strcmp(s, (char *)(dstrings + i + sizeof(short))) == 0)
			return i + sizeof(short);

	/* here if not found */
	n = strlen(s) + sizeof(short) + 1;/* number of new bytes */
#ifdef ALIGN2
	if (n&1) n+=1; /* round to even to keep shorts aligned */
#ifdef ALIGN4
	if (n&2) n+=2; 
#ifdef ALIGN8
	if (n&4) n+=4; 
#endif
#endif
#endif
	if ((DSTRINGS_MAXLEN - dstrings_maxlen) < dstrings_expand)
		capacity("dstrings full");

	if (dstrings_curlen + n >= dstrings_maxlen) {/* if need to extend */
		dstrings_maxlen += dstrings_expand;
		dstrings = (char *) erealloct(dstrings, dstrings_maxlen,
		    "dstrings-realloc");
	}
	dp = (unsigned short *)(dstrings + dstrings_curlen);
	*dp = dhashtable[hash];
	dhashtable[hash] = dstrings_curlen;
	strcpy(dstrings + dstrings_curlen + sizeof(short), s);
	dstrings_curlen += n;
	return dhashtable[hash] + sizeof(short);
}

Declaredmap dcl_new(int nh)	/*;dcl_new*/
{
	/* Allocate declared map with nh hash headers(0->10 headers */

	Declaredmap dm;

	dm = (Declaredmap) ecalloct(1, sizeof(Declaredmap_s), "dcl-new-dm");

	nh = nh == 0 ? 4 : nh;
	dm->dmap_curlen = 0;
	dm->dmap_maxlen = nh;
	dm->dmap_table = (struct Dment   *) ecalloct((unsigned) nh,
	  sizeof(Dment), "dcl-new-dmap-table");

	return dm;
}


Symbol dcl_get_vis(Declaredmap dmap, char *s)	/*;dcl_get_vis*/
{
	/* return Symbol for string s if present in map else appropriate
	 * This is to return only if visible.
	 */
	return dcl_getp(dmap, s, TRUE);
}

Symbol dcl_get(Declaredmap dmap, char *s)		/*;dcl_get*/
{
	return dcl_getp(dmap, s, FALSE);
}

static Symbol dcl_getp(Declaredmap dmap, char *s, int ifvis) /*;dcl_getp*/
{
	/* return Symbol for string s if present in map else appropriate
	 * null pointer . If ifvis is TRUE then return only if entry visible.
	 */

	unsigned short  idnum, i;
	struct Dment   *p;

	if (dmap == (Declaredmap) 0)
		chaos("dcl_getp: declared map null pointer");
	idnum = dcl_lookup(s);
	p = dmap->dmap_table;
	for (i = 0; i < dmap->dmap_curlen; i++, p++) {
		if (p->dment_i.dment_idnum == idnum) {/* if match */
			/* fail if must be visible and symbol not visible */
			if (ifvis && p->dment_i.dment_visible == 0)
				return (Symbol) 0;
			else	/* here if want returned ignoring visibility */
				return (p->dment_symbol);
		}
	}
	/* here if not present */
	return (Symbol) 0;
}

void dcl_put_vis(Declaredmap dmap, char *s, Symbol sym, int vis)
/*;dcl_put_vis*/
{
	/* Set symbol for s to be sym, adding s to map if necessary */

	unsigned short  idnum;
	struct Dment   *p;
	int     i;

	if (dmap == (Declaredmap) 0)
		chaos("dcl_put: declared map NULL");
	idnum = dcl_lookup(s);
	p = dmap->dmap_table;
#ifdef DEBUG
	/* Ultimately this code should be removed. Since this check should
	 * never yield a duplicate value under the new scheme where entries
	 * that already exist are removed first before being reentered.
	 */
	for (i = 0; i < dmap->dmap_curlen;(i++, p++)) {
		if (idnum == p->dment_i.dment_idnum) {/* if match */
			chaos(strjoin("dcl_put_vis found duplicate entry", s));
			p->dment_i.dment_visible = vis;
			p->dment_symbol = sym;
			return;
		}
	}
#endif

	/* here if not present, add to table */
	if (dmap->dmap_curlen >= dmap->dmap_maxlen) {/* need to expand */
		dmap->dmap_maxlen += 4;		/* allocate room for four more entries */
		/* dmap_chk(dmap, "realloc"); */
		dmap->dmap_table = (struct Dment *) erealloct((char *) dmap->dmap_table,
		  (unsigned) (dmap->dmap_maxlen * sizeof(Dment)), "dcl-put-realloc");
	}
	p = dmap->dmap_table + dmap->dmap_curlen;
	p->dment_i.dment_idnum = idnum;
	p->dment_i.dment_visible = vis;
	dmap->dmap_curlen += 1;
	/* dmap_chk(dmap, "retrieve"); */
	p->dment_symbol = sym;
	return;
}

void dcl_put(Declaredmap dmap, char *s, Symbol sym)	/*;dcl_put*/
{
	dcl_put_vis(dmap, s, sym, FALSE);
}

void dcl_undef(Declaredmap dmap, char *s)		/*;dcl_undef*/
{
	/* Set entry for s to be undefined if presently defined */

	unsigned short  idnum, i, j;
	struct Dment   *p;

	idnum = dcl_lookup(s);
	p = dmap->dmap_table;
	for (i = 0; i < dmap->dmap_curlen;(i++, p++)) {
		if (idnum == p->dment_i.dment_idnum) {/* if found */
#ifdef IBM_PC
			/* need memcpy for PC, as possible code generation bug causes
			 * problem on PC if use array code		ds 4-26-86
			 */
			dmap->dmap_curlen -= 1;
			if (i <dmap->dmap_curlen)
				memcpy((char *)p, (char *) (p+1) ,
				  ((dmap->dmap_curlen - i) * sizeof(Dment)));
#else
			for (j = i + 1; j < dmap->dmap_curlen; j++)
				dmap->dmap_table[j - 1] = dmap->dmap_table[j];
			dmap->dmap_curlen -= 1;
#endif
			return;
		}
	}
}

Declaredmap dcl_copy(Declaredmap dm)	/*;dcl_copy*/
{
	/* return copy of declared map */

	Fordeclared fd;
	Symbol sa;
	char   *id;
	Declaredmap rm;

	if (dm == (Declaredmap) 0) chaos("dcl_copy: declared map NULL");

	rm = dcl_new(dm->dmap_curlen);
	FORDECLARED(id, sa, dm, fd)
	    dcl_put_vis(rm, id, sa, IS_VISIBLE(fd));
	ENDFORDECLARED(fd)
    return (rm);
}

#ifdef DEBUG_DCL
dstrings_dump()			/*;dstrings_dump*/
{
	int i, n=0;
	unsigned short j;

	printf("dstrings dump\n");
	for (i=0; i<DSTRINGS_HASH; i++) {
		for (j=dhashtable[i]; j != 0; 
		    j = *((unsigned short *)(dstrings + j)) ) {
			printf("%5d %5d %s\n", i, j,  dstrings + j +sizeof(short));
			n++;
		}
	}
	printf("%d entries require %u\n", n, dstrings_curlen);
}

dmap_chk(Declaredmap dmap, char *lab)				/*;dmap_chk*/
{
	struct Dment * p;
	int	i;

	return;
	printf("dmap chk %s\n", lab);
	p = dmap->dmap_table;
	for (i=0; i<dmap->dmap_curlen; i++, p++) {
		if (p->dment_symbol == (Symbol)0) {
			printf("dmap_chk fails %s\n", lab);
			chaos("dmap_chk");
		}
	}
}

int dcl_dump(Declaredmapdm)		/*;dcl_dump*/
{
	/* write dm to standard output */

	int     i, n=0;
	struct Dment   *p;

	printf("dm dump\n");

	p = dm->dmap_table;
	for (i = 0; i < dm->dmap_curlen;(i++, p++)) {
		n++;
		printf("%u %u %s %lu\n", p->dment_i.dment_visible, 
		  p->dment_i.dment_idnum,
		  dstrings + p->dment_i.dment_idnum, p->dment_symbol);
	}
	printf("%d entries in map, dstrings: curlen %u  maxlen %u\n", n,
	    dstrings_curlen, dstrings_maxlen);
}
#endif
