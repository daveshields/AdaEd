/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#ifndef __segment_h
#define __segment_h

/* header file for Segment structure and constants */
typedef struct Segment_s {
    short seg_id;		/* code to identify segment */
    short seg_kind;		/* segment kind, one of SEGMENT_KIND...*/
    short seg_size;		/* size of entry in bytes */
    unsigned int seg_pos;	/* index of next element */
    unsigned int seg_maxpos;	/* maximum position value */
    unsigned int seg_dim;  	/* dimension of data area */
    unsigned int seg_extend; 	/* extension count */
    int **seg_ptr;		/* pointer tracking field */
    char *seg_data; 		/* data string as char */
} Segment_s;

typedef struct Segment_s *Segment;

#define SEGMENT_KIND_CODE 0
#define SEGMENT_KIND_DATA 1

#define SEG_ID  1985

#endif
