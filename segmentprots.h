/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#ifdef MACHINE_CODE
void print_data_segment();
#endif
void segment_append(Segment, Segment);
void seg_check(Segment);
void segment_empty(Segment);
void segment_free(Segment);
int segment_get_int(Segment, int);
unsigned int segment_get_pos(Segment);
unsigned int segment_get_maxpos(Segment);
int segment_get_off(Segment, int);
void segment_put_byte(Segment, int);
void segment_put_const(Segment, Const);
void segment_put_int(Segment, int);
void segment_put_long(Segment, long);
void segment_put_off(Segment, int, int);
void segment_put_real(Segment, double);
void segment_put_ref(Segment, int, int);
void segment_put_word(Segment, int);
void segment_set_pos(Segment, unsigned, unsigned);
Segment template_new(int, int, int, int **);
unsigned int PC();
#ifdef DEBUG
void zpseg(Segment);
#endif
