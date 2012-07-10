/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

void rselect(int);
int actual_size(int *, int []);
void record_move(int *, int *, int *);
void membership();
int qual_index(int *type_ptr1, int *type_ptr2);
int qual_sub(int *type_ptr1, int *type_ptr2);
void qual_discr(int, int);
void allocate_new();
void allocate_copy(int, int);
void fix_convert(int *, struct tt_fx_range *, struct tt_fx_range *);
int fix_out_of_bounds(long, int *);
void create(int, int *, int *, int **);
void allocate(int, int *, int *, int **);
void push_task_frame(int);
int pop_task_frame();
void deallocate(int *);
int expn(float);
void check_subtype_with_discr(int *, int []);
