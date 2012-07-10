/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/*    +---------------------------------------------------+
      |                                                   |
      |      I N T E R P R E T E R   V A R I A B L E S    |
      |                                                   |
      |                    (C Version)                    |
      |                                                   |
      |   Adapted From Low Level SETL version written by  |
      |                                                   |
      |                    Monte Zweben                   |
      |                 Philippe Kruchten                 |
      |                 Jean-Pierre Rosen                 |
      |                                                   |
      |    Original High Level SETL version written by    |
      |                                                   |
      |                     Clint Goss                    |
      |                  Tracey M. Siesser                |
      |                  Bernard D. Banner                |
      |                  Stephen C. Bryant                |
      |                    Gerry Fisher                   |
      |                                                   |
      |                 C version written by              |
      |                                                   |
      |                  Robert B. K. Dewar               |
      |                                                   |
      +---------------------------------------------------+     */


/* Revision History
  19 Jun 1985, 10:11 (RBKD)
  First complete version, from low level version 10-23-1984
 */
C#include <stdlib.h>
C#include "config.h"
C#include "int.h"
/*  This module contains variables used in all parts of the interpretor */

/*
 *  Memory lay-out
 *  --------------
 */

X int *stack_segments [MAX_TASKS]; /* one stack segment for each task */
X int task_stackptr [MAX_TASKS];   /* stack pointers for task stacks */
X unsigned int data_segments_dim;  /* dimension of data_segments */
X int **data_segments;             /* one data segment for each cunit */
X int *data_seglen;                /* length of data segments */
X unsigned int code_segments_dim;  /* dimension of code_segments */
X char **code_segments;            /* segments containing code */
X int *code_seglen;                /* length of code segments */
X int *cur_stack;                  /* current stack segment */
X int cur_stackptr;                /* stack ptr for cur_stack */
X char *cur_code;                  /* current code segment */
X int num_cunits;                  /* number of compilation units */

/*
 *  Context of a task
 *  -----------------
 */

X int cs;       /* index of current code_segment in code_segments */
X int ip;       /* instruction pointer in cur_code */
X int sp;       /* stack pointer */
X int sfp;      /* stack frame pointer */
X int bfp;      /* block frame pointer */
X int exr;      /* exception register */
X int lin;      /* line number for tracing */

/*
 *  Global context (not preserved by context switch)
 *  ------------------------------------------------
 */

X int tp;                /* index of current task in stack_segments */
X int *heap_next;        /* top of heap for allocation */
X int heap_base;         /* segment number of heap */
X int *heap_addr;        /* address of beginning of heap */
X long next_clock;        /* next time to call clock_interrupts */
X long time_offset;       /* cumulative skipped time for simulated time */
X int next_clock_flag;   /* request to check the clock (task waiting) */
X int simul_time_flag;   /* run with simulated time (versus real time) */
X int time_slicing_flag; /* time slicing (vs schedule at system call) */
X long time_slice;        /* length of time slice (500 ms default) */
X int tasking_trace;     /* TRUE to trace tasking */
X int rendezvous_trace;  /* TRUE to trace rendezvous */
X int debug_trace;       /* TRUE for general debugging trace */
X int exception_trace;   /* TRUE to trace exceptions */
X int call_trace;        /* TRUE to trace calls */
X int line_trace;        /* TRUE to trace line numbers */
X int instruction_trace; /* TRUE to trace instructions */
X int context_sw_trace;  /* TRUE to trace context switches */
X int rr_flag;           /* TRUE to allow round-robin scheduling */
X int rr_counter;        /* counter of statements - round_robin scheme*/
X int rr_nb_max_stmts;   /* max value of rr_counter. */

/* Number of slots */

X unsigned int data_slots_dim;      /* dimension of data_slots */
X char **data_slots;
X unsigned int code_slots_dim;      /* dimension of code_slots */
X char **code_slots;
X unsigned int exception_slots_dim; /* dimension of exception_slots */
X char **exception_slots;

/* Global Variables (for main interpreter) */

X int max_mem;                      /* size of a heap segment */
X int w;                            /* used by GET_WORD */
X struct tt_fx_range *temp_template;/* fixed point work template */

X int bse,bas1,bas2,bas3,bas4;      /* address base values */
X int off,off1,off2,off3,off4;      /* address offset values */
X int *ptr,*ptr1,*ptr2,*ptr3,*ptr4; /* memory addresses */
X int value,val1,val2;              /* operands for int operations */
X int length1,length2;              /* for array operations */
X long lvalue,lval1,lval2;          /* operands for long operations */
X long fval1,fval2,fvalue;          /* operands for fixed operations */
X float rvalue,rval1,rval2;         /* operands for float operations */
X int val_high,val_low;             /* low/high of INT range */
X int result,delta;                 /* used in fixed point */
X int size;                         /* size of object */
X int attribute;                    /* attribute code */
X int slot;                         /* for create structure */
X int component_size;               /* size of array component */
X long now_time;                     /* current time */
X int to_type;                      /* type from template */
X int discr_list[MAX_DISCR];        /* accumulate list of discriminants */
X int nb,i;                         /* loop counters etc */
X int overflow;                     /* overflow flag from arith routines */
X int nb_discr;                     /* number of discriminants */
X int nb_dim;                       /* dimension of array */
X int ratio,power;                  /* used in attribute processing */
X int d,n;                          /* temporaries */
X int old_cs;                       /* old value of cs */
X int jump;                         /* jump address */
X int lim;                          /* limit in for loop */
X struct bf *bfptr;                 /* pointer to block frame */
X int *tfptr1,*tfptr2;              /* pointers to task frames */
X int cur_col;                      /* temporary for predef */

X int break_point;       /* next break point */  

X int fix_val1[20];      /* fixed point intermediate values */
X int fix_val2[20];     
X int fix_resu[20];     
X int fix_temp[20];     
X int mul_fact[20];     
X int div_fact[20];     

X int arith_overflow;
X int sgn;
X int last_task;
X int *free_list INIT((int *)0);
X int raise_cs;
X int raise_lin;
X char *raise_reason;

/*
 *                             P R E D E F
 */

/* Define maximum number of files and AFCB vector to match */

/*
 * Note that file numbers are 1's origin subscripts into this vector, so that
 * the file number value of 1 corresponds to the first entry, i.e. afcbs[0]
 */

#define MAXFILES 20
X struct afcb *(afcbs[MAXFILES]);

/* Variables for predef */

X int operation;         /* operation for predef. set in the main loop */
X int data_exception;    /* exception to raise on data error */
X int filenum;           /* number of current file */
X int standard_in_file;  /* index of standard input file */
X int standard_out_file; /* index of standard output file */
X int current_in_file;   /* index of current default input file */
X int current_out_file;  /* index of current default output file */
X int current_in_file_saved;   
	 /* duplicate index of current default input file */
X int current_out_file_saved;  
	 /* duplicate index of current default output file */
X int file_offset;       /* Offset due to file argument in the stack */
                         /* 2 if explicit file, 0 if default file */
X struct tfile *tfiles;  /* linked list of temporary files */

/*
 * The area work_string is used to hold an ASCIIZ string. It is a strictly
 * temporary area which can be destroyed by almost any function. Anyone
 * who needs to keep this string value must copy it using make_string.
 *
 * Note that the maximum length of strings in the Ada system is 4K bytes.
*/

X char work_string[4096];

/* The task stack size for created tasks is given by new_task_size,
 * and the size of the main task is given by main_task_size.
 * These are initialized in imain.c; and can be set by program options
 * -s and -p, respectively.
 */

X int main_task_size;
X int new_task_size;
