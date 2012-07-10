/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/*    +---------------------------------------------------+
      | 						  |
      | 	    I N T E R P     M A I N		  |
      | 						  |
      | 		  (C Version)			  |
      | 						  |
      |   Adapted From Low Level SETL version written by  |
      | 						  |
      | 		 Monte Zweben			  |
      | 	      Philippe Kruchten 		  |
      | 	      Jean-Pierre Rosen 		  |
      | 						  |
      |    Original High Level SETL version written by	  |
      | 						  |
      | 	      Robert B. K. Dewar		  |
      | 		  Clint Goss			  |
      | 	      Tracey M. Siesser 		  |
      | 	      Bernard D. Banner 		  |
      | 	      Stephen C. Bryant 		  |
      | 		 Gerry Fisher			  |
      | 						  |
      | 	     C version written by		  |
      | 						  |
      | 	      Robert B. K. Dewar		  |
      | 						  |
      +---------------------------------------------------+		     */

#include <stdio.h>

/*  This module contains constants used in all parts of the interpretor */

/*
 *  General use constants
 *  ---------------------
 */

#define VERSION            "9-25-85"           /* version identification */
#define NB_REGISTERS	   6
#define ADA_MAX_REAL	   8.507055E+37	       /* maximum real with safety */
#ifndef TRUE
#define TRUE		   1		       /* boolean true = Ada true */
#endif
#ifndef FALSE
#define FALSE		   0		       /* boolean false = Ada false */
#endif
#define MIN_LONG	   ((long)0x80000000)	       /* minimum fixed value */
#define MAX_LONG	   ((long)0x7fffffff)	       /* maximum fixed value */
#define ENDLESS 	   -1		       /* value for endless delay */
#define NULL_INT	   ((int *)0)	       /* null pointer value */

/* Special task values, note that OWNER_WAITING must be less than NULL_TASK
 * when two task numbers are compared. This is required for correct functioning
 * of the tasking code.
 */

#define NULL_TASK	   -1		       /* null task pointer value */
#define OWNER_WAITING	   -2		       /* minimum fixed value */

/* Mask for stack access = MAX_TASKS - 1.
 * Note that MAX_TASKS must be a power of two.
 */

#define TMASK              0177

/* Default Values */

#define SECURITY_LEVEL 50 /* free words in the stack before calls */
#define TASK_CODE_OFFSET 4 /* starting offset in code segment for task */

/* Size of long and float values in words (ints) */

#define WORDS_FLOAT (sizeof(float)/sizeof(int))
#define WORDS_LONG   (sizeof(long)/sizeof(int))
#define WORDS_PTR  (sizeof(int *)/sizeof(int))
/* WORDS_HDR is number of words in header of heap block */
#define WORDS_HDR  (1 + WORDS_PTR)

/* Definition of a stack frame */

#define SF_PREVIOUS_SFP 	     0
#define SF_RETURN_CS		     1
#define SF_RETURN_IP		     2

/* Definition of exceptions */

#define CONSTRAINT_ERROR	     1
#define NUMERIC_ERROR		     1
#define PROGRAM_ERROR		     3
#define STORAGE_ERROR		     4
#define TASKING_ERROR		     5
#define SYSTEM_ERROR		     6
/* these come from predef and not be defined here */
#define STATUS_ERROR		     7
#define MODE_ERROR		     8
#define NAME_ERROR		     9
#define USE_ERROR		     10
#define DEVICE_ERROR		     11
#define END_ERROR		     12
#define DATA_ERROR		     13
#define LAYOUT_ERROR		     14
#define TIME_ERROR		     15

/* Attributes */

/* Those attributes marked "static" are treated by the front end and do not
 * appear as arguments to the attribute instruction. Note that POS and VAL
 * are not static, but do not appear as attribute instruction arguments
Static:
A_AFT ATTR_BASE ATTR_DELTA ATTR_DIGITS ATTR_EMAX ATTR_EPSILON ATTR_FIRST_BIT
ATTR_MACHINE_EMAX ATTR_MACHINE_EMIN ATTR_MACHINE_MANTISSA
ATTR_MACHINE_OVERFLOWS ATTR_MACHINE_RADIX ATTR_MACHINE_ROUNDS
ATTR_POS	   -- not static but generates nothing
ATTR_SAFE_EMAX ATTR_SAFE_LARGE ATTR_SAFE_SMALL
ATTR_SMALL ATTR_STORAGE_SIZE(?)
ATTR_VAL --not static but generate a qual_range
 */
#include "attr.h"
#include "ops.h"


/* General Addressing Macros */

/*
 *  LONG(ptr)		Pointer regarded as pointer to long value
 *  ADDR(ds,off)	Get address from data seg offset values
 *  ADDRL(ds,off)	Get address of long from data seg offset values
 *  POP(val)		Pop int val off stack
 *  POPF(fval)		Pop float fval off stack
 *  POPL(lval)		Pop long lvall off stack
 *  POPP(lval)		Pop pointer from stack
 *  POP_ADDR(bs,of)	Pop base/offset address from stack
 *  POP_PTR(ptr)	Pop pointer from stack
 *  PUSH(val)		Push int val onto stack
 *  PUSHF(fval)		Push float fval onto stack
 *  PUSHL(lval)		Push long lval onto stack (also used for fixed)
 *  PUSHP(lval)		Push pointer onto stack
 *  PUSH_ADDR(bs,of)	Push address onto stack
 *  TOS			Reference top of stack as int
 *  TOSF		Reference top of stack as float
 *  TOSL		Reference top of stack as long
 *  TOSM(n)		Reference n'th item from top (TOS = TOSM(0))
 *  BLOCK_FRAME		Pointer to the current block frame
 *  STACK_FRAME(dsp)	Access an element from the current stack frame
 */


#define LONG(ptr)	  ((long *)(ptr))
#define ADDR(ds,off)	  (data_segments[ds] + off)
#define ADDRL(ds,off)	  (LONG(data_segments[ds] + off))
#define POP(val)	  val=cur_stack[cur_stackptr--]
#define POPF(fval)	  fval = TOSF,cur_stackptr -= WORDS_FLOAT
#define POPL(lval)	  lval = TOSL,cur_stackptr -= WORDS_LONG
#define POPP(lval)	  POPL((long)lval)
#define POP_ADDR(bs,of)   POP(of),POP(bs)
#define POP_PTR(pt)       pt=ADDR(TOSM(1),TOS),cur_stackptr -= 2
#define PUSH(val)	  cur_stack[++cur_stackptr] = val
#define PUSHF(fval)	  cur_stackptr+=WORDS_FLOAT,TOSF=fval
#define PUSHL(lval)	  cur_stackptr+=WORDS_FLOAT,TOSL=lval
#define PUSHP(lval)	  PUSHL((long)lval)
#define PUSH_ADDR(bs,of)  PUSH(bs),PUSH(of)
#define TOS		  (cur_stack[cur_stackptr])
#define TOSF		  *((float *)(cur_stack+cur_stackptr+1-WORDS_FLOAT))
#define TOSL		  *(LONG(cur_stack+cur_stackptr+1-WORDS_LONG))
#define TOSML(n)	  *(LONG(cur_stack+cur_stackptr+1-((n)+1)*WORDS_LONG))
#define TOSM(n) 	  (cur_stack[cur_stackptr-(n)])
#define BLOCK_FRAME	  ((struct bf *)(cur_stack+bfp))
#define ARB_BLOCK_FRAME(t,b) ((struct bf *)((STACK(t))+(b)))
#define STACK_FRAME(dsp)  cur_stack[sfp+dsp]

/* Macros for accessing fields of block frame */

#define BF_PREVIOUS_BFP(t,b) 	(ARB_BLOCK_FRAME(t,b))->bf_previous_bfp
#define BF_DATA_LINK(t,b) 	(ARB_BLOCK_FRAME(t,b))->bf_data_link
#define BF_TASKS_DECLARED(t,b) 	(ARB_BLOCK_FRAME(t,b))->bf_tasks_declared
#define BF_SUBTASKS(t,b) 	(ARB_BLOCK_FRAME(t,b))->bf_subtasks
#define BF_HANDLER(t,b) 	(ARB_BLOCK_FRAME(t,b))->bf_handler
#define BF_NUM_NOTERM(t,b) 	(ARB_BLOCK_FRAME(t,b))->bf_num_noterm
#define BF_NUM_DEPS(t,b) 	(ARB_BLOCK_FRAME(t,b))->bf_num_deps

#define MY_PREVIOUS_BFP	  	(BLOCK_FRAME)->bf_previous_bfp
#define MY_DATA_LINK	  	(BLOCK_FRAME)->bf_data_link
#define MY_TASKS_DECLARED	(BLOCK_FRAME)->bf_tasks_declared
#define MY_SUBTASKS	  		(BLOCK_FRAME)->bf_subtasks
#define MY_HANDLER	  		(BLOCK_FRAME)->bf_handler
#define MY_BF_NUM_NOTERM	(BLOCK_FRAME)->bf_num_noterm
#define MY_BF_NUM_DEPS		(BLOCK_FRAME)->bf_num_deps

/* Utility Macros */

#define ABS(v)		  ((v) >= 0 ? (v) : -(v))
#define BOOL(v)       ((v) % 2)
#define MAX(a,b)	  (((a) >= (b)) ? (a) : (b))
#define MIN(a,b)	  (((a) <= (b)) ? (a) : (b))
#define SIGN(a) 	  (((a) > 0) - ((a) < 0))


/* Block Frame */

   struct bf {
      int	  bf_previous_bfp;	/* offset to previous block frame */
      int	 *bf_data_link; 	/* head of chain of data blocks */
      int	 *bf_tasks_declared;	/* head of chain of created tasks */
      int	  bf_num_noterm;	/* number of non terminated */
      int	  bf_num_deps;		/* number of non terminated */
      int	  bf_subtasks;		/* head of chain of dependent tasks */
      int	  bf_handler;		/* IP of exception handler */
   };

/** NEW TYPES **/

/* Item Type for Multi-Queues */

   struct rts_item {
      int	  mult, save_mult;	/* multiplicity count             */
      int	  parent;			/* parent tcb index               */
      int	  *tcbs;			/* array of tcb nums of new tasks */
      int	  type;				/* action - create or activate    */
      int	  prio;		 		/* priority of rts item           */
      int	  templ_base;		/* task's template's base         */
      int	  templ_off;		/* task's template's offset       */
      int	  master_task;		/* master task number             */
      int 	  master_block;		/* offset in master task's stack  */
      struct rts_item *next;	/* pointer to next item           */
   };

/* Lock type */

#define LOCK(a)		(a)->lock
   struct lock_type {
      int	  add_lock; 		/* lock needed by callers of entry */
      int	  del_lock; 		/* lock needed by owner of entry   */
   };

/* Ready queue header type */

   struct ready_q {
      struct lock_type lock;   		/* lock needed by callers of entry */
      int	  count;		 		/* number of tasks queued on entry */
      struct rts_item *first;		/* first task queued on entry      */
      struct rts_item *last;		/* last task queued on entry       */
      int	  first_mult;			/* multiplicity left of first item */
   };

/* Entry Queue item type */

   struct q_item {
      int	  flag;			/* bit on if has not been removed */
      int	  task;		 	/* task id 			  */
      struct q_item *next;		/* next on chain		  */
   };

/* Entry type in Task Control Block */

   struct entry_type {
      struct lock_type lock;   		/* lock needed by callers of entry */
      int	  count; 		/* number of tasks queued on entry */
      struct q_item *first;		/* first task queued on entry      */
      struct q_item *last;		/* last task queued on entry       */
      int	  guard;  		/* guard of the entry              */
   };

/* Io_item type in Task Control Block */

   struct io_item_type {
      int 	task;
      int       flag;
      long      delta;
      struct io_item_type *next;
   };

/* Task Control Block */
/*  Note:  The first two fields (tbase and toff) must appear in that order */
/*   	   as the first two fields of the tcb ... 			   */

   struct tcb_type {
      int	  tcb_tbase;            /* task base address               */
      int	  tcb_toff;             /* task offset                     */
      int	  tcb_abnormal;			/* flag set when task is aborted   */
      int	  tcb_action;			/* action executing when blocked   */
      int	  tcb_brother;			/* next direct dep. of master const*/
      int         *tcb_block_ptr;	/* currently executing block frame */
      struct q_item *tcb_entry_item; /* pointer to item in entry queue  */
      struct entry_type *tcb_curr_entry;/* pointer to current entry queue  */
      int	  tcb_event;			/* event to unblock (set by others)*/
      int	  tcb_exception;		/* current exception raised        */
      int	  tcb_first;			/* first field                     */
      int	  tcb_id;				/* index of task in RTS item       */
      struct io_item_type *tcb_io_item;	/* curr. io_item (made when delay) */
      int	  tcb_master_task;	 	/* number of the master task       */
      int         tcb_master_block; /* number of the master block      */
      int	  tcb_next;				/* ptr to next task to activate OR */
					/* prev. partner of my partner     */ 
      int	  tcb_num_items;		/* number of items                 */
      int	  tcb_num_noterm;		/* # of nonterminatable direct dep.*/
      int	  tcb_num_deps;			/* # of nonterminatd direct dep.   */
      int	  tcb_num_entries;		/* # of entries                    */
      int	  tcb_num_events;		/* # of pending events             */
      int	  tcb_parent;			/* tcb index of parent task        */
      int	  tcb_prio;				/* task priority                   */
      int	  tcb_rdv;				/* flag set when executes open acpt*/
      struct rts_item *tcb_rts_item;/* my current rts item             */
      int	  tcb_save_prio;		/* task save priority              */
      int	  tcb_serviced;			/* current calling partners chain  */
      int	  tcb_status;			/* current status, set by me       */
      int	  tcb_what;				/* entry called (set by caller)    */
      int	  tcb_who;				/* who called entry (set by caller)*/
      struct entry_type  tcb_entry;	/* list of entries 		   */
   };




/* Functions returning other than INT values */

#include "type.h"

#define FIX_BAS 128
#define FIX_DIGS 7
#define FIX_LENGTH 19

/* rename some procedures to avoid name conflicts with library routines
 * on pc or bsd (these confuse lint output).
 */
#define abort abortp
#define kill killp
#define signal signalp
#define wait waitp

/*
 *                         P R E D E F
 */
/* GENERAL DATA STRUCTURES FOR FILES
 *
 * Files in Ada are described by a structure called an AFCB (Ada File
 * Control Block). The vector afcb contains pointers to allocated AFCB's
 * with a null entry indicating an unused index value. An Ada file value
 * is an index into this vector, with zero indicating a closed file.
*/

struct afcb {

   /* Fields used for all file modes */

   FILE	*io_fdesc;	     /* file descriptor (null if not associated) */
   char *io_fname;	     /* file name */
   char *io_form;	     /* file form string */
   int	io_mode;	     /* file mode */

   /* Fields used only for DIRECT_IO, undefined for other cases */

   int dio_pos; 	     /* current file index */
   int dio_length;	     /* length of record */
   int dio_size;	     /* number of records currently written */

   /* Fields used only for TEXT_IO, undefined for other cases */

   int	tio_page;	     /* page number */
   int	tio_line;	     /* line number */
   int	tio_col;	     /* column number */
   int	tio_line_length;     /* line length, 0 = unbounded */
   int	tio_page_length;     /* page length, 0 = unbounded */

   /* The following fields implement up to a three character look ahead
    * for TEXT_IO input files, with tio_count being the number of characters
    * currently stored. If tio_count is less than 3, it means that the end
    * of file is after the last stored character.
   */

   int	 tio_count;	     /* count of chars stored in tio_look_ahead */
   char  tio_look_ahead[3];  /* three characters of look ahead */

};

/* Structure used to remember names of temporary files in linked list */

struct tfile {
   struct tfile *tfile_next;	/* next entry on list */
   char tfile_name [15];
};
