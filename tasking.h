/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* GLOBAL DECLARATIONS */

#define TRACE 
#define time_slice 50

/* Macros used to access tasks stacks and stacks pointers */

#define ORIG(task)                original_task[task & TMASK]
#define STACK(task)               stack_segments[task & TMASK]
#define STACKPTR(task)            task_stackptr[task & TMASK]

#define NULL_BROTHER	-2

/* Macros used to access TCB fields in current task */

#define MY_TCB			  ((struct tcb_type *)cur_stack)
#define WORDS_TCB ((sizeof(struct tcb_type)-sizeof(struct entry_type)) \
				/(sizeof(int)))
#define WORDS_ENT    		  6
#define REAL_ENT    		  ((sizeof(struct entry_type))/(sizeof(int)))
#define TCB(task)		  ((struct tcb_type *)stack_segments[task & TMASK])

/* Macros used to access TCB fields in current task */

#define MY_ABNORMAL 	  MY_TCB->tcb_abnormal
#define MY_ACTION         MY_TCB->tcb_action
#define MY_BROTHER	  MY_TCB->tcb_brother    
#define MY_BLOCK_PTR	  MY_TCB->tcb_block_ptr   
#define MY_CURR_ENTRY	  MY_TCB->tcb_curr_entry
#define MY_ENTRY_ITEM	  MY_TCB->tcb_entry_item
#define MY_EVENT	  MY_TCB->tcb_event 
#define MY_EXCEPTION  	  MY_TCB->tcb_exception   
#define MY_FIRST	  MY_TCB->tcb_first
#define MY_ID  	  	  MY_TCB->tcb_id   
#define MY_IO_ITEM	  MY_TCB->tcb_io_item   
#define MY_MASTER_TASK	  MY_TCB->tcb_master_task
#define MY_MASTER_BLOCK	  MY_TCB->tcb_master_block
#define MY_NEXT	  	  MY_TCB->tcb_next    
#define MY_NOT_TERM	  MY_TCB->tcb_not_term    
#define MY_NUM_ITEMS      MY_TCB->tcb_num_items
#define MY_NUM_NOTERM  	  MY_TCB->tcb_num_noterm
#define MY_NUM_DEPS 	  MY_TCB->tcb_num_deps
#define MY_NUM_ENTRIES    MY_TCB->tcb_num_entries
#define MY_NUM_EVENTS  	  MY_TCB->tcb_num_events
#define MY_PARENT  	  MY_TCB->tcb_parent
#define MY_PRIO		  MY_TCB->tcb_prio
#define MY_RDV  	  MY_TCB->tcb_rdv
#define MY_RTS_ITEM  	  MY_TCB->tcb_rts_item  
#define MY_SAVE_PRIO 	  MY_TCB->tcb_save_prio
#define MY_SERVICED  	  MY_TCB->tcb_serviced
#define MY_STATUS  	  MY_TCB->tcb_status 
#define MY_TBASE	  MY_TCB->tcb_tbase
#define MY_TOFF	  	  MY_TCB->tcb_toff
#define MY_WHAT  	  MY_TCB->tcb_what
#define MY_WHO  	  MY_TCB->tcb_who
#define MY_ENTRY(i)   (struct entry_type *) (&(MY_TCB->tcb_entry)+(i-1))

/* Macros used to access TCB fields in another task */

#define TCB_ABNORMAL(task) 	  TCB(task)->tcb_abnormal
#define TCB_ACTION(task)	  TCB(task)->tcb_action
#define TCB_BROTHER(task)	  TCB(task)->tcb_brother 
#define TCB_BLOCK_PTR(task)	  TCB(task)->tcb_block_ptr   
#define TCB_CURR_ENTRY(task)	  TCB(task)->tcb_curr_entry   
#define TCB_ENTRY_ITEM(task)	  TCB(task)->tcb_entry_item   
#define TCB_EVENT(task)		  TCB(task)->tcb_event
#define TCB_EXCEPTION(task)  	  TCB(task)->tcb_exception   
#define TCB_FIRST(task)		  TCB(task)->tcb_first
#define TCB_ID(task)  	  	  TCB(task)->tcb_id   
#define TCB_IO_ITEM(task)	  TCB(task)->tcb_io_item   
#define TCB_MASTER_TASK(task)	  TCB(task)->tcb_master_task    
#define TCB_MASTER_BLOCK(task)	  TCB(task)->tcb_master_block   
#define TCB_NEXT(task)	  	  TCB(task)->tcb_next    
#define TCB_NUM_ITEMS(task)  	  TCB(task)->tcb_num_items
#define TCB_NUM_NOTERM(task)  	  TCB(task)->tcb_num_noterm
#define TCB_NUM_DEPS(task) 	  TCB(task)->tcb_num_deps
#define TCB_NUM_ENTRIES(task)  	  TCB(task)->tcb_num_entries
#define TCB_NUM_EVENTS(task)  	  TCB(task)->tcb_num_events
#define TCB_PARENT(task)  	  TCB(task)->tcb_parent
#define TCB_PRIO(task)  	  TCB(task)->tcb_prio
#define TCB_RDV(task)  		  TCB(task)->tcb_rdv
#define TCB_RTS_ITEM(task)  	  TCB(task)->tcb_rts_item
#define TCB_SAVE_PRIO(task)	  TCB(task)->tcb_save_prio
#define TCB_SERVICED(task)  	  TCB(task)->tcb_serviced
#define TCB_STATUS(task)  	  TCB(task)->tcb_status 
#define TCB_TBASE(task)		  TCB(task)->tcb_tbase
#define TCB_TOFF(task)		  TCB(task)->tcb_toff 
#define TCB_WHAT(task)  	  TCB(task)->tcb_what
#define TCB_WHO(task)  		  TCB(task)->tcb_who
#define TCB_ENTRY(task,i)         (struct entry_type *)(&(TCB(task)->tcb_entry)\
					+ (i-1))

/* Macros for accessing entry structure */

#define ENTRY_COUNT(e)		(e)->count
#define ENTRY_FIRST(e)		(e)->first
#define ENTRY_LAST(e)		(e)->last
#define ENTRY_GUARD(e)		(e)->guard
#define ENTRY_ADD_LOCK(e)	(e)->lock.add_lock
#define ENTRY_DEL_LOCK(e)	(e)->lock.del_lock
#define EMPTY		-1     /* value of EMPTY CHAIN */

/* Macros for accessing io_items */

#define II_FLAG(i)		(i)->flag
#define II_TASK(i)		(i)->task
#define II_DELTA(i)		(i)->delta
#define II_NEXT(i)		(i)->next

/* Macros for accessing entry queue items */

#define ITEM_FLAG(i)		(i)->flag
#define ITEM_TASK(i)		(i)->task
#define ITEM_NEXT(i)		(i)->next

/* Macros for rts items */

#define RTS_PARENT(i)		(i)->parent
#define RTS_MULT(i)		(i)->mult
#define RTS_SAVE_MULT(i)		(i)->save_mult
#define RTS_TCBS(i,j)		(i)->tcbs[j]
#define RTS_TYPE(i)		(i)->type
#define RTS_PRIO(i)		(i)->prio
#define RTS_TF(i)		(i)->tf
#define RTS_TEMPL_BASE(i)	(i)->templ_base
#define RTS_TEMPL_OFF(i)	(i)->templ_off
#define RTS_MASTER_TASK(i)	(i)->master_task
#define RTS_MASTER_BLOCK(i)	(i)->master_block
#define RTS_NEXT(i)		(i)->next

/* Status values */

#define ACTIVE		  0
#define ACTIVATING	  1
#define CALLING_RDV	  2
#define TIMED_RDV	  3
#define SELECTING_NOTERM  4
#define SELECTING_TERM	  5
#define COMPLETE_BLOCK    6
#define COMPLETED	  7
#define TERMINATED	  8
#define ABNORMAL	  9
#define WAIT             10
#define QUIESCENT        11

/* Definition of events */

#define TERMINATE_EVENT  -1
#define ENDRDV_EVENT	 -2
#define TASKERR_EVENT	 -3
#define NO_EVENT	 -4
#define RDV_EVENT        -5
#define DISABLED_EVENT   -6
#define ABORT_EVENT	 -7
#define TIMER_EVENT	 -8
#define PROGERR_EVENT	 -9


/* Definition of action codes */

#define NO_ACTION 	1
#define ABORT_ONE	2
#define FREE_TASK_SPACE	3
#define COMPLETE_TASK_ONE 	4
#define COMPLETE_BLOCK_ONE	5
#define COMPLETE_BLOCK_TWO	6
#define ENTRY_CALL	7
#define SELECTIVE_WAIT	8
#define TERM_WAVE	9
/* #define WAIT		10		-- already defined as a status -- */
#define DONE_ACTIVATION 11
#define DONE_CREATION	12
#define CONTEXT_SWITCH	13
#define ACTIVATE_SELF	14

/* Definition of actions of RTS items */

#define ACTIVATE	1
#define CREATE		2
#define READY		3
