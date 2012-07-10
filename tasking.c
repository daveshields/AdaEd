/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/*
	  +---------------------------------------------------+
	  |                                                   |
	  |          I N T E R P         T A S K I N G        |
	  |                                                   |
	  |                    (C Version)                    |
	  |                                                   |
	  |   Adapted From Low Level SETL version written by  |
	  |                                                   |
	  |                  Monte Zweben                     |
	  |               Philippe Kruchten                   |
	  |               Jean-Pierre Rosen                   |
	  |                                                   |
	  |    Original High Level SETL version written by    |
	  |                                                   |
	  |               Robert B. K. Dewar                  |
	  |                   Clint Goss                      |
	  |               Tracey M. Siesser                   |
	  |               Bernard D. Banner                   |
	  |               Stephen C. Bryant                   |
	  |                  Gerry Fisher                     |
	  |                                                   |
	  |              C version written by                 |
	  |                                                   |
	  |               Robert B. K. Dewar                  |
	  |                                                   |
	  +---------------------------------------------------+
*/


/* Include standard header modules */
#include <stdlib.h>
#include <stdio.h>
#include "config.h"
#include "ipar.h"
#include "ivars.h"
#include "int.h"
#include "tasking.h"
#include "segment.h"
#include "iparprots.h"
#include "intaprots.h"
#include "intbprots.h"
#include "intcprots.h"
#include "miscprots.h"
#include "taskingprots.h"

#ifdef IBM_PC
#include <time.h>
static void sleep(unsigned);
#endif

static void done_creation();
static void create_task(int, int, struct rts_item *, int);
static void done_activation();
static void activate_self(int, int);
static void kill(int);
static void abortme();
static void post_abort_one();
static void post_complete_task_one();
static void post_complete_block();
static void post_complete_block_two();
static void task_term();
static void free_task_space();
static void check_termination(int, int);
static void check_done(int, int);
static void check_unterm();
static void tell_termination(int);
static void uncreate_tasks(int);
static void my_set_timer(struct io_item_type *, long);
static int long my_reset_timer(long);
static void wait(long, int);
static void post_wait();
static void catcher(long);
static struct io_item_type *chain(int, long);
static void check_free(struct io_item_type *);
static int get_io(struct io_item_type *);
static void disable_io(struct io_item_type **);
static int remove_io(struct io_item_type **);
static void schedule(int);
static void finish_action(struct rts_item *);
static void make_ready(int, int);
static void transfer(int);
static void evaluate_guards(int [], int);
static void close_guards(int [], int);
static void post_selective_wait(int, int, int [], int []);
static void accept_rdv(int, int, int);
static void post_entry_call();
static void einit(struct entry_type	*);
static int eremove(int);
static void eput(struct entry_type *, int, struct q_item **);
static int eget(struct entry_type *);
static void add_lock(struct lock_type *);
static void add_unlock(struct lock_type *);
static void del_lock(struct lock_type *);
static void del_unlock(struct lock_type *);
static int entry_number(int, int, int);
static void multisignal(int, int);
static void add_serviced(int, int);
static int remove_serviced();
static void qinit();
static void enqueue(int, int);
static void enqueue_item(int, struct rts_item *);
static struct rts_item *dequeue(struct ready_q *, int *);
static void context_switch();

/* Global variables for tasking management */

/* id of the owner of the corr. stack */
static int original_task[MAX_TASKS];
/* Head of task chained waiting on clock */
static struct io_item_type *clock_head;
/* Highest priority of tasks to schedule */
static int highest_priority;
/* Previous value of time */
static long last_time;
/* temporary decl of ready queues  */
static struct ready_q *ready_queue[MAX_PRIO];

/*-------------------------------------------------------------------------*
 *                ----  T A S K I N G    S Y S T E M   ---                 *
 *                                                                         *
 *  The module contains all of the tasking control routines.  It is        *
 *  divided into nine major sections.  Itemized under each section are the *
 *  routines which are callable from outside the tasking module.  Unless   *
 *  interface changes are made it is essential that the status of the      *
 *  stack, on entry and exit from these routines, be maintained.           *
 *                                                                         *
 *      - Task Initialization                                              *
 *               * initialize_tasking                                      *
 *      - Task Creation                                                    *
 *               * start_creation                                          *
 *      - Task Activation                                                  *
 *               * start_activation                                        *
 *               * union_tasks_declared                                    *
 *               * end_activation                                          *
 *      - Task Abortion                                                    *
 *               * abort                                                   *
 *      - Task Termination                                                 *
 *               * complete_task                                           *
 *               * complete_block                                          *
 *               * terminate_unactivated                                   *
 *               * purge_rdv                                               *
 *      - Timer Maintainence                                               *
 *               * delay_stmt                                              *
 *               * clock_interrupt                                         *
 *      - Task Scheduler                                                   *
 *               * round_robin                                             *
 *      - Rendezvous                                                       *
 *               * entry_call                                              *
 *               * selective_wait                                          *
 *               * end_rendezvous                                          *
 *      - Utility Routines (queue routines etc.                            *
 *               * raise_in_caller                                         *
 *               * is_callable                                             *
 *               * is_terminated                                           *
 *               * count                                                   *
 *                                                                         *
 *-------------------------------------------------------------------------*/


/*-------------------------------------------------------------------------*/
/*            T A S K I N G    I N I T I A L I Z A T I O N                 */
/*                                                                         */
/*  Procedure to perform necessary initialization for tasking system       */
/*-------------------------------------------------------------------------*/

void initialize_tasking()							/*;initialize_tasking*/
{
	int     i;
	int    *p;
	long   itime();

	/*  Initialize variables */

	last_task = 1;

	for (i = 0; i < MAX_TASKS; i++) {
		STACK(i) = (int *)0;
		ORIG(i) = NULL_TASK;
	}
	qinit();
	time_offset = 0;
	last_time = itime();
	clock_head = NULL;
	next_clock = itime();
	next_clock_flag = FALSE;
	rr_counter = 0;

	/*  Initiate the idle task */

	p = STACK(0) = (int *) malloc((unsigned) sizeof(int) * main_task_size);
	ORIG(0) = 0;
	if (p == (int *)0) {
		printf("Unable to allocate stack\n");
		exit(RC_ABORT);
	}

	TCB_ABNORMAL(0) 	 = 0;
	TCB_ACTION(0) 	 	 = NO_ACTION;
	TCB_BROTHER(0)	     = 0;
	TCB_BLOCK_PTR(0)	 = (int *) 0;
	TCB_CURR_ENTRY(0)	 = NULL;
	TCB_EVENT(0)		 = NO_EVENT;
	TCB_EXCEPTION(0)  	 = 0;
	TCB_ENTRY_ITEM(0)	 = 0;
	TCB_FIRST(0)		 = 0;
	TCB_ID(0)		     = 0;
	TCB_IO_ITEM(0)	     = NULL;
	TCB_MASTER_TASK(0)	 = NULL_TASK;
	TCB_MASTER_BLOCK(0)	 = 0;
	TCB_NEXT(0)	  	     = NULL_TASK;
	TCB_NUM_ITEMS(0)  	 = 0;
	TCB_NUM_NOTERM(0)  	 = 0;
	TCB_NUM_DEPS(0) 	 = 0;
	TCB_NUM_ENTRIES(0)   = 0;
	TCB_NUM_EVENTS(0)  	 = 0;
	TCB_PARENT(0)	 	 = NULL_TASK;
	TCB_PRIO(0)  	     = 0;
	TCB_RDV(0)  		 = 0;
	TCB_RTS_ITEM(0)		 = NULL;
	TCB_SAVE_PRIO(0)	 = 0;
	TCB_SERVICED(0)  	 = 0;
	TCB_STATUS(0)  	     = ACTIVE;
	TCB_TBASE(0)		 = 1;
	TCB_TOFF(0)		     = 52;
	TCB_WHAT(0)  	     = 0;
	TCB_WHO(0)  		 = NULL_TASK;

	/*  Set context for idle task */

	STACKPTR(0) = WORDS_TCB;
	tp = 0;
	cur_stack = STACK(tp);
	cur_stackptr = STACKPTR(tp);
	bfp = 0;
	ip = TASK_CODE_OFFSET;
	cs = 1;
	sfp = 0;
	lin = 0;
	exr = 0;
	cur_code = code_segments[cs];
}


/*--------------------------------------------------------------------------*/
/*                     T A S K    C R E A T I O N                           */
/*                                                                          */
/*  The following set of routines perform task creation                     */
/*--------------------------------------------------------------------------*/

/*-------------------------------------------------------------------------*/
/*                             START  CREATION                             */
/*  Create an array of tasks, do so by creating a RTS item for the array   */
/*  As tasks become ready to run they will perform activations etc. first  */
/*  using this RTS item                                                    */
/*-------------------------------------------------------------------------*/

void start_creation(int templ_base, int templ_off)			/*;start_creation*/
{
	int	mult = 1;
	struct rts_item 	*rts;

	if (BLOCK_FRAME->bf_tasks_declared == NULL)
		push_task_frame(NULL_TASK);		/* create null frame */

	rts = (struct rts_item *) malloc(sizeof(struct rts_item));
	if (rts == (struct rts_item *)0) {
		raise(STORAGE_ERROR, "Allocating space for task");
		return;
	}
	rts->tcbs = (int *) malloc((unsigned) sizeof(int)*mult);
	if (rts->tcbs == (int *)0) {
		raise(STORAGE_ERROR, "Allocating space for task");
		return;
	}
	RTS_TYPE(rts) = CREATE;
	RTS_PRIO(rts) = MY_PRIO;
	RTS_TEMPL_BASE(rts) = templ_base;
	RTS_TEMPL_OFF(rts) = templ_off;
	RTS_MULT(rts) = mult;
	RTS_NEXT(rts) = NULL;
	RTS_PARENT(rts) = tp;

	MY_WHAT = NULL_TASK;
	MY_NUM_ITEMS = mult;
	enqueue_item(MY_PRIO, rts);
	schedule(DONE_CREATION);
}

/*--------------------------------------------------------------------------*/
/*                             DONE   CREATION                              */
/*   Performed after all of my tasks have finished creation.  Add current   */
/*   RTS item to chain                                                      */
/*--------------------------------------------------------------------------*/

static void done_creation()									/*;done_creation*/
{
	if (MY_EXCEPTION == STORAGE_ERROR) {
		raise(STORAGE_ERROR, "Not enough space for new tasks");
		MY_EXCEPTION = 0;
	}
	if (MY_WHAT != NULL_TASK) 		/* MY_WHAT is leader of RTS */
		TCB_BROTHER(MY_WHAT) = FAS(MY_TASKS_DECLARED, MY_WHAT);
	PUSH(MY_WHAT); /* Must add item to chain of rts items */
}

/*-----------------------------------------------------------------------*/
/*                            CREATE  TASK                               */
/*  Procedure to create task and put it on parents frame chain           */
/*-----------------------------------------------------------------------*/

static void create_task(int templ_base, int templ_off, struct rts_item *rts,
  int my_id)													/*;create_task*/
{
	int     task_nr, parent;	/* nr of the task to be created */
	int     i, *p, old_last_task;	/* temporary variable */

	/* STEP 1: Search the stack_segments for a stack */

	old_last_task = last_task;
	task_nr = INC(last_task);
	parent = RTS_PARENT(rts);
	for(;task_nr < old_last_task + MAX_TASKS; task_nr = INC(last_task))
		if (ORIG(task_nr) == NULL_TASK) break;
	if (task_nr >= old_last_task + MAX_TASKS) {/* Error if no avail stack */
		FAS(&(TCB_EXCEPTION(parent)),PROGRAM_ERROR);
		multisignal(parent, NO_EVENT);
		return;
	}

	/* STEP 2: Create task frame for new task */

	p=STACK(task_nr) = (int *) malloc((unsigned) sizeof(int)*new_task_size);
	ORIG(task_nr) = task_nr;

	/* STEP 3 : Create storage area for task and initialize */
	if (p == (int *)0) {
		RTS_TCBS(rts, my_id) = NULL_TASK;
		DEC(RTS_MULT(rts));
		FAS(&(TCB_EXCEPTION(parent)), STORAGE_ERROR);
		STACKPTR(task_nr) = 0;
		multisignal(parent, NO_EVENT);
	}
	else {
		TCB_ABNORMAL(task_nr) 	  = 0;
		TCB_ACTION(task_nr) 	  = ACTIVATE_SELF;
		TCB_BLOCK_PTR(task_nr) 	  = (int *) 0;
		TCB_BROTHER(task_nr) 	  = NULL_BROTHER;
		TCB_CURR_ENTRY(task_nr)   = NULL;
		TCB_ENTRY_ITEM(task_nr)   = NULL;
		TCB_EVENT(task_nr) 	      = NO_EVENT;
		TCB_EXCEPTION(task_nr)    = 0;
		TCB_FIRST(task_nr)	      = 0;
		TCB_ID(task_nr)	          = my_id;
		TCB_IO_ITEM(task_nr) 	  = NULL;
		TCB_MASTER_BLOCK(task_nr) = 0;
		TCB_MASTER_TASK(task_nr)  = NULL_TASK;
		TCB_NEXT(task_nr) 	      = NULL_TASK;
		TCB_NUM_ITEMS(task_nr) 	  = 0;
		TCB_NUM_DEPS(task_nr) 	  = 0;
		TCB_NUM_ENTRIES(task_nr)  =
	      TASK(ADDR(templ_base,templ_off))->nb_entries;
		TCB_NUM_EVENTS(task_nr)   = 0;
		TCB_NUM_NOTERM(task_nr)   = 0;
		TCB_PARENT(task_nr) 	  = RTS_PARENT(rts);
		TCB_PRIO(task_nr)         = TASK(ADDR(templ_base, templ_off))->priority;
		TCB_RDV(task_nr)  	      = 0;
		TCB_RTS_ITEM(task_nr)     = rts;
		TCB_SAVE_PRIO(task_nr)	  = 0;
		TCB_SERVICED(task_nr) 	  = NULL_TASK;
		TCB_STATUS(task_nr) 	  = ACTIVATING;
		TCB_TBASE(task_nr) 	      = templ_base;
		TCB_TOFF(task_nr) 	      = templ_off + WORDS_TASK;
		TCB_WHAT(task_nr) 	      = 0;
		TCB_WHO(task_nr) 	      = NULL_TASK;

		/* add space for queue headers */

		for (i=1; i<=TASK(ADDR(templ_base,templ_off))->nb_entries; i++)
			einit(TCB_ENTRY(task_nr, i));
		p = (int *)(TCB_ENTRY(task_nr, i));

		*p++ = 0;		/* EXR */
		*p++ = 0;		/* LIN */
		*p++ = 0;		/* SFP */
		*p++ = 0;		/* CS */
		*p++ = 0;		/* IP */
		STACKPTR(task_nr) = p - STACK(task_nr);
		*p++ = 0;		/* BFP */
#ifdef TRACE
		if(tasking_trace)
			printf("task %d creating task %d\n",tp,task_nr);
#endif
		RTS_TCBS(TCB_RTS_ITEM(task_nr), TCB_ID(task_nr)) = task_nr;
		TCB_WHAT(TCB_PARENT(task_nr)) = task_nr;
		multisignal(RTS_PARENT(TCB_RTS_ITEM(task_nr)), NO_EVENT);
	}
}

/*--------------------------------------------------------------------------*
 *                     T A S K    A C T I V A T I O N                       *
 *                                                                          *
 *  The following set of routines perform task activation                   *
 *--------------------------------------------------------------------------*/


/*--------------------------------------------------------------------------*
 *                         START  ACTIVATION                                *
 *  This routines is used by a task to preprocess it's task list in order   *
 *  to find out how many tasks must be activated.  It then adds the items   *
 *  in the tasks list to the ready queue in order that they may then be     *
 *  activated in parallel.  When they are done being activated, the parent  *
 *  task may continue processing.                                           *
 *--------------------------------------------------------------------------*/

void start_activation(int task_list, int task_master, int task_block)
														/*;start_activation*/
{
	int	i, task, next_task, num_tasks;
	struct rts_item	*item;

	if (MY_ABNORMAL) {
		uncreate_tasks(task_list);
		abortme();
		return;
	}

	task = task_list;
	num_tasks = 0;
	while (task != NULL_TASK) {
		num_tasks += RTS_MULT(TCB_RTS_ITEM(task));
		task = TCB_BROTHER(task);
	}
	MY_NUM_ITEMS = num_tasks;
	MY_EVENT = NO_EVENT;

	if (TCB_ABNORMAL(task_master)) return;

	MY_STATUS = ACTIVATING;
	task = task_list;
	for (i=0;i<num_tasks;i++) {
		next_task = TCB_BROTHER(task);
		item = TCB_RTS_ITEM(task);
		RTS_MASTER_TASK(item) = task_master;
		RTS_MASTER_BLOCK(item) = task_block;
		RTS_PRIO(item) = MY_PRIO;
		RTS_TYPE(item) = ACTIVATE;
		RTS_NEXT(item) = NULL;
		enqueue_item(MY_PRIO, item);
		task = next_task;
	}
	schedule(DONE_ACTIVATION);
}

/*--------------------------------------------------------------------------*/
/*                         DONE   ACTIVATION                                */
/*  This routines is called by the parent task when all of its tasks have   */
/*  finished their activation.  It checks that it is ok, if not it aborts   */
/*  all of the children.                                                    */
/*--------------------------------------------------------------------------*/

static void done_activation() 							/*;done_activation*/
{
	if (MY_ABNORMAL) {
		abortme();
		return;
	}
	if (MY_EVENT == TASKERR_EVENT) {
		raise(TASKING_ERROR, "Tasking error in activation");
		MY_EXCEPTION = 0;
	}
	else if (MY_EVENT == PROGERR_EVENT) {
		raise(PROGRAM_ERROR, "Activating an unelaborated task");
		MY_EXCEPTION = 0;
	}
	MY_ACTION = NO_ACTION;
}

int union_tasks_declared(int list1, int list2)		/*;union_tasks_declared */
{
	int	head2, tail1;

	if (list1 == NULL_TASK) return list2;
	if (list2 == NULL_TASK) return list1;

	tail1 = list1;
	while (TCB_BROTHER(tail1) != NULL_TASK) tail1 = TCB_BROTHER(tail1);

	head2 = FAS(&(list2), list1);
	FAS(&(TCB_BROTHER(tail1)), head2);
	return list1;
}

/*------------------------------------------------------------------------*/
/* 			     TASK  ACTIVATION                                         */
/* Procedure to activate self and put on the bf_subtasks chain if leader  */
/*------------------------------------------------------------------------*/

static void activate_self(int task_master, int task_bfp) 	/*;activate_self*/
{
	int    *ptr;				  /* memory address */
	int     i, val1, val2, tmp_base, tmp_off; /* temporary base */

	if (MY_BROTHER != NULL_BROTHER) 	/* I am leader of RTS */
		MY_BROTHER =
		  FAS(&(((struct bf *)(STACK(task_master)+task_bfp))->bf_subtasks), tp);

	if (MY_STATUS == TERMINATED || MY_ABNORMAL) { /* may have been aborted */
		MY_STATUS = TERMINATED;
		multisignal(MY_PARENT, NO_EVENT);
		schedule(NO_ACTION);
		return;
	}

	MY_MASTER_TASK = task_master;
	MY_MASTER_BLOCK= task_bfp;
	MY_NUM_NOTERM = 1; 		/* myself */
	MY_NUM_DEPS = 1; 		/* myself */

	ptr = ADDR(MY_TBASE, MY_TOFF-WORDS_TASK);
	tmp_base = TASK(ptr)->body_base;
	tmp_off = TASK(ptr)->body_off;
	ptr = ADDR(tmp_base, tmp_off);
	cs = *ptr;
	if (cs < 1) {	/* Not elaborated !! TBSL */
		TCB_EXCEPTION(MY_PARENT) = PROGRAM_ERROR;
		multisignal(MY_PARENT, PROGERR_EVENT);
		schedule(NO_ACTION);
		return;
	}
	ip = TASK_CODE_OFFSET;

	/* reserve space for local variables */
	/* note: this could be somehow optimized by just moving */
	/*   the Top of Stack.... */

#ifdef ALIGN_WORD
	val1 = get_int((int *)(code_segments[cs] + code_seglen[cs] - sizeof(int)
	  -1));
#else
	val1 = *(int *)(code_segments[cs] + code_seglen[cs] - sizeof(int) - 1);
#endif
	for (i = 0; i < val1; i++)
		PUSH(0);

	i = cur_stackptr + NB_REGISTERS - 1;
	PUSH(i);        /* SFP -- this is a trap */
	PUSH(cs);		/* CS */
	PUSH(lin);      /* LIN*/
	PUSH(ip);		/* IP */
	sfp = cur_stackptr + 1;
	/* copy relay set */

	val2 = *++ptr * 2;	/* length */
	for (i = 0; i < val2; i++)
		PUSH(*++ptr);

	/* Dummy block frame for trapping exceptions */
	PUSH(0);		/* bfp */
	bfp = cur_stackptr;
	PUSHP(0L);		/* data_link */
	PUSHP(0L);		/* tasks_declared */
	PUSH(1);		/* num_noterm */
	PUSH(1);		/* num_deps */
	PUSH(NULL_TASK);/* subtasks */
	PUSH(2);		/* exception vector */
	cur_code = code_segments[cs];

	/* This must occur after possible to detect all errors */

	INC(TCB_NUM_NOTERM(MY_MASTER_TASK));
	INC(TCB_NUM_DEPS(MY_MASTER_TASK));
	INC(BF_NUM_NOTERM(MY_MASTER_TASK, MY_MASTER_BLOCK));
	INC(BF_NUM_DEPS(MY_MASTER_TASK, MY_MASTER_BLOCK));

#ifdef TRACE
	if (tasking_trace) {
		printf("task %d activating task %d\n",task_master,tp);
	}
#endif
}


/*-------------------------------------------------------------------------*/
/*                            END  ACTIVATION                              */
/* Procedure called at the end of activation to signal the parent task     */
/* that everything is OK (or not as the case may be)                       */
/*-------------------------------------------------------------------------*/

void end_activation(int term_code) 				/*;end_activation*/
{
	/* after we passed the end of activation, the exception vector */
	/* of the very first block shall designate the task_trap. */

	BF_HANDLER(tp, MY_PREVIOUS_BFP) = 2;
	if (term_code == 0) {
		TCB_EXCEPTION(MY_PARENT) = TASKING_ERROR;
		DEC(RTS_MULT(MY_RTS_ITEM));
		RTS_TCBS(MY_RTS_ITEM, MY_ID) = NULL_TASK;
		multisignal(MY_PARENT, TASKERR_EVENT);
	}
	else {
		MY_STATUS = ACTIVE;
		multisignal(MY_PARENT, NO_EVENT);
	}
}

/*--------------------------------------------------------------------------*/
/*                  A B O R T    R O U T I N E S                            */
/*--------------------------------------------------------------------------*/

/*--------------------------------------------------------------------------*/
/*                                 ABORT                                    */
/* Procedure used to abort nr_task tasks whose numbers are on the stack     */
/*--------------------------------------------------------------------------*/

void abort(int nr_tasks)						                 /*;abort*/
{
	int     current;	/* pointer to the task currently aborting */
	int     i;		/* temporary loop index */

	for (i = 0; i < nr_tasks; i++) {
		POP(current);
		kill(current);
	}
	if (MY_ABNORMAL)   /* Suicide! */
		abortme();
}

/*--------------------------------------------------------------------------*/
/*   			        KILL		                                        */
/* Procedure to abort task, after having aborted its dependent tasks. If    */
/* nobody in the family is engaged in a rendezvous, then the task is made   */
/* terminated and space of dependent tasks is released. This procedure does */
/* not call WAIT: this has to be done by the caller if it aborts itself.    */
/*--------------------------------------------------------------------------*/

static void kill(int task)											/*;kill*/
{
	int  	task2, dep, i, j, block;

	/* STEP 1: Check status etc. of task being aborted ...  */

	if (INC(TCB_ABNORMAL(task)) || (TCB_STATUS(task) == TERMINATED)) {
		/* more than one task trying to abort it, must clean up ... */
#ifdef TRACE
		if (tasking_trace)
			printf("task %d aborting terminated task %d\n",tp,task);
#endif
		DEC(TCB_ABNORMAL(task));		/* avoid overflow */
		return;
	}

#ifdef TRACE
	if (tasking_trace && TCB_ABNORMAL(task))
		printf("task %d aborting task %d\n",tp,task);
#endif

	/* STEP 2:  Kill all dependent tasks by block
	 *	    I can spawn tasks and use a multi-wait count here to make sure done
	 */
	if (TCB_BLOCK_PTR(task) == NULL) block = 0;  /* no yet activated ... */
	else block = *(TCB_BLOCK_PTR(task));
	while (block != 0) {
		task2 = BF_SUBTASKS(task, block);
		while (task2 != NULL_TASK) {
			i = 0; 
			j = 0;
			while (i < RTS_MULT(TCB_RTS_ITEM(task2)))
				if ((dep=RTS_TCBS(TCB_RTS_ITEM(task2),j++)) != NULL_TASK) {
					i++;
					kill(dep);
				}
			task2 = TCB_BROTHER(task2);
		}
		block = BF_PREVIOUS_BFP(task, block);
	}
	/* STEP 3: Perform cleanup. Try to disable task if it waiting, if
	 *    successful then must signal.  Otherwise it will discover itself
	 *    when awakens or when it reaches a synchronization point (when it
	 *    is 'active' but paused by the round-robin scheduling scheme).
	 */
	switch (TCB_STATUS(task)) {
	case COMPLETED      :
	case ACTIVATING     :
	case ACTIVE         :
	case COMPLETE_BLOCK :
		break;
	case SELECTING_TERM:
	case SELECTING_NOTERM:
		if (FAS(&(TCB_RDV(task)),0) == 1)
			make_ready(task, ABORT_EVENT);            
		break;
	case TIMED_RDV:
	case CALLING_RDV:
		if (eremove(task)) make_ready(task, ABORT_EVENT); 
		break;
	case WAIT:
		if (remove_io(&(TCB_IO_ITEM(task))))
			make_ready(task, ABORT_EVENT);            
		break;
	default: 
		raise(SYSTEM_ERROR, "Aborting task in unknown state");
		break;
	} /* status TERMINATED & ABNORMAL already tested in kill.
	   * QUIESCENT depends on ABNORMAL (Cf post_selective_wait & abortme)
	   * COMPLETE_BLOCK and ACTIVE have been added (Cf round-robin)
	   */

}

/*--------------------------------------------------------------------------*/
/*   			        ABORTME                                             */
/* Task has discovered it was aborted. kids in select term have been sig-   */
/* nalled.  Completed kids will be notified when their kids are through.    */
/* My terminated kids are already done.                                     */
/*--------------------------------------------------------------------------*/

static void abortme()							/*;abortme */
{
	purge_rdv(tp);
	if ((MY_STATUS != QUIESCENT) && (DEC(MY_NUM_NOTERM) != 1)) {
		MY_STATUS = COMPLETED;
		schedule(ABORT_ONE);
	}
	else post_abort_one();
}

static void post_abort_one()								/*;post_abort_one*/
{
	if (MY_STATUS != QUIESCENT)
		check_termination(MY_MASTER_TASK, MY_MASTER_BLOCK);
	task_term();	/* not strictly needed for abort, just "term-wave" */
}

/*--------------------------------------------------------------------------*/
/*                           T E R M I N A T I O N                          */
/*                                                                          */
/*  The following set of routines maintain the counters and data structures */
/*  used to perform task temination.  They are divided into two sets: those */
/*  used in the termination of blocks and subprograms and those used in the */
/*  termination of tasks.                                                   */
/*--------------------------------------------------------------------------*/


/*--------------------------------------------------------------------------*/
/*                          COMPLETE  TASK                                  */
/*  This is the last instruction in a task's instruction stream             */
/*--------------------------------------------------------------------------*/

void complete_task()										/*;complete_task*/
{
	MY_STATUS = COMPLETED;
	if (DEC(MY_NUM_NOTERM) != 1) schedule(COMPLETE_TASK_ONE);
	else post_complete_task_one();
}

static void post_complete_task_one()				/*;post_complete_task_one*/
{
	check_termination(MY_MASTER_TASK, MY_MASTER_BLOCK);
	if (INC(MY_ABNORMAL) == 0)
		task_term();
	else if (DEC(MY_NUM_DEPS) != 1) schedule(FREE_TASK_SPACE);
	else free_task_space();
}

/*--------------------------------------------------------------------------*/
/*                              COMPLETE  BLOCK                             */
/*--------------------------------------------------------------------------*/

void complete_block()										/*;complete_block*/
{
	MY_STATUS = COMPLETE_BLOCK;
	if (DEC(MY_BF_NUM_NOTERM) != 1)
		schedule(COMPLETE_BLOCK_ONE);
	else post_complete_block();
}

static void post_complete_block()						/*;post_complete_block*/
{
	if (MY_ABNORMAL == 0)
		tell_termination(*MY_BLOCK_PTR);
	if (DEC(MY_BF_NUM_DEPS) != 1)	schedule(COMPLETE_BLOCK_TWO);
	else post_complete_block_two();
}

static void post_complete_block_two()			/*;post_complete_block_two*/
{
	MY_STATUS = ACTIVE;
}

/*--------------------------------------------------------------------------*/
/*                     TERMINATION  SUPPORT  ROUTINES                       */
/*--------------------------------------------------------------------------*/

static void task_term()											/*;task_term*/
{
	int block;

	if (DEC(MY_NUM_DEPS) != 1) {
		block = *MY_BLOCK_PTR;
		while (block != 0) {
			tell_termination(block);
			block = BF_PREVIOUS_BFP(tp, block);
		}
		schedule(FREE_TASK_SPACE);
	}
	else free_task_space();
}

static void free_task_space()							/*;free_task_space */
{
	int	block;

	block = *MY_BLOCK_PTR;
	while (block != 0) {
		uncreate_tasks(BF_SUBTASKS(tp, block));
		block = BF_PREVIOUS_BFP(tp, block);
	}
	MY_STATUS = TERMINATED;
	check_done(MY_MASTER_TASK, MY_MASTER_BLOCK);
	schedule(NO_ACTION);
}

/* Recursive procedure to check master tasks and blocks called by quiescent */
/* dependent of "task" and "block" 					    */

static void check_termination(int task, int block)		/*;check_termination */
{
	if ((task != NULL_TASK) && (task != 0) && (DEC(TCB_NUM_NOTERM(task)) == 1))
		if ((TCB_STATUS(task) == COMPLETED) && (INC(TCB_FIRST(task)) == 0)) {
			if (TCB_NUM_NOTERM(task) == 0)
				make_ready(task, TERMINATE_EVENT);
		}
		else
			check_termination(TCB_MASTER_TASK(task),TCB_MASTER_BLOCK(task));

	if ((block != 0) && (DEC(BF_NUM_NOTERM(task, block)) == 1))
		make_ready(task, TERMINATE_EVENT);
}

static void check_done(int task, int block)						/*;check_done*/
{
	int	dd;
	dd = DEC(TCB_NUM_DEPS(task));
	if ((DEC(BF_NUM_DEPS(task, block)) == 1) || (dd == 1))
		make_ready(task, NO_EVENT);
}

static void check_unterm()									/*;check_unterm*/
{
	if (INC(MY_NUM_NOTERM) == 0) {
		INC(TCB_NUM_NOTERM(MY_MASTER_TASK));
		INC(BF_NUM_NOTERM(MY_MASTER_TASK, MY_MASTER_BLOCK));
	}
}

static void tell_termination(int block)					/*;tell_termination*/
{
	int i, j, dep, task;

	task = BF_SUBTASKS(tp, block);
	while (task != NULL_TASK) {
		i = 0; 
		j = 0;
		while (i < RTS_MULT(TCB_RTS_ITEM(task)))
			if ((dep=RTS_TCBS(TCB_RTS_ITEM(task),j++)) != NULL_TASK) {
				i++;
				if ((TCB_STATUS(dep) != TERMINATED)
				  && (INC(TCB_ABNORMAL(dep)) == 0))
					make_ready(dep, TERMINATE_EVENT);
			}
		task = TCB_BROTHER(task);
	}
}

/* Procedure used when an exception is raised to terminate tasks that have
 * created, but not yet activated.(LRM 9.3(4)) Such tasks may have pending
 * rendezvous. All tasks linked to task frames depending on the current BFP
 * are made terminated. They are linked together and put on bf_subtasks in
 * order to release their space when the block is exited.
 */

void terminate_unactivated() 					/*;terminate_unactivated */
{
	int     current, next, removed, dep, i, j;
	int    *task_frame;

	task_frame = MY_TASKS_DECLARED;
	if (task_frame != (int *)0) {
		removed = NULL_TASK;
		*(task_frame - WORDS_PTR - 1) = -(*(task_frame - WORDS_PTR - 1));
		for (;;) {
			current = *task_frame;
			if (current != NULL_TASK) {
				for (;;) {
					i = 0; 
					j = 0;
					while (i < RTS_MULT(TCB_RTS_ITEM(current)))
						if ((dep=RTS_TCBS(TCB_RTS_ITEM(current),j++))
						  != NULL_TASK) {
							i++;
							TCB_STATUS(dep) = TERMINATED;
							purge_rdv(dep);
						}
					next = TCB_BROTHER(current);
					if (next == NULL_TASK)
						break;
					current = next;
				}

				/* we are still in the context of the last task on the chain
				 * merge the chain with previous one
				 */

				TCB_BROTHER(current) = removed;
				removed = *task_frame;/* head of the chain */
			}
			task_frame = *((int **)(task_frame - WORDS_PTR));
			if (task_frame == (int *)0)
				break;
		}

		if (removed != NULL_TASK)  /* merge on bf_subtasks to release space */
			MY_SUBTASKS = union_tasks_declared(removed, MY_SUBTASKS);
		MY_TASKS_DECLARED = (int *)0;
	}
}

/* Procedure to raise TASKING_ERROR in all tasks waiting for or engaged   */
/* in a rendezvous with the currently active task                         */

void purge_rdv(int curr)										/*;purge_rdv */
{
	int     task, i;

	for (i = 1; i <= TCB_NUM_ENTRIES(curr); i++)
		while (ENTRY_COUNT(TCB_ENTRY(curr,i)) > 0) {
			DEC(ENTRY_COUNT(TCB_ENTRY(curr,i)));
			if ((task = eget(TCB_ENTRY(curr,i))) != NULL_TASK) {
				TCB_EXCEPTION(task) = TASKING_ERROR;
				make_ready(task, TASKERR_EVENT);
			}
		}

	task = TCB_SERVICED(curr);
	while (task != NULL_TASK) {
		TCB_EXCEPTION(task) = TASKING_ERROR;
		make_ready(task, TASKERR_EVENT);
		task = TCB_NEXT(task);
	}
}

static void uncreate_tasks(int task_list)				/*;uncreate_tasks */
{
	int		task, next, i, j;
	struct rts_item	*item;

	task = task_list;
	while (task > 0) {
		next = TCB_BROTHER(task);
		item = TCB_RTS_ITEM(task);
		i = 0; 
		j = 0;
		while (i < RTS_MULT(item))
			if ((task = RTS_TCBS(item,j++)) != NULL_TASK) {
				i++;
				efree((char *) STACK(task));
				STACK(task) = (int *) 0;
				ORIG(task) = NULL_TASK;
			}
		task = next;
	}
}

/*--------------------------------------------------------------------------*/
/*                  T I M E   M A N A G E M E N T                           */
/*                                                                          */
/*  	The following set of routines perform time management for "delay"   */
/*  statements.   The chain of waiting tasks associated with each PE        */
/*  is sorted in ascending time of end of delay.  The time associated       */
/*  with each entry in the chain in the amount of time it must wait after   */
/*  the previous entry is done (e.g.  the wait time is kept incrementally)  */
/*  A global variable "next_clock" keeps the absolute time value of the next*/
/*  interrupt.  When the interrupt processing routine is called all interupt*/
/*  which are now ready -or- were previously ready are made ready.          */
/*	Io_items are freed by either the owning task or the interrupt       */
/*  process.  If the io_item has been disabled, it is freed by the catcher  */
/*  routine.  Otherwise it is freed by the process when it awakens from     */
/*  make ready.                                                             */
/*--------------------------------------------------------------------------*/


static void my_set_timer(struct io_item_type *item, long now) /*;my_set_timer*/
{
	next_clock = II_DELTA(item) + now;
}

static int long my_reset_timer(long now)				/*;my_reset_timer*/
{
	last_time = now;
	return(next_clock - now);
}

/*--------------------------------------------------------------------------*/
/*                              DELAY_STMT                                  */
/*  Guarantees that all wait times are positive (provided for compatability)*/
/*  Note that it recognizes three types of delays:                          */
/*      0       - signifies simply a request to context switch              */
/*      ENDLESS - signifies simply relinquishing the CPU                    */
/*      other   - actual create a timer chain element and chain it          */
/*--------------------------------------------------------------------------*/

void delay_stmt(long delay_time)								/*;delay_stmt*/
{
	long effective_delay;

	effective_delay = delay_time >= 0 ? delay_time : 0;
#ifdef TRACE
	if (rendezvous_trace) {
		printf("task %d delaying %ld effective delay %ld \n", tp,
		  delay_time, effective_delay);
	}
#endif
	if (effective_delay == (long) ENDLESS)
		schedule(NO_ACTION);
	else if (effective_delay == 0)
		context_switch();
	else
		wait(effective_delay, WAIT);
}

/*--------------------------------------------------------------------------*/
/*                                 WAIT                                     */
/*  Routines which makes the task wait for the delay time                   */
/*--------------------------------------------------------------------------*/

static void wait(long delay, int action) 							/*;wait*/
{
	MY_STATUS = WAIT;
	if (MY_ABNORMAL && MY_STATUS != TERMINATED) { 
		abortme(); 
		return; 
	}
	MY_IO_ITEM = chain(tp, delay);
	schedule(action);
}

static void post_wait()											/*;post_wait*/
{
	MY_STATUS = ACTIVE;
	if (MY_ABNORMAL) 
		abortme(); 
}

/*--------------------------------------------------------------------------*/
/*                              CATCHER                                     */
/* Routine called when a timer interrupt occurs.                           */
/*--------------------------------------------------------------------------*/

void clock_interrupt(long now_time) 					/*;clock_interrupt*/
{
	catcher(now_time);
	context_switch();
}

static void catcher(long now_time) 								/*;catcher*/
{
	struct io_item_type	*item;
	long			time;

	/* Time Out head of io_item list and all others following with delta 0 */
	time = now_time - last_time;
	last_time = now_time;

	while ((clock_head != NULL) && (II_DELTA(clock_head)<=time)) {
		item = II_NEXT(clock_head);  /* TO others waiting in interval */
		time -= II_DELTA(clock_head);
		check_free(clock_head);
		clock_head = item;
	}

	/* remove interior deletes from head of list */

	item = clock_head;
	while ((clock_head != NULL) && (II_FLAG(clock_head) == 0)) {
		time -= II_DELTA(clock_head);
		item = II_NEXT(clock_head);
		efree((char *) clock_head);
		clock_head = item;
	}
	if (clock_head != NULL) {
		II_DELTA(clock_head) -= time;
		my_set_timer(clock_head, now_time);
	}
	else next_clock_flag = FALSE;
}

/*--------------------------------------------------------------------------*/
/*                                CHAIN                                     */
/*  Called when execute a delay.  Add task to timeout chain                 */
/*--------------------------------------------------------------------------*/

static struct io_item_type *chain(int task, long delay) 		/*;chain*/
{
	long	my_reset_time(), itime();
	long	now;
	struct io_item_type *new_item, *item, *prev_item;

	now = itime() + time_offset;
	if (TCB_IO_ITEM(task) == NULL) {
		new_item=(struct io_item_type *)malloc(sizeof(struct io_item_type));
		if (new_item == (struct io_item_type *)0) {
			raise(STORAGE_ERROR, "Allocating space for timer chain");
			return(NULL);
		}
	}
	else new_item = TCB_IO_ITEM(task);
	if (clock_head == NULL) {
		clock_head = new_item;
		II_TASK(new_item) = task;
		II_FLAG(new_item) = TCB_STATUS(task);
		II_NEXT(new_item) = NULL;
		II_DELTA(new_item) = delay;
	}
	else {
		II_DELTA(clock_head) = my_reset_timer(now); /* time in intval*/
		II_TASK(new_item) = task;
		II_FLAG(new_item) = TCB_STATUS(task);

		/* seq. search for new_item's position based on relative deltas */
		if (delay <= II_DELTA(clock_head)) {
			II_NEXT(new_item) = clock_head;
			II_DELTA(new_item) = delay;
			II_DELTA(clock_head) -= delay;
			clock_head = new_item;
		}
		else {
			item = clock_head;
			prev_item = clock_head;
			while ((item != NULL) && (delay-II_DELTA(item) > 0)) {
				delay -= II_DELTA(item);
				prev_item = item;
				item = II_NEXT(item);
			}
			II_NEXT(new_item) = item;
			II_NEXT(prev_item) = new_item;
			II_DELTA(new_item) = delay;
			if (item != NULL)
				II_DELTA(item) -= delay;
		}
	}
	next_clock_flag = TRUE;
	my_set_timer(clock_head, now);
	return(new_item);
}

/*--------------------------------------------------------------------------*/
/*                              CHECK  FREE                                 */
/* Called by catcher to see if timeout is possible                          */
/*--------------------------------------------------------------------------*/

static void check_free(struct io_item_type *item)				/*;check_free*/
{
	int	value;

	value = get_io(item);
	if (value > 0)     /* anything else being waited for has been disble */
		make_ready(II_TASK(item), TIMER_EVENT);

	/*  Originally we were going to deallocate the io_item.  This was later
	 *  changed EXCEPT in the case where it was already disabled ...
	 */
	else if (value == -1)
		efree((char *) item);
}

/*--------------------------------------------------------------------------*/
/*                                GET  IO                                   */
/*--------------------------------------------------------------------------*/

static int get_io(struct io_item_type *item)						/*;get_io*/
{
	int	wake;

	switch (FAS(&(II_FLAG(item)),TIMER_EVENT)){  /* was task's status */
	case DISABLED_EVENT:  
		wake = -1; 
		break;      /* already gone */
	case TIMED_RDV :      
		wake = eremove(II_TASK(item));
		FAS(&(II_FLAG(item)), 0);        
		break;
	case SELECTING_NOTERM:  			   /* disable */
	case SELECTING_TERM:  
		wake = FAS(&(TCB_RDV(II_TASK(item))),0);
		FAS(&(II_FLAG(item)), 0);        
		break;
	case WAIT :           
		wake = 1; 
		break;        /* must wake up */
	case 0    :           
		wake = -1; 
		break;       /* innner remove*/
	default :             
		raise(SYSTEM_ERROR, "Unexpected event");
		break;
	}
	II_FLAG(item) = 0;
	return wake;
}


/*--------------------------------------------------------------------------*/
/*                             DISABLE IO                                   */
/* Called when rdv ti disable timeouts.  No timeouts possible, but avoids   */
/* race (that item.flag may be gotten, rendezvous, then RDV reset for next  */
/* rendezvous).                                                             */
/*--------------------------------------------------------------------------*/

static void disable_io(struct io_item_type **item_ptr)			/*;disable_io*/
{
	struct io_item_type	*item;

	item = *item_ptr;
	if (item != (struct io_item_type*)0) {
		if (FAS(&(II_FLAG(item)),DISABLED_EVENT) == TIMER_EVENT) {
			/* Timeout in progress, wait for it to end then delete */
			while (II_FLAG(item) != 0) continue;
			efree((char *) item);
		}
		*item_ptr =(struct io_item_type *)0 ;
	}
}

/*--------------------------------------------------------------------------*/
/*                             REMOVE  IO                                   */
/* Called when abort in delay                                               */
/*--------------------------------------------------------------------------*/

static int remove_io(struct io_item_type **item_ptr)			/*;remove_io */
{
	struct io_item_type	*item;

	item = *item_ptr;
	if (item != (struct io_item_type *)0)
		if (FAS(&(II_FLAG(item)),DISABLED_EVENT) == TIMER_EVENT) {
			efree((char *) item);  /* too late, has timed out ... */
			*item_ptr = (struct io_item_type *)0;
			return 0;
		}
	return 1;
}

/*--------------------------------------------------------------------------*
 *                           S C H E D U L E R                              *
 *                                                                          *
 *    The following set of routines perform decentralized scheduling based  *
 *  on two different schemes: "run-until-blocked" or "round-robin". Because *
 *  the interpreter simply simulates tasks, it is absolutely necessary that *
 *  once "schedule" is call and control is  passed to a new virtual task,   *
 *  that the interpretor return to the highest level without executing any  *
 *  other code (excepting the cleanup routines  called in "schedule").      *
 *    Thus any statement which (recursively) executes "schedule" must be    *
 *  immediately succeeded by a return statement.  The "dangerous" routines  *
 *  in the system are:                                                      *
 *                                                                          *
 *	- activate_self		- abort			- abortme           *
 *	- complete_task		- complete_task_one	- task_term         *
 *	- complete_block	- post_complete_block			    *
 *	- wait			- post_wait		- delay_stmt        *
 *	- entry_call		- post_entry_call	- end_rendezvous    *
 *	- selective_wait	- post_selective_wait		            *
 *--------------------------------------------------------------------------*/

/*--------------------------------------------------------------------------*
 *                             SCHEDULE                                     *
 * Block the currently executing task and select a new task to run.         *
 *--------------------------------------------------------------------------*/

static void schedule(int action)								/*;schedule*/
{
	int 	done, p, i;
	struct rts_item	*item;

	MY_ACTION = action;
	if (DEC(MY_NUM_EVENTS) > 0) {
		finish_action(MY_RTS_ITEM);  /* an event is waiting */
		return;
	}
	if (action == CONTEXT_SWITCH) INC(MY_NUM_EVENTS);
	done = FALSE;
	while (!done) {
		for (p=MAX_PRIO-1;p>=0;p--) {
			item = dequeue(ready_queue[p], &i);
			if (item != (struct rts_item *)0) {
				switch(RTS_TYPE(item)) {
				case ACTIVATE :
				case READY :
#ifdef TRACE
					if (context_sw_trace && (action != DONE_CREATION)) {
					/* Don't print internal CS during creation */
					/* i.e. task x switching to itself. */
						printf("task %d switching to task %d \n",
							tp,item->tcbs[i]);
					}
#endif
					highest_priority = p;
					transfer(item->tcbs[i]);
					done = TRUE;
					break;
				case CREATE :
					create_task(RTS_TEMPL_BASE(item),
					    RTS_TEMPL_OFF(item),item,i);
					break;
				default :
					raise(SYSTEM_ERROR, "Unexpected type");
					break;
				}
				break;   /* out of for loop */
			}
			else if (p == 0) done = TRUE;  /* end loop (error) */
		}
	}

	if (item == (struct rts_item *)0)
	{ /* No active task was found, error condition */
		MY_STATUS = ACTIVE;
		raise(SYSTEM_ERROR, "No activatable task");
		MY_EXCEPTION = 0;
		return;
	}
	finish_action(item);
}

/* Now the new task is processing.  It must perform the appropriate   */
/* cleanup routine based on the action which it was performing before */
/* making the call to the scheduler ...				      */

static void finish_action(struct rts_item *item)			/*;finish_action*/
{
	int	open_en[MAX_ALTS], accept_index[MAX_ALTS];
	long 	sleep_time;
	long	itime();

	switch (MY_ACTION) {
	case WAIT 		: 
		post_wait(); 			
		break;
	case SELECTIVE_WAIT 	: 
		post_selective_wait(0, 0, open_en, accept_index); 		
		break;
	case ENTRY_CALL 	: 
		post_entry_call(); 		
		break;
	case COMPLETE_BLOCK_ONE	: 
		post_complete_block(); 	
		break;
	case COMPLETE_BLOCK_TWO : 
		post_complete_block_two(); 
		break;
	case ABORT_ONE		: 
		post_abort_one(); 		
		break;
	case COMPLETE_TASK_ONE	: 
		post_complete_task_one();	
		break;
	case FREE_TASK_SPACE 	: 
		free_task_space();	
		break;
	case DONE_ACTIVATION    : 
		done_activation();		
		break;
	case DONE_CREATION   	: 
		done_creation();		
		break;
	case ACTIVATE_SELF      : 
		activate_self(RTS_MASTER_TASK(item), RTS_MASTER_BLOCK(item)); 
		break;
	case CONTEXT_SWITCH	:
	case NO_ACTION   	: 				
		break;
	default : 
		raise(SYSTEM_ERROR, "Tasks awakened in an unknown state");
		MY_EXCEPTION = 0; 				
		break;
	}

	/* then see if someone else waiting to be scheduled */

	if (tp == 0) {		/* we schedule IDLE */
		if (next_clock_flag) {		   /* exists task waiting? */
			if (simul_time_flag) 		/* speed up time! */
				time_offset += next_clock - itime();
			else if ((sleep_time=(next_clock-itime())/1000L) > 1L)
				sleep((unsigned)sleep_time);
		}
		else if ((MY_ACTION != DONE_CREATION) && (MY_ACTION != DONE_ACTIVATION))
			raise(PROGRAM_ERROR, "System inactive(deadlock)");
	}
	MY_ACTION = NO_ACTION;
}

/*--------------------------------------------------------------------------*/
/*                              MAKE READY                                  */
/* Moves the specified task to the ready queue setting it's event flag.     */
/*--------------------------------------------------------------------------*/

static void make_ready(int task, int event)					/*;make_ready*/
{
	if (event != NO_EVENT) /* Mulitple events may overwrite (COMP,TERM,ABORT) */
		TCB_EVENT(task)=event;  /* but task can tell if correct one happened */

	if (INC(TCB_NUM_EVENTS(task)) == -1) enqueue(TCB_PRIO(task), task);
}

/*--------------------------------------------------------------------------*/
/*                              ROUND ROBIN                                 */
/*                                                                          */
/* Procedure called when the round-robin scheme is invoked. First, detect   */
/* (asynchronously !) if there is a ready task of higher or same priority   */
/* than the task blocked. If yes, perform the context_switch.               */
/* WARNING: the task blocked by the round-robin scheme has still the        */
/*          status ACTIVE !!!                                               */
/*                                                                          */
/*--------------------------------------------------------------------------*/

void round_robin()							/*;round_robin*/
{
	int p, found;

	/* is it worth doing a context-switch ? */
	/* --> test if there is one ready task of higher or same priority */
	/* warning: asynch test (Cf dequeue with DEC & INC)   */

	found = FALSE;
	for (p=MAX_PRIO-1; p>=MY_PRIO; p--)
		if (ready_queue[p]->count >= 1)
			found = TRUE;
	if (found)
		context_switch();
}

/*---------------------------------------------------------------------------*/
/*                              TRANSFER                                     */
/*  Transfers control from the currently executing task to the one specified */
/*---------------------------------------------------------------------------*/

static void transfer(int new_task)              			/*;transfer*/
{
	PUSH(exr);
	PUSH(lin);
	PUSH(sfp);
	PUSH(cs);
	PUSH(ip);
	PUSH(bfp);	/*  ----------MUST be on top of stack----------  */
	MY_BLOCK_PTR = (int *) (cur_stack+cur_stackptr);
	STACKPTR(tp) = cur_stackptr;

	tp = new_task;
	rr_counter = 0;
	cur_stack = STACK(tp);
	cur_stackptr = STACKPTR(tp);
	POP(bfp);
	MY_BLOCK_PTR = &bfp;
	POP(ip);
	POP(cs);
	POP(sfp);
	POP(lin);
	POP(exr);
	cur_code = code_segments[cs];
}

/*--------------------------------------------------------------------------*
 *                           R E N D E Z V O U S                            *
 *                                                                          *
 * The following set of procedures are used to performs rendezvous.  They   *
 * are divided into two sets: those used to perform a "select" call and     *
 * those used to execute an "entry" call.    They make use of the parallel  *
 * queue routines and use the "rdv" flag, the array of "entry" records, the *
 * "io_item" when processing delays as well as checking and setting the     *
 * "status" and "abnormal" fields in the caller and/or owner task's TCB.    *
 * The routines which are called by the interpretor directly are:           *
 * 	- selective_wait                                                    	*
 * 	- end_rendezvous                                                    	*
 * 	- entry_call                                                        	*
 * There calling interface (stack upon entry and return as well as parms.   *
 * passed are identical to the original system.                             *
 *--------------------------------------------------------------------------*/


/*--------------------------------------------------------------------------*
 *                          SELECTIVE WAIT                                  *
 *--------------------------------------------------------------------------*/

void selective_wait(int num_alts)							/*;selective_wait */
{
	int	alt_kind;		/* delay, terminate or accept */
	long	delay_time;		/* value of delay */
	long	min_delay;		/* minimum delay */
	int	family;			/* family index of entry */
	int	member;			/* member of family */
	int	guard;			/* guard of statement (boolean) */
	int	open_ai[MAX_ALTS];	/* list of open accept indices */
	int	open_en[MAX_ALTS];	/* list of open entry numbers  */
	int	num_open_alts;		/* number of open alternatives */
	int	delay_index;		/* index to delay alt. (or -1) */
	int	term_index;		/* index to terminate alt. (or -1) */
	int	accept_index;		/* index to chosen alternative */
	int 	caller;			/* chosen task id of caller */
	struct entry_type *entry;	/* pointer to entry */
	int 	i, temp;


	/*  STEP 1: Build a set of open alternatives and determine the shortest
	 * delay and the index set of the terminate (if any)
	 */

	term_index = -1;
	min_delay = ENDLESS;
	delay_index = -1;

	if (num_alts == 0) {  /* simple accept */
		POP(member);
		POP(family);
		num_open_alts = 1;
		open_ai[0] = 1;
		open_en[0] = entry_number(tp, family, member);
	}
	else num_open_alts = 0;

	for (accept_index = num_alts; accept_index >= 1; accept_index --) {
		POP(alt_kind);
		if (alt_kind == 1) {    /* accept */
			POP(member);
			POP(family);
			POP(guard);
			if (guard == 1) {
				open_ai[num_open_alts] = accept_index;
				open_en[num_open_alts++] = entry_number(tp, family, member);
			}
		}
		else if (alt_kind == 2) {    /* delay */
			POPL(delay_time);
			POP(guard);
			if (guard == 1)
				if (delay_index == -1 || delay_time<min_delay) {
					min_delay = (delay_time>=0L) ? delay_time : 0L;
					delay_index = accept_index;
				}
		}
		else if (alt_kind == 3) {    /* terminate */
			POP(guard);
			if (guard == 1)
				term_index = accept_index;
		}
		else raise(SYSTEM_ERROR,
		    "Unknown alternative in select statement");
	}

	/* STEP 2: Check local status, terminatability, guards, rdv flag etc.  */

	if (MY_ABNORMAL) { 
		abortme(); 
		return; 
	}
	MY_STATUS = SELECTING_NOTERM;

	evaluate_guards(open_en, num_open_alts);

	FAS(&(MY_RDV), 1);	/* an rdv is now possible     */
	if (MY_ABNORMAL && (FAS(&(MY_RDV), 0) == 1)) { 
		abortme(); 
		return; 
	}

	/* STEP 3: See if can start an immediate rendezvous */

	if (num_open_alts > 0) {
		i = 0;
		while (MY_RDV && (i < num_open_alts)) {
			temp = open_ai[i];
			entry = MY_ENTRY(open_en[i++]);
			if (ENTRY_GUARD(entry)) {
				del_lock(&(LOCK(entry)));
				if ((DEC(ENTRY_COUNT(entry)) > 0) && (FAS(&(MY_RDV),0) == 1)) {
					/* a task is waiting and got flag so rdv is possible */
					caller = eget(entry);
					del_unlock(&(LOCK(entry)));
					close_guards(open_en, num_open_alts);
					TCB_SAVE_PRIO(caller) = MY_PRIO;
					MY_PRIO = MAX(TCB_SAVE_PRIO(caller),MY_PRIO);
					accept_rdv(caller,temp,num_alts);
					return;
				}
				else {     /* we did not - disable the rendezvous...  */
					INC(ENTRY_COUNT(entry));
					del_unlock(&(LOCK(entry)));
				}
			}
		}
	}

	/* STEP 4:  Unfortunately, couldn't perform rendezvous.  Now either detect
	 *    an error condition, try to terminate or delay
	 */

	if ((num_open_alts == 0) && (delay_index == -1) && (term_index == -1)){
		raise(PROGRAM_ERROR, "No open alternatives in select");
		return;
	}

	if (MY_RDV == 0) {     /* have been aborted or called, busywait */
		while ((MY_EVENT != RDV_EVENT) && (!MY_ABNORMAL)) continue;
		post_selective_wait(1, num_open_alts, open_en, open_ai);
	}
	else if ((min_delay == 0) && FAS(&(MY_RDV), 0) == 1) {
		MY_EVENT = TIMER_EVENT;
		open_en[num_open_alts] = TIMER_EVENT;
		open_ai[num_open_alts++] = delay_index;
		post_selective_wait(1, num_open_alts, open_en, open_ai);
		return;
	}
	else {
		if (num_alts != 0)	/* push open entry table on stack */
			for (i=0;i<num_open_alts;i++) {
				PUSH(open_en[i]);
				PUSH(open_ai[i]);
			}
		if (delay_index != -1) {
			PUSH(TIMER_EVENT);
			PUSH(delay_index);
			num_open_alts++;
		}
		if (term_index != -1) {
			PUSH(TERMINATE_EVENT);
			PUSH(term_index);
			MY_STATUS = SELECTING_TERM;
			if (DEC(MY_NUM_NOTERM) == 1)      /* am quiescent */
				check_termination(MY_MASTER_TASK, MY_MASTER_BLOCK);
			num_open_alts++;
		}
		if (num_alts == 0)     /* simple accept */
			PUSH(0); 
		else  
			PUSH(num_open_alts); 

#ifdef TRACE
		if (rendezvous_trace)
			printf("task %d waiting for a rendezvous \n", tp);
#endif
		if (min_delay == ENDLESS) schedule(SELECTIVE_WAIT);
		else wait(min_delay, SELECTIVE_WAIT);
	}
}


/*--------------------------------------------------------------------------*/
/*                              EVALUATE GUARDS                             */
/*--------------------------------------------------------------------------*/

static void evaluate_guards(int open_en[], int num_open)	/*;evaluate_guards*/
{
	int i;
	struct entry_type	*entry;

	for (i=0;i< num_open;i++) {
		entry = MY_ENTRY(open_en[i]);
		del_lock(&(LOCK(entry)));
		ENTRY_GUARD(entry) = 1;
		del_unlock(&(LOCK(entry)));
	}
}

/*--------------------------------------------------------------------------*/
/*                            CLOSE  GUARDS                                 */
/*--------------------------------------------------------------------------*/


static void close_guards(int open_en[], int num_open)		/*;close_guards*/
{
	int i;
	struct entry_type	*entry;

	for (i=0;i< num_open;i++) {
		if ((open_en[i] != TERMINATE_EVENT) && (open_en[i] != TIMER_EVENT)){
			entry = MY_ENTRY(open_en[i]);
			del_lock(&(LOCK(entry)));
			ENTRY_GUARD(entry) = 0;
			del_unlock(&(LOCK(entry)));
		}
	}
}

/*--------------------------------------------------------------------------*/
/*                      POST  SELECTIVE  WAIT                               */
/*--------------------------------------------------------------------------*/

static void post_selective_wait(int in_mem, int num_alts, int open_en[],
  int open_ai[])									/*;post_selective_wait*/
{
	int	status, x, ai, accept_index;

	status = MY_STATUS;
	MY_STATUS = ACTIVE;
	if (MY_ABNORMAL) {
		if (status == SELECTING_TERM) MY_STATUS = QUIESCENT;
		abortme();
		return;
	}
	if (status == SELECTING_TERM) check_unterm();

	/* We must find the accept index for the selected alternative ... */
	if (MY_EVENT == TIMER_EVENT) MY_WHAT = TIMER_EVENT;
	accept_index = -1;
	if (in_mem) {
		if (num_alts != 0)
			for (x = 0; x < num_alts; x++)
				if (open_en[x] == MY_WHAT) accept_index=open_ai[x];
	}
	else {
		POP(num_alts);
		if (num_alts != 0)
			for (x =0 ; x < num_alts; x++) {
				POP(ai);
				POP(open_en[x]);
				if (open_en[x] == MY_WHAT) accept_index = ai;
			}
	}

	if ((num_alts != 0) && (accept_index == -1)) {
		raise(SYSTEM_ERROR, "Nonexistant alternative selected");
		return;
	}
	close_guards(open_en, num_alts);

	switch (MY_EVENT) {
	case TIMER_EVENT : 
		if (status == WAIT) {
			efree((char *) MY_IO_ITEM);
			MY_IO_ITEM = NULL;
		}
		PUSH(accept_index);			 
		break;
	case RDV_EVENT :
		disable_io(&MY_IO_ITEM);
		accept_rdv(MY_WHO,accept_index,num_alts); 
		break;
	default	      : 
		raise(SYSTEM_ERROR, 
		    "Unexpected event in select/accept"); 
		break;
	}
}

/*--------------------------------------------------------------------------*/
/*                               ACCEPT                                     */
/*--------------------------------------------------------------------------*/

static void accept_rdv(int caller, int accept_index, int push_index)
																/*;accpt_rdv*/
{
	int	num_param;	/* number of parameters to transfer */
	int	disp, i;

	/* Must copy parameters over from the caller's stack */

	disp = STACKPTR(caller) - NB_REGISTERS;
	num_param = STACK(caller)[disp];
	disp -= num_param + 1;
	for (i = 1; i <= num_param; i++)
		PUSH(STACK(caller)[disp+i]);

	add_serviced(tp, caller);	/* may be nested rdv need if aborted */
	if (push_index)
		PUSH(accept_index);
}

/*--------------------------------------------------------------------------*/
/*                          END_RENDEZVOUS                                  */
/*--------------------------------------------------------------------------*/

void end_rendezvous()										/*;end_rendevous*/
{
	int	caller;

	caller = remove_serviced();
#ifdef TRACE
	if (rendezvous_trace)
		printf("task %d end rendezvous with task %d \n",tp, caller);
#endif
	MY_PRIO = TCB_SAVE_PRIO(caller);
	if (MY_EXCEPTION)	       /* propagate exception to calling task */
		TCB_EXCEPTION(caller) = MY_EXCEPTION;

	make_ready(caller, ENDRDV_EVENT);
	if (MY_ABNORMAL) {              /* owner aborted, raise TASKING ERROR */
		TCB_EXCEPTION(caller) = TASKING_ERROR;
		abortme();
		return;
	}
}


/*--------------------------------------------------------------------------*/
/*                         ENTRY  CALL                                      */
/*--------------------------------------------------------------------------*/

void entry_call(long delay_time, int num_param)					/*;entry_call*/
{
	struct entry_type *entry;
	int	owner;			/* owner of entry */
	int	family;			/* index of family of the entry */
	int	member;			/* index of member of the entry */
	int	entry_num;		/* actual entry number */

	/* STEP 1:  Get calling information from the stack */

	member = TOSM(num_param);
	family = TOSM(num_param + 1);
	owner  = TOSM(num_param + 2);
	if (is_callable(owner) == FALSE) {
		switch(TCB_STATUS(owner)) {
		case TERMINATED:
			raise(TASKING_ERROR, "Call to an entry of a terminated task");
			return;
		case COMPLETED:
		default:
			raise(TASKING_ERROR, "Call to an entry of a completed task");
			return;
		}
	}
	entry_num = entry_number(owner, family, member);

#ifdef TRACE
	if (rendezvous_trace)
		printf("task %d calling rendezvous with task %d entry %d\n",
		  tp, owner, entry_num);
#endif

	/* STEP 2: Perform some error detection */

	if (entry_num > TCB_NUM_ENTRIES(owner)) {
		raise(SYSTEM_ERROR, "Nonexistant entry called");
		return;
	}

	/* STEP 3: Set statuses */

	if (MY_ABNORMAL) { 
		abortme(); 
		return; 
	}
	if (delay_time == ENDLESS)
		MY_STATUS = CALLING_RDV;
	else MY_STATUS = TIMED_RDV;
	entry = TCB_ENTRY(owner, entry_num);
	PUSH(num_param);
	add_lock(&(LOCK(entry)));

	/* STEP 4:  See if immediate rendezvous */

	if ((INC(ENTRY_COUNT(entry)) == 0) && ENTRY_GUARD(entry) &&
	  (FAS(&(TCB_RDV(owner)), 0) == 1)) {
		/* owner is commited to a rendezvous with the caller */
		DEC(ENTRY_COUNT(entry));	/* restore counter */
		TCB_WHAT(owner) = entry_num;
		TCB_WHO(owner) = tp;
		add_unlock(&(LOCK(entry)));
		disable_io(&(TCB_IO_ITEM(owner)));
		MY_SAVE_PRIO = TCB_PRIO(owner);
		TCB_PRIO(owner) = MAX(TCB_PRIO(owner),MY_PRIO);
		make_ready(owner, RDV_EVENT);
		schedule(ENTRY_CALL);		/* wait for end of rdv */
	}

	/* STEP 5: Cannot rendezvous immediately */

	else {    /* cannot immediately start a rendezvous */
		if (delay_time == 0) {   /* else changed to "delay 0" */
			DEC(ENTRY_COUNT(entry));
			add_unlock(&(LOCK(entry)));
			cur_stackptr -= 3;
			PUSH(0);
		}
		else {
			MY_CURR_ENTRY = entry;
			eput(entry, tp, &MY_ENTRY_ITEM);
			add_unlock(&(LOCK(entry)));
			if (MY_ABNORMAL && eremove(tp)) {
				abortme();
				return;
			}
			if (delay_time != ENDLESS)
				MY_IO_ITEM = chain(tp, delay_time);
			schedule(ENTRY_CALL);
		}
	}
}

/*-------------------------------------------------------------------*/
/*                       POST  ENTRY  CALL                           */
/*-------------------------------------------------------------------*/

static void post_entry_call()							/*;post_entry_call*/
{
	int	num_param;	/* number of parameters */
	int	i;

	POP(num_param);
	if (MY_ABNORMAL)  {
		disable_io(&MY_IO_ITEM);
		abortme();
		return;
	}

	i = MY_EVENT;
	switch (MY_EVENT) {
	case TIMER_EVENT : 
		efree((char *) MY_IO_ITEM);
		MY_IO_ITEM = NULL;
		cur_stackptr -= 3;
		PUSH(0); 				
		break;
	case ENDRDV_EVENT: 
		disable_io(&MY_IO_ITEM);
		if (MY_EXCEPTION)
			raise(MY_EXCEPTION, "Exception propagated from called task");
		MY_EXCEPTION = 0;
		for (i = cur_stackptr - num_param - 3 + 1; i <= cur_stackptr; i++)
			cur_stack[i] = cur_stack[i+3];
		cur_stackptr -=3;
		if (MY_STATUS == TIMED_RDV) 
			PUSH(1); 
		break;
	case TASKERR_EVENT :
		raise(TASKING_ERROR, "Entry call failed: called task terminated");
		MY_EXCEPTION = 0; 			
		break;
	default	: 
		raise(SYSTEM_ERROR, "Unexpected event in entry call"); 	
		break;
	}
	MY_STATUS = ACTIVE;
}


/*-----------------------------------------------------------------------*/
/*                       U T I L I T Y    R O U T I N E S                */
/*-----------------------------------------------------------------------*/

/*--------------------------------------------------------------------------*/
/*                          ENTRY  QUEUE  ROUTINES                          */
/*   The following four routines (einit, eremove, eput & eget) are parallel */
/*   access queue routines for maintaining the entry queue in tasks' tcbs.  */
/*--------------------------------------------------------------------------*/

static void einit(struct entry_type	*entry)							/*;einit*/
{
	ENTRY_LAST(entry) = NULL;
	ENTRY_FIRST(entry) = NULL;
	(LOCK(entry)).add_lock = 0;
	(LOCK(entry)).del_lock = 0;
	ENTRY_GUARD(entry) = 0;
	ENTRY_COUNT(entry) = 0;
}

static int eremove(int task)									/*;eremove*/
{
	if ((TCB_ENTRY_ITEM(task) == NULL) || (TCB_CURR_ENTRY(task) == NULL))
		return FALSE;

	add_lock(&(LOCK(TCB_CURR_ENTRY(task))));
	if (FAS(&(ITEM_FLAG(TCB_ENTRY_ITEM(task))), 0) == 0) {
		add_unlock(&(LOCK(TCB_CURR_ENTRY(task))));
		return FALSE;
	}
	else {
		DEC(ENTRY_COUNT(TCB_CURR_ENTRY(task)));
		add_unlock(&(LOCK(TCB_CURR_ENTRY(task))));
		TCB_CURR_ENTRY(task) = NULL;
		TCB_ENTRY_ITEM(task) = NULL;
		return TRUE;
	}
}

static void eput(struct entry_type *entry, int caller, struct q_item **ret_item)
																	/*;eput*/
{
	struct q_item	*prev_item, *item;

	item = (struct q_item*) malloc(sizeof(struct q_item));
	if (item == (struct q_item*)0) {
		raise(STORAGE_ERROR, "Allocating space for entry queue");
		return;
	}
	ITEM_FLAG(item) = 1;
	ITEM_TASK(item) = caller;
	ITEM_NEXT(item) = NULL;
	prev_item =  FAS_Q(&(ENTRY_LAST(entry)), item);
	if (prev_item == (struct q_item *)0)
		FAS_Q(&(ENTRY_FIRST(entry)), item);
	else
		FAS_Q(&(ITEM_NEXT(prev_item)), item);
	*ret_item = item;
}

static int eget(struct entry_type *entry)							/*;eget*/
{
	struct q_item		*caller, *new_caller;
	int			task;

	del_lock(&(LOCK(entry)));
	if (ENTRY_FIRST(entry) == NULL) {
		del_unlock(&(LOCK(entry)));
		return NULL_TASK;
	}

	ENTRY_GUARD(entry) = 0;
	caller = FAS_Q(&(ENTRY_FIRST(entry)), (ITEM_NEXT(ENTRY_FIRST(entry))));
	while ((caller != (struct q_item*)0) && (FAS(&(ITEM_FLAG(caller)),0) == 0)){
		new_caller = FAS_Q(&(ENTRY_FIRST(entry)),ITEM_NEXT(ENTRY_FIRST(entry)));
		efree((char *) caller);
		caller = new_caller;
	}

	if (caller != (struct q_item*)0) {
		if (TCB_IO_ITEM(ITEM_TASK(caller)) != NULL)
			disable_io(&(TCB_IO_ITEM(ITEM_TASK(caller))));
		if (ENTRY_COUNT(entry) == 0) FAS_Q(&(ENTRY_LAST(entry)), NULL);
		task = ITEM_TASK(caller);
		efree((char *) caller);
		TCB_ENTRY_ITEM(task) = (struct q_item *)0;
	}
	else task = NULL_TASK;
	del_unlock(&(LOCK(entry)));
	return(task);
}

/*---------------------------------------------------------------------------*
 *                           LOCKING  ROUTINES                               *
 *                                                                           *
 * Locks on entries may be either "add" locks or "del" locks.  "del" (or     *
 * delete) locks have precedence over "add" locks.  These are implemented    *
 * using a standard A-B locking scheme.                                      *
 *---------------------------------------------------------------------------*/

static void add_lock(struct lock_type *lock)					/*;add_lock*/
{
	for (;;) {
		while (lock->del_lock > 1) continue;  /* wait for dels to end */
		INC(lock->add_lock);		     /* try tp get add lock  */
		if (lock->del_lock > 1)               /* oops, del started... */
			DEC(lock->add_lock);
		else break;
	}
}

static void add_unlock(struct lock_type *lock)					/*;add_unlock*/
{
	DEC(lock->add_lock);
}

static void del_lock(struct lock_type *lock)					/*;del_lock */
{
	INC(lock->del_lock);		 /* don't allow adds to start */
	while (lock->add_lock > 1) continue;  /* wait for adds to end */
}

static void del_unlock(struct lock_type *lock)					/*;del_unlock*/
{
	DEC(lock->del_lock);
}

/*-----------------------------------------------------------------------*/
/*                          ENTRY NUMBER                                 */
/*-----------------------------------------------------------------------*/

static int entry_number(int owner, int family, int member)	/*;entry_number*/
{
	return (*ADDR(TCB_TBASE(owner), TCB_TOFF(owner) + 2 * (family -1))
	  + member + 1);
}

/*------------------------------------------------------------------------*
 *                          RAISE  IN  CALLER                             *
 * Procedure to raise an exception in the task waiting for the completion *
 * of the current rendezvous						  *
 * -----------------------------------------------------------------------*/

void raise_in_caller()									/*;raise_in_caller*/
{
#ifdef TRACE
	if (exception_trace)
		printf("task %d raising exception %s in task %d\n",tp,
		  exception_slots[exr],MY_SERVICED);
#endif
	TCB_EXCEPTION(MY_SERVICED) = exr;
}


/* -----------------------------------------------------------------------*
 *                           ATTRIBUTE  ROUTINES                          *
 *  The following three routines (is_callable, is_terminated and count)   *
 *  return the attributes 'CALLABLE, 'TERMINATED and 'COUNT respecitvely  *
 *  for the given task                                                    *
 * -----------------------------------------------------------------------*/

int is_callable(int task)									/*;is_callable*/
{
	if (task != ORIG(task) || STACK(task) == (int *)0 || TCB_ABNORMAL(task))
		return FALSE;
	switch(TCB_STATUS(task)) {
	case TERMINATED:
	case ABNORMAL: 
		return FALSE;
	case COMPLETED: 	/* are we completed on the last level? */
		return BF_PREVIOUS_BFP(task, *(TCB_BLOCK_PTR(task))) == NULL_TASK;
	default: 
		return TRUE;
	}
}

int is_terminated(int task)								/*;is_terminated*/
{
	if (task != ORIG(task) || STACK(task) == (int *)0 )  return TRUE;
	return (TCB_STATUS(task) == TERMINATED);
}

int count(int family, int member)								/*;count*/
{
	return(ENTRY_COUNT(MY_ENTRY(entry_number(tp, family, member))));
}

/*---------------------------------------------------------------------------*/
/*                              MULTISIGNAL                                  */
/*---------------------------------------------------------------------------*/

static void multisignal(int task, int event) 				/*;multisignal*/
{
	if (event != NO_EVENT) TCB_EVENT(task) = event;
	if (DEC(TCB_NUM_ITEMS(task)) == 1)
		make_ready(task, NO_EVENT);
}

/*---------------------------------------------------------------------------*/
/*                            "SERVICED"  QUEUE                              */
/*---------------------------------------------------------------------------*/

static void add_serviced(int server, int task)				/*;add_serviced*/
{
	TCB_NEXT(task) = FAS(&(TCB_SERVICED(server)), task);
}

static int remove_serviced()							/*;remove_serviced*/
{
	return(FAS(&(MY_SERVICED), TCB_NEXT(MY_SERVICED)));
}

/*--------------------------------------------------------------------------*/
/*                             READY  QUEUE                                 */
/*  The following three routines (qinit, enqueue, enqueue_item and dequeue) */
/*  are the routines used in accessing the ready queue.  The other three    */
/*  routines are used to control the scheduler.                             */
/*--------------------------------------------------------------------------*/

static void qinit()													/*;qinit*/
{
	int	i;
	struct ready_q	*q;

	for (i = 0; i < MAX_PRIO; i++) {
		ready_queue[i] = (struct ready_q *)malloc(sizeof(struct ready_q));
		q = ready_queue[i];
		if (q == (struct ready_q *)0) {
			printf("Unable to allocate stack\n");
			exit(RC_ABORT);
		}
		q->first = NULL;
		q->last = NULL;
		q->first_mult = 0;
		q->count = 0;
		q->lock.add_lock = 0;
		q->lock.del_lock = 0;
	}
}

static void enqueue(int priority, int value)					/*;enqueue*/
{
	struct rts_item	*item;

	item = (struct rts_item *) malloc(sizeof(struct rts_item));
	if (item == (struct rts_item *)0){
		raise(STORAGE_ERROR, "Allocating space for ready queue");
		return;
	}
	item->tcbs = (int *) malloc(sizeof(int));
	if (item->tcbs == (int *)0){
		raise(STORAGE_ERROR, "Allocating space for ready queue");
		return;
	}
	RTS_TYPE(item) = READY;
	RTS_PRIO(item) = priority;
	RTS_MULT(item) = 1;
	RTS_NEXT(item) = NULL;
	RTS_TCBS(item, 0) = value;
	enqueue_item(priority, item);
}

static void enqueue_item(int priority, struct rts_item *item)  /*;enqueue_item*/
{
	struct ready_q	*q;
	struct rts_item	*prev;

	RTS_SAVE_MULT(item) = RTS_MULT(item);
	q = ready_queue[priority];
	while (highest_priority < priority)
		priority = FAS(&highest_priority, priority);
	add_lock(&(LOCK(q)));
	prev = FAS_RTS(&(q->last), item);
	if (prev == (struct rts_item *)0) {
		FAS_RTS(&(q->first), item);
		FAS(&(q->first_mult), item->mult);
	}
	else	FAS_RTS(&(prev->next), item);
	q->count += item->mult;
	add_unlock(&(LOCK(q)));
}

static struct rts_item *dequeue(struct ready_q *q, int *i)			/*;dequeue*/
{
	struct rts_item	*item;
	int	j, k;

	if (q->count <= 0) return (struct rts_item *)0;
	else if (DEC(q->count) < 1) {
		INC(q->count);
		return (struct rts_item *)0;
	}
	else {
		while (q->first_mult > 0 && DEC(q->first_mult) < 1) continue;
		item = q->first;
		if ((j = DEC(q->first->mult)) == 1) {  /* remove from list */
			RTS_MULT(q->first) = RTS_SAVE_MULT(q->first);
			if (q->first->next == NULL)  {
				del_lock(&(LOCK(q)));
				if (q->first->next == NULL)  {
					FAS_RTS(&q->first, NULL);
					FAS_RTS(&q->last, NULL);
				}
				else {
					FAS_RTS(&(q->first), q->first->next);
					FAS(&(q->first_mult), q->first->mult);
				}
				del_unlock(&(LOCK(q)));
			}
			else {
				FAS_RTS(&(q->first), q->first->next);
				FAS(&(q->first_mult), q->first->mult);
			}
		}
		k = 0; 
		*i = -1;
		while (k < j)
			if (item->tcbs[++(*i)] != NULL_TASK) k++;
		return item;
	}
}

static void context_switch()								/*;context_switch*/
{
	DEC(MY_NUM_EVENTS);
	make_ready(tp, TIMER_EVENT);
	schedule(CONTEXT_SWITCH);
}

#ifdef IBM_PC
static void sleep(unsigned secs)
{
	clock_t check = clock();
	check += secs * CLOCKS_PER_SEC;
	while (clock() < check)
		;
}
#endif
