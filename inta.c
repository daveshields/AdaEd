/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/* interpreter procedures - interpreter part a */


/* Include standard header modules */
#include <stdio.h>
#include <stdlib.h>
#include "config.h"
#include "int.h"
#include "ivars.h"
#include "farithprots.h"
#include "predefprots.h"
#include "machineprots.h"
#include "taskingprots.h"
#include "imiscprots.h"
#include "intbprots.h"
#include "intcprots.h"
#include "intaprots.h"

static int main_loop();
static int get_word();
#ifdef DEBUG_INT
static void zbreak(int);
#endif

#define TRACE
/* MAIN PROGRAM */

#ifdef DEBUG_STORES
int *heap_store_addr;
/* set heap_store_offset non zero to trace stores to that offset
 * in primary heap 
 */
extern int heap_store_offset;
int heap_store_now=0;
#endif

int int_main()												/*;int_main*/
{
	int	    status;

	reset_clock();
	num_cunits = 0;

	/* Memory initialization, allocate primary heap segment. */

	if(!allocate_new_heap()) {
		fprintf(stderr,"Unable to allocate primary heap\n");
		exit(RC_ABORT);
	}

	/* Initialize working template for fixed point arithmetic */

	*heap_next++ = 1 + WORDS_PTR + WORDS_FX_RANGE;
	heap_next += WORDS_PTR;
	temp_template = FX_RANGE(heap_next);
	temp_template->ttype = TT_FX_RANGE;
	temp_template->object_size = 2;
	temp_template->small_exp_2 = 0;
	temp_template->small_exp_5 = 0;
	temp_template->fxlow = MIN_LONG;
	temp_template->fxhigh = MAX_LONG;
	heap_next += WORDS_FX_RANGE;

	/* Other initialization */

	sfp = bfp = 0;
	initialize_predef();
	initialize_tasking();

	/* Perform the main loop of the interpretor(terminates at end of pgm) */

	status = main_loop();

	/* Termination processing */

	predef_term();

	return status;
}

/*
 *  MAIN LOOP
 *  =========
 */

/*
 *  GET_BYTE		Next code byte (char), IP is incremented
 *  GET_WORD		Next code word (int), IP is incremented
 *  GET_GAD(bse,off)	Get base/offset from code, IP incremented
 *  GET_LAD(bse,off)	Get local addr from code, and get corr global addr
 */
#define GET_BYTE	  (0xff & (int)cur_code[ip++])
#ifdef ALIGN_WORD
#define GET_WORD	  (w=get_word(), w)
#else
#define GET_WORD          (w = *((int *)(cur_code+ip)), ip += sizeof(int), w)
#endif
#define GET_GAD(bse,off)  bse=GET_BYTE,off=GET_WORD
#define GET_LAD(bse,off)  sp=GET_WORD+sfp,bse=cur_stack[sp],off=cur_stack[sp+1]

static int main_loop()											/*;main_loop*/
{
#ifdef DEBUG_INT
	int     iparg;
#endif
#ifdef ALIGN_WORD
	/* auxiliary procedures if must unpack from code stream byte by byte */
#endif

	/* General purpose work locations */

	/* Loop through instructions */

	for (;;) {

		/* Simulate the Clock Interrupt */

		if (next_clock_flag &&(next_clock <(now_time = itime() + time_offset)))
			clock_interrupt(now_time);

		/* Round-robin scheme: next task's turn ? */

		if (rr_flag && (rr_counter++ > rr_nb_max_stmts))
			round_robin();

#ifdef DEBUG_INT
#ifdef DEBUG_STORES
		if (heap_store_offset!=0 && 
		  heap_store_now != heap_store_addr[heap_store_offset]) {
			printf("heap stores change %d from %d to %d\n",
			  heap_store_offset, heap_store_now, 
			  heap_store_addr[heap_store_offset]);
			heap_store_now = heap_store_addr[heap_store_offset];
		}
#endif
		iparg = ip;
		if (instruction_trace)
			i_list1(&iparg, cur_code);		/* debug */
		if(break_point && (ip >= break_point))
			zbreak(0);
#endif
		/* Get next opcode, bump instruction pointer and switch to routine */
		switch(GET_BYTE) {

		case I_NOP:
			break;

			/* Instructions Dealing with Tasking */

		case I_ABORT:
			value = GET_WORD;			/* number of tasks in stack */
			abort(value);
			break;

		case I_ACTIVATE:
			if (BLOCK_FRAME->bf_tasks_declared != 0) {
				value = pop_task_frame();
				start_activation(value, tp, bfp);
				/* master is current block frame */
			}
			break;

		case I_ACTIVATE_NEW_L:
			GET_LAD(bse, off);
			if (BLOCK_FRAME->bf_tasks_declared != 0) {
				value = pop_task_frame();
				ptr = ADDR(bse, off);
				start_activation(value, ACCESS(ptr)->master_task, 
				  ACCESS(ptr)->master_bfp);
			}
			break;

		case I_ACTIVATE_NEW_G:
			GET_GAD(bse, off);
			if (BLOCK_FRAME->bf_tasks_declared != 0) {
				value = pop_task_frame();
				ptr = ADDR(bse, off);
				start_activation(value, ACCESS(ptr)->master_task, 
				  ACCESS(ptr)->master_bfp);
			}
			break;

		case I_CREATE_TASK_G:
			GET_GAD(bse, off);
			start_creation(bse, off);
			break;

		case I_CREATE_TASK_L:
			GET_LAD(bse, off);
			start_creation(bse, off);
			break;

		case I_POP_TASKS_DECLARED_G:
			GET_GAD(bse, off);
			if (BLOCK_FRAME->bf_tasks_declared != 0)
				value = pop_task_frame();
			else
				value = 0;
			*ADDR(bse, off) = value;
			break;

		case I_POP_TASKS_DECLARED_L:
			GET_LAD(bse, off);
			if (BLOCK_FRAME->bf_tasks_declared != 0)
				value = pop_task_frame();
			else
				value = 0;
			*ADDR(bse, off) = value;
			break;

		case I_LINK_TASKS_DECLARED:
			POP(value);
			push_task_frame(value);
			break;

		case I_CURRENT_TASK:
			PUSH(tp);
			break;

		case I_END_ACTIVATION:
			value = GET_BYTE;
			end_activation(value);	/* 0=error during activation, 1=ok */
			break;

		case I_END_RENDEZVOUS:
			end_rendezvous();
			break;

		case I_ENTRY_CALL:
			value = GET_WORD;		/* retrieve parameter from code */
			entry_call((long) ENDLESS,value);
			break;

		case I_RAISE_IN_CALLER:
			raise_in_caller();
			break;

		case I_SELECTIVE_WAIT:
			value = GET_WORD;		/* number of alternatives */

			/* if = 0 then it is a simple accept, entry addr is on stack. */
			/* else: alternative descriptors on to of stack are scanned by */
			/*   the procedure, which leaves the index of the chosen one.  */

			selective_wait(value);
			break;

		case I_TERMINATE:
			purge_rdv(tp);
			value = GET_BYTE;
			deallocate(BLOCK_FRAME->bf_data_link);

			/* bf_tasks_declared always null here */

			switch(value) {

			case 0: /* task terminates because reaches the end */
				break;

			case 1: /* task terminates because of terminate alternative */
				break;

			case 2:
				value = 0;
				if (exception_trace)
					printf("task %d terminated due to unhandled exception: %s\n"
					  ,tp,exception_slots[exr]);
				break;

			case 3:
				printf("unhandled exception in library unit %s\n",
				  exception_slots[exr]);
				return RC_ERRORS;

			case 4:
				printf("main task terminated due to unhandled exception %s\n",
				  exception_slots[exr]);
				printf("propagated from %s",code_slots[raise_cs]);
				if (raise_lin) printf(" at line %d",raise_lin);
				printf(" (%s)\n",raise_reason);
				return RC_ERRORS;

			case 5: /* normal end of main */
				return RC_SUCCESS;

			case 6: /* dead-lock */
				printf("dead-lock: system inactive\n");
				return RC_ERRORS;
			}
			complete_task();
			break;

		case I_TIMED_ENTRY_CALL:
			POPL(lvalue);
			/* retrieve length of parameter table from code */
			entry_call((lvalue >= 0) ? lvalue : (long) 0, GET_WORD);
			break;

		case I_WAIT: 	/* delay */
			POPL(lvalue);
			delay_stmt(lvalue);
			break;

			/* Instructions for Memory Allocation */

		case I_CREATE_B:
		case I_CREATE_W:
			create(1, &bse, &off, &ptr);
			PUSH_ADDR(bse, off);
			break;

		case I_CREATE_L:
			create(WORDS_LONG, &bse, &off, &ptr);
			PUSH_ADDR(bse, off);
			break;

		case I_CREATE_A:
			create(2, &bse, &off, &ptr);
			PUSH_ADDR(bse, off);
			break;

		case I_CREATE_STRUC:
			create_structure();
			break;

		case I_CREATE_COPY_STRUC:
			create_copy_struc();
			break;

		case I_CREATE_COPY_B:
		case I_CREATE_COPY_W:
			create(1, &bse, &off, &ptr);
			POP(value);
			PUSH_ADDR(bse, off);
			*ptr = value;
			break;

		case I_CREATE_COPY_L:
			create(WORDS_LONG, &bse, &off, &ptr);
			POPL(lvalue);
			PUSH_ADDR(bse, off);
			*LONG(ptr) = lvalue;
			break;

		case I_CREATE_COPY_A:
			create(2, &bse, &off, &ptr);
			POP_ADDR(bas1, off1);
			PUSH_ADDR(bse, off);
			*ptr++ = bas1;
			*ptr = off1;
			break;

		case I_DECLARE_B:
		case I_DECLARE_W:
			create(1, &bse, &off, &ptr);
			sp = sfp + GET_WORD;
			cur_stack[sp] = bse;
			cur_stack[sp + 1] = off;
			break;

		case I_DECLARE_D:
			create(4, &bse, &off, &ptr);
			sp = sfp + GET_WORD;
			cur_stack[sp] = bse;
			cur_stack[sp + 1] = off;
			break;

		case I_DECLARE_L:
			create(WORDS_LONG, &bse, &off, &ptr);
			sp = sfp + GET_WORD;
			cur_stack[sp] = bse;
			cur_stack[sp + 1] = off;
			break;

		case I_DECLARE_A:
			create(2, &bse, &off, &ptr);
			sp = sfp + GET_WORD;
			cur_stack[sp] = bse;
			cur_stack[sp + 1] = off;
			break;

		case I_ALLOCATE:
			allocate_new();
			break;

		case I_ALLOCATE_COPY_G:
			GET_GAD(bse, off);			/* addr. of the type template */
			allocate_copy(bse, off);
			break;

		case I_ALLOCATE_COPY_L:
			GET_LAD(bse, off);			/* addr. of the type template */
			allocate_copy(bse, off);
			break;

		case I_UPDATE:
			sp = sfp + GET_WORD;
			cur_stack[sp] = TOSM(1);	/* base */
			cur_stack[sp + 1] = TOS;	/* offset */
			break;

		case I_UPDATE_AND_DISCARD:
			sp = sfp + GET_WORD;
			POP_ADDR(bse, off);
			cur_stack[sp] = bse;
			cur_stack[sp + 1] = off;
			break;

		case I_UNCREATE:
			POP_ADDR(bse, off);
			ptr = ADDR(bse, off) - WORDS_PTR - 1;
			*ptr = - *ptr;
			break;
			/* should withdraw the variable from bf_data_link TBSL */

			/* Data Transfer Instructions */

		case I_COMPARE_B:
		case I_COMPARE_W:
			POP(val1);
			POP(val2);
			value = (val1 == val2) + 2 *((val1 < val2) ? 1:0);
			/* 0 1 2 for < = > */
			PUSH(value);
			break;

		case I_COMPARE_L:
			POPL(lval1);
			POPL(lval2);
			value = (lval1 == lval2) + 2 *((lval1 < lval2) ? 1:0);
			/* 0 1 2 for < = > */
			PUSH(value);
			break;

		case I_COMPARE_A:
			POP_ADDR(bas1, off1);
			POP_ADDR(bas2, off2);
			value = (off1 == off2 && bas1 == bas2);
			PUSH(value);
			break;

		case I_COMPARE_ARRAYS:
			compare_arrays();
			break;

		case I_COMPARE_STRUC:
			compare_struc();
			break;

		case I_DEREF_B:
		case I_DEREF_W:
			POP_ADDR(bse, off);
			if (bse == 255)
				raise(CONSTRAINT_ERROR, "Null access value");
			else {
				value = *ADDR(bse, off);
				PUSH(value);
			}
			break;

		case I_DEREF_L:
			POP_ADDR(bse, off);
			if (bse == 255)
				raise(CONSTRAINT_ERROR, "Null access value");
			else {
				lvalue = *ADDRL(bse, off);
				PUSHL(lvalue);
			}
			break;

		case I_DEREF_A:
			POP_ADDR(bse, off);
			if (bse == 255)
				raise(CONSTRAINT_ERROR, "Null access value");
			else {
				value = *ADDR(bse, off);
				PUSH(value);
				value = *ADDR(bse, off + 1);
				PUSH(value);
			}
			break;

		case I_DEREF_D:
			POP_ADDR(bse, off);
			if (bse == 255)
				raise(CONSTRAINT_ERROR, "Null access value");
			else {
				value = *ADDR(bse, off);
				PUSH(value);
				value = *ADDR(bse, off + 1);
				PUSH(value);
				value = *ADDR(bse, off + 2);
				PUSH(value);
				value = *ADDR(bse, off + 3);
				PUSH(value);
			}
			break;

		case I_DISCARD_ADDR:
			value = GET_WORD;
			cur_stackptr -= (2 * value);
			break;

		case I_DUPLICATE_B:
		case I_DUPLICATE_W:
			value = TOS;
			PUSH(value);
			break;

		case I_DUPLICATE_L:
			lvalue = TOSL;
			PUSHL(lvalue);
			break;

		case I_DUPLICATE_A:
			POP_ADDR(bse, off);
			PUSH_ADDR(bse, off);
			PUSH_ADDR(bse, off);
			break;

		case I_DUPLICATE_D:
			value = TOSM(3);
			PUSH(value);
			value = TOSM(3);
			PUSH(value);
			value = TOSM(3);
			PUSH(value);
			value = TOSM(3);
			PUSH(value);
			break;

		case I_INDIRECT_MOVE_B:
		case I_INDIRECT_MOVE_W:
			POP_ADDR(bas1, off1);
			POP_ADDR(bas2, off2);
			if (bas1 == 255 || bas2 == 255)
				raise(CONSTRAINT_ERROR, "Null access value");
			else
				*ADDR(bas2, off2) = *ADDR(bas1, off1);
			break;

		case I_INDIRECT_MOVE_L:
			POP_ADDR(bas1, off1);
			POP_ADDR(bas2, off2);
			if (bas1 == 255 || bas2 == 255)
				raise(CONSTRAINT_ERROR, "Null access value");
			else
				*ADDRL(bas2, off2) = *ADDRL(bas1, off1);
			break;

		case I_INDIRECT_MOVE_A:
			POP_ADDR(bas1, off1);
			POP_ADDR(bas2, off2);
			if (bas1 == 255 || bas2 == 255)
				raise(CONSTRAINT_ERROR, "Null access value");
			else {
				*ADDR(bas2, off2) = *ADDR(bas1, off1);
				*ADDR(bas2, off2 + 1) = *ADDR(bas1, off1 + 1);
			}
			break;

		case I_INDIRECT_POP_B_G:
		case I_INDIRECT_POP_W_G:
			GET_GAD(bse, off);
			POP_ADDR(bas1, off1);
			if (bas1 == 255)
				raise(CONSTRAINT_ERROR, "Null access value");
			else
				*ADDR(bse, off) = *ADDR(bas1, off1);
			break;

		case I_INDIRECT_POP_L_G:
			GET_GAD(bse, off);
			POP_ADDR(bas1, off1);
			if (bas1 == 255)
				raise(CONSTRAINT_ERROR, "Null access value");
			else
				*ADDRL(bse, off) = *ADDRL(bas1, off1);
			break;

		case I_INDIRECT_POP_A_G:
			GET_GAD(bse, off);
			POP_ADDR(bas1, off1);
			if (bas1 == 255)
				raise(CONSTRAINT_ERROR, "Null access value");
			else {
				*ADDR(bse, off) = *ADDR(bas1, off1);
				*ADDR(bse, off + 1) = *ADDR(bas1, off1 + 1);
			}
			break;

		case I_INDIRECT_POP_B_L:
		case I_INDIRECT_POP_W_L:
			GET_LAD(bse, off);
			POP_ADDR(bas1, off1);
			if (bas1 == 255)
				raise(CONSTRAINT_ERROR, "Null access value");
			else
				*ADDR(bse, off) = *ADDR(bas1, off1);
			break;

		case I_INDIRECT_POP_L_L:
			GET_LAD(bse, off);
			POP_ADDR(bas1, off1);
			if (bas1 == 255)
				raise(CONSTRAINT_ERROR, "Null access value");
			else
				*ADDRL(bse, off) = *ADDRL(bas1, off1);
			break;

		case I_INDIRECT_POP_A_L:
			GET_LAD(bse, off);
			POP_ADDR(bas1, off1);
			if (bas1 == 255)
				raise(CONSTRAINT_ERROR, "Null access value");
			else {
				*ADDR(bse, off) = *ADDR(bas1, off1);
				*ADDR(bse, off + 1) = *ADDR(bas1, off1 + 1);
			}
			break;

		case I_MOVE_B:
		case I_MOVE_W:
			POP(value);
			POP_ADDR(bse, off);
			if (bse == 255)
				raise(CONSTRAINT_ERROR, "Null access value");
			else 
				*ADDR(bse, off) = value;
			break;

		case I_MOVE_L:
			POPL(lvalue);
			POP_ADDR(bse, off);
			if (bse == 255)
				raise(CONSTRAINT_ERROR, "Null access value");
			else 
				*ADDRL(bse, off) = lvalue;
			break;

		case I_MOVE_A:
			POP_ADDR(bas1, off1);
			POP_ADDR(bse, off);
			ptr = ADDR(bse, off);
			*ptr++ = bas1;
			*ptr = off1;
			break;

		case I_POP_B_G:
		case I_POP_W_G:
			GET_GAD(bse, off);
			POP(value);
			*ADDR(bse, off) = value;
			break;

		case I_POP_L_G:
			GET_GAD(bse, off);
			POPL(lvalue);
			*ADDRL(bse, off) = lvalue;
			break;

		case I_POP_D_G:
			/* This has to be set later  TBSL:
			 * for the moment, we do not take care of the poped value. We
			 * beleive this is only being used for the evaluation of object size
			 */
			GET_GAD(bse, off);
			for (i=1; i <= 4 ; i++)
				POP (value);
			break;

		case I_POP_D_L:
			GET_LAD(bse, off);
			for (i=1; i <= 4; i++)
				POP (value);
			break;

		case I_POP_A_G:
			GET_GAD(bse, off);
			POP_ADDR(bas1, off1);
			*ADDR(bse, off) = bas1;
			*ADDR(bse, off + 1) = off1;
			break;

		case I_POP_B_L:
		case I_POP_W_L:
			GET_LAD(bse, off);
			POP(value);
			*ADDR(bse, off) = value;
			break;

		case I_POP_L_L:
			GET_LAD(bse, off);
			POPL(lvalue);
			*ADDRL(bse, off) = lvalue;
			break;

		case I_POP_A_L:
			GET_LAD(bse, off);
			POP_ADDR(bas1, off1);
			*ADDR(bse, off) = bas1;
			*ADDR(bse, off + 1) = off1;
			break;

		case I_PUSH_B_G:
		case I_PUSH_W_G:
			GET_GAD(bse, off);
			value = *ADDR(bse, off);
			PUSH(value);
			break;

		case I_PUSH_L_G:
			GET_GAD(bse, off);
			lvalue = *ADDRL(bse, off);
			PUSHL(lvalue);
			break;

		case I_PUSH_A_G:
			GET_GAD(bse, off);
			ptr = ADDR(bse, off);
			bas1 = *ptr++;
			off1 = *ptr;
			PUSH_ADDR(bas1, off1);
			break;

		case I_PUSH_B_L:
		case I_PUSH_W_L:
			GET_LAD(bse, off);
			value = *ADDR(bse, off);
			PUSH(value);
			break;

		case I_PUSH_L_L:
			GET_LAD(bse, off);
			lvalue = *ADDRL(bse, off);
			PUSHL(lvalue);
			break;

		case I_PUSH_A_L:
			GET_LAD(bse, off);
			ptr = ADDR(bse, off);
			bas1 = *ptr++;
			off1 = *ptr;
			PUSH_ADDR(bas1, off1);
			break;

		case I_PUSH_EFFECTIVE_ADDRESS_G:
		case I_PUSH_IMMEDIATE_A:
			GET_GAD(bse, off);
			PUSH_ADDR(bse, off);
			break;

		case I_PUSH_EFFECTIVE_ADDRESS_L:
			GET_LAD(bse, off);
			PUSH_ADDR(bse, off);
			break;

		case I_PUSH_IMMEDIATE_B:
			PUSH(GET_WORD);
			break;

		case I_PUSH_IMMEDIATE_W:
			PUSH(GET_WORD);
			break;

		case I_PUSH_IMMEDIATE_L:
#ifdef ALIGN_WORD
			lvalue = get_long(LONG(cur_code + ip));
#else
			lvalue = *LONG(cur_code + ip);
#endif
			PUSHL(lvalue);
			ip += sizeof(long);
			break;

			/* Floating Point Instructions */

		case I_FLOAT_ADD_L:
			POPF(rval2);
			POPF(rval1);
			rvalue = rval1 + rval2;
			if (ABS(rvalue) > ADA_MAX_REAL)
				raise(NUMERIC_ERROR, "Floating point addition overflow");
			PUSHF(rvalue);
			break;

		case I_FLOAT_SUB_L:
			POPF(rval2);
			POPF(rval1);
			rvalue = rval1 - rval2;
			if (ABS(rvalue) > ADA_MAX_REAL)
				raise(NUMERIC_ERROR, "Floating point subtraction overflow");
			PUSHF(rvalue);
			break;

		case I_FLOAT_MUL_L:
			POPF(rval2);
			POPF(rval1);
			rvalue = rval1 * rval2;
			if (ABS(rvalue) > ADA_MAX_REAL)
				raise(NUMERIC_ERROR, "Floating point multiplication overflow");
			PUSHF(rvalue);
			break;

		case I_FLOAT_DIV_L:
			POPF(rval2);
			POPF(rval1);
			if (rval2 == 0.0)
				raise(NUMERIC_ERROR, "Floating point division by zero");
			else {
				rvalue = rval1 / rval2;
				if (ABS(rvalue) > ADA_MAX_REAL)
					raise(NUMERIC_ERROR, "Floating point division overflow");
			}
			PUSHF(rvalue);
			break;

		case I_FLOAT_COMPARE_L:
			POPF(rval1);
			POPF(rval2);
			value = (rval1 == rval2) + 2 *(rval1 < rval2);
			/* 0 1 2 for < = > */
			PUSH(value);
			break;

		case I_FLOAT_POW_L:
			POP(val2);
			POPF(rval1);
			if (val2 == 0)
				rvalue = 1.0;				/* x ** 0 = 0.0 */
			else if (rval1 == 0.0) {
				if (val2 < 0)				/* 0 ** -x = error */
					raise(NUMERIC_ERROR, "Negative power of zero");
				else
					rvalue = 0.0;/* 0 ** +x = 0.0 */
			}
			else {
				rvalue = rval1;
				for (i = 1; i < ABS(val2); i++) {
					rvalue = rvalue * rval1;
					if (ABS(rvalue) > ADA_MAX_REAL) {
						if (val2 > 0) {
							/* the exception has to be raised only if the
							 * exponent is positive. If it is negative, the
							 * result will converge towards 0
							 */
							raise(NUMERIC_ERROR, "Exponentiation");
							break;
						}
						else { 
							rvalue = 0.0; 
							val2 = 1;
							break ; 
						}
					}
				}
				if (val2 < 0)
					rvalue = 1.0 / rvalue;
			}
			PUSHF(rvalue);
			break;

		case I_FLOAT_NEG_L:
			POPF(rval1);
			rvalue = -rval1;
			PUSHF(rvalue);
			break;

		case I_FLOAT_ABS_L:
			POPF(rval1);
			rvalue = ABS(rval1);
			PUSHF(rvalue);
			break;

			/* Logical and Arithmetic Instructions */

		case I_ADD_B:
			POP(val2);
			POP(val1);
			value = val1 + val2;
			if (value < -128 || value > 127)
				raise(NUMERIC_ERROR, "Overflow");
			else
				PUSH(value);
			break;

		case I_ADD_W:
			POP(val2);
			POP(val1);
			value = word_add(val1, val2, &overflow);
			if (overflow)
				raise(NUMERIC_ERROR, "Overflow");
			else
				PUSH(value);
			break;

		case I_ADD_L:
			POPL(lval2);
			POPL(lval1);
			lvalue = long_add(lval1, lval2, &overflow);
			if (overflow)
				raise(NUMERIC_ERROR, "Overflow");
			else
				PUSHL(lvalue);
			break;

		case I_ADD_IMMEDIATE_B:
			POP(val1);
			val2 = GET_WORD;
			value = val1 + val2;
			if (value < -128 || value > 127)
				raise(NUMERIC_ERROR, "Overflow");
			else
				PUSH(value);
			break;

		case I_ADD_IMMEDIATE_W:
			POP(val1);
			val2 = GET_WORD;
			value = word_add(val1, val2, &overflow);
			if (overflow)
				raise(NUMERIC_ERROR, "Overflow");
			PUSH(value);
			break;

		case I_ADD_IMMEDIATE_L:
			POPL(lval1);
#ifdef ALIGN_WORD
			lval2 = get_long(LONG(cur_code + ip));
#else
			lval2 = *(LONG(cur_code + ip));
#endif
			ip += WORDS_LONG;
			lvalue = long_add(lval1, lval2, &overflow);
			if (overflow)
				raise(NUMERIC_ERROR, "Overflow");
			PUSHL(lvalue);
			break;

		case I_DIV_B:
			POP(val2);
			POP(val1);
			if (val2 == 0)
				raise(NUMERIC_ERROR, "Division by zero");
			else if (val1 == -128 && val2 == -1)
				raise(NUMERIC_ERROR, "Overflow");
			else {
				value = val1 / val2;
				PUSH(value);
			}
			break;

		case I_DIV_W:
			POP(val2);
			POP(val1);
			if (val2 == 0)
				raise(NUMERIC_ERROR, "Division by zero");
			else if (val1 == MIN_INTEGER && val2 == -1)
				raise(NUMERIC_ERROR, "Overflow");
			else {
				value = val1 / val2;
				PUSH(value);
			}
			break;

		case I_DIV_L:
			POPL(lval2);
			POPL(lval1);
			if (lval2 == 0)
				raise(NUMERIC_ERROR, "Division by zero");
			else if (lval1 == MIN_LONG && lval2 == -1)
				raise(NUMERIC_ERROR, "Overflow");
			else {
				lvalue = lval1 / lval2;
				PUSHL(lvalue);
			}
			break;

		case I_REM_B:
		case I_REM_W:
			/*
			 * Remainder Operation
			 * -------------------
			 * 
			 * The modification has been done in order to prevent complex
			 * calculation. The remonder operator of Ada is equivallent to "%"
			 * of C. The modification is straightfoward.
			 * 
			 * NB : The previous program was not satisfying. The first operation
			 * was to transform the second parameter into a positive one. The
			 * assignment "val2 = -val2" can be incorrect if the value is the
			 * first integer (-2 ** 31) since 2**31 is not an integer.
			 */

			POP(val2);
			POP(val1);
			if (val2 == 0)
				raise(NUMERIC_ERROR, "Division by zero");
			else {
				value = val1 % val2;
				PUSH(value);
			}
			break;

		case I_REM_L:
			POPL(lval2);
			POPL(lval1);
			if (lval2 == 0)
				raise(NUMERIC_ERROR, "Division by zero");
			else {
				lvalue = lval1 % lval2;
				PUSHL(lvalue);
			}
			break;

		case I_MOD_B:
		case I_MOD_W:

			/* Modulo Operation
			 * ----------------
			 * 
			 * The idea of the modification is to reduce the complexity of the
			 * calculation. The, modulo can be calculated quite easily if the
			 * first parameter is positive. Therefore if the first parameter is
			 * negative then we calculate the first positive number according
			 * to the following equality:
 			 * a mod b = (a + n*b) mod b
			 */

			POP(val2);
			POP(val1);
			if (val2 == 0)
				raise(NUMERIC_ERROR, "Division by zero");
			else {
				/* the idea is to transform val1 in a positive value.
				 * a mod b = (a + k*b) mod b
				 */
				if ( (val1 <= 0) && ( val2 > 0)) {
					/* val1 = (val1 + (1 - val1/val2)* val2  */
					val1 = val1 - ((val1/val2) * val2) + val2; 
				}
				if ( (val1 <= 0) && ( val2 < 0)) {
					/* val1 = (val1 + (-1 - val1/val2)* val2  */
					val1 = (val1 - val2) - (val1/val2)*val2; 
				}
				if (val2 > 0)
					value = val1 % val2;
				else
					value = (val2 + (val1 % val2)) % val2;
				PUSH(value);
			}
			break;

		case I_MOD_L:
			POPL(lval2);
			POPL(lval1);
			if (lval2 == 0)
				raise(NUMERIC_ERROR, "Division by zero");
			else {
				/* the idea is to transform lval1 in a positive value.
				 * a mod b = (a + k*b) mod b
				 */
				if ( (lval1 <= 0) && ( lval2 > 0)) {
					/* lval1 = (lval1 + (1 - lval1/lval2)* lval2  */
					lval1 = lval1 - ((lval1/lval2) * lval2) + lval2; 
				}
				if ( (lval1 <= 0) && ( lval2 < 0)) {
					/* lval1 = (lval1 + (-1 - lval1/lval2)* lval2  */
					lval1 = (lval1 - lval2) - (lval1/lval2)*lval2; 
				}
				if (lval2 > 0)
					lvalue = lval1 % lval2;
				else
					lvalue = (lval2 + (lval1 % lval2)) % lval2;
				PUSHL(lvalue);
			}
			break;

		case I_MUL_B:
			POP(val2);
			POP(val1);
			value = val1 * val2;
			if (value < -128 || value > 127)
				raise(NUMERIC_ERROR, "Overflow");
			else
				PUSH(value);
			break;

		case I_MUL_W:
			POP(val2);
			POP(val1);
			value = word_mul(val1, val2, &overflow);
			if (overflow)
				raise(NUMERIC_ERROR, "Overflow");
			PUSH(value);
			break;

		case I_MUL_L:
			POPL(lval2);
			POPL(lval1);
			lvalue = long_mul(lval1, lval2, &overflow);
			if (overflow)
				raise(NUMERIC_ERROR, "Overflow");
			PUSHL(lvalue);
			break;

		case I_POW_B:
			POP(val2);
			POP(val1);
			if (val2 < 0)
				raise(NUMERIC_ERROR, "Overflow");
			else if (val2 == 0)
				value = 1;
			else {
				value = val1;
				for (i = 1; i < val2; i++) {
					value = value * val1;
					if (value > 127)
						raise(NUMERIC_ERROR, "Overflow");
				}
			}
			PUSH(value);
			break;

		case I_POW_W:
			POP(val2);
			POP(val1);
			if (val2 < 0)
				raise(NUMERIC_ERROR, "Overflow");
			else if (val2 == 0)
				value = 1;
			else
				value = val1;
			for (i = 1; i < val2; i++) {
				value = word_mul(value, val1, &overflow);
				if (overflow)
					raise(NUMERIC_ERROR, "Overflow");
			}
			PUSH(value);
			break;

		case I_POW_L:
			POPL(lval2);
			POPL(lval1);
			if (lval2 < 0)
				raise(NUMERIC_ERROR, "Overflow");
			else if (lval2 == 0)
				lvalue = 1;
			else {
				lvalue = lval1;
				for (i = 1; i < lval2; i++) {
					lvalue = long_mul(lvalue, lval1, &overflow);
					if (overflow)
						raise(NUMERIC_ERROR, "Overflow");
				}
			}
			PUSHL(lvalue);
			break;

		case I_FIX_MUL:
			POP_ADDR(bas1, off1);/* type and value of op2 */
			ptr2 = ADDR(bas1, off1);
			POPL(fval2);

			POP_ADDR(bas1, off1);/* type and value of op1 */
			ptr1 = ADDR(bas1, off1);
			POPL(fval1);

			POP_ADDR(bas1, off1);/* result type */
			ptr = ADDR(bas1, off1);

			if (fval2 == 0 || fval1 == 0) {
				fvalue = 0;
				PUSHL(fvalue);
			}
			else {
				to_type = TYPE(ptr);
				if (to_type == TT_FX_RANGE) {

					sgn  = SIGN(fval1);
					fval1 = ABS(fval1);
					sgn *= SIGN(fval2);
					fval2 = ABS(fval2);
					int_tom(fix_val1,fval1);
					int_tom(fix_val2,fval2);

					temp_template->small_exp_2 = FX_RANGE(ptr1)->small_exp_2 +
					  FX_RANGE(ptr2)->small_exp_2;
					temp_template->small_exp_5 = FX_RANGE(ptr1)->small_exp_5 +
					  FX_RANGE(ptr2)->small_exp_5;

					int_mul(fix_val1, fix_val2, fix_resu);
					fix_convert(fix_resu, temp_template, FX_RANGE(ptr));
					fvalue = int_tol(fix_resu);
					if (arith_overflow)
						raise(NUMERIC_ERROR,
						  "Fixed point multiplication overflow");
					if (fix_out_of_bounds(fvalue, ptr))
						raise(CONSTRAINT_ERROR,
						  "Fixed point value out of bounds");
					PUSHL(sgn*fvalue);
				}
				else
					raise(SYSTEM_ERROR, "Conversion to invalid type");
			}
			break;

		case I_FIX_DIV:
			POP_ADDR(bas1, off1);/* type and value of op2 */
			ptr2 = ADDR(bas1, off1);
			POPL(fval2);

			POP_ADDR(bas1, off1);/* type and value of op1 */
			ptr1 = ADDR(bas1, off1);
			POPL(fval1);

			POP_ADDR(bas1, off1);/* result type */
			ptr = ADDR(bas1, off1);

			if (fval2 == 0) {
				raise(NUMERIC_ERROR, "Fixed point division by zero");
				fvalue = 0;
				PUSHL(fvalue);
			}
			else {
				to_type = TYPE(ptr);
				if (to_type == TT_FX_RANGE) {

					sgn  = SIGN(fval1);
					fval1 = ABS(fval1);
					sgn *= SIGN(fval2);
					fval2 = ABS(fval2);
					int_tom(fix_val1,fval1);
					int_tom(fix_val2,fval2);

					temp_template->small_exp_2 = FX_RANGE(ptr)->small_exp_2 +
					  FX_RANGE(ptr2)->small_exp_2;
					temp_template->small_exp_5 = FX_RANGE(ptr)->small_exp_5 +
					  FX_RANGE(ptr2)->small_exp_5;

					fix_convert(fix_val1, FX_RANGE(ptr1), temp_template);
					int_div(fix_val1, fix_val2, fix_resu);
					fvalue = int_tol(fix_resu);
					if (arith_overflow)
						raise(NUMERIC_ERROR, "Fixed point division overflow");
					if (fix_out_of_bounds(fvalue, ptr))
						raise(CONSTRAINT_ERROR,
						  "Fixed point value out of bounds");
					PUSHL(sgn*fvalue);
				}
				else
					raise(SYSTEM_ERROR, "Conversion to invalid type");
			}
			break;

		case I_CONVERT_TO_L:
			GET_LAD(bse, off);
			convert(bse, off);
			break;

		case I_CONVERT_TO_G:
			GET_GAD(bse, off);
			convert(bse, off);
			break;

		case I_NEG_B:
			if (TOS == -128)
				raise(NUMERIC_ERROR,"Byte overflow");
			else
				TOS = -TOS;
			break;

		case I_NEG_W:
			if (TOS == MIN_INTEGER)
				raise(NUMERIC_ERROR,"Overflow");
			else
				TOS = -TOS;
			break;

		case I_NEG_L:
			if (TOS == MIN_LONG)
				raise(NUMERIC_ERROR,"Overflow");
			else
				TOSL = -TOSL;
			break;

		case I_ABS_B:
			if (TOS == -128)
				raise(NUMERIC_ERROR,"Byte overflow");
			else
				TOS = ABS(TOS);
			break;

		case I_ABS_W:
			if (TOS == MIN_INTEGER)
				raise(NUMERIC_ERROR,"Overflow");
			else
				TOS = ABS(TOS);
			break;

		case I_ABS_L:
			if (TOS == MIN_LONG)
				raise(NUMERIC_ERROR,"Overflow");
			else
				TOSL = ABS(TOSL);
			break;

		case I_NOT:
			TOS = 1 - TOS;
			break;

		case I_AND:
			POP(val2);
			POP(val1);
			value = (val1 & val2);
			PUSH(value);
			break;

		case I_XOR:
			POP(val2);
			POP(val1);
			value = (val1 ^ val2);
			PUSH(value);
			break;

		case I_OR:
			POP(val2);
			POP(val1);
			value = (val1 | val2);
			PUSH(value);
			break;

		case I_IS_EQUAL:
			TOS = (TOS == 1);
			break;

		case I_IS_GREATER:
			TOS = (TOS == 2);
			break;

		case I_IS_GREATER_OR_EQUAL:
			TOS = (TOS >= 1);
			break;

		case I_IS_LESS:
			TOS = (TOS == 0);
			break;

		case I_IS_LESS_OR_EQUAL:
			TOS = (TOS <= 1);
			break;

		case I_MEMBERSHIP:
			membership();
			break;

		case I_QUAL_RANGE_G:
			GET_GAD(bse, off);
			ptr1 = ADDR(bse, off);
			if (TYPE(ptr1) == TT_FX_RANGE) {
				if (fix_out_of_bounds(TOSL, ptr1))
					raise(CONSTRAINT_ERROR, "Fixed point value out of bounds");
			}
			else if (TYPE(ptr1) == TT_FL_RANGE) {
				rval1 = FL_RANGE(ptr1)->fllow;
				rval2 = FL_RANGE(ptr1)->flhigh;
				if (TOSF < rval1 || TOSF > rval2)
					raise(CONSTRAINT_ERROR,
					  "Floating point value out of bounds");
			}
			else if ((TYPE(ptr1) == TT_I_RANGE) ||
			    (TYPE(ptr1) == TT_E_RANGE) ||
			    (TYPE(ptr1) == TT_ENUM)) {
				val_low = I_RANGE(ptr1)->ilow;
				val_high = I_RANGE(ptr1)->ihigh;
				if (TOS < val_low || TOS > val_high)
					raise(CONSTRAINT_ERROR, "Out of bounds");
			}
#ifdef LONG_INT
			else if (TYPE(ptr1) == TT_L_RANGE) {
				lvalue = TOSL;
				lval_low = L_RANGE(ptr1)->llow;
				lval_high = L_RANGE(ptr1)->lhigh;
				if (lvalue < lval_low || lvalue > lval_high)
					raise (CONSTRAINT_ERROR, "Out of bounds");
			}
#endif
			else	/* error here */
				;
			break;

		case I_QUAL_RANGE_L:
			GET_LAD(bse, off);
			ptr1 = ADDR(bse, off);
			if (TYPE(ptr1) == TT_FX_RANGE) {
				fval1 = TOSL;
				if (fix_out_of_bounds(fval1, ptr1))
					raise(CONSTRAINT_ERROR, "Fixed point value out of bounds");
			}
			else if (TYPE(ptr1) == TT_FL_RANGE) {
				rvalue = TOSF;
				rval1 = FL_RANGE(ptr1)->fllow;
				rval2 = FL_RANGE(ptr1)->flhigh;
				if (rvalue < rval1 || rvalue > rval2)
					raise(CONSTRAINT_ERROR,
					  "Floating point value out of bounds");
			}
			else if ((TYPE(ptr1) == TT_I_RANGE) ||
			    (TYPE(ptr1) == TT_E_RANGE) ||
			    (TYPE(ptr1) == TT_ENUM)) {
				val_low = I_RANGE(ptr1)->ilow;
				val_high = I_RANGE(ptr1)->ihigh;
				if (TOS < val_low || TOS > val_high)
					raise(CONSTRAINT_ERROR, "Out of bounds");
			}
#ifdef LONG_INT
			else if (TYPE(ptr1) == TT_L_RANGE) {
				lvalue = TOSL;
				lval_low = L_RANGE(ptr1)->llow;
				lval_high = L_RANGE(ptr1)->lhigh;
				if (lvalue < lval_low || lvalue > lval_high)
					raise (CONSTRAINT_ERROR, "Out of bounds");
			}
#endif
			else	/* error here */
				;
			break;

		case I_QUAL_DISCR_G:
			GET_GAD(bse, off);
			qual_discr(bse, off);
			break;

		case I_QUAL_DISCR_L:
			GET_LAD(bse, off);
			qual_discr(bse, off);
			break;

		case I_QUAL_INDEX_G:
			GET_GAD(bse, off);
			ptr = ADDR(bse, off);
			POP_ADDR(bse, off);
			PUSH_ADDR(bse, off);
			ptr1 = ADDR(bse, off);
			if (!qual_index(ptr, ptr1))
				raise(CONSTRAINT_ERROR, "Wrong bounds");
			break;

		case I_QUAL_INDEX_L:
			GET_LAD(bse, off);
			ptr = ADDR(bse, off);
			POP_ADDR(bse, off);
			PUSH_ADDR(bse, off);
			ptr1 = ADDR(bse, off);
			if (!qual_index(ptr, ptr1))
				raise(CONSTRAINT_ERROR, "Wrong bounds");
			break;

		case I_QUAL_SUB_G:
			GET_GAD(bse, off);
			ptr = ADDR(bse, off);
			POP_ADDR(bse, off);
			PUSH_ADDR(bse, off);
			ptr1 = ADDR(bse, off);
			if (!qual_sub(ptr, ptr1))
				raise(CONSTRAINT_ERROR, "Wrong bounds");
			break;

		case I_QUAL_SUB_L:
			GET_LAD(bse, off);
			ptr = ADDR(bse, off);
			POP_ADDR(bse, off);
			PUSH_ADDR(bse, off);
			ptr1 = ADDR(bse, off);
			if (!qual_sub(ptr, ptr1))
				raise(CONSTRAINT_ERROR, "Wrong bounds");
			break;

		case I_SUB_B:
			POP(val2);
			POP(val1);
			value = val1 - val2;
			if (value < -128 || value > 127)
				raise(NUMERIC_ERROR, "Overflow");
			else
				PUSH(value);
			break;

		case I_SUB_W:
			POP(val2);
			POP(val1);
			value = word_sub(val1, val2, &overflow);
			if (overflow)
				raise(NUMERIC_ERROR, "Overflow");
			else
				PUSH(value);
			break;

		case I_SUB_L:
			POPL(lval2);
			POPL(lval1);
			lvalue = long_sub(lval1, lval2, &overflow);
			if (overflow)
				raise(NUMERIC_ERROR, "Overflow");
			else
				PUSHL(lvalue);
			break;

			/* Array Instructions */

		case I_ARRAY_CATENATE:
			array_catenate();
			break;

		case I_ARRAY_MOVE:
			array_move();
			break;

		case I_ARRAY_SLICE:
			array_slice();
			break;

		case I_ARRAY_AND:
			POP_ADDR(bas1, off1);/* right type */
			POP_ADDR(bas2, off2);/* right object */
			POP_ADDR(bse, off);/* left type */
			value = SIZE(ADDR(bse, off));
			if (SIZE(ADDR(bas1, off1)) != value)
				raise(CONSTRAINT_ERROR, "Arrays not same size for AND");
			else {
				POP_ADDR(bas1, off1);/* left object */
				ptr1 = ADDR(bas1, off1);
				ptr2 = ADDR(bas2, off2);
				create(value, &bas1, &off1, &ptr);
				for (i = 0; i <= value - 1; i++)
					*ptr++ = (*ptr1++ & *ptr2++);
				PUSH_ADDR(bas1, off1);/* result object */
				PUSH_ADDR(bse, off);/* result type */
			}
			break;

		case I_ARRAY_OR:
			POP_ADDR(bas1, off1);/* right type */
			POP_ADDR(bas2, off2);/* right object */
			POP_ADDR(bse, off);/* left type */
			value = SIZE(ADDR(bse, off));
			if (SIZE(ADDR(bas1, off1)) != value)
				raise(CONSTRAINT_ERROR, "Arrays not same size for OR");
			else {
				POP_ADDR(bas1, off1);/* left object */
				ptr1 = ADDR(bas1, off1);
				ptr2 = ADDR(bas2, off2);
				create(value, &bas1, &off1, &ptr);
				for (i = 0; i <= value - 1; i++)
					*ptr++ = (*ptr1++ | *ptr2++);
				PUSH_ADDR(bas1, off1);/* result object */
				PUSH_ADDR(bse, off);/* result type */
			}
			break;

		case I_ARRAY_XOR:
			POP_ADDR(bas1, off1);/* right type */
			POP_ADDR(bas2, off2);/* right object */
			POP_ADDR(bse, off);/* left type */
			value = SIZE(ADDR(bse, off));
			if (SIZE(ADDR(bas1, off1)) != value)
				raise(CONSTRAINT_ERROR, "Arrays not same size for XOR");
			else {
				POP_ADDR(bas1, off1);/* left object */
				ptr1 = ADDR(bas1, off1);
				ptr2 = ADDR(bas2, off2);
				create(value, &bas1, &off1, &ptr);
				for (i = 0; i <= value - 1; i++) {
					*ptr++ = (*ptr1++ ^ *ptr2++);
				}
				PUSH_ADDR(bas1, off1);/* result object */
				PUSH_ADDR(bse, off);/* result type */
			}
			break;

		case I_ARRAY_NOT:
			POP_ADDR(bse, off);/* type */
			value = SIZE(ADDR(bse, off));
			POP_ADDR(bas1, off1);/* object */
			ptr1 = ADDR(bas1, off1);
			create(value, &bas1, &off1, &ptr);
			for (i = 0; i <= value - 1; i++)
				*ptr++ = (1 - *ptr1++);
			PUSH_ADDR(bas1, off1);/* result object */
			PUSH_ADDR(bse, off);/* result type */
			break;

			/* Record Instructions */

		case I_RECORD_MOVE_G:
			GET_GAD(bse, off);
			ptr = ADDR(bse, off);
			POP_ADDR(bas1, off1);/* value */
			ptr1 = ADDR(bas1, off1);
			POP_ADDR(bas2, off2);/* object */
			ptr2 = ADDR(bas2, off2);
			record_move(ptr2, ptr1, ptr);
			break;

		case I_RECORD_MOVE_L:
			GET_LAD(bse, off);
			ptr = ADDR(bse, off);
			POP_ADDR(bas1, off1);/* value */
			ptr1 = ADDR(bas1, off1);
			POP_ADDR(bas2, off2);/* object */
			ptr2 = ADDR(bas2, off2);
			record_move(ptr2, ptr1, ptr);
			break;

			/* Attributes */

		case I_ATTRIBUTE:
			attribute = GET_BYTE;
			/* So that all reads from code segment are done in this
			 * procedure, we retrieve the dim argument used for
			 * some attributes
			 */
			if (attribute==ATTR_O_FIRST || attribute==ATTR_O_LAST
			  || attribute == ATTR_O_LENGTH || attribute==ATTR_O_RANGE)
				value = GET_WORD;
			else
				value = 0;
			main_attr(attribute,value);
			break;

			/* Control Instructions */

		case I_ENTER_BLOCK:
#ifdef DEBUG_TASKING
			if (tasking_trace)
				printf("enter block pushing %d for previous\n",bfp);
#endif
			PUSH(bfp);	/* save previous BFP */
			bfp = cur_stackptr;
#ifdef DEBUG_TASKING
			if (tasking_trace)
				printf("enter block bfp %d\n",bfp);
#endif
			PUSHP(0L);	/* data_link */
			PUSHP(0L);        /* tasks_declared */
			PUSH(1);	/* num noterm */
			PUSH(1);	/* num deps */
			PUSH(NULL_TASK);/* subtasks */
			PUSH(0);	/* exception vector */
			break;

		case I_EXIT_BLOCK:
#ifdef DEBUG_TASKING
			if (tasking_trace) {
#ifdef IBM_PC
				printf("exit block bfp %d %p\n",bfp,cur_stack+bfp);
#else
				printf("exit block bfp %d %ld\n",bfp,cur_stack+bfp);
#endif
			}
#endif
			if (BLOCK_FRAME->bf_num_deps >= 1) {
				--ip;	/* to reexecute the 'leave_block' */
				complete_block();
			}
			else {
				deallocate(BLOCK_FRAME->bf_data_link);
				sp = BLOCK_FRAME->bf_previous_bfp;
				if ((tfptr1 = BLOCK_FRAME->bf_tasks_declared) != 0) {
					bfptr = (struct bf *)(&cur_stack[sp]);
					tfptr2 = bfptr->bf_tasks_declared;
					if (tfptr2 != 0) {
						value = pop_task_frame();
						*tfptr2 = union_tasks_declared(value, *tfptr2);
					}
					else	/* put task frame on previous bfp */
						bfptr->bf_tasks_declared = tfptr1;
				}
				cur_stackptr = bfp - 1;
				bfp = sp;
#ifdef DEBUG_TASKING
				if (tasking_trace)
					printf("exit block setting bfp %d\n",bfp);
#endif
			}
			break;

		case I_LEAVE_BLOCK:
#ifdef DEBUG_TASKING
			if (tasking_trace) {
#ifdef IBM_PC
				printf("leave block bfp %d %p\n",bfp,cur_stack+bfp);
#else
				printf("leave block bfp %d %ld\n",bfp,cur_stack+bfp);
#endif
			}
#endif
			if (BLOCK_FRAME->bf_num_deps >= 1) {
				--ip;	/* to reexecute the 'leave_block' */
				complete_block();
			}
			else {
				deallocate(BLOCK_FRAME->bf_data_link);
				sp = BLOCK_FRAME->bf_previous_bfp;
				if ((tfptr1 = BLOCK_FRAME->bf_tasks_declared) != 0) {
					bfptr = (struct bf *)(&cur_stack[sp]);
					tfptr2 = bfptr->bf_tasks_declared;
					if (tfptr2 != 0) {
						value = pop_task_frame();
						*tfptr2 = union_tasks_declared(value, *tfptr2);
					}
					else	/* put task frame on previous bfp */
						bfptr->bf_tasks_declared = tfptr1;
				}
				if (sp < sfp) {/* return to previous stack_frame */
					cur_stackptr = sfp - 1;/* get rid of the relay set */
					/* in case an exception is propagated, ip */
					/* must point again to the default handler */
#ifdef ALIGN_WORD
					val2 = get_int((int *)(cur_code + code_seglen[cs] 
					  - sizeof(int) - 1));
#else
					val2 = *(int *)(cur_code+code_seglen[cs] - sizeof(int) - 1);
#endif
					/* length of local variables */
					if (ip < 2) {
						--cur_stackptr;/* to discard it */
#ifdef TRACE
						if (call_trace)
							printf("abandoning %s\n", code_slots[cs]);
#endif
					}
					else {
						POP(ip);
#ifdef TRACE
						if (call_trace) {
							if (code_slots[cs])
								printf("returning from %s (tos %d)\n",
								  code_slots[cs],cur_stackptr- 3-val2);
							else 
								printf("returning from %s (tos %d)\n", 
								  "compiler_generated_procedure",
								  cur_stackptr-3-val2);
						}
#endif
					}
					POP(lin);
					POP(cs);
					cur_code = code_segments[cs];
					POP(sfp);
					cur_stackptr -= val2;/* to get rid of it */
				}
				else
					cur_stackptr = bfp - 1;
				bfp = sp;
#ifdef DEBUG_TASKING
				if (tasking_trace)
					printf("leave block setting bfp %d\n",bfp);
#endif
			}
			break;

		case I_CALL_L:
			GET_LAD(bse, off);/* addr of proc. object */
			ptr = ADDR(bse, off);
			value = *ptr;
			if (value < 0)
				raise(PROGRAM_ERROR, "Access before elaboration");
			else {
				if (cur_stackptr+SECURITY_LEVEL>new_task_size)
					raise(STORAGE_ERROR, "Stack overflow");
				else {
					old_cs = cs;
					cs = value;
#ifdef TRACE
					if (call_trace) {
						if (code_slots[cs])
							printf("calling %s (tos %d -> ",
							  code_slots[cs],cur_stackptr);
						else 
							printf("calling %s (tos %d -> ",
							  "compiler_generated_procedure", cur_stackptr);
					}
#endif
					cur_code = code_segments[cs];
#ifdef ALIGN_WORD
					val1 = get_int((int *)(cur_code + code_seglen[cs] 
					  - sizeof(int) - 1));
#else
					val1 = *(int *)(cur_code+code_seglen[cs] - sizeof(int) - 1);
#endif
					/* reserve space for locals */
					if (val1 < 0)
						raise(SYSTEM_ERROR, "Negative size of locals");
					else
						cur_stackptr += val1;
					PUSH(sfp);
					PUSH(old_cs);
					PUSH(lin);
					PUSH(ip);
					sfp = cur_stackptr + 1;
					ip = 2;
					val2 = *(++ptr) * 2;/* length of relay set */
					for (i = 1; i <= val2; i++)			/* copy relay set */
						PUSH(*++ptr);
#ifdef TRACE
					if(call_trace)
						printf("%d)\n",cur_stackptr);
#endif
				}
			}
			break;

		case I_CALL_G:
			GET_GAD(bse, off);/* addr of proc. object */
			ptr = ADDR(bse, off);
			value = *ptr;
			if (value < 0)
				raise(PROGRAM_ERROR, "Access before elaboration");
			else {
				if (cur_stackptr+SECURITY_LEVEL>new_task_size)
					raise(STORAGE_ERROR, "Stack overflow");
				else {
					old_cs = cs;
					cs = value;
#ifdef TRACE
					if (call_trace) {
						if (code_slots[cs])
							printf("calling %s (tos %d -> ",
							  code_slots[cs],cur_stackptr);
						else 
							printf("calling %s (tos %d -> ",
							  "compiler_generated_procedure", cur_stackptr);
					}
#endif
					cur_code = code_segments[cs];
					/* reserve space for local variables */
#ifdef ALIGN_WORD
					val1 = get_int((int *)(cur_code + code_seglen[cs] 
					  - sizeof(int) - 1));
#else
					val1 = *(int *)(cur_code+code_seglen[cs] - sizeof(int) - 1);
#endif
					/* reserve space for locals */
					if (val1 < 0)
						raise(SYSTEM_ERROR, "Negative size of locals");
					else
						cur_stackptr += val1;
					PUSH(sfp);
					PUSH(old_cs);
					PUSH(lin);
					PUSH(ip);
					sfp = cur_stackptr + 1;
					ip = 2;
					/* copy relay set */
					val2 = *(++ptr) * 2;/* length of relay set */
					for (i = 1; i <= val2; i++)			/* copy relay set */
						PUSH(*++ptr);
#ifdef TRACE
					if(call_trace)
						printf("%d)\n",cur_stackptr);
#endif
				}
			}
			break;

		case I_CALL_PREDEF:
			operation = GET_BYTE;
			predef();
			break;

#ifdef INTERFACE
		case I_CALL_INTERFACE: 
			interface(GET_WORD);
			break;
#endif

		case I_CASE_B:
		case I_CASE_W:
		case I_CASE_L:
			POP(value);
			nb = GET_WORD;
			jump = GET_WORD;
			for (i = 1; i <= nb; i++) {
				val_high = GET_WORD;
				if (value < val_high)
					break;
				jump = GET_WORD;
			}
			ip = jump;
			break;

		case I_RETURN_B:
		case I_RETURN_W:
			POP(value);
			cur_stack[sfp + GET_WORD] = value;
			break;

		case I_RETURN_L:
			POPL(lvalue);
			*(LONG(&cur_stack[sfp + GET_WORD])) = lvalue;
			break;

		case I_RETURN_A:
			POP_ADDR(bse, off);
			sp = GET_WORD + sfp;
			cur_stack[sp] = bse;
			cur_stack[sp + 1] = off;
			break;

		case I_RETURN_STRUC:
			sp = GET_WORD + sfp;
			POP_ADDR(bse, off);/* 	type */
			ptr = ADDR(bse, off);
			POP_ADDR(bas2, off2);/* value */
			ptr2 = ADDR(bas2, off2);

			val1 = TYPE(ptr);/* type of type */
			val2 = SIZE(ptr);
			allocate(val2, &bas1, &off1, &ptr1);
			cur_stack[sp] = bas1;
			cur_stack[sp + 1] = off1;

			for (i = 0; i < val2; i++)
				*ptr1++ = *ptr2++;

			switch(val1) {
			case TT_U_ARRAY:
			case TT_C_ARRAY:
			case TT_S_ARRAY:
			case TT_D_ARRAY:
				if (bse >= heap_base) {/* non static template */
					/* create new type template */
					/* size of template */
					val2 = *(ptr -  WORDS_HDR) - WORDS_HDR;
					allocate(val2, &bse, &off, &ptr1);

					for (i = 0; i < val2; i++)
						*ptr1++ = *ptr++;
				}
				cur_stack[sp + 2] = bse;
				cur_stack[sp + 3] = off;
				break;

			case TT_RECORD:
			case TT_U_RECORD:
			case TT_C_RECORD:
			case TT_D_RECORD:
			case TT_V_RECORD:
				break;
			}
			break;

		case I_END_FOR_LOOP_B:
		case I_END_FOR_LOOP_W:
		case I_END_FOR_LOOP_L:
			val2 = GET_WORD;
			off = TOS;
			bse = TOSM(1);
			lim = TOSM(2);
			value = *ADDR(bse, off);
			if (value >= lim) {
				POP_ADDR(bse, off);
				POP(val1);
			}
			else {
				*ADDR(bse, off) = value + 1;
				ip = val2;
			}
			break;

		case I_END_FORREV_LOOP_B:
		case I_END_FORREV_LOOP_W:
		case I_END_FORREV_LOOP_L:
			val2 = GET_WORD;
			off = TOS;
			bse = TOSM(1);
			lim = TOSM(2);
			value = *ADDR(bse, off);
			if (value <= lim) {
				POP_ADDR(bse, off);
				POP(val1);
			}
			else {
				*ADDR(bse, off) = value - 1;
				ip = val2;
			}
			break;

		case I_JUMP:
			val2 = GET_WORD;
			ip = val2;
			break;

		case I_JUMP_IF_FALSE:
			val2 = GET_WORD;
			POP(value);
			if (BOOL(value) == 0)
				ip = val2;
			break;

		case I_JUMP_IF_TRUE:
			val2 = GET_WORD;
			POP(value);
			if (BOOL(value) == 1)
				ip = val2;
			break;

		case I_JUMP_IF_GREATER:
			val2 = GET_WORD;
			POP(value);
			if (value == 2)
				ip = val2;
			break;

		case I_JUMP_IF_GREATER_OR_EQUAL:
			val2 = GET_WORD;
			POP(value);
			if (value >= 1)
				ip = val2;
			break;

		case I_JUMP_IF_LESS:
			val2 = GET_WORD;
			POP(value);
			if (value == 0)
				ip = val2;
			break;

		case I_JUMP_IF_LESS_OR_EQUAL:
			val2 = GET_WORD;
			POP(value);
			if (value <= 1)
				ip = val2;
			break;

			/* Miscellanous Instructions */

		case I_LOAD_EXCEPTION_REGISTER:
			exr = GET_WORD;
			raise_cs = cs;
			raise_lin = lin;
			raise_reason = "Instruction";
			break;

		case I_INSTALL_HANDLER:
			BLOCK_FRAME->bf_handler = GET_WORD;
			break;

		case I_RAISE:
			raise(exr, "");
			break;

		case I_RESTORE_STACK_POINTER:
			sp = GET_WORD + sfp;
			sp = cur_stack[sp];
			cur_stackptr = sp;
			break;

		case I_SAVE_STACK_POINTER:
			sp = GET_WORD + sfp;
			cur_stack[sp] = cur_stackptr;
			break;

		case I_STMT:
			lin = GET_WORD;
#ifdef TRACE
			if (line_trace)
				printf("at line %d (tos %d)\n",lin,cur_stackptr);
#endif
			break;

		case I_SUBSCRIPT:
			subscript();
			break;

		case I_SELECT:
			value = GET_WORD; /* retrieve parameter for select */
			rselect(value);
			break;

		case I_TEST_EXCEPTION_REGISTER:
			PUSH(exr == GET_WORD);
			break;

		case I_TYPE_LOCAL:
			GET_GAD(bse, off);
			type_elaborate(1,bse,off);
			break;

		case I_TYPE_GLOBAL:
			GET_GAD(bse, off);
			type_elaborate(0,bse,off);
			break;

		case I_SUBPROGRAM:
			GET_LAD(bse,off);
			subprogram(bse,off);
			break;

		case I_CHECK_REC_SUBTYPE:
			POP_ADDR(bse, off);
			check_subtype_with_discr (ADDR (bse, off), NULL_INT);
			break;

		default:
			raise(SYSTEM_ERROR, "Bad opcode");

		}			/* end switch on operation code */
	}				/* end loop through instructions */
}					/* end main_loop procedure */

#ifdef DEBUG_INT
static int get_word()			/*;get_word*/
{
	int     w;
	w = *((int *)(cur_code + ip));
	ip += sizeof(int);
	return w;
}

#endif
#ifdef ALIGN_WORD
int get_int(int *n)										/*;get_int*/
{
	register int i;
	int v;
	register char *sp,*tp;

	sp = (char *) n;
	tp = (char *) &v;
	for (i=0; i<sizeof(int); i++) *tp++ = *sp++;
	return v;
}

long get_long(long *n)								/*;get_long*/
{
	register int i;
	long v;
	register char *sp,*tp;

	sp = (char *) n;
	tp = (char *) &v;
	for (i=0; i<sizeof(long); i++) *tp++ = *sp++;
	return v;
}

static int get_word()									/*;get_word*/
{
	/* if integers must be aligned, get byte by byte */
	int w,i;
	char *sp,*tp;
	sp = (char *) ((int *)(cur_code+ip));
	ip += sizeof(int);
	tp = (char *) &w;
	for (i=0; i<sizeof(int); i++)
		*tp++ = *sp++;
	return w;
}
#endif

int allocate_new_heap()								/*;allocate_new_heap*/
{
	/* This procedure attempts to allocate a new heap.
	 * It returns 1 if it succeeds, 0 otherwise.
	 * The size of the heap is defined by max_mem (see config.h).
	 */

	char *temporary;

	/* First tries to reallocate data_segments.  */
	temporary = realloc(data_segments,
	  (data_segments_dim + 2) * sizeof(char **));
	if(temporary == (char *)0) return 0;
	data_segments = (int **)temporary;

	/* Now tries to allocate the new heap. */
	temporary = malloc((unsigned) max_mem * sizeof(int));
	if(temporary == (char *)0) return 0;

	/* Everything ok: increment data_segments_dim and set heap_base,
	 * heap_addr and heap_next.
	 */
	heap_addr = (int *)temporary;
	heap_base = ++data_segments_dim;
	data_segments[heap_base] = heap_addr;
	heap_next = heap_addr;
#ifdef DEBUG_STORES
	heap_store_addr = heap_addr;
#endif
	return 1;
}

#ifdef DEBUG_INT
static void zbreak(int before)							            /*;zbreak*/
{
	break_point = before;
}
#endif
