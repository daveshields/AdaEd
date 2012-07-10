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
#include "ops.h"
#include "genop.h"
#include "genprots.h"
#include "peepprots.h"

static void code_stack_copy(Op, Op);
static int code_same_arg(Op, Op);
static void flush(int);
static int remov(int);

extern int peep_option; /* defined in gmain.c */

#define STACK_DEPTH 50
#define MATCH(v) (code_stack[index-1].op_code == v)

static Op_s code_stack[STACK_DEPTH + 1]; /* stack of instructions */
static int tos = 0;						 /* top of stack for peep-hole */

/*
 *           P E E P - H O L E   O P T I M I Z E R
 *
 * Algorithm: keep a array of instructions to be optimized in the 
 *            global array code_stack. The global variable tos is
 *            the index of the last instruction entered in the array.
 *
 * The algorithm proceeds in three steps:
 *
 * 1/ check if the array is full and take the appropriate action.
 *    Add the new opcode in the array and increment tos.
 *
 * 2/ loop over the list of codes, using the local variable index
 *    as a pointer to the current instruction.
 *
 *    If an optimization is performed, index is set to point to 
 *    the last untouched instruction or to the first instruction
 *    in the array (0 is not used). At the end of the loop, it
 *    is incremented. If an optimization is performed, index may
 *    be decremented by 1 or left untouched. It is incremented
 *    by 1 otherwise. The loop stops when index points to the last
 *    instruction entered in the array. Note: it is essential that
 *    index verifies the following relation on entry of the loop:
 *                       2 <= index < tos
 *    As a consequence, index must be at least 1 on exit of the loop.
 *
 *    If an instruction is garanteed to prevent any further
 *    optimization, all the instructions which preceed are flushed.
 *    This instruction is kept in the array for the shake of the 
 *    'fence post effect'. (I_NOT followed by I_JUMP_IF_FALSE would
 *    not be catched otherwise).
 *
 * 3/ if the last instruction added to the array was I_END, flush
 *    the list and reset tos to 0.
 *
 */

void peep_hole(Op next)											/*;peep_hole*/
{
	int    index; /* index in the array of instructions: 1 < index < tos */
	Op     temp;  /* temporary op_code */
	char *smalloc();

	if (peep_option == 0) { /* if no optimization assemble immediately */
		assemble(next);
		return;
	}

	if (tos == 50)
		flush(10);

	++tos;

	/* put new instruction in the array */
	code_stack_copy(&code_stack[tos], next);
	for(index = ((tos > 2) ? (tos - 1) : 2); index < tos; index++) {

		switch(code_stack[index].op_code) {

#ifdef TBSL
		case(I_POP):
			if(MATCH(I_DEREF)) {
				temp = &code_stack[index-1];
				temp->op_code = I_INDIRECT_POP;
				index = remov(index);
			}
			break;

		case(I_MOVE):
			if(MATCH(I_DEREF)) {
				temp = &code_stack[index-1];
				temp->op_code = I_INDIRECT_MOVE;
				index = remov(index);
			}
			break;
#endif

		case(I_ADD_IMMEDIATE):
			if(MATCH(I_ADD_IMMEDIATE) || MATCH(I_PUSH_IMMEDIATE)) {
				temp = &code_stack[index-1];
				temp->op_arg.arg_int = 
				  (temp->op_arg.arg_int + code_stack[index].op_arg.arg_int);
				index = remov(index);
			}
			/* next is test for integer zero */
			else if (code_stack[index].op_type == OP_INT &&
			    code_stack[index].op_arg.arg_int == 0) {
				index = remov(index);
			}
			break;

		case(I_DEREF):
			if(MATCH(I_PUSH_EFFECTIVE_ADDRESS)) {
				temp = &code_stack[index-1];
				temp->op_code = I_PUSH;
				temp->op_kind = code_stack[index].op_kind;
				index = remov(index);
			}
			break;

		case(I_DISCARD_ADDR):
			if(code_stack[index+1].op_code == I_DISCARD_ADDR) {
				temp = &code_stack[index];
				temp->op_kind += code_stack[index+1].op_kind;
				temp->op_arg.arg_int = temp->op_kind;
				index = remov(index+1);
			}
			else if(code_stack[index].op_kind == 0) {
				index = remov(index);
			}
			else if(MATCH(I_PUSH_EFFECTIVE_ADDRESS)) {
				temp = &code_stack[index];
				temp->op_kind -= 1;
				temp->op_arg.arg_int  -= 1;
				index = remov(index-1);
			}
			else if(MATCH(I_UPDATE)) {
				temp = &code_stack[index];
				temp->op_kind -= 1;
				temp->op_arg.arg_int  -= 1;
				index -= 1;
				code_stack[index].op_code = I_UPDATE_AND_DISCARD;
			}
			break;

		case(I_FLOAT_POW):
			if(MATCH(I_PUSH_IMMEDIATE)) {
				temp = &code_stack[index-1];
				if (temp->op_arg.arg_int == 2) {
					temp->op_code = I_DUPLICATE;
					temp->op_kind = code_stack[index].op_kind;
					code_stack[index].op_code = I_FLOAT_MUL;
				}
			}
			break;

		case(I_PUSH):
			if (MATCH(I_PUSH)
			  && (code_same_arg(&code_stack[index], &code_stack[index-1]))) {
				code_stack[index].op_code = I_DUPLICATE;
			}
			else if(MATCH(I_POP)
			  && (code_same_arg(&code_stack[index], &code_stack[index-1]))) {
				code_stack[index].op_code = I_POP;
				code_stack[index-1].op_code = I_DUPLICATE;
			}
			break;

			case(I_PUSH_EFFECTIVE_ADDRESS):
			if(MATCH(I_UPDATE_AND_DISCARD)
			  && (code_same_arg(&code_stack[index], &code_stack[index-1]))) {
				temp = &code_stack[index-1];
				temp->op_code = I_UPDATE;
				index = remov(index);
			}
			break;

		case(I_POW):
			if(MATCH(I_PUSH_IMMEDIATE)) {
				temp = &code_stack[index-1];
				if (temp->op_type == OP_INT && temp->op_arg.arg_int == 2) {
					temp->op_code = I_DUPLICATE;
					temp->op_kind = code_stack[index].op_kind;
					code_stack[index].op_code = I_MUL;
				}
			}
			break;

		case(I_STMT):
			if (MATCH(I_STMT)) {
				index = remov(index-1);
			}
			break;

		case(I_NOT):
			temp = &code_stack[index+1];
			if(temp->op_code == I_JUMP_IF_FALSE) {
				temp->op_code = I_JUMP_IF_TRUE;
				index = remov(index);
			}
			else if(temp->op_code == I_JUMP_IF_TRUE) {
				temp->op_code = I_JUMP_IF_FALSE;
				index = remov(index);
			}
			else {
				flush(index);
				index = 1;
			}
			break;

		/*
		 * Here follow the instructions for which no optimization
		 * can be attempted. Note: those should not appear in any 
		 * of the preceeding rules.
		 */
		case(I_ABORT):
		case(I_ABS):
		case(I_ACTIVATE):
		case(I_ACTIVATE_NEW):
		case(I_ADD):
		case(I_AND):
		case(I_ALLOCATE):
		case(I_ALLOCATE_COPY):
		case(I_ARRAY_AND):
		case(I_ARRAY_CATENATE):
		case(I_ARRAY_MOVE):
		case(I_ARRAY_NOT):
		case(I_ARRAY_OR):
		case(I_ARRAY_SLICE):
		case(I_ARRAY_XOR):
		case(I_ATTRIBUTE):
		case(I_CALL):
		case(I_CALL_PREDEF):
		case(I_CASE):
		case(I_CASE_TABLE):
		case(I_COMPARE):
		case(I_COMPARE_STRUC):
		case(I_CONVERT_TO):
		case(I_CREATE):
		case(I_CREATE_COPY):
		case(I_CREATE_COPY_STRUC):
		case(I_CREATE_TASK):
		case(I_CURRENT_TASK):
		case(I_DATA):
		case(I_DECLARE):
		case(I_DIV):
		case(I_END_ACTIVATION):
		case(I_END_FOR_LOOP):
		case(I_END_FORREV_LOOP):
		case(I_END_RENDEZVOUS):
		case(I_ENTER_BLOCK):
		case(I_ENTRY_CALL):
		case(I_FIX_MUL):
		case(I_FIX_DIV):
		case(I_FLOAT_ABS):
		case(I_FLOAT_ADD):
		case(I_FLOAT_COMPARE):
		case(I_FLOAT_DIV):
		case(I_FLOAT_MUL):
		case(I_FLOAT_NEG):
		case(I_FLOAT_SUB):
		case(I_INSTALL_HANDLER):
		case(I_IS_EQUAL):
		case(I_IS_GREATER):
		case(I_IS_GREATER_OR_EQUAL):
		case(I_IS_LESS):
		case(I_IS_LESS_OR_EQUAL):
		case(I_JUMP):
		case(I_JUMP_IF_GREATER):
		case(I_JUMP_IF_GREATER_OR_EQUAL):
		case(I_JUMP_IF_LESS):
		case(I_JUMP_IF_LESS_OR_EQUAL):
		case(I_LABEL):
		case(I_LEAVE_BLOCK):
		case(I_LINK_TASKS_DECLARED):
		case(I_LOAD_EXCEPTION_REGISTER):
		case(I_MEMBERSHIP):
		case(I_MOD):
		case(I_MUL):
		case(I_NEG):
		case(I_NOP):
		case(I_OR):
		case(I_POP_TASKS_DECLARED):
		case(I_QUAL_DISCR):
		case(I_QUAL_INDEX):
		case(I_QUAL_RANGE):
		case(I_QUAL_SUB):
		case(I_RAISE_IN_CALLER):
		case(I_RECORD_MOVE):
		case(I_REM):
		case(I_RESTORE_STACK_POINTER):
		case(I_RETURN):
		case(I_RETURN_STRUC):
		case(I_SAVE_STACK_POINTER):
		case(I_SELECT):
		case(I_SELECTIVE_WAIT):
		case(I_SUB):
		case(I_SUBPROGRAM):
		case(I_SUBSCRIPT):
		case(I_TERMINATE):
		case(I_TEST_EXCEPTION_REGISTER):
		case(I_TIMED_ENTRY_CALL):
		case(I_TYPE_GLOBAL):
		case(I_TYPE_LOCAL):
		case(I_UNCREATE):
		case(I_WAIT):
		case(I_XOR):
		case(I_CALL_INTERFACE):
		case(I_COMPARE_ARRAYS):
		case(I_CHECK_REC_SUBTYPE):
			flush(index-1);
			index = 1;
			break;

		default:
			;
		}
	} /* end for */

	if(next->op_code == I_END)
		flush(tos);
}

static void code_stack_copy(Op opnew, Op opold)				/*;code_stack_copy*/
{
	/* copy operation values */
	register int i;
	register char *newc, *old;
	old = (char *) opold;
	newc = (char *) opnew;
	for (i = sizeof(Op_s); i; i--)
		*newc++ = *old++;
}

static int code_same_arg(Op op1, Op op2)					 /*;code_same_arg*/
{
	/* see if operations i1 and i2 in code_stack have same argument */
	if (op1->op_type != op2->op_type)
		return FALSE;

	switch (op1->op_type) {
	case OP_FIX :
		return (op1->op_arg.arg_fix == op2->op_arg.arg_fix);
	case OP_FLT :
		return (op1->op_arg.arg_flt == op2->op_arg.arg_flt);
	case OP_INT :
		return (op1->op_arg.arg_int == op2->op_arg.arg_int);
	case OP_SYM :
		return (op1->op_arg.arg_sym == op2->op_arg.arg_sym);
	}
	return FALSE;
}

static void flush(int n)			                                 /*;flush*/
{
	/* Flush n instructions from the array code_stack and move
	 * the remaining instructions n positions to the beginning
	 * of the array. Note: n should be positive. The global 
	 * variable tos is set accordingly. If the argument is equal
	 * to tos, all the instructions of the array are passed to
	 * assemble and tos is set to 0 (peep-hole called with I_END).
	 */

	int i, j;

	for (i = 1; i <= n; i++)
		assemble(&code_stack[i]);

	for (j = 1, i = n; i++ < tos; j++)
		code_stack_copy(&code_stack[j], &code_stack[i]);

	tos -= n;
}

static int remov(int n)				                                /*;remov*/
{
	/*
	 * Remove the instruction of rank n from the array.
	 * The instructions with greater values of the index, if
	 * any, are shifted one position toward the lower indices.
	 * This function returns the last untouched index or 1.
	 */

	int i;

	for (i = n; i < tos; i++)
		code_stack_copy(&code_stack[i], &code_stack[i+1]);

	tos -= 1;
	return ((n > 1) ? (n-1) : 1);
}
