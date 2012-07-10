/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/* i1_list - list single instruction */

/* Include standard header modules */
#include <stdlib.h>
#include <stdio.h>
#include "config.h"
#include "int.h"
#include "ivars.h"
#include "intaprots.h"
#include "opnameprots.h"
#include "ilistprots.h"

#ifdef DEBUG_FULL_STACK
static void stdump(int);
#endif
static unsigned int dump_byte(int *, char *);
static int dump_word(int *, char *);
static void dump_gad(int *, char *);

#define DUMP_BYTE dump_byte(ip, curcode)
#define DUMP_WORD dump_word(ip, curcode)
#define DUMP_LAD  dump_word(ip, curcode)
#define DUMP_GAD  dump_gad(ip, curcode)

void i_list1(int *ip, char *curcode)							/*;i_list1*/
{

	unsigned int     opcode;
	int     jump, fjump;
	long    lvalue;
	float   fvalue;

	/* This procedure lists one instruction, advancing the first
	 * argument ip to point to the next instruction.
	 * It was obtained by editing a copy of the main_loop procedure
	 * and should be modified whenever a change is made in inta.c
	 * to the way in which instructions are decoded.
	 */
	if (debug_trace) {
		printf("tp=%1d,sp=%3d,sfp=%3d,bfp=%3d,exr=%2d,lin=%2d,tos=%3d,",
		  tp    ,sp    ,sfp    ,bfp    ,exr    ,lin    ,cur_stackptr);
		printf("cs=%2d,ip=%3d\n",cs,*ip);
	}
	else
		printf("tos=%3d,cs=%2d,ip=%3d  ",cur_stackptr,cs,*ip);
#ifdef DEBUG_FULL_STACK
	stdump(sfp);
#endif
	opcode = (unsigned ) curcode[*ip] & 0xff;
	*ip += 1;
	printf("%s ", op_name(opcode)); /* debug */
	switch(opcode) {

	case I_NOP:
		break;

		/* Instructions Dealing with Tasking */

	case I_ABORT:
		DUMP_WORD;		/* number of tasks in stack */
		break;

	case I_ACTIVATE:
		break;

	case I_ACTIVATE_NEW_L:
		DUMP_LAD;
		break;

	case I_ACTIVATE_NEW_G:
	case I_CREATE_TASK_G:
		DUMP_GAD;
		break;

	case I_CREATE_TASK_L:
		DUMP_LAD;
		break;

	case I_POP_TASKS_DECLARED_G:
		DUMP_GAD;
		break;

	case I_POP_TASKS_DECLARED_L:
		DUMP_LAD;
		break;

	case I_LINK_TASKS_DECLARED:
	case I_CURRENT_TASK:
		break;

	case I_END_ACTIVATION:
		DUMP_BYTE;
		break;

	case I_END_RENDEZVOUS:
		break;

	case I_ENTRY_CALL:
		DUMP_WORD;
		break;

	case I_RAISE_IN_CALLER:
		break;

	case I_SELECTIVE_WAIT:
		DUMP_WORD;		/* number of alternatives */
		break;

	case I_TERMINATE:
		DUMP_BYTE;
		break;

	case I_TIMED_ENTRY_CALL:
	case I_WAIT: 		/* delay */
		break;
	case I_CREATE_COPY_B:
	case I_CREATE_COPY_W:
		printf(" ( %d ) ",TOS);
	case I_CREATE_B:
	case I_CREATE_W:
	case I_CREATE_L:
	case I_CREATE_A:
	case I_CREATE_STRUC:
	case I_CREATE_COPY_STRUC:
	case I_CREATE_COPY_L:
	case I_CREATE_COPY_A:

		break;

	case I_DECLARE_B:
	case I_DECLARE_W:
	case I_DECLARE_L:
	case I_DECLARE_A:
		DUMP_WORD;
		break;

	case I_ALLOCATE:
		break;

	case I_ALLOCATE_COPY_G:
		DUMP_GAD;
		break;

	case I_ALLOCATE_COPY_L:
		DUMP_LAD;
		break;

	case I_UPDATE:
	case I_UPDATE_AND_DISCARD:
		DUMP_WORD;
		break;

	case I_UNCREATE:
		printf(" ( %d  %d ) ",TOSM(1),TOS);
		break;
		/* should withdraw the variable from bf_data_link TBSL */

		/* Data Transfer Instructions */

	case I_COMPARE_B:
	case I_COMPARE_W:
	case I_DEREF_B:
	case I_DEREF_W:
	case I_DEREF_L:
	case I_DEREF_D:
	case I_DEREF_A:
		printf(" ( %d  %d ) ",TOSM(1),TOS);
		break;

	case I_COMPARE_L:
		printf(" ( %ld  %ld ) ",TOSML(1),TOSL);
		break;

	case I_COMPARE_A:
		printf(" ( %d  %d  %d  %d ) ",TOSM(3),TOSM(2),TOSM(1),TOS);
	case I_COMPARE_ARRAYS:
	case I_COMPARE_STRUC:
		break;

	case I_DISCARD_ADDR:
		DUMP_WORD;
		break;

	case I_DUPLICATE_B:
	case I_DUPLICATE_W:
		printf(" ( %d ) ",TOS);
		break;

	case I_DUPLICATE_L:
		printf(" ( %ld ) ",TOSL);
		break;

	case I_DUPLICATE_A:
		printf(" ( %d  %d ) ",TOSM(1),TOS);
		break;

	case I_INDIRECT_MOVE_B:
	case I_INDIRECT_MOVE_W:
	case I_INDIRECT_MOVE_L:
	case I_INDIRECT_MOVE_A:
		printf(" ( %d  %d  %d  %d ) ",TOSM(3),TOSM(2),TOSM(1),TOS);
		break;

	case I_INDIRECT_POP_B_G:
	case I_INDIRECT_POP_W_G:
		DUMP_GAD;
		break;

	case I_INDIRECT_POP_L_G:
	case I_INDIRECT_POP_A_G:
		DUMP_GAD;
		break;

	case I_INDIRECT_POP_B_L:
	case I_INDIRECT_POP_W_L:
	case I_INDIRECT_POP_L_L:
	case I_INDIRECT_POP_A_L:
		DUMP_LAD;
		break;

	case I_MOVE_B:
	case I_MOVE_W:
	case I_MOVE_L:
	case I_MOVE_A:
		printf(" ( %d  %d ) ",TOSM(2),TOSM(1));
		break;

	case I_POP_B_G:
	case I_POP_W_G:
		printf(" ( %d ) ",TOS);
		DUMP_GAD;
		break;

	case I_POP_L_G:
	case I_POP_A_G:
		DUMP_GAD;
		break;

	case I_POP_B_L:
	case I_POP_W_L:
		printf(" ( %d ) ",TOS);
	case I_POP_L_L:
	case I_POP_A_L:
		DUMP_LAD;
		break;

	case I_PUSH_B_G:
	case I_PUSH_W_G:
	case I_PUSH_L_G:
	case I_PUSH_A_G:
		DUMP_GAD;
		break;

	case I_PUSH_B_L:
	case I_PUSH_W_L:
	case I_PUSH_L_L:
	case I_PUSH_A_L:
		DUMP_LAD;
		break;

	case I_PUSH_EFFECTIVE_ADDRESS_G:
	case I_PUSH_IMMEDIATE_A:
		DUMP_GAD;
		break;

	case I_PUSH_EFFECTIVE_ADDRESS_L:
		jump = sfp + dump_word(ip, curcode);
		printf(" (%d  %d)",cur_stack[jump], cur_stack[jump+1]);
		break;

	case I_PUSH_IMMEDIATE_B:
		DUMP_WORD;
		break;

	case I_PUSH_IMMEDIATE_W:
		DUMP_WORD;
		break;

	case I_PUSH_IMMEDIATE_L:
#ifdef ALIGN_WORD
		lvalue = get_long(LONG(curcode + *ip));
		fvalue = lvalue;
#else
		lvalue = *LONG(curcode + *ip);
		fvalue = *((float *)(curcode + *ip));
#endif
		printf(" %ld  %15.3e ", lvalue,fvalue);
		*ip += sizeof(long);
		break;

		/* Floating Point Instructions */

	case I_FLOAT_ADD_L:
	case I_FLOAT_SUB_L:
	case I_FLOAT_MUL_L:
	case I_FLOAT_DIV_L:
	case I_FLOAT_COMPARE_L:
		fvalue = *((float *)(cur_stack+cur_stackptr+1-2*WORDS_FLOAT));
		printf(" ( %e  %e ) ",fvalue,TOSF);
		break;

	case I_FLOAT_POW_L:
		fvalue = *((float *)(cur_stack+cur_stackptr-WORDS_FLOAT));
		printf(" ( %e  %d ) ",fvalue,TOS);
		break;

	case I_FLOAT_NEG_L:
	case I_FLOAT_ABS_L:
		printf(" ( %e ) ",TOSF);
		break;

	case I_ADD_B:
	case I_ADD_W:
		printf(" ( %d  %d ) ",TOSM(1),TOS);
	case I_ADD_L:
		break;

	case I_ADD_IMMEDIATE_B:
		printf(" ( %d ) ",TOS);
		DUMP_WORD;
		break;

	case I_ADD_IMMEDIATE_W:
		printf(" ( %d ) ",TOS);
		DUMP_WORD;
		break;

	case I_ADD_IMMEDIATE_L:
		lvalue = *(LONG(curcode + *ip));
		printf(" ( %ld ) %ld ",TOSL,lvalue);
		*ip += WORDS_LONG;
		break;

	case I_DIV_B:
	case I_DIV_W:
	case I_DIV_L:
	case I_REM_B:
	case I_REM_W:
	case I_REM_L:
	case I_MOD_B:
	case I_MOD_W:
	case I_MOD_L:
	case I_MUL_B:
	case I_MUL_W:
	case I_MUL_L:
	case I_POW_B:
	case I_POW_W:
	case I_POW_L:
	case I_FIX_MUL:
	case I_FIX_DIV:
		printf(" ( %d  %d ) ",TOSM(1),TOS);
		break;

	case I_CONVERT_TO_L:
		DUMP_LAD;
		break;

	case I_CONVERT_TO_G:
		DUMP_GAD;
		break;

	case I_NEG_B:
	case I_NEG_W:
	case I_NEG_L:
	case I_ABS_B:
	case I_ABS_W:
	case I_ABS_L:
	case I_NOT:
	case I_AND:
	case I_XOR:
	case I_OR:
	case I_IS_EQUAL:
	case I_IS_GREATER:
	case I_IS_GREATER_OR_EQUAL:
	case I_IS_LESS:
	case I_IS_LESS_OR_EQUAL:
		printf(" ( %d ) ",TOS);
	case I_MEMBERSHIP:
		break;

	case I_QUAL_RANGE_G:
		DUMP_GAD;
		break;

	case I_QUAL_RANGE_L:
		DUMP_LAD;
		break;

	case I_QUAL_DISCR_G:
		DUMP_GAD;
		break;

	case I_QUAL_DISCR_L:
		DUMP_LAD;
		break;

	case I_QUAL_INDEX_G:
		DUMP_GAD;
		break;

	case I_QUAL_INDEX_L:
		DUMP_LAD;
		break;

	case I_QUAL_SUB_G:
		DUMP_GAD;
		break;

	case I_QUAL_SUB_L:
		DUMP_LAD;
		break;

	case I_SUB_B:
	case I_SUB_W:
	case I_SUB_L:

	case I_ARRAY_CATENATE:
	case I_ARRAY_MOVE:
	case I_ARRAY_SLICE:
	case I_ARRAY_AND:
	case I_ARRAY_OR:
	case I_ARRAY_XOR:
	case I_ARRAY_NOT:
		break;

		/* Record Instructions */

	case I_RECORD_MOVE_G:
		DUMP_GAD;
		break;

	case I_RECORD_MOVE_L:
		DUMP_LAD;
		break;

		/* Attributes */

	case I_ATTRIBUTE:
		DUMP_WORD; /* attribute */
		break;

	case I_ENTER_BLOCK:
	case I_LEAVE_BLOCK:
	case I_EXIT_BLOCK:
		break;

	case I_CALL_L:
		DUMP_LAD;
		break;

	case I_CALL_G:
		DUMP_GAD;
		break;

	case I_CALL_PREDEF:
		DUMP_BYTE;
		break;

	case I_CALL_INTERFACE:
		DUMP_WORD;
		break;

	case I_CASE_B:
	case I_CASE_W:
	case I_CASE_L:
		printf(" ( %d ) case table :\n",TOS);
		printf(" value ");
		DUMP_WORD;  /* nb */
		printf(" jump ");
		fjump = DUMP_WORD;
		printf("\n");
		for (; *ip < fjump;) {
			printf(" value ");
			DUMP_WORD; /* nb */
			printf(" jump ");
			jump = DUMP_WORD;
			printf("\n");
			fjump = ((fjump < jump) ? fjump : jump);
		}
		break;

	case I_RETURN_B:
	case I_RETURN_W:
		DUMP_WORD;
		printf(" ( %d ) ",TOS);
		break;

	case I_RETURN_L:
		DUMP_WORD;
		printf(" ( %d %e ) ",TOS,TOSF);
		break;

	case I_RETURN_A:
		DUMP_WORD;
		printf(" ( %d %d ) ",TOSM(1),TOS);
		break;

	case I_RETURN_STRUC:
		DUMP_WORD;
		break;

	case I_END_FOR_LOOP_B:
	case I_END_FOR_LOOP_W:
	case I_END_FOR_LOOP_L:
	case I_END_FORREV_LOOP_B:
	case I_END_FORREV_LOOP_W:
	case I_END_FORREV_LOOP_L:

	case I_JUMP_IF_FALSE:
	case I_JUMP_IF_TRUE:
	case I_JUMP_IF_GREATER:
	case I_JUMP_IF_GREATER_OR_EQUAL:
	case I_JUMP_IF_LESS:
	case I_JUMP_IF_LESS_OR_EQUAL:
		printf(" ( %d ) ",TOS);
		DUMP_WORD;
		break;
	case I_JUMP:
		DUMP_WORD;
		break;

		/* Miscellanous Instructions */

	case I_LOAD_EXCEPTION_REGISTER:
	case I_INSTALL_HANDLER:
		DUMP_WORD;
		break;

	case I_RAISE:
		break;

	case I_RESTORE_STACK_POINTER:
		DUMP_WORD;
		break;

	case I_SAVE_STACK_POINTER:
		break;

	case I_STMT:
		DUMP_WORD;
		break;

	case I_SUBSCRIPT:
		break;

	case I_SELECT:
		DUMP_WORD;
		break;

	case I_TEST_EXCEPTION_REGISTER:
		DUMP_WORD;
		break;

	case I_TYPE_LOCAL:
		DUMP_GAD;
		break;

	case I_TYPE_GLOBAL:
		DUMP_GAD;
		break;

	case I_SUBPROGRAM:
		DUMP_LAD;
		break;

	default:
		printf("bad opcode");

	}				/* end switch on operation code */
	printf(" \n");
}

#ifdef DEBUG_FULL_STACK
/* give full stack dump for each instruction (use in desparation!) */
static void stdump(int pd)			/*;stdump*/
{
	/* stack dump p is current value of sfp */
	int i;
	printf("stdump sfp %d %d\n",pd,pd-18);
	for (i= (-18); ;i++) {
		if ((pd+i) <0) continue;
		if ((pd+i)>cur_stackptr) break;
		printf("%6d %03d ", cur_stack[pd+i], pd+i);
		if (i%7 == 0) printf("\n");
	}
	printf("\n");
}
#endif

static unsigned int dump_byte(int *ip, char *curcode)			/*;dump_byte*/
{
	unsigned int     byte;
	/*byte = curcode[*ip++];*/
	byte = (unsigned) curcode[*ip];
	byte = byte & 0xff;
	*ip += 1;
	printf(" %u ", byte);
	return byte;
}

static int dump_word(int *ip, char *curcode)					/*;dump_word*/
{
	int     w;
#ifdef ALIGN_WORD
	w = get_int((int *)(curcode + *ip));
#else
	w = *((int *)(curcode + *ip));
#endif
	printf(" %d ", w);
	*ip += sizeof(int);
	return w;
}

static void dump_gad(int *ip, char *curcode)					/*;dump_gad*/
{
    unsigned int     bse, off;
    bse = (int) curcode[*ip];
    *ip += 1;
#ifdef ALIGN_WORD
    off = get_int((int *)(curcode + *ip));
#else
    off = *((int *)(curcode + *ip));
#endif
    *ip += sizeof(int);
    printf(" %3u %5u ", bse, off);
}
