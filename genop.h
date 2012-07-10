/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#ifndef __genop_h
#define __genop_h

/* argument types :*/
/* K is kind, S is symbol V is value (const)
 * I is integer, R is ref
 */
#define OP_FLT	1		/* float */
#define	OP_FIX	2		/* fixed (long) */
#define OP_INT	3		/* int */
#define OP_REF	4		/* reference */
#define OP_SYM	5		/* symbol*/
/* op_code is opcode.
 * op_kind is small integer giving adjustment to be made to opcode or
 * small integer giving attribute code (I_ATTRIBUTE), or argument for
 * i_discard_address (always one).
 * op_type gives which operands exist.
 * op_arg is additional argument, usually a symbol but may be an integer
 * const, or (pointer to) explicit ref (Eref).
 */
typedef struct Op_s	*Op;
typedef struct Op_s {
	int	op_code;
	int     op_kind;
	short	op_type;
	union {
	    float	  arg_flt;
	    long	  arg_fix; 	/* fixed, assume long suffices */
	    int		  arg_int;
	    Explicit_ref  arg_ref;
	    Symbol  	  arg_sym;
	} op_arg;
	char	*op_com;
} Op_s;
extern Op op_new();

#endif
