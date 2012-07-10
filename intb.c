/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/* Continuation of ada interpreter - auxiliary procedures */

/* Include standard header modules */
#include <stdlib.h>
#include <setjmp.h>
#include "config.h"
#include "int.h"
#include "ivars.h"
#include "machineprots.h"
#include "farithprots.h"
#include "taskingprots.h"
#include "predefprots.h"
#include "intcprots.h"
#include "intbprots.h"

extern jmp_buf raise_env;

static void update_address(int *);
static void image_attribute();
static void value_attribute();
static int same_dimensions(int *, int *);
static int compare_fields_record(int *, int *, int *);

void main_attr(int attribute, int dim)						/*;attribute*/
{
	switch(attribute) {

	case ATTR_ADDRESS:
		POP_ADDR(bse, off);
		create(2, &bas1, &off1, &ptr1);/* ADDRESS is a record */
		*ADDR(bas1, off1) = bse;
		*ADDR(bas1, off1 + 1) = off;
		PUSH_ADDR(bas1, off1);
		break;

	case ATTR_CALLABLE:
		POP(value);	/* task object */
		value = (is_callable(value));
		PUSH(value);
		break;

	case ATTR_COUNT:
		POP(val2);		/* member in family */
		POP(val1);		/* entry family */
		value = count(val1, val2);
		PUSH(value);
		break;

	case ATTR_T_CONSTRAINED:
		break;

	case ATTR_O_CONSTRAINED:
		break;

	case ATTR_T_FIRST:
	case ATTR_T_LAST:
		POP_ADDR(bse, off);/* type */
		ptr = ADDR(bse, off);
		size = SIZE(ptr);
		if (TYPE(ptr) == TT_FX_RANGE) {
			if (attribute == ATTR_T_FIRST)
				PUSHL(FX_RANGE(ptr)->fxlow);
			else
				PUSHL(FX_RANGE(ptr)->fxhigh);
		}
		else if (TYPE(ptr) == TT_FL_RANGE) {
			if (attribute == ATTR_T_FIRST)
				PUSHF(FL_RANGE(ptr)->fllow);
			else
				PUSHF(FL_RANGE(ptr)->flhigh);
		}
		else if ((TYPE(ptr) == TT_I_RANGE)
		  ||     (TYPE(ptr) == TT_E_RANGE)
		  ||     (TYPE(ptr) == TT_ENUM)) {
			if (attribute == ATTR_T_FIRST)
				PUSH(I_RANGE(ptr)->ilow);
			else
				PUSH(I_RANGE(ptr)->ihigh);
		}
#ifdef LONG_INT
		else if (TYPE(ptr) == TT_L_RANGE) {
			if (attribute == ATTR_T_FIRST)
				PUSHL(L_RANGE(ptr)->llow);
			else
				PUSHL(L_RANGE(ptr)->lhigh);
		}
#endif
		else	/* error */
			raise(SYSTEM_ERROR,"Unknown type for attribute FIRST or LAST");
		break;

	case ATTR_O_FIRST:
	case ATTR_O_LAST:
		POP_ADDR(bse, off);/* type */
		ptr = ADDR(bse, off);
		POP_ADDR(bas1, off1);/* to get rid of array */
		val1 = *ptr;	/* type of type */
		if (val1 == TT_S_ARRAY) {
			if (attribute == ATTR_O_LAST)
				value = S_ARRAY(ptr)->sahigh;
			else
				value = S_ARRAY(ptr)->salow;
			PUSH(value);
		}
		else if (val1 == TT_C_ARRAY || val1 == TT_U_ARRAY) {
			/* Beware: indices in reverse order */
			ptr += 2 * (ARRAY(ptr)->dim - dim);
			bse = ARRAY(ptr)->index1_base;
			off = ARRAY(ptr)->index1_offset;
			ptr = ADDR(bse, off);
			if ((TYPE(ptr) == TT_I_RANGE)
			  ||(TYPE(ptr) == TT_E_RANGE)
			  ||(TYPE(ptr) == TT_ENUM)) {
				if (attribute == ATTR_O_LAST)
					PUSH(I_RANGE(ptr)->ihigh);
				else
					PUSH(I_RANGE(ptr)->ilow);
			}
#ifdef LONG_INT
			else if (TYPE(ptr) == TT_L_RANGE) {
				if (attribute == ATTR_O_LAST)
					PUSHL(L_RANGE(ptr)->lhigh);
				else
					PUSHL(L_RANGE(ptr)->llow);
			}
#endif
		}
		else if (val1 == TT_D_ARRAY) {
			bas1 = D_TYPE(ptr)->dbase;
			off1 = D_TYPE(ptr)->doff;
			ptr += WORDS_D_TYPE + 4 *(dim - 1);
			if (attribute == ATTR_O_LAST)
				ptr += 2;
			if (*ptr == 0)
				PUSH(*(ptr + 1));
			else
				raise(SYSTEM_ERROR, "Attribute on discriminant bound");
		}
		break;

	case ATTR_T_LENGTH:
		POP_ADDR(bse, off);
		ptr = ADDR(bse, off);
		size = SIZE(ptr);
		if (size == 1) {
			if (I_RANGE(ptr)->ihigh < I_RANGE(ptr)->ilow)
				value = 0; 
			else
				value = I_RANGE(ptr)->ihigh - I_RANGE(ptr)->ilow + 1;
			PUSH(value);
		}
#ifdef LONG_INT
		else /* size=2 */ {
			if (L_RANGE(ptr)->lhigh < L_RANGE(ptr)->llow)
				lvalue = 0; 
			else
				lvalue = L_RANGE(ptr)->lhigh - L_RANGE(ptr)->llow;
			PUSHL(lvalue);
		}
#endif
		break;

	case ATTR_O_LENGTH:
		POP_ADDR(bse, off);/* type */
		ptr = ADDR(bse, off);
		POP_ADDR(bas1, off1);/* to get rid of array */
		val1 = TYPE(ptr);	/* type of type */
		if (val1 == TT_S_ARRAY) {
			/* the calculation of max is unuseful ! the substraction may
			 * produce an overflow and a positive result
			 */
			if (S_ARRAY(ptr)->sahigh < S_ARRAY(ptr)->salow)
				value = 0; 
			else {
				/*value=MAX(S_ARRAY(ptr)->sahigh-S_ARRAY(ptr)->salow + 1, 0);*/
				value = S_ARRAY(ptr)->sahigh - S_ARRAY(ptr)->salow + 1;
			}
			PUSH(value);
		}
		else if (val1 == TT_C_ARRAY) {
			/* Beware: indices in reverse order */
			ptr += 2 * (ARRAY(ptr)->dim - dim);
			bse = ARRAY(ptr)->index1_base;
			off = ARRAY(ptr)->index1_offset;
			ptr = ADDR(bse, off);
			/*  value = MAX(I_RANGE(ptr)->ihigh - I_RANGE(ptr)->ilow + 1, 0); */
			if (I_RANGE(ptr)->ihigh < I_RANGE(ptr)->ilow)
				value = 0; 
			else
				value = I_RANGE(ptr)->ihigh - I_RANGE(ptr)->ilow + 1;
			PUSH(value);
		}
		break;

	case ATTR_T_RANGE:
		POP_ADDR(bse, off);
		ptr = ADDR(bse, off);
		size = SIZE(ptr);
		if (size == 1) {
			PUSH(I_RANGE(ptr)->ilow);
			PUSH(I_RANGE(ptr)->ihigh);
		}
#ifdef LONG_INT
		else /* size == 2 */ {
			lvalue = L_RANGE(ptr)->lhigh - L_RANGE(ptr)->llow;
			PUSHL(lvalue);
		}
#endif
		break;

	case ATTR_O_RANGE:
		POP_ADDR(bse, off);/* type */
		ptr = ADDR(bse, off);
		POP_ADDR(bas1, off1);/* to get rid of array */
		val1 = TYPE(ptr);	/* type of type */
		if (val1 == TT_S_ARRAY) {
			val_high = S_ARRAY(ptr)->sahigh;
			val_low = S_ARRAY(ptr)->salow;
			PUSH(val_low);
			PUSH(val_high);
		}
		else if (val1 == TT_C_ARRAY) {
			/* 	 Beware: indices in reverse order */
			ptr += 2 * (ARRAY(ptr)->dim - dim);
			bse = ARRAY(ptr)->index1_base;
			off = ARRAY(ptr)->index1_offset;
			ptr = ADDR(bse, off);
			size = SIZE(ptr);
			if (size == 1) {
				PUSH(I_RANGE(ptr)->ilow);
				PUSH(I_RANGE(ptr)->ihigh);
			}
#ifdef LONG_INT
			else /*(size == 2)*/ {
				PUSHL(L_RANGE(ptr)->llow);
				PUSHL(L_RANGE(ptr)->lhigh);
			}
#endif
		}
		break;

	case ATTR_IMAGE:
		image_attribute();
		break;

	case ATTR_VALUE:
		value_attribute();
		break;

	case ATTR_PRED:
		POP_ADDR(bse, off);/* type */
		ptr = ADDR(bse, off);
		if ((TYPE(ptr) == TT_I_RANGE)
		  ||(TYPE(ptr) == TT_E_RANGE)
		  ||(TYPE(ptr) == TT_ENUM)) {
			POP(value);
			if (value <= I_RANGE(ptr)->ilow)
				raise(CONSTRAINT_ERROR, "Out of range (PRED)");
			value--;
			PUSH(value);
		}
#ifdef LONG_INT
		else if (TYPE(ptr) == TT_L_RANGE) {
			POPL(lvalue);
			if (lvalue <= L_RANGE(ptr)->llow)
				raise (CONSTRAINT_ERROR, "Out of range (PRED)");
			lvalue--;
			PUSHL(lvalue);
		}
#endif
		else	/* error */
			raise(SYSTEM_ERROR,"Unknown type for attribute PRED");
		break;

	case ATTR_SUCC:
		POP_ADDR(bse, off);/* type */
		ptr = ADDR(bse, off);
		if ((TYPE(ptr) == TT_I_RANGE)
		  ||(TYPE(ptr) == TT_E_RANGE)
		  ||(TYPE(ptr) == TT_ENUM)) {
			POP(value);
			if (value >= I_RANGE(ptr)->ihigh)
				raise(CONSTRAINT_ERROR, "Out of range (SUCC)");
			value++;
			PUSH(value);
		}
#ifdef LONG_INT
		else if (TYPE(ptr) == TT_L_RANGE) {
			POPL(lvalue);
			if (lvalue >= L_RANGE(ptr)->lhigh)
				raise (CONSTRAINT_ERROR, "Out of range (SUCC)");
			lvalue++;
			PUSHL(lvalue);
		}
#endif
		else	/* error */
			raise(SYSTEM_ERROR,"Unknown type for attribute SUCC");
		break;

	case ATTR_SIZE:
		POP_ADDR(bse, off);
		ptr1 = ADDR(bse, off);
		value = SIZE(ptr1);
	    if ((TYPE(ptr1) == TT_RECORD 	
			|| TYPE(ptr1) == TT_C_RECORD
		 	|| TYPE(ptr1) == TT_U_RECORD 	
			|| TYPE(ptr1) == TT_V_RECORD)
		    && (U_RECORD(ptr1)->repr_size != 0)) {
		   PUSH(U_RECORD(ptr1)->repr_size);
	    }	
		else if (TYPE(ptr1) == TT_ACCESS) {
		   PUSH(32);
	    }	
		else {
		   PUSH(value * BITS_SU);
		}
		break;

	case ATTR_STORAGE_SIZE:
		POP_ADDR(bse, off);
		ptr1 = ADDR(bse, off);
	    if (TYPE(ptr1) == TT_ACCESS) {
		   value = ACCESS(ptr1)->collection_size;
		}
		else {
			value = TASK(ptr1)->collection_size;
		}
		PUSH(value);
		break;

	case ATTR_TERMINATED:
		POP(value);	/* task object */
		value = (is_terminated(value));
		PUSH(value);
		break;

	case ATTR_MANTISSA:
	case ATTR_LARGE:
		POP_ADDR(bse, off);/* type */
		ptr = ADDR(bse, off);
		if (TYPE(ptr) == TT_FX_RANGE) {
			long power ;
			fval1 = FX_RANGE(ptr)->fxlow;
			fval2 = FX_RANGE(ptr)->fxhigh;
			fval1 = MAX(fval1, fval2);
			value = 1;
			POP(ratio);	/* ratio between subtype's and base type's SMALL */
			power = 1;
			/* Compute value s.t. 2 ** value - 1 includes the upper bound -1.
			 * Given that the small of the subtype may be larger than that of
			 * the type, the 'last of the subtype may be -ratio- away from the
			 * given bound.
			 */
			while (power * ratio < fval1 - ratio) {
				power = power + power + 1;
				value++;
			}
			if (attribute == ATTR_MANTISSA)
				PUSH(value);
			else {		/* attribute = A_LARGE */
				lvalue = power * ratio ;
				PUSHL(lvalue) ;
			}
		}
		else {		/* floating point */
			/* TBSL */
		}
		break;

	case ATTR_FORE:
		POP_ADDR(bse, off);/* type */
		ptr = ADDR(bse, off);
		POP(d);
		POP(n);

		fval1 = FX_RANGE(ptr)->fxhigh;
		fval2 = FX_RANGE(ptr)->fxlow;
		fval1 = ABS(fval1);
		fval2 = ABS(fval2);
		n *= MAX(fval1, fval2);
		value = 2;
		while (n / d >= 10) {
			d *= 10;
			value++;
		}
		PUSH(value);
		break;

	case ATTR_WIDTH:
		POP_ADDR(bse, off);/* type */
		ptr = ADDR(bse, off);
		val1 = TYPE(ptr);	/* type of type */
		val_low = I_RANGE(ptr)->ilow;
		val_high = I_RANGE(ptr)->ihigh;
		if (val1 == TT_I_RANGE) {
			if (val_low > val_high)
				value = 0;
			else {
				val1 = ABS(val_low);
				val2 = ABS(val_high);
				i = MAX(val1, val2);
				value = 2;
				while (i > 10) {
					value += 1;
					i = i / 10;
				}
			}
		}

		else {
			if (val1 == TT_E_RANGE) {
				bse = E_RANGE(ptr)->ebase;/* Literals are */
				off = E_RANGE(ptr)->eoff;/* in base type */
				ptr = ADDR(bse, off);
			}
			ptr += WORDS_E_RANGE;/* skip litrals not in subtype */
			for (i = 0; i <= val_low - 1; i++)
				ptr += *ptr + 1;
			value = 0;
			for (i = val_low; i <= val_high; i++) {
				if (*ptr > value)
					value = *ptr;
				ptr += *ptr + 1;
			}
		}
		PUSH(value);
		break;

	default:
		raise(SYSTEM_ERROR, "Unknown attribute");
	}
}

void convert(int bse, int off)								/*;convert*/
{
	int    *ptr_from, *ptr_to, *ptr4, exp2, exp5;
	int     res_sign, exponent;
	long    mul_fact, div_fact;
	int     from_is_empty,to_is_empty;

	ptr_to = ADDR(bse, off);
	POP_ADDR(bas1, off1);
	ptr_from = ADDR(bas1, off1);

	/* Deal with combinations of from/to (other combinations handled by
	 * codegen) 
	 */
	if (TYPE(ptr_to) == TT_I_RANGE) {
		if (TYPE(ptr_from) == TT_FL_RANGE) {
			POPF(rvalue);
			if (ABS(rvalue) >(float)(MAX_LONG))
				raise(NUMERIC_ERROR, "Integer out of bounds");
			else {
				value = (rvalue + (rvalue > 0.0? 0.5 : -0.5));
				PUSH(value);
			}
		}
		/* If fixed range, is always integer_fixed ($FIXED) */
		else if (TYPE(ptr_from) == TT_FX_RANGE) {
			POPL(lvalue);
			value = lvalue;
			PUSH(value);
			if ((long) value != lvalue)					/* if overflow */
				raise(NUMERIC_ERROR, "fixed_point conversion");
		}
		/* Note: nothing to do if *ptr_from == TT_I_RANGE */
	}

	else if (TYPE(ptr_to) == TT_FL_RANGE) {
		if (TYPE(ptr_from) == TT_I_RANGE) {
			POP(value);
			rvalue = value;
			PUSHF(rvalue);
		}
		else if (TYPE(ptr_from) == TT_FX_RANGE) {
			POPL(lvalue);
			ptr = ptr_from;
			exp2 = FX_RANGE(ptr)->small_exp_2;
			exp5 = FX_RANGE(ptr)->small_exp_5;
			if (lvalue == 0)
				PUSHF(0.0);
			else {
				res_sign = SIGN(lvalue);/* sign of result */
				mul_fact = ABS(lvalue);
				div_fact = 1;

				if (exp5 < 0) {	/* take care of powers of 5 */
					for (i = exp5; i != 0; i++)
						div_fact *= 5;
				}
				else {
					for (i = exp5; i != 0; i--)
						mul_fact *= 5;
				}

				/* 	 compute the division as if there were no problem */
				/* 	(convert the two factors to floating points before) */

				rvalue = FLOAT(mul_fact) / FLOAT(div_fact);
				/* expn returns the integer exponent of a positive float */
				exponent = expn(rvalue) - 21; /* float'mantissa = 21 */
				if (exponent < 0) { /* if not enough bits, get larger num */
					for (i = exponent; i != 0; i++)
						mul_fact *= 2;
				}
				else {
					for (i = exponent; i != 0; i--)
						div_fact *= 2;
				}
				exp2 += exponent; /* adjust the exponent */

				lvalue = mul_fact / div_fact; /* compute result */
				if (lvalue <(1024L * 1024L)) { /* case of < 21 bits */
					mul_fact *= 2;
					exp2--;
				}
				else if (lvalue >(1024L * 2048L) - 1) { /* case of > 21 bits */
					div_fact *= 2;
					exp2++;
				}
				else {		/* 21 bits exactly */
				}
				/* 	 watch out: we introduced a bias in the exponent */
				if (exp2 >(84 - 21))
					raise(NUMERIC_ERROR, "Floating point value overflow");
				else if (exp2 <(-84 - 21))
					PUSHF(0.0);	/* underflow */
				else {
					rvalue = FLOAT(res_sign *(mul_fact / div_fact));
					if (exp2 < 0) {
						for (i = exp2; i != 0; i++)
							rvalue /= 2.0;
					}
					else {
						for (i = exp2; i != 0; i--)
							rvalue *= 2.0;
					}
					PUSHF(rvalue);
				}
			}
		}
		/* Note: nothing to do in TYPE(ptr_from) == TT_FL_RANGE case */
	}

	else if (TYPE(ptr_to) == TT_FX_RANGE) {
		if (TYPE(ptr_from) == TT_I_RANGE) {
			POP(value); /* target type is integer_fixed */
			lvalue = (long) value;
			PUSHL(lvalue);
		}
		else if (TYPE(ptr_from) == TT_FL_RANGE) {
			POPF(rvalue);
			if (rvalue == 0.0)
				PUSHL(0);
			else {
				res_sign = SIGN(rvalue);
				rvalue = ABS(rvalue);
				exp2 = expn(rvalue) - 21;
				if (exp2 < 0) {
					for (i = exp2; i != 0; i++)
						rvalue *= 2.0;
				}
				else {
					for (i = exp2; i != 0; i--)
						rvalue /= 2.0;
				}
				mul_fact = rvalue;	/* exactly 21 bits */
				div_fact = 1;
				exp2 = FX_RANGE(ptr_to)->small_exp_2 - exp2;
				exp5 = FX_RANGE(ptr_to)->small_exp_5;
				if (exp5 < 0) {	/* at most 42 bits */
					for (i = exp5; i != 0; i++)
						mul_fact *= 5;
				}
				else {
					for (i = exp5; i != 0; i--)
						div_fact *= 5;
				}
				if (exp2 < 0) {
					for (i = exp2; i != 0; i++)
						mul_fact *= 2;
				}
				/* delay div by powers of two to avoid overflows om div_fact */
				lvalue = mul_fact / div_fact;
				if (exp2 > 0) {
					for (i = exp2; i != 0; i--)
						lvalue /= 2;
				}
				lvalue *= res_sign;
				if (lvalue < MIN_LONG || lvalue > MAX_LONG) {
					raise (NUMERIC_ERROR, "Fixed point overflow");
					lvalue = 0;
				}
			}
			PUSHL(lvalue);
		}

		else if (TYPE(ptr_from) == TT_FX_RANGE) {
			POPL(lvalue);
			res_sign = SIGN(lvalue);
			lvalue = ABS(lvalue);
			int_tom(fix_val1,lvalue);
			fix_convert(fix_val1, FX_RANGE(ptr_from), FX_RANGE(ptr_to));
			lvalue = int_tol(fix_val1);
			if(arith_overflow)
				raise(NUMERIC_ERROR,"Fixed point conversion overflow");
			PUSHL(res_sign*lvalue);
		}
		else
			raise(SYSTEM_ERROR,"Conversion from an unknown type");
	}
	else if (TYPE(ptr_to) == TT_U_ARRAY || TYPE(ptr_to) == TT_C_ARRAY) {
		if (TYPE(ptr_from) == TT_U_ARRAY || TYPE(ptr_from) == TT_C_ARRAY) {
			nb_dim = ARRAY(ptr_to)->dim;
			ptr3 = &(ARRAY(ptr_from)->index1_base);
			ptr4 = &(ARRAY(ptr_to)->index1_base);
			from_is_empty = FALSE;
			to_is_empty = FALSE;
			for (i = 1; i <= nb_dim; i++) {
				bas1 = *ptr3++;
				off1 = *ptr3++;
				ptr1 = ADDR(bas1, off1);
				bas2 = *ptr4++;
				off2 = *ptr4++;
				ptr2 = ADDR(bas2, off2);
				if (I_RANGE(ptr1)->ilow > I_RANGE(ptr1)->ihigh)
					from_is_empty = TRUE;
				if (I_RANGE(ptr2)->ilow > I_RANGE(ptr2)->ihigh)
					to_is_empty = TRUE;
			}
			if (from_is_empty && to_is_empty) {
				/* both are empty arrays: do not convert */
				PUSH_ADDR(bse,off);
				return;
			}
			if (from_is_empty || to_is_empty) {
				/* one is empty, the other is not */
				raise(CONSTRAINT_ERROR, "Array conversion");
				return;
			}

			/* both have components: do the conversion */
			ptr_from = &(ARRAY(ptr_from)->index1_base);
			ptr_to = &(ARRAY(ptr_to)->index1_base);
			for (i = 1; i <= nb_dim; i++) {
				bas1 = *ptr_from++;
				off1 = *ptr_from++;
				ptr1 = ADDR(bas1, off1);
				bas2 = *ptr_to++;
				off2 = *ptr_to++;
				ptr2 = ADDR(bas2, off2);
				if (I_RANGE(ptr1)->ihigh - I_RANGE(ptr1)->ilow
				  !=I_RANGE(ptr2)->ihigh - I_RANGE(ptr2)->ilow) {
					raise(CONSTRAINT_ERROR, "Array conversion");
					return;
				}
			}
		}
		else if (TYPE(ptr_from) == TT_S_ARRAY) {
			bas2 = ARRAY(ptr_to)->index1_base;
			off2 = ARRAY(ptr_to)->index1_offset;
			ptr2 = ADDR(bas2, off2);
			from_is_empty =
			  (S_ARRAY(ptr_from)->salow > S_ARRAY(ptr_from)->sahigh);
			to_is_empty = (I_RANGE(ptr2)->ilow > I_RANGE(ptr2)->ihigh);
			if (from_is_empty && to_is_empty) {
				/* both are empty arrays: do not convert */
				PUSH_ADDR(bse,off);
				return;
			}
			if (from_is_empty || to_is_empty) {
				/* one is empty, the other is not */
				raise(CONSTRAINT_ERROR, "Array conversion");
				return;
			}
			/* both have components: do the conversion */
			if (S_ARRAY(ptr_from)->sahigh - S_ARRAY(ptr_from)->salow !=
			    I_RANGE(ptr2)->ihigh - I_RANGE(ptr2)->ilow) {
				raise(CONSTRAINT_ERROR, "Array conversion");
				return;
			}
		}
		PUSH_ADDR(bse,off);
	}
	else if (TYPE(ptr_to) == TT_S_ARRAY) {
		if (TYPE(ptr_from) == TT_U_ARRAY || TYPE(ptr_from) == TT_C_ARRAY) {
			bas1 = ARRAY(ptr_from)->index1_base;
			off1 = ARRAY(ptr_from)->index1_offset;
			ptr1 = ADDR(bas1, off1);
			from_is_empty = (I_RANGE(ptr1)->ilow > I_RANGE(ptr1)->ihigh);
			to_is_empty = (S_ARRAY(ptr_to)->salow > S_ARRAY(ptr_to)->sahigh);
			if (from_is_empty && to_is_empty) {
				/* both are empty arrays: do not convert */
				PUSH_ADDR(bse,off);
				return;
			}
			if (from_is_empty || to_is_empty) {
				/* one is empty, the other is not */
				raise(CONSTRAINT_ERROR, "Array conversion");
				return;
			}
			/* both have components: do the conversion */
			if (I_RANGE(ptr1)->ihigh - I_RANGE(ptr1)->ilow !=
			    S_ARRAY(ptr_to)->sahigh - S_ARRAY(ptr_to)->salow) {
				raise(CONSTRAINT_ERROR, "Array conversion");
				return;
			}
		}
		else if (TYPE(ptr_from) == TT_S_ARRAY) {
			from_is_empty =
			  (S_ARRAY(ptr_from)->salow > S_ARRAY(ptr_from)->sahigh);
			to_is_empty = (S_ARRAY(ptr_to)->salow > S_ARRAY(ptr_to)->sahigh);
			if (from_is_empty && to_is_empty) {
				/* both are empty arrays: do not convert */
				PUSH_ADDR(bse,off);
				return;
			}
			if (from_is_empty || to_is_empty) {
				/* one is empty, the other is not */
				raise(CONSTRAINT_ERROR, "Array conversion");
				return;
			}
			/* both have components: do the conversion */
			if (S_ARRAY(ptr_from)->sahigh - S_ARRAY(ptr_from)->salow !=
			    S_ARRAY(ptr_to)->sahigh - S_ARRAY(ptr_to)->salow) {
				raise(CONSTRAINT_ERROR, "Array conversion");
				return;
			}
		}
		PUSH_ADDR(bse,off);
	}
}

/* TYPE_ELABORATE */

void type_elaborate(int flag, int bse, int off)			/*;type_elaborate*/
{
	/*
	 *  flag = 0 == type template is to remain global and the original
	 *		can be updated on the spot
	 *  flag = 1 == a new local type template has to be created
	 *
	 *  In the local case, the size of the object to allocate is computed, the
	 *  new type is created and initialized with the old one. From then on,
	 *  both cases, local and global, can proceed with the same code, given a
	 *  ptr in memory to the beginning of the type template.
	 */

	int    template_size, nb_field, variant_size, component_size, nb_fixed,
	templ_bse, templ_off, temporary, last_offset, first_case,
	*case_table_ptr, *field_table_ptr, offset, lbd, ubd, lng;
	float  fval_high,fval_low;
	long   fix_val_high,fix_val_low;

	/*GET_GAD(bse,off); bse,off retrieved by main_loop */
	ptr = ADDR(bse,off);

	value = TYPE(ptr);	  /*  type of type */
	if (flag == 1) {
		switch (value) {

		case TT_I_RANGE:
			template_size = WORDS_I_RANGE;
			break;

		case TT_FL_RANGE:
			template_size = WORDS_FL_RANGE;
			break;

		case TT_E_RANGE:
			template_size = WORDS_E_RANGE;
			break;

		case TT_FX_RANGE:
			template_size = WORDS_FX_RANGE;
			break;

		case TT_ACCESS:
			template_size = WORDS_ACCESS;
			break;

		case TT_RECORD:
			nb_field = RECORD(ptr)->nb_field;
			template_size = 3 * nb_field + WORDS_RECORD;
			break;

		case TT_U_RECORD:
		case TT_V_RECORD:
			nb_field      = U_RECORD(ptr)->nb_field_u;
			variant_size  = U_RECORD(ptr)->variant;
			template_size = 3 * nb_field + WORDS_U_RECORD + variant_size;
			break;

		case TT_C_RECORD:
			nb_discr      = C_RECORD(ptr)->nb_discr_c;
			template_size = WORDS_C_RECORD + nb_discr;
			break;

		case TT_U_ARRAY:
		case TT_C_ARRAY:
			nb_dim	       = ARRAY(ptr)->dim;
			template_size = 2 * (nb_dim - 1) + WORDS_ARRAY;
			break;

		case TT_D_RECORD:
			nb_discr      = D_TYPE(ptr)->nb_discr_d;
			template_size = WORDS_D_TYPE + 2 * nb_discr;
			break;

		case TT_D_ARRAY:
			nb_discr      = D_TYPE(ptr)->nb_discr_d;
			template_size = WORDS_D_TYPE + 4 * nb_discr;
			break;

		case TT_S_ARRAY:
			template_size = WORDS_S_ARRAY;
			break;

		case TT_TASK:
			template_size = WORDS_TASK + (TASK(ptr)->nb_families * 2);
			break;

		default:
			;
		}

		ptr1 = ptr;
		create (template_size, &templ_bse, &templ_off, &ptr);

		for (i = 0; i < template_size; i++)
			*ptr++ = *ptr1++;

		ptr -= template_size;	       /* restore ptr */
	}

	/* Now ptr designates the template to modify */

	switch (value) {

	case TT_E_RANGE:
		POP(val_high);
		E_RANGE(ptr)->ehigh = val_high;
		POP(val_low);
		E_RANGE(ptr)->elow = val_low;
		break;

	case TT_FL_RANGE:
		POPF(fval_high);
		FL_RANGE(ptr)->flhigh = fval_high;
		POPF(fval_low);
		FL_RANGE(ptr)->fllow = fval_low;
		break;

	case TT_I_RANGE:
		POP(val_high);
		I_RANGE(ptr)->ihigh = val_high;
		POP(val_low);
		I_RANGE(ptr)->ilow = val_low;
		break;

	case TT_FX_RANGE:
		POPL(fix_val_high);
		POPL(fix_val_low);
		FX_RANGE(ptr)->fxlow = fix_val_low;
		FX_RANGE(ptr)->fxhigh = fix_val_high;
		break;

	case TT_ACCESS:
		ACCESS(ptr)->master_task = tp;
		ACCESS(ptr)->master_bfp = bfp;
		break;

	case TT_S_ARRAY:
		break;

	case TT_U_ARRAY:
		nb_dim = ARRAY(ptr)->dim;
		update_address(ptr1 = &(ARRAY(ptr)->component_base));
		for (i = 0; i < nb_dim; i++) {
			ptr1 += 2;
			update_address(ptr1);
		}
		break;

	case TT_C_ARRAY:
		nb_dim = ARRAY(ptr)->dim;
		update_address(ptr1 = &(ARRAY(ptr)->component_base));
		component_size = SIZE(ADDR(*ptr1, *(ptr1 + 1)));
		for (i = 0; i < nb_dim; i++) {
			ptr1 += 2;
			update_address(ptr1);
			val_high = I_RANGE(ADDR(*ptr1, *(ptr1 + 1)))->ihigh;
			val_low  = I_RANGE(ADDR(*ptr1, *(ptr1 + 1)))->ilow;
			if(val_low > val_high) component_size = 0;
			if (component_size) {
				temporary = word_sub(val_high,val_low,&overflow);
				if (overflow) break;
				temporary = word_add(temporary,1,&overflow);
				if (overflow) break;
				temporary = MAX(0,temporary);
				component_size = word_mul(component_size,temporary,&overflow);
				if (overflow) break;
			}
		}
		if (overflow)
			raise(NUMERIC_ERROR,"Type size overflow");
		I_RANGE(ptr)->object_size = component_size;
		break;

	case TT_D_ARRAY:
		update_address(&(D_TYPE(ptr)->dbase));
		nb_discr = D_TYPE(ptr)->nb_discr_d;
		ptr2 = ptr + WORDS_D_TYPE + 4 * nb_discr - 1;
		for (i = 0; i < 2 * nb_discr; i++) {
			POP(value);
			*ptr2 = value;
			ptr2 -= 2;
		}
		break;

	case TT_RECORD:
		nb_field = RECORD(ptr)->nb_field;
		last_offset =
		  compute_offset(0,nb_field-1,0,-1, ptr + WORDS_RECORD, 0);
		SIZE(ptr) = last_offset;
		break;

	case TT_U_RECORD:
		nb_field = U_RECORD(ptr)->nb_field_u;
		nb_fixed = U_RECORD(ptr)->nb_fixed_u;
		first_case = U_RECORD(ptr)->first_case;
		field_table_ptr = ptr + WORDS_U_RECORD;
		case_table_ptr = field_table_ptr + 3 * nb_field;
		last_offset = compute_offset(
		  0,		      /*  first field of fixed part */
		  nb_fixed-1,     /*  last field of fixed part */
		  0,		      /*  offset of first field */
		  first_case,
		  field_table_ptr,
		  case_table_ptr);
		SIZE(ptr) = last_offset;
		break;

	case TT_V_RECORD:
		nb_field = U_RECORD(ptr)->nb_field_u;
		nb_fixed = U_RECORD(ptr)->nb_fixed_u;
		first_case = U_RECORD(ptr)->first_case;
		field_table_ptr = ptr + WORDS_U_RECORD + 1;
		for (i = 1; i <= nb_field; i++) {
			update_address(field_table_ptr);
			field_table_ptr += 3;
		}
		break;

	case TT_C_RECORD:
		update_address (&(C_RECORD(ptr)->cbase));
		ptr2 = ADDR (C_RECORD(ptr)->cbase, C_RECORD(ptr)->coff); /* base type */
		nb_discr = C_RECORD(ptr)->nb_discr_c;
		ptr1 = ptr + WORDS_C_RECORD;
		for (i = 0; i < nb_discr; i++) {
			POP(value);
			*ptr1++ = value;
			discr_list[i] = value;
		}
		if (TYPE(ptr2) == TT_U_RECORD)
			SIZE(ptr) = SIZE(ptr2);
		else if (TYPE(ptr2) == TT_V_RECORD) {
			/* Here compute size of the subtype */
			SIZE(ptr) = actual_size (ptr2,discr_list);
		}
		break;

	case TT_D_RECORD:
		update_address (&(D_TYPE(ptr)->dbase));
		nb_discr = D_TYPE(ptr)->nb_discr_d;
		ptr2 = ptr + WORDS_D_TYPE + 2 * nb_discr - 1;
		for (i = 1; i <= nb_discr; i++) {
			POP(value);
			*ptr2 = value;
			ptr2 -= 2;
		}
		break;

	case TT_TASK:
		update_address (&(TASK(ptr)->body_base));
		ptr1   = ptr + WORDS_TASK;
		offset = 0;
		for (i = 1; i <= TASK(ptr)->nb_families; i++) {
			bse = *ptr1;
			off = *(ptr1 + 1);
			if (bse == 0 && off == 0) {		 /* Simple entry */
				*ptr1++ = offset;
				*ptr1++ = 1;
				offset += 1;
			}
			else {
				if (bse == 0) {			 /* Index subtype is local */
					bse = STACK_FRAME(off);
					off = STACK_FRAME(off+1);
				}
				lbd = I_RANGE(ADDR(bse, off))->ilow;
				ubd = I_RANGE(ADDR(bse, off))->ihigh;
				lng = ubd - lbd +1;
				*ptr1++ = offset - lbd;
				*ptr1++ = lng;
				offset += lng;
			}
		}
		TASK(ptr)->nb_entries = offset;
		break;


	default:
		raise (SYSTEM_ERROR, "Elaborate unknown type");
	}

	if (flag == 1)
		PUSH_ADDR(templ_bse,templ_off);
}

void subprogram(int bse, int off) 						/*;subprogram*/
{
	ptr = ADDR(bse, off);
	if (*ptr < 0)
		*ptr = -*ptr;		/* mark the procedure as elab. */

	/* copy relay table */

	POP_ADDR(bas1, off1);	/* subprogram template */
	ptr1 = ADDR(bas1, off1);
	if ((slot = SUBPROG(ptr1)->relay_slot) != 0) {
		ptr1 = ADDR(1, *ADDR(1,0));
		while (*ptr1 != slot)
			ptr1 += *(ptr1 + 1) + 2;
		ptr1 += 2;
	}
	else
		ptr1 += WORDS_SUBPROG;

	value = SIZE(ptr);		/* # of relayed objects */
	ptr += 2;
	for (i = 1; i <= value; i++) {
		sp = sfp + *ptr1++;
		*ptr++ = cur_stack[sp];
		*ptr++ = cur_stack[sp + 1];
	}
}

int compute_offset(int from_field, int to_field, int  field_offset,
  int next_case, int *field_table_ptr, int * case_table_ptr) /*;compute_offset*/
{
	int     i, *field_ptr, type_base, type_off, *type_ptr, *case_ptr,
	  max_field_offset, nb_choices,last_offset;

	field_ptr = field_table_ptr + 3 * from_field;
	for (i = from_field; i <= to_field; i++) {
		*field_ptr = field_offset;
		update_address(field_ptr += 1);
		type_base = *field_ptr;
		type_off = *++field_ptr;
		type_ptr = ADDR(type_base, type_off);
		field_offset += SIZE(type_ptr);
		field_ptr++;
	}

	max_field_offset = field_offset;
	if (next_case != -1) {
		case_ptr = case_table_ptr + next_case + 1;
		nb_choices = *case_ptr;

		for (i = 1; i <= nb_choices; i++) {
			from_field = *++case_ptr;
			to_field = *++case_ptr;
			next_case = *++case_ptr;
			last_offset = compute_offset(
			    from_field, to_field,
			    field_offset,
			    next_case,
			    field_table_ptr,
			    case_table_ptr);
			if (last_offset > max_field_offset)
				max_field_offset = last_offset;
			case_ptr++;
		}
	}
	return max_field_offset;
}

static void update_address(int *addr_ptr)					/*;update_address*/
{
	int     type_base, type_off;

	type_base = *addr_ptr;
	if (type_base == 0) {	/* local address */
		type_off = *(addr_ptr + 1);
		type_base = STACK_FRAME(type_off);
		type_off = STACK_FRAME(type_off + 1);
		*addr_ptr = type_base;
		*(addr_ptr + 1) = type_off;
	}
}

void raise(int exception_value, char *reason)					/*;raise*/
{
	if (exception_trace && cs > 2) {
		printf("raising exception %s in %s",
		  exception_slots[exception_value],code_slots[cs]);
		if(lin>0)
			printf(" at line %d",lin);
		if(*reason != '\0')
			printf(" (%s)\n",reason);
		else
			printf("\n");
	}
	if(*reason != '\0') {
		raise_cs = cs;
		raise_lin = lin;
		raise_reason = reason;
	}
	exr = exception_value;
	terminate_unactivated();
	ip = BLOCK_FRAME->bf_handler;
	BLOCK_FRAME->bf_handler = 0;
}

static void image_attribute()							/*;image_attribute*/
{
	char    s[MAX_IDLEN];	/* chars and length of string */
	int     slen;		/* length of string */
	long    lv;

	POP_ADDR(bse, off);	/* type */
	ptr = ADDR(bse, off);
	val1 = TYPE(ptr);

	if (val1 == TT_E_RANGE) {	/* take base type */
		bse = E_RANGE(ptr)->ebase;
		off = E_RANGE(ptr)->eoff;
		ptr = ADDR(bse, off);
		val1 = TYPE(ptr);
	}

	if (val1 == TT_ENUM) {
		POP(value);
		ptr += WORDS_E_RANGE;
		if(*ptr == -1) { /* special case for CHARACTER */
			slen = 3;
			s[0] = s[2] = 39; /* prime character */
			s[1] = value;
		}
		else {
			for (i = 1; i <= value; i++)
				ptr = ptr + *ptr + 1;

			slen = *ptr++;
			for (i = 0; i < slen; i++)
				s[i] = *ptr++;
		}
	}
	else {
		if (val1 == TT_I_RANGE) {
			POP(value);
			lvalue = value;
		}
#ifdef LONG_INT
		else			 /* val1 = TT_L_RANGE */
			POPL(lvalue);
#endif
                if (value == MIN_INTEGER) {
                   slen = strlen(MIN_INTEGER_IMAGE);
                   strcpy(s, MIN_INTEGER_IMAGE);
		}
		else {
		   lv = ABS(value);
		   i = MAX_IDLEN-1;
		   if (lv == 0)
			s[i--] = '0';
		   while (lv != 0) {
			s[i--] = (lv % 10) + '0';
			lv = lv / 10;
		   }
		   if (lvalue < 0)
			s[i] = '-';
		   else
			s[i] = ' ';
		   slen = 0;
		   while (i < MAX_IDLEN)
			s[slen++] = s[i++];
                }
	}

	create(slen, &bas1, &off1, &ptr1);
	for (i = 0; i < slen; i++)
		*ptr1++ = s[i];
	PUSH_ADDR(bas1, off1);
	create(WORDS_S_ARRAY, &bas2, &off2, &ptr2);
	S_ARRAY(ptr2)->ttype = TT_S_ARRAY;
	S_ARRAY(ptr2)->object_size = slen;
	S_ARRAY(ptr2)->index_size = 1;
	S_ARRAY(ptr2)->component_size = 1;
	S_ARRAY(ptr2)->salow = 1;
	S_ARRAY(ptr2)->sahigh = slen;
	PUSH_ADDR(bas2, off2);
}

static void value_attribute()							/*;value_attribute*/
{
	int    *s;			/* pointer to string chars */
	int     slen;		/* length of string */
	int    i;			/* string index */

	POP_ADDR(bse, off);	/* type */
	ptr = ADDR(bse, off);
	POP_ADDR(bas1, off1);	/* string template */
	ptr1 = ADDR(bas1, off1);
	POP_ADDR(bas2, off2);	/* string value */
	s = ADDR(bas2, off2);
	slen = SIZE(ptr1);
	if (slen) { 		/* point to end */
		s += slen; 
		s--;
	}
	while (slen > 0 && *s == ' ') {
		s--;  
		slen--;		/* get rid of the trailing blanks */
	}
	s = ADDR(bas2, off2);
	while (slen > 0 && *s == ' ') {
		s++;  
		slen--;		/* get rid of the leading blanks */
	}
	i = 0;
	while (i < slen)        /* convert to C string */
		work_string[i++] = (char)*s++;
	work_string[i] = '\0';

	if (setjmp(raise_env)) {
		data_exception = DATA_ERROR;
		return;
	}
	data_exception = CONSTRAINT_ERROR;

	val1 = TYPE(ptr);
	if (val1 == TT_ENUM || val1 == TT_E_RANGE)
		value = enum_ord(ptr, slen, CONSTRAINT_ERROR);

	else if (val1 == TT_I_RANGE
#ifdef LONG_INT
	    || val1==TT_L_RANGE
#endif
	    ) { /* second argument is dummy */
		lvalue = scan_integer_string(ptr,&i);
		if ((i+1) != slen)			/* If not all scanned */
			raise(CONSTRAINT_ERROR, "Number not integer literal for VALUE");
	}
	if (val1 == TT_I_RANGE) {
		value = (int) lvalue;
		if (value == lvalue)
			PUSH(value);
		else
			raise(CONSTRAINT_ERROR, "Number out of range for VALUE");
	}
	else
		PUSH(value);
}

void create_structure()									/*;create_structure*/
{

	POP_ADDR(bse, off);
	ptr = ADDR(bse, off);
	val1 = TYPE(ptr);
	val2 = SIZE(ptr);

	switch(val1) {

	case TT_U_ARRAY:
	case TT_C_ARRAY:
	case TT_S_ARRAY:
	case TT_D_ARRAY:
		create(val2, &bas1, &off1, &ptr1);
		PUSH_ADDR(bas1, off1);
		PUSH_ADDR(bse, off);			/* push type template */
		break;

	case TT_RECORD:
		create(val2, &bas1, &off1, &ptr1);
		PUSH_ADDR(bas1, off1);
		break;

	case TT_U_RECORD:
	case TT_V_RECORD:
		create(val2, &bas1, &off1, &ptr1);
		PUSH_ADDR(bas1, off1);
		*ptr1 = 0;		/* unconstrained */
		/* initialize the full record for the shake of comparisons.
		 * note that the value used does not matter but has to be
		 * the same in the code generator. If zero is used, 
		 * the constraint bit might be included in that loop.
		 */
		for (i = 1; i < val2; i++)
			*(ptr1 + i) = 0;
		break;

	case TT_C_RECORD:
		create(val2, &bas1, &off1, &ptr1);
		PUSH_ADDR(bas1, off1);
		*ptr1 = 1;		/* constrained */
		nb_discr = C_RECORD(ptr)->nb_discr_c;

		for (i = 1; i <= nb_discr; i++)
			*(ptr1 + i) = *(ptr + WORDS_C_RECORD  + i);
		break;

	case TT_D_RECORD:       /* to be checked */
		create(val2, &bas1, &off1, &ptr1);
		PUSH_ADDR(bas1, off1);
		*ptr1++ = 1;	/* constrained */
		nb_discr = C_RECORD(ptr)->nb_discr_c;

		for (i = 1; i <= nb_discr; i++)
			*ptr1++ = *(ptr++ + WORDS_C_RECORD + i);
		break;

	case TT_SUBPROG:
		if ((slot = SUBPROG(ptr)->relay_slot) != 0) {
			ptr2 = ADDR(1, *ADDR(1,0));
			while (*ptr2 != slot)
				ptr2 += *(ptr2 + 1) + 2;
			val2 = *(ptr2 + 1);/* # of relayed objects */
		}
		create(2 * val2 + 2, &bas1, &off1, &ptr1);
		*ptr1 = -SUBPROG(ptr)->cs;/* Not yet elab. */
		*(ptr1 + 1) = val2;
		PUSH_ADDR(bas1, off1);
		break;

	default:
		raise(SYSTEM_ERROR, "Creating object of unknown type");
	}
}

void create_copy_struc()						/*;create_copy_struc*/
{
	POP_ADDR(bse, off);	/* type */
	ptr = ADDR(bse, off);
	POP_ADDR(bas2, off2);	/* value */
	ptr2 = ADDR(bas2, off2);

	val1 = TYPE(ptr);
	val2 = SIZE(ptr);
	create(val2, &bas1, &off1, &ptr1);
	PUSH_ADDR(bas1, off1);

	switch(val1) {
	case TT_U_ARRAY:
	case TT_C_ARRAY:
	case TT_S_ARRAY:
	case TT_D_ARRAY:
		if (val2 > 0) {	/* copy the object */
			for (i = 1; i <= val2; i++)
				*ptr1++ = *ptr2++;
		}
		if (bse >= heap_base) {
			/* create new type template */
			val2 = *(ptr - WORDS_HDR) - WORDS_HDR;
			/* size of template */
			create(val2, &bas3, &off3, &ptr3);
			for (i = 1; i <= val2; i++)
				*ptr3++ = *ptr++;
		}
		else {
			bas3 = bse;	/* static template, use same */
			off3 = off;
		}
		PUSH_ADDR(bas3, off3);
		break;

	case TT_RECORD:
	case TT_C_RECORD:
	case TT_U_RECORD:
	case TT_D_RECORD:
	case TT_V_RECORD:
		for (i = 1; i <= val2; i++)
			*ptr1++ = *ptr2++;
		break;
	}
}

void compare_struc()									/*;compare_struc*/
{
	POP_ADDR(bse, off);	                /* type */
	ptr3 = ADDR(bse, off);
	length1 = SIZE(ptr3);
	POP_ADDR(bse, off);	                /* first value */
	ptr1 = ADDR(bse, off);

	switch TYPE(ptr3) {		/* type of type */
	case TT_U_ARRAY:
	case TT_C_ARRAY:
	case TT_S_ARRAY:
	case TT_D_ARRAY:
		POP_ADDR(bse, off);         /* type of the other one */
		ptr4 = ADDR(bse, off);
		length2 = SIZE(ptr4);
		POP_ADDR(bse, off);	        /* second value */
		if (length1 != length2) {
			PUSH(FALSE);
			return;
		}
		if (length1 == 0) {
			PUSH(TRUE);
			return;
		}
		if ((TYPE(ptr3) == TT_U_ARRAY || TYPE(ptr3) == TT_C_ARRAY)
		    && !same_dimensions(ptr3, ptr4)) {
			PUSH(FALSE);
			return ;
		}
		ptr2 = ADDR(bse, off);
		break;

	case TT_RECORD:
	case TT_U_RECORD:
	case TT_C_RECORD:
	case TT_D_RECORD:
		POP_ADDR(bse, off);	/* second value */
		ptr2 = ADDR(bse, off);
		if (TYPE(ptr3) != TT_RECORD) {
			ptr1 += 1; /* skip constraint bit */
			ptr2 += 1;
			length1 -= 1;
		}
		/*
		else {
			PUSH (compare_fields_record (ptr1, ptr2, ptr3));
			return;
	    }
		*/
		break;
	}

	while (length1-- > 0) {
		val1 = *ptr1++;
		val2 = *ptr2++;
		if (val1 != val2) {
			PUSH(FALSE);
			return;
		}
	}
	PUSH(TRUE);
}

void compare_arrays()									/* compare_arrays */
{
	int eq_val;
	int inf_val;

	POP_ADDR(bse, off);             /* type */
	ptr3 = ADDR(bse, off);
	length1 = SIZE(ptr3);
	POP_ADDR(bse, off);             /* first value */
	ptr1 = ADDR(bse, off);
	POP_ADDR(bse, off);             /* type of the other one */
	ptr4 = ADDR(bse, off);
	length2 = SIZE(ptr4);
	POP_ADDR(bse, off);             /* second value */
	ptr2 = ADDR(bse, off);
	eq_val = (length1 == length2);
	inf_val = (length1 < length2);
	if (length1 <= length2) {
		if (length2 == 0) {
			eq_val  = 1;
			inf_val = 0;
		}
		else if (length1 == 0) {
			eq_val  = 0;
			inf_val = 1;
		}
		else {
			while (length1-- > 0) {
				if ((val1 = *ptr1++) < (val2 = *ptr2++)) {
					eq_val  = 0;
					inf_val = 1;
					break;
				}
				else if (val1 > val2) {
					eq_val  = 0;
					inf_val = 0;
					break;
				}
			}
		}
	}
	else {
		while (length2-- > 0) {
			if ((val2 = *ptr2++) > (val1 = *ptr1++)) {
				eq_val  = 0;
				inf_val = 1;
				break;
			}
			else if (val2 < val1) {
				eq_val  = 0;
				inf_val = 0;
				break;
			}
			else if (length2 == 0) {
				eq_val  = 0;
				inf_val = 0;
			}
		}
	}
	PUSH(eq_val+2*inf_val);
}

void array_slice()										/*;array_slice*/
{
	int     low_bound, high_bound, length;

	POP_ADDR(bse, off);	/* type */
	ptr = ADDR(bse, off);
	POP_ADDR(bas1, off1);	/* value */

	/* extract bounds and size of component */

	if (TYPE(ptr) == TT_S_ARRAY) {
		component_size = S_ARRAY(ptr)->component_size;
		high_bound = S_ARRAY(ptr)->sahigh;
		low_bound = S_ARRAY(ptr)->salow;
	}
	else if (TYPE(ptr) == TT_C_ARRAY) {
		bse = ARRAY(ptr)->component_base;
		off = ARRAY(ptr)->component_offset;
		component_size = SIZE(ADDR(bse, off));
		bse = ARRAY(ptr)->index1_base;
		off = ARRAY(ptr)->index1_offset;
		high_bound = I_RANGE(ADDR(bse, off))->ihigh;
		low_bound = I_RANGE(ADDR(bse, off))->ilow;
	}

	POP(val_high);
	POP(val_low);
	if (val_high < val_low)				/* make null slice if null */
		length = 0;
	else if (val_high > high_bound || val_low < low_bound) {
		raise(CONSTRAINT_ERROR, "Slice index out of bounds");
		return;
	}
	else
		length = val_high - val_low + 1;
	size = length * component_size;
	off1 = off1 + (val_low - low_bound) * component_size;
	PUSH_ADDR(bas1, off1);

	create(WORDS_S_ARRAY, &bse, &off, &ptr);
	S_ARRAY(ptr)->ttype = TT_S_ARRAY;
	S_ARRAY(ptr)->object_size = size;
	S_ARRAY(ptr)->component_size = component_size;
	S_ARRAY(ptr)->index_size = 1;
	S_ARRAY(ptr)->salow = val_low;
	S_ARRAY(ptr)->sahigh = val_high;
	PUSH_ADDR(bse, off);
}

/* ARRAY_CATENATE */

void array_catenate()									/*;array_catenate*/
{
	int     catsize, val_low, val_high, rlow, rhigh, index_kind;

	POP_ADDR(bse, off);	/* type of result for qual */
	ptr = ADDR(bse, off);

	/* right argument */

	POP_ADDR(bas1, off1);	/* type of right arg */
	ptr1 = ADDR(bas1, off1);
	POP_ADDR(bas2, off2);	/* right arg */
	ptr2 = ADDR(bas2, off2);

	/* left operand */

	POP_ADDR(bas3, off3);	/* type */
	ptr3 = ADDR(bas3, off3);
	POP_ADDR(bas4, off4);
	ptr4 = ADDR(bas4, off4);

	/* empty arrays */

	if ((length2 = SIZE(ptr3)) == 0) {
		PUSH_ADDR(bas2, off2);
		PUSH_ADDR(bas1, off1);
		return;			/* result is right operand */
	}
	if ((length1 = SIZE(ptr1)) == 0) {
		PUSH_ADDR(bas4, off4);
		PUSH_ADDR(bas3, off3);
		return;			/* result is left operand */
	}

	/* get lower bound of left */

	if (*ptr3 == TT_S_ARRAY) {
		val_low = S_ARRAY(ptr3)->salow;
		index_kind = S_ARRAY(ptr3)->index_size;
		component_size = S_ARRAY(ptr3)->component_size;
	}

	else if (*ptr3 == TT_C_ARRAY || *ptr3 == TT_U_ARRAY) {
		component_size = SIZE(ADDR(ARRAY(ptr3)->component_base,
		  ARRAY(ptr3)->component_offset));
		val_low = I_RANGE(ADDR(ARRAY(ptr3)->index1_base,
		  ARRAY(ptr3)->index1_offset))->ilow;
		index_kind = SIZE(ADDR(ARRAY(ptr3)->index1_base,
		  ARRAY(ptr3)->index1_offset));
	}

	catsize = length2 + length1;
	val_high = val_low +(catsize / component_size) - 1;

	/* get bounds of result */

	if (*ptr == TT_S_ARRAY) {
		rlow = S_ARRAY(ptr)->salow;
		rhigh = S_ARRAY(ptr)->sahigh;
	}
	else if (*ptr == TT_C_ARRAY || *ptr == TT_U_ARRAY) {
		rlow = I_RANGE(ADDR(ARRAY(ptr)->index1_base,
		  ARRAY(ptr)->index1_offset))->ilow;
		rhigh = I_RANGE(ADDR(ARRAY(ptr)->index1_base,
		  ARRAY(ptr)->index1_offset))->ihigh;
	}

	/* check bounds */

	if (val_low < rlow || val_high > rhigh) {
		raise(CONSTRAINT_ERROR, "Array catenate");
		return;
	}

	/* everything ok: do the job */

	create(catsize, &bse, &off, &ptr);
	for (i = 0; i < length2; i++)
		*ptr++ = *ptr4++;
	for (i = 0; i < length1; i++)
		*ptr++ = *ptr2++;

	PUSH_ADDR(bse, off);

	create(WORDS_S_ARRAY, &bse, &off, &ptr);
	S_ARRAY(ptr)->ttype = TT_S_ARRAY;
	S_ARRAY(ptr)->object_size = catsize;
	S_ARRAY(ptr)->component_size = component_size;
	S_ARRAY(ptr)->index_size = index_kind;
	S_ARRAY(ptr)->salow = val_low;
	S_ARRAY(ptr)->sahigh = val_high;
	PUSH_ADDR(bse, off);
}

void subscript()												/*;subscript*/
{
	POP_ADDR(bas1, off1);	/* type */
	POP_ADDR(bse, off);	/* array */
	ptr1 = ADDR(bas1, off1);

	val1 = TYPE(ptr1);		/* type of type */
	if (val1 == TT_S_ARRAY) {
		POP(value);
		val2 = S_ARRAY(ptr1)->component_size;
		val_low = S_ARRAY(ptr1)->salow;
		val_high = S_ARRAY(ptr1)->sahigh;
		if (value < val_low || value > val_high)
			raise(CONSTRAINT_ERROR, "Index out of bounds");
		result = (value - val_low) * val2;
	}

	else if ((val1 == TT_C_ARRAY) ||(val1 == TT_U_ARRAY)) {
		bas1 = ARRAY(ptr1)->component_base;
		off1 = ARRAY(ptr1)->component_offset;
		val1 = SIZE(ADDR(bas1, off1));/* size of component */
		val2 = ARRAY(ptr1)->dim;
		result = 0;
		delta = 1;
		ptr1 = &(ARRAY(ptr1)->index1_base);
		for (i = 1; i <= val2; i++) {
			POP(value);
			bas2 = *ptr1++;
			off2 = *ptr1++;
			ptr2 = ADDR(bas2, off2);
			val_low = I_RANGE(ptr2)->ilow;
			val_high = I_RANGE(ptr2)->ihigh;
			if (value < val_low || value > val_high) {
				raise(CONSTRAINT_ERROR, "Index out of bounds");
			}
			value = value - val_low;
			result = (value * delta) + result;
			delta = delta *(val_high - val_low + 1);
		}
		result = result * val1;
	}
	else
		raise(SYSTEM_ERROR, "Illegal array type");
	off += result;
	PUSH_ADDR(bse, off);
}

void array_move()												/*;array_move*/
{
	POP_ADDR(bse, off);	/* type of the value */
	ptr1 = ADDR(bse, off);
	POP_ADDR(bse, off);	/* value */
	ptr2 = ADDR(bse, off);

	POP_ADDR(bse, off);	/* type of the object */
	ptr3 = ADDR(bse, off);
	POP_ADDR(bse, off);	/*  object */
	ptr4 = ADDR(bse, off);

	length1 = SIZE(ptr1);
	length2 = SIZE(ptr3);
	/* : The test of the length equalities has to be done at first otherwise
	 * "a := b" will be valid if a is a null array and b a non null one
	 */
	if (length1 != length2)
		raise(CONSTRAINT_ERROR, "Arrays not same length");
	else if (length1 == 0) return; /* null array */
	else {
		if (ptr4 < ptr2) {
			for (i = 0; i <= length2 - 1; i++)	/* copy in ascending order */
				*(ptr4 + i) = *(ptr2 + i);
		}
		else {
			ptr4 += length2;	/* copy in descending order */
			ptr2 += length2;
			for (i = 1; i <= length2; i++)
				*(ptr4 - i) = *(ptr2 - i);
		}
	}
}

static int same_dimensions(int *temp1, int *temp2)		/*;same_dimensions */
{
	int *p1, *p2, *p3 ;
	int low1, low2, high1, high2;
	int d ;
	/* When comparing multidimensional arrays, must check that they have
	 * the same dimensions (otherwise a 2 by 3 array might check equal to a
	 * 3 by 2 array. See c34005m).
	 */

	d = ARRAY(temp1)->dim;
	if (d == 1) return (TRUE) ;
	p1 = &(ARRAY(temp1)->index1_base);
	p2 = &(ARRAY(temp2)->index1_base);
	for (i = 1; i <= d; i++) {
		bas1  = *p1++;
		off1  = *p1++;
		p3    = ADDR(bas1, off1);		/* template of 1st index type */
		low1  = I_RANGE(p3)->ilow;
		high1 = I_RANGE(p3)->ihigh;

		bas2  = *p2++;
		off2  = *p2++;
		p3    = ADDR(bas2, off2);		/* template of 2nd index type */
		low2  = I_RANGE(p3)->ilow;
		high2 = I_RANGE(p3)->ihigh;
		if (high1 - low1 != high2 - low2)
			return (FALSE) ;
	}
	return TRUE ;
}

static int compare_fields_record (int *v_ptr1, int *v_ptr2, int *itemplate)
													/*;compare_fields_record*/
{
	/* this procedure allows the comparison of record.
	 * The comparison is not straightfoward if one in unconstrained
	 * and the other is constrained or if there are variant parts.
	 * This procedure was not intended to be completed. It was just a
	 * test  to solve one acv test of c3.
	 * This procedure is not called from the Ada machine because it
	 * slows down the comparison.
	 * Nevertheless, this case has to be taken into account for future
	 * work
	*/
	int length1, *ptr1, *ptr2 ;
	int i, nb_field, type_base, type_off, *type_ptr, *field_ptr;
	int field_offset;

	ptr1 = v_ptr1;
	ptr2 = v_ptr2;

	switch TYPE (itemplate) {
	case TT_RECORD:
		nb_field = RECORD(itemplate)->nb_field;
		field_ptr = itemplate + WORDS_RECORD;
		for (i = 1; i <= nb_field; i++) {
			field_offset = *field_ptr;
			field_ptr = field_ptr + 1;
			type_base = *field_ptr;
			type_off = *++field_ptr;
			type_ptr = ADDR(type_base, type_off);
			if (!compare_fields_record (v_ptr1 + field_offset,
			    v_ptr2 + field_offset, type_ptr)) {
				return FALSE;
			}
			field_ptr++;
		}
		return TRUE;

	case TT_U_RECORD:
	case TT_C_RECORD:
	case TT_D_RECORD:
		length1 = SIZE (itemplate);
		ptr1 += 1; /* skip constraint bit */
		ptr2 += 1;
		length1 -= 1;
		break;

	default:
		length1 = SIZE (itemplate);
		break;
	}
	while (length1-- > 0) {
		val1 = *ptr1++;
		val2 = *ptr2++;
		if (val1 != val2)
			return FALSE;
	}
	return TRUE;
}
