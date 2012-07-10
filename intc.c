/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* continuation of interpreter procedures - part c */

/* include standard header files */
#include <stdlib.h>
#include "config.h"
#include "int.h"
#include "ivars.h"
#include "machineprots.h"
#include "farithprots.h"
#include "intaprots.h"
#include "intbprots.h"
#include "intcprots.h"

static int get_variable_bound(int *, int []);

void rselect(int field)									 			/*;rselect*/
{
	/*
	 *   Perform the Ada record selection operation:
	 *
	 *     Get the address of the record type template from the TOS
	 *     Get the address of the record object from the TOS
	 *     Get the number of the component(or field) from the instruction
	 *	 stream
	 *
	 *     Check the existence of that particular component in that particular
	 *     record(and raise CONSTRAINT_ERROR otherwise)
	 *
	 *     Push the absolute address of the component on TOS. If component
	 *     is an array, push also the address of the array type template.
	 *     If the type of this array depends on a discriminant of the  record
	 *     a template must be dynamically built.
	 */

	int
	type_base, type_off, record_base, record_off, field_offset,
	    *type_ptr, *record_ptr, *field_table_ptr, *case_table_ptr,
	    *case_ptr, type_type, next_case, discr_number, discr_offset,
	    first_field, last_field, value_discr, val_high, nb_choices,
	    nb_field, nb_fixed, *field_ptr, *component_ptr, *a_type_ptr,
	    *u_type_ptr, nb_dim, low, high, comp_off, comp_base, component_size,
	    object_size, template_size, *new_type_ptr, *some_ptr;

	POP_ADDR(type_base, type_off);
	POP_ADDR(record_base, record_off);
	type_ptr = ADDR(type_base, type_off);
	record_ptr = ADDR(record_base, record_off);
	type_type = TYPE(type_ptr);

	/* constrained record subtype */

	if (type_type == TT_C_RECORD) { 		/* find base type */
		type_base = C_RECORD(type_ptr)->cbase;
		type_off = C_RECORD(type_ptr)->coff;
		type_ptr = ADDR(type_base, type_off);
		type_type = TYPE(type_ptr);
	}
	else if (type_type == TT_D_RECORD) {
		type_base = D_TYPE(type_ptr)->dbase;
		type_off = D_TYPE(type_ptr)->doff;
		type_ptr = ADDR(type_base, type_off);
		type_type = TYPE(type_ptr);
	}
	else if (type_type == TT_RECORD) {
		field_table_ptr = type_ptr + WORDS_RECORD;
		nb_fixed = RECORD(type_ptr)->nb_field;
	}

	if (type_type == TT_U_RECORD || type_type == TT_V_RECORD) {
		nb_fixed = U_RECORD(type_ptr)->nb_fixed_u;
		nb_field = U_RECORD(type_ptr)->nb_field_u;
		field_table_ptr = type_ptr + WORDS_U_RECORD;
		case_table_ptr = field_table_ptr + 3 * nb_field;
	}

	/* The result is simple to obtain... unless the record has varying size */

	if (type_type == TT_V_RECORD) {
		field_offset = 0;
		first_field = 0;
		last_field = nb_fixed - 1;
		next_case = U_RECORD(type_ptr)->first_case;
		nb_discr = U_RECORD(type_ptr)->nb_discr_u;

		for (i = 0; i < nb_discr; i++)
			discr_list[i] = *(record_ptr + i);

		for (;;) {
			field_ptr = 3 * first_field + field_table_ptr;
			for (i = first_field; i <= MIN((field - 1), last_field); i++) {
				/* accumulate size of components */
				component_ptr = ADDR(*(field_ptr + 1), *(field_ptr + 2));
				field_offset += actual_size(component_ptr, discr_list);
				field_ptr += 3;
			}

			if (field >= first_field && field <= last_field) {
				break;
			}
			else if (field < first_field  
			  ||(field > last_field && next_case == -1)) {

				raise(CONSTRAINT_ERROR, "Record component not present");
				return;
			}

			/*  We have : field > last_field and next_case /= -1 */

			case_ptr = case_table_ptr + next_case;
			discr_number = *case_ptr++;
			discr_offset = *(field_table_ptr + 3 * discr_number);
			value_discr = *(record_ptr + discr_offset);
			nb_choices = *case_ptr;
			case_ptr += 4;
			val_high = *case_ptr;
			for (i = 2; i <= nb_choices; i++) {
				if (val_high > value_discr)
					break;
				case_ptr += 4;
				val_high = *case_ptr;
			}
			next_case = *--case_ptr;
			last_field = *--case_ptr;
			first_field = *--case_ptr;
		}
		field_ptr = field_table_ptr + 3 * field;
	}

	/* Record is not varying */

	else {
		field_ptr = field_table_ptr + 3 * field;
		field_offset = *field_ptr;
	}

	PUSH_ADDR(record_base, field_offset + record_off);

	/* check if component is an array */

	type_base = *(field_ptr + 1);
	type_off = *(field_ptr + 2);
	type_type = TYPE(ADDR(type_base, type_off));

	if ( type_type == TT_S_ARRAY
	  || type_type == TT_U_ARRAY
	  || type_type == TT_C_ARRAY
	  || type_type == TT_D_ARRAY) {

		if (type_type == TT_D_ARRAY) {
			/* must build a type template */
			/* necessarily the record is a TT_V_RECORD or a TT_U_RECORD with */
			/* default values for the discriminants */
			nb_discr = U_RECORD(type_ptr)->nb_discr_u;
			for (i = 0; i < nb_discr; i++)
				discr_list[i] = *(record_ptr + i);
			a_type_ptr = ADDR(type_base, type_off);
			nb_dim = D_TYPE(a_type_ptr)->nb_discr_d;
			type_base = D_TYPE(a_type_ptr)->dbase;
			type_off = D_TYPE(a_type_ptr)->doff;
			u_type_ptr = ADDR(type_base, type_off);
			a_type_ptr += WORDS_D_TYPE;/* =bounds */
			type_type = *u_type_ptr;

			if (nb_dim == 1) {
				/* unidimensional case: we build an s_array */
				low = get_variable_bound(a_type_ptr, discr_list);
				a_type_ptr += 2;
				high = get_variable_bound(a_type_ptr, discr_list);
				if (type_type == TT_S_ARRAY) {
					component_size = S_ARRAY(u_type_ptr)->component_size;
				}
				else {
					comp_base = ARRAY(u_type_ptr)->component_base;
					comp_off = ARRAY(u_type_ptr)->component_offset;
					component_size = SIZE(ADDR(comp_base, comp_off));
				}
				object_size = component_size *(high - low + 1);
				if (object_size < 0)
					object_size = 0;

				create(WORDS_S_ARRAY, &type_base, &type_off, &new_type_ptr);
				S_ARRAY(new_type_ptr)->ttype = TT_S_ARRAY;
				S_ARRAY(new_type_ptr)->object_size = object_size;
				S_ARRAY(new_type_ptr)->component_size = component_size;
				S_ARRAY(new_type_ptr)->index_size = 1;
				S_ARRAY(new_type_ptr)->salow = low;
				S_ARRAY(new_type_ptr)->sahigh = high;
			}

			else {		/* nb_dim > 1 */
				template_size = 2 *(nb_dim - 1) + WORDS_ARRAY;
				create(template_size, &type_base, &type_off, &new_type_ptr);
				ARRAY(new_type_ptr)->ttype = TT_C_ARRAY;
				ARRAY(new_type_ptr)->dim = nb_dim;
				comp_base = ARRAY(u_type_ptr)->component_base;
				comp_off = ARRAY(u_type_ptr)->component_offset;
				ARRAY(new_type_ptr)->component_base = comp_base;
				ARRAY(new_type_ptr)->component_offset = comp_off;
				component_size = SIZE(ADDR(comp_base, comp_off));
				/* Beware: indices in reverse order */
				some_ptr = new_type_ptr + WORDS_ARRAY + 2 * nb_dim - 3;
				for (i = 1; i <= nb_dim; i++) {
					low = get_variable_bound(a_type_ptr, discr_list);
					a_type_ptr += 2;
					high = get_variable_bound(a_type_ptr, discr_list);
					a_type_ptr += 2;
					create(WORDS_I_RANGE, &bas2, &off2, &ptr2);
					TYPE(ptr2) = TT_I_RANGE;
					SIZE(ptr2) = 1;
					I_RANGE(ptr2)->ilow = low;
					I_RANGE(ptr2)->ihigh = high;
					*some_ptr-- = off2;
					*some_ptr-- = bas2;
					if (high >= low)
						component_size *= (high - low + 1);
					else
						component_size = 0;
				}
				SIZE(new_type_ptr) = component_size;
			}
		}
		PUSH_ADDR(type_base, type_off);
	}

	/*  no check to perform if done already for varying size records */

	if (type_type == TT_V_RECORD)
		return;

	first_field = 0;
	last_field = nb_fixed - 1;
	next_case = U_RECORD(type_ptr)->first_case;

	for (;;) {
		if ((field >= first_field) &&(field <= last_field)) {
			return;
		}
		else if (field < first_field 
		    ||(field > last_field && next_case == -1)) {
			raise(CONSTRAINT_ERROR, "Record component not present");
			return;
		}

		/*  then we have : field > last_field and next_case /= -1 */

		case_ptr = case_table_ptr + next_case;
		discr_number = *case_ptr++;
		discr_offset = *(field_table_ptr + 3 * discr_number);
		value_discr = *(record_ptr + discr_offset);
		nb_choices = *case_ptr;
		case_ptr += 4;
		val_high = *case_ptr;
		for (i = 2; i <= nb_choices; i++) {
			if (val_high > value_discr) {
				break;
			}
			case_ptr += 4;
			val_high = *case_ptr;
		}
		next_case = *--case_ptr;
		last_field = *--case_ptr;
		first_field = *--case_ptr;
	}

}

static int get_variable_bound(int *bound_ptr, int discr_list[])
														/*;get_variable_bound*/
{
	int bound = *(bound_ptr + 1);
	if (*bound_ptr == 1)
		bound = discr_list[bound];
	return bound;
}

int actual_size(int *type_ptr, int discr_list[])				/*;actual_size*/
{
	/*
	 *     Returns the actual size of an object of the type designated by
	 *     type_ptr, with the discriminants of the enclosing record
	 *     given by discr_list
	 *
	 *     the real problem arises with discriminant dependant types and
	 *     varying length records(or their subtypes)
	 */

	int     new_discr_list[MAX_DISCR];
	int    *base_type_ptr, *discr_ptr, nb_discr, i, size, *component_ptr;
	int		nb_dim, low, high;
	int     nb_field, nb_fixed, *field_ptr, *case_table_ptr, *field_table_ptr;
	int     first_field, last_field, next_case, *case_ptr;
	int     discr_number, value_discr, nb_choices;

	if (TYPE(type_ptr) == TT_D_RECORD) {
		base_type_ptr = ADDR(D_TYPE(type_ptr)->dbase, D_TYPE(type_ptr)->doff);
		discr_ptr = type_ptr + WORDS_D_TYPE;
		nb_discr = D_TYPE(type_ptr)->nb_discr_d;
		for (i = 0; i < nb_discr; i++) {
			new_discr_list[i] = get_variable_bound(discr_ptr, discr_list);
#ifdef TBSN
			*discr_ptr++ = 0; /* To be checked: patch the template */
			*discr_ptr++ = new_discr_list[i];
#endif
			discr_ptr += 2;
		}
		size = actual_size(base_type_ptr, new_discr_list);
		SIZE(type_ptr) = size;
	}

	else if (TYPE(type_ptr) == TT_D_ARRAY) {
		base_type_ptr = ADDR(D_TYPE(type_ptr)->dbase, D_TYPE(type_ptr)->doff);
		discr_ptr = type_ptr + WORDS_D_TYPE;
		nb_dim = D_TYPE(type_ptr)->nb_discr_d;

		if ( TYPE(base_type_ptr) == TT_U_ARRAY
		  || TYPE(base_type_ptr) == TT_C_ARRAY) {
			component_ptr =
			  ADDR(ARRAY(base_type_ptr)->component_base,
			  ARRAY(base_type_ptr)->component_offset);
#ifdef TBSL
			-- note review use of NULL corresponding to setl []  ds 9-30-85
#endif
			    size = actual_size(component_ptr, NULL_INT);
		}
		else if (TYPE(base_type_ptr) == TT_S_ARRAY) {
			size = S_ARRAY(base_type_ptr)->component_size;
		}

		for (i = 1; i <= nb_dim; i++) {
			low = get_variable_bound(discr_ptr, discr_list);
#ifdef TBSN
			*discr_ptr++ = 0; /* to be checked: patch the template */
			*discr_ptr++ = low;
#endif
			discr_ptr += 2;
			high = get_variable_bound(discr_ptr, discr_list);
#ifdef TBSN
			*discr_ptr++ = 0; /* to be checked: patch the template */
			*discr_ptr++ = high;
#endif
			discr_ptr += 2;
			size = size *(MAX(0, high - low + 1));
		}
		SIZE(type_ptr) = size;
	}
	else if (TYPE(type_ptr) == TT_C_RECORD) {
		if ((size = SIZE(type_ptr)) < 0) {
			base_type_ptr = ADDR(C_RECORD(type_ptr)->cbase,
			  C_RECORD(type_ptr)->coff);
			nb_discr = C_RECORD(type_ptr)->nb_discr_c;
			for (i = 0; i < nb_discr; i++)
				new_discr_list[i] = *(type_ptr + WORDS_C_RECORD + i);
			size = actual_size(base_type_ptr, new_discr_list);
		}
	}

	else if (TYPE(type_ptr) == TT_V_RECORD) {
		nb_field = U_RECORD(type_ptr)->nb_field_u;
		nb_fixed = U_RECORD(type_ptr)->nb_fixed_u;
		field_table_ptr = type_ptr + WORDS_U_RECORD;
		case_table_ptr = field_table_ptr + 3 * nb_field;
		size = 0;
		first_field = 0;
		last_field = nb_fixed - 1;
		next_case = U_RECORD(type_ptr)->first_case;
		for (;;) {
			field_ptr = 3 * first_field + field_table_ptr;
			for (i = first_field; i <= last_field; i++) {
				/* accumulate size of components */
				component_ptr = ADDR(*(field_ptr + 1), *(field_ptr + 2));
				size += actual_size(component_ptr, discr_list);
				field_ptr += 3;
			}

			if (next_case == -1)
				break;

			/* we have : next_case != -1 */

			case_ptr = case_table_ptr + next_case;
			discr_number = *case_ptr++;
			value_discr = discr_list[discr_number];
			nb_choices = *case_ptr;
			case_ptr += 4;
			val_high = *case_ptr;
			for (i = 2; i <= nb_choices; i++) {
				if (val_high > value_discr)
					break;
				case_ptr += 4;
				val_high = *case_ptr;
			}
			next_case = *--case_ptr;
			last_field = *--case_ptr;
			first_field = *--case_ptr;
		}
	}

	else
		size = SIZE(type_ptr);

	return size;
}

void record_move(int *ptr_a, int *ptr_v, int *ptr_t)       /*;record_move*/
{
	int    discr;

	length1 = SIZE(ptr_t);

	switch(TYPE(ptr_t)) {

	case TT_RECORD:
		break;

	case TT_D_RECORD:
		nb_discr = D_TYPE(ptr_t)->nb_discr_d;
		ptr_a++;		/* skip constrained flag */
		ptr_v++;
		length1 -= nb_discr--;
		i = nb_discr;
		while (i-- > 0) {
			if (*ptr_a++ != *ptr_v++) {
				raise(CONSTRAINT_ERROR, "Discriminant");
				return;
			}
		}
		break;

	case TT_C_RECORD:
	case TT_U_RECORD:

		/* 	the type given must not be trusted, as this may be an assignment
		 * to some unconstrained out or in out parameter, in which case the
		 * 	status constrained is inherited from the actual
		 */

		if (*ptr_a == 0) { 	/* unconstrained */

			length1--;	/* constrained flag is not copied ! */
			ptr_a++;
			ptr_v++;
			for (i = 0; i < length1; i++)
				*ptr_a++ = *ptr_v++;
			return;
		}
		else {
			if (TYPE(ptr_t) == TT_C_RECORD)
				nb_discr = C_RECORD(ptr_t)->nb_discr_c;
			else
				nb_discr = U_RECORD(ptr_t)->nb_discr_u;
			ptr_a++;	/* skip contrained flag */
			ptr_v++;
			length1 -= nb_discr--;
			i = nb_discr;
			while(i-- > 0) {
				if (*ptr_a++ != *ptr_v++) {
					raise(CONSTRAINT_ERROR, "Discriminant");
					return;
				}
			}
		}
		break;

	case TT_V_RECORD:
		if (*ptr_a == 0) {	/* unconstrained */
			/* constrained flag is not copied ! */
			length1--;
			ptr_a++;
			ptr_v++;
			if (TYPE(ptr_t) == TT_C_RECORD)
				nb_discr = C_RECORD(ptr_t)->nb_discr_c;
			else
				nb_discr = U_RECORD(ptr_t)->nb_discr_u;
			discr_list[0] = *ptr_a;
			for (i = 1; i < nb_discr; i++) {
				/*
				discr = *ptr_a++;
		    	discr_list[i] = discr;
		    	if (discr != *ptr_v++) 
				raise(CONSTRAINT_ERROR, "Discriminant");
				return;
				*/
				discr_list [i] = *ptr_v;
				*ptr_a++ = *ptr_v++;
			}
			length1 = actual_size(ptr_t, discr_list) - nb_discr;
			for (i = 0; i < length1; i++)
				*ptr_a++ = *ptr_v++;
			return;
		}
		else {
			if (TYPE(ptr_t) == TT_C_RECORD)
				nb_discr = C_RECORD(ptr_t)->nb_discr_c;
			else
				nb_discr = U_RECORD(ptr_t)->nb_discr_u;
			discr_list[0] = *ptr_a;
			ptr_a++;	/* skip constrained flag */
			ptr_v++;
			for (i = 1; i < nb_discr; i++) {
				discr = *ptr_a++;
				discr_list[i] = discr;
				if (discr != *ptr_v++) {
					raise(CONSTRAINT_ERROR, "Discriminant");
					return;
				}
			}
			length1 = actual_size(ptr_t, discr_list) - nb_discr;
		}
		break;
	}

	for (i = 0; i < length1; i++)
		*ptr_a++ = *ptr_v++;
}

void membership()												/*;membership*/
{
	int     some_bool;

	POP_ADDR(bse, off);

	switch(TYPE(ADDR(bse, off))) {

	case TT_I_RANGE:
	case TT_E_RANGE:
	case TT_ENUM:
		POP(value);
		PUSH((I_RANGE(ADDR(bse, off))->ilow <=
		  I_RANGE(ADDR(bse,off))->ihigh) &&
		  (value >= I_RANGE(ADDR(bse, off))->ilow &&
		  value <= I_RANGE(ADDR(bse, off))->ihigh));
		break;

	case TT_FL_RANGE:
		POPF(rvalue);
		PUSH((FL_RANGE(ADDR(bse, off))->fllow <=
		  FL_RANGE(ADDR(bse,off))->flhigh) &&
		  (rvalue >= FL_RANGE(ADDR(bse, off))->fllow &&
		  rvalue <= FL_RANGE(ADDR(bse, off))->flhigh));
		break;

	case TT_FX_RANGE:
		POPL(lvalue);
		PUSH((FX_RANGE(ADDR(bse, off))->fxlow <=
		  FX_RANGE(ADDR(bse,off))->fxhigh) &&
		  (lvalue >= FX_RANGE(ADDR(bse, off))->fxlow &&
		  lvalue <= FX_RANGE(ADDR(bse, off))->fxhigh));
		break;

	case TT_C_RECORD:
		ptr1 = ADDR(bse, off);
		POP_ADDR(bse, off);
		ptr2 = ADDR(bse, off);
		nb_discr = C_RECORD(ptr1)->nb_discr_c;
		some_bool = TRUE;
		ptr1 += WORDS_C_RECORD;
		for (i = 1; i < nb_discr; i++)
			if (*++ptr2 != *++ptr1) {
				some_bool = FALSE;
			}
		PUSH(some_bool);
		break;

	case TT_V_RECORD:
	case TT_U_RECORD:
		POP_ADDR(bse, off);
		PUSH(TRUE);
		break;

	/* If the array type is unconstrained, the value must be within the
	 * given bounds. If constrained bounds must be the same. This rule is
	 * the same for null arrays.
	 */
	case TT_U_ARRAY:
		ptr1 = ADDR(bse, off);
		POP_ADDR(bse, off);
		ptr3 = ADDR(bse, off);/* type of the value */
		POP_ADDR(bse, off);/* to get rid of the value */
		/* PUSH(qual_index(ptr1, ptr3)); */
		PUSH(qual_sub(ptr1, ptr3));
		break;

	case TT_C_ARRAY:
	case TT_S_ARRAY:
		ptr1 = ADDR(bse, off);
		POP_ADDR(bse, off);
		ptr3 = ADDR(bse, off);/* type of the value */
		POP_ADDR(bse, off);/* to get rid of the value */
		PUSH(qual_index(ptr1, ptr3));
		break;

	case TT_ACCESS:
		/* membership on an access type is converted into a test on the
	     * designated type.  If the designated type itself is an access,
	     * no further checks are needed.
	     */
		POP_ADDR(bse, off);
		PUSH(TRUE);
		break;

	case TT_TASK:
		/* Does nothing need to be checked?  This case added because
		 * default popped too many elements off stack - failed c45291a.
		 * bp - 07/04/91.
		 */
		POP(value);
		PUSH(TRUE);
		break;

	default:
		POP_ADDR(bse, off);
		PUSH(TRUE);
		break;
	}
}

int qual_index(int *type_ptr1, int *type_ptr2)      /*;qual_index*/
{

	if (TYPE(type_ptr1) == TT_U_ARRAY || TYPE(type_ptr1) == TT_C_ARRAY) {
		if (TYPE(type_ptr2) == TT_U_ARRAY || TYPE(type_ptr2) == TT_C_ARRAY) {
			nb_dim = ARRAY(type_ptr1)->dim;
			type_ptr1 = &(ARRAY(type_ptr1)->index1_base);
			type_ptr2 = &(ARRAY(type_ptr2)->index1_base);
			for (i = 1; i <= nb_dim; i++) {
				bas1 = *type_ptr1++;
				off1 = *type_ptr1++;
				ptr1 = ADDR(bas1, off1);
				bas2 = *type_ptr2++;
				off2 = *type_ptr2++;
				ptr2 = ADDR(bas2, off2);
				if (I_RANGE(ptr1)->ilow != I_RANGE(ptr2)->ilow ||
				    I_RANGE(ptr1)->ihigh != I_RANGE(ptr2)->ihigh)
					return FALSE;
			}
		}

		else if (TYPE(type_ptr2) == TT_S_ARRAY)
			return qual_index(type_ptr2, type_ptr1);

		else if (TYPE(type_ptr2) == TT_D_ARRAY) {
			raise(SYSTEM_ERROR, "qual index on TT_D_ARRAY");
			return FALSE;
#ifdef TBSN
			return qual_index(type_ptr2, type_ptr1);
#endif
		}
	}

	else if (TYPE(type_ptr1) == TT_S_ARRAY) {
		if (TYPE(type_ptr2) == TT_U_ARRAY || TYPE(type_ptr2) == TT_C_ARRAY) {
			bas2 = ARRAY(type_ptr2)->index1_base;
			off2 = ARRAY(type_ptr2)->index1_offset;
			ptr2 = ADDR(bas2, off2);
			if ( S_ARRAY(type_ptr1)->salow != I_RANGE(ptr2)->ilow
			  || S_ARRAY(type_ptr1)->sahigh != I_RANGE(ptr2)->ihigh) {
				return FALSE;
			}
		}

		else if (TYPE(type_ptr2) == TT_S_ARRAY) {
			if ( S_ARRAY(type_ptr1)->salow != S_ARRAY(type_ptr2)->salow
			  || S_ARRAY(type_ptr1)->sahigh != S_ARRAY(type_ptr2)->sahigh) {
				return FALSE;
			}
		}

		else if (TYPE(type_ptr2) == TT_D_ARRAY)
			return qual_index(type_ptr2, type_ptr1);
	}
	else if (TYPE(type_ptr1) == TT_D_ARRAY) {
		raise(SYSTEM_ERROR, "qual index on TT_D_ARRAY");
		return FALSE;
#ifdef TBSN
		if (TYPE(type_ptr2) == TT_U_ARRAY || TYPE(type_ptr2) == TT_C_ARRAY) {
			nb_dim = ARRAY(type_ptr2)->dim;
			ptr1 = type_ptr1 + WORDS_D_TYPE - 1;
			type_ptr2 = &(ARRAY(type_ptr2)->index1_base);
			for (i = 1; i <= nb_dim; i++) {
				ptr1 += 2;
				bas2 = *type_ptr2++;
				off2 = *type_ptr2++;
				ptr2 = ADDR(bas2, off2);
				if (*ptr1++ != I_RANGE(ptr2)->ilow ||
				    *++ptr1 != I_RANGE(ptr2)->ihigh)
					return FALSE;
			}
		}

		else if (TYPE(type_ptr2) == TT_S_ARRAY) {
			ptr1 = type_ptr1 + WORDS_D_TYPE + 1;
			if (*ptr1++ != S_ARRAY(type_ptr2)->salow ||
			    *++ptr1 != S_ARRAY(type_ptr2)->sahigh) {
				return FALSE;
			}
		}

		else if (TYPE(type_ptr2) == TT_D_ARRAY) {
			nb_dim = D_TYPE(type_ptr2)->nb_discr_d;
			ptr1 = type_ptr1 + WORDS_D_TYPE - 1;
			ptr2 = type_ptr2 + WORDS_D_TYPE - 1;
			for (i = 1; i <= nb_dim; i++) {
				ptr1 += 2;
				ptr2 += 2;
				if (*ptr1++ != *ptr2++ || *++ptr1 != *++ptr2)
					return FALSE;
			}
		}
#endif
	}
	return TRUE;
}

int qual_sub(int *type_ptr1, int *type_ptr2)	     /*;qual_sub*/
{
	switch (TYPE(type_ptr1)) {

	case TT_I_RANGE:
	case TT_E_RANGE:
	case TT_ENUM:
		return ((I_RANGE(type_ptr2)->ilow > I_RANGE(type_ptr2)->ihigh)
		  ||   ((I_RANGE(type_ptr2)->ilow >= I_RANGE(type_ptr1)->ilow)
		  &&    (I_RANGE(type_ptr2)->ihigh <= I_RANGE(type_ptr1)->ihigh)));

	case TT_FL_RANGE:
		return ((FL_RANGE(type_ptr2)->fllow > FL_RANGE(type_ptr2)->flhigh)
		  ||   ((FL_RANGE(type_ptr2)->fllow >= FL_RANGE(type_ptr1)->fllow)
		  &&    (FL_RANGE(type_ptr2)->flhigh <= FL_RANGE(type_ptr1)->flhigh)));

	case TT_FX_RANGE:
		return ((FX_RANGE(type_ptr2)->fxlow > FX_RANGE(type_ptr2)->fxhigh)
		   ||  ((FX_RANGE(type_ptr2)->fxlow >= FX_RANGE(type_ptr1)->fxlow)
		   &&  (FX_RANGE(type_ptr2)->fxhigh <= FX_RANGE(type_ptr1)->fxhigh)));

	case TT_U_ARRAY:
	case TT_C_ARRAY:
		if (TYPE(type_ptr2) == TT_U_ARRAY || TYPE(type_ptr2) == TT_C_ARRAY) {
			nb_dim = ARRAY(type_ptr1)->dim;
			type_ptr1 = &(ARRAY(type_ptr1)->index1_base);
			type_ptr2 = &(ARRAY(type_ptr2)->index1_base);
			for (i = 1; i <= nb_dim; i++) {
				bas1 = *type_ptr1++;
				off1 = *type_ptr1++;
				ptr1 = ADDR(bas1, off1);
				bas2 = *type_ptr2++;
				off2 = *type_ptr2++;
				ptr2 = ADDR(bas2, off2);
				if (I_RANGE(ptr2)->ilow > I_RANGE(ptr2)->ihigh) {
					continue;
				}
				else if (I_RANGE(ptr1)->ilow > I_RANGE(ptr2)->ilow ||
				    I_RANGE(ptr1)->ihigh < I_RANGE(ptr2)->ihigh) {
					return FALSE;
				}
			}
			return TRUE;
		}
		else if (TYPE(type_ptr2) == TT_S_ARRAY) {
			bas1 = ARRAY(type_ptr1)->index1_base;
			off1 = ARRAY(type_ptr1)->index1_offset;
			ptr1 = ADDR(bas1, off1);
			if (S_ARRAY(type_ptr2)->salow > S_ARRAY(type_ptr2)->sahigh) {
				return TRUE;
			}
			if (S_ARRAY(type_ptr2)->salow < I_RANGE(ptr1)->ilow ||
			    S_ARRAY(type_ptr2)->sahigh > I_RANGE(ptr1)->ihigh) {
				return FALSE;
			}
			return TRUE;
		}
		break;

	case TT_S_ARRAY:
		if (TYPE(type_ptr2) == TT_U_ARRAY || TYPE(type_ptr2) == TT_C_ARRAY) {
			bas2 = ARRAY(type_ptr2)->index1_base;
			off2 = ARRAY(type_ptr2)->index1_offset;
			ptr2 = ADDR(bas2, off2);
			if (I_RANGE(ptr2)->ilow > I_RANGE(ptr2)->ihigh) {
				return TRUE;
			}
			if ( S_ARRAY(type_ptr1)->salow > I_RANGE(ptr2)->ilow
			  || S_ARRAY(type_ptr1)->sahigh < I_RANGE(ptr2)->ihigh){
				return FALSE;
			}
			return TRUE;
		}
		else if (TYPE(type_ptr2) == TT_S_ARRAY) {
			if (S_ARRAY(type_ptr2)->salow > S_ARRAY(type_ptr2)->sahigh) {
				return TRUE;
			}
			if ( S_ARRAY(type_ptr1)->salow > S_ARRAY(type_ptr2)->salow
			  || S_ARRAY(type_ptr1)->sahigh < S_ARRAY(type_ptr2)->sahigh) {
				return FALSE;
			}
			return TRUE;
		}
		break;

	default:
		;
	}
	return TRUE;
}

void qual_discr(int bse, int off)							 /*;qual_discr*/
{
	ptr = ADDR(bse, off);
	off = TOS;
	bse = TOSM(1);
	if (TYPE(ptr) == TT_RECORD)
		raise(SYSTEM_ERROR, "Qual discr on simple record");
	else if (TYPE(ptr) == TT_U_RECORD)
		return;			/* no constraint applied */
	else if (TYPE(ptr) == TT_C_RECORD) {
		nb_discr = C_RECORD(ptr)->nb_discr_c - 1;
		ptr1 = ADDR(bse, off) + 1;/* skip constrained flag */
		ptr += WORDS_C_RECORD + 1;
		while (nb_discr > 0) {
			if (*ptr++ != *ptr1++) {
				raise(CONSTRAINT_ERROR, "Discriminant");
				return;
			}
			nb_discr--;
		}
	}
	else if (TYPE(ptr) == TT_D_RECORD) {
		raise(SYSTEM_ERROR, "Qual discr on TT_D_RECORD");
		return;
#ifdef TBSN
		nb_discr = C_RECORD(ptr)->nb_discr_c - 1;
		ptr1 = ADDR(bse, off) + 1;/* skip constrained flag */
		ptr += WORDS_C_RECORD + 3;
		while (nb_discr > 0) {
			if (*ptr++ != *ptr1++) {
				raise(CONSTRAINT_ERROR, "Discriminant");
				return;
			}
			ptr++;
			nb_discr--;
		}
#endif
	}
	else
		raise(SYSTEM_ERROR, "Unknown record type in qual discr");
}

void allocate_new()											/*;allocate_new*/
{

	POP_ADDR(bse, off);  	/*  addr. of the type template for access type*/
	ptr1 = ADDR(bse, off);
	POP_ADDR(bse, off);  	/*  addr. of the designated type */
	ptr = ADDR(bse, off);
	value = SIZE(ptr);
    if (ACCESS(ptr1)->collection_avail > 0) {
       ACCESS(ptr1)->collection_avail = ACCESS(ptr1)->collection_avail - value;
	} 
	else {
		raise(STORAGE_ERROR, "collection exhausted");
	    return;
	}
	allocate(value, &bas2, &off2, &ptr2);

	switch(*ptr) {

	case TT_U_ARRAY:
	case TT_C_ARRAY:
	case TT_S_ARRAY:
		if (bse < heap_base) {			/* 	 Non global, must make a copy */
			if (TYPE(ptr) == TT_S_ARRAY) {
				val1 = WORDS_S_ARRAY;
			}
			else {
				nb_dim = ARRAY(ptr)->dim;
				val1 = 2 *(nb_dim - 1) + WORDS_ARRAY;
			}
			allocate(val1, &bse, &off, &ptr1);
			for (i = 0; i < val1; i++)
				*ptr1++ = *ptr++;
		}

		/* build an array descriptor */

		allocate(4, &bas1, &off1, &ptr1);
		*ptr1++ = bas2;
		*ptr1++ = off2;
		*ptr1++ = bse;
		*ptr1 = off;
		PUSH_ADDR(bas1, off1);
		break;

	case TT_C_RECORD:
		PUSH_ADDR(bas2, off2);
		*ptr2 = 1;		/*  constrained */
		nb_discr = C_RECORD(ptr)->nb_discr_c;
		for (i = 0; i < nb_discr; i++)
			*ptr2++ = *(ptr++ + WORDS_C_RECORD);
		break;

	case TT_U_RECORD:
	case TT_V_RECORD:
		raise(SYSTEM_ERROR, "Allocate unconstrained record");
		break;

	default:
		PUSH_ADDR(bas2, off2);
	}
}

void allocate_copy(int bse, int off)			             /*;allocate_copy*/
{
	POP_ADDR(bas4, off4);  	/*  addr. of the type template for access type*/
	ptr4 = ADDR(bas4, off4);
	i = TYPE(ADDR(bse, off));
	if (i == TT_U_ARRAY || i == TT_C_ARRAY || i == TT_S_ARRAY)
		POP_ADDR(bse, off);
	value = SIZE(ADDR(bse, off));
    if (ACCESS(ptr4)->collection_avail > 0) {
       ACCESS(ptr4)->collection_avail = ACCESS(ptr4)->collection_avail - value;
	} 
	else {
		raise(STORAGE_ERROR, "collection exhausted");
	    return;
	}
	allocate(value, &bas1, &off1, &ptr1);

	switch(i) {

	case TT_U_ARRAY:
	case TT_C_ARRAY:
	case TT_S_ARRAY:
		POP_ADDR(bas2, off2);/* value to be copied */
		ptr2 = ADDR(bas2, off2);
		move_mem(ptr2, ptr1, value);
		bas2 = bas1;	/* build an array descriptor */
		off2 = off1;
		allocate(4, &bas1, &off1, &ptr1);
		*ptr1++ = bas2;
		*ptr1++ = off2;
		*ptr1++ = bse;
		*ptr1 = off;
		break;

	case TT_RECORD:
		POP_ADDR(bas2, off2);
		ptr2 = ADDR(bas2, off2);
		move_mem(ptr2, ptr1, value);
		break;

	case TT_C_RECORD:
	case TT_U_RECORD:
		POP_ADDR(bas2, off2);
		ptr2 = ADDR(bas2, off2);
		move_mem(ptr2, ptr1, value);
		*ptr1 = 1;		/* always constrained */
		break;

	default: 		/* scalar, task, or access */
		if (value == 1) {
			POP(val1);
			*ptr1 = val1;
		}
		else if (value == 2) {
			POP(val1);
			*(ptr1 + 1) = val1;
			POP(val1);
			*ptr1 = val1;
		}
	}
	PUSH_ADDR(bas1, off1);
}

void fix_convert(int *fix_value, struct tt_fx_range *from_template,
  struct tt_fx_range *to_template)								/*;fix_convert*/
{
	/*
	 * DESCR: Takes a fixed point number and convert it to another fixed point
	 *	  number.
	 * INPUT: value: fixed value to be converted
	 *	  from_template: type template of value
	 *	  to_template: target type template
	 * OUTPUT: the converted number
	 */

	int     from_exp_2, to_exp_2;
	int     from_exp_5, to_exp_5;

	from_exp_5 = from_template->small_exp_5;
	to_exp_5 = to_template->small_exp_5;

	from_exp_2 = from_template->small_exp_2;
	to_exp_2 = to_template->small_exp_2;


	if (from_exp_5 > to_exp_5) {
		pow_of5(mul_fact, from_exp_5 - to_exp_5);
		int_tom(div_fact,1L);
	}
	else {
		int_tom(mul_fact,1L);
		pow_of5(div_fact, to_exp_5 - from_exp_5);
	}

	if (from_exp_2 > to_exp_2)
		int_mp2(mul_fact, from_exp_2 - to_exp_2);
	else
		int_mp2(div_fact, to_exp_2 - from_exp_2);

	int_mul(fix_value, mul_fact, fix_temp);
	int_div(fix_temp, div_fact, fix_value);
}

int fix_out_of_bounds(long fvalue, int *itemplate)		/*;fix_out_of_bounds*/
{
	/*
	 * DESCR: checks if value is out of the bounds described by template
	 * INPUT: value: fixed value to be checked
	 *	  template: pointer to type template.
	 * OUTPUT: returns TRUE if out of bounds
	 */

	return (fvalue > FX_RANGE(itemplate)->fxhigh
	  || fvalue < FX_RANGE(itemplate)->fxlow);
}

void create(int size, int *bse, int *off, int **ptr)			/*;create*/
{
	/* Procedure to allocate a block in memory, heap_next points to the next
	 * location and is updated by the call. The parameter size is the number
	 * of words to be allocated, ptr points to the newly allocated block,
	 * and bse and off are set to the base and offset based on heap_base,ADDR.
	 * Procedure create is only used for object creation.
	 */

	int *p;

	if (size < 0 || size >max_mem) {
		raise(SYSTEM_ERROR, "Ridiculous size for object creation");
		*ptr = heap_addr + WORDS_PTR + 1;
		*off = *ptr - heap_addr;
		*bse = heap_base;
		return;
	}
	size += 1 + WORDS_PTR;
	if (heap_next > heap_addr + max_mem - size) {
		if(!allocate_new_heap()) {
			raise(STORAGE_ERROR, "Object creation");
			*ptr = heap_addr + WORDS_PTR + 1;
			*off = *ptr - heap_addr;
			*bse = heap_base;
			return;
		}
	}

#ifdef GARBAGE
	p = BLOCK_FRAME->bf_data_link;
	while (p) {
		if(*--p <= -size) { /* first fit */
			*p = -*p;
			p += WORDS_PTR + 1;
			*ptr = p;
			*off = *ptr - heap_addr;
			*bse = heap_base;
			return;
		}
		p = *(int **)++p;
	}

	int *q;
	p = free_list;
	while (p) {
		if(*--p <= -size) { /* first fit */
			*p = -*p;
			p += 1;
			q = *(int **)p;
			*(int **)p = BLOCK_FRAME->bf_data_link;
			BLOCK_FRAME->bf_data_link = free_list;
			free_list = q;
			p += WORDS_PTR;
			*ptr = p;
			*off = *ptr - heap_addr;
			*bse = heap_base;
			return;
		}
		p = *(int **)++p;
	}
#endif

	*heap_next++ = size;
	*(int **)(heap_next) = BLOCK_FRAME->bf_data_link;
	BLOCK_FRAME->bf_data_link = heap_next;
	heap_next += WORDS_PTR;
	*ptr = heap_next;
	*off = *ptr - heap_addr;
	*bse = heap_base;
	heap_next += size - 1 - WORDS_PTR;
}

void allocate(int size, int *bse, int *off, int **ptr)			/*;allocate*/
{
	/* The ALLOCATE procedure is just like CREATE except that it is used for
	 * the case of an allocator allocating from the heap. It differs only
	 * in the error message issued if there is insufficient room.
	 */

	int *p;

	if (size < 0) {
		raise(SYSTEM_ERROR, "Ridiculous size for object allocation");
		*ptr = heap_addr + WORDS_PTR + 1;
		*off = *ptr - heap_addr;
		*bse = heap_base;
		return;
	}
	size += 1 + WORDS_PTR;
	if (heap_next > heap_addr + max_mem - size) {
		if(!allocate_new_heap()) {
			raise(STORAGE_ERROR, "Allocator");
			*ptr = heap_addr + WORDS_PTR + 1;
			*off = *ptr - heap_addr;
			*bse = heap_base;
			return;
		}
	}

#ifdef GARBAGE
	p = BLOCK_FRAME->bf_data_link;
	while (p) {
		if(*--p <= -size) { /* first fit */
			*p = -*p;
			p += WORDS_PTR + 1;
			*ptr = p;
			*off = *ptr - heap_addr;
			*bse = heap_base;
			return;
		}
		p = *(int **)++p;
	}

	int *q;
	p = free_list;
	while (p) {
		if(*--p <= -size) { /* first fit */
			*p = -*p;
			p += 1;
			q = *(int **)p;
			*(int **)p = BLOCK_FRAME->bf_data_link;
			BLOCK_FRAME->bf_data_link = free_list;
			free_list = q;
			p += WORDS_PTR;
			*ptr = p;
			*off = *ptr - heap_addr;
			*bse = heap_base;
			return;
		}
		p = *(int **)++p;
	}
#endif

	*heap_next++ = size;
	*(int **)(heap_next) = BLOCK_FRAME->bf_data_link;
	BLOCK_FRAME->bf_data_link = heap_next;
	heap_next += WORDS_PTR;
	*ptr = heap_next;
	*off = *ptr - heap_addr;
	*bse = heap_base;
	heap_next += size - 1 - WORDS_PTR;
}

void push_task_frame(int first)							/*;push_task_frame*/
{
	if (heap_next > heap_addr + max_mem - 4 - 2*WORDS_PTR)
		raise(STORAGE_ERROR, "Tasking");
	else {
		*heap_next++ = 4 + WORDS_PTR;
		*(int **)(heap_next) = BLOCK_FRAME->bf_tasks_declared;
		heap_next += WORDS_PTR;
		BLOCK_FRAME->bf_tasks_declared = heap_next;
		*heap_next++ = first;
	}
}

int pop_task_frame()										/*;pop_task_frame*/
{
	ptr = BLOCK_FRAME->bf_tasks_declared;
	value = *ptr;		/*  Task chain */
	BLOCK_FRAME->bf_tasks_declared = *(int **)(ptr - WORDS_PTR);
	*(ptr - WORDS_PTR - 1) = -(*(ptr - WORDS_PTR - 1));/*Release task frame*/
	*(int **)(ptr - WORDS_PTR) = (int *)0;
	return (value);
}

void deallocate(int *p)											/*;deallocate*/
{
	/* Procedure to deallocate a * block. This is done simply by setting
 	 * the length word negative, which indicates a block which is not in use.
 	 */

#ifdef GARBAGE
	int *q,*r;

	if (p == (int *)0) return;

	q = p; /* head of list */
	while (p) {
		r = p;
		if (*--p > 0) {
			*p = -*p;
		}
		p = *(int **)r;
	}
	*(int **)r = free_list;
	free_list = q;
#else
	return;
#endif
}

int expn(float fvalue)												/*;expn*/
{
	/* this procedure is supposed to return the exponent of a normalized
	 *  positive floating point number. Since it is supposed to be
	 *  rewritten as an host function, we didn't try to optimize it.
	 */

	int exponent = 0;

	while(fvalue < 0.5) {
		fvalue *= 2.0;
		exponent -= 1;
	}
	while(fvalue >= 1.0) {
		fvalue /= 2.0;
		exponent += 1;
	}
	return exponent;
}

void check_subtype_with_discr(int *type_ptr, int discr_list[])
											     /*;check_subtype_with_discr*/
{
	int     new_discr_list[MAX_DISCR];
	int    *base_type_ptr, *discr_ptr, nb_discr, i, *component_ptr, nb_dim;
	int		low, high;
	int     nb_field, nb_fixed, *field_ptr, *case_table_ptr, *field_table_ptr;
	int     first_field, last_field, next_case, *case_ptr;
	int     discr_number, value_discr, nb_choices;
	int	    *type_ptr1, bas1, off1, *ptr1, *type_discr;

	if (TYPE(type_ptr) == TT_D_RECORD) {
		base_type_ptr = ADDR(D_TYPE(type_ptr)->dbase, D_TYPE(type_ptr)->doff);
		discr_ptr = type_ptr + WORDS_D_TYPE;
		nb_discr = D_TYPE(type_ptr)->nb_discr_d;
		field_ptr = base_type_ptr + WORDS_U_RECORD;
		for (i = 0; i < nb_discr; i++) {
			new_discr_list[i] = get_variable_bound(discr_ptr, discr_list);
			type_discr = ADDR (*(field_ptr+1), *(field_ptr+2));
			if ( I_RANGE(type_discr)->ilow > new_discr_list [i]
			  || I_RANGE(type_discr)->ihigh < new_discr_list [i]) {
				raise (CONSTRAINT_ERROR, "Discr. does not hold in bounds");
			}
			field_ptr += 3;
			discr_ptr += 2;
		}
		check_subtype_with_discr(base_type_ptr, new_discr_list);

	}

	else if (TYPE(type_ptr) == TT_D_ARRAY) {
		base_type_ptr = ADDR(D_TYPE(type_ptr)->dbase, D_TYPE(type_ptr)->doff);
		discr_ptr = type_ptr + WORDS_D_TYPE;
		nb_dim = D_TYPE(type_ptr)->nb_discr_d;

		if ( TYPE(base_type_ptr) == TT_U_ARRAY
		  || TYPE(base_type_ptr) == TT_C_ARRAY) {
			component_ptr =
			  ADDR(ARRAY(base_type_ptr)->component_base,
			  ARRAY(base_type_ptr)->component_offset);
			check_subtype_with_discr(component_ptr, NULL_INT);
		}
		else if (TYPE (base_type_ptr) == TT_S_ARRAY) {
			/* in a simple array, the component can only be a simple
			 * type : therefore there is no need to test
			 */
			return;
		}

		type_ptr1 = &(ARRAY(base_type_ptr)->index1_base);
		for (i = 1; i <= nb_dim; i++) {
			low = get_variable_bound(discr_ptr, discr_list);
			discr_ptr += 2;
			high = get_variable_bound(discr_ptr, discr_list);
			discr_ptr += 2;

			bas1 = *type_ptr1++;
			off1 = *type_ptr1++;
			ptr1 = ADDR(bas1, off1);
			if ((low <= high) && (I_RANGE(ptr1)->ilow > low
			  || I_RANGE(ptr1)->ihigh < high)) {
				raise (CONSTRAINT_ERROR,
				  "Array with discr. does not hold in bounds");
			}
		}
	}
	else if (TYPE(type_ptr) == TT_C_RECORD) {
		base_type_ptr = ADDR(C_RECORD(type_ptr)->cbase,
		  C_RECORD(type_ptr)->coff);
		nb_discr = C_RECORD(type_ptr)->nb_discr_c;
		field_ptr = base_type_ptr + WORDS_U_RECORD;
		for (i = 0; i < nb_discr; i++) {
			new_discr_list[i] = *(type_ptr + WORDS_C_RECORD + i);
			type_discr = ADDR (*(field_ptr+1), *(field_ptr+2));
			if ( I_RANGE(type_discr)->ilow > new_discr_list [i]
			  || I_RANGE(type_discr)->ihigh < new_discr_list [i]) {
				raise (CONSTRAINT_ERROR, "Discr. does not hold in bounds");
			}
			field_ptr += 3;
		}
		check_subtype_with_discr(base_type_ptr, new_discr_list);
	}

	else if (TYPE(type_ptr) == TT_V_RECORD) {
		nb_field = U_RECORD(type_ptr)->nb_field_u;
		nb_fixed = U_RECORD(type_ptr)->nb_fixed_u;
		field_table_ptr = type_ptr + WORDS_U_RECORD;
		case_table_ptr = field_table_ptr + 3 * nb_field;
		first_field = 0;
		last_field = nb_fixed - 1;
		next_case = U_RECORD(type_ptr)->first_case;
		for (;;) {
			field_ptr = 3 * first_field + field_table_ptr;
			for (i = first_field; i <= last_field; i++) {
				component_ptr = ADDR(*(field_ptr + 1), *(field_ptr + 2));
				check_subtype_with_discr(component_ptr, discr_list);
				field_ptr += 3;
			}

			if (next_case == -1)
				break;

			/* we have : next_case != -1 */

			case_ptr = case_table_ptr + next_case;
			discr_number = *case_ptr++;
			value_discr = discr_list[discr_number];
			nb_choices = *case_ptr;
			case_ptr += 4;
			val_high = *case_ptr;
			for (i = 2; i <= nb_choices; i++) {
				if (val_high > value_discr)
					break;
				case_ptr += 4;
				val_high = *case_ptr;
			}
			next_case = *--case_ptr;
			last_field = *--case_ptr;
			first_field = *--case_ptr;
		}
	}
}
