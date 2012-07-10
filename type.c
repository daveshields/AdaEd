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
#include "segment.h"
#include "gvars.h"
#include "attr.h"
#include "ops.h"
#include "type.h"
#include "axqrprots.h"
#include "setprots.h"
#include "dbxprots.h"
#include "initobjprots.h"
#include "maincaseprots.h"
#include "gmainprots.h"
#include "arithprots.h"
#include "segmentprots.h"
#include "genprots.h"
#include "exprprots.h"
#include "gutilprots.h"
#include "arithprots.h"
#include "genprots.h"
#include "miscprots.h"
#include "gmiscprots.h"
#include "smiscprots.h"
#include "statprots.h"
#include "typeprots.h"

static void init_enum(Symbol, Segment, int, int);
static void install_type(Symbol, Segment, int);
static Segment make_fixed_template(Const, Const, Const, Const,
  struct tt_fx_range **);
static void split_powers(int *);
static void process_record(Symbol);
static int linearize_record(Tuple, Node);
static int discr_dep_subtype(Node);
static void get_discr(Node, int *, int *);
static void eval_max_size(Symbol, Tuple);

#define TT_PTR(p) (int **) p
extern Segment	CODE_SEGMENT, DATA_SEGMENT, DATA_SEGMENT_MAIN;
extern Segment   VARIANT_TABLE, FIELD_TABLE;

extern int ADA_MIN_INTEGER, ADA_MAX_INTEGER;
extern *ADA_MIN_INTEGER_MP, *ADA_MAX_INTEGER_MP;
extern long ADA_MIN_FIXED, ADA_MAX_FIXED;
extern int *ADA_MIN_FIXED_MP, *ADA_MAX_FIXED_MP;

static char  *PRECISION_NOT_SUPPORTED = 
  "Precision not supported by implementation. (Appendix F)";
/* split_ variables use to report result from split_powers()*/
static int split_powers_2, split_powers_5, split_powers_value;

/* Chapter 3: types */
/* type elaboration */

void gen_type(Symbol type_name)									/*;gen_type*/
{
	/* This is the main procedure for type elaboration.
	 *
	 *   type_name : in the case of a type declaration, this is the
	 *               name of the type.
	 */

	Node l_node, u_node, d_node, s_node, low_node, high_node, entry_node;
	Node name_node, pragma_id, pragma_list, pragma_op, pragma_val, value_node;
	Symbol parent_type, comp_type, typ, entry_name, entry_type, index;
	Symbol indx_type, task_proc;
	Tuple type_list, index_list, tup, sig, entry_list;
	int  nb_dim, lng, priority, offset;
	long nb_elements, nb_len;	/* long to avoid overflow problems */
	int family_number, len, global_flag, ubd, lbd;
	int		collection_size;
	Tuple	repr_tup;
	Const low_const, high_const, delta_const, small_const;
	Segment stemplate, static_template, non_static_template;
	Fortup ft1;
	struct tt_array *tt_array_ptr;
	struct tt_e_range  *tt_e_range_ptr;
	struct tt_access   *tt_access_ptr;
	struct tt_task *tt_task_ptr;
	struct tt_fx_range *tt_fx_range_ptr;

#ifdef TRACE
	if (debug_flag)
		gen_trace_symbol("GEN_TYPE", type_name);
#endif

	switch(NATURE(type_name)) {

	case(na_type):
		/* Case of FIXED types for which we create a template.
		 *  Also case of derived types.
		 */
		if (is_fixed_type(type_name)) {
			sig = SIGNATURE(type_name);
			l_node = (Node) sig[2];
			u_node = (Node) sig[3];
			d_node = (Node) sig[4];
			s_node = (Node) sig[5];

			low_const = get_ivalue(l_node);
			high_const = get_ivalue(u_node);
			delta_const = get_ivalue(d_node);
			small_const = get_ivalue(s_node);
			stemplate = make_fixed_template(low_const, high_const, delta_const,
			  small_const, &tt_fx_range_ptr);
			/* SETL ver supports 2 kinds of fixed point, in C we have only 1 */
			tt_fx_range_ptr->fxlow = ADA_MIN_FIXED + 1;
			tt_fx_range_ptr->fxhigh = ADA_MAX_FIXED;
			TYPE_KIND(type_name) = TK_LONG;
			TYPE_SIZE(type_name) = su_size(TK_LONG);

			install_type(type_name, stemplate, TRUE);
			root_type(type_name) = type_name;
		}
		else {		/* Derived type */
			parent_type = TYPE_OF(type_name);
			assign_same_reference(type_name, parent_type);
			TYPE_KIND(type_name) = TYPE_KIND(parent_type);
			TYPE_SIZE(type_name) = TYPE_SIZE(parent_type);
		}
		break;

	case(na_array):
		tup = (Tuple) SIGNATURE(type_name);
		index_list = (Tuple) tup[1];
		comp_type = (Symbol) tup[2];
		if (is_entry_type(comp_type))
			return;
		nb_dim = tup_size(index_list);
		nb_elements = 1L;
		FORTUP(index = (Symbol), index_list, ft1);
			len = length_of(index);
			if (len >= 0)
				nb_elements *= len;
			else
				nb_elements = -1L;
		ENDFORTUP(ft1);
		if ((nb_elements >= 0L) && has_static_size(comp_type)) {
			/* want TYPE_SIZE to be number of storage units for array , */
			/* TBSL: check that TYPE_KIND assignment below right,
	     	 * as in SETL just have TYPE_SIZE assignment of course 
	     	 */
			TYPE_KIND(type_name) = TYPE_KIND(comp_type);
			nb_len= nb_elements * TYPE_SIZE(comp_type);
			if (nb_len > MAX_STATIC_SIZE) nb_len = -1;
			TYPE_SIZE(type_name) = nb_len;
		}
		else {
			TYPE_SIZE(type_name) = -1;
		}
		stemplate = template_new(TT_U_ARRAY, size_of(type_name),
		  WORDS_ARRAY - 4, TT_PTR(&tt_array_ptr));
		/* TBSL: need to define field TT_U_ARRAY_DIMENSIONS: byte or integer? */
		tt_array_ptr->dim = nb_dim;
		global_flag = has_static_size(type_name);
		type_list = tup_copy(index_list);
		type_list = (Tuple) tup_with(type_list, (char *) comp_type);
		while(tup_size(type_list)) {
			typ = (Symbol) tup_frome(type_list);
			reference_of(typ);
			/* template      +:= ref; */
			segment_put_int(stemplate, REFERENCE_SEGMENT);
			segment_put_int(stemplate, (int) REFERENCE_OFFSET);
			global_flag &= is_global(typ);
		}
		tup_free(type_list);
		install_type(type_name, stemplate, global_flag);
		break;

	case(na_record):
		process_record(type_name);
		break;

	case(na_enum):
		/* this one is certainly static... */
		sig = SIGNATURE(type_name);
		low_node = (Node) sig[2];
		high_node = (Node) sig[3];
		lbd = get_ivalue_int(low_node);
		ubd = get_ivalue_int(high_node);
		stemplate = template_new(TT_ENUM, 1, WORDS_E_RANGE, 
		  TT_PTR(&tt_e_range_ptr));
		tt_e_range_ptr->elow = lbd;
		tt_e_range_ptr->ehigh = ubd;
		init_enum(type_name, stemplate, lbd, ubd);
		/* TYPE_SIZE(type_name) = ubd <= 255 ? mu_size(mu_byte) :
		  mu_size(mu_word); */
		TYPE_KIND(type_name) = TK_WORD; /* only word case for 1st version */
		TYPE_SIZE(type_name) = 1; /* only word case for 1st version ds*/
		/* put that in the static segment.... */
		install_type(type_name, stemplate, TRUE);
		break;

	case(na_access):
		/* Needs own template, as the accessed type contains a task
		 * (otherwise expander changed it to derived type from $ACCESS).
		 */
		TYPE_KIND(type_name) = TYPE_KIND(symbol_daccess);
		TYPE_SIZE(type_name) = TYPE_SIZE(symbol_daccess);
		stemplate = template_new(TT_ACCESS, size_of(type_name),
		  WORDS_ACCESS, TT_PTR(&tt_access_ptr));
		tt_access_ptr->master_task = 0;
		tt_access_ptr->master_bfp = 0;
		repr_tup = REPR(type_name);
		if (repr_tup == (Tuple)0) 		/* error condition */
			value_node = OPT_NODE;
		else 
			value_node = (Node) repr_tup[3];
		if (N_KIND(value_node) == as_opt) {
		   tt_access_ptr->collection_size = ADA_MAX_INTEGER;
		   tt_access_ptr->collection_avail = ADA_MAX_INTEGER;
		}
		else if (N_KIND(value_node) == as_ivalue) {
		   collection_size = INTV((Const)N_VAL(value_node));
		   tt_access_ptr->collection_size = collection_size;
		   tt_access_ptr->collection_avail = collection_size;
		}
		install_type(type_name, stemplate, FALSE);
		if ((N_KIND(value_node) != as_opt) && 
			(N_KIND(value_node) != as_ivalue)) {
 		   gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
           gen_kic(I_ADD_IMMEDIATE, mu_word, 
				   WORD_OFF(tt_access, collection_size), "collection size");
		   gen_value(value_node);
		   gen_kc(I_MOVE, mu_word, "update collection size");
 		   gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
           gen_kic(I_ADD_IMMEDIATE, mu_word, 
				   WORD_OFF(tt_access, collection_avail), "collection avail");
		   gen_value(value_node);
		   gen_kc(I_MOVE, mu_word, "update collection avail");
		}
		break;

	case(na_task_type_spec):
	case(na_task_type):
		entry_list = SIGNATURE(type_name);
		priority = MAX_PRIO-2;
		TYPE_KIND(type_name) = TK_WORD;/* SETL has '2' for this size */
		TYPE_SIZE(type_name) = su_size(TK_WORD);
		/* SETL has '2' for this size */
		global_flag = TRUE;
		offset = 0;
		family_number = 0;
		static_template = segment_new(SEGMENT_KIND_DATA, 4);
		non_static_template = segment_new(SEGMENT_KIND_DATA, 4);

		FORTUP(entry_node = (Node), entry_list, ft1);
			if (N_KIND(entry_node) == as_line_no) {
				;
			}
			else if (N_KIND(entry_node) == as_pragma) {
				pragma_id = N_AST1(entry_node);
				pragma_list = N_AST2(entry_node);
				if (streq(N_VAL(pragma_id), "priority")) {
					pragma_op = (Node) N_LIST(pragma_list)[1];
					pragma_val = N_AST2(pragma_op);
					priority = (int) N_VAL(pragma_val);
				}
			}
			else {
				family_number += 1;
				name_node = N_AST1(entry_node);
				entry_name = N_UNQ(name_node);
				S_SEGMENT(entry_name) = 0;
				S_OFFSET(entry_name) = family_number;
				/* TBSL: do we need set TYPE_KIND here (think not) ds 8-14-85 */
				TYPE_SIZE(entry_name) = size_entry(entry_name);
				if (N_KIND(entry_node) == as_entry_family) {
					entry_type = TYPE_OF(entry_name);
					/* [[indx_type], -] := SIGNATURE(entry_type); */
					tup = (Tuple) SIGNATURE(entry_type);
					tup = (Tuple) tup[1];
					indx_type = (Symbol) tup[1];
					reference_of(indx_type);
					global_flag &= is_static_type(indx_type);
					if (global_flag) {
						lng = length_of(indx_type);
						low_node = (Node) SIGNATURE(indx_type)[2];
						/*  static_template 
						 *	+:= [offset-get_ivalue(low_node), lng];
						 */
						segment_put_word(static_template,
					      offset - get_ivalue_int(low_node));
						segment_put_word(static_template, lng);
						offset += lng;
					}
					/* non_static_template +:= ref; */
					segment_put_word(non_static_template, REFERENCE_SEGMENT);
					segment_put_word(non_static_template,
				      (int) REFERENCE_OFFSET);
				}
				else {
					/* static_template     +:= [offset, 1]; */
					segment_put_word(static_template, offset);
					segment_put_word(static_template, 1);
					offset += 1;
					/* non_static_template +:= [0, 0]; */
					segment_put_word(non_static_template, 0);
					segment_put_word(non_static_template, 0);
				}
			}
		ENDFORTUP(ft1);

		/* This may be a derived type */
		parent_type = TYPE_OF(type_name);
		task_proc = assoc_symbol_get(parent_type, TASK_INIT_PROC);
		global_flag &= is_global(task_proc);

		stemplate = template_new(TT_TASK, 1, WORDS_TASK, TT_PTR(&tt_task_ptr));
		tt_task_ptr->priority = priority;
		reference_of(task_proc);
		tt_task_ptr->body_base = REFERENCE_SEGMENT;
		tt_task_ptr->body_off = REFERENCE_OFFSET;
		tt_task_ptr->nb_entries = offset;
		tt_task_ptr->nb_families = family_number;
		repr_tup = REPR(type_name);
		if (repr_tup == (Tuple)0) 		/* error condition */
			value_node = OPT_NODE;
		else
        	value_node = (Node) repr_tup[3];
        if (N_KIND(value_node) == as_opt) {
           tt_task_ptr->collection_size = ADA_MAX_INTEGER;
           tt_task_ptr->collection_avail = ADA_MAX_INTEGER;
        }
        else if (N_KIND(value_node) == as_ivalue) {
           collection_size = INTV((Const)N_VAL(value_node));
           tt_task_ptr->collection_size = collection_size;
           tt_task_ptr->collection_avail = collection_size;
        }

		if (global_flag) {
			/* template +:= static_template; */
			segment_append(stemplate, static_template);
		}
		else {
			/* template +:= non_static_template; */
			segment_append(stemplate, non_static_template);
			/* TBSL: see if static_template and non_static template can be free
	       here */
		}

		install_type(type_name, stemplate, global_flag);
        if ((N_KIND(value_node) != as_opt) &&
            (N_KIND(value_node) != as_ivalue)) {
           gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
           gen_kic(I_ADD_IMMEDIATE, mu_word,
                   WORD_OFF(tt_task, collection_size), "collection size");
           gen_value(value_node);
           gen_kc(I_MOVE, mu_word, "update collection size");
           gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
           gen_kic(I_ADD_IMMEDIATE, mu_word,
                   WORD_OFF(tt_task, collection_avail), "collection avail");
           gen_value(value_node);
           gen_kc(I_MOVE, mu_word, "update collection avail");
        }

		break;

	case(na_entry):
	case(na_entry_former):
		break;

	default:
		compiler_error_s("Unexpected type nature: ", type_name);
	}
}

static void init_enum(Symbol type_name, Segment stemplate, int lbd, int ubd)
																/*;init_enum*/
{
	/* initialize enumeration map values in segment.
	 * the literal map is a tuple with pairs of values giving the string
	 * and the value. For C version we put values first, followed by length
	 * of string, followed by characters in string, one per word.
	 */

	Tuple litmap;
	int     i, n;
	char   *str;
	int     value, nstr;

	/*	enum_map := {[value, enum_lit]:
	 *	[enum_lit, value] in OVERLOADS(type_name)};
	 *	loop for value in [lbd..ubd] do
	 *	template with:= #(enum_lit := enum_map(value));
	 *	template    +:= [ abs(charac): charac in enum_lit ];
	 *	end loop for;
	 */
	litmap = (Tuple) literal_map(type_name);
	n = tup_size(litmap);
	for (value = lbd; value <= ubd; value++) {
		/* find string for value */
		str = (char *) 0;
		for (i = 1; i <= n; i += 2) {
			if ((int) litmap[i + 1] == value) {
				str = litmap[i];
				break;
			}
		}
		if (str == (char *) 0) {
			chaos("type.c: init_enum cannot find literal value");
		}
		nstr = strlen(str);
		/* put string length */
		segment_put_int(stemplate, nstr);
		for (i = 0; i < nstr; i++) {
			segment_put_int(stemplate, (int) str[i]);
		}
	}
}

/* Subtype elaboration */

void gen_subtype(Symbol type_name)							/*;gen_subtype*/
{
	/* This procedure processes subtypes only.
	 * Note: all access subtypes have been changed to derived types by expander.
	 */

	int type_install_done;
	int global_flag, i, nelts;
	Node l_node, u_node, d_node, s_node, parent_l_node, parent_u_node;
	Tuple type_list, index_list, discr_list, constraint, tup, sig;
	int nb_dim, l, inum2, inum5, iden2, iden5;
	long nb_elements, nb_len; /* long to avoid overflow problems */
	Symbol type_mark, comp_type, index, typ, indx_type, b_index;
	Symbol temp_name, field_name, temp_var, sym , x;
	Fortup ft1;
	Node low, high, b_low, b_high, dgt_node, lbd_node;
	Node ubd_node, dlt_node, sml_node;
	int static_qual, static_check;
	Tuple base_index_list, field_map;
	Const plow, phigh, lw_val, hg_val, b_lw_val, b_hg_val, consT;
	int lw_vali, hg_vali, b_lw_vali, b_hg_vali;
	int low_int, high_int, val_low = 0, val_high = 0, val_defined = 0;
	float low_float, high_float;
	Const low_const, high_const, small_const;
	Rational rat;
	int *num1, *den1, *num2, *den2;
	Const parent_low_const, parent_high_const;
	Segment stemplate;
	struct tt_array *tt_array_ptr;
	struct tt_s_array  *tt_s_array_ptr;
	struct tt_e_range  *tt_e_range_ptr;
	struct tt_i_range  *tt_i_range_ptr;
	struct tt_fl_range *tt_fl_range_ptr;
	struct tt_fx_range *tt_fx_range_ptr;
	struct tt_c_record *tt_c_record_ptr;



#ifdef TRACE
	if (debug_flag)
		gen_trace_symbol("GEN_SUBTYPE", type_name);
#endif

	type_mark = TYPE_OF(type_name);
	constraint = get_constraint(type_name);

	switch((int) constraint[1]) {

	case(co_access):
		if ((int) CONTAINS_TASK((Symbol) designated_type(type_name))) {
			assign_same_reference(type_name, type_mark);
			TYPE_KIND(type_name) = TYPE_KIND(type_mark);
			TYPE_SIZE(type_name) = TYPE_SIZE(type_mark);
		}
		else {
			assign_same_reference(type_name, symbol_daccess);
			TYPE_KIND(type_name) = TYPE_KIND(symbol_daccess);
			TYPE_SIZE(type_name) = TYPE_SIZE(symbol_daccess);
		}
		break;

	case(co_index):
		sig = SIGNATURE(type_name);
		index_list = (Tuple) sig[1];
		comp_type = (Symbol) sig[2];
		nb_dim = tup_size(index_list);
		nb_elements = 1;
		FORTUP(index = (Symbol), index_list, ft1);
			l = length_of(index);
			if (l >= 0)
				nb_elements *= l;
			else
				nb_elements = -1;
		ENDFORTUP(ft1);
		if (nb_elements >= 0 && has_static_size(comp_type)) {
			/* This is a kludge, needed for c43206a (shields 7-8-86) */
			nb_len =  nb_elements * TYPE_SIZE(comp_type);
			if (nb_len > MAX_STATIC_SIZE)
				nb_len = -1;
			TYPE_SIZE(type_name) = nb_len;
		}
		else {
			TYPE_SIZE(type_name) = -1;/* SETL uses -1 here */
		}
		stemplate = template_new(TT_C_ARRAY, size_of(type_name),
		  WORDS_ARRAY, TT_PTR(&tt_array_ptr));
		tt_array_ptr->dim = nb_dim;
		global_flag = has_static_size(type_name);
		type_list = tup_copy(index_list);
		type_list = tup_with(type_list, (char *) comp_type);
		/* The first two items retrieved correspond to the component
	     * type and first index type, respectively. These are stored
	     * in the fixed part of the template; further items (if any)
	     * follow this fixed part.
	     */
		nelts = 0;
		while (tup_size(type_list)) {
			typ = (Symbol) tup_frome(type_list);
			reference_of(typ);
			global_flag &= is_global(typ);
			if (nelts == 0) { /* if component type */
				tt_array_ptr->component_base = REFERENCE_SEGMENT;
				tt_array_ptr->component_offset = REFERENCE_OFFSET;
				nelts++;
			}
			else if (nelts == 1)  { /* if first index type */
				tt_array_ptr->index1_base = REFERENCE_SEGMENT;
				tt_array_ptr->index1_offset = REFERENCE_OFFSET;
				nelts++;
			}
			else {
				segment_put_int(stemplate, REFERENCE_SEGMENT);
				segment_put_int(stemplate, (int) REFERENCE_OFFSET);
			}
		}
		tup_free(type_list);
		if ((nb_dim == 1) && global_flag) {
			indx_type = (Symbol) index_list[1];
			tup = SIGNATURE(indx_type);
			low = (Node) tup[2];
			high = (Node) tup[3];
			stemplate = template_new(TT_S_ARRAY, size_of(type_name),
			  WORDS_S_ARRAY, TT_PTR(&tt_s_array_ptr));
			tt_s_array_ptr->component_size = size_of(comp_type);
			tt_s_array_ptr->index_size = size_of(indx_type);

			/* TBSL: check bounds are integers, assume so for now */
			low_const = get_ivalue(low);
			if (low_const->const_kind == CONST_INT)
				low_int = low_const->const_value.const_int;
			else
				chaos("low bound not int");
			high_const = get_ivalue(high);
			if (high_const->const_kind == CONST_INT)
				high_int = high_const->const_value.const_int;
			else
				chaos("high bound not int");
			tt_s_array_ptr->salow = low_int;
			tt_s_array_ptr->sahigh = high_int;
		}

		static_qual = TRUE;
		base_index_list = INDEX_TYPES(base_type(type_name));
		base_index_list = tup_copy(base_index_list);
		FORTUP(index = (Symbol), index_list, ft1);
			b_index = (Symbol) tup_fromb(base_index_list);
			tup = SIGNATURE(index);
			low = (Node) tup[2];
			high = (Node) tup[3];
			tup = SIGNATURE(b_index);
			b_low = (Node) tup[2];
			b_high = (Node) tup[3];
			lw_val = get_ivalue(low);
			hg_val = get_ivalue(high);
			b_lw_val = get_ivalue(b_low);
			b_hg_val = get_ivalue(b_high);
			if ( lw_val->const_kind == CONST_OM
		      || hg_val->const_kind == CONST_OM
		      || b_lw_val->const_kind == CONST_OM
		      || b_hg_val->const_kind == CONST_OM) {
				static_qual = FALSE;
				break;
			}
			/* TBSL:check that values are in fact integers */
			else {
				lw_vali = lw_val->const_value.const_int;
				hg_vali = hg_val->const_value.const_int;
				b_lw_vali = b_lw_val->const_value.const_int;
				b_hg_vali = b_hg_val->const_value.const_int;
				if (lw_vali <= hg_vali &&/* No check on null ranges */
			    	(lw_vali < b_lw_vali || hg_vali > b_hg_vali)) {
					/* Raise CONSTRAINT_ERROR */
					gen_s(I_LOAD_EXCEPTION_REGISTER, symbol_constraint_error);
					gen(I_RAISE);
					break;
				}
			}
		ENDFORTUP(ft1);

		install_type(type_name, stemplate, global_flag);

		if (!static_qual) {
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
			gen_s(I_QUAL_SUB, base_type(type_name));
			gen_ks(I_DISCARD_ADDR, 1, type_name);
		}
		break;

	case(co_range):
		/* The SETL version builds range part of template and then puts it 
		 * in the proper place in the final template. In C we set the 
		 * desired values in val_low and val_high.
		 */
		val_defined = FALSE;
		l_node = (Node) constraint[2];
		u_node = (Node) constraint[3];
		tup = SIGNATURE(type_mark);
		parent_l_node = (Node) tup[2];
		parent_u_node = (Node) tup[3];
		parent_low_const = get_ivalue(parent_l_node);
		parent_high_const = get_ivalue(parent_u_node);
		low_const = get_ivalue(l_node);
		high_const = get_ivalue(u_node);
		if (low_const->const_kind != CONST_OM
		  && high_const->const_kind != CONST_OM
		  && parent_low_const->const_kind != CONST_OM
		  && parent_high_const->const_kind != CONST_OM) {
			/* static range */
			static_check = TRUE;
			global_flag = TRUE;

			if ( const_gt(low_const, high_const)/* null range */
			  ||(const_ge(low_const, parent_low_const)
			  && const_le(high_const, parent_high_const))) {

				/* template    := [val_low, val_high]; */
				val_defined = TRUE;
				val_low = get_const_int(low_const);
				val_high =  get_const_int(high_const);
			}
			else {
				gen_s(I_LOAD_EXCEPTION_REGISTER, symbol_constraint_error);
				gen(I_RAISE);
				/* template    := [val_low, val_high]; */
				val_defined = TRUE;
				val_low = get_const_int(low_const);
				val_high =  get_const_int(high_const);
			}
		}
		else {
			gen_value(l_node);
			gen_value(u_node);
			if (base_type(type_mark) == type_mark) {
				/* Subtype of the base type, no check needed */
				static_check = TRUE;
			}
			else {
				static_check = FALSE;
			}
			global_flag = FALSE;
			/* TBSL: see if int_const is proper for all types if parent_ not
			 * defined	ds 8-1-85
			 */
			/* template     := [parent_low ? 0, parent_high ? 0]; */
			if (parent_low_const->const_kind != CONST_OM) {
				val_defined = TRUE;
				val_low =  get_const_int(parent_low_const);
			}
			else {
				val_defined = TRUE;
				val_low = 0;
			}
			if (parent_high_const->const_kind != CONST_OM) {
				val_defined = TRUE;
				val_high = get_const_int(parent_high_const);
			}
			else {
				val_defined = TRUE;
				val_high = 0;
			}
		}

		TYPE_KIND(type_name) = TYPE_KIND(type_mark);
		TYPE_SIZE(type_name) = TYPE_SIZE(type_mark);
		if (is_enumeration_type(type_name)) {
			/* SETL code builds trailing part then puts standard header at front
			 * In C, we have set val_defined if there are values to insert
			 * and have the values in val_low and val_high, respectively.
			 */
			/* template :=  [TT_E_RANGE, size_of(type_mark)] + template */
			stemplate = template_new(TT_E_RANGE, size_of(type_mark),
			  WORDS_E_RANGE, TT_PTR(&tt_e_range_ptr));
			if (val_defined) {
				tt_e_range_ptr->elow = val_low;
				tt_e_range_ptr->ehigh = val_high;
			}
			reference_of(root_type(type_mark));
			tt_e_range_ptr->ebase = REFERENCE_SEGMENT;
			tt_e_range_ptr->eoff = REFERENCE_OFFSET;
		}
		else {
			/* TBSL: need re adjust type to i_range_l if long, etc */
			/* template := [TT_I_RANGE, size_of(type_mark)]+template; */
			stemplate = template_new(TT_I_RANGE, size_of(type_mark),
			  WORDS_I_RANGE, TT_PTR(&tt_i_range_ptr));
			tt_i_range_ptr->ilow = val_low;
			tt_i_range_ptr->ihigh = val_high;
		}
		/* This is more or less equivalent to INSTALL_TYPE: */
		if (global_flag) {	/* static type */
			assign_same_reference(type_name, get_constant_name(stemplate));
		}
		else {
			if (CURRENT_LEVEL == 1) {/* non-static, global */
				next_global_reference_template(type_name, stemplate);
				gen_s(I_TYPE_GLOBAL, type_name);
			}
			else {
				next_local_reference(type_name);
				temp_name = new_unique_name("type_template");
				assign_same_reference(temp_name, get_constant_name(stemplate));
				gen_s(I_TYPE_LOCAL, temp_name);
				gen_s(I_UPDATE_AND_DISCARD, type_name);
			}
		}

		if (!static_check) {
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
			gen_s(I_QUAL_SUB, type_mark);
			gen_ks(I_DISCARD_ADDR, 1, type_name);
		}
		break;

	case(co_digits):
		l_node = (Node) constraint[2];
		u_node = (Node) constraint[3];
		d_node = (Node) constraint[4];
		tup = get_constraint(TYPE_OF(type_name));
		lbd_node = (Node) tup[2];
		ubd_node = (Node) tup[3];
		dgt_node = (Node) tup[4];
		if (const_gt(get_ivalue(d_node), get_ivalue(dgt_node))) {
			gen_s(I_LOAD_EXCEPTION_REGISTER, symbol_constraint_error);
			gen(I_RAISE);
		}
		low_const = get_ivalue(l_node);
		high_const = get_ivalue(u_node);
		if (low_const->const_kind != CONST_OM
		  && high_const->const_kind != CONST_OM) {
			plow = get_ivalue(lbd_node);
			phigh = get_ivalue(ubd_node);
			if (plow->const_kind != CONST_OM && phigh->const_kind != CONST_OM) {
				if (const_lt(low_const, high_const)
				  && (const_lt(low_const, plow) || const_gt(high_const,phigh))){
					gen_s(I_LOAD_EXCEPTION_REGISTER, symbol_constraint_error);
					gen(I_RAISE);
				}
			}
			global_flag = TRUE;
			/* template    := [low, high]; */
			low_float = REALV(low_const);
			high_float = REALV(high_const);
		}
		else {
			gen_value(l_node);
			gen_value(u_node);
			global_flag = FALSE;
			low_float = 0.0;
			high_float = 0.0;
			/* template    := [0, 0]; */
		}
		TYPE_KIND(type_name) = TYPE_KIND(type_mark);
		TYPE_SIZE(type_name) = TYPE_SIZE(type_mark);
		/* template := [TT_F_RANGE, size_of(type_mark)] + template; */
#ifdef TBSL
		-review carefully the setting of template here
#endif
		stemplate = template_new(TT_FL_RANGE, size_of(type_mark),
		  WORDS_FL_RANGE, TT_PTR(&tt_fl_range_ptr));
		tt_fl_range_ptr->fllow = low_float;
		tt_fl_range_ptr->flhigh = high_float;
		install_type(type_name, stemplate, global_flag);
		break;

	case(co_delta):
#ifdef TBSL
		-- review template initialization. Note that low and high as et
		    -- in template must be longs.
#endif
		l_node = (Node) constraint[2];
		u_node = (Node) constraint[3];
		d_node = (Node) constraint[4];
		s_node = (Node) constraint[5];
		constraint = get_constraint(TYPE_OF(type_name));
		lbd_node = (Node) constraint[2];
		ubd_node = (Node) constraint[3];
		dlt_node = (Node) constraint[4];
		sml_node = (Node) constraint[5];
		consT = get_ivalue(d_node);
		if (consT->const_kind != CONST_RAT)
			chaos("arg not rational");
		rat = consT->const_value.const_rat;
		num1 = num(rat);
		den1 = den(rat);
		consT = get_ivalue(dlt_node);
		/* [num2, den2] := get_ivalue(dlt_node); */
		if (consT->const_kind != CONST_RAT)
			chaos("arg not rational");
		rat = consT->const_value.const_rat;
		num2 = num(rat);
		den2 = den(rat);
		if (int_lss(int_mul(num1, den2), int_mul(num2, den1))) {
			gen_s(I_LOAD_EXCEPTION_REGISTER, symbol_constraint_error);
			gen(I_RAISE);
		}
		/* The subtype uses the same run-time representation as the type
	     * so we place in the template the 'small of the type.
	     */
		small_const = get_ivalue(sml_node);
		split_powers(num(RATV(small_const)));
		inum2 = split_powers_2;
		inum5 = split_powers_5;
		split_powers(den(RATV(small_const)));
		iden2 = split_powers_2;
		iden5 = split_powers_5;
		/* template := [TT_FIXED, size_of(type_mark), num2-den2, num5-den5]; */
		stemplate = template_new(TT_FX_RANGE, size_of(type_mark),
		  WORDS_FX_RANGE, TT_PTR(&tt_fx_range_ptr));
		tt_fx_range_ptr->small_exp_2 = inum2 - iden2;
		tt_fx_range_ptr->small_exp_5 = inum5 - iden5;
		/* TBSL: may want to force size to 4 here */
		root_type(type_name) = root_type(base_type(type_name));
		low_const = get_ivalue(l_node);
		high_const = get_ivalue(u_node);
		if (low_const->const_kind != CONST_OM
		  && high_const->const_kind != CONST_OM) {
			plow = get_ivalue(lbd_node);
			phigh = get_ivalue(ubd_node);
			if (plow->const_kind != CONST_OM && phigh->const_kind != CONST_OM) {
				if (int_lss(int_mul(num(RATV(low_const)),den(RATV(high_const))),
				  int_mul(num(RATV(high_const)), den(RATV(low_const))))
				  && (int_lss(int_mul(num(RATV(low_const)), den(RATV(plow))),
				  int_mul(num(RATV(plow)), den(RATV(low_const))))
				  || int_gtr(int_mul(num(RATV(high_const)), den(RATV(phigh))),
				  int_mul(num(RATV(phigh)), den(RATV(high_const)))))) {
					gen_s(I_LOAD_EXCEPTION_REGISTER, symbol_constraint_error);
					gen(I_RAISE);
				}
			}
			global_flag = TRUE;

			tt_fx_range_ptr->fxlow = rat_tof(low_const, small_const, 1);
			tt_fx_range_ptr->fxhigh = rat_tof(high_const, small_const, 1);

			TYPE_KIND(type_name) = TK_LONG;
			TYPE_SIZE(type_name) = su_size(TK_LONG);
		}
		else {
			global_flag = FALSE;
			segment_put_int(stemplate, 0);
			segment_put_int(stemplate, 0);
			/* template   +:= if template(1+TT_OBJECT_SIZE) = 1 then [0, 0] *
	              else [0, 0, 0, 0] *	end; */
			gen_value(l_node);
			gen_s(I_QUAL_RANGE, type_mark);
			gen_value(u_node);
			gen_s(I_QUAL_RANGE, type_mark);
		}

		install_type(type_name, stemplate, global_flag);
		break;

	case(co_discr):
		type_install_done = FALSE;
		type_mark = base_type(type_mark);
		field_map = (Tuple) constraint[2];
		stemplate = template_new(TT_C_RECORD, size_of(type_mark),
		  WORDS_C_RECORD, TT_PTR(&tt_c_record_ptr));
		reference_of(type_mark);
		tt_c_record_ptr->cbase = REFERENCE_SEGMENT;
		tt_c_record_ptr->coff = REFERENCE_OFFSET;
		/* TBSL: Adjust type_size if no default values for discriminants */
		TYPE_KIND(type_name) = TT_C_RECORD;
		TYPE_SIZE(type_name) = TYPE_SIZE(type_mark);

		/* obtain discriminants in same order as in unconstrained type */
		tup = SIGNATURE(type_mark);
		/* need tup_copy for discr_list since used in tup_frome below */
		discr_list = tup_copy((Tuple) tup[3]);
		tt_c_record_ptr->nb_discr_c = tup_size(discr_list);
		if (tup_size(field_map) == 0) {
			/* Special case: vals of discriminants fetched from record object */
			/* already on TOS. */
			global_flag = FALSE;
			for (i = 1; i <= tup_size(discr_list); i++) {
				segment_put_int(stemplate, 0);
			}
			/* template   +:= [0: x in discr_list]; */
			temp_var = new_unique_name("temporary");

			next_local_reference(temp_var);
			gen_s(I_UPDATE, temp_var);
			while (tup_size(discr_list) != 0) {
				field_name = (Symbol) tup_frome(discr_list);
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, temp_var);
				/* SETL has field_name as last argument, presumably as part of
				 * comment part of instruction and not part of generated code
				 * ds 7-5-85
				 */
				/* gen_ki(I_ADD_IMMEDIATE, mu_word, *
		   		 * field_offset(field_name)(TARGET), field_name);
				 */
				gen_ki(I_ADD_IMMEDIATE, mu_word, FIELD_OFFSET(field_name));
				gen_k(I_DEREF, kind_of(TYPE_OF(field_name)));
			}
		}
		else {
			/* global_flag = is_global(type_mark) and
	    	 *  (forall x in
	    	 * discr_list | is_ivalue(field_map(x))); 
	    	 */
			global_flag = is_global(type_mark) && (TYPE_SIZE(type_mark) != -1);
			FORTUP(x = (Symbol), discr_list, ft1);
				if (!is_ivalue(discr_map_get(field_map, x))) {
					global_flag = FALSE;
					break;
				}
			ENDFORTUP(ft1);
			if (global_flag) {
				/* template +:= [get_ivalue(field_map(x)):x in discr_list]; */
				FORTUP(sym = (Symbol), discr_list, ft1);
					segment_put_const(stemplate,
				      get_ivalue(discr_map_get(field_map, sym)));
				ENDFORTUP(ft1);
			}
			else {
				/* template +:= [0: x in discr_list]; */
				for (i = 1; i <= tup_size(discr_list); i++) {
					segment_put_int(stemplate, 0);
				}
				/* if there is a TT_D_ARRAY or a TT_D_RECORD containing
                 * a TT_D_ARRAY, a check is made so that the discriminant
                 * belongs to the index subtype of the array.
                 */
				while (tup_size(discr_list) != 0) {
					field_name = (Symbol) tup_frome(discr_list);
					d_node = (discr_map_get(field_map, field_name));
					gen_value(d_node);
					gen_s (I_QUAL_RANGE, TYPE_OF (field_name));
				}
				install_type(type_name, stemplate, global_flag);

				gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
				gen (I_CHECK_REC_SUBTYPE);
				type_install_done = TRUE;

			}
		}
		if (! type_install_done) {
			install_type(type_name, stemplate, global_flag);
		}
		break;
	default:

		compiler_error_c("Unexpected subtype constraint: ", constraint);
	}
}

static void install_type(Symbol type_name, Segment stemplate, int global_flag)
															/*;install_type*/
{
	Symbol temp_name;

	if (global_flag) {		/* static type */
		assign_same_reference(type_name, get_constant_name(stemplate));
	}
	else if (CURRENT_LEVEL == 1) {/* non-static, global */
		next_global_reference_template(type_name, stemplate);
		gen_s(I_TYPE_GLOBAL, type_name);
	}
	else {			/* non-static, local */
		next_local_reference(type_name);
		temp_name = new_unique_name("type_template");
		assign_same_reference(temp_name, get_constant_name(stemplate));
		gen_s(I_TYPE_LOCAL, temp_name);
		gen_s(I_UPDATE_AND_DISCARD, type_name);
	}
	/* free template - this is final use*/
	segment_free(stemplate);
}

static Segment make_fixed_template(Const old_lbd, Const old_ubd,
  Const old_delta, Const old_small_arg, struct tt_fx_range **ptr)
													/*;make_fixed_template*/
{
	/*DESCR: Elaborates the template from the front end's fixed point ITYPE.
	 *INPUT: old_itype: Fixed Point ITYPE from ADASEM.(with added
	 *	           small field for the new length clause.  This
	 *		   field will be OM unless small has been set by
	 *		   length clause.
	 *OUTPUT: Returns template: Fixed point type template.
	 */

	int small_exp_2,	/* parameters of new type template */
	  small_exp_5, size;
	int bits;
	int power_conv; /* set when cannot convert small representation */
	long new_lbd, new_ubd;
	int num_2, num_5, num_other, /* powers of numerator */
	  den_2, den_5, den_other;/* powers of denominator */
	Segment stemplate;
	Const old_small;		/* need to copy arg since value changed */
	struct tt_fx_range *tt_fx_range_ptr;

	old_small = rat_const(RATV(old_small_arg));

	/* find SMALL exponents */
	split_powers(num(RATV(old_small)));
	num_2 = split_powers_2;
	num_5 = split_powers_5;
	num_other = split_powers_value;
	/* [den_2, den_5, den_other] := split_powers(den(old_small)); */
	split_powers(den(RATV(old_small)));
	den_2 = split_powers_2;
	den_5 = split_powers_5;
	den_other = split_powers_value;
	if (num_other != den_other) {/* small not allowed */
		user_error("Small not supported by implementation.(Appendix F)");
		power_conv = power_of_2(old_delta);
		if (power_conv) {
			user_error(
			  "Precision not supported by implementation. (Appendix F)");
		}
		small_exp_2 = power_of_2_power;
		small_exp_5 = 0;
		RATV(old_small) = power_of_2_small;
	}
	else {
		small_exp_2 = num_2 - den_2;
		small_exp_5 = num_5 - den_5;
	}
#ifdef TBSL
	if (ABS(small_exp_2) > 30 || ABS(small_exp_5) > 9) {
		-- check that 1/MAX_INT < old_small < MAX_INT 
		    SIGN(small_exp_2) == SIGN(small_exp_5) && 
		    5**(iabs( small_exp_5)) * 2**(iabs( small_exp_2)) > MAX_INT ) {
			user_error(PRECISION_NOT_SUPPORTED);
		}
#endif
	bits = fx_mantissa(RATV(old_lbd), RATV(old_ubd), RATV(old_small))+1;
	/* +1 for sign*/
	if (bits > WORD_SIZE) {
		user_error(PRECISION_NOT_SUPPORTED);
	}
	size = su_size(TK_LONG);	/* FORCE this for initial C version  ds 6-6-85
						*/
	new_lbd = rat_tof(old_lbd, old_small, size);
	new_ubd = rat_tof(old_ubd, old_small, size);
	/* return [TT_FIXED, size, small_exp_2, small_exp_5]+new_lbd+new_ubd; */
	stemplate = template_new(TT_FX_RANGE, size, WORDS_FX_RANGE,
	  TT_PTR(&tt_fx_range_ptr));
	tt_fx_range_ptr->small_exp_2 = small_exp_2;
	tt_fx_range_ptr->small_exp_5 = small_exp_5;
	tt_fx_range_ptr->fxlow = new_lbd;
	tt_fx_range_ptr->fxhigh = new_ubd;
	*ptr = tt_fx_range_ptr;
	return (stemplate);
}

static void split_powers(int *avalue)						/*;split_powers*/
{
	/*DESCR: This procedure splits value into a power of 5, a power of 2
	 *       and the remaining factors.
	 *INPUT: value: integer.
	 *OUTPUT: [pow_2 pow_5 others] such that
	 *        value= 2**pow_2 * 5**pow_5 * others
	 */
	/* The C version does not return a tuple, but sets the variables
	 * split_powers_2, split_powers_5 and split_powers_value global
	 * to this module
	 */

	int     pow_2,		/* desired power of 2 */
	pow_5;		/* desired power of 5 */
	int     *int_2, *int_5;
	int     *v;

	pow_2 = 0;
	pow_5 = 0;
	int_2 = int_fri(2);	/* should be global   */
	int_5 = int_fri(5);
	v     = int_copy(avalue);

	while((v[v[0]] % 2 ) == 0 && v[0] > 0) {
		v = int_quo(v, int_2);
		pow_2 += 1;
	}
	while((v[v[0]] % 5 ) == 0 && v[0] > 0) {
		v = int_quo(v, int_5);
		pow_5 += 1;
	}
	/* return [pow_2, pow_5, value]; */
	split_powers_2 = pow_2;
	split_powers_5 = pow_5;
	split_powers_value = int_toi(v);
}

long rat_tof(Const value, Const small, int size)				/*;rat_tof*/
{
	/* DESCR: This procedure converts a rational number into a fixed
	 *	 point number with the given small and size.
	 * INPUT: value: [num den], A rational number(see RATIONAL
	 *	        ARITHMETIC PACKAGE).
	 *	 small: the given small as a rational number
	 *	 size:  1 or 2, size(in words or tuples) for the result
	 * OUTPUT: [N] N being one or two integers(depending on size)
	 */

	long    N;			/* intermediate value */

	/* for first C version, use rat_tol which returns long. SETL uses rat_toi.*/
	/* force size to be 1 for initial C version */
	size = 1;
	if (value->const_kind != CONST_RAT || small->const_kind != CONST_RAT) {
#ifdef DEBUG
		zpcon(value); 
		zpcon(small);
#endif
		chaos("rat_tof arguments not rationals");
	}
	N = rat_tol(rat_div(RATV(value), RATV(small)));
	if (size == 1) {
#ifdef TBSN
-- ignore overflow: 
		if called by make_fixed_template message already
		-- emitted. In case of expression or initial value should be OK
		    -- (as long as they belong to the type)
		    if (arith_overflow) {
			compiler_error("Value too big");
		}
#endif
		return N;
	}
#ifdef TBSN
	-- do this when have multiple fixed types
	    $will work anyway...
	else
	if N >= 0 then
	if N > MAX_INT*(MAX_UNS+1)+MAX_UNS then
	compiler_error("Value too big");
	end if;
	RAT_TO_F_1 = N div (MAX_UNS+1);
	RAT_TO_F_2 = N mod (MAX_UNS+1);
	return;
	else
	if N < MIN_INT*(MAX_UNS+1) then
	compiler_error("Value too big");
	end if;
	RAT_TOF_1 = (N-MAX_UNS) div (MAX_UNS+1);
	RAT_TOF_2 = N mod (MAX_UNS+1);
	return;
	end if;
	end if;
#endif
}

static void process_record(Symbol type_name)				/*;process_record*/
{
	Tuple repr_tup, tup, type_list, discr_decl, fixed_part, dep_types;
	Node invariant_node, variant_node, node, id_list_node, n, d;
	Node subtype_node, id_node, type_node;
	Fortup ft1, ft2;
	int     i, varying_size_flag, type_class, discr_with_defaults;
	Symbol subtype_name, t_name, discr, some_discr_name;
	Tuple discr_subtypes;
	Segment stemplate;
	struct tt_u_record *tt_u_record_ptr;

#ifdef TRACE
	if (debug_flag )
		gen_trace_symbol("PROCESS_RECORD", type_name);
#endif

	segment_empty(VARIANT_TABLE);
	CURRENT_FIELD_NUMBER = 0;
	CURRENT_FIELD_OFFSET = 0;
	segment_empty(FIELD_TABLE);
	INTERNAL_ACCESSED_TYPES = tup_new(0);
	STATIC_REC = TRUE;		/* just an assumption... */

	tup = SIGNATURE(type_name);
	/* [[invariant_node, variant_node], discr_decl] := SIGNATURE(type_name); */
	/* recall that signature is 5-tuple in C version */
	invariant_node = (Node) tup[1];
	variant_node = (Node) tup[2];
	discr_decl = (Tuple) tup[3];
	type_list = tup_new(0);
	fixed_part = tup_new(0);
	FORTUP(node = (Node), N_LIST(invariant_node), ft1);
		switch(N_KIND(node)) {
		case(as_field):
			id_list_node = N_AST1(node);
			FORTUP(n = (Node), N_LIST(id_list_node), ft2);
				fixed_part = tup_with(fixed_part, (char *) N_UNQ(n));
			ENDFORTUP(ft2);
			/* fixed_part    +:= [N_UNQ(n) : n in N_LIST(id_list_node)]; */
			break;
		case(as_subtype_decl):
			type_list = tup_with(type_list, (char *) node);
			break;
		case(as_deleted):
			break;
		default:
			compiler_error_k("Unexpected kind of selector in record: ",
		      node);
		}
	ENDFORTUP(ft1);

	/* then, are there discriminants ? */
	if (tup_size(discr_decl) != 0) {
		linearize_record(discr_decl, OPT_NODE);

		/* discriminant dependent subtypes: elaborate and check if varying sz */
		/* dep_types         := [discr_dep_subtype(d):d in type_list]; */
		dep_types = tup_new(tup_size(type_list));
		FORTUPI(d = (Node), type_list, i, ft1);
			dep_types[i] = (char *) discr_dep_subtype(d);
		ENDFORTUP(ft1);
		varying_size_flag = FALSE;
		for (i = 1; i <= tup_size(type_list); i++) {
			subtype_node = (Node) type_list[i];
			id_node = N_AST1(subtype_node);
			subtype_name = N_UNQ(id_node);

			/* An anonymous subtype used by a constrained access subtype 
			 * indication, that refers to discriminants, does not make the
			 * record of variable size....
			 */
			if (dep_types[i] && !tup_mem((char *) subtype_name,
			  INTERNAL_ACCESSED_TYPES)) {
				varying_size_flag = TRUE;
				break;
			}
		}

		/* class of type: */
		some_discr_name = (Symbol) discr_decl[tup_size(discr_decl)];
		discr_with_defaults = (Node) default_expr(some_discr_name) != OPT_NODE;
		if (discr_with_defaults) {
			type_class = TT_U_RECORD;
			TYPE_KIND(type_name) = TT_U_RECORD;
			/* discr_subtypes := [ TYPE_OF(discr) : discr in discr_decl]; */
			discr_subtypes = tup_new(tup_size(discr_decl));
			FORTUPI(discr = (Symbol), discr_decl, i, ft1);
				discr_subtypes[i] = (char *) TYPE_OF(discr);
			ENDFORTUP(ft1);
			/* loop forall i in [1..#type_list] | dep_types(i) do */
			for (i = 1; i <= tup_size(type_list); i++) {
				if (dep_types[i]) {
					id_node = N_AST1((Node) type_list[i]);
					eval_max_size(N_UNQ(id_node), discr_subtypes);
				}
			}
		}
		else if (varying_size_flag) {
			TYPE_KIND(type_name) = TT_V_RECORD;
			type_class = TT_V_RECORD;
		}
		else {
			TYPE_KIND(type_name) = TT_U_RECORD;
			type_class = TT_U_RECORD;
		}

		stemplate = template_new(type_class, 0, WORDS_U_RECORD,
		  TT_PTR(&tt_u_record_ptr));
		tt_u_record_ptr->nb_field_u = 0;	/* nb_fields */
		tt_u_record_ptr->nb_discr_u = tup_size(discr_decl);	/* nb_discr */
		tt_u_record_ptr->nb_fixed_u =
		  tup_size(discr_decl) + tup_size(fixed_part);		/* nb_fixed */
		/* set first entry in field_table after end of fixed part of template */

		tt_u_record_ptr->first_case = linearize_record(fixed_part,variant_node);
		/* size of variant table */
		tt_u_record_ptr->variant = segment_get_maxpos(VARIANT_TABLE);
	}
	else {
		FORTUP(type_node = (Node), type_list, ft1);/* Elaborate types */
			id_node = N_AST1(type_node);
			t_name = N_UNQ(id_node);
			gen_subtype(t_name);
		ENDFORTUP(ft1);
		TYPE_KIND(type_name) = TT_RECORD;
		type_class = TT_RECORD;
		stemplate = template_new(TT_RECORD, 0, WORDS_RECORD, 
		  TT_PTR(&tt_u_record_ptr));
		linearize_record(fixed_part, OPT_NODE);
	}

	if (type_class == TT_V_RECORD) {
		TYPE_SIZE(type_name) = -1;/* TBSL: SETL uses -1 here */
	}
	else {
		TYPE_SIZE(type_name) = CURRENT_FIELD_OFFSET;
	}
	tt_u_record_ptr->object_size = size_of(type_name);
	repr_tup = REPR(type_name);
	if (repr_tup != (Tuple)0) {
	   tt_u_record_ptr->repr_size = (int) repr_tup[2];
    }
	else {
	   tt_u_record_ptr->repr_size = 0;
	}
	/* template may also be tt_record case, but no harm since
	 * nb_field_u at same offset as nb_field 
	 */
	tt_u_record_ptr->nb_field_u = CURRENT_FIELD_NUMBER;

	/* template +:= FIELD_TABLE+VARIANT_TABLE; */
	segment_append(stemplate, FIELD_TABLE);
	segment_append(stemplate, VARIANT_TABLE);
	install_type(type_name, stemplate, STATIC_REC);
}

static int linearize_record(Tuple fixed_part_list, Node variant_part_node)
														/*;linearize_record*/
{
	/* process fixed part
	 * For each record comp in fixed part, add three entries to FIELD_TABLE:
	 * offset, base of template for comp, segment of template for component.
	 */

	Symbol f_name, f_type, name;
	Fortup ft1, ft2;
	int     tsize, first_field, v_index, index;
	Node variant_node, name_node, others_body, alt_node;
	Node f_node, v_node, id_list_node, node, n_sym;
	int     save_field_offset, max_field_offset, variant_offset;
	Tuple bodies, f_part, ntable, tup4, table, tup;
	Tuple case_range;
	int     i, n, b;

#ifdef TRACE
	if (debug_flag) {
		gen_trace_symbols("LINEARIZE_RECORD_F", fixed_part_list);
		gen_trace_node("LINEARIZE_RECORD_V", variant_part_node);
	}
#endif
	FORTUP(f_name = (Symbol), fixed_part_list, ft1);
		f_type = TYPE_OF(f_name);
		FIELD_NUMBER(f_name) = (char *) CURRENT_FIELD_NUMBER;
		CURRENT_FIELD_NUMBER += 1;
		FIELD_OFFSET(f_name) = CURRENT_FIELD_OFFSET;
		/* FIELD_TABLE +:= [CURRENT_FIELD_OFFSET] + * reference_of(f_type); */
		segment_put_word(FIELD_TABLE, CURRENT_FIELD_OFFSET);
		reference_of(f_type);
		segment_put_int(FIELD_TABLE, REFERENCE_SEGMENT);
		segment_put_int(FIELD_TABLE, REFERENCE_OFFSET);
		/* STATIC_REC  and:= is_static_type(f_type); */
		STATIC_REC = STATIC_REC ? is_static_type(f_type) : FALSE;
		if (CURRENT_FIELD_OFFSET != -1) {
			tsize = TYPE_SIZE(f_type);
			if (tsize >= 0 && CURRENT_FIELD_OFFSET >= 0) {
				CURRENT_FIELD_OFFSET += tsize;
			}
			else {
				CURRENT_FIELD_OFFSET = -1;
			}
		}
	ENDFORTUP(ft1);

	if (variant_part_node != OPT_NODE) {
		name_node = N_AST1(variant_part_node);
		variant_node = N_AST2(variant_part_node);
		name = N_UNQ(name_node);
		/*-- bodies is used in tup_from? below: see if tup_copy needed here
   		 *-    ds  6-25-85
   		 */
		tup = make_case_table(variant_node);
		table = (Tuple) tup[1];
		bodies = (Tuple) tup[2];
		bodies = tup_copy(bodies);/* to be safe - see above comment */
		others_body = (Node) tup[3];
		tup_free(tup);
		/* [table, bodies, others_body] := make_case_table(variant_node); */
		n = tup_size(table);
		table = tup_exp(table, n + 1);
		for (i = n; i > 0; i--)
			table[i + 1] = table[i];
		tup = tup_new(2);
		tup[1] = (char *)(n + 1);
		tup[2] = (char *) 0;
		table[1] = (char *) tup;
		ntable = tup_new(n+1);
		/* table := [ [#table+1, 0] ] + table; */
		if (others_body != OPT_NODE) {
			index = 0;
			/* bodies := [others_body]+bodies; */
			n = tup_size(bodies);
			bodies = tup_exp(bodies, n + 1);
			for (i = n; i > 0; i--)
				bodies[i + 1] = bodies[i];
			bodies[1] = (char *) others_body;
		}
		else {
			index = 1;
			/* The SETL version mixes quadruples and pairs in the tuple
			 * table. Here we keep all quadruples in another tuple ntable; 
			 * table := * [ [a, if b = 0 then [0, -1, -1] else b end]: [a, b]
			 * in table ];
			 */
			FORTUPI(tup = (Tuple), table, i, ft1);
				b = (int) tup[2];
				if (b == 0) {
					tup4 = tup_new(4);
					tup4[1] = tup[1];
					tup4[2] = (char *) 0;
					tup4[3] = (char *) - 1;
					tup4[4] = (char *) - 1;
					ntable[i] = (char *) tup4;
				}
			ENDFORTUP(ft1);
		}

		/*  to allow overlapping of variants: */
		save_field_offset = max_field_offset = CURRENT_FIELD_OFFSET;
		/*  process each variant */
		while(tup_size(bodies) != 0) {
			CURRENT_FIELD_OFFSET = save_field_offset;
			first_field = CURRENT_FIELD_NUMBER;

			alt_node = (Node) tup_fromb(bodies);
			f_node = N_AST1(alt_node);
			v_node = N_AST2(alt_node);
			f_part = tup_new(0);
			FORTUP(node = (Node), N_LIST(f_node), ft1);
				id_list_node = N_AST1(node);
				/* f_part        +:= [ N_UNQ(n) : n in N_LIST(id_list_node)]; */
				FORTUP(n_sym = (Node), N_LIST(id_list_node), ft2);
					f_part = tup_with(f_part, (char *) N_UNQ(n_sym));
				ENDFORTUP(ft2);
			ENDFORTUP(ft1);
			v_index = linearize_record(f_part, v_node);
			/* case_range := [first_field, first_field+#f_part-1, v_index]; */
			case_range = tup_new(3);
			case_range[1] = (char *) first_field;
			case_range[2] = (char *)(first_field + tup_size(f_part) - 1);
			case_range[3] = (char *) v_index;
			/* table := 
			 * [ [a, if b = index then case_range else b end]: [a, b] in
			 * table ]; 
			 */
			FORTUPI(tup = (Tuple), table, i, ft1);
				b = (int) tup[2];
				if (b == index) {
					tup4 = tup_new(4);
					tup4[1] = tup[1];
					tup4[2] = case_range[1];
					tup4[3] = case_range[2];
					tup4[4] = case_range[3];
					ntable[i] = (char *) tup4;
				}
			ENDFORTUP(ft1);
			if (max_field_offset < CURRENT_FIELD_OFFSET) {
				max_field_offset = CURRENT_FIELD_OFFSET;
			}
			index += 1;
		}
		CURRENT_FIELD_OFFSET = max_field_offset;
		variant_offset = segment_get_maxpos(VARIANT_TABLE);
		/* VARIANT_TABLE       +:= [FIELD_NUMBER(name)]
         *               +/[ [a, b, c, d]: [a, [b, c, d]] in table ];
		 */

		/* this code was added because of a test like :
		 *
		 *   type x (a, b : integer) is record
		 *      case a is ...
		 *        when others =>
		 *   case b is
		 *              when others => ...;
		 *           end case;
		 *      end case;
		 *   end record;
		 *
		 *  The inner case does not refer explictly to "b". Therefore in the
		 *  tree its name is not set. In this  case "name" is null. On acf2,
		 *  the generated value for FIELD_NUMBER (name) was anything. On lang1
		 *  there was an internal error (null pointer dereference). 
		 *  Now in this case, the value is set to 0
		 */

		if (name == (Symbol) 0) {
			segment_put_int(VARIANT_TABLE, 0);
		}
		else {
			segment_put_int(VARIANT_TABLE, (int)FIELD_NUMBER(name));
		}
		FORTUP(tup = (Tuple), ntable, ft1);
			segment_put_int(VARIANT_TABLE, (int) tup[1]);
			segment_put_int(VARIANT_TABLE, (int) tup[2]);
			segment_put_int(VARIANT_TABLE, (int) tup[3]);
			segment_put_int(VARIANT_TABLE, (int) tup[4]);
		ENDFORTUP(ft1);
		return variant_offset;
	}
	else {
		return - 1;		/* = no variant part */
	}
}

static int discr_dep_subtype(Node decl)					/*;discr_dep_subtype*/
{
	/*
	 *   This procedure takes care of the special type templates
	 *   used for subtypes whose constraints depends on the discriminants
	 *   of the enclosing record.
	 *
	 *   The templates produced are TT_D_RECORD and TT_D_ARRAY.
	 *
	 *   return TRUE in that case, FALSE if not a discr_dep_subtype.
	 */

	Node id_node, low, high, lbd, ubd, de, discr_value_node;
	Symbol type_name, type_mark, indx_type, discr_type, comp_type, field_name;
	Tuple constraint, tup, index_list, field_map, discr_list;
	int     varying_size_flag, max_nb_elem, nb_dim, tsize, i, n;
	Fortup ft1;
	Const min_low, max_high;
	Segment stemplate;
	int discr_depends, discr_value; /* used for get_discr values */
	struct tt_d_type   *tt_d_type_ptr;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("DISCR_DEP_SUBTYPE", decl);
#endif

	id_node = N_AST1(decl);
	type_name = N_UNQ(id_node);
	type_mark = base_type(type_name);
	constraint = get_constraint(type_name);
	varying_size_flag = FALSE;
	stemplate = (Segment) 0;

	switch((int) constraint[1]) {

	case(co_access):
		INTERNAL_ACCESSED_TYPES = tup_with(INTERNAL_ACCESSED_TYPES,
		  (char *) DESIGNATED_TYPE(type_name));
		compile(decl);
		return FALSE;

	case(co_index):
		tup = SIGNATURE(type_name);
		index_list = (Tuple) tup[1];
		comp_type = (Symbol) tup[2];
		max_nb_elem = 1;
		FORTUP(indx_type = (Symbol), index_list, ft1);
			tup = SIGNATURE(indx_type);
			low = (Node) tup[2];
			high = (Node) tup[3];
			if (is_discr_ref(low)) {
				varying_size_flag = TRUE;
				discr_type = N_TYPE(low);
				tup = SIGNATURE(discr_type);
				low = (Node) tup[2];
			}
			if (is_discr_ref(high)) {
				varying_size_flag = TRUE;
				discr_type = N_TYPE(high);
				tup = SIGNATURE(discr_type);
				high = (Node) tup[3];
			}
			min_low = get_ivalue(low);
			max_high = get_ivalue(high);
			if (max_nb_elem >= 0
		      && min_low->const_kind != CONST_OM
		      && max_high->const_kind != CONST_OM) {
				max_nb_elem *= get_ivalue_int(high) - get_ivalue_int(low) + 1;
			}
			else {
				max_nb_elem = -1;
			}
		ENDFORTUP(ft1);
		if (!varying_size_flag) {
			compile(decl);
			return FALSE;
		}
		nb_dim = tup_size(index_list);
		tsize = TYPE_SIZE(comp_type);
		TYPE_SIZE(type_name) = (max_nb_elem < 0 || tsize < 0) ? -1
		  : max_nb_elem * tsize;
		TYPE_KIND(type_name) = TT_D_ARRAY;

		reference_of(type_mark);
		/* template        := [TT_D_ARRAY, size_of(type_name)]+ref+[nb_dim]; */
		stemplate = template_new(TT_D_ARRAY, size_of(type_name),
		  WORDS_D_TYPE, TT_PTR(&tt_d_type_ptr));
		tt_d_type_ptr->dbase = REFERENCE_SEGMENT;
		tt_d_type_ptr->doff = REFERENCE_OFFSET;
		tt_d_type_ptr->nb_discr_d = nb_dim;

		FORTUP(indx_type = (Symbol), index_list, ft1);
			tup = SIGNATURE(indx_type);
			low = (Node) tup[2];
			high = (Node) tup[3];
			/* template +:= get_discr(low);  template +:= get_discr(high); */
			get_discr(low, &discr_depends, &discr_value);
			segment_put_int(stemplate, discr_depends);
			segment_put_int(stemplate, discr_value);
			get_discr(high, &discr_depends, &discr_value);
			segment_put_int(stemplate, discr_depends);
			segment_put_int(stemplate, discr_value);
		ENDFORTUP(ft1);
		break;

	case(co_discr):
		field_map = (Tuple) constraint[2];
		n = tup_size(field_map);
		for (i = 1; i <= n; i += 2) {
			de = (Node) field_map[i+1];
			varying_size_flag |= is_discr_ref(de);
		}

		if (!varying_size_flag) {
			compile(decl);
			return FALSE;
		}
		TYPE_KIND(type_name) = TT_D_RECORD;
		TYPE_SIZE(type_name) = TYPE_SIZE(type_mark);
		/* template := [TT_D_RECORD, size_of(type_name)]+ref+[#field_map]; */
		stemplate = template_new(TT_D_RECORD, size_of(type_name),
		  WORDS_D_TYPE, TT_PTR(&tt_d_type_ptr));
		reference_of(type_mark);
		tt_d_type_ptr->dbase = REFERENCE_SEGMENT;
		tt_d_type_ptr->doff = REFERENCE_OFFSET;
		/* In SETL, want number of entries in field map; in C, this
    	 * is number of entries in tuple used for for field map divided
    	 * by two, since two elements are required for each single entry
    	 * (domain and range values) in SETL version.
    	 */
		tt_d_type_ptr->nb_discr_d = tup_size(field_map) / 2;
		/* obtain discriminants in same order as in unconstrained type */
		tup = SIGNATURE(type_mark);
		discr_list = (Tuple) tup[3];
		FORTUP(field_name = (Symbol), discr_list, ft1);
			discr_value_node = discr_map_get(field_map, field_name);
			if (N_KIND (discr_value_node) == as_qual_range) {
				N_TYPE (discr_value_node) = root_type(TYPE_OF (field_name));
			}
			/* template   +:= get_discr(discr_value); */
			get_discr(discr_value_node, &discr_depends, &discr_value);
			segment_put_int(stemplate, discr_depends);
			segment_put_int(stemplate, discr_value);
		ENDFORTUP(ft1);
		break;

	case(co_range):
		lbd = (Node) constraint[2];
		ubd = (Node) constraint[3];
		if (is_discr_ref(lbd) || is_discr_ref(ubd)) {
			/* can only be an anonymous type for an index of a TT_D_ARRAY
			 * no explicit template built for it
			 */
			break;
		}
		else {
			compile(decl);
		}
		return FALSE;

	default:
		return FALSE;
	}
	if (stemplate != (Segment) 0) {
		install_type(type_name, stemplate, FALSE);
	}
	return varying_size_flag;
}

static void get_discr(Node node, int *discr_depends, int *discr_value)
																/*;get_discr*/
{
	/* discr_depends and discr_value are used to return values corresponding
	 * to use of tuple for SETL return value 
	 */

	/*
	 * if the expression depends on a discriminant, then returns
	 *    [ 1, field number of the discriminant ]
	 * otherwise return
	 *    [ 0, value of the discriminant ]
	 *
	 */

	Symbol discr;
	int     fn;

#ifdef TRACE
	if (debug_flag)
		gen_trace_node("GET_DISCR", node);
#endif

	if (is_discr_ref(node)) {
		if (N_KIND(node) == as_qual_range)
			node = N_AST1(node);
		discr = N_UNQ(node);
		fn = (int) FIELD_NUMBER(discr);
		gen_kvc(I_PUSH_IMMEDIATE, mu_byte, int_const(fn), "discr. ref.");
		*discr_depends = TRUE;
		*discr_value = fn;
		return;
	}
	else {
		gen_value(node);
		*discr_depends = FALSE;
		*discr_value = 0;
		return;
	}
}

static void eval_max_size(Symbol type_name, Tuple discr_subtypes)
															/*;eval_max_size*/
{
	Symbol discr, type_mark, comp_type, indx_type;
	int     discr_low, discr_high, fn;
	Node low_node, high_node;
	Tuple constraint, index_list, tup;

#ifdef TRACE
	if (debug_flag)
		gen_trace_symbol("EVAL_MAX_SIZE", type_name);
#endif
	if (size_of(type_name) != -1) {/* static, already evaluated */
		return;
	}

	type_mark = TYPE_OF(type_name);
	constraint = get_constraint(type_name);

	switch((int) constraint[1]) {

	case(co_access):
		break;

	case(co_index):
		comp_type = (Symbol) COMPONENT_TYPE(type_mark);
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
		/* WORD_OFF is(obscure) macro defined in type.h to get
		 * offset(in ints) to object_size field 
		 */
		gen_kic(I_ADD_IMMEDIATE, mu_word, WORD_OFF(tt_i_range, object_size),
		  "Object size");
		gen_s(I_PUSH_EFFECTIVE_ADDRESS, comp_type);
		gen_kic(I_ADD_IMMEDIATE, mu_word, WORD_OFF(tt_i_range, object_size),
		  "Compon. size");
		gen_k(I_DEREF, kind_of(symbol_integer));
		tup = INDEX_TYPES(type_name);
		index_list = tup_copy(tup);
		while(tup_size(index_list) != 0) {
			indx_type = (Symbol) tup_fromb(index_list);
			tup = SIGNATURE(indx_type);
			low_node = (Node) tup[2];
			high_node = (Node) tup[3];
			discr_low = is_discr_ref(low_node);
			discr_high = is_discr_ref(high_node);
			if (!(discr_low | discr_high)) {
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, indx_type);
				gen_kv(I_ATTRIBUTE, ATTR_T_LENGTH, int_const(0));
			}
			else {
				if (discr_high) {
					if (N_KIND(high_node) == as_qual_range)
						high_node = N_AST1(high_node);
					discr = N_UNQ(high_node);
					fn = (int) FIELD_NUMBER(discr) + 1;
					/* field # start from 0 */
					if (base_type (indx_type) == ((Symbol) discr_subtypes [fn]))
						gen_s(I_PUSH_EFFECTIVE_ADDRESS, TYPE_OF(indx_type));
					else
						gen_s(I_PUSH_EFFECTIVE_ADDRESS,
						  (Symbol) discr_subtypes[fn]);
					gen_kv(I_ATTRIBUTE, ATTR_T_LAST, int_const(0));
				}
				else {
					if (base_type (indx_type) == (N_TYPE (high_node)))
						gen_s(I_PUSH_EFFECTIVE_ADDRESS, TYPE_OF(indx_type));
					else
						gen_s(I_PUSH_EFFECTIVE_ADDRESS, N_TYPE (high_node));
					gen_kv(I_ATTRIBUTE, ATTR_T_LAST, int_const(0));
				}
				if (discr_low) {
					if (N_KIND(low_node) == as_qual_range)
						low_node = N_AST1(low_node);
					discr = N_UNQ(low_node);
					fn = (int) FIELD_NUMBER(discr) + 1;
					/* field # start from 0 */
					if (base_type (indx_type) == ((Symbol) discr_subtypes [fn]))
						gen_s(I_PUSH_EFFECTIVE_ADDRESS, TYPE_OF(indx_type));
					else
						gen_s(I_PUSH_EFFECTIVE_ADDRESS,
						  (Symbol) discr_subtypes[fn]);
					gen_kv(I_ATTRIBUTE, ATTR_T_FIRST, int_const(0));
				}
				else {
					if (base_type (indx_type) == (N_TYPE (low_node)))
						gen_s(I_PUSH_EFFECTIVE_ADDRESS, TYPE_OF(indx_type));
					else
						gen_s(I_PUSH_EFFECTIVE_ADDRESS, N_TYPE (low_node));
					gen_kv(I_ATTRIBUTE, ATTR_T_FIRST, int_const(0));
				}
				gen_k(I_SUB, kind_of(symbol_integer));
				gen_ki(I_ADD_IMMEDIATE, kind_of(symbol_integer), 1);
			}
			gen_k(I_MUL, kind_of(symbol_integer));
		}
		gen_kc(I_MOVE, mu_word, "update tt size");
		break;

	case(co_discr):
		break;		/* should be no problem as the TT_D_RECORD is
						   constrained */

	case(co_range):
		break;
	}
}
