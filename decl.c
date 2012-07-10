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
#include "setprots.h"
#include "maincaseprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "segment.h"
#include "genprots.h"
#include "typeprots.h"
#include "statprots.h"
#include "segmentprots.h"
#include "exprprots.h"
#include "gmiscprots.h"
#include "gutilprots.h"
#include "axqrprots.h"
#include "declprots.h"

static void gen_structured_object(Node, Symbol, int);

void create_object(Tuple id_list_arg, Symbol type_name, Node init_node,
  int obj_is_constant)										 /*;create_object*/
{
	/*
	 * This procedure is used to create objects (const or var).
	 * id_list is a list (tuple) of name nodes of objects to be created.
	 * The initialization part cannot have side effect, unless id_list
	 * contains a single element (transformation by expander)
	 *
	 * In order to generate not too bad a code, this procedure is organized
	 * as a gigantic if ... elseif ... elseif... structure, checking for the
	 * different configurations. Optimizations may still be added.
	 *
	 * The following cases are considered:
	 *
	 *       1/ Size of object and initial value are known statically.
	 *             a/ Global object or local constant (promoted to global)
	 *                with static initial value.
	 *             b/ Global object initialized with dynamic value.
	 *                Static part is initialized in data segment.
	 *             c/ Uninitialized global object (variable or deferred
	 *                constant).
	 *             d/ Local constant initialized with dynamic value,
	 *                deferred constant, or local variable.
	 *              
	 *       2/ Size of object is not known statically
	 *             a/ Global object with variable size (transformed into
	 *                renaming).
	 *             b/ Local array or record with variable size.
	 *
	 */

	Node		node, id, first_id, last_id, init_call_node, pre_node;
	Symbol	first_name, obj_name;
	int		obj_is_global, ikind, i, n;
	Fortup	ft1;
	Segment	init_val;	/* type should be Ivalue */
	Node		dyn_node;
	Symbol	model_name, subtype;
	Tuple	tup, id_list;
	Const	ival, small_const;
	int          special_aggregate;

	/* id_list_arg needed since id_list used desctructively  6-25-85 */
	id_list = tup_copy(id_list_arg);
#ifdef TRACE
	if (debug_flag) {
		/*gen_trace("CREATE_OBJECT", id_list);*/
		gen_trace("CREATE_OBJECT");
		FORTUP(node = (Node), id_list, ft1);
			gen_trace_node("  CREATE_OBJECT argument", node);
		ENDFORTUP(ft1);
	}
#endif
	init_val = (Segment)0; /* indicate not yet defined */
	obj_is_global = CURRENT_LEVEL == 1;
	if (N_KIND(init_node) == as_init_call) {
		/* Initialization procedure call */
		init_call_node = init_node;
		init_node      = OPT_NODE;
	}
	else {
		init_call_node = OPT_NODE;
	}

	while (N_KIND(init_node) == as_insert) {
		FORTUP(pre_node = (Node), N_LIST(init_node), ft1);
			compile(pre_node);
		ENDFORTUP(ft1);
		init_node = N_AST1(init_node);
	}

	if (N_KIND(init_node) == as_raise) {
		/* Simplest case, indeed. */
		compile(init_node);
		init_node = OPT_NODE;
	}

	if (has_static_size(type_name) && !(is_array_type(type_name)
	  &&is_unconstrained(type_name))
	  && (init_node == OPT_NODE ||has_static_size(get_type(init_node)))) {
		/*
		 * 1- Size of object is known statically(and also size of initial value)
		 * -------------------------------------
		 */
		if ((obj_is_global || obj_is_constant) && is_ivalue(init_node)) {
			/*
			 *         1a- Global object or local const (promoted to global)
			 *             with static initial value.
			 *             Generate objects in data seg initialized with value
			 *             Generate only one object for multiple constants.
			 */
			if (is_fixed_type(type_name)) {
				init_val = segment_new(SEGMENT_KIND_DATA, 1);
				small_const = small_of(base_type(type_name));
				segment_put_long(init_val , rat_tof(get_ivalue(init_node),
				  small_const, size_of(type_name) ));
			}
			else if (is_simple_type(type_name)) {
				ival = get_ivalue(init_node);
				ikind = ival->const_kind;
				if(ikind == CONST_INT) {
					init_val = segment_new(SEGMENT_KIND_DATA, 1);
					segment_put_word(init_val, ival->const_value.const_int);
				}
				else if(ikind == CONST_REAL) {
					init_val = segment_new(SEGMENT_KIND_DATA, 1);
					segment_put_real(init_val, ival->const_value.const_real);
				}
				else {
#ifdef DEBUG
					printf("const_kind %d\n", ikind);
#endif		
					chaos("create_object:unsupported kind");
				}
			}
			else if (is_array_type(type_name)) {
				/* build the appropriate vector... */
				init_val = array_ivalue(init_node);
			}
			else if (is_record_type(type_name)) {
				init_val = record_ivalue(init_node);
			}
			else {
				compiler_error_k("Unknown type for constant ", init_node);
				return;
			}
			if (obj_is_constant) {
				first_name = get_constant_name(init_val);
				FORTUP(id = (Node), id_list, ft1);
					obj_name = N_UNQ(id);
					assign_same_reference(obj_name, first_name);
				ENDFORTUP(ft1);
			}
			else {
				FORTUP(id = (Node), id_list, ft1);
					obj_name = N_UNQ(id);
					next_global_reference_segment(obj_name, init_val);
				ENDFORTUP(ft1);
			}
		}
		else if (obj_is_global && init_node != OPT_NODE) {
			/*
			 *          1b- Global object initialized with dynamic value
			 *              Generate first object in data seg with static part
			 *              initialized, compile code to initialize the rest,
			 *              then assign first object to others
			 */
			if (N_KIND(init_node) == as_array_aggregate) {
				init_val = array_ivalue(init_node);
			}
			else if (N_KIND(init_node) == as_record_aggregate) {
				init_val = record_ivalue(init_node);
			}
			else {
				/* TBSL: review translation from SETL */
				/* build segment of desired length, initially all zero */
				n = size_of(type_name);
				init_val = segment_new(SEGMENT_KIND_DATA, n);
				for (i = 1; i <= n; i++) {
					segment_put_word(init_val, 0);
				}
			}
			FORTUP(id = (Node), id_list, ft1);
				obj_name = N_UNQ(id);
				next_global_reference_segment(obj_name, init_val);
			ENDFORTUP(ft1);

			if (is_simple_type(type_name)) {
				gen_value(init_node);
				last_id = (Node) tup_frome(id_list);
				FORTUP(id = (Node), id_list, ft1);
					id = (Node) tup_fromb(id_list);
					obj_name = (Symbol) N_UNQ(id);
					gen_k(I_DUPLICATE, kind_of(type_name));
					gen_ks(I_POP, kind_of(type_name), obj_name);
				ENDFORTUP(ft1);
				obj_name = N_UNQ(last_id);
				gen_ks(I_POP, kind_of(type_name), obj_name);
			}
			else {
				first_id = (Node) tup_fromb(id_list);
				if (is_aggregate(init_node)) {
					init_node = N_AST2(N_AST1(init_node));
					compile(init_node);
				}
				else {
					select_assign(first_id, init_node, type_name);
				}
				FORTUP(id = (Node), id_list, ft1);
					select_assign(id, first_id, type_name);
				ENDFORTUP(ft1);
			}
		}
		else if (obj_is_global) {
			/*
			 *         1c- Uninitialized global object (Variable or deferred
			 *             constant)
			 *             Generate objects in data segment. If initialization
			 *             procedure, call it on first object, then assign first
			 *             object to others.
			 */
			/* build a segment, initially all zeros, of desired length */
			n = size_of(type_name);
			/*
			 * this is a kludge for deferred const EMPTY in VAR_STRING package.
			 */
			if (n== 0) n = 3;
			init_val = segment_new(SEGMENT_KIND_DATA, n);
			for (i = 1; i <= n; i++)
				segment_put_word(init_val, 0);
			FORTUP(id = (Node), id_list, ft1);
				obj_name = N_UNQ(id);
				next_global_reference_segment(obj_name, init_val);
			ENDFORTUP(ft1);
			if (init_call_node != OPT_NODE ) {
				compile(init_call_node);     /* This initializes 1st object */
				first_id = (Node) tup_fromb(id_list);
				FORTUP(id = (Node), id_list, ft1); /* Assign it to other objs */
				select_assign(id, first_id, type_name);
				ENDFORTUP(ft1);
			}
		}
		else {
			/*
			 *     1d- Local constant initialized with dynamic value, deferred
			 *         constant, or local variable, initialized or not.
			 *         Create local references. If no initialization (implicit
			 *         or explicit) create objects, otherwise create and
			 *         initialize first objects, and create copies for others.
			 */
			FORTUP(id = (Node), id_list, ft1);
				next_local_reference(N_UNQ(id));
			ENDFORTUP(ft1);
			if (is_simple_type(type_name)) {
				if (init_node != OPT_NODE) {
					gen_value(init_node);
					last_id = (Node) tup_frome(id_list);
					FORTUP(id = (Node), id_list, ft1);
						gen_k(I_DUPLICATE, kind_of(type_name));
						gen_k(I_CREATE_COPY, kind_of(type_name));
						gen_s(I_UPDATE_AND_DISCARD, N_UNQ(id));
					ENDFORTUP(ft1);
					gen_k(I_CREATE_COPY, kind_of(type_name));
					gen_s(I_UPDATE_AND_DISCARD, N_UNQ(last_id));
				}
				else{
					FORTUP(id = (Node), id_list, ft1);
						gen_ks(I_DECLARE, kind_of(type_name), N_UNQ(id));
					ENDFORTUP(ft1);
				}
			}
			else {  /* Array or record */
				if (!local_reference_map_defined(type_name)
				  && is_constant (N_UNQ ((Node) set_arb (id_list)))
				  && S_SEGMENT(type_name) == -1) {
					/* deferred constant: type not elaborated yet */
					return;
				}
				if (init_node != OPT_NODE) {
					first_id = (Node) tup_fromb(id_list);
					first_name  = N_UNQ(first_id);
					if (is_aggregate(init_node)) {
						/*
						 * Create a static model containing the static part if
						 * there is one, then create a copy and initialize
						 * dynamic part in the copy. Note: the name of the
						 * aggregate is already first_name.
						 */
						/*stat_node=N_AST1(init_node); -- not used   ds 7-8-85*/
						dyn_node = N_AST2(N_AST1(init_node));
						/*nam_node=N_AST3(init_node); -- not used   ds 7-8-85*/
						model_name   = new_unique_name("static_");
						special_aggregate = FALSE;
						/* A special aggregate is an array aggregate whose
						 * unique name is not defined.  In this case we have
						 * to compile the initialization part of the
						 * aggregate first : the assignements refer to
						 * model_name 
						 * This situation occurs when we have an aggregate with
						 * a qualification that appears as an initiliazation of
						 * an object. Expand_decl cannot execute the code that
						 * deals with an aggregate. The qualification is
						 * removed by the expander and therefore the init part
						 * is just an aggregate. But the work in expand_decl
						 * has not be performed...
						 */
						if (is_array_type(type_name)) {
							if (!is_defined (N_UNQ (init_node))) {
								special_aggregate = TRUE;
								model_name   = N_UNQ (init_node); 
							}
							next_global_reference_template(model_name,
							  array_ivalue(init_node));
						}
						else {
							next_global_reference_template(model_name,
							  record_ivalue(init_node));
						}
						if (special_aggregate)
							compile(dyn_node); 
						gen_s(I_PUSH_EFFECTIVE_ADDRESS, model_name);
						gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
						gen(I_CREATE_COPY_STRUC);
						if (is_array_type(type_name))
							gen_ks(I_DISCARD_ADDR, 1, type_name);
						gen_s(I_UPDATE_AND_DISCARD, first_name);
						if (! special_aggregate)
							compile(dyn_node);
					}
					else {
						gen_structured_object(init_node, type_name,
						  obj_is_constant);
						if (is_array_type(type_name))
							gen_ks(I_DISCARD_ADDR, 1, type_name);
						gen_s(I_UPDATE_AND_DISCARD, first_name);
					}

					if (tup_size(id_list)) {
						gen_s(I_PUSH_EFFECTIVE_ADDRESS, first_name);
						FORTUP(id = (Node), id_list, ft1);
							gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
							gen(I_CREATE_COPY_STRUC);
							if (is_array_type(type_name)) /* remove type */
								gen_ks(I_DISCARD_ADDR, 1, type_name);
							gen_s(I_UPDATE, N_UNQ(id));
						ENDFORTUP(ft1);
						gen_ks(I_DISCARD_ADDR, 1, 
						  N_UNQ((Node) id_list[tup_size(id_list)]));
					}
				}
				else if (init_call_node != OPT_NODE ) {
					gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
					first_id = (Node) tup_fromb(id_list);
					first_name  = N_UNQ(first_id);
					gen(I_CREATE_STRUC);
					if (is_array_type(type_name))
						gen_ks(I_DISCARD_ADDR, 1, type_name);
					gen_s(I_UPDATE_AND_DISCARD, first_name);
					compile(init_call_node);  /* First object now initialized */

					if (tup_size(id_list)) {
						gen_s(I_PUSH_EFFECTIVE_ADDRESS, first_name);
						FORTUP(id = (Node), id_list, ft1);
							gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
							gen(I_CREATE_COPY_STRUC);
							if (is_array_type(type_name)) /* remove type */
								gen_ks(I_DISCARD_ADDR, 1, type_name);
							gen_s(I_UPDATE, N_UNQ(id));
						ENDFORTUP(ft1);
						gen_ks(I_DISCARD_ADDR, 1,
						  N_UNQ((Node)id_list[tup_size(id_list)]));
					}
				}
				else { /* Absolutely no initialization */
					gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
					last_id = (Node) tup_frome(id_list);
					FORTUP(id = (Node), id_list, ft1);
						obj_name = N_UNQ(id);
						gen_k(I_DUPLICATE, mu_addr);
						gen(I_CREATE_STRUC);
						if (is_array_type(type_name))
							gen_ks(I_DISCARD_ADDR, 1, type_name);
						gen_s(I_UPDATE_AND_DISCARD, obj_name);
					ENDFORTUP(ft1);
					obj_name = N_UNQ(last_id);
					gen(I_CREATE_STRUC);
					if (is_array_type(type_name))
						gen_ks(I_DISCARD_ADDR, 1, type_name);
					gen_s(I_UPDATE_AND_DISCARD, obj_name);
				}
			}
		}
		/* 2- Size of object is not known statically
		 * -----------------------------------------
		 * Also some pathological cases where size of initial value is not known
		 * although size of object is known: V: constrained_type := (F..G => 0);
		 * No use in optimizing that case: Only JBG can write that.
		 */
	}
	else if (obj_is_global) {
		/*    2a- Global object
		 *          Variable size => transformed into renaming
		 *          If initialization, initialize first object and then create
		 *          copies.
		 */
		if (init_node != OPT_NODE) { /* Explicit initialization */
			first_id = (Node) tup_fromb(id_list);
			obj_name = N_UNQ(first_id);
			next_global_reference_z(obj_name);
#ifdef TBSL
			ALIAS(obj_name) = new_unique_name("dyn_global"); /*not used */
#endif
			gen_structured_object(init_node, type_name, obj_is_constant);
			if (is_array_type(type_name) && is_unconstrained(type_name)) {
				/*       Completely dynamic unconstrained constant.
				 *	      Ex: X: constant STRING := F(..) & V;
				 */
				subtype = new_unique_name("typeof_");
				next_global_reference_z(subtype);

				/* Note: no index type list can be given... */
				tup = tup_new(2);
				tup[1] = (char *) tup_new1((char *) symbol_none);
				tup[2] = (char *) COMPONENT_TYPE(type_name);
				new_symbol(subtype, na_subtype, type_name,
				  tup, root_type(type_name));
				TYPE_OF(obj_name) = subtype;
				type_name         = subtype;     /* To be used by other obj. */
				gen_ks(I_POP, mu_addr, subtype);
				gen_ks(I_PUSH, mu_addr, subtype);
			}
			if (is_record_type(type_name)) {
				/* May be useless, but the peep-hole will take care of it */
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
			}

			FORTUP(id = (Node), id_list, ft1);
				gen_k(I_DUPLICATE, mu_dble);
				gen(I_CREATE_COPY_STRUC);
				if (is_array_type(type_name))
					gen_ks(I_DISCARD_ADDR, 1, type_name);
				gen_ks(I_POP, mu_addr, obj_name);
				first_id         = id;
				obj_name         = N_UNQ(first_id);
				TYPE_OF(obj_name) = type_name;    /* May have been changed. */
#ifdef TBSL
				ALIAS (obj_name) = new_unique_name("dyn_global"); /*not used */
#endif
			ENDFORTUP(ft1);
			gen_ks(I_DISCARD_ADDR, 1, type_name);
			gen_ks(I_POP, mu_addr, obj_name);
		}
		else if (init_call_node != OPT_NODE) { /* Implicit initialization */
			first_id = (Node) tup_fromb(id_list);
			first_name   = N_UNQ(first_id);
			next_global_reference_z(first_name);
#ifdef TBSL
			ALIAS(first_name) = new_unique_name("dyn_global"); /*not used */
#endif
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
			gen(I_CREATE_STRUC);
			gen_ks(I_POP, mu_addr, first_name);
			compile(init_call_node);      /* first object now initialized */

			FORTUP(id = (Node), id_list, ft1);
				obj_name = N_UNQ(id);
				next_global_reference_z(obj_name);
				gen_ks(I_PUSH, mu_addr, first_name);
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
				gen(I_CREATE_COPY_STRUC);
				if (is_array_type(type_name))
					gen_ks(I_DISCARD_ADDR, 1, type_name);
				gen_ks(I_POP, mu_addr, obj_name);
#ifdef TBSL
				ALIAS(obj_name) = new_unique_name("dyn_global"); /*not used */
#endif
			ENDFORTUP(ft1);
		}
		else { /* No initialization */
			last_id = (Node) tup_frome(id_list);
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
			FORTUP(id = (Node), id_list, ft1);
				obj_name = N_UNQ(id);
				next_global_reference_z(obj_name);
				gen_k(I_DUPLICATE, mu_addr);
				gen(I_CREATE_STRUC);
				gen_ks(I_POP, mu_addr, obj_name);
#ifdef TBSL
				ALIAS(obj_name) = new_unique_name("dyn_global"); /*not used */
#endif
			ENDFORTUP(ft1);
			obj_name = N_UNQ(last_id);
			next_global_reference_z(obj_name);
			gen(I_CREATE_STRUC);
			gen_ks(I_POP, mu_addr, obj_name);
#ifdef TBSL
			ALIAS(obj_name) = new_unique_name("dyn_global"); /*not used */
#endif
		}
	}
	else {
		/*    2b- Local array or record, variable size
		 *          Create local reference and object.
		 *      TBSL optimization
		 */
		FORTUP(id = (Node), id_list, ft1);
			obj_name = N_UNQ(id);
			next_local_reference(obj_name);
			if (init_node != OPT_NODE) {
				gen_structured_object(init_node, type_name, obj_is_constant);
				if (is_array_type(type_name) && is_unconstrained(type_name)) {
					/*
					 *         Completely dynamic unconstrained constant.
					 *	       Ex: X: constant STRING := F(..) & V;
					 */
					subtype = new_unique_name("typeof_");
					next_local_reference(subtype);

					/*  Note: no index type list can be given...  */

					tup = tup_new(2);
					tup[1] = (char *) tup_new1((char *) symbol_none);

					tup[2] = (char *) COMPONENT_TYPE(type_name);
					new_symbol(subtype, na_subtype, type_name,
				      tup, root_type(type_name));
					TYPE_SIZE(subtype) = -1;
					TYPE_OF(obj_name)  = subtype;
					gen_s(I_UPDATE, subtype);
					type_name = subtype;
				}
			}
			else {
				gen_s(I_PUSH_EFFECTIVE_ADDRESS, type_name);
				gen(I_CREATE_STRUC);
			}
			if (is_array_type(type_name))
				gen_ks(I_DISCARD_ADDR, 1, type_name);
			gen_s(I_UPDATE_AND_DISCARD, obj_name);
			if (init_call_node != OPT_NODE) {
				compile(init_call_node);
				/*  This first object will now serve as initial value for
				 *    other objects
				 */
				init_node      = id;
				init_call_node = OPT_NODE;
			}
		ENDFORTUP(ft1);
	}

}

static void gen_structured_object(Node init_node, Symbol type_name,
  int obj_is_constant)							 /*;gen_structured_object*/
{
	/*
	 * This procedure is used in place of GEN_VALUE when it is necessary to
	 * generate a new object, i.e. making a copy in cases where GEN_VALUE may
	 * generate the address of an already existing object.
	 */

	Node	expr_node;
	Symbol	expr_type;
	int		needs_copy, constrained_obj, val_is_constant, constrained_val;

	expr_node = init_node;
	expr_type = get_type(init_node);

	while (N_KIND(expr_node) == as_qual_discr
	  ||   N_KIND(expr_node) == as_qual_index
	  ||   N_KIND(expr_node) == as_qual_sub) {
		expr_node = N_AST1(expr_node);
	}
	needs_copy = is_object(expr_node) | is_ivalue(expr_node);

	gen_value(init_node);

	if (needs_copy) {
		if (is_record_type(expr_type))
			gen_s(I_PUSH_EFFECTIVE_ADDRESS, expr_type);
		gen(I_CREATE_COPY_STRUC);
	}
	if (is_record_type(type_name) ) {/* May need to adjust constrained */
		constrained_obj = ! is_unconstrained(type_name) || obj_is_constant;
		val_is_constant = is_simple_name(expr_node) &&
		  (NATURE(N_UNQ(expr_node)) == na_constant);
		constrained_val = ! is_unconstrained(expr_type) || val_is_constant;
		if (constrained_obj != constrained_val) {
			gen_k(I_DUPLICATE, mu_addr);
			gen_kic(I_PUSH_IMMEDIATE, kind_of(symbol_boolean), 
			  constrained_obj, "constrained bit");
			gen_k(I_MOVE, kind_of(symbol_boolean));
		}
	}
}
