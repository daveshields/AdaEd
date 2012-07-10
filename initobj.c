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
#include "attr.h"
#include "setprots.h"
#include "gutilprots.h"
#include "gmiscprots.h"
#include "smiscprots.h"
#include "gnodesprots.h"
#include "initobjprots.h"

static Tuple proc_init_rec(Symbol, Tuple, Node, Node);
static Node initialization_proc(Symbol, Symbol, Tuple, Tuple);
static Tuple build_comp_names(Node);
static Node remove_discr_ref(Node, Node);

Node build_proc_init_ara(Symbol type_name)				/*;build_proc_init_ara*/
{
	/*
	 *  This is the   main procedure for  building default  initialization
	 *  procedures for array  types. Those  initialization  procedures are
	 *  built if  the type  given  contains  some subcomponent for which a
	 *  default initialization exists (at any level of nesting),  or if it
	 *  has determinants.
	 *  Note that scalar objects are not initialized at all, which implies
	 *  that they get whatever initial value is in that location in memory
	 *  This saves some time in object creation.
	 *
	 *  All init. procedures  have an 'out' parameter that  designates the
	 *  object being initialized (the space has already been allocated).
	 *
	 */

	int		side_effect;
	Tuple	tup, formals, subscripts;
	Symbol	c_type, ip, index_t, proc_name, index_sym;
	Node	one_component, init_stmt, out_param, i_nodes, d_node, iter_node;
	Fortup	ft1;
	Node	iterator, index_node;

#ifdef TRACE
	if (debug_flag) {
		gen_trace_symbol("BUILD_PROC_INIT_ARR", type_name);
	}
#endif

	side_effect = FALSE;	 /* Let's hope... TBSL */

	tup = SIGNATURE(type_name);
	c_type    = (Symbol) tup[2];
	one_component = new_node(as_index);

	ip = INIT_PROC(base_type(c_type));
	if (ip != (Symbol)0 ){
		/* Use the initialization procedure for the component type */
		init_stmt = (Node) build_init_call(one_component, ip, c_type, OPT_NODE);
	}
	else if (is_task_type(c_type)) {
		/* initialization is task creation. */
		init_stmt =
		  new_assign_node(one_component, new_create_task_node(c_type));
	}
	else if (is_access_type(c_type)) {
		/* default value is the null pointer. */
		init_stmt = new_assign_node(one_component, new_null_node(c_type));
	}
	else {
		init_stmt = (Node) 0;
	}

	if (init_stmt != (Node)0) {
		/* body of initialization procedure is a loop over the indices */
		/* allocating each component. Generate loop variables and code */
		/* for iteration, using the attributes of the type. */

		proc_name = new_unique_name("type_name+INIT");
		out_param = new_param_node("param_type_name", proc_name,
		   type_name, na_out);
		generate_object(N_UNQ(out_param));
		formals               = tup_new1((char *) out_param);
		subscripts            = tup_new(0);
		FORTUP(index_t=(Symbol), index_types(type_name), ft1);
			/*index          = index_t + 'INDEX';*/
			index_sym          = new_unique_name("index_t+INDEX");
			NATURE (index_sym) = na_obj;
			TYPE_OF(index_sym) = index_t;
			subscripts = tup_with(subscripts, (char *)new_name_node(index_sym));
		ENDFORTUP(ft1);

		i_nodes         = new_node(as_list);
		/* need tup_copy since subscripts used destructively below */
		N_LIST(i_nodes) = tup_copy(subscripts);

		/* Build the tree for the one_component of the array. */
		N_AST1(one_component) = out_param;
		N_AST2(one_component) = i_nodes;
		N_TYPE(one_component) = c_type;

		while (tup_size(subscripts)) {
			/* Build loop from innermost index outwards. The iterations */
			/* span the ranges of the array being initialized. */

			/* dimension spanned by this loop: */
			d_node   = new_ivalue_node(int_const(tup_size(subscripts)), 
			  symbol_integer);
			iterator = new_attribute_node(ATTR_O_RANGE,
			  new_name_node(N_UNQ(out_param)), d_node, type_name);

			index_node = (Node) tup_frome(subscripts);
			iter_node        = new_node(as_for);
			N_AST1(iter_node) = index_node;
			N_AST2(iter_node) = iterator;

			init_stmt = new_loop_node(OPT_NODE, iter_node, 
			  tup_new1((char *)init_stmt));
		}

		INIT_PROC(type_name) = proc_name;
		return initialization_proc(proc_name, type_name,
		  formals, tup_new1((char *) init_stmt));
	}
	else {
		return OPT_NODE;
	}

}

Node build_proc_init_rec(Symbol type_name)				/*;build_proc_init_rec*/
{
	/*
	 *  This is the   main procedure for  building default  initialization
	 *  procedures for record  types. Those initialization  procedures are
	 *  built if  the type  given  contains  some subcomponent for which a
	 *  default initialization exists (at any level of nesting),  or if it
	 *  has determinants.
	 *  Note that scalar objects are not initialized at all, which implies
	 *  that they get whatever initial value is in that location in memory
	 *  This saves some time in object creation.
	 *
	 *  All init. procedures  have an 'out' parameter that  designates the
	 *  object begin initialized (the space has already been allocated).
	 *
	 */

	int		side_effect;
	Node	invar_node; /* TBSL: is invar_node local??*/
	Tuple	stmts, tup, nstmts, formals, invariant_fields;
	Tuple	discr_list; /* is this local ?? TBSL */
	Fortup	ft1;
	Symbol	d, proc_name;
	Node	param, var_node, out_param;

	Node	node, node1, node2, discr_value_node;
#ifdef TRACE
	if (debug_flag)
		gen_trace_symbol("BUILD_PROC_INIT_REC", type_name);
#endif

	side_effect = FALSE;	 /* Let's hope... TBSL */

	/*
	 * The initialization procedure for records has the usual out param.,
	 * and one in parameter per discriminant. The CONSTRAINED flag is the
	 * first of the discriminants
	 */
	proc_name = new_unique_name("Init_ type_name");
	out_param = new_param_node("param_type_name", proc_name, type_name, na_out);
	generate_object(proc_name);
	generate_object(N_UNQ(out_param));
	tup = SIGNATURE(type_name);
	invar_node = (Node) tup[1];
	var_node = (Node) tup[2];
	discr_list = (Tuple) tup[3];
	invariant_fields = build_comp_names(invar_node);

	stmts = tup_new(0);
	if (tup_size(discr_list)) {
		/* Generate formal parameters for each. The body of the procedure */
		/* assigns them to the field of the object. */
		/* Note: the 'constrained' field is part of the discriminants. */

		formals = tup_new(0);
		FORTUP(d=(Symbol), discr_list, ft1);
			param = new_param_node("param_type_name", proc_name, TYPE_OF(d),
			  na_in);
			generate_object(N_UNQ(param));
			formals = tup_with(formals, (char *) param );
			stmts = tup_with(stmts,
			  (char *) new_assign_node(new_selector_node(out_param, d), param));
			discr_value_node = new_selector_node (out_param, d);

			/* generate code in order to test if the value of discriminant is
			 * compatible with its subtype
			 */

			node1 = new_attribute_node(ATTR_T_FIRST, new_name_node(TYPE_OF(d)),
			  OPT_NODE, TYPE_OF(d));
			node2 = new_attribute_node(ATTR_T_LAST, new_name_node(TYPE_OF(d)),
			  OPT_NODE, TYPE_OF(d));
			node = node_new (as_list);
			make_if_node(node,
			  tup_new1((char *) new_cond_stmts_node( new_binop_node(symbol_or,
		 	    new_binop_node(symbol_lt, discr_value_node, node1,
				 symbol_boolean),
			    new_binop_node(symbol_gt, discr_value_node, node2,
				 symbol_boolean),
			    symbol_boolean),
			    new_raise_node(symbol_constraint_error))), OPT_NODE);
			stmts = tup_with(stmts, (char *) node);
		ENDFORTUP(ft1);
		formals = tup_with(formals, (char *) out_param );

		/* if there are default expressions for any other components, */
		/* further initialization steps are needed. */
		tup = proc_init_rec(type_name, invariant_fields, var_node, out_param);
		/*stmts += proc_init_rec(invariant_fields, var_node, out_param);*/
		nstmts = tup_add(stmts, tup);
		tup_free(stmts); 
		tup_free(tup); 
		stmts = nstmts;
	}
	else {
		/* record without discriminants. There may still be default values */
		/* for some components. */
		formals = tup_new1((char *) out_param);
		stmts   = proc_init_rec(type_name,invariant_fields,var_node, out_param);
	}
	if (tup_size(stmts)) {
		INIT_PROC(type_name) = proc_name;
		return initialization_proc(proc_name, type_name, formals, stmts);
	}
	else {
		return OPT_NODE;
	}
}

static Tuple proc_init_rec(Symbol type_name, Tuple field_names,
  Node variant_node, Node out_param)					/*;proc_init_rec*/
{
	/*
	 *  This is a subsidiary procedure to BUILD_PROC_INIT, which performs
	 *  the recursive part of construction of an initialization procedure
	 *  for a record type.
	 *
	 *  Input: field_names is a list of component unique names (excluding
	 *         discriminants. Variant node is the AST for the variant part
	 *         of a component list.
	 *	  variant_node is the variant part of the record declaration
	 *	  and has the same structure as a case statement.
	 *
	 *         out_param designates the object being initialized
	 *
	 *  Output: the statement list required to initialize this fragment of
	 *          the record, or [] if not default initialization is needed.
	 */

	Tuple	init_stmt, stmts;
	Node		one_component, f_init, c_node, variant_list;
	Symbol	f_type, f_name, ip;
	Fortup	ft1;
	int		empty_case;
	Tuple	case_list, comp_case_list;
	Node		choice_list, comp_list, disc_node;
	Node		invariant_node, new_case, list_node, case_node;

	Tuple	tup, index_list;
	int		nb_dim, i;
	Node		d_node,  node, node1, node2, node3, node4, node5;
	Symbol	one_index_type;

	/* process fixed part first. */
	init_stmt = tup_new(0);
	FORTUP(f_name=(Symbol), field_names, ft1);
		one_component    = new_selector_node(out_param, f_name);
		f_type           = TYPE_OF(f_name);
                CONTAINS_TASK(type_name) = (char *)
                  ((int)CONTAINS_TASK(type_name) | (int) CONTAINS_TASK(f_type));

		f_init = (Node) default_expr(f_name);
		if (f_init  != OPT_NODE) {
			init_stmt = tup_with(init_stmt,
			  (char *) new_assign_node(one_component,
			   remove_discr_ref(f_init, out_param)));
		}
		else if ((ip = INIT_PROC(base_type(f_type)))!=(Symbol)0) {
			init_stmt  = tup_with(init_stmt,
		      (char *) build_init_call(one_component, ip, f_type, out_param));
		}
		else if (is_task_type(f_type)) {
			init_stmt  = tup_with(init_stmt, (char *)
		      new_assign_node(one_component, new_create_task_node(f_type)));
		}
		else if (is_access_type(f_type)) {
			init_stmt  = tup_with(init_stmt, (char *)
		      new_assign_node(one_component, new_null_node(f_type)));
		}


		/* if we have an aray then we have to check if its bounds are
		 * compatible with the index subtypes (of the unconstrained array) 
		 * (This code was generated beforehand in type.c ("need_qual_r") but
		 * it was wrong : we have to test the bounds only if the field is
		 * present (case of variant record).
		 * The generation of the tests is easier here
		 */

		if (is_array_type (f_type)) {
			tup = (Tuple) SIGNATURE(TYPE_OF(f_type));
			index_list = tup_copy((Tuple) tup[1]);
			nb_dim = tup_size(index_list);

			for (i = 1; i <= nb_dim; i++) {
				one_index_type = (Symbol) (tup_fromb (index_list));

				d_node   = new_ivalue_node(int_const(i), symbol_integer);

				node1 = new_attribute_node(ATTR_O_FIRST,
			      one_component, d_node, one_index_type);

				node2 = new_attribute_node(ATTR_O_LAST,
			      one_component, d_node, one_index_type);

				node3 = new_attribute_node(ATTR_T_FIRST,
				  new_name_node(one_index_type), OPT_NODE, one_index_type);

				node4 = new_attribute_node(ATTR_T_LAST,
				  new_name_node(one_index_type), OPT_NODE, one_index_type);

				node5 = new_binop_node(symbol_or,
			      new_binop_node(symbol_lt, node1, node3, symbol_boolean),
			      new_binop_node(symbol_gt, node2, node4, symbol_boolean),
			      symbol_boolean);

				node = node_new (as_list);
				make_if_node(node,
			    tup_new1((char *) new_cond_stmts_node(
			      new_binop_node(symbol_and,
			      new_binop_node(symbol_le, node1, node2, symbol_boolean),
			      node5, symbol_boolean),
			      new_raise_node(symbol_constraint_error))), OPT_NODE);
				init_stmt  = tup_with(init_stmt, (char *) (node));
			}
		}
	ENDFORTUP(ft1);

	/* then build case statement to parallel structure of variant part. */

	empty_case = TRUE;    /* assumption */
	if (variant_node != OPT_NODE) {

		disc_node= N_AST1(variant_node);
		variant_list = N_AST2(variant_node);

		case_list = tup_new(0);

		comp_case_list = N_LIST(variant_list);

		FORTUP(c_node=(Node), comp_case_list, ft1);
			choice_list = N_AST1(c_node);
			comp_list = N_AST2(c_node);
			invariant_node = N_AST1(comp_list);
			variant_node = N_AST2(comp_list);

			field_names = build_comp_names(invariant_node);
			stmts = proc_init_rec(type_name,field_names,variant_node, out_param);

			/*empty_case and= stmts = [];*/
			empty_case = empty_case ? (tup_size(stmts)==0) : FALSE;
			new_case = (N_KIND(c_node) == as_others_choice) ?
			  new_node(as_others_choice) : new_node(as_variant_choices);
			N_AST1(new_case) = copy_tree(choice_list);
			N_AST2(new_case) = new_statements_node(stmts);
			case_list = tup_with(case_list, (char *)  new_case );
		ENDFORTUP(ft1);

		if (! empty_case) {
			/* Build a case statement ruled by the value of the discriminant */
			/* for this variant part. */

			list_node         = new_node(as_list);
			N_LIST(list_node) = case_list;
			case_node         = new_node(as_case);
			N_AST1(case_node)  = new_selector_node(out_param, N_UNQ(disc_node));
			N_AST2(case_node) = list_node;
			init_stmt    = tup_with(init_stmt, (char *) case_node );
		}
	}
	return init_stmt;
}

int is_discr_ref(Node expr_node)							/*;is_discr_ref*/
{
	int 	n, i, nk;
	Node	node;
	Tuple	tup;

	if (N_KIND(expr_node) == as_discr_ref)
		return TRUE;

	nk = N_KIND(expr_node);
	node = N_AST1(expr_node);
	if (node != (Node)0 && is_discr_ref(node)) return TRUE;
	node = N_AST2_DEFINED(nk) ? N_AST2(expr_node) : (Node) 0;
	if (node != (Node)0 && is_discr_ref(node)) return TRUE;
	node = N_AST3_DEFINED(nk) ? N_AST3(expr_node) : (Node) 0;
	if (node != (Node)0 && is_discr_ref(node)) return TRUE;
	node = N_AST4_DEFINED(nk) ? N_AST4(expr_node) : (Node) 0;
	if (node != (Node)0 && is_discr_ref(node)) return TRUE;
	tup = N_LIST_DEFINED(nk) ? N_LIST(expr_node) : (Tuple) 0;
	if (tup==(Tuple)0) return FALSE;
	n = tup_size(tup);
	for (i = 1; i <= n; i++)
		if (is_discr_ref((Node) tup[i])) return TRUE;
	return FALSE;
}

static Node remove_discr_ref(Node expr_node, Node object) /*;remove_discr_ref*/
{
	/* Within the record definition, a discriminant reference can be replaced
	 * by a selected component for the instance of the record being built.
	 */

	Node		e;
	int		i, nk;
	Tuple	tup;

	if (N_KIND(expr_node) == as_discr_ref)
		return new_selector_node(object, N_UNQ(expr_node));
	else if (N_KIND(expr_node) == as_opt)
		return OPT_NODE;
	else {
		e = copy_node(expr_node);
		nk = N_KIND(e);
		if (N_AST1_DEFINED(nk) && N_AST1(e)!=(Node)0)
			N_AST1(e) = remove_discr_ref(N_AST1(e), object);
		if (N_AST2_DEFINED(nk) && N_AST2(e)!=(Node)0)
			N_AST2(e) = remove_discr_ref(N_AST2(e), object);
		if (N_AST3_DEFINED(nk) && N_AST3(e)!=(Node)0)
			N_AST3(e) = remove_discr_ref(N_AST3(e), object);
		if (N_AST4_DEFINED(nk) && N_AST4(e)!=(Node)0)
			N_AST4(e) = remove_discr_ref(N_AST4(e), object);
	}
	/*N_LIST(e) = [remove_discr_ref(n, object): n in N_LIST(e)];*/
	if (N_LIST_DEFINED(nk) && N_LIST(e)!=(Tuple)0) {
		tup = N_LIST(e);
		for (i = 1; i <= tup_size(tup); i++)
			tup[i] = (char *) remove_discr_ref((Node) tup[i], object);
	}
	return e;
}

static Node initialization_proc(Symbol proc_name, Symbol type_name,
  Tuple formals, Tuple stmts)							/*;initialization_proc*/
{
	/* Build procedure with given formals and statement list. */

	Node	proc_node;

	int		i, n;
	Tuple	tup;
	NATURE   (proc_name)  = na_procedure;
	n = tup_size(formals);
	tup = tup_new(n);

	for (i = 1; i <= n; i++)
		tup[i] = (char *) N_UNQ((Node)formals[i]);
	SIGNATURE(proc_name)  = tup;
	generate_object(proc_name);

	/* 
     * Create as_subprogram_tr node with statements node as N_AST1 
     * instead of N_AST3 as it is with as_subprogram.
     */
	proc_node         = new_node(as_subprogram_tr);
	N_UNQ(proc_node) = proc_name;
	N_AST1(proc_node)  = new_statements_node(stmts);
	N_AST2(proc_node)  = OPT_NODE;
	N_AST4(proc_node)  = OPT_NODE;

	return proc_node;
}

Node build_init_call(Node one_component, Symbol proc_name, Symbol c_type,
  Node object)												/*;build_init_call*/
{
	/*
	 * Construct statement to initialize an object component for which
	 * an initialization procedure exists. The statement is a call to that
	 * procedure.
	 * c_type is the (composite) type of the component.
	 * If this is a record type whose discriminants have default values,
	 * use these defaults as parameters of the initialization procedure.
	 *
	 * If it is a subtype, use  the discriminant  values  elaborated for
	 * the subtype template.
	 *
	 * In the case of record component that is a record subtype, the const-
	 * raint may be given by a discriminant of the outer record. Such const-
	 * raints can only be evaluated when the outer object itself is being
	 * elaborated. In  that case  the  value of discriminant is rewritten as
	 * a selected  component of the enclosing object.
	 *
	 * The constrained bit is treated like other discriminants. Its value is
	 * FALSE for a record type, TRUE for a record subtype.
	 *
	 * If this is an array type, the procedure has one_component as its
	 * single actual.
	 */

	Tuple	disc_vals, tup, discr_map, arg_list;
	Fortup	ft1;
	Symbol	d;
	Node	node, p_node, args_node, d_val, d_val_new;
	int		i, n;

#ifdef TRACE
	if (debug_flag)
		gen_trace_symbol("BUILD_INIT_CALL", proc_name);
#endif

	if (is_record_type(c_type)) {
		if (is_record_subtype(c_type)) {
			/* examine constraint of subtype. */
			disc_vals = tup_new(0);
			tup = SIGNATURE(c_type);
			discr_map = (Tuple) tup[2];

			FORTUP(d=(Symbol), discriminant_list_get(c_type), ft1);
				d_val = discr_map_get(discr_map, d);
				if (is_discr_ref(d_val) ) {
					/* depends on determinant of outer object */
					d_val_new = remove_discr_ref(d_val, object);
				}
				else if (is_ivalue(d_val) ) {
					/* useless to retrieve from subtype here */
					d_val_new = d_val;
				}
				else {
					/* elaborated: retrieve from subtype. */
					d_val_new = new_discr_ref_node(d, c_type);
				}
				disc_vals = tup_with(disc_vals, (char *) d_val_new);
			ENDFORTUP(ft1);
		}
		else {
			/* Use default values to initialize discriminants. */
			tup = discriminant_list_get(c_type);
			n = tup_size(tup);
			disc_vals = tup_new(n);
			for (i = 1; i <= n; i++)
				disc_vals[i] = (char *) default_expr((Symbol) tup[i]);
		}
		arg_list = disc_vals;/* last use of disc_vals so no need to copy*/
		arg_list = tup_with(arg_list, (char *) one_component);
	}
	else {
		arg_list = tup_new1((char *) one_component);
	}

	/* Build call to initialization procedure. */
	node              = new_node(as_init_call);
	p_node            = new_name_node(proc_name);
	args_node         = new_node(as_list);
	N_LIST(args_node) = arg_list;
	N_AST1(node)       = p_node;
	N_AST2(node)       = args_node;
	N_SIDE(node)      = FALSE;
	return node;
}

static Tuple build_comp_names(Node invariant_node)		/*;build_comp_names*/
{
	/* Collect names of record components in the invariant part of the
	 * record. Skip nodes generated for internal anonymous subtypes.
	 */

	Tuple	all_component_names;
	Node	node, id_list_node, id_node;
	Fortup	ft1, ft2;

	all_component_names = tup_new(0);
	FORTUP(node=(Node), N_LIST(invariant_node), ft1);
		if(N_KIND(node) ==as_subtype_decl || N_KIND(node)==as_deleted)
			continue;
		id_list_node= N_AST1(node);
		FORTUP(id_node=(Node), N_LIST(id_list_node), ft2);
			all_component_names  = tup_with(all_component_names,
	    	  (char *) N_UNQ(id_node));
		ENDFORTUP(ft2);
	ENDFORTUP(ft1);
	return all_component_names;
}
