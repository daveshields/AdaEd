/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* chapter 12, part c */
#include "hdr.h"
#include "vars.h"
#include "attr.h"
#include "dbxprots.h"
#include "dclmapprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "setprots.h"
#include "nodesprots.h"
#include "errmsgprots.h"
#include "chapprots.h"

/* ctype.h needed by desig_to_op */
#include <ctype.h>

static Tuple instantiation_code;		/* code from instantiation */
static int instantiation_code_n = 0;	/* current length */

static Node instantiate_object(Node, Symbol, Symbolmap);
static int can_rename(Node);
static Tuple flatten_tree(Node);
static int is_discr_ref(Node, Tuple);
static Symbol instantiate_type(Node, Symbol, Symbolmap);
static Symbol valid_type_instance(Symbol, Symbol, Symbolmap);
static Symbol valid_scalar_instance(Symbol, Symbol, Symbolmap);
static void check_actual_constraint(Symbol, Symbol);
static Symbol valid_priv_instance(Symbol, Symbol, Symbolmap);
static Symbol valid_access_instance(Symbol, Symbol, Symbolmap);
static Symbol valid_array_instance(Symbol, Symbol, Symbolmap);
static int is_valid_disc_instance(Symbol, Symbol, Symbolmap);
static Tuple get_array_info(Symbol);
static void generic_subprog_instance(Node, Symbol, Symbolmap, int);
static Tuple find_renamed_types(int, Tuple, Symbol, Node);
static Node make_rename_node(Symbol, Node);
static void instantiation_code_with(Node);

/* number of slots to expand instantiation_code when full, initial alloc*/
#define INSTANTIATION_CODE_INC	50

Tuple instantiate_generics(Tuple gen_list, Node instance_node)
  /*;instantiate_generics*/
{
	/* Produce the list of renamings which transforms generic parameters
	 * into actual ones.
	 * Generic types play a special role in this renaming. We collect the
	 * Instantiations of generic types into the map	 -type_map-and use it
	 * in a substitution procedure to obtain the signature of generic
	 * subprogram arguments.
	 * Generic subprograms are also renamed by the actual subprograms, and
	 * the mapping from one to the other is also added to the same renaming
	 * map.
	 */

	Tuple	error_instance, empty_tuple, inst_code;
	Symbolmap	type_map, empty_typemap;
	Tuple	gtup;
	Tuple	instance, new_instance;
	int		i, j, k, gn, ni, seen, same_formal_subprog;
	Node	assoc;
	int		first_named, exists, is_default;
	Symbol	g_name, name, over;
	Node	actual;
	Symbol	actual_type;
	Node	init_node;
	Node	id_node;
	Tuple	tup;
	int		nat;
	Fortup	ft1;
	Forset  fs1;

	if( cdebug2 > 3) TO_ERRFILE("AT PROC :  instantiate_generics ");

	/*    const error_instance = [ [], {} ];		$$ES7 */
	instantiation_code = tup_new(0);
	instantiation_code_n = 0;
	type_map = symbolmap_new();
	empty_tuple = tup_new(0);
	empty_typemap = symbolmap_new();
	error_instance = tup_new2((char *) empty_tuple, (char *) empty_typemap);
	instance = N_LIST(instance_node);

	if (tup_size( instance) > tup_size( gen_list)){
		errmsg("Too many actuals in generic instantiation", "12.3", instance_node);
	}

	/* Values may be supplied either positionally or by name.  */
	exists = FALSE;
	FORTUPI(assoc=(Node), instance, i, ft1);
		if (N_AST1(assoc) != OPT_NODE){
			exists = TRUE;
			break;
		}
	ENDFORTUP(ft1);
	if (exists) {
		first_named = i;
		exists = FALSE;
		for (k=i; k <= tup_size(instance); k++) {
			if (N_AST1((Node)instance[k]) == OPT_NODE){
				exists = TRUE;
				break;
			}
		}
		if (exists) {
			errmsg("Positional association after named one", "12.3",
			  (Node)instance[k]);
			return error_instance;
		}
	}
	else
		first_named = tup_size(instance) + 1;
	seen = first_named - 1;
	new_instance = tup_new(0);
	for (i = 1; i <= seen; i++) {
		actual = N_AST2((Node)instance[i]);
		new_instance = tup_with(new_instance, (char *) actual);
	}

	/* Collect named instances in the proper order.*/
	gn = tup_size(gen_list);
	for (i=first_named; i <= gn; i++) {
		gtup = (Tuple) gen_list[i];
		g_name = (Symbol) gtup[1];
		init_node = (Node) gtup[2];
		exists = FALSE;
		ni = tup_size(instance);
		for (j=first_named; j <= ni; j++) {
			id_node = N_AST1((Node) instance[j]);
			if (id_node == OPT_NODE) continue;
			if (streq(N_VAL(id_node), ORIG_NAME(g_name))) {
				exists = TRUE;
				break;
			}
		}
		if (exists) {
			actual = N_AST2((Node) instance[j]);
			new_instance = tup_with(new_instance, (char *) actual);
			seen += 1;

			if (NATURE(g_name) == na_procedure || 
			    NATURE(g_name) == na_function) {
			   name = dcl_get(DECLARED(SCOPE_OF(g_name)), N_VAL(id_node));
                        /*
                         * We must distinguish between generic formal
                         * subprogram and those defined in the generic spec.
                         * We perform the check only on those defined in the
                         * generic spec (i.e. those that have their ALIAS 
                         * field defined.
                         */
			   same_formal_subprog = 0;
			   FORSET(over = (Symbol), OVERLOADS(name), fs1);
			      if (ALIAS(over)!=(Symbol)0) same_formal_subprog++;
			   ENDFORSET(fs1);
			   if (same_formal_subprog > 1) 
			       errmsg("named associations not allowed for overloaded names",
				      "12.3(3)", id_node);
			}
			/* Otherwise a default must exist for this generic parameter.*/
			/* Mark the place for use below.*/
		}
		else if (init_node != OPT_NODE ) 
			new_instance = tup_with(new_instance, (char *) OPT_NODE);
		else {
			errmsg_id("Missing instantiation for generic parameter %" ,
			  g_name, "12.3", current_node);
			return error_instance;
		}
	}
#ifdef TBSN
	if (cdebug2 > 0){
		TO_ERRFILE('new instance ' + str new_instance);
	}
#endif
	/* Now process all actuals in succession. */
	gn = tup_size(gen_list);
	for (i = 1; i <= gn; i++) {
		gtup= (Tuple) gen_list[i];
		g_name = (Symbol) gtup[1];
		init_node = (Node) gtup[2];
		actual = (Node) new_instance[i];

		if (actual != OPT_NODE ) {
			adasem(actual);
			if (NATURE(g_name) == na_in) {
				/* type check expression for in parameter. */
				actual_type = replace(TYPE_OF(g_name), type_map);
				check_type(actual_type, actual);
			}
			else if (NATURE(g_name)== na_procedure
			  || NATURE(g_name)== na_function) {
				/* Actual may be given by an operator symbol, which appear  */
				/*  as string literal. */
				is_default = FALSE;
				if (N_KIND(actual) == as_string_literal)
					desig_to_op(actual);
				find_old(actual);
			}
		}
		else {
			/* Use default value given.*/
			actual = init_node;
			if (NATURE(g_name) == na_in )
				/* May depend on generic types: replace by their instances.*/
				actual = instantiate_tree(init_node, type_map);
			else	{		/* generic subprogram parameter */
				/* If the box was used to specify a default subprogram, we
				 * retrieve the visible instances of the generic identifier.
				 */
				is_default = TRUE;
				if (N_KIND(actual) == as_simple_name
				  && streq(N_VAL(actual), "box")) {
					actual = node_new(as_simple_name);
					N_VAL(actual) = original_name(g_name);
					copy_span(instance_node, actual);
					find_old(actual);
					is_default = FALSE;
				}
				else if (N_KIND(actual) == as_attribute)
					/* Will depend on generic types. Must instantiate. */
					actual = instantiate_tree(init_node, type_map);
			}
		}
		nat = NATURE(g_name);
		if (nat == na_in || nat == na_inout)
			/* TBSL: see if instantiation_code might be large in which case
			 * may want to avoid too many tup_with calls
			 */
			instantiation_code_with(
			  instantiate_object(actual, g_name, type_map));
		else if (nat == na_procedure || nat == na_function)
			generic_subprog_instance(actual, g_name, type_map, is_default);
		else {			/* generic type. */
			actual_type = instantiate_type(actual, g_name, type_map);
			if (actual_type == (Symbol)0)
				return error_instance;
			else {
				symbolmap_put(type_map, g_name, actual_type);
				if (is_scalar_type(g_name))
					/* indicate the instantiation of its base type as well. */
					symbolmap_put(type_map, TYPE_OF(g_name),
					  base_type(actual_type));
			}
		}
	}
	if (seen != tup_size(instance)) {
		/* Not all named associations were processed.*/
		errmsg("duplicate or erroneous named associations in instantiation",
		  "12.3", current_node);
	}

	if (cdebug2 > 0 ) TO_ERRFILE("Type map: ");
	/* Attach newly created declarative nodes to the instance node itself
	 * so that AST tree remains connected (separate compilation need).
	 * TBSL: check whether this trick is still necessary now that the node
	 * stack (in save_tree) is initialized with all nodes in unit_nodes
	 */
	inst_code = tup_new(instantiation_code_n);
	for (i = 1; i <= instantiation_code_n; i++)
		inst_code[i] = instantiation_code[i];
	N_LIST(instance_node) = tup_add(N_LIST(instance_node), inst_code);
	tup = tup_new(2);
	/* TBSL: is tup_copy needed below since i...code also include in N_LIST*/
	tup[1]= (char *) inst_code;
	tup[2] = (char *) type_map;
	return tup;
}

void desig_to_op(Node node)			/*;desig_to_op*/
{
	/* a designator appears syntactically as a string literal. Verify that it
	 * does designate a valid operator symbol.
	 */

	char	*op_name, *p;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  desig_to_op");

	N_KIND(node) = as_simple_name;
	/*op_name := +/[to_lower(c) ? c : c in N_VAL(node)];*/
	op_name = strjoin(N_VAL(node), ""); /* copy operator name */
	for (p = op_name; *p; p++)  /* fold name to lower case*/
		if (isupper(*p)) *p = tolower(*p);
	if (in_op_designators(op_name))
		N_VAL(node) = (char *) op_name;
	else {
		errmsg_str("% is not an operator designator", op_name, "4.5", node);
		N_VAL(node) = string_any_id; /* "any_id" */
	}
}

static Node instantiate_object(Node actual_node, Symbol g_name,
  Symbolmap type_map)						/*;instantiate_object*/
{
	int		g_mode;
	Symbol	g_type, actual_type;
	Node	d, n, i, t;
	Symbol	actual_name;
	Tuple	tup;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : instantiate_object");

	/* Unpack information about generic parameter.*/
	g_mode = NATURE(g_name);
	g_type = TYPE_OF(g_name);

	actual_type = symbolmap_get(type_map, g_type);
	/* If generic. */
	if (actual_type == (Symbol)0) actual_type = g_type;
	/* Otherwise. */
	/* For each instantiation we must create locations for the generic
	 * parameters, and replace in the body of the object the generic ones
	 * with the actual ones.
	 */

#ifdef TBSN
	actual_name = prefix + original_name(g_name) + str newat;
#endif
	actual_name = sym_new(na_void);
	ORIG_NAME(actual_name) = ORIG_NAME(g_name);
	symbolmap_put(type_map, g_name, actual_name);

	if (g_mode == na_in) {
		/* Expression has already been type_checked*/
		if (is_deferred_constant(actual_node)) {
			errmsg_l("Instantiation of a generic in parameter cannot be a ",
			  " deferred constant", "7.4.3", actual_node);
			return OPT_NODE;
		}
		NATURE(actual_name) = na_constant;
		TYPE_OF(actual_name) = actual_type;
		SIGNATURE(actual_name) = (Tuple) actual_node;
		/* Build declaration tree for it.  */
		d = node_new(as_const_decl);
		n = node_new(as_list);
		i = node_new(as_simple_name);
		t = node_new(as_simple_name);
		N_UNQ(i) = actual_name;
		N_UNQ(t) = actual_type;
		N_LIST(n) = tup_new1((char *) i);
		N_AST1(d) = n;
		N_AST2(d) = t;
		N_AST3(d) = actual_node;
		return  d;
	}
	else {						/* in out parameter. */
		TYPE_OF(actual_name) = actual_type;
		SIGNATURE(actual_name) = (Tuple) OPT_NODE;
		if (N_KIND(actual_node) != as_name) {
			errmsg(
			  "Instantiation of generic in out parameter must be a variable",
			  "12.1.1, 12.3.1", actual_node);
			return OPT_NODE;
		}
		else {
			find_old(actual_node);
		}

		/*
		 * this next test may be superfluous, as is_variable() no longer
		 * allows conversions!
		 */
		if (N_KIND(actual_node) == as_convert) {
			errmsg_l("Instantiation of generic in out parameter ",
			  "cannot be a conversion", "12.3.1", actual_node);
			return OPT_NODE;
		}
		out_context = FALSE;

		check_type(base_type(actual_type), actual_node);
		tup = check_nat_type(actual_node);
		NATURE(actual_name) = (int) tup[1];
		SCOPE_OF(actual_name) = scope_name;

		/* actual_name carries the type of the actual, not the renamed formal.*/
		/* remove spurious constraint that may have been imposed by check_type*/

		if (in_qualifiers(N_KIND(actual_node)))
			actual_node = N_AST1(actual_node);
		if (N_KIND(actual_node) == as_simple_name)
			/* should deal with general name here. */
			TYPE_OF(actual_name) = TYPE_OF(N_UNQ(actual_node));

		if (!is_variable(actual_node)){
			errmsg_l("Instantiation of generic in out parameter ",
			  "must be a variable", "12.1.1, 12.3.1", actual_node);
			return OPT_NODE;
		}
		/*TBSL: SETL has is_dis(actual), substituting actual_node */
		else if ( ! can_rename( actual_node )) {
			errmsg_l_id(
			  "instantiation of generic in out parameter % depends on a ",
			  "discriminant", g_name, "12.3.1", actual_node);
			return OPT_NODE;
		}
		else {
			/* Build a renaming declaration for object.
			 * Possible optimization if actual is simple name (later).
			 */
			d = node_new(as_rename_obj);
			i = new_name_node(actual_name);
			N_AST1(d) = i;
			N_AST2(d) = OPT_NODE;
			N_AST3(d) = actual_node;
			return d;
		}
	}
}

static int can_rename(Node obj)						/*;can_rename */
{
	/* This procedure detects illegal  dependence on discriminants for renamed
	 * variables  and in out  generic parameters, as  defined  in 8.5(7).  The
	 * expression is  linearized  and subsequent retrievals examined to detect
	 * subcomponents whose existence depends on outer discriminants. The first
	 * retrieval is the only  one that can apply to an unconstrained variable.
	 */

	Tuple	seq, discrs, discr_map;
	Node	var_node, sel_node, first, node, lo, hi;
	Symbol	var_name, var_type, selector, comp_type, i;
	int	d, dsize;
	Fortup	ft;

	seq = (Tuple) flatten_tree(obj);
	if (tup_size(seq) == 0) return TRUE;
	first = (Node) seq[tup_size(seq)];

	var_node = N_AST1(first);
	sel_node = N_AST2(first);

	/* The first prefix is a simple name, an allocator, or a function call.
	 * We only consider simple names here.
	 */
	if (N_KIND(var_node) != as_simple_name ) return TRUE;

	var_name = N_UNQ(var_node);
	var_type = TYPE_OF(var_name);

	if ( can_constrain(var_type)) {
		/* Any dependence on its discriminants will be illegal.
		 * TBSL: a generic in out parameter.
		 */
		discrs = discriminant_list(var_type);
		if (is_formal(var_name) ) {
			FORTUP(i=(Symbol), discrs, ft)
			    if (default_expr(i) == (Tuple) OPT_NODE) {
					discrs = tup_new(0);
					break;
				}
			ENDFORTUP(ft);
		}
	}
	else
		discrs = tup_new(0);

	/* other dependence is if subtype indication of subcomponent
    * depends on discriminants of variable, or on discriminants of
    * inner constrainable components.
    */
	while (tup_size(seq) != 0) {
		node = (Node) tup_frome(seq);
		if (N_KIND(node) == as_selector) {
			sel_node = N_AST2(node);
			comp_type = TYPE_OF(N_UNQ(sel_node));
		}
		else
			/* other subcomponents cannot depend on discriminants */
			return TRUE;
		selector = N_UNQ(sel_node);
		if (tup_size(discrs) != 0 && !tup_mem((char *)selector,
		  build_comp_names((Node) invariant_part(var_type))))
			/* component is in variant part: illegal renaming. */
			return FALSE;
		if (is_array(comp_type)) {
			FORTUP(i=(Symbol), index_types(comp_type), ft)
			    lo = (Node) SIGNATURE(i)[2];
				hi = (Node) SIGNATURE(i)[3];
				if (is_discr_ref(lo, discrs) || is_discr_ref(hi, discrs))
					return FALSE;
			ENDFORTUP(ft);
		}
		else if (is_record(comp_type)) {
			if (NATURE(comp_type) == na_subtype) {
				discr_map = (Tuple) numeric_constraint_discr(
				  SIGNATURE(comp_type));
				/* if exists node in range discr_map |
	    		 *	is_discr_ref(node, discrs) then	 return false; end if;
	    		 */
				dsize = tup_size(discr_map);
				for (d = 1; d <= dsize; d += 2 ) {
					node = (Node) discr_map[d+1];
					if (is_discr_ref(node, discrs))
						return FALSE;
				}
				discrs = tup_new(0);
			}
			else	{
				discrs = discriminant_list(comp_type);
				var_type = comp_type;  /* for inner subcomponents */
			}
		}
		else return TRUE;		/* scalar component */
	}
	/* If we exit, no discriminant dependence was found. */
	return TRUE;
}

static Tuple flatten_tree(Node expn)				/*;flatten_tree */
{
	/* In order to determine whether a subcomponent depends on a discriminant,
	 * it is easiest  to simulate  in order	 the sequence of  retrievals  that
	 * yields that subcomponent. Only nodes that retrieve  components are kept.
	 */

	Node prefix;
	int kind;

	kind = N_KIND(expn);
	if (kind == as_selector ||kind == as_index || kind == as_slice) {
		prefix = N_AST1(expn);
		return (tup_add(tup_new1((char *)expn), flatten_tree(prefix)));
	}
	else
		return tup_new(0);
}

static int is_discr_ref(Node node, Tuple discrs)		/*;is_discr_ref */
{

	if (N_KIND(node) != as_discr_ref)
		return FALSE;
	else
		return tup_mem((char *) N_UNQ(node), discrs);
}

/* THIS IS OBSOLETE !!! */
int is_discriminant_dependent(Node  expn)  /*;is_discriminant_dependent*/
{
	/*   Function :
	 *	 this (non-recursive) procedure accepts as parameter an
	 *	 expression that has been parsed as a valid 'name', and
	 *	 return true if the existence of the object designated
	 *	 may depend on a discriminant. See LRM 8.5, 3.7.1, 12.3.1.
	 *   Usage :
	 *	 for generic in out parameter
	 *	 for renaming
	 */

/*  comment out for less warning messages from  CC
	Tuple	lexpn;
	Symbol	first;
	int		is_first_element;
	Symbol	current_type;
	Tuple	discr;
	Symbol	op_name, base_type_rec, field_name, name;
	Tuple	nam_list;
	Tuple	bounds;
	Symbol	i;
*/
	/* lo, hi, bound */

	if (cdebug2 > 3)
		TO_ERRFILE("AT PROC : is_discriminant_dependent ( + str expn + )");

	return	FALSE;	  /* $$$ FOR NOW */
	/*****************************************************/
	/*   the expression is first 'flattened' : */

	/* Ihave changed expn to lexpn as lexpn must be flattened */
#ifdef TBSN
	lexpn = linear(expn);
	first fromb lexpn;
	is_first_element =  TRUE;
	current_type = TYPE_OF( first );
	discr = tup_new(0);

	/*  the guess along that loop is that it is not dependent : */
	( while (lexpn?[]) /= [] )
	case op_name fromb lexpn of

		/*
 *  Record case : check that component is in fixed part
 *		  keep discriminants in case of array component
 */
		('.'):
base_type_rec :
		    = base_type ( current_type );
	field_name fromb lexpn;
*$ES147  field_name :
	= declared_components(base_type_rec)(field_name);
	if ((nature ( current_type ) == 'subtype') ||
	    /*
 *  if it is a formal parameter of some unconstrained type, the actual
 *  parameter must have been constrained...
 */
	(	    is_first_element
	    && is_formal ( first )
	    && is_unconstrained ( current_type ))){
discr :
		= discriminant_list ( base_type_rec );
else
	if (not exists
	    [ -, nam_list, - ] in invariant_part ( base_type_rec ) ,
	    name in nam_list | name = field_name ){
		return TRUE;
	}
discr :
= [];
	}
current_type :
	= type_of ( field_name );

	/*
 * Array or Slice case : if bound is dynamic, is must be constrained
 */
	('[]', '[..]'):
	*$ES147 (
bounds :
	    = [];
	    (for i in index_types(current_type))
[-, low, high] :
	    = signature (i);
bounds +:
	    = [low, high];
	    end for;
	    if( exists bound in bounds || is_tuple(bound)
	    && (bound(1) = 'discr_rep')  && (bound(2) notin discr)){
		return TRUE;
	}

	if (op_name == '[]'){
current_type :
		= component_type ( current_type );
	}

	*$ES147 )
	    /*
 * Access case : cannot depend on a discriminant !
 * Function call : idem
 */
	('@', 'call'):
	return	 FALSE;

	/*
 * Possible gap here
 */
else
	return	 FALSE;
end case;
is_first_element :
=  FALSE;

}

return  FALSE; /* $ the initial guess */

#endif
}

void linear(Symbol  expn ) /*;linear*/
{
/*  comment out for less warning messages from  CC
	Symbol	op_name;
	Symbol	exp1, exp2;
*/

	/*   Recursive function used by 'is_discriminant_dependent' to
	 *   flatten its argument. The grammar of interest for expn is :
	 *	 expn ::= identifier
	 *	       |  '.' rec_expr field_name
	 *	       |  '[]' arr_expr index
	 *	       |  '[..]' arr_expr slice
	 *	       |  '@' expr
	 *	       |  'call' identifier
	 */
	chaos("linear(12) not implemented");
#ifdef TBSN
	if (is_identifier ( expn ) ){
		return [ expn ];
	}
	else{
[ op_name, exp1, exp2 ] :
		= expn;
	case op_name of
		('.'):
		return linear(exp1)+[op_name]+linear(exp2);
		('[]', '[..]', '@', 'call'):
		return linear(exp1)+[op_name];
else
	return [];
end case;
	}
#endif
}

static Symbol instantiate_type(Node type_node, Symbol g_name,Symbolmap type_map)
  /*;instantiate_type*/
{
	/* Validate the	 instantiation of a generic  type. The	actual must be
	 * a type mark.
	 */

	Symbol	actual_type;
	int		nk;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  instantiate_type");

	nk = N_KIND(type_node);
	if (nk == as_name || nk == as_simple_name){
		find_type(type_node);
		actual_type = N_UNQ(type_node);
		if (actual_type == symbol_any)			    /* Not a type */
			return (Symbol)0;
		else 
			return valid_type_instance(g_name, actual_type, type_map);
	}
	else{
		errmsg_id("invalid expression for instantiation of %", g_name,
		  "12.3", current_node);
		return (Symbol)0;
	}
}

static Symbol valid_type_instance(Symbol g_name, Symbol actual_type,
  Symbolmap type_map)						/*;valid_type_instance*/
{
	if (is_scalar_type(g_name))
		return valid_scalar_instance(g_name, actual_type, type_map);
	else if (is_access(g_name))
		return valid_access_instance(g_name, actual_type, type_map);
	else if (is_array(g_name))
		return  valid_array_instance(g_name, actual_type, type_map);
	else
		return valid_priv_instance(g_name, actual_type, type_map);
}

static Symbol valid_scalar_instance(Symbol g_name, Symbol actual_type,
  Symbolmap type_map)						/*;valid_scalar_instance*/
{
	/* Complete the validation of the instantiation of a generic scalar type.
	 * This procedure is also used to emit constraint checks on access types
	 * and array types.
	 */

	Symbol	g_type;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : valid_scalar_instance");

	g_type = root_type(g_name); /*INTEGER, FLOAT, $FIXED, etc.*/
	if (g_type == root_type(actual_type) && is_generic_type(g_name))
		return actual_type;
	else if (base_type(g_type) == base_type(actual_type)){
		/* Checking instantiation of the designated type of an access type
    	 * or  index type of an  array type. Verify that constraints match.
    	 */
		check_actual_constraint(g_name, actual_type);
		return actual_type;
	}
	else if  ((is_fixed_type(g_type) && is_fixed_type(actual_type))
	  || (g_type == symbol_discrete_type  && is_discrete_type(actual_type)))
		return actual_type;
	else {
		errmsg_id("Invalid type for instantiation of %", g_name,
		  "12.3.2 - 12.3.5", current_node);
		return (Symbol)0;
	}
}

static void check_actual_constraint(Symbol g_type, Symbol a_type)
  /*;check_actual_constraint*/
{
	/* Verify that the constraint on the designated type of an access type,
	 * or an index type of an array type, match the constraints on the cor-
	 * responding formal generic type. The types are known to be compatible.
	 */

	Node	n, d, g, a, t;
	Tuple	g_discr_map, g_list, a_list;
	Symbol	discr;
	Tuple	g_info, a_info;
	int		i;
	Tuple	tup;
	Fortup	ft;

	if (is_scalar_type(g_type)){
		if (g_type == a_type) return;   /* simplest optimization. */
		n = node_new(as_check_bounds);
		g = new_name_node(g_type);
		a = new_name_node(a_type);
		N_AST1(n) = g;
		N_AST2(n) = a;
		instantiation_code_with(n);
	}
	else if (is_record(g_type)  && NATURE(g_type) == na_subtype){
		/* Check that discriminants match.  */
		if (NATURE(a_type) != na_subtype)
			/* Mismatch was already signalled.  */
			return;

		tup = SIGNATURE(g_type);
		/* Compare the values of each discriminant. */
		g_list = discriminant_list(base_type(g_type));
		a_list = discriminant_list(base_type(a_type));
		g_discr_map = (Tuple) SIGNATURE(g_type)[2];

		FORTUPI(discr=(Symbol), g_list, i, ft)
		    n = node_new(as_check_discr);
			t = new_name_node(a_type);
			d = new_name_node((Symbol) a_list[i]);
			N_AST1(n) = discr_map_get(g_discr_map, discr);
			N_AST2(n) = t;
			N_AST3(n) = d;
			instantiation_code_with(n);
		ENDFORTUP(ft);
	}
	else if (is_array(g_type)) {
		g_info = (Tuple) get_array_info(g_type);
		a_info = (Tuple) get_array_info(a_type);

		for (i = 1; i <= tup_size(g_info); i++)
			check_actual_constraint((Symbol) g_info[i], (Symbol) a_info[i]);
	}
	else if (is_access(g_type) )
		check_actual_constraint(designated_type(g_type),
		  designated_type(a_type));
}

static Symbol valid_priv_instance(Symbol g_name, Symbol actual_type,
  Symbolmap type_map)								/*;valid_priv_instance*/
{
	Symbol	g_type, actual_base;

	g_type = TYPE_OF(g_name);
	actual_base = base_type(actual_type);

	if (TYPE_OF(actual_base) == symbol_incomplete){
		errmsg_id("Invalid use of incomplete type in instantiation of %",
		  g_name, "12.3", current_node);
		return (Symbol)0;
	}
	else if (private_ancestor(actual_base) != (Symbol)0 ){
		errmsg_id("Invalid use of private type in instantiation of %" , g_name,
		  "12.3", current_node);
		return (Symbol)0;
	}
	else if (g_type == symbol_private && is_limited_type(actual_type)) {
		errmsg_id("Expect non-limited type to instantiate %" , g_name,
		  "12.3.2", current_node);
		return (Symbol)0;
	}
	else if (is_record(g_name) && has_discriminants(g_name)
	    /*TBSL: check precdeence of next expr */
	  && (!is_record(actual_base) || !has_discriminants(actual_base)
	  || !is_valid_disc_instance(g_name, actual_base, type_map))) {
		errmsg_id("discriminant mismatch in instantiation of %", g_name,
		  "12.3.2", current_node);
		return (Symbol)0;
	}
	else if (has_discriminants(g_name) && NATURE(actual_type) == na_subtype) {
		errmsg_id("Instantiation of % must be unconstrained", g_name,
		  "12.3.2", current_node);
		return (Symbol)0;
	}

	else if ((TA_CONSTRAIN & (int)misc_type_attributes(g_name))
	    /* The predefined packages cannot perform I/O on unconstrained
		 * types. This is caught explicitly here.
		 */
	  || streq(original_name(SCOPE_OF(g_name)) , "SEQUENTIAL_IO")
	  || streq(original_name(SCOPE_OF(g_name)) , "DIRECT_IO" )) {
		if (is_unconstrained(actual_type)) {
			errmsg_l_id("Usage of private type % requires instantiation with",
			  " constrained type", g_name, "12.3.2", current_node);
			return (Symbol)0;
		}
		else if (is_generic_type(actual_type)) {
			/* instantiation of this actual will also have to be constrained
			 *	(see ACV test BC3205FB)
			 */
			misc_type_attributes(actual_type) |= TA_CONSTRAIN;
		}
	}
	return actual_type;
}

static Symbol valid_access_instance(Symbol g_name, Symbol actual_type,
  Symbolmap type_map)						/*;valid_access_instance*/
{
	Symbol	g_type, designated_formal, designated_actual;

	g_type = (Symbol) designated_type(g_name);

	if (is_access(actual_type)){
		/* the accessed actual type must be the proper instantiation
  		 * of the accessed generic.
  		 */
		designated_formal = symbolmap_get(type_map, g_type);
		if(designated_formal == (Symbol)0) designated_formal = g_type;
		designated_actual = (Symbol) designated_type(actual_type);

		if (base_type(designated_formal) != base_type(designated_actual)) {
			errmsg_id_id("expect access to % to instantiate %" ,
			  designated_formal, g_name, "12.3.3", current_node);
			return (Symbol)0;
		}
		if (is_access(designated_formal)){
			designated_formal = (Symbol) designated_type(designated_formal);
			designated_actual = (Symbol) designated_type(designated_actual);
		}
		if ((can_constrain(designated_formal)
		  != can_constrain(designated_actual))){
			errmsg_l("formal and actual designated types must be both ",
			  "constrained or unconstrained", "12.3.3", current_node);
			return (Symbol)0;
		}
		check_actual_constraint(designated_formal, designated_actual);

		return actual_type;
	}
	else{
		errmsg_id("Expect access type to instantiate %", g_name, "12.3.5",
		  current_node);
		return (Symbol)0;
	}
}

static Symbol valid_array_instance(Symbol g_name, Symbol actual_type,
  Symbolmap type_map)						/*;valid_array_instance*/
{
	Symbol	g_type, g_comp, a_comp, t;
	int		i;
	Tuple	g_info, a_info, new_info;
	int		exists;
	Fortup	ft1;
	g_type = TYPE_OF(g_name);

	if ( !is_array(actual_type)) {
		errmsg_id("Expect array type to instantiate %", g_name, "12.3.4",
		  current_node);
		return (Symbol)0;
	}
	else if (can_constrain(actual_type) && !can_constrain(g_name)){
		errmsg_id("Expect constrained array type to instantiate %", g_name,
		  "12.3.4", current_node);
		return (Symbol)0;
	}
	else if (!can_constrain(actual_type) && can_constrain(g_name)){
		errmsg_id("Expect unconstrained array type to instantiate %", g_name,
		  "12.3.4", current_node);
	}
	else if (no_dimensions(actual_type) != no_dimensions(g_type)) {
		errmsg_id("Dimensions of actual type do not match those of %", g_name,
		  "12.3.4", current_node);
		return (Symbol)0;
	}
	else{
		/* Collect index types and component type. */
		g_info = get_array_info(g_type);
		a_info = get_array_info(actual_type);
		new_info = tup_new(tup_size(g_info));
		FORTUPI(t=(Symbol), g_info, i, ft1);
			new_info[i] = (char *) replace(t, type_map);
		ENDFORTUP(ft1);
		g_comp = (Symbol) new_info[tup_size(new_info)];
		a_comp = (Symbol)a_info[tup_size(a_info)];

		exists = FALSE;
		FORTUPI(t=(Symbol), new_info, i, ft1);
			if (!compatible_types(t, (Symbol) a_info[i])) {
				exists = TRUE;
				break;
			}
		ENDFORTUP(ft1);
		if (exists) {
			errmsg_l_id("index or component type mismatch in instantiation",
			  " of array type %", g_name, "12.3.4", current_node);
			return (Symbol)0;
		}
		/* Check components. */
		else if  (is_access(g_comp)	 ?
		  can_constrain(designated_type(g_comp)) !=
		  can_constrain(designated_type(a_comp))
		  : can_constrain(g_comp) !=can_constrain(a_comp) ) {
			errmsg_l("formal and actual array component type must be both ",
			  "constrained or unconstrained", "12.3.4", current_node);
			return (Symbol)0;
		}
		else {
			for (i = 1; i <= tup_size(new_info); i++)
				check_actual_constraint((Symbol)new_info[i],(Symbol) a_info[i]);
			return actual_type;
		}
	}
}

static int is_valid_disc_instance(Symbol g_name, Symbol a_name,
  Symbolmap type_map)							/*;is_valid_disc_instance*/
{
	/* checks that the formal and actual discriminant lists match in type
	 * and position.
	 */

	Tuple	g_list, a_list;
	Symbol	ad, gd;
	int		i;
	Symbol	t;
	Fortup	ft1;
	Symbol	gt, at;

	g_list = (Tuple) discriminant_list(g_name);
	a_list = (Tuple) discriminant_list(a_name);
	if (tup_size(g_list) != tup_size(a_list))
		return FALSE;
	else{
		FORTUPI(gd=(Symbol), g_list, i, ft1);
			ad = (Symbol)a_list[i];
			t = TYPE_OF(gd);			/* Type of discriminant */
			gt = symbolmap_get(type_map, t);	/* may be formal generic. */
			if (gt == (Symbol)0) gt = t;
			at = TYPE_OF(ad);			/* Base type of actual */
			if (base_type(gt) != base_type(at))   /* must match. */
				return  FALSE;
			else{
				check_actual_constraint(gt, at);	/* and constraints also. */
				/* The discriminant names of the formal may have been used
				 * in a selector in the generic body.They must be mapped into
				 * the actual discriminants.
				 */
				symbolmap_put(type_map, gd, ad);
			}
		ENDFORTUP(ft1);
	}
	return	TRUE;
}

static Tuple get_array_info(Symbol a_type)			/*;get_array_info*/
{
	/* Make sequence of index and component type marks, for comparing a
	 * generic array type with its instantiation.
	 */

	Tuple	tup;

	if (cdebug2 > 3 ) TO_ERRFILE("AT PROC :  get_array_info(a_type) ");

	tup = tup_copy(index_types(a_type));
	tup = tup_with(tup, (char *) component_type(a_type));
	return tup;
}

static void generic_subprog_instance(Node instance, Symbol g_name,
  Symbolmap type_map, int is_default)			/*;generic_subprog_instance*/
{
	/* Determine the operator, procedure, or attribute which is used to
	 * instantiate a given generic subprogram parameter .
	 *
	 * To validate the new instance, we must first replace generic types by
	 * actual types, to find the  instantiated signature of the  subprogram.
	 */

	Tuple	new_sig, tup, new_types;
	Symbol	new_type, proc_name, new_name;
	Symbol	real_proc, f;
	Fortup	ft1;
	int		i;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  generic_subprog_instance");

	if (SIGNATURE(g_name)!=(Tuple)0) {
		new_sig = tup_new(tup_size(SIGNATURE(g_name)));
		FORTUPI(f=(Symbol), SIGNATURE(g_name), i, ft1);
			tup = tup_new(4);
			tup[1] = ORIG_NAME(f);
			tup[2] = (char *) NATURE(f);
			tup[3] = (char *)replace(TYPE_OF(f), type_map);
			tup[4] = (char *) instantiate_tree((Node) default_expr(f),type_map);
			new_sig[i] = (char *) tup;
		ENDFORTUP(ft1);
	}
	new_type = replace(TYPE_OF(g_name), type_map);
	if (cdebug2 > 0 ) TO_ERRFILE("Gen.Subprog. has signature " );
	if (is_default)
		new_types = find_renamed_types(NATURE(g_name),
		  new_sig, new_type, instance);
	else {	/* instantiate using actual */
		new_types = find_renamed_entity(NATURE(g_name),
		  new_sig, new_type, instance);
		if (tup_size(new_types) == 0) {		/* renaming error; */
			errmsg_id("invalid match for generic subprogram %",
			  g_name, "12.3.6", instance);
			return;
		}
	}
	if (tup_size(new_types) != 0) {		/* no renaming error; */
		new_type = (Symbol) tup_frome(new_types);
		FORTUPI(tup=(Tuple), new_sig, i, ft1)
		    tup[3] = new_types[i];
		ENDFORTUP(ft1)
	}
	if (N_KIND(instance) == as_simple_name) {
		/* It must be the name of an operator or user-defined procedure. */
		proc_name = N_UNQ(instance);

		/* instance is a renamed or derived subprogram. Subprogram calls */
		/* must use the name of the parent subprogram, so:*/
		if ((real_proc = ALIAS(proc_name)) != (Symbol)0)
			proc_name = real_proc;
		symbolmap_put(type_map, ALIAS(g_name), proc_name);
	}
	else {
		/* Instantiation by an attribute or an entry. */
		new_name = anon_proc_instance(g_name, new_sig, new_type);
		symbolmap_put(type_map, ALIAS(g_name), new_name);
		instantiation_code_with(make_rename_node(new_name, instance));
	}
}

static Tuple find_renamed_types(int kind, Tuple formals, Symbol ret,
  Node name_node)								/*;find_renamed_types*/
{
	/* This procedure is finds the types for the default of a generic
	 * subprogram parameter. In such a case, find_renamed_entity is called
	 * from generic_subp_decl (generic declaration), and if no subprogram
	 * is supplied at instantiation, this procedure is called to determine the
	 * types of the new signature
	 */

	Symbol	old1, e_name, typ, typ2, res, i;
	Node		e_node, attr_node, typ_node;
	int		attr;
	Tuple	types, tup;
	Fortup	ft1;

	types = tup_new(0);

	switch (N_KIND(name_node)) {
	case as_simple_name:
		/* suprogram name renames subprogram name. */
		old1 = N_UNQ(name_node);
		if (NATURE(old1) != na_op) {
			FORTUP(i=(Symbol), SIGNATURE(old1), ft1);
				types = tup_with(types, (char *) TYPE_OF(i) );
			ENDFORTUP(ft1);
			types = tup_with(types, (char *) TYPE_OF(old1));
		}
		else {
			FORTUP(tup=(Tuple), formals, ft1);
				types = tup_with(types, (char *) base_type((Symbol) tup[3]));
			ENDFORTUP(ft1);
			types = tup_with(types, (char *) base_type(ret));
		}
		break;
	case as_entry_name:
		/* Procedure renames a entry given by a qualified name. Find */
		/* the full entry (and task) name. */
		e_node = N_AST2(name_node);
		if (e_node != OPT_NODE) {
			e_name = N_UNQ(e_node);
			FORTUP(i=(Symbol), SIGNATURE(e_name), ft1)
			    types = tup_with(types, (char *) TYPE_OF(i) );
			ENDFORTUP(ft1)
		    types = tup_with(types, (char *) symbol_none);
		}
		break;
	case as_attribute:
		/* The name can be an attribute, renaming a function. */
		attr_node = N_AST1(name_node);
		typ_node = N_AST2(name_node);
		attr = (int) attribute_kind(name_node);
		typ	 = N_UNQ(typ_node);
		/* Find type returned by the attribute, and the required type of its
		 * second argument.
		 */
		if (attr == ATTR_SUCC || attr == ATTR_PRED) {
			typ2 = base_type(typ);
			res = base_type(typ);
		}
		else if (attr == ATTR_IMAGE) {
			typ2 = base_type(typ);
			res = symbol_string;
		}
		else if (attr == ATTR_VALUE) {
			typ2 = symbol_string;
			res = base_type(typ);
		}
		types = tup_new(2);
		types[1] = (char *) typ2;
		types[2] = (char *) res;
		break;
	default:
#ifdef DEBUG
		zpnod(name_node);
#endif
		chaos("unexpected node in find_renamed_types");
	}
	return types;
}

static Node make_rename_node(Symbol name, Node instance)  /*;make_rename_node*/
{
	/* Create a renaming node, for	use when a generic subprogram parameter
	 * is instantiated with	 an attribute or  an entry name. The rename node
	 * of kind as_rename_sub_tr need not contain the spec node as this info
	 * can be obtained by EXPAND from the symbol table but instead only contains
	 * the unique name of the subprogram plus the instance info.
	 */

	Node rename_node;

	rename_node = node_new(as_rename_sub_tr);
	N_AST2(rename_node) = instance;
	N_UNQ(rename_node) = name;
	return rename_node;
}

Symbol anon_proc_instance(Symbol g_name, Tuple sig, Symbol typ)
{
	/* When a generic subprogam is instantiated with an attribute or an
	 * entry, we create a renaming declaration for an anonymous procedure.
	 * The generic subprogram then renames this anonymous one.
	 */
	Symbol	new_name, t, nam;
	Tuple	new_sig, tup, def;
	Fortup	ft1;
	int		kind;
	char	*id, *newat;
	char	*newat_str();

	new_name = sym_new(NATURE(g_name));
	newat = newat_str();
	dcl_put(DECLARED(scope_name), newat, new_name);
	TYPE_OF(new_name) = typ;
	ORIG_NAME(new_name) = strjoin(ORIG_NAME(g_name), newat);

	newscope(new_name);
	new_sig = tup_new(0);

	FORTUP(tup=(Tuple), sig, ft1);
		id = tup[1];
		kind = (int) tup[2];
		t = (Symbol) tup[3];
		def = (Tuple) tup[4];
		nam = find_new(id);
		NATURE(nam) = kind;
		TYPE_OF(nam) = t;
		SIGNATURE(nam) = def;
		new_sig = tup_with(new_sig, (char *) nam);
	ENDFORTUP(ft1);
	SIGNATURE(new_name) = new_sig;
	popscope();

	return new_name;
}

static void instantiation_code_with(Node node)
{
	/* add item to instantiation_code */

	int	n = (int) instantiation_code[0];

	if (instantiation_code_n >= n)
		instantiation_code = tup_exp(instantiation_code,
		    (unsigned) n+INSTANTIATION_CODE_INC);
	instantiation_code[++instantiation_code_n] = (char *) node;
}

/* the following procedures formerly in undone.c have been put here
 * as the only references to them occurred in chapter 12 and they
 * should no longer be needed once that chapter fully translated.
 */
void is_identifier() {
	undone("is_identifier");
}
void is_tuple() {
	undone("is_tuple");
}
