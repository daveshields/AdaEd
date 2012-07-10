/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "3.h"
#include "attr.h"
#include "setprots.h"
#include "dclmapprots.h"
#include "errmsgprots.h"
#include "evalprots.h"
#include "nodesprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "chapprots.h"

static void new_unconstrained_array(Symbol, Node);
static Symbol constrain_index(Symbol, Node);
static void discr_decl(Node);
static Tuple process_anons(Tuple);
static int reformat_requires(Node);

Tuple apply_range(Node range_expr) /*;apply_range*/
{
	/* A'RANGE is equivalent to A'FIRST..A'LAST. When the range attribute
	 * is used as a constraint, the bounds are expressed according to the
	 * above equivalence. This is not strictly correct if the elaboration
	 * of A has side-effects, but we ignore this detail for now.
	 */

	Node	attr, arg1, arg2;
	Tuple	new_c;
	Node	l_node, f_node;
	int	f, l, attr_kind;

	if (N_KIND(range_expr) == as_qual_range)
		/* discard spurious constraint. */
		range_expr = N_AST1(range_expr);
	attr = N_AST1(range_expr);
	arg1 = N_AST2(range_expr);
	arg2 = N_AST3(range_expr);

	/* The attribute is either O_RANGE or T_RANGE, according as arg1 is an
	 * object or a type. FIRST and LAST must be marked accordingly.
	 */
	/* In C note that base attribute kind followed by O_ kind, then T_. */
	attr_kind = (int) attribute_kind(range_expr);

	if (attr_kind == ATTR_O_RANGE) {
		f = ATTR_O_FIRST;
		l = ATTR_O_LAST;
	}
	else {
		f = ATTR_T_FIRST;
		l = ATTR_T_LAST;
	}

	f_node = new_attribute_node(f, arg1, arg2, N_TYPE(range_expr));
	l_node = new_attribute_node(l, copy_tree(arg1), copy_tree(arg2),
	  N_TYPE(range_expr));

	N_KIND(range_expr) = as_range;
	N_AST1(range_expr) = f_node;
	N_AST2(range_expr) = l_node;

	/*return ?? ['range', f_node, l_node];*/
	new_c = constraint_new(CONSTRAINT_RANGE);
	numeric_constraint_low(new_c) = (char *) f_node;
	numeric_constraint_high(new_c) = (char *) l_node;
	return new_c;
}

void array_typedef(Node node)								/*;array_typedef*/
{
	Node index_list_node, type_indic_node;
	Tuple index_nodes;
	Node indx_node, indx1_node;
	Tuple index_type_list;
	Symbol	element_type;
	int i, exists;
	Fortup	ft1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : array_typedef");

	index_list_node = N_AST1(node);
	type_indic_node = N_AST2(node);
	sem_list(index_list_node);
	index_nodes = N_LIST(index_list_node);

	index_type_list =  tup_new(tup_size(index_nodes));
	FORTUPI(indx_node =(Node), index_nodes, i, ft1);
		index_type_list[i] = (char *) make_index(indx_node);
	ENDFORTUP(ft1);

	adasem(type_indic_node);
	element_type = promote_subtype(make_subtype(type_indic_node));

	/* Validate an array type definition.*/

	exists = FALSE;
	FORTUP(indx_node =(Node) , index_nodes, ft1);
		if (N_KIND(indx_node) == as_box) {
			exists = TRUE;
			break;
		}
	ENDFORTUP(ft1);
	if (exists) {
		exists = FALSE;
		/*Unconstrained array . Verify that all indices are unconstrained.*/
		FORTUP(indx1_node = (Node), index_nodes, ft1);
			if (N_KIND(indx1_node) != as_box) {
				exists = TRUE;
				break;
			}
		ENDFORTUP(ft1);
		if (exists) {
			errmsg("Constraints apply to all indices or none", "3.6.1", node);
		}
	}
	if (is_unconstrained(element_type)) {
		errmsg("Unconstrained element type in array declaration",
		  "3.6.1, 3.7.2", type_indic_node);
	}
	check_fully_declared2(element_type);

	for (i = 1; i<= tup_size(index_nodes); i++) {
		Node tmp = (Node) index_nodes[i];
		N_UNQ(tmp) = (Symbol) (index_type_list[i]);
	}
	N_UNQ(type_indic_node) = element_type;
}

void new_array_type(Symbol array_type, Node def_node)  /*;new_array_type*/
{
	/* This	 procedure  is	called	whenever  an array type is created.
	 * For each new array type we create a corresponding sequence type,
	 * which is an unconstrained  array. Unconstrained array types have
	 * nature na_array, while constrained arrays have nature na_subtype.
	 */

	Node	index_list_node;
	Tuple	tn;
	Node	tnn;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : new_array_type(array_type");

	adasem(def_node);
	index_list_node = N_AST1(def_node);

	tn =  N_LIST(index_list_node);
	tnn = (Node) tn[1];
	if (N_KIND(tnn) == as_box)
		/* Unconstrained array definition. In this case, introduce only the*/
		/* unconstrained type, and ignore the actual array type.*/
		new_unconstrained_array(array_type, def_node);
	else
		new_constrained_array(array_type, def_node);
}

static void new_unconstrained_array(Symbol sequence_type, Node def_node)
													/*;new_unconstrained_array*/
{
	Node index_list_node, type_indic_node, indx_node;
	Fortup	ft1;
	int	i, l;
	Tuple	index_list, array_info;
	Symbol	comp;

	index_list_node= N_AST1(def_node);
	type_indic_node = N_AST2(def_node);
	/*index_list := [N_UNQ(indx_node) : indx_node in N_LIST(index_list_node)];*/
	index_list = tup_new(tup_size(N_LIST(index_list_node)));
	FORTUPI(indx_node=(Node), N_LIST(index_list_node), i, ft1);
		index_list[i] = (char *) N_UNQ(indx_node);
	ENDFORTUP(ft1);
	/*??array_info := [index_list, N_UNQ(type_indic_node)];*/
	array_info = tup_new(2);
	array_info[1] = (char *) index_list;
	comp = N_UNQ(type_indic_node);
	array_info[2] = (char *) comp;
	/*SYMBTAB(sequence_type) := [na_array, sequence_type, array_info];*/
	NATURE(sequence_type) = na_array;
	TYPE_OF(sequence_type) = sequence_type;
	SIGNATURE(sequence_type) = array_info;
	/*Mark the type as limited if the component type is.*/
	if (is_access(comp))
		misc_type_attributes(sequence_type) = 0;
	else {
		l= (int) private_kind(comp);
		misc_type_attributes(sequence_type) = l;
	}
	root_type(sequence_type) = sequence_type;
	initialize_representation_info(sequence_type,TAG_ARRAY);

	/* For each unconstrained array type, we introduce an instance of the
	 * 'aggregate' pseudo-operator for that array.
	 */
	new_agg_or_access_agg(sequence_type);
}

void new_constrained_array(Symbol array_type, Node def_node)
													/*;new_constrained_array*/
{
	char	*nam;
	Fortup	ft1;
	Symbol	sequence_type;
	Tuple	t, index_list, array_info;
	Node	index_list_node, type_indic_node, indx_node;
	int	i;
	char	*sequence_type_name;

	/* Construct meaningful name for anonymous parent type.*/
	nam = original_name(array_type);
	if (strcmp(nam , "") == 0) nam = "anonymous_array";
	sequence_type_name = strjoin(nam , strjoin("\'base" , newat_str()));
	sequence_type = sym_new(na_void);
	dcl_put(DECLARED(scope_name), sequence_type_name, sequence_type);
	SCOPE_OF(sequence_type) = SCOPE_OF(array_type);
	/* emit sequence type as an anonymous type. It is used in aggregates
	 * that are assigned to slices, and in other unconstrained contexts.
	 * (This should only be needed for one dimensional arrays).
	 */
	/*top(NEWTYPES) with:= sequence_type;*/
	t = (Tuple) newtypes[tup_size(newtypes)];
	t = tup_with(t, (char *) sequence_type);
	newtypes[tup_size(newtypes)] = (char *) t;
	new_unconstrained_array(sequence_type, def_node);

	/* Make the actual array type into a subtype of the unconstrained one*/

	index_list_node = N_AST1(def_node);
	type_indic_node = N_AST2(def_node);
	index_list = tup_new(tup_size(N_LIST(index_list_node)));
	FORTUPI(indx_node = (Node), N_LIST(index_list_node), i, ft1);
		index_list[i] = (char *) N_UNQ(indx_node);
	ENDFORTUP(ft1);
	/*array_info := [index_list, N_UNQ(type_indic_node)];*/
	array_info = tup_new(2);
	array_info[1] = (char *) index_list;
	array_info[2] = (char *) N_UNQ(type_indic_node);
	/*??SYMBTAB(array_type) = [na_subtype, sequence_type, array_info];*/
	NATURE(array_type) = na_subtype;
	TYPE_OF(array_type) = sequence_type;
	SIGNATURE(array_type) = array_info;
	misc_type_attributes(array_type) = misc_type_attributes(sequence_type);
	root_type(array_type) = sequence_type;
}

Symbol anonymous_array(Node node) /*;anonymous_array*/
{
	/* Process an array definition in an object or constant declaration.
	 * The node is an array_type node.
	 */

	Symbol typ;
	Tuple	t;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : anonymous_array");

	typ =	find_new(strjoin("anon", newat_str()));	  /*Create  a  name for it*/
	new_array_type(typ, node);	/*elaborate   definition*/
	/*??top(NEWTYPES) with:= typ;*/
	/* Insert into type stack */
	t = (Tuple) newtypes[tup_size(newtypes)];
	t = tup_with(t, (char *) typ);
	newtypes[tup_size(newtypes)] = (char *) t;
	return typ;
}

Symbol constrain_array(Symbol type_mark, Node constraint) /*;constrain_array*/
{
	int	i;
	Symbol	new_array;
	Tuple	indices, constraint_nodes, new_indices;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  constrain_array");

	/* Apply index constraints to array type.*/

	if (! can_constrain(type_mark)) {
		errmsg("Array type is already constrained", "3.6.1", constraint);
		return symbol_any;
	}

	if (N_LIST_DEFINED(N_KIND(constraint)))
		constraint_nodes = N_LIST(constraint);
	else
		constraint_nodes = (Tuple)0;
	if (constraint_nodes == (Tuple)0
	  || tup_size(constraint_nodes) != no_dimensions(type_mark)) {
		errmsg_id("Incorrect no. of index constraints for type %", type_mark,
		  "3.6.1", constraint);
		return symbol_any;
	}

	if (constraint == OPT_NODE)
		new_array = type_mark;
	else {
		/* apply constraints to each index type. */
		indices = (Tuple) (index_types(type_mark) );
		/* ??  new_indices = [constrain_index(indices(i), constraint_nodes(i)):
		 *   i in [1..#constraint_nodes]];
		 */
		new_indices = tup_new(tup_size(constraint_nodes));
		for (i = 1; i <= tup_size(constraint_nodes); i++)
			new_indices[i] = (char *) constrain_index((Symbol) indices[i],
			  (Node) constraint_nodes[i]);
	}

	new_array = anonymous_type();	/* Create  a  name for it*/
	/* ??SYMBTAB(new_array):= [na_subtype, type_mark,
	 *     [new_indices, component_type(type_mark)]];
	 */
	/* The signature should be in form of constraint. For now we
	 * will detect this case by nature na_subtype with signature
	 * being tuple of length two. This will be compatible with 
	 * uses of this signature.
	 */
	NATURE(new_array) = na_subtype;
	TYPE_OF(new_array) = type_mark;
	{ 
		Tuple t;
		t = tup_new(2);
		t[1] = (char *) new_indices;
		t[2] = (char *) component_type(type_mark);
		SIGNATURE(new_array) = t;
	}
	root_type(new_array) = root_type(type_mark);
	return new_array;
}

Symbol make_index(Node subtype)							/*;make_index*/
{
	/* Process an index  in an array declaration,  an entry family declara-
	 * tion, or a loop iteration. The index is given by an index declaration
	 * ( a 'box' ), or by a discrete range. The later can be  the name of a
	 * discrete type, or a subtype indication.
	 */

	Node	type_indic_node, constraint, lo, hi;
	Symbol	typ, new_index, type_name;
	Tuple	new_c;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : make_index");

	if (N_KIND(subtype) == as_box) {
		/* Unconstrained index definition. verify that the type_mark is*/
		/* discrete. */
		type_indic_node = N_AST1(subtype);
		new_index = find_type(type_indic_node);

	}
	else if (N_KIND(subtype) == as_range_attribute
	  || N_KIND(subtype) == as_attribute) {
		/* The discrete range is given by a range attribute. Resolve as such.*/
		N_KIND(subtype) = as_attribute;
		find_old(subtype); 
		check_type_d(subtype);
		typ = N_TYPE(subtype);
		new_index = anonymous_type();	/* Create  a  name for it*/
		/*??SYMBTAB(new_index):=[na_subtype, typ, apply_range(subtype)];*/
		NATURE(new_index) = na_subtype;
		TYPE_OF(new_index) = typ;
		SIGNATURE(new_index) = (Tuple) apply_range(subtype);
		root_type(new_index) = root_type(typ);
	}
	else if (N_KIND(subtype) == as_name) {
		type_indic_node = N_AST1(subtype);
		new_index = find_type(type_indic_node);
	}
	else if (N_KIND(subtype) == as_subtype) {
		/* the index is given by a subtype with a range constraint.*/

		type_indic_node = N_AST1(subtype);
		constraint = N_AST2(subtype);

		lo = N_AST1(constraint);
		hi = N_AST2(constraint);

		if (type_indic_node == OPT_NODE)
			check_type_d(subtype);
		else {			/* Type name is an identifier.*/
			find_old(type_indic_node);
			type_name = N_UNQ(type_indic_node);
			check_type(base_type(type_name), subtype);
		}
		new_index = anonymous_type();	/* Create  a  name for it*/
		typ	 = N_TYPE(subtype);
		/*SYMBTAB(new_index) = [na_subtype, typ, ['range', lo, hi]];*/
		NATURE(new_index) = na_subtype;
		TYPE_OF(new_index) = typ;
		new_c = constraint_new(CONSTRAINT_RANGE);
		numeric_constraint_low(new_c) = (char *) lo;
		numeric_constraint_high(new_c) = (char *) hi;
		SIGNATURE(new_index) = new_c;
		root_type(new_index) = root_type(typ);
	}
	else {
		errmsg("Invalid expression for index definition", "3.6.1", subtype);
		return symbol_any;
	}
	/* Check that a type for the range was found, and that it is
	 * discrete, and generate an anonymous type for it.
	 */
	if (noop_error)
		/* Error message was emitted already. */
		return  symbol_any;
	else if (! is_discrete_type(new_index))	 {
		errmsg("expect discrete type in discrete range", "3.3, 3.6.1", subtype);
		return  symbol_any;
	}
	return new_index;
}

static Symbol constrain_index(Symbol index, Node constraint)/*;constrain_index*/
{
	/* Process an index constraint in a constrained array declaration.
	 * The constraint can be a subtype name, or a range with or without
	 * an explicit type mark. The index has been obtained from the signature
	 * of the unconstrained array.
	 */

	Node type_node, range_node, lo, hi;
	Symbol	base_index, new_index, typ;
	Tuple new_constraint;
	int	nk;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : constrain_index");

	base_index = base_type(index);
	nk = N_KIND(constraint);

	if (nk == as_range_attribute) {
		find_old(constraint);
		N_KIND(constraint) = as_attribute;/* For resolution*/
		check_type_d(constraint);

		typ = N_TYPE(constraint);
		new_constraint = apply_range(constraint);

		if (! compatible_types(index, typ)) {
			errmsg_id("Invalid index constraint for %", index, "3.6.1",
			  constraint);
		}
	}
	else if (nk == as_subtype) {
		/* The type name in the given constraint must be the same as the*/
		/* original unconstrained index.*/
		type_node = N_AST1(constraint);
		range_node = N_AST2(constraint);
		if (type_node == OPT_NODE) {
			type_node = node_new(as_simple_name);
			copy_span(range_node, type_node);
			N_UNQ(type_node) = index;
			N_AST1(constraint) = type_node;
			N_AST2(constraint) = range_node;
		}
		else
			find_old(type_node);
		check_type(index, constraint);
		lo = N_AST1(range_node);
		hi = N_AST2(range_node);
		/*new_constraint := ['range', lo, hi];*/
		new_constraint = constraint_new(CONSTRAINT_RANGE);
		numeric_constraint_low(new_constraint) = (char *) lo;
		numeric_constraint_high(new_constraint) = (char *) hi;
	}
	else if (nk == as_range) {
		/* In the case of allocator, the constraint appears as a range
		 * node, because syntactically it is just a name. Rebuild the
		 * node as a subtype of the index.
		 */

		type_node = node_new(as_simple_name);
		copy_span(constraint, type_node);
		N_UNQ(type_node) = index;
		range_node = copy_node(constraint);
		N_KIND(constraint) = as_subtype;
		N_AST1(constraint)  = type_node;
		N_AST2(constraint)  = range_node;

		check_type(index, constraint);
		lo = N_AST1(range_node);
		hi = N_AST2(range_node);
		new_constraint = constraint_new(CONSTRAINT_RANGE);
		numeric_constraint_low(new_constraint) = (char *) lo;
		numeric_constraint_high(new_constraint) = (char *) hi;
	}
	else if (nk == as_name) {
		type_node = N_AST1(constraint);
		if (N_KIND(type_node) == as_attribute) {
			find_old(constraint);
			check_type(symbol_discrete_type, constraint);
			typ = N_TYPE(constraint);
			new_constraint = apply_range(constraint);
			if (! compatible_types(index, typ) ) {
				errmsg_id("Invalid index constraint for %", index, "3.6.1",
				  constraint);
			}
		}
		else {
			find_old(type_node);
			new_index = N_UNQ(type_node);
			if (! compatible_types(index, new_index) ) {
				errmsg_id("Invalid index constraint for %", index, "3.6.1",
				  constraint);
			}
		}
	}
	else {
		errmsg_id("Invalid index constraint for %", index, "3.6.1", constraint);
		new_index = base_index;
	}

	if (N_KIND(constraint) != as_name ) {
		/* create anonymous type for index.*/
		new_index = anonymous_type();
		/*??SYMBTAB(new_index) := [na_subtype, index, new_constraint];*/
		NATURE(new_index) = na_subtype;
		TYPE_OF(new_index) = index;
		SIGNATURE(new_index) = (Tuple) new_constraint;
		root_type(new_index) = root_type(index);
	}
	return new_index;
}

void record_decl(Symbol type_name, Node opt_disc, Node type_def)/*;record_decl*/
{
	/* Records constitute  a scope	for  the  component declarations within.
	 * The	scope is created prior to  the processing of these declarations.
	 * Discriminants  are  processed first, so  that  they are visible when
	 * processing the  other components. After the	discriminants have  been
	 * processed we set the nature of the type to na_record.
	 *
	 * If  an  incomplete or private  type declaration  was already given for
	 * the type, then this	scope already exists, and  the discriminants have
	 * been declared within. We must verify that the full declaration matches
	 * the	incomplete one.
	 */

	Node comp_list_node, comp_dec_node, variant_node;
	Symbol n;
	Fordeclared	div;
	Symbol	comp;
	int	l;
	char	*str;
	Tuple	rectup;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : record_decl");

	newscope(type_name);
	if (record_declarations(type_name) == (Tuple)0)
		process_discr(type_name, opt_disc);
	NATURE(type_name) = na_record;
	TYPE_OF(type_name) = type_name;
	root_type(type_name) = type_name;

	/* Now process remaining field declarations.*/
	adasem(type_def);
	comp_list_node = N_AST1(type_def);

	comp_dec_node = N_AST1(comp_list_node);
	variant_node = N_AST2(comp_list_node);
	/* use indices in next few assignments since cannot use macros
	 * invariant_part, variant_part and declared_components on left hand side 
	 */
	rectup = SIGNATURE(type_name);
	rectup[1] = (char *) comp_dec_node; /* invariant_part */
	/*invariant_part(type_name) = (char *) comp_dec_node;*/
	/*variant_part(type_name) = (char *) variant_node;*/
	rectup[2] = (char *) variant_node;

	/*declared_components(type_name) = (char *) DECLARED(scope_name);*/
	rectup[4] =  (char *) DECLARED(scope_name);
	misc_type_attributes(type_name) = 0;
#ifdef TBSL
	-- in SETL, following qualified by 'if exists'. review this  ds 6-jan-85
#endif
	FORDECLARED(str, comp, (Declaredmap)DECLARED(scope_name), div)
    	l = private_kind(TYPE_OF(comp));
		misc_type_attributes(type_name) = 
	      (int) misc_type_attributes(type_name) | l;
		if  (l != 0) 
			break;
	ENDFORDECLARED(div)

	/* The nature of the record components is given as na_field while the
	 * record is being processed, in order to catch invalid dependencies
	 * among component declarations. Reset the nature  of each to 'obj'
	 * (except for discriminants of course).
	 */

	FORDECLARED(str, n, (Declaredmap)(DECLARED(scope_name)), div)
	    if (NATURE(n) == na_field)
			NATURE(n) = na_obj;
		else if (NATURE(n) == na_discriminant) {
			/* constant folding of default values of discriminants is
	     	* delayed until after conformance checks
	     	*/
			eval_static((Node)default_expr(n));
		}
	ENDFORDECLARED(div)
    popscope();			/* Exit record scope.*/

	/* For each record type we create an aggregate of the corresponding
	 * type.
	 */
 	initialize_representation_info(type_name,TAG_RECORD);
#ifdef TBSL
	not_chosen_put(type_name, (Symbol)0);
#endif

	current_node = type_def;
	new_agg_or_access_agg(type_name);
}

void process_discr(Symbol type_name, Node opt_disc) /*;process_discr*/
{
	/* Process discriminants, or reprocess them in a full type declaration.
	 * Introduce the record scope. It is exited after the call, in type_decl
	 * or record decl, or private_decl.
	 */

	Tuple disc_names;
	Node	discr_node, id_list_node, id_node;
	Fortup	ft1, ft2;
	int	i, has_default;
	Tuple	rectup;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  process_discr");

	record_declarations(type_name) = tup_new(5);
	discr_decl(opt_disc);
	/*discr_decl_tree(type_name) = (char *) opt_disc;*/
	/* use index since cannot use discr_decl_tree macro on left	 ds 31 dec 84*/
	rectup = SIGNATURE(type_name);
	rectup[5] = (char *) opt_disc;
	if (opt_disc != OPT_NODE) {
		/* add 'constrained' bit as additional discriminant in front.*/
		disc_names = tup_new1((char *)symbol_constrained);

		FORTUP(discr_node =(Node), N_LIST(opt_disc), ft1 );
			id_list_node = N_AST1(discr_node);
			FORTUP(id_node =(Node), N_LIST(id_list_node), ft2);
				disc_names = tup_with(disc_names, (char *) N_UNQ(id_node));
			ENDFORTUP(ft2);
		ENDFORTUP(ft1);

		/* Check that all discriminants have default values, or none.*/
		/* Omit constrained bit from this test.                      */
		has_default = ((Node)default_expr((Symbol)disc_names[2]) != OPT_NODE);

		for (i = 3; i <= tup_size(disc_names); i++) {
			if (((Node)(default_expr((Symbol)disc_names[i])) != OPT_NODE)
			  != has_default) {
				errmsg(
				  "Incomplete specification of default vals for discriminants",
				  "3.7.1", opt_disc);
			}
		}
	}
	else disc_names = tup_new(0);
	/*discriminant_list(type_name) = (char *) disc_names;*/
	rectup = SIGNATURE(type_name);
	rectup[3] = (char *) disc_names;
	/* Make names of discriminants visible at this point, because they may
     * be used in constraints to other components of the current record type.
     */
	/*declared_components(type_name) = DECLARED(scope_name);*/
	rectup[4] = (char *) DECLARED(scope_name);
}

static void discr_decl(Node discr_list_node) /*;discr_decl*/
{
	/* Process discriminant declarations. Discriminants  are processed  like
	 * variable declarations, except that the type of a discriminant must be
	 * discrete,  and  the	nature	of  a  discriminant is, naturally enough
	 * na_discriminant. This insures that discriminants cannot appear on the
	 * left of an assignment, nor in expressions.
	 */

	Node discr_node, id_list_node, type_node, init_node, id_node;
	Tuple id_nodes, nam_list;
	Symbol type_mark, n;
	int    i;
	Fortup ft1, ft2;
	Node	i_node, tmpnode, type_copy;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  discr_decl");

	FORTUP(discr_node =(Node), N_LIST(discr_list_node), ft1);
		id_list_node = N_AST1(discr_node);
		type_node = N_AST2(discr_node);
		init_node = N_AST3(discr_node);
		id_nodes = N_LIST(id_list_node);
		current_node = id_list_node;
		nam_list = tup_new(tup_size(id_nodes));
		FORTUPI(id_node=(Node), id_nodes, i, ft2);
			nam_list[i] = (char *) find_new(N_VAL(id_node));
		ENDFORTUP(ft2);
		/* save original type_node for later conformance checks */
		type_copy = copy_tree(type_node);
		find_type(type_copy);
		type_mark = N_UNQ(type_copy);

		if (! is_discrete_type(type_mark) ) {
			errmsg("Discriminant must have discrete type", "3.7.1", type_node);
			type_mark = symbol_any;
		}

		if (init_node != OPT_NODE ) {
			/* type check, but do not perform constant folding, for later
	 		 * conformance checks
	 		 */
			i_node = copy_tree(init_node);
			adasem(i_node);
			normalize(type_mark, i_node);
		}
		else i_node = init_node;

		FORTUP(n =(Symbol), nam_list, ft2);
			NATURE(n) = na_discriminant;
			TYPE_OF(n) = type_mark;
			SIGNATURE(n) = (Tuple) i_node;
		ENDFORTUP(ft2);
		for	 (i = 1; i <= tup_size(id_nodes); i++) {
			tmpnode = (Node) id_nodes[i];
			N_UNQ(tmpnode) = (Symbol) nam_list[i];
		}
	ENDFORTUP(ft1);
}

void discr_redecl(Symbol type_name, Node discr_list)	/*;discr_redecl */
{
	/* Verify conformance of discriminant part on redeclarations of types. */

	Node  node, old_node, old_discr_list, id_list, type_node, init_node;
	Node  old_type_node, old_id_list, old_init_node;
	Tuple discr_tup, old_discr_tup;
	Symbol  discr;
	int  i;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  discr_redecl");

	old_discr_list = (Node) discr_decl_tree(type_name);

	if (!conform(discr_list, old_discr_list)) {
		conformance_error(discr_list != OPT_NODE ? discr_list : current_node);
		return;
	}

	discr_tup = N_LIST(discr_list);
	old_discr_tup = N_LIST(old_discr_list);
	for (i = 1; i <= tup_size(old_discr_tup); i++) {
		node = (Node) discr_tup[i];
		old_node = (Node) old_discr_tup[i];
		/* Pick a representatitive discriminant from current id list. */
		old_id_list = N_AST1(old_node);
		id_list = N_AST1(node);
		discr = N_UNQ((Node)N_LIST(old_id_list)[1]);

		old_type_node = N_AST2(old_node);
		type_node = N_AST2(node);
		init_node = N_AST3(node);
		old_init_node = N_AST3(old_node);
		find_type(type_node);
		if (N_UNQ(type_node) != TYPE_OF(discr))  {
			conformance_error(type_node);
			return;
		} /* end if; */

		if (init_node != OPT_NODE) {
			adasem(init_node);
			normalize(N_UNQ(type_node), init_node);
		}
		/* Verify that the default values are the same.  */
		if (!same_expn(init_node, (Node)default_expr(discr)) ) {
			conformance_error(init_node == OPT_NODE ? node : init_node);
			return;
		}
	}
}

int same_expn(Node exp1, Node exp2) 					/*;same_expn */
{
	/* verify that two resolved expression trees designate the same entity,
	 * or evaluate to the same.
	 */

	int i, nk;
	Tuple l1, l2;

	if (N_KIND(exp1) != N_KIND(exp2))
		return FALSE;

	nk = N_KIND(exp1);
	switch (nk) {
	case (as_simple_name):
		return (N_UNQ(exp1) == N_UNQ(exp2));
	case (as_ivalue):
		return const_eq((Const)N_VAL(exp1), (Const)N_VAL(exp2));
	default:
		if (N_AST1_DEFINED(nk) && (N_AST1(exp1) != (Node)0)) {
			if (!same_expn(N_AST1(exp1), N_AST1(exp2)))
				return FALSE;
			if (N_AST2_DEFINED(nk) && N_AST2(exp1) != (Node)0) {
				if (!same_expn(N_AST2(exp1), N_AST2(exp2)))
					return FALSE;
				if (N_AST3_DEFINED(nk) && N_AST3(exp1) != (Node)0) {
					if (!same_expn(N_AST3(exp1), N_AST3(exp2)))
						return FALSE;
					if (N_AST4_DEFINED(nk) && N_AST4(exp1) != (Node)0) {
						if (!same_expn(N_AST4(exp1), N_AST4(exp2)))
							return FALSE;
					}
				}
			}
		}
		if (N_LIST_DEFINED(nk))
			l1 = N_LIST(exp1);
		else
			l1 = (Tuple)0;
		if (l1  != (Tuple)0 ) {
			if (N_LIST_DEFINED(N_KIND(exp2)))
				l2 = N_LIST(exp2);
			else
				l2 = (Tuple) 0;
			if (l2 == (Tuple)0 || tup_size(l1) != tup_size(l2))
				return FALSE;
			for (i = 1; i<= tup_size(l1); i++) {
				if (!same_expn((Node)l1[i], (Node)l2[i]))
					return FALSE;
			}
		}
		return TRUE;		/* AST and LIST match. */
	}
}

void conformance_error(Node node) 				/*;conformance_error */
{
	errmsg("non conformance to previous declaration", "6.3.1", node);
}

#ifdef TBSN
Tuple bind_discr(Tuple discr_list)  /*;bind_discr*/
{
	/* The conformance rules  for  discriminant specifications require  the
	 * equality of the corresponding trees after name resolution and before
	 * constant  folding. (In fact, overload  resolution  may be  needed if
	 * function calls appear in the default expressions).
	 */
	Tuple	t1, t2;
	Fortup	ft1;
	Tuple	res;
	int	i;

	res = tup_new(tup_size(discr_list));
	FORTUPI(t1=(Tuple), discr_list, i, ft1);
		t2 = tup_new(4);
		t2[1] = t1[1];
		t2[2] = t1[2];
		t2[3] = t1[3];
		t2[4] = (char *) bind_names(t1[4]);
		res[i] = (char *) t2;
	ENDFORTUP(ft1);
	return res;
}
#endif

void comp_decl(Node field_node) /*;comp_decl*/
{
	/* Process record component declaration.
	 * Verify that the type is a constrained one, or that default values
	 * exist for the discriminants of the type.
	 */

	Node id_list_node, type_indic_node, expn_node, id_node;
	Tuple id_nodes, nam_list;
	Symbol type_mark, t_m, n;
	int		i;
	Fortup	ft1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  comp_decl");

	id_list_node = N_AST1(field_node);
	type_indic_node = N_AST2(field_node);
	expn_node = N_AST3(field_node);

	id_nodes = N_LIST(id_list_node);
	nam_list = tup_new(tup_size(id_nodes));
	FORTUPI(id_node=(Node), id_nodes, i, ft1);
		nam_list[i] = (char *) find_new(N_VAL(id_node));
	ENDFORTUP(ft1);

	adasem(type_indic_node);
	type_mark = promote_subtype(make_subtype(type_indic_node));
	N_UNQ(type_indic_node) = type_mark;
	check_fully_declared2(type_mark);
	adasem(expn_node);

	/* Type-check the initial value, if provided.*/

	if (expn_node != OPT_NODE) {
		t_m = check_init(type_indic_node, expn_node);
		/* check_type(type_mark, expn_node); */
	}

	/* Try to catch self-reference within a record type (a common mistake).*/
	if (in_open_scopes(type_mark )) {
		errmsg_nval("Invalid self-reference in definition of %",
		  type_indic_node, "3.1", type_indic_node);
	}
	if (is_unconstrained(type_mark)) {
		errmsg_nat("Unconstrained % in component declaration", type_mark,
		  "3.6.1, 3.7.2", type_indic_node);
	}

	FORTUP(n=(Symbol), nam_list, ft1);
		NATURE(n) = na_field;
		TYPE_OF(n) = type_mark;
		SIGNATURE(n) = (Tuple) expn_node;
	ENDFORTUP(ft1);

	for (i = 1; i <= tup_size(id_nodes); i++) {
		Node tmp = (Node) id_nodes[i];
		N_UNQ(tmp) = (Symbol) nam_list[i];
	}
}

Symbol constrain_record(Symbol type_mark, Node constraint) /*;constrain_record*/
{
	/* Process discriminant constraints of record type.
	 * Verify that values have been provided for all discriminants, that
	 * the original type is unconstrained, and that the types of the
	 * supplied expressions match the discriminant types.
	 */

	Symbol	d_name, typ;
	Tuple d_list;
	Tuple c_list, discr_map;
	char *d_id;
	Tuple d_seen;
	/* TBSL: d_seen should be freed before return	ds 6-jan-85 */
	Declaredmap comps;
	Tuple constraint_list;
	Node  ct, choice_list_node, choice_node, expn, name, nam, comp_assoc;
	int i, first_named, exists, j, k, d_list_size;
	Fortup	ft1, ft2;
	Tuple	dconstraint;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : constrain_record");

	if (! is_record(type_mark)) {
		errmsg("Invalid type for constraint", "3.3, 3.7.2", constraint);
		return symbol_any;
	}
	d_list = (Tuple) discriminant_list(type_mark);

	if(d_list == (Tuple)0 || tup_size(d_list) == 0) {
		errmsg("Invalid constraint: Record type has no discriminant",
		  "3.7.1, 3.7.2", constraint);
		return symbol_any;
	}

	d_seen = tup_new(0);		/*To verify that all discriminants were*/
	/* given values.*/

	constraint_list = N_LIST(constraint);

	/* Look for named associations in discriminant constraint list.*/

	exists = FALSE;
	FORTUPI(ct = (Node), constraint_list, i, ft1);
		if  (N_KIND(ct) == as_choice_list) {
			exists = TRUE;
			break;
		}
	ENDFORTUP(ft1);
	if  (exists) {
		first_named = i;
		exists = FALSE;
		for (j=i+1; j <= tup_size(constraint_list); j++) {
			nam = (Node) constraint_list[j];
			if ( N_KIND(nam) != as_choice_list ) {
				exists = TRUE;
				break;
			}
		}
		if (exists) {
			errmsg("Positional associations after named ones", "3.7.2", nam);
			return symbol_any;
		}
	}
	else
		first_named = tup_size(constraint_list) + 1;
	d_list_size = tup_size(d_list);
	discr_map = tup_new(0);

	/* The constrained bit is treated like a discriminant, and the system
	 * provides the initial constraint for it. This may be reset in the
	 * expander. 
	 */
	discr_map = discr_map_put(discr_map, symbol_constrained,
	  new_ivalue_node(int_const(TRUE), symbol_boolean));
	d_seen = tup_with(d_seen, (char *) symbol_constrained);

	for (i = 1; i<first_named; i++) {
		if (i+1 > d_list_size) {	/* Exhausted discriminant list*/
			errmsg("Too many constraints for record type", "3.7.2",
			  current_node);
			return symbol_any;
		}
		d_name = (Symbol) d_list[i+1];
		constraint = (Node) constraint_list[i];
		check_type(TYPE_OF(d_name), constraint);
		check_discriminant(constraint);

		if (N_TYPE(constraint) == symbol_any)  /* Type error occurred.*/
			;
		else
			discr_map = discr_map_put(discr_map, d_name, constraint );
		if (!tup_mem( (char *) d_name, d_seen))
			d_seen = tup_with(d_seen, (char *)  d_name);
	}

	/* recall that in SETL
	 * named_constraint = constraint_list(first_named..);
	 * so can replace comp_assoc in named_constraint by following
	 */
	for (j=first_named; j <= tup_size(constraint_list); j++) {
		comp_assoc = (Node) constraint_list[j];
		choice_list_node = N_AST1(comp_assoc);
		expn = N_AST2(comp_assoc);
		c_list = tup_new(0);	/* to collect names in this association.*/

		FORTUP(choice_node=(Node), N_LIST(choice_list_node), ft2);
			name = N_AST1(choice_node);
			if (N_KIND(choice_node) != as_choice_unresolved ) {
				errmsg_l("Expect discriminant names only in discriminant",
				  " constraint", "3.7.1, 3.7.2", choice_node);
				return	symbol_any;
			}

			d_id = N_VAL(name);
			comps = (Declaredmap) declared_components(type_mark);
			if (d_id == (char *)0  || (comps == (Declaredmap) 0)
			  || (d_name = dcl_get(comps, d_id)) == (Symbol) 0
			  || NATURE(d_name) != na_discriminant) {
				errmsg("Invalid discriminant name in discriminant constraint",
				  "3.7. 3.7.2", choice_node);
				return symbol_any;
			}
			if (tup_mem((char *) d_name, d_seen)) {
				errmsg_str("Duplicate constraint for discriminant %",
				  d_id, "3.7.1, 3.7.2", choice_node);
			}
			else {
				c_list = tup_with(c_list, (char *) d_name);
				if (!tup_mem((char *) d_name, d_seen))
					d_seen = tup_with(d_seen, (char *) d_name);
				TO_XREF(d_name);

				if (tup_size(c_list) == 1) {
					/* need to resolve it only for the first in list */
					check_type(TYPE_OF(d_name), expn);
					check_discriminant(expn);
				}
			}
		ENDFORTUP(ft2);
		discr_map = discr_map_put(discr_map, (Symbol) c_list[1], expn);

		for (k = 2; k <= tup_size(c_list); k++) {
			discr_map = discr_map_put(discr_map, (Symbol) c_list[k],
			  copy_tree(expn));
			if (base_type(TYPE_OF((Symbol)c_list[k]))
			  != base_type(TYPE_OF((Symbol)c_list[1]))) {
				errmsg("discriminants in named association must have same type",
				  "3.7.2(4)", comp_assoc);
			}
		}
	}
	if (tup_size(d_seen) == tup_size(d_list)) { /* All discriminants were ok.*/
		typ = anonymous_type(); 		/* Create a name for it*/
		NATURE(typ) = na_subtype;
		TYPE_OF(typ) = type_mark;
		dconstraint = constraint_new(CONSTRAINT_DISCR);
		numeric_constraint_discr(dconstraint) = (char *) discr_map;
		SIGNATURE(typ) = (Tuple) dconstraint;
		root_type(typ) = type_mark;
		not_chosen_put(type_mark, typ);
		type_mark = typ;
	}
	else {
		errmsg("Missing constraints for discriminants", "3.7.2", constraint);
	}
	/* TBSL: free d_seen if defined		ds 6-jan-85*/
	return type_mark;
}

int check_discriminant(Node expn) /*;check_discriminant*/
{
	/* Verify that when a discriminant appears in an index constraint or a
	 * discriminant constraint, it appears by itself and not as part of a
	 * larger expression. The check is made after type checking, in which case
	 * a constraint check may be applied on the node. The expression being
	 * constrained may be a valid discriminant reference itself.
	 */

	int	i, nk;
	Node	sub_expn;
	Fortup	ft;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  check_discriminant");

	if (NATURE(scope_name) != na_record) return FALSE;
	if (N_KIND(expn) == as_simple_name) return FALSE;

	if ( (N_KIND(expn) == as_discr_ref) || (N_KIND(expn) == as_qual_range
	  && N_KIND(N_AST1(expn)) == as_discr_ref))
		return TRUE;
	/* TBSN: check recoding of following loop over all AST subnodes*/
	nk = N_KIND(expn);
	for (i = 1; i <= 4; i++) {
		sub_expn = (Node)0;
		if (i == 1)
			if (N_AST1_DEFINED(nk)) sub_expn = N_AST1(expn);
		else if (i == 2)
			if (N_AST2_DEFINED(nk)) sub_expn = N_AST2(expn);
		else if (i == 3)
			if (N_AST3_DEFINED(nk)) sub_expn = N_AST3(expn);
		else if (i == 4)
			if (N_AST4_DEFINED(nk)) sub_expn = N_AST4(expn);
		if (sub_expn != (Node)0 && check_discriminant(sub_expn)) {
			errmsg_l("a discriminant appearing in a subtype indication ",
			  "must appear by itself", "3.7.1", expn);
			return FALSE;		/*No need to propagate error.*/
		}
	}
	/* must also search through N_LIST */
	if (N_LIST_DEFINED(nk) && N_LIST(expn) != (Tuple)0) {
		FORTUP(sub_expn=(Node), N_LIST(expn), ft);
			if (check_discriminant(sub_expn)) {
				errmsg_l("a discriminant appearing in a subtype indication ",
				  "must appear by itself", "3.7.1", expn);
				return FALSE;		/*No need to propagate error.*/
			}
		ENDFORTUP(ft);
	}
	return FALSE;
}

void variant_decl(Node node)								/*;variant_decl*/
{
	Node id_node, variant_list;
	Symbol	discr_name, dtyp;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  variant_decl");

	id_node = N_AST1(node);
	variant_list = N_AST2(node);

	find_old(id_node);
	discr_name = N_UNQ(id_node);
	if (NATURE(discr_name) != na_discriminant) {
		errmsg("Invalid discriminant name in variant part", "3.7.1, 3.7.3", id_node);
		return;
	}
	else if ((dtyp = TYPE_OF(discr_name)) == (Symbol)0 )
		return;
	else
		process_case(dtyp, variant_list);
}

void incomplete_decl(Node node)								/*;incomplete_decl*/
{
	Node	id_node, discr_list_node;
	char	*id;
	Symbol	name, old_name;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  incomplete_decl");

	/* Process  an	incomplete  declaration. The  identifier  must	not  have
	 * been declared already in the scope. However, an incomplete declaration
	 * may	appear in  the private part of a package, for a private type that
	 * has already been  declared. In  this case,  the discriminants (if any)
	 * must match.
	 */

	id_node = N_AST1(node);
	discr_list_node = N_AST2(node);

	sem_list(discr_list_node);
	id = N_VAL(id_node);
	old_name = dcl_get(DECLARED(scope_name), id);
	if (old_name == (Symbol)0 ) {
		name = find_new(id);
		N_UNQ(id_node) = name;
		TYPE_OF(name) = symbol_incomplete;
		root_type(name) = name;
		newscope(name);
		process_discr(name, discr_list_node);
		NATURE(name) = na_type;
		popscope();
	}
	else if (NATURE(scope_name) == na_private_part
	  && (TYPE_OF(old_name) == symbol_private
	  ||  TYPE_OF(old_name) == symbol_limited_private))
	{
		/* redeclaration of private type in private part.*/
		newscope(old_name);
		process_discr(old_name, discr_list_node);
		N_UNQ(id_node) = old_name;
		popscope();
	}
	else {
		errmsg_str("invalid redeclaration of %", id, "3.8, 8.2", id_node);
	}
}

void check_incomplete(Symbol type_mark)					  /*;check_incomplete*/
{
	/* Called to verify that an incomplete type is not used prematurely.*/

	if (TYPE_OF(base_type(type_mark)) == symbol_incomplete) {
		errmsg_id("Invalid use of type % before its full declaration",
		  type_mark, "3.8.1", current_node);
	}
}

void declarative_part(Node node)						/*;declarative_part*/
{
	/* Clean up list of declarations and generate nodes for anonymous types
	 * that are created when elaborating subtype indications, etc.
	 */

	Tuple	decl_nodes, type_list, anon_nodes, tup, id_list;
	Node	d, type_def, nam, component_list, invariant_node, init_node;
	Node	constraint, nod, id_node, subtype_indic, id_list_node;
	Fortup	ft1, ft2, ft3; 
	int		reformat;
	Node	type_indic_node, pnode, new_decl, a;
	Node	ancestor_node, decl_node, init;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  declarative_part");

	decl_nodes = tup_new(0);

	FORTUP(d = (Node), N_LIST(node), ft1);
		if (N_KIND(d) == as_line_no) {	 /* keep it for debugging */
			decl_nodes = tup_with(decl_nodes, (char *) d);
			continue;
		}

		/* For object and constant declarations create distinct declaration
		 * nodes for each item in the id_list except in the case where the 
		 * subtype indication is just a type mark. Complete constant decls.
		 * are always expanded.
		 */
		id_list_node    = N_AST1(d);
		type_indic_node = N_AST2(d);
		init_node       = N_AST3(d);

		if (N_KIND(d) == as_const_decl) reformat = TRUE;

		else if (N_KIND(d) == as_obj_decl ) {
			if (N_KIND(type_indic_node) == as_subtype_indic ) {
				/* if subtype indication carries explicit constraint,
            	 * must elaborate each declaration separately.
	      		 * (This latter is a little bit to strict.
				 * In a declaration like :
		  		 * type ARR is array (integer range <>) of integer;
 		  		 * A, B, C : ARR (1..100);
	 			 * There is no need to split (reformat) this declaration.
				 * This reformat generates 3 types and therefore 3
				 * 3 type templates 
            	 */
				reformat = (N_AST2(type_indic_node) != OPT_NODE)
				  && reformat_requires (type_indic_node);
			}
			else		/* anonymous array.*/
				reformat = TRUE;
		}
		else reformat = FALSE;

		if (reformat) {
			id_list = N_LIST(id_list_node);
			FORTUP(id_node = (Node), id_list, ft2);
				new_decl = d;
				if (tup_size(id_list) > 1) {
					new_decl = copy_tree(d);
					N_LIST(N_AST1(new_decl)) = tup_new1((char *) id_node);
				}
				newtypes = tup_with(newtypes, (char *) tup_new(0));
				/* To collect anonymous types*/
				adasem(new_decl);
				type_list = (Tuple) tup_frome(newtypes);
				FORTUP(pnode = (Node), process_anons(type_list), ft3);
					decl_nodes = tup_with(decl_nodes, (char *)  pnode);
				ENDFORTUP(ft3);
				decl_nodes = tup_with(decl_nodes, (char *) new_decl);
				/* A declaration like "a : array_type := (aggregate or
				 * qualification)" is split in two parts : a simple
				 * declaration, followed by an assignment.  The reason is the
				 * following : In the previous version there was a call to
				 * "array_ivalue", which makes a call to "compute_index".
				 * This is done to copy each component of the aggregate to its
				 * position in the array "a".  But, this can lead to incorrect
				 * results or to a constraint_error (incorrect subscript) in
				 * case of array sliding (the following assignement has to be
				 * performed : a (i) := aggregate (i + drift) instead of  a (i)
				 * := aggregate (i) ).  The solution we have chosen is the
				 * simplest and requires very little modifications.
				 */
				if (init_node != OPT_NODE
		    	  && (N_AST2_DEFINED(N_KIND(type_indic_node)))
		    	  && (N_AST2(type_indic_node) != OPT_NODE)
		    	  && (is_record(TYPE_OF(N_UNQ(id_node)))
		    	  || (is_array(TYPE_OF(N_UNQ(id_node)))
				  && ((N_KIND (init_node) == as_qualify)
				  || (N_KIND (init_node) == as_array_aggregate))))) {
					/* split object elaboration from actual assignment of
		    		* initial value to constrained records
		    		*/
					init = new_assign_node(copy_node(id_node),
			    		N_AST3(new_decl));
					N_AST3(new_decl) = OPT_NODE;
					decl_nodes = tup_with(decl_nodes, (char *) init);
				}
			ENDFORTUP(ft2);
			continue;
		}
		else {
			newtypes = tup_with(newtypes, (char *) tup_new(0));
			/* To collect anonymous types*/
			adasem(d);
			type_list  = (Tuple) tup_frome(newtypes);
			/* Create (sub)type declaration nodes for the anonymous types.*/
			anon_nodes = process_anons(type_list);
		}
	
		/* For record types, the anonymous types generated (which  may depend
		 * on discriminants) are attached to the invariant part of the record
		 * declaration, so that they may be emitted and elaborated within the
		 * record.
 		 */
		if (N_KIND(d) == as_type_decl) {
			id_node = N_AST1(d);
			type_def = N_AST3(d);
			if (N_KIND(type_def) == as_record) {
				component_list = N_AST1(type_def);
				invariant_node = N_AST1(component_list);
				FORTUP(a=(Node), anon_nodes, ft2);
					if (N_KIND(a) == as_subtype_decl) {
						nam = N_AST1(a);
						if (TYPE_OF(N_UNQ(nam)) == N_UNQ(id_node)) {
							/* We have an anonymous subtype of the current
							 * record type declaration. Mark it as a delayed
							 * type also.
							 */
							decl_node = copy_node(a);
							N_KIND(a) = as_delayed_type;
							ancestor_node = new_name_node(N_UNQ(id_node));
							N_AST1(a) = nam;
							N_AST2(a) = ancestor_node;
							N_AST3(a) = decl_node;
						}
					}
				ENDFORTUP(ft2);
				/* N_LIST(invariant_node) := anon_nodes */
				/*    + N_LIST(invariant_node); */
				tup = anon_nodes;
				FORTUP(nod = (Node), N_LIST(invariant_node), ft2);
					tup = tup_with(tup, (char *) nod);
				ENDFORTUP(ft2);
				N_LIST(invariant_node) = tup;
			}
			else {
				/*decl_nodes +:= anon_nodes;*/
				FORTUP(nod = (Node), anon_nodes, ft2);
					decl_nodes = tup_with(decl_nodes, (char *) nod);
				ENDFORTUP(ft2);
			}
		}
		else if (N_KIND(d) == as_subtype_decl) {
			id_node = N_AST1(d);
			subtype_indic = N_AST2(d);
			constraint = N_AST2(subtype_indic);
			if (constraint == OPT_NODE && !is_scalar_type(N_UNQ(id_node)) ) {
				/* The subtype is a renaming of its parent, and does not 
				 *  appear in the code. Ignore the node.
 				 */
				/*    tup_free(anon_nodes);*/
				continue;
			}
			else {
				if (is_array(N_UNQ(id_node)) || (is_record(N_UNQ(id_node)))) {
					/* discard anonymous array or record subtype to avoid 
		 			 * double elaboration 
		 			 */
					nod = (Node) tup_frome(anon_nodes);
					if (N_KIND (nod) != as_subtype_decl) {
						/*  the last node may be a type declaration: case 
		 				 *  of derived type and therefore must not be removed 
	 	 				 */
						anon_nodes = tup_with (anon_nodes, (char *) nod); 
					}
				}
				/*decl_nodes +:= anon_nodes;*/
				FORTUP(nod=(Node), anon_nodes, ft2);
					decl_nodes = tup_with(decl_nodes, (char *) nod);
				ENDFORTUP(ft2);
			}
		}
		else if (N_KIND(d) == as_num_decl ) {
			/* This represents declaration of a static universal constant
	 		 *  which can be removed from the tree, since it needs to be noted 
	 		 * only in the symbol table. The ivalue node representing the actual
	 		 * value will be picked up by collect_unit_nodes.
	 		 */
			continue;
		}
		else if (N_KIND(d) == as_rename_ex) {
			/* This represents a renaming of an exception which is handled
	 		 * strictly in the symbol table and no longer needs to be in the
	 		 * tree, so it is removed.
	 		 */
			continue;
		}
		else {
			/*decl_nodes +:= anon_nodes;*/
			FORTUP(nod = (Node), anon_nodes, ft2);
				decl_nodes = tup_with(decl_nodes, (char *) nod);
			ENDFORTUP(ft2);
		}

		decl_nodes = tup_with(decl_nodes, (char *) d);
		/*tup_free(anon_nodes);*/
	ENDFORTUP(ft1);
	N_LIST(node) = decl_nodes;
}

static Tuple process_anons(Tuple type_list)					/*;process_anons*/
{
	Symbol	t;
	Node	nam, decl;
	Fortup	ft1;
	Tuple	anon_nodes;

	/* Create (sub)type declaration nodes for the anonymous types.*/
	anon_nodes = tup_new(0);

	FORTUP(t=(Symbol), type_list, ft1);
		nam = node_new(as_simple_name);
		N_UNQ(nam) = t;
		decl = node_new( NATURE(t) == na_subtype ? as_subtype_decl
	      : as_type_decl );
		N_AST1(decl) = nam;
		N_AST2(decl) = OPT_NODE;
		if (N_KIND(decl) == as_type_decl)
			N_AST3(decl) = OPT_NODE;
		check_delayed_type(decl, t);
		anon_nodes = tup_with(anon_nodes, (char *)  decl );
	ENDFORTUP(ft1);
	return anon_nodes;
}

Symbol promote_subtype(Symbol subtype)					/*;promote_subtype*/
{
	/* This	 procedure is  called when a  subtype  indication  produces  an
	 * anonymous type.  This occurs	 when processing an object, constant or
	 * subtype  declaration, when  processing  an iteration	 scheme, or the
	 * range  of an entry  family.	If the subtype is  already a type name,
	 * it is returned as is.  If a previous subtype with the same structure
	 * in the same scope was already promoted,  then that one  is returned.
	 * Otherwise, the type mark is placed in the NEWTYPES stack, and atta-
	 * ched to the current declaration.
	 */

	Symbol parent_type;
	Tuple	t;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  promote_subtype");

	if (! is_anonymous(subtype)) return subtype;

    t =(Tuple) newtypes[tup_size(newtypes)];
	/*TBSL see if can reallocate tuple in top(top...) calculation below */
	if (!tup_mem((char *) subtype, t))
		newtypes[tup_size(newtypes)] = (char *) tup_with(t, (char *) subtype);
	parent_type = TYPE_OF(subtype);
	root_type(subtype) = root_type(parent_type);
	misc_type_attributes(subtype) = misc_type_attributes(parent_type);
	return subtype;
}

Tuple subtype_expr(Symbol name)							/*;subtype_expr*/
{
	/* OBSOLETE: used to generate AIS, return null tuple. */

	if (cdebug2 > 3) TO_ERRFILE("AT PROC: subtype_expr");
	return tup_new(0);
}

int is_character_type(Symbol name)						 /*;is_character_type*/
{
	/* An enumeration type is a character type if it contains at least one
	 * character literal.
	 */

	Symbol	bt;
	char		*c;
	int	i;
	Tuple	tup;

	if ( root_type(name) == symbol_character ) return TRUE;
	bt = base_type(name);
	if (NATURE(bt)	!= na_enum) return FALSE;
	tup = (Tuple) literal_map(bt);
	for (i = 1; i <= tup_size(tup); i += 2) {
		c = tup[i];
		if (strlen(c) == 3 &&c[0] == '\'' && c[2] == '\'') return TRUE;
	}
	return FALSE;
}

int is_discrete_type(Symbol name) /*;is_discrete_type*/
{
	Symbol	btype;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  is_discrete_type");

	if (TYPE_OF(name) != (Symbol)0) btype = root_type(name);
	else return FALSE;

	if (btype == symbol_integer
	  || btype== symbol_universal_integer
	  || btype == symbol_discrete_type
	  || btype == symbol_any) return TRUE;
	if (NATURE(btype) == na_enum ) return TRUE;
	return FALSE;
}

int is_numeric(Symbol name)									  /*;is_numeric*/
{
	Symbol r;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  is_numeric");

	/* ??const numeric_types = {'INTEGER', 'FLOAT', '$FIXED',
	 *  'universal_integer', 'universal_fixed', 'universal_real'};
	 * return (root_type(name) ??in numeric_types );
	 */
	r = root_type(name);
	return (r == symbol_integer || r == symbol_float 
	  || is_fixed_type(r) || r == symbol_universal_integer
	  || r == symbol_universal_real || r == symbol_universal_fixed );
}

int is_incomplete_type(Symbol t)				  /*;is_incomplete_type*/
{
	/* A type is incomplete if only an incomplete type declaration for it
	 * has been seen, or if one of its subcomponents is an incomplete private
	 * type (because of other rules, a subcomponent can never have an
	 * incomplete type).
	 */

	Symbol	b;

	b = base_type(t);
	return (TYPE_OF(b) == symbol_incomplete
	  || private_ancestor(b) != (Symbol)0);
}

int is_unconstrained(Symbol typ)					 /*;is_unconstrained*/
{
	Symbol	discr;
	Fortup	ft1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  is_unconstrained");

	/*TBSL: check translation of this*/
	if	(NATURE(typ) == na_array) return TRUE;
	if (NATURE(typ) != na_record ) 
		if(!in_incp_types(TYPE_OF(typ))) return FALSE;
	/* Some discriminant has no default value.*/
	FORTUP(discr=(Symbol), (Tuple) discriminant_list(typ), ft1);
		if (discr == symbol_constrained) continue;
		if ((Node) default_expr(discr) == OPT_NODE ) return TRUE;
	ENDFORTUP(ft1);
	return FALSE;
}

Symbol base_type(Symbol name) /*;base_type*/
{
	Symbol	b;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  base_type");

	/* It is possible to define subtypes of scalar subtypes. The base type
	 * is then obtained by following the subtype chain until we reach a type
	 */
	if (NATURE(name) == na_subtype) {
		b = TYPE_OF(name);
		while (NATURE(b) == na_subtype && b != name) {
			name = b;
			b = TYPE_OF(name);
		}
		return b;
	}
	else if (NATURE(name) == na_record || NATURE(name) == na_array)
		/* The type_of the array is its base type (it can be itself).*/
		return TYPE_OF(name);
	else
		return name;
}

Symbol named_type(char *name)  /*;named_type*/
{
	/* calls corresponding to the SETL named_type(str newat) send  & as first
	 * character, so that they can be detected by the macro is_anonymous
	 */

	Symbol	type_name;
	static int tint=0;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  named_type");

	/* This procedure is invoked when an anonymous type can be given a name
	 * that relates to its nature (e.g the base type of a derived type).
	 */
	/* this is now obsolete -- newat_str() has already generated a unique string
	 *	tint +=1;
	 *	name = emalloc(6); -- t + 4 digits + null 
	 *	sprintf(name, "t%04d", tint);
	 */
	type_name =  sym_new(na_type);
	ORIG_NAME(type_name) = name;
	dcl_put(DECLARED(scope_name), name, type_name);
	SCOPE_OF(type_name) = scope_name;
	return type_name;
}

Symbol anonymous_type()									 /*;anonymous_type*/
{
	/* This procedure is called to produce a new identifier for an anonymous
	 * type. The new identifier is inserted into the symbol table, and into
	 * the type stack.
	 */

	Symbol	new_name;
	Tuple	t;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  anonymous_type");

	new_name = named_atom("&anon");
	dcl_put(DECLARED(scope_name), str_newat(), new_name );
	SCOPE_OF(new_name) = scope_name;
	t = (Tuple) newtypes[tup_size(newtypes)];
	newtypes[tup_size(newtypes)] = (char *) tup_with(t, (char *) new_name);
	return new_name;
}

Symbol named_atom(char *id)									 /*;named_atom*/
{
	/* This procedure uses the unique name generated for a compilation
	 * unit to produce new names that will be unique throughout a library,
	 * especially one containing more than one AIS file.
	 */
	/* In C this returns a Symbol - the details of naming it are to
	 * be resolved later		ds 4 aug
	 */

	Symbol	s;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  named_atom");

	s = sym_new(na_void);
	ORIG_NAME(s) = strjoin(id, "");
	return s;
#ifdef TBSN
	??     return

	    if unit_name(1) = 'body' then 'UB:' else '' end
	+/[unit_name(i) + '.' : i in [#unit_name, #unit_name-1..3]]
	    + unit_name(2)
	    + if unit_name(2) = '' then '' else '.' end
	    + id
	    + str newat;
#endif
}

int is_static_expr(Node node)							 /*;is_static_expr*/
{
	/* note - use statc since static is C keyword */
	int	statc, nat, nk;
	Fortup	ft1;
	Node	parm_node, gen_agg, aggregate, expression, opn;
	Node	arg2, attr, type_node;
	int	attrkind;
	Symbol n, prefix_type;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC:is_static_expr ");

	if (N_TYPE(node) == symbol_any)	/* previous error */
		return TRUE;

	nk = N_KIND(node);

	if (nk == as_ivalue  || nk == as_int_literal
	  || nk == as_real_literal || nk == as_character_literal)
		statc = TRUE;
	else if (nk == as_simple_name) {
		nat = NATURE(N_UNQ(node));
		if (nat == na_literal) statc = TRUE;
		else if (nat == na_constant)
			statc = is_static_expr((Node) SIGNATURE(N_UNQ(node)));
		else
			statc = FALSE;
	}
	else if (nk == as_un_op || nk == as_op) {
		statc = TRUE;
		opn = N_AST1(node);
		gen_agg = N_AST2(node);
		if ((N_UNQ(opn) == symbol_andthen)
		  || (N_UNQ(opn) == symbol_orelse))
			statc = FALSE;
		FORTUP(parm_node =(Node), N_LIST(gen_agg), ft1);
			if (! is_static_expr(parm_node))
				statc = FALSE;
		ENDFORTUP(ft1);
	}
	else if (nk == as_attribute) {
		attr = N_AST1(node);
		type_node = N_AST2(node);
		arg2 = N_AST3(node);
		attrkind = (int) attribute_kind(node);

		if (attrkind == ATTR_O_RANGE
		  || attrkind == ATTR_T_RANGE
		  || attrkind == ATTR_RANGE
		  || attrkind == ATTR_O_LENGTH
		  || attrkind == ATTR_T_LENGTH
		  || attrkind == ATTR_LENGTH
		  || attrkind == ATTR_FIRST_BIT
		  || attrkind == ATTR_LAST_BIT
		  || attrkind == ATTR_POSITION
		  || attrkind == ATTR_TERMINATED
		  || attrkind == ATTR_COUNT
		  || attrkind == ATTR_CONSTRAINED
		  || attrkind == ATTR_STORAGE_SIZE )
			return FALSE;

		if (N_KIND(type_node) != as_simple_name)
			prefix_type = N_TYPE(type_node);
		else {
			n = N_UNQ(type_node);
			if (is_type(n))
				prefix_type = n;
			else
				prefix_type = TYPE_OF(n);
		}
		if (is_generic_type(prefix_type))
			statc = FALSE;
		else {
			if (attrkind == ATTR_O_FIRST
			  || attrkind == ATTR_T_FIRST
			  || attrkind == ATTR_FIRST
			  || attrkind == ATTR_O_LAST
			  || attrkind == ATTR_T_LAST
			  || attrkind == ATTR_LAST) {
				if (is_array(prefix_type) )
					statc = FALSE;
				else
					statc = is_static_subtype(prefix_type);
			}
			else if (attrkind == ATTR_POS
			  || attrkind == ATTR_VAL 
			  || attrkind == ATTR_SUCC
			  || attrkind == ATTR_PRED
			  || attrkind == ATTR_IMAGE
			  || attrkind == ATTR_VALUE ) {
				statc = is_static_subtype(prefix_type) &
				  is_static_expr(arg2);
			}
			else if (attrkind == ATTR_SIZE) {
				if (N_KIND(type_node) == as_attribute 
				  && (int) attribute_kind(type_node) == ATTR_RANGE)
					errmsg("Invalid argument for attribute SIZE", "Annex A",
					  type_node);
				statc = is_static_subtype(prefix_type);
			}
			else
				/* May need further refinement. */
				statc = TRUE;
		}
	}
	else if (nk == as_range_attribute)
		statc = FALSE;
	else if (nk == as_qualify) {
		/*type_mark = N_AST1(node); set but never used	ds 18 aug*/
		aggregate = N_AST2(node);
		statc = is_static_expr(aggregate);
	}
	else if (nk == as_parenthesis || nk == as_qual_range) {
		expression = N_AST1(node);
		statc = is_static_expr(expression);
	}
	else
		statc = FALSE;

	return statc;
}

/* the following function return FALSE if we have an array object
    declaration whose index subtypes are static. This will avoid
    the generation of n types (and n types templates) where n is
    the size of the object list */

static int reformat_requires(Node node_param) /*;reformat_requires*/
{
	Node	node, node1, ln;
	Fortup ftp1;

	if (N_KIND (node_param) == as_subtype_indic) {
		node = N_AST2 (node_param);
		if (N_KIND (node) != as_constraint ) 
			return TRUE; 
		if (N_LIST (node) == (Tuple) 0) 
			return TRUE; 
		FORTUP (ln= (Node), N_LIST (node), ftp1);
			if (N_KIND (ln) != as_subtype)
				return TRUE;
			node1 = N_AST2 (ln);
			if (N_KIND (node1) != as_range) 
				return TRUE;
			if (!is_static_expr (N_AST1 (node1))
			  || !is_static_expr (N_AST2 (node1)))
				return TRUE;
		ENDFORTUP (ftp1);
		return FALSE;
	}
	else
		return TRUE;
}
