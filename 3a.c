/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "3.h"
#include "attr.h"
#include "arithprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "dclmapprots.h"
#include "nodesprots.h"
#include "errmsgprots.h"
#include "evalprots.h"
#include "setprots.h"
#include "chapprots.h"

extern int *ADA_MIN_FIXED_MP, *ADA_MAX_FIXED_MP;

static void const_redecl(Node, Node, Node);
static Symbol set_type_mark(Tuple, Node);
static void build_type(Symbol, Node, Node);
static void derived_type(Symbol, Node);
static void build_derived_type(Symbol, Symbol, Node);
static int in_unconstrained_natures(int);
static int is_derived_type(Symbol);
static void derive_subprograms(Symbol, Symbol);
static void derive1_subprogram(Symbol, Symbol, Symbol, Symbol);
static int hidden_derived(Symbol, Symbol);
static Symbol find_neq(Symbol);
static void new_enum_type(Symbol, Node);
static void new_integer_type(Symbol, Node);
static void new_floating_type(Symbol, Node);
static void new_fixed_type(Symbol, Node);
static Node real_bound(Node, Symbol);
static Symbol constrain_scalar(Symbol, Node);

void obj_decl(Node node)									 /*;obj_decl*/
{
	/* Process variable declaration. Verify that the type is a constrained one,
	 * or that default values exist for the discriminants of the type.
	 */

	Node id_list_node, type_indic_node, init_node, id_node, node1;
	Symbol	type_mark, t_m, n;
	int i;
	Tuple	nam_list, id_nodes;
	Fortup	ft1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : obj_decl");

	id_list_node  = N_AST1(node);
	type_indic_node	 = N_AST2(node);
	init_node = N_AST3(node);

	id_nodes = N_LIST(id_list_node);
	nam_list = tup_new(tup_size(id_nodes));
	FORTUPI(id_node =(Node) , id_nodes, i,  ft1);
		nam_list[i] = (char *) find_new(N_VAL(id_node));
	ENDFORTUP(ft1);
	type_mark = set_type_mark(nam_list, type_indic_node);

	current_node = type_indic_node;
	check_fully_declared(type_mark);
	adasem(init_node);

	/* If an initialization is provided, verify it has the specified type.  */
	if (init_node != OPT_NODE)
		t_m = check_init(type_indic_node, init_node);

	if (is_unconstrained(type_mark)) {
		errmsg_nat("Unconstrained % in object declaration", type_mark,
		  "3.6.1, 3.7.2", type_indic_node);
	}

	/*(forall n in nam_list) nature(n) := na_obj; end forall;*/
	FORTUP(n=(Symbol), nam_list, ft1);
		NATURE(n) = na_obj;
	ENDFORTUP(ft1);
	for (i = 1; i <= tup_size(id_nodes); i++) {
		node1 = (Node) id_nodes[i];
		N_UNQ(node1) = (Symbol) nam_list[i];
	}
}

void const_decl(Node node)							  /*;const_decl*/
{
	/* Process constant declarations. This may be a new declaration, or the
	 * full declaration of a deferred constant in the private part of a
	 * package. In this later case, recover the names of the constants, and
	 * update their definitions.
	 */

	Node	id_list_node, type_indic_node, init_node, id_node;
	Tuple	id_nodes, id_list, nam_list;
	Symbol	type_mark, t_m, n;
	char	*id;
	int	i, exists;
	Fortup	ft1;
	Symbol	s;

	if (cdebug2 > 3)  TO_ERRFILE("AT PROC : const_decl");

	id_list_node = N_AST1(node);
	type_indic_node = N_AST2(node);
	init_node = N_AST3(node);

	id_nodes = N_LIST(id_list_node);
	id_list = tup_new(tup_size(id_nodes));
	FORTUPI(id_node =(Node), id_nodes, i, ft1);
		id_list[i] = N_VAL(id_node);
	ENDFORTUP(ft1);
	adasem(init_node);

	if (NATURE(scope_name) == na_private_part) {
		exists = FALSE;
		FORTUP(id=, id_list, ft1);
			if (dcl_get(DECLARED(scope_name), id) != (Symbol)0) {
				exists = TRUE;
				break;
			}
		ENDFORTUP(ft1);
		if (exists ){
			/* It must be a deferred constant. */
			const_redecl(id_list_node, type_indic_node, init_node);
			return;
			/* Otherwise it is a fully private constant. */
		}
	}

	nam_list = tup_new(tup_size(id_list));
	FORTUPI(id =, id_list, i, ft1);
		nam_list[i] = (char *) find_new(id);
	ENDFORTUP(ft1);

	type_mark = set_type_mark(nam_list, type_indic_node);

	if (init_node == OPT_NODE) {
		/* Deferred constant.*/
		s = TYPE_OF(base_type(type_mark));
		if (s != symbol_private && s != symbol_limited_private) {
			errmsg("Missing initialization in constant declaration", "3.2",
			  node);
		}
		else if (SCOPE_OF(type_mark) != scope_name) {
			errmsg("Wrong scope for type of deferred constant", "7.4",
			  type_indic_node);
		}
		else if ( (NATURE(scope_name) != na_package_spec)
		  && (NATURE(scope_name) != na_generic_package_spec) ) {
			errmsg("Invalid context for deferred constant", "3.2, 7.4", node);
		}
		else if (is_generic_type(type_mark)
		  || is_generic_type(base_type(type_mark))) { 
			errmsg("constants of a generic type cannot be deferred", "12.1.2",
			  node);
		}
		else if (is_anonymous(type_mark)) {
			errmsg("a deferred constant must be defined with a type mark",
			  "7.4.3", node);
		}
	}
	else {
		t_m = check_init(type_indic_node, init_node);

		if (t_m != type_mark) {
			/* t_m is an anonymous type created from the bounds of init value*/
			FORTUP(n = (Symbol), nam_list, ft1);
				TYPE_OF(n) = t_m;
			ENDFORTUP(ft1);
		}
	}

	FORTUP(n =(Symbol), nam_list, ft1);
		NATURE(n) = na_constant;
		SIGNATURE(n) = (Tuple) init_node;
	ENDFORTUP(ft1);
	for (i = 1; i <= tup_size(id_nodes); i++) {
		Node tmp = (Node) id_nodes[i];
		N_UNQ(tmp) = (Symbol) nam_list[i];
	}
}

static void const_redecl(Node id_list_node, Node type_indic_node,
  Node init_node)											 /*;const_redecl*/
{
	/* Process the full declaration of deferred constants. at least one id
	 * in  id_list is know to have been declared in the visible part of the
	 * current scope.
	 */

	Symbol	u_n, t_m, type_mark;
	Symbol	ut;
	Node	id_node, tmp;
	Tuple	id_nodes, nam_list, id_list;
	char	*id;
	int	i;
	Fortup	ft1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : const_redecl");

	id_nodes = N_LIST(id_list_node);
	id_list = tup_new(tup_size(id_nodes));
	FORTUPI(id_node =(Node), id_nodes, i, ft1);
		id_list[i]  = N_VAL(id_node);
	ENDFORTUP(ft1);
	nam_list = tup_new(0);
	/* The type indication must be a subtype indication .*/

	if (N_KIND(type_indic_node) == as_subtype_indic) {
		adasem(type_indic_node);
		type_mark = promote_subtype(make_subtype(type_indic_node));
	}
	else
		/* An anonymous array is syntactically possible, but incorrect. */
		type_mark = anonymous_array(type_indic_node);

	N_UNQ(type_indic_node) = type_mark;

	FORTUP(id =, id_list, ft1);
		u_n = dcl_get(DECLARED(scope_name), id);
		if (u_n == (Symbol)0) {
			errmsg_str("% is not a deferred constant", id, "3.2, 7.4",
			  id_list_node);
			nam_list = tup_with(nam_list, (char *)symbol_any);
			continue;
		}
		else if((NATURE(u_n) != na_constant)
	      || ((Node) SIGNATURE(u_n) != OPT_NODE)) {
			errmsg_str("Invalid redeclaration of %", id, "8.3", id_list_node);
			nam_list = tup_with(nam_list, (char *)symbol_any);
			continue;
		}
		else if ( ((ut = TYPE_OF(u_n)) != type_mark)
	      /* They may still be the same subtype of some private type.*/
		  && (TYPE_OF(ut) != TYPE_OF(type_mark))
		  || (SIGNATURE(ut) != SIGNATURE(type_mark)))
		{
			errmsg_str("incorrect type in redeclaration of %", id,
			  "7.4, 7.4.1", id_list_node);
			nam_list = tup_with(nam_list, (char *)symbol_any);
		}
		else if (init_node == OPT_NODE) {	/* No initiali(zation ? */
			errmsg_str("Missing initialization in redeclaration of %", id,
			  "7.4", id_list_node);
			nam_list = tup_with(nam_list, (char *)symbol_any);
		}
		else {
			TO_XREF(u_n);
			nam_list = tup_with(nam_list, (char *)  u_n);
		}
	ENDFORTUP(ft1);

	for (i = 1; i <= tup_size(id_nodes); i++) {
		tmp = (Node) id_nodes[i];
		N_UNQ(tmp ) = (Symbol) nam_list[i];
	}

	if (init_node != OPT_NODE ) {
		t_m = check_init(type_indic_node, init_node);
		FORTUP(u_n=(Symbol), nam_list, ft1);
			SIGNATURE(u_n) = (Tuple) init_node;
		ENDFORTUP(ft1);
	}
}

static Symbol set_type_mark(Tuple nam_list, Node type_indic_node)
															/*;set_type_mark*/
{
	/* Set the symbol table entry for object or constant declarations.
	 * The type indication is a subtype indication or an array definition. In
	 * the later case, an anonymous array type must be created for each item
	 * in the name list. For the interpreter, any of these types will do.
	 */

	Symbol	type_mark, n;
	Fortup	ft1;

	if (N_KIND(type_indic_node) == as_subtype_indic) {
		adasem(type_indic_node);
		type_mark = promote_subtype(make_subtype(type_indic_node));
		FORTUP(n=(Symbol), nam_list, ft1);
			TYPE_OF(n) = type_mark;
		ENDFORTUP(ft1);
	}
	else {
		n = (Symbol) nam_list[1];
		type_mark = anonymous_array(type_indic_node);
		TYPE_OF(n) = type_mark;
	}

	N_UNQ(type_indic_node) = type_mark;
	return type_mark;
}

Symbol check_init(Node type_indic_node, Node init_node)	/*;check_init*/
{
	/* Validate the initialization of an object or constant declaration.
	 * Return the resolved expression, and the type (or a subtype of it
	 * in the case of constants of unconstrained type).
	 */
	Symbol	type_mark;
	Tuple	init_array;
	Fortup	ft1;
	int	lo_val, hi_val;
	Tuple	new_indices, tup;
	Symbol	index, new_index, new_array;
	Node	lo, hi;

	type_mark = N_UNQ(type_indic_node);

	if (is_limited_type(type_mark)) {
		errmsg("Initialization not available for entities of limited type",
		  "7.4.4", type_indic_node);
	}

	check_type(type_mark, init_node);

	if (NATURE(type_mark) == na_array && type_mark == symbol_string
	  && (N_KIND(init_node) == as_string_ivalue )) {
		/* Constant definition with unconstrained type: bounds are given by 
   		 * an aggregate :  Create an anonymous subtype using  bounds of
		 * aggregate.  Currently supported for strings only. 
    	 */
		init_array = (Tuple) N_VAL(init_node);

		new_indices = tup_new(0);
		/* Unpack aggregate to obtain actual bounds on each dimension,
    	 * and create constrained index for each.
		 * TBSL.
		 */
		FORTUP(index=(Symbol), (Tuple)index_types(type_mark), ft1);
			if (N_KIND(init_node) == as_string_ivalue  
		   	  && base_type(type_mark) == symbol_string) {
				lo_val = 1;
				hi_val = tup_size( init_array);
			}
			else
				tup = init_array;
				/* TBSL */

			new_index = anonymous_type(); /* Its new subtype. */

			lo = new_ivalue_node(int_const(lo_val), symbol_integer);
			hi = new_ivalue_node(int_const(hi_val), symbol_integer);

			NATURE(new_index)  = na_subtype;
			TYPE_OF(new_index) = index;
			{ 
				Tuple t;
				t = constraint_new(CONSTRAINT_RANGE);
				numeric_constraint_low(t) = (char *) lo;
				numeric_constraint_high(t) = (char *) hi;
				SIGNATURE(new_index) = (Tuple) t;
			}
			root_type(new_index) = root_type(index);
			new_indices = tup_with(new_indices, (char *) new_index);
		ENDFORTUP(ft1);
		new_array = anonymous_type();
		NATURE(new_array) = na_subtype;
		TYPE_OF(new_array) = type_mark;
		{ 
			Tuple t; 
			t = tup_new(2);
			t[1] = (char *) new_indices;
			t[2] = (char *) component_type(type_mark);
			SIGNATURE(new_array) = t;
		};
		root_type(new_array) = root_type(type_mark);
		misc_type_attributes(new_array) = misc_type_attributes(type_mark);

		type_mark = new_array;
		N_TYPE(init_node) = type_mark;
		N_UNQ(type_indic_node) = type_mark;
	}
	return type_mark;
}

int is_deferred_constant(Node con_node)				/*;is_deferred_constant*/
{
	return
	  (N_KIND(con_node) == as_simple_name)
	  && (NATURE(N_UNQ(con_node)) == na_constant)
	  && ((Node) SIGNATURE(N_UNQ(con_node)) == OPT_NODE);
}

void number_decl(Node node) /*;number_decl*/
{
	/* A number declaration differs from a constant declaration in that
	 * the type of the declared object is a universal numeric type, obtained
	 * from the value of the  literal expression supplied for it.
	 * No intermediate code is generated for these: they act as macros,
	 * and are always represented by their value.
	 */

	Node	id_list_node, expn, id_node;
	Symbol	number_type, n;
	Tuple	nam_list;
	Fortup	ft1;
	int	i;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : number_decl");

	id_list_node = N_AST1(node);
	expn = N_AST2(node);

	nam_list = tup_new(tup_size(N_LIST(id_list_node)));
	FORTUPI(id_node =(Node), N_LIST(id_list_node), i, ft1);
		nam_list[i] = (char *)find_new(N_VAL(id_node));
	ENDFORTUP(ft1);
	adasem(expn);
	check_type_u( expn);
	number_type = N_TYPE(expn);
	if (! is_static_expr(expn)) {
		errmsg("Expect literal expression in number declaration", "3.2", expn);
		number_type = symbol_any;
	}

	FORTUP(n=(Symbol), nam_list, ft1);
		/*??SYMBTAB(n) = [na_constant, number_type, expn];*/
		NATURE(n) = na_constant;
		TYPE_OF(n) = number_type;
		SIGNATURE(n) = (Tuple) expn;
	ENDFORTUP(ft1);
}

void type_decl(Node node)	 /*;type_decl*/
{
	/* Process a type declaration. Create new name for type, or find unique
	 * name already given for incomplete declaration.
	 */

	Node	id_node, opt_disc, type_def;
	Symbol	type_name, kind, d_type;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : type_decl");

	id_node = N_AST1(node);
	opt_disc = N_AST2(node);
	type_def  = N_AST3(node);

	type_name = find_type_name(id_node);
	sem_list(opt_disc);

	if (type_name == symbol_any) return;	/* Invalid redeclaration, etc. */

	root_type(type_name) = type_name; 	/* initial value */

	if (opt_disc != OPT_NODE) {
		if ( in_incp_types(TYPE_OF(type_name)))
			/* Full declaration of incomplete or private type. Verify that
			 * discriminant declarations are conforming .
			 */
			discr_redecl(type_name, opt_disc);
		else if (N_KIND(type_def) == as_derived_type)
			NATURE(type_name) = na_record;
	}
	else if (in_incp_types(TYPE_OF(type_name)) && has_discriminants(type_name)){
		errmsg("missing discriminants in full type declaration", "3.8", node);
	}

	kind = TYPE_OF(type_name);

	build_type(type_name, opt_disc, type_def);

	if (opt_disc != OPT_NODE && !is_record(type_name)) {
		errmsg("Invalid use of discriminants", "3.7.1", opt_disc);
	}
	if ((N_KIND(type_def) == as_int_type || N_KIND(type_def) == as_float_type
	  || N_KIND(type_def) == as_fixed_type)
	  ||( N_KIND(type_def) == as_derived_type
	  && NATURE(type_name) == na_subtype)) {
		/* these declarations generate an anonyous parent type. The named
		 * type is actually a subtype.
		 */
		N_KIND(node) = as_subtype_decl;
		/* preserve subtype info in n_ast3 by moving to n_ast2 
		 * Since none of these types have a discriminant 
		 * no information is lost.
		 */
		N_AST2(node) = N_AST3(node);
		N_AST3(node) = (Node)0; /* subtype_decl has no n_ast3 */
	}
	current_node = id_node;
	/* recall that priv_types is {limited, limited_private} */
	/* check_priv_decl first argument is one of MISC_TYPE_ATTRIBUTE ...*/
	if (kind == symbol_private)
		check_priv_decl(TA_PRIVATE, type_name);
	else if (kind == symbol_limited_private)
		check_priv_decl(TA_LIMITED_PRIVATE, type_name);

	else if (kind == symbol_incomplete && S_UNIT(type_name) != unit_number_now){
		/* case of an incomplete type in the private part of a package, whose
		 * complete definition is given in the package body. Create a dummy
		 * symbol to which the complete definition is attached. The expander
		 * retrieves it and updates the symbol table of type_name accordingly.
		 */
		d_type = sym_new(NATURE(type_name));
		N_TYPE(node) = d_type;
		TYPE_OF(d_type)	= TYPE_OF(type_name);
		SIGNATURE(d_type) = SIGNATURE(type_name);
		OVERLOADS(d_type) = OVERLOADS(type_name);
		SCOPE_OF(d_type) = scope_name;
		root_type(d_type) = root_type(type_name);
		dcl_put(DECLARED(scope_name), newat_str(), d_type);
	}
	check_delayed_type(node, type_name);  /* if it has a private ancestor. */
}

Symbol find_type_name(Node id_node)				 /*;find_type_name*/
{
	/* Create a unique  name for a type  definition, or find  the unique name
	 * already created, in the case of the	full declaration of an incomplete
	 * or  private type. 
	 */

	char	*id;
	Symbol	incomplete, type_name, a_t;
	Forset fs1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : find_type_name");

	id = N_VAL(id_node);

	/* Find incomplete declaration, if some was given. */

	incomplete = dcl_get(DECLARED(scope_name), id);

	if (incomplete == (Symbol)0)		/* New type declaration. */
		type_name = find_new(id);
	else {								/* Previous declaration exists.*/
		if (id != (char *)0 && streq(id, "any_id")) {
			/* any_id identifier was inserted (by parser) */
			N_UNQ(id_node) = symbol_any;
			return symbol_any;
		}
		type_name = incomplete;
		TO_XREF(incomplete);
		if (!in_incp_types(TYPE_OF(incomplete))) {
			errmsg_str("Invalid redeclaration of %", id, "8.3", id_node);
			type_name = symbol_any;
		}
		if (TYPE_OF(incomplete) == symbol_incomplete) {
			if(private_dependents(incomplete)) {
				FORSET(a_t = (Symbol), private_dependents(incomplete), fs1)
					if (is_access(a_t) && SCOPE_OF(a_t) == scope_name)
						/* access type is now dereferenceable.*/
						misc_type_attributes(a_t)
						  = (int) misc_type_attributes(a_t) & ~TA_INCOMPLETE;
				ENDFORSET(fs1)
			}
		}
		else {
			/* Full declaration for private type. Save visible declaration in
			 * private decls for this package, so that full declaration can
			 * be installed.
			 */
			private_decls_put((Private_declarations) private_decls(scope_name),
			  type_name);

			if (is_generic_type(incomplete)) {
				errmsg_l_str("Generic private type % cannot have declaration ",
				  "in private part", id, "12.1", id_node);
				type_name = symbol_any;
			}
		}
	}
	N_UNQ(id_node) = type_name;
	return type_name;
}

static void build_type(Symbol type_name, Node opt_disc, Node type_def)
																/*;build_type*/
{
	/* For scalar types, both generic and non-generic, this procedure  simply
	 * constructs the symbol table entry on the basis of the type definition.
	 * Enumeration	types, array  types and	 derived  types	 require  further
	 * processing. They generate additional symbol table entries for literals
	 * and anonymous types.
	 */

	Symbol	parent, desig_type;
	int	l;
	Node	type_indic_node;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : build_type");

	switch (N_KIND(type_def)) {
	case as_enum:
		new_enum_type(type_name, type_def);
		break;
	case as_int_type:
		new_integer_type(type_name, type_def);
		break;
	case as_float_type:
		new_floating_type(type_name, type_def);
		break;
	case as_fixed_type:
		new_fixed_type(type_name, type_def);
		break;
	case as_array_type:
		new_array_type(type_name, type_def);
		break;
	case as_record:
		record_decl(type_name, opt_disc, type_def);
		break;
	case as_derived_type:
		derived_type(type_name, type_def);
		break;
	case as_access_type:
		adasem(type_def);
		type_indic_node = N_AST1(type_def);
		desig_type = N_UNQ(type_indic_node);
		if (type_name == desig_type)
		errmsg_id("Invalid use of type % before its full declaration",
		  type_name, "3.8.1", type_indic_node);
		/*??SYMBTAB(type_name) :=[na_access, type_name, desig_type];*/
		NATURE(type_name)    = na_access;
		TYPE_OF(type_name)   = type_name;
		SIGNATURE(type_name) = (Tuple) desig_type;
		new_agg_or_access_acc(type_name);
		break;
	}
	/* The new type inherits the root type and other attributes of its parent */

	parent = TYPE_OF(type_name);

	/*root_type(type_name) = root_type(parent) ? parent;*/
	if (root_type(parent) != (Symbol)0)
		root_type(type_name) = root_type(parent);
	else root_type(type_name) = parent;

	misc_type_attributes(type_name) = misc_type_attributes(parent);
	l = private_kind(parent);
	if (l != 0) {
		if (misc_type_attributes(type_name) == 0)
			misc_type_attributes(type_name) = l;
		else 
			misc_type_attributes(type_name) = 
			  (int) misc_type_attributes(type_name) | l;
	}
}

void check_delayed_type(Node node, Symbol type_mark)	/*;check_delayed_type*/
{
	/* called for type and subtype declarations. If the type has a sub-
	 * component of a private type, elaboration of the type must be delayed
	 * until the private ancestor has been elaborated.
	 */

	Symbol	pr;
	Node	id_node, decl_node, ancestor_node;
	int		exists;

	pr = private_ancestor(type_mark);
	exists = FALSE;
	if (pr != (Symbol)0) exists = TRUE;
	else {
		if (NATURE(type_mark) == na_subtype) {
			pr = TYPE_OF(type_mark);
			if (TYPE_OF(pr) == symbol_incomplete)
				exists = TRUE;
		}
	}
	if (exists) {
		id_node = N_AST1(node);
		decl_node = copy_node(node);
		N_KIND(node) = as_delayed_type;
		ancestor_node = new_name_node(pr);
		N_AST1(node) = id_node;
		N_AST2(node) = ancestor_node;
		N_AST3(node) = decl_node;
	}
}

void subtype_decl(Node node)								 /*;subtype_decl*/
{
	/* Process  a subtype  declaration. id	is  the	 source	 id  of	 the  new
	 * entity, and subt  is the subtype indication. If the subtype indication
	 * does not include a constraint, subt is either an anonymous array, or a
	 * subtype  indication that fucntions  as a  renaming of  a type. In that
	 * case the  new id  denotes the  same entity,	and does  not needs a new
	 * symbol table entry,	except that  for conformance  purposes it  is not
	 * equivalent to the original type. For now we only introduce  a new sub-
	 * type in the case of scalar types.
	 */

	Node id_node, type_indic_node, constraint;
	char *id;
	Symbol name, subt, parent;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : subtype_decl");

	id_node = N_AST1(node);
	type_indic_node = N_AST2(node);

	constraint = N_AST2(type_indic_node);
	id = N_VAL(id_node);
	adasem(type_indic_node);
	subt = make_subtype(type_indic_node);

	/* The subtype may  be an  array  type which has already  been
	 * promoted to anonymous type. It may also be a type_mark without
	 * a constraint, i.e. a type name.In this case the new subtype is
	 * simply a  renaming of  the type, and	 we set	 its  unique name
	 * to be that type_mark.
	 */

	/* If the constraint is empty the subtype is simply a renaming. */
	if (constraint == OPT_NODE && (!is_scalar_type(subt)
	  || is_generic_type(subt))) {
		N_UNQ(id_node) = subt;
		dcl_put(DECLARED(scope_name), id, subt);
	}
	else {
		current_node = id_node;
		name = find_new(id);
		N_UNQ(id_node) = name;
		SYMBTABcopy(name, subt);
		if (NATURE(subt) == na_enum) {
			/* Do not recopy literal map */
			OVERLOADS(name) = (Set)0;
		}
		NATURE(name) = na_subtype;
		parent = TYPE_OF(name);
		root_type(name) = root_type(parent);
		misc_type_attributes(name) = misc_type_attributes(parent);
		check_delayed_type(node, name);

    	if (is_generic_type(base_type(parent))) {
#ifdef TBSL
       	   repr_stmt := ["delayed_repr", {name}];
#endif
		}
    	else if (already_forced(base_type(parent))) {
       		choose_representation(name);
		}
    	else {
       		not_chosen_put(base_type(parent), name);
		}

	}
	/* Discard the generated anonymous subtype.
	 * subt frome NEWTYPES;
	 * NEWTYPES with:= [];
	 */
}

Symbol make_subtype(Node type_indic_node)					  /*;make_subtype*/
{
	Node	name_node, constraint, selector;
	int		nat;
	Symbol	subtype, type_mark, d_type, d_sub;
	Tuple	sigtup;
	char	*type_id;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : make_subtype");

	/* Process a subtype indication.*/

	name_node = N_AST1(type_indic_node);
	constraint = N_AST2(type_indic_node);

	type_mark = find_type(name_node);

	if (type_mark== symbol_any) return symbol_any;

	/* Retrieve source identifier of type, for test below.*/
	if (N_KIND(name_node) == as_simple_name)
		type_id = N_VAL(name_node);
	else {					/* extended name */
		selector = N_AST2(name_node);
		type_id = N_VAL(selector);
	}

	if (in_open_scopes(base_type(type_mark)) && (! is_task_type(type_mark)
	  || strcmp(original_name(type_mark), type_id) == 0) ) {
		/* Component of record is subtype of record type itself, or task type
    	 * is used within its body.
    	 */
		errmsg_str("invalid use of type % within its definition or body",
		  type_id, "3.3, 9.1", name_node);
		return type_mark;
	}
	else if (constraint == OPT_NODE) {
		current_node = name_node;
		check_incomplete(type_mark);
		return type_mark;
	}
	else {
		/* If the type is a access type, the constraint applies to the type
    	 * being accessed. We create the corresponding subtype of it, promote
    	 * it to an anonymous type, and return an access to it.
    	 */

		nat = NATURE(type_mark);

		if (is_access(type_mark)) {
			d_type = (Symbol) designated_type(type_mark);

			if (NATURE(d_type) == na_array) {
				d_sub = constrain_array(d_type, constraint);
				root_type(d_sub) = root_type(d_type);
				subtype = named_type(strjoin("&", newat_str()));
				/*Create  a  name for it*/
				NATURE(subtype) = na_subtype;
				TYPE_OF(subtype) = type_mark;
				sigtup = constraint_new(CONSTRAINT_ACCESS);
				sigtup[2] = (char *) d_sub;
				SIGNATURE(subtype) = sigtup;
			}
			else if (is_record(d_type) && NATURE(d_type) != na_subtype) {
				d_sub = constrain_record(d_type, constraint);
				root_type(d_sub) = root_type(d_type);
				subtype = named_type(strjoin("&", newat_str()));
				/*Create  a  name for it*/
				NATURE(subtype) = na_subtype;
				TYPE_OF(subtype) = type_mark;
				sigtup = constraint_new(CONSTRAINT_ACCESS);
				sigtup[2] = (char *) d_sub;
				SIGNATURE(subtype) = sigtup;
			}
			else {
				errmsg("Invalid constraint on access type", "3.8", constraint);
				subtype = symbol_any;
			}
		}

		else if (nat == na_type) {
			if (is_scalar_type(type_mark))
				subtype = constrain_scalar(type_mark, constraint);
			else 	   /* Private type with discriminants, hopefully.*/
				subtype = constrain_record(type_mark, constraint);
		}
		else if (nat == na_enum)
			subtype = constrain_scalar(type_mark, constraint);
		else if (nat == na_array)
			subtype=constrain_array(type_mark, constraint);
		else if (nat == na_record)
			subtype = constrain_record(type_mark, constraint);
		else if (nat == na_subtype) {
			if (is_array(type_mark) || is_record(type_mark)) {
				errmsg(
				  "Invalid subtype indication: type is already constrained",
				  "3.6.1, 3.7.2", type_indic_node);
				subtype = symbol_any;
			}
			else
				subtype = constrain_scalar(type_mark, constraint);
		}
		else {
			errmsg_id("Invalid type mark in subtype indication: %",
			  type_mark, "3.3, 3.6.1", name_node);
			subtype = symbol_any;
		}
	}

	if (subtype != symbol_any)
		root_type(subtype) = root_type(type_mark);
	else
		N_AST2(type_indic_node) = OPT_NODE;
	return subtype;
}

static void derived_type(Symbol derived_subtype,Node def_node) /*;derived_type*/
{
	Node type_indic_node, constraint_node;
	Symbol subtype;
	Symbol parent_subtype, derived_type, parent_type;
	int		nat;
	Tuple 	constraint;

	if (cdebug2 > 3) TO_ERRFILE("derived type: ");

	type_indic_node = N_AST1(def_node);
	adasem(type_indic_node);
	subtype = make_subtype(type_indic_node);
	constraint_node = N_AST2(type_indic_node);
	if (constraint_node == OPT_NODE) {
		parent_subtype = subtype;
		constraint = (Tuple) SIGNATURE(parent_subtype);
		/* Inherited by new type*/
	}
	else {
		/* we use parent_subtype to designate the type mark in the subtype
    	 * indication. The code below makes sure that the constraint of the
    	 * parent subtype is also inherited by the derived subtype.
    	 */
		parent_subtype = TYPE_OF(subtype); /*Subtype indication.*/
		constraint = (Tuple) SIGNATURE(subtype); /* Subtype indication.*/
	}

	if (parent_subtype == subtype && (in_unconstrained_natures(NATURE(subtype))
	  /*   || (is_generic_type(subtype)) ||is_access(subtype)  */
	  ||in_priv_types(TYPE_OF(root_type(subtype))) ))	{
		derived_type = derived_subtype;
	}
	else {
		/* If the derived type definition includes a constraint, or if the
		 * old type is constrained, we first derive an anonymous type, and
		 * then construct a subtype of it. 
		 */
		derived_type = named_type(strjoin(original_name(derived_subtype),
		  "\'base"));
		{ 
			Tuple tmp = (Tuple) newtypes[tup_size(newtypes)];
			newtypes[tup_size(newtypes)] = 
			    (char *)tup_with(tmp, (char *) derived_type);

			NATURE(derived_subtype)    = na_subtype;
			TYPE_OF(derived_subtype)   = derived_type;
			SIGNATURE(derived_subtype) = (Tuple) constraint;
			not_chosen_put(derived_type, derived_subtype);
		}
	}
	root_type(derived_type) = derived_type; 		/* initially */

	parent_type = base_type(parent_subtype);
	nat = NATURE(SCOPE_OF(parent_type));
	/* A derived type defined in a prackage specification cannot be used for
	 * further derivation until the end of its visible part. 
	 */
	if (is_derived_type(parent_type) && (in_open_scopes(parent_type)
	  && (nat == na_package_spec || nat == na_generic_package_spec))
	  ||  TYPE_OF(parent_type) == symbol_incomplete
	  || private_ancestor(parent_type) != (Symbol)0 ) {
		errmsg_id("premature derivation of derived or private type %",
		  parent_type, "3.4, 7.4.1", type_indic_node);
	}
	build_derived_type(parent_subtype, derived_type , type_indic_node);
}

static void build_derived_type(Symbol parent_subtype, Symbol derived_type,
  Node node)										/*;build_derived_type */ 
{
	/* build symbol table entry for derived type, after processing constraint.
	 * called from previous procedure, and from update_one_entry, to handle
	 * types derived from generic formal types.
	 */

	Symbol parent_type, parent_scope;
	Symbol comp;
	int	exists, nat1, i, l;
	Forset	fs;
	Symbol new_lit_name, lit_sym, nam;
	Symbol	d1, d2;
	char	*lit_id;
	Tuple new_sig, lit_map, dl1, dl2, array_info;
	Declaredmap	parent_dcl;

	parent_type = base_type(parent_subtype);
	nat1 = NATURE(parent_type);

	switch (nat1 = NATURE(parent_type)) {
	case na_type:
		NATURE(derived_type)    = na_type;
		TYPE_OF(derived_type)   = parent_type;
		SIGNATURE(derived_type) = SIGNATURE(parent_type);
		break;
	case na_array:
		array_info = SIGNATURE(parent_type);
		/* The following code is very similar to new_unconstrained_array but
		 * avoids building a tree fragment for the array and then unpacking it
		 */
		comp = (Symbol) array_info[2];
		NATURE(derived_type)    = na_array;
		TYPE_OF(derived_type)   = derived_type;
		SIGNATURE(derived_type) = array_info;
		/* Mark the type as limited if the component type is.*/
		misc_type_attributes(derived_type) = private_kind(comp);
		/* For each unconstrained array type, we introduce an instance of the
		 * 'aggregate' pseudo-operator for that array.
		 */
		new_agg_or_access_agg(derived_type);
		break;

	/* A derived record type has the same fields and types as the parent.
	 * All we need to do is introduce an aggregate under the new type mark.
	 * The declaration may have a discriminant part, in which case they
	 * must conform to the discriminants of the parent type. We assume that
	 * the discriminant names, types, and default values must be the same.
	 */
	case na_record:
		if (is_record(derived_type)) {
			dl1 = (Tuple) discriminant_list(derived_type);
			dl2 = (Tuple) discriminant_list(parent_type);
			exists = FALSE;
			if (tup_size(dl1) != tup_size(dl2)) {
				exists = TRUE;
				if (! exists) {
					for (i = 1; i <= tup_size(dl1); i++) {
						d1 = (Symbol) dl1[i]; 
						d2 = (Symbol) dl2[i];
						if (TYPE_OF(d1) != TYPE_OF(d2)
					   	  || default_expr(d1) != default_expr(d2) /*$tree equ?*/
						  || strcmp(original_name(d1),original_name(d2)) != 0) {
							exists = TRUE;
							break;
						}
					}
				}
				if (exists) {
					errmsg("discriminant mismatch in derived type declaration",
					  "3.8", node);
				}
			}
		}
		NATURE(derived_type) = na_record;
		TYPE_OF(derived_type) = derived_type;
#ifdef TBSL
		-- is it necessary to 'copy' SIGNATURE and/or DECLARED. 
	   	-- check this. For now, do copy for DECLARED	ds 6-jan-85
#endif
	    SIGNATURE(derived_type) = record_declarations(parent_type);
		DECLARED(derived_type) = DECLARED(parent_type);
		if (DECLARED(parent_type) != (Declaredmap) 0)
			DECLARED(derived_type) = dcl_copy(DECLARED(parent_type));
		new_agg_or_access_agg(derived_type);
		break;
	/* A derived enumeration type has the literals of its parent, but these
   	 * are marked as derived, to enforce the overloading rules.
   	 */
	case na_enum:
		lit_map = (Tuple) literal_map(parent_type);
		parent_scope = SCOPE_OF(parent_type);
		parent_dcl = DECLARED(parent_scope);
		/* Recall that literal map as tuple for now */
		for (i = 1; i <= tup_size(lit_map); i+=2) {
			lit_id = lit_map[i];
			/* retrieve unique_name of literal */
			lit_sym = dcl_get(parent_dcl, lit_id);
			FORSET(nam=(Symbol), OVERLOADS(lit_sym), fs)
		    	if (TYPE_OF(nam) == parent_type)
					break;
			ENDFORSET(fs)
		    new_lit_name =
		      chain_overloads(lit_id, na_literal, derived_type,
			  tup_new(0), nam, OPT_NODE);
			ALIAS(new_lit_name) = nam; /* unique name of parent */
		}
		new_sig = SIGNATURE(parent_type);
		NATURE(derived_type)    = na_enum;
		TYPE_OF(derived_type)   = derived_type;
		SIGNATURE(derived_type) = new_sig;
		OVERLOADS(derived_type) = (Set) lit_map;
		break;
	case na_access:
		NATURE(derived_type)    = na_access;
		TYPE_OF(derived_type)   = derived_type;
		SIGNATURE(derived_type) = SIGNATURE(parent_type);
		new_agg_or_access_acc(derived_type);
		break;
	case na_task_type:
	case na_task_type_spec:
		SYMBTABcopy(derived_type, parent_type);
		NATURE(derived_type)   = na_task_type; /*even if parent is spec*/
		DECLARED(derived_type) = DECLARED(parent_type);
		break;
	default:	/*previous error, unsupported numeric type, etc. */
		break;
	}

	root_type(derived_type) = root_type(parent_type);

	derive_subprograms(parent_subtype, derived_type);
	if (nat1 != na_enum) {
		l = private_kind(parent_type);
		misc_type_attributes(derived_type) = l;
		/* otherwise the attribute is the literal map*/
	}
inherit_representation_info(derived_type, parent_type);
}

static int in_unconstrained_natures(int x)		/*;in_unconstrained_natures*/
{
	/* equiv to x in unconstrained_natures ... */
	return x == na_enum || x == na_array || x == na_record || x == na_access
	  || x == na_task_type || x == na_task_type_spec;
}

static int is_derived_type(Symbol mark)  /*;is_derived_type*/
{
	return (base_type(mark) != root_type(mark) && (! is_generic_type(mark)));

	/* Incomplete for composite types.*/
}

static void derive_subprograms(Symbol parent_subtype, Symbol derived_type)
														/*;derive_subprograms*/
{
	/* In order to derive the subprograms of the parent type, the parent type
	 * must be defined in  the visible part of a package, and the derivation
	 * must take place after the end of this visible part.
	 *
	 * We introduce in the symbol table the new subprograms with the derived
	 * signature, but do not emit code for them. We produce instead a
	 * mapping from the inherited subprogram to its ancestor, and replace
	 * the name at the point of call, in macro-like fashion.
	 *
	 * If the  parent type is a private type whose full declaration is
	 * a first-named subtype, then  its base type is declared in the private
	 * part. Then if the derivation takes place in the private part itself,
	 * the parent type does not appear in the visible part of the package,
	 * but the parent subtype does. This anomaly must be checked for explicitly.
	 * checked for separately.
	 */

	Symbol	parent_scope, sym, obj;
	Symbol  parent_type;
	int	is_visible_type, nat;
	char	*str, *id;
	Fordeclared	div;
	Declaredmap decmap;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : derive_subprograms");

	parent_type  = base_type(parent_subtype);
	parent_scope = SCOPE_OF(parent_type);
	nat          = NATURE(parent_scope);
	is_visible_type = FALSE;
	decmap = (Declaredmap)(DECLARED(parent_scope));

	if ((nat == na_package || nat == na_package_spec)
	  && !in_open_scopes(parent_scope)) {
		/* common case: derivation outside of package.*/
		FORVISIBLE(str, sym, decmap, div)
		    if (sym == parent_type) {
				is_visible_type = TRUE;
				break;
			}
		ENDFORVISIBLE(div)
	}
	else if (nat == na_private_part
	  /* which is a currently open scope. */
	  || (nat == na_package && in_open_scopes(parent_scope))) {
		/* verify that parent SUBtype is declared in visible part. */
		FORVISIBLE(str, sym, decmap, div)
		    if (sym == parent_subtype) {
				is_visible_type = TRUE;
				break;
			}
		ENDFORVISIBLE(div)
	}
	if (is_visible_type) {	/* calculate inheritance.*/
		if (parent_scope == scope_name) {
			/* Derivation is in private part of package that declares the
			 * parent. Copy declared map to insure that domain of iteration of
			 * following loop is not modified by insertions of derived
			 * subprograms.
        	 */
			decmap = dcl_copy(decmap);
		}
		FORVISIBLE(id, obj, decmap, div)
		    nat = NATURE(obj);
			if((nat == na_procedure || nat == na_procedure_spec
		      || nat == na_function  || nat == na_function_spec)
		      && !is_derived_subprogram(obj))
				derive1_subprogram(obj, parent_type, derived_type, obj);
		ENDFORVISIBLE(div)
	}
	if (is_derived_type(parent_type) && parent_scope != symbol_standard0) {
		/* If the original type is a derived type, its derived subprograms
		 * are further derived. If such exist, they are aliased subprograms
		 * declared in the same scope as the parent type.
		 */
		if ( !is_visible_type && parent_scope == scope_name)
			decmap = dcl_copy(decmap);

		FORDECLARED(id, obj, decmap, div)
		    nat = NATURE(obj);
			if ((nat == na_procedure || nat == na_procedure_spec
		      || nat == na_function || nat == na_function_spec)
		      && is_derived_subprogram(obj)
		      && ( ! is_visible_type || ! hidden_derived(obj, parent_scope) ))
				derive1_subprogram(obj, parent_type, derived_type, ALIAS(obj));
		ENDFORDECLARED(div)
	}
}

static void derive1_subprogram(Symbol obj, Symbol parent_type,
  Symbol derived_type, Symbol parent_subp)				/*;derive1_subprogram*/
{
	/* obj is a subprogram declared in the same scope as parent_type. If
	 * some type in its profile is compatible with parent_type, produce
	 * a derived subprogram by replacing the parent_type with the derived
	 * one, and introduce a subprogram declaration with this new profile.
	 * The parent subprogram is either obj itself, or ALIAS(obj) if obj is
	 * already a derived subprogram.
	 */
	Symbol	new_typ, formal, tf, dx, new_proc;
	Symbol neq, new_neq;
	char	*id;
	int	is_new, nat;
	Fortup	ft1;
	Tuple	new_sig, t;

	new_sig = tup_new(0);
	new_typ = TYPE_OF(obj);
	is_new = FALSE;

	FORTUP(formal =(Symbol) , SIGNATURE(obj), ft1);
		nat = NATURE(formal);
		id = original_name(formal);
		tf = TYPE_OF(formal);
		dx = (Symbol) default_expr(formal);

		if (compatible_types(tf, parent_type)) {
			tf = derived_type;
			is_new = TRUE;
		}
		t = tup_new(4);
		t[1] =  strjoin(id, "");
		t[2] = (char *) nat;
		t[3] = (char *) tf;
		t[4] = (char *) dx;
		new_sig = tup_with(new_sig, (char *) t);
	ENDFORTUP(ft1);

	if (compatible_types(new_typ, parent_type) ) {
		new_typ = derived_type;
		is_new  = TRUE;
	}

	if (is_new) {
		/* subprogram is derived. Insert it in current scope, with
    	 * the new signature, and recall its lineage.
    	 * Its nature is a subprogram, not a spec, because no body
    	 * will be defined for it.
    	 */
		nat = NATURE(obj) == na_procedure_spec ? na_procedure : na_function;
		id = original_name(obj);

		/* If the subprogram is /=, it will be automatically derived when
		 * te corresponding equality operator is.
		 */
		if (streq(id, "/=")) return;
		/*new_proc = chain_overloads(id, [nat,new_typ, new_sig, parent_subp]);*/
		new_proc = chain_overloads(id, nat, new_typ, new_sig, parent_subp,
		  OPT_NODE);
		if (new_proc != (Symbol)0) { /* There is no explicit sub-*/
			ALIAS(new_proc) = parent_subp;	   /* program with that name.*/
			if (streq(id, "=")) {
				/* mark the parent of the corresponding inequality. */
				neq            = find_neq(parent_subp);
				new_neq        = find_neq(new_proc);
				ALIAS(new_neq) = neq;
			}
		}
	}
}

static int hidden_derived(Symbol subp, Symbol parent_scope)	/*;hidden_derived */
{
	/* Determine whether a derived subprogram is hidden by an explicit 
	 * declaration in the visible part of a package.
	 * If the derivation occurs within the private part of the package,  or
	 * within its body, the set of subprograms that may hide the derived one is
	 * the overloads set of the private declarations of the symbol. Otherwise
	 * it is  the overloads set of the visible symbol.
	 */

	Symbol seen, s;
	Forset fs1;
	Symbol obj;

	seen = dcl_get_vis(DECLARED(parent_scope), ORIG_NAME(subp));

	if (seen == (Symbol)0) return FALSE;

	else if ( in_open_scopes(parent_scope)
	  && NATURE(parent_scope) != na_package_spec 
	  && (s = private_decls_get((Private_declarations)
	  private_decls(parent_scope), seen)) != (Symbol)0 )
		seen = s;

	if (!can_overload(seen)) return FALSE;

	FORSET(obj=(Symbol), OVERLOADS(seen), fs1)
	    if ( obj != subp && same_signature(obj, subp)
	      && base_type(TYPE_OF(subp)) == base_type(TYPE_OF(obj)))
			return TRUE;
	ENDFORSET(fs1);
	return FALSE;
}

static Symbol find_neq(Symbol eq_name)						    /*;find_new*/
{
	/* find implicitly defined inequality corresponding to an equality operator,
	 * either explicitly defined or derived, by iterating over definitions of /=
	 * in the scope, that have the same signature as the given equality.
	 */

	Forset fs1;
	Symbol neq;

	FORSET(neq=(Symbol), OVERLOADS(dcl_get(DECLARED(SCOPE_OF(eq_name)), "/=")),
	  fs1)
	    if (same_signature(neq, eq_name)) {
		return neq;
	}
	ENDFORSET(fs1)
	chaos("can't find inequality operator in scope");
	return (Symbol)0;
}

int is_derived_subprogram(Symbol name)				 /*;is_derived_subprogram*/
{
	Symbol s;

	s = ALIAS(name);
	return (s != (Symbol)0 && streq(ORIG_NAME(s) , ORIG_NAME(name)) );
}

static void new_enum_type(Symbol type_name, Node def_node)  /*;new_enum_type*/
{
	Tuple c;
	Tuple	lit_map, literals_list;
	int	i;
	Node	lo, hi, tmpnode;

	adasem(def_node);
	literals_list = N_LIST(def_node);
	lit_map = tup_new(2*tup_size(literals_list));

	for (i = 1; i <= tup_size(literals_list); i++) {
		/* insert each literal in symbol table, as an overloadable identifier
		 * Each enumeration type is mapped  into a sequence	of integers, and
		 * each literal is defined as a constant with integer value.
		 */
		tmpnode = (Node)(literals_list[i]);
		chain_overloads(N_VAL(tmpnode), na_literal, type_name, tup_new(0),
		  (Symbol)0, OPT_NODE);
		/*    lit_map(N_VAL(literals_list(i))) := i-1;*/
		/*    lit_map[2*i-1] = (char *) N_VAL((Node)(literals_list[i]));*/
		lit_map[2*i-1] = N_VAL(tmpnode);
		lit_map[2*i] = (char *) i-1;
	}
	lo = new_ivalue_node(int_const(0), type_name);
	hi = new_ivalue_node(int_const(tup_size(literals_list) - 1), type_name);
#ifdef TBSN
	-- this should no longer be necessary, as they are saved in
	-- collect_unit_nodes
	/* Attach nodes of bounds to AST, to insure saving for separate 
	 * compilation.
	 */
	/*N_LIST(def_node) +:= [lo, hi];*/
	N_LIST(def_node) = tup_with(N_LIST(def_node), (char *) lo);
	N_LIST(def_node) = tup_with(N_LIST(def_node), (char *) hi);
#endif
	/*SYMBTAB(type_name) := [na_enum, type_name, ['range', lo, hi], lit_map];*/
	NATURE(type_name) = na_enum;
	TYPE_OF(type_name) = type_name;
	c = constraint_new(CONSTRAINT_RANGE);
	numeric_constraint_low(c) = (char *) lo;
	numeric_constraint_high(c) = (char *) hi;
	SIGNATURE(type_name) = (Tuple) c;
	OVERLOADS(type_name) = (Set) lit_map;
	initialize_representation_info(type_name, TAG_ENUM);
}

static void new_integer_type(Symbol type_name, Node def_node)
														/*;new_integer_type*/
{
	/* Create a new integer, and apply the constraint to obtain subtype of it.*/

	Symbol	newtype;
	Node constraint_node, lo, hi;
	Tuple	c;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : new_integer_type");

	constraint_node = N_AST1(def_node);
	adasem(constraint_node);

	newtype = anonymous_type();
	SYMBTABcopy(newtype, symbol_integer);
	root_type(newtype) = symbol_integer;
	inherit_representation_info(newtype, symbol_integer);

	/* get bounds of range : lo, hi.*/
	lo = N_AST1(constraint_node);
	hi = N_AST2(constraint_node);

	check_type_i(lo);
	check_type_i(hi);
	specialize(lo, symbol_integer);
	specialize(hi, symbol_integer);

	if (!(is_static_expr(lo)) || (! (is_static_expr(hi)))) {
		errmsg("Bounds in an integer type definition must be static",
		  "3.5.4", constraint_node);
	}
	else if (root_type(N_TYPE(lo)) != symbol_integer
	  || root_type(N_TYPE(hi)) != symbol_integer)	 {
		/* these are tests on the root type of each node.*/
		errmsg_l("Bounds in an integer type definition must be of some ",
		  "integer type", "3.5.4", constraint_node);
	}
	NATURE(type_name) = na_subtype;
	TYPE_OF(type_name) = newtype;
	c = constraint_new(CONSTRAINT_RANGE);
	numeric_constraint_low(c) = (char *) lo;
	numeric_constraint_high(c) = (char *) hi;
	SIGNATURE(type_name) = (Tuple) c;
	not_chosen_put(newtype, type_name);
}

static void new_floating_type(Symbol type_name, Node def_node)
														/*;new_floating_type*/
{
	Node	float_pt_node, precision_node, opt_range, lo, hi;
	Symbol	newtype, p_type;
	Symbol	anonymous_type();
	int	digits;
	Tuple constraint;
	Const	con;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : new_floating_type");

	/* Process a floating point declaration.*/
	float_pt_node = N_AST1(def_node);
	adasem(float_pt_node);

	precision_node = N_AST1(float_pt_node);
	opt_range = N_AST2(float_pt_node);

	/* The range constraint is optional. If absent, the range is that of
	 * the parent type. If present,	 the bounds  need not be of the same
	 * type, but of some real type, and static. Their resolution is done
	 * in procedure real-bound.
	 */

	newtype = anonymous_type();
	SYMBTABcopy(newtype, symbol_float);
	root_type(newtype) = symbol_float;
	SYMBTABcopy(type_name, newtype);	   /* by default.*/
	check_type_i(precision_node);
	p_type = N_TYPE(precision_node);

	if (p_type == symbol_any)  /* Type error.*/
		return;
	else if (! is_static_expr(precision_node)) {
		errmsg("Expect static expression for digits", "3.5.7", precision_node);
		return;
	}

	if (p_type == symbol_universal_integer)
		specialize(precision_node, symbol_integer);
	else if (root_type(p_type) != symbol_integer) {
		errmsg("Expect integer expression for DIGITS", "3.5.7", precision_node);
		return;
	}

	eval_static(precision_node);
	con = (Const) N_VAL(precision_node);
	digits = con->const_value.const_int;
	if (digits < 1) {
		errmsg("Invalid digits value in real type declaration", "3.5.7",
		  precision_node);
		return;
	}
	else if (digits > ADA_REAL_DIGITS) {
		errmsg("Precision not supported by implementation", "none",
		  precision_node);
		return;
	}

    inherit_representation_info(newtype, symbol_float);
	if (opt_range == OPT_NODE) {		/* Use system FLOAT.*/
		/* constraint = SIGNATURE(symbol_float);
		 * constraint(4) = precision_node;	
		 */
		Tuple sig = (Tuple) SIGNATURE(symbol_float);
		constraint = constraint_new(CONSTRAINT_DIGITS);
		numeric_constraint_low(constraint) = numeric_constraint_low(sig);
		numeric_constraint_high(constraint) = numeric_constraint_high(sig);
		numeric_constraint_digits(constraint) = (char *) precision_node;
	}
	else {
		lo = N_AST1(opt_range);
		hi = N_AST2(opt_range);

		if (real_bound(lo, symbol_float) == OPT_NODE) return;
		if (real_bound(hi, symbol_float) == OPT_NODE) return;

		constraint = constraint_new(CONSTRAINT_DIGITS);
		numeric_constraint_low(constraint) = (char *) lo;
		numeric_constraint_high(constraint) = (char *) hi;
		numeric_constraint_digits(constraint) = (char *) precision_node;
	}

	NATURE(type_name) = na_subtype;
	TYPE_OF(type_name) = newtype;
	SIGNATURE(type_name) = (Tuple) constraint;
	not_chosen_put(newtype, type_name);
}

static void new_fixed_type(Symbol type_name, Node def_node)  /*;new_fixed_type*/
{
	Node	lo, hi, fixed_pt_node, precision_node, opt_range, small_node;
	Symbol	r, p_type, anon_type;
	Tuple constraint;
	Rational small_val;
	Rational lo_val, hi_val, anon_lo_val, anon_hi_val;
	int	power_conv;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : new_fixed_type");

	/* Process a fixed point declaration. Similar to floating case.*/

	fixed_pt_node = N_AST1(def_node);
	adasem(fixed_pt_node);

	precision_node = N_AST1(fixed_pt_node);
	opt_range = N_AST2(fixed_pt_node);

	anon_type = anonymous_type();
	NATURE(anon_type)  = na_type;
	TYPE_OF(anon_type) = anon_type;
	root_type(anon_type) = symbol_dfixed;

	NATURE(type_name)    = na_subtype;
	TYPE_OF(type_name)   = anon_type;
#ifdef TBSL
	-- see if tup_copy needed for SIGNATURE assignments below
	    ds 6-jan-85
#endif
	SIGNATURE(anon_type) = SIGNATURE(symbol_dfixed);
	SIGNATURE(type_name) = SIGNATURE(symbol_dfixed);

    initialize_representation_info(anon_type, TAG_FIXED);
    not_chosen_put(anon_type, type_name);
	check_type_r(precision_node);
	p_type = N_TYPE(precision_node);

	if (N_TYPE(precision_node) == symbol_any)  /* Type error.*/
		return;
	else if (! is_static_expr(precision_node)) {
		errmsg("Expect static expression for delta", "3.5.7", precision_node);
		return;
	}

	r = root_type(p_type);
	if (is_fixed_type(r) || r == symbol_universal_real);
	else if (r == symbol_float)
		N_VAL(precision_node) = (char *) rat_const(rat_frr
		  (REALV((Const)N_VAL(precision_node))));
	else {
		errmsg("Expression for delta must be of some real type", "3.5.9",
		  precision_node);
		return;
	}

	if (opt_range == OPT_NODE) {
		errmsg("Missing range in Fixed type declaration", "3.5.9",
		  fixed_pt_node);
		return;
	}
	else {
		lo = N_AST1(opt_range);
		hi = N_AST2(opt_range);
		if (real_bound(lo, symbol_dfixed) == OPT_NODE)return;
		if (real_bound(hi, symbol_dfixed) == OPT_NODE) return;

		N_TYPE(lo) = N_TYPE(hi) = anon_type;

		lo_val = RATV((Const)N_VAL(lo));
		hi_val = RATV((Const)N_VAL(hi));
		/* The constraint may eventually carry a rep.spec. for 'SMALL. Its
		 * absence is marked by OPT_NODE.
		 */
		/*constraint := ['delta', lo, hi, precision_node, OPT_NODE];*/
		constraint = constraint_new(CONSTRAINT_DELTA);
		numeric_constraint_low(constraint)   = (char *) lo;
		numeric_constraint_high(constraint)  = (char *) hi;
		numeric_constraint_delta(constraint) = (char *) precision_node;
		numeric_constraint_small(constraint) = (char *) OPT_NODE;
		power_conv = power_of_2((Const) N_VAL(precision_node));
		small_val = power_of_2_small;
		if (power_conv) { /* if cannot convert */
			errmsg("Precision not supported by implementation.",
			  "Appendix F", fixed_pt_node);
		}
		else {
			small_node = new_ivalue_node(rat_const(small_val),
			  get_type(precision_node));
			numeric_constraint_small(constraint) = (char *) small_node;
		}
	}
	SIGNATURE(type_name) = (Tuple) constraint;
	/* compute signature for anonymous type */
	constraint = tup_copy(constraint);
	/* now compute proper lower and upper bounds for anonymous type */
	/* N_VAL(l_node) := [(MIN_INT+1)*num(small), den(small)]; */
	anon_lo_val = rat_fri(int_mul(int_add(ADA_MIN_FIXED_MP, int_fri(1)),
	  num(small_val)), den(small_val));

	/* N_VAL(u_node) := [MAX_INT*num(small), den(small)]; */
	anon_hi_val = rat_fri( int_mul(ADA_MAX_FIXED_MP,
	  num(small_val)), den(small_val));

	numeric_constraint_low(constraint)  = 
	  (char *)new_ivalue_node(rat_const(anon_lo_val), type_name);

	numeric_constraint_high(constraint) = 
	  (char *)new_ivalue_node(rat_const(anon_hi_val), type_name);

	SIGNATURE(anon_type) = (Tuple) constraint;

	if (rat_geq(anon_hi_val, hi_val));   /* type is representable */
	else if (rat_eql(rat_sub(hi_val, anon_hi_val), small_val))
		/* given bound is 'small away from model number. Set 'last of the type
		 * to be largest model number.
		 */
		N_VAL(hi) = (char *)rat_const(anon_hi_val);
	else errmsg("fixed type definition requires more than MAX_MANTISSA bits",
	  "Appendix F", fixed_pt_node);

	if (rat_leq(anon_lo_val, lo_val));
	else if (rat_eql(rat_sub(anon_lo_val, lo_val), small_val))
		/* Set 'first of the type to be smallest model number.  */
		N_VAL(lo) = (char *)rat_const(anon_lo_val);
	else errmsg("fixed type definition requires more than MAX_MANTISSA bits",
	  "Appendix F", fixed_pt_node);
}

static Node real_bound(Node bound, Symbol kind)				  /*;real_bound*/
{
	/* Verify that the bound of a range constraint in a real type definition
	 * is a real type, and convert it to or from universal when needed.
	 */

	Symbol	b_type, r_type;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : real_bound");

	check_type_r(bound);
	b_type = N_TYPE(bound);
/*// Is following return value correct? Added to get code to compile with CC*/
	if (b_type == symbol_any) return OPT_NODE;
	r_type = root_type(b_type);

	if (! is_static_expr(bound)) {
		errmsg("Bound in range constraint of type definition must be static",
		  "3.5.7, 3.5.9", bound);
		return OPT_NODE;
	}
	else if (kind == symbol_float)  /* Fixed or universal bound.*/
		specialize(bound, symbol_float);
	else if (is_fixed_type(kind)) {
		if (r_type == symbol_float) {
			N_VAL(bound) =
			  (char *) rat_const(rat_frr(REALV((Const)N_VAL(bound))));
			N_TYPE(bound) = symbol_dfixed;
		}
	}
	return bound;
}

static Symbol constrain_scalar(Symbol type_mark, Node constraint)
														/*;constrain_scalar*/
{
	/* Constrain a discrete type or a real type */

	int constr;
	Symbol	base_mark, bt, kind;
	Node lo, hi, precision, range_constraint, attr_node, base_precision;
	int constr_type, digits;
	Tuple new_c, old_c;
	Symbol	typ;
	Const	delta;
	Rational	rdelta;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : constrain_scalar");

	constr_type = N_KIND(constraint);
	base_mark = (Symbol) base_type(type_mark);
	old_c = SIGNATURE(type_mark);

	if (constr_type == as_range) {
		/* In this case, the bounds expressions have not been
		 * type-checked yet. Do it now that the desired base
		 * type is known.
		 */
		bt = root_type(type_mark);
		if (! is_scalar_type(bt)) {
			errmsg("Invalid RANGE constraint for type", "3.3, 3.6.1",
			  constraint);
			return symbol_any;
		}
		lo = N_AST1(constraint);
		hi = N_AST2(constraint);
		check_type(base_mark, lo);
		check_type(base_mark, hi);

		constr = (int) numeric_constraint_kind(old_c);
		new_c = constraint_new(constr);
		numeric_constraint_low(new_c)  = (char *) lo;
		numeric_constraint_high(new_c) = (char *) hi;

		if (bt == symbol_float) {
			/* use digits specified for parent type  */
			numeric_constraint_digits(new_c) = numeric_constraint_digits(old_c);
		}
		else if (is_fixed_type(bt)) {
			numeric_constraint_delta(new_c) = numeric_constraint_delta(old_c);
			numeric_constraint_small(new_c) = numeric_constraint_small(old_c);
		}
	}
	else if (constr_type == as_digits  || constr_type== as_delta)	 {
		kind = constr_type == as_digits ? symbol_float: symbol_dfixed;
		if (root_type(type_mark) != kind ) {
			errmsg("Invalid constraint for type", "3.3", constraint);
			return symbol_any;
		}
		/* if (is_generic_type(base_mark)) {
		 * 	  errmsg("accurracy constraint cannot depend on a generic type",
		 * 	  "12.1", constraint);
		 * 	  return symbol_any;
		 * 	}
		 */
		precision = N_AST1(constraint);
		range_constraint = N_AST2(constraint);
		base_precision = (Node) (SIGNATURE(type_mark))[4];

		if (is_generic_type(base_mark)) base_precision = precision;
		check_type((kind == symbol_float ? symbol_integer : symbol_real_type),
		  precision);

		if (N_KIND(precision) == as_ivalue) {
			if (kind == symbol_float) {
				digits = INTV((Const)N_VAL(precision));
				if (digits < 1) {
					errmsg("value for DIGITS must be positive", "3.5.7",
					  precision);
				}
				else if (digits > INTV((Const)N_VAL(base_precision))) {
					warning(
					  "Evaluation of expression will raise CONSTRAINT_ERROR",
					  precision);
				}
			}
			else {
				delta = (Const) N_VAL(precision);
				rdelta = RATV(delta);
				/* need to declae [0, 1] as apropriate global ds 25 nov */
				if (rat_lss(rdelta, rat_fri(int_fri(0), int_fri(1))))  {
					errmsg("value of DELTA must be positive", "3.5.9",
					  precision);
				}
				/* TBSL: check translation of following	ds 26-nov-84*/
				else if (rat_lss(rdelta, (RATV((Const)N_VAL(base_precision))))){
					warning(
					  "Evaluation of expression will raise CONSTRAINT_ERROR",
					  precision);
				}
			}
		}
		else {
			errmsg("expect static expression for DIGITS or DELTA",
			  "3.5.7, 3.5.9", precision);
		}
		if (range_constraint != OPT_NODE) {
			lo = N_AST1(range_constraint);
			hi = N_AST2(range_constraint);
			check_type(base_mark, lo);
			check_type(base_mark, hi);
		}
		else {
			/* Only the precision was given in the constraint. */
			/* Obtain the bounds from the type itself.*/
			lo = (Node) numeric_constraint_low(old_c);
			hi = (Node) numeric_constraint_high(old_c);
		}

		if (constr_type == as_digits) {
			new_c = constraint_new(CONSTRAINT_DIGITS);
			numeric_constraint_digits(new_c) = (char *) precision;
		}
		else {
			int jk;
			new_c = constraint_new(CONSTRAINT_DELTA);
			numeric_constraint_delta(new_c) = (char *) precision;
			jk = power_of_2((Const) N_VAL(precision));
			numeric_constraint_small(new_c) =  (char *)new_ivalue_node(
			  rat_const(power_of_2_small), get_type(precision));
		}
		numeric_constraint_low(new_c)  = (char *) lo;
		numeric_constraint_high(new_c) = (char *) hi;
	}
	else if (constr_type == as_attribute) {
		/* The constraint is given by a RANGE attribute which is folded
		 * as_attribute in adasem routine. We get the bounds of the 
		 * range to construct the new subtype.
		 */
		attr_node = N_AST1(constraint);
		if ((int)attribute_kind(constraint) != ATTR_RANGE) {
			errmsg("Invalid expression for range constraint","3.3", constraint);
			return symbol_any;
		}
		else {
			check_type(base_mark, constraint);
			new_c = apply_range(constraint);
		}
	}
	else {
		errmsg("Invalid constraint for scalar type", "3.3.2", constraint);
		return symbol_any;
	}
	/* Verify that a discriminant does not appear in a scalar constraint.
	 * This must be special-cased because discriminants are otherwise
	 * allowed to appear in index and discriminant constraints, and in
	 * initial values, i.e. arbitrary expressions.
	 */
	check_discriminant(constraint);

	typ = named_type(strjoin("&", newat_str()));   /* Create a name for it*/
	NATURE(typ) = na_subtype;
	TYPE_OF(typ) = type_mark;
	SIGNATURE(typ) = (Tuple) new_c;
	return typ;
}
