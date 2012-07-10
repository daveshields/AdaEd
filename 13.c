/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#ifndef SEM
#define SEM	1
#endif

#include "hdr.h"
#include "vars.h"
#include "attr.h"
#include "setprots.h"
#include "dclmapprots.h"
#include "arithprots.h"
#include "errmsgprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "chapprots.h"


/* 13. Representation Clauses*/

#define max_val(x,y)	((x) > (y) ? (x) : (y)) 

#define rc_unset			 	0	
#define rc_set					1
#define rc_default				(-1)

#define storage_unit             32
#define padding                  0

#define size_position            2
#define storage_size_position    4
#define small_position           4
#define pack_position            4
#define literal_map_position     4
#define alignment_position       6

/*
 * Currently the representation information is structured as follows:
 *
 * integer & floating point types
 * [size]
 *
 * task & access types
 * [size, storage_size]
 *
 * fixed point types
 * [size] -- small is kept in the symbol table as 5th entry of signature
 *
 * array types
 * [size, pack]
 *
 * record types
 * [size, pack, [modulus, [[field, pos, first_bit, last_bit],...]]]
 *
 * enumeration types
 * [size, literal_map]
 *
 */

static char *default_representation(Symbol, int);
static void apply_length_clause(int, Symbol, Node);
static void apply_enum_clause(Symbol, Tuple);
static void apply_record_clause(Symbol, int, Tuple);
static Tuple not_chosen_get(Symbol);
static void not_chosen_delete(Symbol);
static int default_size_value(Symbol);
static int component_size(Symbol);
static Tuple default_record_value(Symbol);
extern int ADA_MAX_INTEGER;
 
void initialize_representation_info(Symbol type_name, int tag)
/*;initialize_representation_info */

{
/*
 * Initialize the representation information of the given type by setting
 * all its fields to the status unset. 
 */
Tuple	rctup;
if (tag == TAG_RECORD) {
   rctup = tup_new(7);
   rctup[1] = (char *) tag;
   rctup[2] = (char *) rc_unset;
   rctup[4] = (char *) rc_unset;
   rctup[6] = (char *) rc_unset;
}
else if (tag == TAG_TASK	|| tag == TAG_ACCESS	||
		 tag == TAG_ARRAY	|| tag == TAG_ENUM) {
   rctup = tup_new(5);
   rctup[1] = (char *) tag;
   rctup[2] = (char *) rc_unset;
   rctup[4] = (char *) rc_unset;
}
else {			/*  TAG_INT  || TAG_FIXED */
   rctup = tup_new(3);
   rctup[1] = (char *) tag;
   rctup[2] = (char *) rc_unset;
}
RCINFO(type_name) = rctup;
FORCED(type_name) = FALSE;
not_chosen_put(type_name, (Symbol)0);
}

void choose_representation(Symbol type_name)
/*;choose_representation(type_name)*/
{
Symbol	b_type;
Tuple	current_rep;
Tuple	tup;
int		status,i,n;

b_type = base_type(type_name);
current_rep = RCINFO(b_type);
 
if (current_rep == (Tuple)0) {
   REPR(type_name) = (Tuple)0;
   return;
}
n = tup_size(current_rep);
for (i=2; i<=n; i+=2) { 
   status = (int) current_rep[i];
   if (status == rc_unset) {
      current_rep[i] = (char *) rc_default;
	  current_rep[i+1] = (char *) default_representation(type_name,i);
   }
}
tup = tup_new((n/2)+1);
tup[1] = current_rep[1];
for (i=1; i<=(n/2); i++) { 
  tup[i+1] = current_rep[2*i+1];
}
REPR(type_name) = tup;
}

void inherit_representation_info(Symbol derived_type, Symbol parent_type)
/*; inherit_representation_info */
{
Symbol	b_type;
Symbol	v_type;
Tuple	current_rep;
int		i,n;

/*
 * A derived type inherits all the representation information of its parent.
 * However, this information is only considered to have a status of a 'default'
 * representation which may be overidden by an explicit representation clause
 * given to the derived type. It is therefore necessary to change the status
 * field of the derived type when the parent had the status of 'set'.
 */
 
/*
 * If the parent type is private we must retrieve its base type from the
 * private_decls entry
 */
   if (TYPE_OF(parent_type) == symbol_private ||   
       TYPE_OF(parent_type) == symbol_limited_private) {
       v_type = private_decls_get((Private_declarations)
					  private_decls(SCOPE_OF(parent_type)), parent_type);
		/*
		 * Check to seem if vis_decl is defined before accessing it. It might be
		 * undefined in the case of compilation errors.
		 */
		 if (v_type != (Symbol)0) {
			 b_type = TYPE_OF(v_type);	 /* TYPE_OF field in the symbol table */
		 }
		 else {
		   return;
		 }
	}
	else  {
		   b_type = base_type(parent_type);
	}
	current_rep = RCINFO(b_type);
	if (current_rep == (Tuple)0) {
		return;
	}
	current_rep = tup_copy((Tuple)RCINFO(b_type));
	n = tup_size(current_rep);
	for (i=2;i<=n;i+=2) {
  		if ((int)current_rep[i] == rc_set) {
	  		current_rep[i] = (char *) rc_default;
		}
        else if ((int) current_rep[i] == rc_unset) {
	  		current_rep[i] = (char *) rc_default;
	        current_rep[i+1] = (char *) default_representation(derived_type,i);
   		}
 	}
	RCINFO(derived_type) = current_rep;
	FORCED(derived_type) = FALSE;
	not_chosen_put(derived_type, (Symbol)0);
}
already_forced(Symbol type_name)				 /*; already_forced */
{
int	result;
result = FORCED(type_name);
return result;
}

void force_representation(Symbol type_name)		 /*; force_representation */
{
Symbol 	b_type,r_type,v_type,sym;
Fortup	ft1;	
Tuple	current_rep,tup,field_names;
int		i,n;

b_type = base_type(type_name);
 
/* Check if type has already been forced. */
if (already_forced(b_type)) {
   return;
}
else {
   if (is_generic_type(b_type)) {
  /*
   * There is no need to force a generic formal type since any use of this
   * type will refer to the generic actual parameter after the instantiation
   * and therefore the representation information is just that of the actual.
   * Subtypes of generic formal types will be handled differently with the
   * 'delayed_repr' instruction generated in Subtype_Declaration.
   */
      not_chosen_delete(b_type);
      return;
   }
#ifdef TBSL
   else if (has_generic_component(b_type)) {
   /* If a type has generic components its forcing must be delayed until
    * the point of instantiation when the representation of the actuals are
    * known, since the representation of the record or array is dependent on
    * the representation of the generic components. The replace routine will
    * choose the representation for all
    * delayed reprs.
    */
      delayed_reprs with:= b_type;
      FORCED(b_type) = TRUE;
      return;
   }
#endif
   FORCED(b_type) = TRUE;
   current_rep = RCINFO(b_type);
   if (current_rep == (Tuple)0) {
	  /* some sort of error condition */
      not_chosen_delete(b_type);
      return;
   }
   n = tup_size(current_rep);
   for (i=2;i<=n;i+=2) {
     if ((int)current_rep[i] == rc_default) {
        current_rep[i] = (char *) rc_set;
     }
   }
   RCINFO(b_type) = current_rep;
  /*
   * Force all component fields of the record type before the representation is
   * decided for the record type since the component types may affect the size
   * of the record.
   */

   if (is_record(b_type)) {
      r_type = root_type(type_name);
	  if (TYPE_OF(r_type) == symbol_private ||
	      TYPE_OF(r_type) == symbol_limited_private) {
          v_type = private_decls_get((Private_declarations)
                         private_decls(SCOPE_OF(r_type)), r_type);
	      if (v_type == (Symbol)0) { 		/* error condition */
              not_chosen_delete(b_type);
			  return;
		  }
          field_names = build_comp_names((Node) invariant_part(v_type));
      }
      else {
          field_names = build_comp_names((Node) invariant_part(b_type));
	  }
      FORTUP(sym=(Symbol),field_names,ft1);
         force_representation(TYPE_OF(sym));
      ENDFORTUP(ft1);
   }
   choose_representation(b_type);
   tup = not_chosen_get(b_type);
   FORTUP(sym=(Symbol),tup, ft1);
     choose_representation(sym);
   ENDFORTUP(ft1);
   not_chosen_delete(b_type);
}
}
void force_all_types()								 /*; force_all_types */
{
Symbol	b_type;

/*
 * Called at the end of a declarative part, to force all types not already
 * affected by a forcing occurence.
 */
 
while (tup_size(NOT_CHOSEN) > 0) {
   b_type = (Symbol) NOT_CHOSEN[1];
   force_representation(b_type);
}
}
static char *default_representation(Symbol type_name,int position)
/*;default_representation */
{
   switch (position) {
      case(size_position):
	   return (char *) default_size_value(type_name);

      case(storage_size_position):
          if (is_task_type(type_name) || is_access(type_name)) {
			 return (char *) OPT_NODE;
#ifdef TBSL
              return (char *) new_ivalue_node(int_const(ADA_MAX_INTEGER), 
							 symbol_integer);
#endif
		  }
          else if (is_fixed_type(type_name)) {
              return (char *) default_size_value(type_name);
          }
          else if (is_array(type_name)) {
          /* (pack_position) */
           return (char *) FALSE;
	      }
          else if (NATURE(type_name) == na_enum)  {
           /*(literal_map_position) */
           return (char *) literal_map(type_name);
	      }
          break;

       case(alignment_position):
         return (char *) default_record_value(type_name);
   }
}
 
/*
 * Changes:
 * 7/10/86     ACD     
 *  Allowed a 'small' field be processed for fixed-point numbers.  This
 *  entailed enabling the function 'length_clause' to process smalls.
 *  Only 'smalls' which are a power of 10 or 2 are allowed (this is
 *  checked in the routine 'make_fixed_template' in type.c in code generator.
 *  Note that all other length specifications are still disabled
 *
 *  In addition, the processing of 'SMALL' the call to 'check_type' was     
 *  modified to "check_type_r(expn)" instead of "check_type(attr_prefix, expn)"
 *  This is how it was done in the SETL system.
 */
void length_clause(Node node)					/*;length_clause*/
{
	Node	attr_node,expn,a_node,arg1;
	int		attr_kind,nk;
	Symbol	b_type,attr_prefix;
	Tuple	tsig;

/*
 *  This procedure processes a length clause.  
 *  It first performs semantic actions on the length clause and the expression
 *  associated with the clause and initializes variables.  If the clause is
 *  a SMALL clause, then it checks that the prefix is a type with fixed
 *  root type.  If so, then it checks that the expression is an ivalue.
 *  If it passes both of these checks then the value of the small is added
 *  to the type constraint.
 */
     attr_node = N_AST1(node);
     expn      = N_AST2(node);
     adasem(attr_node);
     adasem(expn);
     a_node = N_AST1(attr_node);
     arg1 = N_AST2(attr_node);
     attr_kind = (int) attribute_kind(attr_node);
     find_old(arg1);
     attr_prefix = N_UNQ(arg1);

if (attr_kind == ATTR_SIZE) {
   if (is_type(attr_prefix)) {
      check_type (symbol_integer, expn);
     if (is_static_expr(expn)) {
	   apply_length_clause(attr_kind, attr_prefix, expn);
	 }
	 else {
	 errmsg("Expression in size spec is not static","13.2",expn);
	 }
   }
   else {
      errmsg("Prefix of attribute is not type or first named subtype", "13.2", expn);
   }
}
     if (attr_kind == ATTR_SMALL) {
        if (!is_type(attr_prefix) || root_type(attr_prefix) != symbol_dfixed) { 
	    errmsg("expect fixed type in representation clause for SMALL",
                   "13.2(11)", arg1) ;
    	    return ;
 
        }  
        else {
	     check_type_r(expn) ;
             nk = N_KIND(expn);
	     if (nk!=as_ivalue && nk!=as_int_literal && nk!=as_real_literal) { 
/*  The expression is not static.  Do not have to check whether it is a real */
/*  or not, if it is not then an error was already emitted by check_type_r   */
	         errmsg("expression for SMALL must be static","13.2(11)",expn);
	         return ;
	     }   
	     else {
    	         b_type = TYPE_OF(attr_prefix);
	         tsig = SIGNATURE(b_type);
	         tsig[5] = (char *) expn;
	     }
     }
}
else if (attr_kind == ATTR_STORAGE_SIZE) {
   if (is_task_type(attr_prefix) || 
	   is_anonymous_task(attr_prefix) || 
       is_access(attr_prefix)) {
      check_type (symbol_integer, expn);
	  apply_length_clause(attr_kind, attr_prefix, expn);
   }
   else {
      errmsg("Prefix of attribute is not task type or access type", "13.2", expn);
   }
}

else if (attr_kind == ATTR_SMALL) { 
    if (!is_type(attr_prefix) || root_type(attr_prefix) != symbol_dfixed) { 
	errmsg("expect fixed type in representation clause for SMALL", "13.2(11)", arg1) ;
	return ;
    }
    else {
	check_type(attr_prefix, expn) ;
	if (N_KIND(expn) != as_ivalue) { 
	 errmsg("expression for SMALL must be static","13.2(11)",expn);
	 return ;
	}
	else {
	    /* specified value of small is added to the type constraint. */
	    b_type = TYPE_OF(attr_prefix);
	    tsig = SIGNATURE(b_type);
	    tsig[5] = (char *) expn;
	}
    }
}
}
static void apply_length_clause(int attr_kind, Symbol type_name, Node value)
/*;apply_length_clause */
{
	Symbol b_type;
	Tuple	current_rep;

	b_type = base_type(type_name);
	current_rep = RCINFO(b_type);
   if (attr_kind == ATTR_SIZE) {
	  current_rep[size_position] = (char *) rc_set;
	  current_rep[size_position+1] = (char *) INTV((Const) N_VAL(value));
   }
   else if (attr_kind == ATTR_STORAGE_SIZE) { 
	  current_rep[storage_size_position] = (char *) rc_set;
	  current_rep[storage_size_position+1] = (char *) value;
   }
   else { /* SMALL */
   }
}
void enum_rep_clause(Node node)							/*;enum_rep_clause*/
{

Node	name_node,aggr_node,def_node;
Node	indx_node,index_list_node,type_indic_node;
Node	aggr_list_node;
Symbol	type_name,enum_aggr_type;
Tuple	old_lit_map,rep_lit_map,seq,tup;
int		i,n; 

/* This procedure checks the validity of the representation clause for
 * enumeration types. 
 */
 name_node = N_AST1(node); 
 aggr_node = N_AST2(node);
 find_old(name_node);
 type_name = N_UNQ(name_node);
 if (NATURE(root_type(type_name)) != na_enum) {
	errmsg("Identifier is not an enumeration type", "13.3", name_node);
	return;
  }

/*
 * The representation is given by a aggregate, whose index type is the
 * given  enumeration  type,  and whose component  type is integer. We
 * build such an array type for type checking, but emit no code for it.
 */
	enum_aggr_type = find_new(newat_str());
	index_list_node = node_new(as_list);
	indx_node = node_new(as_simple_name);
	N_UNQ(indx_node) = type_name;
	N_LIST(index_list_node) = tup_new1((char *)indx_node);
	type_indic_node = node_new(as_simple_name);
	N_UNQ(type_indic_node) = symbol_integer;
	def_node = node_new(as_array_type);
	N_AST1(def_node) = index_list_node;
	N_AST2(def_node) = type_indic_node;
	
	new_constrained_array(enum_aggr_type, def_node);
	tup = (Tuple) newtypes[tup_size(newtypes)];
	tup_frome(tup);
	
	adasem (aggr_node);
	check_type (enum_aggr_type, aggr_node);
	/*if (is_static_expr(aggr_node)) {*/
	if (1) {
	  aggr_list_node = N_AST1(aggr_node);
	  seq = N_LIST(N_AST1(aggr_list_node));
	  n = tup_size(seq);
	  for (i=1;i<n;i++) {
	     if (const_ge((Const)N_VAL((Node)seq[i]),
					  (Const)N_VAL((Node)seq[i+1]))) {
		errmsg_l("Integer code is not distinct or violates ",
		       "predefined ordering relation of type","13.3",aggr_node);
		return;
	     }
	  }
  	  old_lit_map = (Tuple) OVERLOADS(type_name);
  	  rep_lit_map = tup_new(n * 2);
  	  for (i=1;i<=n;i++) {
    	     rep_lit_map[2*i-1] = strjoin(old_lit_map[2*i-1], "");;
    	     rep_lit_map[2*i] = (char *)  INTV((Const)N_VAL((Node)seq[i]));
	  }
          apply_enum_clause(type_name, rep_lit_map);
  	}
        else {
         errmsg_l("Component of aggregate in enumeration representation clause",
                  "is not static","13.3",aggr_node);
         return ;
	}
}
static void apply_enum_clause(Symbol type_name, Tuple rep_lit_map) 
/*;apply_enum_clause*/
{
Symbol	b_type;
Tuple	current_rep;

b_type = base_type(type_name);
current_rep = (Tuple) RCINFO(b_type);
if (current_rep == (Tuple)0) {
  initialize_representation_info(b_type, TAG_ENUM);
  current_rep = (Tuple) RCINFO(b_type);
}
current_rep[literal_map_position] = (char *) rc_set;
current_rep[literal_map_position+1] = (char *) rep_lit_map;
}

void rec_rep_clause(Node node) 				/*;rec_rep_clause */

{
int		repr_err;
int		modulus_value;
Node	name_node;
Symbol	type_name,comp;
Node	align_clause,comp_clause_list;
char	*field;
Tuple	field_names,location_lists, duplic_list, loc_list;
Node	comp_clause, rel_addr, bit_range,first_bit, last_bit;
int		rel_addr_val;
Fortup	ft1;
Fordeclared	fd;

name_node = N_AST1(node);
align_clause = N_AST2(node);
comp_clause_list = N_AST3(node);

adasem(align_clause);
sem_list(comp_clause_list);
find_old(name_node);
type_name = N_UNQ(name_node);

if (!is_record(type_name)) {
   errmsg("Identifier is not a record type", "13.4", name_node);
   return ;
}

repr_err = FALSE;
if (align_clause == OPT_NODE) {
  modulus_value = 0;
}
else {
  check_type(symbol_integer, align_clause);
  if (is_static_expr(align_clause)) {
     modulus_value = INTV((Const)N_VAL(align_clause));
  }
  else {
     errmsg("Alignment clause must contain a static expression", "13.4", align_clause);
     repr_err = TRUE;
   }
}
location_lists = tup_new(0);
field_names = tup_new(0);
FORDECLARED(field,comp,(Declaredmap)declared_components(base_type(type_name)),fd)
   field_names = tup_with(field_names,field);
ENDFORDECLARED(fd)

duplic_list = tup_new(0);

FORTUP(comp_clause=(Node), N_LIST(comp_clause_list), ft1)
  field = N_VAL(N_AST1(comp_clause)); 
  rel_addr = N_AST2(comp_clause);
  bit_range = N_AST3(comp_clause); /* range node */
   
   if (!tup_memstr(field, field_names)) {
	/* must verify what field in following errmsg calls (gs sep 20) */
      errmsg_str("Component % does not appear in record type", field, "none",(Node)0);
      repr_err = TRUE;
   }
   else if (tup_memstr(field,duplic_list)) {
      errmsg_str("Component % already occurs in clause", field,"none",(Node)0);
      repr_err = TRUE;
   }
   else {
      duplic_list = tup_with(duplic_list,field);
   }

   check_type (symbol_integer, rel_addr);
   if (is_static_expr (rel_addr)) {
      rel_addr_val = INTV((Const) N_VAL(rel_addr));
   }
   else {
      errmsg_str("Expression for component % must be static", field,"13.4", rel_addr);
      repr_err = TRUE;
   }
   
   if (N_KIND(bit_range) == as_range) {
      first_bit = N_AST1(bit_range);
      last_bit = N_AST2(bit_range);
      check_type (symbol_integer, first_bit);
      check_type (symbol_integer, last_bit);
      if (is_static_expr(first_bit) && is_static_expr(last_bit)) {
	 loc_list = tup_new(4);
	 loc_list[1] = field;
	 loc_list[2] = (char *) rel_addr_val;
	 loc_list[3] = (char *) INTV((Const) N_VAL(first_bit));
	 loc_list[4] = (char *) INTV((Const) N_VAL(last_bit));
	 location_lists = tup_with(location_lists, (char *)loc_list);
       }
       else  {
	 errmsg_str("Range for component % must be static",field, "13.4",(Node)0);
	 repr_err = TRUE;
       }
   }
ENDFORTUP(ft1)

  if (repr_err) {
     return;
  }
  else {
     apply_record_clause(type_name, modulus_value, location_lists);
  }
}
static void apply_record_clause(Symbol type_name, 
								int modulus_value, Tuple location_lists)
/*;apply_record_clause*/

{
	Symbol	b_type;
    char	*field;
	Tuple	current_rep,attribute_list,tup,tup2,tup4;
	int		offset,position,first_bit,start_bit,end_bit;
	int		start_unit,field_size,record_size;
	Fortup	ft1;
    Declaredmap	decls;

	b_type = base_type(type_name);
	current_rep = RCINFO(b_type);
	record_size = 0;
	attribute_list = tup_new(0);
	decls = (Declaredmap) declared_components(b_type);

   FORTUP(tup=(Tuple),location_lists,ft1);
      field = tup[1];
      start_unit = (int) tup[2];
      start_bit = (int) tup[3];
      end_bit = (int) tup[4];
      offset = storage_unit * start_unit + start_bit;
      position = offset / storage_unit;
      first_bit = offset % storage_unit;
      field_size = end_bit - start_bit + 1;
      record_size = max_val(record_size, (offset + field_size));
	  tup4 = tup_new(4);
	  tup4[1] = (char *) dcl_get(decls, field);
	  tup4[2] = (char *) position;
	  tup4[3] = (char *) first_bit;
	  tup4[4] = (char *) (first_bit + field_size -1);;
      attribute_list = tup_with(attribute_list, (char *) tup4);
   ENDFORTUP(ft1);
   tup2 = tup_new(2);
   tup2[1] = (char *) modulus_value;
   tup2[2] = (char *) attribute_list;
   current_rep[alignment_position] = (char *) rc_set;
   current_rep[alignment_position+1] = (char *) tup2;
   current_rep[size_position] = (char *) rc_set;
   current_rep[size_position+1] = (char *) record_size;
   RCINFO(b_type) = current_rep;
}
 
static Tuple not_chosen_get(Symbol sym)    					/*;not_chosen_get*/
{
    int     i,n;

n = tup_size(NOT_CHOSEN);
for (i=1;i<=n; i+=2) {
    if ((Symbol) NOT_CHOSEN[i]== sym) {
    return (Tuple) NOT_CHOSEN[i+1];
    }
}
return tup_new(0);
}
void not_chosen_put(Symbol sym1, Symbol sym2)		/*;not_chosen_put*/
{
	Tuple	tup;
    int     i,n;

if (already_forced(sym1)) {
   if (sym2 != (Symbol)0) choose_representation(sym2);
   return;
}

n = tup_size(NOT_CHOSEN);
for (i=1;i<=n; i+=2) {
    if ((Symbol) NOT_CHOSEN[i]==sym1) {
	   tup = (Tuple) NOT_CHOSEN[i+1];
	   if (sym2 != (Symbol)0)  { 
	      NOT_CHOSEN[i+1] = (char *) tup_with(tup, (char *) sym2);
	   }
       return;
	}
}
NOT_CHOSEN = tup_exp(NOT_CHOSEN, (unsigned) n+2);
NOT_CHOSEN[n+1] = (char *) sym1;
if (sym2 == (Symbol)0)
	NOT_CHOSEN[n+2] = (char *) tup_new(0);
else
	NOT_CHOSEN[n+2] = (char *) tup_new1((char *)sym2);
return;
}
static void not_chosen_delete(Symbol sym)        		/*;not_chosen_delete*/
{
    int     i,n;

n = tup_size(NOT_CHOSEN);
for (i=1;i<=n; i+=2) {
    if ((Symbol) NOT_CHOSEN[i]== sym) {
	   NOT_CHOSEN[i] = NOT_CHOSEN[n-1];
	   NOT_CHOSEN[i+1] = NOT_CHOSEN[n];
	   NOT_CHOSEN[0] = (char *) n-2;
       return;
    }
}
}
static default_size_value(Symbol type_name)			/*; default_size_value */
/*
 * Robert might want to add to this routine.
 *
 * If there were any errors in the compilation just return a default of 32
 * rather than any more detailed calculation since the type might be
 * an incorrect syntactic form (type 'any' or the like) or semantically
 * incorrect. (i.e. using a floating point as the index type of an array)
 */
{
int		size_v,num_of_comps;
Fortup	ft1; 
Tuple	bounds;
Node	lo,hi;
Symbol	i,component;
Symbol	b_type, r_type, v_type, priv_decl;
int		swap_private;
Tuple	components;
Symbol	field_name;

if (errors) {
   return 32;
}
if (is_numeric_type(type_name)) {
    size_v = 32;
}
else if (NATURE(root_type(type_name)) == na_enum) {
  /*
   * Some more elaborate code would be here to determine the # of bits
   * depending on the # of enumeration values.
   */
   size_v = 8;
}
else if (is_array(type_name)) {
   num_of_comps = 1;
   FORTUP(i=(Symbol),index_types(type_name),ft1);
      bounds = SIGNATURE(i);
	/*
     * The bounds are undefined in the case where one of the indices was
     * some incorrect syntactic form (type 'any' or the like).
	 */
 
      if (bounds == (Tuple)0) {
          return -1;
      }
 
      lo = (Node) numeric_constraint_low(bounds);
	  hi = (Node) numeric_constraint_high(bounds);
	/*
     * The size of the array can be calculated now only if they are static
     * and are integers. Static non-integer values can come about due to
     * error conditions such as using a floating point type as the index.
     * Non-static size is indicated with -1.
	 */
 
      if (!(is_static_expr(lo) && is_static_expr(hi))) {
         return -1;
	  }
      num_of_comps =  num_of_comps * 
					  (INTV((Const)N_VAL(hi)) - INTV((Const)N_VAL(lo)) + 1);
   ENDFORTUP(ft1);
   component = component_type(type_name);
   size_v = num_of_comps * default_size_value(component);
}
else if (is_record(type_name)) {
   size_v = 0;
   b_type = base_type(type_name);
   swap_private = FALSE;
   r_type = root_type(type_name);
/*
 * Check to see if either the base_type or the root_type is private and
 * if it is swap the private decls with the visible part so that the record
 * components can be made fully visible. We will swap them back at the end.
 */
   if (TYPE_OF(b_type) == symbol_private || 
	   TYPE_OF(b_type) == symbol_limited_private) {
 	   swap_private = TRUE;
   }
   else if (TYPE_OF(r_type) == symbol_private || 
	   	 	TYPE_OF(r_type) == symbol_limited_private) {
      	b_type = r_type;
      	swap_private = TRUE;
   }
 
   if (swap_private) {
      v_type = private_decls_get((Private_declarations)
                      private_decls(SCOPE_OF(b_type)), b_type);

      /*  Check for error condition and if so return standard size. */
	  if (v_type == (Symbol)0) {
          return 32;
	  }
      priv_decl = b_type ;
      b_type = v_type ;
   }
 
   components = build_comp_names((Node) invariant_part(b_type));
   /* add in the disciminants to the invariant fields , but not the special
    * constrained symbol
    */
   FORTUP(field_name=(Symbol),(Tuple) discriminant_list(b_type), ft1);
	  if (field_name != symbol_constrained) {
        components = tup_with(components, (char *) field_name);
	  }
   ENDFORTUP(ft1);

#ifdef TBSL
   variant = variant_part(b_type);
   /* Currently does not work with nested variants */
   if (tup_size(variant) != 0) {
      [-, variants] := variant;
      for [-, decls] in variants loop
         if decls /= ["null"] then
            components +:= decls(1);
         end if;
      end loop;
   }
#endif 
 
   FORTUP(field_name=(Symbol),components, ft1);
      size_v = size_v + component_size(TYPE_OF(field_name));
   ENDFORTUP(ft1);
      
   if (swap_private)  {
      b_type = priv_decl ;
   }
}
else {
   size_v = 32;
}
return size_v;
}
 
static int component_size(Symbol type_name)			/*; component_size*/

/*
 * Return the size of a component of a record or an array by first checking its
 * representation. At this point since the type of the component should have 
 * been forced already we just need to extract the size given in the 
 * representation. This was derived by either an explicit rep clause specifying
 * the size or computed based on some default formula. In the case where the 
 * type was not forced yet a default size is calculated for it.
 */
 
{
if (REPR(type_name) != (Tuple)0) {
   return (int) REPR(type_name)[size_position];
}
else {
   /* Type was not forced yet. (Probably some error condition) */
   return default_size_value(type_name);
}
}
 
static Tuple default_record_value(Symbol type_name)		/*;default_record_value */
{
	Symbol 	b_type,r_type,v_type, field_name, priv_decl;
	int		swap_private;
    Tuple	attribute_list, tup2, tup4, field_names;
	int		position, first_bit, field_size, current_offset;
    int		record_size;
	Fortup	ft1;


   	b_type = base_type(type_name);
   	swap_private = FALSE;
   	r_type = root_type(type_name);

/* 
 * Check to see if either the base_type or the root_type is private and
 * if it is swap the private decls with the visible part so that the record
 * components can be made fully visible. We will swap them back at the end.
 */
   if (TYPE_OF(b_type) == symbol_private ||
	   TYPE_OF(b_type) == symbol_limited_private) {
       swap_private = TRUE;
   }
   else if (TYPE_OF(r_type) == symbol_private ||
	        TYPE_OF(r_type) == symbol_limited_private) {
      	b_type = r_type;
      	swap_private = TRUE;
   }
  if (swap_private) {
      v_type = private_decls_get((Private_declarations)
                      private_decls(SCOPE_OF(b_type)), b_type);
 
      priv_decl = b_type ;
      b_type = v_type ;
   }
 
current_offset = 0;
attribute_list = tup_new(0);
#ifdef TBSL
variant := ST(b_type).signature.variant_part;
 
-- Currently does not work with nested variants
if variant /= [] then
   [-, variants] := variant;

   for [-, decls] in variants loop
      if decls /= ["null"] then
         components +:= decls(1);
      end if;
   end loop;
end if;
#endif
 
field_names = build_comp_names((Node) invariant_part(b_type));
FORTUP(field_name=(Symbol),field_names, ft1);
   position = current_offset / storage_unit;
   first_bit = current_offset % storage_unit;
   field_size = component_size(TYPE_OF(field_name)) + padding;
   current_offset = current_offset + field_size + padding;
   tup4 = tup_new(4);
   tup4[1] = (char *) field_name;
   tup4[2] = (char *) position;
   tup4[3] = (char *) first_bit;
   tup4[4] = (char *) (first_bit + field_size -1);
   attribute_list = tup_with (attribute_list, (char *) tup4);
ENDFORTUP(ft1);
       
/* Ignore record size for now */
record_size = current_offset + padding;
 
if (swap_private) {
   b_type = priv_decl ;
}
tup2 = tup_new(2); 
tup2[1] = (char *) 0;
tup2[2] = (char *) attribute_list;
return tup2;
} 

Node size_attribute(Node expn)						 /*;size_attribute*/
{
Symbol	typ1, v_type,b_type;
Tuple	current_rep;
Node	typ_node;
int		size_value;

typ_node = N_AST2(expn);
if (N_KIND(typ_node) != as_simple_name) {
    typ1 = N_TYPE(typ_node);
}
else {
    typ1 = N_UNQ(typ_node);
}     
if (!is_type(typ1)) {
   typ1 = TYPE_OF(typ1);
}
if (!is_static_subtype(typ1)) {
   return expn;
}
if (is_generic_type(typ1)) {
   return expn;
}
if (TYPE_OF(typ1) == symbol_private ||   
    TYPE_OF(typ1) == symbol_limited_private) {
    v_type = private_decls_get((Private_declarations)
			   				   private_decls(SCOPE_OF(typ1)), typ1);
    /*
     * Check to seem if vis_decl is defined before accessing it. It might be
     * undefined in the case of compilation errors.
     */
	 if (v_type != (Symbol)0) {
		 typ1 = TYPE_OF(v_type);	 /* TYPE_OF field in the symbol table */
	 }
}
if (is_scalar_type(typ1)) {
   b_type = base_type(typ1);
   force_representation(b_type);
   current_rep = RCINFO(b_type);
   if ((int) current_rep[size_position] == rc_unset) {
      size_value = default_size_value(b_type);
   }
   else {
      size_value = (int) current_rep[size_position+1];
   }
   return new_ivalue_node(uint_const(int_fri(size_value)), symbol_integer);
}
else {
   return expn;
}
}
#ifdef ERRORS
#endif
