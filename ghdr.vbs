/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/*
 * 14-aug-85		shields
 * add type_kind field. This will hold one of the TK_ type kind values.
 * type_size will now always be in storage units, except for initial value
 * -1 indicating undefined.
 * The (new) procedure kind_size maps TK_ values to storage units.
 *
 * 25-jul-85		shields
 * add structure def for Gref and Gref_s for use by print_global_reference_map.
 *
 * 8-jul-85		shields
 * Note that code generator defines SIGNATURE of package to be a tuple
 * of symbols. This is incomptatible with adasem usage. Instead we
 * now define the third entry in the MISC value for a package, which is
 * a tuple, to be the tuple formerly held in the SIGNATURE.
 *
 * 31-may-85		shields
 * modify co_ codes to agree with values defined by adasem.
 *
 * 22-mar-85		shields
 * renamed discriminant_list to discriminant_list_get to avoid
 * confusion with SEM macro of same name.
 */

/*				Introduction 		
 *
 * This section describes the main issues and data structures that
 * arise in translating the SETL version of the  Ada/Ed code generator
 * from SETL to C.  It augments the documentation available in the
 * preliminary draft of the Kruchten-Rosen thesis describing the
 * design of Ada machine.
 *
 * The SETL version does not
 * clearly present a solution for the addressing problems for a
 * conventional byte-addressable machine; the addressing issues are
 * avoided by using an abstract approach in which memory and related
 * structures are organized as SETL tuples, whose components can
 * have varying length. Much of the work in translating to C involves
 * identifying the tuple operations that require mapping to byte strings
 * and computing the appropriate offsets, etc.
 * 
 * The initial C version has a storage unit size corresponding to a 'word
 * (C integer). 
 */


/*				
	TYPE_SIZE, mem_loc_map, and related procedures

 In SETL, the TYPE_SIZE field is used both to hold a type 'kind' and
 the number of storage units associated with a type. In the C version
 there are two symbol table fields - type_kind and type_size.
 Type_kind is the 'kind' one of the TK_ codes defined below.
 Type_size is the number of storage units, except for the value -1
 used to indicate the size not yet known. The procedure su_size()
 takes TK_ codes to the correspond storage unit count.
 */
#define TK_BYTE 1
#define TK_WORD 2
#define TK_ADDR 3
#define TK_LONG 4
#define TK_DBLE 5
#define TK_XLNG 6
/*
 The SETL macro SIZE_OF just corresponds to TYPE_SIZE.
 Note that TYPE_SIZE is in some cases set to -1 so it must be treated
 as a signed number.
 TYPE_SIZE is also used in the SETL version for holding the array size
 and for record component offsets ('POSITION) values. For the C version
 the procedure su_size is used to convert the TK_ type to the number
 of storage units required.

 The mu_... codes identify the kinds of memory units.. The procedure
 mu_size(mu...) gives the number of actual storage units 
 needed for the given mu class. In SETL the variable mem_loc_map is
 used to determine the number of bytes. It is
 not needed in the C version, where mu_size is a
 procedure. Note that mu_size is called only within file gmisc and there
 to compute stack and varaiable offsets.
 The procedure kind_of(type_name) returns the memory unit addressing
 mode for the argument type_name; the return value is one of the
 mu_ codes. The kind_of value is used in the generate() procedures
 (see below) to determine the 'kind' of an operation, a small integer
 code to select which of several variants of a base operation is to
 be performed.

	Representation of fixed-point values (TBSL)
	Program parameters (TBSL)
 */

/* 				Segments 

The memory of the target ada pseudo-machine is organized into segments.
In SETL, a segment is a tuple of 'words',  where it is understood that the
contents of the tuples are to be concatened together to represent the
true memory image. In C a segment is represented by a structure which
maintains a varying length array. The data can consist of bytes or
words (unsigned integers). The fields of the structure are as follows:
Seg_kind is the kind of the segment - SEGMENT_KIND_CODE for a code segment
and SEGMENT_KIND_DATA for a data segment. Seg_size is the number of
bytes in a segment entry: one for a code segment, or sizeof(int) for a
data segment. Seg_pos is the index at which the next value will be placed.
seg_maxpos is the largest value attained by seg_pos, so that the actual
segment data consists of entries in range 0 .. seg_maxpos - 1.
Seg_dim is the allocated dimension of the data area.
Seg_extend is the number of new entries to allocate when the segment
becomes full.
The segment must be extended whenever seg_pos >= seg_dim.
The header file segment.h has declarations for segments.
 */

#define MAIN_CS 2	/* code segment number for main code segment */
/* 

The variables CODE_SEGMENT and DATA_SEGMENT indicate the current
segments being used for code and data, respectively.  The operations on
segments are represented in C by following procedures:  
	segment_append(sa, sb) Segment sa,sb;
		append contents of segment sb at end of segment sa
		(currently defined only for word segments)
 	segment_new(kind, n) int kind,n;
 		allocate new segment of kind kind, 
		with initial room for n entries
	segment_free(s) Segment s;
		free segment s;
	segment_get_off(seg, i) Segment seg; int i;
		return seg value at position i in segment seg as unsigned int.
	segment_get_word(seg, i) Segment seg; int i;
		synonym for segment_get_off.
	segment_put_off(seg,v) Segment seg; int i,v
		put value of offset v at location i (seg_i not updated)
	segment_put_int(seg,v) Segment seg,int v;
		put value of v at current position in segment seg.
	segment_put_long(seg, lv) Segment seg; long lv;
		put value of lv at current position in segment seg.
	segment_put_ref(seg, rseg, roff) Segment seg; ing rseg,roff;
		put values of rseg and roff at current position in segment seg.
	segment_put_word(seg,v) Segment seg,int v;
		put value of v at current position in segment seg.
		(identical to segment_put_int)

Segments are also used when building up varying length strings before
their inclusion in the final code and data segments; for example, while
computing the string corresponding to the initial value of an aggregate.
 */
 
/*			References

A memory address or 'reference' on the Ada machine consists of a
segment and an offset.  The offset is an unsigned integer, zero origin,
of 16 bits.  In the SETL version, a 'reference' is a pair
[segment,offset].  Rather than introducing a structure for this in C, we
use two integers.  The case of an 'undefined' reference is indicated by
using a negative segment number, typically -1.  For the PC, we want to
view the offset as an unsigned int.  The SETL map REFERENCE_MAP becomes
two symbol table fields:  S_SEGMENT and S_OFFSET.  The SETL map
LOCAL_REFERENCE_MAP is represented in C with a procedural interface:  
	local_reference_map_defined(sym)
	    returns TRUE if map defined for symbol sym, else FALSE
	local_reference_map_put(sym,val);
	local_reference_map_get(sym);
	local_reference_map_new(n)
These procedures access the global variable LOCAL_REFERENCE_MAP, which
is a tuple with successive pairs of elements giving the symbol and
offset values.

In SETL, the procedure next_global_reference has the form
	next_global_reference(sym,val)
where sym is a symbol and val is a value, usually a tuple.  This should
be read 'set the address of sym to be the next free address in the
current data segment and intialize it to the value val'.  In SETL, val is
typically a tuple.  However, in C we need to know the `type' of val, so
we use the procedures 
	next_global_reference_r(sym,seg,off)
		seg is segment, off is offset
	next_global_reference_segment(sy, seg)
		sy is symbol, seg is Segment.
	next_global_reference_template(sy, seg)
		same as next_global_reference_segment.
	next_global_reference_def(sym)
		just reference, no value, same as SETL
		next_global_reference(sym,[]);
  	next_global_reference_z(sym)
		this is used for SETL case next_global_reference(sym,[0,0]);
		This appears to be a common case, indicating that the initial
		value is set to 'zero' for sake of completeness, but
		will be overwritten at execution time by the address
		of a generated location.
	next_global_reference_word(sym, n)
		sym is symbol, n is word (integer).


In SETL, reference_of is a procedure that returns a pair giving a 
segment and offset.
In C, this procedure sets two globals, REFERENCE_SEGMENT and REFERENCE_OFFSET.
*/

/*			Slots

Slots are used for segments and exceptions.  A code slot is a code
segment number, a data slot is a data segment number, and an exception
slot is the exception number assigned to an exception.  A slot is
allocated when spec encountered; for a package, the slot is 
'owned' by the package spec.
A slot number is an integer in range 1..255.  In SETL slots are
maintained by maps OWNED_SLOTS and BORROWED_SLOTS.  OWNED_SLOTS for a
unit has three entries 
	1	for 'data_slots'
	2	for 'code_slots'
	3	for 'exception_slots'
BORROWED_SLOTS for a unit has two entries:
	1	for 'data_borrowed'
	2	for 'code_borrowed'
In C, these are accessed through the procedures
	unit_slots_put(unit_number,tup)
	Tuple unit_slots_get(unit_number)
The second argument to unit_slots_put and the value returned by unit_slots_get
are a tuple of length five, as follows:
	1	for 'data_slots'   	SLOTS_DATA
	2	for 'code_slots'	SLOTS_CODE
	3	for 'exception_slots'	SLOTS_EXCEPTION
	4	for 'data_borrowed'	SLOTS_DATA_BORROWED
	5	for 'code_borrowed'	SLOTS_CODE_BORROWED
The variables OWNED_SLOTS and BORROWED_SLOTS in the SETL version do not
exist in the C version; instead OWNED_SLOTS corresponds to the first three
components of the tuple returned by unit_slots_get(), and BORROWED_SLOTS
corresponds to the remaining two components of this tuple.

CODE_SLOTS, DATA_SLOTS and EXCEPTION_SLOTS are maps that have symbols as
their domain.  They are represented in C by tuples with successive pairs
of values giving the domain and range values.  Note that CODE_SLOTS and
DATA_SLOTS occur in SETL source primarily as first arguments to
select_entry.  A 'slot_map_name' is a unit_name.  These are represented
in C as 'tuple maps', a tuple with successive pairs of elements giving
the domain and range values.  The domain values are slot_map_names.  The
range values are tuples.  
 
OWNED_SLOTS and BORROWED_SLOTS are not variables in the C version; their
values can be obtained from the first three or last two components of the
tuple returned by unit_slots_get().
INIT_SLOTS and MAX_INDEX are procedures init_slots() and max_index() in
the C version.  
 
Types used for select_entry:
 */
#define SLOTS_DATA 1
#define SLOTS_CODE 2
#define SLOTS_EXCEPTION 3
#define SLOTS_DATA_BORROWED 4
#define SLOTS_CODE_BORROWED 5

/* 
These correspond to tags 'data_slots', 'code_slots', 'exception_slots',
'data_borrowed' and 'code_borrowed', respectively, used as third argument
to select_entry.
 
The first argument to select_entry is either CODE_SLOTS or DATA_SLOTS
in SETL. In C this is represented by one fo the following constants:
 */
#define SELECT_CODE 0
#define SELECT_DATA 1
#define SELECT_EXCEPTIONS 2

/* OWNED_SLOTS is map from slot_map_names showing the slots allocated to
a unit.  BORROWED_SLOTS is similar, but gives slots used by a unit but
owned by another unit.  INIT_SLOTS is map from slot_map_names to highest
occupied number.  MAX_INDEX is map from slot_map_names to max allowed
slot number.  MAX_INDEX is a procedure in C version.
CURRENT_CODE_SEGMENT and CURRENT_DATA_SEGMENT are the current segment
numbers for the code and data segment, respectively.  CODE_SEGMENT_MAP
and DATA_SEGMENT_MAP are maps from segment numbers to the corresponding
segments.  In C these are kept as tuples and accessed using the
following procedures:  
    tup = segment_map_new(n)
    seg = segment_map_get(tup,segnum)
    tup = segment_map_put(tup,segnum,seg)
where n is integer, tup is CODE_SEGMENT_MAP or DATA_SEGMENT_MAP, segnum
is integer giving segment number and seq is segment.
Note that call to segment_map_put must assign the result to a variable as the
variable value may be changed by reallocating the value if a new entry is being
added.
 */


/*			Instruction generation

The operand of an operation is one of following
	Symbol
	Immediate value
A symbol is used for global or local reference, the address is obtained
from the symbol.  An immediate value is either byte word long or xlong.
For an exception it is a byte.  The length of the immediate value is
determined from the opcode.  There are psudeo-ops.  Notable is i_equal
which has two operands, both symbols.  

In SETL, the procedure generate is used to generate an instruction.  It
is called with a varying number of arguments of differing types.  In C,
each call to generate is translated to a procedure call giving the types
and number of its arguments.  
	generate(op)	->	gen(op)
Otherwise, the procedure name is gen_ followed by one letter for each
argument after the first (which is always an integer opcode).  The
suffixes are as follows:  
 	i	integer
 	s	symbol	
 	c	comment (argument is string)
 	v	ivalue
Sample procedure used, include gen_i, gen_s, gen_ic, etc.  In cases
where SETL uses pair as single argument to procedure, the C version will
use two arguments.  For generator routines, this will be indicated by
argument type of rr, indicating two arguments actually passed, the first
a segment, the second an offset.  

 */
/* The following constants define the data and addressing modes used
 * in generating instructions.
 */
#define D_NONE	0
#define D_ALL	1
#define D_INT	2
#define	D_FIX	3
#define D_FLOAT 4
#define D_PSEUDO 5

#define A_NONE	0
#define A_BOTH	1
#define	A_LOCAL	2
#define A_GLOBAL 3
#define A_CODE	4
#define	A_PREDEF 5
#define A_EXCEPTION 6
#define A_IMM	7
#define A_ATTR	8
#define A_PSEUDO 9

/* An Explicit_ref is used to main an explicit reference (segment and
 * offset).
 */
typedef struct Explicit_ref_s {
	short	explicit_ref_seg;
	short	explicit_ref_off;
} Explicit_ref_s;
typedef struct Explicit_ref_s *Explicit_ref;

/* 			Relay sets 

In SETL a relay set is a set of symbols.  In C, we keep it as a tuple of
symbols, always checking for membership before adding a new symbol.  
 */

/*			Patches

To handle forward references, several 'patch' sets are maintained.
SUBPROG_PATCH is kept as a 'map as tuple' and accessed using the
following procedures:  
	subprog_patch_get(symbol)
	subprog_patch_put(symbol,offset)
	subprog_patch_undef(symbol)
SUBPROG_PATCH is similar to CODE_PATCH_SET and DATA_PATCH_SET as
described below, except that it is a map from procedure names (symbols)
to offsets.  It is iterated over and values in the domain are unefined
(SUBPROG_PATCH(sym) := OM).  Note that it is dead after the (single)
iteration over it (about lines 10247/10315 in SETL source.  For now, we
will kept SUBPROG_PATCH as a 'map as tuple', i.e., a tuple in which
successive pairs of elements give the domain and range values.  

In SETL, CODE_PATCH_SET and DATA_PATCH_SET are sets of offsets.  In the
C version we keep them as tuples (of unsigned integers giving offsets).
The references to them are relatively few.  We will maintain tradition
and check for duplicates before insertion, although there is a single
iteration over them, and this check could be deferrred until that point,
doing a to sort then and eliminating duplicates.  
 */

/*			Type Templates */


/*			Associated symbols

Several symbols have associated with them other symbols. This is done
in SETL version by adding a special suffix to the unique name. Of
course this is a no-no in C. In C there is a (new) symbol table field
associated_symbols, whose value is a tuple of symbols. They are needed
as follows:

For a subprogram
	(1)	proc_template: the template for the procedure
	(2)	return_template: the template for the returned value 
		(defined only for functions).
For a package:
	(1)	init_spec: procedure to initialize package specification
	(2)	init_body: procedure corresponding to package body
	(3)	init_tasks: procedure to activate tasks declared
		in package.
For a task:
	(1)	task_init_proc: procedure to elaborate task
NOTE: In original change to SETL version to introduce these (edits
done 3-35-85, what is here called 'task_init_proc' was called 'init_proc'
in SETL version. We changed name to avoid conflict with 'init_proc' map in
SETL version.
For a formal parameter:
	(1)	formal_template: template for formal parameter
	(2)	actual_template: template for actual, reused
		at each call
The above fields are accessed using the following procedures:
	Symbol assoc_symbol_get(sym,fldname)
	assoc_symbol_put(sym,fldname,sval)
where sym and sval are symbols, and fldname gives the offset of the field within
the tuple of associated_symbols:
*/
#define TASK_INIT_PROC	1
#define PROC_TEMPLATE	1
#define RETURN_TEMPLATE	2
#define FORMAL_TEMPLATE	1
#define ACTUAL_TEMPLATE	2
#define INIT_SPEC	1
#define INIT_BODY	2
#define INIT_TASKS	3
/*
TBSL: save and restore the associated names in the binder, as well
as everything else!
 */

/* 

Calls to COMPILER_ERROR in SETL are translated to calls to
commpiler_error in C.  Where the SETL version builds up a string the C
version adds a suffix to indicate argument type.  For example
compiler_error_n(s,n) to pass node.  The case compiler_error_k is used
to pass node for which the SETL version has 
 	COMPILER_ERROR(s  + str N_KIND(node)
This is written in C as
	compiler_error_k(s, node)
 */
#ifdef EXPORT
#define compiler_error(r) 	  exit_internal_error()
#define compiler_error_k(r,n) 	  exit_internal_error()
#define compiler_error_c(r,c)	  exit_internal_error()
#define compiler_error_s(r,s)	  exit_internal_error()
#endif

/* macros for GEN from preface */
#define COMPONENT_TYPE(type_name) component_type(type_name)

#define DEFAULT_EXPR(obj_name) default_expr(obj_name)

#define DESIGNATED_TYPE(acc_typ) designated_type(acc_typ)

/*
macro DISCRIMINANT_LIST(record); SIGNATURE(root_type(record))(2)   endm;
This is procedure in C version.
 */

#define FIELD_NUMBER(x)           MISC(x)

#define FIELD_OFFSET(x)      S_OFFSET(x)

/*
macro FIND;	                 assert exists                     endm;
 */

/*
 * GET_TYPE is procedure get_type() in C:
 * 	macro GET_TYPE(node);
 *  (if N_KIND(node) in [as_simple_name, as_subtype_indic]
 *                        then TYPE_OF(N_UNQ(node))
 *                        }
 *                        else N_TYPE(node) end )                   endm;
 */

/*
 *	GET_CONSTRAINT is procedure get_constraint() in C:
 *	macro GET_CONSTRAINT(type_name);
 *              (if is_access_type(type_name) then [co_access]
 *               }
 *               elseif is_array_type(type_name)	then [co_index]
 *		else SIGNATURE(type_name) end )                    endm;
 */

/*
 *   macro GLOBAL_REFERENCE(name,ref);(REFERENCE_MAP(name) = ref)      endm;
 *  This macro is never used, so its translation is immaterial!
 *
 *
 *
 *
 */
#define INDEX_TYPES(type_name) index_types(type_name)

#define INVARIANT_PART(record) invariant_part(record)

/*
macro MU_SIZE(mu_nam);           MEM_LOC_MAP(mu_nam)(TARGET)       endm;
 * is procedure in C
 */


/* NEW_UNIQUE_NAME is procedure new_unique_name() in C:
 *  macro NEW_UNIQUE_NAME(name);     (name + str(newat))               endm;
 */

#ifdef TBSN
macro NEXT_NODE;                 (NODE_COUNT += 1)                endm;
#endif

/*
 *  macro NO(arg);                   ((arg)=om)                        endm;
 */

/*
   macro PC;                        (#CODE_SEGMENT+1)                 endm;
  done as procedure PC() in C version.
 */

/*
 * macro PRESENT(x);                ((x)/=om)                         endm;
 */

#define ROOT_TYPE(typ) root_type(typ)


/*
 * macro SIZE_OF(typ);              TYPE_SIZE(typ)(TARGET)            endm;
 *
 * In C, SIZE_OF corresponds to TYPE_SIZE. Since the SETL version always
 * uses 'size_of' not 'SIZE_OF' we define the macro in lower case
 */
#define size_of(typ) TYPE_SIZE(typ)

/* SMALL_OF is procedure small_of() in C:
 *   macro SMALL_OF(typ); GET_IVALUE(SIGNATURE(typ)(5))     endm;
 */

/*
 * macro TOP(x);                    x(#x)                             endm;
 */

/*
 * macro USER_WARNING(line);
 *   PRINTA(GENfile,ERR_WARNING,ada_line,0,ada_line,0,'	'+line)    endm;
 * in SETL, USER_WARNING is often called with long strings, so in C
 * we permit two arguments, which are concatenated when message written
 */
#define USER_WARNING(s1,s2) user_warning(s1,s2)

/* USER_INFO is called only two or three times, in each case withi
 * the argument being 'formatted_name...'
 * macro USER_INFO(line);
 *    PRINTA(GENfile,INFORMATION,ada_line,0,ada_line,0,'	'+line)    endm;
 * This is done by procedure user_info in gmisc.c.
 */
#define USER_INFO(line) user_info(line)

/* In the C version, the TO_GEN macro corresponds to the procedures 
 * whose names begin with to_gen in file gmisc.c 
 *  macro TO_GEN(line);
 *   PRINTA(GENfile,INFORMATION,ada_line,0,ada_line,0,'	'+line)    endm;
 * Similarly TO_LIST corresponds to procedure to_list().
 * macro TO_LIST(line);
 *    PRINTA(GENfile,INFORMATION,9999,0,9999,0,'	'+line)            endm;
 */

/* IN SETL TO_ERR is always called with string followed by filename 
 * In C, call to_err with two arguments and let to_err() in gmisc.c sort
 * things out
 *   macro TO_ERR(line);
 *    PRINTA(GENfile,ERR_SEMANTIC,ada_line,0,ada_line,0,'	'+line)    endm;
 */
#define TO_ERR(line,filename) to_err(line,filename)

/* In C, BIND_ERR corresponds to procedure bind_err 
 *macro BIND_ERR(line);
 *    ERROR_IN_UNIT = true;
 *   PRINTA(GENfile,ERR_BIND,ada_line,0,ada_line,0,'	'+line)    endm;
 */

/* Macro defined but never used in code generator
 * macro MISC_TYPE_ATTRIBUTES(typ); OVERLOADS(typ)                    endm;
 */

/* NATURE_ROOT_TYPE is procedure nature_root_type() in C:
 *	NATURE_ROOT_TYPE(typ)     NATURE(root_type(typ))
 */

/* PRIVATE_DECLS is not defined here as a macro for C version.
 * Needed definition in sem hdr.c
 *   macro PRIVATE_DECLS(package);    OVERLOADS(package)                endm;
 */

/* VARIANT_PART defined but not used in code generator
 * macro VARIANT_PART(record);      SIGNATURE(record)(1)(2)           endm;
 */

/*S+ Is... and other predicate macros */

/* HAS_DISCRIMINANT is procedure has_discriminant() in C:
 *    HAS_DISCRIMINANT(typ);   (discriminant_list(typ) ? [] /= []) endm;
 */

/* HAS_SIDE_EFFECT defined but never used
 * macro HAS_SIDE_EFFECT(node);    N_SIDE(node)                       endm;
 */

/* HAS_STATIC_SIZE is procedure has_static_size() in C:
 *	HAS_STATIC_SIZE(typ);    (size_of(typ) >= 0)                 endm;
 */

/* IS_AGGREGATE is procedure is_aggregate() in C:
    macro IS_AGGREGATE(node);   (N_KIND(node) in
                     [as_array_aggregate,  as_array_ivalue,
                      as_record_aggregate, as_record_ivalue])      endm;
 */

/*
 * macro IS_ANCESTOR(na); (na(2..) = UNIT_NAME(#UNIT_NAME-#na+2..))   endm;
 * is procedure is_ancestor() in C.
 */
#define IS_ANCESTOR(na) is_ancestor()


/* IS_FORMAL_PARAMETER is procedure is_formal_parameter() in C:
 *   IS_FORMAL_PARAMETER(na);NATURE(na) in [na_in,na_inout,na_out]endm;
 *

 * IS_GLOBAL is procedure is_global in C 
 *	IS_GLOBAL(na);            present(REFERENCE_MAP(na))         endm;
 * In SETL this is defined as IS_GLOBAL but then referenced using
 * is_global.
 *
 */

/* 
 * macro IS_GENERIC(na);       (na(2) in domain late_instances)       endm;
 * is procedure is_generic_gen() in C
 * use is_generic_gen since is_generic is macro in hdr.c (sem)
 */
#define IS_GENERIC(na) is_generic_gen(na)


/* IS_IVALUE is procedure is_ivalue() in C;
 *   macro IS_IVALUE(node);      (N_KIND(node) in
 *     [as_ivalue, as_int_literal, as_string_ivalue, as_real_literal,
 *      as_array_ivalue, as_record_ivalue])                             endm;
 *
 *   macro IS_OBJECT(node);      (N_KIND(node) in
 *  [as_simple_name,as_null,as_name,as_slice,as_index,as_selector]) endm;
 * This is procedure in C.
 *
 * IS_RENAMING is procedure is_renaming() in C;
 *   macro IS_RENAMING(na);          present(ALIAS(na))                 endm;
 *
 *
 *   macro IS_SIMPLE_NAME(node);
 *       (N_KIND(node) in [as_simple_name,as_null,as_name])         endm;
 * is procedure in C.
 *
 * In C, IS_SUBUNIT is procedure is_subunit():
 *	IS_SUBUNIT(na);           (#na > 2)                          endm;
 *
 * IS_ACCESS_TYPE is procedure is_access_type() in C:
 *   IS_ACCESS_TYPE(typ)     (nature_root_type(typ) == na_access)
 *
 * IS_ARRAY_TYPE is procedure is_array_type() in C;
 *   IS_ARRAY_TYPE(typ)      (nature_root_type(typ) == na_array)
 *
 *
 * IS_ENTRY_TYPE is procedure is_entry_type() in C:
 *   IS_ENTRY_TYPE(typ)      (nature(typ)==na_entry_former)
 */

#define IS_ENUMERATION_TYPE(typ) (nature_root_type(typ) == na_enum)

/* IS_FIXED_TYPE is procedure is_fixed_type() in C:
 *   macro IS_FIXED_TYPE(typ);      (SIGNATURE(typ)(1) = co_delta)      endm;
 *
 * IS_FLOAT_TYPE is procedure is_float_type() in C:
 *	IS_FLOAT_TYPE(typ);     (SIGNATURE(typ)(1) = co_digits)     
 *
 * IS_INTEGER_TYPE is procedure is_integer_type() in C:
 *   IS_INTEGER_TYPE(typ)    (root_type(typ) == symbol_integer) 
 *
 * IS_RECORD_TYPE is procedure is_record_type() in C:
 *   define IS_RECORD_TYPE(typ)     (nature_root_type(typ) == na_record)
 *
 * IS_RECORD_SUBTYPE is procedure is_record_subtype() in C:
 *   #IS_RECORD_SUBTYPE(typ) 
 *               (is_record_type(typ) && NATURE(typ)==na_subtype)
 *
 * IS_SIMPLE_TYPE is procedure is_simple_type() in C:
 *  
 * (nature_root_type(typ) != na_array && 
 *               nature_root_type(typ) != na_record)
 *
 * IS_STRUCTURED_TYPE is procedure is_structured_type() in C:
 *   IS_STRUCTURED_TYPE(typ) 
 *    (nature_root_type(typ) == na_array || nature_root_type(typ) == na_record)
 *
 * IS_STATIC_TYPE is procedure is_static_type() in C:
 *   macro IS_STATIC_TYPE(typ);
 *                        (is_global(typ) and has_static_size(typ)) endm;
 *
 * IS_TASK_TYPE is procedure is_task_type() in C:
 *   IS_TASK_TYPE(typ);
 *                 (   (nature_root_type(typ) = na_task_type)
 *                  or (nature_root_type(typ) = na_task_type_spec)) endm;
 *
 * 
 *	CONTAINS_TASK(typ)      MISC(typ)
 */
#define CONTAINS_TASK(typ)     MISC(typ)

/*S+Macros for operations on real numbers */
/* For C, F_TO_I and I_TO_F are no-ops. These are needed in SETL
 * for repr's.
 */
#define F_TO_I(x) x
#define I_TO_F(x) x

/*S+Macros for operations on rational numbers */

/* performs rounded division of u by v 
 * macro ROUND_DIV(u,v); ((2*u+sign(u)*v) div (2*v)) endm;
 * This is done by procedure round_div in C version.
 */

/* numerator and denominator
 * SETL macros NUM and DEN correspond to macros num and den defined
 * in arith.h.
 */

/*  Absolute value of rational number 
 *
 *    macro RAT_ABS (u);    [abs (num(u)), den(u)]  endm;
 * This corresponds to procedure rat_abs() in arith.c in C version.
 */

/*
 *    macro RAT_ADD (u, v);
 *        [num(u)*den(v) + num(v)*den(u), den(u)*den(v)]             endm;
 * This is procedure rat_add() in arith.c in C version.
 */


/*
macro RAT_DIV (u, v);
         [num(u)*den(v), num(v)*den(u)]                            endm;
* This is procedure rat_div() in arith.c in C  version.
*/


/* Test rational numbers for equality 
 *
    macro RAT_EQL (u, v);  (num(u)*den(v) = num(v)*den(u))             endm;
 * This is not used in SETL source.
 */
/* RAT_LT is procedure rat_lss() in C:
 *	 RAT_LT (u, v);
 *       (num(u)*den(v) < num(v)*den(u))                            endm;
 */
#define rat_lt(a,b) rat_lss(a,b)

/* In C, RAT_GTR is defined in arith.c 
 *  macro RAT_GTR (u, v);
 *       (num(u)*den(v) > num(v)*den(u))                            endm;
 */


/* In C, rat_toi is defined in arith.c
 *  macro RAT_TOI(u);
 *           round_div(num(u),den(u))		                   endm;
 */

/*
 *  Convert the rational number u to a SETL integer.  The number
 *  u is rounded.
 */

/*S+ macros for operations on booleans 
 *	macro ada_bool(X);    transform a SETL boolean into 0 or 1 
 *  (if X then 1 else 0 end) endm
 * This is procedure ada_bool() in C version.
 */

/*S+ macros to pack/unpack information from symbol tables */
#ifdef TBSN
macro AIS_INFO(name);
   [COMP_DATE(name) ,PRE_COMP(name), UNIT_DECL(name), CODE_UNITS(name)]
endm;
#endif

/*
macro SYMBTABF(unam);
   [NATURE   (unam), TYPE_OF(unam), SIGNATURE(unam), OVERLOADS(unam),
    SCOPE_OF (unam), ALIAS  (unam)
   ]
endm;
 */

/*
macro SYMBTABFQ(unam);
   [NATURE   (unam), TYPE_OF(unam), SIGNATURE(unam), OVERLOADS(unam),
    SCOPE_OF (unam), ALIAS  (unam),
    TYPE_SIZE(unam), REFERENCE_MAP(unam), MISC(unam),INIT_PROC(unam)
   ]
endm;
*/

/* ops.h defines symbols starting with i_ that are used for 
 * ada machine opcodes. This file is included explicitly by those
 * files that need it.
 */ 


/*S+ Global constants */
#define   SETL                           1
#define   VAXC                           2
#define   IBMPC                          3

/* error types for makelist listing processor */
/* make ERR_COMPILER macro if needed; needed ERR_ codes defined in config.h */
/*ERR_COMPILER                   16 */

#define   IBMPC_MAX_INTEGER              +32767
#define   IBMPC_MIN_INTEGER              -32768
#define   IBMPC_MAX_SHORT                +127
#define   IBMPC_MIN_SHORT                -128
#ifdef TBSN
-- these are defined by SEM
#define   ADA_MIN_REAL                   -1.0E30
#define   ADA_MAX_REAL                   +1.0E30
#define   ADA_REAL_DIGITS                 6
#endif

/*S+ Nature definitions */

/* -- na_ codes defined in hdr.h  */


/*S+ Constraints definitions */
/* These are currently handled differently in sem and gen; perhaps
 * the following codes used in gen phase should be used in sem as well:
 * These are defined as strings in SETL, make integers in C.
 * Codes _range, _digits, _delta _discr and _array defined by adasem.
 * codes _index and _access defined by adagen
 */
#define co_range 0
#define co_digits 1
#define co_delta 2
#define co_discr 3
#define co_array 4
#define co_index 5
#define co_access 6

/*S+ Memory units definitions */
/* These are defined as strings in SETL, can be integers in C. */
#define   mu_byte			 1
#define   mu_word			 2
#define   mu_addr			 3
#define   mu_long			 4
#define   mu_dble			 5
#define   mu_xlng			 6
/* mu_fixed1 and mu_fixed2 are codes for short and long fixed, resp.*/
/* They were added to C version since SETL code in type.c used
 * explicit values
 *	ds	21-mar-85
 */
#define   mu_fixed1			mu_word  /* check this */
#define   mu_fixed2			mu_dble	 /* review this too */

/*S+ Nodes definition */
/* These are constants in SETL, should be variables in C 

   OPT_NAME                      = '',
   OPT_NODE     	         = 0,
   ANY_NODE    		         = 1,
 */

/* The following codes define node kinds. Copy code from sem hdr file
 * and verify that no new natures introduced.
 */

/*
-- as_ codes defined in hdr.c
 */

/*S+ Machine instructions */
/* these are defined in hdr.c */

/*S+ Definition of attributes */
/* TBSL: The SETL code uses the folowing attribute codes - they should 
be
 * converted to those used by adasem:
 */

/* a_... attributes codes defined in hdr.c */


/*			Type Templates

A type template is a record used for the run-time elaboration of types.
In SETL, it is represented as a tuple; however, such a tuple is
typically a 'ragged array' in that the elements reflect different value
types and lengths so that the translation to C is not obvious.  Template
handling is largely confined to initialization (init.c), and the type
generation procedures (type.c).  Templates are only generated, never
used.  The generator does not look at templates once generated.  
In C, templates are represented as data segments; however, they are
allocated by the procedure template_new(kind, sizeof) which sets the
allocation expansion factor and the values of the first two entries.

There are 17 different kinds of templates. The first entry of each is
the template type code, one of TT_I_RANGE .. TT_SUBPROG. The second
entry gives the object size (TT_OBJECT_SIZE), typically one. The
remaining entries depend on the template type code. 

It appears to be the case that templates are generated and then
passed to the procedure install_type() that copies their values to
the appropriate generated segment, after which the template value is
dead, so that install_type() could free the space allocated to the
template. This should be confirmed.

*/
/*
 *S+ constants for type template access
 *  type templates are internally generated objects used to represent
 *  ada types at run-time.
 *  For the intial version, we define variant template types where
 *  the SETL version has a single template type but with differing
 *  object sizes, for example,the SETL TT_I_RANGE becomes TT_I_RANGE_I
 *  and TT_I_RANGE_L (for integer and long integer respectively).
 *
 *S+ type templates
 */

/* Note that TT_I_RANGE assumed to be two byte int for now ds 6-6-85*/
/* The structures and macros used for template accessed are defined
 * in the header file type.h
 */

/*S+Miscelleanous */
/* for fixed_point representation */
#define  WORD_SIZE  32	

/* number of elements in the SFP */
#define  SFP_SIZE   4

/* for pretty-print */
#define  max_width  80

/* The SETL map EMAP is accessed in C by the following procedures:
	 emap_get(symbol)
	emap_put(symbol,value)
  Note that emap_get returns TRUE if EMAP defined for the argument,
  and sets EMAP_VALUE to the value, or returns FALSE if the value
  not defined.
  The SETL sequence
	EMAP(s) = OM;
  is translated as
	emap_undef(s);
 */

/* The SETL maps STATIC_DEPTH, POSITION, PATCHES and EQUAL are
 * handled by procedure calls in the C version,
 *
 *
 *    STATIC_DEPTH,    map { label_name -> positive_integer } 
 *   POSITION,        map { label_name -> code location } 
 *   PATCHES,         map { label_name -> {set of locations} } 
 *   EQUAL,           map { label_name -> {set of label names} } 
 *
 *  Suggest representing these using EMAP 
 * We represent these using EMAP as a tuple: 1-STATIC_DEPTH,
 * 2-POSITION, 3-PATCHES, 4-EQUAL.
 */
#define LABEL_SIZE 4
#define LABEL_STATIC_DEPTH 1
#define LABEL_POSITION 2
#define LABEL_PATCHES 3
#define LABEL_EQUAL 4

/* The following structure is used to save global variable definitions
 * for use by print_global_reference_map.
 */

typedef struct Gref_s {
	Symbol gref_sym; /* symbol */
	short  gref_seg; /* segment */
	int    gref_off; /* offset */
    } Gref_s;
typedef struct Gref_s *Gref;
