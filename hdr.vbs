/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#ifndef _hdr_h
#define _hdr_h

/*
	Symbol Table Definitions for Ada/ED in C 

Change history:

October 1989	gs
Remove Sybmol Table stuff and put in separate file symbol.h.
This is included from this file now.

July 1989	gs
Add field to node N_OPERAND to hold either the register or literal value
associated with the Amiable generated code for the Node. 

19-dec-86	gs
Revise format for nodes storing left span (only) for terminal nodes,
and overlaying these 2 fields with N_AST1 of nonterminal nodes.

18-sep-86	ds
Revise format for nodes used for aggregates to permit overlaying of n_unq
and n_ast3 fields. This requires that n_ast3 not be used for such nodes, so
a new node kind  - as_aggregate_list - has been introduced and placed in the
n_ast1 position to hold the two nodes formerly
kept in n_ast1 and n_ast2. The former n_ast3 field is now at n_ast2.
The affected node kinds are as_array_aggregate, as_record_aggregate,
as_array_ivalue and as_record_ivalue.

15-nov-85	gs
add CONSTRAINT_ACCESS for subtypes of access types.

28-sep-85	ds
defintions of ATTR_ codes moved to separate inclusion file attr.h

14-aug-85	ds
Add new symbol table field type_kind, used only by code_generator.

8-jul-85	ds
Add new member const_fixed to Const structure used for fixed-point 
values during code generation.

24-apr-85	ds
Support only lower case na_ codes, drop NA_ codes. Only NA_ENUM
was actually used in upper case and this has been changed to lower case
where so used. Also, delete declarations for externs that return int's.

16-apr-65	ds
Reduce the size of the FORDECLARED macro by using (new) procedures
fordeclared_1() and fordeclared_2() to initiate and advance the
iteration, respectively.

3-apr-85
add structure definitions for Symbolmap and Nodemap because node_map
must be global (to all of chapter 12).

21-mar-85
Redefine associated_name to associated_symbols, a tuple of symbols.
This is described in more detail in ghdr.c.

13-mar-85
The macro index_type was conditionally defined only for SEM since
this name was used as variable name within code generator. Such usages
within code generator have been changed to use name indx_type so that
conditional definition no longer needed. This avoids need for SEM
conditional option in this case.

12-mar-85
Redo declarations for nodes and symbols so that single struct used for
both SEM and GEN with all fields defined. Fields used only by GEN are
defined at end of symbol_s declaration so that (eventually) SEM can ignore
these fields when building entries. For now will process full entry.
I merged in corrections from sem hdr.c through version 1.46.

4-mar-85
Add codes CODE_SLOTS etc for string used as third arg to 
select entry (this is enumeration type).
Add symbol table field associated_name. THis is used for example
to give the _type variable associated with an array name, etc.
In SETL version, these names are referenced by taking name and appending
string...

21-jan-85
modify to permit use with GEN and SEM phases. Use conditional symbols
GEN and SEM to indicate code needed only for that phase. 

31-dec-84
add NEEDNAME field to indicate symbols for which identifier needed as
name for SETL code generator. Add CONSTRAINT_ARRAY code for use when
writing out signatures for constrained arrays.

26-dec-84	ds
add N_COUNT field to hold NODE_COUNT values for node.

16-dec-84	ds
Use overloads for literal map for enumeration types, accessed using
macro literal_map. This was modified to used declared field due to original
handling of misc_type_attributes. Now that type_attr field available, it is
possible (and necessary to avoid bugs) to use overloads, as this avoids
adding further code for special handling of declared map.

12-nov-84	ds
make is_anonymous_task a procedure.

08-nov-84	ds
add n_spans field to Node_s for spans information.
NOTE: attempt to declare n_spans as short (which it should be) caused
very mysterious failures in malloc for no apparent reason; hence n_spans
is declared as int.
add s_type_attr field to Symbol_s to hold 'miscellaneous_type_attributes'
which cannot be kept in overloads field in C version. Change definition
of misc_type_attributes macro so it now refers to new field and definition
of private_dependents macro so it now refers to overloads.

31-oct-84	ds
Node that numeric_constraint for 'delta' now has four nodes; new
one is 'small' with new macro numeric_constraint_small.

15-oct-84	ds
Merge const.h and pdecl.h files into this file.

6-oct-84	ds
Revise to use seq_node tuple to record allocated nodes. Assigned values of
N_SEQ start with 1, seq_node[i] is address of node with N_SEQ == i.
seq_node_n is number of actual nodes so far allocated; only the first
seq_node_n entries of seq_node correspond to allocated nodes, the remaining
entries provide expansion space.
Similarly for allocated symbols, using seq_symbol.
SEQ_NODE_INC defines number of new entries allocated when have to expand
seq_node, similarly for SEQ_SYMBOL_INC and seq_symbol.
*/
#define SEQ_NODE_INC 50
#define SEQ_SYMBOL_INC	50

/*
ds 5-oct-84
Delete n_anon field for node, add n_seq field for node sequence number.
Also add n_unit field for unit number of node.
Change name of Symbol field sequence to s_seq and add s_unit field
for a Symbol to hold unit number.
ds 29-sep-84
I originally made numeric_constraint data structure (see na_subtype)
because I thought lo, hi, etc were actual values. It turns out they
are just nodes, and it is more convenient to represent contraints
as tuples, as is done in SETL. I have modified code to do this,
thbough macors numeric_constraint_low, etc, are still used. They
can be edited out later. But structure numeric_constraint_s is now
gone.

ds 1 aug
Modify symbol sequence handling as follows:
unit_symbol is tuple of symbol table pointers for current unit - the
i-th entry should have sequence number i. unit_symbols is number of
symbols allocated. To avoid reallocating the tuple unit_symbol when
each new symbol is allocated, unit_symbol_length will be allocated
length, and must always be >= unit_symbols.
Will also have unit_scope, a tuple with an entry for each new scope
created within a compilation unit.


ds 20 july
Need to check macro definitions to see where need parentheses
around argument names.

ds 12 july
add new symbol table field 'sequence' that contains sequence number
assigned for symbols. The global SEQUENCE_NUMBER gives the number of
the last symbol allocated; numbering starts with one. The global
SEQUENCE_LIST is a tuple indexed by sequence numbers that gives the
address of the corresponding symbol table entry.

----

This file contains the (proposed) definitions and declarations for symbol
table access for Ada/Ed-C, the C version of Ada/Ed.


Coding conventions:
-------------------

In this section we outline a suggested set of coding conventions that
are used in the remainder of this document.

C does not have the 'end-of-line' comment using a single character,
but requires that all comments begin with slash asterisk and end
with asterisk slash (we are naming the characters here to avoid
having a comment within a comment!).
There are a variety of conventions used for writing comments in C,
including the all too common convention of writing no comments at all
(a practice we do not intend to follow). 

We follow the following convention:

If a line begins with white space followed by the comment opener, then
it is the first of possibly several comment lines. The comment continues
up to and including the next line containing the comment closer. No code
may follow the comment closer on the last line. 

If a line otherwise contains a comment opener, then it must also contain
the comment closer, and no code must follow the comment closer.

This permits each line to be classified as either code followed by a
comment extending to the end of the line, code with no comment, or part
of a comment, and makes it possible to write a filter to convert to
other comment conventions. 


Significance of Character Case
------------------------------

In C, unlike SETL, the case of an identifier is significant, so that
'I' and 'i' are distinct identifiers.  The SETL version uses such
case-ignorant names at times; and these will have to be removed as
part of the translation to C. In general, we will follow the following
rules, with occasional exceptions, noted in comments below, which will
simplify the translation of the SETL source to C; such exceptions
will typically introduce mixed-case identifiers.

1. Names defined by #define are capitalized, i.e., defined constants
and macros.

2. SETL strings used as discriminants will usually be changed to 
defined constants, with some appropriate prefix, and will thus be capitalized.

3. User-defined type names have their first letter capitalized.

4. Structure tags are to be defined with initial letter capitalized
and are given the same name via a typdef. For example, 

  struct Str { ... } Str;

5. Since much of the code will involve merely passing pointers to
structures, we will often use type names that in fact just pointers.
This requires two names, one for the structure and one for a pointer
to the structure. Having two names permits us to write
	Str	x,y,z;
instead of
	Str	*x,*y,*z;
For such cases, our convention is to use
	Name
for a pointer to the structure, and
	Name_s
for the structure itself. This permits us to write code using the first
approach, avoiding needless (since they are always implicit) asterisks
in declarations and other references, such as casts, involving the type
name. 

*/

/* Include declarations for sets and tuples */

#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include "config.h"
#include "arith.h"
/*
		SYMBOL TABLE


   In SETL, the symbol table is represented as several maps:
nature, type_of, scope_of, signature, overloads and alias.
In C, a symbol table entry will be a structure, with fields 
corresponding to the SETL maps, in the order given above.
Not all fields are defined for each entry. We provide a single 
declaration and leave it up to the allocator (which will be given the
nature) to allocate the proper length entry.

The alias field is used for derived subprograms and renamed subprograms,
and also for types.

The overloads field is defined for procedures, functions, literals and
operators; for packages it is used to store private declarations.

The SETL version has declared as a map; in the C version this will be
a field in symbol table entries for which it is defined.

The orig_name field gives the original name of the symbol.
*/


typedef struct Declaredmap_s *Declaredmap;

#ifdef AMIABLE
/*
#include "gena.h"
*/
			/* it includes symbol.h */
#else
#include "symbol.h"
#endif

/* 
Each entry in the symbol type has a nature. The nature is represented
as a string in the SETL source, and as one of the following constant
values of the form na_ in C. 
*/

/*		AST declarations and definitions

This file contains the declarations and definitions for the
AST representation for the ADA/ED-C ADASEM phase.

The following summary is taken from file [ada.dev]ast.doc
(perhaps should merge in this whole file later):

    The following is a description of the nodes used in building the
abstract syntax tree (AST) for an ADA source program (in the SETL
version).

    The AST is represented as a collection of nodes on which certain
maps are defined to form the tree. The nodes correspond to 
non-terminals such as "pragma", "object_declaration", etc...  Nodes
are represented by setl integers and are described as either equivalent
to other nodes or by specifying values for the maps N_KIND, N_AST,
N_VAL, and/or N_LIST that are defined on them.	These maps are used as
follows:

N_KIND(node) is a string (for now) that names the node and serves as a
discriminant for the other maps defined on it.

N_AST(node) is a tuple of nodes, corresponding to the right-hand side
of a production for the node.

N_VAL(node) is defined for terminal nodes. For simple_names it is the
source identifier for that node. The semantic actions use the N_VAL map
to store miscellaneous information used by the EMIT routine.

N_LIST(node) is a tuple of arbitrary length whose components are nodes
of the same kind. N_LIST(node) is defined for all occurrences in the
grammar of arbitrary repetitions. These are noted below as nodes of the
form <node...>, and have the N_KIND 'list'.



SEMANTIC PROCESSING.


The semantic routines are driven by the N_KIND of each AST node. In most
cases the AST is not directly modified by the semantic actions; rather,
several maps, including the symbol table, are constructed and updated. 
The following maps are used by sem:

N_UNQ(node) is the unique name corresponding to a name node. The N_KIND
of such a node is always set to 'simple_name'. The N_UNQ is a symbol
table pointer, through which all attributes of an entity are retrieved.

N_NAMES(node) is the overloaded set of names coresponding to a name node
before overload resolution is performed. It is used only during type
resolution.

The above two maps, N_UNQ and N_NAMES, are defined only on name nodes.

N_TYPE(node) is the unique name of the type of an expression node. This
field is set for all expressions and names that are not simple names.

N_PTYPES(node) is the set of possible types of an overloaded construct,
before resolution. It is also useless after type resolution.

The maps N_TYPE and N_PTYPES are defined only on expression nodes.

-- end excerpt from AST.DOC

In C N_KIND will be represented as an integer constant of the form AS_.

A node has N_UNQ and N_NAMES defined; or it has	 N_TYPE and
N_PTYPES defined. Field n_sym is used for N_UNQ or N_TYPE, which
are both pointers to symbol table entries. Field n_set is used for
N_NAMES or N_PTYPES, which are both pointers to sets of symbol table
pointers.

The fields for N_LIST and N_VAL can overlap, and are hence declared
as a union.

The fields for N_AST and N_LIST can overlap since they are never both
defined for a node

Note that for the case where the SETL AST map id defined, the number of
components is fixed for a particular kind, and at most five. We thus
define fields n_ast1, n_ast2 ... n_ast5 and allocate only as many fields
as needed for each particular node. It is not necessary to keep the 
number of AST entries, since the length can be deduced from N_KIND. 

*/

typedef struct Span_s *Span;   /* pointer to spans information */

typedef struct Span_s {
	short line;
	short col;
} Span_s;

typedef struct Node_s *Node; /* Node is pointer to Node_s */
#define NODE_SIZE  sizeof(Node_s)

typedef struct Node_s
{
#ifndef IBM_PC
	struct {
	unsigned n_kind:8;
	unsigned n_unit:8;
	unsigned n_side:1;
	unsigned n_overloaded:1;
	} n_flags;
	
	short n_seq;
#else
	struct {
	unsigned n_kind:8;
	unsigned n_unit:8;
	} n_flag1;

	struct {
	unsigned n_side:1;
	unsigned n_seq:14;
	unsigned n_overloaded:1;
	} n_flag2;

#endif

	union {
	Node	n_ast1;
	Span_s	n_span;
	} nu1;

 	union {
	Node	n_ast2;
	Tuple	n_list;
	char	*n_val; 
	int n_id;
	} nu2;
 	union { 
	Node	n_ast3;
	Set	n_names;
	Symbol	n_unq; 
	} nu3;
 	union {
	Node	n_ast4;
	Set	n_ptypes;
	Symbol	n_type; 
	} nu4;
#ifdef AMIABLE
	Operand_s n_operand;
#endif
}  Node_s;

struct unit {
	char *name;
	int isMain;
	char *libUnit;
	struct {
		char *fname;
		char *obsolete;
		char *currCodeSeg;
		char *localRefMap;
		char *compDate;
	} libInfo;
	struct {
		char *preComp;
		char *pragmaElab;
		char *compDate;
		char *symbols;
		int  numberSymbols;
		char *unitDecl;
	} aisInfo;
	struct {
		char *tableAllocated;
		int nodeCount;
		int rootSeq;
	} treInfo;
};

#define MAX_UNITS 100

#ifdef IBM_PC
#define N_KIND(p)	((p)->n_flag1.n_kind)
#define N_UNIT(p)	((p)->n_flag1.n_unit)
#define N_OVERLOADED(p)	((p)->n_flag2.n_overloaded)
#define N_SIDE(p)	((p)->n_flag2.n_side)
#define N_SEQ(p)	((p)->n_flag2.n_seq)
#else
#define N_KIND(p)	((p)->n_flags.n_kind)
#define N_UNIT(p)	((p)->n_flags.n_unit)
#define N_OVERLOADED(p)	((p)->n_flags.n_overloaded)
#define N_SIDE(p)	((p)->n_flags.n_side)
#define N_SEQ(p)	((p)->n_seq)
#endif
#define N_SPAN(p)	(&(p)->nu1.n_span)
#define N_SPAN0(p)	((p)->nu1.n_span.line)
#define N_SPAN1(p)	((p)->nu1.n_span.col)
#define N_AST1(p)	((p)->nu1.n_ast1)
#define N_VAL(p)	((p)->nu2.n_val)
#define N_LIST(p)	((p)->nu2.n_list)
#define N_AST2(p)	((p)->nu2.n_ast2)
#define N_AST3(p)	((p)->nu3.n_ast3)
#define N_UNQ(p)	((p)->nu3.n_unq)
#define N_ID(p)	 	((p)->nu2.n_id)
#define N_NAMES(p)	((p)->nu3.n_names)
#define N_AST4(p)	((p)->nu4.n_ast4)
#define N_TYPE(p)	((p)->nu4.n_type)
#define N_PTYPES(p)	((p)->nu4.n_ptypes)
#ifdef AMIABLE
#define N_OPERAND(p)    ((p)->n_operand)
#endif

/* N_D_ macros define which fields defined for node according to kind */
#define N_D_AST1 1
#define N_D_AST2 2
#define N_D_AST3 4
#define N_D_AST4 8
#define N_D_LIST 16
#define N_D_VAL 32
#define N_D_UNQ 64
/* was N_CHAOS 128  ds 10-29-86 */
#define N_D_TYPE 256

#define N_AST1_DEFINED(p) (N_DEFINED[p]&N_D_AST1)
#define N_AST2_DEFINED(p) (N_DEFINED[p]&N_D_AST2)
#define N_AST3_DEFINED(p) (N_DEFINED[p]&N_D_AST3)
#define N_AST4_DEFINED(p) (N_DEFINED[p]&N_D_AST4)
#define N_VAL_DEFINED(p) (N_DEFINED[p]&N_D_VAL)
/* N_UNQ_DEFINED and N_TYPE defined are set for nodes for which these fields
 * are to written to library files and for which the fields are to be set 
 * during instantiation.
 */
#define N_UNQ_DEFINED(p) (N_DEFINED[p]&N_D_UNQ)
#define N_TYPE_DEFINED(p) (N_DEFINED[p]&N_D_TYPE)
#define N_LIST_DEFINED(p) (N_DEFINED[p]&N_D_LIST)

/*
From schonber Tue Feb 11 00:51:07 1986
Date: Tue, 11 Feb 86 00:51:03 est
From: schonber
Received: by nyu-acf2.arpa; Tue, 11 Feb 86 00:51:03 est
To: shields
Subject: data compression.
Status: R

Have you tried overlapping N_PTYPES and N_TYPE? This should be safe in all
cases, as they have always disjoint usage. A further possibility is N_NAMES
and N_UNQ, but this requires the use of some additional bit to indicate whether
an entity is overloaded or not. By the way, N_NAMES is ONLY defined on simple
names and ops, so maybe overlapped with unused N_AST field. THere is still some
juice to be squeezed out.

Franck says:
	N_NAMES and N_UNQ cannot be overlaid

From chiabaut@nyu.arpa Thu Sep 11 10:27:20 1986
Received: from nyu.arpa by nyu-acf2.arpa; Thu, 11 Sep 86 10:27:17 edt
Date: Thu, 11 Sep 86 10:28:48 edt
From: chiabaut@nyu.arpa (Jerome Chiabaut)
Message-Id: <8609111428.AA03384@nyu.arpa>
Received: by nyu.arpa; Thu, 11 Sep 86 10:28:48 edt
To: shields@nyu-acf2.arpa
Subject: Re: overlaying n_unq and n_type
Status: RO

  I'm not sure but i think that an aggregate or array-aggregate has more than
two n_asts defined along with n_type and n_unq. In any case the idea is that
for a few nodes it might require to change the shape of the tree.
     Jerome

*/


#define as_pragma  0
#define as_arg	1
#define as_obj_decl  2
#define as_const_decl  3
#define as_num_decl  4
#define as_type_decl  5
#define as_subtype_decl	 6
#define as_subtype_indic  7
#define as_derived_type	 8
#define as_range  9
#define as_range_attribute  10
#define as_constraint  11
#define as_enum	 12
#define as_int_type  13
#define as_float_type  14
#define as_fixed_type  15
#define as_digits  16
#define as_delta  17
#define as_array_type  18
#define as_box	19
#define as_subtype  20
#define as_record  21
#define as_component_list  22
#define as_field  23
#define as_discr_spec  24
#define as_variant_decl	 25
#define as_variant_choices  26
#define as_string  27
#define as_simple_choice  28
#define as_range_choice	 29
#define as_choice_unresolved  30
#define as_others_choice  31
#define as_access_type	32
#define as_incomplete_decl  33
#define as_declarations	 34
#define as_labels  35
#define as_character_literal  36
#define as_simple_name	37
#define as_call_unresolved  38
#define as_selector  39
#define as_all	40
#define as_attribute  41
#define as_aggregate  42
#define as_parenthesis	43
#define as_choice_list	44
#define as_op  45
#define as_in  46
#define as_notin  47
#define as_un_op  48
#define as_int_literal	49
#define as_real_literal	 50
#define as_string_literal  51
#define as_null	 52
#define as_name	 53
#define as_qualify  54
#define as_new_init  55
#define as_new	56
#define as_statements  57
#define as_statement  58
#define as_null_s  59
#define as_assignment  60
#define as_if  61
#define as_cond_statements  62
#define as_condition  63
#define as_case	 64
#define as_case_statements  65
#define as_loop	 66
#define as_while  67
#define as_for	68
#define as_forrev  69
#define as_block  70
#define as_exit	 71
#define as_return  72
#define as_goto	 73
#define as_subprogram_decl  74
#define as_procedure  75
#define as_function  76
#define as_operator  77
#define as_formal  78
#define as_mode	 79
#define as_subprogram  80
#define as_call	 81
#define as_package_spec	 82
#define as_package_body	 83
#define as_private_decl	 84
#define as_use	85
#define as_rename_obj  86
#define as_rename_ex  87
#define as_rename_pack	88
#define as_rename_sub  89
#define as_task_spec  90
#define as_task_type_spec  91
#define as_task	 92
#define as_entry  93
#define as_entry_family	 94
#define as_accept  95
#define as_delay  96
#define as_selective_wait  97
#define as_guard  98
#define as_accept_alt  99
#define as_delay_alt  100
#define as_terminate_alt  101
#define as_conditional_entry_call  102
#define as_timed_entry_call  103
#define as_abort  104
#define as_unit	 105
#define as_with_use_list  106
#define as_with	 107
#define as_subprogram_stub  108
#define as_package_stub	 109
#define as_task_stub  110
#define as_separate  111
#define as_exception  112
#define as_except_decl	113
#define as_handler  114
#define as_others  115
#define as_raise  116
#define as_generic_function  117
#define as_generic_procedure  118
#define as_generic_package  119
#define as_generic_formals  120
#define as_generic_obj	121
#define as_generic_type	 122
#define as_gen_priv_type  123
#define as_generic_subp	 124
#define as_generic  125
#define as_package_instance  126
#define as_function_instance  127
#define as_procedure_instance  128
#define as_instance  129
#define as_length_clause  130
#define as_enum_rep_clause  131
#define as_rec_rep_clause  132
#define as_compon_clause  133
#define as_address_clause  134
#define as_any_op  135
#define as_opt	136
#define as_list	 137
#define as_range_expression  138
#define as_arg_assoc_list  139
#define as_private  140
#define as_limited_private  141
#define as_code	 142
#define as_line_no  143
#define as_index  144
#define as_slice  145
#define as_number  146
#define as_convert  147
#define as_entry_name  148
#define as_array_aggregate  149
#define as_record_aggregate  150
#define as_ecall  151
#define as_call_or_index  152
#define as_ivalue  153
#define as_qual_range  154
#define as_qual_index  155
#define as_qual_discr  156
#define as_qual_arange	157
#define as_qual_alength	 158
#define as_qual_adiscr	159
#define as_qual_aindex	160
#define as_check_bounds	 161
#define as_discr_ref  162
#define as_row	163
#define as_current_task	 164
/* new node added aug 84 by banner */
#define as_check_discr	165
#define as_end	166
#define as_terminate 167
#define as_exception_accept 168
#define as_test_exception 169
#define as_create_task 170
#define as_predef	171
#define as_deleted 172
#define as_insert 173
#define as_arg_convert 174
#define as_end_activation 175
#define as_activate_spec 176
#define as_delayed_type 177
#define as_qual_sub 178
#define as_static_comp 179
#define as_array_ivalue 180
#define as_record_ivalue 181
#define as_expanded 182
#define as_choices 183
#define as_init_call 184
#define as_type_and_value 185
#define as_discard 186
/* as_unread used by C version to indicate node not yet read in.
 * The SETL test N_KIND(node)=om thus becomes
 * N_KIND(node)==as_unread in C
 */
#define as_unread 187
#define as_string_ivalue 188
#define as_instance_tuple 189
#define as_entry_family_name 190
/* The next two kinds are used internally only by astread */
#define as_astend	191
#define as_astnull	192
/* aggregate_list added 9-15-86 so can overlay n_ast3 and n_unq  (DS) */
#define as_aggregate_list 193
#define as_interfaced 194
#define as_record_choice 195
#define as_subprogram_decl_tr 196
#define as_subprogram_tr 197
#define as_subprogram_stub_tr 198
#define as_rename_sub_tr 199

/*
PARSE TREE
----------
This section describes changes and additions to the parse tree (nodes) 
in the C version:

AS_ATTRIBUTE
------------
In the SETL version a node of this kind has as its first subnode (AST1)
a name-type node with a string giving the attribute name. The SETL version
alters this string by adding a prefix of "T_" or "O_" to indicate attributes
for types and objects, respectively. In C this is done by storing a numeric
attribute code in the N_VAL field for the as_attribute node. The attribute
codes are chosen so that where "T_" and "O_" codes are needed, the
codes are in the order	base code, then "O_" code and then "T_" code.
The procedure attribute_str() maps numeric codes to their string
equivalents. The original subnode is left intact; all manipulation of
codes is done with the numeric codes.
The codes are defined in header file attr.h:
*/


/*

SYMBOL TABLE 
------------
Let us now continue out the description of the symbol table entries.
Entries whose nature ends in '_SPEC' have the same form as the
corresponding nature with '_SPEC' removed. The initial entry
with '_SPEC' is made when the specification is seen; the other
is made when the body is encountered.

For a field, 'not used' means the field is defined but not used, so that
its contents are not relevant (they will, and should, be NULL, the null
pointer); 
*/

/* 
 * Define nature codes. To assist conversion of SETL source each
 * code is defined in both upper and lower case. 
 */

#define na_op  1
#define na_un_op  2
#define na_attribute  3
#define na_obj	4
#define na_constant  5
#define na_type	 6
#define na_subtype  7
#define na_array  8
#define na_record  9
#define na_enum	 10
#define na_literal  11
#define na_access  12
#define na_aggregate  13
#define na_block  14
#define na_procedure_spec  15
#define na_function_spec  16
#define na_procedure  17
#define na_function  18
#define na_in  19
#define na_inout  20
#define na_out	21
#define na_package_spec	 22
#define na_package  23
#define na_task_type  24
#define na_task_type_spec  25
#define na_task_obj  26
#define na_task_obj_spec  27
#define na_entry  28
#define na_entry_family	 29
#define na_entry_former	 30
#define na_generic_procedure_spec  31
#define na_generic_function_spec  32
#define na_generic_package_spec	 33
#define na_generic_procedure  34
#define na_generic_function  35
#define na_generic_package  36
#define na_exception  37
#define na_private_part	 38
#define na_void	 39
#define na_null	 40
#define na_discriminant	 41
#define na_field  42
#define na_label  43
#define na_generic_part	 44
/* na_subprog, na_body and na_task referenced in sem0.c, addedm15-may 
 for debugging 
 */
#define na_subprog 45
#define na_body 46
#define na_task 47
/* added for use with symbol_op (cf find_qual (8) and result_types(4))*/
#define na_task_body 48

/*
NA_ACCESS:
----------
denotes an access type.

type_of: map of an access type is itself. The macro
designated_type(access_type) retrieves the unique name of
the type of designated objects of the access type.
this macro is also available on	 subtypes of access types.

signature: designated_type (as noted above)

overloads: not used

type_attr:  misc_type_attributes

NA_AGGREGATE:	
-------------
Every array and record declaration introduces an aggre-
gate into the environment, i.e. one possible meaning
for any aggregate expression appearing in the code. In order
to disambiguate such an expression, it is convenient to view
aggregates as overloaded constructs. Each aggregate entry
is uniquely characterized by its type (held in type_of).
Note that constraining an array does not introduce a new
aggregate. Properly speaking, it is only a new sequence type
(an unbounded array) which introduces a new aggregate.

type_of: (unique characterization of) type

signature: not used

overloads: set of other aggregate types (symbols) in same scope


NA_ARRAY:
---------
This denotes an entry for an array type. This entry is built
when an array declaration is processed, and also when a task
family or an entry family is elaborated. An array denotes an
unconstrained type.

type_of: unique name of parent sequence. 
This is invariably a generated name. For the predef
defined STRING type, the parent sequence is STRING itself.
all sequences are arrays whose type is themselves.

signature: the pair :

		[ index-types, component-type]

where index_types is a tuple of type names.


overloads: 

type_attr:  misc_type_attributes

NA_ATTRIBUTE:
-------------
An entry of this nature denotes a predefined attribute
of the language.
Many attributes are generic : they apply to classes of types.

type_of: either a predefined type, (INTEGER or STRING) or the 
marker 'overloaded'. This indicates
that the type returned by the attribute depends on the type of
its arguments.

signature,overloads: not used 


NA_BLOCK:	
---------
There are three kinds of blocks, distinguished by their overloads values:
block, loop or handler. A loop has alias defined, so all entries need
full length symbol table entry.
In SETL, the type_of field is used to hold the block type. In C we
use special codes stored in the overloads field.
Blocks are not used for separate compilation, so it is an error
if one occurs.

signature: miscellaneous information.
	unused externally

overloads: block type, one of the following
 */
#define BLOCK_BLOCK	0
#define BLOCK_LOOP	1
#define BLOCK_HANDLER	2
/*
Note that the use of overloads for NA_BLOCK is internal to adasem. This
information need not be written out externally.


NA_CONSTANT:	
------------
Denotes a symbol table slot for a user-defined constant
or for the result of evaluating a static expression.

type_of: specified type for constant.

signature: Node for expression

overloads: not used 

NA_ENTRY:	
---------
denotes an entry object. 

type_of: points to an entry former. 

signature: the formalslist, and is identical
to that of a subprogram. 
 
overloads: identical to that of a subprogram


NA_ENTRY_FAMILY:	
----------------
denotes an entry family object. This is a non-over-
loadable entity, constructed as an array of entries. 

type_of: anonymous array type whose component is an entry-type.

signature: formal parameters

overloads: not used


NA_ENTRY_FORMER:	
----------------
denotes the type of an entry object. Calls to entries
(rendez-vous) have the same syntax as procedure calls, and
named and default parameters are also present. 

type_of: task type in which it is declared (same as scope_of, in fact)
*	??   As for procedures, the TYPE_OF an entry is the marker 'none'.

signature: the list of formals for the entry, and has the same format 
as that of a procedure.
An entry call does not return a value. 

overloads: not used


NA_ENUM:
--------
Denotes an enumeration type.

type_of: parent type, if derived, or the typename itself for 
BOOLEAN, CHARACTER, and non-derived enumerations.

signature: the range for the enumeration type in the format:

		['range', low, high]

where low and high are the integer values for the first
and last enumeration literals of the type.

overloads: a map, from the literals to their POS in the type. 
By default the range of this map is dense
and 0-origined, but it can be modified by a representation
clause. This map is accessed by the macro literal_map.
It is represented in C as a tuple with element i being pointer to
string for literal, element i+1 being value of literal map for
the string.



NA_EXCEPTION:
-------------

NA_FUNCTION:	
------------
identical to NA_PROCEDURE. 

type_of: the type which it returns.

signature:	same as for procedure.

overloads:	same as for procedure.


NA_FUNCTION_SPEC:	
-----------------

An entry is given this
nature after the corresponding subprogram specification
is processed. When the subprogram body is encountered
the specification is examined again, and if it coincides with
an existing symbol table slot, the _spec tag is removed.

signature:	same as for procedure

overloads:	same as for procedure

NA_GENERIC_FUNCTION_SPEC:
NA_GENERIC_PROCEDURE_SPEC:
NA_GENERIC_PACKAGE:	
---------------------

Generic objects have the same organization as their non-generic
counterparts. The SIGNATURE of a generic entity has, in addition to
its non-generic purpose, the further role of holding the list of
generic parameters and the body of the generic object.

type_of: unused. 

signature:	The signature is a tuple with two elements:
		1) gen_list, a tuple of pairs, each consisting 
		   of a symbol and a node.
		2) form_list, a tuple of symbols

overloads: not used

NA_GENERIC_PACKAGE:	
---------------------


type_of: unused. 

signature:	A tuple with three elements:
		1) gen_list, a tuple of pairs, as for generic_procedure
		2) decl_node, a node.
		3) opt_priv_node, a node.

overloads: not used

NA_IN:
------

type_of:	type of formal parameter

signature:	initial value (node) if there is one, else null node.

overloads:	not used.

NA_INOUT:	
---------

type_of:	type of formal parameter

signature:	initial value (node) if there is one, else null node.

overloads:	not used.


NA_LABEL:	
---------
An entry for a label requires only a single bit, indicating whether
the label has been defined.	

NA_LITERAL:	
-----------
an entry of this nature denotes an enumeration literal.

type_of: entry holds the unique name of the enumeration type
to which it belongs.

signature: is the same as that of a parameterless function, i.e. [].

overloads: same meaning as for operators

NA_NULL
-------
TBSL (almost certainly dead - does not occur in SETL)

NA_OBJ:	 
-------
Denotes a symbol table slot for a program variable.

type_of: a unique name, namely that of a user-defined or 
internally generated type.

signature:	holds the initial value for fields of a record. Otherwise,
                it is not used.

overloads:	not used

NA_OP:		
------
An entry with this nature denotes a predefined operator in the
language.

type_of: for an operator is usually a generic marker
which indicates the family of types to which this operator can
apply. This marker obviates the need to introduce a separate
operator for each type derived from the predefined types. These
generic type marks are also given a symbol table slot. The
following are used :

	   1) 'universal_integer' : for all arithmetic operators which apply
	   to integers.
	   2) 'universal_real'	 : ditto for floating and fixed types.
	   3) 'array_type'   : used for the (idiosyncratic) concatenation
	      operator.
	   4) 'order_type'   : for comparison operators.
	  5) 'boolean type' : for boolean operators. This simplifies the
	      handling of arrays of booleans and derived(!) booleans.
	   6) 'string_type'  : for string literals, which overload any
	      array of characters.


   We represent these in C as values of following global variables:
	gtm_universal_integer
	gtm_universal_real
	gtm_array_type
	gtm_order_type
	gtm_boolean_type
	gtm_string_type
*/

/*

signature: follows the same format as the one for a subprogram. 
The canonical parameter names LEFT and RIGHT are not stored explicitly
but are known to an internal procedure order_arg_list in those rare
cases when an operator is used in functional notation with named
associatoins.
Note that this need not appear when writing externally.

overloads: has the same meaning as for subprograms. 
Given that operators are entered into the symbol
table during initialization, at the outermost scope, most ope-
rators in fact do not overload anything. For arithmetic ope-
rators however, we give different unique names to the integer
and floating point version of them.


*/


/*

NA_OUT:		
-------

type_of:	type of formal parameter

signature: not used
Note however that as a byproduct of initializing nodes for arguments,
the signature may be a node, namely OPT_NODE.

NA_PACKAGE:	
-----------
designates a package or a package specification. 

type_of: not used

signature: not used

overloads: pointer to private symbol table with private declarations
of the package.

*/

/*
 *	Private Declarations
 *
 * Access to entities declared in a package is through its declared map 
 * (when inside the package) or through its visible map, which holds only the
 * declarations in the visible part of the package specification.
 * The private declarations for the package are stored as a map
 * in its overloads entry, and installed in the symbol table on
 * entry to the package body (i.e. when compiling the body).
 * The	macro  private_decls(pack) accesses the private decls,
 * which are installed when compiling the body of the package,
 * and removed after the body.
 * Access to entities in the specification is
 * via the mapping VISIBLE. The domain of visible(p) is a sub-
 * set of that of declared(p).
 * The private declarations of the package are stored in a
 * separate structure, private_decls(p). These private decla-
 * rations are installed in the global symbol table when the
 * body of the package is compiled, and removed afterwards, so
 * that only the visible attributes remain accessible outside
 * of the package.
 * 
 * Note that in the C version, VISIBLE is not a separate map but
 * an attribute associated with each entry in a declared map.
 * alias: ??
 * -- pdecl.doc
 * In the C version, private_decls is represented as a pointer to a tuple.
 * The pointer is needed so we can expand the tuple as necessary.
 * Each odd entry is a symbol table pointer and is followed by 
 * a symbol table pointer to a symbol table information saved when
 * the declaration was installed (by private_decls_put).
 * 
 * private_decls is accessed by the
 * following procedures:
 * 
 *	Private_declarations	pdecl;
 *	Symbol	s1,s2;
 * 
 *	private_decls_new(n) - allocate new tuple for n symbols
 * 
 *	private_decls_put(pdecl,s1);
 *	Install s1 in pdecl if not yet present. Copy current symbol
 *	table field values for s1 into saved entry in pdecl.
 * 
 *	Symbol private_decls_get(pdecl,s1)
 *	Return entry in pdecl for s1 if present, (Symbol)0 otherwise.
 * 
 *	private_decls_swap(s1,s2)
 *	swaps symbol table blocks for s1 and s2.
 */
typedef struct Private_declarations_s 
{
	Tuple	private_declarations_tuple;	
} Private_declarations_s;
typedef Private_declarations_s	*Private_declarations;


typedef struct	Forprivate_decls {
	Tuple	forprivate_tup;
	int	forprivate_i;
	int	forprivate_n;
} Forprivate_decls;

#define FORPRIVATE_DECLS(s1,s2,pd,fp) \
     fp.forprivate_tup = (Tuple) (pd)->private_declarations_tuple; \
     fp.forprivate_n = tup_size(fp.forprivate_tup) ; \
      for (fp.forprivate_i=1; fp.forprivate_i<=fp.forprivate_n;) { \
	s1 = (Symbol) fp.forprivate_tup[fp.forprivate_i++]; \
	s2 = (Symbol) fp.forprivate_tup[fp.forprivate_i++];

#define ENDFORPRIVATE_DECLS(fp) }

/*

NA_PACKAGE_SPEC:
----------------
overloads: not used
signature: not used

NA_PRIVATE_PART:
----------------
 * 'private_part': for technical reasons, it is convenient to regard the
 *	  private part of a package specification as a scope in its own
 *	  right. This simplifies the segregation of private declarations
 *	  from visible ones, and the detection of sundry semantic errrors
 *
overloads:	not used
signature:	not used

NA_PROCEDURE:	
-------------
Denotes a symbol table slot for a procedure subprogram.

type_of: holds the marker NULL (ie., a null pointer).

signature: describes the formal parameters of the procedure.
It is a tuple of symbol table pointers to formal parameter entries 
(of type na_in, na_out, or na_inout).

overloads: the set of procedures with the
same name (source identifier, that is) which appear in the
current lexical scope, and which are
not hidden by the current entry. This set is built when the
procedure specification is processed (See procedure : chain-
overloads in the semantic actions) and is central to the
overload resolution mechanism.
overloads(id) always includes -id- itself.

If the procedure is the only visible instance of the name,
(i.e. it overloads no other identifier) then the overloads
entry is the singleton set containing its own name.

alias: ??

declared: ??


NA_PROCEDURE_SPEC:	
------------------

An entry is given this nature after the corresponding subprogram
specification is processed. When the subprogram body is encountered the
specification is examined again, and if it coincides with an existing
symbol table slot, the _spec tag is removed. Apart from generic objects,
all remaining types of entries denote type entities. 

signature:	same as for procedure.

overloads:	same as for procedure.

Other fields same as procedure spec.

NA_TYPE:
--------
This denotes an entry for a new, or derived type
from one of the numeric types 'INTEGER', 'FLOAT',
or '$FIXED', or from another numeric type, or
the error type 'any'.
All such entries have all symbol fields, including alias, defined.

type_of: unique name of the type from which the current one is derived.

signature: the constraint (see 'subtype' below).

Private and incomplete type declarations produce type
entries whose type_of field is 'private','limited private'
or 'incomplete' respectively.

overloads: The map 'misc_type_attributes' collects various useful predi-
cates on types, in particular composite and generic types.
This information is kept in the field type_attr.

In C, misc_type_attributes can be represented as a byte, assigning
a bit for each of the necessary attributes:
flag TA_ISPRIVATE is used only when writing out files in C format
to flag the case of a private or limited private type. This is determined
in SETL by a symbol having a TYPE_OF corresponding to 'private' or
'limited private', and in C by TYPE_OF being symbol_private or symbol_limited
private. For such symbols we set TA_ISPRIVATE when writing the symbol to
indicate that the signature has the same format as for a record (na_record),
even though the nature is not necessarily na_record.

*/

#define TA_ISPRIVATE  1
#define TA_INCOMPLETE 2
#define TA_LIMITED	4
#define TA_LIMITED_PRIVATE	8
#define TA_PRIVATE		16
#define TA_OUT			32
/* GENERIC corresponds to '$generic' in SETL */
#define TA_GENERIC		64
/* CONSTRAIN corresponds to '$constrain' in SETL */
#define TA_CONSTRAIN		128

/*


NA_RECORD:
----------
Denotes a record type.

type_of: the type name itself.

signature: a tuple formatted as follows (in SETL):

	    [ [invariant_part, variant_part], discriminant_list ,
						declared_map, discr_decl_tree ]

the discriminant list is [] for a record without discrimants.
In the above, invariant_part and variant_part refer to AST nodes.

In C version, signature is quintuple as follows:
	[ invariant_part, variant_part, discriminant_list, declared_map,
		discr_decl_tree]
invariant_part, variant_part and discr_decl_tree are nodes.
discriminant list is tuple of symbols.
The declared_map is the (declared) map from selector names
to the unique names which have been assigned to them.
(NOTE: This is redundant if we keep declared for record)

Note that this is initialized in process_discr in ch 3.

overloads:  not used (was misc_type_attributes)

type_attr:  misc_type_attributes


NA_SUBTYPE:
-----------
This denotes an entry for a declared subtype, or for a
range descriptor which has been promoted to a subtype.

type_of: unique name of the type of which the current one is a subtype, 
i.e. its base type.

signature: the constraint which defines the subtype. 
For numeric types, the constraint has one of the
following formats :

		['range' low, high]		for integer subtypes.

		['digits', low, high, digits]	for floating types.

		['delta', low, high, delta,small]	for fixed types.

In each case, -low- and -high- are the bounds of the subytpe.
digits is a SETL integer, delta is a SETL floating point.
Both of them have their standard Ada meaning .
Components other than the first are nodes.

Add CONSTRAINT_DISCR (ds 14 aug) to correspond to 'discr' case
in SETL. For this type numeric_constraint_value[0] will be tuple with
list of discriminant values. 
This will be referenced as numeric_constraint_discr.

Add CONSTRAINT_ARRRY (ds 1 jan 84) to correspond to constrained aray
case. For this type the SETL signature has the same form as form an
array type - a pair whose first component is a tuple of symbols and
whose second component is a symbol. 
In C we keep the signature as a tuple, using CONSTRAINT_ARRAY only when
writing and reading the ais file in c format.

Add CONSTRAINT_ACCESS for subtypes of access types. In SETL, this was
just the designated type. Here, for uniformity of subtypes, we keep
it as a constraint (a tuple whose first element is CONSTRAINT_ACCESS, 
and second is the designated type).  The macro designated_type 
has been changed to reflect this.

In C we represent the constraint as the following structure:
*/
#define CONSTRAINT_RANGE 0
#define CONSTRAINT_DIGITS 1
#define CONSTRAINT_DELTA 2
#define CONSTRAINT_DISCR 3
#define CONSTRAINT_ARRAY 4
#define CONSTRAINT_ACCESS 6

#define numeric_constraint_kind(p) p[1]
#define numeric_constraint_low(p) p[2]
#define numeric_constraint_high(p) p[3]
#define numeric_constraint_digits(p) p[4]
#define numeric_constraint_delta(p) p[4]
#define numeric_constraint_small(p) p[5]
#define numeric_constraint_discr(p) p[2]

/* new instances of above allocated by new_constraint(type) */
/*
   for record subtypes, the constraint as the format :
		['discr', list of discriminant values]
For records we also need the discriminant map. In SETL this is a map
from symbols to nodes. The only operations used are initialization,
assignment, retrieval and interation, so in C we keep this map as a tuple
with successive pairs of elements representing the domain (Symbol) and
range (Node) values.  The following procedures are used to access the
map:
	Node discr_map_get(dmap, sym);
	    Symbol  sym;
	retrieve value of map for symbol sym.

	Tuple discr_map_put(dmap,sym,nod)
	   Symbol  sym; Node nod;
	set value of map dmap for symbol sym to node nod.

Note that symbols corresponding to private types have a signature of
the same form as for a record; see discussion of TA_ISPRIVATE above.

overloads: field present, but not used.

declared: not used

alias: yes, for all types, the root type

*/

/*

NA_TASK_OBJ	
-----------
Denotes a task type. A task object is either an object of
task type, or (in the case of a task family) an array of
objects of task type. A task contains declarations for
entries. Access is obtained by means of the -declared- map for
the task.

type_of: task type
signature: not used
overloads: not used
declared: defined

NA_TASK_OBJ_SPEC
----------------

NA_TASK_TYPE:	
-------------
Same as NA_TASK.

NA_TASK_TYPE_SPEC
-----------------
Same as NA_TASK_TYPE.


NA_VOID
-------
TBSL
A symbol of this type is
generated for the symbol "$used". It has as signature a tuple of symbols:
	signature:	tuple of symbols
corresponding to the macro use_declarations in SETL.

*/



/*
		DECLARED definitions and declarations


In the SETL version, program identifiers are related to unique
names using a global map DECLARED. Every lexical
scope corresponds to an entry in DECLARED. In turn, this entry is a
map from source identifiers to their unique names in that scope.

     DECLARED : scope-name ->  (map : identifier -> unique-name )

The scope manipulation routines and the name resolution routines
revolve around DECLARED. In the SETL code, access is typically via
	DECLARED(SCOPE_OF(name))(identifier)

In C, each symbol table entry has a field scope_of that gives the symbol
table entry of the scope for the entry. The declared field of the entry
for the scope is a pointer to the declared map from identifiers to
symbol table entries. Since access to the declared map involves a hashed
lookup, we will access the map using procedures (or macros that
ultimately invoke procedures). For example, SETL code 
	DECLARED(s)(id)
will become
	dcl_get(s,id)
for retrievial, or
	dcl_put(s,id,sym)
or
	dcl_put_vis(s,id,sym,vis)
to explicitly set visibility: dcl_put(s,id,sym) is same as
	dcl_put_vis(s,id,sym,TRUE);
for assignment,where s will often have one of the forms
	scope_name	or	scope_of(name)

Our intent is that, as much as possible, the existing SETL code can
be translated to C using dcl_get and dcl_put, using a 'paging' algorithm
to bring in names from other compilation units, possibly on library files,
in a manner transparent to most of the code. This paging process will involve
marking names as one of the following:
	installed	symbol table entry available
	not installed	name and location known, but symbol table entry
			not yet installed.
An identifer that is not installed will have an indication of the compilation
unit and 'file address' of the information needed to install the name.
Installation consists of converting the external 'file address' to an
internal pointer.

Note that map VISIBLE maintained in the SETL version is represented in 
the C version by the attribute is_visible associated with an entry
in a declared map.

*/

typedef struct Declaredmap_s
{
	short		dmap_curlen;	/* current number of elements */
	short		dmap_maxlen;	/* maximum number of elements */
	struct Dment	*dmap_table;	/* pointer to entry list */
 } Declaredmap_s;

/* Each entry in the hash table is a pointer to a declared map entry */

typedef struct Dment
{
	struct {
#ifdef IBM_PC
/* avoid overlaying on PC, due to bad generated code  ds 4-26-86 */
	unsigned	dment_idnum ;   /* source identifier number */
	unsigned	dment_visible ;  /* non-zero if visible */
#else
	unsigned	dment_idnum : 15;   /* source identifier number */
	unsigned	dment_visible : 1;  /* non-zero if visible */
#endif
	} dment_i;
	Symbol		dment_symbol;	    /* symbol table pointer */
}  Dment;

/*
dment_id is the character string for the source identifier. dment_hash
is the hash code of the string. This is	 kept so that the hash table
size can be changed as the map grows without avoiding the need to rehash
all the strings. dment_next is a pointer to the next entry on the hash
chain, or NULL for the end of a chain. dment_symbol is a symbol table
pointer for an installed name, or NULL if the name not yet installed.
dment_install is a boolean, initially FALSE, that is set when the
identifier has been installed in the symbol table. Note that it may be
possible to avoid the use of this bit and just say a symbol is not
installed if dment_symbol is NULL. dment_file and dment_fileoff are the
file identifier and file offset; the details of these have to be worked
out. 
*/

/* A tentative list of the procedures that are used to access a declared
map is as follows:

Declaredmap dcl_new(nh)	 int nh;
  initializes declared map with nh hash headers
  (zero may be given, in which case default values
  are taken).

dcl_free(dmap)	Declaredmap dmap;
  free space occupied by declared map dmap.

Symbol dcl_get(dmap,s)	Declaredmap dmap; char * s;
  return current value of declared map dmap for string s, or NULL
  if map not defined for s.

Symbol dcl_get_vis(dmap,s)	Declaredmap dmap; char * s;
  return current value of declared map dmap for string s, or NULL
  if map not defined for s. This returns current value only if it
  is visible.



dcl_put_vis(dmap,str,sym,vis) Declaredmap dmap; char *str; Symbol sym; int vis;
  define value of declared map dmap for string s to be symbol s.
  This sets visible attribute for entered sym to vis.

dcl_put(dmap,str,sym) ...
  same as dcl_put_vis(dmap,str,sym,TRUE).

dcl_undef(dmap,str) Declaredmap dmap, char *str;
  undefine declared map dmap for string s; i.e., remove entry from map
  if present.

The form of an iteration over a declared map is:
  FORDECLARED(str,sym, dmap, dmapiv)
which iterates over declared map dmap using dmapiv to control iteration.
For each pass, str is set to identifier, sym to symbol table pointer.

  Fordeclared dmapiv;
  Declaredmap	dmap;
  char *str; Symbol sym;
  FORDECLARED(str,sym,dmap,dmapiv)

  ENDFORDECLARED(dmapiv)

Within a FORDECLARED iteration, the macro IS_VISIBLE may used to get
visibility status of the current variable, by
	IS_VISIBLE(dmapiv).
ISVISIBLE may be used on the left hand side to change visibility,
	IS_VISIBLE(dmapiv) = 0	.
*/
typedef struct	Fordeclared {
	Declaredmap fordeclared_map;
	unsigned short	fordeclared_i;
	unsigned short	fordeclared_n;
	struct Dment *fordeclared_dment;
} Fordeclared;

extern char *dstrings;

#define FORDECLARED(str,sym,dmap,iv) \
    iv.fordeclared_map = dmap; \
    iv.fordeclared_n = iv.fordeclared_map->dmap_curlen;\
    iv.fordeclared_dment = iv.fordeclared_map->dmap_table; \
    for (iv.fordeclared_i=0; iv.fordeclared_i<iv.fordeclared_n; \
	(iv.fordeclared_i++,iv.fordeclared_dment++)) { \
	  str = dstrings + iv.fordeclared_dment->dment_i.dment_idnum;\
	  sym = iv.fordeclared_dment->dment_symbol;\

#define ENDFORDECLARED(iv) }
#define IS_VISIBLE(iv) iv.fordeclared_dment->dment_i.dment_visible 
#define SETDECLAREDVISIBLE(iv,n) \
	IS_VISIBLE(iv) = n;	
/*
The form of an iteration over a declared map, visiting only the visible
entries, is:
  FORVISIBLE(str,sym, dmap, dmapiv)
which iterates over declared map dmap using dmapiv to control iteration,
processing only visible entries.
For each pass, str is set to identifier, sym to symbol table pointer.

  Fordeclared dmapiv;
  Declaredmap	dmap;
  char *str; Symbol sym;
  FORVISIBLE(str,sym,dmap,dmapiv)

  ENDFORVISIBLE(dmapiv)


*/
#define FORVISIBLE(str,sym,dmap,iv) \
	FORDECLARED(str,sym,dmap,iv) \
		if (IS_VISIBLE(iv)==0) continue;


#define ENDFORVISIBLE(iv) }

/* Declarations for use by evalstat. 
 * Values returned by evalstat are as follows:
 */

typedef struct Const_s	*Const;
typedef struct Const_s {
	int	const_kind;
	union	{
		int	const_int;
		int	*const_uint;
		double	const_real;
		char	*const_str;
		Rational	const_rat;
		long	const_fixed;
		} const_value;
	} Const_s;

#ifdef IVALUE
/* Const should be ivalue. Define both until Sem changed */
typedef struct Ivalue_s *Ivalue;
typedef struct Ivalue_s {
	int	ivalue_kind;
	union	{
		int	ivalue_int;
		int	*ivalue_uint;
		double	ivalue_real;
		char	*ivalue_str;
		Rational	ivalue_rat;
		long	ivalue_fixed;
		} ivalue_value;
	} Ivalue_s;
#endif
/* kinds for const_kind */
#define CONST_OM	0
#define CONST_INT	1
#define CONST_REAL	2
#define CONST_STR	3
#define CONST_RAT	4
#define CONST_CONSTRAINT_ERROR 5
#define CONST_UINT	6
#define CONST_FIXED	7

/* predicates for const_kind */
#define is_const_om(c) ((c)->const_kind == CONST_OM)
#define is_const_int(c) ((c)->const_kind == CONST_INT)
#define is_const_real(c) ((c)->const_kind == CONST_REAL)
#define is_const_str(c) ((c)->const_kind == CONST_STR)
#define is_const_rat(c) ((c)->const_kind == CONST_RAT)
#define is_const_constraint_error(c) ((c)->const_kind == CONST_CONSTRAINT_ERROR)
#define is_const_uint(c) ((c)->const_kind == CONST_UINT)
#define is_const_fixed(c) ((c)->const_kind == CONST_FIXED)

/* kinds for const_kind */
#ifdef IVALUE
/* CONST_ should be IVALUE_. Define both until convert Sem */
#define IVALUE_OM	0
#define IVALUE_INT	1
#define IVALUE_REAL	2
#define IVALUE_STR	3
#define IVALUE_RAT	4
#define IVALUE_CONSTRAINT_ERROR 5
#define IVALUE_UINT	6
#define IVALUE_FIXED	7
#endif

/* Macros to access values of a Const */
#define INTV(op) (op)->const_value.const_int
#define UINTV(op) (op)->const_value.const_uint
#define REALV(op) (op)->const_value.const_real
#define RATV(op) (op)->const_value.const_rat
#define FIXEDV(op) (op)->const_value.const_fixed

	
/* The SETL maps rename_map and type_map are maps from symbols
 * to symbols. In the C version these are kept as type Symbolmap,
 * currently represented using a tuple map, i.e.,  a tuple with
 * successive pairs of domain values followed by the range value.
 */

typedef struct Symbolmap_s 
{
	Tuple	symbolmap_tuple;	
} Symbolmap_s;
typedef Symbolmap_s	*Symbolmap;
/* and is accessed using the following procedures (defined in 12.c): */

/*
Iteration over symbolmaps is done as follows:
 */
typedef struct	Forsymbol {
	Tuple	forsymbolmap_tuple;
	int	forsymbolmap_i;
	int	forsymbolmap_n;
} Forsymbol;

#define FORSYMBOL(s1,s2,pd,fp) \
     fp.forsymbolmap_tuple = (Tuple) (pd)->symbolmap_tuple; \
     fp.forsymbolmap_n = tup_size(fp.forsymbolmap_tuple) ; \
      for (fp.forsymbolmap_i=1; fp.forsymbolmap_i<=fp.forsymbolmap_n;) { \
	s1 = (Symbol) fp.forsymbolmap_tuple[fp.forsymbolmap_i++]; \
	s2 = (Symbol) fp.forsymbolmap_tuple[fp.forsymbolmap_i++];

#define ENDFORSYMBOL(fp) }

typedef struct Nodemap_s 
{
	Tuple	nodemap_tuple;	
} Nodemap_s;
typedef Nodemap_s	*Nodemap;
/*
 *T+ UTILITY MACROS FOR SEMANTIC MODULES.
 *S+ Global macros for the use of all modules:
*/

/* We define the utility macros in lower case since that is the
 * case used in the SETL source.
 */

/* macro find;	assert exists		endm; */
#define find ???

/* macro top(x);	x(#x)			endm; */

/* *S+ Macros for manipulation of the AST. */

/*macro is_empty(node);	 (node=[])	  endm ; */
#define is_empty(node) ((int)node[0] == 0)

/* macro attribute_name(node) ; ;N_VAL(N_AST(node)(1))	endm; */
/* In C this returns integer attribute code stored in ast1 node of  node */
/* this returns integer not string */
#define attribute_name(node) N_VAL(N_AST1(node))

/* In C we define attribute_kind to return integer attribute code */
#define attribute_kind(node) N_VAL(N_AST1((node)))

/*
macro SYMBTAB(name);
    [NATURE(name),TYPE_OF(name),SIGNATURE(name),OVERLOADS(name)] endm;
*/

/*
 * For library and stub manipulation, the scope_of map must also
 * be saved and restored. The following macro is usedfor that purpose.
 */

/*
macro SYMBTABF(name) ;
    [NATURE(name), TYPE_OF(name), SIGNATURE(name), OVERLOADS(name),
     SCOPE_OF(name), ALIAS(name) ]
endm ;
*/

/*
 * The following is a lexical macro which converts a double-quoted
 * character which appears as a designator, into a one-character
 * string. This distinction is imposed by the need to differentiate
 * the literal	a  from the character  "a"  when they appear in an
 * enumeration literal, but nowhere else.
 */

/*macro char_to_name(desig) ;
(if # desig = 3 and desig(1) = '"' and desig(3) = '"' then
      desig(2) else desig end)
endm ;
*/

/* *S+ Macros for accessing type information. */

/* macro root_type(type_mark) ;	 ALIAS(type_mark) endm ;  $$ES68 */
#define root_type(type_mark) ((type_mark)->alias)

/*
macro index_types(array_type) ;
	signature(array_type)(1) endm ;
*/
#define index_types(array_type) ((Tuple) ((array_type)->signature)[1])

/*
 * macro component_type(array_type) ;
 *  signature(array_type)(2)
 * endm ;
 */
#define component_type(array_type) ((Symbol) ((array_type)->signature)[2])

/*
macro no_dimensions(array_type) ;
	(#index_types(array_type))
endm ;
*/

/*
macro index_type(array_type) ;
	(index_types(array_type)(1))
endm ;
 */
#define index_type(array_type)	((Tuple) (index_types(array_type))[1])

/*
macro literal_map(enumeration) ;
	overloads(enumeration)
endm ;
 */
#define literal_map(enumeration) ((enumeration)->overloads)

/* macro record_declarations(record); signature(record) endm ; */
#define record_declarations(record) ((record)->signature)

/* In C, will have the following reference a single quadruple
   ds	14 aug
 */
/* macro all_components(record) ;     signature(record)(1) endm ; */
#ifdef TBSN
-- all_components should be dead	ds 14 aug
#define all_components(record) (((record)->signature)[1])
#endif

/* the macros for records that access components of the signature
 * cannot be written on the left hand side due to use of (Tuple)
 * cast to get indexing right. The left hand case is done by
 * explicit assignment; see record_decl(3b.c) and process_discr (3b.c).
 * ds 31-dec-84
 */
/* macro discriminant_list(record) ;  signature(record)(2) endm ; */
#define discriminant_list(record) ((Tuple) ((record)->signature)[3])

/* macro invariant_part(record) ;     all_components(record)(1) endm ;*/
#define invariant_part(record) ((Tuple) ((record)->signature)[1])

/* macro variant_part(record) ;	   all_components(record)(2) endm ; */
#define variant_part(record)	((Tuple) ((record)->signature)[2])

/* macro declared_components(record); signature(record)(3) endm ; */
/* The value returned by declared_components is a declared map */
#define declared_components(record) ((Tuple) ((record)->signature)[4])

/* TBSLshould this be four or five  ds 14 aug */
/* macro discr_decl_tree(record);     signature(record)(4) endm ; */
#define discr_decl_tree(record) ((Tuple) ((record)->signature)[5])
/*
macro has_discriminants(record) ;
      (discriminant_list(root_type(record)) /= [])		   endm ;
 */

#define has_discriminants(record) \
	(discriminant_list(root_type(record)) != (Tuple) 0  &&   \
	 tup_size(discriminant_list(root_type(record))) != 0)


/*
macro designated_type(access_type) ;
			(signature(access_type))	     endm ;
*/
/* In the C version, the signature of a subtype of an access type is a
 * tuple whose first element is CONSTRAINT_ACCESS, and whose second
 * is the designated type symbol
 */
#define designated_type(access_type) 					 \
	(((NATURE(access_type)==na_subtype) 				 \
		? (Symbol)((access_type)->signature)[2] 		 \
		: (Symbol)((access_type)->signature) ))

/*
macro is_range_attribute(e) ;
     (is_tuple(e) and e(1) = '''' and e(2) = 'RANGE')	     endm ;
*/

/* macro label_status(lab) ; signature(lab)		     endm ; */
#define label_status(lab) ((lab)->signature)

/* default_expr has a node as its value (ds 15 may) */
/* macro default_expr(nam) ; signature(nam)		     endm ;*/
#define default_expr(nam) ((nam)->signature)

#define formal_decl_tree(proc_name)  ((proc_name)->init_proc)
   /* formal_decl_tree stores the formals subtree for subsequent conformance
    * checks. It is defined for a subprogram_spec only, and therefore
    * overlays the init_proc fields used during code generation .
    */

/* *S+ Macros for scope manipulation. */

/* *$BB5 */
/*
macro init_scope_info ;
    ['STANDARD#0', '', ['STANDARD#0', 'UNMENTIONABLE#0'], [],
     ['ASCII'], ''
    ]
endm;
*/

/*
macro is_comp_unit ;	(#scope_st = 0)	     endm ;

macro scope_info ;
    [scope_name, prefix, open_scopes, used_mods, vis_mods, suffix]
endm ;
*/


/* make c macro name upper case since no arguments*/
#define IS_COMP_UNIT (tup_size(scope_st)==0)

 /*S+ Miscellaneous type predicates.*/
/*macro is_access(name) ;
    (NATURE(root_type(name)) = na_access)		  endm ; 
*/
/* is_access now a procedure in the C version (smisc.c) */

/*macro is_identifier(name) ; is_string(name)	endm ; */
/*
Make this a procedure int is_identifier();*/

/*macro is_literal(name) ; nature(name) = 'literal'	  endm ; */
#define is_literal(name) (NATURE((name)) == na_literal)

/*macro is_overloaded ; (is_set(name))	  endm ; */
/* this is field N_OVERLOADED in C version */

/*  macro is_constant(name) ;
    (is_identifier(name) and nature(name) = 'constant') endm ;
*/
/* In C is_identifier for symbol is just test that not null */
#define is_constant(name) ((name)!=(Symbol) 0 && NATURE((name))== na_constant)

/*macro is_proc(proc_name) ;
    nature(proc_name) in
     {'procedure', 'function','generic_procedure', 'generic_function'} endm;
*/
/*
#define is_proc(proc_name) ( (TMP := nature(proc_name) == na_procedure ? 
TRUE : (TMP == na_function || TMP == na_generic_procedure \
  || TMP == na_generic function) ? TRUE : FALSE ) )
*/

/*macro is_anonymous(typ) ; (original_name(typ) =='') endm ;*/
/* in C anonymous types are given an original name beginnning with & */
#define is_anonymous(typ)  (*(ORIG_NAME(typ)) == '&')

/*macro is_first_named_subtype(typ);  (is_anonymous(base_type(typ))) endm;*/

/* macro is_array(typ) ;  (nature(base_type(typ)) = 'array')   endm ; */
#define is_array(typ) (NATURE(base_type(typ)) == na_array)

 /**$PK3 ES118 */
/*
macro is_formal(id) ;  (nature(id) in ['in', 'out', 'inout']) endm ;
*/
#define is_formal(id) (NATURE(id)==na_in || NATURE(id)==na_out	 \
			|| NATURE(id)==na_inout)

/*
macro is_generic(scope ; nat) ;
  ((nat:=nature(scope)) /= om and match(nat,'generic_') /= om)
endm ;
*/

/* macro misc_type_attributes(type_mark) ;
				overloads(type_mark)	    endm;
*/
/* In C misc_type_attributes are kept in separate field */
#define misc_type_attributes(type_mark) TYPE_ATTR(type_mark)

/*
macro private_dependents(type_mark) ;				 $$ES132
		misc_type_attributes(type_mark)		    endm;
*/
/* In C, private_dependents is kept in overloads field 
 */
#define private_dependents(type_mark)	OVERLOADS(type_mark)

/* macro private_decls(package);	overloads(package) endm; */

/* this yields a tuple	ds 25 jul */
#define private_decls(package) OVERLOADS(package) 

/*
 *$ES48
macro use_declarations(package) ;
	signature(declared(package)('$used'))		    endm;
*/
/* Since use_declarations appears on left hand side - we avoid
 * defining a macro for it in C (at least for now)	ds 4 aug 
 */
#ifdef TBSN
#define use_declarations(package) \
	SIGNATURE(dcl_get(DECLARED(package),"$used"))
#endif


/*
macro is_anonymous_task(name) ;
	(is_task_type(name) and 'task_type:' in original_name(name))
endm ;
*/
/* make a procedure in C (by not defining as macro!) */

/*
macro is_integer_type(x) ;
(x in {'INTEGER', 'SHORT_INTEGER', 'LONG_INTEGER', 'universal_integer'})
endm ;
*/

/*
 * The following macro is used by cross-reference making statements.
 * spans(node) is either [l_span] or [l_span, r_span] ,
 * l_span := [line_no, col1, col2].

macro TO_XREF(name) ;
if spans /= om and spans(current_node) /= om then
    XREF(name) := ( XREF(name) ? {} ) +
		      { spans(current_node)(1)(1) } ;
end if
endm;
*/
#define TO_XREF(name)

#define TO_ERRFILE(text) to_errfile(text)

/* streq() in misc.c tests strings for equality */

#define		errmsg_l(msg1,msg2,lrm,node)		\
			errmsg(strjoin(msg1,msg2),lrm,node)
#define		errmsg_l_id(msg1,msg2,name,lrm,node)	\
			errmsg_id(strjoin(msg1,msg2),name,lrm,node)
#define		errmsg_l_str(msg1,msg2,str,lrm,node)		\
			errmsg_str(strjoin(msg1,msg2),str,lrm,node)
extern int N_DEFINED[];

/* power_of_2. In SETL this procedure returns a tuple. In C it sets
 * global variables whose names begin with power_of_2_. Also needed
 * are two constants corresponding to the SETL strings 'exact'and
 * 'approximate'.
 */
#define POWER_OF_2_EXACT 0
#define POWER_OF_2_APPROXIMATE 1

#ifdef GEN
#include "ghdr.h"
#endif

#define TAG_RECORD              0
#define TAG_TASK                1
#define TAG_ACCESS              2
#define TAG_ARRAY               3
#define TAG_ENUM                4
#define TAG_FIXED               5
#define TAG_INT                 6
#define TAG_FLOAT               7

#endif
