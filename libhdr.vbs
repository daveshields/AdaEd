/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* header file for libfile*/
#ifndef _libhdr_h
#define _libhdr_h
/*

Changes:

20-aug-85
delete fs_symbol_orig_name field since it is dead.

25-june-85
add field ev_nodes to Stubenv to store unit_nodes for a stub.

12-mar-85
Add fields f_node and f_symbol for generator fields. This version of
libhdr.c built starting from sem version 1.17 and should be merged
with sem libhdr.c ASAP

12-dec-84	ds
Replace use of tuple for unit_decl values by struct.
Change AIS version to 1.

18-nov-84	ds
Need to keep record of root node: change calling sequence of write_tre,
add new (last) entry to ref_info with sequence number of root node.

16-nov-84	ds
Add f_node_spans[4] fields for span information.
add f_symbol_type_attr for type_attribute field information.
-------
This file documents features related to separate compilation.

Information about separate compilation is kept in three files:
	TRE	holds abstract trees for one or more units
	AIS	holds symbol table and additional info for one or
		more units
	LIB	indicates which TRE and AIS files to use.

The format of the ais and tree files is kept in the file header block
(described below). This header block includes a version indication
that should be changed whenever the format is changed:
The version numbers are defined in config.h  (ds 9-16-85).
*/

/*
We begin by describing the representation in C of the data structures
needed and the additional procedures introduced. We then discuss the
actual formats used for the external file representation in C.

unit names		*;UNIT_NAMES
----------------------
A unit_name is represented by a single string. The first two characters give 
the unit type:
	su	subprog
	ss	subprog spec
	sp	package spec
	bo	package body
The unit type is followed by the unit name.
This name may be followed by the names of depedent units, each preceded
by a period in the case of subunits.
The following procedures are provided to assist in checking the
attributes of unit_names:
	char *unit_name_type(uname)
		returns first two chracters
	char *unit_name_name(uname)
		returns the second field (i.e, rest starting with 3rd char
	char *unit_name_names(uname)
		returns all names, beginning with the second field.
	char *unit-name_tail(uname)
		returns names, starting with third field, or null string.

*/
	
/*
Unit numbers		*;UNIT_NUMBERS
------------
Each compilation unit has a unique unit number. 
Once assigned, this unit number does not change. The procedure
	unit_number(unitname)
gives the unit number of the unit with name unitname. 
unit_number will assign a number if none yet assigned and initialize
related data structures (cf. descriptions of lib_info, ais_info and
tre_info below). To see if a unit has been numbered, that is, encountered
before, use the procedure
	unit_numbered(unitname)
which returns the unit number if a unit number has already been assigned,
0 otherwise.
The global
	 int unit_numbers 
gives the number of units for which units numbers have been assigned.
Nodes in the AST belonging to the unit have their N_UNIT field set to the 
unit number; symbols have their S_UNIT field set to the unit number. 
Unit numbers begin with one, except that symbols in the scope 'standard' 
have unit number zero.
The names of compilation units are kept in the tuple unit_names.
unit_names[i] is name of the compilation unit with compilation unit
number i. If

	i = unit_number(uname);
then
	unit_names[i] is uname.
*/

/*
Sequence numbers		*;SEQUENCE
----------------
While compiling a unit, the (global) tuples seq_node (for nodes)
and seq_sym are kept to track the location of allocated nodes and
symbols.
seq_node[0] is maximum number, seq_node_n is number
actually allocated, so allocatin sequence is
	if ((seq_node_n = (int) seq_node[0]) {
		seq_node = tup_exp(seq_node,seq_node+SEQ_NODE_INC);
	}
		seq_node_n += 1;
		seq_node[seq_node_n] = ...
To reset so can reuse list, just set seq_node_n = 0.
 */

/*
Library Files.		*;LIBRARY_FILES (Internal)
--------------
In SETL a library consists of two maps defined on unit names.
The first yields a tuple [LIB_COUNT,LIB_TREE, LIB_UNIT] where LIB_COUNT
is an integer, LIB_TREE is the name of the TREE file, and LIB_UNIT is
the name of the AIS file. The second, LIB_STUB is a map to file names.

The unit name is expressed in the standard string form used within
the C version. 
The unit index is used to access the global tuple
	lib_info
lib_info[i] is a tuple with components as follows:
1)	name of ais (tre) file
Additional entries may be allocated later. The following macro gives
the length of each tuple in lib_info:
 */
#define LIB_INFO_TUPLEN		5

/*
LIB_UNIT		*;LIB_UNIT
--------

As for LIB_UNIT, in SETL this is a map from unit_name's to (ais) file names.
In C we maintain it using the following procedures:

char *lib_unit_get(uname)
	char	*uname;
 returns filename or null string pointer ( (char *) 0).

lib_unit_put(uname,fname);
	char	*uname,*fname;
 set filename for unit uname to be fname.

These routines access lib_info as described above.

Similar routines are provided for lib_stub.

 */


/*
In SETL the AIS file consists of five maps: COMP_DATE, PRE_COMP,
UNIT_DECL and STUB_ENV. We now discuss how each is represented
in the C version.

COMP_DATE			*;COMP_DATE
 In the SETL version a compilation date is kept as a tuple of three components:
 the date, the time and the compilation unit number. In the C version,
 the date and time are as computed by greentime() (misc.c).
 greentime(un) returns a string of 23 characters, formatted as follows:
	123456789a123456789b123
	1984 10 02 16 30 36 uuu
 where uuu is unitnumber un converted to string.
The COMP_DATE map in SETL is maintained in C using the following
procedures:
	char *comp_date_get(unitindex,unitname)
		int	unitindex;
		char	*unitname;
	comp_date_put(unitindex,unitname,unitdate)
		char	*unitdate;

 where unitindex is unit index returned by compunit_index, unitname
 is the unit name, and unitdate is a string.

 The SETL code sequence

	if COMP_DATE(spec_name)= om then om
	else COMP_DATE(spec_name)(spec_name) end;
 occurs several times and is represented in C by
	versions_used_update(spec_name);
 The SETL map versions_used is kept in C as a tuple, with i-th
 component being unit name (string), and i+1-st component being
 value (a tuple).
   The SETL version also has map versions_used which is maintained in
   the same way.

 */

/*
PRE_COMP			*;PRE_COMP
PRE_COMP is a list of unit names that need to be compiled before this
unit. In SETL it is kept as a set. In C it is kept as a tuple.
*/

/*
UNIT_DECL			*;UNIT_DECL
---------
In SETL, UNIT_DECL is a map from unit names to tuples. In C, the structure
Unitdecl is used instead of tuples. We first describe the use of UNIT_DECL
in SETL.  Note that in SETL the first two components are the same for 
each unit type.

SUBPROGRAM: (unit type "su"or "ss")
In the SETL version, UNIT_DECL for a subprogram is a tuple with the
following components:

1) UNIT_NAM:  unit name
2) S_INFO:  a map from unique names to their symbol table fields, computed
	by unit_symbtab(10).
3) DECMAP:  declared map
4) CONTEXT:  tuple of with and use clause names
5) UNIT_NODES: tuple of nodes
See for instance, subprog_body (6)
Note that components CONTEXT and UNIT_NODES were recently added, 
cf. save_comp_info(10).
CONTEXT is a tuple of with and use clauses; each entry is a pair,
the first component is either AS_WITH or AS_USE, the second component
is a tuple of strings.

The declaration for the struct used is as follows:
*/
typedef struct Unitdecl_s
{
	Symbol	ud_unam;  /* unit name */
	int	ud_unit;  /* unit number of unit name     */
	int	ud_useq;  /* sequence number of unit name */
	Tuple	ud_context;
	Tuple	ud_nodes;
	Tuple	ud_symbols;
	Tuple	ud_decscopes;
	Tuple	ud_decmaps;
	Tuple	ud_oldvis;
} Unitdecl_s;

typedef Unitdecl_s *Unitdecl;

typedef struct Stubenv_s
{
	Tuple	ev_scope_st;
	Tuple	ev_open_decls;
	Tuple   ev_nodes;
	Symbol	ev_unit_unam;
	Declaredmap ev_decmap;
	Tuple	ev_context;
	int	ev_current_level;
	Tuple	ev_relay_set;
	Tuple   ev_dangling_relay_set;
} Stubenv_s;

typedef Stubenv_s *Stubenv;
/*
ud_type is string giving unit type, "ss" for subprogram spec, etc.
ud_unum is the unit number.
ud_unam is symbol table pointer for unit name.
ud_useq is sequence number of ud_unam symbol.
ud_context is tuple of use and with clauses. Each clause is a tuple with
two components. The first component is the kind: AS_WITH or AS_USE; the second
component is a tuple of strings.
ud_nodes is a tuple of nodes.
ud_symbols is a tuple of symbols.
ud_decscopes is a tuple of symbols.
ud_decmaps is a tuple of declared maps.
ud_oldvis is a tuple of strings naming units formerly visible.
 
In the C version, the following fields are used:
Field		SETL component		name
ud_unam		1			UNIT_NAM
ud_useq		1			"
ud_symbols	2			S_INFO
ud_decscopes    3			DECMAP
ud_decmaps	3			DECMAP
ud_context	4			CONTEXT
ud_nodes	5			UNIT_NODES


PACKAGE (unit type "sp")
-------
In the SETL version, UNIT_DECL for a package is a tuple as follows:
1)  UNIT_UNAM: the unit name
2)  SPECS:  a map from unique names to their symbol table fields,
	computed by unit_symbtab (10).
3)  DECMAP:  a map from scopes to declared maps
4)  OLD_VIS:  a tuple of units formerly visible
5)  NOTVIS:  similar to decmap this is map from scopes to  declared maps,
	but kept only for non-visible entries. This is used to reconstruct
	the visible map.
6) CONTEXT: as for subprogram
7) UNIT_NODES: as for subprogram

Cf, module_body(7), get_specs(7).

In the C version, the following fields are used:
Field		SETL component		name
ud_unam		1			UNIT_UNAM
ud_useq		1			UNIT_USEQ
ud_symbols	2			SPECS
ud_decmaps	3			DECMAP (see below)
ud_decscopes	3			DECMAP (see below)
ud_oldvis	4			OLD_VIS
(not needed)	5			NOTVIS (see below)
ud_context	6			CONTEXT
ud_nodes	7			UNIT_NODES

In the C version, notvis is not necessary since we are keeping the visible
attribute as part of the declared map. In the C version, we keep decmap
as two tuples: a tuple of scopes and a tuple of pointers to their
corresponding declared maps.

PACKAGE_BODY (unit type "bo")
The SET version has
1) unit name
2) unit_symbtab, as compued by unit_symbtab (10).
3) context
4) unit_nodes

unit_type: "bo"
The C version has
In the C version, the following fields are used:
Field		SETL component		name
ud_unam		1			UNIT_NAME
ud_useq		1			UNIT_NAME
ud_symbols	2			UNIT_SYMBTAB
ud_context	3			CONTEXT
ud_nodes	4			UNIT_NODES


Note that the components are same as for PACKAGE, except there are only
five of them.
Cf. save_body_info (10).

The SETL map UNIT_DECL is maintained in C by the following procedures:

unit_decl_put(s,t)
	char	*s;
	Unitdecl	t;
  save info t for unit with unit_name s

Unitdecl unit_decl_get(s) 
	char *s;
  return saved (by unit_decl_put) info for unit_name s.
  returns (Unitdecl) 0 if no such saved tuple exists.

*/


 
/*
CODE_UNITS			*;CODE_UNITS
In SETL CODE_UNITS is the tuple produced by emit. In the C version this
is not needed, and is always a null tuple.
*/

/*
STUB_ENV			*;STUB_ENV
In SETL, STUB_ENV is a tuple with seven entries. See save_stub (10) for
exact details of components. The C representation of STUB_ENV is still
open.
 */

/*
AIS_INFO			*;AIS_INFO
The maps COMP_DATE, etc. maintained in the SETL version are maintained 
in
the tuple ais_info indexed by unit number. Each entry is a tuple,
as follows:
1) COMP_DATE
2) PRE_COMP
3) UNIT_DECL
4) CODE_UNITS
5) STUB_ENV
6) SYMBOLS: number of symbols
7) SYMPTR: tuple such that SYMPTR[i] is pointer to symbol table
	entry allocated for symbol with sequence number i.
	When writing the file, this is a copy of SEQ_SYMBOL.
8) SYMOFF: ptr to array of longs SYMOFF such that SYMOFF[i] is file offset
	of start of information for symbol with sequence number i.
	The array SYMOFF is stored in the file starting at offset SOFFSET.

The length of each tuple in ais_info is given by:
*/
#define AIS_INFO_TUPLEN		8

/*
PREDEF_UNITS			*;PREDEF
------------
In SETL PREDEF_UNITS is a set of unit_names. 
In C, it is a tuple 'predef_units', accessed using the following procedures 
(the standard tuple operations less and with cannot be used since elements 
are strings):

	in_predef_units(u) char *u;
	returns TRUE if u is in predef_units
	
	predef_units_with(u,s) char *u; Symbol s;
	adds u to predef_units

	predef_units_less(u) char *u;
	removes u from predef_units;

 */

	
/*
LIB FILE			*;LIB FILE (External)
LIB File		*;LIB FILE (external)
The C representation of a library file (LIB) will be as a text file.
The first line gives the number of entries in the first map.
The following information is maintained for each unit in the lib (one line per
unit).
	unit name,
	unit number
	name of AIS (TRE) file
The next line gives the number of entries in the LIB_STUB map.
There follow two lines for each entry (or no further lines if the
entry count is zero): the first is the unit name, the second is the
name of the file containing the translation of the stub of the subunit.

For example:
1			number of entries	
suMAIN			type and name of first unit
1			unit number of first unit
main			name of ais (tre) file	
0			number of entries in LIB_

The procedure read_lib reads in a library file and updates lib_names
and lib_info. The procedure write_lib writes lib_names and lib_info
to the library file in the text format described above.
 */
	
/*
Header block		*;HEADER
-----------------------------------------------
The TRE and AIS files produced by the C version each
contains information for one or more compilation units.

Character strings are represented in these files as follows:
The undefined string - (char *) 0 - is written as zero. Otherwise
there is written
an integer (int) giving the number of characters in the string
(including the trailing null byte). This word is followed
by the specified number of bytes (the trailing null byte does
not appear in the file). 

In the file references to symbols and nodes are indicated by
writing the unit and sequence numbers, respectively, each in
a word (int). An optimization, NOT implemented now, would be
to suppress the unit number if it is that of the unit being
written, writing a negative sequence number in this case.

Each of the files begins with a standard header block:
	char	type ('a' for ais, 't' for tre files)
	char	version
The current versions are defined by the macros AIS_VERSION and
TRE_VERSION.

Each records begins with a long word giving offset (from start of file) 
of start of next record. For the last record this will be a value greater
than the file length, or zero if no records in file.

To open a tree or ais file, use:

	FILE *open_file(fname,mode,type)
	    char *fname,*mode,type

where fname is the file name, mode the file mode ("r" or "w") and
type is 'a' or 't' for ais or tree file, respectively.

When writing a file, begin a record with

	long	begpos;
	begpos = write_start();

and do

	write_end(begpos)

when record done to update pointers kept in the file.

To read a file, use the sequence:

	long	record,read_init(),read_next();
	for	(record=read_init; record!=0; record=read_next(record)) {
		...
	}

*/

/*
TREE File Structure			*;TREE
-------------------
A tree file has the standard header block. 
The tree for each unit is formatted as follows:
	(str)	unit name
	(int)	unit number
	(int)	number of items (nodes)
	(long)	N+1 longs, the i-th gives the file offset (if any)
		of node with sequence i, etc.
	(int)	sequence number of root node.
	(...)	The entries for the nodes follow, in format as
		described below (cf. putnod).
*/


/* The information for the following fields is optional:
	n_list
		shorts representing node references
	n_val
		the format varies according to the n_kind, see
		putnval (and getnval) for details
	
	the N_NAMES and P_TYPES maps are irrelevant after semantic
	processing and therefore, are not written.

The global tuple tre_info contains information about a tree that has
been read in. For  unit number i, tre_info[i] is a tuple as follows:
1) NODES: number of nodes
2) NODPTR: Tuple such that NODPTR[i] is ptr to node with sequence
	number i.
	When writing the file, this is a copy of SEQ_NODE.
	When reading the file, this is used to create SEQ_NODE.
3) NODOFF: ptr to array of longs NODOFF such that 
	NODOFF[i] is file offset of node with sequence number I.
	This array is stored in the file at offset NOFFSET.
4) NODROOT: sequence number of root node.
*/
#define TRE_INFO_TUPLEN 4

/*
AIS File Structure			*;AIS
------------------
An AIS file contains one or more compilation units. 
The file begins with the standard header block, type 'a'.

The data for each compilation unit as follows:
	(str)	unit name
	(int)	unit number
	(long)	offset to code generator information (or 0 if no info yet)
	(int)	number of items (symbols) N
	(long)	N+1 longs, the i-th gives the file offset (if any)
		of symbol with sequence i, etc.
There follows the initial ais_info values, as follows:
COMP_DATE: 
	(int)	number of entries
each entry is as follows:
	(str)	name of first unit
	(str)	name of second unit

PRE_COMP:
	(int)	number of entries
each entry is a string.

UNIT_DECL:
The first four components in the C form are always the same:
1) Symbol table for unit
2) Sequence number of (1)
3) Context: tuple of use and with clauses 
4) UNIT_NODES:tuple of nodes
These are written to the file as follows:
(int)		sequence number
There follows context, a tuple: each entry is itself a tuple
with the first component written as an int, the second as a string.
There follows UNIT_NODES: a tuple of nodes, written as node references.
The fifth component is always a tuple of symbol table pointers, written
as a tuple of symbol references.

SUBPROG:
In the C version, the UNIT_DECL information is written as follows:
(int)	UNIT_SEQ: sequence number for unit UNIT_NAM symbol
	tuple of symbol table references
DECMAP	declared map.
Declared maps are written as follows. Each entry is written as a 
string, a symbol reference and a byte indicating visibility (zero
for invisible, one for visible). The list ends with an entry with
a null string, a symbol reference with unit and sequence zero, and
a visibility byte of zero.

CONTEXT:  tuple of use and with clause names.
Each entry is written as a word (int) giving clause type, followed
by a string.

UNIT_NODES: tuple of nodes


PACKAGE
-------

	UNIT_SEQ:	sequence number of unit_unam symbol (int)

	SPECS - tuple of symbol table pointers

	DECSCOPES - tuple of scopes

	OLD_VIS - tuple of unit names

	DECMAPS; tuple of declared maps
		this consists of (int) with tuple size followed by
		entry for each declared map.

	CONTEXT: tuple of use and with clauses

	UNIT_NODES tuple of nodes


	CODE_UNITS:
Retained for compatibility, no data written now, just:
	(int)	0

STUB_ENV:
???

The symbol table information follows:
	(int)	number of symbol table entries
Each symbol table entry begins with the standard information
written using the following structure:
 */
typedef struct f_symbol_s
{
	short		f_symbol_nature;		
	short		f_symbol_seq;	
	short		f_symbol_unit;	
	short		f_symbol_type_of_seq;
	short		f_symbol_type_of_unit;
	short		f_symbol_scope_of_seq;
	short		f_symbol_scope_of_unit;
	short		f_symbol_signature;	
	short		f_symbol_overloads;
	short		f_symbol_declared;
	short		f_symbol_alias_seq;
	short		f_symbol_alias_unit;
	short		f_symbol_type_attr;
	/* remaining fields used by code generator */
	short		f_symbol_misc;
	short		f_symbol_type_kind;
	short		f_symbol_type_size;
	short		f_symbol_init_proc_seq;
	short		f_symbol_init_proc_unit;
	short		f_symbol_assoc_list;  /* for _type, etc */
	short		f_symbol_s_segment; /* REFERENCE_MAP segment */
	short	f_symbol_s_offset; /* REFERENCE_MAP offset */
} f_symbol_s;

/* 
  orig_name follows struct if string not empty. It is written by putstr.

  The overloads information is written by procedure putovl.

  The declared map info follows. For symbol with nature na_enum,
  this is literal map (see procedure putlitmap); 
  othwerwise is it declared map in standard format (see procedure putdcl).

  The signature is written by procedure putsig; sese it for
  details on how signature written.
 
*/

#endif
