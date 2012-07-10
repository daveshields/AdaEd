/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* sem0 - part a - initializations */

/* TODO

01-nov-84	ds
delete refs to ast_nodes.
Note that need to review initializatio of symbol_short_integer.

19-oct-84	ds
Review copy_node etc to see if proper fields being copied.
Need to review use of copy_node, copy_attributes.

sort out SEQUENCE_LIST problem, if initial length ever requires reaalloc
call then malloc is 'botched'. For now have large length in place (about
600 elements)  ds 15 jul 84


There is dcl_put in setl to standard, in c to standard0.Things working
 ok now, but sort this out		ds 19 jul
 */

#include "hdr.h"
#include "vars.h"
#include "dbxprots.h"
#include "dclmapprots.h"
#include "arithprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "setprots.h"
#include "chapprots.h"
/* ctype.h needed for isupper, tolower, etc in 4.2 bsd*/

extern int ADA_MIN_INTEGER, ADA_MAX_INTEGER;

static Declaredmap declared_standard0, declared_standard, declared_ascii,
  declared_unmentionable;
static int init_node_count = 1;   /* node 0 is OPT_NODE jc 2/8/86 */
/* NOTE: if change op_desig_array, also change desig_of_op (chap 12)*/
static char *op_desig_array[] = {
	"and", "or", "xor", "not", "mod", "rem", "abs",
	"=", "/=", "<=", "<", ">=", ">",
	"+", "-", "&", "*", "/", "**", 0
};

static Node val_node1(int);
static Node val_nodea1(int);
static Node val_node2(double);
static Node val_node3(Rational);
static void init_node_save(Node);
static Symbol ini_chain(char *, int, Symbol);
static Symbol symbtab_enter(char *, Symbol);
static Symbol new_arith_op(char *, Symbol);
static void ini_new_agg(Symbol);

void init_sem()													/*;init_sem*/
{
	/*
	 * This is the primary initialization procedure.  It is called
	 * when the compiler is initialized.
	 *
	 */

	/*VARDECL*/
	Tuple constr_new;
	int	    i;
	Tuple tup;
	Symbol sym;
	char   *id;
	Fordeclared fd;
	static char *char_names[] = {
		"NUL 0",
		"SOH 1",
		"STX 2",
		"ETX 3",
		"EOT 4",
		"ENQ 5",
		"ACK 6",
		"BEL 7",
		"BS 8",
		"HT 9",
		"LF 10",
		"VT 11",
		"FF 12",
		"CR 13",
		"SO 14",
		"SI 15",
		"DLE 16",
		"DC1 17",
		"DC2 18",
		"DC3 19",
		"DC4 20",
		"NAK 21",
		"SYN 22",
		"ETB 23",
		"CAN 24",
		"EM 25",
		"SUB 26",
		"ESC 27",
		"FS 28",
		"GS 29",
		"RS 30",
		"US 31",
		"EXCLAM 33",
		"QUOTATION 34",
		"SHARP 35",
		"DOLLAR 36",
		"PERCENT 37",
		"AMPERSAND 38",
		"COLON 58",
		"SEMICOLON 59",
		"QUERY 63",
		"AT_SIGN 64",
		"L_BRACKET 91",
		"BACK_SLASH 92",
		"R_BRACKET 93",
		"CIRCUMFLEX 94",
		"UNDERLINE 95",
		"GRAVE 96",
		"LC_A 97",
		"LC_B 98",
		"LC_C 99",
		"LC_D 100",
		"LC_E 101",
		"LC_F 102",
		"LC_G 103",
		"LC_H 104",
		"LC_I 105",
		"LC_J 106",
		"LC_K 107",
		"LC_L 108",
		"LC_M 109",
		"LC_N 110",
		"LC_O 111",
		"LC_P 112",
		"LC_Q 113",
		"LC_R 114",
		"LC_S 115",
		"LC_T 116",
		"LC_U 117",
		"LC_V 118",
		"LC_W 119",
		"LC_X 120",
		"LC_Y 121",
		"LC_Z 122",
		"L_BRACE 123",
		"BAR 124",
		"R_BRACE 125",
		"TILDE 126",
		"DEL 127",
		" "
	};

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : INIT_SEM;");

	lib_stub = tup_new(0);

	seq_node = tup_new(400);
	seq_node_n = 0;

	seq_symbol = tup_new(300);
	seq_symbol_n = 0;

#ifdef TBSL
	unit_nodes = tup_new(30);
	unit_nodes_n = 0;
#endif

	stub_info = tup_new(0);
	unit_number_now = 0;

    NOT_CHOSEN = tup_new(0);

	init_nodes = tup_new(30);
	init_symbols = tup_new(0);
	/* op_designators no longer needed, just use op_desig_array */

#ifdef COMMENT
	/* retained for documentation purposes (DS 26 jun 84) */
	op
	    misc_attributes = {
		'ADDRESS', 'IMAGE'},
		    u_integer_attributes = {
			'AFT',		 'COUNT',	 'DIGITS',	 'EMAX',
			    'FIRST_BIT',	 'FORE',	 'LAST_BIT',	 'LENGTH',
			    'MACHINE_EMAX',	 'MACHINE_EMIN', 'MACHINE_MANTISSA',
			'MACHINE_RADIX', 'MANTISSA',	 'POS',		 'POSITION',
			    'SAFE_EMAX',	 'SIZE',	 'STORAGE_SIZE', 'WIDTH'
			    },
			??attributes := misc_attributes + u_integer_attributes +

			    overloaded_attributes = {
				'BASE',		 'FIRST',	 'LAST',	  'PRED',
				    'RANGE',	 'SUCC',	 'VAL',		  'VALUE'
				    },
				    float_attributes = {
					'DELTA',	 'EPSILON',   'LARGE',	 'SMALL', 'SAFE_LARGE',
					    'SAFE_SMALL'
					    },

					    boolean_attributes = {
						'CONSTRAINED', 'MACHINE_OVERFLOWS', 'MACHINE_ROUNDS',
						    'CALLABLE',    'TERMINATED'
						    },

#endif

	/* Initialize global mappings for abstract syntax tree and symbol table.*/
	/*
	 * N_KIND    := {[OPT_NODE, as_opt]};
	 * N_AST     := {[OPT_NODE, []]};
	 * N_VAL     := {};
	 * N_LIST    := {[OPT_NODE, []]};
	 */

	/* Initialize OPT_NODE - will get unit 0, seq 1, which is used in places */
	/*  to identify it; then remove from seq_node so it isn't modified		 */
	OPT_NODE = node_new(as_opt);
	N_LIST(OPT_NODE) = tup_new(0);

	scope_st = tup_new(0);
	newtypes = tup_new(0);
	has_return_stk = tup_new(0);
	current_instances = tup_new(0);
	lab_seen = tup_new(0);
	/* current_node = tup_new(0); need not initialize for C */
	/* need to decide representation for unit_name*/
	unit_name = "";
#ifdef IBM_PC
	/* copy literals */
	unit_name = strjoin("","");
#endif

	/* need to use setname to enter identifier names for initial symbols
	 * need to see if handle C semantics w.r.t. string constants properly
	 * here also
	 */
	/* need to copy literals on PC since code overlaid */
#ifdef IBM_PC
#define setname(sym, str) ORIG_NAME(sym) = strjoin(str, "");
#else
#define setname(sym, str) ORIG_NAME(sym) = str
#endif

	OPT_NAME = sym_new(na_obj);
	setname(OPT_NAME, "opt_name");

#define syminit1(sym, na, typ) sym = sym_new(na); TYPE_OF(sym) = typ
	syminit1(symbol_integer, na_type, symbol_integer);
	setname(symbol_integer, "INTEGER");
	syminit1(symbol_short_integer_base, na_type, symbol_integer);
	setname(symbol_short_integer_base, "SHORT_INTEGER\'base");
	syminit1(symbol_short_integer, na_type, symbol_short_integer_base);
	setname(symbol_short_integer, "SHORT_INTEGER");
	syminit1(symbol_universal_integer, na_type, symbol_integer);
	setname(symbol_universal_integer, "universal_integer");
	syminit1(symbol_float, na_type, symbol_float);
	setname(symbol_float, "FLOAT");
	syminit1(symbol_universal_real, na_type, symbol_float);
	setname(symbol_universal_real, "universal_real");
	syminit1(symbol_dfixed, na_type, symbol_dfixed);
	setname(symbol_dfixed, "$FIXED");
	syminit1(symbol_natural, na_subtype, symbol_integer);
	setname(symbol_natural, "NATURAL");
	syminit1(symbol_positive, na_subtype, symbol_integer);
	setname(symbol_positive, "POSITIVE");
	syminit1(symbol_duration, na_type, symbol_duration);
	setname(symbol_duration, "DURATION");
	syminit1(symbol_character, na_enum, symbol_character);
	setname(symbol_character, "CHARACTER");
	syminit1(symbol_boolean, na_enum, symbol_boolean);
	setname(symbol_boolean, "BOOLEAN");
	syminit1(symbol_string, na_array, symbol_string);
	setname(symbol_string, "STRING"); /* ?? */
	tup = tup_new(2);
	tup[1] =(char *) tup_new1((char *) symbol_positive);
	tup[2] =(char *) symbol_character;
	SIGNATURE(symbol_string) = tup;
	symbol_character_type = sym_new(na_enum);
	setname(symbol_character_type, "char_type");
	root_type(symbol_character_type) = symbol_character_type;
	syminit1(symbol_string_type, na_array, symbol_string_type);
	setname(symbol_string_type, "string_type");
	tup = tup_new(2);
	tup[1] = (char *) tup_new1((char *) symbol_positive);
	tup[2] = (char *) symbol_character_type;
	SIGNATURE(symbol_string_type) = tup;
	syminit1(symbol_daccess, na_access, symbol_daccess);
	setname(symbol_daccess, "$ACCESS");
	syminit1(symbol_null, na_null, symbol_any);
	setname(symbol_null, "null");
	syminit1(symbol_main_task_type, na_task_type, symbol_main_task_type);
	setname(symbol_main_task_type, "main_task_type");
	syminit1(symbol_constrained, na_discriminant, symbol_boolean);
	setname(symbol_constrained, "constrained");
	syminit1(symbol_none, na_type, symbol_none);
	setname(symbol_none, "none");
	symbol_standard0 = sym_new(na_package);
	setname(symbol_standard0, "STANDARD#0");

	/* new symbol definitions that are common with the code generator should */
	/* be placed before this comment.					     */

	symbol_undef = sym_new(na_obj); /* for '?' case */
	setname(symbol_undef, "?-undef");

	/*  In SETL, have
	 *    scope_info = init_scope_info;
	 * scope_info is macro: translates into
	 *    scope_name = 'STANDARD#0';
	 *    prefix := suffix := '';
	 *    open_scopes := ['STANDARD#0', 'UNMENTIONABLE#0']
	 *    used_mods := [];
	 *    vis_mods := ['ASCII'];
	 *
	 * TBSL - where to put string for standard0 etc 
	 */
	symbol_standard = sym_new(na_package);
	setname(symbol_standard, "standard");
	symbol_unmentionable = sym_new(na_package);
	setname(symbol_unmentionable, "unmentionable");
	symbol_ascii = sym_new(na_package);
	setname(symbol_ascii, "ASCII");
	symbol_system = (Symbol) 0; /* until defined */
	scope_name = symbol_standard0;
	open_scopes = tup_new(2);
	open_scopes[1] =(char *) symbol_standard0;
	open_scopes[2] =(char *) symbol_unmentionable;
	vis_mods = tup_new1((char *) symbol_ascii);
	used_mods = tup_new(0);

	noop_error = FALSE;
	out_context = FALSE;

	full_others = FALSE;	/*common case for assignment.*/
	fold_context = TRUE; /* Everywhere but for conformance*/

	base_declared_symbols[0] = symbol_standard0;
	base_declared_symbols[1] = symbol_unmentionable;
	base_declared_symbols[2] = symbol_standard;
	base_declared_symbols[3] = symbol_ascii;

	syminit1(symbol_long_integer, na_type, symbol_integer);
	setname(symbol_long_integer, "LONG_INTEGER");
	syminit1(symbol_long_float, na_type, symbol_float);
	setname(symbol_long_float, "LONG_FLOAT");
	syminit1(symbol_universal_fixed, na_type, symbol_universal_fixed);
	setname(symbol_universal_fixed, "universal_fixed");
	syminit1(symbol_array_type, na_array, symbol_any);
	setname(symbol_array_type, "array_type");
	tup = tup_new(2);
	tup[1] =(char *) tup_new1((char *) symbol_any);
	tup[2] =(char *) symbol_character;
	SIGNATURE(symbol_array_type) = tup;
	syminit1(symbol_discrete_type, na_type, symbol_discrete_type);
	setname(symbol_discrete_type, "discrete_type");
	/* 'I:1' is symbol_universal_integer_1' */
	syminit1(symbol_universal_integer_1, na_constant, symbol_universal_integer);
	setname(symbol_universal_integer_1, "I:1");
	/* initialize signature at end for compatibility with gen */

	/* ['I:1',  [na_constant, 'universal_integer', val_node(1) ]], */
	/* Definitions of symbol_unmentionable, symbol_standard and symbol_ascii
	 * done at this point in SETL version are done at start of this procedure
	 * in C version
	 */

	syminit1(symbol_any, na_type, symbol_any);
	setname(symbol_any, "any");

	syminit1(symbol_any_id, na_obj, symbol_any);
	SCOPE_OF(symbol_any_id) = symbol_unmentionable;
	root_type(symbol_any_id) = symbol_any;
	setname(symbol_any_id, "any_id");
	syminit1(symbol_left, na_in, symbol_any);
	setname(symbol_left, "LEFT");
	SIGNATURE(symbol_left) = (Tuple) OPT_NODE;
	syminit1(symbol_right, na_in, symbol_any);
	setname(symbol_right, "RIGHT");
	SIGNATURE(symbol_right) = (Tuple) OPT_NODE;

	/* Initialize bounds of predefined types. */
	/* Note that val_node is only called from this procedure, so that
	 * calling sequence can be changed if necessary; moreover the code
	 * should be put in this module, not in utilities
	 */

	constr_new = constraint_new(CONSTRAINT_RANGE);
	numeric_constraint_low(constr_new) = (char *) val_node1(ADA_MIN_INTEGER);
	numeric_constraint_high(constr_new) = (char *)val_node1(ADA_MAX_INTEGER);
	SIGNATURE(symbol_integer) =(Tuple) constr_new;

	SIGNATURE(symbol_long_integer) = SIGNATURE(symbol_integer);

	constr_new = constraint_new(CONSTRAINT_RANGE);
	/* avoid use of -32768 as this causes problems on pc */
	i = -32767;
	numeric_constraint_low(constr_new) = (char *) val_node1(i-1);
	numeric_constraint_high(constr_new) = (char *) val_node1(32767);
	SIGNATURE(symbol_short_integer) = constr_new;
	SIGNATURE(symbol_short_integer_base) = constr_new;

	constr_new = constraint_new(CONSTRAINT_DIGITS);
	numeric_constraint_low(constr_new) = (char *) val_node2(ADA_MIN_REAL);
	numeric_constraint_high(constr_new) = (char *) val_node2(ADA_MAX_REAL);
	numeric_constraint_digits(constr_new) =
	    (char *) val_node1(ADA_REAL_DIGITS);
	SIGNATURE(symbol_float) = constr_new;

	SIGNATURE(symbol_long_float) = SIGNATURE(symbol_float);

	constr_new = constraint_new(CONSTRAINT_DELTA);
	numeric_constraint_low(constr_new) = (char *) val_node3(rat_fri(int_fri(-1),
	  int_fri(0)));
	numeric_constraint_high(constr_new) = (char *) val_node3(rat_fri(int_fri(1),
	  int_fri(0)));
	numeric_constraint_delta(constr_new) =
	    (char *) val_node3(rat_fri(int_fri(0), int_fri(1)));
	numeric_constraint_small(constr_new) = (char *) OPT_NODE;
	SIGNATURE(symbol_dfixed) =(Tuple) constr_new;

	constr_new = constraint_new(CONSTRAINT_RANGE);
	numeric_constraint_low(constr_new) = (char *) val_node1(0);
	numeric_constraint_high(constr_new) = (char *) val_node1(ADA_MAX_INTEGER);
	SIGNATURE(symbol_natural) =(Tuple) constr_new;

	constr_new = constraint_new(CONSTRAINT_RANGE);
	numeric_constraint_low(constr_new) = (char *) val_node1(1);
	numeric_constraint_high(constr_new) = (char *) val_node1(ADA_MAX_INTEGER);
	SIGNATURE(symbol_positive) =(Tuple) constr_new;

	constr_new = constraint_new(CONSTRAINT_DELTA);
	numeric_constraint_low(constr_new) = (char *)
	  val_node3(rat_fri(int_frs("-86400000"), int_fri(1000)));
	numeric_constraint_high(constr_new) =  (char *)
	  val_node3(rat_fri(int_frs("86400000"), int_fri(1000)));
	numeric_constraint_delta(constr_new) = 
	  (char *) val_node3(rat_fri(int_fri(1), int_fri(1000)));
	numeric_constraint_small(constr_new) =
	  (char *)val_node3(rat_fri(int_fri(1), int_fri(1000)));
	SIGNATURE(symbol_duration) =(Tuple) constr_new;

	constr_new = constraint_new(CONSTRAINT_RANGE);
	numeric_constraint_low(constr_new) = (char *) val_node1(0);
	numeric_constraint_high(constr_new) = (char *) val_node1(127);
	SIGNATURE(symbol_character) =(Tuple) constr_new;

	constr_new = constraint_new(CONSTRAINT_RANGE);
	numeric_constraint_low(constr_new) = (char *)val_node1(0);
	numeric_constraint_high(constr_new) = (char *) val_node1(1);
	SIGNATURE(symbol_boolean) =(Tuple) constr_new;

	/* set size of init_nodes.
	 * NOTE, must NOT make any new entries to init_nodes after
	 * doing assignment of tup_size below	ds 24 sep 84
	 */
	init_nodes[0] = (char *)init_node_count;

	SIGNATURE(symbol_universal_integer) = SIGNATURE(symbol_integer);
	SIGNATURE(symbol_universal_real) = SIGNATURE(symbol_float);
	SIGNATURE(symbol_universal_fixed) = SIGNATURE(symbol_dfixed);
	/* So that the usual naming conventions can be followed for the package */
	/* STANDARD, STANDARD is declared within yet another scope, UNMENTIONABLE.*/
	/* DECLARED := {[standard, {}], ['ASCII', {}],
	 *   ['UNMENTIONABLE#0', {['STANDARD', standard]}] };
	*/
	declared_standard0 = dcl_new(190);
	declared_ascii = dcl_new(80);
	declared_unmentionable = dcl_new(1);
	declared_standard = dcl_new(4);

	declared_all[0] = declared_standard0;
	declared_all[1] = declared_unmentionable;
	declared_all[2] = declared_standard;
	declared_all[3] = declared_ascii;

	for (i = 0; i <= 3; i++) {
		Symbol s;
		s = base_declared_symbols[i];
		DECLARED(s) = declared_all[i];
	}

	dcl_put(declared_unmentionable, "STANDARD", symbol_standard0);

	/* Operators(most) entered into SYMBTAB and DECLARED.*/

	/* concat_ops	   = {'&'}, */
	/*NOTE:: 'boolean_type', etc used only here and in chapter 4 */

	/* boolean_ops	  = {'not', 'and', 'or', 'xor'}, */
	symbol_boolean_type = sym_new(na_type);
	TYPE_OF(symbol_boolean_type) = symbol_boolean_type;
	setname(symbol_boolean_type, "boolean_type");

	symbol_not = symbtab_enter("not", symbol_boolean_type);
	symbol_and = symbtab_enter("and", symbol_boolean_type);
	symbol_or = symbtab_enter("or", symbol_boolean_type);
	symbol_xor = symbtab_enter("xor", symbol_boolean_type);

	/* short_circ_ops = { 'andthen', 'orelse'}, */
	symbol_andthen = symbtab_enter("andthen", symbol_boolean_type);
	symbol_orelse = symbtab_enter("orelse", symbol_boolean_type);

	/*    equal_ops	     = {':=', '=', '/=', 'in', 'notin'}, */
	symbol_assign = symbtab_enter(":=", symbol_boolean);
	symbol_eq = symbtab_enter("=", symbol_boolean);
	symbol_ne = symbtab_enter("/=", symbol_boolean);
	symbol_in = symbtab_enter("IN", symbol_boolean);
	symbol_notin = symbtab_enter("NOTIN", symbol_boolean);

	symbol_order_type = sym_new(na_type);
	TYPE_OF(symbol_order_type) = symbol_order_type;
	setname(symbol_order_type, "order_type");
	symbol_lt = symbtab_enter("<", symbol_order_type);
	symbol_le = symbtab_enter("<=", symbol_order_type);
	symbol_ge = symbtab_enter(">=", symbol_order_type);
	symbol_gt = symbtab_enter(">", symbol_order_type);

	/*    arith_ops	     = {'+u', '-u', 'abs', '+', '-', '*', '/'}, */
	/* symbol_numeric denote type of numeric operators, make void for now */
	/* symbol_numeric is not explicitly created as such in setl version,
	 * rather this is tag used only in chapter 4 
	 */
	symbol_numeric = sym_new(na_void);
	setname(symbol_numeric, "numeric");
	symbol_addu = symbtab_enter("+u", symbol_numeric);
	symbol_subu = symbtab_enter("-u", symbol_numeric);
	symbol_abs = symbtab_enter("abs", symbol_numeric);
	symbol_add = symbtab_enter("+", symbol_numeric);
	symbol_sub = symbtab_enter("-", symbol_numeric);
	symbol_mul = symbtab_enter("*", symbol_numeric);
	symbol_div = symbtab_enter("/", symbol_numeric);

	symbol_mod = symbtab_enter("mod", symbol_numeric);
	symbol_rem = symbtab_enter("rem", symbol_numeric);

	symbol_exp = symbtab_enter("**", symbol_numeric);

	symbol_cat = symbtab_enter("&", symbol_array_type);

	/* We have introduced some new symbols in order to deal array catenations 
	 * &cc : catenation of one component and one component
	 * &ac : catenation of an array and a component
	 * &ca : catenation of a component and an array
	 */

	symbol_cat_cc = symbtab_enter ("&cc", symbol_array_type);
	symbol_cat_ac = symbtab_enter ("&ac", symbol_array_type);
	symbol_cat_ca = symbtab_enter ("&ca", symbol_array_type);

	symbtab_enter("any_op", symbol_any);

	/* The ABS operator is not a reserved word, and the interpreter
	 *  nevertheless expects its name in lower case. Thus :
	 */

	/*declared(standard)('ABS') := declared(standard)('abs');*/
	dcl_put(declared_standard0, "ABS", dcl_get(declared_standard0, "abs"));

	symbol_modi = new_arith_op("modi", symbol_universal_integer);
	symbol_remi = new_arith_op("remi", symbol_universal_integer);
	symbol_addui = new_arith_op("+ui", symbol_universal_integer);
	symbol_subui = new_arith_op("-ui", symbol_universal_integer);
	symbol_absi = new_arith_op("absi", symbol_universal_integer);
	symbol_addi = new_arith_op("+i", symbol_universal_integer);
	symbol_subi = new_arith_op("-i", symbol_universal_integer);
	symbol_muli = new_arith_op("*i", symbol_universal_integer);
	symbol_divi = new_arith_op("/i", symbol_universal_integer);

	/*    arith_ops	     = {'+u', '-u', 'abs', '+', '-', '*', '/'}, */
	symbol_addufl = new_arith_op("+ufl", symbol_universal_real);
	symbol_subufl = new_arith_op("-ufl", symbol_universal_real);
	symbol_absfl = new_arith_op("absfl", symbol_universal_real);
	symbol_addfl = new_arith_op("+fl", symbol_universal_real);
	symbol_subfl = new_arith_op("-fl", symbol_universal_real);
	symbol_mulfl = new_arith_op("*fl", symbol_universal_real);
	symbol_divfl = new_arith_op("/fl", symbol_universal_real);

	symbol_addufx = new_arith_op("+ufx", symbol_universal_dfixed);
	symbol_subufx = new_arith_op("-ufx", symbol_universal_dfixed);
	symbol_absfx = new_arith_op("absfx", symbol_universal_dfixed);
	symbol_addfx = new_arith_op("+fx", symbol_universal_dfixed);
	symbol_subfx = new_arith_op("-fx", symbol_universal_dfixed);
	symbol_mulfx = new_arith_op("*fx", symbol_universal_dfixed);
	symbol_divfx = new_arith_op("/fx", symbol_universal_dfixed);
	/* The fixed multiplication and division operators return the
	 * singular type universal_fixed, which must be explicitly con-
	 * verted before use.
	 */

	TYPE_OF(symbol_mulfx) = symbol_universal_fixed;
	TYPE_OF(symbol_divfx) = symbol_universal_fixed;

	/* There are two types of mixed mode arithmetic operators: the ones
	 * for fixed-integer operations, used at run-time, and the ones for
	 * universal_real - universal_integer operations, used only in literal
	 * espressions.
	 */
	/* new_arith_ops({'*fxi', '*ifx', '/fxi'}, '$FIXED'); */
	symbol_mulfxi = new_arith_op("*fxi", symbol_dfixed);
	symbol_mulifx = new_arith_op("*ifx", symbol_dfixed);
	symbol_divfxi = new_arith_op("/fxi", symbol_dfixed);

	/* new_arith_ops({'*fli', '*ifl', '/fli'}, 'universal_real'); */
	symbol_mulfli = new_arith_op("*fli", symbol_universal_real);
	symbol_mulifl = new_arith_op("*ifl", symbol_universal_real);
	symbol_divfli = new_arith_op("/fli", symbol_universal_real);

	symbol_expi = new_arith_op("**i", symbol_universal_integer);
	symbol_expfl = new_arith_op("**fl", symbol_universal_real);

	/* Exceptions entered into SYMBTAB.*/
#undef symint2
#define symint2(name) name = sym_new(na_exception); \
	TYPE_OF(name) = symbol_exception; SIGNATURE(name) = tup_new(0);
	symbol_exception = sym_new(na_exception);/* ?? check this */
	setname(symbol_exception, "EXCEPTION");

	symint2(symbol_constraint_error)
	    setname(symbol_constraint_error, "CONSTRAINT_ERROR");
	symint2(symbol_numeric_error)
	    setname(symbol_numeric_error, "NUMERIC_ERROR");
	symint2(symbol_program_error)
	    setname(symbol_program_error, "PROGRAM_ERROR");
	symint2(symbol_storage_error)
	    setname(symbol_storage_error, "STORAGE_ERROR");
	symint2(symbol_tasking_error)
	    setname(symbol_tasking_error, "TASKING_ERROR");
	symint2(symbol_system_error)
	    setname(symbol_storage_error, "SYSTEM_ERROR");
	/* Types and exceptions entered into DECLARED.  */
	/* NOTE: 'NULL' obsolete and hence not entered here(DS 24 Feb 84) */
#define DCLENT(c, s) dcl_put(declared_standard0, c, s)
	DCLENT("ASCII", symbol_ascii);
	DCLENT("BOOLEAN", symbol_boolean);
	DCLENT("CHARACTER", symbol_character);
	DCLENT("DURATION", symbol_duration);
	DCLENT("FLOAT", symbol_float);
	DCLENT("INTEGER", symbol_integer);
	DCLENT("$FIXED", symbol_dfixed);
	DCLENT("NATURAL", symbol_natural);
	DCLENT("POSITIVE", symbol_positive);
	DCLENT("STRING", symbol_string);
	DCLENT("universal_integer", symbol_universal_integer);
	DCLENT("universal_real", symbol_universal_real);
	DCLENT("discrete_type", symbol_discrete_type);
	DCLENT("universal_fixed", symbol_universal_fixed);
	DCLENT("string_type", symbol_string_type);
	DCLENT("array_type", symbol_array_type);
	DCLENT("any", symbol_any);
	DCLENT("none", symbol_none);
	DCLENT("CONSTRAINT_ERROR", symbol_constraint_error);
	DCLENT("NUMERIC_ERROR", symbol_numeric_error);
	DCLENT("PROGRAM_ERROR", symbol_program_error);
	DCLENT("STORAGE_ERROR", symbol_storage_error);
	DCLENT("TASKING_ERROR", symbol_tasking_error);
	DCLENT("SYSTEM_ERROR", symbol_system_error);
#undef DCLENT

	/* Printable characters are entered into SYMBTAB, as overloaded
	 * literals whose source name is the character between single quotes.
	 */
	{
		Tuple lmap;
		int	i;
		char   *s;

		lmap = tup_new(2 * 128);
		for (i = 0; i <= 127; i++ ) {
			s = smalloc(4);
			s[3] = '\0';
			s[0] = '\'';
			s[1] = (char) i;
			s[2] = '\'';
			lmap[2 * i + 1] = s;
			lmap[2 * i + 2] =(char *) i;
			/* if (i >= 32 && i <= 126 )  -- enter all ascii chars in SYMBTAB */
			ini_chain(s, na_literal, symbol_character);
		}
		literal_map(symbol_character) =(Set) lmap;
	}
	/* characters.  */
	/* scope_info is macro [scope_name, prefix, open_scopes, used_mods,
	 * vis_mods, suffix] in SETL. In C prefix and suffix do not apply,
	 * and we represent as tuple
	 * [scope_name, open_scopes, used_mods, vis_mods]
	 */
	{
		Tuple t;
		t = tup_new(4);
		t[1] =(char *) scope_name;
		t[2] =(char *) tup_copy(open_scopes);
		t[3] =(char *) tup_copy(used_mods);
		t[4] =(char *) tup_copy(vis_mods);
		scope_st = tup_with(scope_st, (char *) t);
	}
	/* scope_info =
	 * ['ASCII', '', ['ASCII', 'STANDARD#0', 'UNMENTIONABLE#0'], [], [], '']; ];
	 */

	scope_name = symbol_ascii;
	open_scopes = tup_new(3);
	open_scopes[1] =(char *) symbol_ascii;
	open_scopes[2] =(char *) symbol_standard0;
	open_scopes[3] =(char *) symbol_unmentionable;
	vis_mods = tup_new(0);
	used_mods = tup_new(0);
	{
		int	i;
		char   *p, *p1;
		Symbol sym;
		char	name[20];

		for (i = 0; p = char_names[i]; i++) {
			if (p[0] == ' ')
				/* code folded from here */
				break;
			/* unfolding */
			p1 = strchr(p, ' ');
			if (p1 == p)
				/* code folded from here */
					break;
			/* unfolding */
			sym = sym_new(na_constant);
			TYPE_OF(sym) = symbol_character;
			SIGNATURE(sym) =(Tuple) val_nodea1(atoi(p1));
			name[0] = '\0';
			strncat(name, p, p1 - p);/* extract string with name */
			setname(sym, strjoin(name, "")); /* p1 points to original name */
			dcl_put(declared_ascii, name, sym);
		}
	}

	/* In the SETL version, we call popscope();
	 * to restore scope environment. For initialization purposes we need only
	 * restore scope info from that saved on scope stack, as follows:
	 */
	tup = (Tuple) tup_frome(scope_st);
	scope_name = (Symbol) tup[1];
	open_scopes = (Tuple) tup[2];
	used_mods = (Tuple) tup[3];
	vis_mods = (Tuple) tup[4];

	/* For the enumeration type BOOLEAN*/

#ifndef IBM_PC
	ini_chain("FALSE", na_literal, symbol_boolean);
	ini_chain("TRUE", na_literal, symbol_boolean);
#else
	ini_chain(strjoin("FALSE", ""), na_literal, symbol_boolean);
	ini_chain(strjoin("TRUE", ""), na_literal, symbol_boolean);
#endif
	{
		Tuple lmap;
		char   *s;
		lmap = tup_new(4);
		s = smalloc(6);
		lmap[1] = strcpy(s, "FALSE");
		lmap[2] = 0;
		s = smalloc(5);
		lmap[3] = strcpy(s, "TRUE");
		lmap[4] =(char *) 1;
		literal_map(symbol_boolean) =(Set) lmap;
	}

	/*   The only predefined aggregate is the one for string literals.*/
	ini_new_agg(symbol_string);

	/* Initialize the scope map for all identifiers in standard packages.
	 *  (forall [scop, decl] in declared)
	 *   (forall [-, id] in decl) SCOPE_OF(id) := scop; end;
	 *  end forall;
	 */
	{
		int	i;
		Fordeclared dmapiv;
		Declaredmap dmap;
		char   *p;
		Symbol sym, scop;

		for (i = 0; i <= 3; i++) {
			scop = base_declared_symbols[i];
			dmap = DECLARED(scop);
			FORDECLARED(p, sym, dmap, dmapiv)
			    SCOPE_OF(sym) = scop;
			ENDFORDECLARED(dmapiv)
		}
	}

#define RSET(sym) root_type(sym) = sym
	RSET(symbol_boolean);
	RSET(symbol_character);
	RSET(symbol_duration);
	RSET(symbol_float);
	RSET(symbol_integer);
	RSET(symbol_dfixed);
	RSET(symbol_natural);
	RSET(symbol_positive);
	RSET(symbol_string);
	RSET(symbol_universal_integer);
	RSET(symbol_universal_real);
	RSET(symbol_discrete_type);
	RSET(symbol_universal_fixed);
	RSET(symbol_string_type);
	RSET(symbol_array_type);
	RSET(symbol_any);
	RSET(symbol_none);
#undef RSET
	/* except for...*/

	root_type(symbol_natural) = symbol_integer;
	root_type(symbol_positive) = symbol_integer;
	root_type(symbol_duration) = root_type(symbol_dfixed);
	/*$ root_type('array_type') := 'any';*/
	root_type(symbol_short_integer) = symbol_integer;
	root_type(symbol_short_integer_base) = symbol_integer;

    initialize_representation_info(symbol_boolean,TAG_ENUM);
    initialize_representation_info(symbol_character,TAG_ENUM);
    initialize_representation_info(symbol_duration,TAG_FIXED);
    initialize_representation_info(symbol_integer,TAG_INT);
    initialize_representation_info(symbol_float,TAG_FLOAT);
    initialize_representation_info(symbol_dfixed,TAG_FIXED);

    force_representation(symbol_boolean);
    force_representation(symbol_character);
    force_representation(symbol_duration);
    force_representation(symbol_float);
    force_representation(symbol_integer);
    force_representation(symbol_dfixed);

    choose_representation(symbol_positive);
    choose_representation(symbol_natural);


	/* base_declared is used to save declared maps as currently defined*/
	base_declared[0] = dcl_copy(declared_standard0);
	base_declared[1] = dcl_copy(declared_unmentionable);
	base_declared[2] = dcl_copy(declared_standard);
	base_declared[3] = dcl_copy(declared_ascii);
	/* VISIBLE('ASCII') := DECLARED('ASCII'); entries visible by default */
	FORDECLARED(id, sym, DECLARED(symbol_ascii), fd);
		IS_VISIBLE(fd) = TRUE;
	ENDFORDECLARED(fd);
	newtypes = tup_with(newtypes, (char *) tup_new(0));

	/* initialize sets of types(constants in setl version) */

	/* Next four symbols introduced for maps incp_types, priv_types */
	symbol_private = sym_new(na_type);
	setname(symbol_private, "private");
	symbol_limited_private = sym_new(na_type);
	setname(symbol_limited_private, "limited_private");
	symbol_limited = sym_new(na_type);
	setname(symbol_limited, "limited");
	symbol_incomplete = sym_new(na_type);
	setname(symbol_incomplete, "incomplete");

	/* the following symbols are used as markers by check_type in chapter 4 */
	symbol_universal_type = sym_new(na_void);
	setname(symbol_universal_type, "universal_type");
	symbol_integer_type = sym_new(na_void);
	setname(symbol_integer_type, "integer_type");
	symbol_real_type = sym_new(na_void);
	setname(symbol_real_type, "real_type");
	symbol_composite_type = sym_new(na_void);
	setname(symbol_composite_type, "composite_type");
	symbol_equal_type = sym_new(na_void);
	setname(symbol_equal_type, "equal_type");

	SIGNATURE(symbol_universal_integer_1) = (Tuple)  val_node1(1);

	/* TBSN: base_attributes
	 * ??const base_attributes = {'BASE','POS','PRED','SUCC','VAL','VALUE'};
	 */
	/* define binary_sig and unary_sig used by valid_op_types et. al. 
	 * in chapter 4
	 */
	unary_sig = tup_new1((char *) symbol_right);
	binary_sig = tup_new(2);
	binary_sig[1] = (char *) symbol_left;
	binary_sig[2] = (char *) symbol_right;
	return;
}

/* In C, need several versions of val_node, since we cannot test argument */
/* type as we can in SETL */

static Node val_node1(int init_val)								/*;val_node1*/
{
	/* Called from init_sem to initialize the bounds of predefined types.*/

	Node node;

	node = node_new(as_ivalue);
	init_node_save(node);
	/* INTEGER case */
	N_TYPE(node) = symbol_integer;

	N_VAL(node) =(char *) int_const(init_val);
	return node;
}

static Node val_nodea1(int init_val)					/*;val_nodea1*/
{
	/* Called from init_sem to initialize the bounds of predefined types.*/
	/* like val_node1, but does not save generated node */

	Node node;

	node = node_new(as_ivalue);
	/* INTEGER case */
	N_TYPE(node) = symbol_integer;

	N_VAL(node) =(char *) int_const(init_val);
	return node;
}

static Node val_node2(double init_val)	/*;val_node2*/
{
	/* Called from init_sem to initialize the bounds of predefined types.*/

	Node node;
	/* 'REAL' case */
	node = node_new(as_ivalue);
	init_node_save(node);

	N_TYPE(node) = symbol_float;

	N_VAL(node) = (char *)real_const(init_val);
	return node;
}

static Node val_node3(Rational init_val)					/*;val_node3*/
{
	/* Called from init_sem to initialize the bounds of predefined types.*/

	Node node;

	node = node_new(as_ivalue);
	init_node_save(node);
	/* INTEGER TUPLE case */
	N_TYPE(node) = symbol_universal_real;

	N_VAL(node) =(char *) rat_const(init_val);
	return node;
}

static void init_node_save(Node node)		/*;init_node_save*/
{
	init_node_count += 1;
	init_nodes[init_node_count] = (char *)node;
}

static Symbol ini_chain(char *name, int nat, Symbol typ)	/*;ini_chain*/
{
	/* variant of chain_overloads for use by sem_init */

	Symbol ent;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  chain_overloads");
	/* Insert enumeration literal into the current
	 * symbol table.
	 *    declared(scope)(id) = name;
	 */
	ent = sym_new(nat);
	dcl_put(declared_standard0, name, ent);
	/* Place in symbol table maps the specification of a new overloadable
	 * object .
	 */
	TYPE_OF(ent) = typ;
	SIGNATURE(ent) = tup_new(0);
	SCOPE_OF(ent) = symbol_standard0;
	/* TO_XREF(ent);*/

	OVERLOADS(ent) = set_new1((char *) ent);
	ORIG_NAME(ent) = name;

	return ent;
}

static Symbol symbtab_enter(char *opr, Symbol result)		/*;symbtab_enter*/
{
	/* Enter into symbol table the names of all predefined operators.
	 * They have generic types which cover all types derived from the pre-
	 * defined ones, and overload themselves.
	 */

	Symbol s;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : symbtab_enter(oprs, result) ");

	s = sym_new(na_op);
#ifdef IBM_PC
	ORIG_NAME(s) = strjoin(opr, ""); /* added by ds 17 jul 84 */
#else
	ORIG_NAME(s) = opr; /* added by ds 17 jul 84 */
#endif
	dcl_put(declared_standard0, opr, s);
	/*	declared(standard)(op_name) := op_name;*/
	/* Each of the predefined operators overloads itself. */
	TYPE_OF(s) = result;
	SIGNATURE(s) = tup_new(0);
	OVERLOADS(s) = set_new1((char *) s);
	SCOPE_OF(s) = symbol_standard0;
	return s;
}

static Symbol new_arith_op(char *opr, Symbol result)		/*;new_arith_op*/
{
	Symbol s;

	if (cdebug2 > 3) {
#ifdef ERRMSG
		TO_ERRFILE('AT PROC : new_arith_ops(opr, result) ');
#endif
		TO_ERRFILE("AT PROC : new_arith_ops(opr, result) ");
	}
	/* Arithmetic operators are introduced for integer, floating point and
	 * fixed point results. These operators are never accessed directly by
	 * name resolution routines, but rather by the type resolution routine
	 * valid_arith_args. As a result, they need not appear in declared(St.)
	 * and need not have nay overloading specified.
	 */
	s = sym_new(na_op);
#ifdef IBM_PC
	/* must use strjoin since overlaying 0a.c */
	ORIG_NAME(s) = strjoin(opr, "");
#else
	ORIG_NAME(s) = opr;
#endif
	TYPE_OF(s) = result;
	SIGNATURE(s) = tup_new(0);
	return s;
}

static void ini_new_agg(Symbol type_mark)		 			/*;ini_new_agg*/
{
	/* variant of new_agg_or_access for use by semini */
	/*
	 * The possible types of an aggregate are all composite types that are
	 * currently visible. To simplify their use, an entry  with the marker
	 * 'aggregate' is created for each such type definition. Its overloads
	 * set carries all such types  defined in  the current	scope. This is
	 * similar to what is done for other overloadable constructs.
	 * The same is done for access types, using the marker 'access'.
	 */
	Symbol scope, new_def;

	/* make a no-op for now */
	scope = scope_name;

	new_def = sym_new(na_aggregate);
	dcl_put(DECLARED(scope), "aggregate", new_def);
	SCOPE_OF(new_def) = scope;
	NATURE(new_def)	  = na_aggregate;
	TYPE_OF(new_def)  = type_mark;
	OVERLOADS(new_def) = set_new1((char *) type_mark);

#ifdef TBSN
	if (old_def != (Symbol)0) { /* Save its overloads*/
		set_with(OVERLOADS(new_def) +:
		= overloads(old_def);
		    declared(scope)(str newat) :
		= old_def;	$ and keep accessible
	}
#endif
	return;
}

int in_op_designators(char *s)							/*;in_op_designators*/
{
	/* op_designators is a set of strings, so must use strcmp to check
	 * for set membership.
	 */
	int	i;

    for (i = 0; op_desig_array[i]; i++)
		if(streq(op_desig_array[i], s)) return TRUE;
	return FALSE;
}
