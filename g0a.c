/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/* g0a -  initializations (corresponds to needed parts of adasem 0a.c */

#define GEN

#include "hdr.h"
#include "vars.h"
#include "gvars.h"
#include "gutilprots.h"
#include "dbxprots.h"
#include "setprots.h"
#include "arithprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "g0aprots.h"

static Node val_node1(int);
static Node val_nodea1(int);
static Node val_node2(double);
static Node val_node3(Rational);
static void init_node_save(Node);
static void sym_inits(Symbol, Symbol, Tuple, Symbol);
static void sym_initg(Symbol, int, int, int);

static int	init_node_count = 0;
extern int ADA_MIN_INTEGER, ADA_MAX_INTEGER;
extern int list_unit_0; /* set by gmain.c to list unit 0 structure */

void init_sem()											/*; init_sem */
{
	Tuple	constr_new, tup, boolean_constraint, constr_character, lmap;
	Symbol	s;
	int	i;
	char   *p, *p1;
	Symbol sym;
	char	name[20];
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
	current_instances = tup_new(0);
	lib_stub = tup_new(0);

	seq_node = tup_new(400);
	seq_node_n = 0;

	seq_symbol = tup_new(100);
	seq_symbol_n = 0;

	unit_nodes = tup_new(0);
#ifdef TBSL
	unit_nodes_n = 0;
#endif

	stub_info = tup_new(0);
	unit_number_now = 0;

	init_nodes = tup_new(30);
	init_symbols = tup_new(0);

	interfaced_procedures = tup_new(0);

	OPT_NODE = node_new(as_opt);
	N_LIST(OPT_NODE) = tup_new(0);
	init_node_save(OPT_NODE);

#ifdef IBM_PC
	/* avoid copy of literal for PC */
#define setname(sym, str) ORIG_NAME(sym) = strjoin(str, "")
#else
#define setname(sym, str) ORIG_NAME(sym) = str
#endif

	OPT_NAME = sym_new(na_obj);
	setname(OPT_NAME, "opt_name");

#ifdef IBM_PC
#define sym_op_enter(sym, name) sym = sym_new(na_op); \
 ORIG_NAME(sym) = strjoin(name, "");
#else
#define sym_op_enter(sym, name) sym = sym_new(na_op); ORIG_NAME(sym) = name;
#endif

	symbol_integer = sym_new(na_type);
	/* note that val_node1 sets N_TYPE field to symbol_integer, so must
     * define symbol_integer before calling val_node1
     */
	constr_new = constraint_new(CONSTRAINT_RANGE);
	numeric_constraint_low(constr_new) = (char *) val_node1(ADA_MIN_INTEGER);
	numeric_constraint_high(constr_new) = (char *)val_node1(ADA_MAX_INTEGER);
	sym_inits(symbol_integer, symbol_integer, constr_new, symbol_integer);
	sym_initg(symbol_integer, TK_WORD, 1, 3);
	setname(symbol_integer, "INTEGER");

	constr_new = constraint_new(CONSTRAINT_RANGE);
	numeric_constraint_low(constr_new) = (char *) val_node1(-32768);
	numeric_constraint_high(constr_new) = (char *) val_node1(32767);
	symbol_short_integer_base = sym_new(na_type);
	sym_inits(symbol_short_integer_base, symbol_integer,
	  constr_new, symbol_short_integer);
	sym_initg(symbol_short_integer_base, TK_WORD, 1, 77);
	setname(symbol_short_integer_base, "SHORT_INTEGER\'base");

	symbol_short_integer = sym_new(na_type);
	sym_inits(symbol_short_integer, symbol_short_integer_base,
	  SIGNATURE(symbol_short_integer_base), symbol_short_integer);
	sym_initg(symbol_short_integer, TK_WORD, 1, 77);
	setname(symbol_short_integer, "SHORT_INTEGER");
	ALIAS(symbol_short_integer_base) = symbol_short_integer;

	symbol_universal_integer = sym_new(na_type);
	sym_inits(symbol_universal_integer , symbol_integer, 
	  SIGNATURE(symbol_integer), symbol_integer);
	sym_initg(symbol_universal_integer, TK_WORD, 1, 3);
	setname(symbol_universal_integer, "universal_integer");

	constr_new = constraint_new(CONSTRAINT_DIGITS);
	numeric_constraint_low(constr_new) = (char *) val_node2(ADA_MIN_REAL);
	numeric_constraint_high(constr_new) = (char *) val_node2(ADA_MAX_REAL);
	numeric_constraint_digits(constr_new) = (char *) val_node1(ADA_REAL_DIGITS);
	symbol_float = sym_new(na_type);
	sym_inits(symbol_float, symbol_float, constr_new, symbol_float);
	/* TBSL: there should be TK_REAL for floating point */
	sym_initg(symbol_float, TK_LONG, 1, 73);
	setname(symbol_float, "FLOAT");

	symbol_universal_real = sym_new(na_type);
	sym_inits(symbol_universal_real, symbol_float, 
	  SIGNATURE(symbol_float), symbol_universal_real);
	sym_initg(symbol_universal_real, TK_LONG, 1, 73);
	setname(symbol_universal_real, "universal_real");

	constr_new = constraint_new(CONSTRAINT_DELTA);
	numeric_constraint_low(constr_new) = (char *) val_node3(rat_fri(int_fri(-1),
	  int_fri(0)));
	numeric_constraint_high(constr_new) = (char *) val_node3(rat_fri(int_fri(1),
	  int_fri(0)));
	numeric_constraint_delta(constr_new) =
	  (char *) val_node3(rat_fri(int_fri(0), int_fri(1)));
	numeric_constraint_small(constr_new) = (char *) OPT_NODE;
	symbol_dfixed = sym_new(na_type);
	sym_inits(symbol_dfixed , symbol_dfixed, constr_new, symbol_dfixed);
	sym_initg(symbol_dfixed, TK_LONG, 1, 67);
	setname(symbol_dfixed, "$FIXED");

	constr_new = constraint_new(CONSTRAINT_RANGE);
	numeric_constraint_low(constr_new) = (char *) val_node1(0);
	numeric_constraint_high(constr_new) = (char *) val_node1(ADA_MAX_INTEGER);
	symbol_natural = sym_new(na_subtype);
	sym_inits(symbol_natural , symbol_integer, constr_new, symbol_integer);
	sym_initg(symbol_natural, TK_WORD, 1, 57);
	setname(symbol_natural, "NATURAL");

	constr_new = constraint_new(CONSTRAINT_RANGE);
	numeric_constraint_low(constr_new) = (char *) val_node1(1);
	numeric_constraint_high(constr_new) = (char *) val_node1(ADA_MAX_INTEGER);
	symbol_positive = sym_new(na_subtype);
	sym_inits(symbol_positive , symbol_integer,
	  constr_new, symbol_integer);
	sym_initg(symbol_positive, TK_WORD, 1, 22);
	setname(symbol_positive, "POSITIVE");

	constr_new = constraint_new(CONSTRAINT_DELTA);
	numeric_constraint_low(constr_new) = (char *)
	  val_node3(rat_fri(int_frs("-86400000"), int_fri(1000)));
	numeric_constraint_high(constr_new) =  (char *)
	  val_node3(rat_fri(int_frs("86400000"), int_fri(1000)));
	numeric_constraint_delta(constr_new) = 
	  (char *) val_node3(rat_fri(int_fri(1), int_fri(1000)));
	numeric_constraint_small(constr_new) = (char *)val_node3(rat_fri(int_fri(1),
	  int_fri(1000)));
	symbol_duration = sym_new(na_type);
	sym_inits(symbol_duration , symbol_duration, constr_new, symbol_dfixed);
	sym_initg(symbol_duration, TK_LONG, 1, 61);
	setname(symbol_duration, "DURATION");

	constr_character = constraint_new(CONSTRAINT_RANGE);
	numeric_constraint_low(constr_character) = (char *) val_node1(0);
	numeric_constraint_high(constr_character) = (char *) val_node1(127);
	symbol_character = sym_new(na_enum);
	sym_inits(symbol_character , symbol_character, constr_character,
	  symbol_character);
	sym_initg(symbol_character, TK_WORD, 1, 43);
	setname(symbol_character, "CHARACTER");

	constr_new = constraint_new(CONSTRAINT_RANGE);
	numeric_constraint_low(constr_new) = (char *)val_node1(0);
	numeric_constraint_high(constr_new) = (char *) val_node1(1);
	/* save constraint - needed to initialize symbol_constrained below*/
	boolean_constraint = constr_new;
	symbol_boolean = sym_new(na_enum);
	sym_inits(symbol_boolean,  symbol_boolean, constr_new, symbol_boolean);
	sym_initg(symbol_boolean, TK_WORD, 1, 7);
	setname(symbol_boolean, "BOOLEAN");

	tup = tup_new(2);
	tup[1] =(char *) tup_new1((char *) symbol_positive);
	tup[2] = (char *) symbol_character;
	symbol_string = sym_new(na_array);
	sym_inits(symbol_string , symbol_string, tup, symbol_string);
	sym_initg(symbol_string, -1, 1, 26);
	setname(symbol_string, "STRING");

	/* In SETL, symbol_string_type has a different signature from
	 * that defined by adasem. This symbol should never be
	 * used by the generator, so it seems safe to give it the
	 * same signature as is defined by adasem.
	 */
	/* symbol_character_type references should not be produced by adasem.
	 * However, in those cases where they do occur they should be treated
	 * the same as for symbol_character, so we initialize 
	 * symbol_character_type to correspond to symbol_character.
	 *  ds 9-26-85
	 */
	symbol_character_type = sym_new(na_enum);
	sym_inits(symbol_character_type , symbol_character, constr_character,
	  symbol_character);
	sym_initg(symbol_character_type, TK_WORD, 1, 43);
	setname(symbol_character_type, "character_type");

	symbol_string_type = sym_new(na_array);
	tup = tup_new(2);
	tup[1] =(char *) tup_new1((char *) symbol_positive);
	tup[2] = (char *) symbol_character_type;
	sym_inits(symbol_string_type , symbol_string_type, tup, symbol_string_type);
	sym_initg(symbol_string_type, -1, 1, 26);
	setname(symbol_string_type, "string_type");

	symbol_daccess = sym_new(na_access);
	sym_inits(symbol_daccess , symbol_daccess, tup_new(0), symbol_daccess);
	sym_initg(symbol_daccess, TK_ADDR, 1, 1);
	setname(symbol_daccess, "$ACCESS");

	symbol_null = sym_new(na_obj);
	sym_inits(symbol_null , symbol_daccess, tup_new(0), symbol_null);
	sym_initg(symbol_null, TK_ADDR, 255, 32767);
	setname(symbol_null, "null");

	symbol_main_task_type = sym_new(na_task_type);
	sym_inits(symbol_main_task_type , symbol_main_task_type, tup_new(0),
	  symbol_main_task_type);
	sym_initg(symbol_main_task_type, TK_WORD, 1, 47);
	setname(symbol_main_task_type, "main_task_type");

	/* The signature for symbol_constrained is its default_expr,
     * and corresponds to the first value entered for symbol boolean (FALSE)
     */
	symbol_constrained = sym_new(na_discriminant);
	sym_inits(symbol_constrained , symbol_boolean, 
	  (Tuple) numeric_constraint_low(boolean_constraint), symbol_constrained);
	sym_initg(symbol_constrained, 0, 0, 0);
	setname(symbol_constrained, "constrained");

	symbol_none = sym_new(na_type);
	sym_inits(symbol_none , symbol_none, (Tuple)0, symbol_none);
	sym_initg(symbol_none, 0, 0, 0);
	setname(symbol_none, "none");

	symbol_standard0 = sym_new(na_package);
	setname(symbol_standard0, "STANDARD#0");

	symbol_undef = sym_new(na_obj); /* for '?' case */
	setname(symbol_undef, "?-undef");
	symbol_standard = sym_new(na_package);
	setname(symbol_standard, "standard");
	symbol_unmentionable = sym_new(na_package);
	setname(symbol_unmentionable, "unmentionable");
	symbol_ascii = sym_new(na_package);
	setname(symbol_ascii, "ASCII");
	symbol_long_integer = sym_new(na_type);
	setname(symbol_long_integer, "LONG_INTEGER");
	symbol_long_float = sym_new(na_type);
	setname(symbol_long_float, "LONG_FLOAT");
	symbol_universal_fixed = sym_new(na_type);
	setname(symbol_universal_fixed, "universal_fixed");
	symbol_array_type = sym_new(na_array);
	setname(symbol_array_type, "array_type");
	symbol_discrete_type = sym_new(na_type);
	setname(symbol_discrete_type, "discrete_type");
	symbol_universal_integer_1 = sym_new(na_obj);
	setname(symbol_universal_integer_1, "I:1");
	symbol_any = sym_new(na_type);
	setname(symbol_any, "any");
	symbol_any_id = sym_new(na_obj);
	root_type(symbol_any_id) = symbol_any;
	setname(symbol_any_id, "any_id");
	symbol_left = sym_new(na_in);
	setname(symbol_left, "LEFT");
	symbol_right = sym_new(na_in);
	setname(symbol_right, "RIGHT");

	symbol_boolean_type = sym_new(na_type);
	setname(symbol_boolean_type, "boolean_type");

	sym_op_enter(symbol_not, "not");
	sym_op_enter(symbol_and, "and");
	sym_op_enter(symbol_or, "or");
	sym_op_enter(symbol_xor, "xor");
	sym_op_enter(symbol_andthen, "andthen");

	sym_op_enter(symbol_orelse, "orelse");
	sym_op_enter(symbol_assign, ":=");
	sym_op_enter(symbol_eq, "=");
	sym_op_enter(symbol_ne, "/=");
	sym_op_enter(symbol_in, "IN");
	sym_op_enter(symbol_notin, "NOTIN");

	symbol_order_type = sym_new(na_type);
	setname(symbol_order_type, "order_type");

	sym_op_enter(symbol_lt, "<");
	sym_op_enter(symbol_le, "<=");
	sym_op_enter(symbol_ge, ">=");
	sym_op_enter(symbol_gt, ">");

	symbol_numeric = sym_new(na_void);
	setname(symbol_numeric, "numeric");

	sym_op_enter(symbol_addu, "+u");
	sym_op_enter(symbol_subu, "-u");
	sym_op_enter(symbol_abs, "abs");
	sym_op_enter(symbol_add, "+");
	sym_op_enter(symbol_sub, "-");
	sym_op_enter(symbol_mul, "*");
	sym_op_enter(symbol_div, "/");
	sym_op_enter(symbol_mod, "mod");
	sym_op_enter(symbol_rem, "rem");
	sym_op_enter(symbol_exp, "**");
	sym_op_enter(symbol_cat, "&");
	sym_op_enter(symbol_cat_cc, "&cc");
	sym_op_enter(symbol_cat_ac, "&ac");
	sym_op_enter(symbol_cat_ca, "&ca");
	s = sym_new(na_op);
#ifdef IBM_PC
	ORIG_NAME(s) = strjoin("any_op", "");
#else
	ORIG_NAME(s) = "any_op";
#endif

	sym_op_enter(symbol_modi, "modi");
	sym_op_enter(symbol_remi, "remi");
	sym_op_enter(symbol_addui, "+ui");
	sym_op_enter(symbol_subui, "-ui");
	sym_op_enter(symbol_absi, "absi");
	sym_op_enter(symbol_addi, "+i");
	sym_op_enter(symbol_subi, "-i");
	sym_op_enter(symbol_muli, "*i");
	sym_op_enter(symbol_divi, "/i");
	sym_op_enter(symbol_addufl, "+ufl");
	sym_op_enter(symbol_subufl, "-ufl");
	sym_op_enter(symbol_absfl, "absfl");
	sym_op_enter(symbol_addfl, "+fl");
	sym_op_enter(symbol_subfl, "-fl");
	sym_op_enter(symbol_mulfl, "*fl");
	sym_op_enter(symbol_divfl, "/fl");
	sym_op_enter(symbol_addufx, "+ufx");
	sym_op_enter(symbol_subufx, "-ufx");
	sym_op_enter(symbol_absfx, "absfx");
	sym_op_enter(symbol_addfx, "+fx");
	sym_op_enter(symbol_subfx, "-fx");
	sym_op_enter(symbol_mulfx, "*fx");
	sym_op_enter(symbol_divfx, "/fx");
	sym_op_enter(symbol_mulfxi, "*fxi");
	sym_op_enter(symbol_mulifx, "*ifx");
	sym_op_enter(symbol_divfxi, "/fxi");
	sym_op_enter(symbol_mulfli, "*fli");
	sym_op_enter(symbol_mulifl, "*ifl");
	sym_op_enter(symbol_divfli, "/fli");

	sym_op_enter(symbol_expi, "**i");
	sym_op_enter(symbol_expfl, "**fl");

	symbol_exception = sym_new(na_exception);/* ?? check this */
	symbol_constraint_error = sym_new (na_exception);
	setname(symbol_constraint_error, "CONSTRAINT_ERROR");
	symbol_numeric_error = sym_new(na_exception);
	setname(symbol_numeric_error, "NUMERIC_ERROR");
	symbol_program_error = sym_new(na_exception);
	setname(symbol_program_error, "PROGRAM_ERROR");
	symbol_storage_error = sym_new(na_exception);
	setname(symbol_storage_error, "STORAGE_ERROR");
	symbol_tasking_error = sym_new(na_exception);
	setname(symbol_tasking_error, "TASKING_ERROR");
	symbol_system_error = sym_new(na_exception);
	setname(symbol_system_error, "SYSTEM_ERROR");


	/*
	 * Printable characters are entered into SYMBTAB, as overloaded
	 * literals whose source name is the character between single quotes.
 	*/
	{
		int	i;
		char   *s;
		Symbol sy;
		lmap = tup_new(2 * 128);

		for (i = 0; i <= 127; i++ ) {
			s = smalloc(4);
			s[3] = '\0';
			s[0] = '\'';
			s[1] = i;
			s[2] = '\'';
			lmap[2 * i + 1] = s;
			lmap[2 * i + 2] =(char *) i;
			/* if (i>=32 && i<=126 )   -- all ascii chars entered in SYMBTAB */
			sy = sym_new(na_literal);
			ORIG_NAME(sy) = s;
		}
		literal_map(symbol_character) =(Set) lmap;
	}
	for (i = 0; p = char_names[i]; i++) {
		if (p[0] == ' ')
			break;
		p1 = strchr(p, ' ');
		if (p1 == p)
			break;
		sym = sym_new(na_constant);
		TYPE_OF(sym) = symbol_character;
		SIGNATURE(sym) =(Tuple) val_nodea1(atoi(p1));
		name[0] = '\0';
		strncat(name, p, p1 - p);			/* extract string with name */
		setname(sym, strjoin(name, ""));	/* p1 points to original name */
	}

	s = sym_new(na_literal); 
	setname(s, "FALSE");
	TYPE_OF(s) = symbol_boolean;
	s = sym_new(na_literal); 
	setname(s, "TRUE");
	TYPE_OF(s) = symbol_boolean;

	{
		char   *litname;
		lmap = tup_new(4);
		litname = smalloc(6);
		lmap[1] = strcpy(litname, "FALSE");
		lmap[2] = (char *) 0;
		litname = smalloc(5);
		lmap[3] = strcpy(litname, "TRUE");
		lmap[4] =(char *) 1;
		literal_map(symbol_boolean) =(Set) lmap;
	}

	/*   The only predefined aggregate is the one for string literals.*/
	sym_new(na_aggregate);

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

	/* new symbol definitions that are common with the code generator should */
	/* be placed before this comment.					     */

	/* 'task_block' is marker symbol used in expand.c - it need never be
	 * written out
	 */
	symbol_task_block = sym_new(na_void);
	/* Initialize bounds of predefined types. */
	/* Note that val_node is only called from this procedure, so that
	 * calling sequence can be changed if necessary; moreover the code
	 * should be put in this module, not in utilities
	 */

	/* set size of init_nodes.
	 * NOTE, must NOT make any new entries to init_nodes after
	 * doing assignment of tup_size below	ds 24 sep 84
	 */
	init_nodes[0] = (char *)init_node_count;
#ifdef DEBUG
	if (list_unit_0)
		zpunit(0);
#endif
}

/* In C, need several versions of val_node, since we cannot test argument
 * type as we can in SETL
 */

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

static Node val_nodea1(int init_val)							/*;val_nodea1*/
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

static Node val_node2(double init_val)						/*;val_node2*/
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

static Node val_node3(Rational init_val)						/*;val_node3*/
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

static void init_node_save(Node node)						/*;init_node_save*/
{
	init_node_count += 1;
	init_nodes[init_node_count] = (char *)node;
}

static void sym_inits(Symbol sym, Symbol typ, Tuple sig, Symbol ali)
															  	/*;sym_inits*/
{
	/* initialize standard part of symbol. These are the fields used
	 * by both adasem and adagen.
	 */

	TYPE_OF(sym) = typ;
	SIGNATURE(sym) = sig;
	ALIAS(sym) = ali;
}

static void sym_initg(Symbol sym, int tkind, int r1, int r2)	/*;sym_initg*/
{
	/* initialize the fields of a symbol used only by the code generator */
	if (tkind<=0) { /* if want to indicate type_size not defined */
		TYPE_SIZE(sym) = -1;
	}
	else {
		TYPE_KIND(sym) = tkind; /* type kind */
		TYPE_SIZE(sym) = su_size(tkind); /* storage units needed*/
	}
	S_SEGMENT(sym) = r1;
	S_OFFSET(sym) = r2;
	/* Note that the correct values of offsets for most of the standard
     * symbols are set by procedure main_data_segment() in glib.c
     */
	/* The following default value of MISC (happily) also corresponds to
     * setting CONTAINS_TASK(sym) to FALSE.
     */
	MISC(sym) = (char *) 0;
}
