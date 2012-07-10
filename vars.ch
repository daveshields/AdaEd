/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
H#ifndef _vars_h
H#define _vars_h

C#include "hdr.h"

/* vars.ch - global declarations and initializations */

/*
 *T+ GLOBAL DECLARATIONS and DEFINITIONS
 *S+ Constants
 */

X double	ADA_MIN_REAL INIT((-79228162514264337593543950336.0));/* - 2.0**96 */
X double	ADA_MAX_REAL INIT(79228162514264337593543950336.0);/* 2.0**96 */
X int	ADA_REAL_DIGITS INIT(6);
X int	cdebug2;

X Declaredmap declared_all[4];	/* array of standard declareds */
X int	full_others;  /* a boolean */
X int	fold_context; /* a boolean */
X Node current_node;
X Node OPT_NODE;	/*initialized in sem0 */

/* Initialized in SEMINIT */
/*
??const qualifiers = {as_qual_range,  as_qual_length,  as_qual_discr,
		    as_qual_arange, as_qual_alength, as_qual_adiscr };
 */

/*S+ Variables*/
 /* declared map from standard environment */
/*base_declared is array of copies of maps for standard0,standard,
umnentionable0, and ascii. base_declared_symbols is corresponding
array of symbol table pointers */
X Declaredmap base_declared[4];
X Symbol base_declared_symbols[4];
X Tuple scope_st;			/* stack of lexical scopes */
X Tuple has_return_stk;		/* stack to track return statements */
X Tuple newtypes;			/* list of type declaration code to be */
 /* emitted before declaration being processed. */
X Tuple lab_seen;			/* set of labels in procedure . */
X Tuple current_instances;	/* stack for recursive instantiation check */

X Symbol scope_name;		/* unique name for each scope */
X char *unit_name;		/* compilation unit information */
X Tuple all_vis;			/* Modules whose visibility is required */
				/* all_vis used only in ch. 10 */

X Tuple open_scopes;		/* nest of currently open scopes, from inner */
 /* to outer.  Outermost is STANDARD. */
X Tuple used_mods;		/* packages appearing in a use clause */
X Tuple vis_mods;	/* list of package names visible in this unit*/

X int	noop_error;

 /* used by procs init_compunit and compunit. */
X Set non_local_names;		/* To collect non_local references in each subp. */

X int	out_context;		/* Signals valid appearance of out parameter.  */

X Symbol
symbol_and,
symbol_andthen,
symbol_any,
symbol_any_id,
symbol_array_type,
symbol_ascii,
symbol_assign,
symbol_boolean,
symbol_boolean_type,
symbol_callable,
symbol_character,
symbol_character_type,
symbol_constrained,
symbol_constraint_error,
symbol_daccess,
symbol_dfixed,
symbol_discrete_type,
symbol_divfx,
symbol_duration,
symbol_eq,
symbol_exception,
symbol_float,
symbol_ge,
symbol_gt,
symbol_in,
symbol_incomplete,		/* incomplete, for incp_types */
symbol_integer,
symbol_le,
symbol_left,
symbol_limited,			/* limited for priv_types, incp_types */
symbol_limited_private,		/* cf. symbol_limited */
symbol_long_float,
symbol_long_integer,
symbol_lt,
symbol_main_task_type,
symbol_mulfx,
symbol_natural,
symbol_none,
symbol_not,
symbol_ne,
symbol_notin,
symbol_null,
symbol_numeric,
symbol_numeric_error,
symbol_or,
symbol_order_type,
symbol_orelse,
symbol_overloaded,
symbol_positive,
symbol_private,			/* for priv_types, incp_types */
symbol_program_error,
symbol_right,
symbol_short_integer,
symbol_short_integer_base,
symbol_standard,
symbol_standard0,
symbol_storage_error,
symbol_system_error,
symbol_string,
symbol_string_type,
symbol_system,
symbol_tasking_error,
symbol_undef,
symbol_universal_dfixed,
symbol_universal_fixed,
symbol_universal_integer,
symbol_universal_integer_1,
symbol_universal_real,
symbol_unmentionable,
symbol_xor;

/* following used in Chapter 4 mainly for check_type */
X Symbol 
symbol_universal_type,
symbol_integer_type,
symbol_real_type,
symbol_composite_type,
symbol_equal_type;


X Symbol
symbol_addu,  /* +u */
symbol_subu,  /* -u */
symbol_abs,  /* abs */
symbol_add,  /* + */
symbol_sub,  /* - */
symbol_mul,  /* * */
symbol_div,  /* / */
symbol_mod,  /* mod */
symbol_rem,  /* rem */
symbol_exp,  /* ** */
symbol_cat,  /* & */
/* new symbols for the catenation operations */
symbol_cat_cc, /* &cc */
symbol_cat_ac, /* &ac */
symbol_cat_ca, /* &ca */
symbol_modi,  /* modi */
symbol_remi,  /* remi */
symbol_addui,  /* +ui */
symbol_subui,  /* -ui */
symbol_absi,  /* absi */
symbol_addi,  /* +i */
symbol_subi,  /* -i */
symbol_muli,  /* *i */
symbol_divi,  /* /i */
symbol_addufl,	/* +ufl */
symbol_subufl,	/* -ufl */
symbol_absfl,  /* absfl */
symbol_addfl,  /* +fl */
symbol_subfl,  /* -fl */
symbol_mulfl,  /* *fl */
symbol_divfl,  /* /fl */
symbol_addufx,	/* +ufx */
symbol_subufx,	/* -ufx */
symbol_absfx,  /* absfx */
symbol_addfx,  /* +fx */
symbol_subfx,  /* -fx */
symbol_mulfxi,	/* *fxi */
symbol_mulifx,	/* *ifx */
symbol_divfxi,	/* /fxi */
symbol_mulfli,	/* *fli */
symbol_mulifl,	/* *ifl */
symbol_divfli,	/* /fli */
symbol_expi,  /* **i */
symbol_expfl;  /* **fl */

X Tuple unary_sig;
X Tuple binary_sig; /* TBSL: to be initialized in sem0*/

X int num_predef_units; /* number of units in predef.ada */

X int errors INIT(FALSE); /* flag if errors are present*/

/* adaval_overflow is set to indicate overflow from adaval; corresponds
 * to SETL ADAVAL returning 'OVERFLOW'
 */
X int adaval_overflow; 
X char *FILENAME;
X FILE *MSGFILE INIT(stdout);
/* added 24 sep 84*/
/* init_nodes is tuple of nodes needed by save_tree (10) */
X Tuple init_nodes;
X Tuple init_symbols; /* tuple of symbols created by sem initialization*/
/* varying length tuple, unit_nodes_n gives current length */
X Tuple unit_nodes;
#ifdef TBSL
X int unit_nodes_n INIT(0);
#endif
X char *PREDEFNAME; /* name of predef file */
X char *AISFILENAME;
X int lib_option INIT(FALSE);
X int new_library INIT(FALSE); /* set if creating library */
X struct unit *pUnits[MAX_UNITS+1];
X Tuple lib_stub;
X Tuple stub_info;

X int seq_node_n INIT(0); /* number of nodes allocated */
X Tuple seq_node; /* tuple of allocated nodes*/
X int seq_symbol_n INIT(0);/* number of symbols allocated*/
X Tuple seq_symbol;	/* tuple of allocated symbols */

/* added 12 oct 84 to track nodes read from ast */
X int unit_number_now INIT(0);
X int unit_numbers INIT(0);
X int empty_unit_slots INIT(0);

/* following variables used to trap references to selected node or symbol.
 * Node specified by trapns and trapnu (giving node sequence and unit),
 * symbol specified by trapss and trapsu (giving symbol sequence and unit).
 * These are meaningful only if either nonzero. When a trapped node referenced,
 * then procedure trap is called.
 * Code to watch for traps is planted at several places, notably sym_new,
 * node_new, zptupsym, zptupnod (these latter two do not call trap).
 */
X int trapns INIT(0),trapnu INIT(0),trapss INIT(0),trapsu INIT(0);

X Tuple aisunits_read;

X Nodemap node_map;
/* OPT_NAME is used by code_generator but defined here so it can be
 * referenced from libr procedures */
X Symbol OPT_NAME; /* This is to symbols what OPT_NODE is to nodes*/

/* compiling predef */
X int	compiling_predef INIT(0); /* set if we are compiling predef */

/* the following are used to avoid having string literals in code that
 * might be overlaid on the PC 
 */
X char *string_any_id  INIT("any_id"); 
X char *string_ok  INIT("ok");
X char *string_ds  INIT("$D$");
/* variables to report result from power_of_2(), thus avoiding
 * need to compute a tuple, as is done in SETL version.
 */
X int power_of_2_accuracy; 
X int power_of_2_power;
X Rational power_of_2_small;
X Set stubs_to_write;
X Tuple NOT_CHOSEN;
H#endif
