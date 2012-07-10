/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#define GEN

#include <stdio.h>
#include <ctype.h>
#include "hdr.h"
#include "vars.h"
#include "gvars.h"
#include "libhdr.h"
#include "segment.h"
#include "ifile.h"
#include "dbxprots.h"
#include "packprots.h"
#include "g0aprots.h"
#include "dclmapprots.h"
#include "arithprots.h"
#include "axqrprots.h"
#include "axqwprots.h"
#include "genprots.h"
#include "segmentprots.h"
#include "expandprots.h"
#include "procprots.h"
#include "libprots.h"
#include "libfprots.h"
#include "librprots.h"
#include "libwprots.h"
#include "readprots.h"
#include "setprots.h"
#include "initprots.h"
#include "glibprots.h"
#include "gutilprots.h"
#include "miscprots.h"
#include "gmiscprots.h"
#include "gmainprots.h"

static void fold_upper(char *);
static void preface();
static void exitf(int);
static void init_gen();
static void finit_gen();

IFILE	*AISFILE, *AXQFILE, *STUBFILE, *LIBFILE, *TREFILE;
int list_unit_0 = 0; /* set by '0' option to list unit 0 structure */
int peep_option = 1; /* on for peep_hole optimization */

extern Segment	CODE_SEGMENT, DATA_SEGMENT, DATA_SEGMENT_MAIN;
extern Tuple units_in_compilation;
extern Segment   VARIANT_TABLE, FIELD_TABLE ;

#ifdef DEBUG
extern int zpadr_opt; /* not for EXPORT */
#endif

char *lib_name;

main (int argc, char **argv)
{
	Node	 node_new ();
	int		c, i, n;
	int		errflg = 0, nobuffer = 0, mflag = 0;
	extern int  optind;
	extern char *optarg;
	char	*fname, *tfname;
	char	*t_name;

	AISFILE = (IFILE *)0;
	AXQFILE = (IFILE *)0;
	LIBFILE = (IFILE *)0;
	STUBFILE = (IFILE *)0;
	TREFILE = (IFILE *)0;

	MAINunit = "";
	interface_files = "";


	while ((c = getopt (argc, argv, "g:l:m:ni:")) != EOF)
		/*    user:
		 *	g	debugging, followed by list of options:
		 *		0	show structure of unit 0
		 *		b	do not buffer standard output
		 *		e	flag signalling errors in the parsing phase
		 *		g	list generated code
		 *		l	show line numbers in generated code
		 *		p	compiling predef units
		 *		z	call trapini to initialize traps
		 *      i   to specify object files and librairies for pragma interface
		 *  	l	using library
		 *		m	main unit name
		 *  	n	new library
		 */
		switch (c) {
		case 'i':
			interface_files = strjoin(interface_files, optarg);
			interface_files = strjoin(interface_files, " ");
			break;
		case 'l': /* using existing library */
			lib_name= emalloc((unsigned) strlen(optarg) + 1);
			strcpy(lib_name, optarg);
			break;
		case 'm': /* specify main unit name */
			MAINunit = malloc((unsigned) strlen(optarg)+1);
			strcpy(MAINunit, optarg);
			fold_upper(MAINunit);
			break;
		case 'n': /* indicates new library */
			new_library = TRUE;
			break;
		case 'g': /* gen debug options */
			n = strlen(optarg);
			for (i = 0; i < n; i++) {
				switch((int)optarg[i]) {
#ifdef DEBUG
				case 'a':
					zpadr_opt = 0; /* do not print addresses in zpadr */
					break;
#endif
				case 'g':
					list_code++;
					break;
				case 'l':
					line_option++;
					break;
				case 'p': /* compiling predef units */
					printf("compiling predef\n");
					compiling_predef++ ;
					break;
#ifdef DEBUG
				case 'b': /* do not buffer output */
					nobuffer++;
					break;
				case 'd': /* force debugging output */
					debug_flag++;
					break;
				case 'e':
					errors = TRUE;
					break;
				case 'o': /* disable optimization (peep) */
					peep_option = 0;
					break;
				case '0': /* read trace including unit 0 */
					list_unit_0++;
					break;
				case 'z': 
					trapini();
					break;
#endif
				}
			}
			break;
		case '?':
			errflg++;
		}
	fname = (char *)0;
	if (optind < argc)
		fname = argv[optind];
	if (fname == (char *)0) errflg++;
	if (errflg) {
		fprintf (stderr, "Usage: adagen -aAbglnmMnrstw file\n");
		exitp(RC_ABORT);
	}
	tup_init(); /* initialize set and tuple procedures */
	FILENAME =  (fname != (char *)0) ? strjoin(fname, "") : fname;

	if (compiling_predef) {
		PREDEFNAME = "";
	}
	else
		PREDEFNAME = predef_env();
	if (nobuffer) {
		setbuf (stdout, (char *) 0);	/* do not buffer output (for debug) */
	}
	rat_init(); /* initialize arithmetic and rational package*/
	dstrings_init(2048, 256); /* initialize dstrings package */
	init_sem();
	DATA_SEGMENT_MAIN = main_data_segment();
	aisunits_read = tup_new(0);
	init_symbols = tup_exp(init_symbols, seq_symbol_n);
	for (i = 1; i <= seq_symbol_n; i++)
		init_symbols[i] = seq_symbol[i];
	t_name = libset(lib_name);

	num_predef_units = (compiling_predef) ? 0 : init_predef();

	/*
	 * When the separate compilation facility is being used all references to
	 * AIS files will be made via the directory in LIBFILE. AISFILENAME is set
	 * to a number.
	 */
	if (compiling_predef)
		AISFILENAME = "0";
	else if (new_library)
		AISFILENAME = "1";
	else
		AISFILENAME = lib_aisname(); /* retrieve name from library */

	/* open the appropriate files using the suffix .axq for axq files and
	 * .trc for tree file. 
	 *
	 * Open MESSAGEFILE with suffixe ".msg" if a file name specified;
	 * otherwise, if a file name not required, and one is not given,
	 * used stderr.
	 */
	AXQFILE  = ifopen(AISFILENAME, "axq", "w", 0);

	MSGFILE = (FILENAME != (char *) 0 ) ? efopenl(FILENAME, "msg", "a", "t") :
	  stderr;

	/* delete any existing st2 file for this AISFILENAME since it is now
	 * obsolete
	 */
	ifdelete(strjoin(AISFILENAME, ".st2"));
	/* unbuffer output for debugging purposes */
	if (MSGFILE != stderr)
		setbuf(MSGFILE, (char *) 0);
	preface();

	/* Code formerly procedure finit() in init.c is now put here directly */
	if (!errors) {
		write_glib();
		cleanup_files();
	}

	if (compiling_predef) printf("Compilation of predef complete\n");
	exitf(RC_SUCCESS);
}

static void fold_upper(char *s)								/*;fold_upper*/
{
	register char c;

	while (c = *s) {
		if (islower(c)) *s = toupper(c);
		s++;
	}
}

void fold_lower(char *s)					/*;fold_lower*/
{
	register char c;

	while (c = *s) {
		if (isupper(c)) *s = tolower(c);
		s++;
	}
}

/* In the SETL version, preface has the global declarations of macros and
 * variables. In the C version, the global variables are defined in gvars.ch
 * (from which gvars.c and gvars.h are derived); macros and structure
 * declarations are in ghdr.h.
 * This file is retained for now to hold parts of code not moved to other
 * files in the C version.
 *
 * pref2 - part 2 of preface: global variables, procedure declarations 
 *
 * Conventions for capitalization.
 * The SETL version uses upper case names for some procedures, macros
 * and global variables. Since case conventions are not enforced by the
 * SETL compiler, there are cases where the same name is written more 
 * than one way, differing only in case.

 * In C, we will use upper case for macro names, defined constants and most
 * of the global variables, especially, the variables defined here. Where
 * mixed-case usage is known to exist in the SETL version, such will be
 * indicated by writine (mixed-case) after the variable name.
 */

/* macros moved to hdr.c*/

static Set units_loaded;

static void preface()										/*;preface*/
{
	int	indx, last_index, i, rootseq, body_number;
	Node	first_node, unit_node;
	Tuple	aisread_tup, tup;
	int unit_number_now;
	struct unit *pUnit;
	char	*spec_nam;
	aisread_tup = tup_new(0);
	initialize_1();
	/* 1- Load PREDEF */

	TASKS_DECLARED = FALSE;
	/* 2- Generate user program */

	initialize_2();

	if (gen_option) {
		/* read all the units in file, aisunits_read is tuple of unit names of
		 * units found in file.
		 */
		TREFILE  = ifopen(AISFILENAME, "aic", "r", 0);
		last_index = last_comp_index(TREFILE);
		indx = 0;
		units_loaded = set_new(0);
		for (indx = 1; indx <= last_index; indx++) {
			unit_name = read_ais(AISFILENAME, TRUE, (char *) 0, indx, TRUE);
			TREFILE  = ifopen(AISFILENAME, "trc", "r", 0);
			load_tre(TREFILE, indx);
			unit_number_now = unit_numbered(unit_name);
			pUnit = pUnits[unit_number_now];
			seq_node_n = pUnit->treInfo.nodeCount;
			seq_node = tup_new(seq_node_n);

			/* set seq_symbol to corresponding values of symbols just read in */
			seq_symbol_n = pUnit->aisInfo.numberSymbols;
			tup = (Tuple) pUnit->aisInfo.symbols;
			if ((int) seq_symbol[0] < seq_symbol_n)
				seq_symbol = tup_exp(seq_symbol, seq_symbol_n);
			for (i = 1; i <= seq_symbol_n; i++)
				seq_symbol[i] = (char *) tup[i];

			rootseq = pUnit->treInfo.rootSeq;
			first_node = (Node) getnodptr(rootseq, unit_number_now);
			unit_node = N_AST2(first_node);
			init_gen();
			if (errors) {
				/* cannot retrieve message... already printed */
				user_info("Code generation for ");
				user_info(strjoin(formatted_name(unit_name), "abandonned"));
			}
			else {
				save_ada_line = ada_line;
				mint(unit_node);	/* remove qualify, name, parenthesis */
				expand(unit_node);
				if (errors) {
#ifdef DEBUG
					to_list("Expander stopped");
#endif
					exitf(RC_ERRORS);
				}
				ada_line = save_ada_line;
				if (N_KIND(unit_node) == as_separate)
					unit_node = N_AST2(unit_node);

				switch (N_KIND(unit_node)) {
				case (as_subprogram_tr):
					if (is_generic(unit_name)) {
						/* Have the spec  designate this AXQfile */
						/* spec_nam = ['subprog spec'] + unit_name(2..); */
						spec_nam = strjoin("ss", unit_name_names(unit_name));
						/* not sure about use of _MEMORY 
						 * LIB_UNIT(spec_nam)(2) = '_MEMORY';
						 * LIB_UNIT(spec_nam)(3) = '_MEMORY';
						 */
					}
					else {
						unit_subprog(unit_node);
					}
					break;
				case as_subprogram_decl_tr:
					unit_subprog_spec(unit_node);
					break;
				case(as_package_spec):
					unit_package_spec(unit_node);
					break;
				case(as_package_body):
					if (is_generic(unit_name)) {
						/* Have the spec  designate this AXQfile */
						/* spec_nam = ['spec'] + unit_name(2..); */
						spec_nam = strjoin("sp", unit_name_names(unit_name));
						/* not sure about use of _MEMORY 
						 * LIB_UNIT(spec_nam)(2) = '_MEMORY';
						 * LIB_UNIT(spec_nam)(3) = '_MEMORY';
						 */
					}
					else {
						unit_package_body(unit_node);
					}
					break;
				case(as_generic_function):
				case(as_generic_procedure):
					/* late_instances(UNIT_NAME(2)) := {}; */
					late_instances = tup_with(late_instances,(char *)unit_name);
					/* allocate unit_number for body */
					/* TBSL: this should be done for spec ONLY */
					body_number =
					  unit_number(strjoin("su", unit_name_names(unit_name)));
					pUnits[body_number]->libInfo.obsolete = string_ds;
					break;
				case(as_generic_package):
					/* late_instances(UNIT_NAME(2)) := {}; */
					late_instances = tup_with(late_instances,(char *)unit_name);
					/* allocate unit_number for body */
					/* TBSL: this should be done for spec ONLY */
					body_number =
					  unit_number(strjoin("bo", unit_name_names(unit_name)));
					pUnits[body_number]->libInfo.obsolete = string_ds;
					break;
				case(as_procedure_instance):
				case(as_function_instance):
				case(as_package_instance):
					compiler_error("Late instantiations not implemented");
					break;
				default:
					compiler_error_k("Unexpected unit: ", unit_node);
				}
				finit_gen();
				tup_free(seq_node);
				if (errors) {
#ifdef DEBUG
					to_list("Code generation stopped");
#endif
					exitf(RC_ERRORS);
				}
				store_axq(AXQFILE, unit_number_now);
			}
		} /* for */
	}
}

static void exitf(int status)										/*;exitf*/
{
	/* exit after closing any open files */
	ifoclose(AXQFILE);
	ifoclose(LIBFILE);
	ifoclose(STUBFILE);
	exitp(status);
}

void user_error(char *reason)									/*;user_error*/
{
	errors++;
	list_hdr(ERR_SEMANTIC);
	fprintf(MSGFILE, " %s\n", reason);
}

void user_info(char *line)										/*;user_info*/
{
	list_hdr(INFORMATION);
	fprintf(MSGFILE, "%s\n", line);
}

static void init_gen()											/*;init_gen*/
{
	/*
	 *  Initialization of global variables to be performed for each
	 *  compilation unit
	 */

	Tuple	tup;
	struct unit *pUnit;
	int		si, i, unum, u_new;
	int in_names, ii;
	char *tstr;
	char	*unam, *unam_type;
	Set		units_to_load;
	Forset	fs1;
	Fortup	ft1;
	Symbol	unit_unam;
	Tuple	s_info, decscopes, decmaps;
	Unitdecl	ud;
	Stubenv	ev;

	if (EMAP != (Tuple)0) tup_free(EMAP);
	EMAP = tup_new(0);
#ifdef TBSN
	/* STATIC_DEPTH POSITION and PATCHES are part of EMAP in C version */
	STATIC_DEPTH	     = {
	};
	POSITION	     = {
	};
	PATCHES	     = {
	};
#endif
	/* PATCH_SET is defined by never used
	 *  PATCH_SET	     = tup_new(0);
	 */
	PARAMETER_SET     = tup_new(0);
	RELAY_SET	     = tup_new(0);
	SPECS_DECLARED    =	0;
	SUBPROG_PATCH     = tup_new(0);
	SUBPROG_SPECS     = tup_new(0);
	GENERATED_OBJECTS = tup_new(0);
	DANGLING_RELAY_SETS	     = tup_new(0);
	/* Initialize slots correspondint to  SETL OWNED_SLOTS and BORROWED_SLOTS */
	/* Assume that unit_number_now has unit_number corresponding to unit_name */
	/* Set initial unit_slots map to null value */
	/* assume unit_number_now gives curent unit number; the correct
	 * assignment of this may best be done elsewhere
	 *	ds  6-20-85
	 */
	unit_number_now = unit_number(unit_name);
	tup = tup_new(5);
	for (i = 1; i <= 5; i++)
		tup[i] = (char *) tup_new(0);
	unit_slots_put(unit_number_now, tup);

	/* remove any slots belonging to this unit from previous compilation */
	remove_slots(CODE_SLOTS, unit_number_now);
	remove_slots(DATA_SLOTS, unit_number_now);

	/* remove any pragma interface belonging to this unit from previous
	 * compilation
	 */
	remove_interface(interfaced_procedures, unit_number_now);

	/*  Initialization of global variables */

#ifdef TBSN
	NATURE    = INIT_NATURE;
	TYPE_OF   = INIT_TYPE_OF;
	SIGNATURE = INIT_SIGNATURE;
	ALIAS     = INIT_ALIAS;
	TYPE_SIZE = INIT_TYPE_SIZE;
	MISC	     = INIT_MISC;
	INIT_PROC = {
	};
	CONSTANT_MAP	  = {
	};
	REFERENCE_MAP  = INIT_REFERENCE_MAP;
#endif
	STUBS_IN_UNIT  = FALSE;
	errors = FALSE;
	TASKS_DECLARED = FALSE;
	/*
	 * Load necessary (direct and indirect) units BEFORE this one, in order for 
	 * body's defns to override spec's. A 'subprog' is loaded only if there 
	 * is no corresponding 'subprog spec'. Bodies can be here because of pragma 
	 * ELABORATE, and need not be loaded. On the other hand, a body that is an 
	 * ancestor of the curr unit, or a generic body, needed for instantiation, 
	 * is loaded.
	 */
	ud = unit_decl_get(unit_name);
	unit_unam = ud->ud_unam;
	if (NATURE(unit_unam) != na_generic_procedure 
	  && NATURE(unit_unam) != na_generic_function
	  && NATURE(unit_unam) != na_generic_package) {
		/* do not bring in spec (or anything) for generic unit */
		/* units_to_load = PRE_COMP(unit_name); */
		pUnit = pUnits[unit_number_now];
		units_to_load = set_copy((Set) pUnit->aisInfo.preComp);
		while (set_size(units_to_load) != 0) {
#ifdef TRACE
			if (debug_flag)
				gen_trace_units("UNITS_TO_LOAD", units_to_load);
#endif
			/* unam from units_to_load; */
			unum = (int) set_from(units_to_load);
			unam = pUnits[unum]->name;
			unam_type = unit_name_type(unam);
			in_names = FALSE;
			tstr = strjoin("sp", unit_name_name(unam));
			for (ii = 1; ii <= unit_numbers; ii++) {
				if (streq(tstr, pUnits[ii]->name)) {
					in_names = TRUE;
					break;
				}
			}
			if (((streq(unam_type, "sp") || streq(unam_type, "ss"))
			  || (streq(unam_type, "su") && !in_names))
			  || is_ancestor(unam) || is_generic(unam)) {
				if (!set_mem((char *) unum, units_loaded)) {
					errors = errors || !load_unit(unam, TRUE);
					units_loaded = set_with(units_loaded, (char *) unum);
				}
				ud = unit_decl_get(unam) ;
				private_install(ud->ud_unam) ;
				/* units_to_load += PRE_COMP(unam) ? {}; --May be om if error */
				pUnit = pUnits[unum];
				if ((Set)pUnit->aisInfo.preComp != (Set)0) {
					/* add any units now yet seen to list of those to be loaded,
	    			 * but load no unit more than once.
	    			 */
					FORSET(u_new = (int), (Set)pUnit->aisInfo.preComp, fs1);
						if (!set_mem((char *) u_new, units_loaded))
							units_to_load =
							  set_with(units_to_load, (char *) u_new);
					ENDFORSET(fs1);
				}
				if (is_generic(unam)
				  && (streq(unam_type, "ss")||streq(unam_type, "sp"))) {
					char *fname, *body_name;
					if (streq(unam_type, "ss"))
						body_name = strjoin("su", unit_name_name(unam));
					else 
						body_name = strjoin("bo", unit_name_name(unam));
					fname = lib_unit_get(body_name) ;
					if (fname != (char *)0) {
						/* body already seen */
						load_unit(body_name, TRUE);
					}
					else {
						/* try to read from current file */
						read_ais(AISFILENAME, TRUE, body_name, 0, TRUE);
					}
				}
				/* Temp kludge until FE removes self references: (generics) */
				units_to_load = set_less(units_to_load, (char *) unum);
			}
		} /* end while */
		set_free(units_to_load);
	}

	if (errors) return;
#ifdef IGNORE
	ud = unit_decl_get(unit_name);
	/* [unit_unam, s_info, decls] = UNIT_DECL(unit_name); */
	unit_unam = ud->ud_unam;
#endif
	s_info = ud->ud_symbols;
	decscopes = ud->ud_decscopes;
	decmaps = ud->ud_decmaps;
	/* TBSL does the info from decscopes and decmaps need to be restored 
	 * or is the info restored by symtab_restore since 
	 * stored with the symbols.
	 * DECLARED  += decls; 
	 * SYMBTABQ restore 
	 */
	symtab_restore(s_info);

	if (is_subunit(unit_name)
	  && (NATURE(unit_unam) != na_generic_procedure
	  && NATURE(unit_unam) != na_generic_function)) {
		/* retrieve stub environment */

		/* [-, -, decl,-,-,-,-,-,-,-,package_info] = STUB_ENV(unit_name);
		 * loop forall decls = decl(os) do
		 *   loop forall [-, unam, entry] in decls do
		 *      SYMBTABF(unam) = entry;
		 *   end loop;
		 * end loop;
		 */
		if (!streq(lib_stub_get(unit_name), AISFILENAME))
			read_stub(lib_stub_get(unit_name), unit_name, "st2");
		si = stub_numbered(unit_name);
		tup = (Tuple) stub_info[si];
		ev = (Stubenv) tup[2];
		update_stub(ev);
		s_info = ev->ev_open_decls;
		symtab_restore(s_info);
	}
	DATA_SEGMENT = segment_new(SEGMENT_KIND_DATA, 0);
	CODE_SEGMENT = segment_new(SEGMENT_KIND_CODE, 0);

	/* If the unit was previously compiled remove possible obselete stubs of it
	 * from the library.
	 */
	FORTUP(unam = (char *), lib_stub, ft1);
		if (stub_parent_get(unam) ==  unit_number_now)
			lib_stub_put(unam, (char *)0);
	ENDFORTUP(ft1);

#ifdef MACHINE_CODE
	if (list_code) {
		to_gen(" ");
		to_gen(" ");
		to_gen_unam("============== UNIT : ", formatted_name(unit_name),
		    " ==============" );
	}
#endif
}

static void finit_gen()											/*;finit_gen*/
{
	/*
	 * Clean up symbol table, and write it back to file, together with
	 * the code slots and the data_segment
	 */

	int			unum;
	Set			precedes, suppressed_units;
	Forset		fs1;
	Fortup		ft1;
	struct unit *pUnit;
	Tuple		symbols, new_comp_table;
	Symbol		package_name;
	Unitdecl		ud;

#ifdef MACHINE_CODE
	if (list_code) {
		to_gen(" ");
		to_gen_unam("============== end of " , formatted_name(unit_name),
		    " ==============" );
		to_gen(" ");
		to_gen("--- Global reference map :");
		print_ref_map_global();
	}
#endif
	/* If it is a package, swap private and full declarations 
	 *
	 * if UNIT_NAME(1) in {'spec', 'body'} then
	 *   package_name = UNIT_NAME(2);
	 *   temp_symbtab = {};
	 *   loop forall [unam, entry] in OVERLOADS(package_name) ? {} do
	 *	   temp_symbtab(unam) = SYMBTABF(unam);
	 *	   SYMBTABF(unam) = entry;
	 *    end loop;
	 *    OVERLOADS(package_name) = temp_symbtab;
	 *  end if;
	 */
	ud = unit_decl_get(unit_name);
	if (!is_generic(unit_name) && (streq(unit_name_type(unit_name), "sp")
	  || streq(unit_name_type(unit_name), "bo"))) {
		package_name =  ud->ud_unam;
		private_exchange(package_name) ;
	}

	/* Add Code generator infos to unit symbol table 
	 *  [unit_unam, s_info, decls, old_vis, notvis, context, unit_nodes] =
	 *     UNIT_DECL(unit_name);
	 *
	 * loop forall unam in domain s_info do
	 * s_info(unam) = SYMBTABFQ(unam);
	 * end loop;
	 *
	 * Add infos for internally generated objects 
	 *
	 * loop forall unam in GENERATED_OBJECTS do
	 *  s_info(unam) = SYMBTABFQ(unam);
	 * end loop;
	 *
	 * UNIT_DECL(unit_name) =
	 *	[unit_unam, s_info, decls, old_vis, notvis, context, unit_nodes];
	 */

	symbols = ud->ud_symbols;
	symbols = tup_add(symbols, GENERATED_OBJECTS);
	ud->ud_symbols = symbols;

	if (!is_generic(unit_name)) {
		/* DATA_SEGMENT_MAP(CURRENT_DATA_SEGMENT) = DATA_SEGMENT;*/
		DATA_SEGMENT_MAP = segment_map_put(DATA_SEGMENT_MAP,
		  CURRENT_DATA_SEGMENT, DATA_SEGMENT);
#ifdef MACHINE_CODE
		if (list_code) print_data_segment();
#endif
	}
	if (errors) {
		to_gen_unam("Error(s) were detected in ",
		  formatted_name(unit_name), " unit not inserted in library");
	}
#ifdef TBSL
	else {
		if (is_generic(unit_name)) {
			/* Free slots allocated by INIT_GEN */
			OWNED_SLOTS(unit_name) = [ {}, {}, {}];
		}
#endif
	/*  Suppress dependant units and collect their slots; update library */
	/*    Report all units which are removed */
	if (!compiling_predef)
		suppressed_units = remove_same_name(unit_name);
	else
		suppressed_units = set_new(0);
#ifdef TBSL
		set_ds = set_cs :
		= set_es :
		  = {
		  };
#endif
	if (set_size(suppressed_units) != 0) {
		to_list( strjoin(
		  "Following unit(s) have been deleted by compilation of ",
		  formatted_name(unit_name) ) );
		FORSET(unum = (int), suppressed_units, fs1);
			to_list(formatted_name(pUnits[unum]->name));

			/* LIB_UNIT(unam) = OM; */
			lib_unit_put(pUnits[unum]->name, (char *)0);
			precedes_map_put(pUnits[unum]->name, set_new(0));
			/* remove slots belonging to obselete units */
			remove_slots(CODE_SLOTS, unum);
			remove_slots(DATA_SLOTS, unum);
			/* remove pragma interface belonging to obsolete units */
			remove_interface(interfaced_procedures, unum);
		ENDFORSET(fs1);
		to_list(" ");
	}
#ifdef TBSL
	/* Warning: user units may have same name as a predefined one */
	PREDEF_UNITS = [[unam in PREDEF_UNITS(1)
		  | unam notin suppressed_units with unit_name],
	       PREDEF_UNITS(2) - suppressed_units less unit_name
	      ];

	DATA_SLOTS     = { [x, y]: 
		[x, y] in DATA_SLOTS
		    |   y notin set_ds
		    or y in OWNED_SLOTS(unit_name)(1)		};
	CODE_SLOTS     = { [x, y]: 
		[x, y] in CODE_SLOTS
		    |   y notin set_cs
		    or y in OWNED_SLOTS(unit_name)(2)		};
	EXCEPTION_SLOTS= { [x, y]: 
		[x, y] in EXCEPTION_SLOTS
		    |   y notin set_es
		    or y in OWNED_SLOTS(unit_name)(3)		};
	/* less unit_name: temporary kludge FE. */
#endif
	/* precedes{unit_name} = PRE_COMP(unit_name) less unit_name; */
	pUnit = pUnits[unit_number_now];
	precedes = set_copy((Set)pUnit->aisInfo.preComp);
	precedes_map_put(unit_name, precedes);
	/* compilation_table = [name: name in compilation_table
	 *  			| name notin suppressed_units]	with unit_name;
	 */
	new_comp_table = tup_new(0);
	FORTUP(unum = (int), compilation_table, ft1);
		if (!set_mem((char *)unum,
		   suppressed_units) && unum != unit_number_now)
			new_comp_table = tup_with(new_comp_table, (char *) unum);
	ENDFORTUP(ft1);
	compilation_table = tup_with(new_comp_table, (char *) unit_number_now);
	lib_unit_put(unit_name, AISFILENAME);
	/* if the same compilation unit appears in the same compilation (file)
	 * more than once, disable the code for all but the last in the axqfile
	 * so that it is not read.
	 */
	if (tup_mem((char *)unit_number_now, units_in_compilation))
		overwrite_unit_name(unit_name);

	units_in_compilation = 
	  tup_with(units_in_compilation, (char *)unit_number_now);

	pUnit->libInfo.currCodeSeg = (char *) CURRENT_CODE_SEGMENT;
	if (STUBS_IN_UNIT)
		pUnit->libInfo.localRefMap = (char *) tup_copy(LOCAL_REFERENCE_MAP);
}
