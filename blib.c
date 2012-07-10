/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#define GEN

#include "hdr.h"
#include "libhdr.h"
#include "vars.h"
#include "segment.h"
#include "gvars.h"
#include "ops.h"
#include "type.h"
#include "ifile.h"
#include "axqrprots.h"
#include "genprots.h"
#include "segmentprots.h"
#include "ginterprots.h"
#include "setprots.h"
#include "bmainprots.h"
#include "gutilprots.h"
#include "dclmapprots.h"
#include "libprots.h"
#include "libfprots.h"
#include "librprots.h"
#include "glibprots.h"
#include "miscprots.h"
#include "gmiscprots.h"
#include "smiscprots.h"
#include "gnodesprots.h"
#include "blibprots.h"

static void update_elaborate(char *);
static void main_code_segment();
static Tuple delayed_map_get(int);
static void delayed_map_put(int, Tuple);
static void delayed_map_undef(int);
static void add_code(char *);
static int needs_body_bnd(char *);
static int depth_level(char *);
static Tuple build_relay_sets(char *, int);
static void update_subunit_context(char *);
static int load_binding_unit(char *);
static char *read_binding_ais(char *, char *);

extern int ADA_MIN_INTEGER, ADA_MAX_INTEGER;
extern int adacomp_option;
extern long ADA_MIN_FIXED, ADA_MAX_FIXED;
extern Segment	CODE_SEGMENT, DATA_SEGMENT, DATA_SEGMENT_MAIN;
extern IFILE *AXQFILE, *LIBFILE, *AISFILE, *STUBFILE;

/* variables used only by binder */
static Symbol	mainunit_sym;

int binder(Tuple aisread_tup)									/*;binder*/
{
	/*
	 * BINDER checks the program library of a given main program for
	 * completeness.  Missing modules are printed.
	 * Otherwise, idle_task and main_task are generated. idle_task calls
	 * the initialization procedures required to elaborate the various
	 * units in (one of) the order(s) prescribed by the language
	 */

	char	*name, *body, *main_name, *s_name;
	int		prior, unit, name_num, delayed_unit;
	Set		elaborated, idle_precedes, precedes;
	struct unit *pUnit;
	Tuple	missing_units, to_check, to_bind, u_slots, tup;
	Tuple	elaboration_table, compiled_units, delayed, s, u_rs;
	Fortup	ft1;
	Forset	fs1;
	Unitdecl	ud;
	int		i, n;
	int         is_interfaced_bind_unit_now;

#ifdef DEBUG
	Tuple       axq_needed; /* list of predefined units */
#endif

	/* Reset global tuple of node and symbols for binder. */
	seq_node_n = 0;
	seq_node = tup_new(SEQ_NODE_INC);
	seq_symbol_n = 0;

	/*  Miscelleanous variables needed for code generation */
	LOCAL_REFERENCE_MAP =  local_reference_map_new();
	RELAY_SET = tup_new(0);
	/*
	 * POSITION and PATCHES is stored in EMAP and is set implicitly when a new
	 * EMAP is created for a symbol and therefore is not needed here.
	 *
	 * POSITION	 = {};
	 * PATCHES	 = {};
	 */
	CURRENT_LEVEL = 0;
	LAST_OFFSET	 = 0;
	MAX_OFFSET	 = 0;

	call_lib_unit = tup_new(0);

	if (streq(MAINunit, "")) {
		to_check = tup_new(0);
		/* collect all possible main units i.e. all parameterless subprograms
		 * which are not proper bodies (subunits).
		 */
		for (i = 15; i <= unit_numbers; i++) {
			struct unit *pUnit = pUnits[i];
			if (pUnit->isMain && !streq("ma", unit_name_type(pUnit->name)))
				to_check = tup_with(to_check,pUnit->name);
		}
		if (tup_size(to_check) == 0) {
			user_error("No subprogram in library");
			return FALSE;
		}
		else if (tup_size(to_check) == 1) {
			main_name = tup_frome(to_check);
			MAINunit  = unit_name_name(main_name);
		}
		else {
			user_error(
				  "Several subprograms in library please specify main from:");
			FORTUP(name = (char *), to_check, ft1);
				user_info(unit_name_name(name));
			ENDFORTUP(ft1);
			return FALSE;
		}
	}
	else {
		main_name = strjoin("su", MAINunit);
	}

	if (!load_binding_unit(main_name)) {
		/* message cannot retrieve... already printed */
		return FALSE;
	}
	update_elaborate(main_name);
	ud = unit_decl_get(main_name);
	mainunit_sym = ud->ud_unam;
	if (NATURE(mainunit_sym) != na_procedure	/* only procedures */
	  || tup_size(SIGNATURE(mainunit_sym)) != 0) {	/* without parameters */
		user_error(strjoin(formatted_name(main_name),
		  " is not a valid main program."));
		return FALSE;
	}
	name  = strjoin(MAINunit, "_idle_task");
	/* The name of the binding unit is "ma" followed by the name */
	/* In SETL unit_name was ['main_unit', name] */
	/* Note that this may create a new unit */
	unit_name	  = strjoin("ma", name);
	unit_number_now  = unit_number(unit_name);
	lib_unit_put(unit_name, AISFILENAME);

	/*	Symbol table initialized with 'main_task_type' */

	symbol_main_task_type = sym_new(na_task_type);
	TYPE_OF(symbol_main_task_type) = symbol_main_task_type;
	SIGNATURE(symbol_main_task_type) = tup_new(0);
	ALIAS(symbol_main_task_type) = symbol_main_task_type;
	ORIG_NAME(symbol_main_task_type) = "main_task_type";
	DECLARED(symbol_main_task_type) = dcl_new(0);
	TYPE_KIND(symbol_main_task_type) = TK_WORD;
	TYPE_SIZE(symbol_main_task_type) = su_size(TK_WORD);
#ifdef TBSL
	/* REFERENCE_MAP = {['main_task_type', [1, 47]]}; */
	S_SEGMENT(symbol_main_task_type) = 1;
	S_OFFSET(symbol_main_task_type)  = 47;
#endif
	MISC(symbol_main_task_type) = (char *)TRUE;

	/* Here we duplicate that part of the code from init_gen needed
	 * when starting a new unit
	 *
	 * Set initial unit_slots map to null value 
	 * assume unit_number_now gives curent unit number; the correct
	 * assignment of this may best be done elsewhere
	 */
	tup = tup_new(5);
	for (i = 1; i <= 5; i++)
		tup[i] = (char *) tup_new(0);
	unit_slots_put(unit_number_now, tup);
	to_check	  = tup_new1(main_name);
	idle_precedes  = set_new1((char *) unit_numbered(main_name));
	to_bind	  = tup_new(0);
	missing_units  = tup_new(0);
	compiled_units = tup_new(unit_numbers);
	for (i = 1; i <= unit_numbers; i++)
		compiled_units[i] = pUnits[i]->libUnit;

	/* check that any needed unit has been compiled. 
	 *
	 * All units needed (directly or indirectly) by main_name are checked. 
	 * The order in which these checks are performed is unimportant. The 
	 * ordering map 'precedes' has been loaded from library, for later use 
	 * in a topological sort. 
	 *
	 * All units needed, but not referenced by with clauses (typically 
	 * package bodies, procedure bodies and subunits) are noted into 
	 * idle_precedes to make later idle_task depend on them, in order to 
	 * suppress the binding unit if they are recompiled. 
	 */

	while (tup_size(to_check)!= 0) {

		/* always load the item at the front of the queue so that specs are
		 * read before their bodies.
		 * TBSL: this is due to the fact that the body sometimes contains
		 * info that is not in the spec(e.g. ASSOC_SYMBOLS) and since they share
		 * the same symbol the info would be overridden by the spec if the spec 
		 * was read last.
		 */
		name = tup_fromb(to_check);
		if (is_generic(name))
			continue;

		/* Check to see whether a package specification requires a body and
		 * if yes, that the body has been compiled.
		 */
		if (streq(unit_name_type(name), "sp")
		  || streq(unit_name_type(name), "bo")) {
			/* AXQ needed */
			if (!load_binding_unit(name))
				missing_units = tup_with(missing_units, name);
			else
				update_elaborate(name);
		}
		/* Collect the stubs of the current unit. */
		s = stubs(name);
		/*
		 * to_check      +:= s;
		 * missing_units +:= s - compiled_units;  
		 * idle_precedes +:= s;
		 */
		FORTUP(s_name = (char *), s, ft1);
			 if (!tup_memstr(s_name, to_check))
				 to_check = tup_with(to_check, s_name);
			 if (!tup_memstr(s_name, compiled_units))
				 missing_units = tup_with(missing_units, s_name);
			 idle_precedes = set_with(idle_precedes,
			   (char *) unit_numbered(s_name));
		ENDFORTUP(ft1);

		if (streq(unit_name_type(name), "sp")) {
			body = strjoin("bo", unit_name_name(name));
			if (tup_memstr(body, compiled_units)) {
				to_check = tup_with(to_check, body);
				idle_precedes = set_with(idle_precedes,
				  (char *)unit_numbered(body));
			}
			else if (needs_body_bnd(name))
				missing_units = tup_with(missing_units, body);
		}
		else if (streq(unit_name_type(name), "ss")) {
			/* Suprogram body must be present.*/
			body = strjoin("su", unit_name_name(name));
			if (tup_memstr(body, compiled_units) && load_binding_unit(body)) {
				to_check = tup_with(to_check, body);
				update_elaborate(body);
			}
			else
				missing_units = tup_with(missing_units, body);
			idle_precedes = set_with(idle_precedes,
			  (char *) unit_numbered(body));
		}

		else if (streq(unit_name_type(name), "su")) {
			if (is_subunit(name)) {     /* no previous unit spec, of course. */
				if (load_binding_unit(name))
					update_elaborate(name);
			}
			else if (!tup_memstr(name, compiled_units))   /* no previous spec */
				missing_units = tup_with(missing_units, name);
		}

		/* Check the units indicated by visibility lists (precedes).
		 *  
		 * loop forall prior in precedes{name} | prior notin to_bind do
		 *    to_check with= prior;
		 * end loop forall;
		 */
		precedes = precedes_map_get(name);
		FORSET(prior = (int), precedes, fs1);
			 if (!tup_memstr(pUnits[prior]->name, to_bind))
				 to_check = tup_with(to_check, pUnits[prior]->name);
		ENDFORSET(fs1);

		if (is_subunit(name) && tup_memstr(name, compiled_units))
			update_subunit_context(name);

		to_bind = tup_with(to_bind, name);

	} /* end while */

	/* If compilation units are missing, report them and return. */

	if (tup_size(missing_units) != 0) {
		user_error("Missing units in library:");
		FORTUP(name = (char *), missing_units, ft1);
			user_info(formatted_name(name));
		ENDFORTUP(ft1);
		return FALSE;
	}
	if (tup_size(interfaced_procedures) != 0) {
		int i, j, n, m;
		n = tup_size(interfaced_procedures);
		m = tup_size(to_bind);
		for (i = 1; i <= n; i += 2) {
			for (j = 1; j <= m; j++) {
				if((int)interfaced_procedures[i] == unit_numbered(to_bind[j])) {
					/* the field of is_main which is usualy always 0 for a
					 * binding unit is set to 1 in this case to specify that
					 * this binding unit calls an interfaced subprogram
					 */
					pUnits[unit_number_now]->isMain = 1;
					is_interfaced_bind_unit_now = 1;
					break;
				}
				else {
					is_interfaced_bind_unit_now = 0;
				}
			}
		}
	}
	else {
		is_interfaced_bind_unit_now = 0;
	}

	if (is_interfaced_bind_unit_now) geninter(to_bind);
	/*
	 * call_lib_unit is built in an order consistent with the rules for 
	 * the elaboration of library units. 
	 * The algorithm tries to use the compilation order, unless some unit 
	 * depends on a not yet elaborated unit. In that case, it is appended 
	 * to a list of units depending on one of the not yet elaborated units 
	 * When this unit is elaborated, one tries again to elaborate units 
	 * depending on it. 
	 * If a unit depends on one of its own delayed units, it is a 
	 * circularity 
	 * elaborated: set of already elaborated units 
	 * delayed	 : map from units to the list of dependant units. 
	 */

	/* Use the compilation order */
	/* TBSL: for now we elaborate all units even if we don't use them.
	 * a better scheme is to have elaboration_table be only units we need.
	 */
	elaboration_table = tup_copy(compilation_table);
	elaborated	     = set_new1((char *)0);
	DELAYED_MAP      = tup_new(0);
#ifdef DEBUG
	axq_needed        = tup_new(0);
#endif

	while (tup_size(elaboration_table) != 0) {
		name_num = (int) tup_fromb(elaboration_table);
		name = pUnits[name_num]->name;

		if (is_generic(name) || is_subunit(name)) {
			/* Generics are not elaborated 
			 * subunits are elaborated from the parent 
			 */
			elaborated = set_with(elaborated, (char *) name_num);
		}
		else if (!tup_memstr(name, to_bind)) {
			/* Don't need this unit */
		}
		else if (set_subset(precedes_map_get(name), elaborated)) {
			/* May elaborate this unit now */
			add_code(name);
			elaborated = set_with(elaborated, (char *) name_num);
#ifdef TBSL
			if (name_num < 11) { /* predef unit */
#endif
			/*
			 * if (name in domain delayed) then 
			 * -- Retry units depending on this one 
			 *   elaboration_table := delayed(name) + elaboration_table;
			 *   delayed(name) := OM;
			 * end if;
			 */
			n = tup_size(DELAYED_MAP);
			for (i = 1; i <= n; i += 2) {
				if (DELAYED_MAP[i] == (char *)name_num) {
					/* Retry units depending on this one */
					elaboration_table=
					  tup_add(delayed_map_get(name_num), elaboration_table);
					delayed_map_undef(name_num);
					break;
				}
			}
		}
		else {
			/* Depends on a not yet elaborated unit => delay elaboration */
			precedes = precedes_map_get(name);
			unit     = (int) set_arb(set_diff(precedes, elaborated));
			/* delayed(unit) = (delayed(unit) ? []) with name; */
			delayed = delayed_map_get(unit);
			if (delayed == (Tuple)0)
				delayed_map_put(unit, tup_new1((char *) name_num));
			else
				delayed_map_put(unit, tup_with(delayed, (char *)name_num));
			/* TBSL: This code to be removed when predef is handled correctly */
			if (name_num < num_predef_units) {
				elaboration_table =
				  tup_add(tup_new1((char *)unit), elaboration_table);
			}
		}
	} /* end while */

	/* Check for circularity among units */
	n = tup_size(DELAYED_MAP);
	if (n != 0) {
		user_error("Circularity detected among these units:");
		for (i = 1; i <= n; i += 2) {
			delayed = (Tuple) DELAYED_MAP[i+1];
			FORTUP(delayed_unit = (int), delayed, ft1);
				user_info(formatted_name(pUnits[delayed_unit]->name));
			ENDFORTUP(ft1);
		}
		return FALSE;
	}

	/* Everything is OK: build idle and main task */

#ifdef TBSL
	axqfiles_read = tup_with(axqfiles_read, AXQfile);
	aisread_tup(1)    with= unit_name;
#endif

	CURRENT_DATA_SEGMENT = 1;
	CURRENT_CODE_SEGMENT = 1;
#ifdef MACHINE_CODE
	if (list_code) {
		to_gen(" ");
		to_gen(" ");
		to_gen_unam("============== UNIT : ", formatted_name(unit_name),
		  " ==============");
		to_gen(" ");
		to_gen("--- Idle task ---");
		to_gen_int("	data slot # ", CURRENT_DATA_SEGMENT);
		to_gen_int("	code slot # ", CURRENT_CODE_SEGMENT);
		to_gen(" ");
	}
#endif
	u_slots = tup_new(5);
#ifdef DEBUG
	if(tup_size(axq_needed)) { /* binding requiring predef data segments */
		tup = read_predef_axq(axq_needed);
		u_slots[SLOTS_DATA] = (char *)tup_with((Tuple) tup[1],
		  (char *)CURRENT_DATA_SEGMENT);
		u_slots[SLOTS_CODE] = (char *)tup_with((Tuple) tup[2],
		  (char *)CURRENT_CODE_SEGMENT);
	}
	else { /* library option or no predefined unit needed */
		u_slots[SLOTS_DATA] = (char *)tup_new1((char *)CURRENT_DATA_SEGMENT);
		u_slots[SLOTS_CODE] = (char *)tup_new1((char *)CURRENT_CODE_SEGMENT);
	}
#else
	u_slots[SLOTS_DATA] = (char *)tup_new1((char *)CURRENT_DATA_SEGMENT);
	u_slots[SLOTS_CODE] = (char *)tup_new1((char *)CURRENT_CODE_SEGMENT);
#endif
	u_slots[SLOTS_EXCEPTION] = (char *)tup_new(0);
	u_slots[SLOTS_DATA_BORROWED] = (char *)tup_new(0);
	u_slots[SLOTS_CODE_BORROWED] = (char *)tup_new(0);
	unit_slots_put(unit_number_now, u_slots);

	precedes_map_put(unit_name, idle_precedes);

	DATA_SEGMENT = DATA_SEGMENT_MAIN;

	/* Compute the relay sets of subunits: 
	 *
	 * loop forall name in to_bind | not is_subunit(name) do
	 *  [-, u_rs] = build_relay_sets(name, 1);
	 *  if (u_rs !== []) then 
	 *	 COMPILER_ERROR ("Relay set at level 1 in "+formatted_name(name));
	 *	if debug_flag then
	 *	   gen_trace("BINDER", u_rs);
	 *	end if;
	 *  end if;
	 * end loop;
	 */

	FORTUP(name = (char *), to_bind, ft1);
		if (!is_subunit(name)) {
			tup = build_relay_sets(name, 1);
			u_rs = (Tuple) tup[2];
			if (tup_size(u_rs) != 0) {
				compiler_error (
				  strjoin("Relay set at level 1 in ", formatted_name(name)));
			}
		}
	ENDFORTUP(ft1);

	main_code_segment();
	/* Update library */

	/* OWNED_SLOTS(unit_name)(2) with= CURRENT_CODE_SEGMENT; */
	u_slots[SLOTS_CODE] = (char *)tup_with((Tuple) u_slots[SLOTS_CODE],
	  (char *)CURRENT_CODE_SEGMENT);

#ifdef TBSL
	LIB_UNIT (unit_name) = [NODE_COUNT, '' , AXQfile]
	   + OWNED_SLOTS(unit_name);
	PRE_COMP (unit_name) = idle_precedes;
	COMP_DATE(unit_name) = {
[name, COMP_DATE(name)(name)] :
		name in idle_precedes * compiled_units		};
	today = DATE;
	COMP_DATE(unit_name)(unit_name) =
	    [today(9..17), today(20..27), #aisread_tup(1)];
#endif

	/* DATA_SEGMENT_MAP(CURRENT_DATA_SEGMENT) = DATA_SEGMENT; */
	DATA_SEGMENT_MAP = 
	  segment_map_put(DATA_SEGMENT_MAP, CURRENT_DATA_SEGMENT, DATA_SEGMENT);

	compilation_table = tup_with(compilation_table, (char *)unit_number_now);
	pUnit = pUnits[unit_number_now];
	pUnit->aisInfo.numberSymbols = seq_symbol_n;
	pUnit->aisInfo.symbols = (char *) tup_new(seq_symbol_n);
#ifdef MACHINE_CODE
	if (list_code) print_data_segment();
#endif
	return TRUE;
}

static void update_elaborate(char *name)				/*;update_elaborate*/
{
	Set	  precedes;
	Tuple  pragma_tup;
	char	  *unam;
	int	  unit, name_num;
	Fortup ft1;

	name_num = unit_numbered(name);
	pragma_tup = (Tuple) pUnits[name_num]->aisInfo.pragmaElab;
	precedes = (Set) precedes_map_get(name);
	FORTUP(unam = (char *), pragma_tup, ft1);
		unit = unit_numbered(unam);
		/* if the pragma names a unit which is not explicitly present (unit is 0
		 * or the body may be obsolete) ignore it
		 */
		if (unit != 0) {
			if (streq(pUnits[unit]->libInfo.obsolete, "ok"))
				precedes = set_with(precedes, (char *) unit);
		}
	ENDFORTUP(ft1);
	precedes_map_put(name, precedes);
}

static void main_code_segment()						/*;main_code_segment */
{
	Node  call_node;
	Symbol      loop_name;
	Segment	task_id;
	Symbol 	handler1, handler2, handler3;
	Fortup	ft1;

	/* check that symbol_main_task_type defined */
	if (symbol_main_task_type == (Symbol)0)
		chaos("glib.c main_code_segment  symbol_main_task_type not defined");

	CODE_SEGMENT = segment_new(SEGMENT_KIND_CODE, 0);
	gen_c(I_NOP, "no handling; go to task trap");
	gen(I_NOP);
	gen_ic(I_TERMINATE, 6, "task trap in case of dead-lock");

	symbol_main_task = sym_new(na_obj);
	ORIG_NAME(symbol_main_task) = strjoin("main_task", "");
	new_symbol(symbol_main_task, na_obj, symbol_main_task_type, (Tuple)0,
	  (Symbol)0);
	task_id = segment_new(SEGMENT_KIND_DATA, 1);
	segment_put_word(task_id, 0);
	next_global_reference_segment(symbol_main_task, task_id);
	gen(I_ENTER_BLOCK);
	gen_s(I_CREATE_TASK, symbol_main_task_type);
	gen_ks(I_POP, kind_of(symbol_main_task_type), symbol_main_task);
	gen(I_ACTIVATE);
	loop_name = new_unique_name("endless_loop");
	gen_s(I_LABEL, loop_name);
	gen_s(I_JUMP, loop_name);
	gen(I_EXIT_BLOCK);
	gen(I_END);		 /* flush peep-hole buffer */

	/*CODE_SEGMENT_MAP(CURRENT_CODE_SEGMENT) = CODE_SEGMENT;*/
	CODE_SEGMENT_MAP = segment_map_put(CODE_SEGMENT_MAP, CURRENT_CODE_SEGMENT,
	  CODE_SEGMENT);

	CURRENT_CODE_SEGMENT = MAIN_CS;
#ifdef MACHINE_CODE
	if (list_code) {
		to_gen(" ");
		to_gen(" ");
		to_gen("--- Main task ---");
		to_gen_int("	   code slot # ", CURRENT_CODE_SEGMENT);
		to_gen(" ");
	}
#endif
	CODE_SEGMENT = segment_new(SEGMENT_KIND_CODE, 0);
	gen(I_LEAVE_BLOCK);
	gen(I_RAISE);
	gen_ic(I_TERMINATE, 5, "never used");
	gen(I_ENTER_BLOCK);
	gen_ic(I_END_ACTIVATION, 1, "Ok");
	handler1 = new_unique_name("handler");
	gen_s(I_INSTALL_HANDLER, handler1);
	gen(I_ENTER_BLOCK);
	FORTUP(call_node = (Node), call_lib_unit, ft1);
		if (N_KIND(call_node) == as_activate_spec) {
			gen_ks(I_PUSH, mu_word, N_UNQ(N_AST1(call_node)));
			gen(I_LINK_TASKS_DECLARED);
			gen(I_ACTIVATE);
		}
		else {
			gen_s(I_CALL, N_UNQ(N_AST1(call_node)));
		}
	ENDFORTUP(ft1);
	handler2 = new_unique_name("handler");
	gen_s(I_INSTALL_HANDLER, handler2);
	gen_s(I_CALL, mainunit_sym);
	gen(I_EXIT_BLOCK);
	handler3 = new_unique_name("end_handler");
	gen_s(I_JUMP, handler3);
	gen_s(I_LABEL, handler2);
	gen_ic(I_TERMINATE, 4, "unhandled exception in main");
	gen_s(I_LABEL, handler3);
	gen(I_EXIT_BLOCK);
	handler3 = new_unique_name("end_handler");
	gen_s(I_JUMP, handler3);
	gen_s(I_LABEL, handler1);
	gen_ic(I_TERMINATE, 3, "exception in library unit elaboration");
	gen_s(I_LABEL, handler3);
	gen_ic(I_TERMINATE, 5, "library tasks are completed");
	gen_ic(I_DATA, 0, "size of local objects");
	gen(I_END);		 /* flush peep-hole buffer */

	/*CODE_SEGMENT_MAP(CURRENT_CODE_SEGMENT) = CODE_SEGMENT;*/
	CODE_SEGMENT_MAP = segment_map_put(CODE_SEGMENT_MAP, CURRENT_CODE_SEGMENT,
	  CODE_SEGMENT);
}

static Tuple delayed_map_get(int unum)					/*;delayed_map_get*/
{
	int		i, n;

	n = tup_size(DELAYED_MAP);
	for (i = 1; i <= n; i += 2) {
		if (DELAYED_MAP[i] == (char *)unum)
			return (Tuple) DELAYED_MAP[i+1];
	}
	return (Tuple)0;
}

static int needs_body_bnd(char *name)							/*;needs_body */
{
	Unitdecl ud;
	Tuple   tup;
	Symbol  unit_unam;

	ud = unit_decl_get(name);
	/* A spec which is obsolete needs no body */
	if (ud == (Unitdecl)0) return FALSE;
	unit_unam = ud->ud_unam;
	tup = (Tuple) MISC(unit_unam);
	return ((int)tup[2] != 0);
}

static void delayed_map_put(int unum, Tuple ntup)			/*;delayed_map_put*/
{
	int		i, n;

	n = tup_size(DELAYED_MAP);
	for (i = 1; i <= n; i += 2) {
		if (DELAYED_MAP[i] == (char *) unum) {
			DELAYED_MAP[i+1] = (char *) ntup;
			return;
		}
	}
	DELAYED_MAP = tup_exp(DELAYED_MAP, n + 2);
	DELAYED_MAP[n+1] = (char *) unum;
	DELAYED_MAP[n+2] = (char *) ntup;
}

static void delayed_map_undef(int unum)					/*;delayed_map_undef*/
{
	int	i, n;

	n = tup_size(DELAYED_MAP);
	for (i = 1; i <= n; i += 2) {
		if (DELAYED_MAP[i] == (char *) unum) {
			DELAYED_MAP[i] = DELAYED_MAP[n-1];
			DELAYED_MAP[i+1] = DELAYED_MAP[n];
			DELAYED_MAP[0] = (char *) (n-2);
			return;
		}
	}
}

static void add_code(char *name)								/*;add_code*/
{
	/*
	 * Adds to call_lib_unit the calls required to elaborate packages.
	 * Library subprograms never need elaboration.
	 * Subunits are elaborated in the parent unit at the location of the
	 * correponding stub.
	 */

	Unitdecl	ud;
	Symbol	unit_unam;
	Node		act_node;
	char		*unit_kind, *body;
	int			has_body, i;
	/* Late generic instantiations : TBSL */

	unit_kind = unit_name_type(name);
	/* elaboration only needed for packages */
	if (!streq(unit_kind, "sp") && !streq(unit_kind, "bo")) return;

	ud = unit_decl_get(name);
	unit_unam = ud->ud_unam;

	if (streq(unit_kind, "sp")) {
		call_lib_unit = tup_with(call_lib_unit, (char *) new_call_node(
		  assoc_symbol_get(unit_unam, INIT_SPEC), tup_new(0), symbol_none));
		body = strjoin("bo", unit_name_name(name));
		has_body = FALSE;
		for (i = 1; i <= unit_numbers; i++)
			if (streq(body, pUnits[i]->name)) {
				has_body = TRUE;
				break;
			}
		if (lib_package_with_tasks(unit_unam)	/* spec declares tasks */
		  && !has_body) {		/* but has no body */
			act_node = new_node(as_activate_spec);
			N_AST1(act_node) = new_name_node(assoc_symbol_get(unit_unam,
			  INIT_TASKS));
			call_lib_unit = tup_with(call_lib_unit, (char *) act_node);
		}
	}
	else if (streq(unit_kind, "bo")) {
		call_lib_unit = tup_with(call_lib_unit, (char *) new_call_node(
		  assoc_symbol_get(unit_unam, INIT_BODY), tup_new(0), symbol_none));
	}
}

static int depth_level(char *stub_name)						/*;depth_level*/
{
	/* calculate the current nesting depth of the subunit by trailing down its
	 * parent chain until its ancestor os reached.
	 */

	int		level, parent;
	char	*s_name;

	level = 1;
	s_name = stub_name;
	while (1) {
		parent = stub_parent_get(s_name);
		if (parent != 0) {
			s_name = pUnits[parent]->name;
			level++;
		}
		else {
			break;
		}
	}
	return level;
}

static Tuple build_relay_sets(char *unit, int depth)	/*;build_relay_sets*/
{
	/*
	 * This procedure computes the relay sets for the subunits of unit.
	 * Yield the relay tables of all (direct or indirect) subunits of unit.
	 * Depth is the level of imbrication ofsubunits (1 if unit is not a
	 * subunit).
	 * u_xxx stands for unit xxx
	 * s_xxx stands for subunit xxx
	 * sl	 stands for (relay) slot
	 * rs	 stands for relay set
	 */

	Tuple	save_relay_set, save_local_reference_map;
	Tuple	s_rs, u_rs, stubs_tup, s_table, return_tup;
	Tuple	stubtup, tup;
	Stubenv	ev;
	struct unit *pUnit;
	int		u_sl, s_sl, offset, seg_num, si;
	Symbol	name;
	Fortup	ft1, ft2;
	char		*s_name;

	/******
   save_local_reference_map = LOCAL_REFERENCE_MAP;
   save_relay_set	    = RELAY_SET;

   [-,-,-,-,-,-,[u_sl,LOCAL_REFERENCE_MAP]] = LIB_UNIT(unit);
   if (is_subunit(unit)) {
		[-,-,-,-,-,-,-,RELAY_SET,DANGLING_RELAY_SETS] = STUB_ENV(unit);
		DATA_SEGMENT += DANGLING_RELAY_SETS;
   }
   else {
		RELAY_SET = [];
   }
	********/

	save_local_reference_map = tup_copy(LOCAL_REFERENCE_MAP);
	save_relay_set	    = tup_copy(RELAY_SET);

	pUnit = pUnits[unit_numbered(unit)];
	u_sl = (int)pUnit->libInfo.currCodeSeg;
	LOCAL_REFERENCE_MAP = tup_copy((Tuple) pUnit->libInfo.localRefMap);

	if (is_subunit(unit) && !is_generic(unit)) {
		si = stub_numbered(unit);
		stubtup = (Tuple) stub_info[si];
		ev = (Stubenv) stubtup[2];
		RELAY_SET = tup_copy(ev->ev_relay_set);
		DANGLING_RELAY_SETS = tup_copy(ev->ev_dangling_relay_set);
		FORTUP(seg_num = (int), DANGLING_RELAY_SETS, ft1);
		segment_put_int(DATA_SEGMENT, seg_num);
		ENDFORTUP(ft1);
	}
	else {
		RELAY_SET = tup_new(0);
	}
	/******
   loop forall s_name in stubs(unit) | #s_name = depth+2 do
	[s_sl, s_rs]   = build_relay_sets(s_name, depth+1);
	s_table	    = [reference_of(name)(2): name in s_rs];
	DATA_SEGMENT += [s_sl, #s_table] + s_table;
   end loop;
	*****/

	stubs_tup = stubs(unit);
	FORTUP(s_name = (char *), stubs_tup, ft1);
		if (depth_level(s_name) != depth+1) continue;
		tup = build_relay_sets(s_name, depth+1);
		s_sl = (int) tup[1];
		s_rs = (Tuple) tup[2];
		s_table = tup_new(0);
		FORTUP(name = (Symbol), s_rs, ft2);
			reference_of(name);
			s_table = tup_with(s_table, (char *) REFERENCE_OFFSET);
		ENDFORTUP(ft2);
		segment_put_int(DATA_SEGMENT, s_sl);
		segment_put_int(DATA_SEGMENT, tup_size(s_table));
		FORTUP(offset = (int), s_table, ft2);
			segment_put_int(DATA_SEGMENT, offset);
		ENDFORTUP(ft2);
	ENDFORTUP(ft1);
	/******
   u_rs		       = RELAY_SET;
   RELAY_SET	       = save_relay_set;
   LOCAL_REFERENCE_MAP = save_local_reference_map;
   return [u_sl, u_rs];
	*****/
	u_rs 		= tup_copy(RELAY_SET);
	RELAY_SET 		= save_relay_set;
	LOCAL_REFERENCE_MAP 	= save_local_reference_map;
	return_tup = tup_new(2);
	return_tup[1] = (char *) u_sl;
	return_tup[2] = (char *) u_rs;
	return return_tup;
}

static void update_subunit_context(char *subunit)	/*;update_subunit_context*/
{
	Set		stub_context, precedes;
	char		*ancestor_body;
	int		ancestor_num, unum, subunit_num;
	Forset	fs1;
	int		has_ancestor, i;

	/* Add the library units mentioned in the context clause for the subunit
	 * to the precedes map for the ancestor unit of the stub since all the units
	 * in the context clause need to be elaborated before the ancestor.
	 */

	subunit_num = unit_numbered(subunit);
	stub_context = precedes_map_get(subunit);
	/* if the unit has not been loaded return */
	if (stub_context == (Set)0) return;
	ancestor_body = strjoin("bo", stub_ancestor(subunit));
	/* determine if the ancestor unit is package or subprogram */
	has_ancestor = FALSE;
	for (i = 1; i <= unit_numbers; i++)
		if (streq(ancestor_body, pUnits[i]->libUnit)) {
			has_ancestor = TRUE;
			break;
		}
	if (!has_ancestor)
		ancestor_body = strjoin("su", stub_ancestor(subunit));
	ancestor_num = unit_numbered(ancestor_body);
	precedes = precedes_map_get(ancestor_body);
	FORSET(unum = (int), stub_context, fs1);
		/* add in units that were in context clause of subunit so exclude
		 * subunits which happen to be in the PRE_COMP field of this subunit.
		 */
		if (!is_subunit(pUnits[unum]->name) && unum != ancestor_num)
			precedes = set_with(precedes, (char *)unum);
	ENDFORSET(fs1);
	precedes_map_put(ancestor_body, precedes);
}

static int load_binding_unit(char *unit)				/*;load_binding_unit*/
{
	char	*fname;
	int		file_retrieved;
	Unitdecl	ud;
	/* When binding is done load the necessary units if they are not loaded 
	 * already. However, when a unit is to be loaded use read_binding_ais so 
	 * that only the absolute necessary components of the ais are read.
	 */
	fname = lib_unit_get(unit);
	if (fname == (char *)0) {
		user_error(strjoin(formatted_name(unit), " not present in library"));
		return FALSE;
	}
	else if (in_aisunits_read(unit)) {
		file_retrieved = TRUE;
	}
	else {
		file_retrieved = (read_binding_ais(fname, unit) != (char *)0);
		if (is_subunit(unit)) read_stub(lib_unit_get(unit), unit, "st2");
	}

	if (file_retrieved && (ud = unit_decl_get(unit)) != (Unitdecl)0) {
		return TRUE;
	}
	else {
		user_error(strjoin("Cannot retrieve unit ", formatted_name(unit)));
		user_info(strjoin(" from file ", fname));
		return FALSE;
	}
}

static char *read_binding_ais(char *fname, char *uname)  /*;read_binding_ais*/
{
	long	rec, genoff;
	int		fnum, unum, n, nodes, symbols, i, is_main_unit;
	Tuple	symptr, tup;
	struct unit *pUnit;
	char	*funame, *retrieved ;
	Unitdecl	ud;
	IFILE	*ifile;
	Symbol	sym;
	char 	*lname, *tname;
	int		is_predef; /* set when reading predef file */

	/* This is a modified version of read_ais, which reads only the neccesary
	 * items needed for binding. All other information is skipped.
	 */

	retrieved = (char *)0;
	is_predef = streq(fname, "0");
	if (is_predef) {
		fname = "predef" ;
		lname= libset(PREDEFNAME);/* use predefined library */
	}
	ifile = ifopen(fname, "axq", "r", 0);
	if (is_predef) {
		tname= libset(lname); /* restore library name */
	}
	for (rec = read_init(ifile); rec != 0; rec = read_next(ifile, rec)) {
		funame = getstr(ifile, "unit-name");
		if (uname != (char *)0  && streq(uname, funame) == 0) continue;
		fnum = getnum(ifile, "unit-number");
		unum = unit_number(funame);
		if (unum != fnum)
			chaos("read_ais sequence number error");
		genoff = getlong(ifile, "code-gen-offset");
		is_main_unit = streq(unit_name_type(funame), "ma");
		if (!is_main_unit) { /* read only if NOT main unit (it has no ais info*/
			symbols = getnum(ifile, "seq-symbol-n");
			nodes = getnum(ifile, "seq-node-n");
			pUnit = pUnits[unum];
			symptr = (Tuple)pUnit->aisInfo.symbols;
			if (symptr == (Tuple)0) { /* if tuple not yet allocated */
				symptr = tup_new(symbols);
				pUnit->aisInfo.symbols = (char *) symptr;
			}

			/* ELABORATE PRAGMA INFO */
			n = getnum(ifile, "pragma-info-size");
			tup = tup_new(n);
			for (i = 1; i <= n; i++) {
				tup[i] = getstr(ifile, "pragma-info-value");
			}
			pUnit->aisInfo.pragmaElab = (char *)tup;
			/* UNIT_DECL */
			ud = unit_decl_new();
			pUnit->aisInfo.unitDecl = (char *)ud;
			sym = getsym(ifile, "ud-unam");
			ud->ud_unam = sym;
			ud->ud_useq = S_SEQ(sym);
			ud->ud_unit = S_UNIT(sym);
			get_unit_unam(ifile, sym);
			aisunits_read = tup_with(aisunits_read, funame);
		}
		retrieved = funame;
		break;
	}
	ifclose(ifile);
	return retrieved;
}
