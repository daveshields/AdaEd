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
#include "slot.h"
#include "ifile.h"
#include "axqrprots.h"
#include "axqwprots.h"
#include "libwprots.h"
#include "gutilprots.h"
#include "gmiscprots.h"
#include "gmainprots.h"
#include "libfprots.h"
#include "librprots.h"
#include "setprots.h"
#include "libprots.h"
#include "miscprots.h"
#include "readprots.h"

static void get_local_ref_maps(IFILE *, int);
static void put_local_ref_maps(IFILE *, int);
static void relocate_slots_a();
static void relocate_slots_b();
static void overwrite_stub_name(char *);

extern Segment	CODE_SEGMENT, DATA_SEGMENT, DATA_SEGMENT_MAIN;
extern IFILE *AXQFILE, *LIBFILE, *AISFILE, *STUBFILE;

static Tuple code_slots_syms, data_slots_syms;

/* Input/Output of compiler files */

int load_unit(char *unit, int tree_is_needed)					/*;load_unit*/
{
	/*
	 * Retrieves the symbol table of the given unit and puts its information
	 * into the compilation maps.
	 * An AXQ may be read from the library if the unit has not yet been
	 * loaded. If the file cannot be opened, or the unit is not found, an
	 * error message is printed.
	 * BEWARE: the loaded AXQ may contain an unit with the same name as the
	 * current one, that must not be loaded, as its symbol table would
	 * override the current one.
	 */

	char	*fname;
	int		file_retrieved;
	Symbol	unit_unam;
	Tuple	decmaps, decscopes, s_info;
	Unitdecl	ud;

	fname = lib_unit_get(unit);
#ifdef TRACE
	if (debug_flag) gen_trace(strjoin("load_unit ", unit));
#endif
	if (fname == (char *)0) {
		user_error(strjoin(formatted_name(unit), " not present in library"));
		return FALSE;
	}
	else if (in_aisunits_read(unit)) {
		file_retrieved = TRUE;
	}
	else {
		file_retrieved = 
		  (read_ais(fname, FALSE, unit, 0, tree_is_needed) != (char *)0);

		if (is_subunit(unit)) read_stub(lib_unit_get(unit), unit, "st2");
#ifdef TBSL
		if (is_subunit(unit)) {
			/* If the subunit  has been  compiled, its  stub environment 
   			 * overrides the one appearing in the axq of the parent unit.
			 */
			(for [n, env] in axqt) STUB_ENV(n) : = env; 
			end ;
		}
		else {
			STUB_ENV +: = axqt;
		}
#endif
	}

	if (file_retrieved && (ud = unit_decl_get(unit)) != (Unitdecl)0) {
		/* [unit_unam, s_info, decls] = UNIT_DECL(unit); */
		unit_unam = ud->ud_unam;
		s_info = ud->ud_symbols;
		decscopes = ud->ud_decscopes;
		decmaps = ud->ud_decmaps;
		/* TBSL does the info from decscopes and decmaps need to be restored 
		 * or is the info restored by symtab_restore since declared info is 
		 * stored with the symbols.
		 * DECLARED  += decls; 
		 * SYMBTABQ restore 
		 */
		symtab_restore(s_info);
		return TRUE;
	}
	else {
		user_error(strjoin("Cannot retrieve unit ", formatted_name(unit)));
		user_info(strjoin(" from file ", fname));
		return FALSE;
	}
}


void load_library(Axq axq)									/*;load_library*/
{
	/*
	 * retrieve information from LIBFILE
	 * Called only not newlib.
	 */

	int		comp_status, si, i, j, n, m, unumber, nodes, symbols, cur_level;
	int		parent, unit_count;
	Tuple	stubtup, tup;
	char	*parent_name, *uname, *aisname, *tmp_str, *compdate;
	Set		precedes;
	int		n_code_slots, n_data_slots, n_exception_slots;
	long	cde_pos; /* offset for start of slot info */
	IFILE	*ifile;

	ifile = LIBFILE;
	/* library already opened */
	unit_count = getnum(ifile, "lib-unit-count");
	n = getnum(ifile, "lib-n");
	empty_unit_slots = getnum(ifile, "lib-empty-slots");
	tmp_str = getstr(ifile, "lib-tmp-str");
	unit_number_expand(n);
	for (i = 1; i <= unit_count; i++) {
		struct unit *pUnit;
		uname = getstr(ifile, "lib-unit-name");
		unumber = getnum(ifile, "lib-unit-number");
		aisname = getstr(ifile, "lib-ais-name");
		compdate = getstr(ifile, "comp-date");
		symbols = getnum(ifile, "lib-symbols");
		nodes = getnum(ifile, "lib-nodes");
		pUnit = pUnits[unumber];
		pUnit->name = strjoin(uname, "");
		pUnit->isMain = getnum(ifile, "lib-is-main");
		pUnit->libInfo.fname = strjoin(aisname, "");
		pUnit->libInfo.compDate = compdate;
		comp_status = getnum(ifile, "lib-status");
		pUnit->libInfo.obsolete = (comp_status) ? "ok" : "$D$";
		pUnit->libUnit = (comp_status) ? strjoin(uname, "") : "$D$";
		pUnit->aisInfo.numberSymbols = symbols;
		pUnit->treInfo.nodeCount = nodes;
		pUnit->treInfo.tableAllocated = (char *) tup_new(0);
	}
	n = getnum(ifile, "lib-n");
	for (i = 1; i <= n; i++) {
		uname = getstr(ifile, "lib-unit-name");
		aisname = getstr(ifile, "lib-ais-name");
		lib_stub_put(uname, aisname);
		parent = getnum(ifile, "lib-parent");
		if (parent == 0) parent_name = " ";
		else parent_name = pUnits[parent]->name;
		stub_parent_put(uname, parent_name);
		cur_level = getnum(ifile, "lib-cur-level");
		current_level_put(uname, cur_level);
		si = stub_numbered(uname);
		stubtup = (Tuple) stub_info[si];
		m = getnum(ifile, "stub-file-size");
		tup = tup_new(m);
		for (j = 1; j <= m; j++)
			tup[j] = (char *) getnum(ifile, "stub-files");
		stubtup[4] = (char *) tup;
	}
	n = getnum(ifile, "precedes-map-size");
	PRECEDES_MAP = tup_new(n);
	for (i = 1; i <= n; i += 2) {
		PRECEDES_MAP[i] = (char *) getnum(ifile, "precedes-map-ent");
		m = getnum(ifile, "precedes-map-set-size");
		precedes = set_new(m);
		for (j = 1; j <= m; j++) {
			precedes = set_with(precedes,
			  (char *) getnum(ifile, "precedes-map-ent"));
		}
		PRECEDES_MAP[i+1] = (char *) precedes;
	}
	n = getnum(ifile, "compilation_table_size");
	compilation_table = tup_new(n);
	for (i = 1; i <= n; i++)
		compilation_table[i] = (char *) getnum(ifile, "compilation-table-ent");
	/* late_instances */
	n = getnum(ifile, "late-instances-size");
	late_instances = tup_new(n);
	for (i = 1; i <= n; i++)
		late_instances[i] = getstr(ifile, "late-instances-str");
	n = getnum(ifile, "interfaced-procedures-size");
	interfaced_procedures = tup_new(n);
	for (i = 1; i <= n; i += 2) {
		interfaced_procedures[i] =
		  (char *) getnum(ifile, "interfaced-procedures-num");
		interfaced_procedures[i+1]= getstr(ifile, "interfaced-procedures-str");
	}
	interface_counter = getnum(ifile, "interface-counter");
	n = getnum(ifile, "units-size");
	for (i = 1; i <= n; i++) {
		pUnits[i]->libInfo.currCodeSeg =
		  (char *) getnum(ifile, "current-code-seg");
	}
	n = getnum(ifile, "units-size");
	/* read local_reference_map for each unit (tuple of symbols and offsets) */
	get_local_ref_maps(LIBFILE, n);
	cde_pos = get_cde_slots(LIBFILE, axq);
	/* Now set CODE_SLOTS, DATA_SLOTS and EXCEPTION_SLOTS from axq */
	n_code_slots = axq->axq_code_slots_dim -1;
	n_data_slots = axq->axq_data_slots_dim - 1;
	n_exception_slots = axq->axq_exception_slots_dim - 1;
	CODE_SLOTS = tup_new(n_code_slots);
	for (i = 1; i <= n_code_slots; i++) {
		CODE_SLOTS[i] = (char *) axq->axq_code_slots[i];
	}
	DATA_SLOTS = tup_new(n_data_slots);
	for (i = 1; i <= n_data_slots; i++) {
		DATA_SLOTS[i] = (char *) axq->axq_data_slots[i];
	}
	EXCEPTION_SLOTS = tup_new(n_exception_slots);
	for (i = 1; i <= n_exception_slots; i++) {
		EXCEPTION_SLOTS[i] = (char *) axq->axq_exception_slots[i];
	}
	/* could free axq_data_slots, etc., but keep for now */
	/* read out LIB_STUB map (always empty for now) */
	ifclose(LIBFILE);
	return;
}

void store_axq(IFILE *file, int unit_num)						/*;store_axq*/
{
	/* Writes the AXQ file of compiled units (symmetrical to LOAD_AIS) */

	int		si, i, n, symbols, slots_ind, nsegs;
	long	begpos;
	Tuple	u_slots, symtup, tup;
	Symbol	sym;
	Segment	seg;
	Fortup	ft1;
	Forset	fs1;
	char	*uname;
	Stubenv	ev;
	IFILE	*ofile;

#ifdef TRACE
	if (debug_flag) gen_trace_string("STORE_AXQ: ", pUnits[unit_num]->name);
#endif

	/* In order to make the sequence of symbols written out dense (consecutive)
	 * without holes, the new symbols which are needed externally, namely 
	 * GENERATED_OBJECTS have their seq numbers renumbed before being written
	 * out. This new ordering begins right after the sequence number of the last
	 * symbol read in from the semantic phase.
	 */
	pUnits[unit_num]->libInfo.compDate = (char *)greentime(0);
	n = (GENERATED_OBJECTS == (Tuple)0) ? 0 : tup_size(GENERATED_OBJECTS);
	symbols = pUnits[unit_num]->aisInfo.numberSymbols;
	relocate_slots_a();
	for (i = 1; i <= n; i++) {
		sym = (Symbol) GENERATED_OBJECTS[i];
		S_SEQ(sym) = symbols + i;
		seq_symbol[symbols + i] = (char *) sym;
	}
	seq_symbol_n = symbols + n;
	relocate_slots_b();
	AISFILE = AXQFILE;
	begpos = write_ais(unit_num);
	ofile = AXQFILE;

	if (n > 0) {
		symtup = (Tuple)pUnits[unit_num]->aisInfo.symbols;
		symtup = tup_exp(symtup, symbols + n);
		for (i = 1; i <= n; i++) 
			symtup[i+symbols] = (char *) GENERATED_OBJECTS[i];
		pUnits[unit_num]->aisInfo.symbols = (char *) symtup;
	}


	u_slots = unit_slots_get(unit_num);
	/* put out data slots info */
	for (slots_ind = 1; slots_ind <= 4; slots_ind += 3) {
		tup = (Tuple) u_slots[slots_ind];
		nsegs  = 0; /* first count number of defined segments */
		FORTUP(i = (int), tup , ft1)
		    seg = segment_map_get(DATA_SEGMENT_MAP, i);
			if (seg != (Segment)0)
				nsegs++;
		ENDFORTUP(ft1);
		putnum(ofile, "number-segments", nsegs);
		FORTUP(i = (int), tup , ft1)
		    seg = segment_map_get(DATA_SEGMENT_MAP, i);
			if (seg != (Segment)0) {
				putnum(ofile, "segment-number", i);
				segment_write(AXQFILE, seg);
			}
		ENDFORTUP(ft1);
	}
	/* put out code slots info */
	for (slots_ind = 2; slots_ind <= 5; slots_ind += 3) {
		nsegs = 0;
		FORTUP(i = (int), (Tuple) u_slots[slots_ind], ft1)
		    seg = segment_map_get(CODE_SEGMENT_MAP, i);
			if (seg != (Segment)0)
				nsegs++;
		ENDFORTUP(ft1);
		putnum(ofile, "number-segments", nsegs);
		FORTUP(i = (int), (Tuple) u_slots[slots_ind], ft1)
		    seg = segment_map_get(CODE_SEGMENT_MAP, i);
			if (seg != (Segment)0) {
				putnum(ofile, "slot-number", i);
				segment_write(AXQFILE, seg);
			}
		ENDFORTUP(ft1);
	}

	write_end(ofile, begpos);
	uname = pUnits[unit_num]->name;
	if (is_subunit(uname) &&!is_generic(uname)) {
		si = stub_numbered(uname);
		tup = (Tuple) stub_info[si];
		ev = (Stubenv)tup[2];
		update_stub(ev);
		if (streq(lib_stub_get(uname), AISFILENAME)) overwrite_stub_name(uname);
		write_stub(ev, uname, "st2");
		/* lib_stub_put(uname, AISFILENAME); */
	}
	FORSET(si = (int), stubs_to_write, fs1);
		tup = (Tuple)stub_info[si];
		ev = (Stubenv)tup[2];
		write_stub(ev, lib_stub[si], "st2");
	ENDFORSET(fs1);
	stubs_to_write = set_new(0);
}

static void get_local_ref_maps(IFILE *ifile, int units)	/*;get_local_ref_map*/
{
	int		unit, defined, i, off, n;
	Symbol	sym;
	Tuple	local_ref_map;

	for (unit = 1; unit <= units; unit++) {
		/* ignore empty ref maps (predef units) and obselete units */
		defined = getnum(ifile, "local-ref-map-defined");
		if (!defined) continue;
		n = getnum(ifile, "local-ref-map-size");
		local_ref_map = tup_new(n);
		pUnits[unit]->libInfo.localRefMap = (char *) local_ref_map;
		for (i = 1; i <= n; i += 2) {
			sym = getsymref(ifile, "local-ref-map-sym");
			local_ref_map[i] = (char *) sym;
			off = getnum(ifile, "local-ref-map-off");
			local_ref_map[i+1] = (char *) off;
		}
	}
}

static void put_local_ref_maps(IFILE *ofile, int units)	/*;put_local_ref_map*/
{
	int		unit, i, off, n, symbols;
	Symbol	sym;
	Tuple	local_ref_map;

	for (unit = 1; unit <= units; unit++) {
		struct unit *pUnit = pUnits[unit];
		local_ref_map = (Tuple) pUnit->libInfo.localRefMap;
		n = tup_size(local_ref_map);
		/* ignore empty ref maps (predef units) and obselete units */
		if (streq(pUnit->libInfo.obsolete, "ok") && n != 0) {
			putnum(ofile, "local-ref-map-defined", 1);
		}
		else {
			putnum(ofile, "local-ref-map-defined", 0);
			continue;
		}
		symbols = pUnit->aisInfo.numberSymbols;
		putnum(ofile, "local-ref-map-size", n);
		for (i = 1; i <= n; i += 2) {
			/* if the sequence num of the symbol is greater than the number of
       		 * symbols it is a case of a generated symbol which is not in
			 * generated objects. Ignore for now.
			 */
			sym = (Symbol) local_ref_map[i];
			if (sym == (Symbol)0 || (S_UNIT(sym)==unit && S_SEQ(sym) >symbols)){
				putnum(ofile, "ignore", 0);
				putnum(ofile, "ignore", 0);
				putnum(ofile, "ignore", 0);
				continue;
			}
			off = (int) local_ref_map[i+1];
			putsymref(ofile, "local-ref-map-sym", sym);
			putnum(ofile, "local-ref-map-off", off);
		}
	}
}

void write_glib()											/*;write_glib*/
{
	int		i, j, n, m, nodes, symbols;
	int		unit_count = 0;
	Tuple	stubtup, tup;
	Set		precedes;
	Forset	fs1;
	IFILE	*ofile;
	extern	char *lib_name;
	char	*t_name, *l_name;

	n  = unit_numbers; /* number of units */
	l_name = libset(lib_name);
	ofile = ifopen(LIBFILENAME, "", "w", 0);
	t_name = libset(l_name);
	LIBFILE = ofile;
	for (i = 1; i <= n; i++) {
		if (!streq(pUnits[i]->libInfo.fname, "0") || compiling_predef)
			unit_count++;
	}
	putnum(ofile, "lib-unit-count", unit_count);
	putnum(ofile, "lib-n", n);
	putnum(ofile, "lib-empty-unit-slots", empty_unit_slots);
	putstr(ofile, "lib-aisname", AISFILENAME);
	for (i = 1; i <= n; i++) {
		struct unit *pUnit =  pUnits[i];
		if (compiling_predef) { /* trace for predef build */
			nodes = pUnit->treInfo.nodeCount;
			symbols = pUnit->aisInfo.numberSymbols;
                        /* The first 14 units are predefined by the language */
			if (i <= 14) {
				if (!streq(pUnit->name, predef_unit_name(i))) {
					chaos("predef unit name error");
				}
			}
		}
		if (streq(pUnit->libInfo.fname, "0") && !compiling_predef) continue;
		putstr(ofile, "unit-name", pUnit->name);
		putnum(ofile, "unit-number", i);
		putstr(ofile, "libtup-1", pUnit->libInfo.fname);
		putstr(ofile, "unit-date", pUnit->libInfo.compDate);
		if (streq(pUnit->libInfo.obsolete, "$D$")) {
			putnum(ofile, "unit-symbols", 0);
			putnum(ofile, "unit-nodes", 0);
			putnum(ofile, "unit-is-main", 0);
			putnum(ofile, "unit-comp-status", 0);
			continue;
		}
		putnum(ofile, "unit-symbols", pUnit->aisInfo.numberSymbols);
		putnum(ofile, "unit-nodes", pUnit->treInfo.nodeCount);
		putnum(ofile, "unit-is-main", pUnit->isMain);
		putnum(ofile, "unit-comp-status", 1);
	}
	/* write out lib_stub info */
	unit_count = 0;
	n = tup_size(lib_stub);
	for (i = 1; i <= n; i++) if (!streq(lib_stub[i], "$D$")) unit_count++;
	putnum(ofile, "stub-unit-count", unit_count);
	for (i = 1; i <= n; i++) {
		if (streq(lib_stub[i], "$D$")) continue;
		stubtup = (Tuple) stub_info[i];
		putstr(ofile, "stub-libstub", lib_stub[i]);
		putstr(ofile, "stub-stubtup", stubtup[1]);
		putnum(ofile, "stub-parent", (int)stubtup[5]);
		putnum(ofile, "stub-cur-level", (int)stubtup[3]);
		tup = (Tuple) stubtup[4];
		m = tup_size(tup);
		putnum(ofile, "stub-file-size", m);
		for (j = 1; j <= m; j++) {
			putnum(ofile, "stub-files", (int)tup[j]);
		}
	}
	n = tup_size(PRECEDES_MAP);
	putnum(ofile, "precedes-map-size", n);
	for (i = 1; i <= n; i += 2) {
		putnum(ofile, "precedes-map-ent", (int)PRECEDES_MAP[i]);
		precedes = (Set) PRECEDES_MAP[i+1];
		m = set_size(precedes);
		putnum(ofile, "precedes-map-set-size", m);
		FORSET(m = (int), precedes, fs1);
			putnum(ofile, "precedes-map-ent", m);
		ENDFORSET(fs1);
	}
	n = tup_size(compilation_table);
	putnum(ofile, "compilation-table-size", n);
	/* print compilation table (tuple of unit names) */
	for (i = 1; i <= n; i++) {
		putnum(ofile, "compilation-table-ent", (int)compilation_table[i]);
	}
	n = tup_size(late_instances);
	putnum(ofile, "late-instances-size", n);
	/* print late_instances (tuple of unit names) */
	for (i = 1; i <= n; i++) {
		putstr(ofile, "late-instances-ent", late_instances[i]);
	}
	n = tup_size(interfaced_procedures);
	putnum(ofile, "interfaced-procedures-size", n);
	for (i = 1; i <= n; i += 2) {
		putnum(ofile, "interfaced-procedures-num",
		  (int) interfaced_procedures[i]);
		putstr(ofile, "interfaced-procedures-str", interfaced_procedures[i+1]);
	}
	putnum(ofile, "interface-counter", interface_counter);
	n = unit_numbers;
	putnum(ofile, "units-size", n);
	for (i = 1; i <= n; i++) {
		putnum(ofile, "current-code-seg", (int) pUnits[i]->libInfo.currCodeSeg);
	}
	putnum(ofile, "unit-size", unit_numbers);
	put_local_ref_maps(LIBFILE, unit_numbers);
	put_cde_slots(LIBFILE, 0);/* write slots info and close file */
	LIBFILE = (IFILE *) 0;
}

static void relocate_slots_a()							/*;relocate_slots_a*/
{
	/* This procedure is the first in the possible relocation of sequence
	 * numbers which appear in the Slot field. 
	 */
	int 	i, n;
	Slot 	slot;

	n = tup_size(CODE_SLOTS);
	code_slots_syms = tup_new(n);
	for (i = 1; i <= n; i++) {
		slot = (Slot) CODE_SLOTS[i];
		if (slot != (Slot)0 && slot->slot_unit == unit_number_now)
			code_slots_syms[i] = (char *) seq_symbol[slot->slot_seq];
	}
	n = tup_size(DATA_SLOTS);
	data_slots_syms = tup_new(n);
	for (i = 1; i <= n; i++) {
		slot = (Slot) DATA_SLOTS[i];
		if (slot != (Slot)0 && slot->slot_unit == unit_number_now)
			data_slots_syms[i] = (char *) seq_symbol[slot->slot_seq];
	}
}

static void relocate_slots_b()							/*;relocate_slots_b*/
{
	int 	i, n;
	Slot 	slot;
	Symbol 	sym;

	n  = tup_size(CODE_SLOTS);
	for (i = 1; i <= n; i++) {
		slot = (Slot) CODE_SLOTS[i];
		if (slot != (Slot)0 && slot->slot_unit == unit_number_now) {
			sym = (Symbol) code_slots_syms[i];
			slot->slot_seq = S_SEQ(sym);
		}
	}
	n = tup_size(DATA_SLOTS);
	for (i = 1; i <= n; i++) {
		slot = (Slot) DATA_SLOTS[i];
		if (slot != (Slot)0 && slot->slot_unit == unit_number_now) {
			sym = (Symbol) data_slots_syms[i];
			slot->slot_seq = S_SEQ(sym);
		}
	}
	tup_free(data_slots_syms);
	tup_free(code_slots_syms);
}

void update_stub(Stubenv ev)								/*;update_stub*/
{
	Tuple   tup;
	Symbol  ev_sym, sym;
	int	   i, n;

	/* update the SEGMENT and OFFSET fields for procedure symbols since the
	 * code generator might have updated their values in a previous unit.
	 * Also update  the associated_symbols fields for procedure and packages.
	 * Note: this is necessary since for procedures a copy of the symbol is
	 * made when the symbol is read into ev_open_decls and therefore some fields
	 * might not have been updated when the global symbol accessed by getsymptr
	 * is updated.
	 * TBSL this might have to be done for packages, and functions.
	 */
	tup = ev->ev_open_decls;
	n = tup_size(tup);
	for (i = 1; i <= n; i++) {
		ev_sym = (Symbol) tup[i];
		if (NATURE(ev_sym) == na_procedure) {
			sym = getsymptr(S_SEQ(ev_sym), S_UNIT(ev_sym));
			S_SEGMENT(ev_sym) = S_SEGMENT(sym);
			S_OFFSET(ev_sym) = S_OFFSET(sym);
		}
		if (NATURE(ev_sym) == na_package || NATURE(ev_sym) == na_procedure) {
			sym = getsymptr(S_SEQ(ev_sym), S_UNIT(ev_sym));
			if (ASSOCIATED_SYMBOLS(sym) != (Tuple)0)
				ASSOCIATED_SYMBOLS(ev_sym) = ASSOCIATED_SYMBOLS(sym);
		}
	}
}

static void overwrite_stub_name(char *uname)			/*;overwrite_stub_name*/
{
	/* If a stub and its proper body are in the same compilation, this 
	 * procedure is called. Normally the code generator write the st2 file
	 * after the unit constaining the stub is processed. If the proper body
	 * then appears later in the compilation, we must go back to where the 
	 * info for the stub was written and change its name so that only the
	 * second appearance (proper body) is recognized.
	 */
	long  str_pos, rec;
	char  *funame;
	IFILE *ifile;

	ifclose(STUBFILE);
	STUBFILE = ifopen(AISFILENAME, "st2", "r+", 0);
	ifile = STUBFILE;
	for (rec = read_init(ifile); rec != 0; rec = read_next(ifile, rec)) {
		str_pos = iftell(ifile);
		funame = getstr(ifile, "stub-name");
		if (!streq(uname, funame)) continue;
		ifseek(ifile, "seek to string", str_pos, 0);
		funame[0] = '$';
		putstr(ifile, "stub-name", funame);
		break;
	}
	ifseek(ifile, "seek to end", 0L, 2);
	ifile->fh_mode = 'w';
}

void overwrite_unit_name(char *uname)				/*;overwrite_unit_name*/
{
	/* If a compilation unit appears more than once in the same compilation,
	 * this procedure is called.  The code for the first occurrence must be
	 * disabled. This is done by going back to where the info for the unit was
	 * written and change its name so that only the second appearance is
	 * recognized.
	 */
	long  str_pos, rec;
	char  *funame;
	IFILE *ifile;

	ifclose(AXQFILE);
	AXQFILE = ifopen(AISFILENAME, "axq", "r+", 0);
	ifile = AXQFILE;
	for (rec = read_init(ifile); rec != 0; rec = read_next(ifile, rec)) {
		str_pos = iftell(ifile);
		funame = getstr(ifile, "unit-name");
		if (!streq(uname, funame)) continue;
		ifseek(ifile, "seek to string", str_pos, 0);
		funame[0] = '$';
		putstr(ifile, "unit-name", funame);
		break;
	}
	ifseek(ifile, "seek to end", 0L, 2);
	ifile->fh_mode = 'w';
}

int read_stub_short(char *fname, char *uname, char *ext)	/*;read_stub_short*/
{
	long	rec;
	Stubenv	ev;
	int		i, j, k, n, m, si;
	char	*funame;
	Tuple	stubtup, tup, tup2, tup3;
	int		ci, cn;
	Tuple	cent, ctup, cntup;
	Symbol	sym;
	int		retrieved = FALSE;
	IFILE	*ifile;

	/* This is a modifed version of read_stub which only reads enough
	 * information from the stubfile so that it can be rewritten. Notably it
	 * reads just the symbol references and not the full symbol definitions.
	 * It is called from gen_stub.
 	 */

	/* open so do not fail if no file */
	ifile = ifopen(fname, ext, "r", 1);
	if (ifile == (IFILE *)0) { /* if not stub file */
		return retrieved;
	}
	for (rec = read_init(ifile); rec != 0; rec = read_next(ifile, rec)) {
		funame = getstr(ifile, "stub-name");
		if (uname != (char *)0  && !streq(uname, funame)) continue;
		si = stub_number(funame);
		if (uname == (char *)0) lib_stub_put(funame, fname);
		ev = stubenv_new();
		stubtup = (Tuple) stub_info[si];
		stubtup[2] = (char *) ev;
		n = getnum(ifile, "scope-stack-size");
		tup = tup_new(n);
		for (i = 1; i <= n; i++) {
			tup2 = tup_new(4);
			tup2[1] = (char *) getsymref(ifile, "scope-stack-symref");
			for (j = 2; j <= 4; j++) {
				m = getnum(ifile, "scope-stack-m");
				tup3 = tup_new(m);
				for (k = 1; k <= m; k++)
					tup3[k] = (char *) getsymref(ifile, "scope-stack-m-symref");

				tup2[j] = (char *) tup3;
			}
			tup[i] = (char *) tup2;
		}
		ev->ev_scope_st = tup;
		ev->ev_unit_unam = getsymref(ifile, "ev-unit-name-symref");
		ev->ev_decmap = getdcl(ifile);

		/* unit_nodes */
		n = getnum(ifile, "ev-nodes-size");
		tup = tup_new(n);
		for (i = 1; i <= n; i++) {
			tup[i] = (char *) getnodref(ifile, "ev-nodes-nodref");
		}
		ev->ev_nodes = tup;

		/* context */
		n = getnum(ifile, "stub-context-size");
		if (n>0) {
			n -= 1; /* true tuple size */
			ctup = tup_new(n);
			for (i = 1; i <= n; i++) {
				cent = (Tuple) tup_new(2);
				cent[1] = (char *) getnum(ifile, "stub-cent-1");
				cn = getnum(ifile, "stub-cent-2-size"); 
				cntup = tup_new(cn);
				for (ci = 1; ci <= cn; ci++) {
					cntup[ci] = getstr(ifile, "stub-cent-2-str");
				}
				cent[2] = (char *) cntup;
				ctup[i] = (char *) cent;
			}
			ev->ev_context =  ctup;
		}
		/* tuple of symbol table pointers */
		n = getnum(ifile, "ev-open-decls-size");
		if (n > 0) {
			n -= 1; /* true tuple size */
			tup = tup_new(n);
			for (i = 1; i <= n; i++) {
				sym = getsymref(ifile, "ev-open-decls-sym");
				tup[i] = (char *) sym;
			}
			ev->ev_open_decls = tup;
		}
		ev->ev_relay_set = tup_new(0);
		ev->ev_dangling_relay_set = tup_new(0);
		retrieved = TRUE;
		if (uname != (char *)0)  break;
	}
	ifclose(ifile);
	return retrieved;
}

void retrieve_generic_body(Symbol sym)				/*;retrieve_generic_body*/
{
	Symbol	scope_of_sym;
	char	*uname, *fname;

	scope_of_sym = SCOPE_OF(sym);
	if (scope_of_sym == symbol_standard0) return;
	while (scope_of_sym != symbol_standard0) {
		sym = scope_of_sym;
		scope_of_sym = SCOPE_OF(sym);
	}
	if (NATURE(sym) == na_package_spec) {
		uname = strjoin("bo", ORIG_NAME(sym));
		fname = lib_unit_get(uname);
		if (fname == (char *)0) { /* body not present in library */
			return;
		}
		/* unit read already or predefined unit which is not necessary to read*/
		else if (in_aisunits_read(uname) || streq(fname, "0")) {
			return;
		}
		/* accessing unit within the same files */
		else if (streq(fname, AISFILENAME)) {
			return;
		}
		read_ais(fname, FALSE, uname, 0, FALSE);
	}
}

void collect_stub_node_units(int si)				/*;collect_stub_node_units*/
{
	/*
	 * Collect the unit numbers which potentially have nodes in them that are
	 * referenced by the open_decls (symbol table) of the .st1 file for the
	 * stub "si". This information will be used to retrieve the tree nodes when
	 * the proper body is seen.
	 */

	Stubenv ev;
	Tuple   tup, units_tup, stubtup;
	Symbol  sym;
	int 	   i, n;

	stubtup = (Tuple) stub_info[si];
	ev = (Stubenv) stubtup[2];
	tup = ev->ev_open_decls;
	n = tup_size(tup);
	units_tup = tup_new(0);
	for (i = 1; i <= n; i++) {
		sym = (Symbol) tup[i];
		if (!tup_mem((char *)S_UNIT(sym), units_tup))
			units_tup = tup_with(units_tup, (char *)S_UNIT(sym));
	}
	stubtup[4] = (char *) units_tup;
}
