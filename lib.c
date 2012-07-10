/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#include "hdr.h"
#include "vars.h"
#include "libhdr.h"
#include "ifile.h"
#include "dbxprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "setprots.h"
#include "libfprots.h"
#include "librprots.h"
#include "libprots.h"

static char *update_lib_maps_remove(char *, int);
static void sym_restore(Symbol);

/* keeping unit_nodes as tuple, unit_nodes_now is number of actual elements */
void unit_nodes_add();

/*
 *   Procedures in this module serve two phases of the compiler:
 *
 *     (1)  maintaining a program library during semantic translation,
 *
 *     (2)  reading in and writing out the intermediate files associated with
 *	    semantic processing.
 *
 *   Three types of files are used here:
 *
 *	AIS files    information generated during the translation of a source 
 *		     file,
 *
 *	TRE files    intermediate code
 *
 *	LIB files    directory to units in AIS files,
 *
 *    LIB files and AIS files are each organized as a pair of maps whose
 *    domain elements are unique compilation unit names such as:
 *
 *	['subprog spec', 'MAIN']
 *
 *	['spec', 'MATH_PACK']
 *
 *	['subprog', 'SIN', 'MATH_PACK']
 *
 *   The first string in these names is gives the unit's class as seen
 *   by the binder:
 *
 *	'subprog spec', 'subprog'  -- subprogram specifications & bodies
 *
 *	'spec', 'body'	-- package specifications & module bodies
 *
 *   The second string is the name of the compilation unit itself.  If
 *   this is a subunit, the remaining names are those of its enclosing
 *   scopes.
 *
 *   A LIB file is a pair of maps from these unique names to the
 *   appropriate AIS files names:
 *
 *	(1)  LIB_UNIT, which indicates the file containing the
 *	     translation of each compilation unit, and
 *
 *	(2)  LIB_STUB, which indicates the file containing the
 *	     translation of the stub of the subunit.
 *
 *   Each AIS file is a parallel pair of maps, again from unique names,
 *   containing the translation of each compilation unit and the
 *   environment of each stub.	For convenience, these two maps are split
 *   into five within the translator itself:
 *
 *   COMP_DATE
 *	A map for each compilation unit to compilation dates & times
 *	checking consistency).	Dates themselves are a tuple including
 *	the date and clock time of translation, and an indication of
 *	the order of compilation within a single session.
 *
 *   PRE_COMP
 *	List of units that should have been compiled before this one.
 *
 *   UNIT_DECL
 *	The declarations that can be seen by other units, or that will
 *	be needed later by the translator.
 *
 *   STUB_ENV
 *	The environment at the point where the stub was declared.
 *
 *   During the initialization of the compiler, several predefined
 *   library units are read in and permanently installed.  These units
 *   are not included explicitly in the library, but may be accessed
 *   as if they were.  The information from their AIS files is stored in
 *   the map 'predef_map' (local to this module), and a set of those
 *   currently available (not displaced by a user's unit) is maintained
 *   in the global variable PREDEF_UNITS.  For simplicity, these
 *   predefined units may not have stubs.
 *
 *   The semantic analyser has access to compilation information in the
 *   AIS files through the procedures RETRIEVE and STUB_RETRIEVE.  When
 *   called, these two procedures try to make the requested information
 *   available in the five compilation maps listed above (it may read
 *   an AIS file, copy from predef_map or the information may
 *   already be present). If successful, they return the value TRUE,
 *   otherwise they return FALSE.
 *
 *   UPDATE_LIB_MAPS is called to do some housekeeping when a new 
 *   compilation unit is started.
 *
 *   The user may choose to not use the separate compilation facility
 *   and put every compilation unit into one file.  In this case,
 *   the LIB file can be omitted, since its role is to group several
 *   AIS files together.  Furthermore, since AIS files contain all of
 *   the information produced by a translation session, more than
 *   one LIB file may refer to a single AIS file.
 */



extern IFILE *LIBFILE;

int init_predef()				/*;init_predef*/
{
	char *lname;
	char *t_name;
	extern char *PREDEFNAME;

	lname = libset(PREDEFNAME); /* set PREDEF library as library */
	LIBFILE = ifopen("predef", "lib", "r", 0);
	t_name =libset(lname); /* restore prior library */
	return(read_lib());	/* number of units read */
}

char *predef_unit_name(int i)							/*;predef_unit_name*/
{
	static	char *predef_unit_names[15] = { "",
	 "spSYSTEM", "spIO_EXCEPTIONS", "spSEQUENTIAL_IO", 
	 "boSEQUENTIAL_IO", "spDIRECT_IO", "boDIRECT_IO", 
	  "spTEXT_IO", "boTEXT_IO", "spCALENDAR", "boCALENDAR",
	  "ssUNCHECKED_DEALLOCATION", "suUNCHECKED_DEALLOCATION",
	  "ssUNCHECKED_CONVERSION", "suUNCHECKED_CONVERSION"};
    return predef_unit_names[i];
}

int predef_node_count(int i)							/*;predef_node_count*/
{
    static int node_count[15] = {0,166, 29, 449, 5, 620, 5, 2654, 17, 470, 5,
	  20, 21, 19, 32};
	return node_count[i];
}

int predef_symbol_count(int i)						/*;predef_symbol_count*/
{
	static int symbol_count[15] = {0,31, 13, 61, 0, 88, 0, 409, 1, 83, 1,
	  5, 0 ,4 ,1};
    return symbol_count[i];
}

int retrieve(char *name)							/*;retrieve*/
{
	char	*fname;
	/*
	 * If the unit 'name' has not previously been read from
	 * an AIS file, the file is read and its the unit's contents added
	 * to the compilation maps.
	 */

#ifdef TBSN
	if (getdebug) TO_ERRFILE(strjoin("RETRIEVE ", name));
#endif
	fname = lib_unit_get(name);
	if (fname == NULL) return FALSE;
	if (!streq(fname, AISFILENAME) && !in_aisunits_read(name)){
		if (read_ais(fname, FALSE, name, 0, TRUE) == NULL) { 
			return FALSE;  /* Message emitted by READ_AIS.*/
		}
	}
	return TRUE;
}

int last_comp_index(IFILE *ifile)						/*;last_comp_index*/
{
	/* determine the number of comp units in ifile. */
    long	rec;
    int		i;

	i=0;
	for (rec=read_init(ifile); rec!=0; rec=read_next(ifile,rec)) i++; 
	return i;
}

int stub_retrieve(char *name)					/*;stub_retrieve*/
{
	char	*fname;
	Tuple	stubtup, tup;
	int		si, n, i;

	/*
	 * Reads, if necessary, information from the file in which the stub
	 * 'name' was declared.
	 */
#ifdef TBSN
	if (putdebug) TO_ERRFILE(strjoin("STUB_RETRIEVE ", name));
#endif
	fname = lib_stub_get(name);
	if (fname == NULL) return FALSE;
	if (!streq(fname, AISFILENAME)) {
		si = stub_numbered(name);
		stubtup = (Tuple) stub_info[si];
		tup = (Tuple) stubtup[4];
		n = tup_size(tup);
		for (i = 1;i <= n; i++) {
		 	retrieve(pUnits[(int)tup[i]]->name);
		}
		if (!read_stub(fname, name, "st1")) return FALSE;
	}
	return TRUE;
}

void update_lib_maps(char *name, char unit_typ)				/*;update_lib_maps*/
{
	char	*uname, *body, *typ, *other, *unit;
	int	i;

	/*
	 * Add current unit -name- to lib map, and remove references in
	 * library maps to previously compiled units with the same name.
	 * 
	 * The effect of constant map 'remove' in SETL version is achieved
	 * in C using procedure update_lib_maps_remove, which is to be
	 * found after this procedure.
	 */

	uname = unit_name_type(name);
	if (unit_typ == 'u') {
		if (streq(uname , "sp") && lib_unit_get(name) != NULL) {
			body = strjoin("bo", unit_name_names(name));
			if (lib_unit_get(body) != NULL)
			lib_unit_put(body, NULL);
		}
	/*
	 * If no other units points to the AISCODE in question, remove it
	 * from LIB_AIS.  In principle, something analoguous should may be done
	 * for systems that allows deletion of a file.
	 */
		lib_unit_put(name, AISFILENAME);
		for (i = 1;i <= 2; i++) {
			typ = update_lib_maps_remove(uname, i);
			/*(forall typ in (remove(name(1)) ? {}) )*/
			if (typ == NULL) continue;
			/*other := [typ] + name(2..);*/
			other = strjoin(typ, unit_name_names(name));
			if (lib_unit_get(other) != NULL) {
				lib_unit_put(other, NULL);
				empty_unit_slots++;
		 	}
		}
	}
	else if  (unit_typ == 's') {
		lib_stub_put(name, AISFILENAME);
		if (streq(uname, "su"))
			unit = strjoin("bo", unit_name_names(name));
		else if (streq(uname, "bo"))
			unit = strjoin("su", unit_name_names(name));
		if (lib_stub_get(unit) != NULL) 
			lib_stub_put(unit, NULL);
	}
}

static char *update_lib_maps_remove(char *nam, int lev)
{
	/*
	 *    const remove = {
	 *	['ss', {'sp', 'bo'} ],
	 *	['su', {'sp', 'bo'} ],
	 *	['sp', {'ss', 'su'} ],
	 *	['bo', {'ss', 'su'} ] };
	 */
	if (streq(nam, "ss") || streq(nam, "su")) {
	    if (lev == 1) return "sp";
	    else return "bo";
	}
	else if (streq(nam, "sp") || streq(nam, "bo")) {
	   if (lev == 1) return "ss";
	   else return "su";
	}
	else return NULL;
}

/* unit_name... procedures */
char *unit_name_name(char *u)
{
	int	n;
	char	*s1, *s2;

	n  = strlen(u);
	if ( n <= 2) return NULL;
	s1 = u + 2;				/* point to start of name*/
	s2 = strchr(s1, '.');	/* look for dot after first name */
	if (s2 == NULL)			/* if no dot take rest of string */
		s2 = u + n;			/* find end */
	n = s2 - s1;
	s2 = smalloc((unsigned) n+1);
	strncpy(s2, s1, n);
	s2[n] = '\0';			/* terminate result */
	return (s2);
}

int stub_parent_get(char *stub)					/*;stub_parent_get*/
{
	int	si;
	Tuple	stubtup;

	/*
	 * return the comp unit number of the parent unit for stub. 
	 */
	si = stub_numbered(stub);
	if (si == 0) return 0;
	stubtup = (Tuple) stub_info[si];
	return (int) stubtup[5];
}

void stub_parent_put(char *stub, char *parent)				/*;stub_parent_put*/
{
	int	si;
	Tuple	stubtup;
	si = stub_numbered(stub);
	stubtup = (Tuple) stub_info[si];
	stubtup[5] = (char *) unit_numbered(parent);
}

char *unit_name_names(char *u)				/*;unit_name_names*/
{
	char	*s1;

	if (u == NULL || strlen(u) <= 2)
	    chaos("unit_name_names: invalid unit name");
	s1 = u+2;		/* point to start of names fields */
	return strjoin("", s1);
}

char *stub_ancestors(char *u)					/*;stub_ancestors*/
{
	char	*s1;

	if (strlen(u) <= 2) return strjoin("", "");
	s1 = strchr(u+2, '.');		/* look for dot after first name */
	if (s1 == NULL) return strjoin("", "");
	return strjoin(s1+1, "");
}
	
char *stub_ancestor(char *u)					/*;stub_ancestor*/
{
	char	*s1;

	if (strlen(u) <= 2) return strjoin("", "");
	s1 = strrchr(u, '.');		/* seek last dot of name*/
	if (s1 == NULL) s1 = u+1;	/* called on unit name which is not stub*/
	return strjoin("", s1+1);	/* return rest of string */
}

int is_subunit(char *u)				/*;is_subunit*/
{
	char	*s1, *s2;

	if (u == NULL) chaos("is_subunit: null pointer");

	if (strlen(u) <= 2) return FALSE;
	s1 = u+2;				/* point to start of name*/
	s2 = strchr(s1, '.');	/* look for dot after first name */
	if (s2 == NULL)			/* if no dot take rest of string */
		return FALSE;
	return TRUE; /* if subunit*/
}

void unit_nodes_add(Node node) 				/*;unit_nodes_add*/
{
	if (node == (Node)0 || N_UNIT(node) == 0) return;
	if (N_UNIT(node) != unit_number_now) return;
	if (tup_mem((char *) node, unit_nodes))  return;
	unit_nodes = tup_with(unit_nodes, (char *)node);
}

Unitdecl unit_decl_new()				/*;unit_decl_new*/
{

	return (Unitdecl) ecalloct(sizeof(Unitdecl_s), 1, "unit-decl-new");
}

Stubenv stubenv_new()					/*;stubenv_new*/
{
	return (Stubenv) ecalloct(sizeof(Stubenv_s), 1, "stubenv-new");
}

void unit_decl_put(char *u, Unitdecl t)				/*;unit_decl_put*/
{
	int	i;
	i = unit_number(u);
	pUnits[i]->aisInfo.unitDecl = (char *) t;
}

Unitdecl unit_decl_get(char *u)				/*;unit_decl_get*/
{
	int	i;
	i = unit_numbered(u);
	if (i == 0) return (Unitdecl)0;		/* if not yet defined */
	return (Unitdecl) pUnits[i]->aisInfo.unitDecl; /*UNIT_DECL*/
}

char *lib_unit_get(char *name)				/*;lib_unit_get*/
{
	int	i;

	i = unit_numbered(name);
	if (i == 0) return NULL;
	if (streq(pUnits[i]->libInfo.obsolete, string_ok))
		return pUnits[i]->libInfo.fname;
	else
		return NULL;
}

void lib_unit_put(char *uname, char *fname)			/*;lib_unit_put*/
{
	int	i;
	struct unit *pUnit;

	i = unit_numbered(uname);
	if (i == 0) return;
	pUnit = pUnits[i];
	if (fname == NULL) {
		pUnit->libInfo.obsolete = string_ds;
		pUnit->libUnit = string_ds;
		pUnit->isMain = 0;
	}
	else {
		pUnit->libInfo.fname = fname;
		pUnit->libInfo.obsolete =string_ok;	/*"ok"*/
		pUnit->libUnit = strjoin(uname, "");
	}
}

char *lib_stub_get(char *name)				/*;lib_stub_get*/
{
	int	i;
	Tuple	tup;
	i = stub_numbered(name);
	if (i == 0) return NULL; 
	tup = (Tuple) stub_info[i];
	return tup[1];
}

void lib_stub_put(char *sname, char *fname)				/*;lib_stub_put*/
{
	int	i;
	Tuple	tup;

	i = stub_number(sname);
	if (fname == NULL)
		lib_stub[i] = strjoin(string_ds, "");
	else {
		tup = (Tuple) stub_info[i];
		tup[1] = fname;
	}
}

int current_level_get(char *sname)						/*;current_level_get*/
{
	Tuple	tup;
	int	i,cur_level;

	i = stub_numbered(sname);
	if (i == 0) return 0; 
	tup = (Tuple) stub_info[i];
	cur_level = (int) tup[3] ;
	return cur_level;
}

void current_level_put(char *sname, int cur_level)		/*;current_level_put*/
{
	int	i;
	Tuple	tup;

	i = stub_numbered(sname);
	tup = (Tuple) stub_info[i];
	tup[3] = (char *) cur_level;
}

int stub_number(char *name)					/*;stub_number*/
{
	int i, n;
	Tuple  stubtup;

	n = tup_size(lib_stub);
	for (i = 1; i <= n; i++)
		if (streq(lib_stub[i], name)) return i;
	lib_stub = tup_exp(lib_stub, (unsigned) n+1);
	lib_stub[n+1] = strjoin(name, ""); 
	stub_info = tup_exp(stub_info, (unsigned) n+1);
	stubtup = tup_new(5);
	/*
	 * [1] == stub filename 
	 * [2] == Stubenv
	 * [3] == current level
	 * [4] == tuple of stub node units
	 * [5] == stub parent
	 */
	stubtup[4] = (char *) tup_new(0);
	stub_info[n+1] = (char *) stubtup;
	return n+1;
}

int stub_numbered(char *name)					/*;stub_numbered*/
{
	int i, n;

	n = tup_size(lib_stub);
	for (i = 1; i <= n; i++)
		if (streq(lib_stub[i], name)) return i;
	return 0;
}

int unit_number(char *name)					/*;unit_number*/
{
	int i;

	for (i = 1;i <= unit_numbers; i++) {
		 if (pUnits[i]->name != NULL && 
		streq(pUnits[i]->name, name)) return i;
	}
/*
	if (empty_unit_slots) {
		for (i = 1;i <= unit_numbers; i++) {
		if (pUnits[i]->name == NULL) {
		   empty_unit_slots--;
		   break;
		}
		}
	}
	else {
*/
		i = unit_numbers + 1;
		unit_number_expand(i);
/*
	}
*/
	pUnits[i]->name = strjoin(name, "");
	return i;
}

void unit_number_expand(int n)				/*;unit_number_expand */
{
	struct unit *pUnit;

	if (n > MAX_UNITS) {	/* Figure out the way we die. bp */
		fprintf(stderr, "Too many units\n");
		exit(1);
	}
	/* expand unit_names et. al. to permit up to n entries */
	if (n <= unit_numbers) return;
	while (unit_numbers <n) {
		unit_numbers += 1;
		pUnit = pUnits[unit_numbers]
		  = (struct unit *)emalloc(sizeof(struct unit));
		pUnit->name = strjoin(string_ds, "");
		pUnit->isMain = 0;
		pUnit->libUnit = strjoin(string_ds, "");
		/* initially current ais file (tre file) name*/
		pUnit->libInfo.fname = AISFILENAME;
		pUnit->libInfo.obsolete = string_ok;
		pUnit->libInfo.currCodeSeg = NULL;
		pUnit->libInfo.localRefMap = (char *)tup_new(0);
		pUnit->libInfo.compDate = NULL;
		pUnit->aisInfo.compDate = NULL;
		pUnit->aisInfo.preComp = NULL;
		pUnit->aisInfo.unitDecl = NULL;
		pUnit->aisInfo.pragmaElab = NULL;
		pUnit->aisInfo.numberSymbols = 0;
		pUnit->aisInfo.symbols = NULL;
		pUnit->treInfo.nodeCount = 0;
		pUnit->treInfo.tableAllocated = NULL;
	}
}

int unit_numbered(char *name)				/*;unit_numbered*/
{
	int i;
	
	for (i = 1; i <= unit_numbers; i++)
		 if (streq(pUnits[i]->name, name)) return i;
	return 0;
}

int in_aisunits_read(char *f)					/*;in_aisunits_read*/
{
	int i, n;

	n = tup_size(aisunits_read);
	for (i = 1; i <= n; i++)
		if (streq(aisunits_read[i], f)) return TRUE;
	return FALSE;
}

Symbol getsymptr(int seq, int unit)		/*;getsymptr*/
{
	/* here to convert seq and unit to pointer to symbol.
	 * we require that the symbol has already been allocated
	 */
	Tuple	symptr;
	Symbol	sym;
	int	items;
	/* here to convert seq and unit to pointer to symbol.
	 * we require that the symbol has already been allocated
	 */
	/* TBSL: need to get SEQPTR table for unit, and return address
	 */

	if (unit == 0 ) {
		if (seq == 0) return (Symbol)0;
		if (seq>0 && seq <= tup_size(init_symbols)) {
			sym = (Symbol) init_symbols[seq];
			return sym;
		}	
		else
			chaos("unit 0 error getsymptr");
	}
	if (unit <= unit_numbers) {
		struct unit *pUnit = pUnits[unit];
		symptr = (Tuple) pUnit->aisInfo.symbols;
		if (symptr == (Tuple)0) {
			items = pUnit->aisInfo.numberSymbols;
			symptr = tup_new(items);
			pUnit->aisInfo.symbols = (char *) symptr;
		}
		if (seq <= tup_size(symptr)) {
			sym = (Symbol) symptr[seq];
			if (sym == (Symbol)0) {
		 		sym = sym_new_noseq(na_void);
		 		symptr[seq] = (char *) sym;
		 		S_SEQ(sym) = seq;
		 		S_UNIT(sym) = unit;
			}
#ifdef DEBUG
			if (trapss>0 && seq == trapss && unit == trapsu) traps(sym);
#endif
			return sym; /* return newly allocated symbol */
		}
		else
			chaos("getsymptr error"); return (Symbol) 0;
 	}
	chaos("getsymptr unable to find node"); return (Symbol) 0;
}

void symtab_restore(Tuple s_info)		/*;symtab_restore*/
{
	int		i, n;

	n = tup_size(s_info);
	for (i = 1; i <= n; i++)
		sym_restore((Symbol)s_info[i]);
}

static void sym_restore(Symbol sym)				/*;sym_restore*/
{
	Symbol	unam;
	
	unam = getsymptr(S_SEQ(sym), S_UNIT(sym));
	sym_copy(unam, sym);
}

Tuple sym_save(Tuple m, Symbol sym, char unit_typ)			/*;sym_save*/
{
	/* we maintain the SETL symbtab_map map from symbol table pointers to 
	 * symbol table entries as a tuple of symbol table pointers. From
	 * each symbol table pointer we can obtain the symbol table entries
	 * contained in the SETL map.
	 */
	int	i, n, seq, unit, exists;

	seq = S_SEQ(sym);
	unit = S_UNIT(sym);
	/* save only if in current unit */
	if (unit != unit_number_now && unit_typ == 'u') return m; 
	n = tup_size(m);
	exists = FALSE;
	for (i = 1; i <= n; i++) {
		if (S_SEQ((Symbol) m[i]) == seq && S_UNIT((Symbol) m[i]) == unit) {
			exists = TRUE;
			break;
		}
	}
	if (!exists) {			/* expand and allocate new symbol entry */
		m = (Tuple) tup_exp(m, (unsigned) n+1);
		i = n + 1;
		m[i] = (char *) sym_new_noseq(na_void);
	}
	sym_copy((Symbol) m[i], sym);
	return m;
}
