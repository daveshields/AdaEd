/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* libr - procedures for reading (in C format) ais and tre files*/

#include "hdr.h"
#include "vars.h"
#include "libhdr.h"
#include "ifile.h"
#include "dbxprots.h"
#include "chapprots.h"
#include "arithprots.h"
#include "dclmapprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "setprots.h"
#include "libfprots.h"
#include "libprots.h"
#include "librprots.h"

static void getlitmap(IFILE *, Symbol);
static char *getmisc(IFILE *, Symbol, int);
static void getrepr(IFILE * , Symbol);
static void getnod(IFILE *, char *, Node, int);
static void getnval(IFILE *, Node);
static int *getuint(IFILE *, char *);
static void getovl(IFILE *, Symbol);
static void getsig(IFILE *, Symbol, int);
static void getudecl(IFILE *, int);
static Tuple add_tree_node(Tuple, Node);
static void retrieve_tree_nodes(IFILE *, int, Tuple);

extern IFILE *TREFILE, *AISFILE, *STUBFILE, *LIBFILE;

Declaredmap getdcl(IFILE *ifile)			/*;getdcl*/
{
	Declaredmap d;
	char	*id;
	Symbol	sym;
	int n = 0, vis, i;

	n = getnum(ifile, "dcl_is_map_defined");
	if (n == 0) {
		return (Declaredmap) 0;
	}
	n = getnum(ifile, "dcl-number-defined"); /* get item count */
	d = dcl_new(n);
	if (n == 0) return d;
	for (i = 1; i <= n; i++) {
		id = getstr(ifile, "sym-str");
		sym = getsymref(ifile, "");
		vis = getnum(ifile, "sym-vis");
		dcl_put_vis(d, id, sym, vis);
	}
	return(d);
}

static void getlitmap(IFILE *ifile, Symbol sym)				/*;gettlitmap*/
/* called for na_enum to input literal map.
 * The literal map is a tuple, entries consisting of string followed
 * by integer.
 */
{
	Tuple	tup;
	int i, n;

	n = getnum(ifile, "litmap-n");
	tup = tup_new(n);
	for (i = 1; i <= n; i+=2) {
		tup[i] = getstr(ifile, "litmap-str");
		tup[i+1] = (char *) getnum(ifile, "litmap-value");
	}
	OVERLOADS(sym) = (Set) tup;
}

static char *getmisc(IFILE *ifile, Symbol sym, int mval)			/*;getmisc*/
{
	/* read MISC information if present 
 * MISC is integer except for package, in which case it is a triple.
 * The first two components are integers, the last is  a tuple of
 * symbols
 */
	int	nat, i, n;
	Tuple  tup, stup;

	nat = NATURE(sym);
	if ((nat == na_package || nat == na_package_spec)) {
		if (mval) {
			tup = tup_new(3);
			tup[1] = (char *) getnum(ifile, "misc-package-1");
			tup[2] = (char *) getnum(ifile, "misc-package-2");
			n = getnum(ifile, "misc-package-tupsize");
			stup = tup_new(n);
			for (i = 1; i<= n; i++)
				stup[i] = (char *) getsymref(ifile, "misc-package-symref");
			tup[3] = (char *) stup;
			return (char *) tup;
		}
		else {
			getnum(ifile, "misc");
			return  (char *)MISC(sym);
		}
	}
	else if ((nat == na_procedure || nat == na_function) && mval) {
		tup = tup_new(2);
		tup[1] = (char *) getnum(ifile, "misc-number");
		tup[2] = (char *) getsymref(ifile, "misc-symref");
		return (char *) tup;
	}
	else {
		return  (char *)getnum(ifile, "misc");
	}
}
static void getrepr(IFILE * ifile, Symbol sym)			/*;getrepr*/
{
    /* read int representation information if present */

    int 	repr_tag, i, n;
    Tuple 	align_mod_tup,align_tup,repr_tup;
    Tuple 	tup4;

    repr_tag = getnum(ifile, "repr-type");
    if (repr_tag != -1) {
        	if (repr_tag == TAG_RECORD) 	{ /* record type */
				repr_tup = tup_new(4);
				repr_tup[1] = (char *) TAG_RECORD;
           		repr_tup[2] = (char *) getnum(ifile,"repr-rec-size");
            	align_mod_tup = tup_new(2);
            	align_mod_tup[1] = (char *) getnum(ifile,"repr-rec-mod");
            	n = getnum(ifile,"repr-align_tup_size");
				align_tup = tup_new(0);
            	for (i=1; i<=n; i++) {
				    tup4 = tup_new(4);
					tup4[1] = (char *) getsymref(ifile,"repr-rec-align-1");
                	tup4[2] = (char *) getnum(ifile,"repr-rec-align-2");
                	tup4[3] = (char *) getnum(ifile,"repr-rec-align-3");
                	tup4[4] = (char *) getnum(ifile,"repr-rec-align-4");
					align_tup = tup_with(align_tup, (char *) tup4);
				}
				align_mod_tup[2] = (char *) align_tup;
           		repr_tup[4] = (char *) align_mod_tup;
				REPR(sym) = repr_tup;
        	}
			else if (repr_tag == TAG_ACCESS || 
					 repr_tag == TAG_TASK) { /* access or task type */
				repr_tup = tup_new(3);
				repr_tup[1] = (char *) repr_tag;
 				repr_tup[2] = (char *) getnum(ifile, "repr-size-2");
            	repr_tup[3] = (char *) getnodref(ifile, "repr-storage-size");
				REPR(sym) = repr_tup;
			}
        	else { 		/* non-record, non-access, non-task type */
            	n = getnum(ifile, "repr-tup-size");
				repr_tup = tup_new(n);
				repr_tup[1] = (char *) repr_tag;
            	for (i=2; i <= n; i++)
                	repr_tup[i] = (char *) getnum(ifile, "repr-info");
				REPR(sym) = repr_tup;
			}
	}
}


static void getnod(IFILE *ifile, char *desc, Node node, int unum)	/*;getnod*/
{
	/* 
	 * Read information for the node from a file (ifile)
	 * Since all the nodes in the tree all have the same N_UNIT value, 
	 * the node can be read from the file in a more compact format.
	 * The N_UNIT of the node itself and of its children (N_AST1...) need not
	 * be read only their N_SEQ filed needs to be read. There is one 
	 * complication of this scheme. OPT_NODE which is (seq=1, unit=0) will
	 * conflict with (seq=1,unit=X)  of current unit. Therefore, in this case a 
	 * sequence # of -1 will signify OPT_NODE.
	 */
	int i;
	short	nk, num1, num2, has_n_list;
	Tuple	ltup;
	short	fnum[24], fnums, fnumr=0;

	/* copy standard info */
	fnums = getnum(ifile, desc);
	/*fread((char *) &fnums, sizeof(short), 1, ifile->fh_file);*/
	fread((char *) fnum,  sizeof(short), fnums, ifile->fh_file);
	if (fnums == 0) {
		chaos("getnod-fnums-zero");
	}
	fnumr = 0;
	nk = fnum[fnumr++];
	N_KIND(node) = nk;
	N_SEQ(node) = fnum[fnumr++];
	N_UNIT(node) = unum;
#ifdef DEBUG
	if (trapns>0 && N_SEQ(node)== trapns && N_UNIT(node) == trapnu) trapn(node);
#endif

	N_SPAN0(node) = N_SPAN1(node) = 0;

	if (N_LIST_DEFINED(nk)) {
		has_n_list = fnum[fnumr++];
		ltup = (has_n_list) ? tup_new(has_n_list - 1) : (Tuple) 0;
	}
	else {
		has_n_list = 0;
	}
	/* ast fields */
	/* See comment above for description of compact format of node */
	N_AST1(node) = N_AST2(node) = N_AST3(node) = N_AST4(node) = (Node)0;
	if (N_AST1_DEFINED(nk)) {
		num1 = fnum[fnumr++];
		N_AST1(node) = (num1 == -1) ? OPT_NODE : getnodptr(num1, unum);
	}
	if (N_AST2_DEFINED(nk)) {
		num1 = fnum[fnumr++];
		N_AST2(node) = (num1 == -1) ? OPT_NODE : getnodptr(num1, unum);
	}
	if (N_AST3_DEFINED(nk)) {
		num1 = fnum[fnumr++];
		N_AST3(node) = (num1 == -1) ? OPT_NODE : getnodptr(num1, unum);
	}
	if (N_AST4_DEFINED(nk)) {
		num1 = fnum[fnumr++];
		N_AST4(node) = (num1 == -1) ? OPT_NODE : getnodptr(num1, unum);
	}

	if (N_UNQ_DEFINED(nk)) {
		num1 = fnum[fnumr++]; 
		num2 = fnum[fnumr++];
		if (num1>0 || num2>0)
			N_UNQ(node) = getsymptr(num1, num2);
	}
	if (N_TYPE_DEFINED(nk)) {
		num1 = fnum[fnumr++]; 
		num2 = fnum[fnumr++];
		if (num1>0 || num2>0) {
			N_TYPE(node) = getsymptr(num1, num2);
		}
	}

	/* read out n_list if needed */
	if (has_n_list > 0) {
		for (i = 1; i<has_n_list; i++) {
			ltup[i] = (char *) getnodref(ifile, "n-list-nodref");
		}
		if (ltup != (Tuple)0) {
			N_LIST(node) = ltup;
		}
	}
	if (N_VAL_DEFINED(nk))
		getnval(ifile, node);
}

Node getnodref(IFILE *ifile, char *desc)			/*;getnodref*/
{
	Node	node;
	int	seq, unit;

	/* 
	 * OPT_NODE is node in unit 0 with sequence 1, and needs
	 * no special handling here
	 */
	seq = getnum(ifile, "nref-seq");
	unit = getnum(ifile, "nref-unt");
	if (seq == 1 && unit == 0) {
		return OPT_NODE;
	}
	else {
		node = getnodptr(seq, unit);
#ifdef DEBUG
		if (trapns>0 && trapns == seq && trapnu == unit) trapn(node);
#endif
	}
	return node;
}

static void getnval(IFILE *ifile, Node node)				/*;getnval*/
{
	/* read N_VAL field for node to AISFILE */
	int		nk, ck;
	Const	con;
	char	*nv;
	Tuple	tup;
	int		i, n, *rn, *rd;
	double	doub;
	Symbolmap   smap;
	Symbol	s1, s2;

	nv = NULL;       /* gs nov 1: added to avoid setting N_VAL incorrectly
						at end of this routine */
	switch (nk = N_KIND(node)) {
	  case	as_simple_name:
	  case	as_int_literal:
	  case	as_real_literal:
	  case	as_string_literal:
	  case	as_character_literal:
	  case	as_subprogram_stub_tr:
	  case	as_package_stub:
	  case	as_task_stub:
				nv = (char *) getstr(ifile, "nval-name");
				break;
	  case	as_line_no:
	  case	as_number:
	  case	as_predef:
				nv = (char *) getnum(ifile, "nval-int");
				break;
	  case	as_mode:
				/* convert mode, indeed, the inverse of change made in astread*/
				nv = (char *) getnum(ifile, "nval-mode");
				break;
	  case	as_ivalue:
				ck = getnum(ifile, "nval-const-kind");
				con = const_new(ck);
				nv = (char *) con;
				switch (ck) {
				  case	CONST_INT:
					con->const_value.const_int =
					  getint(ifile, "nval-const-int-value");
					break;
				  case	CONST_REAL:
					fread((char *) &doub, sizeof(double), 1, ifile->fh_file);
					con->const_value.const_real = doub;
					break;
				  case	CONST_UINT:
					con->const_value.const_uint =
					  getuint(ifile, "nval-const-uint");
					break;
				  case	CONST_OM:
					break; /* no further data needed if OM */
				  case	CONST_RAT:
					rn = getuint(ifile, "nval-const-rat-num");
					rd = getuint(ifile, "nval-const-rat-den");
					con->const_value.const_rat = rat_fri(rn, rd);
					break;
				  case	CONST_CONSTRAINT_ERROR:
					break;
				};
				break;
	  case	as_terminate_alt:
				/*: terminate_statement (9)  nval is depth_count (int)*/
				nv = (char *) getnum(ifile, "nval-terminate-depth");
				break;
	  case	as_string_ivalue:
				/* nval is tuple of integers */
				n = getnum(ifile, "nval-string-ivalue-size");
				tup	 = tup_new(n);
				for (i = 1;i <= n; i++)
					tup[i] = (char *)getchr(ifile, "nval-string-ivalue");
				nv = (char *) tup;
				break;
	  case	as_instance_tuple:
				n = getnum(ifile, "nval-instance-size");
				if (n != 0) {
					if (n != 2)
						chaos("getnval: bad nval for instantiation");
					tup = tup_new(n);
					/* first component is instance map */
					n = getnum(ifile, "nval-symbolmap-size");
					smap = symbolmap_new();
					for (i = 1; i <= n/2; i++) {
						s1 = getsymref(ifile, "symbolmap-1");
						s2 = getsymref(ifile, "symbolmap-2");
						symbolmap_put(smap, s1, s2);
					}
					tup[1] = (char *)smap;
					/* second component is needs_body flag */
					tup [2] = (char *)getnum(ifile, "nval-flag");
					nv = (char *)tup;
				}
				else nv = NULL;
				break;
	};

	if (N_VAL_DEFINED(nk)) N_VAL(node) = nv;
	if (N_VAL_DEFINED(nk) == FALSE && nv != NULL) {
		chaos("libr.c: nval exists, but N_VAL_DEFINED not");
	}

	/* need to handle following cases:
as_simple_name:
	otherwise	identifier string

	procedure package_instance (12)
	  this procedure builds a node of type as_simple_name
	  with N_VAL a symbol pointeger.
as_pragma??
as_array aggregate
as_generic: (cf. 12)

 */

}

static int *getuint(IFILE *ifile, char *desc)				/*;getuint*/
{
	int n, *res;
	n = getnum(ifile, "uint-size");
	res = (int *) ecalloct((unsigned)n+1, sizeof(int), "getuint");
	fread((char *) res, sizeof(int), n+1, ifile->fh_file);
	return res;
}

static void getovl(IFILE *ifile, Symbol sym)				/*;getovl*/
{
	int		nat, n, i;
	Set		ovl;
	Private_declarations	pd;
	Tuple	tup;

	nat = NATURE(sym);
	ovl = (Set) 0;
	/* 
	 * It is the private declarations for na_package and na_package_spec,
	 * and na_generic_package_spec.
	 * Otherwise it is a set of symbols:
	 *	na_aggregate  na_entry	na_function  na_function_spec
	 *	na_literal  na_op  na_procedure	 na_procedure_spec
	 * It is literal map for enumeration type (na_enum).
	 */
	if(nat == na_enum) {
		getlitmap(ifile, sym);
		return;
	}
	else if (nat == na_package || nat == na_package_spec
	  || nat == na_generic_package_spec || nat == na_generic_package
	  || nat == na_task_type || nat == na_task_obj) {
		/* read in private declarations (rebuild tuple) */
		n = getnum(ifile, "ovl-private-decls-size");
		pd = private_decls_new(n);
		tup = tup_new(n+n);
		for (i = 1; i <= n; i++) {
			tup[2*i-1] =  (char *) getsym(ifile, "ovl-pdecl-1-sym");
			tup[2*i] =  (char *) getsym(ifile, "ovl-pdecl-2-sym");
		}
		pd->private_declarations_tuple = tup;
		ovl = (Set) pd;
	}
	else {	 /* if (ovl != (Set)0) */
		/* this is condition for write, but for read, we call this routine */
	 	/* iff overloads field is defined	 (gs Nov 9 ) */
		n = getnum(ifile, "ovl-set-size");
		ovl = set_new(n);
		for (i = 1; i <= n; i++)
			ovl = set_with(ovl, (char *) getsymref(ifile, "ovl-set-symref"));
	}
	if (nat != na_package || SCOPE_OF(sym) != symbol_standard0)
		/* otherwise the private dcls are inherited from the spec.*/
		OVERLOADS(sym) = ovl;
}

static void getsig(IFILE *ifile, Symbol sym, int is_private)		/*;getsig*/
{
	int nat, i, n;
	Tuple	sig, tup, sigtup;
	Node	node;
	Symbol	s, s2;

	/* The signature field is used as follows:
	 * It is a symbol for:
	 *	na_access
	 * It is a node for
	 *	na_constant  na_in  na_inout
	 * It is also a node (always OPT_NODE) for na_out. For now we read this
	 * out even though it is not used. 
	 * It is a pair for na_array.
	 * It is a triple for na_enum.
	 * It is a triple for na_generic_function_spec na_generic_procedure_spec
	 * The first component is a tuple of pairs, each pair consisting of
	 * a symbol and a (default) node.
	 * The second component is a tuple of symbols.
	 * The third component is a node.
	 * It is a tuple with four elements for na_generic_package_spec:
	 * the first is a tuple of pairs, with same for as for generic procedure.
	 * the second third,and fourth components are nodes.
	 *	(see libw.c for format)
	 * It is a 5-tuple for na_record.
	 * It is a constraint for na_subtype and na_type.
	 * It is a node for na_obj.
	 * It is a tuple of nodes for na_task_type, na_task_type_spec
	 * Otherwise it is the signature for a procedure, namely a tuple
	 * of quadruples.
	 * In the expand tasks are converted to procedures so their signature is
	 * like that of procs.
	 */

	nat = NATURE(sym);
	/* is_private indicates signature has form of that for record */
	if (is_private) nat=na_record;

	switch (nat) {
	  case	na_access:
				/* access: signature is designated_type;*/
				sig = (Tuple) getsymref(ifile, "sig-access-symref");
				break;
	  case	na_array:
array_case:
				/* array: signature is pair [i_types, comp_type] where
	 			* i_types is tuple of type names
	 			*/
				sig = tup_new(2);
				n = getnum(ifile, "sig-array-itypes-size");
				tup = tup_new(n);
				for (i = 1; i <= n; i++)
					tup[i] = (char *)getsymref(ifile, "sig-array-i-types-type");
				sig[1] = (char *) tup;
				sig[2] = (char *) getsymref(ifile, "sig-array-comp-type");
				break;
	  case	na_block:
				/* block: miscellaneous information */
				/* This information not needed externally*/
				chaos("getsig: signature for block");
				break;
	  case	na_constant:
	  case	na_in:
	  case	na_inout:
	  case	na_out:
	  case	na_discriminant:
				sig = (Tuple) getnodref(ifile, "sig-discriminant-nodref");
				break;
	  case	na_entry:
	  case	na_entry_family:
	  case	na_entry_former:
	  /* entry: list of symbols */
	  case	na_function:
	  case	na_function_spec:
	  case	na_literal:
	  case	na_op:
	  case	na_procedure:
	  case	na_procedure_spec:
	  case	na_task_body:
				n = getnum(ifile, "sig-tuple-size");
				sig = tup_new(n);
				for (i = 1; i <= n; i++)
					sig[i] = (char *) getsymref(ifile, "sig-tuple-symref");
				break;
	  case	na_enum:
				/* enum: tuple in form ['range', lo, hi]*/
				/* we read this as two node references*/
				sig = tup_new(3);
				/*sig[1] = ???;*/
				sig[2] = (char *) getnodref(ifile, "sig-enum-low-nodref");
				sig[3] = (char *) getnodref(ifile, "sig-enum-high-nodref");
				break;
	  case	na_type:
#ifdef TBSL
				s  = TYPE_OF(sym);
				s2 = TYPE_OF(root_type(sym));
				if ((s != (Symbol)0 && NATURE(s) == na_access) || 
		    		(s2 != (Symbol)0 && NATURE(s2) == na_access))  {
					getsymref(ifile, "sig-access-symref");
					break;
				}
#endif
                        	i = getnum(ifile, "sig-type-is-access");
                        	if (i == 1) break; 
				/* for private types, is_private will be true, and
				*  signature is that of record 
	 			*/
				n = getnum(ifile, "sig-type-size");
				i = getnum(ifile, "sig-constraint-kind");
				sig = tup_new(n);
				sig[1] = (char *) i;
				for (i=2; i <= n; i++)
					sig[i] = (char *) getnodref(ifile, "sig-type-nodref");
				break;
	  case na_subtype:
				n = getnum(ifile, "sig-subtype-size");
				i = getnum(ifile, "sig-constraint-kind");
				if (i == CONSTRAINT_ARRAY) goto array_case;
				sig = tup_new(n);
				sig[1] = (char *) i;
				if (i == CONSTRAINT_DISCR) {
					/* discriminant map */
					n = getnum(ifile, "sig-constraint-discrmap-size");
					tup = tup_new(n);
					for (i = 1; i <= n; i+=2) {
						tup[i] = (char *)getsymref(ifile,
						  "sig-constraint-discr-map-symref");
						tup[i+1] = (char *)getnodref(ifile,
						  "sig-constraint-discr-map-nodref");
					}
					sig[2] = (char *) tup;
				}
				else if (i == CONSTRAINT_ACCESS) {
					sig[2] = (char *)getsymref(ifile, "sig-subtype-acc-symref");
				}
				else {
					for (i=2; i <= n; i++)
						sig[i] = (char *)getnodref(ifile, "sig-subtype-nodref");
				}
				break;
	  case	na_generic_function:
	  case	na_generic_procedure:
	  case	na_generic_function_spec:
	  case	na_generic_procedure_spec:
				sig = tup_new(4);
				if (tup_size(sig) != 4) chaos(
					"getsig: bad signature for na_generic_procedure_spec");
				/* tuple count known to be four, just put elements */
				/* the first component is a tuple of pairs, just read count
	 			* and the values of the successive pairs 
	 			*/
				n = getnum(ifile, "sig-generic-size");
				sigtup = tup_new(n);
				for (i = 1;i <= n; i++) {
					tup = tup_new(2);
					tup[1] = (char *) getsymref(ifile, "sig-generic-symref");
					tup[2] = (char *) getnodref(ifile, "sig-generic-nodref");
					sigtup[i] = (char *) tup;
				}
				sig[1] = (char *) sigtup;
				n = getnum(ifile, "sig-generic-typ-size"); /* symbol list */
				tup = tup_new(n);
				for (i = 1;i <= n; i++)
					tup[i] = (char *) getsymref(ifile,
					  "sig-generic-symbol-symref");
				sig[2] = (char *) tup;
				node = getnodref(ifile, "sig-generic-3-nodref");
				if (nat == na_generic_procedure || nat == na_generic_function)
					sig[3] = (char *) node;
				else sig[3] = (char *) OPT_NODE;
				/* the four component is tuple of must_constrain symbols */
				n = getnum(ifile, "sig-generic-package-tupsize");
				tup = tup_new(n);
				for (i = 1;i <= n; i++)
					tup[i] = (char *) getsymref(ifile,
					  "sig-generic-package-symref");
				sig[4] = (char *) tup;
				break;
	  case	na_generic_package_spec:
	  case	na_generic_package:
				/* signature is tuple with four elements */
				sig = tup_new(5);
				/* the first component is a tuple of pairs, just write count
	 			* and the values of the successive pairs 
	 			*/
				n = getnum(ifile, "sig-generic-package-tupsize");
				tup = tup_new(n);
				for (i = 1;i <= n; i++) {
					sigtup = tup_new(2);
					sigtup[1] = (char *) getsymref(ifile,
					  "sig-generic-package-symref");
					sigtup[2] = (char *) getnodref(ifile,
					  "sig-generic-package-nodref");
					tup[i] = (char *) sigtup;
				}
				sig[1] = (char *) tup;
				/* the second third, and fourth components are just nodes */
				sig[2] = (char *) getnodref(ifile, "sig-generic-node-2");
				sig[3] = (char *) getnodref(ifile, "sig-generic-node-3");
				sig[4] = (char *) getnodref(ifile, "sig-generic-node-4");
				/* the fifth component is tuple of must_constrain symbols */
				n = getnum(ifile, "sig-generic-package-tupsize");
				tup = tup_new(n);
				for (i = 1;i <= n; i++)
					tup[i] = (char *) getsymref(ifile,
					  "sig-generic-package-symref");
				sig[5] = (char *) tup;
				break;
	  case	na_record:
				/* the signature is tuple with five components:
		 		* [node, node, tuple of symbols, declaredmap, node]
		 		* NOTE: we do not read component count - 5 assumed 
		 		*/
				sig = tup_new(5);
				sig[1] = (char *) getnodref(ifile, "sig-record-1-nodref");
				sig[2] = (char *) getnodref(ifile, "sig-record-2-nodref");
				n = getnum(ifile, "sig-record-3-size");
				tup = tup_new(n);
				for (i = 1; i <= n; i++)
					tup[i] = (char *) getsymref(ifile, "sig-record-3-nodref");
				sig[3]= (char *) tup;
				sig[4] = (char *) getdcl(ifile);
				sig[5] = (char *) getnodref(ifile, "sig-record-5-nodref");
				break;
	  case	na_void:
				/* special case assume entry for $used, in which case is tuple
		 		* of symbols
		 		*/
				if (streq(ORIG_NAME(sym), "$used") ) {
					n = getnum(ifile, "sig-$used-size");
					sig = tup_new(n);
					for (i = 1; i <= n; i++)
						sig[i] = (char *) getsymref(ifile, "sig-$used-symref");
				}
				else {
#ifdef DEBUG
					zpsym(sym);
#endif
					chaos("getsig: na_void, not $used");
				}
				break;
	  case	na_obj:
				sig = (Tuple) getnodref(ifile, "sig-obj-nodref");
				break;
	  case	na_task_type:
	  case	na_task_type_spec:
				/* a tuple of nodes */
				n = getnum(ifile, "task-type-spec-size");
				sig = tup_new(n);
				for (i = 1; i <= n; i++)
					sig[i] = (char *)getnodref(ifile, "sig-task-nodref");
				break;
	default:
#ifdef DEBUG
				printf("getsig: default error\n");
				zpsym(sym);
#endif
				chaos("getsig: default");
	} /* End of switch */
	SIGNATURE(sym) = sig;
}

Symbol getsym(IFILE *ifile, char *desc)								/*;getsym*/
{
	Symbol	sym, tmp_sym;
	struct f_symbol_s fs;
	int i, nat, is_private;

	/* read description for symbol sym to input file */
	fread((char *) &fs, sizeof(f_symbol_s), 1, ifile->fh_file);
	sym = getsymptr(fs.f_symbol_seq, fs.f_symbol_unit);
	nat = fs.f_symbol_nature;
	NATURE(sym) = nat;
	S_SEQ(sym) = fs.f_symbol_seq;
	S_UNIT(sym) = fs.f_symbol_unit;
#ifdef DEBUG
	if (trapss>0 && trapss == fs.f_symbol_seq 
	    && trapsu == fs.f_symbol_unit) traps(sym);
#endif
	TYPE_OF(sym) = getsymptr(fs.f_symbol_type_of_seq,
	    fs.f_symbol_type_of_unit);
	SCOPE_OF(sym) = getsymptr(fs.f_symbol_scope_of_seq,
	    fs.f_symbol_scope_of_unit);
	ALIAS(sym) = getsymptr(fs.f_symbol_alias_seq,
	    fs.f_symbol_alias_unit);
	if (fs.f_symbol_type_attr & TA_ISPRIVATE) {
		is_private = TRUE;
		fs.f_symbol_type_attr ^= TA_ISPRIVATE; /* turn off ISPRIVATE bit*/
	}
	else {
		is_private = FALSE;
	}
	TYPE_ATTR(sym) = fs.f_symbol_type_attr;
	ORIG_NAME(sym) = getstr(ifile, "orig-name");
	/* process overloads separately due to variety of cases */
	if (fs.f_symbol_overloads) getovl(ifile, sym);

	/* read out declared map, treating na_enum case separately */
	if (fs.f_symbol_declared) DECLARED(sym)= getdcl(ifile);

	/* signature */
	if (fs.f_symbol_signature) getsig(ifile, sym, is_private);

	MISC(sym) = getmisc(ifile, sym, fs.f_symbol_misc);

	/* the following fields are extracted for the code generator use only */
	if (TYPE_KIND(sym)  ==  0) TYPE_KIND(sym) = fs.f_symbol_type_kind;
	if (TYPE_SIZE(sym) == 0) TYPE_SIZE(sym) = fs.f_symbol_type_size;
	if (is_type(sym))
		INIT_PROC(sym) = getsymptr(fs.f_symbol_init_proc_seq,
		  fs.f_symbol_init_proc_unit);
	else 		 /* formal_decl_tree for subprogram specs */
		INIT_PROC(sym) = (Symbol) getnodptr(fs.f_symbol_init_proc_seq,
		  fs.f_symbol_init_proc_unit);
	if (ASSOCIATED_SYMBOLS(sym) != (Tuple)0) {
		for (i = 1; i<fs.f_symbol_assoc_list; i++) {
			tmp_sym = (Symbol) getsymref(ifile, "assoc-symbol-symref");
			if (tmp_sym != (Symbol)0)
				ASSOCIATED_SYMBOLS(sym)[i] = (char *) tmp_sym;
		}
	}
	else {
		if (fs.f_symbol_assoc_list == 0)
			ASSOCIATED_SYMBOLS(sym) = (Tuple) 0;
		else 
			ASSOCIATED_SYMBOLS(sym) = tup_new(fs.f_symbol_assoc_list -1);
		if (fs.f_symbol_assoc_list > 1) {
			for (i = 1; i<fs.f_symbol_assoc_list; i++)
				ASSOCIATED_SYMBOLS(sym)[i] =
				  (char *) getsymref(ifile, "assoc-symbol-symref");
		}
	}
	getrepr(ifile, sym);
	if (S_SEGMENT(sym) == -1) S_SEGMENT(sym) = fs.f_symbol_s_segment;
	if (S_OFFSET(sym) == 0)   S_OFFSET(sym) = fs.f_symbol_s_offset;
	return sym;
}


Node getnodptr(int seq, int unit)		/*;getnodptr*/
{
	Tuple	nodptr;
	Node	node;
	/* here to convert seq and unit to pointer to symbol.
	 * we require that the symbol has already been allocated
	 */
	/* TBSL: need to get SEQPTR table for unit, and return address
	 */
	if (unit == 0) {
		if (seq == 1) return OPT_NODE;
		if (seq == 0) return (Node)0;
		if (seq>0 && seq <= tup_size(init_nodes)) {
			node = (Node) init_nodes[seq];
			return node;
		}
		else {
			chaos("error for unit 0 in getnodptr");
		}
	}
	if (unit <= unit_numbers) {
		struct unit *pUnit = pUnits[unit];
		nodptr = (Tuple) pUnit->treInfo.tableAllocated;
		if (seq == 0) chaos("getnodptr seq 0");
		if (tup_size(nodptr) != pUnit->treInfo.nodeCount) {
			/* this check is to avoid preallocation of node ptrs for all units
	 		* in the library.
	 		*/
			tup_free(nodptr);
			nodptr = tup_new(pUnit->treInfo.nodeCount);
			pUnit->treInfo.tableAllocated = (char *)nodptr;
		}
		if (seq <= pUnit->treInfo.nodeCount) {
			node = (Node) nodptr[seq];
			if (node == (Node)0) {/* here to allocate node on first reference */
				node = node_new_noseq(as_unread);
				N_SEQ(node) = seq;
				N_UNIT(node) = unit;
				nodptr[seq] = (char *) node;
			}
			return node;
		}
	}
	chaos("getnodptr unable to find node");
	return (Node) 0;	/* dummy return for lint's sake */
}

Symbol getsymref(IFILE *ifile, char *desc)			/*;getsymref*/
{
	Symbol	sym;
	int seq, unit;
	seq = getnum(ifile, "sym-seq");
	unit = getnum(ifile, "sym-unt");
	sym = getsymptr(seq, unit);
#ifdef DEBUG
	if (trapss > 0 && trapss == seq && trapsu == unit) traps(sym);
#endif
	return sym;
}

static void getudecl(IFILE *ifile, int ui)				/*;getudecl*/
{
	int i, n, ci, cn;
	Tuple	tup, cent, ctup, cntup, symtup;
	Symbol	usym;
	Unitdecl	ud;

	ud = unit_decl_new();
	pUnits[ui]->aisInfo.unitDecl = (char *) ud;
	/* The second entry is the sequence of the symbol table entry
	 * identifying the unit. We use this sequence number to find
	 * the actual entry alread allocated.
	 */
	usym = getsym(ifile, "ud-unam");
	ud->ud_unam = usym;
	ud->ud_useq = S_SEQ(usym);
	ud->ud_unit = S_UNIT(usym);
	get_unit_unam(ifile, usym);
	/* context */
	n = getnum(ifile, "decl-context-size");
	if (n > 0) {
		n -= 1; /* true tuple size */
		ctup = tup_new(n);
		for (i = 1; i <= n; i++) {
			cent = (Tuple) tup_new(2);
			cent[1] = (char *) getnum(ifile, "decl-ctup-1");
			cn = getnum(ifile, "decl-cntup-size"); 
			cntup = tup_new(cn);
			for (ci = 1; ci <= cn; ci++)
				cntup[ci] = getstr(ifile, "decl-tupstr-str");
			cent[2] = (char *) cntup;
			ctup[i] = (char *) cent;
		}
		ud->ud_context =  ctup;
	}
	/* unit_nodes */
	n = getnum(ifile, "decl-ud-nodes-size");
	tup = tup_new(n);
	for (i = 1; i <= n; i++) {
		tup[i] = (char *) getnodref(ifile, "decl-nodref");
	}
	ud->ud_nodes = tup;
	/* tuple of symbol table pointers */
	n = getnum(ifile, "decl-tuple-size");
	if (n > 0) {
		n -= 1; /* true tuple size */
		tup = tup_new(n);
		for (i = 1; i <= n; i++) {
			tup[i] = (char *) getsym(ifile, "decl-symref");
		}
		ud->ud_symbols = tup;
	}
	/* decscopes - tuple of scopes */
	n = getnum(ifile, "decl-descopes-tuple-size");
	if (n > 0) {
		n -= 1; /* true tuple size */
		symtup = tup_new(n);
		for (i = 1; i <= n; i++) {
			symtup[i] = (char *) getsym(ifile, "decl-decscopes-symref");
		}
		ud->ud_decscopes =	symtup;
	}
	/* decmaps - tuple of declared maps */
	n = getnum(ifile, "decmaps-tuple-size");
	if (n > 0) {
		n -= 1; /* true tuple size */
		tup = tup_new(n);
		for (i = 1; i <= n; i++) {
#ifdef TBSN
			-- use decl maps read in with symbols	ds 21 dec 
			    -- but read in anyway for completeness
#endif
		    tup[i] = (char *) getdcl(ifile);
			tup[i] = (char *) DECLARED((Symbol)symtup[i]);
		}
		ud->ud_decmaps = tup;
	}
	/* oldvis - tuple of unit names */
	n = getnum(ifile, "vis");
	if (n > 0) {
		n -= 1; /* true tuple size */
		tup = tup_new(n);
		for (i = 1; i <= n; i++) {
			tup[i] = getstr(ifile, "vis-str");
		}
		ud->ud_oldvis = tup;
	}
	return;
}

char *read_ais(char *fname, int is_aic_file, char *uname,
  int comp_index, int tree_is_needed)  /*;read_ais*/
{
	/* read aic or axq for unit with name uname from file fname.
	 * is_aic_file indicates whether we are reading from an aic or axq file.
	 * if uname is the null pointer, read 'comp_index'th unit from the file.
	 * return TRUE if read ok, FALSE if not. tree_is_needed is a flag to
	 * indicate whether retrieve_tree_nodes needs to be called. Is is always
	 * TRUE for the semantic phase and when called by the expander but is
	 * FALSE when called by BIND in the code generator.
	 */

	long	rec, genoff;
	int		indx, fnum, unum, n, nodes, symbols, i, is_main_unit;
	Tuple	symptr, tup, nodes_group;
	Set		set;
	struct unit *pUnit;
	char	*funame, *retrieved ;
	Unitdecl	ud;
	IFILE	*ifile;
	char    *lname, *tname, *full_fname;
	int		is_predef; /* set when reading predef file */
	/* Read information from the current compilation to
	 * 'file', restructuring the separate compilation maps
	 * to improve the readability of the AIS code.
	 */

	retrieved = NULL;
	indx = 0;
	is_predef = streq(fname, "0") && strlen(PREDEFNAME);
	if (is_predef) {
		/* reading predef, but not compiling it ! */
		lname = libset(PREDEFNAME);
		full_fname = "predef" ;
	}
	else {
		full_fname = fname;
	}
	if (is_aic_file)
		ifile = ifopen(full_fname, "aic", "r", 0);
	else
		ifile = ifopen(full_fname, "axq", "r", 0);
	if (is_predef)
		tname = libset(lname); /* restore library name after predef read */
	for (rec=read_init(ifile); rec != 0; rec=read_next(ifile, rec)) {
		indx++;
		funame = getstr(ifile, "unit-name");
		if (uname == NULL && indx != comp_index) continue;
		if (uname != NULL  && streq(uname, funame) == 0) continue;
		fnum = getnum(ifile, "unit-number");
		unum = unit_number(funame);
		if (unum != fnum) chaos("read_ais sequence number error");
		pUnit = pUnits[unum];
		genoff = getlong(ifile, "code-gen-offset");
		is_main_unit = streq(unit_name_type(funame), "ma");
		if (!is_main_unit) { /* read only if NOT main unit (it has no ais info*/
			symbols = getnum(ifile, "seq-symbol-n");
			nodes = getnum(ifile, "seq-node-n");
			/* install tre node info and symbol count in the case where the
			*  generator reads semantic aisfile and therefore bypasses
			*  read_lib where the info is normally installed.
	 		*/
			if (is_aic_file) {
				pUnit->treInfo.nodeCount = nodes;
				pUnit->treInfo.tableAllocated = (char *) tup_new(nodes);
				pUnit->aisInfo.numberSymbols = symbols;
				/* May be old value of aistup[7] may be freed at this point
				*  of this is recompilation of unit within the last compilation.
	 			*/
				pUnit->aisInfo.symbols = (char *) tup_new(symbols);
				pUnit->libInfo.fname = AISFILENAME;
				pUnit->libInfo.obsolete = string_ok;
			}
			symptr = (Tuple) pUnit->aisInfo.symbols;
			if (symptr == (Tuple)0) { /* if tuple not yet allocated */
				symptr = tup_new(symbols);
				pUnit->aisInfo.symbols = (char *) symptr;
			}

			/* ELABORATE PRAGMA INFO */
			n = getnum(ifile, "pragma-info-size");
			tup = tup_new(n);
			for (i = 1; i <= n; i++)
				tup[i] = getstr(ifile, "pragma-info-value");
			pUnit->aisInfo.pragmaElab = (char *) tup;
			/* UNIT_DECL */
			getudecl(ifile, unum);
			/* PRE_COMP */
			n = getnum(ifile, "precomp-size");
			set = (Set) set_new(n);
			for (i = 1; i <= n; i++)
				set = set_with(set, (char *) getnum(ifile, "precomp-value"));
			pUnit->aisInfo.preComp = (char *) set;
			/* tuple of symbol table pointers */
			aisunits_read = tup_with(aisunits_read, funame);
		}
		retrieved = funame;
		break;
	}
	if (tree_is_needed && retrieved) {
		ud = (Unitdecl) pUnit->aisInfo.unitDecl;
		tup = (Tuple) ud->ud_nodes;
		n = tup_size(tup);
		nodes_group = tup_new(n);
		for (i = 1; i <= n; i++)
			nodes_group[i] = (char *) N_SEQ((Node)tup[i]);
		retrieve_tree_nodes(ifile, unum, nodes_group);
	}
	ifclose(ifile);
	return retrieved;
}

int read_stub(char *fname, char *uname, char *ext)				/*;read_stub*/
{
	long	rec;
	Stubenv	ev;
	int		i, j, k, n, m, si;
	char	*funame;
	Tuple	stubtup, tup, tup2, tup3;
	int		ci, cn;
	int		parent_unit;
	Tuple	cent, ctup, cntup, nodes_group;
	Symbol	sym;
	int		retrieved = FALSE;
	IFILE	*ifile;

	/* open so do not fail if no file */
	ifile = ifopen(fname, ext, "r", 1);
	if (ifile == (IFILE *)0) return retrieved; /* if not stub file */
	
	for (rec = read_init(ifile); rec != 0; rec=read_next(ifile, rec)) {
		funame = getstr(ifile, "stub-name");
		if (uname != NULL  && !streq(uname, funame)) continue;
		si = stub_number(funame);
		if (uname == NULL) lib_stub_put(funame, fname);
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
				for (k=1; k <= m; k++)
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
		if (n > 0) {
			n -= 1; /* true tuple size */
			ctup = tup_new(n);
			for (i = 1; i <= n; i++) {
				cent = (Tuple) tup_new(2);
				cent[1] = (char *) getnum(ifile, "stub-cent-1");
				cn = getnum(ifile, "stub-cent-2-size"); 
				cntup = tup_new(cn);
				for (ci = 1; ci <= cn; ci++)
					cntup[ci] = getstr(ifile, "stub-cent-2-str");
				cent[2] = (char *) cntup;
				ctup[i] = (char *) cent;
			}
			ev->ev_context =  ctup;
		}
		/* tuple of symbol table pointers */
		/* read in but ignore symbol table references. This is for
		 * read_stub_short so that the generator can rewrite the stubfile
		 * without reading in full symbol table info from semantics phase.
		 */
		n = getnum(ifile, "ev-decls-refs-size");
		if (n > 0) {
			n -= 1; /* true tuple size */
			for (i = 1; i <= n; i++)
				sym = getsymref(ifile, "ev-decls-sym-ref");
		}
		/* tuple of symbol table pointers */
		n = getnum(ifile, "ev-open-decls-size");
		if (n > 0) {
			n -= 1; /* true tuple size */
			tup = tup_new(n);
			for (i = 1; i <= n; i++) {
				sym = getsym(ifile, "ev-open-decls-sym");
/*
	if (NATURE(sym) == na_package || NATURE(sym) == na_procedure) {
		sym_temp = sym_new_noseq(na_void);
		sym_copy(sym_temp, sym);
		tup[i] = (char *) sym_temp;
	}
	else {
		tup[i] = (char *) sym;
 	}
*/
				tup[i] = (char *) sym;
			}
			ev->ev_open_decls = tup;
		}
		ev->ev_current_level = getnum(ifile, "ev-current-level");
		/* tuple of relay-set symbols */
		n = getnum(ifile, "ev-relay-set-size");
		if (n > 0) {
			n -= 1; /* true tuple size */
			tup = tup_new(n);
			for (i = 1; i <= n; i++) {
				tup[i] = (char *) getsymref(ifile, "relay-set-sym");
			}
			ev->ev_relay_set = tup;
		}
		else {
			ev->ev_relay_set = tup_new(0);
		}
		/* tuple of dang-relay-set symbols */
		n = getnum(ifile, "ev-dang-relay-set-size");
		if (n > 0) {
			n -= 1; /* true tuple size */
			tup = tup_new(n);
			for (i = 1; i <= n; i++)
				tup[i] = (char *) getnum(ifile, "dang-relay-set-ent");
			ev->ev_dangling_relay_set = tup;
		}
		else {
			ev->ev_dangling_relay_set = tup_new(0);
		}
		retrieved = TRUE;
		if (uname != NULL)  break;
	}
	if (retrieved)  {
		tup = ev->ev_nodes;
		n = tup_size(tup);
		nodes_group = tup_new(n);
		for (i = 1; i <= n; i++)
			nodes_group[i] = (char *) N_SEQ((Node)tup[i]);
		parent_unit = stub_parent_get(funame);
		retrieve_tree_nodes(ifile, parent_unit, nodes_group);
	}
	ifclose(ifile);
	return retrieved;
}

int read_lib()					/*;read_lib*/
{
	int		comp_status, si, i, j, n, m, nodes, symbols, cur_level;
	int		parent, unit_count;
	Tuple	stubtup, tup;
	struct unit *pUnit;
	char	*uname, *aisname, *tmp_str, *parent_name, *compdate;
	IFILE	*ifile;

	ifile = LIBFILE;
	/* note that library file opened by lib_aisname */
	unit_count = getnum(ifile, "lib-unit-count");
	n = getnum(ifile, "lib-n");
	empty_unit_slots = getnum(ifile, "lib-empty-slots");
	tmp_str = getstr(ifile, "tmp-str");
	unit_number_expand(n);
	for (i = 1;i <= unit_count; i++) {
		uname = getstr(ifile, "lib-unit-name");
		pUnit = pUnits[getnum(ifile, "lib-unit-number")];
		aisname = getstr(ifile, "lib-ais-name");
		compdate = getstr(ifile, "comp-date");
		symbols = getnum(ifile, "lib-symbols");
		nodes = getnum(ifile, "lib-nodes");
		pUnit->name = strjoin(uname, "");
		pUnit->isMain = getnum(ifile, "lib-is-main");
		comp_status = getnum(ifile, "lib-status");
		pUnit->libInfo.fname = strjoin(aisname, "");
		pUnit->libInfo.obsolete = (comp_status) ? string_ok: string_ds ;
		pUnit->libUnit = (comp_status) ? strjoin(uname, "") : string_ds;
		pUnit->aisInfo.numberSymbols = symbols;
		pUnit->treInfo.nodeCount = nodes;
		pUnit->treInfo.tableAllocated = (char *) tup_new(0);
	}
	n = getnum(ifile, "lib-n");
	for (i = 1;i <= n; i++) {
		uname = getstr(ifile, "lib-unit-name");
		aisname = getstr(ifile, "lib-ais-name");
		lib_stub_put(uname, strjoin(aisname, ""));
		parent = getnum(ifile, "lib-parent");
		if (parent == 0) parent_name = " ";
		else parent_name = pUnits[parent]->name;
		stub_parent_put(uname, parent_name);
		cur_level = getnum(ifile, "lib-cur-level");
		current_level_put(uname, cur_level);
		/* the following is the associated symbol for a package stub */
		si = stub_numbered(uname);
		stubtup = (Tuple) stub_info[si];
		m = getnum(ifile, "stub-file-size");
		tup = tup_new(m);
		for (j = 1;j <= m;j++)
			tup[j] = (char *) getnum(ifile, "stub-file");
		stubtup[4] = (char *) tup;
	}
	ifclose(LIBFILE);
	LIBFILE = (IFILE *) 0;
	return(unit_count);

	/* read out LIB_STUB map (always empty for now) */
}

void load_tre(IFILE *ifile, int comp_index)						/*;load_tre*/
{
	/* load entire tree file. */

    long	rec, *off;
    int		i, fnum, unum, n, nodes, rootseq;
    char	*funame; 

	i=0;
	for (rec=read_init(ifile); rec!=0; rec=read_next(ifile, rec)) {
    	i++;
    	if (i != comp_index) continue;
    	funame = getstr(ifile, "unit-name");
    	fnum = getnum(ifile, "unit-number");
    	unum = unit_number(funame);
    	if (unum!=fnum)
			chaos("load_tre sequence number error");
    	nodes = getnum(ifile, "node-count");
    	/* the rest of the tree info is set in read_ais. Perhaps all can be
		 * done there.
    	 */
    	off= (long *)ecalloct((unsigned)nodes+1,sizeof(long),"load-tree-tup-3");
    	fread((char *) off, sizeof(long), nodes+1, ifile->fh_file);
    	rootseq = getnum(ifile, "root-seq");
		pUnits[unum]->treInfo.rootSeq = rootseq;
    	for (n = 1; n <= nodes; n++) {
			if (off[n] == 0) { /* node not needed */
	   			continue;
			}
			else {
	   			ifseek(ifile, "seek-node", off[n], 0);
	   			getnod(ifile, "unit-node", getnodptr(n, unum), unum);
			}
    	}
		break;
	}
	tup_free((Tuple) off);
	ifclose(ifile);
}

static Tuple add_tree_node(Tuple tup, Node nod)				/*;add_tree_nodes */
{
	int		seq;

	if (nod == (Node)0 || nod == OPT_NODE) return tup;
	seq = N_SEQ(nod);
	if (tup_mem((char *) seq, tup)) return tup;
	tup = tup_with(tup, (char *) seq);
	return tup;
}

static void retrieve_tree_nodes(IFILE *ifile,
  int node_unit, Tuple nodes_list)   /*;retrieve_tree_nodes*/
{
	long	rec, *off;
	int		unum, items;
	int		node_seq, nkind;
	char  	*fname;
	char    *tfname;
	Node	fn, nd;
	Fortup	ft1;
	char    *lname, *tname;

	/* read tree file for unit with unit number "node_unit" and load only
	 * the nodes in nodes_list.
	 */

	fname = lib_unit_get(pUnits[node_unit]->name);
	if (streq(fname, "0") && !streq(PREDEFNAME, "")) {
		/* reading predef, but not compiling it ! */
		lname = libset(PREDEFNAME);
		tfname = "predef";
	}
	else {
		tfname = fname;
	}
	ifile = ifopen(tfname, "trc", "r", 0);
	if (streq(fname, "0") && !streq(PREDEFNAME, ""))
		tname= libset(lname); /* restore library name */

	for (rec=read_init(ifile); rec != 0; rec=read_next(ifile, rec)) {
		getstr(ifile, "unit_name"); /* skip over unit name */
		unum = getnum(ifile, "unit-number");
		if (unum != node_unit) continue;
		items = getnum(ifile, "node-count");
		off = (long *) ecalloct((unsigned)items+1, sizeof(long), "read-tree");
		fread((char *) off, sizeof(long), items+1, ifile->fh_file);
		break;
	}
	while (tup_size(nodes_list)) {
		node_seq = (int) tup_frome(nodes_list);
		ifseek(ifile, "seek-node", off[node_seq], 0);
		fn = getnodptr(node_seq, node_unit);
		getnod(ifile, "unit-node", fn, unum);

		nkind = N_KIND(fn);
		if (N_AST1_DEFINED(nkind) && N_AST1(fn) != (Node)0)
			nodes_list = add_tree_node(nodes_list, N_AST1(fn));
		if (N_AST2_DEFINED(nkind) && N_AST2(fn) != (Node)0)
			nodes_list = add_tree_node(nodes_list, N_AST2(fn));
		if (N_AST3_DEFINED(nkind) && N_AST3(fn) != (Node)0)
			nodes_list = add_tree_node(nodes_list, N_AST3(fn));
		if (N_AST4_DEFINED(nkind) && N_AST4(fn) != (Node)0)
			nodes_list = add_tree_node(nodes_list, N_AST4(fn));

		if (N_LIST_DEFINED(N_KIND(fn)) && N_LIST(fn) != (Tuple)0) {
			FORTUP(nd=(Node), N_LIST(fn), ft1);
			nodes_list = add_tree_node(nodes_list, nd);
			ENDFORTUP(ft1);
		}
	}
	tup_free((Tuple) off);
	tup_free(nodes_list);
	ifclose(ifile);
}

void retrieve_generic_tree(Node node1, Node node2)	/*;retrieve_generic_tree*/
{
	Tuple	tup;
	int		unum;

	/* Bring in the part of the tree corresponding to a generic package spec
	 * or body, or a generic subprogram body.
	 * When node2 is not 0 it is the case of generic packages and node1
	 * represent the decls_node and node2 represents the priv_node. Otherwise
	 * node1 represents the body_node.
	 */
	if (N_KIND(node1) ==  as_unread) {
		tup = tup_new1((char *) N_SEQ(node1));
	}
	else {
		tup = tup_new(0);
	}
	if (node2 != (Node)0 && N_KIND(node2) == as_unread) {
		tup = tup_with(tup, (char *) N_SEQ(node2));
	}
	if (tup_size(tup) != 0) {
		unum = N_UNIT(node1);
		retrieve_tree_nodes((IFILE *)0, unum, tup);
	}
}

char *lib_aisname()										/*;lib_aisname*/
{
	int		n, f_num, unit_count;
	char	*tmp_str, temp_str[4];
	char	*aisfilename;
	long	spos;
	IFILE	*ifile;

	/* Get name for next ais file from library. The offset within the
	 * library file is not changed.
	 */
	/* should have last arg nonzero to avoid crash if lib does not exist
	 * and then issue error message
	 */

	LIBFILE = ifopen(LIBFILENAME, "", "r", 0);
	ifile = LIBFILE;
	spos = iftell(ifile); /* get current offset in file */
	unit_count = getnum(ifile, "lib-unit-count");
	n = getnum(ifile, "lib-n");
	empty_unit_slots = getnum(ifile, "lib-empty-slots");
	tmp_str = getstr(ifile, "tmp-str");
	sscanf(tmp_str, "%d", &f_num);
	f_num++;
	sprintf(temp_str, "%d", f_num);
	aisfilename = strjoin(temp_str, "");
	/* restore to entry value of file offset */
	ifseek(ifile, "lib-start", spos, 0);
	return aisfilename;
}

void get_unit_unam(IFILE *ifile, Symbol sym)			/*;get_unit_unam*/
/*  
 * reads the full symbol definitions of the associated symbol field of the
 * unit name symbol. This is needed since when binding is done we want to
 * load the symbols from this field which represent the procedures to 
 * elaborate packages.
 */
{
	int	i;

	for (i = 1;i <= 3; i++)
		getsym(ifile, "ud-assoc-sym");
}
