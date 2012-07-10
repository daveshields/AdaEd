/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/* libw - procedures for writing (in C format) ais and tre files*/

#ifdef __GNUG__
extern "C"
{
#include <sys/types.h>
#include <sys/dir.h>
}
#endif
#include "hdr.h"
#include "vars.h"
#include "libhdr.h"
#include "ifile.h"
#include "setprots.h"
#include "dbxprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "chapprots.h"
#include "libprots.h"
#include "libfprots.h"
#include "libwprots.h"

#ifdef BSD
/* Needed for cleanup_files routine */
#include <sys/types.h>
#include <sys/dir.h>
#endif

#ifdef SYSTEM_V
/* Needed for cleanup_files routine */
#include <fcntl.h>
#include <sys/types.h>
#include <sys/dir.h>
#endif

#ifdef IBM_PC
#include <dos.h>
#include <errno.h>
#endif

extern char *LIBRARY_PREFIX;
extern IFILE *TREFILE, *AISFILE, *STUBFILE, *LIBFILE;

static void putdcl(IFILE *, Declaredmap);
static void putlitmap(IFILE *, Symbol);
static void putnod(IFILE *, char *, Node);
static void putnodref(IFILE *, char *, Node);
static void putint(IFILE *, char *, int );
static void putlong(IFILE *, char *, long);
static void putmisc(IFILE *, Symbol);
static void putrepr(IFILE *, Symbol);
static void putunt(IFILE *, char *, unsigned int);
static void putnval(IFILE *, Node);
static void putuint(IFILE *, char *, int *);
static void putovl(IFILE *, Symbol);
static void putsig(IFILE *, Symbol);
static void putsym(IFILE *, char *, Symbol);
static void putudecl(IFILE *, int);
static long write_next(IFILE *);
static void put_unit_unam(IFILE *, Symbol);

static void putdcl(IFILE *ofile, Declaredmap d)						/*;putdcl*/
{
	Fordeclared fd;
	char	*id;
	Symbol	sym;
	int		i, n = 0;
	typedef struct {
		char *iden;
		short sym_seq;
		short sym_unit;
		short visible;
	}f_dmap_s;
	f_dmap_s ** dptrs;
	f_dmap_s *	filedmap;
	f_dmap_s *	save_filedmap;

	if (d == (Declaredmap)0) {
		putnum(ofile, "putdcl-is-map-defined", 0);
		return;
	}
	putnum(ofile, "putdcl-is-map-defined", 1); /* to indicate map defined */
	n = 0; /* count number of entries where defined */
	FORDECLARED(id, sym, d, fd);
		n += 1;
	ENDFORDECLARED(fd);
	putnum(ofile, "putdcl-number-defined", n);
	if (n == 0) return;
	save_filedmap = filedmap = (f_dmap_s *)
	  ecalloct((unsigned)n, sizeof(f_dmap_s), "put-dcl-save-filedmap");
	dptrs =
	  (f_dmap_s **) emalloct(sizeof(f_dmap_s *) * (unsigned)n, "put-dcl-dptrs");
	n = 0;
	FORDECLARED(id, sym, d, fd);
		n++;  /* number of entries seen so far */
		filedmap->iden = id;
		if (sym == (Symbol) 0)
			filedmap->sym_seq = filedmap->sym_unit = 0;
		else {
			filedmap->sym_seq = S_SEQ(sym);
			filedmap->sym_unit = S_UNIT(sym);
		}
		filedmap->visible = IS_VISIBLE(fd);
		/* now, insert pointer to new record such that ids are sorted 
		 * this is necessary (for debugging only!) to ensure entries appear
		 * in the same order each time the declared map is written
		 */
		i = n-1;
		while ( i > 0 && strcmp(filedmap->iden, dptrs[i-1]->iden) < 0) {
			dptrs[i] = dptrs[i-1];
			i--;
		}
		dptrs[i] = filedmap;
		filedmap++;
	ENDFORDECLARED(fd);

	/* now, write to file */
	for (i = 0; i < n; i++ ) {
		putstr(ofile, "str", dptrs[i]->iden);
		putnum(ofile, "seq", dptrs[i]->sym_seq);
		putnum(ofile, "unt", dptrs[i]->sym_unit);
		putnum(ofile, "vis", dptrs[i]->visible);
	}
	efreet((char *)save_filedmap, "putdcl-save-filedmap");
	efreet((char *) dptrs, "putdcl-dptrs");
}

static void putlitmap(IFILE *ofile, Symbol sym)				/*;putlitmap*/
{
	/* called for na_enum to output literal map.
	 * The literal map is a tuple, entries consisting of string followed
	 * by integer.
	 */

	Tuple	tup;
	int i, n;

	tup = (Tuple) OVERLOADS(sym);
	n = tup_size(tup);
	putnum(ofile, "litmap-n", n);
	for (i = 1; i <= n; i += 2) {
		putstr(ofile, "litmap-str", tup[i]);
		putnum(ofile, "litmap-value", (int) tup[i+1]);
	}
}

static void putnod(IFILE *ofile, char *desc, Node node)				/*;putnod*/
{
	/* Write information for the node to a file (ofile)
	 * Since all the nodes in the tree all have the same N_UNIT value, 
	 * the node can be written to the file in a more compact format.
	 * The N_UNIT of the node itself and of its children (N_AST1...) need not
	 * be written out only their N_SEQ filed needs to be written out. There
	 * is one complication of this scheme. OPT_NODE which is (seq=1,unit=0) will
	 * conflict with (seq=1,unit=X)  of current unit. Therefore, in this case a 
	 * sequence # of -1 will signify OPT_NODE.
	 */

	Tuple	tup;
	Fortup	ft1;
	int 	has_n_list = 0;
	int		nk;
	Node	nod;
	short	fnum[24];
	int		fnums = 0;
	Symbol	sym;

#ifdef DEBUG
	if (trapns>0 && N_SEQ(node) == trapns && N_UNIT(node) == trapnu)trapn(node);
#endif
	/* copy standard info */
	nk = N_KIND(node);
	fnum[fnums++] = nk;
	fnum[fnums++] = N_SEQ(node);
	if (N_LIST_DEFINED(nk)) {
		tup = N_LIST(node);
		if (tup == (Tuple)0) 
			has_n_list = 0;
		else
			has_n_list = 1 + tup_size(tup);
		fnum[fnums++] = has_n_list;
	}
	/* ast fields */
	/* See comment above for description of compact format.*/
	if (N_AST1_DEFINED(nk)) {
		nod = N_AST1(node);
		fnum[fnums++] = (N_UNIT(nod) != 0) ? N_SEQ(nod) : -1;
	}
	if (N_AST2_DEFINED(nk)) {
		nod = N_AST2(node);
		fnum[fnums++] = (N_UNIT(nod) != 0) ? N_SEQ(nod) : -1;
	}
	if (N_AST3_DEFINED(nk)) {
		nod = N_AST3(node);
		fnum[fnums++] = (N_UNIT(nod) != 0) ? N_SEQ(nod) : -1;
	}
	if (N_AST4_DEFINED(nk)) {
		nod = N_AST4(node);
		fnum[fnums++] = (N_UNIT(nod) != 0) ? N_SEQ(nod) : -1;
	}
	/*fnum[fnums++] = N_SIDE(node);*/
	/* N_UNQ only if defined */
	if (N_UNQ_DEFINED(nk))  {
		sym = N_UNQ(node);
		fnum[fnums++] = (sym != (Symbol)0) ? S_SEQ(sym) : 0;
		fnum[fnums++] = (sym != (Symbol)0) ? S_UNIT(sym) : 0;
	}
	if (N_TYPE_DEFINED(nk)) {
		sym = N_TYPE(node);
		fnum[fnums++] = (sym != (Symbol)0) ? S_SEQ(sym) : 0;
		fnum[fnums++] = (sym != (Symbol)0) ? S_UNIT(sym) : 0;
	}
	/* write fnums followed by fnum info as array */

	putnum(ofile, desc, fnums);
	/*fwrite((char *) &fnums, sizeof(short), 1, ofile->fh_file);*/
	fwrite((char *) fnum, sizeof(short), fnums, ofile->fh_file);

	/* write out n_list if needed */
	if (has_n_list>1) {
		tup = N_LIST(node);
		FORTUP(nod = (Node), tup, ft1);
			putnodref(ofile, "n-list-nodref", nod);
		ENDFORTUP(ft1);
	}
	if (N_VAL_DEFINED(nk)) {
		putnval(ofile, node);
	}
}

static void putnodref(IFILE *ofile, char *desc, Node node)		/*;putnodref*/
{
	/* OPT_NODE is node in unit 0 with sequence 1, and needs
	 * no special handling here
	 */

	if (node == (Node)0) {
		putpos(ofile, "nref-seq", 0);
		putunt(ofile, "nref-unt", 0);
	}
	else {
		putpos(ofile, "nref-seq", N_SEQ(node));
		putunt(ofile, "nref-unt", N_UNIT(node));
	}
}

static void putint(IFILE *ofile, char *desc, int n)				/*;putint*/
{
	/* write int to output file */

	int s = n;

	fwrite((char *) &s, sizeof(int), 1, ofile->fh_file);
}

static void putlong(IFILE *ofile, char *desc, long n)				/*;putlong*/
{
	/* write long to output file */

	long s = n;

	fwrite((char *) &s, sizeof(long), 1, ofile->fh_file);
}

static void putmisc(IFILE *ofile, Symbol sym)				/*;putmisc*/
{
	/* write out MISC information if present 
	 * MISC is integer except for package, in which case it is a triple.
	 * The first two components are integers, the last is  a tuple of
	 * symbols
	 */

	int	nat, i, n;
	char   *m;
	Tuple tup;

	nat = NATURE(sym);
	m = MISC(sym);
	if ((nat == na_package || nat == na_package_spec )&& m != (char *)0) {
		tup = (Tuple) m;
		putnum(ofile, "misc-package-1", (int)tup[1]);
		putnum(ofile, "misc-package-2", (int)tup[2]);
		tup = (Tuple) tup[3];
		n = tup_size(tup);
		putnum(ofile, "misc-package-tupsize", n);
		for (i = 1; i <= n; i++)
			putsymref(ofile, "misc-package-symref", (Symbol) tup[i]);
	}
	else if ((nat == na_procedure || nat == na_function) && m != (char *)0) {
		/* misc is tuple. first entry is string, second is symbol */
		tup = (Tuple) m;
		putnum(ofile, "misc-number", (int) tup[1]);
		putsymref(ofile, "misc-symref", (Symbol) tup[2]);
	}
	else {
		putnum(ofile, "misc", (int)m);
	}
}

static void putrepr(IFILE *ofile, Symbol sym)				/*;putrepr*/
{
	/* write out representation  information if present */

	int	i, n;
	Tuple repr_tup, tup4, align_mod_tup, align_tup;
	int		repr_tag, swap_private;
	Fortup	ft1;

    swap_private = FALSE;
	if (is_type(sym) && !(is_generic_type(sym))) {
#ifdef TBSL
	    if (TYPE_OF(sym) == symbol_private ||
            TYPE_OF(sym) == symbol_limited_private) {
 		    vis_decl = private_decls_get((Private_declarations)
                    			         private_decls(SCOPE_OF(sym)), sym);
		   /*
            * Check to seem if vis_decl is defined before swapping it. It 
			* might be undefined in the case of compilation errors.
            */
			if (vis_decl != (Symbol)0) {
				private_decls_swap(sym, vis_decl);
       			swap_private = TRUE;
			}
	    }
#endif
	    repr_tup = REPR(sym);
	    if (repr_tup != (Tuple)0) repr_tag = (int) repr_tup[1]; 	
        if (repr_tup == (Tuple)0) { /* probably error condition */
		   putnum(ofile, "repr-type", -1);
		}
	    else if (repr_tag == TAG_RECORD) {
		    putnum(ofile, "repr-type", repr_tag);
		   	putnum(ofile,"repr-rec-size %d\n", (int) repr_tup[2]);
			align_mod_tup = (Tuple) repr_tup[4];
		   	putnum(ofile,"repr-rec-mod %d\n", (int) align_mod_tup[1]);
			align_tup = (Tuple) align_mod_tup[2];
			putnum(ofile, "repr-align-tup-size", tup_size(align_tup));
			FORTUP (tup4=(Tuple), align_tup, ft1);
				putsymref(ofile,"repr-rec-align-1", (Symbol)tup4[1]);
		    	putnum(ofile,"repr-rec-align-2", (int) tup4[2]);
		    	putnum(ofile,"repr-rec-align-3", (int) tup4[3]);
		    	putnum(ofile,"repr-rec-align-4", (int) tup4[4]);
			ENDFORTUP(ft1);
		}
		else if (repr_tag == TAG_ACCESS || 
				 repr_tag == TAG_TASK) {
		    putnum(ofile, "repr-type", repr_tag);
			putnum(ofile, "repr-size", (int)repr_tup[2]);
			putnodref(ofile, "repr-storage-size", (Node) repr_tup[3]);
		}
		else {
		    putnum(ofile, "repr-type", repr_tag);
			putnum(ofile, "repr-tup-size", (int)repr_tup[0]);
			n = tup_size(repr_tup);
			for (i = 2; i <= n; i++)
				putnum(ofile, "repr-info", (int) repr_tup[i]);
			}
		}
	else {
		putnum(ofile, "repr-type", -1);
	}
#ifdef TBSL
	if (swap_private)
		private_decls_swap(sym, vis_decl);
#endif
}
static void putunt(IFILE *ofile, char *desc, unsigned int n)		/*;putunt*/
{
	/* like putnum, but verifies that argument positive 
	 * and also that it is 'small'. In particular this is used
	 * to guard for absurd unit numbers 
	 */
	/* write integer (as a short) to output file */

	if (n > 200) chaos("putunt: absurd unit number");
	putnum(ofile, desc, (int) n);
}

static void putnval(IFILE *ofile, Node node)					/*;putnval*/
{
	/* write out N_VAL field for node to AISFILE */

	int nk, ck, nv;
	Const	con;
	char	*s;
	char	*inttos();
	Rational	rat;
	Tuple	tup, stup;
	int		i, n;
	int		*ui;
	double	doub;

	nk = N_KIND(node);
	s = N_VAL(node);
	if (nk == as_simple_name || nk == as_int_literal || nk == as_real_literal
	  || nk == as_string_literal || nk == as_character_literal 
	  || nk == as_subprogram_stub_tr || nk == as_package_stub
	  || nk == as_task_stub) {
		putstr(ofile, "nval-name", s);
	}
	else if (nk == as_line_no || nk == as_number || nk == as_predef) {
		putnum(ofile, "nval-int", (int) s);
	}
	else if (nk == as_mode)  {
		/* convert mode, indeed, the inverse of change made in astread*/
		nv = (int) N_VAL(node);
		putnum(ofile, "val-mode", nv);
	}
	else if (nk == as_ivalue ) {
		con = (Const) N_VAL(node);
		ck = con->const_kind;
		putnum(ofile, "nval-const_kind", ck);
		if (ck == CONST_INT)
			putint(ofile, "nval-const-int-value", con->const_value.const_int);
		else if (ck == CONST_REAL) {
			doub = con->const_value.const_real;
			fwrite((char *) &doub, sizeof(double), 1, ofile->fh_file);
		}
		else if (ck == CONST_UINT) {
			ui = con->const_value.const_uint;
			putuint(ofile, "nval-const-uint", ui);
		}
		else if (ck == CONST_OM) {
			; /* no further data needed if OM */
		}
		else if (ck == CONST_RAT) {
			rat = con->const_value.const_rat;
			putuint(ofile, "nval-const-rat-num", rat->rnum);
			putuint(ofile, "nval-const-rat-den", rat->rden);
		}
		else if (ck == CONST_CONSTRAINT_ERROR) {
			chaos("putnval: CONST_CONSTRAINT_ERROR");
		}
	}
	else if (nk == as_terminate_alt) {
		/*: terminate_statement (9)  nval is depth_count (int)*/
		putnum(ofile, "nval-terminate-depth", (int) s);
	}
	else if (nk == as_string_ivalue) {
		/* nval is tuple of integers */
		tup = (Tuple) s;
		n = tup_size(tup);
		putnum(ofile, "nval-string-ivalue-size", n);
		for (i = 1; i <= n; i++) {
			putchr(ofile, "nval-string-ivalue", (int) tup[i]);
		}
	}
	else if (nk == as_instance_tuple) {
		stup = (Tuple) s;
		if (stup != (Tuple)0) {
			n = tup_size(stup);
			if (n != 2)
				chaos("putnval: bad nval for instantiation");
			putnum(ofile, "nval-instance-tupsize", n);
			/* first component is instance map */
			tup = ((Symbolmap)(stup)[1])->symbolmap_tuple;
			n = tup_size(tup);
			putnum(ofile, "nval-symbolmap-size", n);
			for (i = 1; i <= n; i += 2) {
				putsymref(ofile, "symbolmap-1", (Symbol)tup[i]);
				putsymref(ofile, "symbolmap-2", (Symbol)tup[i+1]);
			}
			/* second component is needs_body flag */
			putnum(ofile, "nval-flag", (int)(stup)[2]);
		}
		else putnum(ofile, "nval-instance-empty", 0);
	}
	/* need to handle following cases:
	 * (when do them, update libr and libs as well).
	 *     see also how handled for record_aggregates (gs: as_simple_name nodes
	 * 			now attatched to n_list of as_record_aggregate )
	 * as_pragma: cf. process_pragma (2)
	 * as_array aggregate
	 * Need to review assignments of N_VAL in chapter 12, including:
	 *     as_generic: (cf. 12)
	 *     see subprog_instance (12) where N_VAL set to triple.
	 */
}

static void putuint(IFILE *ofile, char *desc, int *pint)			/*;putuint*/
{
	int n;
	n = pint[0];
	putnum(ofile, "uint-size", n);
	fwrite((char *) pint, sizeof(int), n+1, ofile->fh_file);
}

static void putovl(IFILE *ofile, Symbol sym)					/*;putovl*/
{
	int nat, n;
	Set ovl;
	Forset	fs1;
	Forprivate_decls	fp;
	Private_declarations	pd;
	Symbol	s, s1, s2;

	nat = NATURE(sym);
	ovl = OVERLOADS(sym);

	/* It is the private declarations for na_package and na_package_spec.
	 * (and also na_generic_package_spec)
	 * Otherwise it is a set of symbols:
	 *	na_aggregate  na_entry	na_function  na_function_spec
	 *	na_literal  na_op  na_procedure	 na_procedure_spec
	 */
	if (nat == na_block) {
		/* ignore any overloads info for block - it is for internal use only */
		return;
	}
	if (nat == na_package|| nat == na_package_spec
	  || nat == na_generic_package_spec || nat == na_generic_package
	  || nat == na_task_type || nat == na_task_obj) {
		/* write out private declarations */
		pd = (Private_declarations) ovl;
		n = 0;
		FORPRIVATE_DECLS(s1, s2, pd, fp);
			n += 1;
		ENDFORPRIVATE_DECLS(fp);
		putnum(ofile, "ovl-private-decls-size", n);
		FORPRIVATE_DECLS(s1, s2, pd, fp);
			putsym(ofile, "ovl-pdecl-1-sym", s1);
			putsym(ofile, "ovl-pdecl-2-sym", s2);
		ENDFORPRIVATE_DECLS(fp);
	}
	else if (ovl != (Set)0) {
		putnum(ofile, "ovl-set-size", set_size(ovl));
		FORSET(s = (Symbol), ovl, fs1);
			putsymref(ofile, "ovl-set-symref", s);
		ENDFORSET(fs1);
	}
	else {
		chaos("putovl surprising case!");
	}
}

static void putsig(IFILE *ofile, Symbol sym)				/*;putsig*/
{
	/* The signature field is used as follows:
	 * It is a symbol for:
	 *	na_access
	 * It is a node for
	 *	na_constant  na_in  na_inout
	 * It is also a node (always OPT_NODE) for na_out. For now we write this
	 * out even though it is not used. 
	 * It is a pair for na_array.
	 * It is a triple for na_enum.
	 * It is a triple for na_generic_function_spec na_generic_procedure_spec
	 * The first component is a tuple of pairs, each pair consisting of
	 * a symbol and a (default) node.
	 * The second component is a tuple of symbols.
	 * The third component is a node
	 * It is a tuple with four elements for na_generic_package_spec:
	 * the first is a tuple of pairs, with same for as for generic procedure.
	 * the second third, and fourth components are nodes.
	 * It is a 5-tuple for na_record.
	 * It is a constraint for na_subtype and na_type.
	 * It is a node for na_obj.
	 * Otherwise it is the signature for a procedure, namely a tuple
	 * of quadruples.
	 * Note however, that for a private type, the signature has the same
	 * form as for a record.
	 * For a subtype whose root type is an array, the signature has the
	 * same form as for an array.
	 * For task_type, task_type_spec, it is a tuple of nodes 
	 *  (created by the expander)
	 * For task_body it is a tuple (empty) to make it correspond to procedures.
	 *  (modified in expanded for as_task)
	 */

	int nat, i, n;
	Tuple	sig, tup, tupent;
	Symbol	s, s2;
	Fortup	ft1;

	nat = NATURE(sym);
	sig = SIGNATURE(sym);
	switch (nat) {
	case na_access:
		/* access: signature is designated_type;*/
		putsymref(ofile, "sig-access-symref", (Symbol) sig);
		break;
	case	na_array:
		/* array: signature is pair [i_types, comp_type] where
		 * i_type is tuple of type names
		 */
array_case:
		putnum(ofile, "sig-array-i-types-size", tup_size((Tuple) sig[1]));
		FORTUP(s = (Symbol), (Tuple) sig[1], ft1);
			putsymref(ofile, "sig-array-i-types-type", s);
		ENDFORTUP(ft1);
		putsymref(ofile, "sig-array-comp-type", (Symbol) sig[2]);
		break;
	case	na_block:
		/* block: miscellaneous information */
		/* This information not needed externally*/
		chaos("putsig: signature for block");
		break;
	case	na_constant:
	case	na_in:
	case	na_inout:
	case	na_out:
	case	na_discriminant:
		putnodref(ofile, "sig-discriminant-nodref", (Node) sig);
		break;
	case	na_entry:
	case	na_entry_family:
	case	na_entry_former:
		/* entry: list of symbols */
	case	na_function:
	case	na_function_spec:
	case	na_literal:		/* is this for literals too? */
	case	na_op:
	case	na_procedure:
	case	na_procedure_spec:
	case	na_task_body:
		putnum(ofile, "sig-tuple-size", tup_size(sig));
		FORTUP(s = (Symbol), sig, ft1);
			putsymref(ofile, "sig-tuple-symref", s);
		ENDFORTUP(ft1);
		break;
	case	na_enum:
		/* enum: tuple in form ['range', lo, hi]*/
		/* we write this as two node references*/
		putnodref(ofile, "sig-enum-low-nodref", (Node) sig[2]);
		putnodref(ofile, "sig-enum-high-nodref", (Node) sig[3]);
		break;
	case	na_type:
		/* treat private types way in same way as for records*/
		s = TYPE_OF(sym);
		s2 = TYPE_OF(root_type(sym));
		if ( s == symbol_private || s == symbol_limited_private 
		  || s== symbol_incomplete || s2 == symbol_private 
		  || s2 == symbol_limited_private || s2 == symbol_incomplete
		  || (s != (Symbol)0 && NATURE(s) == na_record)
		    /* derived of private record or record */
		  || (s2 != (Symbol)0 && NATURE(s2) == na_record)) {
			/* derived of derived of ... */
			goto record_case;
		}
		if ((s != (Symbol)0 && NATURE(s) == na_access)
		  || (s2 != (Symbol)0 && NATURE(s2) == na_access)) {
#ifdef TBSL
			putsymref(ofile, "sig-access-symref", (Symbol) sig);
#endif
			putnum(ofile, "sig-type-is-access", 1);
			break;
		}
		else {
			putnum(ofile, "sig-type-is-access", 0);
		}
		n = tup_size(sig);
		putnum(ofile, "sig-type-size", n);
		putnum(ofile, "sig-type-constraint-kind", (int) sig[1]);
		for (i = 2; i <= n; i++)
			putnodref(ofile, "sig-type-nodref", (Node) sig[i]);
		break;
	case na_subtype:
		n = tup_size(sig);
		putnum(ofile, "sig-subtype-size", n);
		if (is_array(sym)) { /* if constrained array */
			putnum(ofile, "sig-constrained-array", CONSTRAINT_ARRAY);
			goto array_case;
		}
		putnum(ofile, "sig-type-constraint-kind", (int) sig[1]);
		if ((int)sig[1] == CONSTRAINT_DISCR) {
			/* discriminant map */
			tup = (Tuple) numeric_constraint_discr(sig);
			n = tup_size(tup);
			putnum(ofile, "sig-constraint-discrmap-size", n);
			for (i = 1; i <= n; i += 2) {
				putsymref(ofile, "sig-constraint-discrmap-symref",
				  (Symbol)tup[i]);
				putnodref(ofile, "sig-constraint-discrmap-nodref",
				  (Node) tup[i+1]);
			}
		}
		else if ((int)sig[1] == CONSTRAINT_ACCESS) {
			putsymref(ofile, "sig-subtype-acc-symref", (Symbol)sig[2]);
		}
		else {
			for (i = 2; i <= n; i++)
				putnodref(ofile, "sig-subtype-nodref", (Node) sig[i]);
		}
		break;
	case	na_generic_function:
	case	na_generic_procedure:
	case	na_generic_function_spec:
	case	na_generic_procedure_spec:
		if (tup_size(sig) != 4)
			chaos("putsig: bad signature for na_generic_procedure_spec");
		/* tuple count known to be four, just put elements */
		tup = (Tuple) sig[1];
		/* the first component is a tuple of pairs, just write count
		 * and the values of the successive pairs 
		 */
		n = tup_size(tup);
		putnum(ofile, "sig-generic-size", n);
		for (i = 1; i <= n; i++) {
			tupent = (Tuple) tup[i];
			putsymref(ofile, "sig-generic-symref", (Symbol) tupent[1]);
			putnodref(ofile, "sig-generic-nodref", (Node) tupent[2]);
		}
		tup = (Tuple) sig[2];
		n = tup_size(tup); /* symbol list */
		putnum(ofile, "sig-generic-tup-size", n);
		for (i = 1; i <= n; i++)
			putsymref(ofile, "sig-generic-symbol-symref", (Symbol) tup[i]);
		putnodref(ofile, "sig-generic-3-nodref", (Node) sig[3]);
		/* the fourth component is tuple of symbols */
		tup = (Tuple) sig[4];
		n = tup_size(tup);
		putnum(ofile, "sig-generic-contrain-size", n);
		for (i = 1; i <= n; i++)
			putsymref(ofile, "sig-generic-symref", (Symbol)tup[i]);
		break;
	case	na_generic_package_spec:
	case	na_generic_package:
		/* signature is tuple with five elements */
		if (tup_size(sig) != 5)
			chaos("putsig: bad signature for na_generic_package_spec");
		tup = (Tuple) sig[1];
		/* the first component is a tuple of pairs, just write count
		 * and the values of the successive pairs 
		 */
		n = tup_size(tup);
		putnum(ofile, "sig-generic-tup-size", n);
		for (i = 1; i <= n; i++) {
			tupent = (Tuple) tup[i];
			putsymref(ofile, "sig-generic-symref", (Symbol) tupent[1]);
			putnodref(ofile, "sig-generic-nodref", (Node) tupent[2]);
		}
		/* the second third, and fourth components are just nodes */
		putnodref(ofile, "sig-generic-node-2", (Node) sig[2]);
		putnodref(ofile, "sig-generic-node-3", (Node) sig[3]);
		putnodref(ofile, "sig-generic-node-4", (Node) sig[4]);
		/* the fifth component is tuple of symbols */
		tup = (Tuple) sig[5];
		n = tup_size(tup);
		putnum(ofile, "sig-generic-contrain-size", n);
		for (i = 1; i <= n; i++)
			putsymref(ofile, "sig-generic-symref", (Symbol)tup[i]);
		break;
	case	na_record:
		/* the signature is tuple with five components:
		 * [node, node, tuple of symbols, declaredmap, node]
		 * NOTE: we do not write component count - 5 assumed 
		 */
record_case:
		putnodref(ofile, "sig-record-1-nodref", (Node) sig[1]);
		putnodref(ofile, "sig-record-2-nodref", (Node) sig[2]);
		tup = (Tuple) sig[3];
		n = tup_size(tup);
		putnum(ofile, "sig-record-3-size", n);
		for (i = 1; i <= n; i++)
			putsymref(ofile, "sig-record-3-symref", (Symbol) tup[i]);
		putdcl(ofile, (Declaredmap) sig[4]);
		putnodref(ofile, "sig-record-5-nodref", (Node) sig[5]);
		break;
	case	na_void:
		/* special case assume entry for $used, in which case is tuple
		 * of symbols
		 */
		if (streq(ORIG_NAME(sym), "$used") ) {
			n = tup_size(sig);
			putnum(ofile, "sig-$used-size", n);
			for (i = 1; i <= n; i++)
				putsymref(ofile, "sig-$used-symref", (Symbol) sig[i]);
		}
		else {
#ifdef DEBUG
			zpsym(sym);
#endif
			chaos("putsig: na_void, not $used");
		}
		break;
	case	na_obj:
		putnodref(ofile, "sig-obj-nodref", (Node) sig);
		break;
	case na_task_type:
	case na_task_type_spec:
		/* a tuple of nodes */
		n = tup_size(sig);
		putnum(ofile, "task-type-spec-size", n);
		for (i = 1; i <= n; i++)
			putnodref(ofile, "sig-task-nodref", (Node)sig[i]);
		break;
	default:
#ifdef DEBUG
		printf("putsig: default error\n");
		zpsym(sym);
#endif
		chaos("putsig: default");
	}
}

static void putsym(IFILE *ofile, char *desc, Symbol sym)			/*;putsym*/
{
	/* write description for symbol sym to output file */

	struct f_symbol_s fs;
	int nat;
	Tuple	sig, tup;
	Set 	set;
	Symbol	s, s2;
	Fortup	ft1;

	nat = NATURE(sym);
#ifdef DEBUG
	if (trapss>0 && S_SEQ(sym) == trapss && S_UNIT(sym) == trapsu) traps(sym);
#endif
	fs.f_symbol_nature = nat;
	fs.f_symbol_seq = S_SEQ(sym);
	fs.f_symbol_unit = S_UNIT(sym);
	s = TYPE_OF(sym);
	if (s == (Symbol)0) {
		fs.f_symbol_type_of_seq = 0;
		fs.f_symbol_type_of_unit = 0;
	}
	else {
		fs.f_symbol_type_of_seq = S_SEQ(s);
		fs.f_symbol_type_of_unit = S_UNIT(s);
	}
	sig = SIGNATURE(sym);
	if (sig == (Tuple)0) {
		fs.f_symbol_signature = 0;
	}
	else {
		/* signature field not relevant for na_block externally */
		fs.f_symbol_signature = 1;
		if (nat == na_block) fs.f_symbol_signature = 0;
	}
	s = SCOPE_OF(sym);
	if (s == (Symbol)0) {
		fs.f_symbol_scope_of_seq = 0;
		fs.f_symbol_scope_of_unit = 0;
	}
	else {
		fs.f_symbol_scope_of_seq = S_SEQ(s);
		fs.f_symbol_scope_of_unit = S_UNIT(s);
	}
	s = ALIAS(sym);
	if (s == (Symbol)0) {
		fs.f_symbol_alias_seq = 0;
		fs.f_symbol_alias_unit = 0;
	}
	else {
		fs.f_symbol_alias_seq = S_SEQ(s);
		fs.f_symbol_alias_unit = S_UNIT(s);
	}
	set = OVERLOADS(sym);
	if (set == (Set)0) {
		fs.f_symbol_overloads = 0;
	}
	else {
		fs.f_symbol_overloads = 1;
		if (nat == na_block) fs.f_symbol_overloads = 0;
	}
	if (DECLARED(sym) != (Declaredmap)0) {
		fs.f_symbol_declared = 1;
	}
	else {
		fs.f_symbol_declared = 0;
	}
	fs.f_symbol_type_attr = TYPE_ATTR(sym);
	s = TYPE_OF(sym);
	if (NATURE(sym) == na_type ) {
		s2 = TYPE_OF(root_type(sym));
		if (s == symbol_private || s == symbol_limited_private 
		  || s == symbol_incomplete || s2 == symbol_private 
		  || s2 == symbol_limited_private || s2 == symbol_incomplete
		  /* I think the following test is true in case of derived of record 
		   * and therefore that the code is wrong. JC
		   */
		  || (s != (Symbol)0 && NATURE(s) == na_record)
		  /* derived of private record or record */
		  || (s2 != (Symbol)0 && NATURE(s2) == na_record)) {
			/* derived of derived of ... */
			fs.f_symbol_type_attr |= TA_ISPRIVATE;
		}
	}
	/* The following fields are for use by the code generator only */
	fs.f_symbol_misc = (MISC(sym) != (char *)0);
	fs.f_symbol_type_kind = TYPE_KIND(sym);
	fs.f_symbol_type_size = TYPE_SIZE(sym);
	s = INIT_PROC(sym);
	if (s == (Symbol)0) {
		fs.f_symbol_init_proc_seq = 0;
		fs.f_symbol_init_proc_unit = 0;
	}
	else if (!is_type(sym)) {
		/* case of formal_decl_tree for subprogram specs */
		fs.f_symbol_init_proc_seq = N_SEQ((Node)s);
		fs.f_symbol_init_proc_unit = N_UNIT((Node)s);
	}
	else {
		fs.f_symbol_init_proc_seq = S_SEQ(s);
		fs.f_symbol_init_proc_unit = S_UNIT(s);
	}
	tup = ASSOCIATED_SYMBOLS(sym);
	if (tup == (Tuple)0) {
		fs.f_symbol_assoc_list = 0;
	}
	else {
		if (nat == na_in || nat == na_out || nat == na_inout) {
			/* avoid writing associated symbols for functions and subprograms
    		 * as these need not be written  ds 9-aug-85
    		 */
			fs.f_symbol_assoc_list = 0;
		}
		else {
			fs.f_symbol_assoc_list = 1 + tup_size(tup);
		}
	}
	fs.f_symbol_s_segment = S_SEGMENT(sym);
	fs.f_symbol_s_offset = S_OFFSET(sym);

	fwrite((char *) &fs, sizeof(f_symbol_s), 1, ofile->fh_file);
	putstr(ofile, "orig-name", ORIG_NAME(sym));
	/* process overloads separately due to variety of cases */
	/* treat na_enum case separately */
	if (fs.f_symbol_overloads) {
		if(fs.f_symbol_nature == na_enum)
			putlitmap(ofile, sym);
		else
			putovl(ofile, sym);
	}
	if (fs.f_symbol_declared)
		putdcl(ofile, DECLARED(sym));
	/* signature */
	if (fs.f_symbol_signature)
		putsig(ofile, sym);

	putmisc(ofile, sym);

	/* write out associated symbols of necessary */
	if (fs.f_symbol_assoc_list > 1) {
		tup = ASSOCIATED_SYMBOLS(sym);
		FORTUP(s = (Symbol), tup, ft1)
		    putsymref(ofile, "assoc-symbol-symref", s);
		ENDFORTUP(ft1);
	}
	putrepr(ofile, sym);
}

void putsymref(IFILE *ofile, char *desc, Symbol sym)		/*;putsymref*/
{
	if (sym == (Symbol)0) {
		putpos(ofile, "symref-seq", 0);
		putpos(ofile, "symref-unt", 0);
	}
	else {
#ifdef DEBUG
		if(trapss>0 && trapss == S_SEQ(sym) && trapsu == S_UNIT(sym))traps(sym);
#endif
		putpos(ofile, "symref-seq", S_SEQ(sym));
		putpos(ofile, "symref-unt", S_UNIT(sym));
	}
}

static void putudecl(IFILE *ofile, int ui)						/*;putudecl*/
{
	int i, n, cn, ci;
	Tuple	tup, cent, ctup, cntup;
	Unitdecl	ud;

	ud = (Unitdecl) pUnits[ui]->aisInfo.unitDecl;
	putsym(ofile, "ud-unam", ud->ud_unam);
	put_unit_unam(ofile, ud->ud_unam);
	/* context */
	ctup = (Tuple) ud->ud_context;
	if (ctup == (Tuple)0)
		n = 0;
	else
		n = tup_size(ctup)+1;
	putnum(ofile, "decl-context-size", n);
	if (n > 1) {
		n -= 1;
		for (i = 1; i <= n; i++) {
			cent = (Tuple) ctup[i];
			putnum(ofile, "decl-ctup-1", (int) cent[1]);
			cntup = (Tuple) cent[2]; /* 2nd component is tuple of strings */
			cn = tup_size(cntup);
			putnum(ofile, "decl-cntup-size", cn);
			for (ci = 1; ci <= cn; ci++)
				putstr(ofile, "decl-tupstr-str", cntup[ci]);
		}
	}
	/* unit_nodes */
	tup = ud->ud_nodes;
	n = tup_size(tup);
	putnum(ofile, "decl-ud-nodes-size", n);
	for (i = 1; i <= n; i++) {
		putnodref(ofile, "decl-nodref", (Node) tup[i]);
	}
	/* tuple of symbol table pointers */
	tup = ud->ud_symbols;
	if (tup == (Tuple)0)
		n = 0;
	else
		n = tup_size(tup)+1;
	putnum(ofile, "decl-symbol-tuple-size", n);
	if (n>1) {
		n -= 1;
		for (i = 1; i <= n; i++) {
			/*putsymref(ofile, tup[i]);*/
			/* write full symbol def */
			putsym(ofile, "decl-symref", (Symbol) tup[i]);
		}
	}

	/* decscopes - tuple of scopes */
	tup = ud->ud_decscopes;
	if (tup == (Tuple)0)
		n = 0;
	else
		n = tup_size(tup)+1;
	putnum(ofile, "decl-descopes-size", n);
	if (n > 1) {
		n -= 1;
		for (i = 1; i <= n; i++) {
			putsym(ofile, "decl-descopes-symref", (Symbol) tup[i]);
		}
	}
	/* decmaps - tuple of declared maps */
	tup = ud->ud_decmaps;
	if (tup == (Tuple)0)
		n = 0;
	else
		n = tup_size(tup)+1;
	putnum(ofile, "decmaps-tuple-size", n);
	if (n>1) {
		n -= 1;
		for (i = 1; i <= n; i++)
			putdcl(ofile, (Declaredmap) tup[i]);
	}
	/* oldvis - tuple of unit names */
	tup = ud->ud_oldvis;
	if (tup == (Tuple)0)
		n = 0;
	else
		n = tup_size(tup)+1;
	putnum(ofile, "vis", n);
	if (n>1) {
		n -= 1;
		for (i = 1; i <= n; i++) {
			putstr(ofile, "vis-str", tup[i]);
		}
	}
	return;
}

long write_ais(int ui)										/*;write_ais*/
{
	/* Writes information from the current compilation to
	 * 'file', restructuring the separate compilation maps
	 * to improve the readability of the AIS code.
	 */

	int 	i, n, symbols, is_main;
	long	begpos, genoff, endpos;
	Tuple	tup;
	Set		set;
	Forset	fs1;
	IFILE	*ofile;
	struct unit *pUnit = pUnits[ui];

	ofile = AISFILE;
	begpos = write_next(ofile); /* start record*/
	putstr(ofile, "unit-name", pUnit->name); /* unit name */
	putnum(ofile, "unit-number", ui); /* unit number */
	genoff = iftell(ofile);
	/* offset to code generator information */
	putlong(ofile, "code-gen-offset", 0L);
	is_main = streq(unit_name_type(pUnit->name), "ma");
	if (!is_main) {
		putnum(ofile, "seq-symbol-n", seq_symbol_n);
		/* write out the number of tree node for this unit */
		putnum(ofile, "seq-node-n", seq_node_n);
		symbols = seq_symbol_n;
		pUnit->aisInfo.numberSymbols = symbols;

		/* ELABORATE PRAGMA INFO */
		tup = (Tuple) pUnit->aisInfo.pragmaElab;
		n = tup_size(tup);
		putnum(ofile, "pragma-info-size", n);
		for (i = 1; i <= n; i++)
			putstr(ofile, "pragma-str", tup[i]);		/* pragma info*/
		/* UNIT_DECL */
		putudecl(ofile, ui);
		/* now write out info for each symbol in compilation unit.
		 * perhaps we need write out only those referenced in prior
		 * items read in, but for now we write out all for sake of
		 * completeness and to assist debugging	 (ds 19-oct-84)
		 */
		/* PRE_COMP */
		set = (Set) pUnit->aisInfo.preComp; /* pre_comp info*/
		n = set_size(set);
		putnum(ofile, "precomp-size", n);
		FORSET(n = (int), set, fs1);
			putnum(ofile, "precomp-value", n);
		ENDFORSET(fs1);
		ifseek(ofile, "seek-to-end", 0l, 2); /* position back at end*/
		tup = tup_new(symbols);
		for (i = 1; i <= symbols; i++)
			tup[i] = (char *) seq_symbol[i];
		pUnit->aisInfo.symbols = (char *) tup;
	}
	endpos = iftell(ofile); /* get current offset (end of sem info) */
	/* position to word to get end offset */
	ifseek(ofile, "seek-to-gen-offset", genoff, 0);
	putlong(ofile, "end-pos", endpos);
	ifseek(ofile, "seek-to-end", 0L, 2); /* move back to end of file */
	write_end(ofile, begpos);
	return begpos;
}

void write_stub(Stubenv ev, char *stub_name, char *ext)			/*;write_stub*/
{
	/* Writes information from the stub environment for stub si to the end of
	 * STUBFILE. 
	 * First open STUBFILE if this is first stub and therefore STUBFILE is not 
	 * opened yet. The file extension ext is st1 for semantics phase and st2 for
	 * the code generator phase.
	 */

	int		i, j, k, n, m;
	long	begpos;
	Tuple	tup, tup2, tup3;
	int		cn, ci;
	Tuple	cent, cntup;
	IFILE	*ofile;

	if (STUBFILE == (IFILE *)0)
		STUBFILE = ifopen(AISFILENAME, ext, "w", 0);
	ofile = STUBFILE;
	begpos = write_next(ofile); /* start record*/
	putstr(ofile, "stub-name", stub_name); /* stub name */

	/* SCOPE STACKS */
	tup = (Tuple) ev->ev_scope_st;
	n = tup_size(tup);
	putnum(ofile, "scope-stack-size", n);
	for (i = 1; i <= n; i++) {
		tup2 = (Tuple) tup[i];
		putsymref(ofile, "scope-stack-symref", (Symbol) tup2[1]);
		for (j = 2; j <= 4; j++) {
			tup3 = (Tuple) tup2[j];
			m = tup_size(tup3);
			putnum(ofile, "scope-stack-m", m);
			for (k = 1; k <= m; k++)
				putsymref(ofile, "scope-stack-m-symref", (Symbol) tup3[k]);
		}
	}
	putsymref(ofile, "ev-unit-name-symref", ev->ev_unit_unam);
	putdcl(ofile, ev->ev_decmap);

	/* unit_nodes */
	tup = ev->ev_nodes;
	n = tup_size(tup);
	putnum(ofile, "ev-nodes-size", n);
	for (i = 1; i <= n; i++) {
		putnodref(ofile, "ev-nodes-nodref", (Node) tup[i]);
	}

	/* context */
	tup = (Tuple) ev->ev_context;
	if (tup == (Tuple)0)
		n = 0;
	else
		n = tup_size(tup)+1;
	putnum(ofile, "stub-context-size", n);
	if (n>1) {
		n -= 1;
		for (i = 1; i <= n; i++) {
			cent = (Tuple) tup[i];
			putnum(ofile, "stub-cent-1", (int) cent[1]);
			cntup = (Tuple) cent[2]; /* 2nd component is tuple of strings */
			cn = tup_size(cntup);
			putnum(ofile, "stub-cent-2-size", cn);
			for (ci = 1; ci <= cn; ci++)
				putstr(ofile, "stub-cent-2-str", cntup[ci]);
		}
	}
	/* tuple of symbol table pointers */
	tup = ev->ev_open_decls;
	if (tup == (Tuple)0)
		n = 0;
	else
		n = tup_size(tup)+1;
	putnum(ofile, "ev-decls-ref-size", n);
	/* write symbol table references so that they can be read by routine 
	 * read_stub_short bypassing reading of full symbol definitions 
	 */
	if (n>1) {
		n -= 1;
		for (i = 1; i <= n; i++) {
			/* write symbol ref */
			putsymref(ofile, "decls-ref", (Symbol) tup[i]);
		}
	}
	/* tuple of symbol table pointers */
	tup = ev->ev_open_decls;
	if (tup == (Tuple)0)
		n = 0;
	else
		n = tup_size(tup)+1;
	putnum(ofile, "ev-open-decls-size", n);
	if (n>1) {
		n -= 1;
		for (i = 1; i <= n; i++) {
			/*putsymref(ofile, tup[i]);*/
			/* write full symbol def */
			putsym(ofile, "open-decls-sym", (Symbol) tup[i]);
		}
	}
	putnum(ofile, "stub-current-level", ev->ev_current_level);
	tup = (Tuple) ev->ev_relay_set;
	if (tup == (Tuple)0)
		n = 0;
	else
		n = tup_size(tup)+1;
	putnum(ofile, "ev-stub-relay_set-size", n);
	if (n>1) {
		n -= 1;
		for (i = 1; i <= n; i++) {
			putsymref(ofile, "relay_set_sym", (Symbol) tup[i]);
			/* write ref to symbol  */
		}
	}
	tup = (Tuple) ev->ev_dangling_relay_set;
	if (tup == (Tuple)0)
		n = 0;
	else
		n = tup_size(tup)+1;
	putnum(ofile, "ev-dangling_relay_set-size", n);
	if (n>1) {
		n -= 1;
		for (i = 1; i <= n; i++) {
			putnum(ofile, "dangl_relay_ent", (int) tup[i]);
		}
	}
	write_end(ofile, begpos);
}

void write_tre(int uindex, int rootseq, char *reach)			/*;write_tre*/
/* rootseq - sequence number of root node*/
/* uindex - unit number */
{
	long	*rara, dpos;
	int i, nodes;
	Node	node;
	Tuple	tup;
	long	begpos;
	IFILE	*ofile;
	struct unit *pUnit = pUnits[uindex];

	nodes = seq_node_n;
	/* save position of start of data */
	/* write out all nodes if reach is null ptr */
	ofile = TREFILE;
	begpos = write_next(ofile);
	putstr(ofile, "unit-name", pUnit->name); /* unit name */
	putnum(ofile, "unit-number", uindex); /* unit number */
	putnum(ofile, "node-count", nodes);
	pUnit->treInfo.nodeCount = nodes;
	/* allocate space for node directory and write to file, saving position*/
	rara = (long *)ecalloct((unsigned) nodes+1, sizeof(long), "write-tre-rara");
	dpos = iftell(ofile);
	fwrite((char *) rara, sizeof(long), nodes+1, ofile->fh_file);
	putnum(ofile, "root-seq", rootseq);
	for (i = 1; i <= nodes; i++) {
		if (reach != (char *) 0 && reach[i] != '1') continue;
		node = (Node) seq_node[i];
		if (node == (Node)0) continue; /* do not write null nodes */
		rara[i] = iftell(ofile);
		putnod(ofile, "unit-node", node);
	}
	/* rewrite node list now that available */
	ifseek(ofile, "seek-node-list", dpos, 0);
	fwrite((char *) rara, sizeof(long), nodes+1, ofile->fh_file);
	ifseek(ofile, "seek-to-end", 0l, 2); /* position back at end*/
	/* ????? pUnit->treInfo.tupleAllocated = (char *) rara; */
	/* save address of node list */
	tup = tup_new(nodes);
	for (i = 1; i <= nodes; i++)
		tup[i] = (char *) seq_node[i];
	pUnit->treInfo.tableAllocated = (char *) tup;
	write_end(ofile, begpos);
}

static long write_next(IFILE *ofile)							/*;write_next*/
{
	long	startpos;
	ifseek(ofile, "write-next-seek-to-end", 0L, 2); /* move to end of file */
	startpos = iftell(ofile); /* note position */
	putlong(ofile, "start-next-unit", startpos);
	return startpos;
}

void write_end(IFILE *ofile, long startpos)			/*;write_end*/
{
	long pos;

	ifseek(ofile, "write-end-seek-to-end", 0L, 2); /*move to end of file */
	pos = iftell(ofile); /* get offset of end of file*/
	ofile->fh_units_end = pos;
	/* move to start of pointer word */
	ifseek(ofile, "write-end-seek-pointer", startpos, 0);
	/* update pointer to next record */
	putlong(ofile, "write-end-next-unit", pos);
	ifseek(ofile, "write-end-seek-to-end", 0L, 2); /* move to end of file */
}

static void put_unit_unam(IFILE *ofile, Symbol sym)			/*;put_unit_unam*/
{
	/*  
	 * Write the full symbol definitions of the associated symbol field of the
	 * unit name symbol. This is needed since when binding is done we want to
	 * load the symbols from this field which represent the procedures to 
	 * elaborate packages. If a filed entry is undefined we write out the
	 * definition of the OPT_NAME symbol so that we always have 3 entries.
	 */

	Tuple	tup;
	int	i;

	tup = ASSOCIATED_SYMBOLS(sym);
	if (tup == (Tuple)0) tup = tup_new(3);
	for (i = 1; i <= 3; i++) {
		if (tup[i] != (char *)0) putsym(ofile, "ud-assoc-sym", (Symbol)tup[i]);
		else putsym(ofile, "ud-assoc-sym", OPT_NAME);
	}
}

void cleanup_files()										/*;cleanup_files*/
{
	/* This procedure removes all files in the library that are not
	 * attached to currently active compilation units.
	 */
#ifdef BSD
	DIR *dirp;
	struct direct *dp;
#endif

#ifdef SYSTEM_V
	register int	fd;
	struct direct	entry;
#endif 

#ifdef IBM_PC
	char *emalloc();
	char *strjoin();
	char *dname;
	struct find_t dos_fileinfo;
#endif

	char *s1,*s2;
	int  unit;
	Tuple active_files;

	/* create a list of active files (those for which there is at least
	 * one non-obsolete unit in it.)
	 */
	active_files = tup_new1(FILENAME);

	for (unit = 1; unit <= unit_numbers; unit++) {
		struct unit *pUnit = pUnits[unit];
   		if (streq(pUnit->libInfo.obsolete, "ok")) {
 			if (!tup_memstr(pUnit->libInfo.fname, active_files)) {
				active_files = tup_with(active_files, pUnit->libInfo.fname);
			}
 		}
	}

#ifdef BSD
	dirp = opendir(LIBRARY_PREFIX);
	/* Loop through the directory and remove any files of the form #.* if
	 * # is not an active file.
	 */
	for (dp = readdir(dirp); dp != NULL; dp = readdir(dirp)) {
   		s1 = strjoin(dp->d_name,"");
   		s2 = strchr(s1,'.');
   		if (s2 == (char *)0) s2 = s1;
   		*s2 = '\0';
   		/* ignore files that don't have a dot in it. */
   		if (!strlen(s1)) continue;
   		/* only consider of files of the form xxx.yyy where yyy is one of the 
   		 * Ada/Ed extensions 
   		 */
   		s2++; /* file extension */
   		if ((streq(s2,"trc")|| streq(s2,"axq") || streq(s2,"st1")
		  || streq(s2,"st2") || streq(s2,"exe"))
		  && !tup_memstr(s1, active_files)) {
      		ifdelete(dp->d_name);
   		}
	}

	/* remove the current aic file */
	ifdelete(strjoin(AISFILENAME,".aic"));

#endif
#ifdef SYSTEM_V
	fd = open(LIBRARY_PREFIX,O_RDONLY);
	/* Loop through the directory and remove any files of the form #.* if
	 * # is not an active file.
	 */
	while (read(fd,&entry,sizeof(entry)) > 0) {
   		if (entry.d_ino == 0) continue;
   		s1 = strjoin(entry.d_name, "");
   		s2 = strchr(s1,'.');
   		if (s2 == (char *)0) s2 = s1;
   		*s2 = '\0';
   		/* ignore files that don't have a dot in it. */
   		if (!strlen(s1)) continue;
   		/* only consider of files of the form xxx.yyy where yyy is one of the 
   		 * Ada/Ed extensions 
   		 */
   		s2++; /* file extension */
   		if ((streq(s2, "trc")|| streq(s2, "axq") || streq(s2, "st1")
		  || streq(s2, "st2")) && !tup_memstr(s1, active_files)) {
      		ifdelete(entry.d_name);
   		}
	}

	/* remove the current aic file */
	ifdelete(strjoin(AISFILENAME, ".aic"));
#endif
#ifdef IBM_PC
	/* Loop through the directory and remove any files of the form #.* if
	 * # is not an active file.
	 */
	errno = 0;

	dname = emalloc(strlen(LIBRARY_PREFIX) + 5);
	strcpy(dname, LIBRARY_PREFIX);
	strcat(dname,"\\*.*");
	for (_dos_findfirst(dname, _A_NORMAL, &dos_fileinfo);;
	  _dos_findnext(&dos_fileinfo)) {
    	if (errno) break;
    	s1 = strjoin(dos_fileinfo.name, "");
    	s2 = strchr(s1, '.');
    	if (s2 == (char *)0) s2 = s1;
    	*s2 = '\0';
    	/* ignore files that don't have a dot in it. */
    	if (!strlen(s1)) continue;
    	/* only consider of files of the form xxx.yyy where yyy is one of the 
    	 * Ada/Ed extensions 
    	 */
    	s2++; /* file extension */
    	/* On PC, directory folds file names to upper case */
    	if ((streq(s2, "TRC")|| streq(s2, "AXQ") ||streq(s2, "ST1")
		  || streq(s2, "ST2")) && !tup_memstr(s1, active_files)) {
        	ifdelete(dos_fileinfo.name);
    	}
	}

	/* remove the current aic file */
	ifdelete(strjoin(AISFILENAME, ".AIC"));
#endif
}

void ifdelete(char *fname)										/*;ifdelete*/
{
	char *tname;

	/* allow room for library prefix, file name and suffix */
	tname = emalloc((unsigned) (strlen(LIBRARY_PREFIX) + strlen(fname) + 3));
	if (strlen(LIBRARY_PREFIX)) { /* prepend library prefix if present */
		strcpy(tname, LIBRARY_PREFIX);
#ifdef IBM_PC
		strcat(tname, "\\");
#endif
#ifdef BSD
		strcat(tname, "/");
#endif
#ifdef SYSTEM_V
		strcat(tname, "/");
#endif
		strcat(tname, fname);
	}
	else {
		strcpy(tname, fname); /* copy name if no prefix */
	}
#ifdef BSD
	unlink(tname);
#endif
#ifdef SYSTEM_V
	unlink(tname);
#endif
#ifdef IBM_PC
	unlink(tname);
#endif
	efree(tname);
}
