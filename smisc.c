/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include "hdr.h"
#include "vars.h"
#include "setprots.h"
#include "dbxprots.h"
#include "arithprots.h"
#include "chapprots.h"
#include "dclmapprots.h"
#include "miscprots.h"
#include "smiscprots.h"

/* smisc.c: miscellaneous sem procedures needing semhdr.h */
/* 
 * 23-sep-85	ds
 * add ast_clear to clear defined ast fields before resetting N_KIND.
 *
 * 11-jul-86    ACD
 * modified the DEFINED fields for length clauses.  Previously only
 * N_AST1 was recognized as being defined.  Now, both N_AST1 (the 
 * attribute node) and N_AST2 ( the expression) are recognized
 *
 * 16-apr-85	ds
 * add procedures fordeclared_1 and fordeclared_2. These are used to
 * initialize and advance iteration over declared maps, and are 
 * introduced to reduce the size of the FORDECLARED macro.
 *
 * 24-dec-84	ds
 * have dcl_put NOT set visibility by default.
 *
 * 07-nov-84	ds
 * have node_new_noseq set spans info.
 * add spans_copy(new, old) to copy spans information from node old
 * to node new.
 *
 * 04-nov-84	ds
 * move undone() here as undone.c no longer needed.
 *
 * 02-nov-84	ds
 * add attribute_str to return attribute name based on attribute
 * code in N_VAL field of attribute node.
 *
 * 22-oct-84	ds
 * add dcl_put_vis to enter with explicit visibility indication.
 *
 * 12-oct-84	ds
 * merge in procedures formerly in dcl.c
 */

static int const_cmp_kind(Const, Const);

void ast_clear(Node node)									/*;ast_clear*/
{
	int nk = N_KIND(node);
	if (N_AST2_DEFINED(nk)) N_AST2(node) = (Node) 0;
	if (N_AST3_DEFINED(nk)) N_AST3(node) = (Node) 0;
	if (N_AST4_DEFINED(nk)) N_AST4(node) = (Node) 0;
}

Const const_new(int k)										/*;const_new*/
{
	Const	result;

	result = (Const) smalloc(sizeof(Const_s));
	result->const_kind = k;
	result->const_value.const_int = 0; /* reasonable default value */
	return result;
}

Const int_const(int x)									/*;int_const*/
{
	Const	result;

	result = const_new(CONST_INT);
	result->const_value.const_int = x;
	return result;
}

Const fixed_const(long x)								/*;fixed_const*/
{
	Const	result;
	result = const_new(CONST_FIXED);
	result->const_value.const_fixed = x;
	return result;
}

Const uint_const(int *x)								/*;uint_const*/
{
	Const	result;

	if (x == (int *)0) result = const_new(CONST_OM);
	else {
		result = const_new(CONST_UINT);
		result->const_value.const_uint = x;
	}
	return result;
}

Const real_const(double x)								/*;real_const*/
{
	Const	result;

	result = const_new(CONST_REAL);
	result->const_value.const_real = x;
	return result;
}

Const rat_const(Rational x)								/*;rat_const*/
{
	Const	result;

	if (x == (Rational)0) result =  const_new(CONST_OM);
	else {
		result = const_new(CONST_RAT);
		result->const_value.const_rat = x;
	}
	return result;
}

/* Comparison functions for ivalues (Const's) */

int const_eq(Const const1, Const const2)				/*;const_eq*/
{
	/* checks to see if 2 Consts have the same value */

	switch (const_cmp_kind(const1, const2)) {
	case CONST_OM:
	case CONST_CONSTRAINT_ERROR:
		return TRUE;
	case CONST_INT:
		return (INTV(const1) == INTV(const2));
	case CONST_FIXED:
		return (FIXEDV(const1) == FIXEDV(const2));
	case CONST_UINT:
		return int_eql(UINTV(const1), UINTV(const2));
	case CONST_REAL:
		return (RATV(const1) == RATV(const2));
	case CONST_RAT:
		return rat_eql(RATV(const1), RATV(const2));
	case CONST_STR:
		return streq(const1->const_value.const_str,
		  const2->const_value.const_str);
	default:
		return const_cmp_undef(const1, const2);
	}
}

int const_ne(Const cleft, Const cright)						/*;const_ne*/
{
	return !const_eq(cleft, cright);
}

int const_lt(Const cleft, Const cright)						/*;const_lt*/
{
	switch (const_cmp_kind(cleft, cright)) {
	case CONST_INT :
		return (INTV(cleft)<INTV(cright));
	case CONST_UINT :
		return int_lss(UINTV(cleft), UINTV(cright));
	case CONST_FIXED :
		return (FIXEDV(cleft)<FIXEDV(cright));
	case CONST_RAT :
		return rat_lss(RATV(cleft), RATV(cright));
	case CONST_REAL :
		return  REALV(cleft) < REALV(cright);
	default :
		const_cmp_undef(cleft, cright);
		return 0;
	}
}

int const_le(Const cleft, Const cright)						/*;const_le*/
{
	return (const_eq(cleft, cright) || const_lt(cleft, cright));
}

int const_gt(Const cleft, Const cright)						/*;const_gt*/
{
	return const_lt(cright, cleft);
}

int const_ge(Const cleft, Const cright)						/*;const_ge*/
{
	return const_eq(cleft, cright) || const_lt(cright, cleft);
}

static int const_cmp_kind(Const cleft, Const cright)		/*;const_cmp_kind*/
{
	int		ckind;

	ckind = cleft->const_kind;
	if (ckind == CONST_OM) chaos("const comparison left operand not defined");
	if (ckind != cright->const_kind) {
#ifdef DEBUG
		zpcon(cleft); 
		zpcon(cright);
#endif
		chaos("const comparison operands differing kinds");
	}
	return ckind;
}

int const_same_kind(Const cleft, Const cright)			/*;const_same_kind*/
{
	/* returns boolean value indicating whether two Consts are of same kind */
	return (cleft->const_kind == cright->const_kind);
}

int const_cmp_undef(Const cleft, Const cright)		/*;const_cmp_undef*/
{
#ifdef DEBUG
	zpcon(cleft); 
	zpcon(cright);
#endif
	chaos("const comparison not defined for these constant types");
	return 0; /* for sake of lint */
}

int fx_mantissa(Rational lbd, Rational ubd, Rational small)		/*;mantissa*/
{
	Rational exact_val;
	int *vnum, *vden, *int_1;
	int     power;

	lbd = rat_abs(lbd);
	ubd = rat_abs(ubd);

	/*  find the exact # of values to be represented (aside from 0) */

	if (rat_gtr(lbd, ubd))
		exact_val = rat_div(lbd, small);
	else
		exact_val = rat_div(ubd, small);
	vnum = num(exact_val);
	vden = den(exact_val);
	int_1 = int_fri(1);

	/* the mantissa is calculated assuming that the bound is 'small away
     * from a model number, so we subtract one before computing no. of bits
     */

	vnum = int_sub(vnum, int_1);
	vnum = int_quo(vnum, vden);
	vden = int_fri(1);
	power = 1;
	while (int_gtr(vnum, vden)) {
		power++;
		vden = int_add(int_add(vden, vden), int_1);
	}
	return power;
}

/* Not used */
void node_free(Node node)									/*;node_free*/
{
	/* free nodeentry. Since state of allocated fields not clear
	 * only free the node block itself
	 */
	chaos("node free");
	if (node != (Node)0) efreet((char *) node, "node-free");
}

void to_errfile(char *txt)									/*;to_errfile */
{
	printf("%s\n", txt);
}

int needs_body(Symbol name)  /*;needs_body*/	
{
	/* Procedures and function specs need bodies of course. So do package
	 * specs that contain objects which need bodies.
	 */

	Symbol	obj;
	char	*id;
	Fordeclared	fd1;
	int	nat;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  needs_body");

	nat = NATURE(name);
	if (nat == na_package_spec || nat == na_generic_package_spec) {
		FORDECLARED(id, obj, DECLARED(name), fd1);
			if (IS_VISIBLE(fd1) && obj->scope_of == name
			  && needs_body(obj)) return TRUE;
		ENDFORDECLARED(fd1);
		FORDECLARED(id, obj, DECLARED(name), fd1)
		    if (TYPE_OF(obj) == symbol_incomplete) return TRUE;
		ENDFORDECLARED(fd1);
		return FALSE;
	}
	if (nat == na_procedure_spec || nat == na_function_spec 
	  || nat == na_task_type_spec || nat == na_task_obj_spec
	  || nat == na_generic_procedure_spec || nat == na_generic_function_spec)
		return TRUE;
	return FALSE;
}

/* The text of kind_str that follows is generated by a spitbol program
 * called AS
 */
char *kind_str(unsigned int as)		/*;kind_str*/
{
	static char *as_names[] = {
		"pragma",
		"arg",
		"obj_decl",
		"const_decl",
		"num_decl",
		"type_decl",
		"subtype_decl",
		"subtype_indic",
		"derived_type",
		"range",
		"range_attribute",
		"constraint",
		"enum",
		"int_type",
		"float_type",
		"fixed_type",
		"digits",
		"delta",
		"array_type",
		"box",
		"subtype",
		"record",
		"component_list",
		"field",
		"discr_spec",
		"variant_decl",
		"variant_choices",
		"string",
		"simple_choice",
		"range_choice",
		"choice_unresolved",
		"others_choice",
		"access_type",
		"incomplete_decl",
		"declarations",
		"labels",
		"character_literal",
		"simple_name",
		"call_unresolved",
		"selector",
		"all",
		"attribute",
		"aggregate",
		"parenthesis",
		"choice_list",
		"op",
		"in",
		"notin",
		"un_op",
		"int_literal",
		"real_literal",
		"string_literal",
		"null",
		"name",
		"qualify",
		"new_init",
		"new",
		"statements",
		"statement",
		"null_s",
		"assignment",
		"if",
		"cond_statements",
		"condition",
		"case",
		"case_statements",
		"loop",
		"while",
		"for",
		"forrev",
		"block",
		"exit",
		"return",
		"goto",
		"subprogram_decl",
		"procedure",
		"function",
		"operator",
		"formal",
		"mode",
		"subprogram",
		"call",
		"package_spec",
		"package_body",
		"private_decl",
		"use",
		"rename_obj",
		"rename_ex",
		"rename_pack",
		"rename_sub",
		"task_spec",
		"task_type_spec",
		"task",
		"entry",
		"entry_family",
		"accept",
		"delay",
		"selective_wait",
		"guard",
		"accept_alt",
		"delay_alt",
		"terminate_alt",
		"conditional_entry_call",
		"timed_entry_call",
		"abort",
		"unit",
		"with_use_list",
		"with",
		"subprogram_stub",
		"package_stub",
		"task_stub",
		"separate",
		"exception",
		"except_decl",
		"handler",
		"others",
		"raise",
		"generic_function",
		"generic_procedure",
		"generic_package",
		"generic_formals",
		"generic_obj",
		"generic_type",
		"gen_priv_type",
		"generic_subp",
		"generic",
		"package_instance",
		"function_instance",
		"procedure_instance",
		"instance",
		"length_clause",
		"enum_rep_clause",
		"rec_rep_clause",
		"compon_clause",
		"address_clause",
		"any_op",
		"opt",
		"list",
		"range_expression",
		"arg_assoc_list",
		"private",
		"limited_private",
		"code",
		"line_no",
		"index",
		"slice",
		"number",
		"convert",
		"entry_name",
		"array_aggregate",
		"record_aggregate",
		"ecall",
		"call_or_index",
		"ivalue",
		"qual_range",
		"qual_index",
		"qual_discr",
		"qual_arange",
		"qual_alength",
		"qual_adiscr",
		"qual_aindex",
		"check_bounds",
		"discr_ref",
		"row",
		"current_task",
		"check_discr",
		"end",
		"terminate",
		"exception_accept",
		"test_exception",
		"create_task",
		"predef",
		"deleted",
		"insert",
		"arg_convert",
		"end_activation",
		"activate_spec",
		"delayed_type",
		"qual_sub",
		"static_comp",
		"array_ivalue",
		"record_ivalue",
		"expanded",
		"choices",
		"init_call",
		"type_and_value",
		"discard",
		"unread",
		"string_ivalue",
		"instance_tuple",
		"entry_family_name",
		"astend",
		"astnull",
		"aggregate_list",
		"interfaced",
		"record_choice",
		"subprogram_decl_tr",
		"subprogram_tr",
		"subprogram_stub_tr",
		"rename_sub_tr",
		0	};
	return (as <= 199) ? as_names[as] : "INVALID";
}

/* following nature_str generated from spitbol program NA (on acf2) */
char *nature_str(int na)								/*;nature_str*/
{
	static char *na_names[] = {
		"op",
		"un_op",
		"attribute",
		"obj",
		"constant",
		"type",
		"subtype",
		"array",
		"record",
		"enum",
		"literal",
		"access",
		"aggregate",
		"block",
		"procedure_spec",
		"function_spec",
		"procedure",
		"function",
		"in",
		"inout",
		"out",
		"package_spec",
		"package",
		"task_type",
		"task_type_spec",
		"task_obj",
		"task_obj_spec",
		"entry",
		"entry_family",
		"entry_former",
		"generic_procedure_spec",
		"generic_function_spec",
		"generic_package_spec",
		"generic_procedure",
		"generic_function",
		"generic_package",
		"exception",
		"private_part",
		"void",
		"null",
		"discriminant",
		"field",
		"label",
		"generic_part",
		"subprog",
		"body",
		"task",
		"task_body",
		0	};
	return (na > 0 && na <= 48) ? na_names[na-1] : "INVALID";
}

int in_open_scopes(Symbol s)							/*;in_open_scopes*/
{
	return tup_mem((char *) s, open_scopes);
}

char *newat_str()											/*newat_str*/
{
	static int n = 0;
	char	*s;

	n += 1;
	s = smalloc(6);
	sprintf(s, "n%04d", n);
	return s;
}

char *str_newat()											/*;str_newat*/
{
	return newat_str();
}

void symtab_copy(Symbol news, Symbol old)						/*symtab_copy*/
{
	/* Note that this must be changed if symbol table layout changed */
	/* called from ch3 */

	int nseq, nunit;

	nunit = S_UNIT(news);
	nseq = S_SEQ(news);
	sym_copy(news, old);
	S_SEQ(news) = nseq;
	S_UNIT(news) = nunit;
}

void sym_copy(Symbol news, Symbol old)						/*;sym_copy*/
{
	/* Note that this must be changed if symbol table layout changed */

	char	*op, *np;
	int i, n;

	n = sizeof(Symbol_s);
	op = (char *)old; 
	np = (char *) news;
	for (i = 1;i <= n;i++) *np++ = *op++;
}

void SYMBTABcopy(Symbol news, Symbol old)					/*SYMBATBcopy */
{
	/* copy symbol table fields referenced by (Setl) SYMBTAB macro, i.e.,
	 *    NATURE, TYPE_OF, SIGNATURE and OVERLOADS
	 * copies only pointers and not the structures pointed to by these pointers.
	 * thus, it may not be correct in the general case !
	 */

	NATURE(news) = NATURE(old);
	TYPE_OF(news) = TYPE_OF(old);
	SIGNATURE(news) = SIGNATURE(old);
	OVERLOADS(news) = OVERLOADS(old);
	/* what about a set_copy ?? */
}

Symbol sym_new_noseq(int na)							/*;sym_new_noseq*/
{
	/* allocate new symbol table entry, nature na */

	Symbol sym;

	sym = (Symbol) smalloc(sizeof(Symbol_s));
	NATURE(sym) = na;
	/* following not needed since allocate initially as zeros 
     * ORIG_NAME(sym) = (char *)0;
     * S_SEQ(sym) = 0; 
     * S_UNIT(sym) = 0;
	 */
	/* set SEGMENT to -1 to indicate not yet defined */
	S_SEGMENT(sym) = -1;
	return sym;
}

Symbol sym_new(int na)										/*;sym_new*/
{
	/* allocate new symbol table entry, nature na.
	 * Increment sequence number and enter as sequence field of new entry 
	 *
	 */

	Symbol sym;

	sym = sym_new_noseq(na);
	if (seq_symbol_n > (int) seq_symbol[0])
		 chaos("sym_new seq_symbol_n exceeds allocated length");
	if (seq_symbol_n == (int)seq_symbol[0]) {
		seq_symbol = tup_exp(seq_symbol,
		  (unsigned) (seq_symbol_n + SEQ_SYMBOL_INC));
	}
	seq_symbol_n += 1;
	seq_symbol[seq_symbol_n] = (char *) sym;
	S_SEQ(sym) = seq_symbol_n;
	S_UNIT(sym) = unit_number_now; /* added by ds  2 dec 84*/
#ifdef DEBUG
	if (trapss>0 && S_SEQ(sym) == trapss && S_UNIT(sym) == trapsu) traps(sym);
#endif
	return sym;
}

/* Not Used */
int sym_free(Symbol sym)									/*;sym_free*/
{
	/* free symbol entry. Since state of allocated fields not clear
	 * only free the symbol block itself
	 */
	return 0; /* do not free, use smalloc to allocate instead */
#ifdef SKIP
	if (sym != (Symbol)0) efreet((char *) sym, "sym-free");
#endif
}

/* procedures for private_declarations */
Private_declarations private_decls_new(int n)		/*;private_decls_new*/
{
	Private_declarations	ps;
	Tuple	t;

	ps = (Private_declarations) emalloct(sizeof(Private_declarations_s),
	  "private-declarations");
	t = tup_new(n*2);
	ps->private_declarations_tuple = t;
	return ps;
}

Symbol private_decls_get(Private_declarations pdecl, Symbol s)
													/*;private_decls_get*/
{
	Forprivate_decls	fp;
	Symbol	s1, s2;

	if (s == (Symbol)0) return (Symbol)0;
	FORPRIVATE_DECLS(s1, s2, pdecl, fp);
		if (s1 == s) return s2;
	ENDFORPRIVATE_DECLS(fp);
	return	(Symbol)0;
}

void private_decls_put(Private_declarations pdecl, Symbol s1)
													/*;private_decls_put*/
{
	int	i, n, newi = FALSE;
	Tuple	t;
	Symbol	s2;
	Set	ovl;

	t = pdecl->private_declarations_tuple;
	n = tup_size(t);
	s2 = (Symbol)0;
	for (i = 1;i <= n;i += 2) {
		if (t[i] == (char *)s1) {
			s2 = (Symbol) t[i+1]; /* if entry exists */
			break;
		}
	}
	if (s2 == (Symbol)0) { /* if need new entry */
		newi = TRUE;
		t = tup_exp(t, (unsigned) n+2);
		pdecl->private_declarations_tuple = t;
		t[n+1] = (char *)s1;
		s2 = sym_new(NATURE(s1));
		t[n+2] = (char *)s2;
		/* TBSL: we need to copy signature and overloads when entering
		 * symbols with nature na_constant and na_type as these can have
		 * different representations in the private and public parts.
		 * ds 5-dec-84
		 */
	}
	/* if new entry, need to copy overloads (will always be a set) */
	if (newi) {
		/* now copy current information from s1 to s2 */
		symtab_copy(s2, s1);
		ovl = OVERLOADS(s1);
		if (ovl != (Set)0)
			OVERLOADS(s2) = set_copy(ovl);
		/* also need to copy signature if private type */
		if(TYPE_OF(s1) == symbol_private
		  || TYPE_OF(s1) == symbol_limited_private) {
			if (SIGNATURE(s1) != (Tuple)0) {
				SIGNATURE(s2) = tup_copy(SIGNATURE(s1));
				if (declared_components(s2) != (Tuple) 0)
					SIGNATURE(s2)[4] =
					  (char *) dcl_copy((Declaredmap)declared_components(s1));
			}
		}
	}
}

void private_decls_swap(Symbol s1, Symbol s2)		/*;private_decls_swap*/
{
	/* swap symbol table entries for s1 and s2 */

	struct Symbol_s tmp;
	struct Symbol_s		*sp;
	int		i, n, seq1, unit1, seq2, unit2;
	char	*p1, *p2;

	/* this version assumes all symbol table entries of the same size */
	p1 = (char *)s1;
	sp = &tmp;
	n = sizeof(Symbol_s);
	/* copy s1 to tmp */
	seq1 = S_SEQ(s1); 
	unit1 = S_UNIT(s1);
	seq2 = S_SEQ(s2); 
	unit2 = S_UNIT(s2);
	p1 = (char *)sp; 
	p2 = (char *)s1;
	for (i = 0;i<n;i++) *p1++ = *p2++;
	/* copy s2 to s1 */
	p1 = (char *)s1; 
	p2 = (char *)s2;
	for (i = 0;i<n;i++) *p1++ = *p2++;
	/* copy tmp to s2 */
	p1 = (char *)sp; 
	p2 = (char *)s2;
	for (i = 0;i<n;i++) *p2++ = *p1++;
	/* restore original sequence numbers and units */
	S_SEQ(s1) = seq1; 
	S_UNIT(s1) = unit1;
	S_SEQ(s2) = seq2; 
	S_UNIT(s2) = unit2;
	if (REPR(s1)==(Tuple)0) {
	   FORCED(s1) = FORCED(s2);
	   RCINFO(s1) = RCINFO(s2);
	   REPR(s1)   = REPR(s2);
    } 
	else if (REPR(s2)==(Tuple)0) {
	   FORCED(s2) = FORCED(s1);
	   RCINFO(s2) = RCINFO(s1);
	   REPR(s2)   = REPR(s1);
	}
}

char *attribute_str(int attrnum)						/*;attribute_str*/
{
	/* convert internal attribute code to attribute string */

	static char *attrnames[] = { 
		"ADDRESS", "AFT", "BASE", "CALLABLE",
		"CONSTRAINED", "O_CONSTRAINED", "T_CONSTRAINED", "COUNT", "DELTA",
		"DIGITS", "EMAX", "EPSILON", "FIRST", "O_FIRST", "T_FIRST", "FIRST_BIT",
		"FORE", "IMAGE", "LARGE", "LAST", "O_LAST", "T_LAST", "LAST_BIT",
		"LENGTH", "O_LENGTH", "T_LENGTH", "MACHINE_EMAX", "MACHINE_EMIN", 
		"MACHINE_MANTISSA", "MACHINE_OVERFLOWS", "MACHINE_RADIX",
		"MACHINE_ROUNDS", "MANTISSA", "POS", "POSITION", "PRED", "RANGE",
		"O_RANGE", "T_RANGE", "SAFE_EMAX", "SAFE_LARGE", "SAFE_SMALL",
		"SIZE", "O_SIZE", "T_SIZE", "SMALL", "STORAGE_SIZE", "SUCC", 
		"TERMINATED", "VAL", "VALUE", "WIDTH", "any_attr"	};
	/* i = (int) N_VAL(node);	pass code, not node (gcs) */

	if (attrnum > 52) chaos("attribute_str: invalid internal attriubte code");
	return attrnames[attrnum];
}

int no_dimensions(Symbol sym)								/*;no_dimensions*/
{
	/* no_dimensions is macro defined in hdr.c */

	Tuple	tup = SIGNATURE(sym);
	return tup_size((Tuple) tup[1]);
}

int in_incp_types(Symbol s)									/*;in_incp_types*/
{
	return (s == symbol_private || s == symbol_limited_private)
	  || (s == symbol_limited) || (s == symbol_incomplete);
}

int in_qualifiers(unsigned int kind)						/*;in_qualifiers*/
{
	return (kind == as_qual_range || kind == as_qual_index
	  || kind == as_qual_discr || kind == as_qual_aindex
	  || kind == as_qual_adiscr);
}

int in_univ_types(Symbol s)								/*;in_univ_types*/
{
	return s == symbol_universal_real  || s == symbol_universal_integer;
}

int in_vis_mods(Symbol v)									/*;in_vis_mods*/
{
	/* Test for membership in vis_mods. Assume vis_mods is tuple of symbols */
	return tup_mem((char *) v, vis_mods);
}

void undone(char *s)												/*;undone*/
{
	chaos(strjoin(s, " not implemented"));
}

int is_type(Symbol name) 										/*;is_type*/
{
	static int type_natures[8] = {
		na_type, na_subtype, na_array, na_record, na_enum, na_access,
		na_task_type, na_task_type_spec	};
	int i;

	if (name == (Symbol)0) return FALSE;
	for (i = 0; i < 8; i++)
		if(NATURE(name) == type_natures[i]) return TRUE;
	return FALSE;
}

int is_fixed_type(Symbol typ)								/*;is_fixed_type*/
{
	/* IS_FIXED_TYPE is procedure is_fixed_type() in C:
	 *   macro IS_FIXED_TYPE(typ);  (SIGNATURE(typ)(1) = co_delta)  endm;
	 */

	Tuple	tup;

	if (typ == symbol_dfixed) return TRUE;
	tup = SIGNATURE(typ);
	if (tup == (Tuple)0) return FALSE;
	return tup[1] == (char *)CONSTRAINT_DELTA;
}

int is_generic_type(Symbol type_mark)					/*;is_generic_type*/
{
	int attr;

	attr = (int) misc_type_attributes(type_mark);
	return	TA_GENERIC & attr;
}

int is_access(Symbol name)									/*;is_access */
{
	/* TBSL: this appears identical to is_access_type in adagen and should be
	 * merged with it
	 */
	if (name == (Symbol)0 || root_type(name) == (Symbol) 0)
		return FALSE;
	else return (NATURE((root_type(name))) == na_access);
}

int is_scalar_type(Symbol name)							/*;is_scalar_type*/
{
	Symbol	root;
	Tuple   sig;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  is_scalar_type");

	root = root_type(name);
	/* if (root in scalar_types ...)
	 * ??const scalar_types =
	 *     {'INTEGER', 'FLOAT', '$FIXED', 'universal_integer', 'universal_real',
	 *      'universal_fixed', 'discrete_type'};
	 */
	if (root == symbol_integer || root == symbol_float || root == symbol_dfixed
	  || root == symbol_universal_integer || root == symbol_universal_real
	  || root == symbol_universal_fixed || root == symbol_discrete_type )
		return TRUE;
	if (NATURE(root) == na_type) { /* fixed type also scalar */
		sig = SIGNATURE(root);
		if (sig != (Tuple)0 && (int) sig[1] == CONSTRAINT_DELTA) return TRUE;
	}
	return	  NATURE(root) == na_enum;
}

int is_numeric_type(Symbol typ)							/*;is_numeric_type */
{
	Symbol root;

	root = root_type (typ);
	return (root == symbol_integer || root == symbol_float
	  || root == symbol_dfixed || root == symbol_universal_integer
	  || root == symbol_universal_fixed || root == symbol_universal_real);
}

int is_record(Symbol typ)										/*;is_record*/
{
	/* This predicate is used to validate selected component notation and
	 * the examination of discriminant lists.
	 */

	Symbol	r;

	if (typ == (Symbol) 0) /* for case when typ = om in setl */
		return FALSE;
	if (NATURE(typ) == na_record) return TRUE;
	if (NATURE(typ) != na_subtype && NATURE(typ) != na_type) return FALSE;
	if (NATURE(base_type(typ)) == na_record) return TRUE;
	r = root_type(typ);
	/* prevent illegal reference to field of a private type */
        if (typ == symbol_private) return FALSE;
	if (in_incp_types(TYPE_OF(r)) && has_discriminants(r)) return TRUE;
	return FALSE;
}

int is_anonymous_task(Symbol name)						/*;is_anonymous_task*/
{
	/* see if task anonymous (corresponds to macro of same name in SETL vern)*/
	/* Procedure task_spec (9) in SETL uses special prefix to flag anonymous
	 * tasks. We simplify that to making the first character a colon 
	 */

	char	*s;
	int		n;

	if (!is_task_type(name)) return FALSE;
	s = ORIG_NAME(name);
	if (s == (char *)0 ) return FALSE;
	s = substr(s, 1, 10);
	if (s == (char *)0) return FALSE;
	n = streq(s, "task_type:");
#ifndef SMALLOC
	efreet(s, "is-anonymous-task"); /* free temporary substring*/
#endif
	return n;
}

int is_task_type(Symbol task)								/*;is_task_type*/
{
	return NATURE(task) == na_task_type || NATURE(task) == na_task_type_spec;
}

Node discr_map_get(Tuple dmap, Symbol sym)				/*;discr_map_get*/
{
	int		i, n;

	n = tup_size(dmap);
	for (i = 1;i <= n; i += 2)
		if ((Symbol) dmap[i]== sym) return (Node) dmap[i+1];
	return (Node)0;
}

Tuple discr_map_put(Tuple dmap, Symbol sym, Node nod)		/*;discr_map_put*/
{
	int		i, n;

	n = tup_size(dmap);
	for (i = 1;i <= n; i += 2) {
		if ((Symbol) dmap[i] == sym) {
			dmap[i+1] = (char *) nod;
			return dmap;
		}
	}
	dmap = tup_exp(dmap, (unsigned) n+2);
	dmap[n+1] = (char *) sym;
	dmap[n+2] = (char *) nod;
	return dmap;
}

int tup_memsym(Symbol sym, Tuple tp)						/*;tup_memsym*/
{
	/* like tup_mem, but n is symbol, so also check for matching sequence and
	 * unit number
	 */

	int i;
	int sz;

	sz = tup_size(tp);
	for (i = 1;i <= sz;i++) {
		if ((Symbol)tp[i] == sym)
			return TRUE;
		if (S_SEQ((Symbol)tp[i]) == S_SEQ(sym)
		  && S_UNIT((Symbol)tp[i]) == S_UNIT(sym))
			return TRUE;
	}
	return FALSE;
}

void const_check(Const con, int ctyp)						/*;const_check*/
{
	/* check that const has const kind ctyp, raise chaos if not */

	if (con->const_kind == ctyp) return;
#ifdef DEBUG
	fprintf(stderr, "const of kind %d, expect %d\n", con->const_kind, ctyp);
#endif
	chaos("const not of expected kind");
}

int power_of_2(Const const_arg)								/*;power_of_2*/
{
	/*
	 * DESCR: This procedure finds the closest power of 2 <= the argument.
	 * INPUT: arg:  a rational number.
	 * OUTPUT: [accuracy, power, small]
	 *        accuracy: 'exact' if arg= 2**power, or 'approximate'
	 *                  if arg < 2**power.
	 *        power: integer.
	 *	 small: rational value of 2**power
	 * ALGORITHM:
	 *	1- Work only with integers. So if num < den, invert the rational
	 *          and remember.
	 *	2- find first power such that den * 2**power >= num
	 *	3- Adjust and negate if rational was inverted.
	 *  4- Return zero if no errors, or one if cannot convert
	 */

	Rational arg;
	int     *d, *n;		/* numerator and denominator of arg */
	int     inverted;		/* flag TRUE if arg < 1 */
	int     power;		/* the desired power of two */
	int    *next_power_of_2;    /* nearest power of 2 to given delta */
	int     *tmp;

	arg = RATV(const_arg);
	n = int_copy(num(arg));
	d = int_copy(den(arg));

	if (int_lss(n, d)) {
		tmp = n;
		n = d;
		d = tmp;
		inverted = TRUE;
	}
	else
		inverted = FALSE;

	power = 0;
	next_power_of_2 = int_fri(1);
	while(power < 127 && int_lss(int_mul(next_power_of_2, d), n)) {
		/* Should be possible to find  better algorithm.  */
		next_power_of_2 = int_mul(next_power_of_2, int_fri(2));
		power++;
	}

	if (int_eql(int_mul(next_power_of_2, d), n)) {
		power_of_2_accuracy = POWER_OF_2_EXACT;
		if (power == 127) power--;
		if (inverted) {
			power_of_2_power = -power;
			power_of_2_small = rat_fri(int_fri(1), next_power_of_2);
		}
		else {
			power_of_2_power = power;
			power_of_2_small = rat_fri(next_power_of_2, int_fri(1));
		}
	}
	else {
		power_of_2_accuracy = POWER_OF_2_APPROXIMATE;
		if (inverted) {
			if(power == 127) {
				power_of_2_power = 126;
				power_of_2_small = rat_fri(next_power_of_2, int_fri(1));
				return 1;
			}
			power_of_2_power = -power;
			power_of_2_small = rat_fri(int_fri(1), next_power_of_2);
		}
		else {
			power_of_2_power = power - 1;
			power_of_2_small = rat_fri(next_power_of_2, int_fri(2));
		}
	}
	return 0;
}

Node new_ivalue_node(Const value, Symbol typ)			/*;new_ivalue_node*/
{
	/* constructs an ivalue node */
	Node	node;

	node         = node_new(as_ivalue);
	N_VAL (node) = (char *) value;
	N_TYPE(node) = typ;
	return node;
}

Tuple constraint_new(int ty)							/*;constraint_new*/
{
	Tuple p;
	/* TBSL: set length correctly, make always five for now */
	p = tup_new(5);
	p[1] = (char *) ty;

	return p;
}

union node_list {
	union node_list *next;
	Node_s node; };

static union node_list *head_of_nodes = (union node_list *)0;

#define NODE_BLOCK_NUMBER 2000
static Node newBlockOfNodes()
{
		int n;
		union node_list *np = (union node_list *)
		  emalloct(NODE_BLOCK_NUMBER * sizeof(union node_list), "node_group");

		head_of_nodes = np;
		for (n = 1; n < NODE_BLOCK_NUMBER; n++) {
			np->next = np + 1;
			np++;
		}
		np->next = (union node_list *)0;
		return ((Node)head_of_nodes++);
}

Node node_new_noseq(unsigned int na)					/*;node_new_noseq*/
{
	char *np;
	Node p;
	int	i;

	p = (Node)head_of_nodes;
	if (p)
		head_of_nodes = head_of_nodes->next;
	else
		p = newBlockOfNodes();

	np = (char *) p;
	/* clear all fields */
	for (i = 0; i < sizeof(Node_s); i++) *np++ = 0;
	N_KIND(p) = na;
	return p;
}

Node node_new(unsigned int na)									/*;node_new*/
{
	Node p;

	p = node_new_noseq(na);

	if (seq_node_n > (int) seq_node[0]) 
		chaos("node_new seq_node_n exceeds allocated length");
	/* increment allocated count and assign sequence number for node*/
	if(seq_node_n == (int) seq_node[0])
		seq_node = tup_exp(seq_node, (unsigned)  seq_node_n+SEQ_NODE_INC);
	seq_node_n += 1;
	seq_node[seq_node_n] = (char *) p;
	N_SEQ(p) = seq_node_n;
	N_UNIT(p) = unit_number_now;
#ifdef DEBUG
	if (trapns>0 && N_SEQ(p) == trapns && N_UNIT(p) == trapnu) trapn(p);
#endif
	/* initialize other fields later */
	return p;
}

int N_DEFINED[] = {
	N_D_AST1 | N_D_AST2,                        /*   0 pragma */
	N_D_AST1 | N_D_AST2,                        /*   1 arg */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /*   2 obj_decl */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /*   3 const_decl */
	N_D_AST1 | N_D_AST2,                        /*   4 num_decl */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_TYPE,  /*   5 type_decl */
	N_D_AST1 | N_D_AST2 | N_D_UNQ | N_D_TYPE,   /*   6 subtype_decl */
	N_D_AST1 | N_D_AST2 | N_D_UNQ,              /*   7 subtype_indic */
	N_D_AST1,                                   /*   8 derived_type */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /*   9 range */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_TYPE,  /*  10 range_attribute */
	N_D_LIST,                                   /*  11 constraint */
	N_D_LIST,                                   /*  12 enum */
	N_D_AST1,                                   /*  13 int_type */
	N_D_AST1,                                   /*  14 float_type */
	N_D_AST1,                                   /*  15 fixed_type */
	N_D_AST1 | N_D_AST2,                        /*  16 digits */
	N_D_AST1 | N_D_AST2,                        /*  17 delta */
	N_D_AST1 | N_D_AST2 | N_D_UNQ,              /*  18 array_type */
	N_D_AST1 | N_D_UNQ,                         /*  19 box */
	N_D_AST1 | N_D_AST2 | N_D_UNQ | N_D_TYPE,   /*  20 subtype */
	N_D_AST1,                                   /*  21 record */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /*  22 component_list */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /*  23 field */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /*  24 discr_spec */
	N_D_AST1 | N_D_AST2,                        /*  25 variant_decl */
	N_D_AST1 | N_D_AST2,                        /*  26 variant_choices */
	N_D_VAL,                                    /*  27 string */
	N_D_AST1,                                   /*  28 simple_choice */
	N_D_AST1,                                   /*  29 range_choice */
	N_D_AST1,                                   /*  30 choice_unresolved */
	N_D_AST1 | N_D_AST2,                        /*  31 others_choice */
	N_D_AST1,                                   /*  32 access_type */
	N_D_AST1,                                   /*  33 incomplete_decl */
	N_D_LIST,                                   /*  34 declarations */
	N_D_LIST,                                   /*  35 labels */
	N_D_VAL | N_D_TYPE,                         /*  36 character_literal */
	N_D_VAL | N_D_UNQ | N_D_TYPE,               /*  37 simple_name */
	N_D_AST1 | N_D_AST2,                        /*  38 call_unresolved */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /*  39 selector */
	N_D_AST1 | N_D_UNQ | N_D_TYPE,              /*  40 all */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_TYPE,  /*  41 attribute */
	N_D_LIST | N_D_TYPE,                        /*  42 aggregate */
	N_D_AST1 | N_D_TYPE,                        /*  43 parenthesis */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /*  44 choice_list */
	N_D_AST1 | N_D_AST2 | N_D_UNQ | N_D_TYPE,   /*  45 op */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /*  46 in */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /*  47 notin */
	N_D_AST1 | N_D_AST2 | N_D_UNQ | N_D_TYPE,   /*  48 un_op */
	N_D_VAL | N_D_TYPE,                         /*  49 int_literal */
	N_D_VAL | N_D_TYPE,                         /*  50 real_literal */
	N_D_VAL | N_D_TYPE,                         /*  51 string_literal */
	N_D_TYPE,                                   /*  52 null */
	N_D_AST1 | N_D_UNQ | N_D_TYPE,              /*  53 name */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /*  54 qualify */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /*  55 new_init */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /*  56 new */
	N_D_AST1 | N_D_AST2,                        /*  57 statements */
	N_D_AST1 | N_D_AST2,                        /*  58 statement */
	0,                                          /*  59 null_s */
	N_D_AST1 | N_D_AST2,                        /*  60 assignment */
	N_D_AST1 | N_D_AST2,                        /*  61 if */
	N_D_AST1 | N_D_AST2,                        /*  62 cond_statements */
	N_D_AST1,                                   /*  63 condition */
	N_D_AST1 | N_D_AST2,                        /*  64 case */
	N_D_AST1 | N_D_AST2,                        /*  65 case_statements */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /*  66 loop */
	N_D_AST1,                                   /*  67 while */
	N_D_AST1 | N_D_AST2,                        /*  68 for */
	N_D_AST1 | N_D_AST2,                        /*  69 forrev */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_AST4,  /*  70 block */
	N_D_AST1 | N_D_AST2 | N_D_UNQ,              /*  71 exit */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /*  72 return */
	N_D_AST1,                                   /*  73 goto */
	N_D_AST1,                                   /*  74 subprogram_decl */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /*  75 procedure */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /*  76 function */
	N_D_VAL | N_D_UNQ | N_D_TYPE,               /*  77 operator */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_AST4,  /*  78 formal */
	N_D_VAL,                                    /*  79 mode */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_AST4,  /*  80 subprogram */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /*  81 call */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /*  82 package_spec */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_AST4,  /*  83 package_body */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /*  84 private_decl */
	N_D_LIST,                                   /*  85 use */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /*  86 rename_obj */
	N_D_AST1 | N_D_AST2,                        /*  87 rename_ex */
	N_D_AST1 | N_D_AST2,                        /*  88 rename_pack */
	N_D_AST1 | N_D_AST2,                        /*  89 rename_sub */
	N_D_AST1 | N_D_AST2 | N_D_UNQ | N_D_TYPE,   /*  90 task_spec */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /*  91 task_type_spec */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_AST4,  /*  92 task */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /*  93 entry */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_TYPE,  /*  94 entry_family */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_AST4,  /*  95 accept */
	N_D_AST1,                                   /*  96 delay */
	N_D_AST1 | N_D_AST2,                        /*  97 selective_wait */
	N_D_AST1 | N_D_AST2,                        /*  98 guard */
	N_D_AST1 | N_D_AST2,                        /*  99 accept_alt */
	N_D_AST1 | N_D_AST2,                        /* 100 delay_alt */
	N_D_VAL,                                    /* 101 terminate_alt */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /* 102 conditional_entry_call */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /* 103 timed_entry_call */
	N_D_LIST,                                   /* 104 abort */
	N_D_AST1 | N_D_AST2,                        /* 105 unit */
	N_D_LIST,                                   /* 106 with_use_list */
	N_D_LIST,                                   /* 107 with */
	N_D_AST1 | N_D_VAL,                         /* 108 subprogram_stub */
	N_D_VAL | N_D_UNQ,                          /* 109 package_stub */
	N_D_VAL | N_D_UNQ,                          /* 110 task_stub */
	N_D_AST1 | N_D_AST2,                        /* 111 separate */
	N_D_LIST,                                   /* 112 exception */
	N_D_LIST,                                   /* 113 except_decl */
	N_D_AST1 | N_D_AST2,                        /* 114 handler */
	0,                                          /* 115 others */
	N_D_AST1 | N_D_TYPE,                        /* 116 raise */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_AST4,  /* 117 generic_function */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_AST4,  /* 118 generic_procedure */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_AST4,  /* 119 generic_package */
	N_D_LIST,                                   /* 120 generic_formals */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_AST4,  /* 121 generic_obj */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /* 122 generic_type */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /* 123 gen_priv_type */
	N_D_AST1 | N_D_AST2,                        /* 124 generic_subp */
	0,                                          /* 125 generic */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_AST4,  /* 126 package_instance */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_AST4,  /* 127 function_instance */
	N_D_AST1 | N_D_AST2 | N_D_AST3 | N_D_AST4,  /* 128 procedure_instance */
	N_D_AST1 | N_D_AST2,                        /* 129 instance */
	N_D_AST1 | N_D_AST2,                        /* 130 length_clause */
	N_D_AST1 | N_D_AST2,                        /* 131 enum_rep_clause */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /* 132 rec_rep_clause */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /* 133 compon_clause */
	N_D_AST1,                                   /* 134 address_clause */
	N_D_AST1,                                   /* 135 any_op */
	0,                                          /* 136 opt */
	N_D_LIST,                                   /* 137 list */
	N_D_AST1 | N_D_UNQ,                         /* 138 range_expression */
	N_D_LIST,                                   /* 139 arg_assoc_list */
	N_D_AST1,                                   /* 140 private */
	N_D_AST1,                                   /* 141 limited_private */
	N_D_AST1,                                   /* 142 code */
	N_D_VAL,                                    /* 143 line_no */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /* 144 index */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /* 145 slice */
	N_D_VAL,                                    /* 146 number */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /* 147 convert */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /* 148 entry_name */
	N_D_AST1 | N_D_AST2 | N_D_UNQ | N_D_TYPE,   /* 149 array_aggregate */
	N_D_AST1 | N_D_AST2 | N_D_UNQ | N_D_TYPE,   /* 150 record_aggregate */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /* 151 ecall */
	N_D_AST1 | N_D_AST2 | N_D_TYPE,             /* 152 call_or_index */
	N_D_VAL | N_D_TYPE,                         /* 153 ivalue */
	N_D_AST1 | N_D_TYPE,                        /* 154 qual_range */
	N_D_AST1 | N_D_UNQ | N_D_TYPE,              /* 155 qual_index */
	N_D_AST1 | N_D_UNQ | N_D_TYPE,              /* 156 qual_discr */
	N_D_AST1,                                   /* 157 qual_arange */
	N_D_AST1,                                   /* 158 qual_alength */
	N_D_AST1 | N_D_TYPE,                        /* 159 qual_adiscr */
	N_D_AST1 | N_D_TYPE,                        /* 160 qual_aindex */
	N_D_AST1 | N_D_AST2,                        /* 161 check_bounds */
	N_D_AST1 | N_D_UNQ | N_D_TYPE,              /* 162 discr_ref */
	N_D_AST1 | N_D_UNQ | N_D_TYPE,              /* 163 row */
	N_D_UNQ,                                    /* 164 current_task */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /* 165 check_discr */
	N_D_AST1,                                   /* 166 end */
	N_D_AST1 | N_D_VAL,                         /* 167 terminate */
	N_D_AST1,                                   /* 168 exception_accept */
	N_D_AST1,                                   /* 169 test_exception */
	N_D_AST1 | N_D_TYPE,                        /* 170 create_task */
	N_D_VAL | N_D_UNQ | N_D_TYPE,               /* 171 predef */
	0,                                          /* 172 deleted */
	N_D_AST1 | N_D_LIST | N_D_TYPE,             /* 173 insert */
	N_D_AST1,                                   /* 174 arg_convert */
	N_D_AST1 | N_D_VAL,                         /* 175 end_activation */
	N_D_AST1,                                   /* 176 activate_spec */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /* 177 delayed_type */
	N_D_AST1 | N_D_UNQ | N_D_TYPE,              /* 178 qual_sub */
	N_D_AST1 | N_D_AST2,                        /* 179 static_comp */
	N_D_AST1 | N_D_AST2,                        /* 180 array_ivalue */
	N_D_AST1 | N_D_AST2,                        /* 181 record_ivalue */
	N_D_AST1,                                   /* 182 expanded */
	N_D_AST1,                                   /* 183 choices */
	N_D_AST1 | N_D_AST2,                        /* 184 init_call */
	N_D_AST1 | N_D_AST2,                        /* 185 type_and_value */
	N_D_AST1,                                   /* 186 discard */
	N_D_AST1,                                   /* 187 unread */
	N_D_VAL | N_D_TYPE,                         /* 188 string_ivalue */
	N_D_VAL,                                    /* 189 instance_tuple */
	N_D_AST1 | N_D_AST2 | N_D_AST3,             /* 190 entry_family_name */
	0,                                          /* 191 astend */
	0,                                          /* 192 astnull */
	N_D_AST1 | N_D_AST2,                        /* 193 aggregate_list */
	N_D_AST1 | N_D_UNQ,                         /* 194 interfaced */
	N_D_AST1 | N_D_AST2,                        /* 195 record_choice */
	N_D_UNQ,                                    /* 196 subprogram_decl_tr */
	N_D_AST1 | N_D_AST2 | N_D_UNQ | N_D_AST4,   /* 197 subprogram_tr */
	N_D_VAL | N_D_UNQ,                          /* 198 subprogram_stub_tr */
	N_D_AST2 | N_D_UNQ,                         /* 199 rename_sub_tr */
	0};
