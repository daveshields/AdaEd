/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#define GEN

#include "hdr.h"
#include "vars.h"
#include "gvars.h"
#include "ops.h"
#include "segment.h"
#include "slot.h"
#include "attr.h"
#include "genop.h"
#include "opdescprots.h"
#include "segmentprots.h"
#include "gpredefprots.h"
#include "peepprots.h"
#include "setprots.h"
#include "miscprots.h"
#include "gmiscprots.h"
#include "smiscprots.h"
#include "genprots.h"

static void gen_kfc(int, int, long, char *);
static void gen_krc(int, int, float, char *);
static void gen_r(int, Explicit_ref);
static void gop_int(int, int, int, int, char *);
static void gop_fix(int, int, int, long, char *);
static void gop_flt(int, int, int, float, char *);
static void gop_ref(int, int, int, Explicit_ref, char *);
static void gop_sym(int, int, int, Symbol, char *);
#ifdef DEBUG
static void undone_op(int, char *);
#endif
static char *g_kind(int);
static int adjust(int);
static int int_adjust(int);
static int fix_adjust(int);
static int float_adjust(int);
static void pretty_addr(int);
static void asm_exception(Symbol);
static void asm_byte(int);
static void asm_int(int);
static void asm_fix(long);
static void asm_flt(float);
static void asm_seg(int);
static void asm_off(int);
static void G_int(int);
static void G_fix(long);
static void G_flt(float);
#ifdef DEBUG
static void zpop(Op);
#endif
static void gref_sort(Tuple, int);
static int gref_compare_name(Gref *, Gref *);
static int gref_compare_address(Gref *, Gref *);
static char *gs_end();

extern Segment	CODE_SEGMENT, DATA_SEGMENT, DATA_SEGMENT_MAIN;

/*
 2-jun
 note that calls to gen(I_DISCARD_ADDR, n, ..) always have 1 as the
 second argument. This is kept in 'kind' field. The third argument
 is not always present, in which case (Symbol)0 should be written.

 5-jul	ds
 Translated the two calls to gen(I_CASE_TABLE ...) in stat.c as
 gen_ks.
 ---
 Translate the calls for gen(I_ATTRIBUTE, ...) to the form
 gen_kv(...) using (Const) 0 for third arg in cases where SETL
 has only two args.


 15-jul	ds
 Note following from mail note from Rosen:
The integer value is the numb of addresses to discard. It is normally one,
but the peep-hole optimizer may merge severall consecutives discard_addr
into one.
 
Note that the symbol name is given in the COMMENT field (and may thus be
omitted). If present, it is used by the peep-hole optimizer to trap things
like:
discard_addr 1 --symbol
push_addr symbol

*/

static char G_s[256]; /* for trace output of instructions */
/* macro to position at end of G_s */
char *gs_end();
#define G_END gs_end()

/* create dummy entry for p (np is string with name of p)
 * and call chaos if p is called
 * Current operand types:
 *	gen_i	integer
 * 	gen_k	kind (from kind_of, offset added to opcode to get
 *		final opcode) this field is also used for integer
 *		for i_discard_address (always 1) and for attribute
 *		code (<= 50) for I_ATTRIBUTE.
 *	gen_kc
 *	gen_ki
 *	gen_kic
 *	gen_ks	kind and symbol
 *	gen_ksc
 *	gen_kv	kind and value (Const), used mainly for push_immediate
 *		instructions. The v argument must be Const.
 *	gen_kvc
 *	gen_r	explicit reference (two args: segment and offset)
 *		in this case segment and offset always zero!!
 *	gen_rc
 *	gen_s	symbol
 *	gen_sc
 */

struct Op_s op_next;

/* set values in global variable op_next, needed copying done by assemble */
#define gop_new(opc, k, ka, c)	op_next.op_code = opc; op_next.op_kind = k;\
    op_next.op_type  = ka; op_next.op_com = c; 

#ifdef DEBUG
#define undone(p, np) p(op) int op; { undone_op(op, np);}
#endif

void gen(int opc)											/*;gen*/
{
	gop_int(opc, 0, 0, 0, (char *)0);
}

void gen_c(int opc, char *c)								/*;gen_c*/
{
	gop_int(opc, 0, 0, 0, c);
}

void gen_i(int opc, int i)									/*;gen_i*/
{
	gen_ic(opc, i, (char *)0);
}

void gen_ic(int opc, int i, char *c)							/*;gen_ic*/
{
	gop_int(opc, 0, OP_INT, i, c);
}

void gen_k(int opc, int k)										/*;gen_k*/
{
	gen_kc(opc, k, (char *)0);
}

void gen_kc(int opc, int k, char *c)							/*;gen_k*/
{
	gop_int(opc, k, OP_INT, 0, c);
}

void gen_ki(int opc, int k, int n)								/*;gen_ki*/
{
	gen_kic(opc, k, n, (char *)0);
}

void gen_kic(int opc, int k, int n, char *c)					/*;gen_kic*/
{
	gop_int(opc, k, OP_INT, n, c);
}

static void gen_kfc(int opc, int k, long n, char *c)				/*;gen_kfc*/
{
	gop_fix(opc, k, OP_FIX, n, c);
}

static void gen_krc(int opc, int k, float n, char *c)			/*;gen_krc*/
{
	gop_flt(opc, k, OP_FLT, n, c);
}

void gen_ks(int opc, int k, Symbol sym)							/*;gen_ks*/
{
	gen_ksc(opc, k, sym, (char *)0);
}

void gen_ksc(int opc, int k, Symbol sym, char *c)				/*;gen_ksc*/
{
	/* Note that I_DISCARD_ADDR has symbol supplied only for use
	 * by peephole optimizer. Since this is disable for now,
	 * ignore the symbol arg for this operation.
	 */
	if (opc == I_DISCARD_ADDR)
		gen_kic(opc, k, k, c);
	else
		gop_sym(opc, k, OP_SYM, sym, (char *)c);
}

void gen_kv(int opc, int k, Const ref)							/*;gen_kv*/
{
	gen_kvc(opc, k,  ref, (char *)0);
}

void gen_kvc(int opc, int k, Const ref, char *c)					/*;gen_kvc*/
{
	/* Need to get value from Const and see if length compatible with
	 * k argument
	 * Suppress check for now, just handle int's and longs, and
	 * also assume longs same size as ints
	 * TBSL: need to add checks, handle other const types, handle
	 * longs differently for PC		ds 7-15-85
	 */

	int ctype;

	ctype = ref->const_kind;
	if (ctype == CONST_INT) {
		gen_kic(opc, k, INTV(ref), c);
	}
	else if (ctype == CONST_FIXED) {
		gen_kfc(opc, k, FIXEDV(ref), c);
	}
	else if (ctype == CONST_REAL) {
		/* Note that treating ada reals as C reals here */
		gen_krc(opc, k, REALV(ref), c);
	}
	else {
		chaos("gop const undefined case");
	}
}

static void gen_r(int opc, Explicit_ref ref)						/*;gen_r*/
{
	gen_rc(opc, ref, (char *)0);
}

void gen_rc(int opc, Explicit_ref ref, char *c)					/*;gen_rc*/
{
	gop_ref(opc, 0, OP_REF, ref, c);
}

void gen_s(int opc, Symbol s)									/*;gen_s*/
{
	gen_sc(opc, s, (char *)0);
}

void gen_sc(int opc, Symbol s, char *c)								/*;gen_sc*/
{
	gop_sym(opc, 0, OP_SYM, s, c);
}

static void gop_int(int opc, int k, int ka, int arg, char *c)		/*;gop_int*/
{
	gop_new(opc, k, ka, c);
	op_next.op_arg.arg_int = arg;
	peep_hole(&op_next);
}

static void gop_fix(int opc, int k, int ka, long arg, char *c)		/*;gop_fix*/
{
	gop_new(opc, k, ka, c);
	op_next.op_arg.arg_fix = arg;
	peep_hole(&op_next);
}

static void gop_flt(int opc, int k, int ka, float arg, char *c)		/*;gop_flt*/
{
	gop_new(opc, k, ka, c);
	op_next.op_arg.arg_flt = arg;
	peep_hole(&op_next);
}

static void gop_ref(int opc, int k, int ka, Explicit_ref arg, char *c)
																/*;gop_ref*/
{
	gop_new(opc, k, ka, c);
	op_next.op_arg.arg_ref = arg;
	peep_hole(&op_next);
}

static void gop_sym(int opc, int k, int ka, Symbol arg, char *c)	/*;gop_sym*/
{
	gop_new(opc, k, ka, c);
	op_next.op_arg.arg_sym = arg;
	peep_hole(&op_next);
}

#ifdef DEBUG
static void undone_op(int op, char *np)						/*;undone_op*/
{
	/* print name of generation procedure and name of operation */
	extern char *opdesc_name;
	opdesc(op);
	printf("op %s %s\n", np, opdesc_name);
}
#endif

void assemble(Op op)										/*;assemble*/
{
	int	code;
	Symbol	lab_name, new_lab, obj_name;
	extern	char *opdesc_name;
	int	data_mode, addr_mode, addressing_mode;
	int		adj, b, off, type, loc, opkind, value;
	extern	int opdesc_a_mode, opdesc_d_mode;
	Explicit_ref	eref;
	Tuple	labtup, eqtup, newtup, patch_tup;
	Fortup	ft1, ft2;
	int		code_start;

#ifdef MACHINE_CODE
	if (list_code) { /* initialize G_s for trace output */
		G_s[0] = '\0';
		obj_name = (Symbol) 0; /* set nonzero if symbol for trace output*/
	}
#endif
	/* label handling */
	code_start = PC();
	code	= op->op_code;
	opkind = op->op_kind;
	type = op->op_type;
	if (code == I_LABEL) {
		lab_name = op->op_arg.arg_sym;
#ifdef MACHINE_CODE
		if (list_code) {
			/*TO_GEN(pretty_addr + ' '*12 + lab_name + ':');*/
			pretty_addr(code_start);
			if (ORIG_NAME(lab_name) != (char *)0) {
				sprintf(G_END, " s%du%d %s:",
				  S_SEQ(lab_name), S_UNIT(lab_name), ORIG_NAME(lab_name));
			}
			else {
				sprintf(G_END, " s%du%d:", S_SEQ(lab_name), S_UNIT(lab_name));
			}
			to_gen(G_s);
		}
#endif
		/* try labtup code TBSL 7-16-85*/
		labtup = labelmap_get(lab_name);
		eqtup = tup_copy((Tuple) labtup[LABEL_EQUAL]);
		eqtup= tup_with(eqtup, (char *) lab_name);
		FORTUP(new_lab = (Symbol), eqtup, ft1);
			/*loop forall new_lab in (EQUAL(lab_name)?{}) with lab_name do*/
			newtup = labelmap_get(new_lab);
			newtup[LABEL_POSITION] = (char *) PC();
			patch_tup = (Tuple) labtup[LABEL_PATCHES];
			FORTUP(loc = (unsigned int), patch_tup, ft2);
				/*loop forall loc in (PATCHES(new_lab)?{}) do*/
				patch_code((unsigned) loc, (unsigned) PC());
			ENDFORTUP(ft2);
		ENDFORTUP(ft1);
		/* end TBSL that am trying 7-16-85 */
		return;
	}
	else if (code == I_EQUAL) {
		/* I_EQUAL should never be generate by C version */
		chaos("I_EQUAL opcode encountered");
	}
	else if (code == I_END) {
		return;
	}

	NB_INSTRUCTIONS +=1;

	/* compute actual instructions */
	opdesc(code);
	data_mode = opdesc_d_mode;
	addressing_mode = opdesc_a_mode;
	switch (data_mode) {
	case(D_NONE):
		adj = 0;
		if (code == I_STMT) opkind = mu_word; 
		else opkind = mu_byte;
		break;

	case(D_ALL):
		adj = adjust(opkind);
		break;

	case(D_INT):
		adj = int_adjust(opkind);
		break;

	case(D_FIX):
		adj = fix_adjust(opkind);
		break;

	case(D_FLOAT):
		adj = float_adjust(opkind);
		break;

	case(D_PSEUDO):
		adj = 0;
	}

	if (code == I_DATA || code == I_CASE_TABLE) {
		/* Note that I_CASE_TABLE calls generated as gen_ks so that value
		 * below corresponds to k part, location to s part.   ds 7-5-85
		 */
		if (list_code) {
			pretty_addr(code_start);
			sprintf(G_END, " [");
		}
		/* pseudo instructions */
		if (code == I_DATA) { /* argument is integer */
			asm_int(op->op_arg.arg_int);
		}
		else {  /* I_CASE_TABLE */
			value = opkind;
			lab_name = op->op_arg.arg_sym;
			labtup = labelmap_get(lab_name);
			loc = (int)labtup[LABEL_POSITION];
			if (loc == 0) { /* 0 indicates not yet defined */
				patch_tup = (Tuple)labtup[LABEL_PATCHES];
				/*PATCHES(location) = (PATCHES(location)?{}) with PC;*/
				labtup[LABEL_PATCHES] = (char *) tup_with(
				  (Tuple) labtup[LABEL_PATCHES], (char *) (PC()+sizeof(int)-1));
				loc = 0;
			}
			/*instruction = [value, loc];*/
			asm_int(value);
			asm_int(loc);
		}
	}
	else {
#ifdef MACHINE_CODE
		if (list_code) {
			pretty_addr(code_start);
			sprintf(G_END, " [");
			/*inst_string = pretty_map(code)+' ';*/
		}
#endif
		switch ( addressing_mode) {

		case(A_NONE):
			asm_byte(code+adj);
			break;

		case(A_BOTH):
			adj = 2*adj;
			if (type == OP_REF) { /* if explicit ref */
				eref = op->op_arg.arg_ref;
				addr_mode   = A_GLOBAL;
				asm_byte(code+adj);
				asm_seg(eref->explicit_ref_seg);
				asm_off(eref->explicit_ref_off);
				/*obj_name    = str obj_name;*/
			}
			else {
#ifdef MACHINE_CODE
				if (list_code) obj_name = op->op_arg.arg_sym;
#endif
				reference_of(op->op_arg.arg_sym);
				if (REFERENCE_SEGMENT == 0 ) {
					addr_mode   = A_LOCAL;
					/*instruction = [code+adj+1, REFERENCE_OFFSET];*/
					asm_byte(code+adj+1);
					asm_off(off = (int) REFERENCE_OFFSET);
				}
				else {
					addr_mode   = A_GLOBAL;
					asm_byte(code+adj);
					asm_seg(REFERENCE_SEGMENT);
					asm_off((int) REFERENCE_OFFSET);
					/*instruction = [code+adj, b, off];*/
				}
			}
			break;

		case(A_LOCAL):
			if (type == OP_REF) { /* if explicit ref */
				eref = op->op_arg.arg_ref;
				off = eref->explicit_ref_off;
			}
			else {
#ifdef MACHINE_CODE
				if (list_code) obj_name = op->op_arg.arg_sym;
#endif
				reference_of(op->op_arg.arg_sym);
				off = REFERENCE_OFFSET;
			}
			addr_mode   = A_LOCAL;
			asm_byte(code+adj);
			/*instruction = [code+adj, off];*/
			asm_off(off);
			break;

		case(A_GLOBAL):
			if (type == OP_REF) { /* if explicit */
				eref = op->op_arg.arg_ref;
				b = eref->explicit_ref_seg;
				off = eref->explicit_ref_off;
			}
			else {
#ifdef MACHINE_CODE
				if (list_code) obj_name = op->op_arg.arg_sym;
#endif
				reference_of(op->op_arg.arg_sym);
				b = REFERENCE_SEGMENT;
				off = REFERENCE_OFFSET;
			}
			addr_mode   = A_GLOBAL;
			/*instruction = [code+adj, b, off];*/
			asm_byte(code+adj);
			asm_seg(b);
			asm_off(off);
			break;

		case(A_CODE):
			labtup = labelmap_get(op->op_arg.arg_sym);
			/* arg corresponds to SETL location*/
			loc = (int) labtup[LABEL_POSITION];
			if (loc == 0) {
				/*PATCHES(location) = (PATCHES(location)?{}) with PC;*/
				labtup[LABEL_PATCHES] = (char *) tup_with( (Tuple)
				  labtup[LABEL_PATCHES], (char *)PC());
				loc= 0;
			}
			/*instruction = [code+adj, loc];*/
			asm_byte(code+adj);
			asm_off(loc);
			break;

		case(A_PREDEF):
			asm_byte(code);
			asm_byte(op->op_arg.arg_int);
			break;

		case(A_EXCEPTION):
			/* The argument is a symbol from which we need to get the
			 * exception number
			 */
			/*instruction = [code, EXCEPTION_SLOTS(obj_name fromb param)];*/
			asm_byte(code);
			obj_name = op->op_arg.arg_sym;
			asm_exception(obj_name);
			break;

		case(A_IMM):
			asm_byte(code+adj);
			if (type == OP_INT) { /* handle integer immediate values */
				if(code == I_TERMINATE || code == I_END_ACTIVATION) {
					asm_byte(op->op_arg.arg_int);
				}
				else {
					asm_int(op->op_arg.arg_int);
				}
			}
			else if  (type == OP_FIX) {
				asm_fix(op->op_arg.arg_fix);
			}
			else if (type == OP_FLT) {
				asm_flt(op->op_arg.arg_flt);
			}
			else {
#ifdef DEBUG
				zpop(op);
#endif
				chaos("gen.c A_IMM not supported for this case");
			}
			break;

		case(A_ATTR):
			/* k field gives attribute number, arg field is integer constant */
			asm_byte(code);
			asm_byte(op->op_kind);
			if (op->op_kind == ATTR_O_LENGTH || op->op_kind == ATTR_O_FIRST
			  || op->op_kind == ATTR_O_LAST || op->op_kind == ATTR_O_RANGE) {
				asm_int(op->op_arg.arg_int);
			}
		}
	}
#ifdef MACHINE_CODE
	/* generating optional print-out */
	if (list_code) {
		sprintf(G_END, " ]");
		{
			int i, n;
#define I_MARGIN 27
			n =  I_MARGIN - strlen(G_s);/*pad count */
			if (n > 0) {
				for (i = strlen(G_s); i<I_MARGIN; i++) { /* pad out string */
					G_s[i] = ' ';
				}
				G_s[I_MARGIN] = '\0';
			}
		}
		sprintf(G_END, "%s ", opdesc_name);
		switch (data_mode) {

		case(D_NONE):
			break;

		case(D_ALL): 
		case(D_INT): 
		case(D_FIX):
			/*inst_string += kind+' ';*/
			sprintf(G_END, "%s ", g_kind(opkind));
			break;

		case(D_FLOAT):
			if (opkind == mu_xlng) {
				/*inst_string += kind+' ';*/
				sprintf(G_END, "xlng ");
			}
			break;

		case(D_PSEUDO):
			break;
		}

		if (code == I_DATA || code == I_CASE_TABLE) {
			/* pseudo instructions */
			if (code == I_DATA) {
				/*inst_string += str instruction(1);*/
				sprintf(G_END, "%d", op->op_arg.arg_int);
			}
			else {  /* I_CASE_TABLE */
				/*inst_string = '['+str(value)+', '+location+']';*/
				sprintf(G_END," %d  %s ", value, op->op_arg.arg_sym->orig_name);
			}
		}
		else {
			switch (addressing_mode) {

			case(A_NONE):
				break;

			case(A_BOTH): 
			case(A_LOCAL): 
			case(A_GLOBAL):
				if (addr_mode == A_LOCAL) {
					/* SETL 'obj_name' corresonds to C 'arg' (check this TBSL)*/
					if (tup_mem((char *) obj_name , PARAMETER_SET)) {
						/*inst_string += 'param ';*/
						sprintf(G_END, "param");
					}
					else if (off < 0 ) {
						/*inst_string += 'local ';*/
						sprintf(G_END, "local ");
					}
					else {
						/*inst_string += 'relay ';*/
						sprintf(G_END, "relay ");
					}
				}
				/*inst_string += obj_name;*/
				/* TBSL: get obj_name right in instruction dump*/
				if (obj_name != (Symbol)0) {
					sprintf(G_END, " s%du%d %s", S_SEQ(obj_name),
					  S_UNIT(obj_name), ORIG_NAME(obj_name));
					/*sprintf(G_END, " OBJ_NAME ");*/
				}
				break;

			case(A_CODE):
				/*inst_string += location;*/
				/* TBSL: get "location" right in instruction dump */
				obj_name = op->op_arg.arg_sym;
				if (ORIG_NAME(obj_name) != (char *)0) {
					sprintf(G_END, " s%du%d %s", S_SEQ(obj_name),
					  S_UNIT(obj_name), ORIG_NAME(obj_name));
				}
				else {
					sprintf(G_END," s%du%d", S_SEQ(obj_name), S_UNIT(obj_name));
				}
				break;

			case(A_PREDEF):
				sprintf(G_END, " %s", predef_name(op->op_arg.arg_int));
				break;

			case(A_EXCEPTION):
				/*inst_string += obj_name;*/
				sprintf(G_END, " s%du%d %s", S_SEQ(obj_name),
				  S_UNIT(obj_name), ORIG_NAME(obj_name));
				break;

			case(A_IMM):
				/*inst_string += str(value);*/
				if (type == OP_INT)
					sprintf(G_END, " %d ", op->op_arg.arg_int);
				break;

			case(A_ATTR):
				/*inst_string += attribute_map(attr_code) +' '+ value;*/
				/* cannot use opkind below - it has been altered  ds 7-21-85*/
				sprintf(G_END, "%s %d",
				  attribute_str(op->op_kind), op->op_kind);
				break;
			}
		}
		/*inst_string += '  -- '+ (comment fromb param);*/
		if (op->op_com != (char *)0) {
			sprintf(G_END, "-- %s", op->op_com);
		}

		/*  Formatting the output */
		/* TO_GEN(pretty_addr + ' ' + RPAD(str(instruction), 14) + 
		 * ' ' * 4 + inst_string);*/
		to_gen(G_s);
	}
#endif
}

/* adjust, int_adjust, etc. correspond to constant maps at start
 * of assemble() in SETL version.
 */

static char *g_kind(int k)										/*;g_kind*/
{
	/* convert 'kind' code to string identifying operation type */
	if (k == mu_byte) return "word";
	else if (k == mu_word) return "word";
	else if (k == mu_addr) return "addr";
	else if (k == mu_long) return "long";
	else if (k == mu_dble) return "dble";
	else if (k == mu_xlng) return "xlng";
	else return "UNKN";
}

static int adjust(int k)										/*;adjust*/
{
	/* For now, convert byte ops to word form */
	if (k == mu_byte) return 1;
	else if (k == mu_word) return 1;
	else if (k == mu_addr) return 2;
	else if (k == mu_long) return 3;
	else if (k == mu_dble) return 4;
	else if (k == mu_xlng) return 5;
	else return 0;
}

static int int_adjust(int k)								/*;int_adjust*/
{
	/* For now, convert byte ops to word form */
	if (k == mu_byte) return 1;
	else if (k == mu_word) return 1;
	else if (k == mu_long) return 2;
	else return 0;
}

static int fix_adjust(int k)								/*;fix_adjust*/
{
	/* For now, convert byte ops to word form */
	if (k == mu_byte) return 1;
	else if (k == mu_word) return 1;
	else if (k == mu_long) return 2;
	else if (k == mu_xlng) return 3;
	else return 0;
}

static int float_adjust(int k)								/*;float_adjust*/
{
	if (k == mu_long) return 0;
	else if (k == mu_xlng) return 1;
	else return 0;
}

static void pretty_addr(int start)							/*;pretty_addr*/
{
	/* String representing an address in the listing */
	/*(LPAD(str CURRENT_CODE_SEGMENT, 3) +' '+ LPAD(str PC, 4))*/
	sprintf(G_END, " %2d %5d ", CURRENT_CODE_SEGMENT, start);
}

Explicit_ref explicit_ref_new(int seg, int off)			/*;explicit_ref_new*/
{
	Explicit_ref	eref;
	eref = (Explicit_ref) emalloct(sizeof(Explicit_ref_s), "explicit-ref");
	eref->explicit_ref_seg = seg;
	eref->explicit_ref_off = off;
	return eref;
}

/* asm procedures to generate actual instructions */

static void asm_exception(Symbol sym)					/*;asm_exception*/
{
	/* This procedure is called to assemble an exception name by looking up
	 * the corresponding exception value in EXCEPTION_SLOTS, failing if no
	 * value assigned.
	 */

	int	i, n, en, exists;
	Slot slot;

	n = tup_size(EXCEPTION_SLOTS);
	exists = FALSE;
	for (i = 1; i <= n; i++) {
		slot = (Slot) EXCEPTION_SLOTS[i];
		if (slot->slot_seq == S_SEQ(sym) && slot->slot_unit == S_UNIT(sym)) {
			exists  = TRUE;
			en = slot->slot_number;
			break;
		}
	}
	if (exists) {
		/* might want byte not word here, but use word as first cut */
		asm_int(en);
	}
	else {
		chaos("gen.c: cannot find exception value ");
	}
}

static void asm_byte(int i)										/*;asm_byte*/
{
	/* add byte to current instruction */
	G_int(i);
	segment_put_byte(CODE_SEGMENT, i);
}

static void asm_int(int i)										/*;asm_int*/
{
	/* add int to current instruction */
	G_int(i);
	segment_put_int(CODE_SEGMENT, i);
}

static void asm_fix(long i)										/*;asm_fix*/
{
	/* add fix (long) to current instruction */
	G_fix(i);
	segment_put_long(CODE_SEGMENT, i);
}

static void asm_flt(float i)									/*;asm_flt*/
{
	/* add flt (float) to current instruction */
	G_flt(i);
	segment_put_real(CODE_SEGMENT, i);
}

static void asm_seg(int i)										/*;asm_seg*/
{
	/* add segment number to current instruction */
	G_int(i);
	segment_put_byte(CODE_SEGMENT, i);
}

static void asm_off(int i)										/*;asm_off*/
{
	/* add offset (16 bits) to current instruction */
	G_int(i);
	segment_put_word(CODE_SEGMENT,  i);
}

static void G_int(int i)										/*;G_int*/
{
#ifdef MACHINE_CODE
	if (list_code) sprintf(G_END, " %d", i);
#endif
}

static void G_fix(long i)										/*;G_fix*/
{
#ifdef MACHINE_CODE
	if (list_code) sprintf(G_END, " %ld", i);
#endif
}

static void G_flt(float f)										/*;G_flt*/
{
#ifdef MACHINE_CODE
	if (list_code) sprintf(G_END, " %e", f);
#endif
}

#ifdef DEBUG
static void zpop(Op op)											/*;zpop*/
{
	int	code;
	int		type, opkind;
	extern	int opdesc_a_mode, opdesc_d_mode;
	extern	char *opdesc_name;

	code	= op->op_code; 
	opkind = op->op_kind;
	type = op->op_type;


	printf("op code %d %s kind %d type(%d) ", code, opdesc_name, opkind, type);
	if (type == OP_FLT) printf("flt");
	else if (type == OP_FIX) printf("fix");
	else if (type == OP_INT) printf("int");
	else if (type == OP_REF) printf("ref");
	else if (type == OP_SYM) printf("sym");
	printf("\n");
}
#endif

/* print_ref_map, defined in gmisc in SETL version, is defined here
 * in C version, as it needs macros required to support GEN_flag option.
 */
/* On input-output */
/* In SETL this is used only to print the local reference map, so we
 * dispense with the argument here, LOCAL_REFERENCE_MAP being assumed
 */

void print_ref_map_local()							/*;print_ref_map_local*/
{
#ifdef MACHINE_CODE
	int	i, off, n;
	Symbol	sym;
	char 	*name, *nstr;
	if (!list_code) return;
	to_gen(" ");
	n = tup_size(LOCAL_REFERENCE_MAP);
	for (i = 1; i <= n; i += 2) {
		sym = (Symbol) LOCAL_REFERENCE_MAP[i];
		off = (int) LOCAL_REFERENCE_MAP[i+1];
		if (ORIG_NAME(sym) != (char *)0) {
			name = ORIG_NAME(sym);
		}
		else {
			name = "";
		}
		if (NATURE(sym) == na_void) {
			nstr = "internal";
		}
		else {
			nstr = nature_str(NATURE(sym));
		}
		sprintf(G_s, "         %5d %s  %s", off, nstr, name);
		/*LPAD(name, 25)+'  =>  '+RPAD(str(ref), 12)+NATURE(name)?"internal");*/
		to_gen(G_s);
	}
	to_gen(" ");
#endif
}

void print_ref_map_global()							/*;print_ref_map_global*/
{
#ifdef MACHINE_CODE
	int	i, off, n, seg;
	Symbol	sym;
	char 	*name, *nstr;
	Tuple	tup;
	Gref	gref;
	if (!list_code) return;
	to_gen(" ");
	to_gen("-------- Sorted by name ");
	tup = tup_copy(global_reference_tuple);
	gref_sort(tup, 0); /* 0 for name sort*/
	n = tup_size(tup);
	for (i = 1; i <= n; i ++) {
		gref = (Gref) tup[i];
		sym = gref->gref_sym;
		seg = gref->gref_seg;
		off = gref->gref_off;
		if (ORIG_NAME(sym) != (char *)0) {
			name = ORIG_NAME(sym);
		}
		else {
			name = "";
		}
		if (NATURE(sym) == na_void) {
			nstr = "internal";
		}
		else {
			nstr = nature_str(NATURE(sym));
		}
		sprintf(G_s, "\t%s %3d %5d %s  s%du%d", name, seg, off, nstr,
		  S_SEQ(sym), S_UNIT(sym));
		/*LPAD(name, 25)+'  =>  '+RPAD(str(ref), 12)+NATURE(name)?"internal");*/
		to_gen(G_s);
	}
	gref_sort(tup, 1); /* 1 for value sort */
	to_gen("-------- Sorted by value ");
	for (i = 1; i <= n; i++) {
		gref = (Gref) tup[i];
		sym = gref->gref_sym;
		seg = gref->gref_seg;
		off = gref->gref_off;
		if (ORIG_NAME(sym) != (char *)0) {
			name = ORIG_NAME(sym);
		}
		else {
			name = "";
		}
		if (NATURE(sym) == na_void) {
			nstr = "internal";
		}
		else {
			nstr = nature_str(NATURE(sym));
		}
		sprintf(G_s, "\t%3d %5d %s %s s%du%d", seg, off, name, nstr,
		  S_SEQ(sym), S_UNIT(sym));
		/*LPAD(name, 25)+'  =>  '+RPAD(str(ref), 12)+NATURE(name)?"internal");*/
		to_gen(G_s);
	}
	to_gen(" ");
	tup_free(tup);
#endif
}

static void gref_sort(Tuple tup, int type)						/*;gref_sort*/
{
	int		n;
	n = tup_size(tup); /* three entries per reference*/
	if (type == 0)
		qsort((char *) &tup[1], n, sizeof(char *),
		 (int(*)(const void *, const void *)) gref_compare_name);
	else
		qsort((char *) &tup[1], n,  sizeof(char *), 
		 (int(*)(const void *, const void *))gref_compare_address);
}

static int gref_compare_name(Gref *pref1, Gref *pref2)	/*;gref_compare_name*/
{
	Gref	ref1, ref2;
	Symbol	sym1, sym2;
	char	*s1, *s2;
	ref1 = *pref1; 
	ref2 = *pref2;
	sym1 = ref1->gref_sym; 
	sym2 = ref2->gref_sym;
	if (ORIG_NAME(sym1) != (char *)0) s1 = ORIG_NAME(sym1);
	else s1 = "";
	if (ORIG_NAME(sym2) != (char *)0) s2 = ORIG_NAME(sym2);
	else s2 = "";
	return strcmp(s1, s2);
}

static int gref_compare_address(Gref *pref1, Gref *pref2)
													/*;gref_compare_address*/
{
	Gref	ref1, ref2;

	int seg1, off1, seg2, off2;
	ref1 = *pref1, ref2 = *pref2;
	seg1 = ref1->gref_seg; 
	seg2 = ref2->gref_seg;
	off1 = ref1->gref_off; 
	off2 = ref2->gref_off;
	if (seg1<seg2) return -1;
	else if (seg1>seg2) return 1;
	else if (off1<off2) return -1;
	else if (off1 == off2) return 0;
	else return 1;
}

static char *gs_end()									/*;gs_end*/
{
	return (G_s + strlen(G_s));
}
