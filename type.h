/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* type.h - combined header file for types and templates for use
 * by generator and interpreter 
 */

/* Type codes (stored in first word of type template) */

#define TT_I_RANGE		     0
#define TT_L_RANGE		     1
#define TT_FL_RANGE		     2
#define TT_ENUM			     3
#define TT_E_RANGE		     4
#define TT_FX_RANGE		     5
#define TT_ACCESS		     6
#define TT_U_ARRAY		     7
#define TT_C_ARRAY		     8
#define TT_S_ARRAY		     9
#define TT_D_ARRAY		     10
#define TT_RECORD		     11
#define TT_U_RECORD		     12
#define TT_V_RECORD		     13
#define TT_C_RECORD		     14
#define TT_D_RECORD		     15
#define TT_TASK			     16
#define TT_SUBPROG		     17


/* Type templates represent Ada types at interpretor run time */

/* The first two fields (ints) of all type templates contain the type code */
/* (from the above) list in the first word, and the length of the object in */
/* the second word. The following are for accessing these two fields */

#define TYPE(ptr)	      (*ptr)
#define SIZE(ptr)	      (*(ptr + 1))


/* Integer range template */

struct tt_i_range {
   int	       ttype;
   int	       object_size;
   int	       ilow;
   int	       ihigh;
};


#ifdef LONG_INT
/* Long integer range template */
/* Note that long integers are not supported by this version */
struct tt_l_range {
   int	       ttype;
   int	       object_size;
   long	       llow;
   long	       lhigh;
};
#endif


/* Enumeration (sub)type template */
/* This is used for both tt_enum and tt_e_range types in SETL version.
 * fields ebase and eoff are base and offset for base type for tt_e_range
 * case and are not defined (zero) for tt_enum case.
 * For tt_enum case, literal values immediately follow, one for each
 * case in the range. Each literal value consists of word giving length
 * of value followed by that number of further words (with one character
 * per word) giving the characters of the literal.
 */
struct tt_e_range {
   int	       ttype;
   int	       object_size;
   int	       elow;
   int	       ehigh;
   int	       ebase;		/* only in enumeration subtype */
   int	       eoff;		/* only in enumeration subtype */
};


/* Floating point template */

struct tt_fl_range {
   int	       ttype;
   int	       object_size;
   double       fllow;
   double       flhigh;
};


/* Fixed point template */

struct tt_fx_range {
   int	       ttype;
   int	       object_size;
   int	       small_exp_2;
   int	       small_exp_5;
   long	       fxlow;
   long	       fxhigh;
};


/* Access template */

struct tt_access {
   int		   ttype;
   int		   object_size;
   int		   master_task;
   int		   master_bfp;
   int		   collection_size;
   int		   collection_avail;
};


/* Simple array template */

struct tt_s_array {
   int		   ttype;
   int		   object_size;
   int		   component_size;
   int		   index_size;
   int		   salow;
   int		   sahigh;
};


/* Unconstrained or constrained array template */

struct tt_array {
   int		   ttype;
   int		   object_size;
   int		   dim;
   int		   component_base;
   int		   component_offset;
   int		   index1_base;
   int		   index1_offset;
};


/* Template for unconstrained record */

struct tt_u_record {
   int		   ttype;
   int		   object_size;
   int		   repr_size; 
   int		   nb_field_u;
   int		   nb_discr_u;
   int		   nb_fixed_u;
   int		   variant;
   int		   first_case;
   /* field table follows here */
};


/* Template for constrained record */

struct tt_c_record {
   int		   ttype;
   int		   object_size;
   int		   repr_size; 
   int		   cbase;
   int		   coff;
   int		   nb_discr_c;
   /* discriminant values follow here */
};


/* Template for simple record */

struct tt_record {
   int		   ttype;
   int		   object_size;
   int		   repr_size; 
   int		   nb_field;
   /* field table follows here */
};


/* Template for types depending on discriminants */

struct tt_d_type {
   int		   ttype;
   int		   object_size;
   int		   repr_size; 
   int		   dbase;
   int		   doff;
   int		   nb_discr_d;
   /* entries for discriminants follow here */
};


/* Task type template */

struct tt_task {
   int		   ttype;
   int		   object_size;
   int		   collection_size;
   int		   collection_avail;
   int		   priority;
   int		   body_base;
   int		   body_off;
   int		   nb_entries;
   int		   nb_families;
   /* entry table follows here */
};


/* Subprogram template */

struct tt_subprog {
   int		   ttype;
   int		   object_size;
   int		   cs;
   int		   relay_slot;
   /* relay set entries follow here */
};

/* Look at pointers with type changed to pointer to type template */
/* Typical usage is XXX(ptr)->fieldname, where XXX is template name */

#define FL_RANGE(ptr)	      ((struct tt_fl_range *)ptr)
#define FX_RANGE(ptr)	      ((struct tt_fx_range *)ptr)
#define E_RANGE(ptr)	      ((struct tt_e_range  *)ptr)
#define I_RANGE(ptr)	      ((struct tt_i_range  *)ptr)
#define L_RANGE(ptr)	      ((struct tt_l_range  *)ptr)
#define ACCESS(ptr)	      ((struct tt_access   *)ptr)
#define S_ARRAY(ptr)	      ((struct tt_s_array  *)ptr)
#define ARRAY(ptr)	      ((struct tt_array	   *)ptr)
#define TASK(ptr)	      ((struct tt_task	   *)ptr)
#define SUBPROG(ptr)	      ((struct tt_subprog  *)ptr)
#define RECORD(ptr)	      ((struct tt_record   *)ptr)
#define D_TYPE(ptr)	      ((struct tt_d_type   *)ptr)
#define U_RECORD(ptr)	      ((struct tt_u_record *)ptr)
#define C_RECORD(ptr)	      ((struct tt_c_record *)ptr)


/* Size of templates in words (int's), not including variable fields */

#define WORDS_FL_RANGE	      (sizeof(struct tt_fl_range) / sizeof(int))
#define WORDS_FX_RANGE	      (sizeof(struct tt_fx_range) / sizeof(int))
#define WORDS_E_RANGE	      (sizeof(struct tt_e_range)  / sizeof(int))
#define WORDS_I_RANGE	      (sizeof(struct tt_i_range)  / sizeof(int))
#define WORDS_L_RANGE	      (sizeof(struct tt_l_range)  / sizeof(int))
#define WORDS_ACCESS	      (sizeof(struct tt_access)	  / sizeof(int))
#define WORDS_S_ARRAY	      (sizeof(struct tt_s_array)  / sizeof(int))
#define WORDS_ARRAY	      (sizeof(struct tt_array)	  / sizeof(int))
#define WORDS_TASK	      (sizeof(struct tt_task)	  / sizeof(int))
#define WORDS_SUBPROG	      (sizeof(struct tt_subprog)  / sizeof(int))
#define WORDS_RECORD	      (sizeof(struct tt_record)	  / sizeof(int))
#define WORDS_D_TYPE	      (sizeof(struct tt_d_type)	  / sizeof(int))
#define WORDS_U_RECORD	      (sizeof(struct tt_u_record) / sizeof(int))
#define WORDS_C_RECORD	      (sizeof(struct tt_c_record) / sizeof(int))

/* FLOAT corresonds to SETL float.Since C uses doubles, we use double
 * conversion.
 */
#define FLOAT(x) ((double) (x))
#ifdef OLD
-- old GEN codes
#define TT_I_RANGE                      1
#define TT_F_RANGE                      2
#define TT_ENUM                         3
#define TT_E_RANGE                      4
#define TT_FIXED                        5
#define TT_ACCESS                       6
#define TT_U_ARRAY                      7
#define TT_C_ARRAY                      8
#define TT_S_ARRAY                      9
#define TT_D_ARRAY                     10
#define TT_RECORD                      11
#define TT_U_RECORD                    12
#define TT_V_RECORD                    13
#define TT_C_RECORD                    14
#define TT_D_RECORD                    15
#define TT_TASK                        16
#define TT_SUBPROG                     17
#endif
#ifdef GEN
/* TT_I_RANGE_L is introduced in first C version for long case (4 bytes)*/

/* TT_OBJECT_SIZE is offset in words from start of template to tt_object fiel.d
 * This is needed in generating code for evaluting object_size of templates
 * at run-time (cf type.c).
 */
#define TT_OBJECT_SIZE 1

/*S+ fields in enumeration (sub)type */
/* In the C version, TT_E_RANGE_HIGH depends on the length of the enumeration
 * type and immediately followed TT_E_RANGE_LOW.
 */

/* The SETL table of the corresponding literals is represented in C
 * as two vectors.The first has one entry for each literal giving the
 * the length of the literal. This vector is followed the values of
 * the literals. To find the position of the i-th literal we add together
 * the lengths of the literals with index less than i.
 */


/*S+ fields in fixed point type */
/* TBSL: for now assume, only 4 byte case, for VAX */
/* The SETL definitions are misleasing in that ..range_low+1 is used
 * for second word of multi-word case, etc.
 */


#endif


/*
 * TYPE_OFF gives the offset (in int's) of a field in a template
 * (This is an example of C at its worst!)
 */
#define WORD_OFF(str, fld)   ( ((int)&(((struct str *)0)->fld)) / sizeof(int))
