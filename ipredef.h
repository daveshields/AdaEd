/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/*    +---------------------------------------------------+
      | 						  |
      | 	 I N T E R P	 P R E D E F S		  |
      | 						  |
      | 	     D E F I N I T I O N S		  |
      | 						  |
      | 		  (C Version)			  |
      | 						  |
      |   Adapted From Low Level SETL version written by  |
      | 						  |
      | 		 Monte Zweben			  |
      | 	      Philippe Kruchten 		  |
      | 	      Jean-Pierre Rosen 		  |
      | 						  |
      |    Original High Level SETL version written by	  |
      | 						  |
      | 		  Clint Goss			  |
      | 	      Tracey M. Siesser 		  |
      | 	      Bernard D. Banner 		  |
      | 	      Stephen C. Bryant 		  |
      | 		 Gerry Fisher			  |
      | 						  |
      | 	     C version written by		  |
      | 						  |
      | 	      Robert B. K. Dewar		  |
      | 						  |
      +---------------------------------------------------+
*/


/* Constants For PRDEF Operations */

#include <stdlib.h>
#include <stdio.h>
#include "config.h"
#include "int.h"
#include "predef.h"
#include "ivars.h"

/* ASCII control characters */

#define  BS   0x08
#define  HT   0x09
#define  LF   0x0a
#define  FF   0x0c
#define  CR   0x0d

/* ASCII quote character */

#define QUOTE 0x27

/* Codes used in io_mode field of AFCB */

#define SIO_IN_FILE    0	/* SEQUENTIAL_IO IN  */
#define SIO_OUT_FILE   1	/* SEQUENTIAL_IO OUT */

#define DIO_IN_FILE    0	/* DIRECT_IO IN    */
#define DIO_INOUT_FILE 1	/* DIRECT_IO INOUT */
#define DIO_OUT_FILE   2	/* DIRECT_IO OUT   */

#define TIO_IN_FILE    0	/* TEXT_IO IN  */
#define TIO_OUT_FILE   1	/* TEXT_IO OUT */

/* Utility macros to access attributes of current file */

#define IOFDESC 	   (afcbs[filenum-1]->io_fdesc)
#define IOFNAME 	   (afcbs[filenum-1]->io_fname)
#define IOFORM		   (afcbs[filenum-1]->io_form)
#define IOMODE		   (afcbs[filenum-1]->io_mode)
#define DPOS		   (afcbs[filenum-1]->dio_pos)
#define DSIZE		   (afcbs[filenum-1]->dio_size)
#define DLENGTH 	   (afcbs[filenum-1]->dio_length)
#define PAGE		   (afcbs[filenum-1]->tio_page)
#define LINE		   (afcbs[filenum-1]->tio_line)
#define COL		   (afcbs[filenum-1]->tio_col)
#define LINE_LENGTH	   (afcbs[filenum-1]->tio_line_length)
#define PAGE_LENGTH	   (afcbs[filenum-1]->tio_page_length)
#define CHARS		   (afcbs[filenum-1]->tio_count)
#define CHAR1		   (afcbs[filenum-1]->tio_look_ahead[0])
#define CHAR2		   (afcbs[filenum-1]->tio_look_ahead[1])
#define CHAR3		   (afcbs[filenum-1]->tio_look_ahead[2])

/* Macros testing file attributes */

#define BOUNDED_LINE_LENGTH    (LINE_LENGTH > 0)
#define UNBOUNDED_LINE_LENGTH  (LINE_LENGTH == 0)
#define BOUNDED_PAGE_LENGTH    (PAGE_LENGTH > 0)
#define UNBOUNDED_PAGE_LENGTH  (PAGE_LENGTH == 0)
#define PAGE_TERMINATED (COL == 1 && LINE == 1 && PAGE != 1)

/* Maximum identifier length */

#define  MAX_ID 	   80

/* Define special characters in text file */

#define PAGE_MARK  0x0C 	       /* page terminator */
#define LINE_FEED  0x0a 	       /* line terminator */

/* Convert character to upper case */

#define UPPER_CASE(x) (('a' <= (x) && (x) <= 'z') ? (x - 32) : x)

/* Forward definitions for value returning functions */

int scan_integer();
int scan_integer_string();
long scan_fixed();
long scan_fixed_string();
float scan_float();
float scan_float_string();
int get_argument_value();
float get_float_argument_value();
long get_long_argument_value();
int *get_argument_ptr();

char get_char();
char *make_string();
char *predef_alloc();

/* On the PC, need to distinguish binary and text files, so use
 * fopen_bin and fopen_txt, respectively. On other machines, this
 * distinction need not be made, so fopen_bin and fopen_txt are
 * macros.
 */
#ifdef IBM_PC
FILE *fopen_bin();
FILE *fopen_txt();
#else
#define fopen_bin(a,b) fopen(a,b)
#define fopen_txt(a,b) fopen(a,b)
#endif

#define COUNT_LAST 32767
#define LOWER_CASE 0

#define DISCARD_GENERIC_PARAMETER cur_stackptr -= 2

/* if DEBUG_PREDEF defined, get detailed trace on IO operations
 * using pchar and gchar; these are made into null macros if
 * the trace is not desired.
 */
#ifndef DEBUG_PREDEF
#define pchar(a,b)
#define gchar(a,b)
#endif
