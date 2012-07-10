/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/*    +---------------------------------------------------+
      |                                                   |
      |          I N T E R P     P R E D E F S            |
      |                  (C Version)                      |
      |                                                   |
      |   Adapted From Low Level SETL version written by  |
      |                                                   |
      |                  Monte Zweben                     |
      |               Philippe Kruchten                   |
      |               Jean-Pierre Rosen                   |
      |                                                   |
      |    Original High Level SETL version written by    |
      |                                                   |
      |                   Clint Goss                      |
      |               Tracey M. Siesser                   |
      |               Bernard D. Banner                   |
      |               Stephen C. Bryant                   |
      |                  Gerry Fisher                     |
      |                                                   |
      |              C version written by                 |
      |                                                   |
      |               Robert B. K. Dewar                  |
      |                                                   |
      +---------------------------------------------------+ */

/* This module contains routines for the implementation of some of
 * the predefined Ada packages and routines, namely SEQUENTIAL_IO,
 * DIRECT_IO, TEXT_IO, and CALENDAR. Part 1 contains the PREDEF
 * routine which executes a predefined operation.
*/

#include <stdlib.h>
#include <setjmp.h>
#include <string.h>
#include "ipredef.h"
#include "intbprots.h"
#include "intcprots.h"
#include "predefprots.h"

/*
 * Environment variable to save stack pointer for PREDEF_RAISE. On entry to
 * PREDEF, raise_env saves the stack environment (using set_jmp). If an Ada
 * exception is signalled, then the PREDEF_RAISE routine raises the exception
 * using the usual raise procedure, and then exits directly at the top level
 * of the PREDEF procedure, using longjmp.
 */

jmp_buf raise_env;

static int string_offset(int *);

/* Procedure called by main interpreter to execute predefined operation. The
 * operation code has been read from the code stream and is passed as the
 * parameter. The remaining parameters are stacked as needed.
*/

void predef()                                /*;predef*/
{
	/* This procedure handles all predefined operations. It is passed a marker
	 * which determines the operation to be performed. The formal parameters of
	 * the original call have been evaluted onto CURSTACK, but must not be
	 * popped as then will be discarded by the code. In the case of generic
	 * procedures, the type template address is pushed on the parameters AND
	 *  MUST BE POPPED!
	 */

	/* First capture environment for use by PREDEF_RAISE */

	if (setjmp(raise_env))
		return;

	/* Switch on the operation code */

	switch(operation) {


		/* 14.2.1  FILE MANAGEMENT */


		/* SEQUENTIAL_IO:                                     */
		/* procedure CREATE(FILE  : in out FILE_TYPE;         */
		/*                  MODE  : in FILE_MODE := OUT_FILE; */
		/*                  NAME  : in STRING    := "";       */
		/*                  FORM  : in STRING    := "");      */

	case P_SIO_CREATE:
		{
			open_seq_io('C');
			break;
		}


		/* DIRECT_IO:                                          */
		/* procedure CREATE(FILE : in out FILE_TYPE;           */
		/*                  MODE : in FILE_MODE := INOUT_FILE; */
		/*                  NAME : in STRING    := "";         */
		/*                  FORM : in STRING    := "");        */

	case P_DIO_CREATE:
		{
			open_dir_io('C');
			break;
		}


		/* TEXT_IO:                                           */
		/* procedure CREATE(FILE : in out FILE_TYPE;          */
		/*                  MODE : in FILE_MODE := OUT_FILE;  */
		/*                  NAME : in STRING    := "";        */
		/*                  FORM : in STRING    := "");       */

	case P_TIO_CREATE:
		{
			open_textio('C');
			break;
		}


		/*  SEQUENTIAL_IO:                           */
		/*  procedure OPEN(FILE : in out FILE_TYPE;  */
		/*                 MODE : in FILE_MODE;      */
		/*                 NAME : in STRING;         */
		/*                 FORM : in STRING := "");  */

	case P_SIO_OPEN:
		{
			open_seq_io('O');
			break;
		}


		/* DIRECT_IO:                                */
		/* procedure OPEN(FILE : in out FILE_TYPE;   */
		/*                MODE : in FILE_MODE;       */
		/*                NAME : in STRING;          */
		/*                FORM : in STRING := "");   */

	case P_DIO_OPEN:
		{
			open_dir_io('O');
			break;
		}


		/* TEXT_IO:                                  */
		/* procedure OPEN(FILE : in out FILE_TYPE;   */
		/*                MODE : in FILE_MODE;       */
		/*                NAME : in STRING;          */
		/*                FORM : in STRING := "");   */

	case P_TIO_OPEN:
		{
			open_textio('O');
			break;
		}


		/* procedure CLOSE(FILE : in out FILE_TYPE); */

	case P_SIO_CLOSE:
	case P_DIO_CLOSE:
	case P_TIO_CLOSE:
		{
			int    *file_ptr;

			file_ptr = get_argument_ptr(0);
			filenum = *file_ptr;
			check_file_open();

			*file_ptr = 0;

			if (operation == P_SIO_CLOSE || operation == P_DIO_CLOSE)
				close_file();
			else /* operation == P_TIO_CLOSE */
				close_textio();
			break;
		}

		/*  procedure DELETE(FILE : in out FILE_TYPE); */

	case P_SIO_DELETE:
	case P_DIO_DELETE:
	case P_TIO_DELETE:
		{
			int    *file_ptr;

			file_ptr = get_argument_ptr(0);
			filenum = *file_ptr;
			check_file_open();

			strcpy(work_string, IOFNAME);

			if (operation == P_SIO_DELETE || P_DIO_DELETE)
				close_file();
			else /* operation == P_TIO_DELETE */
				close_textio();
			unlink(work_string);

			*file_ptr = 0;
			break;
		}


		/*  SEQUENTIAL_IO:                                                 */
		/*  procedure RESET(FILE : in out FILE_TYPE; MODE : in FILE_MODE); */
		/*  procedure RESET(FILE : in out FILE_TYPE);                      */

	case P_SIO_RESET:
	case P_SIO_RESET_MODE:
		{
			int	newmode;

			DISCARD_GENERIC_PARAMETER;
			get_filenum();
			check_file_open();

			if (operation == P_SIO_RESET_MODE) {
				newmode = get_argument_value(2);
			}
			else
				newmode = IOMODE;

			fclose(IOFDESC);

			if (newmode == SIO_IN_FILE) {
				IOFDESC = fopen_bin(IOFNAME, "r");
				check_opened_ok();
			}
			else {
				IOFDESC = fopen_bin(IOFNAME, "r+");
				check_opened_ok();
			}
			IOMODE = newmode;
			break;
		}

		/* DIRECT_IO:                                                       */
		/* procedure RESET (FILE : in out FILE_TYPE;  MODE : in FILE_MODE); */
		/* procedure RESET (FILE : in out FILE_TYPE);                       */

	case P_DIO_RESET:
	case P_DIO_RESET_MODE:
		{
			int	newmode;

			DISCARD_GENERIC_PARAMETER;
			get_filenum();

			check_file_open();

			if (operation == P_DIO_RESET_MODE)
				newmode = get_argument_value(2);
			else
				newmode = IOMODE;

			fclose(IOFDESC);

			if (newmode == DIO_IN_FILE) {
				IOFDESC = fopen_bin(IOFNAME, "r");
			}
			else {
				IOFDESC = fopen_bin(IOFNAME, "r+");
			}
			check_opened_ok();

			IOMODE = newmode;
			DPOS = 1;
			break;
		}

		/* TEXT_IO:                                                       */
		/* procedure RESET(FILE : in out FILE_TYPE; MODE : in FILE_MODE); */
		/* procedure RESET(FILE : in out FILE_TYPE);                      */

	case P_TIO_RESET:
	case P_TIO_RESET_MODE:
		{
			int     newmode;

			get_filenum();
			check_file_open();

			if (operation == P_TIO_RESET_MODE) {
				newmode = get_argument_value(2);

				/* Raise MODE_ERROR on attempt to change the mode of the
                 * current default input or output file. */

				if ((filenum == current_in_file || filenum == current_out_file)
				  && newmode != IOMODE) {
					predef_raise(MODE_ERROR, "Cannot change mode");
				}
			}
			else
				newmode = IOMODE;

			if (IOMODE == TIO_OUT_FILE) {

				/* Simulate NEW_PAGE unless current page already terminated */

				if (!PAGE_TERMINATED) {
					if (COL > 1 ||(COL == 1 && LINE == 1)) {
						put_line();
					}
					put_page();
				}
			}

			fclose(IOFDESC);

			if (newmode == TIO_IN_FILE) {
				IOFDESC = fopen_txt(IOFNAME, "r");
				check_opened_ok();
			}
			else {
				IOFDESC = fopen_txt(IOFNAME, "r+");
				check_opened_ok();
				LINE_LENGTH = 0;
				PAGE_LENGTH = 0;
			}

			IOMODE = newmode;
			CHARS = 0;
			COL = 1;
			LINE = 1;
			PAGE = 1;
			break;
		}

		/* function MODE(FILE : in FILE_TYPE) return FILE_MODE; */

	case P_SIO_MODE:
	case P_DIO_MODE:
	case P_TIO_MODE:
		{
			get_filenum();
			check_file_open();
			TOSM(2) = IOMODE;
			break;
		}


		/* function NAME(FILE : in FILE_TYPE) return STRING; */

	case P_SIO_NAME:
	case P_DIO_NAME:
	case P_TIO_NAME:
		{
			get_filenum();
			check_file_open();
			return_string(IOFNAME, 2);
			break;
		}


		/* function FORM(FILE : in FILE_TYPE) return STRING; */

	case P_SIO_FORM:
	case P_DIO_FORM:
	case P_TIO_FORM:
		{
			get_filenum();
			check_file_open();
			return_string(IOFORM, 2);
			break;
		}


		/* function IS_OPEN(FILE : in FILE_TYPE) return BOOLEAN; */

	case P_SIO_IS_OPEN:
	case P_DIO_IS_OPEN:
	case P_TIO_IS_OPEN:
		{
			get_filenum();
			TOSM(2) = (filenum != 0);
			break;
		}



		/* 14.2.2  SEQUENTIAL INPUT-OUTPUT */


		/* procedure READ(FILE : in FILE_TYPE; ITEM : out ELEMENT_TYPE); */

	case P_SIO_READ:
		{
			int     *item_tt_ptr;
			int     *item_ptr;
			int     length, lread;
			int     type;

			POP_PTR(item_tt_ptr);          /* pop generic type */

			/* If the type is an array, then we have an extra entry
                 * on the stack, which is the descriptor for the actual
                 * array value. In this case we want to use the length
                 * from the actual value, rather than from the generic
                 * template. In other cases, the length comes from the
                 * generic template */

			type = TYPE(item_tt_ptr);
			if (type == TT_C_ARRAY || type == TT_S_ARRAY ||
			    type == TT_D_ARRAY) {
				item_tt_ptr = get_argument_ptr(2);
				item_ptr = get_argument_ptr(4);
			}
			else {
				item_ptr = get_argument_ptr(2);
			}

			length = SIZE(item_tt_ptr);

			get_filenum();

			check_status(SIO_IN_FILE);

			lread = fread(item_ptr,sizeof(int),length,IOFDESC);
			if (lread == 0)
				predef_raise(END_ERROR, "End of file");
			else if (lread < length)
				predef_raise(DATA_ERROR, "Wrong length item at end of file");
			break;
		}


		/* procedure WRITE(FILE : in FILE_TYPE; ITEM : in ELEMENT_TYPE); */

	case P_SIO_WRITE:
		{
			int     *item_tt_ptr;
			int     *item_ptr;
			int     length, lwrit;
			int     type;

			POP_PTR(item_tt_ptr);      /* pop generic type parameter */

			/* If the type is an array, then we have an extra entry
                 * on the stack, which is the descriptor for the actual
                 * array value. In this case we want to use the length
                 * from the actual value, rather than from the generic
                 * template. In other cases, the length comes from the
                 * generic template */

			type = TYPE(item_tt_ptr);
			if (type == TT_C_ARRAY || type == TT_S_ARRAY ||
			    type == TT_D_ARRAY) {
				item_tt_ptr = get_argument_ptr(2);
				item_ptr = get_argument_ptr(4);
			}
			else {
				item_ptr = get_argument_ptr(2);
			}

			length = SIZE(item_tt_ptr);

			get_filenum();

			check_status(SIO_OUT_FILE);

			lwrit = fwrite(item_ptr,sizeof(int),length,IOFDESC);
			if (lwrit < length) {
				predef_raise(END_ERROR, "File full");
			}
			break;
		}


		/* function END_OF_FILE(FILE : in FILE_TYPE) return BOOLEAN; */

	case P_SIO_END_OF_FILE:
		{
			long    curpos, eofpos;

			get_filenum();
			check_status(SIO_IN_FILE);

			fseek(IOFDESC, 0L, 1);
			curpos = ftell(IOFDESC);
			fseek(IOFDESC, 0L, 2);
			eofpos = ftell(IOFDESC);
			fseek(IOFDESC, curpos, 0);
			TOSM(2) = (curpos == eofpos);
			break;
		}


		/* 14.2.4  DIRECT INPUT-OUTPUT */


		/* procedure READ(FILE : in FILE_TYPE; ITEM : out ELEMENT_TYPE);   */
		/* procedure READ(FILE : in FILE_TYPE; ITEM : out ELEMENT_TYPE;    */
		/*                                     FROM : in  POSITIVE_COUNT); */

	case P_DIO_READ:
	case P_DIO_READ_FROM:
		{
			int     *item_tt_ptr;
			int     *item_ptr;
			int     type_offset;
			int     from;
			long    newpos;
			int     type;

			POP_PTR(item_tt_ptr);      /* pop generic type parameter */

			/* If the type is an array, then we have an extra entry
                 * on the stack, which is the descriptor for the actual
                 * array value. */

			type = TYPE(item_tt_ptr);
			if (type == TT_C_ARRAY || type == TT_S_ARRAY || type == TT_D_ARRAY)
			{
				item_tt_ptr = get_argument_ptr(2);
				type_offset = 2;
			}
			else type_offset = 0;

			item_ptr = get_argument_ptr(2 + type_offset);

			get_filenum();
			check_file_open();

			if (operation == P_DIO_READ_FROM) {
				if (type == TT_RECORD) {
					from = get_argument_value(4);
				}
				else {
					from = get_argument_value(6);
				}
			}
			else from = DPOS;

			if (IOMODE == DIO_OUT_FILE) {
				predef_raise(MODE_ERROR, "Direct read from OUT file");
			}

			if (from > DSIZE) {
				predef_raise(END_ERROR, "Direct read past end of file");
			}

			newpos = (from - 1) * DLENGTH;
			fseek(IOFDESC, newpos, 0);
			fread(item_ptr, 1, DLENGTH, IOFDESC);

			DPOS = from + 1;
			break;
		}


		/* procedure WRITE(FILE : in FILE_TYPE; ITEM : in ELEMENT_TYPE); */
		/* procedure WRITE(FILE : in FILE_TYPE; ITEM : in ELEMENT_TYPE;  */
		/*                                        TO : in POSITIVE_COUNT); */

	case P_DIO_WRITE:
	case P_DIO_WRITE_TO:
		{
			int     *item_tt_ptr;
			int     *item_ptr;
			int     type_offset;
			int     to;
			long    newpos;
			int     type;

			POP_PTR(item_tt_ptr);      /* pop generic type parameter */

			/* If the type is an array, then we have an extra entry
                 * on the stack, which is the descriptor for the actual
                 * array value. */

			type = TYPE(item_tt_ptr);
			if (type == TT_C_ARRAY || type == TT_S_ARRAY || type == TT_D_ARRAY)
			{
				item_tt_ptr = get_argument_ptr(2);
				type_offset = 2;
			}
			else type_offset = 0;

			item_ptr = get_argument_ptr(2 + type_offset);
			get_filenum();
			check_file_open();

			if (operation == P_DIO_WRITE_TO) {
				to = get_argument_value(4 + type_offset);
			}
			else to = DPOS;

			if (IOMODE == DIO_IN_FILE) {
				predef_raise(MODE_ERROR, "Direct write to an IN file");
			}

			newpos = (to - 1) * DLENGTH;
			fseek(IOFDESC, newpos, 0);
			fwrite(item_ptr, 1, DLENGTH, IOFDESC);

			DPOS = to + 1;
			if (to > DSIZE) DSIZE = to;
			break;
		}


		/* procedure SET_INDEX(FILE : in FILE_TYPE; TO : in POSITIVE_COUNT); */

	case P_DIO_SET_INDEX:
		{
			get_filenum();
			check_file_open();

			DPOS = get_argument_value(2);
			break;
		}


		/* function INDEX(FILE : in FILE_TYPE) return POSITIVE_COUNT; */

	case P_DIO_INDEX:
		{
			get_filenum();
			check_file_open();

			TOSM(2) = DPOS;
			break;
		}


		/* function SIZE(FILE : in FILE_TYPE) return COUNT; */

	case P_DIO_SIZE:
		{
			get_filenum();
			check_file_open();

			TOSM(2) = DSIZE;
			break;
		}


		/* function END_OF_FILE(FILE : in FILE_TYPE) return BOOLEAN; */

	case P_DIO_END_OF_FILE:
		{
			get_filenum();
			check_file_open();

			if (IOMODE == DIO_OUT_FILE) {
				predef_raise(MODE_ERROR, "Bad mode in direct END_OF_FILE");
			}

			TOSM(2) = (DPOS > DSIZE);
			break;
		}



		/* 14.3.2  DEFAULT INPUT AND OUTPUT FILES */


		/* procedure SET_INPUT(FILE : in FILE_TYPE); */

	case P_SET_INPUT:
		{
			get_filenum();
			check_status(TIO_IN_FILE);

			current_in_file = filenum;
			/* Save a copy of the current default input file number 
			 * which can be checked after the default file is closed.
			 */
			current_in_file_saved = filenum;
			break;
		}


		/* procedure SET_OUTPUT(FILE : in FILE_TYPE); */

	case P_SET_OUTPUT:
		{
			get_filenum();
			check_status(TIO_OUT_FILE);
			current_out_file = filenum;
			/* Save a copy of the current default output file number 
			 * which can be checked after the default file is closed.
			 */
			current_out_file_saved = filenum;
			break;
		}


		/* function STANDARD_INPUT return FILE_TYPE; */

	case P_STANDARD_INPUT:
		{
			int     bse, off, *ptr;
			create(1, &bse, &off, &ptr);
			*ptr = standard_in_file;
			TOSM(1) = bse;
			TOS = off;
			break;
		}


		/* function STANDARD_OUTPUT return FILE_TYPE; */

	case P_STANDARD_OUTPUT:
		{
			int     bse, off, *ptr;
			create(1, &bse, &off, &ptr);
			*ptr = standard_out_file;
			TOSM(1) = bse;
			TOS = off;
			break;
		}


		/* function CURRENT_INPUT return FILE_TYPE; */

	case P_CURRENT_INPUT:
		{
			int     bse, off, *ptr;
			create(1, &bse, &off, &ptr);
			*ptr = current_in_file;
			TOSM(1) = bse;
			TOS = off;
			break;
		}


		/* function CURRENT_OUTPUT return FILE_TYPE; */

	case P_CURRENT_OUTPUT:
		{
			int     bse, off, *ptr;
			create(1, &bse, &off, &ptr);
			*ptr = current_out_file;
			TOSM(1) = bse;
			TOS = off;
			break;
		}


		/* 14.3.3  SPECIFICATION OF LINE AND PAGE LENGTHS */


		/* procedure SET_LINE_LENGTH(FILE : in FILE_TYPE; TO : in COUNT); */
		/* procedure SET_LINE_LENGTH(TO : in COUNT);                      */

	case P_SET_LINE_LENGTH:
	case P_SET_LINE_LENGTH_FILE:
		{
			get_file_argument_or_default();
			check_status(TIO_OUT_FILE);

			LINE_LENGTH = get_argument_value(0 + file_offset);
			break;
		}


		/* procedure SET_PAGE_LENGTH(FILE : in FILE_TYPE;   TO : in COUNT); */
		/* procedure SET_PAGE_LENGTH(TO : in COUNT);                        */

	case P_SET_PAGE_LENGTH:
	case P_SET_PAGE_LENGTH_FILE:
		{
			get_file_argument_or_default();
			check_status(TIO_OUT_FILE);

			PAGE_LENGTH = get_argument_value(0 + file_offset);
			break;
		}


		/* function LINE_LENGTH(FILE : in FILE_TYPE) return COUNT; */
		/* function LINE_LENGTH return COUNT;                      */

	case P_LINE_LENGTH:
	case P_LINE_LENGTH_FILE:
		{
			get_file_argument_or_default();
			check_status(TIO_OUT_FILE);

			TOSM(0 + file_offset) = LINE_LENGTH;
			break;
		}


		/* function PAGE_LENGTH(FILE : in FILE_TYPE) return COUNT; */
		/* function PAGE_LENGTH return COUNT;                      */

	case P_PAGE_LENGTH:
	case P_PAGE_LENGTH_FILE:
		{
			get_file_argument_or_default();
			check_status(TIO_OUT_FILE);

			TOSM(0 + file_offset) = PAGE_LENGTH;
			break;
		}


		/* 14.3.4  OPERATIONS ON COLUMNS, LINES, AND PAGES */


		/* procedure NEW_LINE(FILE : in FILE_TYPE;                */
		/*                     SPACING : in POSITIVE_COUNT := 1); */
		/* procedure NEW_LINE(SPACING : in POSITIVE_COUNT := 1);  */

	case P_NEW_LINE_FILE:
	case P_NEW_LINE:
		{
			int     spacing, i;

			get_file_argument_or_default();
			check_status(TIO_OUT_FILE);

			spacing = get_argument_value(0 + file_offset);

			for (i = 1; i <= spacing; i++) {
				put_line();
			}
			break;
		}


		/* procedure SKIP_LINE(FILE : in FILE_TYPE;               */
		/*                     SPACING : in POSITIVE_COUNT := 1); */
		/* procedure SKIP_LINE(SPACING : in POSITIVE_COUNT := 1); */

	case P_SKIP_LINE_FILE:
	case P_SKIP_LINE:
		{
			int     spacing;
			int     i;

			get_file_argument_or_default();
			check_status(TIO_IN_FILE);

			spacing = get_argument_value(0 + file_offset);

			for (i = 1; i <= spacing; i++) {
				skip_line();
			}
			break;
		}


		/* function END_OF_LINE(FILE : in FILE_TYPE) return BOOLEAN; */
		/* function END_OF_LINE return BOOLEAN;                      */

	case P_END_OF_LINE_FILE:
	case P_END_OF_LINE:
		{
			get_file_argument_or_default();
			check_status(TIO_IN_FILE);

			load_look_ahead(FALSE);
			TOSM(0 + file_offset) = (CHARS == 0 || CHAR1 == LINE_FEED);
			break;
		}


		/* procedure NEW_PAGE(FILE : in FILE_TYPE); */
		/* procedure NEW_PAGE;                      */

	case P_NEW_PAGE_FILE:
	case P_NEW_PAGE:
		{
			get_file_argument_or_default();
			check_status(TIO_OUT_FILE);

			if (COL > 1 ||(COL == 1 && LINE == 1)) {
				put_line();
			}
			put_page();
			break;
		}


		/* procedure SKIP_PAGE(FILE : in FILE_TYPE); */
		/* procedure SKIP_PAGE;                      */

	case P_SKIP_PAGE_FILE:
	case P_SKIP_PAGE:
		{
			get_file_argument_or_default();
			check_status(TIO_IN_FILE);

			while(get_char() != PAGE_MARK);
			break;
		}


		/* function END_OF_PAGE(FILE : in FILE_TYPE) return BOOLEAN; */
		/* function END_OF_PAGE return BOOLEAN;                      */

	case P_END_OF_PAGE_FILE:
	case P_END_OF_PAGE:
		{
		   int     result;

		   get_file_argument_or_default();
		   check_status(TIO_IN_FILE);

		   if (isatty(fileno(IOFDESC))) {
		      result = FALSE;
		   }
 		   else {
		      load_look_ahead(FALSE);
		      if (CHARS > 1) 
		          result = (CHAR1 == LINE_FEED && CHAR2 == PAGE_MARK);
		       else if (CHARS == 1)
		          result = (CHAR1 == LINE_FEED);
		       else    /* CHARS == 0) */
		          result = TRUE;
		   }
		   TOSM(0 + file_offset) = result;
		   break;
		}


		/* function END_OF_FILE(FILE : in FILE_TYPE) return BOOLEAN; */
		/* function END_OF_FILE return BOOLEAN;                      */

	case P_TIO_END_OF_FILE:
	case P_TIO_END_OF_FILE_FILE:
		{
		   int     result;

		   get_file_argument_or_default();
		   check_status(TIO_IN_FILE);

		   load_look_ahead(TRUE);
		   if (isatty(fileno(IOFDESC))) {
			if (CHARS == 2)
			   result = FALSE;
			else if (CHARS == 1)
			   result = (CHAR1 == LINE_FEED);
			else if (CHARS == 0)
			   result = TRUE;
		   }
		   else {
			if (CHARS == 2)
			   result = (CHAR1 == LINE_FEED && CHAR2 == PAGE_MARK);
			else if (CHARS == 1)
			   result = (CHAR1 == LINE_FEED);
			else if (CHARS == 0)
			   result = TRUE;
			else 		/* CHARS = 3 */
			   result = FALSE;
                   }
			TOSM(0 + file_offset) = result;
			break;
		}


		/* procedure SET_COL(FILE : in FILE_TYPE; TO : in POSITIVE_COUNT); */
		/* procedure SET_COL(TO : in POSITIVE_COUNT);                      */

	case P_SET_COL:
	case P_SET_COL_FILE:
		{
			int     to_val;

			get_file_argument_or_default();
			to_val = get_argument_value(0 + file_offset);
			check_file_open();

			/* SET_COL for file of mode OUT_FILE */

			if (IOMODE == TIO_OUT_FILE) {
				if (BOUNDED_LINE_LENGTH && to_val > LINE_LENGTH)
					predef_raise(LAYOUT_ERROR, "SET_COL past end of line");

				if (to_val > COL) {
					put_blanks(to_val - COL);
					COL = to_val;
				}
				else if (to_val < COL) {
					put_line();
					put_blanks(to_val - 1);
					COL = to_val;
				}
			}

			/* SET_COL for file of mode IN_FILE */

			else {
				load_look_ahead(FALSE);
				while(COL != to_val || CHAR1 == LINE_FEED || CHAR1 == PAGE_MARK)
					get_char();
			}

			break;
		}


		/* procedure SET_LINE(FILE : in FILE_TYPE;  TO : in POSITIVE_COUNT); */
		/* procedure SET_LINE(TO   : in POSITIVE_COUNT);                     */

	case P_SET_LINE:
	case P_SET_LINE_FILE:
		{
			int     to_val;
			int     i;

			get_file_argument_or_default();
			to_val = get_argument_value(0 + file_offset);
			check_file_open();

			/* SET_LINE for file of mode OUT_FILE */

			if (IOMODE == TIO_OUT_FILE) {
				if (BOUNDED_PAGE_LENGTH && to_val > PAGE_LENGTH) {
					predef_raise(LAYOUT_ERROR, "SET_LINE > PAGE_LENGTH");
				}

				if (to_val > LINE) {
					i = to_val - LINE;
					while(i--)
						put_line();
				}
				else if (to_val < LINE) {
					if (COL > 1 ||(COL == 1 && LINE == 1))
						put_line();
					put_page();
					i = to_val - 1;
					while(i--)
						put_line();
				}
			}

			/* SET_LINE for file of mode IN_FILE */

			else {
				load_look_ahead(FALSE);
				while(LINE != to_val || CHAR1 == PAGE_MARK) {
					get_char();
				}
			}
			break;
		}


		/* function COL(FILE : FILE_TYPE)  return POSITIVE_COUNT; */
		/* function COL return POSITIVE_COUNT;                    */

	case P_COL:
	case P_COL_FILE:
		{
			get_file_argument_or_default();
			check_file_open();

			if (COL > COUNT_LAST) {
				predef_raise(LAYOUT_ERROR, "COL > COUNT'LAST");
			}

			TOSM(0 + file_offset) = COL;
			break;
		}


		/* function LINE(FILE : FILE_TYPE) return POSITIVE_COUNT; */
		/* function LINE return POSITIVE_COUNT;                   */

	case P_LINE:
	case P_LINE_FILE:
		{
			get_file_argument_or_default();
			check_file_open();

			if (LINE < 0) {
				predef_raise(LAYOUT_ERROR, "LINE > COUNT'LAST");
			}

			TOSM(0 + file_offset) = LINE;
			break;
		}


		/* function PAGE(FILE : FILE_TYPE) return POSITIVE_COUNT; */
		/* function PAGE return POSITIVE_COUNT;                   */

	case P_PAGE:
	case P_PAGE_FILE:
		{
			get_file_argument_or_default();
			check_file_open();

			if (PAGE > COUNT_LAST) {
				predef_raise(LAYOUT_ERROR, "PAGE > COUNT'LAST");
			}

			TOSM(0 + file_offset) = PAGE;
			break;
		}



		/* 14.3.6  INPUT-OUTPUT OF CHARACTERS AND STRINGS */


		/* procedure GET(FILE : in FILE_TYPE; ITEM : out CHARACTER); */
		/* procedure GET(ITEM : out CHARACTER);                      */

	case P_GET_CHAR_FILE_ITEM:
	case P_GET_CHAR_ITEM:
		{
			int     *item_ptr;
			int     chr;

			get_file_argument_or_default();
			check_status(TIO_IN_FILE);

			item_ptr = get_argument_ptr(0 + file_offset);

			for (;;) {
				chr = get_char();
				if (chr != PAGE_MARK && chr != LINE_FEED)
					break;
			}
			*item_ptr = chr;
			break;
		}


		/* procedure PUT(FILE : in FILE_TYPE; ITEM : in CHARACTER); */
		/* procedure PUT(ITEM : in CHARACTER);                      */

	case P_PUT_CHAR_FILE_ITEM:
	case P_PUT_CHAR_ITEM:
		{
			get_file_argument_or_default();
			check_status(TIO_OUT_FILE);

			put_char(get_argument_value(0 + file_offset));
			break;
		}

		/* procedure GET(FILE : in FILE_TYPE; ITEM : out STRING); */
		/* procedure GET(ITEM : out STRING);                      */

	case P_GET_STRING_FILE_ITEM:
	case P_GET_STRING_ITEM:
		{
			int    *item_tt_ptr;
			int     *item_ptr;
			int     string_size;
			char    c;

			get_file_argument_or_default();
			check_status(TIO_IN_FILE);
			item_tt_ptr = get_argument_ptr(0 + file_offset);
			item_ptr    = get_argument_ptr(2 + file_offset);

			string_size = SIZE(item_tt_ptr);

			while(string_size) {
				c = get_char();
				if (c != PAGE_MARK && c != LINE_FEED) {
					*item_ptr++ = c;
					string_size--;
				}
			}
			break;
		}


		/* procedure PUT(FILE : in FILE_TYPE; ITEM : in STRING); */
		/* procedure PUT(ITEM : in STRING);                      */

	case P_PUT_STRING_FILE_ITEM:
	case P_PUT_STRING_ITEM:
		{
			get_file_argument_or_default();
			check_status(TIO_OUT_FILE);
			get_string_value(0 + file_offset);

			put_string(work_string);
			break;
		}


		/*  procedure GET_LINE(FILE : in FILE_TYPE;  ITEM : out STRING;   */
		/*                                           LAST : out INTEGER); */
		/*  procedure GET_LINE(ITEM : out STRING; LAST : out INTEGER);    */

	case P_GET_LINE_FILE:
	case P_GET_LINE:
		{
			int     *item_tt_ptr;
			int     *item_ptr;
			int     *last_ptr;
			int     string_size;
			int     nstore;
			char    c;

			get_file_argument_or_default();
			check_status(TIO_IN_FILE);

			item_tt_ptr = get_argument_ptr(0 + file_offset);
			item_ptr    = get_argument_ptr(2 + file_offset);
			last_ptr    = get_argument_ptr(4 + file_offset);

			string_size = SIZE(item_tt_ptr);
			if (string_size < 0) string_size = 0;

			nstore = 0;
			for (;;) {
				load_look_ahead(FALSE);
				if (nstore == string_size) break;
				if (CHAR1 == LINE_FEED) {
					skip_line();
					break;
				}
				c = get_char();
				*item_ptr++ = c;
				nstore ++;
			}

			/* set LAST value */

			*last_ptr = nstore + string_offset(item_tt_ptr) - 1;
			break;
		}


		/* procedure PUT_LINE(FILE : in FILE_TYPE; ITEM : in STRING); */
		/* procedure PUT_LINE(ITEM : in STRING);                      */

	case P_PUT_LINE_FILE:
	case P_PUT_LINE:
		{
			get_file_argument_or_default();
			check_status(TIO_OUT_FILE);

			get_string_value(0 + file_offset);
			put_string(work_string);
			put_line();
			break;
		}


		/* 14.3.7  INPUT-OUTPUT FOR INTEGER TYPES */


		/* type NUM is range <>;                                        */
		/* procedure GET(FILE : in FILE_TYPE;  ITEM : out NUM;         */
		/*                                      WIDTH : in FIELD := 0); */
		/* procedure GET(ITEM : out NUM;  WIDTH : in FIELD := 0);      */

	case P_GET_INTEGER_FILE_ITEM:
	case P_GET_INTEGER_ITEM:
		{
			int     *item_tt_ptr;
			int     *item_ptr;
			int     width;

			POP_PTR(item_tt_ptr);      /* pop generic type parameter */

			get_file_argument_or_default();
			check_status(TIO_IN_FILE);

			item_ptr = get_argument_ptr(0 + file_offset);
			width = get_argument_value(4 + file_offset);

			*item_ptr = scan_integer(item_tt_ptr, width);
			break;
		}


		/* procedure PUT(FILE  : in FILE_TYPE;                     */
		/*                ITEM  : in NUM;                          */
		/*                WIDTH : in FIELD       := DEFAULT_WIDTH; */
		/*                BASE  : in NUMBER_BASE := DEFAULT_BASE); */

		/* procedure PUT(ITEM  : in NUM;                           */
		/*               WIDTH : in FIELD       := DEFAULT_WIDTH;  */
		/*               BASE  : in NUMBER_BASE := DEFAULT_BASE);  */

	case P_PUT_INTEGER_FILE_ITEM:
	case P_PUT_INTEGER_ITEM:
		{
			int     item, width, a_base;

			DISCARD_GENERIC_PARAMETER;

			get_file_argument_or_default();
			check_status(TIO_OUT_FILE);

			item = get_argument_value(0 + file_offset);
			width = get_argument_value(2 + file_offset);
			a_base = get_argument_value(4 + file_offset);

			image_integer(item, a_base);
			put_buffer(work_string, width, 'L');
			break;
		}


		/* procedure
		 *   GET(FROM : in STRING; ITEM : out NUM; LAST : out POSITIVE);
		 */

	case P_GET_INTEGER_STRING:
		{
			int     *item_tt_ptr;
			int     *from_tt_ptr;
			int     *item_ptr;
			int     *last_ptr;
			int     last;

			POP_PTR(item_tt_ptr);      /* pop generic type parameter */

			get_string_value(0);
			from_tt_ptr = get_argument_ptr(0);
			item_ptr    = get_argument_ptr(4);
			last_ptr    = get_argument_ptr(8);

			*item_ptr = scan_integer_string(item_tt_ptr, &last);

			last += string_offset(from_tt_ptr) ;
			*last_ptr = last;
			break;
		}


		/* procedure PUT(TO   : out STRING;                       */
		/*               ITEM : in  NUM;                          */
		/*               BASE : in  NUMBER_BASE := DEFAULT_BASE); */

	case P_PUT_INTEGER_STRING:
		{
			int     *to_tt_ptr;
			int     *to_ptr;
			int     item, a_base;
			int     string_size, slength;
			char    *c;

			DISCARD_GENERIC_PARAMETER;
			to_tt_ptr = get_argument_ptr(0);
			to_ptr    = get_argument_ptr(2);
			item      = get_argument_value(4);
			a_base    = get_argument_value(6);

			string_size = SIZE(to_tt_ptr);

			image_integer(item, a_base);
			slength = strlen(work_string);

			if (slength > string_size) {
				predef_raise(LAYOUT_ERROR, "String too long");
			}

			c = work_string;
			while(string_size-- > slength) *to_ptr++ = ' ';
			while(slength--) *to_ptr++ = *c++;
			break;
		}


		/* 14.3.8  INPUT-OUTPUT FOR REAL TYPES */


		/* type NUM is digits <>;                                      */
		/* procedure GET(FILE : in FILE_TYPE;  ITEM  : out NUM;        */
		/*                                     WIDTH : in FIELD := 0); */
		/* procedure GET(ITEM : out NUM;  WIDTH : in FIELD := 0);      */

	case P_GET_FLOAT_FILE_ITEM:
	case P_GET_FLOAT_ITEM:
		{
			int     *item_tt_ptr;
			int     *item_ptr;
			int     width;
			float   fval;

			POP_PTR(item_tt_ptr);      /* pop generic type parameter */

			get_file_argument_or_default();
			check_status(TIO_IN_FILE);

			item_ptr = get_argument_ptr(0 + file_offset);
			width  = get_argument_value(4 + file_offset);

			fval = scan_float(item_tt_ptr, width);

			*((float *)(item_ptr)) = fval;
			break;
		}

		/* procedure PUT(FILE     : in FILE_TYPE;             */
		/*               ITEM     : in NUM;                   */
		/*               FORE     : in FIELD := DEFAULT_FORE; */
		/*               AFT      : in FIELD := DEFAULT_AFT;  */
		/*               EXP      : in FIELD := DEFAULT_EXP); */

		/* procedure PUT(ITEM     : in NUM;                   */
		/*               FORE     : in FIELD := DEFAULT_FORE; */
		/*               AFT      : in FIELD := DEFAULT_AFT;  */
		/*               EXP      : in FIELD := DEFAULT_EXP); */

	case P_PUT_FLOAT_FILE_ITEM:
	case P_PUT_FLOAT_ITEM:
		{
			int     fore, aft, expnt;
			float   fitem;

			DISCARD_GENERIC_PARAMETER;

			get_file_argument_or_default();
			check_status(TIO_OUT_FILE);

			fitem = get_float_argument_value(0 + file_offset);
			fore  = get_argument_value(2 + file_offset);
			aft   = get_argument_value(4 + file_offset);
			expnt = get_argument_value(6 + file_offset);

			image_float(fitem, fore, MAX(aft, 1), expnt);
			put_buffer(work_string,0,'L');
			break;
		}


		/* procedure
		 *   GET(FROM : in STRING; ITEM : out NUM; LAST : out POSITIVE);
		 */

	case P_GET_FLOAT_STRING:
		{
			int     *item_tt_ptr;
			int     *from_tt_ptr;
			int     *item_ptr;
			int     *last_ptr;
			int     last;
			float   fval;

			POP_PTR(item_tt_ptr);      /* pop generic type parameter */

			get_string_value(0);
			from_tt_ptr = get_argument_ptr(0);
			item_ptr =    get_argument_ptr(4);
			last_ptr =    get_argument_ptr(8);

			fval = scan_float_string(item_tt_ptr, &last);
			*((float *)(item_ptr)) = fval;
			last += string_offset(from_tt_ptr) ;
			*last_ptr = last;
			break;
		}


		/* procedure PUT(TO   : out STRING;               */
		/*               ITEM : in NUM;                   */
		/*               AFT  : in FIELD := DEFAULT_AFT;  */
		/*               EXP  : in FIELD := DEFAULT_EXP); */

	case P_PUT_FLOAT_STRING:
		{
			int     *to_tt_ptr;
			int     *to_ptr;
			int     aft, expnt;
			int     string_size, slength;
			float   fitem;
			char    *c;

			DISCARD_GENERIC_PARAMETER;

			to_tt_ptr = get_argument_ptr(0);
			to_ptr  =   get_argument_ptr(2);
			fitem   = get_float_argument_value(4);
			aft     = get_argument_value(6);
			expnt   = get_argument_value(8);

			image_float(fitem, 0, MAX(aft, 1), expnt);
			slength = strlen(work_string);

			string_size = SIZE(to_tt_ptr);
			if (slength > string_size) {
				predef_raise(LAYOUT_ERROR, "String too long");
			}

			c = work_string;
			while(string_size-- > slength) {
				*to_ptr++ = ' ';
			}
			while(slength--) {
				*to_ptr++ = *c++;
			}
			break;
		}


		/* type NUM is delta <>;                                       */
		/* procedure GET(FILE : in FILE_TYPE;  ITEM : out NUM;         */
		/*                                     WIDTH : in FIELD := 0); */
		/* procedure GET(ITEM : out NUM;  WIDTH : in FIELD := 0);      */

	case P_GET_FIXED_FILE_ITEM:
	case P_GET_FIXED_ITEM:
		{
			int     *item_tt_ptr;
			int     *item_ptr;
			int     width;

			POP_PTR(item_tt_ptr);      /* pop generic type parameter */

			get_file_argument_or_default();
			check_status(TIO_IN_FILE);

			item_ptr = get_argument_ptr(0 + file_offset);
			width = get_argument_value(4 + file_offset);

			check_status(TIO_IN_FILE);

			*((long *)(item_ptr)) = scan_fixed(item_tt_ptr, width);
			break;
		}


		/* procedure PUT(FILE   : in FILE_TYPE;              */
		/*               ITEM   : in NUM;                    */
		/*               FORE   : in FIELD := DEFAULT_FORE;  */
		/*               AFT    : in FIELD := DEFAULT_AFT;   */
		/*               EXP    : in FIELD := DECIMAL_EXP);  */

		/* procedure PUT(ITEM   : in NUM;                    */
		/*               FORE   : in FIELD := DEFAULT_FORE;  */
		/*               AFT    : in FIELD := DEFAULT_AFT;   */
		/*               EXP    : in FIELD := DEFAULT_EXP);  */

	case P_PUT_FIXED_FILE_ITEM:
	case P_PUT_FIXED_ITEM:
		{
			int     *item_tt_ptr;
			long    item;
			int     fore, aft, expnt;

			POP_PTR(item_tt_ptr);      /* pop generic type parameter */

			get_file_argument_or_default();
			check_status(TIO_OUT_FILE);

			item = get_long_argument_value(0 + file_offset);
			fore  = get_argument_value(2 + file_offset);
			aft   = get_argument_value(4 + file_offset);
			expnt = get_argument_value(6 + file_offset);

			image_fixed(item, item_tt_ptr, MAX(fore, 1), MAX(aft, 1), expnt);
			put_buffer(work_string,0,'L');
			break;
		}


		/* procedure
		 *   GET(FROM : in STRING; ITEM : out NUM; LAST : out POSITIVE);
		 */

	case P_GET_FIXED_STRING:
		{
			int     *item_tt_ptr;
			int     *from_tt_ptr;
			int     *item_ptr;
			int     *last_ptr;
			int     last;

			POP_PTR(item_tt_ptr);      /* pop generic type parameter */

			get_string_value(0);
			from_tt_ptr = get_argument_ptr(0);
			item_ptr = get_argument_ptr(4);
			last_ptr = get_argument_ptr(8);

			*((long *)(item_ptr)) = scan_fixed_string(item_tt_ptr, &last);

			last += string_offset(from_tt_ptr)  ;
			*last_ptr = last;
			break;
		}


		/* procedure PUT(TO   : out STRING;               */
		/*               ITEM : in NUM;                   */
		/*               AFT  : in FIELD := DEFAULT_AFT;  */
		/*               EXP  : in FIELD := DEFAULT_EXP); */

	case P_PUT_FIXED_STRING:
		{
			int     *item_tt_ptr;
			int     *to_tt_ptr;
			int     *to_ptr;
			long    item;
			int     aft, expnt;
			char    *c;
			int     string_size, slength;

			POP_PTR(item_tt_ptr);      /* pop generic type parameter */

			to_tt_ptr = get_argument_ptr(0);
			to_ptr    = get_argument_ptr(2);
			item = get_long_argument_value(4);
			aft   = get_argument_value(6);
			expnt = get_argument_value(8);

			image_fixed(item, item_tt_ptr, 1, MAX(aft, 1), expnt);
			string_size = SIZE(to_tt_ptr);
			slength = strlen(work_string);

			if (slength > string_size) {
				predef_raise(LAYOUT_ERROR, "String too long");
			}

			c = work_string;
			while(string_size-- > slength)
				*to_ptr++ = ' ';
			while(slength--)
				*to_ptr++ = *c++;
			break;
		}


		/* type ENUM is(<>);                                     */
		/* procedure GET(FILE : in FILE_TYPE;  ITEM : out ENUM); */
		/* procedure GET(ITEM : out ENUM);                       */

	case P_GET_ENUM_FILE_ITEM:
	case P_GET_ENUM_ITEM:
		{
			int     *item_tt_ptr;
			int     *item_ptr;

			POP_PTR(item_tt_ptr);      /* pop generic type parameter */

			get_file_argument_or_default();
			check_status(TIO_IN_FILE);

			item_ptr = get_argument_ptr(0 + file_offset);
			scan_enum();

			/*  Check to see if the identifier or character literal read */
			/*  corresponds to a value of the given enumeration subtype. */

			*item_ptr = enum_ord(item_tt_ptr, -1, DATA_ERROR);
			break;
		}


		/* procedure PUT(FILE  : in FILE_TYPE;                    */
		/*               ITEM  : in ENUM;                         */
		/*               WIDTH : in FIELD    := DEFAULT_WIDTH;    */
		/*               SET   : in TYPE_SET := DEFAULT_SETTING); */

		/* procedure PUT(ITEM  : in ENUM;                         */
		/*               WIDTH : in FIELD    := DEFAULT_WIDTH;    */
		/*               SET   : in TYPE_SET := DEFAULT_SETTING); */

	case P_PUT_ENUM_FILE_ITEM:
	case P_PUT_ENUM_ITEM:
		{
			int     *item_tt_ptr;
			int     item, width, setting;
			char    *c;

			POP_PTR(item_tt_ptr);      /* pop generic type parameter */

			get_file_argument_or_default();
			check_status(TIO_OUT_FILE);

			item    = get_argument_value(0 + file_offset);
			width   = get_argument_value(2 + file_offset);
			setting = get_argument_value(4 + file_offset);

			image_enum(item, item_tt_ptr);
			if (setting == LOWER_CASE && *work_string != QUOTE) {
				for (c = work_string; *c; c++)
					if ('A' <= *c && *c <= 'Z') *c += 32;
			}
			put_buffer(work_string, width, 'T');
			break;
		}


		/* procedure
		 *    GET(FROM : in STRING; ITEM : out ENUM; LAST : out POSITIVE);
		 */

	case P_GET_ENUM_STRING:
		{
			int     *item_tt_ptr;
			int     *from_tt_ptr;
			int     *item_ptr;
			int     *last_ptr;
			int     last;

			POP_PTR(item_tt_ptr);      /* pop generic type parameter */

			get_string_value(0);
			from_tt_ptr = get_argument_ptr(0);
			item_ptr    = get_argument_ptr(4);
			last_ptr    = get_argument_ptr(8);

			scan_enum_string(&last);

			/*  Check to see if the identifier or character literal read */
			/*  corresponds to a value of the given enumeration subtype. */

			*item_ptr = enum_ord(item_tt_ptr, -1,  DATA_ERROR);
			last += string_offset(from_tt_ptr) ;
			*last_ptr = last;
			break;
		}


		/* procedure PUT(TO   : out STRING;                      */
		/*               ITEM : in ENUM;                         */
		/*               SET  : in TYPE_SET := DEFAULT_SETTING); */

	case P_PUT_ENUM_STRING:
		{
			int     *item_tt_ptr;
			int     *to_ptr;
			int     *to_tt_ptr;
			int     string_size, slength;
			int     item;
			int     setting;
			char    *c;

			POP_PTR(item_tt_ptr);      /* pop generic type parameter */

			to_tt_ptr = get_argument_ptr(0);
			to_ptr    = get_argument_ptr(2);
			item    = get_argument_value(4);
			setting = get_argument_value(6);

			image_enum(item, item_tt_ptr);
			if (setting == LOWER_CASE && *work_string != QUOTE) {
				for (c = work_string; *c; c++)
					if ('A' <= *c && *c <= 'Z') *c += 32;
			}

			string_size = SIZE(to_tt_ptr);
			slength = strlen(work_string);

			if (slength > string_size) {
				predef_raise(LAYOUT_ERROR, "String too long");
			}

			to_ptr += string_size;
			c = work_string + slength;
			while(string_size-- > slength) {
				*--to_ptr = ' ';
			}
			while(slength--) {
				*--to_ptr = *--c;
			}
			break;
		}


		/* 9.6  CALENDAR */

	case P_CLOCK:
	case P_YEAR:
	case P_MONTH:
	case P_DAY:
	case P_SECONDS:
	case P_SPLIT:
	case P_TIME_OF:
	case P_ADD_TIME_DUR:
	case P_ADD_DUR_TIME:
	case P_SUB_TIME_DUR:
	case P_SUB_TIME_TIME:
	case P_LT_TIME:
	case P_LE_TIME:
	case P_GT_TIME:
	case P_GE_TIME:
		{
			calendar();
			break;
		}


	default:
		predef_raise(SYSTEM_ERROR, "Unknown PREDEF operation");
	}
}


/* PREDEF_RAISE */

/* This procedure raises a specified exception, and then exits from the
 * PREDEF package completely by unwinding the stack to the top level
 */

void predef_raise(int exception, char *msg)            /*;predef_raise*/
{
	raise(exception, msg);
	longjmp(raise_env, 1);
}

static int string_offset(int *a_ptr)			/*;string_offset*/
{
	if (TYPE(a_ptr) == TT_S_ARRAY) {
		value = S_ARRAY(a_ptr) -> salow ;
	}
	else {
		bse   = ARRAY(a_ptr)->index1_base ;
		off   = ARRAY(a_ptr)->index1_offset ;
		ptr1  = ADDR(bse, off) ;
		value = I_RANGE(ptr1)->ilow ;
	}
	return value;
}
