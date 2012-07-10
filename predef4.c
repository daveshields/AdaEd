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
      |         Part 4: Input/Output Procedures           |
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
      +---------------------------------------------------+
*/

/*  This module contains routines for the implementation of some of
 *  the predefined Ada packages and routines, namely SEQUENTIAL_IO,
 *  DIRECT_IO, TEXT_IO, and CALENDAR. Part 4 contains the initialization
 *  and termination routines for predef, and the basic I/O routines
*/

#include <stdlib.h>
#include <string.h>
#ifdef IBM_PC
#include <io.h>
#endif
#include "ipredef.h"
#include "miscprots.h"
#include "predefprots.h"

static void check_ifile_closed(int *);
static void check_xfile_closed(char *);
static void open_file();
#ifdef IBM_PC
#undef putc
#define putc(A, B) fputc((A),(B));fflush(B)
#endif
#ifdef DEBUG_PREDEF
static void gchar(char *, int);
static void pchar(char *, int);
#endif

/* AFCB for STANDARD_IN_FILE */

static struct afcb  in_afcb = {

	0,                          /* file descriptor for standard input */
	"",                         /* file name(null) */
	"",                         /* form string(null) */
	TIO_IN_FILE,                /* mode, TEXT_IO input */
	0, 0, 0,                    /* unused DIRECT_IO fields */
	1,                          /* page number */
	1,                          /* line number */
	1,                          /* column number */
	0,                          /* unbounded line length */
	0,                          /* unbounded page length */
	0, "  "                    /* look ahead */
};

#ifdef IBM_PC
/* keep track of last character read from stdin so can detect whether we
 * need to flush what is left there before exiting
 */
static int last_char_input = EOF;
#endif

/* AFCB for STANDARD_OUT_FILE */

static struct afcb  out_afcb = {

	0,                          /* file descriptor for standard input */
	"",                         /* file name(null) */
	"",                         /* form string(null) */
	TIO_OUT_FILE,               /* mode, TEXT_IO output */
	0, 0, 0,                    /* unused DIRECT_IO fields */
	1,                          /* page number */
	1,                          /* line number */
	1,                          /* column number */
	0,                          /* unbounded line length */
	0,                          /* unbounded page length */
	0, "  "                    /* look ahead */
};

/* Procedure to initialize input/output data structures */

void initialize_predef()                     /*;initialize_predef*/
{
	/* Clear temporary file list, and clear AFCB vector */

	tfiles = 0;
	for (filenum = 1; filenum <= MAXFILES; filenum++)
		afcbs[filenum - 1] = 0;

	/* Setup references for current and standard files */

	current_in_file = 1;
	current_in_file_saved = 1;
	standard_in_file = 1;
	afcbs[0] = &in_afcb;
	filenum = 1;
	IOFDESC = stdin;
	CHARS = 0;

	current_out_file = 2;
	current_out_file_saved = 2;
	standard_out_file = 2;
	afcbs[1] = &out_afcb;
	filenum = 2;
	IOFDESC = stdout;

	/* Set standard exception signalled on bad data (changed temporarily
     * to CONSTRAINT_ERROR when TEXT_IO routines are called directly from
     * the main interpretor for the IMAGE attribute.
     */

	data_exception = DATA_ERROR;
}


/* CHECK_OPENED_OK */

/* Checks that an fopen succeeded, raise USE_ERROR if not */

void check_opened_ok()			                       /*;check_opened_ok*/
{
	if (IOFDESC == NULL)
		predef_raise(USE_ERROR, "Error opening or resetting file");
}

/* CHECK_IFILE_CLOSED */

/* Checks that the file object stored at file_ptr is closed */

static void check_ifile_closed(int *file_ptr)           /*;check_ifile_closed*/
{
	int     file_val;

	file_val = *file_ptr;
	if (file_val != 0)
		predef_raise(STATUS_ERROR, "File not closed");
}

/* CHECK_XFILE_CLOSED */

/* Checks that no external file with a matching name is currently open */

static void check_xfile_closed(char *fname)             /*;check_xfile_closed*/
{
	int     i;
	for (i = 1; i <= MAXFILES; i++) {
		if (afcbs[i - 1] == NULL) continue;
		if (strcmp(fname, afcbs[i - 1] -> io_fname) == 0 &&
		  afcbs[i - 1] -> io_fdesc != NULL) {
			predef_raise(USE_ERROR, "File already open");
		}
	}
}

/* CHECK_FILE_OPEN */

/* Check if the current file is open or not. If the file is not open,
  * then STATUS_ERROR is raised. Otherwise control returns normally.
*/

void check_file_open()				                       /*;check_file_open*/
{
	if (filenum == 0)
		predef_raise(STATUS_ERROR, "File not open");
}

/* If the current file is not open, then STATUS_ERROR is raised. If
 * the file is open, then the mode is checked against the argument which
 * is the desired mode for the operation. If it does not match, then
 * MODE_ERROR is raised, otherwise control returns normally.
 */

void check_status(int c_mode)			                    /*;check_status*/
{
	check_file_open();
	if (IOMODE != c_mode)
		predef_raise(MODE_ERROR, "Incorrect file status");
}

/*  Routine called by the OPEN and CREATE portions of the PREDEF procedure
 *  to perform common data structure operations for TEXT_IO operations.
 *  The operation in opn is 'C' for a create and 'O' for an open.
 */

void open_textio(char opn)                       /*;open_textio*/
{
	open_file();

#ifdef SYSTEM_V
	if (strlen(IOFNAME) > 14) predef_raise(NAME_ERROR,"Invalid file name");
#endif

	if (opn == 'C') {
		IOFDESC = fopen_txt(IOFNAME, "w");
		if (IOFDESC == NULL) predef_raise(NAME_ERROR,"Invalid file name");
		if (IOMODE == SIO_IN_FILE) {
			fclose(IOFDESC);
			IOFDESC = fopen_txt(IOFNAME, "r");
			check_opened_ok();
		}
	}
	else {                      /* opn == 'O' */
		/*
		* According to AI-00048: 
		* Opening a file with IN_FILE mode which is the default output file 
		* will raise MODE_ERROR. 
		* Opening a file with OUT_FILE mode which is the default input file 
		* will raise MODE_ERROR.
		* The values to be checked is in current_in_file_saved and
		* current_out_file_saved which are copies of the file numbers
		* associated with the default files. These copies must be used
		* because when the default files are closed their filenums saved
		* in current_XXX_file are set to zero and therefore lost for this
		* check.
		*/
		if (filenum == current_in_file_saved && IOMODE == TIO_OUT_FILE)
			predef_raise(MODE_ERROR,"File is default in file");
		if (filenum == current_out_file_saved && IOMODE == TIO_IN_FILE)
			predef_raise(MODE_ERROR,"File is default out file");
		IOFDESC = fopen_txt(IOFNAME, "r");
		if (IOFDESC == NULL) predef_raise(NAME_ERROR,"File not found");
		if (IOMODE == TIO_IN_FILE)
			CHARS = 0;
		else {
			fclose(IOFDESC);
			IOFDESC = fopen_txt(IOFNAME, "w");
			check_opened_ok();
		}
	}

	PAGE = 1;
	LINE = 1;
	COL = 1;
	LINE_LENGTH = 0;
	PAGE_LENGTH = 0;

	*get_argument_ptr(0) = filenum;
}

/* LOAD_LOOK_AHEAD */

/* This procedure loads the lookahead for a TEXT_IO input file, leaving
 * CHARS set to 3 (unless the file is less than 3 bytes long), and CHAR1
 * CHAR2 and CHAR3 containing the initial characters of the file. A special
 * exception occurs when the standard input file is the keyboard in which case
 * we only read 1 character because of interactive  I/O except when 
 * load_look_ahead is called in the case of END_OF_FILE where we want to 
 * read 2 characters to check for the EOT character. The parameter to this
 * routine end_of_file_flag is TRUE when processing for and END_OF_FILE
 * situation and is FALSE otherwise.
*/

void load_look_ahead(int end_of_file_flag)		    /*;load_look_ahead*/
{
	int c;

	/* Load first character of look ahead */

	if (CHARS == 0) {
		CHAR2 = CHAR3 = 0;
		c = fgetc(IOFDESC);
#ifdef IBM_PC
		if (IOFDESC == stdin) last_char_input = c;
#endif
		gchar("load_look 1", c);
		if (c == EOF) {
			CHAR1 = 0;
			return;
		}
		else {
			CHAR1 = c;
			CHARS = 1;
		}
	}

        /* In the case where reading from the keyboard do not read more than
         * 1 character unless you are processing an end_of_file test.
         */
	if (isatty(fileno(IOFDESC)) && (!end_of_file_flag)) return;
	/* Load second character of look ahead */

	if (CHARS == 1) {
		CHAR3 = 0;
		c = fgetc(IOFDESC);
#ifdef IBM_PC
		if (IOFDESC == stdin) last_char_input = c;
#endif
		gchar("load_look 2",c);
		if (c == EOF) {
			CHAR2 = 0;
			return;
		}
		else {
			CHAR2 = c;
			CHARS = 2;
		}
	}

	/* Leave lookahead with at most two characters loaded if */
        /* standard input is the keyboard.                       */

	if (!isatty(fileno(IOFDESC))) {
		/* Load third character of look ahead */

		if (CHARS == 2) {
			c = fgetc(IOFDESC);
			gchar("load_look 3",c);
			if (c == EOF) {
				CHAR3 = 0;
				return;
			}
			else {
				CHAR3 = c;
				CHARS = 3;
			}
		}
	}
}

/* CLOSE_TEXTIO */

/*  This routine is called by the CLOSE portion of the PREDEF procedure to
 *  perform common data structure operations for text_io. Perform various
 *  actions based on whether this is an input or output file.
 */

void close_textio()				                          /*;close_text_io*/
{
	if (IOMODE == TIO_OUT_FILE) {

		/* Simulate effect of NEW_PAGE unless current page is terminated */

		if (!PAGE_TERMINATED) {
			if (COL > 1 ||(COL == 1 && LINE == 1))
				put_line();
			put_page();
		}
	}

	/* Sever the association between the given file and its associated
	 * external file.   The given file is left closed.  Do not perform
	 * system closes on the standard input and output files.
	 */

	if (filenum != standard_in_file && filenum != standard_out_file)
		close_file();

	/* If the file being closed is one of the default files, set the default
	 * file indicator to zero to indicate that the file is closed.
	 */

	if (filenum == current_in_file)
		current_in_file = 0;
	else if (filenum == current_out_file)
		current_out_file = 0;
}

/*  TEXT_IO Line Management Procedures */

/* GET_CHAR */

/*  Procedure to get the next character from the current text input file.
 *  If no character is available, then END_ERROR is raised.
 */

char get_char()							                         /*;get_char*/
{
	char    c;                          /* character read */

	/* Load look ahead and check for no more characters */

	load_look_ahead(FALSE);
	if (CHARS == 0)
		predef_raise(END_ERROR, "End of file on TEXT_IO input");
	c = CHAR1;

	/* Update lookahead */

	CHAR1 = CHAR2;
	CHAR2 = CHAR3;
	CHAR3 = 0;
	CHARS--;

	/* Update PAGE and LINE counters if page mark or line feed read */

	if (c == PAGE_MARK) {
		PAGE += 1;
		LINE = 1;
		COL = 1;
	}
	else if (c == LINE_FEED) {
		LINE += 1;
		COL = 1;
	}
	else
		COL += 1;
	if (c > 127)
		predef_raise(DATA_ERROR, "Character > 127 for TEXT_IO input");
	gchar("get_char",c);
	return c;
}

/* SKIP_LINE */

/* Procedure to perform SKIP_LINE operation for a spacing of 1 line. Skips
 * characters up to and including next line terminator. Also skips any
 * page marks following this line terminator (there should normally be at
 * most one in standard format files, but we just skip past several if
 * we find them present).
*/

void skip_line()					                             /*;skip_line*/
{
	for (;;) {
		load_look_ahead(FALSE);
		if (get_char() == LINE_FEED)
			break;
	}

	/* ignore page marks for standard input. */

	if (IOFDESC == stdin) return;

	for (;;) {
		load_look_ahead(FALSE);
		if (CHAR1 != PAGE_MARK) break;
		get_char();
	}
}

/* PUT_BLANKS */

/* Procedure to write n blanks to current text file. There is no check for
 * line overflow, it is assumed that the caller has checked line overflow.
 */

void put_blanks(int n)				                           /*;put_blanks*/
{
	while (n--) {
		pchar("put_blanks",' ');
		putc(' ', IOFDESC);
	}
}

/* PUT_CHAR */

/* Procedure to write 1 character to current text file. Functions exactly
 * as if writing a one character string(see PUT_STRING function)
 */

void put_char(char c)				                             /*;put_char*/
{
	if (BOUNDED_LINE_LENGTH && COL > LINE_LENGTH )
		put_line();
	pchar("put_char",c);
	putc(c, IOFDESC);
	COL++;
}

/* PUT_LINE */

/* This procedure outputs a line feed to the current text file */

void put_line()						                              /*;put_line*/
{
	pchar("put_line",LINE_FEED);
	putc(LINE_FEED, IOFDESC);
	COL = 1;
	if (BOUNDED_PAGE_LENGTH && LINE >= PAGE_LENGTH)
		put_page();
	else LINE += 1;
}

/* PUT_PAGE */

/* Procedure to write page mark to current text file */

void put_page()					                              /*;put_page*/
{
	pchar("put_page",PAGE_MARK);
	putc(PAGE_MARK, IOFDESC);
	PAGE += 1;
	LINE = 1;
	COL = 1;
}

/* Put a string into the output file, performing line breaks as needed */

void put_string(char *s)			                           /*;put_string*/
{
	int     left_in_string;             /* chars left in string */
	int     left_in_line;               /* chars left in current line */

	left_in_string = strlen(s);

	if (UNBOUNDED_LINE_LENGTH) {
		COL += left_in_string;
		while (left_in_string--) {
			pchar("put_string 1",*s);
			putc(*s++,IOFDESC);
		}
	}

	else {
		while(left_in_string != 0) {
			left_in_line = LINE_LENGTH - COL + 1;
			if (left_in_line <= 0) {
				put_line();
				left_in_line = LINE_LENGTH;
			}

			if (left_in_string <= left_in_line) {
				COL += left_in_string;
				while (left_in_string) {
					pchar("put_string 2",*s);
					putc(*s++,IOFDESC);
					/* left_in_string should never become negative */
					left_in_string--;
				}
			}
			else {
				left_in_string -= left_in_line;
				while (left_in_line--) {
					pchar("put_string 3",*s);
					putc(*s++,IOFDESC);
				}
				put_line();
			}
		}
	}
}


/* PUT_BUFFER */

/*  This routine writes an item(passed in as a string) with appropriate
 *  blank padding. The second parameter is the desired width, and the third
 *  parameter is 'L' for leading blank padding and 'T' for trailing padding.
 */

void put_buffer(char *buffer, int width, char padtype)	      /*;put_buffer*/
{
	int     slength, tlength;
	int n;

	slength = strlen(buffer);
	if (slength < width)
		tlength = width;
	else {
		tlength = slength;
		padtype = ' ';
	}

	/* Ensure the buffer size does not exceed the line length */

	if (BOUNDED_LINE_LENGTH) {
		if (tlength > LINE_LENGTH)
			predef_raise(LAYOUT_ERROR, "Line too big");

		/* New line if does not fit on current line */

		if (COL + tlength - 1 > LINE_LENGTH)
			put_line();
	}

	/* Output data with required padding */

	if (padtype == 'L')
		put_blanks(width - slength);
	n = slength;
	while (n--) {
		pchar("put_buffer",*buffer);
		putc(*buffer++,IOFDESC);
	}
	COL += tlength;
	if (padtype == 'T')
		put_blanks(width - slength);
}

/* OPEN_SEQ_IO */

/*  Create or open a SEQUENTIAL_IO file. If the file is to be created,
 *  an AFCB is created and initialized to empty. If the file is to be opened,
 *  the existing file is accessed, and the AFCB initialized for that file.
 *  The argument opn is 'C' to create a file and 'O' to open a file.
 */

void open_seq_io(int opn)				                        /*;open_seq*/
{
	DISCARD_GENERIC_PARAMETER;

	open_file();

#ifdef SYSTEM_V
	if (strlen(IOFNAME) > 14) predef_raise(NAME_ERROR,"Invalid file name");
#endif

	if (opn == 'C') {
		IOFDESC = fopen_bin(IOFNAME, "w");
		if (IOFDESC == NULL) predef_raise(NAME_ERROR,"Invalid file name");
		if (IOMODE == SIO_IN_FILE) {
			fclose(IOFDESC);
			IOFDESC = fopen_bin(IOFNAME, "r");
			check_opened_ok();
		}
	}
	else {                      /* opn == 'O' */
		IOFDESC = fopen_bin(IOFNAME, "r");
		if (IOFDESC == NULL) predef_raise(NAME_ERROR,"File not found");
		if (IOMODE == SIO_IN_FILE)
			;
		else {
			fclose(IOFDESC);
			IOFDESC = fopen_bin(IOFNAME, "w");
			check_opened_ok();
		}
	}
	*get_argument_ptr(0) = filenum;
}

/* OPEN_DIR_IO */

/*  Open or create a DIRECT_IO file. If the file is to be created, an
 *  AFCB is created and initialized to empty. If the file is to be opened,
 *  the existing file is accessed, and the AFCB initialized for that file.
 *  The argument opn is 'C' to create a file and 'O' to open a file.
 */

void open_dir_io(int opn)			                        /*;open_dir_io*/
{
	int     *item_tt_ptr;
	long    eof_pos;
	int     type;

	POP_PTR(item_tt_ptr);              /* pop generic type */

	type = TYPE(item_tt_ptr);
	if (type == TT_U_ARRAY || type == TT_U_RECORD) {
		predef_raise(USE_ERROR,
		  "Unconstrained types not permitted for direct IO");
	}
	open_file();
	DLENGTH = SIZE(item_tt_ptr) * sizeof(int);

#ifdef SYSTEM_V
	if (strlen(IOFNAME) > 14) predef_raise(NAME_ERROR,"Invalid file name");
#endif

	if (opn == 'C') {
		IOFDESC = fopen_bin(IOFNAME,"w+");
		if (IOFDESC == NULL) predef_raise(NAME_ERROR,"Invalid filename");
		DPOS = 1;
		DSIZE = 0;
	}
	else {
		IOFDESC = fopen_bin(IOFNAME, "r");
		if (IOFDESC == NULL) predef_raise(NAME_ERROR,"File not found");
		if (IOMODE == DIO_IN_FILE)
			;
		else if (IOMODE == DIO_OUT_FILE) {
			fclose(IOFDESC);
			IOFDESC = fopen_bin(IOFNAME, "w");
		}
		else {
			fclose(IOFDESC);
			IOFDESC = fopen_bin(IOFNAME, "r+");
		}
		check_opened_ok();

		DPOS = 1;
		fseek(IOFDESC, 0L, 2);
		eof_pos = ftell(IOFDESC);
		DSIZE = eof_pos / DLENGTH;
	}
	*get_argument_ptr(0) = filenum;
}


/* OPEN_FILE */

/*  This routine is used for all file types to perform the basic operations
 *  of acquiring the parameters for an open and constructing an AFCB. On
 *  return the AFCB is built and filenum references the afcbs entry set.
 */

static void open_file()				                             /*;open_file*/
{
	int     *file_ptr;

	file_ptr = get_argument_ptr(0);
	check_ifile_closed(file_ptr);

	filenum = 1;
	while(afcbs[filenum - 1] != 0 && filenum < 21)
		filenum++;
	if (afcbs[filenum - 1] != 0)
		predef_raise(USE_ERROR, "Too many files open");

	afcbs[filenum - 1] = (struct afcb  *)(predef_alloc(sizeof(struct afcb)));

	IOFDESC = NULL;

	IOMODE = get_argument_value(2);

	get_string_value(4);
	IOFNAME = make_string();

	get_string_value(8);
	IOFORM = make_string();

	/* Check for temporary file */

	if (*IOFNAME == '\0') {
		struct tfile   *tfilep;
#ifdef IBM_PC
		IOFNAME = predef_alloc(L_tmpnam);
		tmpnam(IOFNAME);
#else
		IOFNAME = predef_alloc(15);
		strcpy(IOFNAME, "ADATEMP_XXXXXX");
		IOFNAME = mktemp(IOFNAME);
#endif
		tfilep = (struct tfile *)(predef_alloc(sizeof(struct tfile)));
		tfilep -> tfile_next = tfiles;
		tfiles = tfilep;
		strcpy(tfiles -> tfile_name, IOFNAME);
	}

	/* If not temporary file, make sure it is not already open */

	else
		check_xfile_closed(IOFNAME);
}

/* CLOSE_FILE */

/* Close file and deallocate the AFCB */

void close_file()					                            /*;close_file*/
{
	fclose(IOFDESC);
	predef_free(IOFNAME);
	predef_free(IOFORM);
	predef_free((char *)(afcbs[filenum - 1]));
	afcbs[filenum - 1] = 0;
}

/* PREDEF_TERM : Termination routine for Input/Output packages. */

void predef_term()				                           /*;predef_term*/
{
	/* close all open files except stdin and stdout */

	for (filenum = 3; filenum <= MAXFILES; filenum++) {
		if (afcbs[filenum - 1] != NULL && IOFDESC != NULL) {
			if (IOMODE == SIO_OUT_FILE)
				close_file();
			else if (IOMODE == DIO_OUT_FILE || IOMODE == DIO_INOUT_FILE)
				close_file();
			else if (IOMODE == TIO_OUT_FILE)
				close_textio();
		}
	}

	/* Delete temporary files upon completion of the main program */

	while(tfiles != 0) {
		unlink(tfiles -> tfile_name);
		tfiles = tfiles -> tfile_next;
	}
#ifdef IBM_PC
	/* Flush input buffer if there is something there, since MS_DOS
     * will retain the unwanted information for next program execution.
     * Check that stdin is connected to the console and that the last
     * character read from stdin is not EOF (this will be the case also
     * if we have not read anything from stdin) and not LINE_FEED.
     */
	if ( isatty(fileno(stdin))  && 
	  last_char_input != EOF && last_char_input != LINE_FEED) {
		filenum = 1;	/* stdin */
		do {
			last_char_input = fgetc(IOFDESC);
		} while ( last_char_input != LINE_FEED && last_char_input != EOF);
	}
#endif
}

/* PREDEF_ALLOC */

/* Procedure to allocate storage for use by PREDEF. The argument is the
 * length of storage required in bytes. For now we allocate this storage
 * on the main C heap. Later on when we extend the Ada heap to multiple
 * segments, we may allocate on the Ada heap.
 */

char *predef_alloc(int s)					                 /*;predef_alloc*/
{
	return (char *) malloc(s);
}

/* Procedure to free storage previously acquired by a call to PREDEF_ALLOC */

void predef_free(char *p)			                          /*;predef_free*/
{
	free(p);
}
#ifdef IBM_PC
/* if need to distinguish binary and text files */

FILE *fopen_bin(char *fname, char *fmode)					/*;fopen_bin*/
{
	char mode[30];
	strcpy(mode,fmode);
	strcat(mode,"b");
	return fopen(fname, mode);
}

FILE *fopen_txt(char *fname, char *fmode)					/*;fopen_txt*/
{
	char mode[30];
	strcpy(mode,fmode);
	strcat(mode,"t");
	return fopen(fname, mode);
}
#endif

#ifdef DEBUG_PREDEF
static int pchars=0;
static int gchars=0;

static void gchar(char *msg, int c)									/*;gchar*/
{
	gchars++;
	printf("\ngchar %03d %s %03d %02x ",gchars,msg,c,c);
	if (c>=0 && c<32) printf("^%c",c+64);
	else if (c>32 && c<127) printf(" %c",c);
	else printf(" ");
	printf("\n");
}

static void pchar(char *msg, int c)									/*;pchar*/
{
	pchars++;
	printf("\npchar %03d %s %03d %02x ",pchars,msg,c,c);
	if (c>=0 && c<32) printf("^%c",c+64);
	else if (c>32 && c<127) printf(" %c",c);
	else printf(" ");
	printf("\n");
}
#endif
