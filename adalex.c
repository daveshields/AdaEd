/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/*			Lexical scanner for ADA 

One line of text at a time is read in using getline(). Tokens are scanned
for, and gettok() returns one token at a time to the parser. What is actually
returned is a pointer to a structure for the parse stack capable of holding
the token. No initialization is needed, as it has all been done statically
(before run time).
*/

/* define PDEBUG to get some debug trace output */

#include "hdr.h"
#include "adalex.h"
#include "miscprots.h"
#include "errsprots.h"
#include "adalexprots.h"

static int getline();
static struct prsstack *newtoken(int, int, int, int);
static int isdecimal(char);
static int ishex(char);
static int isletterordigit(char);
static int scanidorint(char *, int *, int *, int (*func)(char), int);
static void scanexp(char *, int *, int *);
static int scandec(char *, int *, int *, int (*func)(char));
static void checkbased(char *, int *);
static void convtoupper(char *);
static void nlisthash(int, int *, int *);
static int newnode(char *, int, int);

/* Global variables */

int lineno = 0;					/* Current line number in adafile */
int colno;						/* Current column number in adafile */

char *data = (char *)source_buf[0];		/* Current line of ada program */
char *line = (char *)source_buf[0];		/* Pointer to character within data array */
/* These are initialized so that an end of line is indicated */

char *nonprintingmsg[] = {	/* Messages for non-printing characters */
	"NUL (^@)",
	"SOH (^A)",
	"STX (^B)",
	"ETX (^C)",
	"EOT (^D)",
	"ENQ (^E)",
	"ACK (^F)",
	"BEL (^G)",
	"BS (^H)",
	"HT (^I)",
	"LF (^J)",
	"VT (^K)",
	"FF (^L)",
	"CR (^M)",
	"SO (^N)",
	"SI (^O)",
	"DLE (^P)",
	"DC1 (^Q)",
	"DC2 (^R)",
	"DC3 (^S)",
	"DC4 (^T)",
	"NAK (^U)",
	"SYN (^V)",
	"ETB (^W)",
	"CAN (^X)",
	"EM (^Y)",
	"SUB (^Z)",
	"ESC",
	"FS",
	"GS",
	"RS",
	"US"};
char source_buf[NUM_LINES][MAXLINE + 1] = { '\0' }; /* Source lines buffer */
int src_index = -1;		/* Index into source lines buffer */


/* Getline: Read a line into data, returning EOF on end of file.
	^J, ^K, ^L, ^M (10-13) are all interpreted as end of line. 
	Line, lineno, and colno	are set as neeeded. */

/* Note: At present, the listing of the ada source file is done after
   reading the line, in getline(). Because the source file may have tabs,
   in order to insure that the relative spacing of the characters in the
   source file appears correctly on the screen and that underlining of
   errors occurs correctly, the number of characters printed on each
   line before the next source line should be a multiple of 8 (tab stops
   are at 8k+1). At present we leave 5 spaces for the line number, print
   a colon (:), and leave 2 more spaces before printing the source line for
   a total of 8 spaces.
*/

/* A buffer of NUM_LINES source lines is kept for the purpose of printing
   error messages. Source_buf is the buffer, src_index is the index into
   the buffer for the current line.
*/


static int getline()											/*;getline*/
{
	int ch, ind = 0;

	if (feof(adafile))
		return(EOF);
	src_index = (src_index + 1) % NUM_LINES;
	line = data = source_buf[src_index];
	lineno++;
	colno = 1;
	for (;;) {
		ch = getc(adafile);
		if (ch==EOF) break;
		if (ch <= 13 && ch >= 10) break;
		if (ind == MAXLINE) {
			char msg[80];
			sprintf(msg,
			  "Line %d exceeds maximum length, truncated to %d characters",
			  lineno, MAXLINE);
			lexerr(lineno, 1, 1, msg);
			while ((ch = getc(adafile)) != EOF && !(ch<=13 && ch>=10));
			break;
		}
		else {
			data[ind++] = ch;
		}
	}

	data[ind] = '\0';
	if (ch == EOF && !ind)
		return(EOF);
#ifdef DEBUG
	if (trcopt)
		fprintf(errfile, "%5d:	%s\n", lineno, data);
	if (termopt)
		printf(         "%5d:	%s\n", lineno, data);
#endif	
	return(0);
}

static struct prsstack *newtoken(int num, int index, int line, int col)
																/*;newtoken*/
{
	/* Newtoken: allocate memory for a new token structure, and initialize */
	/* the fields of the structure. */

	struct prsstack *tok;

	tok = PRSALLOC();
	tok->symbol = num;
	tok->ptr.token = TOKALLOC();
	tok->ptr.token->index = index;
	tok->ptr.token->span.line = line;
	tok->ptr.token->span.col = col;
	return(tok);
}

/* Functions for passing to scanidorint */

static int isdecimal(char ch)									/*;isdecimal*/
{
	return(isdigit(ch));
}

static int ishex(char ch)										/*;ishex*/
{
	return(isdigit(ch) || 'A' <= ch && ch <= 'F' || 'a' <= ch && ch <= 'f');
}

static int isletterordigit(char ch)						/*;isletterordigit*/
{
	return(isalpha(ch) || isdigit(ch));
}

struct prsstack *gettok()										/*;gettok*/
{
	/* Gettok: Scan and return the next token in the adafile, adding the */
	/* token to namelist. */

	static int nextcanbeprime = 0;	/* The next token can be a prime */
	static int canbeprime;			/* The current token can be a prime */
	struct prsstack *tok;			/* Token to be returned */

	while (1) {
		while (1) {
			while (*line == ' ' || *line == '\t') {
				colno += (*line == '\t') ? (8 - ((colno - 1) % 8)) : 1;
				line++;
			}
			if (!*line || *line == '-' && line[1] == '-')
				break;
			canbeprime = nextcanbeprime;
			nextcanbeprime = 0;

			if (isalpha(*line)) {		/* Scan identifiers */
				char id[MAXLINE + 1];
				int idind = 0, chread = 0;
				int tokind, toksym;

				scanidorint(id, &idind, &chread, isletterordigit, 0);
				if (id[idind - 1] == '_')
					idind--;
				id[idind] = '\0';
				convtoupper(id);
				tokind = namemap(id, idind);
				toksym = MIN(tokind, ID_SYM);
				tok = newtoken(toksym, tokind, lineno, colno);
				nextcanbeprime = toksym == ID_SYM || toksym == RANGE_SYM
				  || toksym == ALL_SYM;
				colno += chread;
				line += chread;
				return(tok);
			}

			else if (isdigit(*line) || *line == '.' && isdigit(line[1])) {
			/* Scan numeric literals */
				char num[MAXLINE + 3];
				int ind = 0, chread = 0, result;
				char ch;
				/* ind is the index into the num string */
				/* chread is the index into the line input string */

				result = scandec(num, &ind, &chread, isdecimal);
				ch = line[chread];
				if (result == 1 && (ch == '#' || ch == ':')) {
				/* Scan for the rest of a based literal */
					num[ind++] = '#';
					chread++;
					if (!scandec(num, &ind, &chread, ishex)) {
						lexerr(lineno, colno + chread - 1, colno + chread - 1,
						  "Incomplete based number");
						num[ind++] = '0';
					}
					num[ind++] = '#';
					if (line[chread] != ch) {
						if (line[chread] == '#' + ':' - ch) {
							lexerr(lineno, colno + chread, colno + chread,
							  "Expect #'s or :'s in based number to match");
							chread++;
						}
						else {
							char msg[50];

							sprintf(msg, "Expect '%c' after last digit", ch);
							lexerr(lineno, colno + chread - 1,
							  colno + chread - 1, msg);
						}
					}
					else
						chread++;
					checkbased(num, &ind);
				}
				scanexp(num, &ind, &chread);
				if (isalpha(line[chread]))
					lexerr(lineno, colno, colno + chread - 1,
					  "Number should be separated from adjacent identifier");
				num[ind] = '\0';
				tok = newtoken(NUMBER_SYM, namemap(num, ind), lineno, colno);
				colno += chread;
				line += chread;
				return(tok);
			}

			else if (*line == '\'') {
				int err = 0;

				if (line[1] != '\0' && line[2] == '\'' &&
				    (!canbeprime || line[1] != '(')) {
				/* Scan a character literal */
					char str[4];
					int len = 3;

					strcpy(str, "' '");
					if (!isprint(line[1]) && line[1] != ' ') {
						char msg[80];

						sprintf(msg,
  "Invalid character %s in character literal replaced by space",
						  nonprintingmsg[line[1]]);
						lexerr(lineno, colno + 1, colno + 1, msg);
						len = (line[1] == '\t') ? (10 - (colno % 8)) : 2;
					}
					else
						str[1] = line[1];
					tok = newtoken(CHAR_SYM, namemap(str, 3), lineno, colno);
					colno += len;
					line += 3;
					return(tok);
				}
				else if (!canbeprime) {
				/* Possibly a single quote delimited string */
					int ind;

					if (line[1] == '\'')
						ind = 1;
					else {
						ind = 3;
						while (line[ind]) {
							if (line[ind] == '\'') {
								if (line[ind + 1] && line[ind + 2] == '\'') {
									ind = -1;
									break;
								}
								else {
									if (line[ind + 1] != '\'')
										break;
									ind++;
								}
							}
							ind++;
						}
					}
					if (ind > -1 && line[ind]) {
						err = 1;
						lexerr(lineno, colno, colno + ind,
						  "Expect double quotes to delimit a character string");
						do
							if (line[ind] == '\'')
								line[ind] = '"';
						while (ind--);
					}
				}
				if (!err) {     /* A prime */
					int ind = namemap("'", 1);

					tok = newtoken(ind, ind, lineno, colno);
					colno++;
					line++;
					return(tok);
				}
			}
			else if (*line == '"' || *line == '%') {
			/* Scan a string literal */
				int col = colno;
				int oldindex = 0, newindex = -1;
				char bracket = *line;
				char nxtchr ;
				char tmpstr[MAXLINE + 1];
				int   save_col;	   /* these are maintained to restore line */
				char *save_line;   /* in case of missing string bracket */
				int   save_newindex;

				if ( (strchr(line+1, bracket)) == 0 ) {
					char bracket_str[2];
					*bracket_str = bracket; 
					*(bracket_str + 1) = '\0';
					tok = newtoken(ERROR_SYM, namemap(bracket_str, 1),
					    lineno, colno);
					line++;
					colno++;
					return(tok);
				}
				while (1) {
					save_line = line + oldindex + 1;
					save_col = col + 1;
					save_newindex = newindex + 1;
					do {
						col++;
						oldindex++;
						newindex++;
						nxtchr = line[oldindex] ;
						tmpstr[newindex] = nxtchr ;
					}
					/* test separately for bracket for use of % as delimiter */
					while (nxtchr != bracket  && IS_STRING_CHAR(nxtchr));

					if (line[oldindex] == bracket) {
						if (line[oldindex + 1] == bracket) {
							tmpstr[newindex] = bracket ;
							oldindex++;
							col++;
						}
						else {
							tmpstr[newindex] = '\0';
							tok = newtoken(STRING_SYM, namemap(tmpstr,
							  newindex), lineno, colno+1);
							colno = col + 1;
							line += oldindex + 1;
							return(tok);
						}
					}
					else if (line[oldindex] == '"') {
						oldindex++;
						lexerr(lineno, col, col,
						  "% delimited string contains \", being ignored");
					}
					else if (line[oldindex] == '\0') {
						lexerr(lineno, colno, colno, "Missing string bracket");
						/* restore values of line and colno to values prior to
						 * last set of string characters 
			 			 */
						line = save_line;
						colno = save_col;
						/*  insert a closing string bracket */
						tmpstr[save_newindex] = bracket;
						tmpstr[save_newindex + 1] = '\0';
						tok = newtoken(STRING_SYM, namemap(tmpstr,
						  save_newindex + 1), lineno, colno);
						return(tok);
					}
/*
		    else if (isprint(line[oldindex]) || line[oldindex] == ' ')
			tmpstr[newindex] = line[oldindex];
*/
					else {
						char msg[80];

						sprintf(msg, "Invalid character %s in string deleted",
						  nonprintingmsg[line[oldindex++]]);
						lexerr(lineno, col, col, msg);
						col += (line[oldindex] == '\t') ? 7 - ((col-1)%8) : -1;
					}
				}
			}

			else if (ISDELIMITER(*line))	/* Scan a delimiter */
			{
				int len = 1, ind;
				char str[3];

				switch (*line) {
				case '=' :
					if (line[1] == '>')
						len = 2;
					break;
				case '*' :
					if (line[1] == '*')
						len = 2;
					break;
				case ':' :
				case '/' :
					if (line[1] == '=')
						len = 2;
					break;
				case '>' :
					if (line[1] == '=' || line[1] == '>')
						len = 2;
					break;
				case '<' :
					if (line[1] == '=' || line[1] == '<' || line[1] == '>')
						len = 2;
					break;
				case '.' :
					if (line[1] == '.')
						len = 2;
					break;
				case '!' :
					*line = '|';
					break;
				case '[' :	/* Change to a "(" */
					lexerr(lineno, colno, colno,
					  "Bad character \"[\", replaced by \"(\".") ;
					line[0] = '(' ;
					break ;
				case ']' :	/* Change to a ")" */
					/* Note that this case falls through to the next one */
					lexerr(lineno, colno, colno,
					  "Bad character \"]\", replaced by \")\".") ;
					line[0] = ')' ;
				case ')' :
					nextcanbeprime = 1;
					break;
				}
				strncpy(str, line, len);
				str[len] = '\0';
				ind = namemap(str, len);
				tok = newtoken(ind, ind, lineno, colno);
				colno += len;
				line += len;
				return(tok);
			}

			else if (*line == '_') {	/* An error- an underline _ */
				lexerr(lineno, colno, colno, "Break character misplaced");
				colno++;
				line++;
			}

			else {	/* An error- an unknown character */
				char msg[80];
				char ch[2];

				*ch = *line;
				ch[1] = '\0';
				sprintf(msg, "Bad character in file ignored: %s",
				    (isprint(*line)) ? ch : nonprintingmsg[*line]);
				lexerr(lineno, colno, colno, msg);
				if (isprint(*line))
					colno++;
				line++;
			}
		}
		if (getline() == EOF)
			return(newtoken(EOFT_SYM, EOFT_SYM, lineno, colno));
	}
}

static int scanidorint(char *str, int *ind, int *chread, int (*func)(char),
  int ignore_break)											/*;scanidorint*/
{
	/* Scanidorint: scan for an integer or id, with allowed characters
	 * determined by satisfying function func. 1 returned if found, 0 if not.
	 */
	/* ind is the index into the string str,
	 * chread is the index into the input string line
	 * func is a function to be called to determine what chars are to
	 * be included in the integer or identifier
	 */

	int hadnum = 0;

	while (1) {
		if (line[*chread] == '_') {
			lexerr(lineno, colno + *chread, colno + *chread,
			  "Break character misplaced");
			(*chread)++;
			continue;
		}
		if (!(*func)(line[*chread])) {
			if (hadnum)
				lexerr(lineno, colno + *chread - 1, colno + *chread - 1,
				  "Break character misplaced");
			break;
		}
		str[(*ind)++] = line[(*chread)++];
		hadnum = 1;
		while ((*func)(line[*chread]))
			str[(*ind)++] = line[(*chread)++];
		if (line[*chread] != '_')
			break;
		(*chread)++;
		if (!ignore_break)
			str[(*ind)++] = '_';
	}
	return(hadnum);
}

static void scanexp(char *str, int *ind, int *chread)			/*;scanexp*/
{
	/* Scanexp: scan for an (optional) exponent
	 * ind is the index into the string str,
	 * chread is the index into the input string line
	 */

	int oldchread;

	if (line[*chread] != 'E' && line[*chread] != 'e')
		return;
	oldchread = *chread;
	str[(*ind)++] = 'E';
	*chread += 1;
	if (line[*chread] == '+' || line[*chread] == '-')
		str[(*ind)++] = line[(*chread)++];
	if (!scanidorint(str, ind, chread, isdecimal, 1)) {
		lexerr(lineno, colno + oldchread, colno + *chread - 1,
		  "Incomplete exponent");
		str[(*ind)++] = '0';
	}
}

static int scandec(char *str, int *ind, int *chread, int (*func)(char))
																/*;scandec*/
{
	/* Scandec: scan for an integer followed possibly by a decimal point and 
	 * another integer, with digits determined by satisfying func. 1 is returned
	 * if an integer is found, 2 if a there was a decimal point, 0 if no digits
	 * found.
	 * ind is the index into the string str,
	 * chread is the index into the input string line
	 * func is a func indicating valid characters for numbers being scanned
	 */

	int stat;

	stat = scanidorint(str, ind, chread, func, 1);
	if (line[*chread] == '.') {
		if (line[*chread + 1] != '.') {
			if (!stat) {
				lexerr(lineno, colno + *chread, colno + *chread,
				  "Missing digit before decimal point");
				str[(*ind)++] = '0';
			}
			str[(*ind)++] = '.';
			(*chread)++;
			if (!scanidorint(str, ind, chread, func, 1)) {
				lexerr(lineno, colno + *chread - 1, colno + *chread - 1,
				  "Missing digit after decimal point");
				str[(*ind)++] = '0';
			}
			return(2);
		}
	}
	return(stat);
}

static void checkbased(char *str, int *ind)/*;checkbased*/
{
	/* Checkbased: check the validity of a based literal */

	int base, err = 0;
	char *pos;

	sscanf(str, "%d", &base);
	pos = strchr(str, '#');
	if (base < 2 || base > 16) {
		lexerr(lineno, colno, colno + pos - str - 1,
		  "Base not in range 2..16");
		err = 1;
	}
	else 
		while (*++pos != '#') {
			if (islower(*pos))
				*pos = toupper(*pos);
			if (isdigit(*pos) && *pos - '0' >= base
			  || isalpha(*pos) && *pos - 'A' >= base - 10) {
				lexerr(lineno, colno + pos - str, colno + pos - str,
				  "Invalid based-number digit");
				err = 1;
				break;
			}
		}
	if (err) {
		if (strchr(str, '.') == (char *)0) {
			*ind = 1;
			*str = '0';
		}
		else {
			*ind = 3;
			strcpy(str, "0.0");
		}
	}
}

static void convtoupper(char *s)							/*;convtoupper*/
{
	/* Convtoupper: convert an entire string to uppercase. */

	while (*s) {
		if (islower(*s))
			*s = toupper(*s);
		s++;
	}
}

/* merge below text formerly in namelist.c */

/* This file contains routines for dealing with namelist/namemap.
   The setup of this map is as follows. We have two arrays: numtostrtable
   and strtonumtable, which are used as hash tables for going from numbers
   to strings and strings to numbers. The hash function from numbers to
   strings is simply taking the number modulo the size of numtostrtable,
   which gives us both the row of numtostrtable where the proper entry for
   a given string should be found, and also where in this row it can be
   found, eliminating the need for searching. The numbers representing the
   strings are assigned sequentially, so we will always be adding a structure
   into a row a the end of the list. This list is kept circularly so as
   to be able to always find the beginning and end of the list quickly,
   and not keep two pointers. When going from strings to numbers, we must
   always search for the string, so the order of the strings in a given row
   of strtonumtable does not matter. Each structure that is put into
   these hash tables holds a string and the corresponding number, and two
   pointers. One pointer points to the next structure in the row of
   numtostrtable in which it lies, and the other points to the next structure
   in the row of strtonumtable in which it lies. Each structure is in two
   linked lists at once, one for each hash table. The grammar symbols and
   predefined pragmas are statically initialized to be in these maps, with
   all pointers set up properly.
*/

static void nlisthash(int num, int *row, int *links)			/*;nlisthash*/
{
	/* Nlisthash: Hashing function from numbers to strings */

	if (num <= 0) printf("nlisthash arg %d negative - chaos\n", num);
	*links = (num - 1) / NAMELISTSIZE;
	*row = (num - 1) % NAMELISTSIZE;
}

static int newnode(char *str, int len, int nmhash)				/*;newnode*/
{
	/* Newnode: Allocate storage for a new node; set the fields; insert in 
	 * namelist and namemap. The symbol number is returned. Nmhash is either
	 * the hashvalue for the given string if already known, or -1 indicating
	 * not yet known.
	 */

	struct namelistmap *node;
	int row, links;

	/* Allocate and set fields of node */
	node = (struct namelistmap *)malloc(sizeof(struct namelistmap));
	node->num = ++symcount;
	node->name = malloc((unsigned)(len + 1));
	strcpy(node->name, str);

	/* Insert in namelist */
	nlisthash(symcount, &row, &links);
	node->nextlist = numtostrtable[row]->nextlist;
	numtostrtable[row]->nextlist = node;
	numtostrtable[row] = node;

	/* Insert in namemap */
	if (nmhash == -1)
		nmhash = strhash(node->name) % NAMEMAPSIZE;
	node->nextmap = strtonumtable[nmhash];
	strtonumtable[nmhash] = node;

	return(symcount);
}

char *namelist(int num)											/*;namelist*/
{
	/* Namelist: Given a symbol number return the corresponding string (the
	 * number is assumed to correspond to an entry known to be in the table
	 * already)
	 */

	int row, links;
	struct namelistmap *node;

	nlisthash(num, &row, &links);
	node = numtostrtable[row]->nextlist;
	while (links--)
		node = node->nextlist;
	return(node->name);
}

int namemap(char *str, int len)									/*;namemap*/
{
	/* Namemap: Give the symbol number corresponding to a given string, putting 
	 * the string into the structure if not already there. If the string is
	 * already known to be in the table, then it is not necessary to give the
	 * length.
	 */

	int nmhash;
	struct namelistmap *node;
	int nnode;

#ifdef PDEBUG
	printf("namemap %s\n", str);
#endif
	nmhash = strhash(str) % NAMEMAPSIZE;
	for (node = strtonumtable[nmhash]; node != (struct namelistmap *)0; 
	  node = node->nextmap) {
		if (!strcmp(node->name, str)) {
#ifdef PDEBUG
			printf("namemap returns %d\n", node->num);
#endif
			return(node->num);
		}
	}
	nnode = newnode(str, len, nmhash);
#ifdef PDEBUG
	printf("namemap returns (new) %d\n", nnode);
#endif
	return nnode;
}

int name_map(char *str)											/*;name_map*/
{
	int nmhash;
	struct namelistmap *node;

	nmhash = strhash(str) % NAMEMAPSIZE;
	for (node = strtonumtable[nmhash]; node != (struct namelistmap *)0; 
	  node = node->nextmap) {
		if (!strcmp(node->name, str))
			return(1);
	}
	return(0);
}
