/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* misc.c - miscellaneous programs */


#include "config.h"
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "time.h"
#include "ifile.h"
#include "miscprots.h"
#ifdef BSD
#include <strings.h>
#endif

#ifndef LIBDIR
#define LIBDIR "/usr/local/lib"
#endif

#ifdef ADALIB
#define EXIT_INTERNAL_ERROR
#endif

#ifdef BINDER
#define EXIT_INTERNAL_ERROR
extern int adacomp_option;
#endif

#ifdef INT
#define EXIT_INTERNAL_ERROR
#endif

#ifndef EXPORT
#undef EXIT_INTERNAL_ERROR
#endif
#ifdef BSD
#include <sys/file.h>
#endif

char *LIBRARY_PREFIX= "";

/* PREDEFNAME gives directory path to predef files.
 * libset() is used to toggle between libraries (the users and predef).
 * tname = libset(lname) sets library prefix for ifopen, etc. to lname
 * and returns prior setting in tname.
 */

static void openerr(char *filename, char *mode);

#ifdef SMALLOC
unsigned int smalloc_free = 0;
char	*smalloc_ptr;
#define SMALLOC_BLOCK 2000
char **smalloc_table = (char **)0;
unsigned smalloc_blocks = 0;
#endif

char *smalloc(unsigned n)										/*;smalloc*/
{
	/* variant of malloc for use for blocks that will never be freed,
	 * primarily blocks used for small strings. This permits allocation
	 * in larger blocks avoiding the malloc overhead required for each block.
	 */
#ifndef SMALLOC
	return emalloct(n, "smalloc");
#else
	char *p;
	if (n & 1) n+= 1;
#ifdef ALIGN4
	if (n & 2) n+= 2;
#ifdef ALIGN8
    if (n & 4) n+= 4;
#endif
#endif

	if (n > SMALLOC_BLOCK) { /* large block allocated separately */
		p = emalloct(n, "smalloc");
		return p;
	}
	if (n > smalloc_free) {
		smalloc_ptr = emalloct(SMALLOC_BLOCK, "smalloc-block");
		smalloc_free = SMALLOC_BLOCK;
		smalloc_blocks++;
		if (smalloc_blocks == 1) {
			smalloc_table = (char **) emalloct(sizeof (char **),
			  "smalloc-table");
		}
		else { /* reallocate blocks */
			smalloc_table = (char **) erealloct((char *)smalloc_table,
			  sizeof(char **) * (smalloc_blocks), "smalloc-table-realloc");
		}
		smalloc_table[smalloc_blocks-1] = smalloc_ptr;
	}
	p = smalloc_ptr;
	smalloc_ptr += n;
	smalloc_free -= n;
	return p;
#endif
}

#ifdef DEBUG
void smalloc_list()
{
	int i;
	char **st;
	st = smalloc_table;
	for (i = 0; i < smalloc_blocks; i++) {
		printf("%d %ld %x\n", i, *st, *st);
		st++;
	}
}
#endif

int is_smalloc_block(char *p)							/*;is_smalloc_block*/
{
	/* returns TRUE is p points within block allocated by smalloc */
#ifdef SMALLOC
	int i;
	char **st;

	st = smalloc_table;
	if (smalloc_blocks == 0) chaos("is_malloc_block - no blocks");
	for (i = 0; i < smalloc_blocks; i++) {
		if (*st <= p && p  < (*st+(SMALLOC_BLOCK-1)))
			return TRUE;
		st++;
	}
	return FALSE;
#else
	return FALSE;
#endif
}

void capacity(char *s)				/*;capacity*/
{
	/* called  when compiler capacity limit exceeded.
	 * EXIT_INTERNAL_ERROR is defined when the module is run by itself
	 * (not spawned from adacomp) and DEBUG is not defined.
	 */
#ifdef EXIT_INTERNAL_ERROR
	fprintf(stderr, "capacity limit exceeded: %s\n", s);
	exitp(RC_INTERNAL_ERROR);
#else
#ifdef DEBUG
	printf("capacity limit exceeded: %s\nexecution abandoned \n", s);
#endif
	fprintf(stderr, "capacity limit exceeded: %s\n", s);
	exitp(RC_INTERNAL_ERROR);
#endif
}

#ifdef CHAOS
void chaos(char *s)												/*;chaos*/
{
	/* called when internal logic error detected and it is not meaningful
	 * to continue execution. This is never defined for the export version.
	 */
	fprintf(stderr, "chaos: %s\nexecution abandoned \n", s);
	printf("chaos: %s\nexecution abandoned \n", s);
	exitp(RC_INTERNAL_ERROR);
}
#else
void exit_internal_error()						/*;exit_internal_error*/
{
	/* called when internal logic error detected and it is not meaningful
	 * to continue execution. This procedure is called by the export version.
	 * EXIT_INTERNAL_ERROR is defined when the module is run by itself
	 * (not spawned from adacomp) and EXPORT is defined.
	 * Now that adabind is a separate module which can be called by itself
	 * or spawned from adacomp, we must test the run time flag adacomp_option
	 * to determine which case it is.
	 */
#ifdef EXIT_INTERNAL_ERROR
#ifdef BINDER
	if (adacomp_option)
#endif
		fprintf(stderr, "Adaed internal error - Please report.\n");
	exit(RC_INTERNAL_ERROR);
#else
	exit(RC_INTERNAL_ERROR);
#endif
}
#endif

void exitp(int n)												/*;exitp*/
{
	/* synonym for exit() used so can trap exit() calls with debugger */
	exit(n);
}

char *ecalloc(unsigned nelem, unsigned nsize)			/*;ecalloc */
{
	/* calloc with error check if no more */

	char   *p;

	if (nelem > 20000) chaos("ecalloc: ridiculous argument");

	p = calloc (nelem, nsize);
	if (p == (char *) 0)
		capacity("out of memory \n");
	return p;
}

char *emalloc(unsigned n)										/*;emalloc */
{	/* avoid BUGS - use calloc which presets result to zero  ds 3 dec 84*/
	/* malloc with error check if no more */

	char   *p;

	if (n > 50000) chaos("emalloc: ridiculous argument");
	p = calloc (1, n);
	if (p == (char *) 0)
		capacity("out of memory \n");
	return (p);
}

char *erealloc(char *ptr, unsigned size)						/*;eralloc */
{
	/* realloc with error check if no more */

	char   *p;

	p = realloc (ptr, size);
	if (p == (char *) 0)
		capacity("erealloc: out of memory \n");
	return (p);
}

char *strjoin(char *s1, char *s2)								/*;strjoin */
{
	/* return string obtained by concatenating argument strings
	 * watch for either argument being (char *)0 and treat this as null string
	 */

	char   *s;

	if (s1 == (char *)0) s1= "";
	if (s2 == (char *)0) s2 = "";
	s = smalloc((unsigned) strlen(s1) + strlen(s2) + 1);
	strcpy(s, s1);
	strcat(s, s2);
	return s;
}

int streq(char *a, char *b)											/*;streq*/
{
	/* test two strings for equality, allowing for null pointers */
	if (a == (char *)0 && b == (char *)0)
		return TRUE;
	else if (a == (char *)0 || b == (char *)0)
		return FALSE;
	else return (strcmp(a, b) == 0);
}

char *substr(char *s, int i, int j)								/*;substr */
{
	/* return substring s(i..j) if defined, else return null ptr*/

	int	n;
	char	*ts, *t;

	if (s == (char *)0) return (char *) 0;
	n = strlen(s);
	if (!(i > 0 && j <= n && i <= j)) return (char *)0;
	/* allocate result, including null byte at end */
	ts = smalloc((unsigned) j - i + 2);
	t = ts;
	s = s + (i - 1); /* point to start of source*/
	for (; i <= j; i++) *t++ = *s++; /* copy characters */
	*t = '\0'; /* terminate result */
	return ts;
}

/* getopt(3) procedure obtained from usenet */
/*
 * getopt - get option letter from argv
 */
#ifdef IBM_PC
#define nogetopt
#endif

#ifdef nogetopt
char   *optarg;				/* Global argument pointer. */
int	optind = 0;				/* Global argv index. */

static char *scan = NULL;	/* Private scan pointer. */

int getopt(int argc, char **argv, char *optstring)				/*;getopt */
{
	register char   c;
	register char  *place;
	optarg = NULL;

	if (scan == NULL || *scan == '\0') {
		if (optind == 0)
			optind++;

		if (optind >= argc || argv[optind][0] != '-' || argv[optind][1] == '\0')
			return (EOF);
		if (strcmp (argv[optind], "--") == 0) {
			optind++;
			return (EOF);
		}

		scan = argv[optind] + 1;
		optind++;
	}

	c = *scan++;
	place = strchr (optstring, c);

	if (place == NULL || c == ':') {
		fprintf (stderr, "%s: unknown option -%c\n", argv[0], c);
		return ('?');
	}

	place++;
	if (*place == ':') {
		if (*scan != '\0') {
			optarg = scan;
			scan = NULL;
		}
		else {
			optarg = argv[optind];
			optind++;
		}
	}
	return (c);
}
#endif

char *greentime(int un)										/*;greentime*/
{
	/* get greenwich time in string of 23 characters.
	 * format of result is as follows
	 *	1984 10 02 16 30 36 nnn
	 *	123456789a123456789b123
	 *	year mo da hr mi se uni
	 *
	 * greenwich time is used to avoid problems with daylight savings time.
	 * The last three characters are the compilation unit number
	 * (left filled with zeros if necessary).
	 * NOTE: changed to use local time to give approx. same time as
	 * SETL version			ds  20 nov 84
	 */

	char	*s;
#ifndef IBM_PC
	long clock;
#else
	/* IBM_PC (Metaware) */
	time_t clock;
#endif
	/*struct tm *gmtime();*/
	struct tm *t;
#ifndef IBM_PC
	clock = time(0);
#else
	time(&clock);
#endif
	s = smalloc(24);
	/*t = gmtime(&clock);*/
	t = localtime(&clock);
	sprintf(s,"%04d %02d %02d %02d %02d %02d %03d",
#ifdef IBM_PC
	  /* needed until Metaware fixes bug in tm_year field (ds 6-19-86) */
	  t->tm_year , t->tm_mon + 1, t->tm_mday,
#else
	  t->tm_year + 1900, t->tm_mon + 1, t->tm_mday,
#endif
	  t->tm_hour, t->tm_min, t->tm_sec, un);
	return s;
}

FILE *efopenl(char *filename, char *suffix, char *type, char *mode)	/*;efopenl*/
{
	char       *fname;
	FILE       *f;

	fname = ifname(filename, suffix);
	f =  efopen(fname, type, mode);
	efree(fname);
	return f;
}

FILE *efopen(char *filename, char *type, char *mode)				/*;efopen*/
{
	FILE	*f;
#ifdef IBM_PC
	char    *p;
	/* mode only meaningful for IBM PC for now */

	p = emalloc((unsigned) (strlen(type) + strlen(mode) + 1));
	strcpy(p, type);
	strcat(p, mode);
	f = fopen(filename, p);
	efree(p);
#else
	f = fopen(filename, type);
#endif
	if (f == (FILE *)0)
		openerr(filename, type);
	return f;
}

void efree(char *p)												/*;efree*/
{
	/* free with check that not tryig to free null pointer*/
	if (p == (char *)0)
		chaos("efree: trying to free null pointer");
	free(p);
}

int strhash(char *s)										/*;strhash*/
{
	/* Hashing function from strings to numbers */

	register int hash = 0;

	/* add character values together, adding in the cumulative hash code
	 * at each step so that 'ABC' and 'BCA' have different hash codes.
	 */
	while (*s)
		hash += hash + *s++;
	if (hash < 0) hash = - hash; /* to avoid negative hash code */
	return hash;
}

char *unit_name_type(char *u)							/*;unit_name_type*/
{
	int	n;
	char	*s;

	n = strlen(u);
	if (n < 2) {
		s = smalloc(1); 
		*s = '\0'; 
		return s;
	}
	/* otherwise, return first two characters */
	s = smalloc(3);
	s[0] = u[0];
	s[1] = u[1];
	s[2] = '\0';
	return s;
}

#ifdef BSD
/* BSD doesn't support strchr() and strrchr(), but they are just
 * named index() and rindex(), respectively, so here is code for BSD
 */
char *strchr(const char *s, int c)
{
	return index(s, (char) c);
}

char *strrchr(const char *s, int c)
{
	return rindex(s, (char) c);
}
#endif

char *libset(char *lname)										/*;libset*/
{
	char *old_name;

	old_name = LIBRARY_PREFIX;
	LIBRARY_PREFIX = lname;
	return old_name;
}

char *ifname(char *filename, char *suffix)						/*;ifname*/
{
	char *fname;

	/* allow room for library prefix, file name and suffix */
	fname = emalloc((unsigned) (strlen(LIBRARY_PREFIX) + strlen(filename) +
	  strlen(suffix) + 3));
	if (strlen(LIBRARY_PREFIX)) { /* prepend library prefix if present */
		strcpy(fname, LIBRARY_PREFIX);
#ifdef IBM_PC
		strcat(fname, "\\");
#endif
#ifdef BSD
		strcat(fname, "/");
#endif
#ifdef SYSTEM_V
		strcat(fname, "/");
#endif
		strcat(fname, filename);
	}
	else {
		strcpy(fname, filename); /* copy name if no prefix */
	}
	if (strlen(suffix)) {
		strcat(fname, ".");
		strcat(fname, suffix);
	}
	return fname;
}

IFILE *ifopen(char *filename, char *suffix, char *mode, int pass)	/*;ifopen*/
{
	FILE  *file;
	char  modec;
	char  *fname;
	long  s = 0L;
	int   nr, opened = FALSE, error = FALSE;
	IFILE  *ifile;
#ifdef IBM_PC
	char *t_name;
#endif

	modec= mode[0];

	fname = ifname(filename, suffix); /* expand file name */

#ifdef IBM_PC
	/* mode only meaningful for IBM PC for now */
	t_name = emalloc((unsigned) (strlen(mode) + 2));
	strcpy(t_name, mode);
	strcat(t_name, "b");
	file = fopen(fname, t_name);
	efree(t_name);
#else
	file = fopen(fname, mode);
#endif

	if (file == (FILE *)0) {
		if (pass)
			return (IFILE *) 0;
		else
			openerr(fname, mode);
	}
	ifile = (IFILE *) emalloc(sizeof(IFILE));
	if (modec == 'w') { /* write header */
		/* write long at start to later be replaced with slots offset */
		ifile->fh_mode = modec;
		ifile->fh_slots = 0;
		ifile->fh_units_end = 0;
		/* will be upated on close */
		fwrite((char *) ifile, sizeof(IFILE), 1, file);
	}
	else if (modec == 'r') { /* read and check header */
		nr = fread((char *) ifile, sizeof(IFILE), 1, file);

		if (nr != 1) {
#ifdef DEBUG
			printf("ifopen - unable to read header\n");
#endif
			error = TRUE;
		}
	}
	if (error) {
		openerr(fname, mode);
	}
	ifile->fh_file = file;
	ifile->fh_mode = modec;

	efree(fname);
	return ifile;
}

static void openerr(char *filename, char *mode)					/*;openerr*/
{
	/* EXIT_INTERNAL_ERROR is defined when the module is run by itself
	 * (not spawned from adacomp) and DEBUG is not defined.
	 */
#ifdef EXIT_INTERNAL_ERROR
	fprintf(stderr, "Unable to open file %s for %s \n", filename,
	  (strcmp(mode, "w") == 0 ? "writing"
	  : (strcmp(mode, "r") == 0 ? "reading"
	  : (strcmp(mode, "a") == 0 ? "appending"
	  :  mode))));
	exit(RC_ABORT);
#else
	fprintf(stderr, "Unable to open file %s for %s \n", filename,
	  (strcmp(mode, "w") == 0 ? "writing"
	  : (strcmp(mode, "r") == 0 ? "reading"
	  : (strcmp(mode, "a") == 0 ? "appending"
	  :  mode))));
	exit(RC_ABORT);
#endif
}

void ifclose(IFILE *ifile)									/*;ifclose*/
{
	FILE *file;


	file = ifile->fh_file;
	/* write out file header if write mode */
	if (ifile->fh_mode == 'w') {
		ifile->fh_mode = '\0';
		ifseek(ifile, "update-header", 0L, 0);
		fwrite((char *)ifile, sizeof(IFILE), 1, file);
	}
	if (file == (FILE *)0)
		chaos("ifclose: closing unopened file");
	fclose(file);
	ifile->fh_file = (FILE *)0;
}

void ifoclose(IFILE *ifile)									/*;ifoclose*/
{
	/* close file if still open */
	if (ifile != (IFILE *) 0 && ifile->fh_file != (FILE *) 0) {
		ifclose(ifile);
	}
}

long ifseek(IFILE *ifile, char *desc, long offset, int ptr)		/*;ifseek*/
{
	long begpos, endpos, seekval;
	begpos = iftell(ifile);
	seekval = fseek(ifile->fh_file, offset, ptr);
	if (seekval == -1) chaos("ifseek: improper seek");

	endpos = iftell(ifile);
	return endpos;
}

long iftell(IFILE *ifile)									/*;iftell*/
{
	/* ftell, but arg is IFILE */
	return ftell(ifile->fh_file);
}

/* define MEAS_ALLOC to measure alloc performance */
#define MEAS_ALLOC
/* this causes each malloc action to write a line to standard output
 * formatted as follows:
 * code:one of a, r, f
 * a	allocate block
 * r	reallocate block
 * f	free block
 * the block address (integer)
 * the block length (or zero if not applicable)
 * the remainder of the line describes the action
 */

#ifndef EXPORT
char *emalloct(unsigned n, char *s)								/*;emalloct*/
{
	char *p;
	p = emalloc(n);
	return p;
}
#endif

#ifndef EXPORT
char *malloct(unsigned n, char *s)		/*;malloct*/
{
	/* like emalloct, but ok if not able to allocate block */
	char *p;
	p = malloc(n);
	return p;
}
#endif

#ifndef EXPORT
char *ecalloct(unsigned n, unsigned m, char *msg)
{
	char *p;
	p = ecalloc(n, m);
	return p;
}
#endif

#ifndef EXPORT
char *erealloct(char *ptr, unsigned size, char *msg)		/*;erealloct*/
{
	char *p;
	p = erealloc(ptr, size);
	return p;
}
#endif

#ifndef EXPORT
void efreet(char *p, char *msg)									/*;efreet*/
{
	efree(p);
}
#endif

char *predef_env()			/*;predef_env*/
{
#ifndef IBM_PC
	char *s = getenv("ADAEDPREDEF");
	if (s == (char *)0) s = get_libdir();
	return s;
#else
	char *getenv();
	return getenv("ADAED");
#endif
}

char *get_libdir()
{
    char *s = getenv("ADAED");
    if (s == (char *)0) {
#ifndef IBM_PC
        return LIBDIR;
#else
        fprintf(stderr, "ADAED variable must be defined\n");
        exitp(RC_ABORT);
#endif
    }
    else
        return s;
}

char *parsefile(char *s, int *np, int *nb, int *ns)				/*;parsefile*/
{
	/* Parse file name s, returning the length of prefix, base part, and
	 * suffix in np, nb, and nl, respectively. A pointer to the start of
	 * the base part is returned, or the null pointer if no base part.
	 * The suffix is assumed to begin with period.
	 * The prefix ends with the last instance of any of the prefix characters.
	 */

#ifdef IBM_PC
    char   *prefix_chars = ":/\\";
#endif
#ifdef BSD
    char   *prefix_chars = "/";
#endif
#ifdef SYSTEM_V
    char   *prefix_chars = "/";
#endif
    int    n,i;
    char   *pb;
    char   *p, *p2;
    char   *suffix_chars = ".";
    int    have_prefix = 0;

    n = strlen(s);
    pb = s; /* assume name starts with base */
    *ns = 0;
    p = s + n; /* point to last (null) character in s */
    /* find length of suffix */
    /* but if find a prefix character first, then no suffix possible */
    for (i = n - 1; i >= 0; i--) {
		p--; 
		for (p2 = prefix_chars; *p2 !='\0';) {
	    	if (*p == *p2++) {
		 		/* (p-s) gives number of characters before suffix */
		 		have_prefix = 1;
		 		break;
	    	}
		}
		if (!have_prefix) {
	    	for (p2 = suffix_chars; *p2 !='\0';) {
				if (*p == *p2++) {
		     		/* (p-s) gives number of characters before suffix */
		     		*ns = n - (p - s);
		     		break;
				}
	    	}
		}
    }
    /* find length of prefix */
    *np = 0;
    p = s + n;
    for (i = n - 1; i >= 0; i--) {
		p--; 
		for (p2 = prefix_chars; *p2 !='\0';) {
	    	if (*p == *p2++) {
		 		p++; /* include last delimiter in prefix */
		 		/* (p-s) now gives prefix length*/
		 		*np = (p - s);
		 		pb = p;
		 		break;
	    	}
		}
    }
    /* base is what remains after removing prefix and suffix*/
    *nb = n - (*np + *ns);
    if (*nb == 0)
		pb = (char *)0; /* if no base */
    return pb;
}
