/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

/* adamrg - merge error and ada source files to make listing */

#include "config.h"
#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <malloc.h>
#include <string.h>
#ifdef IBM_PC
#include "stdlib.h"
#else
#endif
#include "miscprots.h"
#include "adamrgprots.h"


#ifndef IBM_PC
#include <sys/types.h>
#include <sys/file.h>
#endif

#ifdef SYSTEM_V
#include <fcntl.h>
#endif
#ifndef IBM_PC
#include <signal.h>
#endif

#ifdef BSD
#include "time.h"
#include <sys/resource.h>
#endif


#ifdef IBM_PC
#include "time.h"
#else
typedef long Time_type;
#endif

/*
 * Author: Alex Dreyzen Jan,1984
 * Revised: Brian Siritzky, June 1984
 * Revised: J. Chiabaut, November 1984
 * Revised: D. Shields, May 1985
 * Revised: D. Shields, July 1985
 * Revised: G. Schenker, April 1986
 * Revised: J. Chiabaut, May 1986
 * Revised: D. Shields, July 1986
 *	make into separate procedure, use single structure for all
 *	messages, simplify logic
 *		   
 */

/*
 * This program takes two arguments giving the name of an adafile and 
 * the msgfile/listfile  and then merges the messages in the file with 
 * suffix '.msg' and source in file with suffix '.ada' to produce 
 * listing file with suffix '.lis'.
 *
 * Function  main(argc,argv)  activates	 functions   init_msg_map(),
 * merge_ada_msg().
 * Function init_msg_map()  counts  lines in the filename.msg,
 * allocates space to store the keys and offsets of each  message,
 * and sorts offsets in ascending order of the keys. Function
 * printmsg() reads messages 
 *
 *
 * Message format is:
 *
 * type_of_msg line_left col_left line_right col_right	<TAB>	message
 *
 * Where type_of_msg is one of :
 *
 *   PRAGMA_LIST_ON 1
 *   PRAGMA_LIST_OFF 2
 *   PRAGMA_LIST_ERR 3
 *   PRAGMA_PAGE 4
 *   ERR_LEXICAL 10
 *   ERR_SYNTAX 11
 *   ERR_SEMANTIC 12
 *   ERR_WARNING 13
 *   INFORMATION 14
 *   ERR_BIND 15
 *   ERR_COMPILER 16
 *
 *  Note that these are defined in config.h
 */

#define MAXLINE 512

#define pagesize 55

#define VERSION_NO "1.11.2"

extern int  n_lex_err, n_syntax_err, n_semantic_err, n_binding_err, 
            n_warning_err, n_generator_err, n_information;
char	header[80];		/* header for output */
int	pageno = 0;		/* output page number */
int	realline = 0;		/* actual number of lines output */
int	n_error = 0;		/* Number of errors */
int	n_lex_err = 0;		/* Counts of the various kinds of messages */
int	n_syntax_err = 0;
int	n_semantic_err = 0;
int	n_generator_err = 0;
int	n_binding_err = 0;
int	n_warning_err = 0;
int     n_information = 0;
/* Pointers to message, ada, and list files */
FILE *msgfile, *adafile, *listfile;
char   *pmsg,
       *pada;
int     line1,
        line2,
        col1,
        col2,
        error_type;

int	msgs_total,
	m_type,
	line_msg,
	line_ada = 0,
	list_on = 1,
	msgs_read = 0;
typedef struct Msg_ent {
    short	msg_type;		/* message type */
    short	msg_line1;		/* starting line */
    short	msg_col1;		/* starting column */
    short	msg_line2;		/* ending line */
    short	msg_col2;		/* ending column */
    short	msg_num;		/* message number (for stable sort) */
    char        *msg_text;		/* message text */
    struct	Msg_ent *msg_prev;	/* link to previous message */
} Msg_ent;
typedef struct Msg_ent *Msg;
Msg *msg_array;
char   *data, *line;
int	adaeof = 0;
char blankl[132] ;	/* blank line for underscore */
char blanks[132];
char dashl[132] ;	/* dash line for underscore */
char dashes[132];

static void getada();
static void getmsg();
static void merge_ada_msg();
static void pblank(int);
static void underscore(int, int);
static void printada();
static void printmsg();
static void newpage();
static void newlin();
static int init_msg_map(char *);
static int compar(Msg *, Msg *);
static char *sindex(char *, char);
static int getlin();
static char *msgtype(int);

int mrg(char *adafilename, char *msgfilename, char *listfilename,
  char *list_arg)													/*;mrg*/
{
    char   *s;
#ifndef IBM_PC
    Time_type bintim;
#else
    time_t bintim;
#endif
    char   *day, *month, *date, *clock, *year;
    int list_opt;

    int    i,istatus;


    list_opt = strcmp(list_arg,"1") == 0;

    for (i=0;i<131;i++) blanks[i] = ' ';
    for (i=0;i<131;i++) dashes[i] = '-';
    blanks[131] = '\0';
    dashes[131] = '\0';
    data = malloc(MAXLINE);
    line = data;


/*
 * if no adafile is given or not open, print only messages
 */
   adafile = efopen(adafilename, "r", "t");
/*
 * returns if the message file is empty and a listing is not required
 */
   istatus = init_msg_map(msgfilename);
#ifdef DEBUG_MRG
   printf("init_msg status %d\n",istatus);
#endif
   if (istatus==-1) return RC_INTERNAL_ERROR;
   if(!istatus && !list_opt) return 0;
#ifdef DEBUG_MRG
printf("opening listfile %s\n",listfilename);
#endif
   listfile = efopen(listfilename, "w", "t");
   if (listfile==(FILE *)0) {
        fprintf(stderr, "Cannot open file %s.\n", listfilename);
        listfile = stderr;
   }

/* get the date and split it */
#ifdef DEBUG_MRG
	printf("get time\n");
#endif
/*  s = "Sun Apr 21 08:00:00 1985\n"; */
#ifndef IBM_PC
    bintim = time((long *) 0);
    s = (char *) ctime(&bintim);
#else
	time(&bintim);
	s = ctime(&bintim);
#endif
    day = s;
    s += 3;
    *s++ = '\0';
    month = s;
    s += 3;
    *s++ = '\0';
    date = s;
    s += 2;
    *s++ = '\0';
    clock = s;
    s += 8;
    *s++ = '\0';
    year = s;
    s += 4;
    *s = '\0';

    sprintf(header,
	    "NYU Ada/ED-C %s  %-15s  %s  %s %s %s  %s  PAGE   ",
	    VERSION_NO, OP_SYS, day, date, month, year, clock);
    newpage();
#ifdef DEBUG_MRG
printf("post header\n");
#endif
    if (adafile!=(FILE *)0) {
		getada();
		realline++;
    }
    else {
		line_ada = -1;
		adaeof = EOF;
		pada = (char *) 0;
    }
    getmsg();
    if (pmsg == (char *) 0)
		line_msg = 9999;
    merge_ada_msg();
    n_error = n_lex_err + n_syntax_err + n_semantic_err + n_binding_err
	  + n_generator_err;
    if (n_error) {
		fprintf(listfile, "\n	 %d error%s detected\n", n_error,
		  ((n_error == 1) ? "" : "s"));
      /* print again to the terminal if it is not stderr */
      if (listfile != stderr) {
          fprintf(stderr,"%d error%s detected\n", n_error,
                ((n_error == 1) ? "" : "s"));
      }

    }
    else {
      fprintf(listfile, "\n    No errors detected\n");
    }
    return 1;
}

static void getada()									/*;getada */
{
    line_ada++;
    adaeof = getlin();
    if (adaeof != EOF)
	pada = data;
    else
	pada = (char *) 0;
}

static void getmsg()									/*;getmsg */
{
    Msg msgp;
    if (msgs_read < msgs_total) {
		msgp = msg_array[msgs_read];
#ifdef DEBUG_MRG
		printf("getmsg msgs_read %d msgp %p\n",msgs_read, msgp);
#endif
		pmsg = msgp -> msg_text;
		line1 = msgp ->msg_line1;
		line2 = msgp ->msg_line2;
		line_msg = line2;
		col1 = msgp -> msg_col1;
		col2 = msgp -> msg_col2;
		error_type = msgp -> msg_type ;
		msgs_read++;
		return;
    }
    else {
		line_msg = 9999;
		pmsg = (char *) 0;
		return;
    }

}

static void merge_ada_msg()							/*;merge_ada_msg */
{
    int	    dummsg;

    while((pmsg != (char *) 0) ||(pada != (char *) 0)) {
		dummsg = 0;
		if (line_msg < line_ada) {/* only if adafile is present */
	    	while((line_msg < line_ada) && pmsg != (char *) 0) {
				printmsg();
				getmsg();
	    	}
		}

	if (line_msg == line_ada) {/* only if adafile is present */
	    switch(m_type) {
		case PRAGMA_PAGE:
		    dummsg = 1;
		    if ((pada != (char *) 0)) {
			if (list_on) {
			    printada();
			}
			getada();
		    }
		    if (list_on)
			newpage();
		    break;
		case PRAGMA_LIST_OFF:
		    dummsg = 1;
		    if (adaeof != EOF) {
			if (list_on)
			    printada();
			getada();
		    }
		    list_on = 0;
		    break;
		case PRAGMA_LIST_ON:
		    dummsg = 1;
		    if (adaeof != EOF) {
			printada();
			getada();
		    }
		    list_on = 1;
		    break;
		default:
		    dummsg = 0;
		    if (adaeof != EOF) {
			printada();
			getada();
		    }
		    printmsg();
	    }
	    getmsg();
	}

	if (line_msg >= line_ada) {/* if only one message on line */
	    if (list_on) {
			if (!dummsg)
		    	newlin();
			while((line_msg > line_ada) && adaeof != EOF) {
		   		printada();
		   		getada();
			}
	    }
	    else		/* read in lines, until the next message or EOF */
			while((line_msg > line_ada) && adaeof != EOF)
		    	getada();

	    if (adaeof == EOF) {/* adafile is not present or EOF reached */
			while((pmsg != (char *) 0) &&(line_msg < 9999)) {
		    	printmsg();
		    	getmsg();
			}
		    newlin();
			while(pmsg != (char *) 0) {
		    	printmsg();
		    	getmsg();
			}
	    }
	}
    }
}

#define printhat(col)pblank(col-1);fprintf(listfile,"^");fprintf(listfile,"\n")

static void pblank(int col)										/*;pblank */
{
    strcpy(blankl,blanks);
    realline++;
    if (col > 0) {
		blankl[col] = '\0';
		fprintf(listfile, "%s", blankl);
		blankl[col] = ' ';
    }
}

static void underscore(int col1, int col2)					/*;underscore */
{
    strcpy(dashl,dashes);
    pblank(col1 - 1);
    fprintf(listfile, "<");
    if (col2 - col1 > 1) {
		dashl[col2 - col1 - 1] = '\0';
		fprintf(listfile, "%s", dashl);
		dashl[col2 - col1 - 1] = '-';
    }
    fprintf(listfile, ">");
    fprintf(listfile, "\n");
}

static void printada()										/*;printada */
{
    if (++realline >= pagesize)
		newpage();
    fprintf(listfile, "%4d:   %s", line_ada, pada);
}

/*	This function prints error message, underscoring
	the corresponding place in the source line		*/

static void printmsg()										/*;printmsg */
{
    if (error_type >= ERR_LEXICAL) {
		if (error_type < INFORMATION) {
	    	if (adafile!=(FILE *)0)
				if (line1 == line2)
		    		if (col2 - col1 < 1) {
						printhat(col1 + 8);
		    		}
		    		else {
						underscore(col1 + 8, col2 + 8);
		    		}
			else {
		    	fprintf(listfile,
			      "\n	   Between line %d column %d and line %d column %d\n",
			      line1, col1, line2, col2);
		    	realline += 2;
			}
	    	else {
				realline += 2;
				if (line1 == line2)
		    		fprintf(listfile,
			    	  "\n	   Line %d between column %d and column %d\n",
			    	  line1, col1, col2);
				else
		    		fprintf(listfile,
			    	"\n	   Between line %d column %d and line %d column %d\n",
			    	  line1, col1, line2, col2);
	    	}
		}
	fprintf(listfile, "%s %s\n", msgtype(error_type), sindex(pmsg, '\t'));
	if (realline++ >= pagesize)
	    newpage();
    }
}

static void newpage()									/*;newpage */
{
	/*
	 * this procedure outputs a form feed, resets the line counter
	 * and prints the standard header at the top of the page
	 */
    pageno++;
    realline = 1;
    fprintf(listfile, "\f");
    /* Add the page number to the end of the string */
    fprintf(listfile, "%s %d\n\n", header, pageno);
}

static void newlin()											/*;newlin */
{
    if ((++realline >= pagesize))
	newpage();
    else
	fprintf(listfile, "\n");
}

static int init_msg_map(char *msgfilename)				/*;init_msg_map */
{
    int    i, line1,line2,col1,col2,type;
    int    nitems;
    int    tab_found;
    Msg	m_prev;
    char *dp;
    Msg		msg;


    msgfile = efopen(msgfilename, "r","t");
    if (msgfile==(FILE *)0) /* cannot open file */
	return(FALSE);
    m_prev = (Msg)0;
#ifdef DEBUG_MRG
	printf("start reading messages\n");
#endif
    while (fgets(data, MAXLINE, msgfile) != (char *)0) {
    	/* delete trailing newline */
		data[strlen(data)-1] = '\0';
		msg = (Msg) malloc(sizeof(Msg_ent));
		if (msg==(Msg)0) {
			fprintf(stderr,"Cannot read error messages\n");
			return -1;
		}
		nitems = sscanf(data,"%d %d %d %d %d",
		  &type, &line1, &col1, &line2, &col2);
		if (nitems!=5) {
			printf("scanned %d\n",nitems);
			printf(data,"%s\n");
			chaos("bad message line");
		}
		msgs_total++;
		msg->msg_num = msgs_total;
		msg->msg_type = type;
		msg->msg_line1 = line1;
		msg->msg_col1 = col1;
		msg->msg_line2 = line2;
		msg->msg_col2 = col2;
		msg->msg_prev = m_prev;
#ifdef DEBUG_MRG
		printf("new msg %p previous %p\n", msg, m_prev);
#endif
		m_prev = msg;
		/* now find message text */
		dp = data;
		tab_found = 0;
		while (*dp != '\0') {	/* skip to first tab */
			if (*dp=='\t') {
		    	tab_found = 1;
		    	break;
			}
			dp++;
		}
		if (!tab_found) dp = data;
		msg->msg_text = strjoin(dp,""); /* copy message text */
#ifdef DEBUG_MRG
		printf("mrg message %d type %d line1 %d col1 %d line2 %d col2 %d\n%s\n",
		 msg->msg_num, msg->msg_type, msg->msg_line1, msg->msg_col1,
		 msg->msg_line2, msg->msg_col2, msg->msg_text);
#endif
    }
    /* now form msg_array, array of pointers to messages */
    if (msgs_total) {
		msg_array = (Msg *) calloc(msgs_total, sizeof(Msg));
		if (msg_array == (Msg *)0) {
		fprintf(stderr,"Cannot read error messages\n");
		return -1;
		}
		for (i=msgs_total-1;i>=0;i--) {
	    	msg_array[i] = m_prev;
#ifdef DEBUG_MRG
		printf("init msg_array i %d ptr %p m_prev %p\n",i,msg_array+i,m_prev);
#endif
	    m_prev = m_prev->msg_prev;
#ifdef DEBUG_MRG
		printf("m_prev set to %p\n",m_prev);
#endif
		}
    }
    else {
		msg_array = (Msg *) 0;
    }

    if (msgs_total) {
		qsort(msg_array, msgs_total, sizeof(Msg),
		  ( int (*)(const void *, const void *)) compar);
    }
    return msgs_total;
}

static int  compar(Msg *a, Msg *b)								/*;compar */
{
    Msg c,d;

    c = *a; d = *b;
	/* compare by lines, then by columns */ 
    if (c->msg_line2 >d->msg_line2) return 1;
    else if (c->msg_line2 < d->msg_line2) return -1;
    /* if same line, use message number */
    else if (c->msg_num >d->msg_num) return 1;
    else if (c->msg_num <d->msg_num) return -1;
    return 0; /* if same */
}

/* This is probably meant to be 4.2 index(), but give it separate name for now*/
static char *sindex(char *s, char c)						/*;sindex */
{
    while(*s != c) {
		if ((*s == '\0') ||(*s == '\n'))
	    	return s;
		s++;
    }
    return++ s;
}


static int getlin()											/*;getlin */
{
	/* this is a stripped down version of getlin in adalex.c */
    int	    ch, ind = 0;

    if (feof(adafile))
		return EOF;
    for (;;) {
		ch = getc(adafile);
		if (ch == EOF)
	    	break;
		if (ch <= 13 && ch >= 10)
	    	break;
       	if (ind == MAXLINE) {
           	while((ch = getc(adafile)) != EOF && !(10 <= ch && ch <= 13));
           	break;
       	}
       	else
           	data[ind++] = ch;
    }

    data[ind++] = '\n';
    data[ind] = '\0';
    if (ch == EOF && !ind)
		return EOF;
    return (0);
}

static char *msgtype(int n)		/*;msgtype */
{
    char   *s;

    switch(n) {
	case ERR_LEXICAL:
	    s = "*** ERROR:";
	    n_lex_err++;
	    break;
	case ERR_SYNTAX:
	    s = "*** ERROR:";
	    n_syntax_err++;
	    break;
	case ERR_SEMANTIC:
	    s = "*** ERROR:";
	    n_semantic_err++;
	    break;
	case ERR_COMPILER:
	    s = "*** ERROR:";
	    n_generator_err++;
	    break;
	case ERR_WARNING:
	    s = "* WARNING:";
	    n_warning_err++;
	    break;
	case INFORMATION:
	    s = "    ";
            n_information++;
	    break;
	case ERR_BIND:
	    s = "*** ERROR:";
	    n_binding_err++;
	    break;
    }
    return (s);
}
