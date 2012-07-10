/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <string.h>
#ifdef __GNUG__
#define WAITPARM (int*)
#else
#define WAITPARM (union wait*)
#endif
#include "config.h"
#include "adamrgprots.h"
#include "miscprots.h"

#include <sys/types.h>
#ifdef IBM_PC
#include <fcntl.h>
#include <process.h>
#else
#include <sys/file.h>
#endif

#ifdef SYSTEM_V
#include <fcntl.h>
#endif
#include <signal.h>

#ifdef BSD
#include "time.h"
#include <sys/resource.h>
#endif

static int check_status(int, char *, char *);
static char *getsym(char *, char *);
static void arg_dump();
static int run_prog(char *, char **);
static void delete_file(char *);

char   *argname;
int     opts_cnt;
char   *other_opts[20];
char   *interface_opts[20];
int     interface_cnt = 0;
int	maxstatus = RC_SUCCESS; /* maximum exit status from called programs */
int     exec_trace = 0;	/* set to print generated command lines */

/* names of executables to use if not defined by environment */
#define FRONT_NAME "adafront"
#define GEN_NAME "adagen"
#define BND_NAME "adabind"

/* status_get extracts program exit code */
#ifdef IBM_PC
#define status_get(s)        (s)
#define system_status_get(s) (s)
#else
#define status_get(s)  	     ((s)>>8)
#define system_status_get(s) ((s) & 0xff)
#endif

char   *base_name;

main(int argc, char **argv)
{
	int     c,fp;
	int     status, ok = TRUE;
	extern int  optind;
	extern char *optarg;
	char   *FRONT, *GEN, *BND; 
	char   *arg_name;
	char   *lib_name;
	char   *list_name;
	char   *source_name;
	char   *msg_name;
	char   *tmp_name;
	char   *s_temp;
	char   *l_name;
	char   *basep;
	int	   prefix_len, base_len, suffix_len;
	char   *lib_opt_str, *main_unit_name;
	char   *object_files = "";
	char   *front_options, *gen_options;
	int     bind_opt = 0, main_opt = 0, save_msg_opt = 0 ;
	int     list_opt = FALSE;   /* set to generate a listing */
	char   *list_arg;		/* for passing list_opt to mrg */
	int     lib_opt = FALSE;    /* set to TRUE if -l specified */
	int     newlib_opt = FALSE; /* set to TRUE if -n specified */
	int	    time_limit = 15;    /* default time limit in minutes */
#ifdef BSD
	struct rlimit rlp;
#endif

/* initializations */
	arg_name = (char *) 0;
	lib_name = (char *) 0;
	front_options = "";
	gen_options = "";

/*
 * command options
 *	-a		generated line number instructions
 *	-b 		bind the unit specified by 'm' option
 *	-g		insert generated code into listing
 *      -i              specify object files and libraries for pragma interface
 *	-l libname	(old) library libname
 *	-m main unit  	specify the main binding unit.
 *			or use default main unit
 *	-n libname	new library libname
 *      -s		create source program listing
 *	-v		trace executed commands and exit status
 *      -Y		save message files (for running B tests)
 *  	-P		compile predef
 */

#ifdef IBM_PC
	while((c = getopt(argc, argv, "AaBbGgL:l:M:m:NnSsVvYPi:")) != EOF) {
          if (isupper(c)) c = tolower(c);
#else
	while((c = getopt(argc, argv, "abgl:m:nsvMPi:")) != EOF) {
#endif
	switch(c) {
	  case 'a':
		s_temp = emalloc(strlen(gen_options) + 2);
		strcpy(s_temp, gen_options);
		strcat(s_temp, "l");
		gen_options = s_temp;
		break;
	  case 'b':
		bind_opt = 1;
		break;
	  case 'g':
		s_temp = emalloc(strlen(gen_options) + 2);
		strcpy(s_temp, gen_options);
		strcat(s_temp, "g");
		gen_options = s_temp;
		break;
	  case 'l':
		lib_opt = TRUE;
		lib_name = emalloc(strlen(optarg) + 1);
		strcpy(lib_name, optarg);
		break;
	  case 'm':    
		main_opt = 1;
		main_unit_name = emalloc(strlen(optarg) + 1);
		strcpy(main_unit_name, optarg);
		break;
	  case 'n':
		newlib_opt = TRUE;
		break;
	  case 'i':
		s_temp = emalloc(strlen(optarg) + 1);
		strcpy(s_temp, optarg);
		interface_opts[interface_cnt++] = s_temp;
		break;
	  case 's':
		list_opt++;
		break;
	  case 'v':
		exec_trace++;
		break;
	  case 'Y':
		save_msg_opt = TRUE ;
		break;
	  case 'P':
		s_temp = emalloc(strlen(front_options) + 2);
		strcpy(s_temp, front_options);
		strcat(s_temp, "p");
		front_options = s_temp;
		s_temp = emalloc(strlen(gen_options) + 2);
		strcpy(s_temp, gen_options);
		strcat(s_temp, "p");
		gen_options = s_temp;
		break;
	  case '?':
		exit(RC_ABORT);
		break;
		default:
		fprintf(stderr, "Unknown Option: %c\n", c);
		exit(RC_ABORT);
	}
	}
	if (optind < argc)
	arg_name = argv[optind];
	if (arg_name == (char *) 0) {
	fprintf(stderr,"Invalid Usage: No ada file specified\n");
	exit(RC_ABORT);
	}
	if (!lib_opt) { /* if -l not specified, try to get from environment */
	   lib_name = getenv("ADALIB");
	   if (lib_name!=(char *)0) {
	   lib_opt++;
	}
	if (lib_opt) {
		printf("library defined by ADALIB: %s\n",lib_name);
	}
	}
	if (!lib_opt) {
	   fprintf(stderr,
		"Invalid Usage: please specify a library\n");
	   exit(RC_ABORT);
	}
#ifdef BSD
	getrlimit(RLIMIT_CPU,&rlp);
	(&rlp)->rlim_cur = time_limit*60;     /* limit to time_limit mins */
	setrlimit(RLIMIT_CPU,&rlp);
#endif

	basep = parsefile(arg_name, &prefix_len, &base_len, &suffix_len);
	/* check for presence of ada file;  if none, make it ada */
	if (suffix_len ==0) {
	source_name = emalloc(strlen(arg_name) + 4 + 1);
	strcpy(source_name, arg_name);
	strcat(source_name, ".ada");
	}
	else {
		source_name = arg_name;
	}
	base_name = emalloc(base_len + 1);
	strncpy(base_name, basep, base_len);
	if ((fp = open(source_name,O_RDONLY,0700)) < 0) {
	fprintf(stderr,"Cannot access file %s\n",source_name);
	exit(RC_ABORT);
	}
	close(fp);


	if (newlib_opt){
		if (exec_trace) {
		fprintf(stderr, "mkdir %s ", lib_name);
		}
		status = mkdir(lib_name, 0777);
		if (exec_trace) {
		fprintf(stderr, " ? %d\n", status);
		}
	}
	status = 0;
	if (status) {
		fprintf(stderr,"%s cannot be used as a library\n", lib_name);
		exit(RC_ABORT);
	}
	if (!newlib_opt) {
		/* check for presence of library file */
	l_name = emalloc(strlen(lib_name) + strlen(LIBFILENAME) + 2);
	strcpy(l_name, lib_name);

#ifdef BSD
	strcat(l_name, "/");
#endif
#ifdef SYSTEM_V
	strcat(l_name, "/");
#endif
#ifdef IBM_PC
	strcat(l_name, "/");
#endif
	strcat(l_name, LIBFILENAME);

		if ((fp = open(l_name,O_RDONLY,0700)) < 0) {
		    fprintf(stderr,"%s cannot be used as a library\n", lib_name);
		    exit(RC_ABORT);
		}
	efree(l_name);
		close(fp);
	}

	/* format library option as expected by adafront & adagen */
	lib_opt_str = ((newlib_opt) ? "-nl" : "-l");

	FRONT = getsym("ADAFRONT", FRONT_NAME);
	other_opts[opts_cnt = 0] = FRONT;
	if (strlen(front_options) != 0) {
		other_opts[++opts_cnt] = "-s";
		other_opts[++opts_cnt] = front_options;
	}
	other_opts[++opts_cnt] = lib_opt_str;
	other_opts[++opts_cnt] = lib_name;
	other_opts[++opts_cnt] = source_name;
	other_opts[++opts_cnt] = (char *) 0;
	if (exec_trace)
		arg_dump();
	status = run_prog(FRONT, other_opts);
	if (exec_trace)
		fprintf(stderr, " ? %d\n", status);
	ok = check_status(status, "FRONT", arg_name);
		/* check for front end errors (adafront will exit with RC_ERRORS) */
	if (status_get(status)== RC_ERRORS)
		ok = FALSE;

	if (ok) {
		GEN = getsym("GEN", GEN_NAME);
		other_opts[opts_cnt = 0] = GEN;
		if (strlen(gen_options) != 0) {
			other_opts[++opts_cnt] = "-g";
			other_opts[++opts_cnt] = gen_options;
		}
		other_opts[++opts_cnt] = lib_opt_str;
		other_opts[++opts_cnt] = lib_name;
		other_opts[++opts_cnt] = base_name;
		other_opts[++opts_cnt] = (char *) 0;
		if (exec_trace)
			arg_dump();
		status =  run_prog(GEN, other_opts);
		if (exec_trace)
			fprintf(stderr, " ? %d\n", status);
		ok = check_status(status, "GEN", arg_name);
	}

	if (ok && bind_opt) { /* run binder if desired */
		BND = getsym("BND", BND_NAME);
		other_opts[opts_cnt = 0] = BND;
		other_opts[++opts_cnt] = "-c"; /* indicate errors in message form */
		other_opts[++opts_cnt] = base_name; /* pass filename for msg listing */

		while(interface_cnt) {
			other_opts[++opts_cnt] = "-i";
			other_opts[++opts_cnt] = interface_opts[--interface_cnt];
		}
		if (main_opt) {
			other_opts[++opts_cnt] = "-m";
			other_opts[++opts_cnt] = main_unit_name;
		}
		other_opts[++opts_cnt] = lib_name; /* library is current directory */
		other_opts[++opts_cnt] = (char *) 0;
		if (exec_trace)
			arg_dump();
		status =  run_prog(BND, other_opts);
		if (exec_trace)
			fprintf(stderr, " ? %d\n", status);
		ok = check_status(status, "BND", arg_name);
	}
#ifdef IBM_PC
	list_name = emalloc(strlen(base_name) + 4 + 1);
	strcpy(list_name, base_name);
	strcat(list_name, ".lis");
#endif
#ifdef SYSTEM_V
	list_name = emalloc(strlen(base_name) + 4 + 1);
	strcpy(list_name, base_name);
	strcat(list_name, ".lis");
#endif
#ifdef BSD
	list_name = emalloc(strlen(base_name) + 4 + 1);
	strcpy(list_name, base_name);
	strcat(list_name, ".lis");
#endif
	list_arg = (list_opt>0) ? "1" : "0";
	msg_name = emalloc(strlen(lib_name) + strlen(base_name) + 7);
	strcpy(msg_name, lib_name);
#ifdef BSD
	strcat(msg_name,"/");
#endif
#ifdef SYSTEM_V
	strcat(msg_name,"/");
#endif
#ifdef IBM_PC
	strcat(msg_name,"/");
#endif
	strcat(msg_name, base_name);
	strcat(msg_name, ".msg");
	status = mrg(source_name,msg_name, list_name, list_arg);
	efree(list_name);
	if (!save_msg_opt) {
		delete_file(msg_name);
	efree(msg_name);
	}

	exit(maxstatus);
}

static char *getsym(char *env_name, char *def_value)		/*;getsym*/
{
  /* Retrieve environment variable designating the executable module for
   * a given phase of the compiler.
   * If the variable is not defined, a default is supplied for BSD systems.
   */
	char   *s;

	s = getenv(env_name);
	if (s==(char *)0) {
		char *t = get_libdir();
		s = emalloc(strlen(t) + strlen(def_value) + 2);
		sprintf(s,"%s/%s", t, def_value);
	}
	return s;
}

static int check_status(int pstatus, char *phase, char *filename)
															/*;check_status*/
{

#ifdef BSD
	if (system_status_get(pstatus) == SIGXCPU) {
		fprintf(stderr, "Ada/Ed cpu time limit exceeded for %s\n",phase);
		return (FALSE);
	}
#endif

	/* check for internal compiler error and a signal (system transmitted)
	 * that is not IGNORE (1) or BAD_SIGNAL (-1)
	 * Check first for crash, since have no guarantee what will appear
	 * in 'user' section of return code (status_get field)
	 */
	if ( (status_get(pstatus)  == RC_INTERNAL_ERROR)
	  || (system_status_get(pstatus) > 1 && system_status_get(pstatus) < 255)) {
		maxstatus = RC_INTERNAL_ERROR;
		fprintf(stderr,"Ada/Ed Internal error(%s) for %s\n", phase, filename);
		return (FALSE);
	}
	if (status_get(pstatus)  == RC_SUCCESS) {
		return (TRUE);
	}
	if (status_get(pstatus) == RC_ERRORS){
		maxstatus = RC_ERRORS;
		return (TRUE);
	}
	if (status_get(pstatus)  == RC_ABORT) {
		maxstatus = RC_ABORT;
		return (FALSE);
	}
}

static void arg_dump()											/*;arg_dump*/
{
	/*list generated command*/
	int     i;
	fprintf(stderr, "%s ", other_opts[0]);
	for (i = 1; i < opts_cnt; i++) {
		fprintf(stderr, " %s", other_opts[i]);
	}
	fprintf(stderr,"\n");
}

static int run_prog(char *prog, char **args)					/*;run_prog*/
{
	int status;

#ifdef IBM_PC
	status = spawnv(P_WAIT, prog, args);
#else
	if (fork() == 0)
		if (execvp(prog , other_opts)) {
			fprintf(stderr,"cannot execute %s\n", prog);
			exit(RC_ABORT);
		}
	wait( WAITPARM &status);
#endif
	return status;
}

static void delete_file(char *file_name)					/* ;delete_file */
{
	int status;

	status = unlink(file_name);
	if (exec_trace)
		fprintf(stderr,"unlink %s ? %d\n",file_name, status);
}
