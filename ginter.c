/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* ginter.c: generate interface code */
#define GEN

#include "hdr.h"
#include "libhdr.h"
#include "vars.h"
#include "segment.h"
#include "gvars.h"
#include "ops.h"
#include "type.h"
#include "ifile.h"
#include "setprots.h"
#include "libprots.h"
#include "miscprots.h"
#include "bmainprots.h"
#include "ginterprots.h"

void geninter(Tuple to_bind)									/*;geninter*/
{
#ifdef SUPPORT_PRAGMA_INTERFACE
	char *INT_DIR;	/* directory containing partially bound interpreter */
	char *INT_FILE;	/* filename representing partially bound interpreter */
	char *PROC_INTERFACE; /* temporary file containing procedure interface() */
	extern char *LIBRARY_PREFIX; /* user library, defined in misc.c */
	char *argp[80];
#endif
	char *code;
	char dummy_array[80];
	int  i, j, n, m, status;
	FILE *file;
	char *token, *ptr, *s;
	char *exec_name;
#ifdef IBM_PC
	FILE *efopen();
#endif

	/* generation of the procedure interface whith the branches of the case
     * which have been stored in the tuple interfaced_procedures*/
	code = "interface(procedure)\nint procedure;\n{\n";
	code = strjoin(code, "extern float get_float_argument_value();\n");
	code = strjoin(code,
	  "extern int cur_stackptr, *cur_stack;\n switch(procedure){\n");
	n = tup_size(interfaced_procedures);
	m = tup_size(to_bind);
	for (i = 1; i <= n; i+=2) {
		for (j = 1; j <= m; j++) {
			if((int)interfaced_procedures[i] == unit_numbered(to_bind[j])) {
				code = strjoin(code, interfaced_procedures[i+1]);
				break;
			}
		}
	}
	sprintf(dummy_array,
	  "\tdefault: raise(%d, \"Interface\");\n}\n}\n", 6);
	code = strjoin(code, dummy_array);
#ifdef SUPPORT_PRAGMA_INTERFACE
	file = efopenl("interface.c", "", "w", "t");
#endif
#ifdef IBM_PC
	file = efopen("iface.c", "w", "t");
#endif
	fprintf(file, code);
	fclose(file);

#ifdef SUPPORT_PRAGMA_INTERFACE
	PROC_INTERFACE = strjoin(LIBRARY_PREFIX, DIR_DELIMITER);
	PROC_INTERFACE = strjoin(PROC_INTERFACE, "interface.c");

	/* construction of the array argp which is a parameter of execvp */
	argp[0] = "cc";
	argp[1] = PROC_INTERFACE;

	INT_DIR = getenv("INT");
	if (INT_DIR == (char *) 0) {
		user_error("environment variable  INT not set");
		return;
	}
	INT_FILE = strjoin(INT_DIR, "/adaint");
	argp[2] = INT_FILE;

	ptr = interface_files;
	i = 3;
	/* the string interface_files consists of a succession of tokens 
	 * followed by one blank. We break this string into tokens and we check 
	 * whether these tokens contain an 'o' extension or not 
	 */
	while (*ptr != '\0') {
		token = ptr;
		while (*ptr != ' ') ptr++;
		*ptr++ = '\0';
		if (strchr(token, '.') == (char *)0) {
			token = strjoin("-l", token);
			argp[i++] = token;
		}
		else {
			s = strchr(token, '.');
			if ((*(s + 1) == 'o') && (*(s + 2) == '\0')) {
				argp[i++] = token;
			}
			else {
				sprintf(dummy_array, "%s not an object file",token);
				user_error(dummy_array);
				return;
			}
		}
	}

	argp[i++] = "-lm";

	exec_name = strjoin(LIBRARY_PREFIX, DIR_DELIMITER);
	exec_name = strjoin(exec_name, AISFILENAME);
	exec_name = strjoin(exec_name, ".exe");
	argp[i++] = "-o";
	argp[i++] = exec_name;

	argp[i] = (char *) 0;

	if (fork() == 0) {
		exit(execvp("gcc", argp));
	}
	else {
		wait(&status);
		unlink(PROC_INTERFACE);
		unlink("interface.o");
	}
#endif
}
