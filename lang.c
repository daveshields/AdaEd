/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#define GEN

#include "hdr.h"
#include "libhdr.h"
#include "vars.h"
#include "gvars.h"
#include "attr.h"
#include "setprots.h"
#include "gutilprots.h"
#include "miscprots.h"
#include "gmiscprots.h"
#include "gmainprots.h"
#include "langprots.h"

char *c_interface(Symbol sym, int func_code)				/*;c_interface*/
{
	/* generation of a branch of a switch in C containing a call to a
	 * subprogram interfaced to C
	 */

	char    dummy_array[80];
	char 	*decl_code = "";
	char 	*call_code;
	char 	*code;
	char    *proc_name;
	Symbol	formal, formal_type, return_type;
	Tuple	formals;
	Fortup	ft1;
	int     indx;
	int 	position = 0;

	sprintf(dummy_array, "\tcase(%d):{\n", func_code);
	code = strjoin(dummy_array, "");
	proc_name = strjoin(ORIG_NAME(sym), "");
	fold_lower(proc_name);
	if (NATURE(sym) == na_function) {
		return_type = TYPE_OF(sym);
		if (is_integer_type(return_type))
			sprintf(dummy_array, "\t\textern int %s();\n", proc_name);
		else if (is_float_type(return_type))
			sprintf(dummy_array, "\t\textern float %s();\n", proc_name);
		else
			compiler_error("Interface: TBSL return_type");
		decl_code = strjoin("", dummy_array);
	}
	if (NATURE(sym) == na_function)
		sprintf(dummy_array, "%s(", proc_name);
	else
		sprintf(dummy_array, "\t\t%s(", proc_name);
	call_code = strjoin(dummy_array, "");
	formals = tup_copy(SIGNATURE(sym));

	FORTUPI(formal = (Symbol), formals, indx, ft1);
		formal_type = TYPE_OF(formal);
		if (is_integer_type(formal_type) || is_enumeration_type(formal_type))
			sprintf(dummy_array, "\n\t\t\t\t\tget_argument_value(%d)",position);
		else if (is_float_type(formal_type))
			sprintf(dummy_array, "\n\t\t\t\t\tget_float_argument_value(%d)",
		      position);
		else if (is_access_type(formal_type))
			sprintf(dummy_array, "\n\t\t\t\t\tget_long_argument_value(%d)",
		      position);
		else if (is_array_type(formal_type) || is_record_type(formal_type)) {
			position+=2;
			sprintf(dummy_array, "\n\t\t\t\t\tget_argument_ptr(%d)", position);
		}
		else
			compiler_error("Interface: TBSL non scalar types");
		call_code = strjoin(call_code, dummy_array);
		if (indx != tup_size(formals))
			call_code = strjoin(call_code, ",");
		position += 2;
	ENDFORTUP(ft1);

	if (NATURE(sym) == na_function) {
		if (is_integer_type(return_type)) {
			sprintf(dummy_array, "\t\tcur_stack[cur_stackptr - %d] = ",
			  position);
		}
		else {
			sprintf(dummy_array,
			  "\t\t((float *)cur_stack)[cur_stackptr - %d] = ", position);
		}
		call_code = strjoin(dummy_array, call_code);
	}
	call_code = strjoin(call_code, ");\n\t\tbreak;\n\t}\n");
	code = strjoin(code, decl_code);
	code = strjoin(code, call_code);
	tup_free(formals);
	return code;
}

char *fortran_interface(Symbol sym, int func_code)		/*;fortran_interface*/
{
	/* generation of a branch of a switch in C containing a call to a
	 * subprogram interfaced to FORTRAN
	 */

	char    dummy_array[80];
	char 	*decl_code = "";
	char 	*call_code;
	char 	*code;
	char    *proc_name;
	Symbol	formal, formal_type, return_type;
	Tuple	formals;
	Fortup	ft1;
	int     indx;
	int 	position = 0;

	sprintf(dummy_array, "\tcase(%d):{\n", func_code);
	code = strjoin(dummy_array, "");
	proc_name = strjoin(ORIG_NAME(sym), "");
	fold_lower(proc_name);
	if (NATURE(sym) == na_function) {
		return_type = TYPE_OF(sym);
		if (is_integer_type(return_type)||is_float_type(return_type)) {
			sprintf(dummy_array, "\t\textern int %s();\n", proc_name);
		}
		else {
			compiler_error("Interface: TBSL return_type");
		}
		decl_code = strjoin("", dummy_array);
	}
	if (NATURE(sym) == na_function) {
		sprintf(dummy_array, "%s_(", proc_name);
	}
	else {
		sprintf(dummy_array, "\t\t%s_(", proc_name);
	}
	call_code = strjoin(dummy_array, "");
	formals = tup_copy(SIGNATURE(sym));

	FORTUPI(formal = (Symbol), formals, indx, ft1);
		formal_type = TYPE_OF(formal);
		if (is_integer_type(formal_type) || is_float_type(formal_type)
		  || is_array_type(formal_type) || is_record_type(formal_type)) {
			if (is_array_type(formal_type) || is_record_type(formal_type)) {
				position+=2;
			}
			if (indx == tup_size(formals)) {
				sprintf(dummy_array, "\n\t\t\t\t\tget_argument_ptr(%d)",
			      position);
			}
			else {
				sprintf(dummy_array, "\n\t\t\t\t\tget_argument_ptr(%d),",
			      position);
			}
		}
		else {
			compiler_error("Interface: unimplemented type for FORTRAN");
		}
		call_code = strjoin(call_code, dummy_array);
		position += 2;
	ENDFORTUP(ft1);

	if (NATURE(sym) == na_function) {
		sprintf(dummy_array, "\t\tcur_stack[cur_stackptr - %d] = ", position);
		call_code = strjoin(dummy_array, call_code);
	}
	call_code = strjoin(call_code, ");\n\t\tbreak;\n\t}\n");
	code = strjoin(code, decl_code);
	code = strjoin(code, call_code);
	tup_free(formals);
	return code;
}
