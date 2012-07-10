/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#include "hdr.h"
#include "vars.h"
#include "libhdr.h"
#include "dclmapprots.h"
#include "libprots.h"
#include "errmsgprots.h"
#include "miscprots.h"
#include "smiscprots.h"
#include "setprots.h"
#include "chapprots.h"

void process_pragma(Node node)								/*;process_pragma*/
{
	/* This arbitrarily extensible procedure  processes pragma declarations.
	 * The name  of the  pragma  determines the way	 in which the  args  are
	 * processed. If no meaning has been attached to a pragma name, the user
	 * is notified, and the pragma is ignored.
	 */

	Node	id_node, arg_list_node, arg_node, i_node, e_node, arg1, arg2;
	Node	priority, marker_node, type_node;
	char	*id;
	Tuple	args, arg_list;
	Symbol	proc_name, p_type, id_sym;
	int		nat, exists, newnat;
	Fortup	ft1;
	Forset	fs1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC : process_pragma(node) ");

	id_node = N_AST1(node);
	arg_list_node = N_AST2(node);
	id = N_VAL(id_node);
	arg_list = N_LIST(arg_list_node);
	/*aix := []; */ /* Most pragmas generate no code.*/
	if (is_empty(arg_list)) {	/* pragma with no parameters */
		errmsg_str("Format error in pragma", id, "Appendices B, F", node);
	}
	else {
		/* Process list of arguments. */
		args = tup_new(0);
		FORTUP(arg_node = (Node), arg_list, ft1);
			i_node = N_AST1(arg_node);
			e_node = N_AST2(arg_node);
			adasem(e_node);
			/* For now, disregard named associations.*/
			args = tup_with(args, (char *) e_node);
		ENDFORTUP(ft1);

		if (streq(id, "IO_INTERFACE") ) {
			/* Current interface to predefined procedures (e.g. text_io).
			 * The pragma makes up the body of a predefined procedure.
			 * This body is formatted into a single tuple :
			 *
			 *		[ io_subprogram, marker , name1, name2...]
			 *
			 * where the marker is the  second argument  of the  pragma. This
			 * marker is  used as an	 internal switch by the tio interpreter.
			 * The remaining components of  the tuple are the unique names of
			 * the formal parameters of the procedure.The pragma must follow
			 * immediately the procedure spec to which it applies. The pragma
			 * then supplies the body for it.
			 */
			arg1 = (Node) args[1];
			/* The first argument in the pragma list is a string in the case
			 * of overloadable operators used in the CALENDAR package.
			 */
			if (N_KIND(arg1) == as_string_literal)
				id = N_VAL(arg1);
			else
				id = N_VAL(N_AST1(arg1));
			/* assert exists proc_name in overloads(declared(scope_name)(id))
			 *  | rmatch(nature(proc_name), '_spec') /= om;
			 */
			exists = FALSE;
			FORSET(proc_name = (Symbol),
			  OVERLOADS(dcl_get(DECLARED(scope_name), id)), fs1);
				nat = NATURE(proc_name);
				if (nat == na_procedure_spec  || nat == na_function_spec
			      || nat == na_task_obj_spec || nat == na_generic_procedure_spec
			      || nat == na_generic_function_spec 
			      || nat == na_generic_package_spec) {
					exists = TRUE;
					break;
				}
			ENDFORSET(fs1);
			if (exists == FALSE)
				warning("subprogram given in pragma not found", node);
			if (nat == na_procedure_spec  ) newnat = na_procedure;
			else if (nat == na_function_spec) newnat = na_function;
			else warning("argument to pragma is not a subprogram", node);
			NATURE(proc_name) = newnat;
			marker_node = N_AST1((Node)args[2]);
			if (tup_size(args) == 3 ) {
				type_node = (Node)args[3];
				find_old(type_node);
			}
			else
				type_node = OPT_NODE;
			N_KIND(node) = as_predef;
			N_UNQ(node) = proc_name;
			/* marker_node is an as_line_no node which carries the numerical 
			 * predef code corresponding to the entry in the pragma 
	 		 * IO_INTERFACE. as_line_no was used to simpify having the predef 
			 * code converted into a number by the parser and relayed here 
			 * as an integer.
			 */
			N_VAL(node) = N_VAL(marker_node);
			N_TYPE(node) = (type_node == OPT_NODE)? OPT_NAME : N_UNQ(type_node);
		}
		else if (streq(id, "INTERFACE") ) {
			/* Current interface to C and FORTRAN 
			 * The pragma makes up the body of a procedure.
			 * This body is formatted into a single tuple :
			 *
			 *		[language, name]
			 *
			 * where language is C or FORTRAN and name is the identifier 
			 * of the subprogram to be interfaced.
			 * This pragma is allowed at the place of a declarative item of
			 * the same declarative part or package specification. The pragma 
			 * is also allowed for a library unit; in this case, the pragma must
			 * appear after the subprogram decl, and before any subsequent
			 * compilation unit. 
			 */
			arg1 = (Node) args[1];
			/* The 1st arg in the pragma list is an identifier (C or FORTRAN) */
			if (N_KIND(arg1) != as_name) {
				warning("invalid format for pragma", node);
				return;
			}
			id = N_VAL(N_AST1(arg1));
			if (!streq(id, "C") && !streq(id, "FORTRAN")) {
				warning("invalid first argument for pragma", node);
				return;
			}

			arg2 = (Node) args[2];
			/* The 2nd argument in the pragma list is a subprogram identifier */
			if (N_KIND(arg2) != as_name) {
				warning("invalid format for pragma", node);
				return;
			}
			id = N_VAL(N_AST1(arg2));
			/* assert exists proc_name in overloads(declared(scope_name)(id))
			 *  | rmatch(nature(proc_name), '_spec') /= om;
			 */
			exists = FALSE;
			id_sym = dcl_get(DECLARED(scope_name), id);
			if (id_sym == (Symbol)0) {
				if (NATURE(scope_name)== na_private_part)
					/* check parent scope, which is scope of visible part */
					id_sym = dcl_get(DECLARED((Symbol)open_scopes[2]), id);
				if (id_sym == (Symbol)0) {
					warning("subprogram given in pragma not found", node);
					return;
				}
			}
			FORSET(proc_name = (Symbol), OVERLOADS(id_sym), fs1);
				nat = NATURE(proc_name);
				if (nat == na_procedure_spec) {
					newnat = na_procedure;
					exists = TRUE;
				}
				else if (nat == na_function_spec) {
					newnat = na_function;
					exists = TRUE;
				}
			ENDFORSET(fs1);
			if (!exists) {
				warning("invalid second argument to pragma", node);
				return;
			}

			NATURE(proc_name) = newnat;
			N_KIND(node) = as_interfaced;
			N_UNQ(node) = proc_name;
			N_AST1(node) = N_AST1(arg1);
		}

		else if (streq(id, "PRIORITY")) {
			Unitdecl ud;
			if (tup_size(args) == 1) {
				ud = unit_decl_get("spSYSTEM");
				if (ud == (Unitdecl)0 || !in_vis_mods(ud->ud_unam) ) {
					warning(
	  "use of PRIORITY without presence of package SYSTEM is ignored",
					  (Node)args[1]);
					N_KIND(node) = as_opt;
					N_AST1(node) = N_AST2(node) = N_AST3(node) = N_AST4(node)
					  = (Node)0;
					return;
				}
				else {
					p_type = dcl_get_vis(DECLARED(ud->ud_unam), "PRIORITY");
				}
				priority = (Node) args[1];
				check_type(p_type, priority);
				if (!is_static_expr(priority))
					warning("Priority must be static", priority);
			}
			else
				warning("Invalid format for pragma priority", node);
		}
		else if (streq(id, "CONTROLLED")
		  || streq(id, "INCLUDE")
		  || streq(id, "INLINE")
		  || streq(id, "LIST")
		  || streq(id, "MEMORY_SIZE")
		  || streq(id, "OPTIMIZE")
		  || streq(id, "PACK")
		  || streq(id, "STORAGE_UNIT")
		  || streq(id, "SUPRESS")
		  || streq(id, "SYSTEM") ) {
			warning("unsupported pragma", id_node);
		}
		else
			warning("unrecognized pragma", node);
	}
}
