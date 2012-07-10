/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#include "hdr.h"
#include "vars.h"
#include "smiscprots.h"
#include "miscprots.h"
#include "setprots.h"
#include "errmsgprots.h"
#include "chapprots.h"

void except_decl(Node id_list_node)							/*;except_decl*/
{
	Node	id_node;
	Symbol	name;
	Fortup	ft1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  except_decl");

	FORTUP(id_node = (Node), N_LIST(id_list_node), ft1);
		name = find_new(N_VAL(id_node));
		N_UNQ(id_node) = name;
		NATURE(name) = na_exception;
		TYPE_OF(name) = symbol_exception;
	ENDFORTUP(ft1);
}

void exception_part(Node node)							/*;exception_part*/
{
	Symbol	handler;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  exception_part'");

	/* A scope is established for the exception handlers. This scope
	 * or a block nested within it, are the only valid scopes for the
	 * occurence of a non-specific RAISE statement.
	 */

	handler = find_new(newat_str());
	newscope(handler);
	/*SYMBTAB(handler) := [na_block, 'handler', []];*/
	NATURE(handler) = na_block;
	OVERLOADS(handler) = (Set) BLOCK_HANDLER;
	SIGNATURE(handler) = tup_new(0);

	/* Process individual handlers.*/
	sem_list(node);

	popscope();
}

void exception_handler(Node node)					/*;exception_handler*/
{
	Node	excp_list_node, statements_node, name_node;
	Tuple	exception_list;
	Symbol	except;
	Fortup	ft1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  exception_handler");

	excp_list_node = N_AST1(node);
	statements_node = N_AST2(node);
	exception_list = N_LIST(excp_list_node);
	FORTUP(name_node = (Node), exception_list, ft1);
		adasem(name_node);

		if (N_KIND(name_node) != as_others) {
			find_old(name_node);
			except = N_UNQ(name_node);
                        /* except is (Symbol)0 in the case that name_node is 
                         * a selector whose prefix is a parameterless function 
                         * This error condition is not caught by find_old
                         */
			if (except == (Symbol)0) {
			   	errmsg("Invalid exception name in handler", 
                                       "11.1", name_node);
                        }
                        else if (NATURE(except) != na_exception) {
				errmsg_id("% is not an exception", except, "11.1", name_node);
			}
			else if (tup_mem((char *) except, SIGNATURE(scope_name)) ) {
				errmsg("Duplicate exception name in handler", "11.2",name_node);
			}
			else {
				SIGNATURE(scope_name) = tup_with(SIGNATURE(scope_name),
			      (char *) except);
			}
		}
		else {
			/* The use of 'others' in SETL is just as a marker for local
			 * processing. Use the null symbol pointer in C version.
			 */
			if (tup_mem((char *)0, SIGNATURE(scope_name)) ) {
				errmsg("Duplicate OTHERS in exception part", "11.2", name_node);
			}
			else if (tup_size(exception_list) == 1)
				SIGNATURE(scope_name) = tup_with(SIGNATURE(scope_name),
				  (char *)0);
		}
	ENDFORTUP(ft1);

	adasem(statements_node);
}

void raise_statement(Node node)							/*;raise_statement*/
{
	Node	name_node;
	Symbol	scope, except;
	int	exists;
	Fortup	ft1;

	if (cdebug2 > 3) TO_ERRFILE("AT PROC :  raise_statement");

	name_node = N_AST1(node);

	if (name_node == OPT_NODE) {
		/* Non-specific raise. This statement form can appear only within
		 * an exception handler.
		 */
		exists = FALSE;

		FORTUP(scope = (Symbol), open_scopes, ft1);
			if(NATURE(scope) != na_block
			  || (int)OVERLOADS(scope) == BLOCK_HANDLER) {
				exists = TRUE;
				break;
			}
		ENDFORTUP(ft1);
		if (!exists) chaos("assert error in raise_statement");

		if ((int)OVERLOADS(scope) != BLOCK_HANDLER) {
			errmsg("RAISE statement not directly in exception handler", "11.3",
			  node);
		}
	}
	else {
		adasem(name_node);
		find_old(name_node);
		except = N_UNQ(name_node);
		if ( except == (Symbol)0
		  || NATURE(except) != na_exception && TYPE_OF(except) != symbol_any) {
			errmsg("Invalid exception name", "11.1", name_node);
		}
	}
}
