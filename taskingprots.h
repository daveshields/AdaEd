/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

void initialize_tasking();
void start_creation(int, int);
void start_activation(int, int, int);
int union_tasks_declared(int list1, int list2);
void end_activation(int);
void abort(int);
void complete_task();
void complete_block();
void terminate_unactivated();
void purge_rdv(int);
void delay_stmt(long);
void clock_interrupt(long);
void selective_wait(int);
void end_rendezvous();
void entry_call(long, int);
void raise_in_caller();
int is_callable(int);
int is_terminated(int);
int count(int, int);
void round_robin();
