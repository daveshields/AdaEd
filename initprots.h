/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

void initialize_1();
void initialize_2();
int max_index(int);
Slot slot_new(Symbol, int);
void remove_slots(Tuple, int);
void remove_interface(Tuple tup, int);
void private_exchange(Symbol);
void private_install(Symbol);
int init_slots(int);
