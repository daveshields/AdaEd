/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#ifndef __slot_h
#define __slot_h

typedef struct Slot_s {
	int	slot_seq;		/* sequence of symbol */
	int	slot_unit;		/* unit of symbol */
	int	slot_number;		/* slot number */
	char	*slot_name;		/* name */
    } Slot_s;

typedef struct Slot_s *Slot;

/* structure returned by read_axq */
typedef struct Axq_s {

    int		axq_cunits;	 	/* number of units */
    int		axq_code_segments_dim; 	/* dimension of code_segments */
    char 	**axq_code_segments; 	/* code segments text */
    int		*axq_code_seglen;   	/* code segments length */
    int		axq_data_segments_dim; 	/* dimension of data_segments */
    int		**axq_data_segments; 	/* data segments text */
    int		*axq_data_seglen; 	/* data segments length */
    int		axq_code_slots_dim; 	/* dimension of code_slots */
    Slot	 *axq_code_slots;	/* code slots */
    int		axq_data_slots_dim;	/* dimension of data_slots */ 
    Slot 	*axq_data_slots;	/* data slots */
    int		axq_exception_slots_dim;/* dimension of exception slots */
    Slot 	*axq_exception_slots;	/* exception slots */
     } Axq_s;

typedef struct Axq_s *Axq;
#endif
