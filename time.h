/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/* include <time.h> header file, accounting for BSD silliness */
/* file config.h must be included before this one to set BSD properly */
#ifndef _time_h
#define _time_h
#ifdef BSD
#include <sys/time.h>
#else
#include <time.h>
#endif
#endif
