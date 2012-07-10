/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
/*    +---------------------------------------------------+
      |                                                   |
      |          I N T E R P     P R E D E F S            |
      |            Part 2: CALENDAR Procedure             |
      |                  (C Version)                      |
      |                                                   |
      |   Adapted From Low Level SETL version written by  |
      |                                                   |
      |                  Monte Zweben                     |
      |               Philippe Kruchten                   |
      |               Jean-Pierre Rosen                   |
      |                                                   |
      |    Original High Level SETL version written by    |
      |                                                   |
      |                   Clint Goss                      |
      |               Tracey M. Siesser                   |
      |               Bernard D. Banner                   |
      |               Stephen C. Bryant                   |
      |                  Gerry Fisher                     |
      |                                                   |
      |              C version written by                 |
      |                                                   |
      |               Robert B. K. Dewar                  |
      |                                                   |
      +---------------------------------------------------+
*/

/* This module contains the implementation of the CALENDAR package */

#include "ipredef.h"
#include "time.h"
#include "intbprots.h"
#include "intcprots.h"
#include "predefprots.h"

/* Structure corresponding to Ada record TIME */

struct time_record {
	int     year_val;
	int     month_val;
	int     day_val;
	long    secs_val;
};

static long days_in(int, int, int);
static void ymd_of(long days, int *, int *, int *);
static void get_time(struct time_record *);

/*  Macros for treating pointer as pointer to time_record, and length in
 *  words of time record(used when creating an object of this type.
 */

#define TIME_RECORD(ptr)    ((struct time_record *)(ptr))
#define WORDS_TIME_RECORD   (sizeof(struct time_record) / sizeof (int))

/*  Constants for CALENDAR */

#define ONE_DAY   86400000L       /* 24 * 60 * 60 * 1000 (milliseconds) */

static int days_before_month[] = {
	0, 0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334
};

static int days_in_month[] = {
	0, 31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31
};


/* CALENDAR */

/* Control passes to the CALENDAR procedure from PREDEF when it encounters an
 * operation code value corresponding to a predefined calendar operation.
*/

void calendar()					                              /*;calendar*/
{
	switch(operation) {

		/* function CLOCK return TIME; */

	case P_CLOCK:
		{
			int    bse, off;
			int    *ptr;

			create(WORDS_TIME_RECORD, &bse, &off, &ptr);
			get_time((struct time_record  *) ptr);
			TOSM(1) = bse;
			TOS = off;
			break;
		}


		/* function YEAR(DATE : in TIME) return YEAR_NUMBER; */

	case P_YEAR:
		TOSM(2) = TIME_RECORD(get_argument_ptr(0)) -> year_val;
		break;

		/* function MONTH(DATE : in TIME) return MONTH_NUMBER; */

	case P_MONTH:
		TOSM(2) = TIME_RECORD(get_argument_ptr(0)) -> month_val;
		break;

		/* function DAY(DATE : in TIME) return DAY_NUMBER; */

	case P_DAY:
		TOSM(2) = TIME_RECORD(get_argument_ptr(0)) -> day_val;
		break;

		/* function SECONDS(DATE : in TIME) return DURATION; */

	case P_SECONDS:
		{
			int  bse,off;
			long secs,tmp;

			/*TOSM(2) = TIME_RECORD(get_argument_ptr(0)) -> secs_val;*/
			/* direct code needed since TOSML macro wrong */
			/* pop arguments, store long and restore args */
			secs = TIME_RECORD(get_argument_ptr(0)) -> secs_val;
			POP_ADDR(bse,off);
			POPL(tmp); /* pop current value */
			PUSHL(secs); /* push correct value */
			PUSH_ADDR(bse,off); /* restore arg on stack */
		}
		break;

		/* procedure SPLIT(DATE      : in  TIME;          */
		/*                 YEAR      : out YEAR_NUMBER;   */
		/*                 MONTH     : out MONTH_NUMBER;  */
		/*                 DAY       : out DAY_NUMBER;    */
		/*                 SECONDS   : out DURATION);     */

	case P_SPLIT:
		{
			struct time_record *time_ptr;
			long *p;

			time_ptr = TIME_RECORD(get_argument_ptr(0));

			*get_argument_ptr(2)  = time_ptr -> year_val;
			*get_argument_ptr(6)  = time_ptr -> month_val;
			*get_argument_ptr(10) = time_ptr -> day_val;
			p = (long *) get_argument_ptr(14) ;
			*p = time_ptr -> secs_val;
			break;
		}

		/* function TIME_OF(YEAR     : YEAR_NUMBER;                   */
		/*                  MONTH    : MONTH_NUMBER;                  */
		/*                  DAY      : DAY_NUMBER;                    */
		/*                  SECONDS  : DURATION := 0.0) return TIME;  */

	case P_TIME_OF:
		{
			int    year, month, day;
			long   secs;
			long   days;
			int    bse, off;
			struct time_record *time_ptr;

			year  = get_argument_value(0);
			month = get_argument_value(2);
			day   = get_argument_value(4);
			secs  = get_long_argument_value(6);

			if ((year % 4) == 0 && month == 2) {
				if (day > 29) { /* check leap year */
					raise(TIME_ERROR, "Day too large");
					return;
				}
			}
			else if (day > days_in_month[month]) {
				raise(TIME_ERROR, "Day too large");
				return;
			}
			if (secs >= ONE_DAY) {
				secs -= ONE_DAY;
				days = days_in(year, month, day + 1);
				ymd_of(days, &year, &month, &day);
				if (year < 1901 || year > 2099) {
					raise(TIME_ERROR, "Year out of range");
					return;
				}
			}
			create(WORDS_TIME_RECORD, &bse, &off,(int **)(&time_ptr));
			time_ptr -> year_val  = year;
			time_ptr -> month_val = month;
			time_ptr -> day_val   = day;
			time_ptr -> secs_val  = secs;
			TOSM(9) = bse;
			TOSM(8) = off;
			break;
		}

		/* function "+"(LEFT : TIME;     RIGHT : DURATION)  return TIME; */
		/* function "+"(LEFT : DURATION; RIGHT : TIME)      return TIME; */
		/* function "-"(LEFT : TIME;     RIGHT : DURATION)  return TIME; */

	case P_ADD_TIME_DUR:
	case P_ADD_DUR_TIME:
	case P_SUB_TIME_DUR:
		{
			struct time_record *time_ptr;
			long   dur;
			int    year, month, day;
			long   secs,days;
			int    add_day;
			int    bse, off;

			if (operation == P_ADD_TIME_DUR) {
				time_ptr = TIME_RECORD(get_argument_ptr(0));
				dur = get_long_argument_value(2);
			}
			else if (operation == P_ADD_DUR_TIME) {
				dur = get_long_argument_value(0);
				time_ptr = TIME_RECORD(get_argument_ptr(2));
			}
			else { /* operation == P_SUB_TIME_DUR */
				time_ptr = TIME_RECORD(get_argument_ptr(0));
				dur = - get_long_argument_value(2);
			}

			year  = time_ptr -> year_val;
			month = time_ptr -> month_val;
			day   = time_ptr -> day_val;
			secs  = time_ptr -> secs_val;

			secs += dur;
			add_day = (int)(secs / ONE_DAY);
			secs -= add_day * ONE_DAY;
			if (secs < 0) {
				secs += ONE_DAY;
				add_day--;
			}

			day += add_day;

			days = days_in(year, month, day);
			if (days <= 0) {
				raise(TIME_ERROR, "Year out of range");
				return;
			}
			ymd_of(days, &year, &month, &day);
			if (year < 1901 || year > 2099) {
				raise(TIME_ERROR, "Year out of range");
				return;
			}
			create(WORDS_TIME_RECORD, &bse, &off,(int **)(&time_ptr));
			time_ptr -> year_val  = year;
			time_ptr -> month_val = month;
			time_ptr -> day_val   = day;
			time_ptr -> secs_val  = secs;

			TOSM(5) = bse;
			TOSM(4) = off;
			break;
		}

		/* function "-"(LEFT : TIME; RIGHT : TIME) return DURATION; */

	case P_SUB_TIME_TIME:
		{
			int    *dur_tt_ptr;
			int    *left_ptr;
			int    *right_ptr;
			int    y1, m1, d1;
			int    y2, m2, d2;
			long   s1, s2, secs, days;
			long   dur;
			struct time_record *time_ptr;
			int    bse, off, bse1, off1;

			POP_PTR(dur_tt_ptr);               /* type must be popped */

			left_ptr  = get_argument_ptr(0);
			right_ptr = get_argument_ptr(2);

			time_ptr = TIME_RECORD(left_ptr);
			y1 = time_ptr -> year_val;
			m1 = time_ptr -> month_val;
			d1 = time_ptr -> day_val;
			s1 = time_ptr -> secs_val;

			time_ptr = TIME_RECORD(right_ptr);
			y2 = time_ptr -> year_val;
			m2 = time_ptr -> month_val;
			d2 = time_ptr -> day_val;
			s2 = time_ptr -> secs_val;

			days = days_in(y1, m1, d1) - days_in(y2, m2, d2);
			secs = s1 - s2;
			dur = ONE_DAY * days + secs;

			if (fix_out_of_bounds(dur, (int *)FX_RANGE(dur_tt_ptr)))
				raise(TIME_ERROR, "Out of range");
			else {
				/* direct code needed since TOSML macro wrong */
				/* pop arguments, store long and restore args */
				POP_ADDR(bse,off);
				POP_ADDR(bse1,off1);
				POPL(secs); /* pop current value */
				PUSHL(dur); /* push correct value */
				PUSH_ADDR(bse1,off1); /* restore args on stack */
				PUSH_ADDR(bse,off);
			}
			break;
		}

		/* function "<"  (LEFT, RIGHT : TIME) return BOOLEAN; */
		/* function "<=" (LEFT, RIGHT : TIME) return BOOLEAN; */
		/* function ">"  (LEFT, RIGHT : TIME) return BOOLEAN; */
		/* function ">=" (LEFT, RIGHT : TIME) return BOOLEAN; */

	case P_LT_TIME:
	case P_LE_TIME:
	case P_GT_TIME:
	case P_GE_TIME:
		{
			int    *left_ptr;
			int    *right_ptr;
			int    y1, m1, d1;
			int    y2, m2, d2;
			long   s1, s2;
			long   dur1, dur2;
			long   days1, days2;
			struct time_record *time_ptr;
			int    result;

			left_ptr  = get_argument_ptr(0);
			right_ptr = get_argument_ptr(2);

			time_ptr = TIME_RECORD(left_ptr);
			y1 = time_ptr -> year_val;
			m1 = time_ptr -> month_val;
			d1 = time_ptr -> day_val;
			s1 = time_ptr -> secs_val;

			time_ptr = TIME_RECORD(right_ptr);
			y2 = time_ptr -> year_val;
			m2 = time_ptr -> month_val;
			d2 = time_ptr -> day_val;
			s2 = time_ptr -> secs_val;

			days1 = days_in(y1, m1, d1);
			days2 = days_in(y2, m2, d2);
			if (days1 == days2) {
				dur1 = s1;
				dur2 = s2;
			}
			else {
				dur1 = days1;
				dur2 = days2;
			}

			if (operation == P_LT_TIME)
				result = dur1 < dur2;
			else if (operation == P_LE_TIME)
				result = dur1 <= dur2;
			else if (operation == P_GT_TIME)
				result = dur1 > dur2;
			else /*(operation == P_GE_TIME) */
				result = dur1 >= dur2;

			TOSM(4) = result;
			break;
		}
	}
}


/* DAYS_IN */

/* Given integer arguments(such as 1981, 2, 28), days_in computes the
 * number of days since January 1st, 1901. Since Ada does not allow dates
 * before 1901 or after 2099, we do not need to consider leap centuries.
*/

static long days_in(int y, int m, int d)		                /*;days_in*/
{
	return
	    (y - 1901) * 365L +(y - 1901) / 4 +
	    days_before_month[m] +((y % 4) ? 0 :(m > 2)) + d;
}


/* YMD_OF */

/* Given an integer which is the number of days since January 1st, 1901
 * this function returns the corresponding date in year/month/day form
*/

static void ymd_of(long days, int *y, int *m, int *d)              /*;ymf_of*/
{
	*y = 1901 +(int)((days * 4 - 1) / 1461);/*(4 * 365 + 1) */
	*d = (int)(days -((*y - 1901) * 365 +(*y - 1901) / 4));
	if (!(*y % 4)) {
		if (*d == 60) {
			*d = 29;
			*m = 2;
			return;
		}
		else if (*d > 60)
			*d -= 1;
	}
	*m = 1;
	while(*d > days_in_month[*m])
		*d -= days_in_month[(*m)++];
}

/* GET_TIME */

/* Get date and time. The format of the result is:
 *
 *      struct time_record = {
 *         int year_val;
 *         int month_val;
 *         int day_val;
 *         long secs_val;
 *      };
*/

static void get_time(struct time_record *time_ptr)                /*;get_time*/
{
	long    itime();
#ifndef IBM_PC
	long clock;
#else
	/* IBM_PC (Metaware) */
	time_t clock;
#endif
	struct tm *t;
#ifndef IBM_PC
	clock = time(0);
#else
	time(&clock);
#endif
	t = localtime(&clock);
#ifdef IBM_PC
	/* needed until Metaware fixes bug in tm_year field (ds 6-19-86) */
	time_ptr -> year_val = t -> tm_year;
#else
	time_ptr -> year_val = 1900 + t -> tm_year;
#endif
	time_ptr -> month_val = t -> tm_mon + 1;
	time_ptr -> day_val = t -> tm_mday;
	time_ptr -> secs_val = itime() % ONE_DAY;
	if (instruction_trace) {
		printf("get_time year %d month %d day %d secs %ld secs_chk %ld\n",
		  time_ptr -> year_val, time_ptr -> month_val,
		  time_ptr -> day_val, time_ptr -> secs_val, 
		  ((long)t->tm_hour*3600 + (long) t->tm_min * 60 
		  + (long) t->tm_sec)*1000L);
	}
	return;
}
