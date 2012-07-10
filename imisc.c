/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */
#include "ipredef.h"
#include "time.h"
#include "imiscprots.h"

/* Procedures reset_clock and itime are used to maintain the 'clock'.
 * reset_now resets the clock, itime returns the number of milliseconds
 * since the clock was reset. Code is include to make it appear as though
 * the clock was reset at the most recent midnight, in order that the
 * addition of TIME and DURATION values can account for the
 * overflow that occurs at midnight.
 */

static long since_midnight;    /* milliseconds since midnight at start */
static long start_time;	/* starting time (units vary according to version) */

/* set TIME_KIND to determine which itime and reset_clock to use */

#define TIME_DEFAULT

#ifdef BSD
#undef TIME_DEFAULT
#define TIME_BSD
/* start_time is in seconds for BSD */
#include <sys/time.h>
static int tzpa[2];
static long tpa[2];
#endif

#ifdef IBM_PC
#undef TIME_DEFAULT
#define TIME_PC
/* start_time is in 'ticks' elapsed since midnight, where there are 
 * CLK_TCK ticks per second.
 * To avoid overflow, we use ms_per_tick, milliseconds per tick. This
 * assumes (as is currently the case) that CLK_TCK divides 1000
 * evenly.
 */
#define ms_per_tick (1000 / CLK_TCK)
#endif


void reset_clock()						                    /*;reset_clock*/
{
	/* set start_time and since_midnight as described above. */
#ifdef TIME_BSD
	struct tm *t;
	struct timeval *tp;

	tp = (struct timeval *)tpa;
	gettimeofday(tp, (struct timezone *)tzpa);
	start_time = tp->tv_sec;
	t = localtime(&tp->tv_sec); /* break into hours, minutes, etc. */
	since_midnight = (t->tm_hour * 3600 + t->tm_min * 60 + t->tm_sec)
	  * 1000L; /* milliseconds since midnight */
#endif
#ifdef TIME_PC
	start_time = clock() * ms_per_tick; /* milliseconds since midnight */
	since_midnight = start_time;
#endif
#ifdef TIME_DEFAULT
#ifdef TBSN
	/* adjustment for midnight still needed */
	chaos("reset_clock for  TIME_DEFAULT not implemented");
#endif
	start_time = time(0);
#endif
}

long itime()	                         /*;itime*/
{
	/* find elapsed seconds, convert to milliseconds, and add offset 
     *  for midnight corresponding to desired origin
     */
	long  itim;
#ifdef TIME_DEFAULT
#ifdef TBSN
	chaos("itime for TIME_DEFAULT not implemented");
#endif
	return (time(0) - start_time) * 1000;
#endif

#ifdef TIME_BSD
	struct timeval *tp;
#endif
#ifdef TIME_PC
	clock_t time_now;
#endif
#ifdef TIME_BSD
	tp = (struct timeval *)tpa;
	gettimeofday(tp, (struct timezone *)tzpa);
	itim = ((tp->tv_sec - start_time)*1000L + tp->tv_usec/1000L);
#endif
#ifdef TIME_PC
	time_now = clock() * (long) ms_per_tick;
	/* adjust for passing midnight if necessary */
	if (time_now < start_time) time_now = time_now + 86400000L ;
	itim =   (long) (time_now - start_time);
#endif
	return itim + since_midnight;
}
