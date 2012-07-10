/*
 * Copyright (C) 1985-1992  New York University
 * 
 * This file is part of the Ada/Ed-C system.  See the Ada/Ed README file for
 * warranty (none) and distribution info and also the GNU General Public
 * License for more details.

 */

#ifndef _ifile_h
#define _ifile_h

/* An IFILE is a FILE with a header block at the front consisting of
 * the following as defined in the struct fh.
 */
struct fh {
	char	fh_mode;        /* mode: 'r' or 'w' */
    long	fh_slots;	/* offset from start of slots info */
    long	fh_units_end;   /* offset from start of end of units info */
    FILE	*fh_file;	/* associated file when open */
};

#define IFILE struct fh 

#ifdef EXPORT
long export_ifseek();
#define ifseek(ifile,desc,offset,ptr)	export_ifseek(ifile,offset,ptr)
#endif

#ifdef EXPORT
#define putnum(ofile,desc,n)		export_put_num(ofile,n)
#define putpos(ofile,desc,n)		export_put_pos(ofile,n)
#define putstr(ofile,desc,s)		export_put_str(ofile,s)
#define putchr(ofile,desc,n)		export_put_chr(ofile,n)
#define putnod(ofile,desc,node)		export_put_nod(ofile,node)
#define putnodref(ofile,desc,node)	export_put_nodref(ofile,node)
#define putint(ofile,desc,n)		export_put_int(ofile,n)	
#define putlong(ofile,desc,n)		export_put_long(ofile,n)
#define putunt(ofile,desc,n)		export_put_unt(ofile,n)
#define putuint(ofile,desc,uint)	export_put_uint(ofile,uint)
#define putsym(ofile,desc,sym)		export_put_sym(ofile,sym)
#define putsymref(ofile,desc,sym)	export_put_symref(ofile,sym)
#define getint(ifile,desc)		export_get_int(ifile)
#define getnum(ifile,desc)		export_get_num(ifile)
#define getchr(ifile,desc)		export_get_chr(ifile)
#define getlong(ifile,desc)		export_get_long(ifile)
#define getstr(ifile,desc)		export_get_str(ifile)
#define getnod(ifile,desc,node,unum)	export_get_nod(ifile,node,unum)
#define getnodref(ifile,desc)		export_get_nodref(ifile)
#define getuint(ifile,desc)		export_get_uint(ifile)
#define getsym(ifile,desc)		export_get_sym(ifile)
#define getsymref(ifile,desc)		export_get_symref(ifile)
#endif

#endif /* _ifile_h */
