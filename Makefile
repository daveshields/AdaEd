# $Header: /griffin.d/ada/ada/new/RCS/Makefile,v 1.14 1992/08/26 20:10:03 banner Exp $

SHELL=/bin/sh

CC= gcc
CFLAGS=-O2

#CC= g++
#CFLAGS=-g

#CC= CC
#CFLAGS=-g -I/usr/lang/include/CC

LINKER= $(CC)
LFLAGS=-lg

INSTALL = install

BINDIR = /usr/local
LIBDIR = /usr/local/lib
MANDIR = /usr/local/man

.SUFFIXES:
.SUFFIXES: .o .c .h .ch .s .vbs

.c.o:
	$(CC)$(CCVAR) $(CFLAGS) -c $<  

.s.o:
	$(CC)$(CCVAR) $(CFLAGS) -c $<

# always remake .h file when rebuild .c from .ch
# we make the derived files read-only so that attempts to edit them
# will fail, and so hopefully remind the user that the .ch file
# is the (single) file to be edited.

.ch.h:
	rm -f $*.h
	echo >$*.h
	chmod u+w $*.h
	makech -h  < $< > $*.h
	chmod a-w $*.h

.ch.c:
	rm -f $*.c
	echo >$*.c
	chmod u+w $*.c
	makech -c < $< > $*.c
	chmod a-w $*.c

.vbs.h:
	rm -f $*.h
	touch $*.h
	chmod u+w $*.h
	cdecom <$*.vbs | uniq >$*.h
	chmod a-w $*.h

# TARGET TO MAKE EVERYTHING

EXECS =	adafront adagen adabind adaexec adacomp adalib

all: $(EXECS)

predef: $(EXECS)
	rm -rf predef predefdir
	mkdir predefdir
	./adafront -s p -nl predefdir predef.ada
	./adagen -g p -nl predefdir predef
	touch predef

install : all predef
	-mkdir $(BINDIR)
	-mkdir $(LIBDIR)
	install adacomp $(BINDIR)
	install adabind $(BINDIR)
	install adaexec $(BINDIR)
	install adalib  $(BINDIR)
	install adafront $(LIBDIR)
	install adagen   $(LIBDIR)
	install predefdir/0.axq $(LIBDIR)/predef.axq
	install predefdir/0.trc $(LIBDIR)/predef.trc
	install predefdir/lib $(LIBDIR)/predef.lib
	-rm $(LIBDIR)/adabind
	ln -s $(BINDIR)/adabind $(LIBDIR)/adabind
	install adabind.l $(MANDIR)/manl
	install adacomp.l $(MANDIR)/manl
	install adaed.l   $(MANDIR)/manl
	install adaexec.l $(MANDIR)/manl
	install adalib.l  $(MANDIR)/manl

# remove all targets
MADE_HDRS =	vars.h gvars.h ivars.h hdr.h libhdr.h ghdr.h
MADE_SRCS =	vars.c gvars.c ivars.c
clean:
	rm -f *.o *.lm core $(EXECS) adaint
	rm -f  $(MADE_HDRS) $(MADE_SRCS)
	rm -rf predefdir predef

#---------------------------#
# adalib FILES AND ACTIOONS #
#---------------------------#

LIB_OBJS = adalib.o misc.o libf.o

adalib: $(LIB_OBJS)
	$(LINKER) -o adalib $(LIB_OBJS) -lm >lib.lm

#---------------------------#
# adacomp FILES AND ACTIONS #
#---------------------------#

COMP_OBJS = adacomp.o adamrg.o misc.o

adacomp: $(COMP_OBJS)
	$(LINKER) -o adacomp $(COMP_OBJS) -lm >comp.lm

#----------------------------#
# adafront FILES AND ACTIONS #
#----------------------------#

FRONT_OBJS = action.o acttoks.o adalex.o adafront.o adared.o debug.o errs.o \
			follow.o libf.o lookup.o makecorr.o misc.o ppredef.o \
			prserr.o prsinit.o prsutil.o pspans.o recover.o reduce.o shift.o \
			0a.o 0b.o 2.o 3a.o 3b.o 4a.o 4b.o 4c.o 5.o 6.o 7.o 8.o 9.o 10.o \
			11.o 12a.o 12b.o 12c.o 13.o 14.o arith.o dbx.o dclmap.o \
			errmsg.o eval.o lib.o libr.o libw.o machine.o  \
			nodes.o set.o smisc.o sspans.o units.o util.o vars.o

adafront: $(FRONT_OBJS)
	$(LINKER) -o adafront $(FRONT_OBJS) -lm >front.lm


#--------------------------------------#
# adagen and adabind FILES AND ACTIONS #
#--------------------------------------#

GEN_OBJS =	12b.o aggr.o arith.o axqr.o axqw.o dbg.o dbx.o dclmap.o decl.o \
			expand.o expand2.o expr.o g0a.o gen.o glib.o  gmain.o gmisc.o \
			gnodes.o gpredef.o gutil.o gvars.o init.o initobj.o lang.o lib.o \
			libf.o libr.o libw.o maincase.o misc.o nam.o opdesc.o pack.o \
			peep.o proc.o read.o segment.o sep.o set.o smisc.o stat.o \
			type.o util.o vars.o

BND_OBJS =	12b.o arith.o axqr.o axqw.o blib.o bmisc.o bmain.o bnodes.o \
			dbg.o dbx.o dclmap.o g0a.o gen.o ginter.o glib.o gpredef.o \
			gutil.o gvars.o init.o lang.o lib.o libf.o libr.o libw.o misc.o \
			opdesc.o peep.o read.o segment.o sep.o set.o smisc.o util.o vars.o

adagen: gvars.c vars.c hdr.h ghdr.h libhdr.h $(GEN_OBJS) 
	$(LINKER) -o adagen $(GEN_OBJS) -lm >gen.lm

adabind: vars.c gvars.c hdr.h ghdr.h libhdr.h $(BND_OBJS)
	$(LINKER) -o adabind $(BND_OBJS) -lm >bind.lm

# $(GEN_OBJS): gvars.c vars.c hdr.h libhdr.h

# $(BND_OBJS): vars.c

# Dependence on gmisc.o causes extra compile but gets dependencies right.
bmisc.o: gmisc.o
	cp gmisc.c bmisc.c
	$(CC) -DBINDER -c bmisc.c
	rm -f bmisc.c

# Look at last comment.
bnodes.o: gnodes.o
	cp gnodes.c bnodes.c
	$(CC) -DBINDER -c bnodes.c
	rm -f bnodes.c

#---------------------------#
# adaexec FILES AND ACTIONS #
#---------------------------#

INT_OBJS = 	axqr.o farith.o ilist.o imain.o imisc.o intb.o intc.o \
			ipar.o ivars.o libf.o machine.o  misc.o opname.o \
			predef1.o predef2.o predef3.o predef4.o predef5.o \
			predef6.o tasking.o

XINT_OBJS =	inta.o load.o

adaexec: ivars.c inta_interface.o load_interface.o $(INT_OBJS)
	$(LINKER) -o adaexec $(LFLAGS) $(INT_OBJS) $(XINT_OBJS) -lm >int.lm
	ld -r -x load_interface.o $(INT_OBJS) inta_interface.o >adaint.lm
	mv a.out adaint

#inta_interface.o: inta.o
#	$(CC)$(CCVAR) -c -DINTERFACE $(CFLAGS) -o inta_interface.o inta.c

inta_interface.o: inta.o
	mv inta.o inta.o.b
	$(CC)$(CCVAR) -c -DINTERFACE $(CFLAGS) inta.c
	mv inta.o inta_interface.o
	mv inta.o.b inta.o
	touch inta_interface.o

load_interface.o: load.o
	mv load.o load.o.b
	$(CC)$(CCVAR) $(CFLAGS) -DINTERFACE -c load.c
	mv load.o load_interface.o
	mv load.o.b load.o
	touch load_interface.o

misc.o :
	$(CC) $(CFLAGS) -DLIBDIR=\"$(LIBDIR)\" -c misc.c

ALL_OBJS =  $(FRONT_OBJS) $(GEN_OBJS) $(BND_OBJS) $(INT_OBJS) \
			$(XINT_OBJS)

Makeext :
	x2hdeps $(ALL_OBJS) >Makeext

include Makeext
