.TH ADAED "" "4 August 1992" "NYU Ada Group" "Unix Programmer's Manual"
.SH NAME
adaed \- NYU translator and interpreter for the Ada programming language
.SH SYNOPSIS
.B adacomp
[ option ] ...
.I file
.TP 9
.B adabind
[ option ]
.TP 9
.B adaexec 
[ option ]
.TP 9
.B adalib
[ \-l 
.I library
]
.SH DESCRIPTION
Adaed is a translator/interpreter for the Ada programming language
that is intended primarily for educational use. 
.B Adacomp 
compiles an Ada program; it invokes in succession
the two compilation phases: parsing and semantic analysis (the front end),
and code generation. The
.I file
argument refers to the source file; if it contains no suffix 
the Ada source is assumed to be in 
.I file.ada. 
It may be a full path name.
The output of the compiler is
an instruction stream for an abstract Ada machine, which is 
subsequently interpreted.
.PP
.B Adabind 
binds a given \fIlibrary\fR with the specified \fImain_unit\fR to form
an executable program.
.PP
.B Adaexec
invokes the Ada machine interpreter for the bound program given in the
specified library.
.PP
.B Adalib
is a utility that enables the user to examine the contents
of the specified library.
.PP
Note: all options must precede the file name for 
.BR adacomp
and must be in lower case.
.SH LIBRARY
All compilations require a library.
A library is a subdirectory, which is created or reinitialized
when the user invokes a command 
containing \fB\-n\fP option, such as:
.in +1.0i
.I
	adacomp -n -l libname adafile
.in -1.0i
Intermediate files appear in subdirectory \fIlibname\fP. 
This directory is created by the command if it does not already exist.
Only the listing files are created in the directory from which \fIadacomp\fR
is invoked. 
The \fIlibname\fR directory should be used to hold files created by
the \fIadaed\fR commands only (i.e. those produced by the Ada/Ed system);
confusion and grief may result if you attempt to use a library directory
to hold other files.
The \fIlibname\fR argument may be a full path name.
.PP
If the environment variable ADALIB is defined, its value is used as
a default library
and the \fB\-l\fP option (including its \fIlibname\fR argument) 
to \fIadacomp, adabind, adaexec,\fP and \fIadalib \fP can be omitted.
.PP
A given utility library, UL (e.g. one that contains mathematical functions)
may be used by several unrelated programs.  It may then be convenient to
create independent libraries for each program, and initialize each library 
with the contents of UL.  This can be done simply by 
creating directories for each library, and copying the contents of UL
into each of these.
.SH OPTIONS
.PP
The options for 
.I adacomp
are as follows:
.TP 15
.B \-a
Generates instructions for use by
the interpreter (\fIadaexec\fP command) to trace the Ada source lines. Used in 
conjunction with the \fB\-t a\fR option of adaexec.
.TP 
.B \-b
Indicates that the binding of the library is to be performed if the current 
compilation is completed without errors.
.TP
.B \-g
Specifies that the compiler is to produce a listing of the generated 
instructions for the Ada machine (of little interest to most users).
.TP
.BI \-i x
This is an option to the binder and is relevant only if the \fB\-b\fP
option is used.
See options for \fIadabind\fP below.
.TP
.BI \-l library
Uses the specified library to satisfy references to compilation units not
present in the file being compiled. If the compilation is successful, the units
defined in the file are added to the library.
If this option is not specified explicitly, a default library is implicitly
defined by the ADALIB environment variable.
.TP 15
.BI \-m unit_name
This is an option to the binder and is relevant only if the \fB\-b\fP
option is used.
See options for \fIadabind\fP below.
.TP
.BI \-n
Indicates that a new library is to be created for this compilation. The name of
the library is indicated by the 
.B \-l
option or through the ADALIB environment variable. The 
.B \-n
option must be specified if the library referenced by the 
.B \-l
option (or the ADALIB environment variable)
does not already exist or must be reinitialized.
.TP
.B \-s
Produces a listing of the source file. The name of the listing file is 
the input file name prefix with suffix \fI.lis\fP. 
By default, no listing file is generated unless
there are warnings, errors or informational messages to report.
.TP
.B \-v
Gives a (verbose) descriptive trace showing the subsidiary 
programs invoked by the
.I adacomp
command, the options and arguments passed to them, and their exit status.
This is used primarily for system checkout.
.PP
The options for
.I adabind
are as follows:
.TP
.BI \-l library
Specifies the library which together with the main unit will produce a
bound program which can be executed by \fIadaexec\fR.
If this option is not specified explicitly, a default library is implicitly
defined by the ADALIB environment variable.
.TP 15
.BI \-m unit_name
Specifies the name of the unit which is to serve as a main program.
When the library contains only one main program (which must be a parameterless 
procedure) this option is not needed.
.TP
.BI \-i x
To be used for programs that use \fBpragma\fR INTERFACE. \fIx\fR 
designates the non-Ada interfaced procedures and may be a) the name of
an object file, created by the user, of the form \fIfilename.o\fR 
(that appears in the same directory as the Ada program); or b)
an abbreviation for the library '/lib/lib\fIx\fR.a'. 
If that does not exist then '/usr/lib/lib\fIx\fR.a' is searched. 
This library is unrelated to the Ada program library referenced by
the various \fIadaed\fP commands, and generally refers to a standard
library provided for another programming language.
This option may be used as many times as necessary, providing that each use
represents only a single file or library. 
Thus, \fIadabind -i a.o -i b.o -i lib ...\fP is acceptable, 
while \fIadabind -i a.o b.o lib ...\fP is not.
To use this option,
the environment variable INT must be set to point to the directory
containing the file \fIadaint\fP (see the Setup file or your system manager).
Usage examples appear below.
.PP
The options for
.I adaexec
are as follows:
.TP
.BI \-l library
Specifies the library which contains the bound program to be executed.
If this option is not specified explicitly, a default library is implicitly
defined by the ADALIB environment variable.
.TP 10
.BI \-m bound_main_unit
Specifies the name of the bound main unit, i.e. the main unit
that was specified to \fIadabind\fP, or \fIadacomp\fP. Note that a given
library may have been bound several times with different main units.
When the library has been bound with only one main unit, this option
is not needed.
.TP
.BI \-h heap_size
Specify the size of the heap increment in kilowords, by which
the heap is expanded when the elaboration of a new entity
requires it. The heap expands to fill available memory. 
The default increment is 128.
This parameter limits the size of the largest object that can be created 
in a program.
.TP
.BI \-p p_size
Specifies the size in bytes of the program stack size for the main task.
The default is 10000.
Argument values in the range 1..31 are multiplied by 1024 to obtain the 
stack  size in bytes.
The maximum value is 32767.
.TP
.BI \-s t_size
Specifies the size in bytes of the stack size for each new task.
The default is 10000. Argument values in the range 1..31 are multiplied
by 1024 to obtain the stack size in bytes.
Use of small stack sizes may be appropriate when executing programs with
many tasks, each of which can run with a small stack.
The maximum value is 32767.
.TP
.BI \-r number_of_stmts (an integer)
Invoke a 'round-robin' scheduling policy instead of the 'run-until-block'
default scheduling policy and specify the maximum number of 
interpreted statements that a given task can execute before switching
to another task (the minimum value is 1).
.TP
.BI \-t trace_options
Specify one or more of the following letters indicating the 
kind of trace(s) requested for the execution of the program.
.RS 10
.TP 20
\fBa\fP    (Ada line)
Display the source line numbers.
This requires that the program be compiled with the \fB\-a\fP option.
.TP 20
\fBc\fP    (calls) 
Display the name of each subprogram as it is entered and exited.
.TP 20
\fBe\fP    (exceptions)
Display the name of each exception as it is raised.
.TP 20
\fBr\fP    (rendezvous)
Trace each rendezvous.
.TP 20
\fBs\fP    (switches)
Display context switches between tasks.
.TP 20
\fBt\fP    (tasks)
Display task creation, activation, and  termination.
.RE
.PP
.SH EXAMPLES
The following examples show typical usage:
.sp
.RS 5
.TP 5
1)
Compile t1.ada into a new library called testlib and bind the library; then 
execute it.
The listing is written to t1.lis.
Note that \fB\-s\fP is used to force a listing file to be created.
.in +1.0i
.I
	adacomp -s -nl testlib -b t1
.br
.I
	adaexec -l testlib
.in -1.0i
.br
.TP 5
2)
Compile a package specification in p.spc and corresponding body in p.bod
into a new library called tstlib.
Then compile t2.ada into the same library, bind the main program, and 
execute it
.br
.in +1.0i
.I
	adacomp -nl tstlib p.spc
.br
.I
	adacomp -l tstlib p.bod
.br
.I
	adacomp -l tstlib -b t2
.br
.I
	adaexec -l tstlib
.br
.in -1.0i
.PP
.TP 5
3)
In the example above, the binding could be done in a separate phase.
This is achieved by replacing the third command above with:
.in +1.0i
.I
	adacomp -l tstlib t2
.br
.I
	adabind -l tstlib
.in -1.0i
.PP
.TP 5
4)
Example 2 above could be done without explicitly specifying the library
by setting the environment variable ADALIB, as follows:
.in +1.0i
.I
	setenv ADALIB \fRmy_default_directory
.br
.I
	adacomp -n p.spc
.br
.I
	adacomp p.bod
.br
.I
	adacomp -b t2
.br
.I
	adaexec
.in -1.0i
.sp
.PP
.TP 5
5)
Compile a program with line numbers included in the generated code.
Execute it displaying Ada source line numbers as they are encountered.
.in +1.0i
.I
	adacomp -a -nl libname -b t1
.br
.I
	adaexec -t a -l libname 
.in -1.0i
.TP 5
6)
Compile a program with two parameterless procedures (potential main programs)
which are named MAIN1 and MAIN2
in files p1.ada and p2.ada respectively, and bind the library \fItstlib\fP
using MAIN1 as the main program.
.in +1.0i
.I
	adacomp -nl tstlib p1
.br
.I
	adacomp -l tstlib p2
.br
.I
	adabind -m main1 -l tstlib
.br
.I
	adaexec -l tstlib
.in -1.0i
.TP 5
7)
Suppose we wish to add another program to the library tstlib (created in 
Example 6) whose main program unit is named MAIN3 and appears in file p3.ada.
The following commands will compile and execute MAIN3. As tstlib was
previously bound with MAIN1 as a main unit, it is now necessary to use the
\fB\-m\fP option to \fIadaexec\fP in order to select the desired bound
main unit.
.in +1.0i
.I
	adacomp -l tstlib p3
.br
.I
	adabind -m main3 -l tstlib
.br
.I
	adaexec -m main3 -l tstlib
.in -1.0i
.TP 5
8)
The contents of the library above can be examined by:
.in +1.0i
.I
	adalib -l tstlib
.in -1.0i
\fIAdalib\fP writes the name, type and compilation date of each unit
in the specified library to standard output.
In addition, it writes the current status (active or obsolete) of each 
unit. Units which may be main programs are noted by "(Main)"; if there
is more than one such unit, the \fB\-m\fP option to adabind must be 
specified during binding.  Libraries that have been bound will contain
at least one unit labeled "binding unit".  If several of these are active,
the \fB\-m\fP option must be specified for \fIadaexec\fP.
.RE
.SH "PRAGMA INTERFACE"
Pragma interface (LRM 13.9) is currently supported for
interfacing to subprograms written in FORTRAN or C.
.PP
Arguments to interfaced procedures must be
one of the following types:
.br
.DS
For C: integer, float, access, array, record, and enumeration types.
.br
For FORTRAN: integer, float and array.
.DE
The return types available are integer and float.
.PP
Following are sample Ada programs that are interfaced
to subprograms coded in FORTRAN and C, 
together with the code for the interfaced subprograms:
.TP 5
1)
Interface to FORTRAN
.PP
.DS
 C This is a source file called \fIfunc.f\fR which contains two functions to be used in an
 C Ada program with pragma INTERFACE.

     function sqr(x)
     sqr = x*x
     return
     end

     function cube(x)
     cube = x*x*x
     return
     end
.DE
.PP
.DS
 -- Assume that the following are the contents of file \fIfortlib.ada\fR. 
 -- It contains a compilation unit that defines two functions which are 
 -- interfaced to the above routines.

 \fBpackage\fR FORTRAN_LIB \fBis\fR
     \fBfunction\fR SQR(X:FLOAT) \fBreturn\fR FLOAT;
     \fBfunction\fR CUBE(X:FLOAT) \fBreturn\fR FLOAT;
 \fBprivate\fR
     \fBpragma\fR INTERFACE(FORTRAN, SQR);
     \fBpragma\fR INTERFACE(FORTRAN, CUBE);
 \fBend\fR FORTRAN_LIB;

 \fBwith\fR FORTRAN_LIB, TEXT_IO; \fBuse\fR FORTRAN_LIB, TEXT_IO;
 \fBprocedure\fR TEST \fBis\fR
    \fBpackage\fR MY_FLOAT_IO \fBis new\fR FLOAT_IO(FLOAT); \fBuse\fR MY_FLOAT_IO;
 \fBbegin\fR
     PUT(SQR(2.0));
     NEW_LINE;
     PUT(CUBE(2.0));
     NEW_LINE;
 \fBend\fR TEST;
.DE
.PP
To compile and execute, enter the following commands:
.in +1.0i
.I
	f77 -c func.f
.br
.I
	adacomp -nl testlib -b -i func.o fortlib
.br
.I
	adaexec -l testlib
.br
.in -1.0i
The output will be:
.DS
 4.00000E+00
 8.00000E+00
 1.41421E+00
.DE
.PP
.DS 
One of the demo programs illustrates how one can use pragma interface
to build a library of mathematical functions from those provided by the
system.
.DE
.TP 5
2)
Interface to C
.PP
.DS
/*
 * Source file \fIproc.c\fP contains procedures PRINTA and PRINTS1 called by
 * the Ada program above.
 */
.br
printa(ara)
.br
int ara[];
.br
{
    int i;
    for (i=0;i<10;i++) {
       printf("%d ",ara[i]);
    }
    printf("\\n");
.br
}

prints1(ara,len)
.br
int ara[];
.br
int len;
.br
{
    int i;
    for (i=0;i<len;i++) {
        printf("%c",ara[i]);
    }
    printf("\\n");
.br
}
.DE
.PP
.DS
-- Assume that file \fItest_interface.ada\fP contains the following program:
 \fBprocedure\fR C_INTERFACES \fBis\fR
     \fBtype\fR ARA10 \fBis\fR \fBarray\fR(1..10) \fBof\fR INTEGER;
     A10: ARA10 := (1,2,3,4,5,6,7,8,9,10);

     \fBprocedure\fR PRINTA(A:ARA10);
     -- PRINTA prints an array of 10 elements of type INTEGER
     \fBpragma\fR INTERFACE(C, PRINTA);

     \fBprocedure\fR PRINTS1(A:STRING; LEN: INTEGER);
     -- PRINTS1 prints an array of LEN elements of type CHARACTER
     \fBpragma\fR INTERFACE(C, PRINTS1);

     \fBprocedure\fR PRINTS(A:STRING) \fBis\fR
     -- This routine prints a string by passing the string and its length
     -- to the routine PRINTS1 which is written in C.
     \fBbegin\fR
         PRINTS1(A, A'length);
     \fBend\fR;

 \fBbegin\fR
    PRINTA(A10);
    PRINTS("this is any string");
 \fBend\fR;
.DE
.PP
To compile and execute, enter the following:
.in +1.0i
.I
	gcc -c proc.c
.br
.I
	adacomp -i proc.o -nl testlib -b test_interface
.br
.I
	adaexec -l testlib 
.in -1.0i
.PP
The resulting output is as follows:
.DS
.br
1 2 3 4 5 6 7 8 9 10
.br
this is any string
.DE
.PP
.SH ENVIRONMENT
.LP
The environment variable
.B \s-1ADALIB\s0
contains the name of the library used if none is specified on the command line.
.LP
Normally the executables called by
.B adacomp
and the predefined libraries are in a directory built into the system.
The directory containing these can be specified by the environment
variable
.B \s-1ADAED\s0
which overrides the built in directory name.
.LP
The location of individual components called by
.B adacomp
or the location of the predefined libraries can be overridden with the
following environment variables:
.BR \s-1ADAFRONT\s0 " For the front end, " "adafront;"
.BR \s-1GEN\s0 " For the code generator, " adagen;
.BR \s-1BND\s0 " For the binder, " "adabind; " and
.BR \s-1ADAEDPREDEF\s0 " For the predefined libraries."
.SH FILES
.ta \w'predef.axq'u+4n
file.ada	Ada source file
.br
adaint	partially built interpreter (used for pragma interface)
.br
predef.axq	symbol table for predef
.br
predef.trc	tree file for predef
.br
predef.lib	library for predef
.SH DIAGNOSTICS
Adaed commands return an exit code of 0 in the
case of success, and nonzero otherwise.
An error code of 1 indicates errors in usage of the Ada language,
2 is returned if there is an internal Adaed system error, and 3 
denotes some invalid usage of the Adaed system.
Error messages regarding invalid system usage are directed to 
the standard error file.
Ada language related messages detected at compilation are written to the
listing file, while those detected by 
.I adabind
or
.I adaexec
appear on standard output.
.PP
Note, that an error in a given compilation unit may cause subsequent
compilation units (within the same compilation) not to be recognized.
.SH AUTHORS
Ada/Ed-C was written by the following members of the NYU Ada Project:
Bernard Banner, Jerome Chiabaut, Robert Dewar, Anne Dinning, Alain Lauque,
Gail Schenker Morgulis, Brett Porter,
Jean-Pierre Rosen, Edmond Schonberg, David Shields, Brian Siritzky,
Franck Triplet.
.SH BUGS
We give absolutley no warranty as to the correctness of the system. It was
designed strictly for teaching purposes. Currently it is unvalidated although 
we hope to put it in a validatable shape in the near future.
.PP
Any compilation or execution that terminates abnormally with
mention of 
.I "internal error"
has uncovered a bug that should be reported to the
NYU Ada group.
.IP
NYUADA project
.br
New York University
.br
251 Mercer Street
.br
New York, N.Y. 10012
.br
(212) 998 \- 3480
