
--::::::::::
--cli.ads
--::::::::::
-- **************************************
-- *                                    *
-- * CLI (Command Line Interface)       * SPEC
-- *                                    *
-- **************************************
package CLI is

--| Purpose
--|   CLI is a package which implements a Command
--| Line Interface.  It mirrors the UNIX/C
--| command line interface, providing an argument
--| count and the arguments themselves.
--|
--| Initialization Exceptions (none)
--|
--| Notes
--|   Compiler limit on string length and dynamic memory.
--|   INITIALIZE must be called once, and only once, during
--| the execution of the main Ada proc.
--|
--| Modifications
--|  2/25/88  Richard Conn    Initial Version
--|  5/12/89  Richard Conn    Review and Upgrade
--|  4/11/90  Richard Conn    MIL-HDBK-1804 Annotations and
--|                           Meridian Ada Interface Added
   
  -- ...................................
  -- .                                 .
  -- . CLI.INITIALIZE                  . SPEC
  -- .                                 .
  -- ...................................
  procedure Initialize (Program_Name        : in STRING;
                        Command_Line_Prompt : in STRING);
  --| Purpose
  --|   Initialize this package.  This routine must be called
  --| before any other routines or objects are called or referenced.
  --|
  --| Exceptions (none)
  --|
  --| Notes
  --|   CALL THIS PROCEDURE ONLY ONE TIME

  -- ...................................
  -- .                                 .
  -- . CLI.ARGC (Argument Count)       . SPEC
  -- .                                 .
  -- ...................................
  function ArgC return NATURAL;
  --| Purpose
  --|   Return the number (1 to N) of command line arguments.
  --| ARGC is at least 1 because the name of the program or
  --| process is always ARGV(0).
  --|
  --| Exceptions (none)
  --| Notes (none)

  -- ...................................
  -- .                                 .
  -- . CLI.ARGV (Argument Value)       . SPEC
  -- .                                 .
  -- ...................................
  function ArgV (Index : in NATURAL) return STRING;
  --| Purpose
  --|   Return the INDEXth (0 <= INDEX < ARGC) command line
  --| argument.  Example: if ARGC = 1, ARGV(0) is the only
  --| valid argument string.  ARGV(0) is always the name of
  --| the program or process.
  --|
  --| Exceptions
  --|   INVALID_INDEX     raised if Index >= ARGC
  --|
  --| Notes (none)

  INVALID_INDEX    : exception;
  UNEXPECTED_ERROR : exception;  -- raised anytime
   
end CLI;
--::::::::::
--cli.adb
--::::::::::
-- This implementation of Package Body CLI is general-purpose.
-- Using TEXT_IO, it prompts the user for input arguments and
-- accepts these arguments via a GET_LINE call.
with TEXT_IO;
package body CLI is

   LOCAL_ARGC : NATURAL := 0;
   
   package STRING_LIST is
      
      NUMBER_OF_STRINGS : NATURAL := 0;
      
      procedure ADD_TO_LIST (ITEM : in STRING);
      function GET_FROM_LIST (ITEM : in NATURAL) return STRING;
      
   end STRING_LIST;
   
   package body STRING_LIST is
      
      type DYNAMIC_STRING_OBJECT (LENGTH : NATURAL);
      type DYNAMIC_STRING is access DYNAMIC_STRING_OBJECT;
      type DYNAMIC_STRING_OBJECT (LENGTH : NATURAL) is 
         record
            DS   : STRING (1 .. LENGTH);
            NEXT : DYNAMIC_STRING;
         end record;
      
      FIRST : DYNAMIC_STRING := null;
      LAST  : DYNAMIC_STRING := null;
      
      procedure ADD_TO_LIST (ITEM : in STRING) is
         
         --========================= PDL ===========================
         --|ABSTRACT:
         --|    ADD_TO_LIST adds the ITEM string to the linked list
         --|    of dynamic strings implemented by this package.
         --|DESIGN DESCRIPTION:
         --|    Create new DYNAMIC_STRING_OBJECT of the proper length
         --|    Set DS field of new object to the ITEM string
         --|    Set the NEXT field of the new object to NULL
         --|    If FIRST pointer is null
         --|      Set FIRST and LAST to point to the new object
         --|    Else
         --|      Set LAST.NEXT to point to the new object
         --|      Set LAST to point to the new object
         --|    End if
         --|    Increment NUMBER_OF_STRINGS
         --=========================================================
         
         TEMP : DYNAMIC_STRING;
      begin
         TEMP := new DYNAMIC_STRING_OBJECT (ITEM'LENGTH);
         TEMP.DS (1 .. ITEM'LENGTH) := ITEM;
         TEMP.NEXT                  := null;
         if FIRST = null then
            FIRST := TEMP;
            LAST  := TEMP;
         else
            LAST.NEXT := TEMP;
            LAST      := TEMP;
         end if;
         NUMBER_OF_STRINGS := NUMBER_OF_STRINGS + 1;
      end ADD_TO_LIST;
      
      function GET_FROM_LIST (ITEM : in NATURAL) return STRING is
         
         --========================= PDL ===========================
         --|ABSTRACT:
         --|    GET_FROM_LIST returns the ITEM string from the linked list
         --|    of dynamic strings implemented by this package.
         --|DESIGN DESCRIPTION:
         --|    If ITEM > 0
         --|        Advance to desired item
         --|    End If
         --|    Return the DS field of the desired item
         --=========================================================
         
         ROVER : DYNAMIC_STRING := FIRST;
      begin
         if ITEM > 0 then
            for I in 1 .. ITEM loop
               ROVER := ROVER.NEXT;
            end loop;
         end if;
         return ROVER.DS;
      end GET_FROM_LIST;
      
   end STRING_LIST;
   
   procedure INITIALIZE (PROGRAM_NAME        : in STRING;
                         COMMAND_LINE_PROMPT : in STRING) is
      
      --========================= PDL ===========================
      --|ABSTRACT:
      --|    INITIALIZE prompts the user for the command line
      --|    arguments and loads the linked list with them.
      --|DESIGN DESCRIPTION:
      --|    Set CURRENT_STATE to LOOKING_FOR_TOKEN
      --|    Set the first list object to PROGRAM_NAME
      --|    Prompt the user with COMMAND_LINE_PROMPT and
      --|      get his response
      --|    Over number of characters in line, loop
      --|        Case CURRENT_STATE
      --|            When LOOKING_FOR_TOKEN
      --|                If character is not white-space
      --|                    Set CURRENT_STATE to IN_TOKEN
      --|                    If character is quote (")
      --|                        Set QUOTED to TRUE
      --|                        Set START to the character's index + 1
      --|                    Else
      --|                        Set QUOTED to FALSE
      --|                        Set START to the character's index
      --|                    End IF
      --|                End If
      --|            When IN_TOKEN
      --|                If QUOTED
      --|                    If character is quote (")
      --|                        Set STOP to the previous character's index
      --|                        Add slice from START to STOP to list
      --|                        Set CURRENT_STATE to LOOKING_FOR_TOKEN
      --|                    End If
      --|                ElsIF character is white-space
      --|                    Set STOP to the previous character's index
      --|                    Add slice from START to STOP to list
      --|                    Set CURRENT_STATE to LOOKING_FOR_TOKEN
      --|                End If
      --|        End Case
      --|    End Loop
      --|    If CURRENT_STATE is IN_TOKEN
      --|        Set STOP to the previous character's index
      --|        Add slice from START to STOP to list
      --|    End if
      --|    Set LOCAL_ARGC to NUMBER_OF_STRINGS
      --|    Output NEW_LINE (to reset column count in TEXT_IO)
      --=========================================================
      
      ARGCOUNT      : NATURAL := 1;
      INLINE        : STRING (1 .. 400);
      LAST          : NATURAL;
      START         : NATURAL;
      STOP          : NATURAL;
      QUOTED        : BOOLEAN;
      type STATE is (LOOKING_FOR_TOKEN, IN_TOKEN);
      CURRENT_STATE : STATE   := LOOKING_FOR_TOKEN;
   begin
      STRING_LIST.ADD_TO_LIST (PROGRAM_NAME);
      TEXT_IO.PUT (COMMAND_LINE_PROMPT);
      TEXT_IO.GET_LINE (INLINE, LAST);
      for I in 1 .. LAST loop
         case CURRENT_STATE is
            when LOOKING_FOR_TOKEN  =>
               if INLINE (I) > ' ' then
                  CURRENT_STATE := IN_TOKEN;
                  if INLINE (I) = '"' then
                     QUOTED := TRUE;
                     START  := I;
                  else
                     QUOTED := FALSE;
                     START  := I;
                  end if;
               end if;
            when IN_TOKEN =>
               if QUOTED then
                  if INLINE (I) = '"' then
                     STOP          := I;
                     STRING_LIST.ADD_TO_LIST (INLINE (START .. STOP));
                     CURRENT_STATE := LOOKING_FOR_TOKEN;
                  end if;
               elsif INLINE (I) <= ' ' then
                  STOP          := I - 1;
                  STRING_LIST.ADD_TO_LIST (INLINE (START .. STOP));
                  CURRENT_STATE := LOOKING_FOR_TOKEN;
               end if;
         end case;
      end loop;
      if CURRENT_STATE = IN_TOKEN then
         STOP := LAST;
         STRING_LIST.ADD_TO_LIST (INLINE (START .. STOP));
      end if;
      LOCAL_ARGC := STRING_LIST.NUMBER_OF_STRINGS;
      TEXT_IO.NEW_LINE;
   end INITIALIZE;
   
   function ARGC return NATURAL is
      
      --========================= PDL ===========================
      --|ABSTRACT:
      --|    ARGC returns the argument count.
      --|DESIGN DESCRIPTION:
      --|    Return LOCAL_ARGC
      --=========================================================
      
   begin
      return LOCAL_ARGC;
   end ARGC;

   function ARGV (INDEX : in NATURAL) return STRING is
      
      --========================= PDL ===========================
      --|ABSTRACT:
      --|    ARGV returns the indicated argument string.
      --|DESIGN DESCRIPTION:
      --|    If INDEX is out of range, raise INVALID_INDEX
      --|    Return GET_FROM_LIST(INDEX)
      --=========================================================
      
   begin
      if INDEX >= LOCAL_ARGC then
         raise INVALID_INDEX;
      end if;
      return STRING_LIST.GET_FROM_LIST (INDEX);
   exception
      when INVALID_INDEX  =>
         raise ;
      when others    =>
         raise UNEXPECTED_ERROR;
   end ARGV;
   
end CLI;
--::::::::::
--pager2.ada
--::::::::::
-- PROGRAM/CODE BODY NAME:	PAGER2
-- AUTHOR:			Richard Conn
-- VERSION:			1.1
-- DATE:			6/12/89
-- REVISION HISTORY -
-- Version	Date	Author		Comments
--    1.0	8/28/87	Richard Conn	Initial
--    1.1       6/12/89 Richard Conn    CLI interface added
-- KEYWORDS -
--	pager, pager2, paged files, page, unpage
-- CALLING SYNTAX -
--	From the command line: pager2
--	From the command line: pager2 verb arguments
-- EXTERNAL ROUTINES -
--	Package CLI
--	Package TEXT_IO
-- DESCRIPTION -
--	PAGER2 assembles, extracts elements from, and lists paged files.
-- Paged files are text files which contain one or more component files
-- prefixed by a banner like:
--
--	::::::::::
--	filename
--	::::::::::
--
-- or
--
--	--::::::::::
--	--filename
--	--::::::::::
--
--	PAGER2 will manipulate paged files whose components
-- are prefixed with either banner, but it assembles paged files with only
-- the second banner (beginning with the Ada comment characters).
 
--===========================================================================
-------------------------- PACKAGE LINE_DEFINITION --------------------------
--===========================================================================
 
-- The following package defines an object of type LINE
package LINE_DEFINITION is
 
    -- The maximum length of a line
    MAX_LINE_LENGTH : constant NATURAL := 200;
 
    -- Type definition for LINE
    type LINE is record
	CONTENT : STRING(1 .. MAX_LINE_LENGTH);
	LAST    : NATURAL;
    end record;
    type LINE_LIST_ELEMENT;
    type LINE_LIST        is access LINE_LIST_ELEMENT;
    type LINE_LIST_ELEMENT is record
	CONTENT : LINE;
	NEXT    : LINE_LIST;
    end record;
 
    -- Banners
    COMMENT_BANNER  : constant STRING  := "--::::::::::";
    BANNER          : constant STRING  := "::::::::::";
 
    -- Convert strings to LINEs and back
    function CONVERT(FROM : in STRING) return LINE;
    function CONVERT(FROM : in LINE) return STRING;

    -- Convert a LINE to lower-case characters
    procedure TOLOWER(ITEM : in out LINE);
    function TOLOWER(ITEM : in LINE) return LINE;
 
end LINE_DEFINITION;
 
package body LINE_DEFINITION is
 
    -- Convert strings to LINEs
    function CONVERT(FROM : in STRING) return LINE is
	TO : LINE_DEFINITION.LINE;
    begin
	TO.CONTENT(TO.CONTENT'FIRST .. TO.CONTENT'FIRST + FROM'LENGTH - 1) :=
	  FROM;
	TO.LAST := FROM'LENGTH;
	return TO;
    end CONVERT;
 
    function CONVERT(FROM : in LINE) return STRING is
    begin
	return FROM.CONTENT(FROM.CONTENT'FIRST .. FROM.LAST);
    end CONVERT;
 
    procedure TOLOWER(ITEM : in out LINE) is
    begin
	for I in ITEM.CONTENT'FIRST .. ITEM.LAST loop
	    if ITEM.CONTENT(I) in 'A' .. 'Z' then
		ITEM.CONTENT(I) :=
                  CHARACTER'VAL(CHARACTER'POS(ITEM.CONTENT(I)) -
		  CHARACTER'POS('A') + CHARACTER'POS('a'));
	    end if;
	end loop;
    end TOLOWER;

    function TOLOWER(ITEM : in LINE) return LINE is
        MYLINE : LINE;
    begin
        MYLINE := ITEM;
        TOLOWER(MYLINE);
        return MYLINE;
    end TOLOWER;
 
end LINE_DEFINITION;
 
--===========================================================================
-------------------------- PACKAGE INPUT_FILE -------------------------------
--===========================================================================
 
-- The following package manipulates an object called an INPUT_FILE,
-- which is a text file that is composed of objects of type LINE.
-- LINEs can only be read from an INPUT_FILE.
with LINE_DEFINITION;
package INPUT_FILE is
 
    -- Open the input file
    -- Exceptions which may be raised: FILE_NOT_FOUND, FILE_ALREADY_OPEN
    procedure OPEN(FILE_NAME : in STRING);
    procedure OPEN(FILE_NAME : in LINE_DEFINITION.LINE);
 
    -- Close the input file
    -- Exceptions which may be raised: FILE_NOT_OPEN
    procedure CLOSE;
 
    -- Read a line from the input file
    -- Exceptions which may be raised: FILE_NOT_OPEN, READ_PAST_END_OF_FILE
    procedure READ(TO : out LINE_DEFINITION.LINE);
 
    -- Return TRUE if the input file is empty (no more lines remain)
    -- Exceptions which may be raised: FILE_NOT_OPEN
    function END_OF_FILE return BOOLEAN;
 
    -- Exceptional conditions
    FILE_NOT_FOUND        : exception;
    FILE_ALREADY_OPEN     : exception;
    FILE_NOT_OPEN         : exception;
    READ_PAST_END_OF_FILE : exception;
 
end INPUT_FILE;
 
with TEXT_IO;
package body INPUT_FILE is
 
    -- The file descriptor for the input file
    FD : TEXT_IO.FILE_TYPE;
 
    -- Open the input file
    procedure OPEN(FILE_NAME : in STRING) is
    begin
	TEXT_IO.OPEN(FD, TEXT_IO.IN_FILE, FILE_NAME);
    exception
	when TEXT_IO.NAME_ERROR =>
	    raise FILE_NOT_FOUND;
	when TEXT_IO.STATUS_ERROR =>
	    raise FILE_ALREADY_OPEN;
    end OPEN;
 
    procedure OPEN(FILE_NAME : in LINE_DEFINITION.LINE) is
    begin
	OPEN(LINE_DEFINITION.CONVERT(FILE_NAME));
    end OPEN;
 
    -- Close the input file
    procedure CLOSE is
    begin
	TEXT_IO.CLOSE(FD);
    exception
	when TEXT_IO.STATUS_ERROR =>
	    raise FILE_NOT_OPEN;
    end CLOSE;
 
    -- Read a line from the input file
    procedure READ(TO : out LINE_DEFINITION.LINE) is
    begin
	TEXT_IO.GET_LINE(FD, TO.CONTENT, TO.LAST);
    exception
	when TEXT_IO.END_ERROR =>
	    raise READ_PAST_END_OF_FILE;
	when TEXT_IO.STATUS_ERROR =>
	    raise FILE_NOT_OPEN;
    end READ;
 
    -- Return TRUE if the input file is empty (no more lines remain)
    function END_OF_FILE return BOOLEAN is
    begin
	return TEXT_IO.END_OF_FILE(FD);
    exception
	when TEXT_IO.STATUS_ERROR =>
	    raise FILE_NOT_OPEN;
    end END_OF_FILE;
 
end INPUT_FILE;
 
--===========================================================================
-------------------------- PACKAGE OUTPUT_FILE ------------------------------
--===========================================================================
 
-- The following package manipulates an object called an OUTPUT_FILE,
-- which is a text file that is composed of objects of type LINE.
-- LINEs can only be written to an OUTPUT_FILE.
with LINE_DEFINITION;
package OUTPUT_FILE is
 
    -- Open the output file
    -- Exceptions which may be raised: CANNOT_CREATE_FILE, FILE_ALREADY_OPEN
    procedure OPEN(FILE_NAME : in STRING);
    procedure OPEN(FILE_NAME : in LINE_DEFINITION.LINE);
 
    -- Close the output file
    -- Exceptions which may be raised: FILE_NOT_OPEN
    procedure CLOSE;
 
    -- Write a line to the output file
    -- Exceptions which may be raised: FILE_NOT_OPEN, DISK_FULL
    procedure WRITE(FROM : in LINE_DEFINITION.LINE);
    procedure WRITE(FROM : in STRING);
 
    -- Exceptional conditions
    CANNOT_CREATE_FILE : exception;
    FILE_ALREADY_OPEN  : exception;
    FILE_NOT_OPEN      : exception;
    DISK_FULL          : exception;
 
end OUTPUT_FILE;
 
with TEXT_IO;
package body OUTPUT_FILE is
 
    -- File descriptor for the output file
    FD : TEXT_IO.FILE_TYPE;
 
    -- Open the output file
    procedure OPEN(FILE_NAME : in STRING) is
	INLINE : STRING(1 .. 80);
	LAST   : NATURAL;
    begin
	TEXT_IO.CREATE(FD, TEXT_IO.OUT_FILE, FILE_NAME);
    exception
	when TEXT_IO.STATUS_ERROR =>
	    raise FILE_ALREADY_OPEN;
	when TEXT_IO.USE_ERROR =>
	    raise CANNOT_CREATE_FILE;
	when TEXT_IO.NAME_ERROR =>
	    TEXT_IO.PUT_LINE(" Cannot create " & FILE_NAME);
	    loop
		begin
		    TEXT_IO.PUT(" Enter New File Name: ");
		    TEXT_IO.GET_LINE(INLINE, LAST);
		    TEXT_IO.CREATE(FD, TEXT_IO.OUT_FILE,
		      INLINE(INLINE'FIRST .. LAST));
		    exit;
		exception
		    when TEXT_IO.NAME_ERROR =>
			TEXT_IO.PUT_LINE(" Cannot create " &
			  INLINE(INLINE'FIRST .. LAST));
		    when others =>
			raise ;
		end;
	    end loop;
    end OPEN;
 
    procedure OPEN(FILE_NAME : in LINE_DEFINITION.LINE) is
    begin
	OPEN(LINE_DEFINITION.CONVERT(FILE_NAME));
    end OPEN;
 
    -- Close the output file
    procedure CLOSE is
    begin
	TEXT_IO.CLOSE(FD);
    exception
	when TEXT_IO.STATUS_ERROR =>
	    raise FILE_NOT_OPEN;
    end CLOSE;
 
    -- Write a line to the output file
    procedure WRITE(FROM : in LINE_DEFINITION.LINE) is
    begin
	TEXT_IO.PUT_LINE(FD, LINE_DEFINITION.CONVERT(FROM));
    exception
	when TEXT_IO.STATUS_ERROR =>
	    raise FILE_NOT_OPEN;
	when others =>
	    raise DISK_FULL;
    end WRITE;
 
    procedure WRITE(FROM : in STRING) is
    begin
	WRITE(LINE_DEFINITION.CONVERT(FROM));
    end WRITE;
 
end OUTPUT_FILE;
 
--===========================================================================
-------------------------- PACKAGE INCLUDE_FILE -----------------------------
--===========================================================================
 
-- The following package manipulates an object called an INCLUDE_FILE,
-- which is a text file that is composed of objects of type LINE.
-- LINEs can only be read from an INCLUDE_FILE.  An INCLUDE_FILE contains
-- the following types of LINE objects:
--	blank lines
--	comment lines ('-' is the first character in the line)
--	file names (a string of non-blank characters which does not
--		begin with the character '-' or '@')
--	include file names (a string of non-blank characters which
--		begins with the character '@', where the '@' is used to
--		prefix the file name within the include file and is not
--		a part of the file name of the actual disk file)
-- Include files may be nested several levels (defined by the constant
-- NESTING_DEPTH).
with LINE_DEFINITION;
package INCLUDE_FILE is
 
    -- Maximum number of levels include files may be nested
    NESTING_DEPTH     : constant NATURAL   := 40;
 
    -- Character which begins an include file name
    INCLUDE_CHARACTER : constant CHARACTER := '@';
 
    -- Character which begins a comment line
    COMMENT_CHARACTER : constant CHARACTER := '-';
 
    -- Open the include file (the LINE input string contains the leading '@')
    -- Exceptions which may be raised: FILE_NOT_FOUND, NESTING_LEVEL_EXCEEDED
    procedure OPEN(FILE_NAME : in LINE_DEFINITION.LINE);
    procedure OPEN(FILE_NAME : in STRING);
 
    -- Read a LINE containing a file name from the include file
    -- Exceptions which may be raised: FILE_NOT_OPEN, READ_PAST_END_OF_FILE
    procedure READ(TO : out LINE_DEFINITION.LINE);
 
    -- Abort processing the include file (close all open files)
    -- Exceptions which may be raised: FILE_NOT_OPEN
    procedure STOP;
 
    -- Exceptional conditions
    FILE_NOT_FOUND         : exception;
    NESTING_LEVEL_EXCEEDED : exception;
    FILE_NOT_OPEN          : exception;
    READ_PAST_END_OF_FILE  : exception;
    INCLUDE_FILE_EMPTY     : exception;
 
end INCLUDE_FILE;
 
with TEXT_IO;
package body INCLUDE_FILE is
 
    -- File Descriptor for main include file
    FD              : array(1 .. NESTING_DEPTH) of TEXT_IO.FILE_TYPE;
    CURRENT_LEVEL   : NATURAL := 0;
    NEXT_LINE       : LINE_DEFINITION.LINE;    -- next line to return by READ
    NEXT_LINE_READY : BOOLEAN := FALSE;        -- indicates next line is
                                               -- available
 
    -- Open the include file (the LINE input string contains the leading '@')
    -- Exceptions which may be raised: FILE_NOT_FOUND, NESTING_LEVEL_EXCEEDED
    procedure OPEN(FILE_NAME : in LINE_DEFINITION.LINE) is
    begin
	if CURRENT_LEVEL = NESTING_DEPTH then
	    raise NESTING_LEVEL_EXCEEDED;
	else
	    CURRENT_LEVEL := CURRENT_LEVEL + 1;
	    TEXT_IO.OPEN(FD(CURRENT_LEVEL), TEXT_IO.IN_FILE,
	      FILE_NAME.CONTENT(2..FILE_NAME.LAST));
	end if;
    exception
	when TEXT_IO.NAME_ERROR =>
	    TEXT_IO.PUT_LINE("Include File " &
	      LINE_DEFINITION.CONVERT(FILE_NAME) &
              " not Found");
	    raise FILE_NOT_FOUND;
	when others =>
	    TEXT_IO.PUT_LINE("Unexpected error with Include File " &
	      LINE_DEFINITION.CONVERT(FILE_NAME));
	    raise FILE_NOT_FOUND;
    end OPEN;
 
    procedure OPEN(FILE_NAME : in STRING) is
    begin
	OPEN(LINE_DEFINITION.CONVERT(FILE_NAME));
    end OPEN;
 
    -- Close the include file
    -- Exceptions which may be raised: FILE_NOT_OPEN
    procedure CLOSE is
    begin
	TEXT_IO.CLOSE(FD(CURRENT_LEVEL));
	CURRENT_LEVEL := CURRENT_LEVEL - 1;
	if CURRENT_LEVEL = 0 then
	    raise INCLUDE_FILE_EMPTY;
	end if;
    end CLOSE;
 
    -- Abort processing the include file
    procedure STOP is
    begin
	while CURRENT_LEVEL > 0 loop
	    TEXT_IO.CLOSE(FD(CURRENT_LEVEL));
	    CURRENT_LEVEL := CURRENT_LEVEL - 1;
	end loop;
    end STOP;
 
    -- Read a LINE containing a file name from the include file
    -- Exceptions which may be raised: FILE_NOT_OPEN, READ_PAST_END_OF_FILE
    procedure READ(TO : out LINE_DEFINITION.LINE) is
	INLINE : LINE_DEFINITION.LINE;
    begin
	loop
	    begin
		TEXT_IO.GET_LINE(FD(CURRENT_LEVEL), INLINE.CONTENT,
		  INLINE.LAST);
		if INLINE.LAST > 0 and INLINE.CONTENT(1) =
		  INCLUDE_CHARACTER then
		    OPEN(INLINE);
		elsif (INLINE.LAST > 0 and INLINE.CONTENT(1) = COMMENT_CHARACTER) or
		  (INLINE.LAST = 0) then
		    null;    -- skip comment lines and empty lines
		else
		    exit;
		end if;
	    exception
		when TEXT_IO.END_ERROR =>
		    CLOSE;
	    end;
	end loop;
	TO := INLINE;
    end READ;
 
end INCLUDE_FILE;
 
--===========================================================================
---------------------------- PROCEDURE PARSER -------------------------------
--===========================================================================
-- PARSER parses a LINE and returns the number of tokens in that LINE
-- and the first token as COMMAND (converted to lower-case) with the
-- rest of the tokens in ARGS (a linked list of argument LINEs)
 
with LINE_DEFINITION;
use  LINE_DEFINITION;
procedure PARSER(INLINE  : in LINE_DEFINITION.LINE;
		 NARGS   : out NATURAL;
		 COMMAND : out LINE_DEFINITION.LINE;
		 ARGS    : in out LINE_DEFINITION.LINE_LIST) is
 
    ROVER    : NATURAL;
    LROVER   : LINE_DEFINITION.LINE_LIST := null;
    LFIRST   : LINE_DEFINITION.LINE_LIST := null;
    LCOMMAND : LINE_DEFINITION.LINE;
    LTEMP    : LINE_DEFINITION.LINE;
    LARGS    : NATURAL                   := 0;
 
    procedure SKIP_SPACES is
    begin
	while INLINE.CONTENT(ROVER) <= ' ' and ROVER <= INLINE.LAST loop
	    ROVER := ROVER + 1;
	end loop;
    end SKIP_SPACES;
 
    procedure EXTRACT(ITEM : out LINE_DEFINITION.LINE) is
	EXTRACT_ROVER : NATURAL := 0;
    begin
	while INLINE.CONTENT(ROVER) > ' ' and ROVER <= INLINE.LAST loop
	    EXTRACT_ROVER := EXTRACT_ROVER + 1;
	    ITEM.CONTENT(EXTRACT_ROVER) := INLINE.CONTENT(ROVER);
	    ROVER := ROVER + 1;
	end loop;
	ITEM.LAST := EXTRACT_ROVER;
    end EXTRACT;
 
begin
    COMMAND.LAST := 0;
    ROVER := INLINE.CONTENT'FIRST;
    SKIP_SPACES;
    if ROVER <= INLINE.LAST then
	EXTRACT(LCOMMAND);
	LCOMMAND.LAST := LCOMMAND.LAST + 1;
	LCOMMAND.CONTENT(LCOMMAND.LAST) := ' ';
	COMMAND := LINE_DEFINITION.TOLOWER(LCOMMAND);
	LARGS := 1;
        LROVER := ARGS;
	while ROVER <= INLINE.LAST loop
	    SKIP_SPACES;
	    if ROVER <= INLINE.LAST then
		EXTRACT(LTEMP);
		if ARGS = null then
		    ARGS := new LINE_DEFINITION.LINE_LIST_ELEMENT;
		    LROVER := ARGS;
		    LROVER.NEXT := null;
		end if;
		LROVER.CONTENT := LTEMP;
		LARGS := LARGS + 1;
                if LROVER.NEXT = null then
                    LROVER.NEXT := new LINE_DEFINITION.LINE_LIST_ELEMENT;
                end if;
                LROVER := LROVER.NEXT;
	    end if;
	end loop;
    end if;
    NARGS := LARGS;
end PARSER;
 
--===========================================================================
---------------------------- PACKAGE PAGED_FILE -----------------------------
--===========================================================================
with LINE_DEFINITION;
package PAGED_FILE is

    procedure COMPUTE_CHECKSUM (NARGS   : in NATURAL;
                                ARGLIST : in LINE_DEFINITION.LINE_LIST);
    -- Compute the checksum of a paged file

    procedure MAKE_INCLUDE_FILE (NARGS   : in NATURAL;
                                 ARGLIST : in LINE_DEFINITION.LINE_LIST);
    -- Create an include file which names the elements of a paged file

    procedure LIST (NARGS   : in NATURAL;
                    ARGLIST : in LINE_DEFINITION.LINE_LIST);
    -- List the names of the elements of a paged file

    procedure CREATE (NARGS   : in NATURAL;
                      ARGLIST : in LINE_DEFINITION.LINE_LIST);
    -- Create a paged file

    procedure UNPAGE (NARGS   : in NATURAL;
                      ARGLIST : in LINE_DEFINITION.LINE_LIST);
    -- Extract the elements of a paged file

end PAGED_FILE;

with INCLUDE_FILE, INPUT_FILE, OUTPUT_FILE, PARSER;
with TEXT_IO;
package body PAGED_FILE is

    INLINE          : LINE_DEFINITION.LINE;
 
    --=======================================================================
    -- PAGED_FILE, Support Utilities
    --=======================================================================
 
    use  LINE_DEFINITION;

    -- Determine if ITEM contains a BANNER or COMMENT_BANNER
    function IS_BANNER(ITEM : in LINE_DEFINITION.LINE) return BOOLEAN is
	RESULT : BOOLEAN;
    begin
	if ITEM.LAST >= LINE_DEFINITION.BANNER'LENGTH and then
	  ITEM.CONTENT(1 .. LINE_DEFINITION.BANNER'LENGTH) =
	  LINE_DEFINITION.BANNER then
	    RESULT := TRUE;
	elsif ITEM.LAST >= LINE_DEFINITION.COMMENT_BANNER'LENGTH and then
	  ITEM.CONTENT(1 .. LINE_DEFINITION.COMMENT_BANNER'LENGTH) =
	  LINE_DEFINITION.COMMENT_BANNER then
	    RESULT := TRUE;
	else
	    RESULT := FALSE;
	end if;
	return RESULT;
    end IS_BANNER;
 
    -- Package to handle line counting
    package COUNTER is
 
        -- Reset the Counter
	procedure SET;
 
        -- Increment the Counter
	procedure INCREMENT;
 
        -- Print the counter
	procedure PRINT;
 
    end COUNTER;
 
    package body COUNTER is
 
	type LINE_COUNT is range 0 .. 10001;
	package LINE_COUNT_IO is new TEXT_IO.INTEGER_IO(LINE_COUNT);
 
	LCOUNT : LINE_COUNT;
 
        -- Reset the LCOUNT variable
	procedure SET is
	begin
	    LCOUNT := 0;
	end SET;
 
        -- Increment the LCOUNT variable
	procedure INCREMENT is
	begin
	    if LCOUNT < LINE_COUNT'LAST then
		LCOUNT := LCOUNT + 1;
	    end if;
	end INCREMENT;
 
        -- Print a count of the number of lines and reset the LCOUNT variable
	procedure PRINT is
	begin
	    TEXT_IO.PUT(" -- ");
	    if LCOUNT = LINE_COUNT'LAST then
		TEXT_IO.PUT("More Than" & LINE_COUNT'IMAGE(LINE_COUNT'LAST -
		  1));
	    else
		LINE_COUNT_IO.PUT(LCOUNT, 1);
	    end if;
	    TEXT_IO.PUT_LINE(" Lines");
	    LCOUNT := 0;
	end PRINT;
 
    end COUNTER;
 
    --=======================================================================
    -- PAGED_FILE, COMPUTE_CHECKSUM Command
    --=======================================================================
    procedure COMPUTE_CHECKSUM (NARGS   : in NATURAL;
                                ARGLIST : in LINE_DEFINITION.LINE_LIST) is
	CHECKSUM : INTEGER;
	package VALUE_IO is new TEXT_IO.INTEGER_IO(INTEGER);
    begin
	if NARGS = 1 then
	    TEXT_IO.PUT_LINE(" CHECK Command requires the name of a file");
	    TEXT_IO.PUT_LINE("   Syntax: list file_name");
	else
 
            -- Step 1: Open the input file
	    INPUT_FILE.OPEN(ARGLIST.CONTENT);
 
            -- Step 2: Compute the Hash (Checksum)
	    CHECKSUM := 0;
	    while not INPUT_FILE.END_OF_FILE loop
		INPUT_FILE.READ(INLINE);
		for I in 1 .. INLINE.LAST loop
		    if INLINE.CONTENT(I) > ' ' then
			CHECKSUM := CHECKSUM +
			  CHARACTER'POS(INLINE.CONTENT(I));
			if CHECKSUM >= 128 then
			    CHECKSUM := CHECKSUM - 128;
			end if;
		    end if;
		end loop;
	    end loop;
	    INPUT_FILE.CLOSE;
 
            -- Step 3: Print the result
	    TEXT_IO.PUT(" Pager Checksum (Hash) of " &
	      LINE_DEFINITION.CONVERT(ARGLIST.CONTENT) & " is ");
	    VALUE_IO.PUT(CHECKSUM, 1);
	    TEXT_IO.NEW_LINE;
 
	end if;
 
    exception
	when INPUT_FILE.FILE_NOT_FOUND =>
            TEXT_IO.PUT(" CHECK:");
	    TEXT_IO.PUT_LINE(" File " &
              LINE_DEFINITION.CONVERT(ARGLIST.CONTENT) &
	      " not Found");
	when INPUT_FILE.READ_PAST_END_OF_FILE =>
            TEXT_IO.PUT(" CHECK:");
	    TEXT_IO.PUT_LINE(" Premature EOF on " &
	      LINE_DEFINITION.CONVERT(ARGLIST.CONTENT));
	    INPUT_FILE.CLOSE;
	when others =>
            TEXT_IO.PUT(" CHECK:");
	    TEXT_IO.PUT_LINE(" Unexpected Error");
	    INPUT_FILE.CLOSE;
 
    end COMPUTE_CHECKSUM;
 
    --=======================================================================
    -- PAGED_FILE, MAKE_INCLUDE_FILE Command
    --=======================================================================
    procedure MAKE_INCLUDE_FILE (NARGS   : in NATURAL;
                                 ARGLIST : in LINE_DEFINITION.LINE_LIST) is
	IN_FILE   : BOOLEAN;
        ARG_ROVER : LINE_DEFINITION.LINE_LIST;
    begin
	if NARGS < 3 then
	    TEXT_IO.PUT_LINE
              (" INCLUDE Command requires the name of a paged file");
	    TEXT_IO.PUT_LINE
              ("   Syntax: include paged_file_name output_include_file");
	else
 
            -- Step 1: Open the input and output files
	    COUNTER.SET;
	    ARG_ROVER := ARGLIST.NEXT;
	    INPUT_FILE.OPEN(ARGLIST.CONTENT);
	    OUTPUT_FILE.OPEN(ARG_ROVER.CONTENT);
	    OUTPUT_FILE.WRITE("-- Include file for " &
	      LINE_DEFINITION.CONVERT(ARGLIST.CONTENT));
 
            -- Step 2: Look for the first banner in the paged file
	    IN_FILE := TRUE;
	    while not INPUT_FILE.END_OF_FILE loop
		INPUT_FILE.READ(INLINE);
		if IS_BANNER(INLINE) then
		    IN_FILE := FALSE;
		    exit;
		end if;
	    end loop;
 
            -- Step 3: If first banner not found, issue error message,
            --         else process component files
	    if IN_FILE then
		TEXT_IO.PUT_LINE
                  (" File " & LINE_DEFINITION.CONVERT(ARGLIST.CONTENT) &
		  " does not contain any components");
	    else
 
                -- Loop until the end of the input paged file
		while not INPUT_FILE.END_OF_FILE loop
 
                    -- Read the next line from the input paged file
		    INPUT_FILE.READ(INLINE);
 
                    -- If we are not in the text of the file, the line just
                    -- read contains the name of a new file, else it contains
                    -- a line of the current component file
		    if not IN_FILE then
 
                    -- Remove leading comment character if any and print the
                    -- name of the component file
			if INLINE.CONTENT(1 .. 2) = "--" then
			    TEXT_IO.PUT(" " &
			      INLINE.CONTENT(3 .. INLINE.LAST));
			    OUTPUT_FILE.WRITE
                              (INLINE.CONTENT(3 .. INLINE.LAST));
			else
			    TEXT_IO.PUT(" " &
			      INLINE.CONTENT(1 .. INLINE.LAST));
			    OUTPUT_FILE.WRITE
                              (INLINE.CONTENT(1 .. INLINE.LAST));
			end if;
 
                        -- Flush the trailing banner line and note that we are
                        -- now within the text of a component file
			INPUT_FILE.READ(INLINE);
			COUNTER.SET;
			IN_FILE := TRUE;
 
		    else
 
                    -- We are within the text of a component file, so check
                    -- for a banner in order to determine if we are at the end
                    -- of the component file
			if IS_BANNER(INLINE) then
			    IN_FILE := FALSE;
			    COUNTER.PRINT;
			else
			    COUNTER.INCREMENT;
			end if;
 
		    end if;
 
		end loop;
 
	    end if;
 
	    COUNTER.PRINT;
	    INPUT_FILE.CLOSE;
	    OUTPUT_FILE.CLOSE;
 
	end if;
 
    exception
	when OUTPUT_FILE.CANNOT_CREATE_FILE =>
            TEXT_IO.PUT(" INCLUDE:");
	    TEXT_IO.PUT_LINE(" Cannot create " &
	      LINE_DEFINITION.CONVERT(ARG_ROVER.CONTENT));
	when INPUT_FILE.FILE_NOT_FOUND =>
            TEXT_IO.PUT(" INCLUDE:");
	    TEXT_IO.PUT_LINE
              (" File " & LINE_DEFINITION.CONVERT(ARGLIST.CONTENT) &
	      " not Found");
	when INPUT_FILE.READ_PAST_END_OF_FILE =>
            TEXT_IO.PUT(" INCLUDE:");
	    TEXT_IO.PUT_LINE(" Premature EOF on " &
	      LINE_DEFINITION.CONVERT(ARGLIST.CONTENT));
	    INPUT_FILE.CLOSE;
	when others =>
            TEXT_IO.PUT(" INCLUDE:");
	    TEXT_IO.PUT_LINE(" Unexpected Error");
	    INPUT_FILE.CLOSE;
 
    end MAKE_INCLUDE_FILE;
 
    --=======================================================================
    -- PAGED_FILE, LIST Command
    --=======================================================================
    procedure LIST (NARGS   : in NATURAL;
                    ARGLIST : in LINE_DEFINITION.LINE_LIST) is
	IN_FILE : BOOLEAN;
    begin
	if NARGS = 1 then
	    TEXT_IO.PUT_LINE
              (" LIST Command requires the name of a paged file");
	    TEXT_IO.PUT_LINE
              ("   Syntax: list paged_file_name");
	else
 
            -- Step 1: Open the input file
	    COUNTER.SET;
	    INPUT_FILE.OPEN(ARGLIST.CONTENT);
 
            -- Step 2: Look for the first banner in the paged file
	    IN_FILE := TRUE;
	    while not INPUT_FILE.END_OF_FILE loop
		INPUT_FILE.READ(INLINE);
		if IS_BANNER(INLINE) then
		    IN_FILE := FALSE;
		    exit;
		end if;
	    end loop;
 
            -- Step 3: If first banner not found, issue error message,
            --         else process component files
	    if IN_FILE then
		TEXT_IO.PUT_LINE
                  (" File " & LINE_DEFINITION.CONVERT(ARGLIST.CONTENT) &
		  " does not contain any components");
	    else
 
                -- Loop until the end of the input paged file
		while not INPUT_FILE.END_OF_FILE loop
 
                    -- Read the next line from the input paged file
		    INPUT_FILE.READ(INLINE);
 
                    -- If we are not in the text of the file, the line just
                    -- read contains the name of a new file, else it contains
                    -- a line of the current component file
		    if not IN_FILE then
 
                        -- Remove leading comment character if any and print
                        -- the name of the component file
			if INLINE.CONTENT(1 .. 2) = "--" then
			    TEXT_IO.PUT(" " &
			      INLINE.CONTENT(3 .. INLINE.LAST));
			else
			    TEXT_IO.PUT(" " &
			      INLINE.CONTENT(1 .. INLINE.LAST));
			end if;
 
                        -- Flush the trailing banner line and note that we are
                        -- now within the text of a component file
			INPUT_FILE.READ(INLINE);
			COUNTER.SET;
			IN_FILE := TRUE;
 
		    else
 
                        -- We are within the text of a component file, so
                        -- check for a banner in order to determine if we
                        -- are at the end of the component file
			if IS_BANNER(INLINE) then
			    IN_FILE := FALSE;
			    COUNTER.PRINT;
			else
			    COUNTER.INCREMENT;
			end if;
 
		    end if;
 
		end loop;
 
	    end if;
 
	    COUNTER.PRINT;
	    INPUT_FILE.CLOSE;
 
	end if;
 
    exception
	when INPUT_FILE.FILE_NOT_FOUND =>
            TEXT_IO.PUT(" LIST:");
	    TEXT_IO.PUT_LINE
              (" File " & LINE_DEFINITION.CONVERT(ARGLIST.CONTENT) &
	      " not Found");
	when INPUT_FILE.READ_PAST_END_OF_FILE =>
            TEXT_IO.PUT(" LIST:");
	    TEXT_IO.PUT_LINE(" Premature EOF on " &
	      LINE_DEFINITION.CONVERT(ARGLIST.CONTENT));
	    INPUT_FILE.CLOSE;
	when others =>
            TEXT_IO.PUT(" LIST:");
	    TEXT_IO.PUT_LINE(" Unexpected Error");
	    INPUT_FILE.CLOSE;
 
    end LIST;
 
    --=======================================================================
    -- PAGED_FILE, CREATE Command
    --=======================================================================
    procedure CREATE (NARGS   : in NATURAL;
                      ARGLIST : in LINE_DEFINITION.LINE_LIST) is
	COMPONENT_FILE_NAME : LINE_DEFINITION.LINE;
	OUTPUT_FILE_NAME    : LINE_DEFINITION.LINE;
        ARG_ROVER           : LINE_DEFINITION.LINE_LIST;
    begin
	if NARGS < 3 then
	    TEXT_IO.PUT_LINE
              (" PAGE Command requires the name of the paged file and include file");
	    TEXT_IO.PUT_LINE
              ("   Syntax: page [@include_file_name|file_name]+ paged_file_name");
	else
	    ARG_ROVER := ARGLIST;
            for I in 1 .. NARGS-2 loop
		ARG_ROVER := ARG_ROVER.NEXT;
	    end loop;
	    OUTPUT_FILE_NAME := ARG_ROVER.CONTENT;
	    OUTPUT_FILE.OPEN(OUTPUT_FILE_NAME);
	    ARG_ROVER := ARGLIST;
	    for I in 1 .. NARGS-2 loop
		if ARG_ROVER.CONTENT.CONTENT(1) =
		  INCLUDE_FILE.INCLUDE_CHARACTER then
		    INCLUDE_FILE.OPEN
                      (LINE_DEFINITION.CONVERT(ARG_ROVER.CONTENT));
		    begin
			loop
			    INCLUDE_FILE.READ(COMPONENT_FILE_NAME);
			    INPUT_FILE.OPEN(COMPONENT_FILE_NAME);
			    OUTPUT_FILE.WRITE(LINE_DEFINITION.COMMENT_BANNER);
			    OUTPUT_FILE.WRITE("--" &
			      LINE_DEFINITION.CONVERT(COMPONENT_FILE_NAME));
			    OUTPUT_FILE.WRITE(LINE_DEFINITION.COMMENT_BANNER);
			    TEXT_IO.PUT(" Adding " &
			      LINE_DEFINITION.CONVERT(COMPONENT_FILE_NAME));
			    COUNTER.SET;
			    while not INPUT_FILE.END_OF_FILE loop
				INPUT_FILE.READ(INLINE);
				OUTPUT_FILE.WRITE(INLINE);
				COUNTER.INCREMENT;
			    end loop;
			    COUNTER.PRINT;
			    INPUT_FILE.CLOSE;
			end loop;
		    exception
			when INCLUDE_FILE.READ_PAST_END_OF_FILE |
			  INCLUDE_FILE.INCLUDE_FILE_EMPTY |
                          INCLUDE_FILE.NESTING_LEVEL_EXCEEDED =>
                            INCLUDE_FILE.STOP;
			when INPUT_FILE.FILE_NOT_FOUND =>
			    TEXT_IO.PUT_LINE(" File " &
			      LINE_DEFINITION.CONVERT(COMPONENT_FILE_NAME) &
			      " not Found");
			    INCLUDE_FILE.STOP;
			when others =>
			    TEXT_IO.PUT_LINE
                              (" Unexpected Error During Processing " &
                              "of Component File " &
			      LINE_DEFINITION.CONVERT(COMPONENT_FILE_NAME));
			    INCLUDE_FILE.STOP;
		    end;
		else
		    INPUT_FILE.OPEN(ARG_ROVER.CONTENT);
		    OUTPUT_FILE.WRITE(LINE_DEFINITION.COMMENT_BANNER);
		    OUTPUT_FILE.WRITE("--" &
		      LINE_DEFINITION.CONVERT(ARG_ROVER.CONTENT));
		    OUTPUT_FILE.WRITE(LINE_DEFINITION.COMMENT_BANNER);
		    TEXT_IO.PUT(" Adding " &
		      LINE_DEFINITION.CONVERT(ARG_ROVER.CONTENT));
		    COUNTER.SET;
		    while not INPUT_FILE.END_OF_FILE loop
			INPUT_FILE.READ(INLINE);
			OUTPUT_FILE.WRITE(INLINE);
			COUNTER.INCREMENT;
		    end loop;
		    COUNTER.PRINT;
		    INPUT_FILE.CLOSE;
		end if;
                ARG_ROVER := ARG_ROVER.NEXT;
	    end loop;
            OUTPUT_FILE.CLOSE;
	end if;
 
    exception
	when OUTPUT_FILE.CANNOT_CREATE_FILE =>
            TEXT_IO.PUT(" PAGE:");
	    TEXT_IO.PUT_LINE(" Cannot create " &
	      LINE_DEFINITION.CONVERT(OUTPUT_FILE_NAME));
	when INCLUDE_FILE.FILE_NOT_FOUND =>
            TEXT_IO.PUT(" PAGE:");
	    TEXT_IO.PUT_LINE(" Cannot open include file");
	when others =>
            TEXT_IO.PUT(" PAGE:");
	    TEXT_IO.PUT_LINE(" Unexpected Error");
	    INPUT_FILE.CLOSE;
 
    end CREATE;
 
    --=======================================================================
    -- PAGED_FILE, UNPAGE Command
    --=======================================================================
    procedure UNPAGE (NARGS   : in NATURAL;
                      ARGLIST : in LINE_DEFINITION.LINE_LIST) is
	IN_FILE          : BOOLEAN;
	OUTPUT_FILE_NAME : LINE_DEFINITION.LINE;
    begin
	if NARGS = 1 then
	    TEXT_IO.PUT_LINE
              (" UNPAGE Command requires the name of a paged file");
	    TEXT_IO.PUT_LINE("   Syntax: unpage paged_file_name");
	else
 
            -- Step 1: Open the input file
	    COUNTER.SET;
	    INPUT_FILE.OPEN(ARGLIST.CONTENT);
 
            -- Step 2: Look for the first banner in the paged file
	    IN_FILE := TRUE;
	    while not INPUT_FILE.END_OF_FILE loop
		INPUT_FILE.READ(INLINE);
		if IS_BANNER(INLINE) then
		    IN_FILE := FALSE;
		    exit;
		end if;
	    end loop;
 
            -- Step 3: If first banner not found, issue error message,
            --         else process component files
	    if IN_FILE then
		TEXT_IO.PUT_LINE(" File " &
                  LINE_DEFINITION.CONVERT(ARGLIST.CONTENT) &
		  " does not contain any components");
	    else
 
                -- Loop until the end of the input paged file
		while not INPUT_FILE.END_OF_FILE loop
 
                    -- Read the next line from the input paged file
		    INPUT_FILE.READ(INLINE);
 
                    -- If we are not in the text of the file, the line just
                    -- read contains the name of a new file, else it contains
                    -- a line of the current component file
		    if not IN_FILE then
 
                        -- Remove leading comment character if any and
                        -- store the name of the component file
			if INLINE.CONTENT(1 .. 2) = "--" then
			    OUTPUT_FILE_NAME :=
			      LINE_DEFINITION.CONVERT
                                (INLINE.CONTENT(3 .. INLINE.LAST));
			else
			    OUTPUT_FILE_NAME :=
			      LINE_DEFINITION.CONVERT
                                (INLINE.CONTENT(1 .. INLINE.LAST));
			end if;
 
                        -- Open the new component file
			OUTPUT_FILE.OPEN(OUTPUT_FILE_NAME);
			TEXT_IO.PUT(" Extracting " &
			  LINE_DEFINITION.CONVERT(OUTPUT_FILE_NAME));
 
                        -- Flush the trailing banner line and note that we are
                        -- now within the text of a component file
			INPUT_FILE.READ(INLINE);
			IN_FILE := TRUE;
			COUNTER.SET;
 
		    else
 
                        -- We are within the text of a component file, so
                        -- check for a banner in order to determine if we
                        -- are at the end of the component file
			if IS_BANNER(INLINE) then
			    OUTPUT_FILE.CLOSE;
			    IN_FILE := FALSE;
			    COUNTER.PRINT;
			else
			    OUTPUT_FILE.WRITE(INLINE);
			    COUNTER.INCREMENT;
			end if;
 
		    end if;
 
		end loop;
 
		OUTPUT_FILE.CLOSE;
 
	    end if;
 
	    COUNTER.PRINT;
	    INPUT_FILE.CLOSE;
 
	end if;
 
    exception
	when OUTPUT_FILE.CANNOT_CREATE_FILE =>
            TEXT_IO.PUT(" UNPAGE:");
	    TEXT_IO.PUT_LINE(" Cannot create " &
	      LINE_DEFINITION.CONVERT(OUTPUT_FILE_NAME));
	when INPUT_FILE.FILE_NOT_FOUND =>
            TEXT_IO.PUT(" UNPAGE:");
	    TEXT_IO.PUT_LINE(" File " &
              LINE_DEFINITION.CONVERT(ARGLIST.CONTENT) &
	      " not Found");
	when INPUT_FILE.READ_PAST_END_OF_FILE =>
            TEXT_IO.PUT(" UNPAGE:");
	    TEXT_IO.PUT_LINE(" Premature EOF on " &
	      LINE_DEFINITION.CONVERT(ARGLIST.CONTENT));
	    INPUT_FILE.CLOSE;
	when others =>
            TEXT_IO.PUT(" UNPAGE:");
	    TEXT_IO.PUT_LINE(" Unexpected Error");
	    INPUT_FILE.CLOSE;
 
    end UNPAGE;
 
end PAGED_FILE;

--===========================================================================
--------------------------------- MAINLINE ----------------------------------
--===========================================================================
with LINE_DEFINITION, PAGED_FILE, PARSER;
use  LINE_DEFINITION;
with TEXT_IO;
with CLI;
procedure PAGER2 is
 
    TITLE           : constant STRING := "PAGER2, Ada Version 1.1";
 
    INLINE          : LINE_DEFINITION.LINE;
 
    NARGS           : NATURAL;
    COMMAND         : LINE_DEFINITION.LINE;
    ARGLIST         : LINE_DEFINITION.LINE_LIST;
    ARG_ROVER       : LINE_DEFINITION.LINE_LIST;
 
    -- Command Verbs
    HELP_COMMAND    : constant STRING := "help ";
    H_COMMAND       : constant STRING := "h ";
    EXIT_COMMAND    : constant STRING := "exit ";
    X_COMMAND       : constant STRING := "x ";    -- same as exit
    CHECK_COMMAND   : constant STRING := "check ";
    C_COMMAND       : constant STRING := "c ";    -- same as check
    INCLUDE_COMMAND : constant STRING := "include ";
    I_COMMAND       : constant STRING := "i ";    -- same as include
    LIST_COMMAND    : constant STRING := "list ";
    L_COMMAND       : constant STRING := "l ";    -- same as list
    PAGE_COMMAND    : constant STRING := "page ";
    P_COMMAND       : constant STRING := "p ";    -- same as page
    UNPAGE_COMMAND  : constant STRING := "unpage ";
    U_COMMAND       : constant STRING := "u ";    -- same as unpage
 
    --=======================================================================
    -- PAGER2, Support Utilities
    --=======================================================================
 
    -- Determine if COMMAND contains one of the two target command strings
    function IS_COMMAND(TARGET1_COMMAND, TARGET2_COMMAND : in STRING)
			return BOOLEAN is
        START : NATURAL;
    begin
        if COMMAND.CONTENT(1) = '-' then
            START := 2;
        else
            START := 1;
        end if;
	if COMMAND.CONTENT(START .. TARGET1_COMMAND'LENGTH + START - 1)
              = TARGET1_COMMAND or
	  COMMAND.CONTENT(START .. TARGET2_COMMAND'LENGTH + START - 1)
              = TARGET2_COMMAND then
	    return TRUE;
	else
	    return FALSE;
	end if;
    end IS_COMMAND;
 
    --=======================================================================
    -- PAGER2, HELP Command
    --=======================================================================
    procedure HELP is
	procedure SPACER is
	begin
	    TEXT_IO.PUT("                  ");
	end SPACER;
    begin
	TEXT_IO.PUT_LINE(" Command Summary");
	TEXT_IO.PUT_LINE("  help or h   - this summary");
	SPACER;
	TEXT_IO.PUT_LINE("Syntax: help");
	TEXT_IO.PUT_LINE("  exit or x   - exit from program");
	SPACER;
	TEXT_IO.PUT_LINE("Syntax: exit");
	TEXT_IO.PUT_LINE
          ("  include or i- list components into an include file");
	SPACER;
	TEXT_IO.PUT_LINE
          ("Syntax: include paged_file_name output_include_file");
	TEXT_IO.PUT_LINE("  list or l   - list components of paged file");
	SPACER;
	TEXT_IO.PUT_LINE("Syntax: list paged_file_name");
	TEXT_IO.PUT_LINE
          ("  page or p   - create paged file from include file");
	SPACER;
	TEXT_IO.PUT_LINE
          ("Syntax: page [@include_file_name|file_name]+ paged_file_name");
	TEXT_IO.PUT_LINE
          ("  unpage or u - extract components from paged file");
	SPACER;
	TEXT_IO.PUT_LINE("Syntax: unpage paged_file_name");
    end HELP;
 
--=======================================================================
-- PAGER2, Mainline
--=======================================================================
begin
    CLI.INITIALIZE ("PAGER2", "Enter verb and arguments: ");

    -- Interactive mode if no arguments
    if CLI.ARGC = 1 then
	TEXT_IO.PUT_LINE(TITLE);
	TEXT_IO.PUT_LINE("Type 'h' for Help");
	loop
	    begin
		TEXT_IO.PUT("PAGER2> ");
		TEXT_IO.GET_LINE(INLINE.CONTENT, INLINE.LAST);
		PARSER(INLINE, NARGS, COMMAND, ARGLIST);
		if NARGS > 0 then
		    exit when IS_COMMAND(EXIT_COMMAND, X_COMMAND);
		    if IS_COMMAND(HELP_COMMAND, H_COMMAND) then
			HELP;
		    elsif IS_COMMAND(CHECK_COMMAND, C_COMMAND) then
			PAGED_FILE.COMPUTE_CHECKSUM (NARGS, ARGLIST);
		    elsif IS_COMMAND(INCLUDE_COMMAND, I_COMMAND) then
			PAGED_FILE.MAKE_INCLUDE_FILE (NARGS, ARGLIST);
		    elsif IS_COMMAND(LIST_COMMAND, L_COMMAND) then
			PAGED_FILE.LIST (NARGS, ARGLIST);
		    elsif IS_COMMAND(PAGE_COMMAND, P_COMMAND) then
			PAGED_FILE.CREATE (NARGS, ARGLIST);
		    elsif IS_COMMAND(UNPAGE_COMMAND, U_COMMAND) then
			PAGED_FILE.UNPAGE (NARGS, ARGLIST);
		    else
			TEXT_IO.PUT_LINE(" Invalid Command: " &
			  LINE_DEFINITION.CONVERT(COMMAND));
		    end if;
		end if;
	    exception
		when others =>
		    null;
	    end;
	end loop;
    -- Non-interactive mode if one or more arguments
    else
	COMMAND := TOLOWER(LINE_DEFINITION.CONVERT(CLI.ARGV(1) & " "));
	NARGS := CLI.ARGC - 1;
	ARGLIST := null;
	for I in 2 .. CLI.ARGC - 1 loop
	    if I = 2 then
		ARGLIST := new LINE_DEFINITION.LINE_LIST_ELEMENT;
		ARG_ROVER := ARGLIST;
	    else
		ARG_ROVER.NEXT := new LINE_DEFINITION.LINE_LIST_ELEMENT;
		ARG_ROVER := ARG_ROVER.NEXT;
	    end if;
	    ARG_ROVER.NEXT := null;
	    ARG_ROVER.CONTENT := LINE_DEFINITION.CONVERT(CLI.ARGV(I));
	end loop;
	if NARGS > 0 then
	    if IS_COMMAND(HELP_COMMAND, H_COMMAND) then
		HELP;
	    elsif IS_COMMAND(CHECK_COMMAND, C_COMMAND) then
		PAGED_FILE.COMPUTE_CHECKSUM (NARGS, ARGLIST);
	    elsif IS_COMMAND(INCLUDE_COMMAND, I_COMMAND) then
		PAGED_FILE.MAKE_INCLUDE_FILE (NARGS, ARGLIST);
	    elsif IS_COMMAND(LIST_COMMAND, L_COMMAND) then
		PAGED_FILE.LIST (NARGS, ARGLIST);
	    elsif IS_COMMAND(PAGE_COMMAND, P_COMMAND) then
		PAGED_FILE.CREATE (NARGS, ARGLIST);
	    elsif IS_COMMAND(UNPAGE_COMMAND, U_COMMAND) then
		PAGED_FILE.UNPAGE (NARGS, ARGLIST);
	    elsif IS_COMMAND(EXIT_COMMAND, X_COMMAND) then
		null;
	    else
		TEXT_IO.PUT_LINE(" Invalid Command: " &
		  LINE_DEFINITION.CONVERT(COMMAND));
	    end if;
	end if;
    end if;
exception
    when others =>
	null;
end PAGER2;
