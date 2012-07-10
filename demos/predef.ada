-- 
-- 
--               ********************************** 
--               *                                *  
--               *           T  e  x  t           * 
--               *                                *  
--               *     Input / Output  Package    * 
--		 *				  *
--		 *	     and other		  *
--		 *				  *
--		 *        Predefined Units	  *
--               *                                *  
--               *                                *  
--		 *	     ADA Project	  *
--		 *	  Courant Institute	  *
--		 *	 New York University	  *
--		 *	  251 Mercer Street,	  *
--		 *	  New York, NY 10012	  *
--               *                                *  
--               ********************************** 
-- 
-- 
--                               by 
--  
--                         Clinton F. Goss 
-- 			  Tracey M. Siesser
--                        Bernard D. Banner
--			    Gerry Fisher
--			  Stephen C. Bryant
-- 
-- 
-- 
-- 
-- 
-- 
--  This file contains several of the predefined Ada package spec-
--  ifications.  They do not actually implement the package's
--  operations, which are coded in the implementation language SETL,
--  provide an interface to them through the standard procedure/
--  function calling mechanism.  The predefined packages are:
--
--      . The SYSTEM package.
--
--      . The IO_EXCEPTIONS package.
--
--  	. The generic SEQUENTIAL_IO package.
--
--      . The generic DIRECT_IO package.
-- 
--  	. The TEXT_IO package.  
--
--	. The CALENDAR package and the predefined subprograms 
--	  UNCHECKED_CONVERSION and UNCHECKED_DEALLOCATION.
--
package SYSTEM is

   type NAME    is (ADA_ED); 
   type ADDRESS is new INTEGER;

   SYSTEM_NAME  : constant NAME := ADA_ED;
   STORAGE_UNIT : constant      := 32;
   MEMORY_SIZE  : constant      := 2**30 - 1;

   -- System Dependent Named Numbers:

   MIN_INT      : constant      := -(2**30 - 1);
   MAX_INT      : constant      := 2**30 - 1;
   MAX_DIGITS   : constant      := 6;
   MAX_MANTISSA : constant      := 1000;
   FINE_DELTA   : constant      := 2.0 ** (-30);
   TICK         : constant      := 0.01;

   -- Other System Dependent Declarations

   subtype PRIORITY is INTEGER range 0 .. 9;

   SYSTEM_ERROR : exception;

end SYSTEM;

package IO_EXCEPTIONS is

   STATUS_ERROR : exception;
   MODE_ERROR   : exception;
   NAME_ERROR   : exception;
   USE_ERROR    : exception;
   DEVICE_ERROR : exception;
   END_ERROR    : exception;
   DATA_ERROR   : exception;
   LAYOUT_ERROR : exception;
end IO_EXCEPTIONS;

with IO_EXCEPTIONS;
generic
    type ELEMENT_TYPE is private;

package SEQUENTIAL_IO is

    type FILE_TYPE is limited private;
    
    type FILE_MODE is (IN_FILE, OUT_FILE);
      

    -- File management


    procedure CREATE   (FILE : in out FILE_TYPE;
                        MODE : in FILE_MODE := OUT_FILE;
                        NAME : in STRING    := "";
                        FORM : in STRING    := "");

    procedure OPEN     (FILE : in out FILE_TYPE;
                        MODE : in FILE_MODE;
                        NAME : in STRING;
                        FORM : in STRING := "");

    procedure CLOSE    (FILE : in out FILE_TYPE);

    procedure DELETE   (FILE : in out FILE_TYPE);

    procedure RESET    (FILE : in out FILE_TYPE; MODE : in  FILE_MODE);
    procedure RESET    (FILE : in out FILE_TYPE);

    function  MODE     (FILE : in FILE_TYPE)  return FILE_MODE;

    function  NAME     (FILE : in FILE_TYPE)  return STRING;

    function  FORM     (FILE : in FILE_TYPE)  return STRING;
    
    function  IS_OPEN  (FILE : in FILE_TYPE)  return BOOLEAN;

    -- Input and Output Operations:

    procedure READ   (FILE : in FILE_TYPE; ITEM : out ELEMENT_TYPE);

    procedure WRITE  (FILE : in FILE_TYPE; ITEM : in ELEMENT_TYPE);

    function  END_OF_FILE(FILE : in FILE_TYPE) return BOOLEAN;

    -- Exceptions:

    STATUS_ERROR : exception renames IO_EXCEPTIONS.STATUS_ERROR;
    MODE_ERROR   : exception renames IO_EXCEPTIONS.MODE_ERROR;
    NAME_ERROR	 : exception renames IO_EXCEPTIONS.NAME_ERROR;
    USE_ERROR	 : exception renames IO_EXCEPTIONS.USE_ERROR;
    DEVICE_ERROR : exception renames IO_EXCEPTIONS.DEVICE_ERROR;
    END_ERROR	 : exception renames IO_EXCEPTIONS.END_ERROR;
    DATA_ERROR	 : exception renames IO_EXCEPTIONS.DATA_ERROR;

private

    type  FILE_TYPE  is 
      record
        FILE_NUM : INTEGER := 0;
      end record;

end SEQUENTIAL_IO;


package body SEQUENTIAL_IO is


    -- The body for each procedure and function consists of an
    -- interface pragma which generates an AIS instruction of
    -- the form:
    --
    --		['predef_', specifier, [formal, formal, ...]]
    --
    -- where the specifier is the second argument to the pragma
    -- in upper case, and the formals are the fully qualified
    -- names of the formal parameters to the subprogram.  The
    -- specifier is used by the SETL INPUT_OUTPUT routines in
    -- determining which routine was called, and the formals are
    -- used for accessing and setting the values of the arguments
    -- to the subprogram.


    -- File management


    procedure CREATE (FILE : in out FILE_TYPE;
                      MODE : in FILE_MODE := OUT_FILE;
                      NAME : in STRING    := "";
                      FORM : in STRING    := "") is
    begin
    	pragma io_interface (PREDEF, SIO_CREATE, ELEMENT_TYPE);  null;
    end CREATE;


    procedure OPEN (FILE : in out FILE_TYPE;
                    MODE : in FILE_MODE;
                    NAME : in STRING;
                    FORM : in STRING := "") is
    begin
    	pragma io_interface (PREDEF, SIO_OPEN, ELEMENT_TYPE);  null;
    end OPEN;


    procedure CLOSE (FILE : in out FILE_TYPE) is
    begin
    	pragma io_interface (PREDEF, SIO_CLOSE);  null;
    end CLOSE;


    procedure DELETE (FILE : in out FILE_TYPE) is
    begin
    	pragma io_interface (PREDEF, SIO_DELETE);  null;
    end DELETE;

    procedure RESET  (FILE : in out FILE_TYPE; MODE : in FILE_MODE) is
    begin
        pragma io_interface (PREDEF, SIO_RESET_MODE);  null;
    end RESET;
    
    procedure RESET  (FILE : in out FILE_TYPE) is
    begin
        pragma io_interface (PREDEF, SIO_RESET);  null;
    end RESET;

    function  MODE   (FILE : in FILE_TYPE) return FILE_MODE is
    begin
        pragma io_interface (PREDEF, SIO_MODE);  null;
    end MODE;

    function  NAME   (FILE : in FILE_TYPE) return STRING is
    begin
    	pragma io_interface (PREDEF, SIO_NAME);  null;
    end NAME;

    function  FORM   (FILE : in FILE_TYPE) return STRING is
    begin
        pragma io_interface (PREDEF, SIO_FORM);  null;
    end FORM;
    
    function  IS_OPEN(FILE : in FILE_TYPE) return BOOLEAN is
    begin
    	pragma io_interface (PREDEF, SIO_IS_OPEN);  null;
    end IS_OPEN;



    -- Input and Output Operations:


    procedure READ (FILE : in FILE_TYPE; ITEM : out ELEMENT_TYPE) is
    begin
    	pragma io_interface (PREDEF, SIO_READ, ELEMENT_TYPE);  null;
    end READ;


    procedure WRITE (FILE : in FILE_TYPE; ITEM : in ELEMENT_TYPE) is
    begin
    	pragma io_interface (PREDEF, SIO_WRITE);  null;
    end WRITE;


    function  END_OF_FILE (FILE : in FILE_TYPE) return BOOLEAN is
    begin
    	pragma io_interface (PREDEF, SIO_END_OF_FILE);  null;
    end END_OF_FILE;


end SEQUENTIAL_IO;

with IO_EXCEPTIONS;
generic
    type ELEMENT_TYPE is private;

package DIRECT_IO is

    type  FILE_TYPE  is limited private;

    type    FILE_MODE       is (IN_FILE, INOUT_FILE, OUT_FILE);
    type    COUNT           is range 0 .. INTEGER'LAST;
    subtype POSITIVE_COUNT  is COUNT range 1 .. COUNT'LAST;    
      

    -- File management


    procedure CREATE   (FILE : in out FILE_TYPE;
                        MODE : in FILE_MODE := INOUT_FILE;
                        NAME : in STRING := "";
                        FORM : in STRING := "");

    procedure OPEN     (FILE : in out FILE_TYPE;
                        MODE : in FILE_MODE;
                        NAME : in STRING;
                        FORM : in STRING := "");

    procedure CLOSE    (FILE : in out FILE_TYPE);

    procedure DELETE   (FILE : in out FILE_TYPE);

    procedure RESET    (FILE : in out FILE_TYPE; MODE : in  FILE_MODE);
    procedure RESET    (FILE : in out FILE_TYPE);

    function  MODE     (FILE : in FILE_TYPE)  return FILE_MODE;

    function  NAME     (FILE : in FILE_TYPE)  return STRING;

    function  FORM     (FILE : in FILE_TYPE)  return STRING;
    
    function  IS_OPEN  (FILE : in FILE_TYPE)  return BOOLEAN;

    -- Input and Output Operations:

    procedure READ   (FILE : in FILE_TYPE; ITEM : out ELEMENT_TYPE);
    procedure READ   (FILE : in FILE_TYPE; ITEM : out ELEMENT_TYPE;
                                           FROM : in POSITIVE_COUNT);

    procedure WRITE  (FILE : in FILE_TYPE;  ITEM : in ELEMENT_TYPE);
    procedure WRITE  (FILE : in FILE_TYPE;  ITEM : in ELEMENT_TYPE;
                                            TO   : in POSITIVE_COUNT);

    procedure SET_INDEX(FILE : in FILE_TYPE; TO :in POSITIVE_COUNT);
   
    function  INDEX    (FILE : in FILE_TYPE)  return POSITIVE_COUNT;

    function  SIZE     (FILE : in FILE_TYPE)  return COUNT;
      
    function  END_OF_FILE(FILE : in FILE_TYPE) return BOOLEAN;

    -- Exceptions:

    STATUS_ERROR : exception renames IO_EXCEPTIONS.STATUS_ERROR;
    MODE_ERROR   : exception renames IO_EXCEPTIONS.MODE_ERROR;
    NAME_ERROR	 : exception renames IO_EXCEPTIONS.NAME_ERROR;
    USE_ERROR	 : exception renames IO_EXCEPTIONS.USE_ERROR;
    DEVICE_ERROR : exception renames IO_EXCEPTIONS.DEVICE_ERROR;
    END_ERROR	 : exception renames IO_EXCEPTIONS.END_ERROR;
    DATA_ERROR	 : exception renames IO_EXCEPTIONS.DATA_ERROR;

private

    type  FILE_TYPE  is 
      record
        FILE_NUM : INTEGER := 0;
      end record;

end DIRECT_IO;


package body DIRECT_IO is


    -- The body for each procedure and function consists of an
    -- interface pragma which generates an AIS instruction of
    -- the form:
    --
    --		['predef_', specifier, [formal, formal, ...]]
    --
    -- where the specifier is the second argument to the pragma
    -- in upper case, and the formals are the fully qualified
    -- names of the formal parameters to the subprogram.  The
    -- specifier is used by the SETL INPUT_OUTPUT routines in
    -- determining which routine was called, and the formals are
    -- used for accessing and setting the values of the arguments
    -- to the subprogram.



    -- File management


    procedure CREATE (FILE : in out FILE_TYPE;
                      MODE : in  FILE_MODE := INOUT_FILE;
                      NAME : in  STRING := "";
                      FORM : in  STRING := "") is
    begin
    	pragma io_interface (PREDEF, DIO_CREATE, ELEMENT_TYPE);  null;
    end CREATE;


    procedure OPEN (FILE : in out FILE_TYPE;
                    MODE : in FILE_MODE;
                    NAME : in STRING;
                    FORM : in STRING := "") is
    begin
    	pragma io_interface (PREDEF, DIO_OPEN, ELEMENT_TYPE);  null;
    end OPEN;

    procedure CLOSE (FILE : in out FILE_TYPE) is
    begin
    	pragma io_interface (PREDEF, DIO_CLOSE);  null;
    end CLOSE;


    procedure DELETE (FILE : in out FILE_TYPE) is
    begin
    	pragma io_interface (PREDEF, DIO_DELETE);  null;
    end DELETE;

    procedure RESET  (FILE : in out FILE_TYPE;  MODE : in FILE_MODE) is
    begin
        pragma io_interface (PREDEF, DIO_RESET_MODE);  null;
    end RESET;
    
    procedure RESET  (FILE : in out FILE_TYPE) is
    begin
        pragma io_interface (PREDEF, DIO_RESET);  null;
    end RESET;

    function  MODE   (FILE : in FILE_TYPE)  return FILE_MODE is
    begin
        pragma io_interface (PREDEF, DIO_MODE);  null;
    end MODE;

    function  NAME   (FILE : in FILE_TYPE)  return STRING is
    begin
    	pragma io_interface (PREDEF, DIO_NAME);  null;
    end NAME;

    function  FORM   (FILE : in FILE_TYPE)  return STRING is
    begin
        pragma io_interface (PREDEF, DIO_FORM);  null;
    end FORM;
    
    function  IS_OPEN(FILE : in FILE_TYPE)  return BOOLEAN is
    begin
    	pragma io_interface (PREDEF, DIO_IS_OPEN);  null;
    end IS_OPEN;



    -- Input and Output Operations:


    procedure READ (FILE : in FILE_TYPE; ITEM : out ELEMENT_TYPE) is
    begin
    	pragma io_interface (PREDEF, DIO_READ, ELEMENT_TYPE);  null;
    end READ;

    procedure READ (FILE : in FILE_TYPE;  ITEM : out ELEMENT_TYPE; 
                                            FROM : in POSITIVE_COUNT) is
    begin
        pragma io_interface (PREDEF, DIO_READ_FROM, ELEMENT_TYPE); null;
    end  READ;

    procedure WRITE (FILE : in FILE_TYPE; ITEM : in ELEMENT_TYPE) is
    begin
    	pragma io_interface (PREDEF, DIO_WRITE);  null;
    end WRITE;

    procedure WRITE (FILE : in FILE_TYPE; ITEM : in ELEMENT_TYPE;
                                              TO : in POSITIVE_COUNT) is
    begin
    	pragma io_interface (PREDEF, DIO_WRITE_TO);  null;
    end WRITE;

    procedure SET_INDEX(FILE : in FILE_TYPE; TO : in POSITIVE_COUNT)
    is begin
        pragma io_interface (PREDEF, DIO_SET_INDEX);  null;
    end SET_INDEX;

    function  INDEX       (FILE : in FILE_TYPE) return POSITIVE_COUNT is
    begin
        pragma io_interface (PREDEF, DIO_INDEX);  null;
    end INDEX;

    function  SIZE        (FILE : in FILE_TYPE) return COUNT is
    begin
        pragma io_interface (PREDEF, DIO_SIZE);  null;
    end SIZE;

    function  END_OF_FILE (FILE : in FILE_TYPE) return BOOLEAN is
    begin
    	pragma io_interface (PREDEF, DIO_END_OF_FILE);  null;
    end END_OF_FILE;


end DIRECT_IO;


with IO_EXCEPTIONS;
package TEXT_IO is 
     
  type FILE_TYPE  is limited private;
 
  type FILE_MODE  is (IN_FILE, OUT_FILE);

  type COUNT is range 0 .. INTEGER'LAST;

  subtype POSITIVE_COUNT IS COUNT range 1 .. COUNT'LAST;

  UNBOUNDED : constant COUNT := 0; -- line and page length

  subtype FIELD is INTEGER range 0 .. 100 ;
  subtype NUMBER_BASE is INTEGER range 2 .. 16;

  type TYPE_SET is (LOWER_CASE, UPPER_CASE);

  -- File Management

     
  procedure CREATE (FILE : in out FILE_TYPE;
                    MODE : in FILE_MODE := OUT_FILE;
                    NAME : in STRING    := "";
                    FORM : in STRING    := "");
    
  procedure OPEN   (FILE : in out FILE_TYPE;
                    MODE : in FILE_MODE;
                    NAME : in STRING;
                    FORM : in STRING := "");
 
  procedure CLOSE  (FILE : in out FILE_TYPE);
    
  procedure DELETE (FILE : in out FILE_TYPE);

  procedure RESET  (FILE : in out FILE_TYPE; MODE : in FILE_MODE);
  procedure RESET  (FILE : in out FILE_TYPE);

  function MODE (FILE : in FILE_TYPE)     return FILE_MODE;

  function NAME (FILE : in FILE_TYPE)     return STRING;

  function FORM (FILE : in FILE_TYPE)     return STRING;      

  function IS_OPEN (FILE : in FILE_TYPE)  return BOOLEAN;

  -- Control of default input and output files
     
  procedure SET_INPUT  (FILE : in FILE_TYPE);
  procedure SET_OUTPUT (FILE : in FILE_TYPE);

  function STANDARD_INPUT  return FILE_TYPE;
  function STANDARD_OUTPUT return FILE_TYPE;

  function CURRENT_INPUT  return FILE_TYPE;
  function CURRENT_OUTPUT return FILE_TYPE;

  -- Specification of line and page lengths

  procedure SET_LINE_LENGTH (FILE : in FILE_TYPE;  TO : in COUNT);
  procedure SET_LINE_LENGTH (TO : in COUNT);	-- default output file

  procedure SET_PAGE_LENGTH (FILE : in FILE_TYPE;  TO : in COUNT);
  procedure SET_PAGE_LENGTH (TO : in COUNT);    -- default output file

  function LINE_LENGTH (FILE : in FILE_TYPE)  return COUNT;
  function LINE_LENGTH return COUNT;  -- default output file
     
  
  function PAGE_LENGTH (FILE : in FILE_TYPE)  return COUNT;
  function PAGE_LENGTH return COUNT; -- default output file

  -- Column, Line and Page Control

  procedure NEW_LINE (FILE : in FILE_TYPE;  SPACING : in POSITIVE_COUNT := 1);
  procedure NEW_LINE (SPACING : in POSITIVE_COUNT := 1); 

  procedure SKIP_LINE (FILE : in FILE_TYPE;  SPACING : in POSITIVE_COUNT := 1);
  procedure SKIP_LINE (SPACING : in POSITIVE_COUNT := 1);

  function END_OF_LINE (FILE : in FILE_TYPE) return BOOLEAN;
  function END_OF_LINE return BOOLEAN; -- default input file

  procedure NEW_PAGE (FILE : in FILE_TYPE);
  procedure NEW_PAGE; -- default output file

  procedure SKIP_PAGE (FILE : in FILE_TYPE);
  procedure SKIP_PAGE; -- default input file

  function END_OF_PAGE (FILE : in FILE_TYPE) return BOOLEAN;
  function END_OF_PAGE return BOOLEAN;      

  function END_OF_FILE (FILE : in FILE_TYPE) return BOOLEAN;
  function END_OF_FILE return BOOLEAN;      

  procedure SET_COL(FILE : in FILE_TYPE; TO : in POSITIVE_COUNT);
  procedure SET_COL(TO : in POSITIVE_COUNT); -- default output file

  procedure SET_LINE(FILE : in FILE_TYPE; TO : in POSITIVE_COUNT);
  procedure SET_LINE(TO : in POSITIVE_COUNT); -- default output file
  
  function COL(FILE : in FILE_TYPE) return POSITIVE_COUNT;
  function COL return POSITIVE_COUNT; -- default output file

  function LINE(FILE : in FILE_TYPE) return POSITIVE_COUNT;
  function LINE return POSITIVE_COUNT; -- default output file

  function PAGE(FILE : in FILE_TYPE) return POSITIVE_COUNT;
  function PAGE return POSITIVE_COUNT; -- default output file


  -- Character Input-Output
 
  procedure GET (FILE : in  FILE_TYPE;  ITEM : out CHARACTER);
  procedure GET (ITEM : out CHARACTER);
  procedure PUT (FILE : in  FILE_TYPE;  ITEM : in CHARACTER);
  procedure PUT (ITEM : in  CHARACTER);

    
  -- String Input-Output
    
  procedure GET (FILE : in  FILE_TYPE;  ITEM : out STRING);
  procedure GET (ITEM : out STRING);    
  procedure PUT (FILE : in  FILE_TYPE;  ITEM : in STRING);
  procedure PUT (ITEM : in  STRING);

  procedure GET_LINE (FILE : in FILE_TYPE; ITEM : out STRING;
                                           LAST : out NATURAL);
  procedure GET_LINE (ITEM : out  STRING; LAST : out NATURAL);

  procedure PUT_LINE (FILE : in FILE_TYPE; ITEM : in STRING);
  procedure PUT_LINE (ITEM : in STRING);
    
  -- Generic package for Input-Output of Integer Types

  generic
    type NUM is range <>;
  package INTEGER_IO is

    DEFAULT_WIDTH : FIELD := NUM'WIDTH;
    DEFAULT_BASE  : NUMBER_BASE := 10;

    procedure GET (FILE  : in FILE_TYPE;  ITEM : out NUM; 
                                          WIDTH : in FIELD := 0);
    procedure GET (ITEM  : out NUM; WIDTH : in FIELD := 0);

    procedure PUT (FILE  : in FILE_TYPE;
    		   ITEM  : in NUM;
    		   WIDTH : in FIELD := DEFAULT_WIDTH;
    		   BASE  : in NUMBER_BASE := DEFAULT_BASE);
    procedure PUT (ITEM  : in NUM;
    		   WIDTH : in FIELD := DEFAULT_WIDTH;
    		   BASE  : in NUMBER_BASE := DEFAULT_BASE);
    
    procedure GET (FROM : in STRING; ITEM: out NUM; LAST: out POSITIVE);
    procedure PUT (TO   : out STRING;
                   ITEM : in  NUM;
                   BASE : in  NUMBER_BASE := DEFAULT_BASE);

  end INTEGER_IO;


  -- Generic packages for Input-Output of Real Types

  generic
    type NUM is digits <>;
  package FLOAT_IO is

    DEFAULT_FORE : FIELD := 2;
    DEFAULT_AFT  : FIELD := NUM'DIGITS-1;
    DEFAULT_EXP  : FIELD := 3;

    procedure GET (FILE : in FILE_TYPE; ITEM : out NUM;
                                        WIDTH : in FIELD := 0);
    procedure GET (ITEM : out NUM; WIDTH : in FIELD := 0);

    procedure PUT (FILE		: in FILE_TYPE;
		   ITEM		: in NUM;
		   FORE        	: in FIELD := DEFAULT_FORE;
		   AFT  	: in FIELD := DEFAULT_AFT;
		   EXP   	: in FIELD := DEFAULT_EXP);

    procedure PUT (ITEM		: in NUM;
		   FORE   	: in FIELD := DEFAULT_FORE;
		   AFT  	: in FIELD := DEFAULT_AFT;
		   EXP  	: in FIELD := DEFAULT_EXP);
    
    procedure GET (FROM : in STRING; ITEM: out NUM; LAST: out POSITIVE);
    procedure PUT (TO   : out STRING;
                   ITEM : in NUM;
                   AFT  : in FIELD := DEFAULT_AFT;
                   EXP  : in FIELD := DEFAULT_EXP);

  end FLOAT_IO;


  generic
    type NUM is delta <>;
  package FIXED_IO is

    DEFAULT_FORE : FIELD := NUM'FORE;
    DEFAULT_AFT  : FIELD := NUM'AFT;
    DEFAULT_EXP  : FIELD := 0;

    procedure GET (FILE : in FILE_TYPE; ITEM : out NUM;
                                        WIDTH : in FIELD := 0);
    procedure GET (ITEM : out NUM; WIDTH : in FIELD := 0);

    procedure PUT (FILE		: in FILE_TYPE;
		   ITEM		: in NUM;
		   FORE 	: in FIELD := DEFAULT_FORE;
		   AFT  	: in FIELD := DEFAULT_AFT;
                   EXP          : in FIELD := DEFAULT_EXP);

    procedure PUT (ITEM		: in NUM;
		   FORE 	: in FIELD := DEFAULT_FORE;
		   AFT  	: in FIELD := DEFAULT_AFT;
                   EXP          : in FIELD := DEFAULT_EXP);

    procedure GET (FROM : in STRING; ITEM: out NUM; LAST: out POSITIVE);
    procedure PUT (TO   : out STRING;
                   ITEM : in  NUM;
                   AFT  : in  FIELD := DEFAULT_AFT;
                   EXP  : in  FIELD := DEFAULT_EXP);

  end FIXED_IO;

      
  -- Generic package for Input-Output of Enumeration Types

  generic
    type ENUM is (<>);
  package ENUMERATION_IO is

    DEFAULT_WIDTH   : FIELD := 0;
    DEFAULT_SETTING : TYPE_SET := UPPER_CASE;

    procedure GET (FILE : in FILE_TYPE; ITEM : out ENUM);
    procedure GET (ITEM : out ENUM);

    procedure PUT (FILE       :	in FILE_TYPE;
		   ITEM       :	in ENUM;
		   WIDTH      :	in FIELD    := DEFAULT_WIDTH;
		   SET        : in TYPE_SET := DEFAULT_SETTING);

    procedure PUT (ITEM       :	in ENUM;
		   WIDTH      :	in FIELD    := DEFAULT_WIDTH;
		   SET        :	in TYPE_SET := DEFAULT_SETTING);
 
    procedure GET(FROM : in STRING; ITEM: out ENUM; LAST: out POSITIVE);
    procedure PUT (TO   : out STRING;
                   ITEM : in  ENUM;
                   SET  : in  TYPE_SET := DEFAULT_SETTING);

  end ENUMERATION_IO;


  -- Exceptions:
  --  
  -- These are the exceptions whose names are visible to the   
  -- calling environment.   
     
  STATUS_ERROR	: exception renames IO_EXCEPTIONS.STATUS_ERROR;
  MODE_ERROR    : exception renames IO_EXCEPTIONS.MODE_ERROR;
  NAME_ERROR	: exception renames IO_EXCEPTIONS.NAME_ERROR;
  USE_ERROR	: exception renames IO_EXCEPTIONS.USE_ERROR;
  DEVICE_ERROR	: exception renames IO_EXCEPTIONS.DEVICE_ERROR;
  END_ERROR	: exception renames IO_EXCEPTIONS.END_ERROR;
  DATA_ERROR	: exception renames IO_EXCEPTIONS.DATA_ERROR;
  LAYOUT_ERROR	: exception renames IO_EXCEPTIONS.LAYOUT_ERROR;


    
private

    type  FILE_TYPE  is 
      record
        FILE_NUM : INTEGER := 0;
      end record;

end TEXT_IO; 


package body TEXT_IO is

-- The bodies for all the procedure and functions consist of an 
-- interface pragma which generates an AIS instruction of the form:
--
--    [ 'predef_', specifier, [formal, formal, ...] ]
--
-- where the specifier is the second argument to the pragma in 
-- upper case, and the formals are the fully qualified names of the 
-- formal parameters to the procedure. The specifier is used by the 
-- SETL TEXT_IO routines in determining which routine was called and 
-- the formal names are used for accessing and setting the values of 
-- the arguments to the procedure or function call. 


-- Global operations for file manipulation:
  
  procedure CREATE (FILE : in out FILE_TYPE;
                    MODE : in FILE_MODE := OUT_FILE;
                    NAME : in STRING    := "";
                    FORM : in STRING    := "") is
  begin
      pragma io_interface (PREDEF, TIO_CREATE);  null;
  end CREATE;
   
  procedure OPEN   (FILE : in out FILE_TYPE;
                    MODE : in FILE_MODE;
                    NAME : in STRING;
                    FORM : in STRING := "") is
  begin
      pragma io_interface (PREDEF, TIO_OPEN);  null;
  end OPEN;
 
  procedure CLOSE  (FILE : in out FILE_TYPE) is
  begin
      pragma io_interface (PREDEF, TIO_CLOSE);  null;
  end CLOSE;
 
  procedure DELETE (FILE : in out FILE_TYPE) is
  begin
      pragma io_interface (PREDEF, TIO_DELETE);  null;
  end DELETE;
    
  procedure RESET  (FILE : in out FILE_TYPE; MODE : in FILE_MODE) is
  begin
      pragma io_interface (PREDEF, TIO_RESET_MODE);  null;
  end RESET;
  procedure RESET  (FILE : in out FILE_TYPE) is
  begin
      pragma io_interface (PREDEF, TIO_RESET);  null;
  end RESET;

  function MODE (FILE : in FILE_TYPE)     return FILE_MODE is
  begin
      pragma io_interface (PREDEF, TIO_MODE);  null;
  end MODE;

  
  function NAME (FILE : in FILE_TYPE)     return STRING is
  begin
      pragma io_interface (PREDEF, TIO_NAME);  null;
  end NAME;

  function FORM (FILE : in FILE_TYPE)     return STRING is
  begin
      pragma io_interface (PREDEF, TIO_FORM);  null;
  end FORM;      

  function IS_OPEN (FILE : in FILE_TYPE)  return BOOLEAN is
  begin
      pragma io_interface (PREDEF, TIO_IS_OPEN);  null;
  end IS_OPEN;
    
  -- Control of default input and output files
     
  procedure SET_INPUT  (FILE : in FILE_TYPE) is
  begin
      pragma io_interface (PREDEF, SET_INPUT);  null;
  end SET_INPUT;
  procedure SET_OUTPUT (FILE : in FILE_TYPE) is
  begin
      pragma io_interface (PREDEF, SET_OUTPUT);  null;
  end SET_OUTPUT;

  function STANDARD_INPUT  return FILE_TYPE is
  begin
      pragma io_interface (PREDEF, STANDARD_INPUT);  null;
  end STANDARD_INPUT;
  function STANDARD_OUTPUT return FILE_TYPE is
  begin
      pragma io_interface (PREDEF, STANDARD_OUTPUT);  null;
  end STANDARD_OUTPUT;

  function CURRENT_INPUT  return FILE_TYPE is
  begin
      pragma io_interface (PREDEF, CURRENT_INPUT);  null;
  end CURRENT_INPUT;
  function CURRENT_OUTPUT return FILE_TYPE is
  begin
      pragma io_interface (PREDEF, CURRENT_OUTPUT);  null;
  end CURRENT_OUTPUT;

  -- Specification of line and page lengths

  procedure SET_LINE_LENGTH (FILE : in FILE_TYPE;  TO : in COUNT) is
  begin
      pragma io_interface (PREDEF, SET_LINE_LENGTH_FILE);  null;
  end SET_LINE_LENGTH;
  procedure SET_LINE_LENGTH (TO : in COUNT) is
  begin
      pragma io_interface (PREDEF, SET_LINE_LENGTH);  null;
  end SET_LINE_LENGTH;	

  procedure SET_PAGE_LENGTH (FILE : in FILE_TYPE;  TO : in COUNT) is
  begin
      pragma io_interface (PREDEF, SET_PAGE_LENGTH_FILE);  null;
  end SET_PAGE_LENGTH;
  procedure SET_PAGE_LENGTH (TO : in COUNT) is
  begin
      pragma io_interface (PREDEF, SET_PAGE_LENGTH);  null;
  end SET_PAGE_LENGTH;    

  function LINE_LENGTH (FILE : in FILE_TYPE)  return COUNT is
  begin
      pragma io_interface (PREDEF, LINE_LENGTH_FILE);  null;
  end LINE_LENGTH;
  function LINE_LENGTH return COUNT is
  begin
      pragma io_interface (PREDEF, LINE_LENGTH);  null;
  end LINE_LENGTH;  
     
  
  function PAGE_LENGTH (FILE : in FILE_TYPE)  return COUNT is
  begin
      pragma io_interface (PREDEF, PAGE_LENGTH_FILE);  null;
  end PAGE_LENGTH;
  function PAGE_LENGTH return COUNT is
  begin
      pragma io_interface (PREDEF, PAGE_LENGTH);  null;
  end PAGE_LENGTH; 

  -- Column, Line and Page Control

  procedure NEW_LINE (FILE : in FILE_TYPE;  SPACING : in POSITIVE_COUNT := 1)
  is begin
      pragma io_interface (PREDEF, NEW_LINE_FILE);  null;
  end NEW_LINE;
  procedure NEW_LINE (SPACING : in POSITIVE_COUNT := 1) is
  begin
      pragma io_interface (PREDEF, NEW_LINE);  null;
  end NEW_LINE; 

  procedure SKIP_LINE (FILE : in FILE_TYPE;  SPACING : in POSITIVE_COUNT := 1) 
  is begin
      pragma io_interface (PREDEF, SKIP_LINE_FILE);  null;
  end SKIP_LINE;
  procedure SKIP_LINE (SPACING : in POSITIVE_COUNT := 1) is
  begin
      pragma io_interface (PREDEF, SKIP_LINE);  null;
  end SKIP_LINE;

  function END_OF_LINE (FILE : in FILE_TYPE) return BOOLEAN is
  begin
      pragma io_interface (PREDEF, END_OF_LINE_FILE);  null;
  end END_OF_LINE;
  function END_OF_LINE return BOOLEAN is
  begin
      pragma io_interface (PREDEF, END_OF_LINE);  null;
  end END_OF_LINE; 

  procedure NEW_PAGE(FILE : in FILE_TYPE) is
  begin
      pragma io_interface (PREDEF, NEW_PAGE_FILE);  null;
  end NEW_PAGE;
  procedure NEW_PAGE is
  begin
      pragma io_interface (PREDEF, NEW_PAGE);  null;
  end NEW_PAGE;

  procedure SKIP_PAGE(FILE : in FILE_TYPE) is
  begin
      pragma io_interface (PREDEF, SKIP_PAGE_FILE);  null;
  end SKIP_PAGE;
  procedure SKIP_PAGE is
  begin
      pragma io_interface (PREDEF, SKIP_PAGE);  null;
  end SKIP_PAGE; 

  function END_OF_PAGE(FILE : in FILE_TYPE) return BOOLEAN is
  begin
      pragma io_interface (PREDEF, END_OF_PAGE_FILE);  null;
  end END_OF_PAGE;
  function END_OF_PAGE return BOOLEAN is
  begin
      pragma io_interface (PREDEF, END_OF_PAGE);  null;
  end END_OF_PAGE;      

  function END_OF_FILE (FILE : in FILE_TYPE) return BOOLEAN is
  begin
      pragma io_interface (PREDEF, TIO_END_OF_FILE_FILE);  null;
  end END_OF_FILE;
  function END_OF_FILE return BOOLEAN is
  begin
      pragma io_interface (PREDEF, TIO_END_OF_FILE);  null;
  end END_OF_FILE;

  procedure SET_COL(FILE : in FILE_TYPE; TO : in POSITIVE_COUNT) is
  begin
      pragma io_interface (PREDEF, SET_COL_FILE);  null;
  end SET_COL;
  procedure SET_COL(TO : in POSITIVE_COUNT) is
  begin
      pragma io_interface (PREDEF, SET_COL);  null;
  end SET_COL;

  procedure SET_LINE(FILE : in FILE_TYPE; TO : in POSITIVE_COUNT) is
  begin
      pragma io_interface (PREDEF, SET_LINE_FILE);  null;
  end SET_LINE;
  procedure SET_LINE(TO : in POSITIVE_COUNT) is
  begin
      pragma io_interface (PREDEF, SET_LINE);  null;
  end SET_LINE; 
  
  function COL(FILE : in FILE_TYPE) return POSITIVE_COUNT is
  begin
      pragma io_interface (PREDEF, COL_FILE);  null;
  end COL;
  function COL return POSITIVE_COUNT is
  begin
      pragma io_interface (PREDEF, COL);  null;
  end COL; 

  function LINE(FILE : in FILE_TYPE) return POSITIVE_COUNT is
  begin
      pragma io_interface (PREDEF, LINE_FILE);  null;
  end LINE;
  function LINE return POSITIVE_COUNT is
  begin
      pragma io_interface (PREDEF, LINE);  null;
  end LINE; 

  function PAGE(FILE : in FILE_TYPE) return POSITIVE_COUNT is
  begin
      pragma io_interface (PREDEF, PAGE_FILE);  null;
  end PAGE;
  function PAGE return POSITIVE_COUNT is
  begin
      pragma io_interface (PREDEF, PAGE);  null;
  end PAGE; 


  -- Character Input-Output
 
  procedure GET (FILE : in FILE_TYPE;  ITEM : out CHARACTER) is
  begin
      pragma io_interface (PREDEF, GET_CHAR_FILE_ITEM);  null;
  end GET;
  procedure GET (ITEM : out CHARACTER) is
  begin
      pragma io_interface (PREDEF, GET_CHAR_ITEM);  null;
  end GET;
    
  procedure PUT (FILE : in FILE_TYPE;  ITEM : in CHARACTER) is
  begin
      pragma io_interface (PREDEF, PUT_CHAR_FILE_ITEM);  null;
  end PUT;
  procedure PUT (ITEM : in CHARACTER) is
  begin
      pragma io_interface (PREDEF, PUT_CHAR_ITEM);  null;
  end PUT;

    
  -- String Input-Output
    
  procedure GET (FILE : in FILE_TYPE;  ITEM : out STRING) is
  begin
      pragma io_interface (PREDEF, GET_STRING_FILE_ITEM);  null;
  end GET;
  procedure GET (ITEM : out STRING) is
  begin
      pragma io_interface (PREDEF, GET_STRING_ITEM);  null;
  end GET;    
    
  procedure PUT (FILE : in FILE_TYPE;  ITEM : in STRING) is
  begin
      pragma io_interface (PREDEF, PUT_STRING_FILE_ITEM);  null;
  end PUT;
  procedure PUT (ITEM : in STRING) is
  begin
      pragma io_interface (PREDEF, PUT_STRING_ITEM);  null;
  end PUT;

  procedure GET_LINE (FILE : in FILE_TYPE; ITEM : out STRING;
                                           LAST : out NATURAL) is
  begin
      pragma io_interface (PREDEF, GET_LINE_FILE);  null;
  end GET_LINE;
  procedure GET_LINE (ITEM  : out  STRING; LAST : out NATURAL) is
  begin
      pragma io_interface (PREDEF, GET_LINE);  null;
  end GET_LINE; 

  procedure PUT_LINE (FILE  : in FILE_TYPE; ITEM : in STRING) is
  begin
      pragma io_interface (PREDEF, PUT_LINE_FILE);  null;
  end PUT_LINE;
  procedure PUT_LINE (ITEM  : in STRING) is
  begin
      pragma io_interface (PREDEF, PUT_LINE);  null;
  end PUT_LINE;
    
  -- Generic package for Input-Output of Integer Types

  package body INTEGER_IO is

    procedure GET (FILE  : in FILE_TYPE;  ITEM : out NUM;
                                          WIDTH : in FIELD := 0) is
    begin
        pragma io_interface (PREDEF, GET_INTEGER_FILE_ITEM, NUM);  null;
    end GET;
    procedure GET (ITEM  : out NUM; WIDTH : in FIELD := 0) is
    begin
        pragma io_interface (PREDEF, GET_INTEGER_ITEM, NUM);  null;
    end GET;

    procedure PUT (FILE  : in FILE_TYPE;
    		   ITEM  : in NUM;
    		   WIDTH : in FIELD := DEFAULT_WIDTH;
    		   BASE  : in NUMBER_BASE := DEFAULT_BASE) is
    begin
        pragma io_interface (PREDEF, PUT_INTEGER_FILE_ITEM);  null;
    end PUT;

    procedure PUT (ITEM  : in NUM;
    		   WIDTH : in FIELD := DEFAULT_WIDTH;
    		   BASE  : in NUMBER_BASE := DEFAULT_BASE) is
    begin
        pragma io_interface (PREDEF, PUT_INTEGER_ITEM);  null;
    end PUT;
    
    procedure GET (FROM : in STRING; ITEM : out NUM; LAST: out POSITIVE)
    is begin
        pragma io_interface (PREDEF, GET_INTEGER_STRING, NUM);  null;
    end GET;
    procedure PUT (TO   : out STRING;
                   ITEM : in NUM;
                   BASE : in NUMBER_BASE := DEFAULT_BASE) is
    begin
        pragma io_interface (PREDEF, PUT_INTEGER_STRING);  null;
    end PUT;

  end INTEGER_IO;


  -- Generic packages for Input-Output of Real Types

  package body FLOAT_IO is

    procedure GET (FILE : in FILE_TYPE; ITEM : out NUM;
                                        WIDTH : in FIELD := 0) is
    begin
        pragma io_interface (PREDEF, GET_FLOAT_FILE_ITEM, NUM);  null;
    end GET;
    procedure GET (ITEM : out NUM; WIDTH : in FIELD := 0) is
    begin
        pragma io_interface (PREDEF, GET_FLOAT_ITEM, NUM);  null;
    end GET;

    procedure PUT (FILE		: in FILE_TYPE;
		   ITEM		: in NUM;
		   FORE        	: in FIELD := DEFAULT_FORE;
		   AFT  	: in FIELD := DEFAULT_AFT;
		   EXP   	: in FIELD := DEFAULT_EXP) is
    begin
        pragma io_interface (PREDEF, PUT_FLOAT_FILE_ITEM);  null;
    end PUT;

    procedure PUT (ITEM		: in NUM;
		   FORE   	: in FIELD := DEFAULT_FORE;
		   AFT  	: in FIELD := DEFAULT_AFT;
		   EXP  	: in FIELD := DEFAULT_EXP) is
    begin
        pragma io_interface (PREDEF, PUT_FLOAT_ITEM);  null;
    end PUT;
    
    procedure GET (FROM : in STRING; ITEM : out NUM; LAST: out POSITIVE)
    is begin
        pragma io_interface (PREDEF, GET_FLOAT_STRING, NUM);  null;
    end GET;
    procedure PUT (TO   : out STRING;
                   ITEM : in NUM;
                   AFT  : in FIELD := DEFAULT_AFT;
                   EXP  : in FIELD := DEFAULT_EXP) is
    begin
        pragma io_interface (PREDEF, PUT_FLOAT_STRING);  null;
    end PUT;

  end FLOAT_IO;


  package body FIXED_IO is

    procedure GET (FILE : in FILE_TYPE; ITEM : out NUM;
                                        WIDTH : in FIELD := 0) is
    begin
        pragma io_interface (PREDEF, GET_FIXED_FILE_ITEM, NUM);  null;
    end GET;
    procedure GET (ITEM : out NUM; WIDTH : in FIELD := 0) is
    begin
        pragma io_interface (PREDEF, GET_FIXED_ITEM, NUM);  null;
    end GET;

    procedure PUT (FILE		: in FILE_TYPE;
		   ITEM		: in NUM;
		   FORE 	: in FIELD := DEFAULT_FORE;
		   AFT  	: in FIELD := DEFAULT_AFT;
                   EXP          : in FIELD := DEFAULT_EXP) is
    begin
        pragma io_interface (PREDEF, PUT_FIXED_FILE_ITEM);  null;
    end PUT;

    procedure PUT (ITEM		: in NUM;
		   FORE 	: in FIELD := DEFAULT_FORE;
		   AFT  	: in FIELD := DEFAULT_AFT;
                   EXP          : in FIELD := DEFAULT_EXP) is
    begin
        pragma io_interface (PREDEF, PUT_FIXED_ITEM);  null;
    end PUT;

    procedure GET (FROM : in STRING; ITEM : out NUM; LAST: out POSITIVE)
    is begin
        pragma io_interface (PREDEF, GET_FIXED_STRING, NUM);  null;
    end GET;
    procedure PUT (TO   : out STRING;
                   ITEM : in  NUM;
                   AFT  : in  FIELD := DEFAULT_AFT;
                   EXP  : in  FIELD := DEFAULT_EXP) is
    begin
        pragma io_interface (PREDEF, PUT_FIXED_STRING);  null;
    end PUT;

  end FIXED_IO;

      
  -- Generic package for Input-Output of Enumeration Types

  package body ENUMERATION_IO is

    procedure GET (FILE : in FILE_TYPE; ITEM : out ENUM) is
    begin
        pragma io_interface (PREDEF, GET_ENUM_FILE_ITEM, ENUM);  null;
    end GET;
    procedure GET (ITEM : out ENUM) is
    begin
        pragma io_interface (PREDEF, GET_ENUM_ITEM, ENUM);  null;
    end GET;

    procedure PUT (FILE       :	in FILE_TYPE;
		   ITEM       :	in ENUM;
		   WIDTH      :	in FIELD    := DEFAULT_WIDTH;
		   SET        : in TYPE_SET := DEFAULT_SETTING) is
    begin
        pragma io_interface (PREDEF, PUT_ENUM_FILE_ITEM, ENUM);  null;
    end PUT;

    procedure PUT (ITEM       :	in ENUM;
		   WIDTH      :	in FIELD    := DEFAULT_WIDTH;
		   SET        :	in TYPE_SET := DEFAULT_SETTING) is
    begin
        pragma io_interface (PREDEF, PUT_ENUM_ITEM, ENUM);  null;
    end PUT;
 
    procedure GET (FROM : in STRING; ITEM: out ENUM; LAST: out POSITIVE)
    is begin
        pragma io_interface (PREDEF, GET_ENUM_STRING, ENUM);  null;
    end GET;
    procedure PUT (TO   : out STRING;
                   ITEM : in  ENUM;
                   SET  : in  TYPE_SET := DEFAULT_SETTING) is
    begin
        pragma io_interface (PREDEF, PUT_ENUM_STRING, ENUM);  null;
    end PUT;

  end ENUMERATION_IO;


end TEXT_IO;

-- Predefined library units:  calendar & generic subprograms

package CALENDAR is
   type TIME is private;

   subtype YEAR_NUMBER  is INTEGER range 1901 .. 2099;
   subtype MONTH_NUMBER is INTEGER range 1 .. 12;
   subtype DAY_NUMBER   is INTEGER range 1 .. 31;

   function CLOCK return TIME;

   function YEAR   (DATE    : TIME) return YEAR_NUMBER;
   function MONTH  (DATE    : TIME) return MONTH_NUMBER;
   function DAY    (DATE    : TIME) return DAY_NUMBER;
   function SECONDS(DATE    : TIME) return DURATION;

   procedure SPLIT (DATE    : in  TIME;
                    YEAR    : out YEAR_NUMBER;
                    MONTH   : out MONTH_NUMBER;
                    DAY     : out DAY_NUMBER;
                    SECONDS : out DURATION);

   function TIME_OF(YEAR    : YEAR_NUMBER;
                    MONTH   : MONTH_NUMBER;
                    DAY     : DAY_NUMBER;
                    SECONDS : DURATION := 0.0) return TIME;

   TIME_ERROR : exception;   --   can be raised by TIME_OF

   function "+"  (LEFT : TIME;     RIGHT : DURATION) return TIME;
   function "+"  (LEFT : DURATION; RIGHT : TIME)     return TIME;
   function "-"  (LEFT : TIME;     RIGHT : DURATION) return TIME;
   function "-"  (LEFT : TIME;     RIGHT : TIME)     return DURATION;

   function "<"  (LEFT, RIGHT : TIME) return BOOLEAN;
   function "<=" (LEFT, RIGHT : TIME) return BOOLEAN;
   function ">"  (LEFT, RIGHT : TIME) return BOOLEAN;
   function ">=" (LEFT, RIGHT : TIME) return BOOLEAN;

private 

   type TIME is
       record 
          YEAR    :   YEAR_NUMBER;
          MONTH   :   MONTH_NUMBER;
          DAY     :   DAY_NUMBER;
          SECONDS :   DURATION;
       end record;

end CALENDAR;

package body CALENDAR is

  function CLOCK return TIME is
  begin
    pragma io_interface(PREDEF, CLOCK);
    null;
  end CLOCK;

  function YEAR   (DATE    : TIME) return YEAR_NUMBER is
  begin
    pragma io_interface(PREDEF, YEAR);
    null;
  end YEAR;

  function MONTH  (DATE    : TIME) return MONTH_NUMBER is
  begin
    pragma io_interface(PREDEF, MONTH);
    null;
  end MONTH;

  function DAY    (DATE    : TIME) return DAY_NUMBER is
  begin
    pragma io_interface(PREDEF, DAY);
    null;
  end DAY;

  function SECONDS(DATE    : TIME) return DURATION is
  begin
    pragma io_interface(PREDEF, SECONDS);
    null;
  end SECONDS;

  procedure SPLIT (DATE    : in  TIME;
                   YEAR    : out YEAR_NUMBER;
                   MONTH   : out MONTH_NUMBER;
                   DAY     : out DAY_NUMBER;
                   SECONDS : out DURATION) is
  begin
    pragma io_interface(PREDEF, SPLIT);
    null;
  end SPLIT;

  function TIME_OF(YEAR    : YEAR_NUMBER;
                   MONTH   : MONTH_NUMBER;
                   DAY     : DAY_NUMBER;
                   SECONDS : DURATION := 0.0) return TIME is
  begin
    pragma io_interface(PREDEF, TIME_OF);
    null;
  end TIME_OF;

  function "+" (LEFT : TIME;     RIGHT : DURATION) return TIME is
  begin
    pragma io_interface(PREDEF, ADD_TIME_DUR);
    null;
  end "+";

  function "+" (LEFT : DURATION; RIGHT : TIME)     return TIME is
  begin
    pragma io_interface(PREDEF, ADD_DUR_TIME);
    null;
  end "+";

  function "-" (LEFT : TIME;     RIGHT : DURATION) return TIME is
  begin
    pragma io_interface(PREDEF, SUB_TIME_DUR);
    null;
  end "-";

  function "-" (LEFT : TIME;     RIGHT : TIME)     return DURATION is
  begin
    pragma io_interface(PREDEF, SUB_TIME_TIME);
    null;
  end "-";

  function "<"  (LEFT, RIGHT : TIME) return BOOLEAN is
  begin
    pragma io_interface(PREDEF, LT_TIME);
    null;
  end "<";

  function "<=" (LEFT, RIGHT : TIME) return BOOLEAN is
  begin
    pragma io_interface(PREDEF, LE_TIME);
    null;
  end "<=";

  function ">"  (LEFT, RIGHT : TIME) return BOOLEAN is
  begin
    pragma io_interface(PREDEF, GT_TIME);
    null;
  end ">";

  function ">=" (LEFT, RIGHT : TIME) return BOOLEAN is
  begin
    pragma io_interface(PREDEF, GE_TIME);
    null;
  end ">=";

end CALENDAR;

generic
  type OBJECT is limited private;
  type NAME   is access OBJECT;
procedure UNCHECKED_DEALLOCATION(X : in out NAME);

generic
  type SOURCE is limited private;
  type TARGET is limited private;
function UNCHECKED_CONVERSION(S : SOURCE) return TARGET;

procedure UNCHECKED_DEALLOCATION(X : in out NAME) is
begin
  if x /= null then x := null; end if;
end UNCHECKED_DEALLOCATION;

function UNCHECKED_CONVERSION(S : SOURCE) return TARGET is
begin
  raise PROGRAM_ERROR;
end UNCHECKED_CONVERSION;

