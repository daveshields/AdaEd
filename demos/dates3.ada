-- DEMONSTRATION PROGRAM:
--   Features:
--     Enumeration types, ENUM_IO (generic package), records and
--     aggregates, dynamic exception handling, packages, etc.

package DATE_PKGE is
   subtype DAY is integer range 1..31;
   type    MONTH is (Jan, Feb, Mar, Apr, May, Jun,
		     Jul, Aug, Sep, Oct, Nov, Dec);
   subtype YEAR is integer range 0..2000;

   type DATE is
      record
         D : DAY;
         M : MONTH;
         Y : YEAR;
      end record;

   function  LEAP (Y : YEAR) return Boolean;
   function  DAYS_IN_MONTH (M : MONTH; IS_LEAP : Boolean)
	     return DAY;
   function  VALID (TODAY : DATE) return Boolean;
   procedure TOMORROW (TODAY : in out DATE);
   procedure READ_DATE (D : out DATE);
   procedure WRITE_DATE (D : DATE);

   BAD_DATE : exception;
end DATE_PKGE;

with TEXT_IO; use TEXT_IO;
package body DATE_PKGE is
   package MONTH_IO is new ENUMERATION_IO (MONTH);
   package INT_IO is new INTEGER_IO(integer);

   function LEAP (Y : YEAR) return Boolean is
   begin
      return (Y mod 4 = 0) and not (Y mod 100 = 0);
   end LEAP;

   function DAYS_IN_MONTH (M : MONTH; IS_LEAP : Boolean)
            return DAY is
   begin
      case M is
         when Sep | Apr | Jun | Nov => return 30;
         when Feb                   =>
            if IS_LEAP then 
               return 29;
            else
               return 28;
            end if;
         when others                => return 31;
      end case;
   end DAYS_IN_MONTH;

   function VALID (TODAY : DATE) return Boolean is
   begin
      return TODAY.D <= DAYS_IN_MONTH (TODAY.M, LEAP (TODAY.Y));
   end VALID;

   procedure TOMORROW (TODAY : in out DATE) is
      LY : constant Boolean := LEAP (TODAY.Y);
   begin
      if not VALID (TODAY) then
	 new_line;
         put_line("There can be no tomorrow when there is no today.");
         raise BAD_DATE;
      elsif TODAY.D < DAYS_IN_MONTH (TODAY.M, LY) then
         TODAY.D := TODAY.D + 1;           -- not last day of month
      elsif TODAY.M < Dec then
         TODAY.D := 1;                     -- last day of month
         TODAY.M := MONTH'SUCC (TODAY.M);  -- but not last month of year
      elsif TODAY.Y < YEAR'LAST then
         TODAY := (1, Jan, TODAY.Y + 1);   -- last day of year
      else
         new_line;
         put_line(" Beyond the end of time...");
              				   -- run out of years
         raise BAD_DATE;
      end if;
   end TOMORROW;

   procedure READ_DATE (D : out DATE) is
      use MONTH_IO, INT_IO;
      type DATE_COMPONENTS is ('D', 'M', 'Y');
   begin
      for I in DATE_COMPONENTS 
      loop
	 loop
            declare
	    begin
               case I is
                  when 'D' =>
		     put_line("Day:   ");
		     get (D.D);
                  when 'M' =>
		     put_line("Month: ");
		     get (D.M);
                  when 'Y' =>
		     put_line("Year:  ");
		     get (D.Y);
               end case;
	       exit;
	    exception
	       when DATA_ERROR | CONSTRAINT_ERROR =>
                  case I is
                     when 'D' =>
			put_line("Please enter integer from 1 to 31.");
                     when 'M' =>
			put_line(
			 "Please enter three-letter abbreviation " &
			     "(i.e. Jan).");
                     when 'Y' =>
			put_line(
			  "Please enter integer from 0 to 2000.");
		  end case;
	    end;
	 end loop;
      end loop;
   end READ_DATE;

   procedure WRITE_DATE (D : DATE) is
      use MONTH_IO, INT_IO;
   begin
      put (D.M);
      put (" ");
      put (D.D);
      put (", ");
      put (D.Y);
   end WRITE_DATE;
end DATE_PKGE;

with TEXT_IO, DATE_PKGE; use TEXT_IO, DATE_PKGE;
procedure dates3 is
   today : DATE;
begin
   loop
      declare
      begin
	 READ_DATE (today);
	 new_line;
	 put("Today is... ");
	 WRITE_DATE (today);
	 TOMORROW (today);
	 put(" and tomorrow is... ");
	 WRITE_DATE (today);
	 new_line(2);
      exception
         when BAD_DATE =>
            new_line;
	 when END_ERROR =>
	    new_line;
	    put_line("Have a nice day!");
            exit;
      end;
   end loop;
end dates3;
