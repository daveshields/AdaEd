
----------------------------------------------------------------------
--
--              Screen Input Output Package
--
--                      written by
--
--                   Edmond Schonberg
--                    David Shields
--
--                      Ada Project
--                   Courant Institute
--                  New York University
--                   251 Mercer Street
--                New York, New York  10012
--
-----------------------------------------------------------------------

with text_io;         use text_io;
with semaphore;       use semaphore;

package screen_io is

-- These screen input output primitives assume that the terminal can
-- function as a VT100 or, for the IBM PC, has ANSI.SYS installed
-- as a screen driver.

    subtype row is integer range 1..25;
    subtype column is integer range 1..80;

    procedure clear ;
    procedure PUTS(s: string; r: row; c: column);
    procedure PUTSN(s: string; n: integer; r: row; c: column);
    procedure PUTC(ch: character; r: row; c: column);
    procedure PUTCB(ch: character; r: row; c: column);
    procedure fill_screen(c: character) ;

end screen_io;

with integer_text_io; use integer_text_io;
package body screen_io is

    protect: ACCESS_BINARY_SEMAPHORE := new BINARY_SEMAPHORE;

    procedure clear is
    begin
        put(ASCII.ESC ); put("[2J") ;
    end ;

    procedure PUT_INT(R: integer) is
	digs: constant string := "0123456789";
	d : integer := R;
    begin
	if d>=100 then
	    put(digs(d/100 + 1));
            d := d mod 100;
	end if;				
	-- always write at least two digits (if setting screen position).
	put(digs(d/10 + 1));
	put(digs(d mod 10 + 1));
    end;

    procedure SET_CURSOR(R: row := 1; C:column := 1) is
      -- uses escape sequence ESC [ row ; column H
    begin
        put(ASCII.ESC); 
        put('['); 
        put_int(R); 
        put( ';');  
        put_int(C); 
        put('H');
    end SET_CURSOR;

    procedure PUTS(S: string; R: row; C: column) is
        index: integer;
    begin
        PROTECT.P;
        SET_CURSOR(R, C); put_line(S);
        PROTECT.V;
    end;

    procedure PUTSN(S: string; N: integer; R: row; C: column) is
        index: integer;
	-- put string and integer values
    begin
        PROTECT.P;
        SET_CURSOR(R, C); put(S);
	put_int(N);
        put_line("   ");
        PROTECT.V;
    end;

    procedure PUTCB(CH: character ; R: row; C: column) is
    -- put "emphasized" character 
        index: integer;
    begin
        PROTECT.P;
        SET_CURSOR(R, C); 
	put(ASCII.ESC); 
	put("[5m"); -- turn on blinking
	put(CH);
	put(ASCII.ESC); 
	put_line("[0m"); -- turn off blinking
        PROTECT.V;
    end;

   procedure PUTC(Ch: character; R: row; C: column) is
   begin
      PROTECT.P;
      SET_CURSOR(R, C); 
      put(Ch); 
      new_line;
      PROTECT.V;
   end PUTC; 

   procedure fill_screen(c: character) is
       line : string(1..80) := (1..80 => c) ;
   begin
       for i in 2..23 loop
          SET_CURSOR(i, 1); put_line(line) ;
       end loop;
   end fill_screen;
 end screen_io;
    

