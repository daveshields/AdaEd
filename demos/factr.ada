-- DEMONSTRATION PROGRAM:
--   Features:
--     Recursive functions, separate compilation units,
--     dynamic exception handling.

with TEXT_IO;
package SHORT_IO is new TEXT_IO.INTEGER_IO(integer);

with TEXT_IO; use TEXT_IO;
with SHORT_IO; use SHORT_IO;
procedure factr is

   subtype short_int is integer range 0..9999;
   x : short_int;

   function factorial (x : short_int) return short_int is separate;

begin

outer: loop                 -- Compute factorial of each input item.
      begin
         put_line ("Factorial of:" );
         loop           -- Get an integer.
	    begin
	       exit outer when end_of_file ;
	       get (x);
               exit;
	    exception
	       when others =>
		  put_line ("Enter a valid integer between 0 and 99");
	    end;
         end loop;
         put ("     ");
         put (x);
         put ("!  =  ");
         put (factorial(x));
         new_line(2);

      exception
	 when constraint_error =>
	    put ("OVERFLOW" );
            new_line(2);
	 when others =>
	    exit;
      end;
   end loop outer;

   put_line("Glad to have been of service!" );
end factr;

separate (factr)
function factorial (x:short_int)return short_int is
begin
   if x <= 1 then
      return 1;
   else
      return x * factorial (x-1);
   end if;
end factorial;
