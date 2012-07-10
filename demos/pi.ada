generic
   type real is digits <>;
function sqrt(y : real) return real;

function sqrt(y : real) return real is
   x, t : real := y;
begin
   if y < 0.0 then 
      raise NUMERIC_ERROR;
   else
      loop
	 t := (x + y / x)/ 2.0;
	 exit when abs(x - t) <= real'epsilon;
	 x := t;
      end loop;
      return x;
   end if;
end sqrt;

with sqrt;
with text_io; use text_io;
procedure main is

   package real_io is new FLOAT_IO(float);
   use real_io;

   package int_io is new INTEGER_IO(integer);
   use int_io;

   epsilon : constant := float'epsilon;

   function sqrt is new sqrt(float);

   procedure pi_comp is

      pi : float := 1.0;
      n  : integer := 1;
      temp : float;
      sum : float := 1.0;

   begin
      loop

	n := n + 2;
	temp := 1.0 / float(n) ** 4;

	put("Term number ");
	put((n + 1)/2);
	put(" is: ");
	put(temp);
	new_line;

	exit when temp <= epsilon;

        sum := sum + temp;

      end loop;

      put("The sum is: ");
      put(sum);
      new_line;

      pi := sqrt(sqrt(96.0 * sum));

      put("The value of PI is ");
      put(pi);
      new_line;

   end pi_comp;

begin
   pi_comp;
end main;
