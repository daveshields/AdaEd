with text_io;
procedure bug4 is
  x : integer := integer'first;
  y : integer := integer'first + 1;
begin
  text_io.put_line("X = " & integer'image(x));
  text_io.put_line("Y = " & integer'image(y));
end bug4;
