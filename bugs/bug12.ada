procedure integer_image is

  c : character;
  j : integer := 3;
  k : constant integer := 3;

begin
  for i in 1 .. 3 loop
    c := integer'image(k)(2); -- ok
    c := integer'image(3)(2); -- ok
    c := integer'image(i)(2); -- causes error
    c := integer'image(j)(2); -- causes error
  end loop;
end integer_image;

