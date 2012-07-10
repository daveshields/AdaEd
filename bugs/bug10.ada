procedure main is
  aft : integer := 1;
  s, str : string(1..3);
begin
  s := "abc";
  str((aft)..3) := s(1..3);
end;
