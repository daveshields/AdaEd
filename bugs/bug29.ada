procedure test1 is

type rec (k : positive := 1) is
  record
    name : string(1 .. k);
  end record;

   -- ok when discriminant has no default value and discriminant
   -- constraint specified explicity on the declaration
  v1 : rec;

  -- also crashes with declaration below
  -- v1 : rec(100); 

begin
  null;
end test1;
