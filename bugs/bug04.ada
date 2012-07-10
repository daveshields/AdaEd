generic
package gene is
end gene;

with text_io;
package body gene is
   -- Different error message  with/without  line below commented out 
   --package flt_io is new text_io.float_io(float);
   procedure test is
   begin
     text_io.new_line;
   end;
end gene;

with gene;
procedure bug1 is
  package my_pkg is new gene;
begin
  null; 
end bug1;


