procedure main IS
   package pack is 
     function func return integer;
   end pack;
   package body pack is
     function func return integer is 
     begin
       return 1;
     end func; 
   end pack;
begin
   null;
exception
   when pack.func.error =>
      null;
end main;
