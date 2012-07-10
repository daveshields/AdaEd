package Tables is 
  procedure Foo ;
end Tables;
----------------------------
package Checked_text_io is
   procedure Foo;
end Checked_text_io;
----------------------------
package body Checked_text_io is
  procedure Foo is 
  begin null; end Foo;
end Checked_text_io;
----------------------------
with Checked_Text_Io;
package body Tables is
   package CTIO renames Checked_Text_IO;
   procedure Foo is 
   begin null; end;
end Tables ;
