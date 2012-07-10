with text_io; 
package int_io is new text_io.integer_io(integer);

-- ERROR
-- text_io incorrectly made visible by "with int_io;"
--
with int_io;
procedure main is
begin
  text_io.put_line("hello");
end;

