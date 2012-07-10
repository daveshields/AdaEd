-- DEMONSTRATION PROGRAM:
--   
--     Producer Consumer Tasking example
--

with text_io; use text_io;
procedure tasker is

task buffer is
  entry read  (c: out integer);
  entry write (c: in integer);
end;

task producer;

task consumer;

task body buffer is separate;
task body producer is separate;
task body consumer is separate;

begin
  null;
end tasker;

------------------------------------------------------------------------

separate(tasker)
task body buffer is
  pool_size : constant integer := 3;
  pool      : array(integer range 1..pool_size) of integer;
  count     : integer range 0..pool_size := 0;
  in_index, out_index : integer range 1..pool_size := 1;
begin
  loop
    select
      when count < pool_size =>
	accept write (c: in integer) do
	  pool (in_index) := c;
	end;
	in_index := in_index mod pool_size + 1;
	count := count + 1;
    or
      when count > 0 =>
	accept read (c: out integer) do
	  c := pool (out_index);
	end;
	out_index := out_index mod pool_size + 1;
	count := count - 1;
     or
	terminate;
     end select;

   end loop;

end buffer;

------------------------------------------------------------------------

separate(tasker)
task body producer is
begin
  for count in 1 .. 6
  loop
    put_line("Entry call to write in buffer number: "
		& integer'image(count));
    buffer.write (count);
    put_line("Entry call to write complete.");
  end loop;
  buffer.write (0);
end producer;

------------------------------------------------------------------------

separate(tasker)
task body consumer is
  use text_io;
  count: integer;
begin
  loop
    put_line("Entry call to read to get number.");
    buffer.read (count);
    exit when count = 0;
    put_line("Entry call to read obtained number: "
		& integer'image(count));
  end loop;
end consumer;

------------------------------------------------------------------------
