I think there is a problem of memory deallocation.
For instance when you run the following program, after a moment you get an 
error of 'swap space' ...

In fact, the compiler don't seem to deallocate the locals variables.

-------------------------
procedure test2 is

          procedure x is
            c : integer;
          begin
                c := 1;
          end;

begin
        while true loop 
              x;
        end loop;
end test2;
