--                      call5.ada
--
-- call for an entry of a completed but not yet terminated task
--
WITH text_io;
PROCEDURE main IS
  task t1 is
    entry e1;
  end t1;
  task body t1 is
    task t2 is  -- t2 depends on t1
      entry e2;
    end t2;
    task body t2 is
    begin
      loop
        select
          accept e2;
--        or
--          terminate;
        end select;
      end loop;
    end t2;

    task t3;    -- t3 depends on t1
    task body t3 is
    begin
      loop
        t2.e2;
        delay 0.5;
      end loop;
    end t3;

  begin
    accept e1;
    text_io.put_line("--------------------------------> TASK T1  COMPLETED");
                -- t1 is completed but not terminated
  end t1;


BEGIN
  t1.e1;
  delay 1.0;
    text_io.put_line("T1'TERMINATED = " & boolean'image(T1'terminated));
    text_io.put_line("T1'CALLABLE = " & boolean'image(T1'callable));
  t1.e1;
  text_io.put_line("-------------------------------------> MAIN COMPLETED");
END main;
