----------------------------------------------------------------------
--
--                    Semaphore Package
--
--                      written by
--
--                   Edmond Schonberg
--
--                      Ada Project
--                   Courant Institute
--                  New York University
--                   251 Mercer Street
--                New York, New York  10012
--
-----------------------------------------------------------------------

package SEMAPHORE is

   generic

      INIT: NATURAL;  -- initial value of semaphore

   package COUNT_SEMAPHORE is
   
      task COUNTING_SEMAPHORE is --similar to Amoroso's counting semaphore
           entry P;
           entry V;
      end COUNTING_SEMAPHORE;

   end COUNT_SEMAPHORE;

   task type BINARY_SEMAPHORE is -- implements binary semaphores as suggested by
        entry P;                 -- Amoroso and Ingargiola.
        entry V;
   end BINARY_SEMAPHORE;   

   type ACCESS_BINARY_SEMAPHORE is access BINARY_SEMAPHORE;

end SEMAPHORE;

package body SEMAPHORE is

   package body COUNT_SEMAPHORE is

      task body COUNTING_SEMAPHORE is
           S: INTEGER := INIT;
      begin
           loop    -- run forever, waiting for P or V to be called
               select
                  when S > 0 => accept P; S := S - 1;
               or
                  accept V; S := S + 1; -- S > INIT implies that new resources
               end select;              -- became available that were originally
           end loop;                    -- unknown. This is not like Amoroso's
       end COUNTING_SEMAPHORE;          -- version.
    
    end COUNT_SEMAPHORE;

    task body BINARY_SEMAPHORE is
    begin
      loop
	 select
             accept P;
	 or
	     terminate ;
         end select ;
         accept V;
      end loop;
    end BINARY_SEMAPHORE;

end SEMAPHORE;
