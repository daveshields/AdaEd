----------------------------------------------------------------------
--
--              Maze Demonstration Main Program
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


with maze, first_task, screen_io; 
use maze, first_task, screen_io ;
with text_io, integer_text_io; 
use text_io, integer_text_io;

with random_numbers; use random_numbers;
procedure draw is
   start: position := (23, 10) ;
   goal : position := (1, 66) ;
   first_one: explore := new ex;
   num_lines: positive;
   rint: integer;
begin
    clear ;
    loop -- loop to get number of paths and random number seed.
	puts(" enter desired number of paths in maze", 1, 1);
       begin
	   get(num_lines) ;
	   exit ;
       exception
          when others => 
	     puts("invalid data. Please make it a positive no.", 1, 1) ;
	     skip_line;
       end ;
    end loop;
    loop
	puts(" enter random seed (0 for value based on clock) ", 3, 1);
       begin
	   get(rint) ;
	   if rint /= 0 then 
	       set_seed(rint); 
	       rint := rand_seed;
	   end if;
	   exit ;
       exception
          when others => 
	     puts("invalid data. Please make it a positive no.", 3, 1) ;
	     skip_line;
       end ;
    end loop;
    maze.goal := goal ;
    new_maze(start, goal, num_lines) ; -- build new maze
    putc('@', goal.row,  goal.col) ;   -- note starting point
    putc('*', start.row, start.col) ;  -- note ending point
    first_one.start(start, up, first_one, first_one) ; -- solve maze
end ;
