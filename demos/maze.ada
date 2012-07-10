----------------------------------------------------------------------
--
--                     Maze Package
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

package maze is
   -- basic data structures.
   type position is record
       row, col: integer ;
   end record ;

   type direction is (up, right, down, left) ;
   goal: position ;

   -- The array dist is a shared data structure, accessed by all exploring
   -- tasks. A given position p in the maze has been visited by some task if
   --     dist(p.pos, p.col) < max_dist.
   dist: array(1..24, 1..80) of integer ;
   max_dist: integer:= 1000 ;

   -- procedures to navigate the maze.

   function open(p: position) return boolean ;
   procedure mark(p: position; d: direction) ;
   procedure new_maze(start, goal: position; num_lines: integer) ;
   function next_pos(p: position; d: direction) return position;
   function right_of(d: direction) return direction ;
   function left_of (d: direction) return direction ;
   function back_of (d: direction) return direction ;
end maze ;

with maze; use maze;
package first_task is
  type ex ;
  type explore is access ex ;
  task type ex is
     entry start(p: position; d: direction; me, parent: explore) ;
     entry report(success: boolean; where: position) ;
  end ex ;
end first_task ;


with screen_io; use screen_io;
with system;
package body maze is

   function next_pos(p: position; d:direction) return position is
       new_p: position := p;
   begin
      case d is
	  when up    => new_p.row := p.row - 1; 
	  when right => new_p.col := p.col + 1;
	  when down  => new_p.row := p.row + 1; 
	  when left  => new_p.col := p.col - 1;
      end case;
      if new_p.row > 23 or new_p.row < 1 or
	 new_p.col > 80 or new_p.col < 1 then
	 return p ;
      else
	 return new_p ;
      end if ;
   end next_pos ;

   function right_of(d: direction) return direction is
   begin
       return direction'val((direction'pos(d) + 1)  mod 4 ) ;
   end ;
   function left_of (d: direction) return direction is
   begin
       return direction'val((direction'pos(d) + 3)  mod 4 ) ;
   end ;

   function back_of (d: direction) return direction is
   begin
       return direction'val((direction'pos(d) + 2)  mod 4 ) ;
   end ;

   function open(p: position) return boolean is
   -- Determine whether a given location has already been explored.
   begin
      return dist(p.row, p.col) = max_dist ;
   end open;

   procedure mark(p: position; d: direction) is
   -- Indicate on the screen the current position of an exploring task.
       c: character ;
   begin
       case SYSTEM.SYSTEM_NAME is
	   when SYSTEM.PC_DOS => 
	       if d = up then c := ASCII.CAN;
	       elsif d = down then c := ASCII.EM;
	       elsif d = left then c := ASCII.DC1;
	       elsif d = right then c := ASCII.DLE;
               end if ;
	   when others =>
       	       if d = up or d = down then c := '|' ; 
	       else c := '-' ; 
	       end if ;
	   end case; 
       putc(c, p.row, p.col);
   end mark;

   procedure new_maze(start, goal: position; num_lines: integer)  is separate ;

begin
   -- initialize dist to indicate that all is terra incognita.
   for i in dist'range(1) loop
      for j in dist'range(2) loop
	 dist(i, j) := 0 ;
      end loop;
    end loop;
end maze ;

with system;
with screen_io; use screen_io;
package body first_task is
    subtype same_ex is ex ;

    task census is
        -- keeps track of the number of active exploring tasks.
	 entry update(del: integer) ;
    end census ;

    task body census is
        population: integer := 1 ;
    begin
	 loop
	     select
  	         accept update(del: integer) do
	         population := population + del ;
	         putsn("active tasks: " , population, 1,1) ;
	         end update ;
	     or
	         terminate ;
            end select ;
        end loop ;
    end census ;

    task body ex is
	-- A new exploring task is created whenever an active exploring task
	-- finds an unexplored cell to the right or left of its current pos.
	-- Each such task has a pointer to itself and to its parent. When it
	-- reaches a dead end, it waits for a report from each son, and then
	-- reports in turn to its parent. The first task to read the goal re-
	-- ports success to its parent, and the successful path is retraced.
	
	 
	pos, new_pos, start_pos: position ;
        dir: direction ;
        found: boolean := false;
        self, pop: explore ;
        progeny: integer := 0 ;

        procedure try_turn(new_dir: direction) is
	   -- see if path exists to right or left of current position.
            new_pos: position := next_pos(pos, new_dir) ;
	     son: explore;
        begin
	    if open(new_pos) then
	        -- This test and the corresponding spawn should be a critical
	        -- section. As it stands, the program is clearly erroneous,
	        -- as  the shared variable -dist-  is being accessed 
	        -- without explicit synchronization.
	        --  The algorithm works in any case, and the benign rare 
		-- condition here is left to allow for greater parallelism,
		--  at the possible expense of additional (short-lived 
		-- and superflouous) tasks.

	        son := new same_ex ;
	        progeny := progeny + 1 ;
	        census.update(1) ;
	        son.start(pos, new_dir, son, self) ;
             end if ;
         end try_turn;

	 procedure retrace(there, here: position) is
	     -- mark the path to success, in reverse.
	     bck: direction := back_of(dir);
	     pos: position := there;
	     ch:  character;
	begin
	    case SYSTEM.SYSTEM_NAME is
		when SYSTEM.PC_DOS =>
		    ch := ASCII.EOT;
		when others =>
		    ch := '+';
		end case;
		while pos /= here loop
		    putcb(ch, pos.row, pos.col) ;
		    pos := next_pos(pos, bck) ;
		end loop ;
	end retrace ;

    begin
        -- upon creation, get identity from creator, and current location.
        accept start(p: position; d: direction; me, parent: explore) do
	    start_pos := p ;
            pos  := next_pos(p, d) ;
            dir  := d ;
	    self := me ;
	    pop  := parent ;
        end start ;

        putc('O', pos.row, pos.col) ;		-- hatch.
        putc('o', pos.row, pos.col) ;

        begin
            loop
	        mark(pos, dir) ;
	        dist(pos.row, pos.col) := 0 ;		-- we've been here.
                try_turn(right_of(dir)) ;		-- look both ways.
                try_turn(left_of(dir)) ;
	        new_pos := next_pos(pos, dir) ;	-- and proceed.
	        exit when new_pos = goal or not open(new_pos) ;
	        pos := new_pos;
            end loop ;
	exception
	    when storage_error | program_error =>
		puts("unable to create new tasks. Try simpler maze.", 23,1);
	end ;

	if new_pos = goal then
	    putc(ascii.bel, goal.row, goal.col);	-- bingo!
	    found := true ;
	else
	    for i in 1..progeny loop		-- anyone got there?
	        accept report(success: boolean; where: position) do
		    found := success ;
		    pos := where ;
  	        end report ;
	        exit when found ;
	    end loop;
	end if ;
	if found then
	    retrace(pos, start_pos) ;
	end if ;
	if pop /= self then			-- not true for first task.
	    if pop'callable then
	        pop.report(found, start_pos) ;
	    end if ;
	elsif not found then
	    puts("no  way from here to there      ", 23, 1);
	end if ;

        census.update(-1) ;			-- exit discretely.
    end ex ;

 end first_task;
