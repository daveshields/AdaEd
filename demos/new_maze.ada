----------------------------------------------------------------------
--
--                New_maze : create a new maze
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

with random_numbers; use random_numbers;
with system;
separate(maze)
procedure new_maze(start, goal: position; num_lines: integer) is
    -- create a new maze with a given number of paths, including two long ones 
    -- that lead to source and destination.
    pos: position;
    d: direction ;
    l: integer ;
 
    task type liner is
        -- one is created for each path.
        entry draw(pos: position; dir: direction; len: integer);
    end liner;
 
    type new_liner is access liner ;
    next_line: new_liner ;
 
    function max_len(p: position; d: direction) return integer is
        -- establish distance from any point to boundary, 
        -- along a given direction.
    begin
        case d is
 	    when up    => return p.row ;
 	    when right => return (80 - p.col) ;
 	    when down  => return (23 - p.row) ;
 	    when left  => return p.col ;
        end case ;
    end max_len;
 
    task body liner is
        p: position ;
        d: direction ;
        l: integer;
    begin
        accept draw(pos: position; dir:direction; len: integer) do
 	p := pos ;
 	d := dir ;
 	l := len ;
    end draw ;
        for i in 1..l loop 
  	    putc(' ', p.row, p.col) ;
 	    dist(p.row, p.col) := max_dist ;
 	    p := next_pos(p, d) ;
        end loop ;
    end liner ;
 
begin
    clear ;
    case SYSTEM.SYSTEM_NAME is
	when SYSTEM.PC_DOS =>
	    fill_screen(ASCII.SI);
	when others =>
	    fill_screen('#');
    end case;
    pos := start ;		-- first path starts at source.
    d := up;			-- which is always on bottom row.
    l := 20 ;
    for i in 1..num_lines loop
        -- create the right number of tasks, and start each at a random posi-
        -- tion, going in a random direction towards the boundary.
        next_line := new liner ;
        next_line.draw(pos, d, l) ;
        pos := (2*(1 + random_int(11)), 2*(1 + random_int(38))) ;
        d := direction'val(random_int(40) mod 4) ;
        l := max_len(pos, d) ;
        l := l/2 + random_int(l/4) ;
    end loop ;
     -- One more for path leading to destination. (always on top row).
    next_line := new liner ;
    next_line.draw(goal, down, 22) ;
exception
    when storage_error | program_error  =>
	puts("unable to create new tasks. Try simpler maze.", 23,1);
end new_maze ;
 
