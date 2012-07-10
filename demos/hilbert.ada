with screen_io, maze; use screen_io , maze;
with integer_text_io; use integer_text_io ;
procedure hilbert is
   here: position ;
   this_way: direction := up;
   last_d: direction := up;
   order: integer ;
   procedure draw_line(l: integer) is
       c: character ;
       steps: integer := l ;
   begin
       if this_way = right or this_way = left then 
	   c := '_' ; 
	   steps := 2* l ;   -- looks better this way.
       else 
	   c := '|' ;
       end if ;
       if steps = 0 then steps := 1 ; end if ;
       if this_way = down  or last_d = down then
          for i in 1..steps loop
	      here := next_pos(here, this_way) ;
	      putc(c, here.row, here.col) ;
          end loop ;
       else
          for i in 1..steps loop
	      putc(c, here.row, here.col) ;
	      here := next_pos(here, this_way) ;
          end loop ; 
       end if ;
       last_d := this_way ;
   end draw_line ;
   procedure turn(left_first: boolean) is
   begin
	if left_first then this_way := left_of(this_way) ; 
		else this_way := right_of(this_way) ;
	end if ;
   end turn ;
   procedure draw_hilbert(size, level: integer; left_first: boolean)  is
   begin
     if level = 0 then return ;
     else
	turn(left_first) ;
        draw_hilbert(size, level - 1, not left_first) ;
	draw_line(size) ;
	turn(not left_first) ;
        draw_hilbert(size, level - 1, left_first) ;
	draw_line(size) ;
        draw_hilbert(size, level - 1, left_first) ;
	turn(not left_first) ;
	draw_line(size) ;
        draw_hilbert(size, level - 1, not left_first) ;
	turn(left_first) ;
     end if ;
   end draw_hilbert ;
begin
   loop
      clear ;
      for i in 1..4 loop
         here := (22, 60) ;
	 clear ;
	 puts("Hilbert's curve", 2, 62) ;
	 --puts("  level  "& integer'image(i), 3, 62) ;
	 putsn("  level  ", i, 3, 62) ;
         draw_hilbert(integer(24.0/(2**i+1)), i, true);
      end loop ;
      end loop ;
end ;
