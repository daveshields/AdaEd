with TEXT_IO; use TEXT_IO;
procedure PRIMES is

   package INT_IO is new INTEGER_IO(INTEGER);
   use INT_IO;

   NUM_PRIMES : constant := 5;
   COUNT      : INTEGER := 0;

   function IS_PRIME(P : INTEGER) return BOOLEAN is
   begin

      if P < 2 then 
         return FALSE;
      end if;

      for I in 2 .. P loop
         if I * I > P then
	    return TRUE;
	 elsif P mod I = 0 then
	    return FALSE;
	 end if;
      end loop;

   end IS_PRIME;

begin

   PUT_LINE("The first " & INTEGER'image(NUM_PRIMES) & " primes are:");
   for P in 2 .. INTEGER'LAST loop
      if IS_PRIME(P) then
	PUT(P);
        PUT(" ");
	COUNT := COUNT + 1;
	exit when COUNT = NUM_PRIMES;
      end if;
   end loop;

   NEW_LINE;

end PRIMES;
