-- A pipeline version of the Sieve or Erastosthenes: we create a chain of tasks
-- each of which holds several primes. The main program feeds successive integers
-- into the pipe; each task tests the integer for divisibility by its own
-- primes, and passes it along to the next task if not divisible. Each task has
-- a pointer to its successor. The end of the pipeline creates a new task when
-- a new prime is discovered and its own complement of primes is full.
-- The value of max regulates the coarseness of the parallel computation.

package prime_dividers is
   type int is range 1..1000000 ;		-- for primes up to 10**6
   task type divider is
       entry my_first(x: int);			-- To initialize the task.
       entry maybe_prime(x: int) ;		-- for successive tests.
   end divider;
end prime_dividers ;

with text_io; use text_io;
package body prime_dividers is
   type pointer is access divider ;		-- who's next.

   procedure initialize(ptr: in out pointer; value: int) is
   begin
      ptr := new divider ;
      ptr.my_first(value) ;
   end initialize; 

   task body divider is
     max: constant := 10;			-- number of primes per task.
     subtype cap is integer range 1..max;
     my_primes: array(cap) of int ;
     last: cap := 1;
     is_prime: boolean := false ;
     next: pointer ;
     candidate: int ;
   begin
	accept my_first(x:int) do 
	    my_primes(last) := x ; 			-- now we know.
            put_line("new task with prime: "& int'image(x)) ;
        end ;
        loop
         select
           accept maybe_prime(x: int) do 
	       candidate := x; 
	       is_prime := true ;			  -- maybe.
	       for i in 1..last loop
                   if candidate mod my_primes(i) = 0 then -- not a prime.
			is_prime := false ;
			exit ;	
	           elsif my_primes(i)**2 > candidate then 
			exit ;				-- must be prime.
		   end if ;
               end loop  ;
            end maybe_prime ;
            if is_prime then
                 if last < max then			-- keep locally.
		    last := last +1 ;
		    my_primes(last) := candidate ;
                    put_line("new prime: "& int'image(candidate)) ;
	         elsif next = null then			-- need new task.
	              initialize(next, candidate) ; 		
 	         else
	              next.maybe_prime(candidate) ;	-- needs further test.
                 end if ; 
	     end if ;
         or
 	    terminate ;
         end select ;
         end loop;
    end divider;
end prime_dividers;
	
with prime_dividers; use prime_dividers ;
with text_io; use text_io;
procedure main is
   first_prime: divider ;			-- Beginning of pipeline.
begin
    first_prime.my_first(3) ;		-- No need to test even numbers
    for i in int range 2..2000 loop
        first_prime.maybe_prime(2*i+1) ;
    end loop;
end main ;



