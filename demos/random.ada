
----------------------------------------------------------------------
--
--                 Random Number Generator
--
--                      written by
--
--                     David Shields
--
--                      Ada Project
--                   Courant Institute
--                  New York University
--                   251 Mercer Street
--                New York, New York  10012
--
-----------------------------------------------------------------------

package random_numbers is
    rand_seed: integer := 1;
    function random_int(r: integer) return integer;
    -- returns random integer in the range 0 ..(r-1).
    procedure set_seed(r: integer); -- set random seed
end random_numbers;

with calendar; use calendar;
package body random_numbers is
    function random_int(r:integer) return integer is
         rvar: float;
    begin
        -- the values used for random number generation avoid overflow
        -- on 16 bit (and larger) machines.
	-- The values are as given in Gimpel, Programming in SNOBOL.
        rand_seed := (rand_seed * 59) mod 491;
        rvar := float(rand_seed) / 491.0;
        -- assume machine rounds, so use r-1
        return integer(rvar * float(r-1));
   
    end;

    procedure set_seed(r: integer) is
    begin
        rand_seed := r;
    end;

begin
    -- set initial value from clock (avoid overflow if 16 bit integers)
    rand_seed := integer(float(seconds(clock)) / 200.0 ) ;
end random_numbers;

