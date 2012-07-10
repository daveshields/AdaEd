-- A generic sorting package, with a parallel quicksort algorithm: each
-- half of the partitioned array is sorted by a separate task.

generic
   type DATA is private;
   type INDEX is (<>);
   with function "<"(X,Y: DATA) return BOOLEAN is <> ;
package SORTS is
   type TABLE is array (INDEX range <>) of DATA;
   procedure QUICKSORT (TAB: in out TABLE);
end SORTS;


package body SORTS is
 
   procedure QUICKSORT( TAB: in out TABLE ) is
      
      task type QSORT is
         entry BOUNDS( L,R: in INDEX );
      end QSORT;
      
      -- The name of the task cannot be used as  a type mark within the
      -- task body. To allow recursive spawning, we make a subtype of it

      subtype SQSORT is QSORT; 

      type AQSORT is access QSORT;
      TSORT:AQSORT;

      task body QSORT is
         TRIGHT,TLEFT: AQSORT;
         LEFT,RIGHT,IL,IR: INDEX;
         MID,TEMP: DATA;
      begin

         accept BOUNDS( L,R: in INDEX ) do
	    -- Acquire bounds of subarray to sort.
            LEFT := L; RIGHT := R;
         end BOUNDS;

         IL := LEFT; IR := RIGHT;

	 -- Pick partitioning element (arbitrarily, in the middle).
         MID := TAB( INDEX'VAL( (INDEX'POS(IL)+INDEX'POS(IR))/2) );

         loop				-- partitioning step.
            while TAB(IL) < MID
            loop
               IL:=INDEX'SUCC(IL);
            end loop;

            while MID < TAB(IR)
            loop
               IR:=INDEX'PRED(IR);
            end loop;

            if IL <= IR then
               TEMP := TAB(IL);
               TAB(IL) := TAB(IR);
               TAB(IR) := TEMP;
               IL:=INDEX'SUCC(IL);
               IR:=INDEX'PRED(IR);
            end if;
            exit when IL > IR;
         end loop;

         if LEFT < IR then		-- spawn new task for left side.
            TLEFT := new SQSORT;
            TLEFT.BOUNDS(LEFT,IR);
         end if;

         if IL < RIGHT then		-- ditto for right side.
            TRIGHT := new SQSORT;
            TRIGHT.BOUNDS(IL,RIGHT);
         end if;
      end QSORT;
        
   begin
      TSORT := new QSORT;		-- Main task for whole array.
      TSORT.BOUNDS( TAB'FIRST, TAB'LAST );
   end QUICKSORT;

end SORTS;

with SORTS;
with TEXT_IO;  use TEXT_IO;

procedure MAIN is

  package SORT_I is new SORTS( INTEGER,   INTEGER) ;
  package SORT_C is new SORTS( CHARACTER, INTEGER) ;
  use SORT_I, SORT_C ;

  package INT_IO is new INTEGER_IO(integer); use INT_IO;

  subtype VECT is SORT_I.TABLE(1..8);
  subtype CHRS is SORT_C.TABLE(1..8);

  A: VECT := (-7, 14, 1, 92, 8,-6, 3, 2);
  B: CHRS := "Alleluia" ;

begin
   put_line("Sort integers") ;
   QUICKSORT(A);
   for I in A'RANGE loop
     PUT (A(I));
   end loop;
   NEW_LINE;

   put_line("Sort characters") ;
   QUICKSORT(B);
   for I in B'RANGE loop
     PUT (B(I));
   end loop;
   NEW_LINE;

end MAIN;
