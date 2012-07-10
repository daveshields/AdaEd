WITH Text_IO;
WITH My_Int_IO;
WITH My_Flt_IO;
WITH Math;
PROCEDURE SquareRoots IS

 -- Illustrates the square root function provided by Math

  MaxNumber : CONSTANT Positive := 20;
  FltNum    : Float;

BEGIN  -- SquareRoots   

  Text_IO.Put (Item => "Number  Square Root");
  Text_IO.New_Line;
  Text_IO.Put (Item => "------  -----------");
  Text_IO.New_Line;

  FltNum := 1.0;
  FOR Number IN 1..MaxNumber LOOP
    My_Int_IO.Put (Item => Number, Width => 3);
    My_Flt_IO.Put (Item => Math.Sqrt (Float(Number)), 
                   Fore => 7, Aft => 5, Exp => 0);
    My_Flt_IO.Put (Item => Math.Sqrt (FltNum), 
                   Fore => 7, Aft => 5, Exp => 0);
    Text_IO.New_Line;
    FltNum := FltNum + 1.0;
  END LOOP;

END SquareRoots;
