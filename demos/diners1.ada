--::::::::::
--io_libs.ada
--::::::::::
-- Precompiled instantiations of Integer_IO and
-- Float_IO for the predefined Integer and Float types
 
WITH Text_IO;
PACKAGE My_Int_IO IS
  NEW Text_IO.Integer_IO (Num => Integer);
 
WITH Text_IO;
PACKAGE My_Flt_IO IS
  NEW Text_IO.Float_IO   (Num => Float);
--::::::::::
--random.ads
--::::::::::
PACKAGE Random IS
 
-- Simple pseudo-random number generator package.
-- Adapated from the Ada literature by
-- Michael B. Feldman, The George Washington University, November 1990.
 
  PROCEDURE Set_Seed (N : Positive);
 
  FUNCTION  Unit_Random RETURN Float;
 
    --returns a float >=0.0 and <1.0
 
  FUNCTION  Random_Int (N : Positive) RETURN Positive;
 
    --return a random integer in the range 1..N
 
END Random;
--::::::::::
--chop.ads
--::::::::::
PACKAGE Chop IS
 
  TASK TYPE Stick IS
    ENTRY Pick_Up;
    ENTRY Put_Down;
  END Stick;
 
END Chop;
--::::::::::
--phil.ads
--::::::::::
PACKAGE Phil IS
  
  TASK TYPE Philosopher IS
    
    ENTRY Come_To_Life (My_ID :      Positive; 
                        Chopstick1 : Positive;
                        Chopstick2 : Positive);
 
  END Philosopher;
 
  TYPE States IS (Breathing, Thinking, Eating, Done_Eating,
                    Got_One_Stick, Got_Other_Stick);
 
END Phil;
--::::::::::
--room.ads
--::::::::::
WITH Chop;
WITH Phil;
PACKAGE Room IS
 
  Table_Size: CONSTANT := 5;
  SUBTYPE Table_Type IS Positive RANGE 1..Table_Size;
 
  Sticks:     ARRAY(Table_Type) OF Chop.Stick;
 
  TASK Head_Waiter IS
    ENTRY Open_The_Room;
    ENTRY Report_State(Which_Phil: Table_Type;
                       State: Phil.States;
                       How_Long: Natural := 0);
  END Head_Waiter;
 
END Room;
--::::::::::
--diners.ada
--::::::::::
WITH Room;
PROCEDURE Diners IS
 
BEGIN
  Room.Head_Waiter.Open_The_Room;
  LOOP
    DELAY 20.0;
  END LOOP;
END Diners;
--::::::::::
--random.adb
--::::::::::
WITH Calendar;
USE  Calendar;
 
PACKAGE BODY Random IS
 
-- Body of random number generator package.
-- Adapted from the Ada literature by
-- Michael B. Feldman, The George Washington University, November 1990.
 
  Modulus      : CONSTANT := 9317;
 
  TYPE Int_16 IS RANGE - 2 ** 15 .. 2 ** 15 - 1;
 
  TYPE Int_32 IS RANGE - 2 ** 31 .. 2 ** 31 - 1;
 
  SUBTYPE Seed_Range IS Int_16 RANGE 0 .. (Modulus - 1);
 
  Seed,
  Default_Seed : Seed_Range;
 
  PROCEDURE Set_Seed (N : Positive) IS SEPARATE;
 
  FUNCTION  Unit_Random RETURN Float IS SEPARATE;
 
  FUNCTION  Random_Int (N : Positive) RETURN Positive IS SEPARATE;
BEGIN
  Default_Seed := Int_16 (Int_32 (Seconds (Clock)) MOD Modulus);
  Seed := Default_Seed;
END Random;
 
SEPARATE (Random)
 
PROCEDURE Set_Seed (N : Positive) IS
BEGIN
  Seed := Seed_Range (N);
END Set_Seed;
 
SEPARATE (Random)
 
FUNCTION  Unit_Random RETURN Float IS
  Multiplier : CONSTANT := 421;
  Increment  : CONSTANT := 2073;
  Result     : Float;
BEGIN
  Seed := (Multiplier * Seed + Increment) MOD Modulus;
  Result := Float (Seed) / Float (Modulus);
  RETURN Result;
EXCEPTION
  WHEN Constraint_Error | Numeric_Error =>
    Seed := Int_16 ((Multiplier * Int_32 (Seed) + Increment) MOD Modulus);
    Result := Float (Seed) / Float (Modulus);
    RETURN Result;
 
END Unit_Random;
 
SEPARATE (Random)
 
FUNCTION  Random_Int (N : Positive) RETURN Positive IS
  Result : Integer RANGE 1 .. N;
BEGIN
  Result := Integer (Float (N) * Unit_Random + 0.5);
  RETURN Result;
EXCEPTION
  WHEN Constraint_Error | Numeric_Error =>
    RETURN 1;
 
END Random_Int;
--::::::::::
--chop.adb
--::::::::::
PACKAGE BODY Chop IS
 
  TASK BODY Stick IS
 
  BEGIN
    
    LOOP
      SELECT
        ACCEPT Pick_Up;
        ACCEPT Put_Down;
      OR
        TERMINATE;
      END SELECT;
    END LOOP;
 
  END Stick;
 
END Chop;
--::::::::::
--phil.adb
--::::::::::
WITH Room;
WITH Random;
PACKAGE BODY Phil IS
  
  TASK BODY Philosopher IS
 
    Who_Am_I   : Positive;
    First_Grab : Positive;
    Second_Grab: Positive;
    Meal_Time  : Natural;
    Think_Time : Natural;
    
  BEGIN
    ACCEPT Come_To_Life (My_ID :     Positive; 
                        Chopstick1 : Positive;
                        Chopstick2 : Positive) DO
      Who_Am_I    := My_ID;
      First_Grab  := Chopstick1;
      Second_Grab := Chopstick2;
 
    END Come_To_Life;
 
    Room.Head_Waiter.Report_State(Who_Am_I, Breathing);
 
    LOOP
 
      Room.Sticks(First_Grab).Pick_Up;
      Room.Head_Waiter.Report_State(Who_Am_I, Got_One_Stick, First_Grab);
 
      Room.Sticks(Second_Grab).Pick_Up;
      Room.Head_Waiter.Report_State(Who_Am_I, Got_Other_Stick, Second_Grab);
 
      Meal_Time := Random.Random_Int(10);
      Room.Head_Waiter.Report_State(Who_Am_I, Eating, Meal_Time);
 
      DELAY Duration(Meal_Time);
      Room.Head_Waiter.Report_State(Who_Am_I, Done_Eating);
 
      Room.Sticks(First_Grab).Put_Down;
      Room.Sticks(Second_Grab).Put_Down;
 
      Think_Time := Random.Random_Int(10);
      Room.Head_Waiter.Report_State(Who_Am_I, Thinking, Think_Time);
      DELAY Duration(Think_Time);
 
    END LOOP;
 
  END Philosopher;
 
END Phil;
--::::::::::
--roomline.adb
--::::::::::
WITH Text_IO;
WITH Chop;
WITH Phil;
WITH Calendar;
PRAGMA Elaborate(Phil);
PACKAGE BODY Room IS
 
-- A line-oriented version of the Room package, for line-oriented
-- terminals like IBM 3270's where the user cannot do ASCII screen control.
-- This is the only file in the dining philosophers system that needs
-- changing to use in a line-oriented environment.
-- Michael B. Feldman, The George Washington University, November 1990.
 
 
  Phils:      ARRAY(Table_Type) OF Phil.Philosopher;
 
  TYPE Phil_Names IS (Dijkstra, Texel, Booch, Ichbiah, Stroustrup);
 
  TASK BODY Head_Waiter IS
 
    T : Integer;
    Start_Time: Calendar.Time;
    Phil_Names: CONSTANT ARRAY(1..5) OF String(1..18) :=
     ("Eddy Dijkstra     ",
      "Putnam Texel      ",
      "Grady Booch       ",
      "Jean Ichbiah      ",
      "Bjarne Stroustrup ");
    Blanks : CONSTANT String := "     ";
 
  BEGIN
 
    ACCEPT Open_The_Room;
    Start_Time := Calendar.Clock;
 
    Phils(1).Come_To_Life(1,1,2);
    Phils(3).Come_To_Life(3,3,4);
    Phils(2).Come_To_Life(2,2,3);
    Phils(5).Come_To_Life(5,1,5);
    Phils(4).Come_To_Life(4,4,5);
 
    LOOP
      SELECT
        ACCEPT Report_State(Which_Phil: Table_Type;
                         State: Phil.States;
                         How_Long: Natural := 0) DO
          T := Integer(Calendar."-"(Calendar.Clock,Start_Time));
          Text_IO.Put( "T=" & Integer'Image(T) & " "
            & Blanks(1..Which_Phil) & Phil_Names(Which_Phil));
 
          CASE State IS
 
            WHEN Phil.Breathing =>
              Text_IO.Put("Breathing");
            WHEN Phil.Thinking =>
              Text_IO.Put( "Thinking"
                         & Integer'Image(How_Long)
                         & " seconds.");
            WHEN Phil.Eating =>
              Text_IO.Put( "Eating"
                         & Integer'Image(How_Long)
                         & " seconds.");
            WHEN Phil.Done_Eating =>
              Text_IO.Put("Yum-yum (burp)");
            WHEN Phil.Got_One_Stick =>
              Text_IO.Put( "First chopstick"
                          & Integer'Image(How_Long));
            WHEN Phil.Got_Other_Stick =>
              Text_IO.Put( "Second chopstick"
                          & Integer'Image(How_Long));
 
          END CASE;
          Text_IO.New_Line;
 
         END Report_State;
        OR
          TERMINATE;
        END SELECT;
 
      END LOOP;
 
    END Head_Waiter;
 
END Room;

