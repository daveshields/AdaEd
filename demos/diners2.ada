--::::::::::
--screen.ads
--::::::::::
PACKAGE Screen IS

-- Procedures for drawing pictures on ANSI Terminal Screen

  ScreenDepth : CONSTANT Integer := 24;
  ScreenWidth : CONSTANT Integer := 80;

  SUBTYPE Depth IS Integer RANGE 1..ScreenDepth;
  SUBTYPE Width IS Integer RANGE 1..ScreenWidth;

  PROCEDURE Beep; 
  PROCEDURE ClearScreen; 
  PROCEDURE MoveCursor (Column : Width; Row : Depth);

END Screen;   
--::::::::::
--windows.ads
--::::::::::
WITH Screen;
USE Screen;
PACKAGE Windows IS

  TYPE Window IS PRIVATE;

  PROCEDURE Open (W      : IN OUT Window; -- Window variable returned 
                  Row    : Depth; -- Upper left corner
                  Column : Width;
                  Height : Depth; -- Size of window
                  Width  : Screen.Width);

  -- Create a window variable and open the window for writing.  
  -- No checks for overlap of windows are made. 


  PROCEDURE Close (W : IN OUT Window);
  -- Close window and clear window variable. 


  PROCEDURE Title (W     : IN OUT Window;
                   Name  : String;
                   Under : Character);

  -- Put a title name at the top of the window.  If the parameter 
  -- under <> 0C or ' ', underline the title with the specified character. 


  PROCEDURE Borders (W                    : IN OUT Window;
                     Corner, Down, Across : Character);

  -- Draw border around current writable area in window with characters
  -- specified.  Call this BEFORE Title.  


  PROCEDURE Gotorowcolumn (W      : IN OUT Window;
                           Row    : Depth;
                           Column : Width);

  -- Goto the row and column specified.  Coordinates are relative to the
  -- upper left corner of window, which is (1, 1) 


  PROCEDURE Put (W  : IN OUT Window;
                 Ch : Character);

  -- put one character to the window.
  -- If end of column, go to the next row.
  -- If end of window, go to the top of the window. 


  PROCEDURE Put_String (W : IN OUT Window;
                        S : String);

  -- put a string to window. 


  PROCEDURE New_Line (W : IN OUT Window);

  -- Go to beginning of next line.  Next line is
  -- not blanked until next character is written  


PRIVATE
  TYPE Window IS
    RECORD
      Currentrow, -- Current cursor row 
      Firstrow,
      Lastrow : Depth;
      Currentcolumn, -- Current cursor column 
      Firstcolumn,
      Lastcolumn : Width;
    END RECORD;

END Windows;
--::::::::::
--screen.adb
--::::::::::
WITH Text_IO;
WITH My_Int_IO;
PACKAGE BODY Screen IS

-- Procedures for drawing pictures on ANSI Terminal Screen


  PROCEDURE Beep IS
  BEGIN
    Text_IO.Put (Item => ASCII.BEL);
  END Beep;

  PROCEDURE ClearScreen IS
  BEGIN
    Text_IO.Put (Item => ASCII.ESC);
    Text_IO.Put (Item => "[2J");
  END ClearScreen;

  PROCEDURE MoveCursor (Column : Width; Row : Depth) IS
  BEGIN                                                
    Text_IO.New_Line;
    Text_IO.Put (Item => ASCII.ESC);
    Text_IO.Put ("[");
    My_Int_IO.Put (Item => Row, Width => 1);
    Text_IO.Put (Item => ';');
    My_Int_IO.Put (Item => Column, Width => 1);
    Text_IO.Put (Item => 'f');
  END MoveCursor;  

END Screen;
--::::::::::
--windows.adb
--::::::::::
WITH Text_IO, My_Int_IO, Screen;
USE Text_IO, My_Int_IO, Screen;
PACKAGE BODY Windows IS

  CursorRow : Depth := 1; -- Current cursor position
  CursorCol : Width := 1;

  PROCEDURE Open (W      : IN OUT Window;
                  Row    : Depth;
                  Column : Width;
                  Height : Depth;
                  Width  : Screen.Width) IS
    --Put the Window's cursor in upper left corner
  BEGIN
    W.CurrentRow    := Row;
    W.FirstRow      := Row;
    W.LastRow       := Row + Height - 1;
    W.CurrentColumn := Column;
    W.FirstColumn   := Column;
    W.LastColumn    := Column + Width - 1;
  END Open;

  PROCEDURE Close (W : IN OUT Window) IS
  BEGIN
    NULL;
  END Close;

  PROCEDURE Title (W     : IN OUT Window;
                   name  : String;
                   under : CHARACTER) IS
    -- Put name at the top of the Window.  If under <>  ' ', underline
    -- the title. 
    i : Width;
  BEGIN
    -- Put name on top line
    W.CurrentColumn := W.FirstColumn;
    W.CurrentRow    := W.FirstRow;
    Put_String (w, name);
    new_line (w);
    -- Underline name if desired, and move the First line of the Window
    -- below the title 
    IF under = ' ' THEN
      W.FirstRow := W.FirstRow + 1;
    ELSE
      FOR i IN W.FirstColumn .. W.LastColumn LOOP
        Put (w, under);
      END LOOP;
      new_line (w);
      W.FirstRow := W.FirstRow + 2;
    END IF;
  END Title;


  PROCEDURE GotoRowColumn (w      : IN OUT Window;
                           Row    : Depth;
                           Column : Width) IS
    -- Relative to writable Window boundaries, of course
  BEGIN
    W.CurrentRow    := W.FirstRow + Row;
    W.CurrentColumn := W.FirstColumn + Column;
  END GotoRowColumn;


  PROCEDURE Borders (w                    : IN OUT Window;
                     corner, down, across : CHARACTER) IS
    -- Draw border around current writable area in Window with characters.
    -- Call this BEFORE Title.  
    i : Depth;
    j : Width;
  BEGIN
    -- Put top line of border
    MoveCursor (W.FirstColumn, W.FirstRow);
    Text_IO.Put (corner);
    FOR j IN W.FirstColumn + 1 .. W.LastColumn - 1 LOOP
      Text_IO.Put (across);
    END LOOP;
    Text_IO.Put (corner);

    -- Put the two side lines
    FOR i IN W.FirstRow + 1 .. W.LastRow - 1 LOOP
      MoveCursor (W.FirstColumn, i);
      Text_IO.Put (down);
      MoveCursor (W.LastColumn, i);
      Text_IO.Put (down);
    END LOOP;

    -- Put the bottom line of the border
    MoveCursor (W.FirstColumn, W.LastRow);
    Text_IO.Put (corner);
    FOR j IN W.FirstColumn + 1 .. W.LastColumn - 1 LOOP
      Text_IO.Put (across);
    END LOOP;
    Text_IO.Put (corner);

    -- Put the cursor at the very end of the Window
    CursorRow := W.LastRow;
    CursorCol := W.LastColumn + 1;

    -- Make the Window smaller by one character on each side
    W.FirstRow      := W.FirstRow + 1;
    W.CurrentRow    := W.FirstRow;
    W.LastRow       := W.LastRow - 1;
    W.FirstColumn   := W.FirstColumn + 1;
    W.CurrentColumn := W.FirstColumn;
    W.LastColumn    := W.LastColumn - 1;
  END Borders;


  PROCEDURE EraseToEndOfLine (W : IN OUT Window) IS
    i : Width;
  BEGIN
    MoveCursor (W.CurrentColumn, W.CurrentRow);
    FOR i IN W.CurrentColumn .. W.LastColumn LOOP
      Text_IO.Put (' ');
    END LOOP;
    MoveCursor (W.CurrentColumn, W.CurrentRow);
    CursorCol := W.CurrentColumn;
    CursorRow := W.CurrentRow;
  END EraseToEndOfLine;


  PROCEDURE Put (W  : IN OUT Window;
                 ch : CHARACTER) IS

    -- If after end of line, move to First character of next line
    -- If about to write First character on line, blank rest of line.
    -- Put character.

  BEGIN
    IF Ch = ASCII.CR THEN
      New_Line (W);
      RETURN;
    END IF;

    -- If at end of current line, move to next line 
    IF W.CurrentColumn > W.LastColumn THEN
      IF W.CurrentRow = W.LastRow THEN
        W.CurrentRow := W.FirstRow;
      ELSE
        W.CurrentRow := W.CurrentRow + 1;
      END IF;
      W.CurrentColumn := W.FirstColumn;
    END IF;

    -- If at W.First char, erase line
    IF W.CurrentColumn = W.FirstColumn THEN
      EraseToEndOfLine (W);
    END IF;

    -- Put physical cursor at Window's cursor
    IF (CursorCol /= W.CurrentColumn) OR (CursorRow /= W.CurrentRow) THEN
      MoveCursor (W.CurrentColumn, W.CurrentRow);
      CursorRow := W.CurrentRow;
    END IF;

    IF Ch = ASCII.BS THEN
      -- Special backspace handling 
      IF W.CurrentColumn /= W.FirstColumn THEN
        Text_IO.Put (Ch);
        W.CurrentColumn := W.CurrentColumn - 1;
      END IF;
    ELSE
      Text_IO.Put (Ch);
      W.CurrentColumn := W.CurrentColumn + 1;
    END IF;
    CursorCol := W.CurrentColumn;
  END Put;


  PROCEDURE new_line (W : IN OUT Window) IS
    col : Width;

    -- If not after line, blank rest of line.
    -- Move to First character of next line

  BEGIN
    IF W.CurrentColumn = 0 THEN
      EraseToEndOfLine (W);
    END IF;
    IF W.CurrentRow = W.LastRow THEN
      W.CurrentRow := W.FirstRow;
    ELSE
      W.CurrentRow := W.CurrentRow + 1;
    END IF;
    W.CurrentColumn := W.FirstColumn;
  END new_line;


  PROCEDURE Put_String (W : IN OUT Window;
                        S : String) IS
  BEGIN
    FOR I IN S'FIRST .. S'LAST LOOP
      Put (W, S (i));
    END LOOP;
  END Put_String;


BEGIN -- Windows
  ClearScreen;
  MoveCursor (1, 1);
END Windows;
--::::::::::
--roomwind.adb
--::::::::::
WITH Windows;
WITH Chop;
WITH Phil;
WITH Calendar; 
PRAGMA Elaborate(Phil);
PACKAGE BODY Room IS

  Phils:      ARRAY(Table_Type) OF Phil.Philosopher;
  Phil_Windows: ARRAY(Table_Type) OF Windows.Window;

  TYPE Phil_Names IS (Dijkstra, Texel, Booch, Ichbiah, Stroustrup);

  TASK BODY Head_Waiter IS

    T : Integer; 
    Start_Time: Calendar.Time;

  BEGIN

    ACCEPT Open_The_Room;
    Start_Time := Calendar.Clock;

    Windows.Open(Phil_Windows(1),1,23,7,30);
    Windows.Borders(Phil_Windows(1),'+','|','-');
    Windows.Title(Phil_Windows(1), "Eddy Dijkstra",'-');
    Phils(1).Come_To_Life(1,1,2);

    Windows.Open(Phil_Windows(3),9,50,7,30); 
    Windows.Borders(Phil_Windows(3),'+','|','-');
    Windows.Title(Phil_Windows(3), "Grady Booch",'-');
    Phils(3).Come_To_Life(3,3,4);

    Windows.Open(Phil_Windows(2),9,2,7,30); 
    Windows.Borders(Phil_Windows(2),'+','|','-');
    Windows.Title(Phil_Windows(2), "Putnam Texel",'-');
    Phils(2).Come_To_Life(2,2,3);

    Windows.Open(Phil_Windows(5),17,41,7,30); 
    Windows.Borders(Phil_Windows(5),'+','|','-');
    Windows.Title(Phil_Windows(5), "Bjarne Stroustrup",'-');
    Phils(5).Come_To_Life(5,1,5);

    Windows.Open(Phil_Windows(4),17,8,7,30); 
    Windows.Borders(Phil_Windows(4),'+','|','-');
    Windows.Title(Phil_Windows(4), "Jean Ichbiah",'-');
    Phils(4).Come_To_Life(4,4,5);

    LOOP
      SELECT
        ACCEPT Report_State(Which_Phil: Table_Type;
                         State: Phil.States;
                         How_Long: Natural := 0) DO
          T := Integer(Calendar."-"(Calendar.Clock,Start_Time));
          Windows.Put_String(Phil_Windows(Which_Phil),
            "T=" & Integer'Image(T) & " ");
          CASE State IS
            WHEN Phil.Breathing =>
              Windows.Put_String(Phil_Windows(Which_Phil), "Breathing...");
              Windows.New_Line(Phil_Windows(Which_Phil));

            WHEN Phil.Thinking =>
              Windows.Put_String(Phil_Windows(Which_Phil),
                         "Thinking"
                         & Integer'Image(How_Long)
                         & " seconds.");
              Windows.New_Line(Phil_Windows(Which_Phil));

            WHEN Phil.Eating =>
              Windows.Put_String(Phil_Windows(Which_Phil),
                         "Eating"   
                         & Integer'Image(How_Long)
                         & " seconds.");
              Windows.New_Line(Phil_Windows(Which_Phil));

            WHEN Phil.Done_Eating =>
              Windows.Put_String(Phil_Windows(Which_Phil), "Yum-yum (burp)");
              Windows.New_Line(Phil_Windows(Which_Phil));

            WHEN Phil.Got_One_Stick =>
              Windows.Put_String(Phil_Windows(Which_Phil), 
                         "First chopstick"
                          & Integer'Image(How_Long));
              Windows.New_Line(Phil_Windows(Which_Phil));

            WHEN Phil.Got_Other_Stick =>
              Windows.Put_String(Phil_Windows(Which_Phil), 
                         "Second chopstick"
                          & Integer'Image(How_Long));
              Windows.New_Line(Phil_Windows(Which_Phil));

          END CASE;

         END Report_State;
        OR
          TERMINATE;
        END SELECT;

      END LOOP;

    END Head_Waiter;

END Room;
