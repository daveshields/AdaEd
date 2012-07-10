-- DEMONSTRATION EXAMPLE:
--   Features:
--     Enumeration types, ENUM_IO (generic package),
--     arrays, dynamic exception handling, etc.

with TEXT_IO; use TEXT_IO;
procedure en is

   type COLOR is (red, yellow, green, blue);
   package COLOR_IO is new ENUMERATION_IO(COLOR);

   ANSWER : constant array (red .. blue) of string (1..10) :=
            ("Anger     ", "The Sun   ", "Ada       ",
             "The Sky   ");

   procedure DIALOGUE is
      use COLOR_IO;
      CHOICE : COLOR;

      function ENTER_COLOR return COLOR is
         CHOICE : COLOR;
      begin
         loop
            declare
            begin
               put_line("Select a color:");
               get(CHOICE);
               return CHOICE;
            exception
               when DATA_ERROR =>
                  put_line("Invalid color, try again.  ");
            end;
         end loop;
      end ENTER_COLOR;

   begin -- body of DIALOGUE
      loop
	 CHOICE := ENTER_COLOR;
         put(CHOICE, SET => LOWER_CASE);
         put_line(" => " & ANSWER(CHOICE));
      end loop;
      
   end DIALOGUE;

begin
   DIALOGUE;

exception
   when END_ERROR => put_line("End of dialogue.");
end en;
