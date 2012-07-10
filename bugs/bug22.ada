package Test1 is
   Question: constant string := "How Many Characters?";
   Ask_Twice: constant string := Question & Question;
end Test1;

with Test1;  use Test1;
package Test2 is
    Str: string(Ask_Twice'range) := Ask_Twice;
end Test2;

