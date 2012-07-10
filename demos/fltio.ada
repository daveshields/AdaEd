-- Precompiled instantiations of Integer_IO and
-- Float_IO for the predefined Integer and Float types
 
WITH Text_IO;
PACKAGE My_Int_IO IS
  NEW Text_IO.Integer_IO (Num => Integer);
 
WITH Text_IO;
PACKAGE My_Flt_IO IS
  NEW Text_IO.Float_IO   (Num => Float);
