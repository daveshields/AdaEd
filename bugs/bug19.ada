GENERIC
  TYPE ValueType IS PRIVATE;
  WITH FUNCTION "+"(L, R: ValueType) RETURN ValueType;
PACKAGE Matrices IS
 
  TYPE Matrix IS ARRAY(Integer RANGE <>, Integer RANGE <>) OF ValueType;
  FUNCTION "+" (K : IN ValueType;  M : IN Matrix) RETURN Matrix;
end Matrices; 

PACKAGE BODY Matrices IS

  FUNCTION "+" (K : IN ValueType;  M : IN Matrix) RETURN Matrix IS
  BEGIN
    RETURN M;
  END "+";
END Matrices;

WITH Matrices;
PROCEDURE UseMatrices IS

  PACKAGE Float_Matrices IS NEW Matrices(ValueType => Float, "+" => "+");

BEGIN
  NULL;
END UseMatrices;
