PACKAGE BODY math IS

  -- body of Math function package, which interfaces to the Ultrix
  -- math library. Normally we could interface our Ada math functions
  -- directly to the corresponding C functions, but this is not possible
  -- because the C functions deal only with double-precision float
  -- quantities and AdaEd deals only with single-precision currently.
  -- For a number of reasons, the coercion between precisions can be
  -- done only on the C side of the interface. Hence the extra layer
  -- of Ada functions: my_sin, etc., which interface directly to an
  -- extra layer of C functions contained in math.c.

  -- To use this interface package, you must
  -- 1. gcc -c math.c   
  -- 2. adacomp -l <your AdaEd library> math.ads
  -- 3. adacomp -l <your AdaEd library> math.adb

  -- Assuming a client programs called UsesMath has been compiled as usual,
  -- bind it with
  -- adabind -i math.o -m usesmath <your library name>

  -- NOTE: this will cause a rather large entry to be placed in your AdaEd
  -- library, because AdaEd's interface to C requires that part of the AdaEd 
  -- interpreter be linked in.

  -- written by Michael B. Feldman, The George Washington University
  -- May 1992

  FUNCTION  my_sin (X : Float) RETURN Float;
  PRAGMA interface (c, my_sin);

  FUNCTION  Sin (X : Float) RETURN Float IS
  BEGIN
    RETURN my_sin (X);
  END Sin;

  FUNCTION  my_cos (X : Float) RETURN Float;
  PRAGMA interface (c, my_cos);

  FUNCTION  Cos (X : Float) RETURN Float IS
  BEGIN
    RETURN my_cos (X);
  END Cos;

  FUNCTION  my_tan (X : Float) RETURN Float;
  PRAGMA interface (c, my_tan);

  FUNCTION  Tan (X : Float) RETURN Float IS
  BEGIN
    RETURN my_tan (X);
  END Tan;

  FUNCTION  my_sinh (X : Float) RETURN Float;
  PRAGMA interface (c, my_sinh);

  FUNCTION  Sinh (X : Float) RETURN Float IS
  BEGIN
    RETURN my_sinh (X);
  END Sinh;

  FUNCTION  my_cosh (X : Float) RETURN Float;
  PRAGMA interface (c, my_cosh);

  FUNCTION  Cosh (X : Float) RETURN Float IS
  BEGIN
    RETURN my_cosh (X);
  END Cosh;

  FUNCTION  my_tanh (X : Float) RETURN Float;
  PRAGMA interface (c, my_tanh);

  FUNCTION  Tanh (X : Float) RETURN Float IS
  BEGIN
    RETURN my_tanh (X);
  END Tanh;

  FUNCTION  my_asin (X : Float) RETURN Float;
  PRAGMA interface (c, my_asin);

  FUNCTION  Asin (X : Float) RETURN Float IS
  BEGIN
    RETURN my_asin (X);
  END Asin;

  FUNCTION  my_acos (X : Float) RETURN Float;
  PRAGMA interface (c, my_acos);

  FUNCTION  Acos (X : Float) RETURN Float IS
  BEGIN
    RETURN my_acos (X);
  END Acos;

  FUNCTION  my_atan (X : Float) RETURN Float;
  PRAGMA interface (c, my_atan);

  FUNCTION  Atan (X : Float) RETURN Float IS
  BEGIN
    RETURN my_atan (X);
  END Atan;

  FUNCTION  my_asinh (X : Float) RETURN Float;
  PRAGMA interface (c, my_asinh);

  FUNCTION  Asinh (X : Float) RETURN Float IS
  BEGIN
    RETURN my_asinh (X);
  END Asinh;

  FUNCTION  my_acosh (X : Float) RETURN Float;
  PRAGMA interface (c, my_acosh);

  FUNCTION  Acosh (X : Float) RETURN Float IS
  BEGIN
    RETURN my_acosh (X);
  END Acosh;

  FUNCTION  my_atanh (X : Float) RETURN Float;
  PRAGMA interface (c, my_atanh);

  FUNCTION  Atanh (X : Float) RETURN Float IS
  BEGIN
    RETURN my_atanh (X);
  END Atanh;

  FUNCTION  my_exp (X : Float) RETURN Float;
  PRAGMA interface (c, my_exp);

  FUNCTION  Exp (X : Float) RETURN Float IS
  BEGIN
    RETURN my_exp (X);
  END Exp;

  FUNCTION  my_log (X : Float) RETURN Float;
  PRAGMA interface (c, my_log);

  FUNCTION  Log (X : Float) RETURN Float IS
  BEGIN
    RETURN my_log (X);
  END Log;

  FUNCTION  my_sqrt (X : Float) RETURN Float;
  PRAGMA interface (c, my_sqrt);

  FUNCTION  Sqrt (X : Float) RETURN Float IS
  BEGIN
    RETURN my_sqrt (X);
  END Sqrt;

  FUNCTION  my_cbrt (X : Float) RETURN Float;
  PRAGMA interface (c, my_cbrt);

  FUNCTION  Cbrt (X : Float) RETURN Float IS
  BEGIN
    RETURN my_cbrt (X);
  END Cbrt;

END Math;
