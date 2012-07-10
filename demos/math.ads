PACKAGE Math IS

   -- specification for math functions to be used with AdaEd.
   -- see package body for usage guidelines.

   -- written by Michael B. Feldman, The George Washington University
   -- May 1992.

   -- Transcendentals

  FUNCTION  Sin (X : Float) RETURN Float;
  FUNCTION  Cos (X : Float) RETURN Float;
  FUNCTION  Tan (X : Float) RETURN Float;

   -- Hyperbolic functions

  FUNCTION  Sinh (X : Float) RETURN Float;
  FUNCTION  Cosh (X : Float) RETURN Float;
  FUNCTION  Tanh (X : Float) RETURN Float;

   -- Arc functions

  FUNCTION  Asin (X : Float) RETURN Float;
  FUNCTION  Acos (X : Float) RETURN Float;
  FUNCTION  Atan (X : Float) RETURN Float;

   -- Hyerbolic Arc functions

  FUNCTION  Asinh (X : Float) RETURN Float;
  FUNCTION  Acosh (X : Float) RETURN Float;
  FUNCTION  Atanh (X : Float) RETURN Float;

   -- Logarithms

  FUNCTION  Exp (X : Float) RETURN Float;      -- e raised to the x power
  FUNCTION  Log (X : Float) RETURN Float;      -- Log x base 10

   -- Roots

  FUNCTION  Sqrt (X : Float) RETURN Float; -- Square root
  FUNCTION  Cbrt (X : Float) RETURN Float; -- Cube root

END Math;
