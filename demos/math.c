#include <math.h>

/* C functions to accommodate interfacing AdaEd to Ultrix math library */
/* The extra layer is needed because AdaEd handles only 32-bit float   */
/* and the Ultrix library handles only 64-bit float.                   */
/* Written by Michael B. Feldman, The George Washington University     */ 
/* May 1992.                                                           */

float my_sin(x)
float x;
{
  return ((float) sin((double) x));
}

float my_cos(x)
float x;
{
  return ((float) cos((double) x));
}

float my_tan(x)
float x;
{
  return ((float) tan((double) x));
}

float my_sinh(x)
float x;
{
  return ((float) sinh((double) x));
}

float my_cosh(x)
float x;
{
  return ((float) cosh((double) x));
}

float my_tanh(x)
float x;
{
  return ((float) tanh((double) x));
}

float my_asin(x)
float x;
{
  return ((float) asin((double) x));
}

float my_acos(x)
float x;
{
  return ((float) acos((double) x));
}

float my_atan(x)
float x;
{
  return ((float) atan((double) x));
}

float my_asinh(x)
float x;
{
  return ((float) asinh((double) x));
}

float my_acosh(x)
float x;
{
  return ((float) acosh((double) x));
}

float my_atanh(x)
float x;
{
  return ((float) atanh((double) x));
}

float my_exp(x)
float x;
{
  return ((float) exp((double) x));
}

float my_log(x)
float x;
{
  return ((float) log((double) x));
}

float my_sqrt(x)
float x;
{
  return ((float) sqrt((double) x));
}

float my_cbrt(x)
float x;
{
  return ((float) cbrt((double) x));
}
