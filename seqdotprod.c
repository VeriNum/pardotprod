#include <math.h>

double seqdotprod(double *vec1, double *vec2, unsigned n) {
  double result=0.0;
  unsigned i;
  for (i=0; i<n; i++)
    result = fma(vec1[i],vec2[i],result);
  return result;
}
