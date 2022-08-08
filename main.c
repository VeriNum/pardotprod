#include <stdlib.h>
#include <stdio.h>
#include "dotprod.h"

double test(unsigned N, unsigned T, unsigned REPEAT) {
  /* Create two random vectors of length N, then compute their 
     dot-product REPEAT times  using T-way parallelism; 
     return the sum of those REPEAT dot-products. */
  int i,j;
  double d;
  double *vec1, *vec2;

  make_dotprod_tasks(T);

  /* Step 3: create and initialize two random vectors of length N */
  vec1=(double *)malloc(N*sizeof(double));
  vec2=(double *)malloc(N*sizeof(double));
  for (i=0; i<N; i++) {
    vec1[i] = (double)(i+1);
    vec2[i] = (double)(i+1);
  }

  /* Step 4: compute the dot-product REPEAT times */
  d=0.0;
  for(j=0; j<REPEAT; j++)
    d+=dotprod(vec1, vec2, N);
  return d;
}

int main (int argc, char **argv) {
  unsigned N, T, R; double d,goal;
  if (argc!=4) {
   fprintf(stderr, "Usage: dotprod N T REPEAT\n\
   computes dot-product of two random N-element vectors,\n\
   using T-way parallelism, iterated REPEAT times and added up.\n\
   In principle the result should be N*REPEAT*(0.5)*(0.5).\n");
   exit(1);
  }
  N=atoi(argv[1]);
  T=atoi(argv[2]);
  R=atoi(argv[3]);
  d=test(N,T,R);
  goal=(double)((N*(N+1.0)*(2.0*N+1.0)/6.0)*R);
  printf("N=%d  T=%d  R=%d  error=%f\n",N,T,R,(d-goal)/goal);
  return 0;
}
