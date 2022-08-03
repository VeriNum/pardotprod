#include <stdlib.h>
#include <stdio.h>
#include "parsplit.h"

extern double drand48(void);

struct task *tasks;
unsigned num_threads;

struct dotprod_task {
  double *vec1, *vec2;
  unsigned n;
  double result;
} *dtasks;

void dotprod_worker(void *closure) {
  struct dotprod_task *w = (struct dotprod_task *)closure;
  double result=0.0;
  unsigned n = w->n;
  double *vec1= w->vec1, *vec2= w->vec2;
  unsigned i;
  for (i=0; i<n; i++)
    result += vec1[i]*vec2[i];
  w->result=result;
}

typedef unsigned long long ubig;

double dotprod(double *vec1, double *vec2, unsigned n) {
  double result;
  unsigned T = num_threads;
  unsigned t;
  unsigned delta = 0;
  unsigned delta_next;
  for (t=0; t<T; t++) {
    dtasks[t].vec1=vec1+delta;
    dtasks[t].vec2=vec2+delta;
    unsigned delta_next = ((ubig)(t+1))*((ubig)n)/((ubig)T);
    dtasks[t].n= delta_next-delta;
    delta=delta_next;
  }
  do_tasks(tasks, T);
  result=0.0;
  for (t=0; t<T; t++)
    result += dtasks[t].result;
  return result;
}

void make_dotprod_tasks(unsigned T) {
  unsigned t;
  tasks = make_tasks(T);
  num_threads=T;
  dtasks=(struct dotprod_task *)malloc(T*sizeof(struct dotprod_task));
  if (!dtasks) exit(1);
  /* tell each task where to find its work (but not yet, what its work is) */
  for (t=0; t<T; t++)
    initialize_task(tasks, t, dotprod_worker, dtasks+t);
}  
    
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
    vec1[i] = drand48();
    vec2[i] = drand48();
  }

  /* Step 4: compute the dot-product REPEAT times */
  d=0.0;
  for(j=0; j<REPEAT; j++)
    d+=dotprod(vec1, vec2, N);
  return d;
}

int main (int argc, char **argv) {
  unsigned N, T, R; double d;
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
  printf("N=%d  T=%d  R=%d  result=%f\n",N,T,R,d);
  return 0;
}
