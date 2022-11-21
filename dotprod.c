#include <stdlib.h>
#include <VSTthreads.h>
#include "parsplit.h"

struct task *tasks;
unsigned num_threads;

struct dotprod_task {
  double *vec1, *vec2;
  size_t n;
  double result;
} *dtasks;

void dotprod_worker(void *closure) {
  struct dotprod_task *w = (struct dotprod_task *)closure;
  double result=0.0;
  size_t n = w->n;
  double *vec1= w->vec1, *vec2= w->vec2;
  size_t i;
  for (i=0; i<n; i++)
    result += vec1[i]*vec2[i];
  w->result=result;
}

typedef unsigned long long ubig;

double dotprod(double *vec1, double *vec2, size_t n) {
  double result;
  unsigned T = num_threads;
  unsigned t;
  size_t delta = 0;
  size_t delta_next;
  for (t=0; t<T; t++) {
    struct dotprod_task *tp = dtasks+t; /* need this workaround for VST issue #613 */
    tp->vec1=vec1+delta;
    tp->vec2=vec2+delta;
    delta_next = ((ubig)(t+1))*((ubig)n)/((ubig)T);
    tp->n= delta_next-delta;
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
  if (!dtasks) exit_thread(1);
  /* tell each task where to find its work (but not yet, what its work is) */
  for (t=0; t<T; t++)
    initialize_task(tasks, t, dotprod_worker, dtasks+t);
}  
    
