/* Usage: first, call make_dotprod_tasks with T = number of threads.
   Then, as many calls to dotprod as you like. */

void make_dotprod_tasks(unsigned T);
double dotprod(double *vec1, double *vec2, unsigned n);
