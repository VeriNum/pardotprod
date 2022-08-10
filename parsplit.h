/* Split work into n multi-threaded tasks, 
  of which task 0 will be done by the current thread,
  and the other tasks will be done by other threads.

  First, tasks=make_tasks(n)  creates n-1 threads (in addition
  to the current one), which may be used over and over again
  in calls to do_tasks.

  Then, initialize_task(tasks, i, f, c),
    for 0<=i<n, instructs the ith task that when do_tasks is called,
    please execute f(c).  This can be reinitialized; that is,
    after a call to do_tasks one can change f and c for any or all
    of the tasks by calling initialize_task again.

   Then, do_tasks(tasks, n) runs all the tasks in parallel,
   and waits until they all complete.
   The value n must be the same as what was passed to make_tasks.
*/


struct task;

struct task *make_tasks (unsigned T);

void initialize_task (struct task *tasks,
		      unsigned i,
		      void (*f)(void *),
		      void *closure);

void do_tasks (struct task *tasks, unsigned T);
