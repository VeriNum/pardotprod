#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <VSTthreads.h>

struct task {
  lock_t go, done;
  void (*f)(void *closure);
  void *closure;
};

int thread_worker(void *arg) {
  struct task *t = (struct task *)arg;
  while (1) {
    acquire(t->go);
    t->f(t->closure);
    release(t->done);
  }
}

struct task *make_tasks(unsigned T) {
  struct task *tasks = (struct task *)malloc(T * sizeof (struct task));
  unsigned i;
  if (!tasks) exit_thread(1);
  for (i=1; i<T; i++) {
    struct task *t = tasks+i; /* need this workaround for VST issue #613 */
    t->go = makelock();
    t->done = makelock();
    spawn(thread_worker, t);
  }
  return tasks;
}

void initialize_task (struct task *tasks,
		      unsigned i,
		      void (*f)(void *),
		      void *closure) {
  tasks[i].f=f;
  tasks[i].closure=closure;
}

void do_tasks(struct task *tasks, unsigned T) {
  int i;
  for (i=1; i<T; i++)
    release (tasks[i].go);
  tasks[0].f(tasks[0].closure);
  for (i=1; i<T; i++)
    acquire (tasks[i].done);
}
