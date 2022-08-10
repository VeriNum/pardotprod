Require Import VST.floyd.proofauto.
Require Import VST.concurrency.conclib.
Require Import VST.concurrency.lock_specs.
Require Import VST.atomics.verif_lock.
Require Import VST.floyd.library.
Require Import parsplit.
Require Import basic_lemmas.
Open Scope logic.
Open Scope gfield_scope.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition malloc_spec := DECLARE _malloc malloc_spec'.
Definition exit_spec := DECLARE _exit exit_spec'.

Inductive query : Set := REMEMBER | ASK | ANSWER.

#[export] Class task_package : Type := {
  task_input_type : Type;
  task_input_inh: Inhabitant task_input_type;
  task_output_type : Type;
  task_pred: Z -> task_input_type -> query -> val -> mpred;
  task_pred_isptr: forall numt contents q p, 
             task_pred numt contents q p |-- !! isptr p;
  task_pred_valid_pointer: forall numt contents q p, 
             task_pred numt contents q p |-- valid_pointer p;
  task_pred_contents_eq: forall numt contents1 contents2  p,
          task_pred numt contents1 REMEMBER p * 
          task_pred numt contents2 ANSWER p 
          |-- !! (contents1 = contents2)
  }.

#[export] Existing Instance task_input_inh.
#[export] Hint Resolve task_pred_isptr : saturate_local.
#[export] Hint Resolve task_pred_valid_pointer : valid_pointer.

Definition t_task := Tstruct _task noattr.

Section TASK.
 Variable TP : task_package.

Definition task_f_spec :=
 WITH T: Z, clo : val, contents: task_input_type
 PRE [ tptr tvoid ]
    PROP() PARAMS(clo) SEP (task_pred T contents ASK clo)
 POST [ tvoid ]
    PROP() RETURN() SEP(task_pred T contents ANSWER clo).

Definition task_inv (T: Z) (q: query) (p: val) : mpred :=
  EX f: val, EX clo: val,
  field_at Ers t_task (DOT _f) f p *
  field_at Ers t_task (DOT _closure) clo p *
  func_ptr' task_f_spec f *
  EX contents: task_input_type,
  task_pred T contents q clo.

Definition task_locks (T: Z) (p: val) : mpred :=
 EX go: lock_handle, EX done: lock_handle,
  field_at Ers  t_task (DOT _go) (ptr_of go) p *
  field_at Ers  t_task (DOT _done) (ptr_of done) p *
  lock_inv Ers go (task_inv T ASK p) *
  lock_inv Ers done (task_inv T ANSWER p).

Definition thread_worker_spec :=
 DECLARE _thread_worker
  WITH arg: val, T_gv: Z*globals  (* need gv only to satisfy forward_spawn *)
  PRE [ tptr tvoid ]
     PROP()
     PARAMS (arg) GLOBALS(snd T_gv)
     SEP (task_locks (fst T_gv) arg)
  POST [ tint ]
     PROP()
     RETURN (Vint Int.zero)
     SEP ().

Definition ith_task (fclo: list (val*val)) (p: val) (i: Z) : mpred :=
 let T := Zlength fclo in 
 EX go: lock_handle, EX done: lock_handle,
  field_at Ers2  (tarray t_task T) (SUB i DOT _go) (ptr_of go) p *
  field_at Ers2  (tarray t_task T) (SUB i DOT _done) (ptr_of done) p *
  field_at Ews (tarray t_task T) (SUB i DOT _f) (fst (Znth i fclo)) p *
  field_at Ews (tarray t_task T) (SUB i DOT _closure) (snd (Znth i fclo)) p *
  lock_inv comp_Ers go (task_inv T ASK (field_address (tarray t_task T) (SUB i) p)) *
  lock_inv comp_Ers done (task_inv T ANSWER (field_address (tarray t_task T) (SUB i) p)).

Definition task_array (fclo: list (val*val)) (p: val) : mpred :=
  !! field_compatible (tarray t_task (Zlength fclo)) nil p &&
 data_at Ews (tarray t_task 1) [(Vundef,(Vundef, Znth 0 fclo))] p *
 pred_sepcon (ith_task fclo p) (fun i => 1 <= i < Zlength fclo).

Definition make_tasks_spec :=
 DECLARE _make_tasks 
 WITH T: Z, gv: globals
 PRE [ tuint ]
   PROP (1 <= T < 10000)
   PARAMS (Vint (Int.repr T)) GLOBALS(gv)
   SEP(mem_mgr gv)
 POST [ tptr t_task ]
  EX p:val,
   PROP ( )
   RETURN (p)
   SEP (mem_mgr gv; task_array (Zrepeat (Vundef,Vundef) T) p; TT).

Definition initialize_task_spec :=
 DECLARE _initialize_task
 WITH p: val, i: Z, f: val, clo: val, fclo: list (val*val) 
 PRE [ tptr t_task, tuint, 
       tptr (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default), 
       tptr tvoid ]
   PROP(0 <= i < Zlength fclo)
   PARAMS (p; Vint (Int.repr i); f; clo)
   SEP(task_array fclo p)
 POST [ tvoid ]
   PROP() RETURN() 
   SEP (task_array (upd_Znth i fclo (f,clo)) p).

Definition ith_spectask
   (fclo: list (val*val))
   (inputs: list task_input_type)
   (q: query) (i: Z)  :=
   func_ptr' task_f_spec (fst (Znth i fclo)) *
    task_pred (Zlength fclo) (Znth i inputs) REMEMBER (snd (Znth i fclo)) *
    task_pred (Zlength fclo) (Znth i inputs) q (snd (Znth i fclo)).

Definition spectasks_list
   (fclo: list (val*val)) (inputs: list task_input_type)
   (q : query) :=
  pred_sepcon (ith_spectask fclo inputs q) (fun i => 0 <= i < Zlength fclo).

Definition do_tasks_spec :=
 DECLARE _do_tasks
 WITH fclo: list (val*val), inputs: list task_input_type, p: val
 PRE [ tptr t_task, tuint ]
    PROP(1 <= Zlength fclo < 10000) 
    PARAMS (p; Vint (Int.repr (Zlength fclo))) 
    SEP(task_array fclo p; spectasks_list fclo inputs ASK)
 POST [ tvoid ]
    PROP() RETURN()
    SEP(task_array fclo p; spectasks_list fclo inputs ANSWER).

Definition Gprog : funspecs :=
  [ spawn_spec; makelock_spec; freelock_spec; acquire_spec; release_spec;
    malloc_spec; exit_spec;
    thread_worker_spec; make_tasks_spec; initialize_task_spec; do_tasks_spec ].

End TASK.
