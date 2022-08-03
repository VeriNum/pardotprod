Require Import VST.floyd.proofauto.
Open Scope logic.

Require Import VST.concurrency.conclib.
Require Import VST.concurrency.lock_specs.
Require Import VST.atomics.verif_lock.
Require Import VST.floyd.library.
Require Import parsplit.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition spawn_spec := DECLARE _spawn spawn_spec.
Definition malloc_spec := DECLARE _malloc malloc_spec'.
Definition exit_spec := DECLARE _exit exit_spec'.

Inductive query : Set := START | REMEMBER | ASK | ANSWER | ANSWERED.

#[export] Class task_package : Type := 
 {
  task_input_type : Type;
  task_input_inh: Inhabitant task_input_type;
  task_output_type : Type;
  task_pred: Z -> task_input_type -> query -> val -> mpred;
  task_pred_isptr: forall numt contents q p, 
             task_pred numt contents q p |-- !! isptr p;
  task_pred_valid_pointer: forall numt contents q p, 
             task_pred numt contents q p |-- valid_pointer p;
  task_pred_join1: forall numt contents p,
          task_pred numt contents START p = 
          task_pred numt contents REMEMBER p * task_pred numt contents ASK p;
  task_pred_join2: forall numt contents p,
          task_pred numt contents ANSWERED p = 
          task_pred numt contents REMEMBER p * task_pred numt contents ANSWER p;
  task_pred_contents_eq: forall numt contents1 contents2  p,
          task_pred numt contents1 REMEMBER p * 
          task_pred numt contents2 ANSWER p 
          |-- !! (contents1 = contents2)
  }.

#[export] Existing Instance task_input_inh.
#[export] Hint Resolve task_pred_isptr : saturate_local.
#[export] Hint Resolve task_pred_valid_pointer : valid_pointer.

Open Scope gfield_scope.

Lemma Ers_not_bot: Ers <> Share.bot.
Proof.
unfold Ers.
intro.
apply lub_bot_e in H. destruct H.
apply juicy_mem.extern_retainer_neq_bot; auto.
Qed.

Definition comp_Ers : share := Share.comp Ers.
Lemma comp_Ers_not_bot: comp_Ers <> Share.bot.
Proof.
unfold comp_Ers. unfold Ers.
unfold extern_retainer.
rewrite Share.demorgan1.
intro.
apply sub_glb_bot with (a:= snd (Share.split Share.Rsh)) in H.
rewrite Share.glb_commute in H.
apply sub_glb_bot with (a:= snd (Share.split Share.Rsh)) in H.
-
rewrite Share.glb_idem in H.
destruct (Share.split Share.Rsh) eqn:?H.
simpl in *. subst.
pose proof Share.split_nontrivial _ _ _ H0.
apply initialize.snd_split_fullshare_not_bot.
apply H. auto.
-
apply sepalg.join_sub_trans with Share.Rsh.
exists (fst (Share.split Share.Rsh)).
apply sepalg.join_comm.
apply split_join. destruct (Share.split Share.Rsh); simpl; auto.
apply leq_join_sub.
apply Share.ord_spec1.
rewrite <- comp_Lsh_Rsh.
rewrite <- Share.demorgan1.
f_equal.
symmetry.
rewrite <- (glb_split_x Share.Lsh).
apply Share.lub_absorb.
-
clear.
apply leq_join_sub.
assert (Share.comp (fst (Share.split Share.Rsh)) = 
                 Share.lub Share.Lsh (snd (Share.split Share.Rsh))). {
 apply join_top_comp.
 split.
 rewrite Share.distrib1.
replace (Share.glb (fst (Share.split Share.Rsh)) Share.Lsh) with Share.bot.
rewrite Share.lub_commute, Share.lub_bot.
apply glb_split.
symmetry.
rewrite Share.glb_commute.
apply sub_glb_bot with (c:=Share.Rsh).
exists (snd (Share.split Share.Rsh)).
apply split_join.
destruct (Share.split Share.Rsh); auto.
apply glb_Lsh_Rsh.
rewrite Share.lub_commute.
rewrite Share.lub_assoc.
rewrite (Share.lub_commute (snd _)).
destruct (Share.split Share.Rsh) eqn:?H. simpl.
apply Share.split_together in H.
rewrite H.
apply lub_Lsh_Rsh.
}
rewrite H.
apply Share.lub_upper2.
Qed.

Lemma join_Ers_comp_Ers: sepalg.join Ers comp_Ers Tsh.
Proof. apply join_comp_Tsh. Qed.
#[export] Hint Resolve Ers_not_bot comp_Ers_not_bot join_Ers_comp_Ers : shares.

(* Ers =  Share.lub extern_retainer (fst (Share.split Share.Rsh)) *)
(* Ews = Share.lub extern_retainer Share.Rsh *)

Definition Ers2 := snd (Share.split Share.Rsh).
Lemma Ers2_not_bot: Ers2 <> Share.bot. 
Proof.
unfold Ers2.
intro.
destruct (Share.split Share.Rsh) eqn:?H.
simpl in *; subst.
apply Share.split_nontrivial in H0; auto.
unfold Share.Rsh in *.
destruct (Share.split Share.top) eqn:?H.
simpl in *; subst.
apply Share.split_nontrivial in H; auto.
apply Share.nontrivial; auto.
Qed.

Lemma join_Ers_Ers2: sepalg.join Ers Ers2 Ews.
Proof.
unfold Ers, Ers2, Ews.
unfold extern_retainer.
split.
rewrite Share.glb_commute.
rewrite Share.distrib1.
match goal with |- Share.lub ?a ?b = _ => replace a with Share.bot; [replace b with Share.bot |] end.
apply Share.lub_bot.
symmetry.
rewrite Share.glb_commute.
apply glb_split.
symmetry.
apply sub_glb_bot with (c:=Share.Lsh).
exists (snd (Share.split Share.Lsh)).
apply sepalg.join_comm.
destruct (Share.split Share.Lsh) eqn:?H.
apply split_join in H. auto.
rewrite Share.glb_commute.
apply sub_glb_bot with (c:=Share.Rsh).
exists (fst (Share.split Share.Rsh)).
apply sepalg.join_comm.
destruct (Share.split Share.Rsh) eqn:?H.
apply split_join in H. auto.
apply glb_Lsh_Rsh.
rewrite Share.lub_assoc.
f_equal.
apply Share.split_together.
destruct (Share.split Share.Rsh); auto.
Qed.
#[export] Hint Resolve Ers2_not_bot join_Ers_Ers2 : shares.

Lemma readable_Ers2: readable_share Ers2. 
Proof.
unfold Ers2.
red.
red.
red.
intro.
apply identity_share_bot in H.
assert (Share.split Share.Rsh = (fst (Share.split Share.Rsh), snd (Share.split (Share.Rsh)))).
destruct (Share.split Share.Rsh); auto.
apply Share.split_together in H0.
set (z := snd _) in H.
rewrite <- H0 in H.
subst z.
clear H0.
rewrite Share.glb_commute in H.
rewrite Share.distrib1 in H.
rewrite Share.glb_commute in H.
rewrite Share.glb_idem in H.
rewrite glb_split in H.
rewrite Share.lub_commute in H.
rewrite Share.lub_bot in H.
destruct (Share.split Share.Rsh) eqn:?H.
apply Share.split_nontrivial in H0; auto.
apply juicy_mem.nonidentity_Rsh.
rewrite H0; apply bot_identity.
Qed.
#[export] Hint Resolve readable_Ers2 :core.

Definition t_task := Tstruct _task noattr.

Section TASK.
 Variable TP : task_package.

Definition task_f_spec :=
 WITH numt: Z, clo : val, contents: task_input_type
 PRE [ tptr tvoid ]
    PROP() PARAMS(clo) SEP (task_pred numt contents ASK clo)
 POST [ tvoid ]
    PROP() RETURN() SEP(task_pred numt contents ANSWER clo).

Definition task_inv (numt: Z) (q: query) (p: val) : mpred :=
  EX f: val, EX clo: val,
  field_at Ers t_task (DOT _f) f p *
  field_at Ers t_task (DOT _closure) clo p *
  func_ptr' task_f_spec f *
  EX contents: task_input_type,
  task_pred numt contents q clo.

Definition task_locks (numt: Z) (p: val) : mpred :=
 EX go: lock_handle, EX done: lock_handle,
  field_at Ers  t_task (DOT _go) (ptr_of go) p *
  field_at Ers  t_task (DOT _done) (ptr_of done) p *
  lock_inv Ers go (task_inv numt ASK p) *
  lock_inv Ers done (task_inv numt ANSWER p).

Definition thread_worker_spec :=
 DECLARE _thread_worker
  WITH arg: val, numt_gv: Z*globals  (* need gv only to satisfy forward_spawn *)
  PRE [ tptr tvoid ]
     PROP()
     PARAMS (arg) GLOBALS(snd numt_gv)
     SEP (task_locks (fst numt_gv) arg)
  POST [ tint ]
     PROP()
     RETURN (Vint Int.zero)
     SEP ().

Definition ith_task (fclo: list (val*val)) (p: val) (i: Z) : mpred :=
 let n := Zlength fclo in 
 EX go: lock_handle, EX done: lock_handle,
  field_at Ers2  (tarray t_task n) (SUB i DOT _go) (ptr_of go) p *
  field_at Ers2  (tarray t_task n) (SUB i DOT _done) (ptr_of done) p *
  field_at Ews (tarray t_task n) (SUB i DOT _f) (fst (Znth i fclo)) p *
  field_at Ews (tarray t_task n) (SUB i DOT _closure) (snd (Znth i fclo)) p *
  lock_inv comp_Ers go (task_inv n ASK (field_address (tarray t_task n) (SUB i) p)) *
  lock_inv comp_Ers done (task_inv  n ANSWER (field_address (tarray t_task n) (SUB i) p)).

Definition task_array (fclo: list (val*val)) (p: val) : mpred :=
  !! field_compatible (tarray t_task (Zlength fclo)) nil p &&
 data_at Ews (tarray t_task 1) [(Vundef,(Vundef, Znth 0 fclo))] p *
 pred_sepcon (ith_task fclo p) (fun i => 1 <= i < Zlength fclo).

Definition make_tasks_spec :=
 DECLARE _make_tasks 
 WITH n: Z, gv: globals
 PRE [ tuint ]
   PROP (1 <= n < 10000)
   PARAMS (Vint (Int.repr n)) GLOBALS(gv)
   SEP(mem_mgr gv)
 POST [ tptr t_task ]
  EX p:val,
   PROP ( )
   RETURN (p)
   SEP (mem_mgr gv; 
          task_array (Zrepeat (Vundef,Vundef) n) p;
          TT).

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
   task_pred (Zlength fclo) (Znth i inputs) q (snd (Znth i fclo)).

Definition spectasks_list
   (fclo: list (val*val)) (inputs: list task_input_type)
   (q : query) :=
  pred_sepcon (ith_spectask fclo inputs q) 
              (fun i => 0 <= i < Zlength fclo).

Definition do_tasks_spec :=
 DECLARE _do_tasks
 WITH fclo: list (val*val), inputs: list task_input_type, p: val
 PRE [ tptr t_task, tuint ]
    PROP(1 <= Zlength fclo < 10000) 
    PARAMS (p; Vint (Int.repr (Zlength fclo))) 
    SEP(task_array fclo p; spectasks_list fclo inputs START)
 POST [ tvoid ]
    PROP() RETURN()
    SEP(task_array fclo p; spectasks_list fclo inputs ANSWERED).

Definition Gprog : funspecs :=
  [ spawn_spec; makelock_spec; freelock_spec; acquire_spec; release_spec;
    malloc_spec; exit_spec;
    thread_worker_spec; make_tasks_spec; initialize_task_spec; do_tasks_spec ].

End TASK.

Lemma pred_sepcon_isolate:
  forall {B: Type}
  (x: B)
  (DECB: forall x y: B, {x=y}+{x<>y})
  (f: B -> mpred) (u: B -> Prop),
  (u x) ->
  pred_sepcon f u = pred_sepcon f (fun y => u y /\ y<>x) * f x.
Proof.
intros.
rewrite !pred_sepcon_eq.
pose (neqx y := negb (proj_sumbool (DECB x y))).
apply pred_ext.
Intros l.
Exists (filter neqx l).
rewrite prop_true_andp.
apply derives_trans with (iter_sepcon f (x :: filter neqx l)).
apply derives_refl'.
apply iter_sepcon_permutation.
apply NoDup_Permutation; auto.
constructor.
intro. apply filter_In in H2. destruct H2.
unfold neqx, proj_sumbool in H3.
destruct (DECB x x). inversion H3. contradiction n; auto.
apply NoDup_filter; auto.
intro.
split; intro.
destruct (DECB x0 x).
subst. left; auto. right. apply filter_In. split; auto.
unfold neqx, proj_sumbool.
destruct (DECB x x0); auto.
destruct H2.
subst.
rewrite <- H0 in H. auto.
apply filter_In in H2. destruct H2; auto.
simpl. cancel.
split.
intro. split; intro.
apply filter_In in H2. destruct H2.
rewrite H0 in H2.
split; auto.
intro; subst.
unfold neqx, proj_sumbool in H3.
destruct (DECB x x); auto. inv H3.
destruct H2.
apply filter_In. split; auto.
rewrite H0; auto.
unfold neqx, proj_sumbool.
destruct (DECB x x0); auto.
apply NoDup_filter. auto.
Intros l.
Exists (x::l).
simpl.
entailer!.
split.
intro.
rewrite H0.
split; intro.
destruct H2.
subst; auto.
destruct H2. auto.
destruct (DECB x0 x).
subst.
auto.
right; auto.
constructor; auto.
rewrite H0.
intros [? ?].
contradiction.
Qed.


