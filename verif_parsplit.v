Require Import VST.floyd.proofauto.
Require Import VST.concurrency.conclib.
Require Import VST.concurrency.ghosts.
Require Import VST.concurrency.cancelable_invariants.
Require Import VST.concurrency.lock_specs.
Require Import VST.atomics.verif_lock.
Require Import VST.floyd.library.
Require Import basic_lemmas.
Require Import spec_parsplit.
Require Import parsplit.

Open Scope gfield_scope.

Section TASK.
 Variable TP : task_package.

Lemma task_inv_exclusive:
 forall T b p, exclusive_mpred (task_inv TP T b p).
Proof.
intros.
unfold task_inv.
red.
Intros f clo f' clo'.
Intros contents contents'.
sep_apply field_at_conflict.
intro.
apply identity_share_bot in H.
pose proof readable_Ers. rewrite H in H0.
apply unreadable_bot; auto.
entailer!.
Qed.

Lemma body_thread_worker: semax_body Vprog (Gprog TP) f_thread_worker (thread_worker_spec TP).
Proof.
start_function.
set (T := fst T_gv).
set (gv := snd T_gv).
clearbody T. clearbody gv. clear T_gv.
unfold bind_ret in POSTCONDITION.  (* bug? *)
forward.
forward_loop (PROP ( )  LOCAL (temp _t arg; temp _arg arg)  
                      SEP (task_locks TP T arg)).
entailer!.
unfold task_locks.
Intros go done.
forward.
assert (Ers <> Share.bot). {
  pose proof readable_Ers. intro; rewrite H0 in H.
  apply unreadable_bot; auto.
}
forward_call (Ers,go,task_inv TP T ASK arg).
unfold task_inv at 2.
Intros f clo contents.
forward.
forward.
forward_call (T, clo, contents).
forward.
forward_call release_simple (Ers, done, task_inv TP T ANSWER arg).
lock_props.
apply task_inv_exclusive.
unfold task_inv.
Exists f clo contents.
cancel.
unfold task_locks.
Exists go done.
entailer!.
Qed.

Lemma bundle_task_locks:
 forall T go done p,
   field_at Ers t_task (DOT _go) (ptr_of go) p
  * field_at Ers t_task (DOT _done) (ptr_of done) p
  * lock_inv Ers go (task_inv TP T ASK p)
  * lock_inv Ers done (task_inv TP T ANSWER p)
  |-- task_locks TP T p.
Proof.
intros.
unfold task_locks.
Exists go done.
cancel.
Qed.

Lemma bundle_ith_task:
 forall (i: Z) (p: val) (T: Z) (fclo: list (val*val)) (go done: lock_handle) 
   go' done' f clo,
 let pi := field_address (tarray t_task T) (SUB i) p in 
  T = Zlength fclo ->
  JMeq f (fst (Znth i fclo)) ->
  JMeq clo (snd (Znth i fclo)) ->
  JMeq go' (ptr_of go) ->
  JMeq done' (ptr_of done) ->
  field_at Ers2 t_task (DOT _go) go' pi
  * field_at Ers2 t_task (DOT _done) done' pi
  * field_at Ews t_task (DOT _f) f pi
  * field_at Ews t_task (DOT _closure) clo pi
  * lock_inv comp_Ers go (task_inv TP T ASK pi)
  * lock_inv comp_Ers done (task_inv TP T ANSWER pi)
 |-- ith_task TP fclo p i.
Proof.
intros.
unfold ith_task. Exists go done.
apply JMeq_eq in H0, H1, H2, H3.
subst.
subst pi.
rewrite !field_at_data_at.
repeat change ([?a; ?b]) with ([a]++[b]).
rewrite !field_address_app.
simpl.
cancel.
Qed.

Lemma body_make_tasks: semax_body Vprog (Gprog TP) 
                           f_make_tasks (make_tasks_spec TP).
Proof.
start_function.
forward_call (tarray t_task T, gv). {
  apply prop_right.
  simpl.
  normalize. do 3 f_equal. lia.
}
simpl. rep_lia.
Intros p.
if_tac.
 subst. forward_if False. forward_call. contradiction. contradiction H0; auto.
forward_if True.
contradiction.
forward.
entailer!.
Intros.
rewrite data_at__tarray.
freeze FR0 := - (mem_mgr gv) (data_at _ (tarray t_task T) _ _).
clear H0.
assert_PROP (field_compatible (tarray t_task T) [] p). entailer!.
pose (lock_bindings := fun go_done => (ptr_of (fst go_done),(ptr_of (snd go_done), 
                         (Vundef,Vundef)))).
forward_for_simple_bound T (EX i:Z, 
   PROP() LOCAL (temp _tasks p; gvars gv; temp _T (vint T))
   SEP (FRZL FR0; mem_mgr gv;
       data_at_ Ews (tarray t_task 1) p;
       pred_sepcon (ith_task TP (Zrepeat (Vundef,Vundef) T) p) (fun j => 1 <= j < i);
       data_at_ Ews (tarray t_task (T-i)) (field_address0 (tarray t_task T) (SUB i) p)))%assert.
-
entailer!.
sep_apply data_at_data_at_.
rewrite !pred_sepcon_False' by lia.
rewrite split2_data_at__Tarray_app with (mid:=1) by lia.
cancel.
-
set (U := data_at_ Ews (tarray t_task 1) p).
forward.
assert_PROP 
  (force_val
        (sem_binary_operation' Oadd (tptr (Tstruct _task noattr)) tuint
           p (vint i))
  =  field_address0 (tarray t_task T) (SUB i) p). {
  entailer!.
  rewrite field_address0_offset by auto with field_compatible.
  simpl; f_equal; lia.
}
rewrite H2; clear H2.
rewrite (split2_data_at__Tarray_app 1 (T-i)) by list_solve.
Intros.
rewrite data__at_singleton_array_eq.
forward_call (gv, fun _ : lock_handle => 
                           task_inv TP T ASK (field_address (tarray t_task T) (SUB i) p)).
Intros go.
forward.
forward_call (gv, fun _ : lock_handle => 
                           task_inv TP T ANSWER (field_address (tarray t_task T) (SUB i) p)).
Intros done.
forward.
rewrite field_address0_SUB_SUB by lia.
rewrite (Z.add_comm 1 i). rewrite <- Z.sub_add_distr.
unfold_data_at (data_at _ t_task _ _).
replace (field_address0 (tarray t_task T) (SUB i) p)
  with (field_address (tarray t_task T) (SUB i) p)
 by auto with field_compatible.
rewrite <- !(lock_inv_share_join Ers comp_Ers Tsh)
  by (auto with shares).
rewrite <- (field_at_share_join Ers Ers2 Ews t_task (DOT _go))
  by (auto with shares).
rewrite <- (field_at_share_join Ers Ers2 Ews t_task (DOT _done))
  by (auto with shares).

Intros.
sep_apply (bundle_task_locks T go done).
sep_apply (bundle_ith_task i p T 
   (Zrepeat (Vundef,Vundef) T) go done (ptr_of go) (ptr_of done)
       Vundef Vundef
      ltac:(list_solve)
      ltac:(apply eq_JMeq; list_solve)
      ltac:(apply eq_JMeq; list_solve)
      (JMeq_refl _)
      (JMeq_refl _)).

(* ISSUE REPORT:
  1. forward_spawn needs to give a lot more error diagnostics 
  2. it's a shame that the thread function is required to use gv in that way
  3. not canceling funcptr'
*)

forward_spawn _thread_worker
  (field_address (tarray t_task T) (SUB i) p)
  (T, gv).
  entailer!.
  apply isptr_is_pointer_or_null; apply field_address_isptr; auto with field_compatible.
+
replace (T - i - 1) with (T - (i+1)) by lia.
entailer!.
rewrite (pred_sepcon_isolate i zeq _ (fun j : Z => 1 <= j < i + 1)) by lia.
subst U.
replace (fun y : Z => 1 <= y < i + 1 /\ y <> i) with (fun j : Z => 1 <= j < i)
 by (extensionality j; apply prop_ext; lia).
cancel.
- (* after the loop *)
forward.
Exists p.
thaw FR0.
unfold task_array.
rewrite Zlength_Zrepeat by lia.
rewrite Znth_Zrepeat by lia.
change (data_at _ _ _ p) with (data_at_ Ews (tarray t_task 1) p).
rewrite !prop_true_andp by auto.
cancel.
Qed.

Lemma body_initialize_task: semax_body Vprog (Gprog TP) 
             f_initialize_task (initialize_task_spec TP).
Proof.
start_function.
unfold task_array.
Intros.
destruct (zeq i 0).
-
subst.
forward.
simpl.
rewrite upd_Znth0.
forward.
unfold task_array.
rewrite !upd_Znth0, !Znth_0_cons. simpl fst.
rewrite Znth_upd_Znth_same, upd_Znth_Zlength by lia.
erewrite data_at_singleton_array_eq by reflexivity.
entailer!.
apply derives_refl'.
apply pred_sepcon_strong_proper. tauto.
intros.
unfold ith_task.
list_simplify.
-
rewrite (pred_sepcon_isolate i zeq) by lia.
set (U := data_at _ _ _ _).
set (V := pred_sepcon _ _).
Intros.
unfold ith_task.
Intros go done.
forward.
forward.
unfold task_array.
rewrite (pred_sepcon_isolate i zeq) by list_simplify.
rewrite Zlength_upd_Znth.
replace (pred_sepcon _ _) with V.
+
subst U.
entailer!.
unfold ith_task.
Exists go done.
list_simplify.
cancel.
+
subst V.
apply pred_sepcon_strong_proper; intros.
list_simplify.
unfold ith_task.
destruct H1.
list_simplify.
Qed.

Definition ith_husk (fclo: list (val*val))  (inputs: list task_input_type) (p: val) i := 
  !! (isptr (fst (Znth i fclo)) /\ isptr (snd (Znth i fclo))) && 
 EX go: lock_handle, EX done: lock_handle,
     task_pred (Zlength fclo) (Znth i inputs) REMEMBER (snd (Znth i fclo))
  * field_at Ers2 (tarray t_task (Zlength fclo)) [StructField _f; ArraySubsc i] (fst (Znth i fclo)) p
  * field_at Ers2 (tarray t_task (Zlength fclo)) [StructField _closure; ArraySubsc i]  (snd (Znth i fclo)) p
  * lock_inv comp_Ers go
            (task_inv TP (Zlength fclo) ASK (field_address (tarray t_task (Zlength fclo)) (SUB i) p))
  * field_at Ers2 (tarray t_task (Zlength fclo))
      [StructField _done; ArraySubsc i] (ptr_of done) p
  * lock_inv comp_Ers done
      (task_inv TP (Zlength fclo) ANSWER
         (field_address (tarray t_task (Zlength fclo)) (SUB i) p))
  * field_at Ers2 (tarray t_task (Zlength fclo))
      [StructField _go; ArraySubsc i] (ptr_of go) p.

Lemma body_do_tasks: semax_body Vprog (Gprog TP) f_do_tasks (do_tasks_spec TP).
Proof.
start_function.
unfold spectasks_list.
rewrite (pred_sepcon_isolate 0 zeq) by lia.
Intros.
unfold task_array.
Intros.
forward_for_simple_bound (Zlength fclo)
  (EX i:Z, 
    PROP() LOCAL(temp _tasks p; temp _T (vint (Zlength fclo)))
    SEP (data_at Ews (tarray t_task 1) [(Vundef, (Vundef, Znth 0 fclo))] p;
           pred_sepcon (ith_husk fclo inputs p) (fun j : Z => 1 <= j < i);
           pred_sepcon (ith_task TP fclo p) (fun j : Z => i <= j < Zlength fclo);
           pred_sepcon (ith_spectask TP fclo inputs ASK)
                   (fun j : Z => i <= j < Zlength fclo);
           ith_spectask TP fclo inputs ASK 0))%assert.
-
entailer!.
replace (fun y : Z => 0 <= y < Zlength fclo /\ y <> 0)
  with (fun j : Z => 1 <= j < Zlength fclo)
  by (extensionality j; apply prop_ext; split; intro; lia).
rewrite (pred_sepcon_False' (fun j : Z => 1 <= j < 1)) by lia.
cancel.
-
rewrite (pred_sepcon_isolate i zeq (ith_spectask TP fclo inputs ASK) ) by lia.
Intros.
(*freeze FR1 := - (ith_spectask TP fclo inputs ASK i). *)
unfold ith_spectask at 2.
Intros.
sep_apply (func_ptr'_isptr (task_f_spec TP) (fst (Znth i fclo))).
sep_apply (task_pred_isptr (Zlength fclo) (Znth i inputs) ASK (snd (Znth i fclo))).
Intros.
rename H2 into Pclo; rename H3 into Pf.
(*thaw FR1.*)
rewrite (pred_sepcon_isolate i zeq (ith_task TP fclo p)) by rep_lia.
Intros.
unfold ith_task at 2.
Intros go done.
freeze FR2 := - 
  (field_at Ers2 (tarray t_task (Zlength fclo)) [StructField _go; ArraySubsc i] _ p)
  (lock_inv comp_Ers go _).
forward.
thaw FR2.
set (clo := snd (Znth i fclo)).
set (f := fst (Znth i fclo)).
rewrite <- !(field_at_share_join Ers Ers2 Ews) by apply join_Ers_Ers2.

assert (
   field_at Ers (tarray t_task (Zlength fclo)) (SUB i DOT _f) f p
  * field_at Ers (tarray t_task (Zlength fclo)) (SUB i DOT _closure) clo p
  * func_ptr' (task_f_spec TP) f
  * task_pred (Zlength fclo) (Znth i inputs) ASK clo
  |-- task_inv TP (Zlength fclo) ASK 
        (field_address (tarray t_task (Zlength fclo)) (SUB i) p)). {
 unfold task_inv.
 Exists f clo (Znth i inputs).
 cancel.
 rewrite !field_at_data_at.
 simpl.
 repeat change ([?a; ArraySubsc i]) with ([a]++[ArraySubsc i]).
 rewrite !field_address_app. apply derives_refl.
}
sep_apply H2. clear H2.
forward_call release_simple (comp_Ers, go, 
  task_inv TP (Zlength fclo) ASK (field_address (tarray t_task (Zlength fclo)) (SUB i) p)).
lock_props. apply task_inv_exclusive.
apply comp_Ers_not_bot. auto.
entailer!.
rewrite (pred_sepcon_isolate i zeq  (ith_husk fclo inputs p) (fun j : Z => 1 <= j < i + 1)) by lia.
replace (fun y : Z => i <= y < Zlength fclo /\ y <> i)
  with  (fun j : Z => i + 1 <= j < Zlength fclo)
 by (clear; extensionality j; apply prop_ext; split; intros; lia).
replace  (fun y : Z => 1 <= y < i + 1 /\ y <> i)
  with (fun y => 1 <= y < i)
 by (clear; extensionality j; apply prop_ext; split; intros; lia).
cancel.
unfold ith_husk.
rewrite prop_true_andp by auto.
Exists go done.
fold clo.
cancel.
-
rewrite !(pred_sepcon_False'  (fun j : Z => Zlength fclo <= j < Zlength fclo)) by lia.
unfold ith_spectask.
Intros.
forward.
forward.
rewrite Znth_0_cons.
fold (fst (Znth 0 fclo)).
fold (snd (Znth 0 fclo)).
forward_call.
assert (func_ptr' (task_f_spec TP) (fst (Znth 0 fclo))
           * task_pred (Zlength fclo) (Znth 0 inputs) REMEMBER (snd (Znth 0 fclo))
           * task_pred (Zlength fclo) (Znth 0 inputs) ANSWER (snd (Znth 0 fclo))
          |-- ith_spectask TP fclo inputs ANSWER 0)
   by (unfold ith_spectask; cancel).
sep_apply H1; clear H1.
forward_for_simple_bound (Zlength fclo)
  (EX i:Z, 
    PROP() LOCAL(temp _tasks p; temp _T (vint (Zlength fclo)))
    SEP (data_at Ews (tarray t_task 1) [(Vundef, (Vundef, Znth 0 fclo))] p;
           pred_sepcon (ith_task TP fclo p) (fun j : Z => 1 <= j < i);
           pred_sepcon (ith_husk fclo inputs p) (fun j : Z => i <= j < Zlength fclo);
           pred_sepcon (ith_spectask TP fclo inputs ANSWER)
                 (fun j : Z => 1 <= j < i);
           ith_spectask TP fclo inputs ANSWER 0))%assert.
+
rewrite !(pred_sepcon_False'  (fun j : Z => 1 <= j < 1)) by lia.
entailer!.
+
rewrite (pred_sepcon_isolate i zeq  (ith_husk fclo inputs p) ) by lia.
Intros.
freeze FR1 := - (ith_husk _ _ _ _).
unfold ith_husk.
Intros go done.
forward.
forward_call (comp_Ers, done,
     (task_inv TP (Zlength fclo) ANSWER
        (field_address (tarray t_task (Zlength fclo)) (SUB i) p))).
apply comp_Ers_not_bot; auto.
thaw FR1.
entailer!.
rewrite (pred_sepcon_isolate i zeq (ith_task TP fclo p)
                        (fun j : Z => 1 <= j < i + 1)) by rep_lia.
unfold task_inv at 2.
Intros f clo contents.
sep_apply (func_ptr'_isptr (task_f_spec TP) f).
sep_apply (task_pred_isptr (Zlength fclo) contents ANSWER clo).
Intros. rewrite <- !sepcon_assoc.

rewrite !field_at_data_at.
repeat change ([?a; ArraySubsc i]) with ([a]++[ArraySubsc i]);
 rewrite !field_address_app.
sep_apply (data_at_value_eq Ers Ers2 tvoid clo (snd (Znth i fclo)) 
                        (field_address t_task (DOT _closure)
         (field_address (tarray t_task (Zlength fclo)) (SUB i) p))); auto.
sep_apply (data_at_value_eq Ers Ers2 
                      (Tfunction (Tcons (tptr tvoid) Tnil) tvoid cc_default)
                       f (fst (Znth i fclo)) 
                        (field_address t_task (DOT _f)
         (field_address (tarray t_task (Zlength fclo)) (SUB i) p))); auto.
Intros; subst f clo.

sep_apply (data_at_share_join Ers Ers2 Ews); auto with shares.
sep_apply (data_at_share_join Ers Ers2 Ews); auto with shares.
rewrite <- !sepcon_assoc.
assert (BIT := bundle_ith_task i p (Zlength fclo) fclo go done
                    (ptr_of go) (ptr_of done) (fst (Znth i fclo)) (snd (Znth i fclo))
                      (eq_refl _)   (JMeq_refl _) (JMeq_refl _)  (JMeq_refl _) (JMeq_refl _)).
rewrite !field_at_data_at in BIT.
simpl in BIT. sep_apply BIT. clear BIT.
rewrite (pred_sepcon_isolate i zeq _
                        (fun j : Z => 1 <= j < i + 1)) by rep_lia.
replace (fun y : Z => 1 <= y < i+1 /\ y <> i)
  with  (fun j : Z => 1 <= j < i)
 by (clear; extensionality j; apply prop_ext; split; intros; lia).
replace (fun y : Z => i <= y < Zlength fclo /\ y <> i)
  with  (fun j : Z => i+1 <= j < Zlength fclo)
 by (clear; extensionality j; apply prop_ext; split; intros; lia).
sep_apply task_pred_contents_eq.
Intros. subst contents.
unfold ith_spectask.
cancel.
+
entailer!.
unfold task_array, spectasks_list.
rewrite prop_true_andp by auto.
rewrite (pred_sepcon_False' (fun y : Z => Zlength fclo <= y < Zlength fclo)) by lia.
rewrite (pred_sepcon_isolate 0 zeq _ (fun i : Z => 0 <= i < Zlength fclo)) by lia.
replace  (fun y : Z => 0 <= y < Zlength fclo /\ y <> 0)
  with   (fun y : Z => 1 <= y < Zlength fclo)
 by (clear; extensionality j; apply prop_ext; split; intros; lia).
cancel.
Qed.

End TASK.
