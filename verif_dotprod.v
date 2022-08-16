Require Import VST.floyd.proofauto.
Require Import VST.concurrency.conclib.
Require Import basic_lemmas.
Require Import spec_parsplit.
Require Import dotprod.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

Definition delta n T t := t*n/T.

Lemma delta_props n T t :
  0 <= n /\ 0 <= t < T ->
  0 <= delta n T t /\ delta n T t <= delta n T (t+1) <= n.
Proof.
intros * [? ?]; unfold delta.
split3.
-
  apply Z_div_nonneg_nonneg.  nia. lia.
-
  apply Z.div_le_mono; auto; try lia.
-
  rewrite Z.mul_comm.
  apply Z.le_trans with (n * T / T).
apply Z.div_le_mono. lia.
  apply Z.mul_le_mono_nonneg_l; lia.
  rewrite Z.div_mul; lia.
Qed.

Lemma delta_props' n T t :
  0 <= n /\  0 < T /\  0 <= t <= T ->
  0 <= delta n T t <= n.
Proof.
intros * [? [? ?]]; unfold delta.
split.
-
  apply Z_div_nonneg_nonneg.  nia. lia.
-
  rewrite Z.mul_comm.
  apply Z.le_trans with (n * T / T).
  apply Z.div_le_mono; auto; try lia.
  apply Z.mul_le_mono_nonneg_l; lia.
  rewrite Z.div_mul; lia.
Qed.

Lemma delta_0: forall n T, delta n T 0 = 0.
Proof.
intros. reflexivity.
Qed.

Lemma delta_T: forall n T,
  0 <= n -> 0 < T -> 
  delta n T T = n.
Proof.
 intros. unfold delta.
 rewrite Z.mul_comm.
 apply Z.div_mul.
 lia.
Qed.

Definition dtask_input_type : Type := (list float * list float) * (val*val).
Definition dtask_output_type : Type := float.

Definition sum (v: list float) := fold_left Float.add v Float.zero.

Definition dotprod (v12: list float * list float) : float :=
  let '(v1,v2) := v12 in
  sum (map (uncurry Float.mul) (combine v1 v2)).

Definition dotprod_f (T: Z) (v12: list float * list float) : dtask_output_type :=
 let '(v1,v2) := v12 in
 let y :=  map (uncurry Float.mul) (combine v1 v2) in
 let n := Zlength y in
  sum (map (fun i => sum (sublist (delta n T i) (delta n T (i+1)) y)) (iota T)).

Lemma dotprod_f_sanity :
 forall T v12,
  0 < T ->
  (forall x y z, (Float.add (Float.add x y) z) = Float.add x (Float.add y z)) ->
  (forall x, Float.add Float.zero x = x) ->
  dotprod_f T v12 = dotprod v12.
Proof.
 intros ? ? H2 ? ?.
 (* Let's pretend we don't know that from assumption H0 one could actually prove False... *)
assert (forall y : float, Float.add Float.zero y = Float.add y Float.zero).
intro; apply Float.add_commut; left; reflexivity.
unfold dotprod_f, dotprod.
destruct v12 as [v1 v2].
simpl.
set (n := Zlength _).
set (d := delta n T).
set (v := map (uncurry _) _) in *.
clearbody v.
transitivity (sum (sublist 0 (d T) v)).
2:{ rewrite sublist_same; auto; try lia. apply delta_T; rep_lia. }
rewrite <- (Z2Nat.id T) by lia.
assert (Z.of_nat (Z.to_nat T) <= T) by lia.
revert H2.
induction (Z.to_nat T); intro.
simpl. unfold d. rewrite delta_0. list_solve.
rewrite inj_S. unfold Z.succ. rewrite iota_S by lia.
pose proof (delta_props n T (Z.of_nat n0)) ltac:(rep_lia).
fold d in H4.
rewrite (sublist_split 0 (d (Z.of_nat n0))) by lia.
rewrite map_app.
simpl.
set (a := map _ _) in *.
clearbody a.
set (b := sublist _ _ _). clearbody b.
set (c := sublist _ _ _) in *. clearbody c.
specialize (IHn0 ltac:(lia) H2).
clear - IHn0 H H0 H1.
assert (forall a b, sum(a++b) = Float.add (sum a) (sum b)). {
 clear - H H0 H1.
 intros.
 unfold sum.
 rewrite !fold_symmetric by auto.
 induction a; simpl. rewrite H0. auto.
 rewrite IHa. rewrite !H. reflexivity.
}
rewrite !H2.
rewrite IHn0.
f_equal.
unfold sum at 1.
simpl.
apply H0.
Qed.

Definition q_share (q: query) : share :=
 match q with
 | REMEMBER => Ers2
 | ASK => Ers
 | ANSWER => Ers
 end.

Definition a_pred (q: query) (m: mpred) : mpred :=
 match q with
 | REMEMBER => emp
 | ASK => m
 | ANSWER => m
 end.

Definition answer_val (q: query) (v: val) :=
 match q with
 | REMEMBER => Vundef
 | ASK => Vundef
 | ANSWER => v
 end.

Definition t_dtask := Tstruct _dotprod_task noattr.

Definition dtask_pred (T: Z) (input: dtask_input_type) (q: query) (p: val) :=
        let '((v1,v2),(p1,p2)) := input in 
        let n := Zlength v1 in 
        !! (n = Zlength v2 /\ n <= Int.max_unsigned) &&
        field_at (q_share q) t_dtask (DOT _vec1) p1 p *
        field_at (q_share q) t_dtask (DOT _vec2) p2 p *
        field_at (q_share q) t_dtask (DOT _n) (vint n) p *
        a_pred q (field_at Ews t_dtask (DOT _result) 
                 (answer_val q (Vfloat (dotprod (v1,v2)))) p) *
        data_at (q_share q) (tarray tdouble n) (map Vfloat v1) p1 *
        data_at (q_share q) (tarray tdouble n) (map Vfloat v2) p2.

Arguments dtask_pred T input q p : simpl never.

Lemma dtask_pred_local_facts:
  forall T input q p,
     dtask_pred T input q p |-- !! isptr p.
Proof.
intros.
unfold dtask_pred.
destruct input as [[? ?] [? ? ]].
entailer!.
Qed.

#[export] Hint Resolve dtask_pred_local_facts : saturate_local.

Lemma dtask_pred_valid_pointer:
  forall T input q p,
   dtask_pred T input q p |-- valid_pointer p.
Proof.
intros.
unfold dtask_pred.
destruct input as [[? ?] [? ? ]].
Intros.
repeat apply sepcon_valid_pointer1.
apply field_at_valid_ptr0.
destruct q; simpl; auto.
simpl. lia.
reflexivity.
Qed.

#[export] Hint Resolve dtask_pred_valid_pointer : valid_pointer.

Lemma isptr_value_defined: forall t p, isptr p -> value_defined (tptr t) p.
Proof.
intros.
destruct p; try contradiction; hnf; simpl.
rewrite andb_false_r. simpl; auto.
Qed.

#[export] Hint Resolve isptr_value_defined : core.

Lemma dtask_pred_input_eq: forall T input1 input2  p,
          dtask_pred T input1 REMEMBER p * 
          dtask_pred T input2 ANSWER p 
          |-- !! (input1 = input2).
Proof.
intros.
unfold dtask_pred.
destruct input1 as [[v11 v12] [p11 p12]].
destruct input2 as [[v21 v22] [p21 p22]].
Intros.
simpl.
assert_PROP (isptr p11 /\ isptr p12 /\ isptr p21 /\ isptr p22) by entailer!.
destruct H3 as [? [? [? ?]]].
rewrite !field_at_data_at. simpl.
sep_apply (data_at_values_cohere Ers Ers2 (tptr tdouble) p21 p11); auto.
sep_apply (data_at_values_cohere Ers Ers2 (tptr tdouble) p22 p12); auto.
sep_apply  (data_at_values_cohere Ers Ers2 tuint); auto. 
Intros. subst. 
apply repr_inj_unsigned in H7; try rep_lia.
rewrite H7.
set (n := Zlength v11) in *.
clear - H H1 H7.
sep_apply (data_at_values_cohere Ers Ers2 (tarray tdouble n)
                               (map Vfloat v21)   (map Vfloat v11)); auto;
  try (apply value_defined_tarray; [list_solve | apply Forall_map; apply Forall_forall; intros; hnf; auto]).
sep_apply (data_at_values_cohere Ers Ers2 (tarray tdouble n)
                               (map Vfloat v22)   (map Vfloat v12)); auto;
  try (apply value_defined_tarray; [list_solve | apply Forall_map; apply Forall_forall; intros; hnf; auto]).
Intros.
apply prop_right.
apply map_inj in H0; [ | congruence].
apply map_inj in H2; [ | congruence].
congruence.
Qed.

Lemma make_REMEMBER_ASK:
 forall T v1 v2 p1 p2 dtp n,
 0 <= n <= Int.max_unsigned ->
 0 < T ->
  data_at Ews (tarray tdouble n) (map Vfloat v1) p1
 * data_at Ews  (tarray tdouble n)  (map Vfloat v2) p2
  * data_at Ews t_dtask (p1,(p2, (vint n, Vundef))) dtp
|-- dtask_pred T ((v1,v2),(p1,p2)) REMEMBER dtp
      * dtask_pred T ((v1,v2),(p1,p2)) ASK    dtp.
Proof.
intros.
unfold dtask_pred; simpl.
saturate_local.
rewrite !prop_true_andp by (split; list_solve).
clear H7 H5 H2.
rewrite !Zlength_map in *.
set (n := Zlength v1) in *.
rewrite <-  !(data_at_share_join Ers Ers2 Ews (tarray tdouble n)); auto with shares.
cancel.
unfold_data_at (data_at _ _ _ _ ).
 rewrite <-  (field_at_share_join Ers Ers2 Ews t_dtask (DOT _vec1)); auto with shares.
 rewrite <- (field_at_share_join Ers Ers2 Ews t_dtask (DOT _vec2)); auto with shares.
 rewrite <- (field_at_share_join Ers Ers2 Ews t_dtask (DOT _n)); auto with shares.
cancel.
Qed.

Lemma unmake_REMEMBER_ANSWER:
 forall T n v1 v2 p1 p2 dtp,
  n = Zlength v1 ->
  dtask_pred T (v1, v2, (p1, p2)) REMEMBER dtp
  * dtask_pred T (v1, v2, (p1, p2)) ANSWER dtp
  |-- data_at Ews t_dtask  (p1,(p2, (vint n, Vfloat (dotprod (v1,v2))))) dtp
      * data_at Ews (tarray tdouble n) (map Vfloat v1) p1
      * data_at Ews (tarray tdouble n) (map Vfloat v2) p2.
Proof.
intros.
sep_apply dtask_pred_input_eq.
Intros.
unfold dtask_pred.
Intros.
simpl.
set (s := sum _). clearbody s.
rewrite <- H in *.
rewrite <- !(data_at_share_join Ers Ers2 Ews (tarray tdouble n)) by auto with shares.
cancel.
repeat (unfold_data_at (data_at _ _ _ _)).
rewrite <- !(field_at_share_join Ers Ers2 Ews) by auto with shares.
cancel.
Qed.

#[export] Instance dtask_package : task_package :=
  Build_task_package dtask_input_type _ dtask_output_type
   dtask_pred 
   dtask_pred_local_facts
   dtask_pred_valid_pointer
   dtask_pred_input_eq.

Definition dotprod_worker_spec :=
 DECLARE _dotprod_worker
 WITH T: Z, clo : val, input: task_input_type
 PRE [ tptr tvoid ]
    PROP() PARAMS(clo) SEP (dtask_pred T input ASK clo)
 POST [ tvoid ]
    PROP() RETURN() SEP(dtask_pred T input ANSWER clo).

Definition fclo (gv: globals) (T: Z) (dtp: val) : list (val*val) :=
  map (fun i => (gv _dotprod_worker, 
                         field_address0 (tarray t_dtask T) (SUB i) dtp)) 
        (iota T).

Lemma Zlength_fclo: forall gv T dtp,
  0 <= T -> Zlength (fclo gv T dtp) = T.
Proof.
 intros.
 unfold fclo. rewrite Zlength_map. rewrite Zlength_iota; lia.
Qed.

Lemma snd_Znth_fclo:
 forall t gv T dtp,
  0 <= t < T ->
  snd (Znth t (fclo gv T dtp)) = field_address0 (tarray t_dtask T) (SUB t) dtp.
Proof.
intros; unfold fclo; rewrite Znth_map, Znth_iota by list_solve; auto.
Qed.

Definition tasking T (gv: globals) :=
  EX tp:val, EX dtp: val,
   !! (0 < T < 10000) &&
   data_at Ews tuint (vint T) (gv _num_threads) *
   data_at Ews (tptr t_task) tp (gv _tasks) *
   task_array dtask_package (fclo gv T dtp) tp *
   data_at Ews (tptr t_dtask) dtp (gv _dtasks) *
   data_at_ Ews (tarray t_dtask T) dtp.

Definition dotprod_spec :=
  DECLARE _dotprod
  WITH T:Z, p1:val, p2: val, v1: list float, v2: list float, gv: globals
  PRE [ tptr tdouble, tptr tdouble, tuint ]
    PROP ( Zlength v1 = Zlength v2; Zlength v1 <= Int.max_unsigned)
    PARAMS ( p1; p2; Vint (Int.repr (Zlength v1))) GLOBALS(gv)
    SEP (tasking T gv;
           data_at Ews (tarray tdouble (Zlength v1)) (map Vfloat v1) p1;
           data_at Ews (tarray tdouble (Zlength v2)) (map Vfloat v2) p2)
  POST [ tdouble ]
    PROP()
    RETURN (Vfloat (dotprod_f T (v1,v2)))
    SEP (tasking T gv;
           data_at Ews (tarray tdouble (Zlength v1)) (map Vfloat v1) p1;
           data_at Ews (tarray tdouble (Zlength v2)) (map Vfloat v2) p2).

Definition make_dotprod_tasks_spec :=
  DECLARE _make_dotprod_tasks
  WITH T: Z, gv: globals
  PRE [ tuint ]
     PROP (1 <= T < 10000)
     PARAMS (vint T) GLOBALS (gv)
     SEP (library.mem_mgr gv;
           data_at_ Ews tuint (gv _num_threads);
           data_at_ Ews (tptr t_task) (gv _tasks);
           data_at_ Ews (tptr t_dtask) (gv _dtasks))
   POST [ tvoid ]
     PROP() RETURN() SEP(library.mem_mgr gv; tasking T gv; TT).

Definition Gprog : funspecs :=
   dotprod_worker_spec :: dotprod_spec ::
    (DECLARE _malloc (@library.malloc_spec' CompSpecs)) ::
  [ exit_spec;
    make_tasks_spec dtask_package; 
    initialize_task_spec dtask_package; do_tasks_spec dtask_package].

Lemma task_array_local_facts:
  forall TP fclo p, 
  task_array TP fclo p |-- !! isptr p.
Proof.
intros.
unfold task_array.
entailer!.
destruct H; auto.
Qed.

#[export] Hint Resolve task_array_local_facts: saturate_local.

Definition partial_dotprod_f (t T: Z) (v12: list float * list float) : dtask_output_type :=
 let '(v1,v2) := v12 in
 let y :=  map (uncurry Float.mul) (combine v1 v2) in
 let n := Zlength y in
  sum (map (fun i => sum (sublist (delta n T i) (delta n T (i+1)) y)) (iota t)).

Lemma body_make_dotprod_tasks: semax_body Vprog Gprog f_make_dotprod_tasks make_dotprod_tasks_spec.
Proof.
start_function.
forward_call .
Intros tp.
forward.
forward.
forward_call (tarray t_dtask T, gv).
entailer!.
simpl.
f_equal; f_equal. f_equal; lia.
unfold sizeof; simpl.
rep_lia.
Intros dtp.
forward.
forward.
if_tac.
forward_if False. forward_call. contradiction. contradiction.
forward_if True. contradiction. 
forward.
entailer!.
Intros. clear H0.
deadvars!.
forward_for_simple_bound T
 (EX t:Z, 
   PROP ( )
   LOCAL (gvars gv; temp _T (vint T))
   SEP (library.mem_mgr gv;
   library.malloc_token Ews (tarray t_dtask T) dtp;
   data_at_ Ews (tarray t_dtask T) dtp;
   task_array dtask_package (
        map (fun i => (gv _dotprod_worker, 
                         field_address0 (tarray t_dtask T) (SUB i) dtp)) 
           (iota t)  ++ Zrepeat (Vundef, Vundef) (T-t)) 
      tp;
   TT;
   data_at Ews tuint (vint T) (gv _num_threads);
   data_at Ews (tptr t_task) tp (gv _tasks);
   data_at Ews (tptr t_dtask) dtp (gv _dtasks)))%assert.
-
entailer!.
simpl; auto.
-
rename i into t.
forward.
forward.
set (fclo' := map _ _ ++ _).
forward_call (tp, t, (gv _dotprod_worker), 
                    field_address0 (tarray t_dtask T) (SUB t) dtp,
                    fclo').
 {entailer!.
  simpl.
  rewrite field_address0_offset by auto with field_compatible.
  reflexivity.
 }
  subst fclo'; list_solve.
entailer!.
apply sepcon_derives; auto.
apply derives_refl'.
f_equal.
subst fclo'.
rewrite upd_Znth_app2 by list_simplify.
list_simplify; rewrite !Znth_iota by lia.
reflexivity.
rewrite <- app_nil_end.
assert (i=t) by lia. subst.
reflexivity.
-
forward.
unfold tasking.
Exists tp dtp.
rewrite prop_true_andp by lia.
list_simplify.
change (map _ _) with (fclo gv T dtp).
cancel.
Qed.

Lemma field_at_SUB_t_DOT_result:
 forall t T a dtp,
 0 <= t < T ->
 T < 10000 ->
 field_compatible (tarray t_dtask T) [] dtp ->
 field_at Ews (tarray t_dtask T) [StructField _result; ArraySubsc t]
  (Vfloat a) dtp
 = field_at Ews t_dtask (DOT _result) (Vfloat a)
      (field_address0 (tarray t_dtask T) (SUB t) dtp).
Proof.
intros.
replace (field_address0 (tarray t_dtask T) (SUB t) dtp) 
 with (field_address (tarray t_dtask T) (SUB t) dtp)
 by auto 50 with field_compatible.
apply (field_at_app _ (tarray t_dtask T) (DOT _result) (SUB t)); auto.
Qed.

Lemma finish_dotprod:
 forall T p1 p2 v1 v2 dtp gv,
  Zlength v1 = Zlength v2 ->
  0 < T < 10000 ->
  let delt := delta (Zlength v1) T in
let inp :=
  map
    (fun i : Z =>
     ((sublist (delt i) (delt (i + 1)) v1, sublist (delt i) (delt (i + 1)) v2),
      (field_address0 (tarray tdouble (Zlength v1)) (SUB delt i) p1,
       field_address0 (tarray tdouble (Zlength v1)) (SUB delt i) p2)))
 (iota T) in
field_compatible (tarray t_dtask T) [] dtp ->
field_compatible0 (tarray tdouble (Zlength v1)) [] p1 ->
field_compatible0 (tarray tdouble (Zlength v1)) [] p2 ->
pred_sepcon (ith_spectask dtask_package (fclo gv T dtp) inp ANSWER)
  (fun i : Z => 0 <= i < T)
|-- data_at_ Ews (tarray t_dtask T) dtp
      * data_at Ews (tarray tdouble (Zlength v1)) (map Vfloat v1) p1
      * data_at Ews (tarray tdouble (Zlength v1)) (map Vfloat v2) p2.
Proof.
intros.
set (t:=T).
unfold t at 1.
replace (data_at Ews (tarray tdouble (Zlength v1)) (map Vfloat v1) p1)
  with (data_at Ews (tarray tdouble (delt t)) (map Vfloat (sublist 0 (delt t) v1)) p1)
  by (unfold t, delt; rewrite delta_T, sublist_same by rep_lia; auto).
replace (data_at Ews (tarray tdouble (Zlength v1)) (map Vfloat v2) p2)
  with (data_at Ews (tarray tdouble (delt t)) (map Vfloat (sublist 0 (delt t) v2)) p2)
  by (unfold t, delt; rewrite delta_T, sublist_same by rep_lia; auto).
assert (0 <= t <= T) by lia.
clearbody t.
rewrite <- (Z2Nat.id t) in * by lia.
induction (Z.to_nat t).
-
rewrite pred_sepcon_False' by lia.
simpl Z.of_nat.
unfold delt; rewrite delta_0.
apply derives_trans with (emp * emp * emp).
cancel.
repeat apply sepcon_derives; apply data_at_zero_array;
 auto with field_compatible.
-
rewrite inj_S. unfold Z.succ. 
rewrite (pred_sepcon_isolate (Z.of_nat n) zeq) by lia.
replace (fun y : Z => 0 <= y < Z.of_nat n + 1 /\ y <> Z.of_nat n)
 with (fun i : Z => 0 <= i < Z.of_nat n)
  by (extensionality j; apply prop_ext; split; intro; lia).
unfold ith_spectask at 2.
sep_apply func_ptr'_emp.
sep_apply IHn; try lia.
clear IHn.
clear t.
rewrite inj_S in H4.
assert (0 <= Z.of_nat n) by lia.
forget (Z.of_nat n) as t. clear n.
set (n := Zlength v1) in *.
change task_pred with dtask_pred.
pose proof (delta_props n T t ltac:(rep_lia)). fold delt in H6.
set (dt := delt t) in *.
set (dt1 := delt (t + 1)) in *.
rewrite (split2_data_at__Tarray_app t (t+1)) by lia.
replace (t + 1 - t) with 1 by lia.
replace  (field_address0 (tarray t_dtask (t+1)) (SUB t) dtp)
 with  (field_address0 (tarray t_dtask t) (SUB t) dtp)
 by (auto with field_compatible).
rewrite snd_Znth_fclo by lia.
rewrite !(sublist_split 0 dt dt1) by lia. rewrite !map_app.
rewrite !(split2_data_at_Tarray_app dt dt1) by list_solve.
cancel.
rewrite data__at_singleton_array_eq.
replace (field_address0 (tarray t_dtask t) (SUB t) dtp)
  with (field_address0 (tarray t_dtask T) (SUB t) dtp)
 by (auto with field_compatible).
subst inp.
rewrite !Znth_map by Zlength_solve.
rewrite Zlength_fclo by lia.
rewrite Znth_iota by lia.
fold dt. fold dt1.
replace  (field_address0 (tarray tdouble dt1) (SUB dt) p1)
  with  (field_address0 (tarray tdouble n) (SUB dt) p1)
 by (auto with field_compatible).
replace  (field_address0 (tarray tdouble dt1) (SUB dt) p2)
  with  (field_address0 (tarray tdouble n) (SUB dt) p2)
 by (auto with field_compatible).
sep_apply unmake_REMEMBER_ANSWER.
rewrite Zlength_sublist by Zlength_solve.
cancel.
Qed.

Lemma body_dotprod: semax_body Vprog Gprog f_dotprod dotprod_spec.
Proof.
start_function.
unfold tasking. Intros tp dtp.
set (n := Zlength v1) in *. rewrite <- H.
assert_PROP (field_compatible0 (tarray t_dtask T) nil dtp /\
                    field_compatible0 (tarray tdouble n) nil p1 /\
                    field_compatible0 (tarray tdouble n) nil p2) as H2 by  entailer!.
destruct H2 as [Hdtp [? ?]].
assert (Hn: 0 <= n) by rep_lia. 
forward.
forward.
set (delt := delta n T) in *.
pose (nthtask i :=  ((sublist (delt i) (delt(i+1)) v1,sublist (delt i) (delt(i+1)) v2),
                             (field_address0 (tarray tdouble n) (SUB (delt i)) p1,
                              field_address0 (tarray tdouble n) (SUB (delt i)) p2))).
freeze FR1:= (data_at Ews _ _ (gv _num_threads)) (task_array _ _ _).
forward_for_simple_bound T 
   (EX t:Z,   
    PROP ()
    LOCAL (temp _delta (vint (delt t)); temp _T (vint T);
                gvars gv; temp _vec1 p1; temp _vec2 p2; 
                temp _n (vint n))
   SEP (FRZL FR1; data_at Ews (tptr t_task) tp (gv _tasks);
          data_at Ews (tptr t_dtask) dtp (gv _dtasks);
          pred_sepcon (fun i => dtask_pred T (nthtask i) REMEMBER
                                  (field_address (tarray t_dtask T) (SUB i) dtp)) (fun i => 0 <= i < t);
          pred_sepcon (fun i => dtask_pred T (nthtask i) ASK
                                  (field_address (tarray t_dtask T) (SUB i) dtp)) (fun i => 0 <= i < t);
          data_at_ Ews (tarray t_dtask (T-t)) (field_address0 (tarray t_dtask T) (SUB t) dtp);
          data_at Ews (tarray tdouble (n-delt t)) (map Vfloat (sublist (delt t) n v1))
                       (field_address0 (tarray tdouble n) (SUB delt t) p1);
          data_at Ews (tarray tdouble (n-delt t)) (map Vfloat (sublist (delt t) n v2))
                       (field_address0 (tarray tdouble n) (SUB delt t) p2)))%assert.
-
entailer!.
rewrite !pred_sepcon_False' by lia.
unfold delt. rewrite delta_0.
rewrite !sublist_same by lia.
pose proof (Zlength_nonneg v1).
rewrite !field_address0_offset by auto with field_compatible.
simpl.  normalize.
-
rename i into t.
pose proof delta_props n T t ltac:(lia).
fold delt in H5.
forward.
forward.
replace (force_val _) with (field_address (tarray t_dtask T) (SUB t) dtp).
2:{
simpl.
rewrite field_address_offset by auto with field_compatible.
 unfold sem_add_ptr_int.
 rewrite sem_add_pi_ptr by (auto; rep_lia).
simpl. f_equal; lia.
}
rewrite (split2_data_at__Tarray_app 1 (T-t)) by lia.
rewrite (data_at__eq Ews (tarray t_dtask 1)).
erewrite data_at_singleton_array_eq by reflexivity.
simpl projT2.
Intros.
rewrite field_address0_SUB_SUB by lia.
replace (t + (T - t)) with T by lia.
replace (T - t - 1) with (T - (t+1)) by lia.
replace (1+t) with (t+1) by (clear; lia).
replace  (field_address0 (tarray t_dtask T) (SUB t) dtp)
 with  (field_address (tarray t_dtask T) (SUB t) dtp)
  by auto with field_compatible.
rewrite <- (field_at_data_at Ews (tarray t_dtask T) (SUB t)).
forward.
replace (force_val _) with (field_address0 (tarray tdouble n) (SUB delt t) p1)
 by (rewrite sem_add_pi' by (auto; rep_lia);
      rewrite field_address0_offset by auto with field_compatible;
      simpl; f_equal; lia).
forward.
replace (force_val _) with (field_address0 (tarray tdouble n) (SUB delt t) p2)
 by (rewrite sem_add_pi' by (auto; rep_lia);
      rewrite field_address0_offset by auto with field_compatible;
      simpl; f_equal; lia).
forward.
  { entailer!.
    apply repr_inj_unsigned64 in H20; try rep_lia.
    rewrite Int.unsigned_repr in H20 by rep_lia.
    lia. }  
forward.
forward.
rewrite add_repr, !Int.unsigned_repr, mul64_repr  by rep_lia.
rewrite divu_repr64; [ | | rep_lia].
2:{ clear - H4 H0 Hn H1.
  assert (T * Int.max_unsigned <= Int64.max_unsigned) by rep_lia.
  split; try lia.
  eapply Z.le_trans; [ | apply H].
  apply Z.mul_le_mono_nonneg; lia.
}
fold (delta n T (t+1)).
rewrite Int64.unsigned_repr
 by (pose proof delta_props n T t ltac:(lia); rep_lia).
rewrite !(pred_sepcon_isolate t zeq _ (fun i:Z => 0 <= i < t+1)) by lia.
replace (fun y : Z => 0 <= y < t + 1 /\ y <> t)
 with (fun i : Z => 0 <= i < t)
  by (extensionality j; apply prop_ext; split; intro; lia).
replace (T - t - 1) with (T - (t+1)) by lia.
entailer!.
rewrite !(sublist_split (delt t) (delt(t+1)) (Zlength v1)) by lia.
rewrite !map_app.
 rewrite !(split2_data_at_Tarray_app (delt (t+1)-delt t)) by list_solve.
rewrite !field_address0_SUB_SUB by lia.
rewrite Z.sub_simpl_r.
replace  (Zlength v1 - delt t - (delt (t + 1) - delt t)) with (Zlength v1 - delt (t+1)) by lia.
replace (delt t + (Zlength v1 - delt t)) with (Zlength v1) by  lia.
cancel.
eapply derives_trans; [ | apply make_REMEMBER_ASK with (n:= delt (t+1) - delt t); lia].
rewrite <- (field_at_data_at Ews (tarray t_dtask T) (SUB t)).
cancel.
-
thaw FR1.
replace (delt T) with n by (unfold delt; rewrite delta_T; lia).
rewrite !Z.sub_diag.
rewrite !sublist_nil. simpl map.
rewrite data_at__eq.
change (default_val (tarray _ 0)) with (@nil (reptype t_dtask)).
rewrite !data_at_zero_array_eq by
 (try apply field_address0_isptr; auto with field_compatible).
forward.
pose (inp := (map (fun i => 
                              ((sublist (delt i) (delt(i+1)) v1,
                                sublist (delt i) (delt(i+1)) v2),
                               (field_address0 (tarray tdouble n) (SUB delt i) p1,
                                field_address0 (tarray tdouble n) (SUB delt i) p2)))
                          (iota T))).
make_func_ptr _dotprod_worker.
change (func_ptr' _) with (func_ptr' (snd dotprod_worker_spec)).
forward_call (fclo gv T dtp ,inp,tp).
  apply prop_right; rewrite Zlength_fclo by lia; reflexivity.
 2: rewrite Zlength_fclo; lia.
{
 subst Frame.
 instantiate (1 := [data_at Ews tuint (vint T) (gv _num_threads);
                   data_at Ews (tptr t_task) tp (gv _tasks);
                   data_at Ews (tptr t_dtask) dtp (gv _dtasks)]).
 simpl fold_right_sepcon.
 cancel.
 sep_apply (@sepcon_pred_sepcon mpred Z _ _ _ ).
 unfold spectasks_list.
rewrite sepcon_comm.
eapply derives_trans; [ apply distribute_pred_sepcon | ].
apply func_ptr'_emp. rewrite <- split_func_ptr'; auto.
rewrite Zlength_fclo by lia.
apply pred_sepcon_derives; intros t ?.
unfold ith_spectask.
simpl task_pred.
rewrite Zlength_fclo by lia.
unfold fclo. subst inp.
rewrite !Znth_map by list_solve. simpl.
rewrite Znth_iota by rep_lia.
fold (nthtask t).
replace  (field_address0 (tarray t_dtask T) (SUB t) dtp)
 with  (field_address (tarray t_dtask T) (SUB t) dtp)
  by auto with field_compatible.
change (func_ptr' _) with (func_ptr' (snd dotprod_worker_spec)).
cancel.
}

forward.
freeze FR2 := - (spectasks_list dtask_package (fclo gv T dtp) inp ANSWER)
   (data_at Ews (tptr t_dtask) dtp (gv _dtasks)).
unfold spectasks_list.
rewrite Zlength_fclo by lia.
forward_for_simple_bound T
  (EX t:Z, 
     PROP ()
     LOCAL (temp _result (Vfloat (partial_dotprod_f t T (v1, v2)));
     temp _T (vint T); gvars gv)
     SEP (FRZL FR2;
     data_at Ews (tptr t_dtask) dtp (gv _dtasks);
     pred_sepcon
      (ith_spectask dtask_package (fclo gv T dtp) inp ANSWER)
      (fun i : Z => 0 <= i < T)))%assert.
+
entailer!.
+
rename i into t.
rewrite (pred_sepcon_isolate t zeq) by lia.
unfold ith_spectask at 2.
change task_pred with dtask_pred.
unfold dtask_pred.
subst inp.
unfold fclo.
rewrite !Znth_map, !Znth_iota by (rewrite ?Zlength_iota; lia).
simpl.
Intros.
forward.

rewrite <- field_at_SUB_t_DOT_result by (auto; lia).
forward.
deadvars!.
forward.
 pose proof delta_props (Zlength v1) T t ltac:(lia).
 fold n in H7.
 fold delt in H7.
entailer!.
* 
 clear H23 H22 H21 H20 H19 H18
         H17 H16 H15 H14 H13 H12 H11 H10 H9 H8.
 f_equal.
 unfold partial_dotprod_f, dotprod_f.
 rewrite !Zlength_map, !Zlength_combine, <- H, !Z.min_id.
 rewrite iota_S by lia.
 rewrite map_app.
 change (map ?f [t]) with ([f t]).
 set (a := map _ (iota t)).
 clearbody a.
 unfold sum at 1.
 rewrite fold_left_app.
 unfold fold_left at 1.
 unfold sum at 2.
 f_equal.
 unfold dotprod.
 rewrite combine_sublist by lia.
 rewrite map_sublist.
 reflexivity.
*
rewrite (pred_sepcon_isolate t zeq _ (fun i : Z => 0 <= i < T)) by lia.
unfold ith_spectask.
rewrite Zlength_map. 
rewrite !Znth_map by (rewrite Zlength_iota; lia).
rewrite !sepcon_assoc.
apply sepcon_derives.
apply derives_refl.
replace (fst (Znth t (fclo gv T dtp))) with (gv _dotprod_worker)
  by (unfold fclo; list_solve).
apply sepcon_derives.
apply derives_refl.
change task_pred with dtask_pred.
unfold dtask_pred.
simpl.
rewrite prop_true_andp
 by (rewrite Znth_iota by lia; rewrite !Zlength_sublist; lia).
rewrite !Znth_iota by lia.
rewrite !Zlength_sublist by lia.
rewrite snd_Znth_fclo by lia.
rewrite <- field_at_SUB_t_DOT_result by (auto; lia).
rewrite prop_true_andp by (split; lia).
cancel.
+

forward.
thaw FR2.
unfold tasking.
Exists tp dtp.
rewrite prop_true_andp by auto.
cancel.
rewrite <- H.
apply finish_dotprod; auto.
Qed.

 









