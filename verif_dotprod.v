Require Import VST.floyd.proofauto.
Require Import VST.concurrency.conclib.
Require Import basic_lemmas.
Require Import spec_parsplit.
Require Import dotprod.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

Definition delta n numt i := i*n/numt.

Lemma delta_range: forall n numt,
   0 <= n -> 0 < numt ->
  forall i,
   0 <= i <= numt -> 0 <= delta n numt i <= n.
Proof.
intros.
  intros. unfold delta.
  split.  apply Z_div_nonneg_nonneg.  nia. lia.
  rewrite Z.mul_comm.
  apply Z.le_trans with (n * numt / numt).
  apply Z.div_le_mono; auto; try lia.
  apply Z.mul_le_mono_nonneg_l; lia.
  rewrite Z.div_mul; lia.
Qed.

Lemma delta_0: forall n numt, delta n numt 0 = 0.
Proof.
intros. reflexivity.
Qed.

Lemma delta_numt: forall n numt,
  0 <= n -> 0 < numt -> 
  delta n numt numt = n.
Proof.
 intros. unfold delta.
 rewrite Z.mul_comm.
 apply Z.div_mul.
 lia.
Qed.

Lemma delta_S: forall n,
 0 <= n -> 
 forall numt i,
  0 <= i < numt -> delta n numt i <= delta n numt (i+1).
Proof.
intros.
unfold delta.
apply Z.div_le_mono. lia.
apply Z.mul_le_mono_nonneg_r; lia.
Qed.

Definition dtask_input_type : Type := (list float * list float) * (val*val).
Definition dtask_output_type : Type := float.

Definition sum (v: list float) :=
  fold_left Float.add v Float.zero.

Definition dotprod (v12: list float * list float) : float :=
  let '(v1,v2) := v12 in
  let y := map (uncurry Float.mul) (combine v1 v2) in
  sum y.

Definition dotprod_f (numt: Z) (v12: list float * list float) : dtask_output_type :=
 let '(v1,v2) := v12 in
 let y :=  map (uncurry Float.mul) (combine v1 v2) in
 let n := Zlength y in
  sum (map (fun i => sum (sublist (delta n numt i) (delta n numt (i+1)) y)) (iota numt)).

Lemma dotprod_f_sanity :
 forall numt v12,
  0 < numt ->
  (forall x y z, (Float.add (Float.add x y) z) = Float.add x (Float.add y z)) ->
  (forall x, Float.add Float.zero x = x) ->
  dotprod_f numt v12 = dotprod v12.
Proof.
 intros ? ? H2 ? ?.
 (* Let's pretend we don't know that from assumption H0 one could actually prove False... *)
assert (forall y : float, Float.add Float.zero y = Float.add y Float.zero).
intro; apply Float.add_commut; left; reflexivity.
unfold dotprod_f, dotprod.
destruct v12 as [v1 v2].
simpl.
set (n := Zlength _).
set (d := delta n numt).
set (v := map (uncurry _) _) in *.
clearbody v.
transitivity (sum (sublist 0 (d numt) v)).
2:{ rewrite sublist_same; auto; try lia. apply delta_numt; rep_lia. }
rewrite <- (Z2Nat.id numt) by lia.
assert (Z.of_nat (Z.to_nat numt) <= numt) by lia.
revert H2.
induction (Z.to_nat numt); intro.
simpl. unfold d. rewrite delta_0. list_solve.
rewrite inj_S. unfold Z.succ. rewrite iota_S by lia.
pose proof delta_range n numt ltac:(rep_lia) ltac:(lia) (Z.of_nat n0) ltac:(rep_lia).
pose proof delta_range n numt ltac:(rep_lia) ltac:(lia)  ((Z.of_nat n0)+1) ltac:(rep_lia).
fold d in H4, H5.
rewrite (sublist_split 0 (d (Z.of_nat n0))).
2: lia.
2:{ split. apply delta_S; lia. lia. }
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

Definition dtask_pred (numt: Z) (input: dtask_input_type) (q: query) (p: val) :=
        let '(contents,(p1,p2)) := input in 
        let n := Zlength (fst contents) in 
        !! (n = Zlength (snd contents) /\ n <= Int.max_unsigned) &&
        field_at (q_share q) t_dtask (DOT _vec1) p1 p *
        field_at (q_share q) t_dtask (DOT _vec2) p2 p *
        field_at (q_share q) t_dtask (DOT _n) (Vint (Int.repr (Zlength (fst contents)))) p *
        a_pred q (field_at Ews t_dtask (DOT _result) 
                 (answer_val q (Vfloat (dotprod contents))) p) *
        data_at (q_share q) (tarray tdouble n) (map Vfloat (fst contents)) p1 *
        data_at (q_share q) (tarray tdouble n) (map Vfloat (snd contents)) p2.

Arguments dtask_pred numt input q p : simpl never.

Lemma dtask_pred_local_facts:
  forall numt input q p,
     dtask_pred numt input q p |-- !! isptr p.
Proof.
intros.
unfold dtask_pred.
destruct input as [[? ?] [? ? ]].
entailer!.
Qed.

#[export] Hint Resolve dtask_pred_local_facts : saturate_local.

Lemma dtask_pred_valid_pointer:
  forall numt input q p,
   dtask_pred numt input q p |-- valid_pointer p.
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

Lemma dtask_pred_input_eq: forall numt input1 input2  p,
          dtask_pred numt input1 REMEMBER p * 
          dtask_pred numt input2 ANSWER p 
          |-- !! (input1 = input2).
Proof.
intros.
unfold dtask_pred.
destruct input1 as [contents1 [p11 p12]].
destruct input2 as [contents2 [p21 p22]].
Intros.
simpl q_share. unfold a_pred.
assert_PROP (isptr p11 /\ isptr p12 /\ isptr p21 /\ isptr p22).
entailer!.
destruct H3 as [? [? [? ?]]].
sep_apply (data_at_value_eq Ers Ers2 tdouble p21 p11
                  (field_address t_dtask (DOT _vec1) p)); auto.
sep_apply (data_at_value_eq Ers Ers2 tdouble p22 p12
                  (field_address t_dtask (DOT _vec2) p)); auto.
Intros.
subst.
clear H5 H6.
rewrite !field_at_data_at.
sep_apply (data_at_int_value_eq Ers Ers2 
                     (Int.repr (Zlength (fst contents2)))
                     (Int.repr (Zlength (fst contents1)))
                     (field_address t_dtask (DOT _n) p)); auto.
Intros.
apply repr_inj_unsigned in H5; try rep_lia.
rewrite H5 in *.
sep_apply (data_at_array_float_value_eq Ers Ers2 (Zlength (fst contents1))
         (fst contents2) (fst contents1)); auto.
sep_apply (data_at_array_float_value_eq Ers Ers2 (Zlength (fst contents1))
         (snd contents2) (snd contents1)); auto.
Intros.
apply prop_right.
clear - H6 H7.
destruct contents1, contents2; simpl in *;
congruence.
Qed.

#[export] Instance dtask_package : task_package :=
  Build_task_package dtask_input_type _ dtask_output_type
   dtask_pred 
   dtask_pred_local_facts
   dtask_pred_valid_pointer
   dtask_pred_input_eq.

Definition dotprod_worker_spec :=
 DECLARE _dotprod_worker
 WITH numt: Z, clo : val, input: task_input_type
 PRE [ tptr tvoid ]
    PROP() PARAMS(clo) SEP (dtask_pred numt input ASK clo)
 POST [ tvoid ]
    PROP() RETURN() SEP(dtask_pred numt input ANSWER clo).

Definition fclo (gv: globals) (numt: Z) (dtp: val) : list (val*val) :=
  map (fun i => (gv _dotprod_worker, 
                         field_address0 (tarray t_dtask numt) (SUB i) dtp)) 
        (iota numt).

Definition tasking numt (gv: globals) :=
  EX tp:val, EX dtp: val,
   !! (0 < numt < 10000) &&
   data_at Ews tuint (vint numt) (gv _num_threads) *
   data_at Ews (tptr t_task) tp (gv _tasks) *
   task_array dtask_package (fclo gv numt dtp) tp *
   data_at Ews (tptr t_dtask) dtp (gv _dtasks) *
   data_at_ Ews (tarray t_dtask numt) dtp.

Definition dotprod_spec :=
  DECLARE _dotprod
  WITH numt:Z, p1:val, p2: val, v1: list float, v2: list float, gv: globals
  PRE [ tptr tdouble, tptr tdouble, tuint ]
    PROP ( Zlength v1 = Zlength v2; Zlength v1 <= Int.max_unsigned)
    PARAMS ( p1; p2; Vint (Int.repr (Zlength v1))) GLOBALS(gv)
    SEP (tasking numt gv;
           data_at Ews (tarray tdouble (Zlength v1)) (map Vfloat v1) p1;
           data_at Ews (tarray tdouble (Zlength v2)) (map Vfloat v2) p2)
  POST [ tdouble ]
    PROP()
    RETURN (Vfloat (dotprod_f numt (v1,v2)))
    SEP (tasking numt gv;
           data_at Ews (tarray tdouble (Zlength v1)) (map Vfloat v1) p1;
           data_at Ews (tarray tdouble (Zlength v2)) (map Vfloat v2) p2).

Definition make_dotprod_tasks_spec :=
  DECLARE _make_dotprod_tasks
  WITH t: Z, gv: globals
  PRE [ tuint ]
     PROP (1 <= t < 10000)
     PARAMS (vint t) GLOBALS (gv)
     SEP (library.mem_mgr gv;
           data_at_ Ews tuint (gv _num_threads);
           data_at_ Ews (tptr t_task) (gv _tasks);
           data_at_ Ews (tptr t_dtask) (gv _dtasks))
   POST [ tvoid ]
     PROP() RETURN() SEP(library.mem_mgr gv; tasking t gv; TT).

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

Definition partial_dotprod_f (t numt: Z) (v12: list float * list float) : dtask_output_type :=
 let '(v1,v2) := v12 in
 let y :=  map (uncurry Float.mul) (combine v1 v2) in
 let n := Zlength y in
  sum (map (fun i => sum (sublist (delta n numt i) (delta n numt (i+1)) y)) (iota t)).

Lemma body_make_dotprod_tasks: semax_body Vprog Gprog f_make_dotprod_tasks make_dotprod_tasks_spec.
Proof.
start_function.
forward_call .
Intros tp.
forward.
forward.
forward_call (tarray t_dtask t, gv).
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
rename t into numt.
Intros. clear H0.
deadvars!.
forward_for_simple_bound numt
 (EX t:Z, 
   PROP ( )
   LOCAL (gvars gv; temp _T (vint numt))
   SEP (library.mem_mgr gv;
   library.malloc_token Ews (tarray t_dtask numt) dtp;
   data_at_ Ews (tarray t_dtask numt) dtp;
   task_array dtask_package (
        map (fun i => (gv _dotprod_worker, 
                         field_address0 (tarray t_dtask numt) (SUB i) dtp)) 
           (iota t)  ++ Zrepeat (Vundef, Vundef) (numt-t)) 
      tp;
   TT;
   data_at Ews tuint (vint numt) (gv _num_threads);
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
                    field_address0 (tarray t_dtask numt) (SUB t) dtp,
                    fclo').
entailer!.
simpl.
rewrite field_address0_offset by auto with field_compatible.
reflexivity.
subst fclo'.
list_solve.
entailer!.
apply sepcon_derives; auto.
apply derives_refl'.
f_equal.
subst fclo'.
rewrite upd_Znth_app2 by list_simplify.
list_simplify.
rewrite !Znth_iota by lia.
reflexivity.
rewrite !Znth_iota by lia.
rewrite <- app_nil_end.
assert (i=t) by lia. subst.
reflexivity.
-
forward.
unfold tasking.
Exists tp dtp.
rewrite prop_true_andp by lia.
list_simplify.
change (map _ _) with (fclo gv numt dtp).
cancel.
Qed.

Lemma field_at_SUB_t_DOT_result:
 forall t numt a dtp,
 0 <= t < numt ->
 numt < 10000 ->
 field_compatible (tarray t_dtask numt) [] dtp ->
 field_at Ews (tarray t_dtask numt) [StructField _result; ArraySubsc t]
  (Vfloat a) dtp
 = field_at Ews t_dtask (DOT _result) (Vfloat a)
      (field_address0 (tarray t_dtask numt) (SUB t) dtp).
(* issue: VST-Floyd should have a lemma for composing paths like this. *)
Proof.
intros until 1. intro Hnumt. intros.
rewrite !field_at_data_at.
simpl.
f_equal.
assert (Ht: 20 * t < 20 * numt) by nia.
rewrite !field_address_offset by auto with field_compatible.
rewrite field_address0_offset by auto with field_compatible.
rewrite field_address_offset.
simpl.
rewrite offset_offset_val.
reflexivity.
simpl.
destruct H0 as [? [? [? [? ?]]]].
destruct dtp; try contradiction.
clear H0.
split3; [ | | split3]; auto.
red in H2 |- *.
simpl.
unfold sizeof in H2; simpl in H2.
rewrite Z.max_r in H2 by lia.
rewrite <- (Ptrofs.repr_unsigned i) in H2|-*.
rewrite ptrofs_add_repr.
rewrite Ptrofs.unsigned_repr in H2 by rep_lia.
rewrite Ptrofs.unsigned_repr by rep_lia.
lia.
red in H3|-*.
unfold offset_val.
eapply align_compatible_rec_Tarray_inv in H3; [ | eassumption].
simpl Ctypes.sizeof in H3.
replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr (0 + 20 * t))))
  with (Ptrofs.unsigned i + 20 * t); auto.
unfold Ptrofs.add.
rewrite !Ptrofs.unsigned_repr; try nia.
rep_lia.
rewrite Ptrofs.unsigned_repr by rep_lia.
red in H2.
simpl sizeof in H2.
rewrite Z.max_r in H2 by lia.
rep_lia.
split; auto. 
simpl.
right; right; right. left; auto.
Qed.

Lemma finish_dotprod:
 forall numt p1 p2 v1 v2 dtp gv,
  Zlength v1 = Zlength v2 ->
  0 < numt < 10000 ->
  let delt := delta (Zlength v1) numt in
let inp :=
  map
    (fun i : Z =>
     ((sublist (delt i) (delt (i + 1)) v1, sublist (delt i) (delt (i + 1)) v2),
      (field_address0 (tarray tdouble (Zlength v1)) (SUB delt i) p1,
       field_address0 (tarray tdouble (Zlength v1)) (SUB delt i) p2)))
 (iota numt) in
field_compatible (tarray t_dtask numt) [] dtp ->
field_compatible0 (tarray tdouble (Zlength v1)) [] p1 ->
field_compatible0 (tarray tdouble (Zlength v1)) [] p2 ->
pred_sepcon (ith_spectask dtask_package (fclo gv numt dtp) inp ANSWER)
  (fun i : Z => 0 <= i < numt)
|-- data_at_ Ews (tarray t_dtask numt) dtp
      * data_at Ews (tarray tdouble (Zlength v1)) (map Vfloat v1) p1
      * data_at Ews (tarray tdouble (Zlength v1)) (map Vfloat v2) p2.
Proof.
intros.
set (t:=numt).
unfold t at 1.
replace (data_at Ews (tarray tdouble (Zlength v1)) (map Vfloat v1) p1)
  with (data_at Ews (tarray tdouble (delt t)) (map Vfloat (sublist 0 (delt t) v1)) p1).
2:{ unfold t. unfold delt.
  rewrite delta_numt by rep_lia.
 f_equal. f_equal.
 apply sublist_same; auto.
}

replace (data_at Ews (tarray tdouble (Zlength v1)) (map Vfloat v2) p2)
  with (data_at Ews (tarray tdouble (delt t)) (map Vfloat (sublist 0 (delt t) v2)) p2).
2:{ unfold t. unfold delt.
 rewrite H.
  rewrite delta_numt by rep_lia.
 f_equal. f_equal.
 apply sublist_same; auto.
}
assert (0 <= t <= numt) by lia.
clearbody t.
rewrite <- (Z2Nat.id t) in * by lia.
induction (Z.to_nat t).
-
replace (fun i : Z => 0 <= i < Z.of_nat 0) with (fun i:Z => False)
  by (extensionality j; apply prop_ext; split; intro; lia).
rewrite pred_sepcon_False.
simpl Z.of_nat.
unfold delt; rewrite delta_0.
apply derives_trans with (emp * emp * emp).
cancel.
repeat apply sepcon_derives; apply data_at_zero_array;
 auto with field_compatible.
-
rewrite inj_S. unfold Z.succ. 
rewrite (pred_sepcon_isolate (Z.of_nat n) zeq) by lia.
unfold ith_spectask.
sep_apply func_ptr'_emp.
replace (fun y : Z => 0 <= y < Z.of_nat n + 1 /\ y <> Z.of_nat n)
 with (fun i : Z => 0 <= i < Z.of_nat n)
  by (extensionality j; apply prop_ext; split; intro; lia).
fold (ith_spectask  dtask_package (fclo gv numt dtp) inp ANSWER).
sep_apply IHn; try lia.
clear IHn.
clear t.
rename n into t.
set (n := Zlength v1) in *.
change task_pred with dtask_pred.
unfold dtask_pred.
subst inp.
unfold fclo.
rewrite !Znth_map by (rewrite ?Zlength_iota; lia).
simpl.
Intros. clear H5 H6.
pose proof delta_range n numt ltac:(rep_lia) ltac:(lia) (Z.of_nat t) ltac:(lia). fold delt in H5.
pose proof delta_range n numt ltac:(rep_lia) ltac:(lia) (Z.of_nat t + 1) ltac:(lia). fold delt in H6.
pose proof delta_S n ltac:(lia) numt (Z.of_nat t) ltac:(lia). fold delt in H7.
rewrite !Znth_iota by lia.
rewrite !Zlength_sublist by lia.
change (data_at_ ?sh ?t ?p) 
  with (data_at sh t (default_val t) p).
sep_apply (field_at_share_join Ers Ers2 Ews t_dtask (DOT _vec1)); auto with shares.
sep_apply (field_at_share_join Ers Ers2 Ews t_dtask (DOT _vec2)); auto with shares.
sep_apply (field_at_share_join Ers Ers2 Ews t_dtask (DOT _n)); auto with shares.
sep_apply (field_at_field_at_ Ews t_dtask (DOT _vec1)).
sep_apply (field_at_field_at_ Ews t_dtask (DOT _vec2)).
sep_apply (field_at_field_at_ Ews t_dtask (DOT _n)).
sep_apply (field_at_field_at_ Ews t_dtask (DOT _result)).
assert (
 field_at_ Ews t_dtask (DOT _vec1)
                 (field_address0 (tarray t_dtask numt) (SUB Z.of_nat t) dtp)
* field_at_ Ews t_dtask (DOT _vec2)
            (field_address0 (tarray t_dtask numt) (SUB Z.of_nat t) dtp)
* field_at_ Ews t_dtask (DOT _n)
       (field_address0 (tarray t_dtask numt) (SUB Z.of_nat t) dtp)
* field_at_ Ews t_dtask (DOT _result)
  (field_address0 (tarray t_dtask numt) (SUB Z.of_nat t) dtp)
|-- data_at_ Ews t_dtask 
  (field_address0 (tarray t_dtask numt) (SUB Z.of_nat t) dtp)). {
 unfold_data_at (data_at_ _ _ _).
 simpl. cancel.
}
sep_apply H8; clear H8.
change (data_at_ ?sh ?t ?p) 
  with (data_at sh t (default_val t) p).
sep_apply (data_at_singleton_array Ews t_dtask [default_val t_dtask] _ 
          (field_address0 (tarray t_dtask numt) (SUB Z.of_nat t) dtp) (eq_refl _)).
pose proof split2_data_at_Tarray_app 
  (delt (Z.of_nat t)) (delt (Z.of_nat t + 1)) Ews.
set (dta := default_val (tarray t_dtask (Z.of_nat t)) : list (reptype t_dtask)).
set (dtb := [default_val t_dtask] : list (reptype t_dtask)).
pose proof (split2_data_at_Tarray_app (Z.of_nat t) (Z.of_nat t+1) Ews
                       t_dtask dta dtb dtp). 
spec H9. { 
 subst dta. unfold default_val; simpl.
  rewrite Zlength_Zrepeat by lia. auto.
}
spec H9. { 
 subst dtb. simpl. list_solve. 
}
pose proof (derives_refl' _ _ (eq_sym H9)).
replace (field_address0 (tarray t_dtask (Z.of_nat t + 1)) (SUB Z.of_nat t) dtp)
 with (field_address0 (tarray t_dtask numt)  (SUB Z.of_nat t) dtp)
 in H10.
2:{
rewrite !field_address0_offset by auto with field_compatible.
reflexivity.
}
replace (Z.of_nat t + 1 - Z.of_nat t) with 1 in H10 by lia.
sep_apply H10.
clear H9 H10.
cancel.
rewrite !(sublist_split 0 (delt (Z.of_nat t)) (delt (Z.of_nat t + 1))) by lia.
rewrite !map_app.
rewrite !(split2_data_at_Tarray_app (delt (Z.of_nat t)) (delt (Z.of_nat t + 1)) 
    Ews tdouble) by list_solve.
cancel.
clear H8 dta dtb.
set (dt := delt (Z.of_nat t)) in *.
set (dt1 := delt (Z.of_nat t + 1)) in *.
clearbody dt. clearbody dt1. clear t H1 delt H4.
replace (field_address0 (tarray tdouble dt1) (SUB dt) p1)
 with  (field_address0 (tarray tdouble n) (SUB dt) p1).
2:{
rewrite !field_address0_offset by auto with field_compatible.
reflexivity.
}
replace (field_address0 (tarray tdouble dt1) (SUB dt) p2)
 with  (field_address0 (tarray tdouble n) (SUB dt) p2).
2:{
rewrite !field_address0_offset by auto with field_compatible.
reflexivity.
}
sep_apply (data_at_share_join Ers Ers2 Ews (tarray tdouble (dt1-dt))); auto with shares.
sep_apply (data_at_share_join Ers Ers2 Ews (tarray tdouble (dt1-dt))); auto with shares.
cancel.
Qed.

Lemma body_dotprod: semax_body Vprog Gprog f_dotprod dotprod_spec.
Proof.
start_function.
unfold tasking. Intros tp dtp.
assert_PROP (field_compatible (tarray t_dtask numt) nil dtp) as Hdtp by entailer!.
rewrite <- H.
set (n := Zlength v1) in *.
assert (Hn: 0 <= n) by apply Zlength_nonneg.
forward.
forward.

assert_PROP (field_compatible0 (tarray tdouble n) nil p1 /\
                    field_compatible0 (tarray tdouble n) nil p2) by  entailer!.
destruct H2.
pose proof delta_range n numt.
set (delt := delta n numt) in *.
assert (Hforce:  
         forall t p, 
          0 <= t <= numt -> 
          field_compatible0 (tarray tdouble n) [] p ->
        force_val
           (sem_add_ptr_int tdouble Unsigned p (vint (delt t))) 
       = field_address0 (tarray tdouble n) (SUB (delt t)) p). {
  intros.
 unfold sem_add_ptr_int.
 pose proof (H4 ltac:(lia) ltac:(lia) t).
 rewrite sem_add_pi_ptr by (auto; rep_lia).
 rewrite field_address0_offset by auto with field_compatible.
 simpl. f_equal; lia.
}
  
freeze FR1 := - (data_at Ews (tptr t_task) tp (gv _tasks))
                (data_at Ews (tptr t_dtask) dtp (gv _dtasks))
               (data_at_ Ews  (tarray t_dtask numt) dtp).
pose (nthtask i := (field_address0 (tarray tdouble n) (SUB (delt i)) p1,
                            (field_address0 (tarray tdouble n) (SUB (delt i)) p2,
                             (Vint (Int.repr (delt (i+1) - delt i)), Vundef)))).
forward_for_simple_bound numt 
   (EX t:Z,   
    PROP ()
    LOCAL (temp _delta (vint (delt t)); temp _T (vint numt);
                gvars gv; temp _vec1 p1; temp _vec2 p2; 
                temp _n (vint n))
   SEP (FRZL FR1;
          data_at Ews (tptr t_task) tp (gv _tasks);
          data_at Ews (tptr t_dtask) dtp (gv _dtasks);
          data_at Ews (tarray t_dtask numt) 
             (map nthtask (iota t)
                     ++ Zrepeat (default_val t_dtask) (numt-t))
             dtp ))%assert.
-
entailer!. apply derives_refl.
-
rename i into t.
pose proof (H4 ltac:(lia) ltac:(lia) t).
replace (numt-t) with (1+(numt-(t+1))) by lia.
rewrite <- Zrepeat_app by lia.
change (Zrepeat (default_val t_dtask) 1) with [ (Vundef,(Vundef,(Vundef,Vundef))) ].
forward.
forward.
rewrite Hforce by (auto; lia).

list_simplify.
rewrite upd_Znth_app2, upd_Znth_app1 by Zlength_solve. 
rewrite Zlength_map, Zlength_iota, Z.sub_diag by lia.
unfold fst, snd.
change (Zrepeat ?a 1) with [a].
rewrite upd_Znth0.
list_simplify. 

forward.
forward.
rewrite Hforce by (auto; lia).
list_simplify.
rewrite upd_Znth_app2, upd_Znth_app1 by Zlength_solve. 
rewrite Zlength_map, Zlength_iota, Z.sub_diag by lia.
unfold fst, snd.
change (Zrepeat ?a 1) with [a].
rewrite upd_Znth0.
list_simplify. 

forward.
entailer!.
rewrite Int.unsigned_repr in H16 by rep_lia.
assert (numt = 0); [ | lia].
clear - H16 H1.
rewrite <- (Int64.unsigned_repr numt) by rep_lia.
rewrite H16. reflexivity.
rewrite add_repr.
rewrite !Int.unsigned_repr by rep_lia.
rewrite mul64_repr.

rewrite divu64_repr; [ | | rep_lia].
2:{ clear - H5 H0 Hn H1.
  assert (numt * Int.max_unsigned <= Int64.max_unsigned) by rep_lia.
  split; try lia.
  eapply Z.le_trans; [ | apply H].
  apply Z.mul_le_mono_nonneg; lia.
}
rewrite Int64.unsigned_repr.
2:{
clear - H5 H0 Hn H1.
split.
apply Z_div_nonneg_nonneg; try lia.
apply Z.div_le_upper_bound. lia.
  apply Z.mul_le_mono_nonneg; rep_lia.
}

forward.
forward.
change (let (q, _) := Z.div_eucl ((t + 1) * n) numt in q) with ((t+1)*n/numt).
change ((t+1)*n/numt) with (delt (t+1)).
list_simplify.
rewrite upd_Znth_app2, upd_Znth_app1 by Zlength_solve. 
rewrite Zlength_map, Zlength_iota, Z.sub_diag by lia.
unfold fst, snd.
change (Zrepeat ?a 1) with [a].
rewrite upd_Znth0.
list_simplify.

forward.

entailer!.
apply  derives_refl'.
f_equal.
rewrite iota_S by lia.
rewrite map_app.
rewrite <- !app_assoc.
reflexivity.

-
list_simplify.
thaw FR1.
make_func_ptr _dotprod_worker. 
 change (func_ptr' _) with (func_ptr' (snd dotprod_worker_spec)).
assert_PROP (isptr tp) by entailer!.
forward.
pose (inp := (map (fun i => 
                              ((sublist (delt i) (delt(i+1)) v1,
                                sublist (delt i) (delt(i+1)) v2),
                               (field_address0 (tarray tdouble n) (SUB delt i) p1,
                                field_address0 (tarray tdouble n) (SUB delt i) p2)))
                          (iota numt))).
forward_call (fclo gv numt dtp ,inp,tp).
apply prop_right.
simpl. f_equal. f_equal. f_equal. unfold fclo. f_equal. autorewrite with sublist. rewrite Zlength_iota. auto.
lia.

assert (
  func_ptr' (snd dotprod_worker_spec) (gv _dotprod_worker)
  * data_at Ews (tarray tdouble n) (map Vfloat v1) p1
  * data_at Ews (tarray tdouble n) (map Vfloat v2) p2
  * data_at Ews (tarray t_dtask numt) (map nthtask (iota numt)) dtp
 |-- spectasks_list dtask_package (fclo gv numt dtp) inp ASK);
 [ | sep_apply H8; cancel]. {
 unfold spectasks_list.
 rewrite pred_sepcon_eq.
 Exists (iota numt).
 rewrite prop_true_andp.
 2:{ split. intros.
   unfold fclo. rewrite Zlength_map, Zlength_iota by lia.

 apply in_iota.
 apply NoDup_iota.
 }
pose proof delta_numt n numt ltac:(lia) ltac:(lia). fold delt in H8.
 assert (data_at Ews (tarray tdouble n) (map Vfloat v1) p1
        |-- data_at Ews (tarray tdouble (delt numt)) (map Vfloat (sublist 0 (delt numt) v1)) p1).
   clear - H8. rewrite sublist_same by auto. rewrite H8. cancel.
 sep_apply H9. clear H9.
 assert (data_at Ews (tarray tdouble n) (map Vfloat v2) p2
        |-- data_at Ews (tarray tdouble (delt numt)) (map Vfloat (sublist 0 (delt numt) v2)) p2).
   clear - H H8. rewrite H8.  rewrite sublist_same by auto. cancel.
 sep_apply H9. clear H9.
 assert_PROP (field_compatible (tarray t_dtask numt) nil dtp) by entailer!.
 clear - H1 H H0 H2 H3 H9.
 set (fclo1 := fclo _ _ _).
 rewrite <- (Z2Nat.id numt) by lia.
 assert (Z.of_nat (Z.to_nat numt) <= numt) by lia.
 revert H4.
 forget (Z.to_nat numt) as t.
 rewrite !map_sublist.
 induction t; intros.
 simpl. change (delt  0) with 0.
 sep_apply data_at_zero_array_inv.
 sep_apply data_at_zero_array_inv.
 sep_apply data_at_zero_array_inv.
 sep_apply func_ptr'_emp.
 cancel.
 pose proof delta_range n numt ltac:(rep_lia) ltac:(lia) (Z.of_nat t) ltac:(lia). fold delt in H5.
 pose proof delta_range n numt ltac:(rep_lia) ltac:(lia) (Z.of_nat t + 1) ltac:(lia). fold delt in H6.
 rename H6 into H5'.
 pose proof delta_S n ltac:(lia) numt (Z.of_nat t) ltac:(lia). fold delt in H6.
 rewrite inj_S. unfold Z.succ. rewrite iota_S by lia.
 rewrite iter_sepcon_app.
 rewrite !(sublist_split 0 (delt (Z.of_nat t)) (delt (Z.of_nat t + 1)))
   by (rewrite ?Zlength_map; lia).
 rewrite !(split2_data_at_Tarray_app (delt (Z.of_nat t))) by list_solve.
 rewrite map_app.
 rewrite <- !sepcon_assoc.
change (@app (val * (val * (val * val)))) with (@app (reptype t_dtask)).
 rewrite (split2_data_at_Tarray_app (Z.of_nat t) (Z.of_nat t + 1) Ews t_dtask)
   by list_solve.
 rewrite split_func_ptr'.
 sep_apply IHt. lia. clear IHt.
 apply sepcon_derives.
 apply derives_refl.
 unfold iter_sepcon.
 unfold ith_spectask.
 replace (fst (Znth (Z.of_nat t) fclo1)) with (gv _dotprod_worker).
 change (snd dotprod_worker_spec)
   with (task_f_spec dtask_package).
 cancel.
 2:{ subst fclo1.
      unfold fclo. rewrite Znth_map. reflexivity.
      rewrite Zlength_iota; lia.
    }
 simpl task_pred. unfold dtask_pred.
 subst inp.
    rewrite !Znth_map by (rewrite Zlength_iota; lia).
 simpl.
 rewrite prop_true_andp.
2:{ rewrite ?Znth_iota by lia.
 rewrite !Zlength_sublist by lia. lia.
}
 subst fclo1. unfold fclo.
    rewrite !Znth_map by (rewrite Zlength_iota; lia).
  simpl fst. simpl snd.
  rewrite !Zlength_sublist by (rewrite Znth_iota by lia; lia).
  replace (Z.of_nat t + 1 - Z.of_nat t) with 1 by lia.
  erewrite data_at_singleton_array_eq by reflexivity. 
  unfold nthtask.
  unfold_data_at (data_at _ t_dtask _ _).
  rewrite Znth_iota by lia.
assert (field_address0 (tarray t_dtask  (Z.of_nat t + 1)) (SUB Z.of_nat t) dtp
         =  field_address0 (tarray t_dtask numt) (SUB Z.of_nat t) dtp). {
  rewrite  !field_address0_offset by auto with field_compatible.
  reflexivity. 
}
 rewrite prop_true_andp by (split; lia).
 set (k := delt _ - delt _).

 rewrite !H7. clear H7.
 rewrite !sublist_map.
rewrite <-  (field_at_share_join Ers Ers2 Ews t_dtask (DOT _vec1)); auto with shares.
rewrite <- (field_at_share_join Ers Ers2 Ews t_dtask (DOT _vec2)); auto with shares.
rewrite <- (field_at_share_join Ers Ers2 Ews t_dtask (DOT _n)); auto with shares.
 cancel.
 assert (field_address0 (tarray tdouble (delt (Z.of_nat t + 1))) (SUB delt (Z.of_nat t)) p1
       = field_address0 (tarray tdouble n) (SUB delt (Z.of_nat t)) p1). {
    rewrite  !field_address0_offset by auto with field_compatible.
    reflexivity.
}
 rewrite H7; clear H7.
 assert (field_address0 (tarray tdouble (delt (Z.of_nat t + 1))) (SUB delt (Z.of_nat t)) p2
       = field_address0 (tarray tdouble n) (SUB delt (Z.of_nat t)) p2). {
    rewrite  !field_address0_offset by auto with field_compatible.
    reflexivity.
}
 rewrite H7; clear H7.
rewrite <- !(data_at_share_join Ers Ers2 Ews) by auto with shares.
cancel.
}
 unfold fclo. rewrite Zlength_map, Zlength_iota. lia. lia.

 forward.
deadvars!.
freeze FR2 := - (spectasks_list dtask_package (fclo gv numt dtp) inp ANSWER)
   (data_at Ews (tptr t_dtask) dtp (gv _dtasks)).
unfold spectasks_list.
unfold fclo at 2.
rewrite Zlength_map, Zlength_iota by lia.
forward_for_simple_bound numt
  (EX t:Z, 
     PROP ()
     LOCAL (temp _result (Vfloat (partial_dotprod_f t numt (v1, v2)));
     temp _T (vint numt); gvars gv)
     SEP (FRZL FR2;
     data_at Ews (tptr t_dtask) dtp (gv _dtasks);
     pred_sepcon
      (ith_spectask dtask_package (fclo gv numt dtp) inp ANSWER)
      (fun i : Z => 0 <= i < numt)))%assert.
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
forward.
 pose proof (delta_range (Zlength v1) numt) ltac:(lia) ltac:(lia) t ltac:(lia).
 pose proof (delta_range (Zlength v1) numt) ltac:(lia) ltac:(lia) (t+1) ltac:(lia).
 pose proof (delta_S (Zlength v1) ltac:(lia) numt t ltac:(lia)).
 fold n in H11, H12, H13.
 fold delt in H11,H12,H13.
entailer!.
* 
 clear H29 H28 H27 H26 H25 H24 H23 H22 H21 H20 H19 H18
         H17 H16 H15 H14.
 f_equal.
 unfold partial_dotprod_f, dotprod_f.
 rewrite !Zlength_map.
 rewrite !Zlength_combine.
 rewrite <- H.
 rewrite !Z.min_id.
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
 fold delt.
 auto.
*
rewrite (pred_sepcon_isolate t zeq _ (fun i : Z => 0 <= i < numt)) by lia.
unfold ith_spectask.
rewrite Zlength_map. 
rewrite !Znth_map by (rewrite Zlength_iota; lia).
rewrite !sepcon_assoc.
apply sepcon_derives.
apply derives_refl.
replace (fst (Znth t (fclo gv numt dtp))) with (gv _dotprod_worker).
2:{ unfold fclo.
  rewrite Znth_map by (rewrite Zlength_iota; lia).
  reflexivity.
}
apply sepcon_derives.
apply derives_refl.
change task_pred with dtask_pred.
unfold dtask_pred.
simpl.
rewrite prop_true_andp.
2:{
rewrite Znth_iota by lia.
rewrite !Zlength_sublist by lia.
split; lia.
}
rewrite !Znth_iota by lia.
rewrite !Zlength_sublist by lia.
unfold fclo.
rewrite !Znth_map by (rewrite Zlength_iota; lia).
simpl fst; simpl snd.
rewrite !Znth_iota by lia.
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

 









