Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.

Open Scope logic.
Print data_at_rec.
Import type_induction aggregate_pred.

Definition value_defined_byvalue {cs: compspecs} t v :=
if type_is_volatile t then False else tc_val t (repinject t v).

Definition value_defined {cs:compspecs} : forall t, reptype t -> Prop :=
  type_func (fun t => reptype t -> Prop)
    value_defined_byvalue
    (fun t n a P v => Zlength (unfold_reptype v) =  Z.max 0 n /\ Forall P (unfold_reptype v))
    (fun id a P v => struct_value_fits_aux (co_members (get_co id)) (co_members (get_co id)) P (unfold_reptype v))
    (fun id a P v => union_value_fits_aux (co_members (get_co id)) (co_members (get_co id)) P (unfold_reptype v)).

Lemma value_defined_eq {cs: compspecs}:
  forall t v,
  value_defined t v =
  match t as t0 return (reptype t0 -> Prop)  with
  | Tarray t' n a => fun v0 : reptype (Tarray t' n a) =>
    (fun v1 : list (reptype t') =>
     Zlength v1 = Z.max 0 n /\ Forall (value_defined t') v1)
      (unfold_reptype v0)
| Tstruct i a =>
    fun v0 : reptype (Tstruct i a) =>
     struct_Prop (co_members (get_co i))
       (fun it : member =>
        value_defined (field_type (name_member it) (co_members (get_co i)))) (unfold_reptype v0)
| Tunion i a =>
    fun v0 : reptype (Tunion i a) =>
     union_Prop (co_members (get_co i))
       (fun it : member =>
        value_defined (field_type (name_member it) (co_members (get_co i)))) (unfold_reptype v0)
  | t0 => value_defined_byvalue t0
  end v.
Proof.
intros.
unfold value_defined.
rewrite type_func_eq.
destruct t; auto.
apply struct_value_fits_aux_spec.
apply union_value_fits_aux_spec.
Qed.

Lemma value_defined_not_volatile:
  forall {cs: compspecs} t v, value_defined t v -> type_is_volatile t = false.
Proof.
intros.
destruct t; try reflexivity; 
do 5 red in H;
destruct (type_is_volatile _); auto; contradiction.
Qed.

(*
Lemma struct_pred_sepcon_cohere: forall m {A}
    (P Q: forall it, A it -> val -> mpred) v1 v2 p,
  struct_pred m P v1 p * struct_pred m Q v2 p |-- !! (v1=v2).
Proof.
  intros.
  destruct m as [| a0 m]; [| revert a0 v1 v2; induction m as [| a1 m]; intros].
  + hnf in v1,v2. destruct v1,v2.  entailer!.
  + simpl. hnf in v1,v2.
    rewrite emp_sepcon; auto.
  + simpl.
    auto.
  + change (struct_pred (a0 :: a1 :: m) P v p)
      with (P a0 (fst v) p * struct_pred (a1 :: m) P (snd v) p).
    change (struct_pred (a0 :: a1 :: m) Q v p)
      with (Q a0 (fst v) p * struct_pred (a1 :: m) Q (snd v) p).
    change (struct_pred (a0 :: a1 :: m) (fun it => P it * Q it) v p)
      with (P a0 (fst v) p * Q a0 (fst v) p * struct_pred (a1 :: m) (fun it => P it * Q it) (snd v) p).
    rewrite !sepcon_assoc; f_equal.
    rewrite <- sepcon_assoc, (sepcon_comm _ (Q _ _ _)), sepcon_assoc; f_equal.
    apply IHm.
Qed.
*)

Local Definition field_atx {cs} sh m (sz: Z) (it : member)
                   (v : reptype
                           (field_type (name_member it) m))
       := 
                 withspacer sh
                   (field_offset (@cenv_cs cs) (name_member it) m
                      + sizeof
                          (field_type (name_member it) m))
                   (field_offset_next (@cenv_cs cs) (name_member it) m sz)
                   (at_offset
                      (@data_at_rec cs sh
                         (field_type (name_member it) m) v)
                      (field_offset (@cenv_cs cs) (name_member it) m)).

Local Definition field_cohere {cs: compspecs} sh1 sh2 
  m b it :=
 forall (v1 v2: reptype (field_type (name_member it) m)) ofs,
        type_is_volatile
          (field_type (name_member it) m) = false ->
        value_defined
          (field_type (name_member it) m) v1 ->
        value_defined
          (field_type (name_member it) m) v2 ->
        data_at_rec sh1
          (field_type (name_member it) m) v1
          (Vptr b ofs)
          * data_at_rec sh2
              (field_type (name_member it) m) v2
              (Vptr b ofs) |-- !! (v1 = v2).

Lemma data_at_rec_share_join_values_cohere' {cs: compspecs}:
       forall (sh1 sh2 : share) (t : type),
       forall (b : block) (ofs : ptrofs),
       type_is_volatile t = false ->
       readable_share sh1 ->
       readable_share sh2 ->
       forall v1 v2 : reptype t,
       value_defined t v1 ->
       value_defined t v2 ->
       data_at_rec sh1 t v1 (Vptr b ofs)
         * data_at_rec sh2 t v2 (Vptr b ofs) 
        |-- !! (v1 = v2).
Proof.
  intros.
  red in H2, H3.
  revert v1 v2 ofs H H2 H3.
  pattern t; type_induction t; intros;
  rewrite !data_at_rec_eq; try solve [ normalize];
try solve [
  do 4 red in H2, H3;
  rewrite ?H in *;
 try (
   apply (mapsto_share_join_values_cohere sh1 sh2); trivial;
  try destruct f;
   (intro H5; apply JMeq_eq in H5; subst; try contradiction));
  try (hnf in H2; destruct (eqb_type _ _) in H2; contradiction);
  try (hnf in H3; destruct (eqb_type _ _) in H3; contradiction)].
- (* array *)
destruct H2.
change (Forall (value_defined t) (unfold_reptype v1)) in H4.
destruct H3.
change (Forall (value_defined t) (unfold_reptype v2)) in H5.
unfold aggregate_pred.array_pred.
destruct (zle z 0).
rewrite Z.max_l in * by lia.
apply prop_right.
rewrite Zlength_length in H2,H3 by lia.
destruct v1; inv H2. destruct v2; inv H3. auto.
rewrite Z.max_r in * by lia.
clear H.
pose proof (Z2Nat.id z) ltac:(lia).
set (n := Z.to_nat z) in *.
clearbody n.
rewrite <- H in *.
subst z.
change (@unfold_reptype cs (Tarray t (Z.of_nat n) a) v1) with v1 in *.
change (@unfold_reptype cs (Tarray t (Z.of_nat n) a) v2) with v2 in *.
assert (type_is_volatile t = false). {
 clear - H2 H4 g.
 destruct v1. rewrite Zlength_nil in H2. lia.
 inv H4.
 apply value_defined_not_volatile in H1; auto.
}
clear g.
change (list (reptype t)) in v1,v2.
revert v1 v2 H5 H3 H4 H2; induction n; intros.
apply prop_right.
clear - H3 H2.
rewrite Zlength_length in H2,H3 by lia.
destruct v1; inv H2. destruct v2; inv H3. auto.
rewrite inj_S in *.
rewrite !(split_array_pred 0 (Z.of_nat n) (Z.succ (Z.of_nat n))) by lia.
rewrite !Z.sub_0_r.
rewrite !(sublist_one (Z.of_nat n)) by lia.
unfold Z.succ.
rewrite !array_pred_len_1.
match goal with |- (?a*?b)*(?c*?d) |-- _ =>
    apply derives_trans with ((a*c)*(b*d)); [ cancel | ] end.
apply derives_trans 
  with (!! (sublist 0 (Z.of_nat n) v1 = sublist 0 (Z.of_nat n) v2) 
           * !! (Znth (Z.of_nat n) v1 = Znth (Z.of_nat n) v2)).
apply sepcon_derives.
apply IHn.
apply Forall_sublist; auto.
Zlength_solve.
apply Forall_sublist; auto.
Zlength_solve.
unfold at_offset.
apply IH; auto.
apply Forall_Znth; auto; lia.
apply Forall_Znth; auto; lia.
rewrite sepcon_prop_prop.
apply prop_derives; intros [? ?].
replace v1 with (sublist 0 (Z.of_nat n) v1 ++ [Znth (Z.of_nat n) v1]).
replace v2 with (sublist 0 (Z.of_nat n) v2 ++ [Znth (Z.of_nat n) v2]).
rewrite H6,H7; auto.
clear - H3.
rewrite <- sublist_last_1 by lia.
apply sublist_same; lia.
clear - H2.
rewrite <- sublist_last_1 by lia.
apply sublist_same; lia.
-
cbv zeta in IH.
clear H.
change (type_func _ _ _ _ _ ) with value_defined in *.
unfold aggregate_pred.struct_pred.
rewrite value_defined_eq in H2, H3.
cbv zeta in IH.
fold (@field_atx cs sh1 (co_members (get_co id)) (co_sizeof (get_co id))).
fold (@field_atx cs sh2 (co_members (get_co id)) (co_sizeof (get_co id))).
fold (field_cohere sh1 sh2 (co_members (get_co id)) b) in IH.
eapply derives_trans with (!! (unfold_reptype v1 = unfold_reptype v2)).
2:{  clear. 
       apply prop_derives; intro.
       unfold reptype, unfold_reptype in *.
       unfold eq_rect in *.
        destruct (reptype_eq (Tstruct id a)).
         auto.
}
set (u1 := unfold_reptype v1) in *.
set (u2 := unfold_reptype v2) in *.
clearbody u1. clearbody u2.
simpl in u1,u2. clear v1 v2.
destruct (get_co id); simpl in *.
rename co_sizeof into sz.
rename co_alignof into al.
rename co_rank into rank.
rename co_members into m.
unfold reptype_structlist in u1,u2.
assert (
forall sh1 sh2 b m0 m
 (IH : Forall (field_cohere sh1 sh2 m0 b) m)
 (ofs : ptrofs)
 (u1 u2 : compact_prod
       (map (fun it : member => reptype (field_type (name_member it) m0))
          m))
 (H2 : struct_Prop m
       (fun it : member =>
        value_defined
          match Ctypes.field_type (name_member it) m0 with
          | Errors.OK t => t
          | Errors.Error _ => Tvoid
          end) u1)
 (H3 : struct_Prop m
       (fun it : member =>
        value_defined
          match Ctypes.field_type (name_member it) m0 with
          | Errors.OK t => t
          | Errors.Error _ => Tvoid
          end) u2),
struct_pred m (field_atx sh1 m0 sz) u1 (Vptr b ofs)
  * struct_pred m (field_atx sh2 m0 sz) u2 (Vptr b ofs) |-- !! (u1 = u2)).
2: eauto.
clear.
intros.
destruct m as [ | a0 m].
destruct u1,u2; entailer!.
revert a0 IH u1 u2 H2 H3.
induction m as [ | a1 m]; intros.
+
simpl.
inv IH. clear H4.
red in H1.
unfold field_atx.
rewrite !withspacer_spacer.
rewrite !spacer_memory_block by (simpl; auto).
set (x1 := memory_block sh1 _ _).
set (x2 := memory_block sh2 _ _).
clearbody x1 x2.
unfold at_offset, offset_val.
set (ofs' := Ptrofs.add _ _). clearbody ofs'. 
sep_apply (H1 u1 u2 ofs'); auto.
clear - H3.
apply value_defined_not_volatile in H3.
apply H3.
entailer!.
+
repeat change (struct_pred (a0 :: a1 :: m) ?P ?u ?p)
      with (P a0 (fst u) p * struct_pred (a1 :: m) P (snd u) p).
inv IH.
specialize (IHm _ H4).
destruct u1 as [v1 u1], u2 as [v2 u2].
destruct H2 as [H2v H2], H3 as [H3v H3].
specialize (IHm u1 u2 H2 H3).
clear H2 H3.
unfold snd. unfold fst.
sep_apply IHm.
set (z1 := struct_pred _ _ _ _).
set (z2 := struct_pred _ _ _ _).
clearbody z1. clearbody z2.
unfold field_atx.
rewrite !withspacer_spacer.
rewrite !spacer_memory_block by (simpl; auto).
set (x1 := memory_block sh1 _ _).
set (x2 := memory_block sh2 _ _).
clearbody x1 x2.
unfold at_offset, offset_val.
set (ofs' := Ptrofs.add _ _). clearbody ofs'. 
specialize (H1 v1 v2 ofs').
sep_apply H1.
clear - H3v.
apply value_defined_not_volatile in H3v.
auto.
Intros. subst. apply prop_right; auto.
-
Admitted.


Lemma data_at_float_value_eq' {cs: compspecs}:
  forall sh1 sh2 v1 v2 p,
   readable_share sh1 ->
   readable_share sh2 ->
   data_at sh1 tdouble (Vfloat v1) p *
   data_at sh2 tdouble (Vfloat v2) p 
  |-- !! (v1=v2).
Proof.
intros.
unfold data_at, field_at.
Intros.
unfold at_offset.
simpl.
destruct H1 as [? _]; destruct p; try contradiction; simpl offset_val.
set (ofs := (Ptrofs.add _ _)). clearbody ofs.
sep_apply data_at_rec_share_join_values_cohere'.
Intros.
inv H2. apply prop_right; auto.
Qed.

Lemma data_at_array_float_value_eq' {cs: compspecs}:
  forall sh1 sh2 n v1 v2 p,
   readable_share sh1 ->
   readable_share sh2 ->
   data_at sh1 (tarray tdouble n) (map Vfloat v1) p *
   data_at sh2 (tarray tdouble n) (map Vfloat v2) p 
  |-- !! (v1=v2).
Proof.
intros.
saturate_local.
unfold data_at, field_at.
Intros.
unfold at_offset.
simpl.
destruct H1 as [? _]; destruct p; try contradiction; simpl offset_val.
set (ofs := (Ptrofs.add _ _)). clearbody ofs.
sep_apply data_at_rec_share_join_values_cohere'.
-
rewrite value_defined_eq; simpl; repeat change (unfold_reptype ?v) with v.
split.
list_solve.
clear; induction v1; constructor; hnf; auto.
-
rewrite value_defined_eq; simpl; repeat change (unfold_reptype ?v) with v.
split.
list_solve.
clear; induction v2; constructor; hnf; auto.
-
Intros.
apply prop_right.
clear - H7.
revert v2 H7; induction v1; destruct v2; simpl; intros; try congruence.
inv H7.
f_equal; auto.
Qed.



Lemma field_at_share_join_values_cohere {cs:compspecs} sh1 sh2 t gfs
    v1 v2 (R:type_is_by_value (nested_field_type t gfs)  = true) p:
    type_is_volatile (nested_field_type t gfs) = false ->
    readable_share sh1 -> readable_share sh2 ->
    ~ (JMeq v1 Vundef) -> ~ (JMeq v2 Vundef) ->
   (field_at sh1 t gfs v1 p * field_at sh2 t gfs v2 p) |-- !!(v1=v2).
Proof. intros. unfold field_at, at_offset; Intros.
  destruct H4 as [? _]. destruct p; try contradiction.
  unfold offset_val.
  apply (data_at_rec_share_join_values_cohere sh1 sh2); trivial.
Qed.

Lemma data_at_share_join_values_cohere {cs:compspecs} sh1 sh2 t
    v1 v2 (R:type_is_by_value (nested_field_type t nil)  = true) p:
    type_is_volatile (nested_field_type t nil) = false ->
    readable_share sh1 -> readable_share sh2 ->
    ~ (JMeq v1 Vundef) -> ~ (JMeq v2 Vundef) ->
   (data_at sh1 t v1 p * data_at sh2 t v2 p) |-- !!(v1=v2).
Proof. intros. apply field_at_share_join_values_cohere; assumption. Qed.

Lemma data_at_int_value_eq {cs: compspecs}:
  forall sh1 sh2 v1 v2 p,
   readable_share sh1 ->
   readable_share sh2 ->
   data_at sh1 tuint (Vint v1) p *
   data_at sh2 tuint (Vint v2) p 
  |-- !! (v1=v2).
Proof.
intros.
eapply derives_trans; [apply data_at_share_join_values_cohere | ]; auto.
intro. apply JMeq_eq in H1. discriminate.
intro. apply JMeq_eq in H1. discriminate.
apply prop_derives. congruence.
Qed.

Lemma data_at_float_value_eq {cs: compspecs}:
  forall sh1 sh2 v1 v2 p,
   readable_share sh1 ->
   readable_share sh2 ->
   data_at sh1 tdouble (Vfloat v1) p *
   data_at sh2 tdouble (Vfloat v2) p 
  |-- !! (v1=v2).
Proof.
intros.
eapply derives_trans; [apply data_at_share_join_values_cohere | ]; auto.
intro. apply JMeq_eq in H1. discriminate.
intro. apply JMeq_eq in H1. discriminate.
apply prop_derives. congruence.
Qed.

Lemma data_at_array_float_value_eq {cs: compspecs}:
  forall sh1 sh2 n v1 v2 p,
   readable_share sh1 ->
   readable_share sh2 ->
   data_at sh1 (tarray tdouble n) (map Vfloat v1) p *
   data_at sh2 (tarray tdouble n) (map Vfloat v2) p 
  |-- !! (v1=v2).
Proof.
intros.
revert v2 n p; induction v1; destruct v2; simpl; intros.
apply prop_right; auto.
entailer!. list_simplify.
entailer!. list_simplify.
assert_PROP (Zlength v1=n-1 /\ Zlength v2=n-1). {
  entailer!. list_solve.
}
change (Vfloat ?a :: ?b) with ([Vfloat a]++b).
rewrite !(split2_data_at_Tarray_app 1) by (try reflexivity; list_solve).
sep_apply (IHv1 v2 (n-1) (field_address0 (tarray tdouble n) (SUB 1) p)).
sep_apply (data_at_singleton_array_inv sh1 tdouble [Vfloat a] (Vfloat a) p (eq_refl _)).
sep_apply (data_at_singleton_array_inv sh2 tdouble [Vfloat f] (Vfloat f) p (eq_refl _)).
sep_apply (data_at_float_value_eq sh1 sh2 a f p).
Intros. subst. apply prop_right; auto.
Qed.

Lemma divu64_repr: (* move to floyd *)
 forall i j,
  0 <= i <= Int64.max_unsigned ->
  0 <= j <= Int64.max_unsigned ->
  Int64.divu (Int64.repr i) (Int64.repr j) = Int64.repr (i / j).
Proof.
intros.
unfold Int64.divu.
rewrite !Int64.unsigned_repr by rep_lia.
auto.
Qed.

Definition iota (n: Z) : list Z := map Z.of_nat (seq 0%nat (Z.to_nat n)).

Lemma Zlength_iota: forall t, 0 <= t -> Zlength (iota t) = t.
Proof.
intros. unfold iota. rewrite Zlength_map. 
rewrite Zlength_length; auto. rewrite seq_length; auto.
Qed.

#[export] Hint Rewrite Zlength_iota using lia : Zlength.

Lemma iota_S: forall n, 0 <= n -> iota (n+1) = iota n ++ [n].
Proof.
intros.
rewrite <- (Z2Nat.id n) by lia. clear.
forget (Z.to_nat n) as i.
unfold iota.
rewrite Nat2Z.id.
replace (Z.to_nat (Z.of_nat i + 1)) with (S i) by lia.
rewrite seq_S.
rewrite map_app. auto.
Qed.

Lemma Znth_iota:
 forall i n, 0 <= i < n -> Znth i (iota n) = i.
Proof.
intros.
pose proof (Zlength_iota n ltac:(lia)).
unfold iota in *.
rewrite Zlength_map in H0.
rewrite <- (Z2Nat.id n) in H0|-* by lia.
rewrite <- (Z2Nat.id i) by lia.
assert (Z.to_nat i < Z.to_nat n)%nat by lia.
forget (Z.to_nat i) as j.
forget (Z.to_nat n) as m.
unfold iota in *.
rewrite Nat2Z.id  in *.
rewrite Znth_map by lia.
rewrite <- nth_Znth by lia.
rewrite seq_nth by lia.
lia.
Qed.

Lemma in_iota:
   forall n x, In x (iota n) <-> 0 <= x < n.
 Proof. intros.
 destruct (zlt n 0).
 split; try lia. unfold iota. 
 replace (Z.to_nat n) with 0%nat by lia. simpl. tauto.
  rewrite <- (Z2Nat.id n) by lia.
  induction (Z.to_nat n).
  simpl. split; try lia.
  rewrite inj_S. unfold Z.succ. rewrite iota_S by lia.
  rewrite in_app.
  split; intro.
  destruct H.
  rewrite IHn0 in H. lia.
  hnf in H. destruct H; try contradiction.
  lia.
  destruct (zeq x (Z.of_nat n0)).
  subst. right; hnf; auto.
  left. rewrite IHn0. lia.
Qed.

Lemma NoDup_iota:
 forall n, NoDup (iota n).
Proof.
intros.
 destruct (zlt n 0).
 unfold iota.  
 replace (Z.to_nat n) with 0%nat by lia. simpl. constructor.
  rewrite <- (Z2Nat.id n) by lia. clear g.
  induction (Z.to_nat n).
  simpl. constructor.
  rewrite inj_S. unfold Z.succ. rewrite iota_S by lia.
 rewrite NoDup_app_iff.
 split; auto.
 split. constructor. intro Hx; inv Hx. constructor.
 intros.
 intro. destruct H0.
 subst x.
 apply in_iota in H. lia. inv H0.
Qed.

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
apply split_join in H. simpl. apply sepalg.join_comm; auto.
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


