Require Import VST.floyd.proofauto.
Require Import VST.msl.iter_sepcon.

Open Scope logic.

Lemma field_address0_SUB_SUB {cs: compspecs}:
 forall t n1 n2 i j p,
 n2 = j+n1 ->
 0 <= i <= n1 -> 0 <= j ->
 field_address0 (tarray t n1) (SUB i) (field_address0 (tarray t n2) (SUB j) p) =
 field_address0 (tarray t n2) (SUB (i+j)) p.
Proof.
intros * Hn2 Hn1 Hj.
subst n2.
unfold field_address0.
destruct (field_compatible0_dec (tarray t (j + n1)) (SUB (i + j)) p).
-
rewrite !if_true.
+ simpl. rewrite offset_offset_val. f_equal. lia.
+
eapply field_compatible0_array_smaller1; try eassumption; lia.
+
rewrite if_true by (eapply field_compatible0_array_smaller1; try eassumption; lia).
simpl.
destruct f as [? [? [? [? [? ?]]]]].
split3; auto. split3; [ | | split]; auto.
*
destruct p; try contradiction.
red in H1|-*.
unfold sizeof in *.
simpl Ctypes.sizeof in *.
rewrite Z.max_r in * by lia.
rewrite Z.mul_add_distr_l in H1.
pose proof (Ctypes.sizeof_pos t).
simpl.
rewrite <- (Ptrofs.repr_unsigned i0).
rewrite ptrofs_add_repr.
rewrite Ptrofs.unsigned_repr.
lia.
assert (Ctypes.sizeof t * n1 >= 0) by nia.
rep_lia.
*
destruct p; try contradiction.
simpl in H4.
red in H2|-*; simpl in H2|-*.
apply align_compatible_rec_Tarray. intros.
eapply align_compatible_rec_Tarray_inv with (i:=i1+j) in H2; try lia.
rewrite Z.mul_add_distr_l in H2.
rewrite <- (Ptrofs.repr_unsigned i0), ptrofs_add_repr.
rewrite Ptrofs.unsigned_repr.
unfold sizeof.
replace  (Ptrofs.unsigned i0 + (0 + Ctypes.sizeof t * j) + Ctypes.sizeof t * i1)
 with   (Ptrofs.unsigned i0 + (Ctypes.sizeof t * i1 + Ctypes.sizeof t * j))
  by lia; auto.
rewrite Z.add_0_l.
unfold sizeof.
pose proof (Ctypes.sizeof_pos t).
assert (0 <= Ctypes.sizeof t * j <= Ctypes.sizeof t * j + Ctypes.sizeof t * i1) by nia.
red in H1.
simpl in H1.
rewrite Z.max_r in H1 by lia.
rewrite Z.mul_add_distr_l in H1.
assert (Ctypes.sizeof t * i1 <= Ctypes.sizeof t * n1) by nia.
rep_lia.
-
if_tac; auto.
if_tac; auto.
contradiction n. clear n.
simpl in H.
auto with field_compatible.
Qed.

Lemma sepcon_pred_sepcon:
 forall {A B : Type} {ND: NatDed A} {SL: SepLog A}{CA: ClassicalSep A}
  (f1 f2: B -> A) (P: B -> Prop),
 pred_sepcon f1 P * pred_sepcon f2 P = pred_sepcon (fun i => f1 i * f2 i) P.
Proof.
intros.
rewrite !pred_sepcon_eq.
apply pred_ext.
-
Intros l1 l2.
normalize.
assert (Permutation l1 l2). {
apply NoDup_Permutation; auto.
intros. rewrite H,H1. tauto.
}
rewrite <- (iter_sepcon_permutation f2 H3).
Exists l1.
rewrite prop_true_andp by auto.
clear - CA SL ND.
induction l1. simpl. rewrite emp_sepcon; auto.
simpl. rewrite !sepcon_assoc. apply sepcon_derives.
auto. rewrite <- !sepcon_assoc. pull_left (f2 a).
rewrite !sepcon_assoc.
apply sepcon_derives; auto.
-
Intros l.
Exists l l.
rewrite !prop_true_andp by auto.
clear H H0.
induction l. simpl. rewrite emp_sepcon; auto.
simpl. rewrite !sepcon_assoc. apply sepcon_derives.
auto. rewrite <- !sepcon_assoc. pull_left (f2 a).
rewrite !sepcon_assoc.
apply sepcon_derives; auto.
Qed.

Lemma pred_sepcon_derives:
 forall {A B : Type} {ND: NatDed A} {SL: SepLog A}
  (f1 f2: B -> A) (P: B -> Prop),
 (forall i, P i -> (f1 i |-- f2 i)) ->
 (pred_sepcon f1 P |-- pred_sepcon f2 P).
Proof.
intros.
rewrite !pred_sepcon_eq.
Intros al.
Exists al.
rewrite prop_true_andp by auto.
apply iter_sepcon_derives.
intros.
apply H.
rewrite <- H0.
auto.
Qed.

Lemma distribute_pred_sepcon:
 forall {A B: Type} {NA: NatDed A} {SA: SepLog A}{CA: ClassicalSep A}
        (e: A) (f: B -> A) (P: B -> Prop),
   (e |-- emp) -> (e |-- e * e) -> 
   (e * pred_sepcon f P |-- pred_sepcon (fun i => e * f i) P).
Proof.
intros.
rewrite !pred_sepcon_eq.
Intros l; normalize; Exists l; rewrite prop_true_andp by auto;
clear H1 H2 P.
induction l; simpl. rewrite sepcon_emp; auto.
eapply derives_trans; [apply sepcon_derives; [apply H0 | apply derives_refl ] | ].
rewrite !sepcon_assoc.
apply sepcon_derives; auto.
rewrite <- sepcon_assoc.
pull_left (f a).
rewrite !sepcon_assoc.
apply sepcon_derives; auto.
Qed.

Lemma repr64_inj_unsigned: (* move to floyd *)
  forall i j,
    0 <= i <= Int64.max_unsigned ->
    0 <= j <= Int64.max_unsigned ->
    Int64.repr i = Int64.repr j -> i=j.
Proof.
intros.
rewrite <- (Int64.unsigned_repr i) by rep_lia.
rewrite <- (Int64.unsigned_repr j) by rep_lia.
congruence.
Qed.

Lemma value_defined_tarray {cs: compspecs}:
 forall t n vl,
  Zlength vl = n -> 
  Forall (value_defined t) vl ->
  value_defined (tarray t n) vl.
Proof.
intros.
red. rewrite type_induction.type_func_eq. unfold tarray.
split; auto.
subst.
unfold unfold_reptype. simpl. rep_lia.
Qed.

Lemma map_inj: forall {A}{B} (f: A -> B), 
   (forall u v, f u = f v -> u=v) ->
   forall x y, 
   map f x = map f y -> x = y.
Proof.
induction x; destruct y; simpl; intros; try discriminate; auto.
inv H0.
f_equal; auto.
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



