Require Import vcfloat.VCFloat.
Require Import List.
Require Import seqdotprod_model.

Require Import Reals.
Open Scope R.

Definition fma_no_overflow (t: type) (x y z: R) : Prop :=
  (Rabs ( Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE)  (x * y + z)) < Raux.bpow Zaux.radix2 (femax t))%R.


Section NAN.
Variable NAN: Nans.

Definition default_rel (t: FPCore.type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (- fprec t + 1).

Definition default_abs (t: FPCore.type) : R :=
  / 2 * Raux.bpow Zaux.radix2 (3 - femax t - fprec t).

Lemma generic_round_property:
  forall (t: type) (x: R),
exists delta epsilon : R,
  (Rabs delta <= default_rel t)%R /\
  (Rabs epsilon <= default_abs t)%R /\
   Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
               x = (x * (1+delta)+epsilon)%R.
Proof.
intros.
destruct (Relative.error_N_FLT Zaux.radix2 (SpecFloat.emin (fprec t) (femax t)) (fprec t) 
             (fprec_gt_0 t) (fun x0 : Z => negb (Z.even x0)) x)
  as [delta [epsilon [? [? [? ?]]]]].
exists delta, epsilon.
split; [ | split]; auto.
Qed.

Lemma fma_accurate: 
   forall (t: type) 
             x (FINx: Binary.is_finite (fprec t) (femax t) x = true) 
             y (FINy: Binary.is_finite (fprec t) (femax t) y = true) 
             z (FINz: Binary.is_finite (fprec t) (femax t) z = true)
          (FIN: fma_no_overflow t (FT2R x) (FT2R y) (FT2R z)), 
  exists delta, exists epsilon,
   Rabs delta <= default_rel t /\
   Rabs epsilon <= default_abs t /\ 
   (FT2R (BFMA x y z) = (FT2R x * FT2R y + FT2R z) * (1+delta) + epsilon)%R.
Proof.
intros.
pose proof (Binary.Bfma_correct  (fprec t) (femax t)  (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t)
                      BinarySingleNaN.mode_NE x y z FINx FINy FINz).
change (Binary.B2R (fprec t) (femax t) ?x) with (@FT2R t x) in *.
cbv zeta in H.
pose proof (
   Raux.Rlt_bool_spec
        (Rabs
           (Generic_fmt.round Zaux.radix2
              (SpecFloat.fexp (fprec t) (femax t))
              (BinarySingleNaN.round_mode
                 BinarySingleNaN.mode_NE) (FT2R x * FT2R y + FT2R z)))
        (Raux.bpow Zaux.radix2 (femax t))).
destruct H0.
-
destruct H as [? _].
fold (@BFMA NAN t) in H.
rewrite H.
apply generic_round_property.
-
red in FIN.
Lra.lra.
Qed.

Definition femin (t: type) : Z := SpecFloat.emin (fprec t) (femax t).
Definition at_least_twice_precision (x y : type) : Prop :=
  (    2 * fprec x <= fprec y /\  femin y <= 2 * femin x)%Z.

Lemma at_least_twice_single_double: at_least_twice_precision Tsingle Tdouble.
Proof.
compute; split; intro; discriminate.
Qed.

Definition Tquadruple : type := {| fprecp := 113; femax := 16383;
             fprec_lt_femax_bool := I; fprecp_not_one_bool := I |}.


Lemma at_least_twice_double_quadruple: at_least_twice_precision Tdouble Tquadruple.
Proof.
compute; split; intro; discriminate.
Qed.

Lemma fma_equiv:
 forall (t t': type)
        (ATLEAST:  at_least_twice_precision t t')
         (x y z: ftype t),
      BFMA x y z =
       cast t (BPLUS t' (BMULT t' (cast t' x) (cast t' y)) (cast t' z)).
Proof.
(* This is likely true, but will be a pain to prove.
 The double-rounding theorems such as Flocq.Prop.Double_rounding.round_round_mult_FLT 
 are stated in terms of injection into the real numbers, not directly
 on concrete Binary.binary_float numbers.  Although there is an
 injection theorem, Binary.B2R_inj, this covers only the strict finite case,
 so there are many other cases that would have to be taken care of.
*)
Abort.

Definition sum: list R -> R := fold_right Rplus 0%R.

Import Lra.

Lemma fold_left_Rplus_Rplus:
 forall al b c, fold_left Rplus al (b+c) = c + fold_left Rplus al b.
Proof.
intros.
rewrite ! fold_symmetric by (intros; lra).
induction al; simpl; intros; lra.
Qed.

Lemma fold_left_Rplus_0:
 forall al b , fold_left Rplus al b = b + fold_left Rplus al 0.
Proof.
intros.
rewrite ! fold_symmetric by (intros; lra).
induction al; simpl; intros; lra.
Qed.

Search Binary.Bfma.
Definition small (n: nat) : R. Admitted.

Lemma small_nonneg: forall n, 0 <= small n. Admitted.

Local Definition FR2 {t: type} (x12: ftype t * ftype t) := (FT2R (fst x12), FT2R (snd x12)).

Local Definition sumabs (w: list (ftype Tdouble * ftype Tdouble)) :=
 fold_right Rplus 0 (map Rabs (map (uncurry Rmult) (map FR2 w))).

Record Fplus_properties (A: Type) (t: type) 
   (A2R: A -> R)
   (Fplus: A -> ftype t -> ftype t) := 
  { Fplus_accuracy: forall x y,
           Binary.is_finite (fprec t) (femax t) (Fplus x y) = true ->
           exists delta, exists epsilon, 
                Rabs delta <= default_rel t /\ Rabs epsilon <= default_abs t /\ 
                 FT2R (Fplus x y) = Rplus (A2R x) (FT2R y) * (1+delta)+epsilon
  }.

Definition Fplus_low_order_error (t: type) (v: list R) : R.  Admitted.

Lemma summation_error:
  forall (A: Type) (t: type) (A2R: A->R) (Fplus: A -> ftype t -> ftype t)
    (P: Fplus_properties _ _ A2R Fplus),
   let D := default_rel t in 
   let E := default_abs t in 
  forall v: list A,
    Binary.is_finite (fprec t) (femax t) (fold_right Fplus (Zconst t 0) v) = true ->
    Rabs (FT2R (fold_right Fplus (Zconst t 0) v) - fold_right Rplus 0 (map A2R v)) <= 
               (INR (List.length v) - 1) * D * fold_right Rplus 0 (map Rabs (map A2R v)) 
                      + Fplus_low_order_error t (map A2R v).
Admitted.

Lemma dotprod_error: 
  forall (t: type) (n: nat) (v1 v2: list (ftype t)), 
    length v1 = n ->
    length v2 = n ->
   let prods := map (uncurry Rmult) (List.combine (map FT2R v1)  (map FT2R v2)) in
     Rabs (FT2R (dotprod t v1 v2) - sum prods)
        <= (INR n-1) * default_rel t *  sum (map Rabs prods)
                 + Fplus_low_order_error t (rev prods).
Proof.
intros.
subst prods.
unfold dotprod, sum.
rewrite <- ! fold_symmetric by (intros; lra).
change 0%R with (@FT2R t (Zconst t 0)).
replace (combine (map FT2R v1) (map FT2R v2)) with (map FR2 (combine v1 v2))
 by (clear; revert v2; induction v1; destruct v2; simpl; auto; f_equal; auto).
assert (Datatypes.length (combine v1 v2) = n) by (rewrite combine_length; lia).
set (v12 := combine v1 v2) in *. clearbody v12.
clear v1 v2 H H0.
rewrite <- fold_left_rev_right.
rewrite <- fold_left_rev_right.
rewrite <- fold_left_rev_right.
rewrite <- !map_rev.
rewrite <- rev_length in H1.
set (v := rev v12) in *. clearbody v. clear v12.
replace (fun y x => x + y) with Rplus
 by (do 2 (apply FunctionalExtensionality.functional_extensionality; intro); lra).
change (FT2R (Zconst t 0)) with 0 in *.
assert (Fplus_properties (ftype t * ftype t) t
             (fun xy => Rmult (FT2R (fst xy)) (FT2R (snd xy)))
             (fun (y : ftype t * ftype t) (x : ftype t) =>
             BFMA  (fst y) (snd y) x) ). {
 apply (Build_Fplus_properties  (ftype t * ftype t) t).
 intros.
 rename y into s.
 destruct x as [x y].
 unfold fst, snd in *.
 assert (Binary.is_finite (fprec t) (femax t) x = true /\ 
           Binary.is_finite (fprec t) (femax t) y  = true /\
           Binary.is_finite (fprec t) (femax t) s = true). {
    destruct x, y, s; try discriminate; simpl; auto;
   simpl in H; unfold BFMA, Binary.Bfma in H; simpl in H.
   destruct (eqb (xorb s0 s1) s); simpl in H; discriminate.
   destruct (eqb (xorb s0 s1) s); simpl in H; discriminate.
   destruct (eqb (xorb s0 s1) s); simpl in H; discriminate.
 }
 destruct H0 as [? [? ?]].
 apply fma_accurate; auto.
 admit.
 }
 pose proof summation_error (ftype t * ftype t) t _ _ H v.
 set (D := default_rel t) in *.
 set (E := default_abs t) in *.
 replace (map
               (fun xy : (ftype t) * (ftype t) =>
                (FT2R (fst xy)) * (FT2R (snd xy))) v)
      with (map (uncurry Rmult) (map FR2 v)) in H0
     by (apply map_map).
  rewrite H1 in H0.
 apply H0.
admit.
all: fail.
Admitted.

End NAN.

