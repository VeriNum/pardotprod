Require Import VST.floyd.proofauto.
Require Import seqdotprod.
Require Import vcfloat.FPCompCert.
Require Import VSTlib.spec_math.
Require Import seqdotprod_model.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

Definition seqdotprod_spec :=
 DECLARE _seqdotprod
 WITH sh: share, p1: val, v1: list (ftype Tdouble), p2: val, v2: list (ftype Tdouble)
 PRE [ tptr tdouble, tptr tdouble, tuint ]
    PROP(readable_share sh; Zlength v1 <= Int.max_unsigned; 
             Zlength v1 = Zlength v2)
    PARAMS(p1; p2; Vint (Int.repr (Zlength v1)))
    SEP (data_at sh (tarray tdouble (Zlength v1)) (map Vfloat v1) p1; 
          data_at sh (tarray tdouble (Zlength v2)) (map Vfloat v2) p2)
 POST [ tdouble ]
    PROP() RETURN(Vfloat (dotprod Tdouble v1 v2))
    SEP (data_at sh (tarray tdouble (Zlength v1)) (map Vfloat v1) p1; 
          data_at sh (tarray tdouble (Zlength v2)) (map Vfloat v2) p2).

Definition SeqdotprodASI : funspecs := [ seqdotprod_spec ].

Definition Gprog: funspecs := SeqdotprodASI ++ MathASI.

Lemma body_seqdotprod: semax_body Vprog Gprog f_seqdotprod seqdotprod_spec.
Proof.
start_function.
subst MORE_COMMANDS; unfold abbreviate; canonicalize_float_constants.
forward.
forward_for_simple_bound (Zlength v1)
  (EX i:Z, PROP() 
       LOCAL(temp _result (Vfloat (dotprod Tdouble (sublist 0 i v1) (sublist 0 i v2)));
                  temp _vec1 p1; temp _vec2 p2; temp _n (Vint (Int.repr (Zlength v1))))
       SEP (data_at sh (tarray tdouble (Zlength v1)) (map Vfloat v1) p1; 
             data_at sh (tarray tdouble (Zlength v2)) (map Vfloat v2) p2))%assert.
- entailer!.
- forward. forward.
   forward_call (Znth i v1, Znth i v2, dotprod Tdouble (sublist 0 i v1) (sublist 0 i v2)).
   entailer!.
   forward.
   entailer!.
   f_equal.
   rewrite !(sublist_split 0 i (i+1)) by list_solve.
   unfold dotprod.
   rewrite combine_app' by list_solve.
   forget (combine (sublist 0 i v1) (sublist 0 i v2)) as a.
   rewrite !sublist_len_1 by list_solve.
   simpl combine.
   rewrite fold_left_app.
   reflexivity.
-
  forward.
  rewrite !sublist_same by list_solve.
  entailer!.
Qed.
