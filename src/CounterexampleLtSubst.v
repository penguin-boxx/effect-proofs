(* ================================================================== *)
(* Stale witness for the former `subst_lt_in_tm_lemma` refutation.     *)
(*                                                                    *)
(* The old counterexample relied on a T_Lam premise requiring the      *)
(* lambda result type to satisfy `no_local_ty`.  The current calculus  *)
(* no longer has that premise, so substituting `lt_local` into this    *)
(* witness is typeable rather than contradictory.                     *)
(* ================================================================== *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import SubstitutionTheory.
Require Import Safety.

Definition K0 : ctor_tag := 1.
Definition A2 : type := type_ctor K0 lt_free [].
Definition Ain : type := type_fun A2 (lt_var 0) A2.
Definition inner : term := term_lam (term_var 0) Ain.
Definition N : term := term_lt_lam inner.
Definition Tinner : type := type_fun Ain lt_free Ain.

Lemma Ain_wf : ty_wf [bind_lt lt_local] Ain.
Proof.
  unfold Ain, A2. constructor.
  - repeat constructor.
  - econstructor. reflexivity.
  - repeat constructor.
Qed.

Lemma Ain_wf_body : ty_wf [bind_tm Ain; bind_lt lt_local] Ain.
Proof.
  unfold Ain, A2. constructor.
  - repeat constructor.
  - econstructor. reflexivity.
  - repeat constructor.
Qed.

Lemma Tinner_wf : ty_wf [bind_lt lt_local] Tinner.
Proof.
  unfold Tinner. constructor; try exact Ain_wf; constructor.
Qed.

Lemma inner_typed : [bind_lt lt_local] ⊢ₜ inner : Tinner.
Proof.
  unfold inner, Tinner.
  apply T_Lam.
  - exact Ain_wf.
  - exact Ain_wf.
  - apply T_Var.
    + reflexivity.
    + exact Ain_wf_body.
  - cbn. apply LS_Free. constructor.
Qed.

Lemma source_typed :
  [] ⊢ₜ term_lt_app N lt_local : subst_lt_in_ty 0 lt_local Tinner.
Proof.
  eapply T_LtApp.
  - unfold N. apply T_LtLam.
    + exact Tinner_wf.
    + reflexivity.
    + apply inner_typed.
  - constructor.
Qed.

Lemma former_reduct_now_typed :
  [] ⊢ₜ subst_lt_in_tm 0 lt_local inner : subst_lt_in_ty 0 lt_local Tinner.
Proof.
  cbn [subst_lt_in_tm subst_lt_in_ty subst_lt Nat.eqb inner Ain A2 Tinner].
  apply T_Lam.
  - unfold A2. repeat constructor.
  - unfold A2. repeat constructor.
  - apply T_Var.
    + reflexivity.
    + unfold A2. repeat constructor.
  - cbn. apply LS_Free. constructor.
Qed.