(* ================================================================== *)
(* Stale witness for the former `subst_ty_in_tm_lemma` refutation.     *)
(*                                                                    *)
(* The old counterexample relied on a T_Lam premise requiring the      *)
(* lambda result type to satisfy `no_local_ty`.  The current calculus  *)
(* no longer has that premise, so substituting a local function type   *)
(* into this witness is typeable rather than contradictory.           *)
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
Definition Tf : type := type_ctor K0 lt_free [].
Definition Sloc : type := type_fun Tf lt_local Tf.
Definition Bnd : type := type_ctor any_tag lt_local [].

Definition tbody : term := term_var 0.
Definition tlam : term := term_lam tbody (type_var 0).
Definition Tlam : type := type_fun (type_var 0) lt_free (type_var 0).

Lemma Bnd_wf_ty : ty_wf [bind_ty Bnd] Bnd.
Proof. unfold Bnd. repeat constructor. Qed.

Lemma type_var0_wf : ty_wf [bind_ty Bnd] (type_var 0).
Proof.
  econstructor.
  - reflexivity.
  - exact Bnd_wf_ty.
Qed.

Lemma Bnd_wf_body : ty_wf [bind_tm (type_var 0); bind_ty Bnd] Bnd.
Proof. unfold Bnd. repeat constructor. Qed.

Lemma type_var0_wf_body : ty_wf [bind_tm (type_var 0); bind_ty Bnd] (type_var 0).
Proof.
  econstructor.
  - reflexivity.
  - exact Bnd_wf_body.
Qed.

Lemma t_typed : [bind_ty Bnd] ⊢ₜ tlam : Tlam.
Proof.
  unfold tlam, tbody, Tlam.
  apply T_Lam.
  - exact type_var0_wf.
  - exact type_var0_wf.
  - apply T_Var.
    + reflexivity.
    + exact type_var0_wf_body.
  - cbn. apply LS_Free. constructor.
Qed.

Lemma s_sub_b : [] ⊢ Sloc <:: Bnd.
Proof.
  unfold Sloc, Bnd. apply SA_Any.
  - unfold Tf. repeat constructor.
  - constructor.
  - cbn. apply LS_Refl. constructor.
Qed.

Lemma former_reduct_now_typed :
  [] ⊢ₜ subst_ty_in_tm 0 Sloc tlam : subst_ty 0 Sloc Tlam.
Proof.
  unfold tlam, tbody, Tlam.
  cbn [subst_ty_in_tm subst_ty Nat.eqb].
  apply T_Lam.
  - unfold Sloc, Tf. repeat constructor.
  - unfold Sloc, Tf. repeat constructor.
  - apply T_Var.
    + reflexivity.
    + unfold Sloc, Tf. repeat constructor.
  - cbn. apply LS_Free. constructor.
Qed.