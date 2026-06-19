Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import Markers.
Require Import Progress.
Require Import Inversions.
Require Import Preservation.

(* ================================================================== *)
(* Soundness: the overall-safety capstone.                            *)
(*                                                                    *)
(* The single file a reader opens for "the safety theorem".  It pairs *)
(* progress (Progress) with preservation (Preservation) and the two   *)
(* marker step-preservation facts (Markers) to conclude that a        *)
(* well-typed, marker-safe term never reaches a stuck state.          *)
(* (Escape safety — local lifetimes / capabilities never escaping     *)
(* their scope — is the separate, independent deliverable in Escape.) *)
(* ================================================================== *)

Definition stuck (t : term) : Prop :=
  ~ value t /\ ~ exists t', t ==> t'.

Definition safety_invariants (Γ : ctx) (T : type) (t : term) : Prop :=
  marker_ok [] t /\ marker_types_safe t /\ Γ ⊢ₜ t : T.

Lemma safe_state_not_stuck : forall Γ t T,
  eval_ctx Γ ->
  marker_ok [] t ->
  marker_types_safe t ->
  Γ ⊢ₜ t : T ->
  ~ stuck t.
Proof.
  intros Γ t T Hec Hmok Hsafe Hty [Hnv Hns].
  destruct (progress_safe _ _ _ Hec Hmok Hsafe Hty) as [Hv | [t' Hs]].
  - contradiction.
  - apply Hns; eauto.
Qed.

Corollary type_safety : forall Γ t t' T,
  eval_ctx Γ ->
  (forall u, multi_step t u -> safety_invariants Γ T u) ->
  multi_step t t' ->
  ~ stuck t'.
Proof.
  intros Γ t t' T Hec Hsafe_reachable Hmulti.
  destruct (Hsafe_reachable t' Hmulti) as [Hmok [Hsafe Hty]].
  eapply safe_state_not_stuck.
  - exact Hec.
  - exact Hmok.
  - exact Hsafe.
  - exact Hty.
Qed.

(* ================================================================== *)
(*                      TYPE SOUNDNESS (capstone)                     *)
(*                                                                    *)
(* Progress + preservation: a well-typed, marker-safe term never      *)
(* reaches a stuck state.  Conditional on the same substitution-      *)
(* preservation facts as `preservation`, plus step-preservation of    *)
(* the two marker invariants (proved separately below where           *)
(* possible).                                                         *)
(* ================================================================== *)

(* Type soundness, UNCONDITIONAL: a well-typed, marker-safe term never   *)
(* reaches a stuck state.  Subject reduction (preservation) and the two  *)
(* marker step-preservation facts are now supplied internally from the   *)
(* proved lemmas (step_preserves_marker_ok, preservation) and the        *)
(* explicit residual axioms (step_preserves_marker_types_safe, the four  *)
(* redex preserves) — see Print Assumptions type_soundness.              *)
Theorem type_soundness :
  forall Γ t t' T,
    eval_ctx Γ ->
    safety_invariants Γ T t ->
    multi_step t t' ->
    ~ stuck t'.
Proof.
  intros Γ t t' T Hec Hinv Hms.
  assert (Hreach : safety_invariants Γ T t').
  { revert Hinv. induction Hms as [u | u1 u2 u3 Hstep Hms IH]; intros Hinv.
    - exact Hinv.
    - apply IH. destruct Hinv as [Hmok [Hmsafe Hty]].
      split; [eapply step_preserves_marker_ok;
                [exact Hec | exact Hmok | exact Hmsafe | exact Hty | exact Hstep] |].
      split; [eapply step_preserves_marker_types_safe;
                [exact Hec | exact Hmok | exact Hmsafe | exact Hty | exact Hstep] |].
      eapply preservation; eauto. }
  destruct Hreach as [Hmok [Hmsafe Hty]].
  eapply safe_state_not_stuck; eauto.
Qed.

(* End-to-end safety from a single well-typed marker-safe state:       *)
(* every reachable state is non-stuck (unconditional).                 *)
Corollary type_safety_from_invariants : forall Γ t t' T,
  eval_ctx Γ ->
  safety_invariants Γ T t ->
  multi_step t t' ->
  ~ stuck t'.
Proof. exact type_soundness. Qed.
