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

(* This is the runtime invariant carried by the multi-step proof.  It is
   deliberately stronger than the old user-facing premise because it includes
   [marker_annots_closed], which is needed to make type/lifetime substitution
   preserve marker annotation equality.  Source terms recover the old shape:
   [has_rt_cap t = false] implies empty marker annotations, hence the closed
   component below is automatic; see [source_type_soundness]. *)
Definition safety_invariants (Γ : ctx) (T : type) (t : term) : Prop :=
  marker_ok [] t /\ marker_annots_closed t /\ marker_types_safe t /\ Γ ⊢ₜ t : T.

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
  destruct (Hsafe_reachable t' Hmulti) as [Hmok [_ [Hsafe Hty]]].
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

(* Type soundness for states carrying the explicit closed-annotation     *)
(* marker invariant.  Subject reduction (preservation) and the marker    *)
(* step-preservation facts are supplied internally from proved lemmas.   *)
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
    - apply IH. destruct Hinv as [Hmok [Hclosed [Hmsafe Hty]]].
      split; [eapply step_preserves_marker_ok;
                [exact Hec | exact Hmok | exact Hmsafe | exact Hty | exact Hstep] |].
      split; [eapply step_preserves_marker_annots_closed_typed;
                [exact Hec | exact Hclosed | exact Hty | exact Hstep] |].
      split; [eapply step_preserves_marker_types_safe_closed_typed;
                [exact Hec | exact Hclosed | exact Hmsafe | exact Hty | exact Hstep] |].
      eapply preservation; eauto. }
  destruct Hreach as [Hmok [_ [Hmsafe Hty]]].
  eapply safe_state_not_stuck; eauto.
Qed.

(* Source-facing form: programs with no runtime marker constructs do not need
   to mention the strengthened closed-annotation invariant explicitly. *)
Corollary source_type_soundness : forall Γ t t' T,
  eval_ctx Γ ->
  has_rt_cap t = false ->
  Γ ⊢ₜ t : T ->
  multi_step t t' ->
  ~ stuck t'.
Proof.
  intros Γ t t' T Hec Hsrc Hty Hms.
  eapply type_soundness; eauto.
  split.
  - apply marker_ok_no_rt_cap. exact Hsrc.
  - split.
    + apply marker_annots_closed_no_rt_cap. exact Hsrc.
    + split.
      * apply marker_types_safe_no_rt_cap. exact Hsrc.
      * exact Hty.
Qed.

(* End-to-end safety from a state satisfying the runtime invariant.    *)
Corollary type_safety_from_invariants : forall Γ t t' T,
  eval_ctx Γ ->
  safety_invariants Γ T t ->
  multi_step t t' ->
  ~ stuck t'.
Proof. exact type_soundness. Qed.
