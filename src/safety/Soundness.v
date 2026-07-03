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
(* progress (Progress) with preservation (Preservation) and the       *)
(* step-preservation of the runtime marker invariants (Markers /      *)
(* Preservation) to conclude that a well-typed, marker-safe term      *)
(* never reaches a stuck state.                                       *)
(* (Escape safety — local lifetimes / capabilities never escaping     *)
(* their scope — is the separate, independent deliverable in Escape.) *)
(* ================================================================== *)

Definition stuck (t : term) : Prop :=
  ~ value t /\ ~ exists t', t ==> t'.

(* The runtime invariant carried by the multi-step proof.  Beyond      *)
(* typing it bundles the marker invariants:                            *)
(*  - [marker_ok]: every live capability's marker is delimited;        *)
(*  - [marker_annots_closed]: marker type annotations are closed, so   *)
(*    type/lifetime substitution preserves annotation equality;        *)
(*  - [marker_types_safe]: annotations for the same marker agree;      *)
(*  - [well_scoped]: marker provenance — each cap's op-body is         *)
(*    well-scoped at the scope OUTSIDE its own delimiter (what the     *)
(*    H_Perform contraction needs);                                    *)
(*  - [rt_closed]: runtime cap op-bodies are term-closed (they are     *)
(*    minted at spine positions of a closed program and stay closed).  *)
(* Every component is established vacuously on source terms            *)
(* ([has_rt_cap t = false]); see [source_type_soundness].              *)
Definition safety_invariants (Γ : ctx) (T : type) (t : term) : Prop :=
  marker_ok [] t /\ marker_annots_closed t /\ marker_types_safe t /\
  well_scoped [] t /\ rt_closed t /\ Γ ⊢ₜ t : T.

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

(* Every component of [safety_invariants] is preserved by one step.    *)
Lemma step_preserves_safety_invariants : forall Γ t t' T,
  eval_ctx Γ ->
  safety_invariants Γ T t ->
  t ==> t' ->
  safety_invariants Γ T t'.
Proof.
  intros Γ t t' T Hec Hinv Hstep.
  destruct Hinv as [Hmok [Hclosed [Hmsafe [Hws [Hrt Hty]]]]].
  split; [eapply step_preserves_marker_ok;
            [exact Hec | exact Hmok | exact Hmsafe | exact Hty
            | exact Hws | exact Hstep] |].
  split; [eapply step_preserves_marker_annots_closed_typed;
            [exact Hec | exact Hclosed | exact Hty | exact Hstep] |].
  split; [eapply step_preserves_marker_types_safe_closed_typed;
            [exact Hec | exact Hclosed | exact Hmsafe | exact Hty | exact Hstep] |].
  split; [eapply step_preserves_well_scoped;
            [exact Hec | exact Hty | exact Hrt | exact Hws | exact Hstep] |].
  split; [eapply step_preserves_rt_closed;
            [exact Hec | exact Hty | exact Hrt | exact Hstep] |].
  eapply preservation; eauto.
Qed.

(* The runtime invariants persist along any reduction sequence.        *)
Lemma multi_step_preserves_safety_invariants : forall Γ t u T,
  eval_ctx Γ ->
  safety_invariants Γ T t ->
  multi_step t u ->
  safety_invariants Γ T u.
Proof.
  intros Γ t u T Hec Hinv Hms. revert Hinv.
  induction Hms as [w | w1 w2 w3 Hstep Hms IH]; intros Hinv.
  - exact Hinv.
  - apply IH. eapply step_preserves_safety_invariants; eauto.
Qed.

(* All runtime invariants hold vacuously on a source term (one with    *)
(* no runtime marker constructs).                                      *)
Lemma source_safety_invariants : forall Γ t T,
  has_rt_cap t = false ->
  Γ ⊢ₜ t : T ->
  safety_invariants Γ T t.
Proof.
  intros Γ t T Hsrc Hty.
  split; [apply marker_ok_no_rt_cap; exact Hsrc|].
  split; [apply marker_annots_closed_no_rt_cap; exact Hsrc|].
  split; [apply marker_types_safe_no_rt_cap; exact Hsrc|].
  split; [apply well_scoped_no_rt_cap; exact Hsrc|].
  split; [apply rt_closed_no_rt_cap; exact Hsrc|].
  exact Hty.
Qed.

(* ================================================================== *)
(*                      TYPE SOUNDNESS (capstone)                     *)
(*                                                                    *)
(* Progress + preservation: a state satisfying the runtime            *)
(* invariants never reaches a stuck state.  UNCONDITIONAL: every      *)
(* invariant is proved step-preserved (subject reduction for typing,  *)
(* and the marker invariants including [well_scoped] / [rt_closed]).  *)
(* ================================================================== *)

Theorem type_soundness :
  forall Γ t t' T,
    eval_ctx Γ ->
    safety_invariants Γ T t ->
    multi_step t t' ->
    ~ stuck t'.
Proof.
  intros Γ t t' T Hec Hinv Hms.
  destruct (multi_step_preserves_safety_invariants _ _ _ _ Hec Hinv Hms)
    as [Hmok [_ [Hmsafe [_ [_ Hty]]]]].
  eapply safe_state_not_stuck; eauto.
Qed.

(* Source-facing form: a well-typed program with no runtime marker     *)
(* constructs never gets stuck.  All runtime invariants hold           *)
(* vacuously at the initial state.                                     *)
Corollary source_type_soundness : forall Γ t t' T,
  eval_ctx Γ ->
  has_rt_cap t = false ->
  Γ ⊢ₜ t : T ->
  multi_step t t' ->
  ~ stuck t'.
Proof.
  intros Γ t t' T Hec Hsrc Hty Hms.
  eapply type_soundness;
    [exact Hec | apply source_safety_invariants; eassumption | exact Hms].
Qed.

(* End-to-end safety from a state satisfying the runtime invariant.    *)
Corollary type_safety_from_invariants : forall Γ t t' T,
  eval_ctx Γ ->
  safety_invariants Γ T t ->
  multi_step t t' ->
  ~ stuck t'.
Proof. exact type_soundness. Qed.
