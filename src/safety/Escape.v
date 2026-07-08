Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import TypingInv.
Require Import Markers.
Require Import Progress.
Require Import Variance.
Require Import Inversions.
Require Import Soundness.

(* ================================================================== *)
(*                                                                    *)
(*                NON-ESCAPING OF LOCAL VALUES                        *)
(*                                                                    *)
(* The lifetime lattice places `lt_free` at the bottom and            *)
(* `lt_local` at the top, with subtyping oriented `free <: local`.    *)
(* A value annotated `local` is confined to its scope: it may be      *)
(* *used where* a `local` value is expected, but it must never flow   *)
(* the other way, into a position demanding a `free` (escapable)      *)
(* lifetime.                                                          *)
(*                                                                    *)
(* The formal content of "local values do not escape" is therefore    *)
(* that subtyping can never relax a `local` lifetime down to `free`:  *)
(* the lattice fact `local <: free` is underivable in *every*         *)
(* context, and consequently a `local`-annotated datum can never be   *)
(* coerced (by subsumption) to its `free` counterpart.                *)
(* ================================================================== *)

(* Value/type form: a `local`-annotated data value can never be       *)
(* subsumed to the same data carrying `free`.  This is the            *)
(* "no escape via subtyping" theorem for local values.                *)
Theorem local_data_not_escapes : forall Γ K Ts,
  eval_ctx Γ ->
  ctx_lookup_eff Γ K = None ->
  K <> any_tag ->
  ~ (Γ ⊢ type_ctor K lt_local Ts <:: type_ctor K lt_free Ts).
Proof.
  intros Γ K Ts Hec Hdata HK H.
  destruct (sub_ctor_inv _ _ _ _ _ Hec H HK) as [l' [Heq Hlsub]].
  injection Heq as Hl'. subst l'.
  exact (lt_local_not_escapes _ Hec Hlsub).
Qed.

(* ================================================================== *)
(*                                                                    *)
(*           OPERATIONAL NON-ESCAPE OF LOCAL VALUES                   *)
(*                                                                    *)
(* The lattice/subtyping theorems above forbid *coercing* a `local`   *)
(* datum to `free`.  Transported along the dynamics they deliver the  *)
(* operational guarantee: whatever value a closed program computes    *)
(* at an escapable (`free`) data type is itself annotated with a      *)
(* lifetime that carries no top-level `local`.  A `local`-confined    *)
(* datum can never surface as the result delivered at a `free` type.  *)
(* ================================================================== *)

(* Operational non-escape: a value produced at an escapable `free`    *)
(* data type is a constructor whose *own* lifetime annotation         *)
(* provably contains no top-level `local`.  Equivalently, a value     *)
(* confined to a `local` lifetime is never the result a program       *)
(* hands back at a `free` (escapable) type.                           *)
Theorem local_value_does_not_escape : forall Γ t K Ts v,
  eval_ctx Γ ->
  ctx_lookup_eff Γ K = None ->
  K <> any_tag ->
  (forall u, multi_step t u -> Γ ⊢ₜ u : type_ctor K lt_free Ts) ->
  multi_step t v ->
  value v ->
  exists K' l' lts' vs,
    v = term_ctor K' l' lts' Ts vs /\
    no_local_lt l' = true.
Proof.
  intros Γ t K Ts v Hec Hdata HK Hty_reachable Hms Hval.
  pose proof (Hty_reachable _ Hms) as Htyv.
  destruct (canonical_ctor_data _ _ _ _ _ Hec Hdata Htyv Hval HK)
    as [K' [l' [lts' [Ts' [vs [Hveq Hvs]]]]]].
  subst v.
  apply ctor_typing_inv in Htyv.
  destruct Htyv as
    (n_lt & n_ty & sig & res & result_tag & Hlk & Hltlen & HTslen & Hresult &
     Hlts_bound & Hvslen & Hf2 & Hsub).
  destruct (sub_ctor_inv _ _ _ _ _ Hec Hsub HK) as [lx [Heq Hlsub]].
  injection Heq as HKeq Hleq HTseq.
  subst result_tag. subst Ts'.
  exists K', l', lts', vs. split; [reflexivity|].
  rewrite Hleq.
  apply (lt_sub_no_local_mono _ _ _ Hec Hlsub).
  reflexivity.
Qed.

(* Source-facing form: for a program with no runtime marker constructs *)
(* the typing-along-the-trace premise is discharged by the             *)
(* step-preserved runtime invariants (subject reduction), so the       *)
(* guarantee needs only the initial typing.                            *)
Corollary source_local_value_does_not_escape : forall Γ t K Ts v,
  eval_ctx Γ ->
  ctx_lookup_eff Γ K = None ->
  K <> any_tag ->
  has_rt_cap t = false ->
  Γ ⊢ₜ t : type_ctor K lt_free Ts ->
  multi_step t v ->
  value v ->
  exists K' l' lts' vs,
    v = term_ctor K' l' lts' Ts vs /\
    no_local_lt l' = true.
Proof.
  intros Γ t K Ts v Hec Hdata HK Hsrc Hty Hms Hval.
  eapply local_value_does_not_escape;
    [exact Hec | exact Hdata | exact HK | | exact Hms | exact Hval].
  intros u Hms'.
  destruct (multi_step_preserves_safety_invariants _ _ _ _ Hec
              (source_safety_invariants _ _ _ Hsrc Hty) Hms')
    as [_ [_ Htyu]].
  exact Htyu.
Qed.

(* ================================================================== *)
(*                                                                    *)
(*                   CAPABILITY CONFINEMENT                           *)
(*                                                                    *)
(* A runtime capability `cap_E^m _ _` is the only construct whose     *)
(* typing rule (`T_Cap`) consults the effect environment: it is       *)
(* well-typed solely in a context that *binds* the effect tag `E`.    *)
(* Capabilities are minted by `S_Handle`, which wraps each one        *)
(* immediately inside its own `handler_m m` delimiter.  Under the     *)
(* full effectful calculus, typing alone no longer rules out visible  *)
(* capabilities; the runtime `marker_ok` invariant does.              *)
(* ================================================================== *)

Lemma well_scoped_plug_cap_pure_in : forall ms E E_tag m n_beta Ts T_R op_body,
  pure_ectx_m m E ->
  well_scoped ms (plug E (term_cap E_tag m n_beta Ts T_R op_body)) ->
  In m ms.
Proof.
  intros ms E E_tag m n_beta Ts T_R op_body Hpure.
  revert ms. induction Hpure; simpl; intros ms Hmok.
  - exact (proj1 Hmok).
  - apply IHHpure. exact (proj1 Hmok).
  - apply IHHpure. exact (proj2 Hmok).
  - apply IHHpure. exact Hmok.
  - apply IHHpure. exact Hmok.
  - apply IHHpure.
    induction vs as [|u vs IHvs]; simpl in Hmok; [tauto|].
    apply IHvs. tauto.
  - apply IHHpure. exact (proj1 Hmok).
  - apply (IHHpure (m' :: ms)) in Hmok.
    destruct Hmok as [Heq | Hin]; [subst; contradiction|exact Hin].
  - apply IHHpure. exact (proj1 Hmok).
  - apply IHHpure. exact (proj2 Hmok).
  all: tauto.
Qed.

Theorem capability_confined : forall E E_tag m n_beta Ts T_R op_body,
  well_scoped [] (plug E (term_cap E_tag m n_beta Ts T_R op_body)) ->
  ~ pure_ectx_m m E.
Proof.
  intros E E_tag m n_beta Ts T_R op_body Hmok Hpure.
  pose proof (well_scoped_plug_cap_pure_in [] E E_tag m n_beta Ts T_R op_body Hpure Hmok) as Hin.
  inversion Hin.
Qed.

Theorem capability_never_exposed : forall Γ t E E_tag m n_beta Ts T_R op_body T,
  eval_ctx Γ ->
  (forall u, multi_step t u -> well_scoped [] u) ->
  Γ ⊢ₜ t : T ->
  multi_step t (plug E (term_cap E_tag m n_beta Ts T_R op_body)) ->
  ~ pure_ectx_m m E.
Proof.
  intros Γ t E E_tag m n_beta Ts T_R op_body T Hec Hmok_reachable Hty Hms Hpure.
  pose proof (Hmok_reachable _ Hms) as Hmok'.
  eapply capability_confined; eauto.
Qed.


(* Source-facing form: for a program with no runtime marker constructs *)
(* the marker_ok trace premise is discharged by the step-preserved     *)
(* runtime invariants, so confinement needs only the initial typing.   *)
Corollary source_capability_never_exposed :
  forall Γ t E E_tag m n_beta Ts T_R op_body T,
  eval_ctx Γ ->
  has_rt_cap t = false ->
  Γ ⊢ₜ t : T ->
  multi_step t (plug E (term_cap E_tag m n_beta Ts T_R op_body)) ->
  ~ pure_ectx_m m E.
Proof.
  intros Γ t E E_tag m n_beta Ts T_R op_body T Hec Hsrc Hty Hms.
  eapply capability_never_exposed; [exact Hec | | exact Hty | exact Hms].
  intros u Hms'.
  destruct (multi_step_preserves_safety_invariants _ _ _ _ Hec
              (source_safety_invariants _ _ _ Hsrc Hty) Hms')
    as [_ [[Hws _] _]].
  exact Hws.
Qed.
