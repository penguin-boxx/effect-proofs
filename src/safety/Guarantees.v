Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import MarkerAnnots.
Require Import WellScoped.
Require Import WsRtLaws.
Require Import Progress.
Require Import Preservation.
Require Import Soundness.
Require Import Escape.
Require Import Occurrence.
Require Import Boundary.
Require Import BoundaryStep.
Require Import Decide.
Require Import Stepf.
Require Import MarkerRename.
Require Import Determinism.

(* ================================================================== *)
(* The certified evaluator decides termination on safe states: on a   *)
(* state satisfying the runtime invariants, [stepf] returns [None]    *)
(* ONLY on values.  Progress supplies value-or-step; evaluator        *)
(* completeness (Determinism.v) turns the absence of a stepf result   *)
(* into the absence of a step.                                        *)
(* ================================================================== *)

Theorem safe_stepf_none_is_value : forall Γ T t,
  eval_ctx Γ ->
  safety_invariants Γ T t ->
  stepf t = None ->
  value t.
Proof.
  intros Γ T t Hec [Hann [Hwr Hty]] Hnone.
  destruct Hann as [Hsafe _].
  destruct Hwr as [Hws _].
  destruct (progress _ _ _ Hec Hws Hsafe Hty) as [Hv | [t' Hs]].
  - exact Hv.
  - exfalso.
    destruct (stepf_complete_modulo_markers _ _ Hs) as [u' [Hsome _]].
    rewrite Hnone in Hsome. discriminate.
Qed.

(* ================================================================== *)
(*                                                                    *)
(*            THE UMBRELLA SOURCE-SAFETY THEOREM                      *)
(*                                                                    *)
(* One record bundling every guarantee the calculus gives a           *)
(* well-typed SOURCE program (no runtime marker constructs), and one  *)
(* theorem establishing all of them from the initial typing alone.    *)
(* This is the paper's single citation point and the single           *)
(* Print Assumptions target; each field is delivered by its           *)
(* dedicated theorem (Soundness.v, Escape.v, Occurrence.v,            *)
(* Boundary.v, BoundaryStep.v, Determinism.v, Stepf.v) — including    *)
(* the operational story: per-step boundary accounting, the           *)
(* evaluator halting only on values, uniqueness of the result, and    *)
(* evaluator completeness, all modulo the fresh-marker choice.        *)
(*                                                                    *)
(* The source premise uses the certified decider [sourceb]            *)
(* (Decide.v): `sourceb t = true` is the executable form of           *)
(* `has_rt_marker t = false`.                                         *)
(* ================================================================== *)

Record source_guarantees (Γ : ctx) (t : term) (T : type) : Prop := {
  (* Type safety: no reachable state is stuck.                        *)
  sg_type_safety :
      forall u, multi_step t u -> ~ stuck u;

  (* The runtime invariant bundle (marker annotations, marker         *)
  (* provenance/well-scopedness, typing) holds in every reachable     *)
  (* state.                                                           *)
  sg_invariants_preserved :
      forall u, multi_step t u -> safety_invariants Γ T u;

  (* Capability confinement, active form: a capability in redex       *)
  (* position always sits under its own delimiter.                    *)
  sg_capabilities_confined :
      forall E E_tag m Ts T_R op_bodies,
      multi_step t (plug E (term_cap E_tag m Ts T_R op_bodies)) ->
      ~ pure_ectx_m m E;

  (* Capability confinement, occurrence form: EVERY syntactic         *)
  (* occurrence — under lambdas, inside data, inside stored op        *)
  (* bodies — has its marker in scope along its path.                 *)
  sg_capability_occurrences_delimited :
      forall u p E_tag m Ts T_R op_bodies,
      multi_step t u ->
      subterm_at u p = Some (term_cap E_tag m Ts T_R op_bodies) ->
      exists ms', scope_at [] u p = Some ms' /\ In m ms';

  (* Results at an escapable type contain no runtime capability or    *)
  (* delimiter at any depth.                                          *)
  sg_noloc_results_cap_free :
      Γ ⊢ₗ lt_of_ty_G Γ T <: lt_free ->
      forall v, multi_step t v -> value v -> has_rt_marker v = false;

  (* Every EXECUTED boundary event on the two guarded data channels   *)
  (* (operation argument in, body result out) carries a value typed   *)
  (* at THE type its channel declares — the delimiter's declared      *)
  (* answer type T_B on the return-out channel, the operation's       *)
  (* instantiated signature on the operation-in channel — and that    *)
  (* type is escapable.  The decomposition the guarantee speaks       *)
  (* about is the fired event's own: it is linked to both endpoints   *)
  (* of the transition (boundary_channel_typed, BoundaryStep.v).      *)
  sg_boundary_channels_noloc :
      forall u u' ch v,
      multi_step t u ->
      boundary_step u u' ch v ->
      boundary_channel_typed Γ u u' ch v;

  (* The reified resumption entering the clause is a lambda typed at *)
  (* closure lifetime lt_local, so it cannot pass either guarded      *)
  (* noloc channel (exempt from that guarantee BY DESIGN); if it is   *)
  (* retained through a local channel, applying it is safe because    *)
  (* its body re-installs the delimiter.                              *)
  sg_boundary_resumptions_local :
      forall u u' v,
      multi_step t u ->
      boundary_step u u' operation_argument_in v ->
      exists E m T_B T_R E_tag Ts op_bodies op Ss A P resumption,
        resumption = term_lam (term_handler_m m T_B T_R
                                 (plug (shift_ectx_tm 1 0 P) (term_var 0))) A /\
        u = plug E (term_handler_m m T_B T_R
              (plug P (term_perform
                         (term_cap E_tag m Ts T_R op_bodies) op Ss A v))) /\
        (exists n_beta op_body,
           nth_error op_bodies op = Some (n_beta, op_body) /\
           u' = plug E (subst_list_tm [v; resumption]
                          (subst_list_ty_in_tm Ss op_body))) /\
        Γ ⊢ₜ resumption : type_fun A lt_local T_R;

  (* Every transition along the run is fully classified: a frame step *)
  (* (both endpoints share the context, so the delimiter spine above  *)
  (* the contraction is unchanged), a fresh-delimiter allocation, or  *)
  (* a boundary event whose crossing value is typed at its channel's  *)
  (* declared escapable type (step_boundary_accounting +              *)
  (* boundary_channel_typed, BoundaryStep.v).                         *)
  sg_step_accounting :
      forall u u',
      multi_step t u ->
      u ==> u' ->
      (exists E r r',
          ectx_wf E /\ u = plug E r /\ u' = plug E r' /\
          r -->h r' /\ frame_redex r)
      \/
      (exists E E_tag Ts T_B T_R op_bodies body m,
          ectx_wf E /\
          u = plug E (term_handle E_tag Ts T_B T_R op_bodies body) /\
          u' = plug E (term_handler_m m T_B T_R
                 (subst_tm 0 (term_cap E_tag m Ts T_R op_bodies) body)) /\
          ~ In m (markers_in u))
      \/
      (exists ch v,
          boundary_step u u' ch v /\
          boundary_channel_typed Γ u u' ch v);

  (* The certified evaluator halts along the run only by delivering a *)
  (* value — never on a stuck state or an unhandled escape.           *)
  sg_stepf_none_is_value :
      forall u, multi_step t u -> stepf u = None -> value u;

  (* The result is unique modulo the fresh-marker choice.             *)
  sg_result_unique_modulo_markers :
      forall v1 v2,
      multi_step t v1 -> value v1 ->
      multi_step t v2 -> value v2 ->
      marker_alpha_equiv v1 v2;

  (* The bounded driver reaches every value the relation can reach.   *)
  sg_evaluator_complete_modulo_markers :
      forall v,
      multi_step t v -> value v ->
      exists n, marker_alpha_equiv v (stepf_run n t)
}.

Theorem source_safety_suite : forall Γ t T,
  eval_ctx Γ ->
  sourceb t = true ->
  Γ ⊢ₜ t : T ->
  source_guarantees Γ t T.
Proof.
  intros Γ t T Hec Hsb Hty.
  apply sourceb_spec in Hsb.
  constructor.
  - intros u Hms. eapply source_type_soundness; eauto.
  - intros u Hms.
    eapply multi_step_preserves_safety_invariants; eauto.
    apply source_safety_invariants; assumption.
  - intros E E_tag m Ts T_R op_bodies Hms.
    eapply source_capability_never_exposed; eauto.
  - intros u p E_tag m Ts T_R op_bodies Hms Hsub.
    eapply source_capability_occurrence_delimited; eauto.
  - intros Hnl v Hms Hval.
    eapply source_noloc_result_no_runtime_forms; eauto.
  - intros u u' ch v Hms Hbs.
    eapply source_boundary_step_noloc; eauto.
  - intros u u' v Hms Hbs.
    eapply source_boundary_resumption_local; eauto.
  - intros u u' Hms Hstep.
    exact (source_step_accounting _ _ _ _ _ Hec Hsb Hty Hms Hstep).
  - intros u Hms Hnone.
    eapply safe_stepf_none_is_value with (T := T);
      [exact Hec | | exact Hnone].
    eapply multi_step_preserves_safety_invariants;
      [ exact Hec
      | apply source_safety_invariants; eassumption
      | exact Hms ].
  - intros v1 v2 Hms1 Hv1 Hms2 Hv2.
    eapply value_unique_modulo_markers; eassumption.
  - intros v Hms Hv.
    apply stepf_run_complete_modulo_markers; assumption.
Qed.

(* Source-facing trace form: running a well-typed source program with  *)
(* [stepf] can only halt at a value — the certified evaluator is a     *)
(* decision procedure for "one more step exists" along any execution.  *)
(* PUBLIC API — terminal deliverable: no internal consumers; do not
   mistake for dead code.  Gated by scripts/check_assumptions.py. *)
Corollary source_stepf_none_is_value : forall Γ t T u,
  eval_ctx Γ ->
  sourceb t = true ->
  Γ ⊢ₜ t : T ->
  multi_step t u ->
  stepf u = None ->
  value u.
Proof.
  intros Γ t T u Hec Hsb Hty Hms Hnone.
  apply sourceb_spec in Hsb.
  eapply safe_stepf_none_is_value with (T := T);
    [exact Hec | | exact Hnone].
  eapply multi_step_preserves_safety_invariants;
    [ exact Hec
    | apply source_safety_invariants; [exact Hsb | exact Hty]
    | exact Hms ].
Qed.

(* ================================================================== *)
(* The stuck verdict, named: [stepf_go_stuck_sound] (Determinism.v)   *)
(* states the SR_stuck claim operationally; here it meets the         *)
(* [stuck] predicate of the soundness capstone (Soundness.v).         *)
(* ================================================================== *)

Corollary stepf_stuck_is_stuck : forall t,
  stepf_go (marker_bound t) t = SR_stuck ->
  stuck t.
Proof.
  intros t Hgo.
  destruct (stepf_go_stuck_sound t Hgo) as [Hnv [Hns _]].
  split; [exact Hnv | intros [u Hs]; exact (Hns u Hs)].
Qed.

(* The stuckness certificate for hand-built states whose verdict is   *)
(* an unhandled ESCAPE rather than SR_stuck (an escaped perform with  *)
(* no matching delimiter above it): a [None] verdict on a non-value   *)
(* is genuine stuckness, because completeness turns "no stepf result" *)
(* into "no step".  Both hypotheses are decidable by [vm_compute].    *)
Corollary stepf_none_nonvalue_stuck : forall t,
  stepf t = None ->
  valueb t = false ->
  stuck t.
Proof.
  intros t Hn Hv. split.
  - intros Hval.
    assert (Hvb : valueb t = true)
      by (destruct (valueb_spec t); [reflexivity | contradiction]).
    congruence.
  - intros [u Hs].
    destruct (stepf_complete_modulo_markers _ _ Hs) as [u' [Hs' _]].
    rewrite Hn in Hs'. discriminate.
Qed.

(* The self-test: on a well-typed source program the stuck verdict is *)
(* unreachable — combined with [source_stepf_none_is_value], the      *)
(* evaluator halts on source states only by classifying them as       *)
(* values (never as SR_stuck, and never as an unhandled escape).      *)
Corollary source_stepf_never_stuck : forall Γ t T u,
  eval_ctx Γ ->
  sourceb t = true ->
  Γ ⊢ₜ t : T ->
  multi_step t u ->
  stepf_go (marker_bound u) u <> SR_stuck.
Proof.
  intros Γ t T u Hec Hsb Hty Hms Hgo.
  apply sourceb_spec in Hsb.
  destruct (multi_step_preserves_safety_invariants _ _ _ _ Hec
              (source_safety_invariants _ _ _ Hsb Hty) Hms)
    as [[Hmsafe _] [[Hws _] Htyu]].
  destruct (stepf_go_stuck_sound _ Hgo) as [Hnv [Hns _]].
  destruct (progress _ _ _ Hec Hws Hmsafe Htyu) as [Hv | [u' Hs]].
  - exact (Hnv Hv).
  - exact (Hns _ Hs).
Qed.
