Require Import Stdlib.Lists.List.
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
Require Import Soundness.
Require Import Escape.
Require Import Occurrence.
Require Import Boundary.
Require Import BoundaryStep.
Require Import Decide.

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
(* Boundary.v, BoundaryStep.v).                                       *)
(*                                                                    *)
(* The source premise uses the certified decider [sourceb]            *)
(* (Decide.v): `sourceb t = true` is the executable form of           *)
(* `has_rt_cap t = false`.                                            *)
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
      forall E E_tag m n_beta Ts T_R op_body,
      multi_step t (plug E (term_cap E_tag m n_beta Ts T_R op_body)) ->
      ~ pure_ectx_m m E;

  (* Capability confinement, occurrence form: EVERY syntactic         *)
  (* occurrence — under lambdas, inside data, inside stored op        *)
  (* bodies — has its marker in scope along its path.                 *)
  sg_capability_occurrences_delimited :
      forall u p E_tag m n_beta Ts T_R op_body,
      multi_step t u ->
      subterm_at u p = Some (term_cap E_tag m n_beta Ts T_R op_body) ->
      exists ms', scope_at [] u p = Some ms' /\ In m ms';

  (* Results at an escapable type contain no runtime capability or    *)
  (* delimiter at any depth.                                          *)
  sg_noloc_results_cap_free :
      Γ ⊢ₗ lt_of_ty_G Γ T <: lt_free ->
      forall v, multi_step t v -> value v -> has_rt_cap v = false;

  (* Every EXECUTED boundary event on the two guarded data channels   *)
  (* (operation argument in, body result out) carries a value typed   *)
  (* at an escapable type.                                            *)
  sg_boundary_channels_noloc :
      forall u u' ch v,
      multi_step t u ->
      boundary_step u u' ch v ->
      exists S, Γ ⊢ₜ v : S /\ Γ ⊢ₗ lt_of_ty_G Γ S <: lt_free;

  (* The one local thing that enters the clause — the reified         *)
  (* resumption — is a lambda typed at closure lifetime lt_local,     *)
  (* which is exactly what pins it inside the clause (exempt from     *)
  (* the noloc guarantee BY DESIGN).                                  *)
  sg_boundary_resumptions_local :
      forall u u' v,
      multi_step t u ->
      boundary_step u u' operation_argument_in v ->
      exists E m T_B T_R E_tag n_beta Ts op_body Ss A P resumption,
        resumption = term_lam (term_handler_m m T_B T_R
                                 (plug (shift_ectx_tm 1 0 P) (term_var 0))) A /\
        u = plug E (term_handler_m m T_B T_R
              (plug P (term_perform
                         (term_cap E_tag m n_beta Ts T_R op_body) Ss A v))) /\
        u' = plug E (subst_list_tm [v; resumption]
                       (subst_list_ty_in_tm Ss op_body)) /\
        Γ ⊢ₜ resumption : type_fun A lt_local T_R
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
  - intros E E_tag m n_beta Ts T_R op_body Hms.
    eapply source_capability_never_exposed; eauto.
  - intros u p E_tag m n_beta Ts T_R op_body Hms Hsub.
    eapply source_capability_occurrence_delimited; eauto.
  - intros Hnl v Hms Hval.
    eapply source_noloc_result_no_runtime_forms; eauto.
  - intros u u' ch v Hms Hbs.
    eapply source_boundary_step_noloc; eauto.
  - intros u u' v Hms Hbs.
    eapply source_boundary_resumption_local; eauto.
Qed.
