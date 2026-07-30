Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import TypingInv.
Require Import MarkerAnnots.
Require Import WellScoped.
Require Import WsRtLaws.
Require Import Progress.
Require Import Preservation.
Require Import Soundness.
Require Import Escape.

(* ================================================================== *)
(*                                                                    *)
(*        HANDLER-BOUNDARY NON-ESCAPE (guarded data channels)         *)
(*                                                                    *)
(* The dynamic guarantee completing the escape story: no value with a *)
(* local type ever passes either GUARDED data channel of a handler    *)
(* boundary, at any step of any execution.  A value observed crossing *)
(* operation argument entering the handler (H_Perform), or the body   *)
(* result leaving the delimiter (H_Return) — is typed at an           *)
(* escapable (noloc) type: `lt_of_ty_G Γ S <: lt_free`, the exact     *)
(* judgment T_HandlerM and T_Perform impose on their boundary types.  *)
(*                                                                    *)
(* The two guarded channels are exactly the flows carrying ordinary   *)
(* data across the delimiter.  The reified resumption is exempt BY    *)
(* DESIGN: it has local closure lifetime, so it cannot pass either    *)
(* guarded noloc channel, and if retained through a local channel,    *)
(* applying it safely re-installs the delimiter (BoundaryStep.v).     *)
(* The abortive clause answer leaves through the UNGUARDED            *)
(* operation-clause answer channel, at the handler's public (and      *)
(* possibly local) answer type T_R.                                   *)
(* ================================================================== *)

(* A value observed crossing a handler boundary in the given state.    *)
(* The two shapes mirror the H_Return / H_Perform redexes              *)
(* (Semantics.v) exactly, so a boundary_crossing under a well-formed   *)
(* evaluation context is precisely a state whose next head step moves  *)
(* v across a delimiter.  `ectx_wf E` is deliberately not required:    *)
(* the typing decomposition below never needs it, so the theorem       *)
(* covers every state of the crossing shape, fireable or not.          *)
(*                                                                     *)
(* The reified resumption is exempt BY DESIGN: in H_Perform the        *)
(* continuation lambda (`term_lam (term_handler_m ...) A`, typed       *)
(* `A -local-> T_R`) also enters the handler, and its type is local,   *)
(* NOT noloc.  Its non-escape is the capability-confinement story      *)
(* (source_capability_never_exposed + the closure-lifetime             *)
(* discipline), not this theorem's.                                    *)
Inductive boundary_crossing : term -> term -> Prop :=
  | bc_return : forall E m T_B T_R v,
      value v ->
      boundary_crossing (plug E (term_handler_m m T_B T_R v)) v
  | bc_perform : forall E E_tag m Ts T_B T_R op_bodies op Ss A v P,
      value v ->
      pure_ectx_m m P ->
      boundary_crossing
        (plug E (term_handler_m m T_B T_R
           (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v))))
        v.

Lemma boundary_crossing_value : forall u v,
  boundary_crossing u v -> value v.
Proof. intros u v H; destruct H; assumption. Qed.

(* Runtime form: in any well-typed state, a value crossing a handler   *)
(* boundary is typed at an escapable (noloc) type.  Pure typing        *)
(* decomposition — no marker invariants, no induction on steps:        *)
(*  - bc_return:  plug_typing_inv + handler_m_typing_inv expose the    *)
(*    delimiter's body type T_B together with T_HandlerM's noloc       *)
(*    premise on it;                                                   *)
(*  - bc_perform: the same, then plug_typing_inv through the pure      *)
(*    context and perform_typing_inv expose the instantiated argument  *)
(*    type together with T_Perform's noloc premise on it.              *)
Theorem handler_boundary_noloc : forall Γ u T v,
  eval_ctx Γ ->
  Γ ⊢ₜ u : T ->
  boundary_crossing u v ->
  exists S, Γ ⊢ₜ v : S /\ Γ ⊢ₗ lt_of_ty_G Γ S <: lt_free.
Proof.
  intros Γ u T v Hec Hty Hbc. revert Hty.
  destruct Hbc as
    [E m T_B T_R v Hval
    |E E_tag m Ts T_B T_R op_bodies op Ss A v P Hval Hpure];
    intros Hty.
  - (* bc_return: v leaves the delimiter *)
    destruct (plug_typing_inv E Γ _ _ Hty) as [T' Hh].
    apply handler_m_typing_inv in Hh.
    destruct Hh as [Hv [_ [Hnl _]]].
    exists T_B. split; assumption.
  - (* bc_perform: the operation argument v enters the handler *)
    destruct (plug_typing_inv E Γ _ _ Hty) as [T' Hh].
    apply handler_m_typing_inv in Hh.
    destruct Hh as [Hplug _].
    destruct (plug_typing_inv P Γ _ _ Hplug) as [Tu Hperf].
    apply perform_typing_inv in Hperf.
    destruct Hperf as
      (E_t & Δ & Ts0 & n_α & ops & n_β & sig & ret & sig_inst
       & _ & _ & _ & _ & _ & _ & _ & _ & Hnlsi & _ & _ & Harg & _).
    exists sig_inst. split; assumption.
Qed.

(* Source-facing trace form: along any execution of a well-typed       *)
(* source program, every value crossing a handler boundary is typed    *)
(* at an escapable type.  The typing of the reached state comes from   *)
(* the step-preserved runtime invariants (subject reduction).          *)
Corollary source_handler_boundary_noloc : forall Γ t T u v,
  eval_ctx Γ ->
  has_rt_cap t = false ->
  Γ ⊢ₜ t : T ->
  multi_step t u ->
  boundary_crossing u v ->
  exists S, Γ ⊢ₜ v : S /\ Γ ⊢ₗ lt_of_ty_G Γ S <: lt_free.
Proof.
  intros Γ t T u v Hec Hsrc Hty Hms Hbc.
  destruct (multi_step_preserves_safety_invariants _ _ _ _ Hec
              (source_safety_invariants _ _ _ Hsrc Hty) Hms)
    as [_ [_ Htyu]].
  eapply handler_boundary_noloc; eauto.
Qed.

(* Data-type specialization: when the crossing type is a data          *)
(* constructor type, the crossing value is literally a constructor     *)
(* whose own lifetime annotation carries no top-level `local` —        *)
(* a local datum never crosses the boundary.                           *)
(* PUBLIC API — terminal deliverable: no internal consumers; do not
   mistake for dead code.  Gated by scripts/check_assumptions.py. *)
Corollary source_boundary_value_non_local : forall Γ t T u v,
  eval_ctx Γ ->
  has_rt_cap t = false ->
  Γ ⊢ₜ t : T ->
  multi_step t u ->
  boundary_crossing u v ->
  exists S,
    Γ ⊢ₜ v : S /\
    Γ ⊢ₗ lt_of_ty_G Γ S <: lt_free /\
    (forall K l Ts,
       S = type_ctor K l Ts ->
       ctx_lookup_eff Γ K = None ->
       K <> any_tag ->
       exists K' l' lts' vs,
         v = term_ctor K' l' lts' Ts vs /\ no_local_lt l' = true).
Proof.
  intros Γ t T u v Hec Hsrc Hty Hms Hbc.
  destruct (source_handler_boundary_noloc _ _ _ _ _ Hec Hsrc Hty Hms Hbc)
    as [S [HtyS Hnl]].
  exists S. split; [exact HtyS|]. split; [exact Hnl|].
  intros K l Ts HS Hdata HK. subst S.
  (* the data type's own top-level lifetime is below the escapable     *)
  (* whole-type lifetime: l <: l + (args) <: free                      *)
  assert (Hlfree : Γ ⊢ₗ l <: lt_free).
  { unfold lt_of_ty_G in Hnl. rewrite lt_of_ty_ctx_ctor in Hnl.
    destruct (lt_sub_wf _ _ _ Hnl) as [Hwfmin _].
    inversion Hwfmin; subst.
    eapply LS_Trans; [|exact Hnl].
    apply LS_JoinR1; [apply LS_Refl|]; assumption. }
  eapply data_value_top_lifetime_non_local;
    [ exact Hec | exact Hdata | exact HK | exact HtyS
    | eapply boundary_crossing_value; exact Hbc | exact Hlfree ].
Qed.
