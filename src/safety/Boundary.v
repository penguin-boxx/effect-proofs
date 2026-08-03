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
(* is typed at THE type its channel declares — the delimiter's own    *)
(* declared answer type T_B for the body result leaving (H_Return),   *)
(* the operation's instantiated signature for the operation argument  *)
(* entering the handler (H_Perform) — and that pinned type is         *)
(* escapable: `lt_of_ty_G Γ S <: lt_free`, the exact judgment         *)
(* T_HandlerM and T_Perform impose on their boundary types.           *)
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

(* Typing kernel of the return-out channel: wherever a delimiter's     *)
(* body has reduced to a value, that value is typed at the delimiter's *)
(* OWN declared answer type T_B, which T_HandlerM's premise makes      *)
(* noloc.  Pure typing decomposition: plug_typing_inv +                *)
(* handler_m_typing_inv — no marker invariants, no step induction.     *)
Lemma boundary_return_typing : forall Γ E m T_B T_R v T,
  Γ ⊢ₜ plug E (term_handler_m m T_B T_R v) : T ->
  Γ ⊢ₜ v : T_B /\ Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free.
Proof.
  intros Γ E m T_B T_R v T Hty.
  destruct (plug_typing_inv E Γ _ _ Hty) as [T' Hh].
  apply handler_m_typing_inv in Hh.
  destruct Hh as [Hv [_ [Hnl _]]].
  split; assumption.
Qed.

(* Typing kernel of the operation-in channel: the argument of a        *)
(* perform-on-a-capability redex is typed at the operation's           *)
(* INSTANTIATED SIGNATURE — `inst_op_all_args n_α Ts n_β Ss sig`, the  *)
(* very type T_Perform computes from the effect declaration — which    *)
(* T_Perform's premise makes noloc.  plug_typing_inv (through the      *)
(* outer context and the pure prefix) + handler_m_typing_inv +         *)
(* perform_typing_inv expose the premises; cap_typing_inv +            *)
(* sub_ctor_inv reconcile the receiver's typed tag/type-arguments      *)
(* with the capability's syntactic ones (eval_ctx_no_eff_any rules     *)
(* out the reserved Any tag).                                          *)
Lemma boundary_operation_typing :
  forall Γ E m T_B T_R E_tag Ts op_bodies op Ss A v P T,
  eval_ctx Γ ->
  Γ ⊢ₜ plug E (term_handler_m m T_B T_R
        (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v))) : T ->
  exists n_α ops n_β sig ret,
    ctx_lookup_eff Γ E_tag = Some (n_α, ops) /\
    nth_error ops op = Some (n_β, sig, ret) /\
    Γ ⊢ₜ v : inst_op_all_args n_α Ts n_β Ss sig /\
    Γ ⊢ₗ lt_of_ty_G Γ (inst_op_all_args n_α Ts n_β Ss sig) <: lt_free.
Proof.
  intros Γ E m T_B T_R E_tag Ts op_bodies op Ss A v P T Hec Hty.
  destruct (plug_typing_inv E Γ _ _ Hty) as [T' Hh].
  apply handler_m_typing_inv in Hh.
  destruct Hh as [Hplug _].
  destruct (plug_typing_inv P Γ _ _ Hplug) as [Tu Hperf].
  apply perform_typing_inv in Hperf.
  destruct Hperf as
    (E_t0 & Δ0 & Ts0 & n_α & ops & n_β & sig & ret & sig_inst
     & Hrecv & Heff0 & Hnth & _ & _ & _ & _ & Hsi & Hnlsi & _ & _ & Harg & _).
  apply cap_typing_inv in Hrecv.
  destruct Hrecv as (n_α' & ops' & _ & _ & _ & _ & _ & _ & HsubRecv).
  assert (HEt0 : E_t0 <> any_tag).
  { intros Heq; subst E_t0.
    rewrite (eval_ctx_no_eff_any _ Hec) in Heff0; discriminate. }
  destruct (sub_ctor_inv _ _ _ _ _ Hec HsubRecv HEt0) as [l' [Heqctor _]].
  injection Heqctor as HEtag Hl HTs.
  subst E_t0 Ts0 sig_inst.
  exists n_α, ops, n_β, sig, ret.
  repeat split; assumption.
Qed.

(* Runtime form: in any well-typed state, a value crossing a handler   *)
(* boundary is typed at THE type of its channel — the delimiter's      *)
(* declared answer type T_B on the return-out channel, the operation's *)
(* instantiated signature on the operation-in channel — and that type  *)
(* is escapable (noloc).  Each disjunct pins the crossing shape and    *)
(* its channel's type; the proof is the pure typing decomposition of   *)
(* the kernels above.                                                  *)
Theorem handler_boundary_noloc : forall Γ u T v,
  eval_ctx Γ ->
  Γ ⊢ₜ u : T ->
  boundary_crossing u v ->
  (* return-out channel (bc_return): v leaves the delimiter at the     *)
  (* delimiter's own declared answer type T_B.                         *)
  (exists E m T_B T_R,
     u = plug E (term_handler_m m T_B T_R v) /\
     Γ ⊢ₜ v : T_B /\
     Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free)
  \/
  (* operation-in channel (bc_perform): v enters the handler clause at *)
  (* the operation's instantiated signature, computed from the effect  *)
  (* declaration exactly as T_Perform computes it.                     *)
  (exists E E_tag m Ts T_B T_R op_bodies op Ss A P n_α ops n_β sig ret sig_inst,
     u = plug E (term_handler_m m T_B T_R
           (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v))) /\
     ctx_lookup_eff Γ E_tag = Some (n_α, ops) /\
     nth_error ops op = Some (n_β, sig, ret) /\
     sig_inst = inst_op_all_args n_α Ts n_β Ss sig /\
     Γ ⊢ₜ v : sig_inst /\
     Γ ⊢ₗ lt_of_ty_G Γ sig_inst <: lt_free).
Proof.
  intros Γ u T v Hec Hty Hbc. revert Hty.
  destruct Hbc as
    [E m T_B T_R v Hval
    |E E_tag m Ts T_B T_R op_bodies op Ss A v P Hval Hpure];
    intros Hty.
  - (* bc_return: v leaves the delimiter *)
    destruct (boundary_return_typing _ _ _ _ _ _ _ Hty) as [Hv Hnl].
    left. exists E, m, T_B, T_R.
    repeat split; try reflexivity; assumption.
  - (* bc_perform: the operation argument v enters the handler *)
    destruct (boundary_operation_typing _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hec Hty)
      as (n_α & ops & n_β & sig & ret & Heff & Hnth & Harg & Hnl).
    right.
    exists E, E_tag, m, Ts, T_B, T_R, op_bodies, op, Ss, A, P,
      n_α, ops, n_β, sig, ret, (inst_op_all_args n_α Ts n_β Ss sig).
    repeat split; try reflexivity; assumption.
Qed.

(* Source-facing trace form: along any execution of a well-typed       *)
(* source program, every value crossing a handler boundary is typed    *)
(* at its channel's declared type (T_B on the return-out channel, the  *)
(* instantiated operation signature on the operation-in channel), and  *)
(* that type is escapable.  The typing of the reached state comes from *)
(* the step-preserved runtime invariants (subject reduction).          *)
Corollary source_handler_boundary_noloc : forall Γ t T u v,
  eval_ctx Γ ->
  has_rt_cap t = false ->
  Γ ⊢ₜ t : T ->
  multi_step t u ->
  boundary_crossing u v ->
  (exists E m T_B T_R,
     u = plug E (term_handler_m m T_B T_R v) /\
     Γ ⊢ₜ v : T_B /\
     Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free)
  \/
  (exists E E_tag m Ts T_B T_R op_bodies op Ss A P n_α ops n_β sig ret sig_inst,
     u = plug E (term_handler_m m T_B T_R
           (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v))) /\
     ctx_lookup_eff Γ E_tag = Some (n_α, ops) /\
     nth_error ops op = Some (n_β, sig, ret) /\
     sig_inst = inst_op_all_args n_α Ts n_β Ss sig /\
     Γ ⊢ₜ v : sig_inst /\
     Γ ⊢ₗ lt_of_ty_G Γ sig_inst <: lt_free).
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
  assert (HS : exists S, Γ ⊢ₜ v : S /\ Γ ⊢ₗ lt_of_ty_G Γ S <: lt_free).
  { destruct (source_handler_boundary_noloc _ _ _ _ _ Hec Hsrc Hty Hms Hbc)
      as [ (E & m & T_B & T_R & _ & HtyS & Hnl)
         | (E & E_tag & m & Ts & T_B & T_R & op_bodies & op & Ss & A & P
            & n_α & ops & n_β & sig & ret & sig_inst
            & _ & _ & _ & _ & HtyS & Hnl) ];
      eauto. }
  destruct HS as [S [HtyS Hnl]].
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
