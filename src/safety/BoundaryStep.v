Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import TypingInv.
Require Import Markers.
Require Import Progress.
Require Import Preservation.
Require Import Soundness.
Require Import Escape.
Require Import Boundary.

(* ================================================================== *)
(*                                                                    *)
(*              LABELLED BOUNDARY TRANSITIONS (events)                *)
(*                                                                    *)
(* Boundary.v phrases guarded-channel safety over boundary_crossing, a *)
(* STATE-shaped relation: it describes a term whose next head step    *)
(* would move a value across a delimiter, but carries no reduction    *)
(* and no `ectx_wf`.  This file upgrades those observations to actual *)
(* labelled TRANSITIONS: `boundary_step u u' ch v` is a genuine       *)
(* reduction u ==> u' (boundary_step_is_step) whose label records     *)
(* which value v crossed the handler boundary and through which       *)
(* channel ch.  The guarded-channel theorems then read as guarantees  *)
(* about every boundary EVENT fired along an execution, one theorem   *)
(* per channel (source_boundary_result_out_noloc,                     *)
(* source_boundary_operation_in_noloc).                               *)
(* ================================================================== *)

(* ================================================================== *)
(* Boundary-flow channel matrix.                                      *)
(*                                                                    *)
(* Five flows touch a handler boundary; the first and fourth are      *)
(* guarded by the noloc theorems below, the other three are exempt    *)
(* BY DESIGN and covered by other parts of the safety story:          *)
(*                                                                    *)
(*  1. operation argument, IN (H_Perform: v enters the clause)        *)
(*       GUARDED: noloc — source_boundary_operation_in_noloc.         *)
(*       T_Perform's premise `lt_of_ty_G Γ sig_inst <: lt_free`.      *)
(*  2. reified resumption, IN (H_Perform: the continuation lambda     *)
(*       enters the clause)                                           *)
(*       EXEMPT BY DESIGN: it is typed `A -local-> T_R`               *)
(*       (source_boundary_resumption_local below), so it cannot pass  *)
(*       either guarded noloc channel.  It MAY be retained through a  *)
(*       local channel; applying it is then safe because its lambda   *)
(*       body re-installs the delimiter.  Its capability content is   *)
(*       covered by the confinement story                             *)
(*       (source_capability_never_exposed, Escape.v).                 *)
(*  3. operation result, INTO the resumption (applying the reified    *)
(*       continuation is ordinary H_Beta)                             *)
(*       EXEMPT BY DESIGN: the value may be local — it flows UNDER    *)
(*       the delimiter the resumption lambda re-installs (read the    *)
(*       contractum of BS_Perform), so it never crosses the           *)
(*       boundary; it re-enters the delimited body.                   *)
(*  4. handler body result, OUT (H_Return: v leaves the delimiter)    *)
(*       GUARDED: noloc — source_boundary_result_out_noloc.           *)
(*       T_HandlerM's premise `lt_of_ty_G Γ T_B <: lt_free`.          *)
(*  5. abortive answer (the clause discards the resumption and        *)
(*       returns at T_R directly)                                     *)
(*       EXEMPT BY DESIGN — the UNGUARDED operation-clause answer     *)
(*       channel: H_Perform consumes the delimiter and the clause's   *)
(*       answer lands in the outer context at the handler's public    *)
(*       answer type T_R, which may legitimately be local; T_HandlerM *)
(*       imposes no noloc premise on T_R.                             *)
(* ================================================================== *)

(* The two guarded channels, as labels on boundary transitions. *)
Inductive boundary_channel : Type :=
  | operation_argument_in
  | handler_body_result_out.

(* `boundary_step u u' ch v`: state u reduces to u' by firing a        *)
(* boundary event — the head redex under the (well-formed) outer       *)
(* context E is exactly an H_Return or H_Perform redex, and v is the   *)
(* value the event moves across the delimiter, through channel ch.     *)
(* The redex and contractum shapes are copied verbatim from            *)
(* H_Return / H_Perform (Semantics.v), so each constructor IS an       *)
(* S_step instance (boundary_step_is_step) and, forgetting the outer   *)
(* context and the reduct, a boundary_crossing observation             *)
(* (boundary_step_to_crossing).                                        *)
Inductive boundary_step : term -> term -> boundary_channel -> term -> Prop :=
  | BS_Return : forall E m T_B T_R v,
      value v ->
      ectx_wf E ->
      boundary_step
        (plug E (term_handler_m m T_B T_R v))
        (plug E v)
        handler_body_result_out
        v
  | BS_Perform : forall E E_tag m Ts T_B T_R op_bodies op n_beta op_body Ss A v P,
      value v ->
      pure_ectx_m m P ->
      ectx_wf P ->
      ectx_wf E ->
      nth_error op_bodies op = Some (n_beta, op_body) ->
      boundary_step
        (plug E (term_handler_m m T_B T_R
           (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v))))
        (plug E (subst_list_tm
                   [v; term_lam (term_handler_m m T_B T_R
                                   (plug (shift_ectx_tm 1 0 P) (term_var 0))) A]
                   (subst_list_ty_in_tm Ss op_body)))
        operation_argument_in
        v.

(* A boundary transition is a genuine reduction: S_step with the       *)
(* outer context E and the H_Return / H_Perform head rule.             *)
Theorem boundary_step_is_step : forall u u' ch v,
  boundary_step u u' ch v -> u ==> u'.
Proof.
  intros u u' ch v Hbs.
  destruct Hbs as
    [E m T_B T_R v Hval HwfE
    |E E_tag m Ts T_B T_R op_bodies op n_beta op_body Ss A v P Hval Hpure HwfP HwfE Hnth].
  - apply S_step; [exact HwfE | apply H_Return; exact Hval].
  - apply S_step; [exact HwfE | eapply H_Perform; eassumption].
Qed.

(* Forgetting the reduct (and the ectx_wf premise, which               *)
(* boundary_crossing deliberately omits) turns a transition into the   *)
(* state-shaped observation of Boundary.v.                             *)
Lemma boundary_step_to_crossing : forall u u' ch v,
  boundary_step u u' ch v -> boundary_crossing u v.
Proof.
  intros u u' ch v Hbs.
  destruct Hbs; [apply bc_return | eapply bc_perform]; assumption.
Qed.

Lemma boundary_step_value : forall u u' ch v,
  boundary_step u u' ch v -> value v.
Proof.
  intros u u' ch v Hbs.
  eapply boundary_crossing_value. eapply boundary_step_to_crossing. exact Hbs.
Qed.

(* Source-facing event form of the guarded-channel theorem: along any  *)
(* execution of a well-typed source program, every value moved across  *)
(* a handler boundary BY AN ACTUAL REDUCTION is typed at an escapable  *)
(* (noloc) type.  Via boundary_step_to_crossing this is exactly        *)
(* source_handler_boundary_noloc (Boundary.v) restricted to fireable   *)
(* states.                                                             *)
Theorem source_boundary_step_noloc : forall Γ t T u u' ch v,
  eval_ctx Γ ->
  has_rt_cap t = false ->
  Γ ⊢ₜ t : T ->
  multi_step t u ->
  boundary_step u u' ch v ->
  exists S, Γ ⊢ₜ v : S /\ Γ ⊢ₗ lt_of_ty_G Γ S <: lt_free.
Proof.
  intros Γ t T u u' ch v Hec Hsrc Hty Hms Hbs.
  eapply source_handler_boundary_noloc; eauto.
  eapply boundary_step_to_crossing. exact Hbs.
Qed.

(* ------------------------------------------------------------------ *)
(* Per-channel corollaries: one citable theorem per guarded channel   *)
(* of the matrix above.                                               *)
(* ------------------------------------------------------------------ *)

(* Channel 4: the handler body's result leaving the delimiter          *)
(* (H_Return) is noloc.                                                *)
Corollary source_boundary_result_out_noloc : forall Γ t T u u' v,
  eval_ctx Γ ->
  has_rt_cap t = false ->
  Γ ⊢ₜ t : T ->
  multi_step t u ->
  boundary_step u u' handler_body_result_out v ->
  exists S, Γ ⊢ₜ v : S /\ Γ ⊢ₗ lt_of_ty_G Γ S <: lt_free.
Proof.
  intros Γ t T u u' v Hec Hsrc Hty Hms Hbs.
  eapply source_boundary_step_noloc; eauto.
Qed.

(* Channel 1: the operation argument entering the handler clause       *)
(* (H_Perform) is noloc.                                               *)
Corollary source_boundary_operation_in_noloc : forall Γ t T u u' v,
  eval_ctx Γ ->
  has_rt_cap t = false ->
  Γ ⊢ₜ t : T ->
  multi_step t u ->
  boundary_step u u' operation_argument_in v ->
  exists S, Γ ⊢ₜ v : S /\ Γ ⊢ₗ lt_of_ty_G Γ S <: lt_free.
Proof.
  intros Γ t T u u' v Hec Hsrc Hty Hms Hbs.
  eapply source_boundary_step_noloc; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Channel 2: the reified resumption is local by construction.        *)
(* ------------------------------------------------------------------ *)

(* Kernel: in any well-typed state of the BS_Perform redex shape, the  *)
(* resumption lambda that H_Perform reifies is typed `A -local-> T_R`. *)
(* This re-exposes the Hresume step buried inside perform_preserves    *)
(* (Preservation.v): perform/cap inversions recover ty_wf of A and     *)
(* T_R, the T_HandlerM premises transport under the new binder by the  *)
(* InsTm weakening lemmas (Weakening.v), the continuation body is      *)
(* typed by perform_resume_body, and the T_Lam capture obligation is   *)
(* trivial — the body carries a literal handler_m, so capture_lt is    *)
(* lt_local.  The closure lifetime lt_local is forced, which is what   *)
(* bars the resumption from both guarded noloc channels (channel 2 of  *)
(* the matrix); an escape through a LOCAL channel remains possible and *)
(* is safe because the lambda body re-installs the delimiter.          *)
Lemma boundary_resumption_typing :
  forall Γ m T_B T_R E_tag Ts op_bodies op Ss A v P T,
  eval_ctx Γ ->
  Γ ⊢ₜ term_handler_m m T_B T_R
        (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v)) : T ->
  Γ ⊢ₜ term_lam (term_handler_m m T_B T_R
                   (plug (shift_ectx_tm 1 0 P) (term_var 0))) A
      : type_fun A lt_local T_R.
Proof.
  intros Γ m T_B T_R E_tag Ts op_bodies op Ss A v P T Hec Hty.
  apply handler_m_typing_inv in Hty.
  destruct Hty as [Hplug [HTBR [HnlTB _]]].
  destruct (plug_typing_inv P Γ _ _ Hplug) as [Tu Hperf].
  apply perform_typing_inv in Hperf.
  destruct Hperf as
    (E_t0 & Δ0 & Ts0 & n_α & ops0 & n_β & sig & ret & sig_inst
     & Hrecv & _ & _ & _ & _ & _ & _ & _ & _ & _ & HwfRi & _ & _).
  apply cap_typing_inv in Hrecv.
  destruct Hrecv as
    (n_α' & ops' & _ & _ & _ & HwfTR & _ & _ & _).
  apply T_Lam.
  - exact HwfRi.
  - exact HwfTR.
  - apply T_HandlerM.
    + eapply ty_wf_InsTm;
        [eapply typing_implies_wf; exact Hplug | apply InsTm_here].
    + eapply ty_wf_InsTm; [exact HwfTR | apply InsTm_here].
    + eapply sub_free_InsTm; [apply InsTm_here | exact HnlTB].
    + eapply sub_InsTm; [exact HTBR | apply InsTm_here].
    + eapply perform_resume_body; [exact Hec | exact HwfRi | exact Hplug].
  - unfold capture_lt. simpl. apply LS_Refl. apply LWF_Local.
Qed.

(* Source-facing form: whenever an operation_argument_in event fires   *)
(* along an execution of a well-typed source program, the resumption   *)
(* it reifies — syntactically, a lambda re-installing the delimiter    *)
(* (first conjunct), and literally the second term substituted into    *)
(* the clause (third conjunct) — is typed at type_fun A lt_local T_R.  *)
(* Complements source_boundary_operation_in_noloc: on the same event,  *)
(* the argument is noloc while the resumption is local, which is why   *)
(* the latter is exempt from the noloc guarantee BY DESIGN.            *)
Theorem source_boundary_resumption_local : forall Γ t T u u' v,
  eval_ctx Γ ->
  has_rt_cap t = false ->
  Γ ⊢ₜ t : T ->
  multi_step t u ->
  boundary_step u u' operation_argument_in v ->
  exists E m T_B T_R E_tag Ts op_bodies op Ss A P resumption,
    resumption = term_lam (term_handler_m m T_B T_R
                             (plug (shift_ectx_tm 1 0 P) (term_var 0))) A /\
    u = plug E (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v))) /\
    (exists n_beta op_body,
       nth_error op_bodies op = Some (n_beta, op_body) /\
       u' = plug E (subst_list_tm [v; resumption] (subst_list_ty_in_tm Ss op_body))) /\
    Γ ⊢ₜ resumption : type_fun A lt_local T_R.
Proof.
  intros Γ t T u u' v Hec Hsrc Hty Hms Hbs.
  destruct (multi_step_preserves_safety_invariants _ _ _ _ Hec
              (source_safety_invariants _ _ _ Hsrc Hty) Hms)
    as [_ [_ Htyu]].
  inversion Hbs; subst.
  destruct (plug_typing_inv E Γ _ _ Htyu) as [T' Hh].
  exists E, m, T_B, T_R, E_tag, Ts, op_bodies, op, Ss, A, P,
    (term_lam (term_handler_m m T_B T_R
                 (plug (shift_ectx_tm 1 0 P) (term_var 0))) A).
  repeat split.
  - do 2 eexists. split; [eassumption | reflexivity].
  - eapply boundary_resumption_typing; [exact Hec | exact Hh].
Qed.
