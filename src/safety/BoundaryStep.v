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
Require Import Boundary.
Require Import Eqb.
Require Import Stepf.
Require Import Determinism.

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
(*       The value is typed at the operation's INSTANTIATED           *)
(*       SIGNATURE `inst_op_all_args n_α Ts n_β Ss sig` (exactly as   *)
(*       T_Perform computes it from the effect declaration), and      *)
(*       T_Perform's premise `lt_of_ty_G Γ sig_inst <: lt_free`       *)
(*       makes that type escapable.                                   *)
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
(*       The value is typed at the delimiter's OWN declared answer    *)
(*       type T_B, and T_HandlerM's premise                           *)
(*       `lt_of_ty_G Γ T_B <: lt_free` makes that type escapable.     *)
(*  5. abortive answer (the clause discards the resumption and        *)
(*       returns at T_R directly)                                     *)
(*       EXEMPT BY DESIGN — the UNGUARDED operation-clause answer     *)
(*       channel: H_Perform consumes the delimiter and the clause's   *)
(*       answer lands in the outer context at the handler's public    *)
(*       answer type T_R, which may legitimately be local; T_HandlerM *)
(*       imposes no noloc premise on T_R.                             *)
(*                                                                    *)
(* The matrix's EXHAUSTIVENESS is itself a theorem, not prose: every  *)
(* reduction step is a frame step (shared context, delimiter spine    *)
(* above the contraction unchanged), a fresh-delimiter allocation, or *)
(* exactly one boundary event — [step_boundary_accounting] at the end *)
(* of this file, with mutual exclusivity and uniqueness of the event  *)
(* label delivered by the computable classifier [classify].           *)
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

(* The pinned crossing type of each guarded channel: the value moved   *)
(* through channel ch of a boundary event u ==> u' is typed at THE     *)
(* type the channel declares — the delimiter's own declared answer     *)
(* type T_B on the return-out channel, the operation's instantiated    *)
(* signature (bound exactly as T_Perform computes it from the effect   *)
(* declaration) on the operation-in channel — and that type is         *)
(* escapable (noloc).                                                  *)
(*                                                                     *)
(* The decomposition is THE fired event's own, not a re-existentialized *)
(* one: each arm links its components to BOTH endpoints of the         *)
(* transition — the source decomposition `u = plug E (redex)` AND the  *)
(* reduct equation `u' = plug E (contractum)` copied verbatim from     *)
(* H_Return / H_Perform, under the same `ectx_wf` (and, on the         *)
(* operation-in channel, `pure_ectx_m`/`ectx_wf P`) side conditions    *)
(* the firing rule carries.  So the delimiter, marker and declared     *)
(* types the typing conjuncts speak about are those of the event that  *)
(* actually reduced, not of some other decomposition of the state.     *)
Definition boundary_channel_typed
    (Γ : ctx) (u u' : term) (ch : boundary_channel) (v : term) : Prop :=
  match ch with
  | handler_body_result_out =>
      exists E m T_B T_R,
        u = plug E (term_handler_m m T_B T_R v) /\
        u' = plug E v /\
        ectx_wf E /\
        Γ ⊢ₜ v : T_B /\
        Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free
  | operation_argument_in =>
      exists E E_tag m Ts T_B T_R op_bodies op Ss A P n_α ops n_β sig ret sig_inst,
        u = plug E (term_handler_m m T_B T_R
              (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v))) /\
        (exists n_beta op_body,
           nth_error op_bodies op = Some (n_beta, op_body) /\
           u' = plug E (subst_list_tm
                  [v; term_lam (term_handler_m m T_B T_R
                                  (plug (shift_ectx_tm 1 0 P) (term_var 0))) A]
                  (subst_list_ty_in_tm Ss op_body))) /\
        ectx_wf E /\
        pure_ectx_m m P /\
        ectx_wf P /\
        ctx_lookup_eff Γ E_tag = Some (n_α, ops) /\
        nth_error ops op = Some (n_β, sig, ret) /\
        sig_inst = inst_op_all_args n_α Ts n_β Ss sig /\
        Γ ⊢ₜ v : sig_inst /\
        Γ ⊢ₗ lt_of_ty_G Γ sig_inst <: lt_free
  end.

(* Source-facing event form of the guarded-channel theorem: along any  *)
(* execution of a well-typed source program, every value moved across  *)
(* a handler boundary BY AN ACTUAL REDUCTION is typed at its           *)
(* channel's declared type, which is escapable (noloc).  The typing    *)
(* content is the kernel decomposition of Boundary.v                   *)
(* (boundary_return_typing / boundary_operation_typing) applied to     *)
(* the reached state.                                                  *)
Theorem source_boundary_step_noloc : forall Γ t T u u' ch v,
  eval_ctx Γ ->
  has_rt_marker t = false ->
  Γ ⊢ₜ t : T ->
  multi_step t u ->
  boundary_step u u' ch v ->
  boundary_channel_typed Γ u u' ch v.
Proof.
  intros Γ t T u u' ch v Hec Hsrc Hty Hms Hbs.
  destruct (multi_step_preserves_safety_invariants _ _ _ _ Hec
              (source_safety_invariants _ _ _ Hsrc Hty) Hms)
    as [_ [_ Htyu]].
  destruct Hbs as
    [E m T_B T_R v Hval HwfE
    |E E_tag m Ts T_B T_R op_bodies op n_beta op_body Ss A v P
       Hval Hpure HwfP HwfE Hnth];
    simpl.
  - (* BS_Return *)
    destruct (boundary_return_typing _ _ _ _ _ _ _ Htyu) as [Hv Hnl].
    exists E, m, T_B, T_R.
    repeat split; try reflexivity; assumption.
  - (* BS_Perform *)
    destruct (boundary_operation_typing _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hec Htyu)
      as (n_α & ops & n_β & sig & ret & Heff & Hnth' & Harg & Hnl).
    exists E, E_tag, m, Ts, T_B, T_R, op_bodies, op, Ss, A, P,
      n_α, ops, n_β, sig, ret, (inst_op_all_args n_α Ts n_β Ss sig).
    repeat split; try reflexivity; try assumption.
    exists n_beta, op_body. split; [exact Hnth | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* Per-channel corollaries: one citable theorem per guarded channel   *)
(* of the matrix above, each naming its channel's crossing type.      *)
(* ------------------------------------------------------------------ *)

(* Channel 4: the handler body's result leaving the delimiter          *)
(* (H_Return) is typed at the delimiter's own declared answer type     *)
(* T_B, which is noloc.  The decomposition is the fired event's own:   *)
(* it is linked to both endpoints of the transition and carries the    *)
(* rule's ectx_wf side condition.                                      *)
Corollary source_boundary_result_out_noloc : forall Γ t T u u' v,
  eval_ctx Γ ->
  has_rt_marker t = false ->
  Γ ⊢ₜ t : T ->
  multi_step t u ->
  boundary_step u u' handler_body_result_out v ->
  exists E m T_B T_R,
    u = plug E (term_handler_m m T_B T_R v) /\
    u' = plug E v /\
    ectx_wf E /\
    Γ ⊢ₜ v : T_B /\
    Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free.
Proof.
  intros Γ t T u u' v Hec Hsrc Hty Hms Hbs.
  exact (source_boundary_step_noloc _ _ _ _ _ _ _ Hec Hsrc Hty Hms Hbs).
Qed.

(* Channel 1: the operation argument entering the handler clause       *)
(* (H_Perform) is typed at the operation's instantiated signature      *)
(* (computed from the effect declaration exactly as T_Perform does),   *)
(* which is noloc.  The decomposition is the fired event's own: it is  *)
(* linked to both endpoints of the transition and carries the rule's   *)
(* ectx_wf / pure_ectx_m side conditions.                              *)
Corollary source_boundary_operation_in_noloc : forall Γ t T u u' v,
  eval_ctx Γ ->
  has_rt_marker t = false ->
  Γ ⊢ₜ t : T ->
  multi_step t u ->
  boundary_step u u' operation_argument_in v ->
  exists E E_tag m Ts T_B T_R op_bodies op Ss A P n_α ops n_β sig ret sig_inst,
    u = plug E (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v))) /\
    (exists n_beta op_body,
       nth_error op_bodies op = Some (n_beta, op_body) /\
       u' = plug E (subst_list_tm
              [v; term_lam (term_handler_m m T_B T_R
                              (plug (shift_ectx_tm 1 0 P) (term_var 0))) A]
              (subst_list_ty_in_tm Ss op_body))) /\
    ectx_wf E /\
    pure_ectx_m m P /\
    ectx_wf P /\
    ctx_lookup_eff Γ E_tag = Some (n_α, ops) /\
    nth_error ops op = Some (n_β, sig, ret) /\
    sig_inst = inst_op_all_args n_α Ts n_β Ss sig /\
    Γ ⊢ₜ v : sig_inst /\
    Γ ⊢ₗ lt_of_ty_G Γ sig_inst <: lt_free.
Proof.
  intros Γ t T u u' v Hec Hsrc Hty Hms Hbs.
  exact (source_boundary_step_noloc _ _ _ _ _ _ _ Hec Hsrc Hty Hms Hbs).
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
  has_rt_marker t = false ->
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

(* ================================================================== *)
(*        COMPLETENESS OF THE MATRIX: delimiter accounting            *)
(*                                                                    *)
(* The matrix above lists every flow that touches a delimiter; this   *)
(* section makes its EXHAUSTIVENESS a theorem                         *)
(* (step_boundary_accounting): every reduction step is               *)
(*                                                                    *)
(*   (i)   a FRAME step — a pure head contraction under a shared      *)
(*         context (both endpoints decompose through the SAME E, so   *)
(*         the delimiter spine above the contraction is unchanged     *)
(*         verbatim), whose redex is not delimiter-headed;            *)
(*   (ii)  a fresh-delimiter ALLOCATION (S_HandleCtx); or             *)
(*   (iii) EXACTLY ONE boundary event — an H_Return / H_Perform       *)
(*         contraction, i.e. a [boundary_step] on one of the two      *)
(*         guarded channels, with its crossing value.                 *)
(*                                                                    *)
(* Method (same as Determinism.v): no standalone unique-decomposition *)
(* lemma.  A computable classifier [classify] walks the SAME spine    *)
(* the evaluator walks — child verdicts are routed through            *)
(* [stepf_go] — and answers, at the redex, which class fires and (for *)
(* a boundary event) which value crosses through which channel.  The  *)
(* exactness lemmas pin the classifier on each redex family, so the   *)
(* three classes are MUTUALLY EXCLUSIVE and the event label is a      *)
(* FUNCTION of the state: "exactly one" is by computation, not by     *)
(* case-bashing decompositions.                                       *)
(*                                                                    *)
(* Scope: the accounting classifies SEMANTICS STEPS.  The matrix's    *)
(* three exempt flows (resumption in, operation result into the       *)
(* resumption, abortive answer) are not separate labels — they occur  *)
(* inside the H_Perform contractum and the frame steps that follow    *)
(* it, exactly as the matrix header argues.                           *)
(* ================================================================== *)

(* The three classes a step can fall into. *)
Inductive step_class : Type :=
  | sc_frame    : step_class
  | sc_alloc    : step_class
  | sc_boundary : boundary_channel -> term -> step_class.

(* A redex that is not delimiter-headed: H_Return and H_Perform are   *)
(* exactly the head rules whose redex is a [term_handler_m].          *)
Definition frame_redex (r : term) : Prop :=
  forall m T_B T_R body, r <> term_handler_m m T_B T_R body.

Fixpoint classify (fresh : marker) (t : term) : option step_class :=
  let fix class_list (ts : list term) : option step_class :=
    match ts with
    | [] => None
    | u :: rest =>
        match stepf_go fresh u with
        | SR_val => class_list rest
        | SR_step _ => classify fresh u
        | SR_esc _ _ => None
        | SR_stuck => None
        end
    end
  in
  match t with
  | term_var _ => None
  | term_lam _ _ => None
  | term_ty_lam _ _ => None
  | term_lt_lam _ => None
  | term_cap _ _ _ _ _ => None
  | term_app t1 t2 =>
      match stepf_go fresh t1 with
      | SR_val =>
          match stepf_go fresh t2 with
          | SR_val =>
              match t1 with
              | term_lam _ _ => Some sc_frame
              | _ => None
              end
          | SR_step _ => classify fresh t2
          | SR_esc _ _ => None
          | SR_stuck => None
          end
      | SR_step _ => classify fresh t1
      | SR_esc _ _ => None
      | SR_stuck => None
      end
  | term_ty_app t1 _ =>
      match stepf_go fresh t1 with
      | SR_val =>
          match t1 with
          | term_ty_lam _ _ => Some sc_frame
          | _ => None
          end
      | SR_step _ => classify fresh t1
      | SR_esc _ _ => None
      | SR_stuck => None
      end
  | term_lt_app t1 _ =>
      match stepf_go fresh t1 with
      | SR_val =>
          match t1 with
          | term_lt_lam _ => Some sc_frame
          | _ => None
          end
      | SR_step _ => classify fresh t1
      | SR_esc _ _ => None
      | SR_stuck => None
      end
  | term_ctor _ _ _ _ ts => class_list ts
  | term_match scrut K _ arity _ _ =>
      match stepf_go fresh scrut with
      | SR_val =>
          match scrut with
          | term_ctor K' _ _ _ vs =>
              if Nat.eqb K' K
              then if Nat.eqb arity (List.length vs)
                   then Some sc_frame
                   else None
              else Some sc_frame
          | _ => None
          end
      | SR_step _ => classify fresh scrut
      | SR_esc _ _ => None
      | SR_stuck => None
      end
  | term_handle _ _ _ _ _ _ => Some sc_alloc
  | term_perform recv _ _ _ arg =>
      match stepf_go fresh recv with
      | SR_val =>
          match stepf_go fresh arg with
          | SR_val => None
          | SR_step _ => classify fresh arg
          | SR_esc _ _ => None
          | SR_stuck => None
          end
      | SR_step _ => classify fresh recv
      | SR_esc _ _ => None
      | SR_stuck => None
      end
  | term_handler_m m0 _ T_R body =>
      match stepf_go fresh body with
      | SR_val => Some (sc_boundary handler_body_result_out body)
      | SR_step _ => classify fresh body
      | SR_esc e _ =>
          if Nat.eqb (esc_mk e) m0
          then if ty_eqb (esc_TR e) T_R
               then Some (sc_boundary operation_argument_in (esc_arg e))
               else None
          else None
      | SR_stuck => None
      end
  end.

(* Top-level twin of the constructor-spine walk, plus the usual       *)
(* go-eq unfolding lemma (same pattern as stepf_list, Stepf.v).       *)
Fixpoint classify_list (fresh : marker) (ts : list term)
    : option step_class :=
  match ts with
  | [] => None
  | u :: rest =>
      match stepf_go fresh u with
      | SR_val => classify_list fresh rest
      | SR_step _ => classify fresh u
      | SR_esc _ _ => None
      | SR_stuck => None
      end
  end.

Lemma classify_class_list_eq : forall fresh ts,
  (fix class_list (ts : list term) : option step_class :=
     match ts with
     | [] => None
     | u :: rest =>
         match stepf_go fresh u with
         | SR_val => class_list rest
         | SR_step _ => classify fresh u
         | SR_esc _ _ => None
         | SR_stuck => None
         end
     end) ts = classify_list fresh ts.
Proof.
  intros fresh; induction ts as [|u rest IH]; simpl.
  - reflexivity.
  - destruct (stepf_go fresh u); congruence.
Qed.

Lemma classify_list_vals_prefix : forall fresh vsl u u0 vsr,
  Forall value vsl ->
  stepf_go fresh u = SR_step u0 ->
  classify_list fresh (vsl ++ u :: vsr) = classify fresh u.
Proof.
  intros fresh vsl u u0 vsr Hvals Hu.
  induction Hvals as [|v vsl' Hv Hvals' IH]; simpl.
  - rewrite Hu. reflexivity.
  - rewrite (stepf_go_value fresh v Hv), IH. reflexivity.
Qed.

(* The classifier is transparent to any well-formed spine above the   *)
(* redex — the classification is decided AT the redex.                *)
Lemma classify_plug : forall fresh E r u0,
  ectx_wf E ->
  stepf_go fresh r = SR_step u0 ->
  classify fresh (plug E r) = classify fresh r.
Proof.
  intros fresh E r u0 Hwf Hr.
  induction Hwf; simpl.
  - reflexivity.
  - erewrite stepf_go_plug_step by eassumption. exact IHHwf.
  - rewrite (stepf_go_value fresh v) by assumption.
    erewrite stepf_go_plug_step by eassumption. exact IHHwf.
  - erewrite stepf_go_plug_step by eassumption. exact IHHwf.
  - erewrite stepf_go_plug_step by eassumption. exact IHHwf.
  - rewrite classify_class_list_eq.
    erewrite classify_list_vals_prefix;
      [ exact IHHwf | assumption | eapply stepf_go_plug_step; eassumption ].
  - erewrite stepf_go_plug_step by eassumption. exact IHHwf.
  - erewrite stepf_go_plug_step by eassumption. exact IHHwf.
  - erewrite stepf_go_plug_step by eassumption. exact IHHwf.
  - rewrite (stepf_go_value fresh v) by assumption.
    erewrite stepf_go_plug_step by eassumption. exact IHHwf.
Qed.

(* Exactness on each redex family: the classifier answers sc_frame on *)
(* every pure head redex, sc_alloc on a handle, and the channel/value *)
(* label on each boundary redex.                                      *)
Lemma classify_head_frame : forall fresh r r',
  r -->h r' ->
  frame_redex r ->
  classify fresh r = Some sc_frame.
Proof.
  intros fresh r r' Hstep Hfr. destruct Hstep; simpl.
  - (* H_Beta *)
    rewrite (stepf_go_value fresh v) by assumption. reflexivity.
  - (* H_TyBeta *) reflexivity.
  - (* H_LtBeta *) reflexivity.
  - (* H_MatchYes *)
    rewrite stepf_go_list_eq.
    rewrite (stepf_list_vals fresh vs) by assumption.
    rewrite !Nat.eqb_refl. reflexivity.
  - (* H_MatchNo *)
    rewrite stepf_go_list_eq.
    rewrite (stepf_list_vals fresh vs) by assumption.
    assert (Hne : Nat.eqb K' K = false) by (apply Nat.eqb_neq; congruence).
    rewrite Hne. reflexivity.
  - (* H_Return *) exfalso. eapply Hfr. reflexivity.
  - (* H_Perform *) exfalso. eapply Hfr. reflexivity.
Qed.

Lemma classify_alloc : forall fresh E_tag Ts T_B T_R op_bodies body,
  classify fresh (term_handle E_tag Ts T_B T_R op_bodies body)
  = Some sc_alloc.
Proof. reflexivity. Qed.

Lemma classify_return : forall fresh m T_B T_R v,
  value v ->
  classify fresh (term_handler_m m T_B T_R v)
  = Some (sc_boundary handler_body_result_out v).
Proof.
  intros fresh m T_B T_R v Hv. simpl.
  rewrite (stepf_go_value fresh v Hv). reflexivity.
Qed.

Lemma classify_perform :
  forall fresh E_tag m Ts T_B T_R op_bodies op Ss A v P,
  value v ->
  pure_ectx_m m P ->
  ectx_wf P ->
  classify fresh
    (term_handler_m m T_B T_R
       (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v)))
  = Some (sc_boundary operation_argument_in v).
Proof.
  intros fresh E_tag m Ts T_B T_R op_bodies op Ss A v P Hv Hpure Hwf.
  simpl.
  rewrite (stepf_go_esc_plug fresh E_tag m Ts T_R op_bodies op Ss A v P)
    by assumption.
  simpl. rewrite Nat.eqb_refl, ty_eqb_refl. reflexivity.
Qed.

(* Every boundary event computes its own label: the channel and the   *)
(* crossing value are a FUNCTION of the state.                        *)
Lemma classify_event : forall t u ch v fresh,
  boundary_step t u ch v ->
  classify fresh t = Some (sc_boundary ch v).
Proof.
  intros t u ch v fresh Hbs.
  destruct Hbs as
    [E m T_B T_R v0 Hval HwfE
    |E E_tag m Ts T_B T_R op_bodies op n_beta op_body Ss A v0 P
       Hval Hpure HwfP HwfE Hnth].
  - rewrite (classify_plug fresh E _ _ HwfE
      (stepf_go_head_step fresh _ _ (H_Return m T_B T_R v0 Hval))).
    apply classify_return; exact Hval.
  - rewrite (classify_plug fresh E _ _ HwfE
      (stepf_go_head_step fresh _ _
         (H_Perform E_tag m Ts T_B T_R op_bodies op n_beta op_body Ss A v0 P
            Hval Hpure HwfP Hnth))).
    apply classify_perform; assumption.
Qed.

(* "Exactly one boundary event": the label is unique — any two events *)
(* fired from the same state agree on both the channel and the        *)
(* crossing value.  (Uniqueness of the LABEL, which is what the       *)
(* guarantees observe; uniqueness of the full decomposition — the     *)
(* outer context E and the redex parameters — is not claimed.)        *)
Theorem boundary_event_unique : forall t u u' ch ch' v v',
  boundary_step t u ch v ->
  boundary_step t u' ch' v' ->
  ch = ch' /\ v = v'.
Proof.
  intros t u u' ch ch' v v' H1 H2.
  pose proof (classify_event _ _ _ _ 0 H1) as E1.
  pose proof (classify_event _ _ _ _ 0 H2) as E2.
  rewrite E1 in E2. injection E2 as Ech Ev. subst. split; reflexivity.
Qed.

(* The classes are mutually exclusive: a pure frame contraction fires *)
(* no boundary event, and neither does a delimiter allocation.        *)
Theorem frame_step_no_boundary_event : forall E r r' u ch v,
  ectx_wf E ->
  r -->h r' ->
  frame_redex r ->
  ~ boundary_step (plug E r) u ch v.
Proof.
  intros E r r' u ch v Hwf Hhead Hfr Hbs.
  pose proof (classify_event _ _ _ _ 0 Hbs) as Ec.
  rewrite (classify_plug 0 E _ _ Hwf (stepf_go_head_step 0 _ _ Hhead)) in Ec.
  rewrite (classify_head_frame 0 _ _ Hhead Hfr) in Ec.
  discriminate Ec.
Qed.

Theorem alloc_step_no_boundary_event :
  forall E E_tag Ts T_B T_R op_bodies body u ch v,
  ectx_wf E ->
  ~ boundary_step (plug E (term_handle E_tag Ts T_B T_R op_bodies body)) u ch v.
Proof.
  intros E E_tag Ts T_B T_R op_bodies body u ch v Hwf Hbs.
  pose proof (classify_event _ _ _ _ 0 Hbs) as Ec.
  erewrite classify_plug in Ec; [ | exact Hwf | reflexivity ].
  rewrite classify_alloc in Ec. discriminate Ec.
Qed.

Local Ltac acc_frame HwfE Hh0 :=
  left; split;
  [ intros ? ? ? ? Hc; discriminate Hc
  | intros fresh;
    rewrite (classify_plug fresh _ _ _ HwfE
               (stepf_go_head_step fresh _ _ Hh0));
    eapply classify_head_frame;
      [ exact Hh0 | intros ? ? ? ? Hc; discriminate Hc ] ].

(* The head-level split: a head contraction under a well-formed spine *)
(* is a frame contraction or a boundary event, never both.            *)
Lemma head_step_accounting : forall E r r',
  ectx_wf E ->
  r -->h r' ->
  (frame_redex r /\
   forall fresh, classify fresh (plug E r) = Some sc_frame)
  \/
  (exists ch v,
     boundary_step (plug E r) (plug E r') ch v /\
     forall fresh, classify fresh (plug E r) = Some (sc_boundary ch v)).
Proof.
  intros E r r' HwfE Hh.
  pose proof Hh as Hh0.
  destruct Hh;
    [ acc_frame HwfE Hh0
    | acc_frame HwfE Hh0
    | acc_frame HwfE Hh0
    | acc_frame HwfE Hh0
    | acc_frame HwfE Hh0
    | (* H_Return *)
      right; exists handler_body_result_out, v;
      split;
      [ apply BS_Return; assumption
      | intros fresh; eapply classify_event; apply BS_Return; assumption ]
    | (* H_Perform *)
      right; exists operation_argument_in, v;
      split;
      [ eapply BS_Perform; eassumption
      | intros fresh; eapply classify_event; eapply BS_Perform; eassumption ] ].
Qed.

(* ------------------------------------------------------------------ *)
(* THE COMPLETENESS THEOREM: every step is a frame step (shared       *)
(* context, delimiter spine above the contraction unchanged), a       *)
(* fresh-delimiter allocation, or exactly one boundary event.  Each   *)
(* arm carries its classifier equation, so the arms are mutually      *)
(* exclusive: [classify] is a function, and no step can satisfy two   *)
(* arms at once.                                                      *)
(* ------------------------------------------------------------------ *)
Theorem step_boundary_accounting : forall t u,
  t ==> u ->
  (* (i) frame step *)
  (exists E r r',
      ectx_wf E /\ t = plug E r /\ u = plug E r' /\
      r -->h r' /\ frame_redex r /\
      forall fresh, classify fresh t = Some sc_frame)
  \/
  (* (ii) fresh-delimiter allocation *)
  (exists E E_tag Ts T_B T_R op_bodies body m,
      ectx_wf E /\
      t = plug E (term_handle E_tag Ts T_B T_R op_bodies body) /\
      u = plug E (term_handler_m m T_B T_R
             (subst_tm 0 (term_cap E_tag m Ts T_R op_bodies) body)) /\
      ~ In m (markers_in t) /\
      forall fresh, classify fresh t = Some sc_alloc)
  \/
  (* (iii) exactly one boundary event *)
  (exists ch v,
      boundary_step t u ch v /\
      forall fresh, classify fresh t = Some (sc_boundary ch v)).
Proof.
  intros t u Hstep.
  inversion Hstep; subst.
  - (* S_step *)
    match goal with
    | HwfE : ectx_wf _, Hh : _ -->h _ |- _ =>
        destruct (head_step_accounting _ _ _ HwfE Hh)
          as [[Hfr Hcl] | (ch & v & Hbs & Hcl)]
    end.
    + left. do 3 eexists.
      split; [eassumption|]. split; [reflexivity|]. split; [reflexivity|].
      split; [eassumption|]. split; [exact Hfr|]. exact Hcl.
    + right; right. exists ch, v. split; [exact Hbs | exact Hcl].
  - (* S_HandleCtx *)
    right; left. do 8 eexists.
    split; [eassumption|]. split; [reflexivity|]. split; [reflexivity|].
    split; [eassumption|].
    intros fresh.
    erewrite classify_plug; [ | eassumption | reflexivity ].
    apply classify_alloc.
Qed.

(* Source-facing form: along any execution of a well-typed source     *)
(* program, every transition is a frame step, an allocation, or a     *)
(* boundary event whose crossing value is typed at its channel's      *)
(* declared (escapable) type — the accounting theorem composed with   *)
(* the guarded-channel guarantee.                                     *)
Corollary source_step_accounting : forall Γ t T u u',
  eval_ctx Γ ->
  has_rt_marker t = false ->
  Γ ⊢ₜ t : T ->
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
      boundary_channel_typed Γ u u' ch v).
Proof.
  intros Γ t T u u' Hec Hsrc Hty Hms Hstep.
  destruct (step_boundary_accounting _ _ Hstep)
    as [ (E & r & r' & HwfE & Ht & Hu & Hh & Hfr & _)
       | [ (E & E_tag & Ts & T_B & T_R & ob & body & m & HwfE & Ht & Hu & Hm & _)
         | (ch & v & Hbs & _) ] ].
  - left. exists E, r, r'. repeat split; assumption.
  - right; left. exists E, E_tag, Ts, T_B, T_R, ob, body, m.
    repeat split; assumption.
  - right; right. exists ch, v. split; [exact Hbs|].
    eapply source_boundary_step_noloc; eassumption.
Qed.
