Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
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
Require Import Boundary.
Require Import BoundaryStep.
Require Import Stepf.
Require Import Examples.
Require Import ExamplesTactics.
Require Import ExamplesProofs.

Import CoreNotation.

(* ================================================================== *)
(* The safety capstones, instantiated on concrete example programs.   *)
(*                                                                    *)
(* [source_type_soundness] and the escape theorems quantify over any  *)
(* well-typed marker-free program under an [eval_ctx]; here they are  *)
(* applied to the example suite's own contexts and programs, so the   *)
(* end-to-end guarantees are witnessed on runnable code.              *)
(* ================================================================== *)

(* The example contexts hold only data-constructor and effect         *)
(* declarations, with closed schemas — i.e. they are eval_ctxs.       *)
Lemma eval_ctx_data_ctx : eval_ctx data_ctx.
Proof.
  unfold data_ctx.
  repeat first
    [ apply ec_nil
    | apply ec_ctor;
      [ cbn; repeat split; try lia
      | cbn; repeat split; try lia
      | cbn; repeat split; try lia
      | ]
    | apply ec_eff;
      [ cbv; lia
      | repeat constructor
      | ] ].
Qed.

Lemma eval_ctx_full_ctx : eval_ctx full_ctx.
Proof.
  unfold full_ctx, data_ctx, effect_ctx. cbn [List.app].
  repeat first
    [ apply ec_nil
    | apply ec_ctor;
      [ cbn; repeat split; try lia
      | cbn; repeat split; try lia
      | cbn; repeat split; try lia
      | ]
    | apply ec_eff;
      [ cbv; lia
      | repeat constructor
      | ] ].
Qed.

(* Type soundness, witnessed: no state reachable from the Reader      *)
(* example is stuck.                                                  *)
Theorem reader_example_safe : forall u,
  multi_step reader_example u -> ~ stuck u.
Proof.
  intros u Hms.
  apply (source_type_soundness full_ctx reader_example u (T_Nat `Lf)
           eval_ctx_full_ctx).
  - vm_compute; reflexivity.
  - exact typed_reader_example_proof.
  - exact Hms.
Qed.

(* Escape safety, witnessed: a local File can never be subsumed to a  *)
(* free (escapable) File.                                             *)
Theorem file_local_confined : ~ (data_ctx ⊢ T_File `Ll <:: T_File `Lf).
Proof.
  unfold T_File.
  apply (local_data_not_escapes data_ctx file_tag []).
  - exact eval_ctx_data_ctx.
  - cbn; reflexivity.
  - unfold file_tag, any_tag. congruence.
Qed.

(* Boundary impermeability, witnessed: along any execution of the     *)
(* Reader example, every value crossing a handler boundary is typed   *)
(* at THE type its channel declares — the delimiter's own declared    *)
(* answer type T_B when the result leaves (return-out channel), the   *)
(* operation's instantiated signature when the argument enters        *)
(* (operation-in channel) — and that pinned type is escapable         *)
(* (noloc).  The statement exposes the per-channel conclusion of the  *)
(* underlying theorem unchanged; no channel-agnostic weakening.       *)
Theorem reader_example_boundary_noloc : forall u v,
  multi_step reader_example u ->
  boundary_crossing u v ->
  (* return-out channel: v leaves the delimiter at the delimiter's    *)
  (* own declared answer type T_B.                                    *)
  (exists E m T_B T_R,
     u = plug E (term_handler_m m T_B T_R v) /\
     full_ctx ⊢ₜ v : T_B /\
     full_ctx ⊢ₗ lt_of_ty_G full_ctx T_B <: lt_free)
  \/
  (* operation-in channel: v enters the handler clause at the         *)
  (* operation's instantiated signature.                              *)
  (exists E E_tag m Ts T_B T_R op_bodies op Ss A P n_α ops n_β sig ret sig_inst,
     u = plug E (term_handler_m m T_B T_R
           (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v))) /\
     ctx_lookup_eff full_ctx E_tag = Some (n_α, ops) /\
     nth_error ops op = Some (n_β, sig, ret) /\
     sig_inst = inst_op_all_args n_α Ts n_β Ss sig /\
     full_ctx ⊢ₜ v : sig_inst /\
     full_ctx ⊢ₗ lt_of_ty_G full_ctx sig_inst <: lt_free).
Proof.
  intros u v Hms Hbc.
  assert (Hsrc : has_rt_marker reader_example = false) by (vm_compute; reflexivity).
  exact (source_handler_boundary_noloc full_ctx reader_example (T_Nat `Lf) u v
           eval_ctx_full_ctx Hsrc typed_reader_example_proof Hms Hbc).
Qed.

(* ================================================================== *)
(* The two-operation State example, witnessed.  [state_ctx]           *)
(* extends [full_ctx] with the two-operation State declaration        *)
(* (get : Unit -> s at index 0, put : s -> Unit at index 1); it is    *)
(* still an eval_ctx, so every source-facing capstone applies.        *)
(* ================================================================== *)

Lemma eval_ctx_state_ctx : eval_ctx state_ctx.
Proof.
  unfold state_ctx, state_sig, full_ctx, data_ctx, effect_ctx.
  cbn [List.app].
  repeat first
    [ apply ec_nil
    | apply ec_ctor;
      [ cbn; repeat split; try lia
      | cbn; repeat split; try lia
      | cbn; repeat split; try lia
      | ]
    | apply ec_eff;
      [ cbv; lia
      | repeat constructor
      | ] ].
Qed.

(* Type soundness, witnessed on the two-operation example: no state   *)
(* reachable from the State example is stuck.                         *)
Theorem state_example_safe : forall u,
  multi_step state_example u -> ~ stuck u.
Proof.
  intros u Hms.
  apply (source_type_soundness state_ctx state_example u (T_Nat `Lf)
           eval_ctx_state_ctx).
  - vm_compute; reflexivity.
  - exact typed_state_example_proof.
  - exact Hms.
Qed.

(* Capability confinement, witnessed: no state reachable from the     *)
(* State example exposes a capability outside its delimiter.          *)
Theorem state_example_cap_confined :
  forall E E_tag m Ts T_R op_bodies,
    multi_step state_example (plug E (term_cap E_tag m Ts T_R op_bodies)) ->
    ~ pure_ectx_m m E.
Proof.
  intros E E_tag m Ts T_R op_bodies Hms.
  apply (source_capability_never_exposed state_ctx state_example
           E E_tag m Ts T_R op_bodies (T_Nat `Lf) eval_ctx_state_ctx).
  - vm_compute; reflexivity.
  - exact typed_state_example_proof.
  - exact Hms.
Qed.

(* Boundary impermeability, witnessed on a CONCRETE EVENT.  The other *)
(* boundary witnesses are conditional on an abstract crossing; here   *)
(* the event is exhibited.  After 13 steps of the State run (the      *)
(* state is stepf_run 13 of the program, so reachability is           *)
(* stepf_run_sound plus vm_compute) the delimiter's body is the       *)
(* state-passing lambda λs.3, and the next step is the H_Return       *)
(* collapse: a real [boundary_step] on the handler_body_result_out    *)
(* channel whose crossing value is that lambda.  The channel typing   *)
(* pins the value at the delimiter's own declared answer type         *)
(* T_B = Nat -{free}-> Nat, which is noloc.                           *)
Theorem state_example_boundary_return_event :
  boundary_step
    (plug (EC_app1 EC_hole three_v)
       (term_handler_m 1
          (T_Nat `Lf -{ `Lf }-> T_Nat `Lf)
          (T_Nat `Lf -{ `Ll }-> T_Nat `Lf)
          (λ: T_Nat `Lf \\ three_v)))
    (plug (EC_app1 EC_hole three_v) (λ: T_Nat `Lf \\ three_v))
    handler_body_result_out
    (λ: T_Nat `Lf \\ three_v) /\
  boundary_channel_typed state_ctx
    (plug (EC_app1 EC_hole three_v)
       (term_handler_m 1
          (T_Nat `Lf -{ `Lf }-> T_Nat `Lf)
          (T_Nat `Lf -{ `Ll }-> T_Nat `Lf)
          (λ: T_Nat `Lf \\ three_v)))
    (plug (EC_app1 EC_hole three_v) (λ: T_Nat `Lf \\ three_v))
    handler_body_result_out
    (λ: T_Nat `Lf \\ three_v).
Proof.
  split.
  - apply BS_Return; [ solve_value | repeat constructor ].
  - eapply (source_boundary_step_noloc state_ctx state_example (T_Nat `Lf)).
    + exact eval_ctx_state_ctx.
    + vm_compute; reflexivity.
    + exact typed_state_example_proof.
    + (* reachability, computed: the state is stepf_run 13 of the run *)
      replace (plug (EC_app1 EC_hole three_v)
                 (term_handler_m 1
                    (T_Nat `Lf -{ `Lf }-> T_Nat `Lf)
                    (T_Nat `Lf -{ `Ll }-> T_Nat `Lf)
                    (λ: T_Nat `Lf \\ three_v)))
        with (stepf_run 13 state_example)
        by (vm_compute; reflexivity).
      apply stepf_run_sound.
    + apply BS_Return; [ solve_value | repeat constructor ].
Qed.

(* ------------------------------------------------------------------ *)
(* The operation-in channel, witnessed on a CONCRETE EVENT.  After 1  *)
(* step of the State run (S_Handle minted marker 1), the reached      *)
(* state IS a perform-redex under its own delimiter: the body's       *)
(* first get (operation index 0) sits, across the pure let frame P,   *)
(* directly under handler_m 1, inside the outer application frame E.  *)
(* The pieces of that decomposition, named:                           *)
(* ------------------------------------------------------------------ *)

(* The capability S_Handle substituted for the handled variable.      *)
Definition state_example_cap : term :=
  term_cap State_tag 1 [T_Nat `Lf]
    (T_Nat `Lf -{ `Ll }-> T_Nat `Lf)
    [(0, state_get_body); (0, state_put_body)].

(* The rest of the delimited body: the put and the second get.        *)
Definition state_example_perform_rest : term :=
  let: T_Unit <- term_perform state_example_cap 1 [] T_Unit three_v in
  let: T_Nat `Lf <- term_perform state_example_cap 0 [] (T_Nat `Lf) unit_v in
  λ: T_Nat `Lf \\ $$ 1.

(* The pure prefix P between delimiter and redex: the first let's     *)
(* argument frame.                                                    *)
Definition state_example_perform_P : ectx :=
  EC_app2 (λ: T_Nat `Lf \\ state_example_perform_rest) EC_hole.

(* The reached state, as the BS_Perform redex decomposition — equal   *)
(* to stepf_run 1 state_example by computation (see the proof).       *)
Definition state_example_perform_state : term :=
  plug (EC_app1 EC_hole two_v)
    (term_handler_m 1
       (T_Nat `Lf -{ `Lf }-> T_Nat `Lf)
       (T_Nat `Lf -{ `Ll }-> T_Nat `Lf)
       (plug state_example_perform_P
          (term_perform state_example_cap 0 [] (T_Nat `Lf) unit_v))).

(* The reduct: H_Perform's contractum verbatim — the get clause with  *)
(* the argument and the reified resumption substituted in.            *)
Definition state_example_perform_next : term :=
  plug (EC_app1 EC_hole two_v)
    (subst_list_tm
       [unit_v;
        term_lam
          (term_handler_m 1
             (T_Nat `Lf -{ `Lf }-> T_Nat `Lf)
             (T_Nat `Lf -{ `Ll }-> T_Nat `Lf)
             (plug (shift_ectx_tm 1 0 state_example_perform_P) (term_var 0)))
          (T_Nat `Lf)]
       (subst_list_ty_in_tm [] state_get_body)).

(* Boundary impermeability, witnessed on a CONCRETE operation-in      *)
(* EVENT: a real [boundary_step] on the operation_argument_in channel *)
(* fires from the reached state (reachability is stepf_run_sound      *)
(* plus vm_compute), and the event-tied channel typing pins its       *)
(* crossing value unit_v at get's instantiated signature Unit, which  *)
(* is noloc.  Companion of state_example_boundary_return_event on     *)
(* the other guarded channel.                                         *)
Theorem state_example_boundary_perform_event :
  boundary_step state_example_perform_state state_example_perform_next
    operation_argument_in unit_v /\
  boundary_channel_typed state_ctx
    state_example_perform_state state_example_perform_next
    operation_argument_in unit_v.
Proof.
  assert (Hbs : boundary_step state_example_perform_state
                  state_example_perform_next operation_argument_in unit_v).
  { unfold state_example_perform_state, state_example_perform_next,
      state_example_cap.
    eapply BS_Perform;
      [ solve_value | repeat constructor | repeat constructor
      | repeat constructor | reflexivity ]. }
  split; [exact Hbs|].
  eapply (source_boundary_step_noloc state_ctx state_example (T_Nat `Lf)).
  - exact eval_ctx_state_ctx.
  - vm_compute; reflexivity.
  - exact typed_state_example_proof.
  - (* reachability, computed: the state is stepf_run 1 of the run    *)
    replace state_example_perform_state with (stepf_run 1 state_example)
      by (vm_compute; reflexivity).
    apply stepf_run_sound.
  - exact Hbs.
Qed.

(* ------------------------------------------------------------------ *)
(* Non-vacuity of the confinement witnesses: the conditional          *)
(* theorems above ([state_example_cap_confined]) quantify over any    *)
(* reachable capability decomposition; here is a CONCRETE one.  The   *)
(* same reached state stepf_run 1, decomposed one frame deeper —      *)
(* down to the capability itself in evaluation position (the          *)
(* perform's receiver) — exhibits a reachable state that really       *)
(* contains a capability, and its surrounding context really          *)
(* contains the handler_m 1 frame: it is NOT marker-1-pure, exactly   *)
(* as confinement demands.                                            *)
(* ------------------------------------------------------------------ *)

(* The context around the capability: outer application frame,        *)
(* delimiter frame, pure let frame, perform-receiver frame.           *)
Definition state_example_cap_ectx : ectx :=
  EC_app1
    (EC_handler_m 1
       (T_Nat `Lf -{ `Lf }-> T_Nat `Lf)
       (T_Nat `Lf -{ `Ll }-> T_Nat `Lf)
       (EC_app2 (λ: T_Nat `Lf \\ state_example_perform_rest)
          (EC_perform_r EC_hole 0 [] (T_Nat `Lf) unit_v)))
    two_v.

Theorem state_example_cap_reachable :
  multi_step state_example (plug state_example_cap_ectx state_example_cap) /\
  plug state_example_cap_ectx state_example_cap = stepf_run 1 state_example /\
  ~ pure_ectx_m 1 state_example_cap_ectx.
Proof.
  split; [|split].
  - (* reachability, computed *)
    replace (plug state_example_cap_ectx state_example_cap)
      with (stepf_run 1 state_example) by (vm_compute; reflexivity).
    apply stepf_run_sound.
  - vm_compute; reflexivity.
  - (* the context is not marker-1-pure: it contains handler_m 1      *)
    intro Hp.
    inversion Hp; subst.
    match goal with
    | H : pure_ectx_m _ (EC_handler_m _ _ _ _) |- _ => inversion H; subst
    end.
    congruence.
Qed.

(* ================================================================== *)
(* The delegating-handler example, witnessed: an operation clause     *)
(* that itself performs an operation of the OUTER handler             *)
(* ([delegate_example] — two Reader delimiters, same effect tag,      *)
(* told apart by markers).                                            *)
(* ================================================================== *)

(* Type soundness: no state reachable from the delegating run is      *)
(* stuck — in particular the clause's own perform, fired from where   *)
(* the inner delimiter used to stand, always finds the outer one.     *)
Theorem delegate_example_safe : forall u,
  multi_step delegate_example u -> ~ stuck u.
Proof.
  intros u Hms.
  apply (source_type_soundness full_ctx delegate_example u (T_Nat `Lf)
           eval_ctx_full_ctx).
  - vm_compute; reflexivity.
  - exact typed_delegate_example_proof.
  - exact Hms.
Qed.

(* Capability confinement: neither capability — the inner one nor the *)
(* outer one the clause delegates through — is ever exposed outside   *)
(* its delimiter.                                                     *)
Theorem delegate_example_cap_confined :
  forall E E_tag m Ts T_R op_bodies,
    multi_step delegate_example (plug E (term_cap E_tag m Ts T_R op_bodies)) ->
    ~ pure_ectx_m m E.
Proof.
  intros E E_tag m Ts T_R op_bodies Hms.
  apply (source_capability_never_exposed full_ctx delegate_example
           E E_tag m Ts T_R op_bodies (T_Nat `Lf) eval_ctx_full_ctx).
  - vm_compute; reflexivity.
  - exact typed_delegate_example_proof.
  - exact Hms.
Qed.

(* Boundary impermeability: every value crossing EITHER of the two    *)
(* delimiters along any run — including the delegated ask's argument  *)
(* and answer — is typed at an escapable (noloc) type.                *)
Theorem delegate_example_boundary_noloc : forall u v,
  multi_step delegate_example u ->
  boundary_crossing u v ->
  exists S,
    full_ctx ⊢ₜ v : S /\ full_ctx ⊢ₗ lt_of_ty_G full_ctx S <: lt_free.
Proof.
  intros u v Hms Hbc.
  assert (Hsrc : has_rt_marker delegate_example = false) by (vm_compute; reflexivity).
  destruct (source_handler_boundary_noloc full_ctx delegate_example (T_Nat `Lf) u v
              eval_ctx_full_ctx Hsrc typed_delegate_example_proof Hms Hbc)
    as [ (E & m & T_B & T_R & _ & HtyS & Hnl)
       | (E & E_tag & m & Ts & T_B & T_R & op_bodies & op & Ss & A & P
          & n_α & ops & n_β & sig & ret & sig_inst
          & _ & _ & _ & _ & HtyS & Hnl) ];
    eexists; eauto.
Qed.
