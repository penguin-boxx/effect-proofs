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

(* The example contexts hold only data-constructor and effect          *)
(* declarations, with closed schemas — i.e. they are eval_ctxs.        *)
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

(* Type soundness, witnessed: no state reachable from the State        *)
(* example is stuck.                                                   *)
Theorem withState_example_safe : forall u,
  multi_step withState_example u -> ~ stuck u.
Proof.
  intros u Hms.
  apply (source_type_soundness full_ctx withState_example u (T_Nat `Lf)
           eval_ctx_full_ctx).
  - vm_compute; reflexivity.
  - exact typed_withState_example_proof.
  - exact Hms.
Qed.

(* A second witness, on the Reader example. *)
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

(* Capability confinement, witnessed: no state reachable from the      *)
(* State example exposes a capability outside its delimiter.           *)
Theorem withState_example_cap_confined :
  forall E E_tag m Ts T_R op_bodies,
    multi_step withState_example (plug E (term_cap E_tag m Ts T_R op_bodies)) ->
    ~ pure_ectx_m m E.
Proof.
  intros E E_tag m Ts T_R op_bodies Hms.
  apply (source_capability_never_exposed full_ctx withState_example
           E E_tag m Ts T_R op_bodies (T_Nat `Lf) eval_ctx_full_ctx).
  - vm_compute; reflexivity.
  - exact typed_withState_example_proof.
  - exact Hms.
Qed.

(* Escape safety, witnessed: a local File can never be subsumed to a   *)
(* free (escapable) File.                                              *)
Theorem file_local_confined : ~ (data_ctx ⊢ T_File `Ll <:: T_File `Lf).
Proof.
  unfold T_File.
  apply (local_data_not_escapes data_ctx file_tag []).
  - exact eval_ctx_data_ctx.
  - cbn; reflexivity.
  - unfold file_tag, any_tag. congruence.
Qed.

(* Boundary impermeability, witnessed: along any execution of the      *)
(* Reader example, every value crossing a handler boundary — the       *)
(* operation argument entering, or the delimiter's result leaving —    *)
(* is typed at an escapable (noloc) type.                              *)
Theorem reader_example_boundary_noloc : forall u v,
  multi_step reader_example u ->
  boundary_crossing u v ->
  exists S,
    full_ctx ⊢ₜ v : S /\ full_ctx ⊢ₗ lt_of_ty_G full_ctx S <: lt_free.
Proof.
  intros u v Hms Hbc.
  assert (Hsrc : has_rt_cap reader_example = false) by (vm_compute; reflexivity).
  (* the strengthened theorem pins each channel's crossing type; the   *)
  (* example-facing statement keeps the channel-agnostic reading, so   *)
  (* project the pinned type out of whichever channel fired.           *)
  destruct (source_handler_boundary_noloc full_ctx reader_example (T_Nat `Lf) u v
              eval_ctx_full_ctx Hsrc typed_reader_example_proof Hms Hbc)
    as [ (E & m & T_B & T_R & _ & HtyS & Hnl)
       | (E & E_tag & m & Ts & T_B & T_R & op_bodies & op & Ss & A & P
          & n_α & ops & n_β & sig & ret & sig_inst
          & _ & _ & _ & _ & HtyS & Hnl) ];
    eexists; eauto.
Qed.

(* ================================================================== *)
(* The two-operation StateM showcase, witnessed.  [statem_ctx]        *)
(* extends [full_ctx] with the two-operation StateM declaration        *)
(* (get : Unit -> s at index 0, put : s -> Unit at index 1); it is    *)
(* still an eval_ctx, so every source-facing capstone applies.        *)
(* ================================================================== *)

Lemma eval_ctx_statem_ctx : eval_ctx statem_ctx.
Proof.
  unfold statem_ctx, statem_sig, full_ctx, data_ctx, effect_ctx.
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

(* Type soundness, witnessed on the two-operation showcase: no state   *)
(* reachable from the StateM example is stuck.                         *)
Theorem statem_example_safe : forall u,
  multi_step statem_example u -> ~ stuck u.
Proof.
  intros u Hms.
  apply (source_type_soundness statem_ctx statem_example u (T_Nat `Lf)
           eval_ctx_statem_ctx).
  - vm_compute; reflexivity.
  - exact typed_statem_example_proof.
  - exact Hms.
Qed.

(* Capability confinement, witnessed: no state reachable from the      *)
(* StateM example exposes a capability outside its delimiter.          *)
Theorem statem_example_cap_confined :
  forall E E_tag m Ts T_R op_bodies,
    multi_step statem_example (plug E (term_cap E_tag m Ts T_R op_bodies)) ->
    ~ pure_ectx_m m E.
Proof.
  intros E E_tag m Ts T_R op_bodies Hms.
  apply (source_capability_never_exposed statem_ctx statem_example
           E E_tag m Ts T_R op_bodies (T_Nat `Lf) eval_ctx_statem_ctx).
  - vm_compute; reflexivity.
  - exact typed_statem_example_proof.
  - exact Hms.
Qed.

(* Boundary impermeability, witnessed on a CONCRETE EVENT.  The other  *)
(* boundary witnesses are conditional on an abstract crossing; here    *)
(* the event is exhibited.  After 13 steps of the StateM run (the      *)
(* state is stepf_run 13 of the program, so reachability is            *)
(* stepf_run_sound plus vm_compute) the delimiter's body is the        *)
(* state-passing lambda λs.3, and the next step is the H_Return        *)
(* collapse: a real [boundary_step] on the handler_body_result_out     *)
(* channel whose crossing value is that lambda.  The channel typing    *)
(* pins the value at the delimiter's own declared answer type          *)
(* T_B = Nat -{free}-> Nat, which is noloc.                            *)
Theorem statem_example_boundary_return_event :
  boundary_step
    (plug (EC_app1 EC_hole three_v)
       (term_handler_m 1
          (T_Nat `Lf -{ `Lf }-> T_Nat `Lf)
          (T_Nat `Lf -{ `Ll }-> T_Nat `Lf)
          (λ: T_Nat `Lf \\ three_v)))
    (plug (EC_app1 EC_hole three_v) (λ: T_Nat `Lf \\ three_v))
    handler_body_result_out
    (λ: T_Nat `Lf \\ three_v) /\
  boundary_channel_typed statem_ctx
    (plug (EC_app1 EC_hole three_v)
       (term_handler_m 1
          (T_Nat `Lf -{ `Lf }-> T_Nat `Lf)
          (T_Nat `Lf -{ `Ll }-> T_Nat `Lf)
          (λ: T_Nat `Lf \\ three_v)))
    handler_body_result_out
    (λ: T_Nat `Lf \\ three_v).
Proof.
  split.
  - apply BS_Return; [ solve_value | repeat constructor ].
  - eapply (source_boundary_step_noloc statem_ctx statem_example (T_Nat `Lf)).
    + exact eval_ctx_statem_ctx.
    + vm_compute; reflexivity.
    + exact typed_statem_example_proof.
    + (* reachability, computed: the state is stepf_run 13 of the run *)
      replace (plug (EC_app1 EC_hole three_v)
                 (term_handler_m 1
                    (T_Nat `Lf -{ `Lf }-> T_Nat `Lf)
                    (T_Nat `Lf -{ `Ll }-> T_Nat `Lf)
                    (λ: T_Nat `Lf \\ three_v)))
        with (stepf_run 13 statem_example)
        by (vm_compute; reflexivity).
      apply stepf_run_sound.
    + apply BS_Return; [ solve_value | repeat constructor ].
Qed.
