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
Require Import Soundness.
Require Import Escape.
Require Import Boundary.
Require Import Examples.
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
Theorem readerExample_safe : forall u,
  multi_step readerExample u -> ~ stuck u.
Proof.
  intros u Hms.
  apply (source_type_soundness full_ctx readerExample u (T_Nat `Lf)
           eval_ctx_full_ctx).
  - vm_compute; reflexivity.
  - exact typed_readerExample_proof.
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
Theorem readerExample_boundary_noloc : forall u v,
  multi_step readerExample u ->
  boundary_crossing u v ->
  exists S,
    full_ctx ⊢ₜ v : S /\ full_ctx ⊢ₗ lt_of_ty_G full_ctx S <: lt_free.
Proof.
  intros u v Hms Hbc.
  apply (source_handler_boundary_noloc full_ctx readerExample (T_Nat `Lf) u v
           eval_ctx_full_ctx).
  - vm_compute; reflexivity.
  - exact typed_readerExample_proof.
  - exact Hms.
  - exact Hbc.
Qed.
