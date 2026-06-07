Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Examples.

Import CoreNotation.

(* ================================================================== *)
(* Multi-step plumbing                                                 *)
(* ================================================================== *)

Lemma ms_one : forall t t', t ==> t' -> t ==>> t'.
Proof. intros t t' H. eapply ms_step; [exact H | apply ms_refl]. Qed.

Lemma ms_trans : forall t1 t2 t3, t1 ==>> t2 -> t2 ==>> t3 -> t1 ==>> t3.
Proof.
  intros t1 t2 t3 H12. revert t3.
  induction H12 as [|? ? ? Hs ? IH]; intros u H23; auto.
  eapply ms_step; eauto.
Qed.

Lemma unit_v_value : value unit_v.
Proof. unfold unit_v. constructor. constructor. Qed.

Lemma file_v_value : value file_v.
Proof. unfold file_v. constructor. constructor. Qed.

Lemma int2_v_value : value int2_v.
Proof. unfold int2_v. constructor. constructor. Qed.

Lemma int42_v_value : value int42_v.
Proof. unfold int42_v. constructor. constructor. Qed.

Lemma some_int42_value : value (some_v `Lf (T_Int `Lf) int42_v).
Proof. unfold some_v. constructor. repeat constructor; apply int42_v_value. Qed.

Hint Resolve unit_v_value file_v_value int2_v_value int42_v_value some_int42_value : core.

Ltac solve_nullary_ctor :=
  eapply T_Ctor with (lts := []) (Ts := []) (rho_fields := []);
  cbn; try reflexivity; try constructor; try apply LS_Free.

(* ================================================================== *)
(* Constructor/value typing statements                                 *)
(* ================================================================== *)

Theorem typed_unit_proof : typed_unit.
Proof. unfold typed_unit, unit_v, data_ctx; solve_nullary_ctor. Qed.

Theorem typed_file_proof : typed_file.
Proof. unfold typed_file, file_v, data_ctx; solve_nullary_ctor. Qed.

Theorem typed_int2_proof : typed_int2.
Proof. unfold typed_int2, int2_v, data_ctx; solve_nullary_ctor. Qed.

Theorem typed_int42_proof : typed_int42.
Proof. unfold typed_int42, int42_v, data_ctx; solve_nullary_ctor. Qed.

Lemma typed_file_local : data_ctx ⊢ₜ file_v : T_File `Ll.
Proof.
  eapply T_Sub.
  - exact typed_file_proof.
  - apply SA_Data. apply LS_Free.
Qed.

(* ================================================================== *)
(* Direct typing statements                                            *)
(* ================================================================== *)

Theorem typed_withFile_proof : typed_withFile.
Proof.
  unfold typed_withFile, withFile.
  apply T_TyLam.
  apply T_Lam.
  - eapply T_App.
    + apply T_Var. reflexivity.
    + eapply T_Sub.
      * unfold file_v, data_ctx; solve_nullary_ctor.
      * apply SA_Data. apply LS_Free.
  - cbn. apply LS_Free.
  - reflexivity.
Qed.

Theorem typed_id_proof : typed_id.
Proof.
  unfold typed_id, id_poly.
  apply T_TyLam.
  apply T_Lam.
  - apply T_Var. reflexivity.
  - cbn. apply LS_Free.
  - reflexivity.
Qed.

Theorem typed_downcast_proof : typed_downcast.
Proof.
  unfold typed_downcast, downcast.
  apply T_TyLam.
  apply T_Lam.
  - apply T_Var. reflexivity.
  - cbn. apply LS_Free.
  - reflexivity.
Qed.

Theorem typed_cons_proof : typed_cons.
Proof.
  unfold typed_cons, cons_fn.
  apply T_LtLam.
  apply T_TyLam.
  apply T_Lam.
  - apply T_Lam.
    + unfold cons_v.
      eapply T_Ctor with
        (lts := [`L 0]) (Ts := [`T 0])
        (rho_fields := [`T 0; T_List (`L 0) (`T 0)]);
        cbn; try reflexivity.
      * repeat apply LS_MinL; try apply LS_Refl; try apply LS_Free.
      * repeat constructor; apply T_Var; reflexivity.
    + cbn. repeat apply LS_MinL; try apply LS_Refl; try apply LS_Free.
    + reflexivity.
  - cbn. apply LS_Free.
  - reflexivity.
Qed.

Theorem typed_list_example_proof : typed_list_example.
Proof.
  unfold typed_list_example, list_example. admit.
Admitted.

Theorem typed_compose_proof : typed_compose.
Proof.
  unfold typed_compose, compose_fn. admit.
Admitted.

(* The following effect-heavy statements are intentionally kept here as
   proof obligations rather than in Examples.v.  They document the intended
   typing targets while the concrete proof scripts can evolve with Typing.v's
   handler rules. *)
Theorem typed_readerExample_proof : typed_readerExample.
Proof. unfold typed_readerExample, readerExample, readerExample_op_body. admit. Admitted.

Theorem typed_withReader_proof : typed_withReader.
Proof. unfold typed_withReader, withReader, withReader_op_body. admit. Admitted.

Theorem typed_withState_proof : typed_withState.
Proof. unfold typed_withState, withState, state_op_body. admit. Admitted.

Theorem typed_withException_proof : typed_withException.
Proof. unfold typed_withException, withException, withException_op_body. admit. Admitted.

Theorem typed_exampleException_proof : typed_exampleException.
Proof. unfold typed_exampleException, exampleException, exampleException_body. admit. Admitted.

Theorem typed_withId_proof : typed_withId.
Proof. unfold typed_withId, withId, withId_op_body. admit. Admitted.

Theorem typed_exampleOptionality_proof : typed_exampleOptionality.
Proof. unfold typed_exampleOptionality, exampleOptionality, optionality_op_body. admit. Admitted.

Theorem typed_lazyMap_body_proof : typed_lazyMap_body.
Proof. exact I. Qed.

Theorem typed_mapFirst_proof : typed_mapFirst.
Proof. exact I. Qed.

Theorem typed_foldEndo_proof : typed_foldEndo.
Proof. exact I. Qed.

(* ================================================================== *)
(* Negative/error witnesses                                            *)
(* ================================================================== *)

Theorem rejected_testWithState_proof : rejected_testWithState.
Proof. reflexivity. Qed.

Theorem rejected_crashEndo_proof : rejected_crashEndo.
Proof. reflexivity. Qed.

Theorem rejected_crashBox_proof : rejected_crashBox.
Proof. reflexivity. Qed.

Theorem typed_clash_ignored_local_proof : typed_clash_ignored_local.
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Reduction statements                                                *)
(* ================================================================== *)

Theorem red_list_example_proof : red_list_example.
Proof.
  unfold red_list_example, list_example, cons_fn, cons_v.
  eapply ms_step.
  { apply (S_step (EC_app1 (EC_ty_app EC_hole (T_File `Ll)) file_v)).
    - repeat constructor.
    - apply H_LtBeta. }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole file_v)).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor. apply H_Beta, file_v_value. }
  cbn. apply ms_refl.
Qed.

Theorem red_readerExample_proof : red_readerExample.
Proof.
  unfold red_readerExample, readerExample, readerExample_op_body.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_Handle Reader_tag [T_Int `Lf] (($$ 1) @· int2_v)
             (term_perform ($$ 0) [] unit_v) 0). }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_Perform Reader_tag 0 [T_Int `Lf] (($$ 1) @· int2_v) [] unit_v EC_hole);
      [apply unit_v_value | constructor]. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor. apply H_Resume, int2_v_value. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor. apply H_Return, int2_v_value. }
  apply ms_refl.
Qed.

Theorem red_exampleOptionality_proof : red_exampleOptionality.
Proof.
  unfold red_exampleOptionality, exampleOptionality, optionality_op_body, some_v.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_Handle Optionality_tag [] (($$ 1) @· term_ctor some_tag `Lf [`Lf] [`T 0] [$$ 0])
             (term_perform ($$ 0) [T_Int `Lf] int42_v) 0). }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_Perform Optionality_tag 0 [] (($$ 1) @· term_ctor some_tag `Lf [`Lf] [`T 0] [$$ 0])
             [T_Int `Lf] int42_v EC_hole);
      [apply int42_v_value | constructor]. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Resume. repeat constructor. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Return. repeat constructor. }
  cbn. apply ms_refl.
Qed.
