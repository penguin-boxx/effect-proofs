Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Decide.
Require Import Stepf.
Require Import Examples.
Require Import ExamplesTactics.

Import CoreNotation.

(* ================================================================== *)
(* Constructor/value typing statements                                *)
(* ================================================================== *)

Theorem typed_unit_proof : typed_unit.
Proof. unfold typed_unit, unit_v, data_ctx; solve_nullary_ctor. Qed.

Theorem typed_file_proof : typed_file.
Proof. unfold typed_file, file_v, data_ctx; solve_nullary_ctor. Qed.

Theorem typed_two_proof : typed_two.
Proof. unfold typed_two, data_ctx. solve_nat. Qed.

Theorem typed_three_proof : typed_three.
Proof. unfold typed_three, data_ctx. solve_nat. Qed.

Lemma typed_file_local : data_ctx ⊢ₜ file_v : T_File `Ll.
Proof.
  eapply T_Sub.
  - exact typed_file_proof.
  - apply SA_Data.
    + apply LS_Free. constructor.
    + constructor.
Qed.

(* ================================================================== *)
(* Direct typing statements                                           *)
(* ================================================================== *)

Theorem typed_withFile_proof : typed_withFile.
Proof.
  unfold typed_withFile, withFile.
  apply T_TyLam.
  - solve_wf.
  - solve_wf.
  - reflexivity.
  - apply T_Lam.
    + solve_wf.
    + solve_wf.
    + eapply T_App.
      * solve_var.
      * eapply T_Sub.
        -- unfold file_v, data_ctx; solve_nullary_ctor.
        -- apply SA_Data.
           ++ solve_free_sub.
           ++ constructor.
    + cbn. solve_free_sub.
Qed.

Theorem typed_id_proof : typed_id.
Proof.
  unfold typed_id, id_poly.
  apply T_TyLam.
  - solve_wf.
  - solve_wf.
  - reflexivity.
  - apply T_Lam.
    + solve_wf.
    + solve_wf.
    + solve_var.
    + cbn. solve_free_sub.
Qed.

(* ================================================================== *)
(* Example terms that USE the polymorphic functions:                  *)
(* typing + reduction.                                                *)
(* ================================================================== *)

Theorem typed_id_example_proof : typed_id_example.
Proof.
  unfold typed_id_example, id_example.
  pose proof typed_id_proof as H. unfold typed_id in H.
  eapply T_TyApp with (S := T_Unit) in H;
    [ | solve_wf | solve_any_sub ]. cbn in H.
  eapply T_App; [ exact H | exact typed_unit_proof ].
Qed.

Theorem typed_withFile_example_proof : typed_withFile_example.
Proof.
  unfold typed_withFile_example, withFile_example.
  pose proof typed_withFile_proof as H. unfold typed_withFile in H.
  eapply T_TyApp with (S := T_Unit) in H;
    [ | solve_wf | solve_any_sub ]. cbn in H.
  eapply T_App; [ exact H | ].
  open_lam (unfold unit_v; solve_nullary_ctor).
Qed.

Theorem red_id_example_proof : red_id_example.
Proof.
  unfold red_id_example, id_example, id_poly, unit_v.
  eapply ms_trans. { apply ms_app1; [ reflexivity | ]. apply ms_one. apply S_TyBeta. } cbn.
  apply ms_one. apply S_Beta. solve_value.
Qed.

Theorem red_withFile_example_proof : red_withFile_example.
Proof.
  unfold red_withFile_example, withFile_example, withFile, unit_v, file_v.
  eapply ms_trans. { apply ms_app1; [ reflexivity | ]. apply ms_one. apply S_TyBeta. } cbn.
  eapply ms_trans. { apply ms_one. apply S_Beta. solve_value. } cbn.
  apply ms_one. apply S_Beta. solve_value.
Qed.


Theorem typed_cons_proof : typed_cons.
Proof.
  unfold typed_cons, cons_fn.
  apply T_LtLam; [ solve_wf | reflexivity |].
  apply T_TyLam.
  - solve_wf.
  - solve_wf.
  - reflexivity.
  - apply T_Lam.
    + solve_wf.
    + solve_wf.
    + apply T_Lam.
      * solve_wf.
      * solve_wf.
      * unfold cons_v.
        eapply T_Ctor with
          (lts := []) (Ts := [`T 0])
          (rho_fields := [`T 0; T_List `Lf (`T 0)]);
          cbn; try reflexivity; try solve [solve_wf].
        -- solve_lt_sub.
        -- constructor.
        -- constructor; [solve_var|].
           constructor; [solve_var|constructor].
      * solve_capture.
    + cbn. solve_free_sub.
Qed.

Theorem typed_list_example_proof : typed_list_example.
Proof.
  unfold typed_list_example, list_example.
  pose proof typed_cons_proof as H. unfold typed_cons in H.
  eapply T_LtApp with (l := `Ll) in H; [ | solve_wf ]. cbn in H.
  eapply T_TyApp with (S := T_File `Ll) in H;
    [ | solve_wf | solve_any_sub ]. cbn in H.
  eapply T_App; [ exact H | ].
  apply typed_file_local.
Qed.

Theorem typed_compose_proof : typed_compose.
Proof.
  unfold typed_compose, compose_fn.
  apply T_LtLam; [ solve_wf | reflexivity |].
  apply T_LtLam; [ solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  open_lam.
  open_lam.
  open_lam.
  eapply T_App.
  - solve_var.
  - eapply T_App; solve_var.
Qed.

Theorem typed_succ_proof : typed_succ.
Proof.
  unfold typed_succ, succ_fn.
  apply T_Lam.
  - solve_wf.
  - solve_wf.
  - solve_nat.
  - cbn. solve_free_sub.
Qed.

(* Built forward: instantiate compose_fn's polymorphic type one elimination
   at a time (so each input type is concrete, avoiding higher-order
   inversion of [subst_ty]/[subst_lt_in_ty]), then apply to succ/succ/Zero. *)
Theorem typed_compose_example_proof : typed_compose_example.
Proof.
  unfold typed_compose_example, compose_example.
  pose proof typed_compose_proof as H. unfold typed_compose in H.
  eapply T_LtApp with (l := `Lf) in H; [ | solve_wf ]. cbn in H.
  eapply T_LtApp with (l := `Lf) in H; [ | solve_wf ]. cbn in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | solve_any_sub ]. cbn in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | solve_any_sub ]. cbn in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | solve_any_sub ]. cbn in H.
  eapply T_App; [ | solve_nat ].
  eapply T_App; [ | exact typed_succ_proof ].
  eapply T_App; [ exact H | exact typed_succ_proof ].
Qed.

Theorem red_compose_example_proof : red_compose_example.
Proof.
  unfold red_compose_example, compose_example, compose_fn, succ_fn, two_v, suc_v, zero_v.
  (* Phase 1: reduce the instantiated polymorphic head to the triple lambda,
     lifting each head beta through the [ty_app]/[lt_app] and outer [app] frames. *)
  eapply ms_trans.
  { apply ms_app1; [ reflexivity | ].
    apply ms_app1; [ reflexivity | ].
    apply ms_app1; [ reflexivity | ].
    eapply ms_trans.
    { do 3 apply ms_ty_app. apply ms_lt_app. apply ms_one. apply S_LtBeta. }
    cbn.
    eapply ms_trans. { do 3 apply ms_ty_app. apply ms_one. apply S_LtBeta. } cbn.
    eapply ms_trans. { do 2 apply ms_ty_app. apply ms_one. apply S_TyBeta. } cbn.
    eapply ms_trans. { apply ms_ty_app. apply ms_one. apply S_TyBeta. } cbn.
    apply ms_one. apply S_TyBeta. }
  cbn.
  (* Phase 2: apply the "+2" function to succ, succ, Zero. *)
  eapply ms_trans.
  { apply ms_app1; [ reflexivity | ].
    apply ms_app1; [ reflexivity | ].
    apply ms_one. apply S_Beta. solve_value. }
  cbn.
  eapply ms_trans.
  { apply ms_app1; [ reflexivity | ].
    apply ms_one. apply S_Beta. solve_value. }
  cbn.
  eapply ms_trans. { apply ms_one. apply S_Beta. solve_value. } cbn.
  (* now [succ (succ Zero)] — reduce the inner argument under [succ]. *)
  eapply ms_trans.
  { apply ms_app2; [ solve_value | reflexivity | ].
    apply ms_one. apply S_Beta. solve_value. }
  cbn.
  apply ms_one. apply S_Beta. solve_value.
Qed.

(* The following effect-heavy statements exercise the handler typing
   rules, on the closed examples and the polymorphic handlers alike. *)
Theorem typed_reader_example_proof : typed_reader_example.
Proof.
  unfold typed_reader_example, reader_example, reader_example_op_body.
  open_handle.
  - apply SA_Refl. solve_wf.
  - constructor; [| constructor].
    cbn. eapply T_App.
    + solve_var.
    + solve_nat.
  - cbn. solve_perform ltac:(unfold unit_v; solve_ctor).
Qed.

Theorem typed_withReader_proof : typed_withReader.
Proof.
  unfold typed_withReader, withReader.
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  open_lam.
  eapply T_Handle with
    (T_B := `T 1 -{ `Lf }-> `T 0)
    (T_R := `T 1 -{ `Ll }-> `T 0);
    try (cbn; reflexivity); try solve_wf; try (cbn; solve_lt_sub).
  - eapply SA_Fun; [ apply SA_Refl; solve_wf | solve_lt | apply SA_Refl; solve_wf ].
  - constructor; [| constructor].
    cbn. open_lam.
    eapply T_App with (A := `T 1) (l := `Ll) (B := `T 0).
    + eapply T_App with (A := `T 1) (l := `Ll) (B := `T 1 -{ `Ll }-> `T 0).
      * solve_var.
      * solve_var.
    + solve_var.
  - cbn. eapply T_App with (A := `T 0) (l := `Lf) (B := `T 1 -{ `Lf }-> `T 0).
    + open_lam.
      open_lam (solve_var).
    + eapply T_App with (A := T_Reader `Ll (`T 1)) (l := `Ll) (B := `T 0).
      * solve_var.
      * solve_var.
Qed.

Theorem typed_withException_proof : typed_withException.
Proof.
  unfold typed_withException, withException, withException_op_body.
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  open_lam.
  open_handle.
  - apply SA_Refl. solve_wf.
  - (* op_body: re-raise the caught value as [Error]. *)
    constructor; [| constructor].
    cbn. unfold error_v. solve_ctor.
  - (* body: wrap the handled computation's result in [Ok]. *)
    cbn. unfold ok_v.
    eapply T_Ctor; cbn; try reflexivity;
      repeat first [ solve_lt | progress solve_wf | progress cbn
                   | apply Forall_nil | apply Forall_cons | apply TS_Nil ].
    apply TS_Cons; [ | apply TS_Nil ].
    eapply T_App; [ solve_var | solve_var ].
Qed.

Theorem typed_exception_example_proof : typed_exception_example.
Proof.
  unfold typed_exception_example, exception_example, exception_example_body.
  eapply T_App with
    (A := T_Exception `Ll (T_Nat `Lf) -{ `Ll }-> T_File `Lf)
    (l := `Lf)
    (B := T_Result `Lf (T_Nat `Lf) (T_File `Lf)).
  eapply T_TyApp with
    (B := T_Any `Lf)
    (S := T_File `Lf)
    (U := (T_Exception `Ll (T_Nat `Lf) -{ `Ll }-> `T 0) -{ `Lf }->
          T_Result `Lf (T_Nat `Lf) (`T 0)).
  eapply T_TyApp with
    (B := T_Any `Lf)
    (S := T_Nat `Lf)
    (U := type_ty_all (T_Any `Lf)
            ((T_Exception `Ll (`T 1) -{ `Ll }-> `T 0) -{ `Lf }->
             T_Result `Lf (`T 1) (`T 0))).
  - exact typed_withException_proof.
  - solve_wf.
  - solve_any_sub.
  - solve_wf.
  - solve_any_sub.
  - cbn. open_lam.
    cbn. eapply T_Perform with (Ss := [T_File `Lf]).
    + solve_var.
    + cbn; reflexivity.
    + cbn; reflexivity.
    + reflexivity.
    + reflexivity.
    + solve_wf.
    + constructor; [cbn; solve_lt_sub | constructor].
    + cbn; reflexivity.
    + cbn; solve_lt_sub.
    + cbn; reflexivity.
    + solve_wf.
    + solve_nat.
Qed.

Theorem typed_withId_proof : typed_withId.
Proof.
  unfold typed_withId, withId, withId_op_body.
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  open_lam.
  open_handle.
  - apply SA_Refl. solve_wf.
  - constructor; [| constructor].
    cbn. eapply T_App; [ solve_var | solve_var ].
  - cbn. eapply T_App; [ solve_var | solve_var ].
Qed.

Theorem typed_optionality_example_proof : typed_optionality_example.
Proof.
  unfold typed_optionality_example, optionality_example, optionality_op_body.
  open_handle.
  - apply SA_Refl. solve_wf.
  - constructor; [| constructor].
    cbn. eapply T_App; [ solve_var | unfold some_v; solve_ctor ].
  - cbn. eapply T_Perform with (Ss := [T_Nat `Lf]).
    + solve_var.
    + cbn; reflexivity.
    + cbn; reflexivity.
    + reflexivity.
    + reflexivity.
    + solve_wf.
    + constructor; [cbn; solve_lt_sub | constructor].
    + cbn; reflexivity.
    + cbn; solve_lt_sub.
    + cbn; reflexivity.
    + solve_wf.
    + solve_nat.
Qed.

Theorem typed_lazyMap_body_proof : typed_lazyMap_body.
Proof.
  unfold typed_lazyMap_body, lazyMap_body, lazyMap_ctx.
  eapply T_Match with
    (Ts := [`T 1]) (Delta := `L 1) (arity := 0) (lts := [])
    (rho_fields := []) (scrut_result_ty := T_LazyList `Lf (`T 1))
    (result_tag := lazy_list_tag) (result_l := `Lf)
    (eta := T_LazyList (`L 2 +l `L 1) (`T 0))
    (elim_result := T_LazyList (`L 2 +l `L 1) (`T 0));
    cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt | solve_var ].
  - (* outer yes: LNil<b>, subsumed up to the joined lifetime *)
    eapply T_Sub.
    + eapply T_Ctor with
        (n_lt := 0) (n_ty := 1) (lts := []) (Ts := [`T 0])
        (sigma_fields := []) (result_ty_schema := T_LazyList `Lf (`T 0));
        cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt ];
        constructor.
    + apply SA_Data; [ solve_lt | solve_wf ].
  - (* outer no: the LCons match *)
    eapply T_Match with
      (Ts := [`T 1]) (Delta := `L 1) (arity := 2) (lts := lt_var_list 4)
      (rho_fields := [T_Unit -{ `L 2 }-> `T 1;
                      T_Unit -{ `L 1 }-> T_LazyList (`L 0) (`T 1)])
      (scrut_result_ty := T_LazyList (`L 1) (`T 1))
      (result_tag := lazy_list_tag) (result_l := `L 1)
      (eta := T_LazyList (`L 6 +l `L 5) (`T 0))
      (elim_result := T_LazyList (`L 2 +l `L 1) (`T 0));
      cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt | solve_var ].
    + (* inner yes: build LCons<b> with all four lifetimes = lf+la *)
      eapply T_Ctor with
        (n_lt := 4) (n_ty := 1)
        (lts := [`L 6 +l `L 5; `L 6 +l `L 5; `L 6 +l `L 5; `L 6 +l `L 5])
        (Ts := [`T 0])
        (sigma_fields := [ T_Unit -{ `L 2 }-> `T 0
                         ; T_Unit -{ `L 1 }-> T_LazyList (`L 0) (`T 0) ])
        (result_ty_schema := T_LazyList (`L 3) (`T 0));
        cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt_var ].
      * (* Forall (<: J) lts *)
        repeat (apply Forall_cons; [ solve_lt_var |]). apply Forall_nil.
      * (* typings: the field values *)
        constructor; [ | constructor; [ | constructor ] ].
        -- (* thunk1 = λ(). f (h ()) *)
           open_lam.
           eapply T_App; [ solve_var |].
           eapply T_App; [ solve_var |].
           solve_nullary_ctor.
        -- (* thunk2 = λ(). self (t ()) f *)
           open_lam.
           eapply T_App; [ | solve_var ].
           eapply T_App; [ solve_var |].
           eapply T_Sub.
           ++ eapply T_App; [ solve_var | solve_nullary_ctor ].
           ++ apply SA_Data; [ solve_lt_var | solve_wf ].
    + (* inner no: LNil<b>, subsumed *)
      eapply T_Sub.
      * eapply T_Ctor with
          (n_lt := 0) (n_ty := 1) (lts := []) (Ts := [`T 0])
          (sigma_fields := []) (result_ty_schema := T_LazyList `Lf (`T 0));
          cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt ];
          constructor.
      * apply SA_Data; [ solve_lt | solve_wf ].
Qed.

Theorem typed_mapFirst_proof : typed_mapFirst.
Proof.
  unfold typed_mapFirst, mapFirst.
  apply T_LtLam; [ solve_wf | reflexivity |].
  apply T_LtLam; [ solve_wf | reflexivity |].
  apply T_LtLam; [ solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  open_lam.
  open_lam.
  open_lam.
  eapply T_Match with
    (Ts := [`T 2; `T 1]) (Delta := `Lf) (arity := 2) (lts := [])
    (rho_fields := [`T 2; `T 1])
    (scrut_result_ty := T_Pair `Lf (`T 2) (`T 1))
    (result_tag := pair_tag) (result_l := `Lf)
    (eta := T_Pair `Lf (`T 0) (`T 1))
    (elim_result := T_Pair `Lf (`T 0) (`T 1));
    cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt | solve_var ].
  eapply T_Ctor with
    (n_lt := 0) (n_ty := 2) (lts := []) (Ts := [`T 0; `T 1])
    (sigma_fields := [`T 0; `T 1])
    (result_ty_schema := T_Pair `Lf (`T 0) (`T 1));
    cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt ].
  - constructor.
  - constructor; [ eapply T_App; [ solve_var | solve_var ] |].
    constructor; [ solve_var | constructor ].
Qed.

Theorem typed_foldEndo_proof : typed_foldEndo.
Proof.
  unfold typed_foldEndo, foldEndo.
  apply T_LtLam; [ solve_wf | reflexivity |].
  open_lam.
  open_lam.
  eapply T_Match with
    (Ts := []) (Delta := `L 0) (arity := 1) (lts := [`L 0])
    (rho_fields := [T_Nat (`L 0) -{ `Lf }-> T_Nat (`L 0)])
    (scrut_result_ty := T_EndoI (`L 0))
    (result_tag := endoi_tag) (result_l := `L 0)
    (eta := T_Nat (`L 0)) (elim_result := T_Nat (`L 0));
    cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt | solve_var ].
  eapply T_App; [ solve_var |].
  eapply T_Sub; [ solve_nat |].
  apply SA_Data; [ solve_lt | solve_wf ].
Qed.

(* ================================================================== *)
(* Negative/error witnesses                                           *)
(* ================================================================== *)

(* The no-local witnesses are certified decisions of the REAL noloc    *)
(* judgment `Γ ⊢ₗ lt_of_ty_G Γ T <: lt_free` via the reflected decider *)
(* [nolocb] (Decide.v).  The [lt_ctx_wf] side condition is discharged  *)
(* by computation: neither example context has a lifetime binder.      *)

Theorem rejected_testWithState_proof : rejected_testWithState.
Proof.
  apply nolocb_false_rejects.
  - intros x Δ H; cbn in H; discriminate.
  - solve_wf.
  - vm_compute; reflexivity.
Qed.

(* [crashEndo]'s witness is a genuine T_Match premise ([elim_ty_n])    *)
(* and remains a direct computation.                                   *)
Theorem rejected_crashEndo_proof : rejected_crashEndo.
Proof. reflexivity. Qed.

Theorem rejected_crashBox_proof : rejected_crashBox.
Proof.
  apply nolocb_false_rejects.
  - intros x Δ H; cbn in H; discriminate.
  - cbn; solve_wf.
  - vm_compute; reflexivity.
Qed.

Theorem typed_clash_ignored_local_proof : typed_clash_ignored_local.
Proof.
  apply nolocb_true_accepts.
  - intros x Δ H; cbn in H; discriminate.
  - solve_wf.
  - vm_compute; reflexivity.
Qed.

(* ================================================================== *)
(* Reduction statements                                               *)
(* ================================================================== *)

Theorem red_list_example_proof : red_list_example.
Proof.
  unfold red_list_example, list_example, cons_fn, cons_v.
  ms_head ((EC_app1 (EC_ty_app EC_hole (T_File `Ll)) file_v)) (apply H_LtBeta).
  ms_head ((EC_app1 EC_hole file_v)) (apply H_TyBeta).
  eapply MS_Step.
  { apply (S_step EC_hole). constructor. apply H_Beta, file_v_value. }
  cbn. apply MS_Refl.
Qed.

Theorem red_reader_example_proof : red_reader_example.
Proof.
  unfold red_reader_example, reader_example, reader_example_op_body.
  eapply MS_Step.
  { apply (S_Handle Reader_tag [T_Nat `Lf] (T_Nat `Lf) (T_Nat `Lf) [(0, ($$ 1) @· two_v)]
             (term_perform ($$ 0) 0 [] (T_Nat `Lf) unit_v) 0).
    cbn. intros H. inversion H. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor.
    apply (H_Perform Reader_tag 0 [T_Nat `Lf] (T_Nat `Lf) (T_Nat `Lf) [(0, ($$ 1) @· two_v)] 0 0 (($$ 1) @· two_v) [] (T_Nat `Lf) unit_v EC_hole);
      [apply unit_v_value | constructor | constructor | reflexivity]. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor. apply H_Beta, two_v_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor. apply H_Return, two_v_value. }
  apply MS_Refl.
Qed.

Theorem red_optionality_example_proof : red_optionality_example.
Proof.
  unfold red_optionality_example, optionality_example, optionality_op_body, some_v.
  eapply MS_Step.
  { apply (S_Handle Optionality_tag [] (T_Option `Lf (T_Nat `Lf)) (T_Option `Lf (T_Nat `Lf))
             [(1, ($$ 1) @· term_ctor some_tag `Lf [] [`T 0] [$$ 0])]
             (term_perform ($$ 0) 0 [T_Nat `Lf] (T_Option `Lf (T_Nat `Lf)) three_v) 0).
    cbn. intros H. inversion H. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor.
    apply (H_Perform Optionality_tag 0 [] (T_Option `Lf (T_Nat `Lf)) (T_Option `Lf (T_Nat `Lf))
             [(1, ($$ 1) @· term_ctor some_tag `Lf [] [`T 0] [$$ 0])] 0 1
             (($$ 1) @· term_ctor some_tag `Lf [] [`T 0] [$$ 0])
             [T_Nat `Lf] (T_Option `Lf (T_Nat `Lf)) three_v EC_hole);
      [apply three_v_value | constructor | constructor | reflexivity]. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta. solve_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor.
    apply H_Return. solve_value. }
  cbn. apply MS_Refl.
Qed.

Theorem red_exception_example_proof : red_exception_example.
Proof.
  unfold red_exception_example, exception_example, withException,
         withException_op_body, exception_example_body, ok_v, error_v.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_ty_app EC_hole (T_File `Lf))
                     (λ: T_Exception `Ll (T_Nat `Lf) \\
                        term_perform ($$ 0) 0 [T_File `Lf] (T_File `Lf) three_v))).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole
                     (λ: T_Exception `Ll (T_Nat `Lf) \\
                        term_perform ($$ 0) 0 [T_File `Lf] (T_File `Lf) three_v))).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  ms_head EC_hole (apply H_Beta; solve_value).
  eapply MS_Step.
  { eapply (S_Handle _ _ _ _ _ _ 0).
    cbn. intros H. inversion H. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_handler_m 0 (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
                     (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
                     (EC_ctor ok_tag `Lf [] [T_Nat `Lf; T_File `Lf] [] EC_hole []))).
    - repeat constructor.
    - apply H_Beta. solve_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _ _ _
                (EC_ctor ok_tag `Lf [] [T_Nat `Lf; T_File `Lf] [] EC_hole [])).
      + apply three_v_value.
      + repeat constructor.
      + repeat constructor.
      + reflexivity. }
  cbn. apply MS_Refl.
Qed.

(* Pair<Nat,Nat>(x, y) typing helper. *)
Lemma typed_pair_nat : forall x y,
  data_ctx ⊢ₜ x : T_Nat `Lf ->
  data_ctx ⊢ₜ y : T_Nat `Lf ->
  data_ctx ⊢ₜ pair_v (T_Nat `Lf) (T_Nat `Lf) x y
    : T_Pair `Lf (T_Nat `Lf) (T_Nat `Lf).
Proof.
  intros x y Hx Hy.
  eapply T_Ctor with
    (n_lt := 0) (n_ty := 2) (lts := []) (Ts := [T_Nat `Lf; T_Nat `Lf])
    (sigma_fields := [`T 0; `T 1])
    (result_ty_schema := T_Pair `Lf (`T 0) (`T 1));
    cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt ].
  - constructor.
  - constructor; [ exact Hx |].
    constructor; [ exact Hy | constructor ].
Qed.

(* EndoI[free](succ) : EndoI'free typing helper. *)
Lemma typed_endoi_v : data_ctx ⊢ₜ endoi_v : T_EndoI `Lf.
Proof.
  unfold endoi_v.
  eapply T_Ctor with
    (n_lt := 1) (n_ty := 0) (lts := [`Lf]) (Ts := [])
    (sigma_fields := [T_Nat (`L 0) -{ `Lf }-> T_Nat (`L 0)])
    (result_ty_schema := T_EndoI (`L 0));
    cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt ].
  - constructor; [ solve_lt | constructor ].
  - constructor; [ | constructor ].
    pose proof typed_succ_proof as Hs. unfold typed_succ in Hs. exact Hs.
Qed.

Theorem typed_foldEndo_example_proof : typed_foldEndo_example.
Proof.
  unfold typed_foldEndo_example, foldEndo_example.
  pose proof typed_foldEndo_proof as H. unfold typed_foldEndo in H.
  eapply T_LtApp with (l := `Lf) in H; [ | solve_wf ]. cbn in H.
  eapply T_App; [ | exact typed_endoi_v ].
  eapply T_App; [ exact H | solve_nat ].
Qed.

Theorem typed_mapFirst_example_proof : typed_mapFirst_example.
Proof.
  unfold typed_mapFirst_example, mapFirst_example.
  pose proof typed_mapFirst_proof as H. unfold typed_mapFirst in H.
  eapply T_LtApp with (l := `Lf) in H; [ | solve_wf ]. cbn in H.
  eapply T_LtApp with (l := `Lf) in H; [ | solve_wf ]. cbn in H.
  eapply T_LtApp with (l := `Lf) in H; [ | solve_wf ]. cbn in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | solve_any_sub ]. cbn in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | solve_any_sub ]. cbn in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | solve_any_sub ]. cbn in H.
  eapply T_App.
  - eapply T_App.
    + eapply T_App; [ exact H |].
      apply typed_pair_nat; solve_nat.
    + apply typed_pair_nat; solve_nat.
  - pose proof typed_succ_proof as Hs. unfold typed_succ in Hs.
    eapply T_Sub; [ exact Hs |].
    eapply SA_Fun;
      [ apply SA_Refl; solve_wf | solve_lt_sub | apply SA_Refl; solve_wf ].
Qed.

Theorem red_foldEndo_example_proof : red_foldEndo_example.
Proof.
  unfold red_foldEndo_example, foldEndo_example, foldEndo, endoi_v.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 EC_hole two_v)
                     (term_ctor endoi_tag `Lf [`Lf] [] [succ_fn]))).
    - repeat constructor.
    - apply H_LtBeta. }
  cbn.
  ms_head ((EC_app1 EC_hole (term_ctor endoi_tag `Lf [`Lf] [] [succ_fn]))) (apply H_Beta; apply two_v_value).
  ms_head EC_hole (apply H_Beta; solve_value).
  ms_head EC_hole (apply (H_MatchYes endoi_tag `Lf [`Lf] [] [succ_fn]); repeat constructor).
  ms_head EC_hole (apply H_Beta; apply three_v_value).
  apply MS_Refl.
Qed.

Theorem red_mapFirst_example_proof : red_mapFirst_example.
Proof.
  unfold red_mapFirst_example, mapFirst_example, mapFirst, pair_v.
  set (p00 := term_ctor pair_tag `Lf [] [T_Nat `Lf; T_Nat `Lf] [zero_v; zero_v]).
  set (p23 := term_ctor pair_tag `Lf [] [T_Nat `Lf; T_Nat `Lf] [two_v; three_v]).
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 (EC_app1 (EC_ty_app (EC_ty_app (EC_ty_app
      (EC_lt_app (EC_lt_app EC_hole `Lf) `Lf)
      (T_Nat `Lf)) (T_Nat `Lf)) (T_Nat `Lf)) p00) p23) succ_fn)).
    - unfold p00, p23; repeat constructor.
    - apply H_LtBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 (EC_app1 (EC_ty_app (EC_ty_app (EC_ty_app
      (EC_lt_app EC_hole `Lf)
      (T_Nat `Lf)) (T_Nat `Lf)) (T_Nat `Lf)) p00) p23) succ_fn)).
    - unfold p00, p23; repeat constructor.
    - apply H_LtBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 (EC_app1 (EC_ty_app (EC_ty_app (EC_ty_app
      EC_hole
      (T_Nat `Lf)) (T_Nat `Lf)) (T_Nat `Lf)) p00) p23) succ_fn)).
    - unfold p00, p23; repeat constructor.
    - apply H_LtBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 (EC_app1 (EC_ty_app (EC_ty_app
      EC_hole (T_Nat `Lf)) (T_Nat `Lf)) p00) p23) succ_fn)).
    - unfold p00, p23; repeat constructor.
    - apply H_TyBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 (EC_app1 (EC_ty_app
      EC_hole (T_Nat `Lf)) p00) p23) succ_fn)).
    - unfold p00, p23; repeat constructor.
    - apply H_TyBeta. }
  cbn.
  ms_head ((EC_app1 (EC_app1 (EC_app1 EC_hole p00) p23) succ_fn)) (unfold p00, p23; repeat constructor) (apply H_TyBeta).
  ms_head ((EC_app1 (EC_app1 EC_hole p23) succ_fn)) (unfold p23; repeat constructor) (apply H_Beta; unfold p00; repeat constructor).
  ms_head ((EC_app1 EC_hole succ_fn)) (apply H_Beta; unfold p23; repeat constructor).
  ms_head EC_hole (apply H_Beta; solve_value).
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply (H_MatchYes pair_tag `Lf [] [T_Nat `Lf; T_Nat `Lf] [two_v; three_v]).
      repeat constructor. }
  cbn.
  ms_head ((EC_ctor pair_tag `Lf [] [T_Nat `Lf; T_Nat `Lf] [] EC_hole [three_v])) (apply H_Beta; apply two_v_value).
  apply MS_Refl.
Qed.

Theorem typed_withReader_example_proof : typed_withReader_example.
Proof.
  unfold typed_withReader_example, withReader_example.
  pose proof typed_withReader_proof as H. unfold typed_withReader in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | solve_any_sub ]. cbn in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | solve_any_sub ]. cbn in H.
  eapply T_App; [ | solve_nat ].
  eapply T_App; [ exact H | ].
  open_lam.
  solve_perform ltac:(unfold unit_v; solve_ctor).
Qed.

Theorem typed_withId_example_proof : typed_withId_example.
Proof.
  unfold typed_withId_example, withId_example.
  pose proof typed_withId_proof as H. unfold typed_withId in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | solve_any_sub ]. cbn in H.
  eapply T_App; [ exact H | ].
  open_lam.
  eapply T_Perform with (Ss := [T_Nat `Lf]).
  - solve_var.
  - cbn; reflexivity.
  - cbn; reflexivity.
  - reflexivity.
  - reflexivity.
  - solve_wf.
  - constructor; [ cbn; solve_lt_sub | constructor ].
  - cbn; reflexivity.
  - cbn; solve_lt_sub.
  - cbn; reflexivity.
  - solve_wf.
  - solve_nat.
Qed.

Theorem red_withReader_example_proof : red_withReader_example.
Proof.
  unfold red_withReader_example, withReader_example, withReader.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 (EC_ty_app
      EC_hole (T_Nat `Lf))
      (λ: T_Reader `Ll (T_Nat `Lf) \\ term_perform ($$ 0) 0 [] (T_Nat `Lf) unit_v)) two_v)).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1
      EC_hole
      (λ: T_Reader `Ll (T_Nat `Lf) \\ term_perform ($$ 0) 0 [] (T_Nat `Lf) unit_v)) two_v)).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  ms_head ((EC_app1 EC_hole two_v)) (apply H_Beta; solve_value).
  ms_alloc (S_HandleCtx (EC_app1 EC_hole two_v) Reader_tag [T_Nat `Lf] _ _ _ _ 0) (cbn; intros H; inversion H).
  ms_head ((EC_app1 (EC_handler_m 0 _ _ (EC_app2 _ EC_hole)) two_v)) (apply H_Beta; solve_value).
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole two_v)).
    - repeat constructor.
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _ _ _ (EC_app2 _ EC_hole)).
      + repeat constructor.
      + repeat constructor.
      + repeat constructor.
      + reflexivity. }
  cbn.
  ms_head EC_hole (apply H_Beta; apply two_v_value).
  ms_head ((EC_app1 EC_hole two_v)) (apply H_Beta; apply two_v_value).
  ms_head ((EC_app1 (EC_handler_m 0 _ _ EC_hole) two_v)) (apply H_Beta; apply two_v_value).
  ms_head ((EC_app1 EC_hole two_v)) (apply H_Return; solve_value).
  ms_head EC_hole (apply H_Beta; apply two_v_value).
  apply MS_Refl.
Qed.

Theorem red_withId_example_proof : red_withId_example.
Proof.
  unfold red_withId_example, withId_example, withId, withId_op_body.
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole
      (λ: T_Id `Ll \\ term_perform ($$ 0) 0 [T_Nat `Lf] (T_Nat `Lf) two_v))).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  ms_head EC_hole (apply H_Beta; solve_value).
  eapply MS_Step.
  { eapply (S_Handle _ _ _ _ _ _ 0).
    cbn. intros H. inversion H. }
  cbn.
  ms_head ((EC_handler_m 0 (T_Nat `Lf) (T_Nat `Lf) EC_hole)) (apply H_Beta; solve_value).
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _ _ _ EC_hole).
      + apply two_v_value.
      + constructor.
      + constructor.
      + reflexivity. }
  cbn.
  ms_head EC_hole (apply H_Beta; apply two_v_value).
  ms_head EC_hole (apply H_Return; apply two_v_value).
  apply MS_Refl.
Qed.

Theorem typed_getOrElse_proof : typed_getOrElse.
Proof.
  unfold typed_getOrElse, getOrElse.
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  open_lam.
  open_lam.
  eapply T_Match with
    (Ts := [`T 0]) (Delta := `Lf) (arity := 1) (lts := [])
    (rho_fields := [`T 0]) (scrut_result_ty := T_Option `Lf (`T 0))
    (result_tag := option_tag) (result_l := `Lf)
    (eta := `T 0) (elim_result := `T 0);
    cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt | solve_var ].
Qed.

Theorem typed_getOrElse_some_proof : typed_getOrElse_some.
Proof.
  unfold typed_getOrElse_some, getOrElse_some.
  pose proof typed_getOrElse_proof as H. unfold typed_getOrElse in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | solve_any_sub ]. cbn in H.
  eapply T_App.
  - eapply T_App; [ exact H | solve_nat ].
  - unfold some_v. eapply T_Ctor with
      (n_lt := 0) (n_ty := 1) (lts := []) (Ts := [T_Nat `Lf])
      (sigma_fields := [`T 0]) (result_ty_schema := T_Option `Lf (`T 0));
      cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt ].
    + constructor.
    + constructor; [ solve_nat | constructor ].
Qed.

Theorem typed_getOrElse_none_proof : typed_getOrElse_none.
Proof.
  unfold typed_getOrElse_none, getOrElse_none.
  pose proof typed_getOrElse_proof as H. unfold typed_getOrElse in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | solve_any_sub ]. cbn in H.
  eapply T_App.
  - eapply T_App; [ exact H | solve_nat ].
  - unfold none_v. eapply T_Ctor with
      (n_lt := 0) (n_ty := 1) (lts := []) (Ts := [T_Nat `Lf])
      (sigma_fields := []) (result_ty_schema := T_Option `Lf (`T 0));
      cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt ];
      constructor.
Qed.

Theorem typed_list_example_full_proof : typed_list_example_full.
Proof.
  unfold typed_list_example_full, list_example_full.
  pose proof typed_list_example_proof as H. unfold typed_list_example in H.
  eapply T_App; [ exact H | ].
  unfold nil_v. eapply T_Ctor with
    (n_lt := 0) (n_ty := 1) (lts := []) (Ts := [T_File `Ll])
    (sigma_fields := []) (result_ty_schema := T_List `Lf (`T 0));
    cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt ];
    constructor.
Qed.

Theorem typed_multishot_example_proof : typed_multishot_example.
Proof.
  unfold typed_multishot_example, multishot_example, multishot_op_body.
  open_handle.
  - apply SA_Refl. solve_wf.
  - constructor; [| constructor].
    cbn. eapply T_App with (A := T_Nat `Lf) (l := `Ll) (B := T_Nat `Lf).
    + open_lam.
      eapply T_App with (A := T_Nat `Lf) (l := `Ll) (B := T_Nat `Lf).
      * open_lam.
        solve_sum_fn.
      * eapply T_App; [ solve_var | solve_nat ].
    + eapply T_App; [ solve_var | solve_nat ].
  - cbn. solve_perform ltac:(unfold unit_v; solve_ctor).
Qed.

Theorem typed_forward_example_proof : typed_forward_example.
Proof.
  unfold typed_forward_example, forward_example, forward_inner_body,
         error_v, ok_v.
  open_handle.
  - apply SA_Refl. solve_wf.
  - (* throw clause: Error<Nat,File>(e) *)
    constructor; [| constructor].
    cbn. eapply T_Ctor with
      (n_lt := 0) (n_ty := 2) (lts := []) (Ts := [T_Nat `Lf; T_File `Lf])
      (sigma_fields := [`T 0]) (result_ty_schema := T_Result `Lf (`T 0) (`T 1));
      cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt ].
    + constructor.
    + constructor; [ solve_var | constructor ].
  - (* body: Ok( inner reader handle ) *)
    cbn. eapply T_Ctor with
      (n_lt := 0) (n_ty := 2) (lts := []) (Ts := [T_Nat `Lf; T_File `Lf])
      (sigma_fields := [`T 1]) (result_ty_schema := T_Result `Lf (`T 0) (`T 1));
      cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt ].
    + constructor.
    + constructor; [ | constructor ].
      open_handle.
      * apply SA_Refl. solve_wf.
      * (* ask clause: resume(2) *)
        constructor; [| constructor].
        cbn. eapply T_App; [ solve_var | solve_nat ].
      * (* let x = ask in throw x *)
        cbn. eapply T_App with (A := T_Nat `Lf) (l := `Ll) (B := T_File `Lf).
        -- open_lam.
           eapply T_Perform with (Ss := [T_File `Lf]).
           ++ solve_var.
           ++ cbn; reflexivity.
           ++ cbn; reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ solve_wf.
           ++ constructor; [ cbn; solve_lt_sub | constructor ].
           ++ cbn; reflexivity.
           ++ cbn; solve_lt_sub.
           ++ cbn; reflexivity.
           ++ solve_wf.
           ++ solve_var.
        -- solve_perform ltac:(unfold unit_v; solve_ctor).
Qed.

Theorem red_getOrElse_some_proof : red_getOrElse_some.
Proof.
  unfold red_getOrElse_some, getOrElse_some, getOrElse, some_v.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 EC_hole zero_v)
                     (term_ctor some_tag `Lf [] [T_Nat `Lf] [three_v]))).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  ms_head ((EC_app1 EC_hole (term_ctor some_tag `Lf [] [T_Nat `Lf] [three_v]))) (apply H_Beta; solve_value).
  ms_head EC_hole (apply H_Beta; solve_value).
  ms_head EC_hole (apply (H_MatchYes some_tag `Lf [] [T_Nat `Lf] [three_v]); repeat constructor).
  apply MS_Refl.
Qed.

Theorem red_getOrElse_none_proof : red_getOrElse_none.
Proof.
  unfold red_getOrElse_none, getOrElse_none, getOrElse, none_v.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 EC_hole zero_v)
                     (term_ctor none_tag `Lf [] [T_Nat `Lf] []))).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  ms_head ((EC_app1 EC_hole (term_ctor none_tag `Lf [] [T_Nat `Lf] []))) (apply H_Beta; solve_value).
  ms_head EC_hole (apply H_Beta; solve_value).
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_MatchNo.
      + repeat constructor.
      + unfold some_tag, none_tag. congruence. }
  cbn. apply MS_Refl.
Qed.

Theorem red_list_example_full_proof : red_list_example_full.
Proof.
  unfold red_list_example_full, list_example_full, list_example, cons_fn,
         cons_v, nil_v.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 (EC_ty_app EC_hole (T_File `Ll)) file_v)
                     (term_ctor nil_tag `Lf [] [T_File `Ll] []))).
    - repeat constructor.
    - apply H_LtBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 EC_hole file_v)
                     (term_ctor nil_tag `Lf [] [T_File `Ll] []))).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  ms_head ((EC_app1 EC_hole (term_ctor nil_tag `Lf [] [T_File `Ll] []))) (apply H_Beta; apply file_v_value).
  ms_head EC_hole (apply H_Beta; solve_value).
  apply MS_Refl.
Qed.

(* Both resumptions run to completion and the bounded sum combines
   their results; the whole run is validated by the certified
   evaluator ([stepf_run_sound], Stepf.v). *)
Theorem red_multishot_example_proof : red_multishot_example.
Proof.
  unfold red_multishot_example.
  replace five_v with (stepf_run 100 multishot_example)
    by (vm_compute; reflexivity).
  apply stepf_run_sound.
Qed.

Theorem red_forward_example_proof : red_forward_example.
Proof.
  unfold red_forward_example, forward_example, forward_inner_body, error_v, ok_v.
  eapply MS_Step.
  { eapply (S_Handle _ _ _ _ _ _ 0).
    cbn. intros H. inversion H. }
  cbn.
  eapply MS_Step.
  { apply (S_HandleCtx
      (EC_handler_m 0 (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
                      (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
        (EC_ctor ok_tag `Lf [] [T_Nat `Lf; T_File `Lf] [] EC_hole []))
      Reader_tag [T_Nat `Lf] (T_File `Lf) (T_File `Lf) _ _ 1).
    - repeat constructor.
    - cbn. intros H.
      repeat (destruct H as [H|H]; [ discriminate H |]). exact H. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_handler_m 0 (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
                      (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
        (EC_ctor ok_tag `Lf [] [T_Nat `Lf; T_File `Lf] [] EC_hole []))).
    - repeat constructor.
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _ _ _ (EC_app2 _ EC_hole)).
      + repeat constructor.
      + repeat constructor.
      + repeat constructor.
      + reflexivity. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_handler_m 0 (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
                      (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
        (EC_ctor ok_tag `Lf [] [T_Nat `Lf; T_File `Lf] [] EC_hole []))).
    - repeat constructor.
    - apply H_Beta. apply two_v_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_handler_m 0 (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
                      (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
        (EC_ctor ok_tag `Lf [] [T_Nat `Lf; T_File `Lf] []
          (EC_handler_m 1 (T_File `Lf) (T_File `Lf) EC_hole) []))).
    - repeat constructor.
    - apply H_Beta. apply two_v_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _ _ _
        (EC_ctor ok_tag `Lf [] [T_Nat `Lf; T_File `Lf] []
          (EC_handler_m 1 (T_File `Lf) (T_File `Lf) EC_hole) [])).
      + apply two_v_value.
      + apply pem_ctor. apply pem_handler_m; [ discriminate | apply pem_hole ].
      + repeat constructor.
      + reflexivity. }
  cbn. apply MS_Refl.
Qed.

(* ================================================================== *)
(* State example proofs.  [state_example] uses the two-operation      *)
(* declaration                                                        *)
(*   effect State<s> { op get(): s ; op put(s): Unit }                *)
(* The typing exercises T_Handle's per-operation typing_ops (two      *)
(* clauses); the reduction fires H_Perform three times — get (index   *)
(* 0), put (index 1), get (index 0) — each clause selected by         *)
(* nth_error.                                                         *)
(* ================================================================== *)

Theorem typed_state_example_proof : typed_state_example.
Proof.
  unfold typed_state_example, state_example, state_example_handler,
         state_get_body, state_put_body.
  eapply T_App with (A := T_Nat `Lf) (l := `Ll) (B := T_Nat `Lf); [ | solve_nat ].
  eapply T_Handle with
    (T_B := T_Nat `Lf -{ `Lf }-> T_Nat `Lf)
    (T_R := T_Nat `Lf -{ `Ll }-> T_Nat `Lf);
    try (cbn; reflexivity); try solve_wf; try (cbn; solve_lt_sub).
  - eapply SA_Fun; [ apply SA_Refl; solve_wf | solve_lt | apply SA_Refl; solve_wf ].
  - (* the TWO operation clauses *)
    constructor; [ | constructor; [ | constructor ] ].
    + (* get clause (index 0): fun(s) resume(s)(s) *)
      cbn. open_lam.
      eapply T_App with (A := T_Nat `Lf) (l := `Ll) (B := T_Nat `Lf).
      * eapply T_App with (A := T_Nat `Lf) (l := `Ll)
          (B := T_Nat `Lf -{ `Ll }-> T_Nat `Lf); solve_var.
      * solve_var.
    + (* put clause (index 1): fun(_) resume(Unit())(s') *)
      cbn. open_lam.
      eapply T_App with (A := T_Nat `Lf) (l := `Ll) (B := T_Nat `Lf).
      * eapply T_App with (A := T_Unit) (l := `Ll)
          (B := T_Nat `Lf -{ `Ll }-> T_Nat `Lf);
          [ solve_var | unfold unit_v; solve_ctor ].
      * solve_var.
  - (* body: let a = get in let _ = put 3 in let b = get in fun(s) b *)
    cbn.
    eapply T_App with (A := T_Nat `Lf) (l := `Ll)
      (B := T_Nat `Lf -{ `Lf }-> T_Nat `Lf).
    + open_lam.
      cbn.
      eapply T_App with (A := T_Unit) (l := `Ll)
        (B := T_Nat `Lf -{ `Lf }-> T_Nat `Lf).
      * open_lam.
        cbn.
        eapply T_App with (A := T_Nat `Lf) (l := `Ll)
          (B := T_Nat `Lf -{ `Lf }-> T_Nat `Lf).
        -- open_lam.
           open_lam (solve_var).
        -- (* third perform: get, index 0 *)
           solve_perform ltac:(unfold unit_v; solve_ctor).
      * (* second perform: put, index 1 *)
        solve_perform solve_nat.
    + (* first perform: get, index 0 *)
      solve_perform ltac:(unfold unit_v; solve_ctor).
Qed.

Theorem red_state_example_proof : red_state_example.
Proof.
  unfold red_state_example, state_example, state_example_handler,
         state_get_body, state_put_body.
  (* allocate the capability (fresh marker 0) under the state application *)
  ms_alloc (S_HandleCtx (EC_app1 EC_hole two_v) State_tag [T_Nat `Lf] _ _ _ _ 0) (cbn; intros H; inversion H).
  (* first get fires: operation index 0 *)
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole two_v)).
    - repeat constructor.
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _ _ _ (EC_app2 _ EC_hole)).
      + repeat constructor.
      + repeat constructor.
      + repeat constructor.
      + reflexivity. }
  cbn.
  (* the get clause's state lambda meets the initial state 2 *)
  ms_head EC_hole (apply H_Beta; apply two_v_value).
  (* resume(2): re-install the delimiter *)
  ms_head ((EC_app1 EC_hole two_v)) (apply H_Beta; apply two_v_value).
  (* continue the body with a = 2 *)
  ms_head ((EC_app1 (EC_handler_m 0 _ _ EC_hole) two_v)) (apply H_Beta; apply two_v_value).
  (* put(3) fires: operation index 1 *)
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole two_v)).
    - repeat constructor.
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _ _ _ (EC_app2 _ EC_hole)).
      + repeat constructor.
      + repeat constructor.
      + repeat constructor.
      + reflexivity. }
  cbn.
  (* the put clause discards the old state 2 *)
  ms_head EC_hole (apply H_Beta; apply two_v_value).
  (* resume(Unit()) *)
  ms_head ((EC_app1 EC_hole three_v)) (apply H_Beta; solve_value).
  (* continue the body with _ = Unit() *)
  ms_head ((EC_app1 (EC_handler_m 0 _ _ EC_hole) three_v)) (apply H_Beta; solve_value).
  (* second get fires: operation index 0 again *)
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole three_v)).
    - repeat constructor.
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _ _ _ (EC_app2 _ EC_hole)).
      + repeat constructor.
      + repeat constructor.
      + repeat constructor.
      + reflexivity. }
  cbn.
  (* the get clause's state lambda meets the current state 3 *)
  ms_head EC_hole (apply H_Beta; apply three_v_value).
  (* resume(3) *)
  ms_head ((EC_app1 EC_hole three_v)) (apply H_Beta; apply three_v_value).
  (* b = 3: the body is exhausted, produce the post-handler λ *)
  ms_head ((EC_app1 (EC_handler_m 0 _ _ EC_hole) three_v)) (apply H_Beta; apply three_v_value).
  (* the delimiter's body is a value: H_Return drops the delimiter *)
  ms_head ((EC_app1 EC_hole three_v)) (apply H_Return; solve_value).
  (* final application: (λs. 3) 3 *)
  ms_head EC_hole (apply H_Beta; apply three_v_value).
  apply MS_Refl.
Qed.

(* ================================================================== *)
(* The bounded-sum family and the many-performs examples it           *)
(* validates.  Reduction runs are certified by the executable         *)
(* evaluator ([stepf_run_sound], Stepf.v).                            *)
(* ================================================================== *)

Theorem typed_sum3_proof : typed_sum3.
Proof.
  unfold typed_sum3. solve_sum_fn.
Qed.

Theorem red_sum3_example_proof : red_sum3_example.
Proof.
  unfold red_sum3_example.
  replace five_v with (stepf_run 40 ((sum3_fn @· two_v) @· three_v))
    by (vm_compute; reflexivity).
  apply stepf_run_sound.
Qed.

Theorem typed_reader_sum_example_proof : typed_reader_sum_example.
Proof.
  unfold typed_reader_sum_example, reader_sum_example, reader_example_op_body.
  open_handle.
  - apply SA_Refl. solve_wf.
  - constructor; [| constructor].
    cbn. eapply T_App.
    + solve_var.
    + solve_nat.
  - cbn. eapply T_App with (A := T_Nat `Lf) (l := `Ll) (B := T_Nat `Lf).
    + open_lam.
      eapply T_App with (A := T_Nat `Lf) (l := `Ll) (B := T_Nat `Lf).
      * open_lam.
        eapply T_App with (A := T_Nat `Lf) (l := `Ll) (B := T_Nat `Lf).
        -- open_lam.
           solve_sum_fn.
        -- solve_perform ltac:(unfold unit_v; solve_ctor).
      * solve_perform ltac:(unfold unit_v; solve_ctor).
    + solve_perform ltac:(unfold unit_v; solve_ctor).
Qed.

Theorem red_reader_sum_example_proof : red_reader_sum_example.
Proof.
  unfold red_reader_sum_example.
  replace six_v with (stepf_run 200 reader_sum_example)
    by (vm_compute; reflexivity).
  apply stepf_run_sound.
Qed.

Theorem typed_state_sum_example_proof : typed_state_sum_example.
Proof.
  unfold typed_state_sum_example, state_sum_example, state_sum_example_handler,
         state_get_body, state_put_body.
  eapply T_App with (A := T_Nat `Lf) (l := `Ll) (B := T_Nat `Lf); [ | solve_nat ].
  eapply T_Handle with
    (T_B := T_Nat `Lf -{ `Lf }-> T_Nat `Lf)
    (T_R := T_Nat `Lf -{ `Ll }-> T_Nat `Lf);
    try (cbn; reflexivity); try solve_wf; try (cbn; solve_lt_sub).
  - eapply SA_Fun; [ apply SA_Refl; solve_wf | solve_lt | apply SA_Refl; solve_wf ].
  - (* the TWO operation clauses, as in [typed_state_example_proof] *)
    constructor; [ | constructor; [ | constructor ] ].
    + cbn. open_lam.
      eapply T_App with (A := T_Nat `Lf) (l := `Ll) (B := T_Nat `Lf).
      * eapply T_App with (A := T_Nat `Lf) (l := `Ll)
          (B := T_Nat `Lf -{ `Ll }-> T_Nat `Lf); solve_var.
      * solve_var.
    + cbn. open_lam.
      eapply T_App with (A := T_Nat `Lf) (l := `Ll) (B := T_Nat `Lf).
      * eapply T_App with (A := T_Unit) (l := `Ll)
          (B := T_Nat `Lf -{ `Ll }-> T_Nat `Lf);
          [ solve_var | unfold unit_v; solve_ctor ].
      * solve_var.
  - (* body: let a = get in let _ = put 3 in let b = get in fun(s) sum3(a, b) *)
    cbn.
    eapply T_App with (A := T_Nat `Lf) (l := `Ll)
      (B := T_Nat `Lf -{ `Lf }-> T_Nat `Lf).
    + open_lam.
      cbn.
      eapply T_App with (A := T_Unit) (l := `Ll)
        (B := T_Nat `Lf -{ `Lf }-> T_Nat `Lf).
      * open_lam.
        cbn.
        eapply T_App with (A := T_Nat `Lf) (l := `Ll)
          (B := T_Nat `Lf -{ `Lf }-> T_Nat `Lf).
        -- open_lam.
           open_lam.
           solve_sum_fn.
        -- solve_perform ltac:(unfold unit_v; solve_ctor).
      * solve_perform solve_nat.
    + solve_perform ltac:(unfold unit_v; solve_ctor).
Qed.

Theorem red_state_sum_example_proof : red_state_sum_example.
Proof.
  unfold red_state_sum_example.
  replace five_v with (stepf_run 100 state_sum_example)
    by (vm_compute; reflexivity).
  apply stepf_run_sound.
Qed.
