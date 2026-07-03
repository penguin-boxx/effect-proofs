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
(* Multi-step plumbing                                                *)
(* ================================================================== *)

Lemma ms_one : forall t t', t ==> t' -> t ==>> t'.
Proof. intros t t' H. eapply MS_Step; [exact H | apply MS_Refl]. Qed.

Lemma ms_trans : forall t1 t2 t3, t1 ==>> t2 -> t2 ==>> t3 -> t1 ==>> t3.
Proof.
  intros t1 t2 t3 H12. revert t3.
  induction H12 as [|? ? ? Hs ? IH]; intros u H23; auto.
  eapply MS_Step; eauto.
Qed.

(* ================================================================== *)
(* Evaluation-context congruence for multi-step reduction.            *)
(*                                                                    *)
(* Reduction lifts through an application/ty-/lt-application frame.   *)
(* For [ty_app]/[lt_app] the frame carries no marker, so the lift is  *)
(* unconditional.  For [app] the sibling operand's markers join the   *)
(* term, so a [S_HandleCtx] (handler allocation) step would need a    *)
(* marker fresh in the sibling too — we require the sibling to be     *)
(* marker-free, which holds for every closed value/argument here.     *)
(* ================================================================== *)

Lemma step_ty_app : forall t t' S, t ==> t' -> term_ty_app t S ==> term_ty_app t' S.
Proof.
  intros t t' S H. inversion H; subst.
  - apply (S_step (EC_ty_app E S)); [ apply wf_ty_app; assumption | assumption ].
  - apply (S_HandleCtx (EC_ty_app E S)); [ apply wf_ty_app; assumption | cbn; assumption ].
Qed.

Lemma step_lt_app : forall t t' l, t ==> t' -> term_lt_app t l ==> term_lt_app t' l.
Proof.
  intros t t' l H. inversion H; subst.
  - apply (S_step (EC_lt_app E l)); [ apply wf_lt_app; assumption | assumption ].
  - apply (S_HandleCtx (EC_lt_app E l)); [ apply wf_lt_app; assumption | cbn; assumption ].
Qed.

Lemma step_app1 : forall t t' u, markers_in u = [] -> t ==> t' -> term_app t u ==> term_app t' u.
Proof.
  intros t t' u Hu H. inversion H; subst.
  - apply (S_step (EC_app1 E u)); [ apply wf_app1; assumption | assumption ].
  - apply (S_HandleCtx (EC_app1 E u)); [ apply wf_app1; assumption | ].
    cbn. rewrite Hu. rewrite app_nil_r. assumption.
Qed.

Lemma step_app2 : forall v t t', value v -> markers_in v = [] -> t ==> t' ->
  term_app v t ==> term_app v t'.
Proof.
  intros v t t' Hv Hm H. inversion H; subst.
  - apply (S_step (EC_app2 v E)); [ apply wf_app2; assumption | assumption ].
  - apply (S_HandleCtx (EC_app2 v E)); [ apply wf_app2; assumption | ].
    cbn. rewrite Hm. cbn. assumption.
Qed.

Lemma ms_ty_app : forall t t' S, t ==>> t' -> term_ty_app t S ==>> term_ty_app t' S.
Proof.
  intros t t' S H. induction H; [ apply MS_Refl |].
  eapply MS_Step; [ apply step_ty_app; eassumption | assumption ].
Qed.

Lemma ms_lt_app : forall t t' l, t ==>> t' -> term_lt_app t l ==>> term_lt_app t' l.
Proof.
  intros t t' l H. induction H; [ apply MS_Refl |].
  eapply MS_Step; [ apply step_lt_app; eassumption | assumption ].
Qed.

Lemma ms_app1 : forall t t' u, markers_in u = [] -> t ==>> t' -> term_app t u ==>> term_app t' u.
Proof.
  intros t t' u Hu H. induction H; [ apply MS_Refl |].
  eapply MS_Step; [ apply step_app1; eassumption | assumption ].
Qed.

Lemma ms_app2 : forall v t t', value v -> markers_in v = [] -> t ==>> t' ->
  term_app v t ==>> term_app v t'.
Proof.
  intros v t t' Hv Hm H. induction H; [ apply MS_Refl |].
  eapply MS_Step; [ apply step_app2; eassumption | assumption ].
Qed.

Lemma unit_v_value : value unit_v.
Proof. unfold unit_v. constructor. constructor. Qed.

Lemma file_v_value : value file_v.
Proof. unfold file_v. constructor. constructor. Qed.

Lemma two_v_value : value two_v.
Proof. unfold two_v, suc_v, zero_v. repeat constructor. Qed.

Lemma three_v_value : value three_v.
Proof. unfold three_v, suc_v, zero_v. repeat constructor. Qed.

Lemma some_three_value : value (some_v (T_Nat `Lf) three_v).
Proof. unfold some_v. constructor. repeat constructor; apply three_v_value. Qed.

Hint Resolve unit_v_value file_v_value two_v_value three_v_value some_three_value : core.

(* [solve_wf] discharges well-formedness side conditions ([ty_wf],
   [types_wf], [lt_wf], [lifetimes_wf]) and the context-lookup equations
   they spawn.  For a [type_var] it picks TWF_Var, resolves the lookup by
   computation, and recurses into the bound's well-formedness (the [cbn]
   on the second branch forces a stuck [shift_ty .. any_at_free] back to a
   concrete [type_ctor] so the generic [constructor] arm can fire). *)
Ltac solve_wf :=
  repeat match goal with
  | |- ty_wf _ (type_var _) => econstructor; [cbn; reflexivity | cbn]
  | |- lt_wf _ (lt_var _) => econstructor; [cbn; reflexivity]
  | |- ty_wf _ _ => constructor
  | |- types_wf _ _ => constructor
  | |- lifetimes_wf _ _ => constructor
  | |- lt_wf _ _ => constructor
  | |- ctx_lookup_ty _ _ = Some _ => cbn; reflexivity
  | |- ctx_lookup_lt _ _ = Some _ => cbn; reflexivity
  end.

(* [solve_var] types a de Bruijn variable: it applies T_Var, resolves the
   term-context lookup by computation, and proves the bound is well-formed.
   [cbn] is required before [reflexivity] because [full_ctx] is built with
   list append ([++]). *)
Ltac solve_var :=
  apply T_Var; [cbn; reflexivity | solve_wf].

Ltac solve_free_sub :=
  apply LS_Free; solve_wf.

Ltac solve_lt_sub :=
  match goal with
  | |- _ ⊢ₗ lt_min _ _ <: _ => apply LS_MinL; solve_lt_sub
  | |- _ ⊢ₗ lt_free <: _ => apply LS_Free; solve_wf
  | |- _ ⊢ₗ ?l <: ?l => apply LS_Refl; solve_wf
  | |- _ ⊢ₗ _ <: lt_local => apply LS_Local; solve_wf
  end.

(* [solve_lt] proves a lifetime-subtyping goal whose endpoints are built
   from [lt_free], [lt_local], [lt_var] and [lt_min] (joins).  It tries the
   reflexive/bottom/join introduction rules and recurses through [lt_min]
   on either side. *)
Ltac solve_lt :=
  solve [ apply LS_Refl; solve_wf
        | apply LS_Free; solve_wf
        | apply LS_MinR1; [solve_lt | solve_wf]
        | apply LS_MinR2; [solve_lt | solve_wf]
        | apply LS_MinL; [solve_lt | solve_lt] ].

Ltac solve_nullary_ctor :=
  eapply T_Ctor with (lts := []) (Ts := []) (rho_fields := []);
  cbn; try reflexivity;
  try solve [ repeat constructor
            | apply LS_Free; repeat constructor
            | apply LS_Refl; repeat constructor ].

(* [solve_ctor] discharges a general constructor-application typing goal
   ([T_Ctor]).  [eapply] leaves the field/lifetime/type arguments as
   evars; the equational premises are closed by [reflexivity] (which
   instantiates those evars), and the loop then proves the remaining
   well-formedness, lifetime-subtyping and [Forall]/[Forall2] obligations.
   The [progress cbn] alternative re-normalises field types of the form
   [inst_ctor_type ..] that only become reducible once the argument evars
   have been resolved. *)
Ltac solve_ctor :=
  eapply T_Ctor; cbn; try reflexivity;
  repeat first
    [ solve_var | solve_lt | progress solve_wf | progress cbn
    | apply Forall2_nil | apply Forall_nil
    | apply Forall2_cons | apply Forall_cons ].

(* [solve_nat] types a Peano numeral [Suc (Suc ... Zero)] at [T_Nat `Lf] in
   any context whose constructor table is computable by [cbn].  It is
   [solve_ctor] with the constructor rule itself added as a fallback, so the
   nested [Suc]-fields (themselves constructor applications) are typed
   recursively rather than left for [solve_var]. *)
Ltac solve_nat :=
  unfold two_v, three_v, suc_v, zero_v;
  repeat first
    [ solve_var | solve_lt | progress solve_wf | progress cbn
    | apply Forall2_nil | apply Forall_nil
    | apply Forall2_cons | apply Forall_cons
    | eapply T_Ctor; cbn; try reflexivity ].

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

Theorem typed_downcast_proof : typed_downcast.
Proof.
  unfold typed_downcast, downcast.
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

(* ===================================================================== *)
(* Example terms that USE the polymorphic functions: typing + reduction. *)
(* ===================================================================== *)

Theorem typed_id_example_proof : typed_id_example.
Proof.
  unfold typed_id_example, id_example.
  pose proof typed_id_proof as H. unfold typed_id in H.
  eapply T_TyApp with (S := T_Unit) in H;
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; apply LS_Local; solve_wf ] ]. cbn in H.
  eapply T_App; [ exact H | exact typed_unit_proof ].
Qed.

Theorem typed_downcast_example_proof : typed_downcast_example.
Proof.
  unfold typed_downcast_example, downcast_example.
  pose proof typed_downcast_proof as H. unfold typed_downcast in H.
  eapply T_TyApp with (S := T_Unit) in H;
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; apply LS_Local; solve_wf ] ]. cbn in H.
  eapply T_App; [ exact H | exact typed_unit_proof ].
Qed.

Theorem typed_withFile_example_proof : typed_withFile_example.
Proof.
  unfold typed_withFile_example, withFile_example.
  pose proof typed_withFile_proof as H. unfold typed_withFile in H.
  eapply T_TyApp with (S := T_Unit) in H;
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; apply LS_Local; solve_wf ] ]. cbn in H.
  eapply T_App; [ exact H | ].
  apply T_Lam; [ solve_wf | solve_wf | unfold unit_v; solve_nullary_ctor | cbn; solve_free_sub ].
Qed.

Theorem red_id_example_proof : red_id_example.
Proof.
  unfold red_id_example, id_example, id_poly, unit_v.
  eapply ms_trans. { apply ms_app1; [ reflexivity | ]. apply ms_one. apply S_TyBeta. } cbn.
  apply ms_one. apply S_Beta. repeat constructor.
Qed.

Theorem red_downcast_example_proof : red_downcast_example.
Proof.
  unfold red_downcast_example, downcast_example, downcast, unit_v.
  eapply ms_trans. { apply ms_app1; [ reflexivity | ]. apply ms_one. apply S_TyBeta. } cbn.
  apply ms_one. apply S_Beta. repeat constructor.
Qed.

Theorem red_withFile_example_proof : red_withFile_example.
Proof.
  unfold red_withFile_example, withFile_example, withFile, unit_v, file_v.
  eapply ms_trans. { apply ms_app1; [ reflexivity | ]. apply ms_one. apply S_TyBeta. } cbn.
  eapply ms_trans. { apply ms_one. apply S_Beta. repeat constructor. } cbn.
  apply ms_one. apply S_Beta. repeat constructor.
Qed.

(* [solve_cmd] types a State command [get]/[put n] : Cmd<Nat> (the [put] field
   is a Nat numeral, typed by [solve_nat]). *)
Ltac solve_cmd :=
  eapply T_Ctor; cbn; try reflexivity;
  repeat first
    [ progress solve_wf | solve_lt
    | apply Forall_nil | apply Forall2_nil
    | apply Forall2_cons; [ solve_nat | ] ].

(* [solve_state_perform] discharges a [perform st.<cmd>() : Nat] goal (the 11
   premises of T_Perform for the single State operation [Cmd<Nat> -> Nat]). *)
Ltac solve_state_perform :=
  eapply T_Perform with (Ss := (@nil type));
  [ solve_var | cbn; reflexivity | reflexivity | reflexivity | solve_wf
  | constructor | cbn; reflexivity | cbn; solve_lt_sub | cbn; reflexivity
  | solve_wf | solve_cmd ].


Theorem typed_cons_proof : typed_cons.
Proof.
  unfold typed_cons, cons_fn.
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
      * cbn. solve_lt_sub.
    + cbn. solve_free_sub.
Qed.

Theorem typed_list_example_proof : typed_list_example.
Proof.
  unfold typed_list_example, list_example.
  eapply T_App.
  - eapply T_TyApp with (B := T_Any `Ll) (S := T_File `Ll)
      (U := (`T 0 -{ `Lf }-> T_List `Lf (`T 0) -{ `Ll }-> T_List `Lf (`T 0))).
    + exact typed_cons_proof.
    + solve_wf.
    + apply SA_Any; [ solve_wf | solve_wf | cbn; apply LS_Local; solve_wf ].
  - apply typed_file_local.
Qed.

Theorem typed_compose_proof : typed_compose.
Proof.
  unfold typed_compose, compose_fn.
  apply T_LtLam; [ solve_wf | reflexivity |].
  apply T_LtLam; [ solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
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
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; apply LS_Local; solve_wf ] ]. cbn in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; apply LS_Local; solve_wf ] ]. cbn in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; apply LS_Local; solve_wf ] ]. cbn in H.
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
    apply ms_one. apply S_Beta. repeat constructor. }
  cbn.
  eapply ms_trans.
  { apply ms_app1; [ reflexivity | ].
    apply ms_one. apply S_Beta. repeat constructor. }
  cbn.
  eapply ms_trans. { apply ms_one. apply S_Beta. repeat constructor. } cbn.
  (* now [succ (succ Zero)] — reduce the inner argument under [succ]. *)
  eapply ms_trans.
  { apply ms_app2; [ repeat constructor | reflexivity | ].
    apply ms_one. apply S_Beta. repeat constructor. }
  cbn.
  apply ms_one. apply S_Beta. repeat constructor.
Qed.

(* The following effect-heavy statements exercise the handler typing rules.
   [readerExample] and [exampleOptionality] are fully closed; the remaining
   polymorphic-handler statements document the intended typing targets. *)
Theorem typed_readerExample_proof : typed_readerExample.
Proof.
  unfold typed_readerExample, readerExample, readerExample_op_body.
  eapply T_Handle; try (cbn; reflexivity); try solve_wf; try (cbn; solve_lt_sub).
  - apply SA_Refl. solve_wf.
  - cbn. eapply T_App.
    + solve_var.
    + solve_nat.
  - cbn. eapply T_Perform with (Ss := (@nil type)).
    + solve_var.
    + cbn; reflexivity.
    + reflexivity.
    + reflexivity.
    + solve_wf.
    + constructor.
    + cbn; reflexivity.
    + cbn; solve_lt_sub.
    + cbn; reflexivity.
    + solve_wf.
    + unfold unit_v. solve_ctor.
Qed.

Theorem typed_withReader_proof : typed_withReader.
Proof.
  unfold typed_withReader, withReader.
  apply T_LtLam; [ solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
  eapply T_Handle with
    (T_B := `T 1 -{ `Lf }-> `T 0)
    (T_R := `T 1 -{ `Ll }-> `T 0);
    try (cbn; reflexivity); try solve_wf; try (cbn; solve_lt_sub).
  - eapply SA_Fun; [ apply SA_Refl; solve_wf | solve_lt | apply SA_Refl; solve_wf ].
  - cbn. apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
    eapply T_App with (A := `T 1) (l := `Ll) (B := `T 0).
    + eapply T_App with (A := `T 1) (l := `Ll) (B := `T 1 -{ `Ll }-> `T 0).
      * solve_var.
      * solve_var.
    + solve_var.
  - cbn. eapply T_App with (A := `T 0) (l := `Lf) (B := `T 1 -{ `Lf }-> `T 0).
    + apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
      apply T_Lam; [ solve_wf | solve_wf | solve_var | cbn; solve_lt ].
    + eapply T_App with (A := T_Reader `Ll (`T 1)) (l := `Ll) (B := `T 0).
      * solve_var.
      * solve_var.
Qed.

Ltac solve_state_k_app :=
  eapply T_App with (A := `T 1) (l := `Ll) (B := `T 0);
  [ eapply T_App with (A := `T 1) (l := `Ll) (B := `T 1 -{ `Ll }-> `T 0);
    [ solve_var | solve_var ]
  | solve_var ].

Theorem typed_withState_proof : typed_withState.
Proof.
  unfold typed_withState, withState, state_op_body.
  apply T_LtLam; [ solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
  eapply T_Handle with
    (T_B := `T 1 -{ `Lf }-> `T 0)
    (T_R := `T 1 -{ `Ll }-> `T 0);
    try (cbn; reflexivity); try solve_wf; try (cbn; solve_lt_sub).
  - eapply SA_Fun; [ apply SA_Refl; solve_wf | solve_lt | apply SA_Refl; solve_wf ].
  - cbn. apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
    eapply T_Match with
      (Ts := [`T 1]) (Delta := `Lf) (arity := 0) (lts := [])
      (rho_fields := []) (scrut_result_ty := T_Cmd `Lf (`T 1))
      (result_tag := cmd_tag) (result_l := `Lf)
      (eta := `T 0) (elim_result := `T 0);
      cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt
                      | solve_var | solve_state_k_app ].
    eapply T_Match with
      (Ts := [`T 1]) (Delta := `Lf) (arity := 1) (lts := [])
      (rho_fields := [`T 1]) (scrut_result_ty := T_Cmd `Lf (`T 1))
      (result_tag := cmd_tag) (result_l := `Lf)
      (eta := `T 0) (elim_result := `T 0);
      cbn; try solve [ reflexivity | discriminate | solve_wf | solve_lt
                      | solve_var | solve_state_k_app ].
  - cbn. eapply T_App with (A := `T 0) (l := `Lf) (B := `T 1 -{ `Lf }-> `T 0).
    + apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
      apply T_Lam; [ solve_wf | solve_wf | solve_var | cbn; solve_lt ].
    + eapply T_App with (A := T_State `Ll (`T 1)) (l := `Ll) (B := `T 0).
      * solve_var.
      * solve_var.
Qed.

Theorem typed_withState_example_proof : typed_withState_example.
Proof.
  unfold typed_withState_example, withState_example.
  pose proof typed_withState_proof as H. unfold typed_withState in H.
  eapply T_LtApp with (l := `Lf) in H; [ | solve_wf ]. cbn in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; solve_lt ] ]. cbn in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; solve_lt ] ]. cbn in H.
  eapply T_App; [ | solve_nat ].
  eapply T_App; [ exact H | ].
  unfold withState_prog.
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt_sub ].
  cbn.
  eapply T_App with (l := `Ll).
  - apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt_sub ].
    cbn.
    eapply T_App with (l := `Ll).
    + apply T_Lam; [ solve_wf | solve_wf | solve_state_perform | cbn; solve_lt_sub ].
    + solve_state_perform.
  - solve_state_perform.
Qed.

Theorem typed_withException_proof : typed_withException.
Proof.
  unfold typed_withException, withException, withException_op_body.
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
  eapply T_Handle; try (cbn; reflexivity); try solve_wf; try (cbn; solve_lt_sub).
  - apply SA_Refl. solve_wf.
  - (* op_body: re-raise the caught value as [Error]. *)
    cbn. unfold error_v. solve_ctor.
  - (* body: wrap the handled computation's result in [Ok]. *)
    cbn. unfold ok_v.
    eapply T_Ctor; cbn; try reflexivity;
      repeat first [ solve_lt | progress solve_wf | progress cbn
                   | apply Forall_nil | apply Forall_cons | apply Forall2_nil ].
    apply Forall2_cons; [ | apply Forall2_nil ].
    eapply T_App; [ solve_var | solve_var ].
Qed.

Theorem typed_exampleException_proof : typed_exampleException.
Proof.
  unfold typed_exampleException, exampleException, exampleException_body.
  eapply T_App with
    (A := T_Exception `Ll (T_Nat `Lf) -{ `Lf }-> T_File `Lf)
    (l := `Lf)
    (B := T_Result `Lf (T_Nat `Lf) (T_File `Lf)).
  eapply T_TyApp with
    (B := T_Any `Lf)
    (S := T_File `Lf)
    (U := (T_Exception `Ll (T_Nat `Lf) -{ `Lf }-> `T 0) -{ `Lf }->
          T_Result `Lf (T_Nat `Lf) (`T 0)).
  eapply T_TyApp with
    (B := T_Any `Lf)
    (S := T_Nat `Lf)
    (U := type_ty_all (T_Any `Lf)
            ((T_Exception `Ll (`T 1) -{ `Lf }-> `T 0) -{ `Lf }->
             T_Result `Lf (`T 1) (`T 0))).
  - exact typed_withException_proof.
  - solve_wf.
  - apply SA_Any; [ solve_wf | solve_wf | cbn; solve_lt ].
  - solve_wf.
  - apply SA_Any; [ solve_wf | solve_wf | cbn; solve_lt ].
  - cbn. apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
    cbn. eapply T_Perform with (Ss := [T_File `Lf]).
    + solve_var.
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
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
  eapply T_Handle; try (cbn; reflexivity); try solve_wf; try (cbn; solve_lt_sub).
  - apply SA_Refl. solve_wf.
  - cbn. eapply T_App; [ solve_var | solve_var ].
  - cbn. eapply T_App; [ solve_var | solve_var ].
Qed.

Theorem typed_exampleOptionality_proof : typed_exampleOptionality.
Proof.
  unfold typed_exampleOptionality, exampleOptionality, optionality_op_body.
  eapply T_Handle; try (cbn; reflexivity); try solve_wf; try (cbn; solve_lt_sub).
  - apply SA_Refl. solve_wf.
  - cbn. eapply T_App; [ solve_var | unfold some_v; solve_ctor ].
  - cbn. eapply T_Perform with (Ss := [T_Nat `Lf]).
    + solve_var.
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
Proof. exact I. Qed.

Theorem typed_mapFirst_proof : typed_mapFirst.
Proof. exact I. Qed.

Theorem typed_foldEndo_proof : typed_foldEndo.
Proof. exact I. Qed.

(* ================================================================== *)
(* Negative/error witnesses                                           *)
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
(* Reduction statements                                               *)
(* ================================================================== *)

Theorem red_list_example_proof : red_list_example.
Proof.
  unfold red_list_example, list_example, cons_fn, cons_v.
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole file_v)).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor. apply H_Beta, file_v_value. }
  cbn. apply MS_Refl.
Qed.

Theorem red_readerExample_proof : red_readerExample.
Proof.
  unfold red_readerExample, readerExample, readerExample_op_body.
  eapply MS_Step.
  { apply (S_Handle Reader_tag 0 [T_Nat `Lf] (T_Nat `Lf) (T_Nat `Lf) (($$ 1) @· two_v)
             (term_perform ($$ 0) [] unit_v) 0).
    cbn. intros H. inversion H. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor.
    apply (H_Perform Reader_tag 0 0 [T_Nat `Lf] (T_Nat `Lf) (T_Nat `Lf) (($$ 1) @· two_v) [] unit_v EC_hole);
      [apply unit_v_value | constructor]. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor. apply H_Resume, two_v_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor. apply H_Return, two_v_value. }
  apply MS_Refl.
Qed.

Theorem red_exampleOptionality_proof : red_exampleOptionality.
Proof.
  unfold red_exampleOptionality, exampleOptionality, optionality_op_body, some_v.
  eapply MS_Step.
  { apply (S_Handle Optionality_tag 1 [] (T_Option `Lf (T_Nat `Lf)) (T_Option `Lf (T_Nat `Lf))
             (($$ 1) @· term_ctor some_tag `Lf [] [`T 0] [$$ 0])
             (term_perform ($$ 0) [T_Nat `Lf] three_v) 0).
    cbn. intros H. inversion H. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor.
    apply (H_Perform Optionality_tag 0 1 [] (T_Option `Lf (T_Nat `Lf)) (T_Option `Lf (T_Nat `Lf))
             (($$ 1) @· term_ctor some_tag `Lf [] [`T 0] [$$ 0])
             [T_Nat `Lf] three_v EC_hole);
      [apply three_v_value | constructor]. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor.
    apply H_Resume. repeat constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor.
    apply H_Return. repeat constructor. }
  cbn. apply MS_Refl.
Qed.

Theorem red_exampleException_proof : red_exampleException.
Proof.
  unfold red_exampleException, exampleException, withException,
         withException_op_body, exampleException_body, ok_v, error_v.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_ty_app EC_hole (T_File `Lf))
                     (λ: T_Exception `Ll (T_Nat `Lf) \\
                        term_perform ($$ 0) [T_File `Lf] three_v))).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole
                     (λ: T_Exception `Ll (T_Nat `Lf) \\
                        term_perform ($$ 0) [T_File `Lf] three_v))).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. constructor. }
  cbn.
  eapply MS_Step.
  { eapply (S_Handle _ _ _ _ _ _ _ 0).
    cbn. intros H. inversion H. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_handler_m 0 (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
                     (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
                     (EC_ctor ok_tag `Lf [] [T_Nat `Lf; T_File `Lf] [] EC_hole []))).
    - repeat constructor.
    - apply H_Beta. constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - eapply (H_Perform _ _ _ _ _ _ _ _ _
                (EC_ctor ok_tag `Lf [] [T_Nat `Lf; T_File `Lf] [] EC_hole [])).
      + apply three_v_value.
      + repeat constructor. }
  cbn. apply MS_Refl.
Qed.

Theorem red_withState_example_proof : red_withState_example.
Proof.
  unfold red_withState_example, withState_example, withState, withState_prog,
         state_op_body.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 (EC_ty_app (EC_ty_app EC_hole (T_Nat `Lf))
                                       (T_Nat `Lf)) withState_prog) two_v)).
    - unfold withState_prog. repeat constructor.
    - apply H_LtBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 (EC_ty_app EC_hole (T_Nat `Lf)) withState_prog) two_v)).
    - unfold withState_prog. repeat constructor.
    - apply H_TyBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 EC_hole withState_prog) two_v)).
    - unfold withState_prog. repeat constructor.
    - apply H_TyBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole two_v)).
    - repeat constructor.
    - apply H_Beta. unfold withState_prog. constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_HandleCtx (EC_app1 EC_hole two_v) State_tag 0 [T_Nat `Lf] _ _ _ _ 0).
    - repeat constructor.
    - cbn. intros H. inversion H. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_handler_m 0 _ _ (EC_app2 _ EC_hole)) two_v)).
    - repeat constructor.
    - apply H_Beta. constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole two_v)).
    - repeat constructor.
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ (EC_app2 _ (EC_app2 _ EC_hole))).
      + repeat constructor.
      + repeat constructor. }
  cbn.
  (* reduct-λ applied to the initial state 2 *)
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. apply two_v_value. }
  cbn.
  (* match get_cmd against get_tag: yes branch *)
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply (H_MatchYes get_tag `Lf [] [T_Nat `Lf] []). constructor. }
  cbn.
  (* k(2): resume re-installs the delimiter *)
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole two_v)).
    - repeat constructor.
    - apply H_Resume. apply two_v_value. }
  cbn.
  (* inner beta: continue the program with the get result *)
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_handler_m 0 _ _ (EC_app2 _ EC_hole)) two_v)).
    - repeat constructor.
    - apply H_Beta. apply two_v_value. }
  cbn.
  (* perform put(3) *)
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole two_v)).
    - repeat constructor.
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ (EC_app2 _ (EC_app2 _ EC_hole))).
      + repeat constructor.
      + repeat constructor. }
  cbn.
  (* reduct-λ applied to the current state 2 *)
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. apply two_v_value. }
  cbn.
  (* match put_cmd against get_tag: NO branch *)
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_MatchNo.
      + repeat constructor.
      + unfold get_tag, put_tag. congruence. }
  cbn.
  (* match put_cmd against put_tag: yes branch (binds the new state 3) *)
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply (H_MatchYes put_tag `Lf [] [T_Nat `Lf] [three_v]). repeat constructor. }
  cbn.
  (* k(3) *)
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole three_v)).
    - repeat constructor.
    - apply H_Resume. apply three_v_value. }
  cbn.
  (* inner beta *)
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_handler_m 0 _ _ (EC_app2 _ EC_hole)) three_v)).
    - repeat constructor.
    - apply H_Beta. apply three_v_value. }
  cbn.
  (* perform get *)
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole three_v)).
    - repeat constructor.
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ (EC_app2 _ EC_hole)).
      + repeat constructor.
      + repeat constructor. }
  cbn.
  (* reduct-λ applied to the current state 3 *)
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. apply three_v_value. }
  cbn.
  (* match get_cmd against get_tag: yes branch *)
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply (H_MatchYes get_tag `Lf [] [T_Nat `Lf] []). constructor. }
  cbn.
  (* k(3) *)
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole three_v)).
    - repeat constructor.
    - apply H_Resume. apply three_v_value. }
  cbn.
  (* inner beta: the body is exhausted, produce the post-handler λ *)
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_handler_m 0 _ _ EC_hole) three_v)).
    - repeat constructor.
    - apply H_Beta. apply three_v_value. }
  cbn.
  (* the delimiter's body is a value: H_Return drops the delimiter *)
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole three_v)).
    - repeat constructor.
    - apply H_Return. constructor. }
  cbn.
  (* final application: (λs. 3) 3 *)
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. apply three_v_value. }
  cbn. apply MS_Refl.
Qed.
