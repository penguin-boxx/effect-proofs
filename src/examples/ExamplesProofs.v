Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Decide.
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

(* [solve_lt_var] extends [solve_lt] with one more move: descend through
   a lifetime variable's declared bound (LS_Trans + LS_Var).  Needed for
   match-fresh lifetime variables, whose bound is the (shifted) scrutinee
   lifetime. *)
Ltac solve_lt_var :=
  solve [ apply LS_Refl; solve_wf
        | apply LS_Free; solve_wf
        | eapply LS_Trans;
          [ eapply LS_Var; [ cbn; reflexivity | solve_wf ] | solve_lt_var ]
        | apply LS_MinR1; [ solve_lt_var | solve_wf ]
        | apply LS_MinR2; [ solve_lt_var | solve_wf ]
        | apply LS_MinL; [ solve_lt_var | solve_lt_var ] ].

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
      * (* Forall2 field typings *)
        constructor; [ | constructor; [ | constructor ] ].
        -- (* thunk1 = λ(). f (h ()) *)
           apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt_var ].
           eapply T_App; [ solve_var |].
           eapply T_App; [ solve_var |].
           solve_nullary_ctor.
        -- (* thunk2 = λ(). self (t ()) f *)
           apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt_var ].
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
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt_sub ].
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt_sub ].
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
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
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
             (term_perform ($$ 0) [] (T_Nat `Lf) unit_v) 0).
    cbn. intros H. inversion H. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor.
    apply (H_Perform Reader_tag 0 0 [T_Nat `Lf] (T_Nat `Lf) (T_Nat `Lf) (($$ 1) @· two_v) [] (T_Nat `Lf) unit_v EC_hole);
      [apply unit_v_value | constructor]. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor. apply H_Beta, two_v_value. }
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
             (term_perform ($$ 0) [T_Nat `Lf] (T_Option `Lf (T_Nat `Lf)) three_v) 0).
    cbn. intros H. inversion H. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor.
    apply (H_Perform Optionality_tag 0 1 [] (T_Option `Lf (T_Nat `Lf)) (T_Option `Lf (T_Nat `Lf))
             (($$ 1) @· term_ctor some_tag `Lf [] [`T 0] [$$ 0])
             [T_Nat `Lf] (T_Option `Lf (T_Nat `Lf)) three_v EC_hole);
      [apply three_v_value | constructor]. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta. repeat constructor. }
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
                        term_perform ($$ 0) [T_File `Lf] (T_File `Lf) three_v))).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole
                     (λ: T_Exception `Ll (T_Nat `Lf) \\
                        term_perform ($$ 0) [T_File `Lf] (T_File `Lf) three_v))).
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
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _
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
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _ (EC_app2 _ (EC_app2 _ EC_hole))).
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
    - apply H_Beta. apply two_v_value. }
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
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _ (EC_app2 _ (EC_app2 _ EC_hole))).
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
    - apply H_Beta. apply three_v_value. }
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
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _ (EC_app2 _ EC_hole)).
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
    - apply H_Beta. apply three_v_value. }
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

Lemma four_v_value : value four_v.
Proof. unfold four_v, three_v, suc_v, zero_v. repeat constructor. Qed.

Lemma endoi_v_value : value endoi_v.
Proof. unfold endoi_v. constructor. constructor; [ constructor | constructor ]. Qed.

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
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; solve_lt ] ]. cbn in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; solve_lt ] ]. cbn in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; solve_lt ] ]. cbn in H.
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
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole (term_ctor endoi_tag `Lf [`Lf] [] [succ_fn]))).
    - repeat constructor.
    - apply H_Beta. apply two_v_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. repeat constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply (H_MatchYes endoi_tag `Lf [`Lf] [] [succ_fn]). repeat constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. apply three_v_value. }
  cbn. apply MS_Refl.
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
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 (EC_app1 EC_hole p00) p23) succ_fn)).
    - unfold p00, p23; repeat constructor.
    - apply H_TyBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 EC_hole p23) succ_fn)).
    - unfold p23; repeat constructor.
    - apply H_Beta. unfold p00; repeat constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole succ_fn)).
    - repeat constructor.
    - apply H_Beta. unfold p23; repeat constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply (H_MatchYes pair_tag `Lf [] [T_Nat `Lf; T_Nat `Lf] [two_v; three_v]).
      repeat constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_ctor pair_tag `Lf [] [T_Nat `Lf; T_Nat `Lf] [] EC_hole [three_v])).
    - repeat constructor.
    - apply H_Beta. apply two_v_value. }
  cbn. apply MS_Refl.
Qed.

Theorem typed_withReader_example_proof : typed_withReader_example.
Proof.
  unfold typed_withReader_example, withReader_example.
  pose proof typed_withReader_proof as H. unfold typed_withReader in H.
  eapply T_LtApp with (l := `Lf) in H; [ | solve_wf ]. cbn in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; solve_lt ] ]. cbn in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; solve_lt ] ]. cbn in H.
  eapply T_App; [ | solve_nat ].
  eapply T_App; [ exact H | ].
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt_sub ].
  eapply T_Perform with (Ss := (@nil type)).
  - solve_var.
  - cbn; reflexivity.
  - reflexivity.
  - reflexivity.
  - solve_wf.
  - constructor.
  - cbn; reflexivity.
  - cbn; solve_lt_sub.
  - cbn; reflexivity.
  - solve_wf.
  - unfold unit_v. solve_ctor.
Qed.

Theorem typed_withId_example_proof : typed_withId_example.
Proof.
  unfold typed_withId_example, withId_example.
  pose proof typed_withId_proof as H. unfold typed_withId in H.
  eapply T_TyApp with (S := T_Nat `Lf) in H;
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; solve_lt ] ]. cbn in H.
  eapply T_App; [ exact H | ].
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt_sub ].
  eapply T_Perform with (Ss := [T_Nat `Lf]).
  - solve_var.
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
  { apply (S_step (EC_app1 (EC_app1 (EC_ty_app (EC_ty_app
      EC_hole (T_Nat `Lf)) (T_Nat `Lf))
      (λ: T_Reader `Ll (T_Nat `Lf) \\ term_perform ($$ 0) [] (T_Nat `Lf) unit_v)) two_v)).
    - repeat constructor.
    - apply H_LtBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1 (EC_ty_app
      EC_hole (T_Nat `Lf))
      (λ: T_Reader `Ll (T_Nat `Lf) \\ term_perform ($$ 0) [] (T_Nat `Lf) unit_v)) two_v)).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_app1
      EC_hole
      (λ: T_Reader `Ll (T_Nat `Lf) \\ term_perform ($$ 0) [] (T_Nat `Lf) unit_v)) two_v)).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole two_v)).
    - repeat constructor.
    - apply H_Beta. constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_HandleCtx (EC_app1 EC_hole two_v) Reader_tag 0 [T_Nat `Lf] _ _ _ _ 0).
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
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _ (EC_app2 _ EC_hole)).
      + repeat constructor.
      + repeat constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. apply two_v_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole two_v)).
    - repeat constructor.
    - apply H_Beta. apply two_v_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 (EC_handler_m 0 _ _ EC_hole) two_v)).
    - repeat constructor.
    - apply H_Beta. apply two_v_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole two_v)).
    - repeat constructor.
    - apply H_Return. constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. apply two_v_value. }
  cbn. apply MS_Refl.
Qed.

Theorem red_withId_example_proof : red_withId_example.
Proof.
  unfold red_withId_example, withId_example, withId, withId_op_body.
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole
      (λ: T_Id `Ll \\ term_perform ($$ 0) [T_Nat `Lf] (T_Nat `Lf) two_v))).
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
  { apply (S_step (EC_handler_m 0 (T_Nat `Lf) (T_Nat `Lf) EC_hole)).
    - repeat constructor.
    - apply H_Beta. constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _ EC_hole).
      + apply two_v_value.
      + constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. apply two_v_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Return. apply two_v_value. }
  apply MS_Refl.
Qed.

Theorem typed_getOrElse_proof : typed_getOrElse.
Proof.
  unfold typed_getOrElse, getOrElse.
  apply T_TyLam; [ solve_wf | solve_wf | reflexivity |].
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt ].
  apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt_sub ].
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
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; solve_lt ] ]. cbn in H.
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
    [ | solve_wf | apply SA_Any; [ solve_wf | solve_wf | cbn; solve_lt ] ]. cbn in H.
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

Theorem typed_multishotExample_proof : typed_multishotExample.
Proof.
  unfold typed_multishotExample, multishotExample, multishot_op_body.
  eapply T_Handle; try (cbn; reflexivity); try solve_wf; try (cbn; solve_lt_sub).
  - apply SA_Refl. solve_wf.
  - cbn. eapply T_App with (A := T_Nat `Lf) (l := `Ll) (B := T_Nat `Lf).
    + apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt_sub ].
      eapply T_App; [ solve_var | solve_nat ].
    + eapply T_App; [ solve_var | solve_nat ].
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

Theorem typed_forwardExample_proof : typed_forwardExample.
Proof.
  unfold typed_forwardExample, forwardExample, forward_inner_body,
         error_v, ok_v.
  eapply T_Handle; try (cbn; reflexivity); try solve_wf; try (cbn; solve_lt_sub).
  - apply SA_Refl. solve_wf.
  - (* throw clause: Error<Nat,File>(e) *)
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
      eapply T_Handle; try (cbn; reflexivity); try solve_wf; try (cbn; solve_lt_sub).
      * apply SA_Refl. solve_wf.
      * (* ask clause: resume(2) *)
        cbn. eapply T_App; [ solve_var | solve_nat ].
      * (* let x = ask in throw x *)
        cbn. eapply T_App with (A := T_Nat `Lf) (l := `Ll) (B := T_File `Lf).
        -- apply T_Lam; [ solve_wf | solve_wf | | cbn; solve_lt_sub ].
           eapply T_Perform with (Ss := [T_File `Lf]).
           ++ solve_var.
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
        -- eapply T_Perform with (Ss := (@nil type)).
           ++ solve_var.
           ++ cbn; reflexivity.
           ++ reflexivity.
           ++ reflexivity.
           ++ solve_wf.
           ++ constructor.
           ++ cbn; reflexivity.
           ++ cbn; solve_lt_sub.
           ++ cbn; reflexivity.
           ++ solve_wf.
           ++ unfold unit_v. solve_ctor.
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
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole (term_ctor some_tag `Lf [] [T_Nat `Lf] [three_v]))).
    - repeat constructor.
    - apply H_Beta. repeat constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. repeat constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply (H_MatchYes some_tag `Lf [] [T_Nat `Lf] [three_v]). repeat constructor. }
  cbn. apply MS_Refl.
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
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole (term_ctor none_tag `Lf [] [T_Nat `Lf] []))).
    - repeat constructor.
    - apply H_Beta. repeat constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. repeat constructor. }
  cbn.
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
  { apply (S_step (EC_app1 (EC_app1 EC_hole file_v)
                     (term_ctor nil_tag `Lf [] [T_File `Ll] []))).
    - repeat constructor.
    - apply H_TyBeta. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app1 EC_hole (term_ctor nil_tag `Lf [] [T_File `Ll] []))).
    - repeat constructor.
    - apply H_Beta. apply file_v_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. repeat constructor. }
  cbn. apply MS_Refl.
Qed.

Theorem red_multishotExample_proof : red_multishotExample.
Proof.
  unfold red_multishotExample, multishotExample, multishot_op_body.
  eapply MS_Step.
  { eapply (S_Handle _ _ _ _ _ _ _ 0).
    cbn. intros H. inversion H. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _ EC_hole).
      + repeat constructor.
      + constructor. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app2 _ EC_hole)).
    - repeat constructor.
    - apply H_Beta. apply two_v_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_app2 _ EC_hole)).
    - repeat constructor.
    - apply H_Return. apply two_v_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. apply two_v_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Beta. apply three_v_value. }
  cbn.
  eapply MS_Step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Return. apply three_v_value. }
  apply MS_Refl.
Qed.

Theorem red_forwardExample_proof : red_forwardExample.
Proof.
  unfold red_forwardExample, forwardExample, forward_inner_body, error_v, ok_v.
  eapply MS_Step.
  { eapply (S_Handle _ _ _ _ _ _ _ 0).
    cbn. intros H. inversion H. }
  cbn.
  eapply MS_Step.
  { apply (S_HandleCtx
      (EC_handler_m 0 (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
                      (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
        (EC_ctor ok_tag `Lf [] [T_Nat `Lf; T_File `Lf] [] EC_hole []))
      Reader_tag 0 [T_Nat `Lf] (T_File `Lf) (T_File `Lf) _ _ 1).
    - repeat constructor.
    - cbn. intros H.
      repeat (destruct H as [H|H]; [ discriminate H |]). exact H. }
  cbn.
  eapply MS_Step.
  { apply (S_step (EC_handler_m 0 (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
                      (T_Result `Lf (T_Nat `Lf) (T_File `Lf))
        (EC_ctor ok_tag `Lf [] [T_Nat `Lf; T_File `Lf] [] EC_hole []))).
    - repeat constructor.
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _ (EC_app2 _ EC_hole)).
      + repeat constructor.
      + repeat constructor. }
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
    - eapply (H_Perform _ _ _ _ _ _ _ _ _ _
        (EC_ctor ok_tag `Lf [] [T_Nat `Lf; T_File `Lf] []
          (EC_handler_m 1 (T_File `Lf) (T_File `Lf) EC_hole) [])).
      + apply two_v_value.
      + apply pem_ctor. apply pem_handler_m; [ discriminate | apply pem_hole ]. }
  cbn. apply MS_Refl.
Qed.
