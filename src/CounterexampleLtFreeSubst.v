Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.

(* Standalone Phase-0 witness for the lt_free SubstLt obstruction.
   This file is intentionally kept out of _CoqProject: it probes whether
   the direct T_TyApp side-condition failure after lt_free substitution is
   a real preservation counterexample or only a proof artifact. *)

Definition K_bad : ctor_tag := 42.
Definition K_unit : ctor_tag := 43.

Definition T_Any (l : lifetime) : type := type_ctor any_tag l [].
Definition T_Unit : type := type_ctor K_unit lt_free [].
Definition T_LocalData : type := type_ctor K_bad lt_local [].

Definition S_bad : type := type_fun T_LocalData lt_free T_Unit.
Definition U_id : type := type_fun T_Unit lt_free T_Unit.
Definition B_var0 : type := T_Any (lt_var 0).

Definition idabs : term := term_lam (term_var 0) T_Unit.
Definition poly_before : term := term_ty_lam B_var0 idabs.
Definition inner_before : term := term_ty_app poly_before S_bad.
Definition body_before : term := term_lam inner_before T_Unit.
Definition source : term := term_lt_app (term_lt_lam body_before) lt_free.
Definition reduct : term := subst_lt_in_tm 0 lt_free body_before.
Definition source_type : type := type_fun T_Unit lt_free U_id.

Definition source_inner_ctx : ctx := [bind_tm T_Unit; bind_lt lt_local].
Definition reduct_inner_ctx : ctx := [bind_tm T_Unit].
Definition inner_after : term := term_ty_app (term_ty_lam any_at_free idabs) S_bad.

Ltac unfold_witness_defs :=
  unfold source_inner_ctx, reduct_inner_ctx, S_bad, B_var0, T_Any,
    T_LocalData, T_Unit, U_id, any_at_free in *.

Ltac solve_wf :=
  unfold_witness_defs;
  repeat match goal with
  | |- lt_wf _ (lt_var _) => eapply LWF_Var; cbn; reflexivity
  | |- ty_wf _ _ => constructor
  | |- types_wf _ _ => constructor
  | |- lt_wf _ _ => constructor
  | |- ctx_lookup_lt _ _ = Some _ => cbn; reflexivity
  | |- ctx_lookup_ty _ _ = Some _ => cbn; reflexivity
  end.

Ltac solve_var :=
  apply T_Var; [cbn; reflexivity | solve_wf].

Lemma idabs_typed : forall Γ,
  Γ ⊢ₜ idabs : U_id.
Proof.
  intros Γ. unfold idabs, U_id.
  apply T_Lam; try solve_wf.
  - solve_var.
  - simpl. apply LS_Refl. solve_wf.
Qed.

Lemma S_bad_sub_B_var0_source :
  source_inner_ctx ⊢ S_bad <:: B_var0.
Proof.
  unfold source_inner_ctx, S_bad, B_var0, T_Any.
  apply SA_Any.
  - solve_wf.
  - apply LWF_Var with (Δ := lt_local). reflexivity.
  - simpl. apply LS_Free. apply LWF_Var with (Δ := lt_local). reflexivity.
Qed.

Lemma source_tyapp_side_condition_true :
  ty_app_arg_no_local source_inner_ctx B_var0 S_bad = true.
Proof. reflexivity. Qed.

Lemma poly_before_typed :
  source_inner_ctx ⊢ₜ poly_before : type_ty_all B_var0 U_id.
Proof.
  unfold poly_before.
  apply T_TyLam; try solve_wf.
  - reflexivity.
  - apply idabs_typed.
Qed.

Lemma inner_before_typed :
  source_inner_ctx ⊢ₜ inner_before : U_id.
Proof.
  unfold inner_before.
  change U_id with (subst_ty 0 S_bad U_id).
  eapply T_TyApp with (B := B_var0).
  - apply poly_before_typed.
  - solve_wf.
  - apply S_bad_sub_B_var0_source.
  - apply source_tyapp_side_condition_true.
Qed.

Lemma body_before_typed_under_lt :
  [bind_lt lt_local] ⊢ₜ body_before : source_type.
Proof.
  unfold body_before, source_type.
  apply T_Lam; try solve_wf.
  - apply inner_before_typed.
  - simpl. apply LS_Refl. solve_wf.
Qed.

Lemma source_typed :
  [] ⊢ₜ source : source_type.
Proof.
  unfold source.
  change source_type with (subst_lt_in_ty 0 lt_free source_type).
  apply T_LtApp.
  - apply T_LtLam; try solve_wf.
    + reflexivity.
    + apply body_before_typed_under_lt.
  - apply LWF_Free.
Qed.

Lemma source_steps_to_reduct :
  source ==> reduct.
Proof.
  unfold source, reduct. apply S_LtBeta.
Qed.

Lemma direct_reduct_side_condition_false :
  ty_app_arg_no_local reduct_inner_ctx any_at_free S_bad = false.
Proof. reflexivity. Qed.

Lemma S_bad_sub_any_free_reduct :
  reduct_inner_ctx ⊢ S_bad <:: any_at_free.
Proof.
  unfold reduct_inner_ctx, S_bad, any_at_free.
  apply SA_Any.
  - solve_wf.
  - solve_wf.
  - simpl. apply LS_Refl. solve_wf.
Qed.

Lemma poly_after_typed_principal :
  reduct_inner_ctx ⊢ₜ term_ty_lam any_at_free idabs : type_ty_all any_at_free U_id.
Proof.
  apply T_TyLam; try solve_wf.
  - reflexivity.
  - apply idabs_typed.
Qed.

Lemma poly_after_forall_sub_bad_bound :
  reduct_inner_ctx ⊢ type_ty_all any_at_free U_id <:: type_ty_all S_bad U_id.
Proof.
  apply SA_TyAll; try solve_wf.
  - apply S_bad_sub_any_free_reduct.
  - apply SA_Refl. solve_wf.
Qed.

Lemma poly_after_typed_bad_bound :
  reduct_inner_ctx ⊢ₜ term_ty_lam any_at_free idabs : type_ty_all S_bad U_id.
Proof.
  eapply T_Sub.
  - apply poly_after_typed_principal.
  - apply poly_after_forall_sub_bad_bound.
Qed.

Lemma reduct_inner_typed :
  reduct_inner_ctx ⊢ₜ inner_after : U_id.
Proof.
  unfold inner_after.
  change U_id with (subst_ty 0 S_bad U_id).
  eapply T_TyApp with (B := S_bad).
  - apply poly_after_typed_bad_bound.
  - solve_wf.
  - apply SA_Refl. solve_wf.
  - reflexivity.
Qed.

Lemma reduct_simpl :
  reduct = term_lam inner_after T_Unit.
Proof. reflexivity. Qed.

Lemma reduct_typed :
  [] ⊢ₜ reduct : source_type.
Proof.
  rewrite reduct_simpl. unfold source_type.
  apply T_Lam; try solve_wf.
  - apply reduct_inner_typed.
  - simpl. apply LS_Refl. solve_wf.
Qed.

(* Verdict: the direct post-substitution T_TyApp side-condition is false,
   but the reduct is still typable by subsuming the type abstraction from
   [forall alpha <: Any@free] to [forall alpha <: S_bad] before applying it.
   Thus this witness is not a preservation counterexample; it points to a
   missing proof move in the R = lt_free case of lifetime substitution. *)