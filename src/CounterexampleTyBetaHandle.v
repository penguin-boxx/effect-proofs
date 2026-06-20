Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import EvalCtx.
Require Import Narrowing.
Require Import Preservation.

(* Standalone Phase-0 witness for the TyBeta/no-local obstruction.
   This file is intentionally kept out of _CoqProject: it probes why
   beta preservation cannot be recovered just by substituting through a
   body typed under an Any@free bound. *)

Definition E_bad : eff_tag := 51.
Definition K_bad : ctor_tag := 52.
Definition K_unit : ctor_tag := 53.

Definition T_Unit : type := type_ctor K_unit lt_free [].
Definition T_LocalData : type := type_ctor K_bad lt_local [].
Definition S_bad : type := type_fun T_LocalData lt_free T_Unit.
Definition U_handle : type := type_fun (type_var 0) lt_local any_at_free.

Definition base_ctx : ctx := [bind_eff E_bad 0 0 any_at_free any_at_free].
Definition lam_ctx : ctx := bind_ty any_at_free :: base_ctx.
Definition body_ctx : ctx := bind_tm (type_var 0) :: lam_ctx.

Definition op_body : term := term_var 0.
Definition handler_body : term := term_var 1.
Definition guarded_handle : term :=
  term_handle E_bad 0 [] (type_var 0) any_at_free op_body handler_body.
Definition guarded_lam : term := term_lam guarded_handle (type_var 0).
Definition poly_guarded : term := term_ty_lam any_at_free guarded_lam.
Definition guarded_redex : term := term_ty_app poly_guarded S_bad.
Definition guarded_reduct : term := subst_ty_in_tm 0 S_bad guarded_lam.

Ltac unfold_probe_defs :=
  unfold base_ctx, lam_ctx, body_ctx, S_bad, T_LocalData, T_Unit,
    U_handle, any_at_free in *.

Ltac solve_probe_wf :=
  unfold_probe_defs;
  repeat match goal with
  | |- ty_wf _ _ => constructor
  | |- types_wf _ _ => constructor
  | |- lt_wf _ _ => constructor
  | |- ctx_lookup_ty _ _ = Some _ => cbn; reflexivity
  | |- ctx_lookup_eff _ _ = Some _ => cbn; reflexivity
  end.

Lemma S_bad_sub_any_base :
  base_ctx ⊢ S_bad <:: any_at_free.
Proof.
  unfold base_ctx, S_bad, any_at_free, T_LocalData, T_Unit.
  apply SA_Any.
  - solve_probe_wf.
  - solve_probe_wf.
  - simpl. apply LS_Refl. solve_probe_wf.
Qed.

Lemma op_body_typed :
  (bind_tm any_at_free
   :: bind_tm (type_fun any_at_free lt_local any_at_free)
   :: body_ctx) ⊢ₜ op_body : any_at_free.
Proof.
  unfold op_body. apply T_Var; [cbn; reflexivity | solve_probe_wf].
Qed.

Lemma handler_body_typed :
  (bind_tm (type_ctor E_bad lt_local []) :: body_ctx) ⊢ₜ handler_body : type_var 0.
Proof.
  unfold handler_body. apply T_Var; [cbn; reflexivity |].
  unfold body_ctx, lam_ctx, base_ctx, any_at_free.
  econstructor; [cbn; reflexivity | solve_probe_wf].
Qed.

Lemma guarded_handle_typed :
  body_ctx ⊢ₜ guarded_handle : any_at_free.
Proof.
  unfold guarded_handle.
  eapply T_Handle with
    (n_α := 0) (n_β := 0) (sig := any_at_free) (ret := any_at_free)
    (sig_β := any_at_free) (ret_β := any_at_free).
  - cbn. reflexivity.
  - reflexivity.
  - constructor.
  - unfold body_ctx, lam_ctx, base_ctx, any_at_free.
    econstructor; [cbn; reflexivity | solve_probe_wf].
  - solve_probe_wf.
  - reflexivity.
  - apply SA_VarCtx.
    + cbn. reflexivity.
    + unfold body_ctx, lam_ctx, base_ctx, any_at_free.
      constructor; [constructor | constructor].
  - reflexivity.
  - reflexivity.
  - exact op_body_typed.
  - exact handler_body_typed.
Qed.

Lemma guarded_lam_typed :
  lam_ctx ⊢ₜ guarded_lam : U_handle.
Proof.
  unfold guarded_lam, U_handle.
  apply T_Lam.
  - unfold lam_ctx, base_ctx, any_at_free.
    econstructor; [cbn; reflexivity | constructor; [constructor | constructor]].
  - solve_probe_wf.
  - exact guarded_handle_typed.
  - simpl. apply LS_Free. solve_probe_wf.
Qed.

Lemma poly_guarded_principal :
  base_ctx ⊢ₜ poly_guarded : type_ty_all any_at_free U_handle.
Proof.
  unfold poly_guarded.
  apply T_TyLam.
  - solve_probe_wf.
  - unfold U_handle, lam_ctx, base_ctx, any_at_free.
    constructor.
    + econstructor; [cbn; reflexivity | constructor; [constructor | constructor]].
    + constructor.
    + constructor; [constructor | constructor].
  - reflexivity.
  - exact guarded_lam_typed.
Qed.

Lemma poly_guarded_sub_bad_bound :
  base_ctx ⊢ type_ty_all any_at_free U_handle <:: type_ty_all S_bad U_handle.
Proof.
  apply SA_TyAll.
  - unfold U_handle, base_ctx, any_at_free.
    constructor.
    + econstructor; [cbn; reflexivity | constructor; [constructor | constructor]].
    + constructor.
    + constructor; [constructor | constructor].
  - unfold U_handle, base_ctx, S_bad, T_LocalData, T_Unit, any_at_free.
    constructor.
    + econstructor; [cbn; reflexivity | constructor; solve_probe_wf].
    + constructor.
    + constructor; [constructor | constructor].
  - apply S_bad_sub_any_base.
  - apply SA_Refl.
    unfold U_handle, base_ctx, S_bad, T_LocalData, T_Unit, any_at_free.
    constructor.
    + econstructor; [cbn; reflexivity | constructor; solve_probe_wf].
    + constructor.
    + constructor; [constructor | constructor].
Qed.

Lemma poly_guarded_typed_bad_bound :
  base_ctx ⊢ₜ poly_guarded : type_ty_all S_bad U_handle.
Proof.
  eapply T_Sub.
  - apply poly_guarded_principal.
  - apply poly_guarded_sub_bad_bound.
Qed.

Lemma guarded_redex_typed :
  base_ctx ⊢ₜ guarded_redex : subst_ty 0 S_bad U_handle.
Proof.
  unfold guarded_redex.
  eapply T_TyApp with (B := S_bad).
  - apply poly_guarded_typed_bad_bound.
  - solve_probe_wf.
  - apply SA_Refl. solve_probe_wf.
  - reflexivity.
Qed.

Lemma guarded_redex_steps :
  guarded_redex ==> guarded_reduct.
Proof.
  unfold guarded_redex, guarded_reduct. apply S_TyBeta.
Qed.

Definition reduct_body_ctx : ctx := bind_tm S_bad :: base_ctx.

Lemma guarded_reduct_simpl :
  guarded_reduct =
  term_lam (term_handle E_bad 0 [] S_bad any_at_free op_body handler_body) S_bad.
Proof. reflexivity. Qed.

Lemma guarded_reduct_handle_no_local_false :
  no_local_ty_G reduct_body_ctx S_bad = false.
Proof. reflexivity. Qed.

Lemma base_ctx_eval :
  eval_ctx base_ctx.
Proof.
  unfold base_ctx, E_bad, any_at_free.
  apply ec_eff.
  - discriminate.
  - simpl. repeat constructor.
  - simpl. repeat constructor.
  - constructor.
Qed.

Lemma guarded_reduct_inner_handle_untypable : forall T,
  ~ reduct_body_ctx ⊢ₜ
      term_handle E_bad 0 [] S_bad any_at_free op_body handler_body : T.
Proof.
  intros T Hty.
  destruct (handle_typing_inv _ _ _ _ _ _ _ _ _ Hty) as
    (n_α & sig & ret & sig_β & ret_β & Heff & HlenTs & HwfTs & HwfTB & HwfTR &
     HnoLocal & Hsub & Hsigβ & Hretβ & Hop & Hbody & Hres).
  unfold reduct_body_ctx, S_bad, T_LocalData, T_Unit in HnoLocal.
  discriminate HnoLocal.
Qed.

Lemma guarded_reduct_untypable : forall T,
  ~ base_ctx ⊢ₜ guarded_reduct : T.
Proof.
  intros T Hty.
  rewrite guarded_reduct_simpl in Hty.
  destruct (lam_typing_inv _ _ _ _ Hty) as (l & B & Hbody & Hsub).
  eapply guarded_reduct_inner_handle_untypable. exact Hbody.
Qed.

Theorem tybeta_preservation_counterexample :
  exists Γ bound body S T,
    eval_ctx Γ /\
    Γ ⊢ₜ term_ty_app (term_ty_lam bound body) S : T /\
    term_ty_app (term_ty_lam bound body) S ==> subst_ty_in_tm 0 S body /\
    ~ Γ ⊢ₜ subst_ty_in_tm 0 S body : T.
Proof.
  exists base_ctx, any_at_free, guarded_lam, S_bad, (subst_ty 0 S_bad U_handle).
  repeat split.
  - apply base_ctx_eval.
  - exact guarded_redex_typed.
  - exact guarded_redex_steps.
  - apply guarded_reduct_untypable.
Qed.

(* Verdict: the redex is typable by first subsuming the type abstraction
   from [forall alpha <: Any@free] to [forall alpha <: S_bad].  The beta
   reduct then exposes a handler whose return type is [S_bad], and the
   T_Handle no-local premise is false.  This isolates the missing proof
   obligation behind [tybeta_preserves]: a successful proof needs a real
   body conversion/narrowing argument, not the declared-bound
   [typing_SubstTy] theorem. *)