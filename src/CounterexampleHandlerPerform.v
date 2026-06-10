Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import SubstitutionTheory.
Require Import Safety.

Definition ce_any : type := type_ctor any_tag lt_free [].
Definition ce_sig : type := type_ctor 2 lt_local [].
Definition ce_ret : type := type_ctor 3 lt_local [].
Definition ce_Gamma : ctx :=
  [bind_eff 1 0 0 ce_sig ce_ret;
   bind_eff 2 0 0 ce_any ce_any].

Definition ce_arg_op : term := term_var 0.
Definition ce_arg : term := term_cap 2 0 0 [] ce_arg_op.
Definition ce_op_body : term := term_var 0.
Definition ce_cap : term := term_cap 1 0 0 [] ce_op_body.
Definition ce_perform : term := term_perform ce_cap [] ce_arg.

Lemma ce_eval_ctx : eval_ctx ce_Gamma.
Proof.
  unfold ce_Gamma.
  apply ec_eff; [unfold any_tag; lia|].
  apply ec_eff; [unfold any_tag; lia|].
  constructor.
Qed.

Lemma ce_ty_wf_any : ty_wf ce_Gamma ce_any.
Proof. unfold ce_any. constructor; constructor. Qed.

Lemma ce_ty_wf_sig : ty_wf ce_Gamma ce_sig.
Proof. unfold ce_sig. constructor; constructor. Qed.

Lemma ce_ty_wf_ret : ty_wf ce_Gamma ce_ret.
Proof. unfold ce_ret. constructor; constructor. Qed.

Lemma ce_arg_typed : ce_Gamma ⊢ₜ ce_arg : ce_sig.
Proof.
  unfold ce_arg, ce_arg_op, ce_sig.
  eapply T_Cap with
    (n_α := 0) (n_β := 0)
    (sig := ce_any) (ret := ce_any)
    (T_R := ce_any)
    (sig_β := ce_any) (ret_β := ce_any).
  - reflexivity.
  - reflexivity.
  - constructor.
  - exact ce_ty_wf_any.
  - reflexivity.
  - reflexivity.
  - simpl. apply T_Var.
    + reflexivity.
    + unfold ce_any. constructor; constructor.
Qed.

Lemma ce_cap_typed : ce_Gamma ⊢ₜ ce_cap : type_ctor 1 lt_local [].
Proof.
  unfold ce_cap, ce_op_body.
  eapply T_Cap with
    (n_α := 0) (n_β := 0)
    (sig := ce_sig) (ret := ce_ret)
    (T_R := ce_sig)
    (sig_β := ce_sig) (ret_β := ce_ret).
  - reflexivity.
  - reflexivity.
  - constructor.
  - exact ce_ty_wf_sig.
  - reflexivity.
  - reflexivity.
  - simpl. apply T_Var.
    + reflexivity.
    + unfold ce_sig. constructor; constructor.
Qed.

Lemma ce_perform_typed : ce_Gamma ⊢ₜ ce_perform : ce_ret.
Proof.
  unfold ce_perform.
  eapply T_Perform with
    (E_tag := 1) (Δ := lt_local) (Ts := [])
    (n_α := 0) (n_β := 0)
    (sig := ce_sig) (ret := ce_ret)
    (sig_inst := ce_sig) (ret_inst := ce_ret).
  - exact ce_cap_typed.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - constructor.
  - reflexivity.
  - reflexivity.
  - exact ce_ty_wf_ret.
  - exact ce_arg_typed.
Qed.

Lemma ce_arg_typing_sub : forall T,
  ce_Gamma ⊢ₜ ce_arg : T -> ce_Gamma ⊢ ce_sig <:: T.
Proof.
  intros T Hty.
  remember ce_Gamma as G eqn:HG.
  remember ce_arg as t eqn:Ht.
  revert HG Ht.
  induction Hty; intros HG Ht; subst; try discriminate.
  - eapply SA_Trans; eauto.
  - injection Ht; intros; subst.
    apply SA_Refl. exact ce_ty_wf_sig.
Qed.

Lemma ce_arg_not_ret : ~ ce_Gamma ⊢ₜ ce_arg : ce_ret.
Proof.
  intros Hbad.
  pose proof (ce_arg_typing_sub _ Hbad) as Hsub.
  destruct (sub_ctor_inv ce_Gamma ce_sig 3 lt_local [] ce_eval_ctx Hsub)
    as [l [Heq _]].
  - unfold any_tag; lia.
  - discriminate Heq.
Qed.

Theorem handler_perform_preservation_counterexample : False.
Proof.
  pose proof
    (handler_perform_preservation ce_Gamma 0 ce_ret 1 0 [] ce_op_body [] ce_arg EC_hole
      ce_eval_ctx ce_perform_typed (value_cap 2 0 0 [] ce_arg_op) (pem_hole 0))
    as Hbad.
  simpl in Hbad.
  exact (ce_arg_not_ret Hbad).
Qed.
