Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import SubstitutionTheory.

(* The no-local side condition threaded through typing_SubstTy: when the
   substituted variable n is treated as no-local (its bound is Any@free),
   the replacement Sb must itself be no-local.  This is exactly
   ty_app_arg_no_local, supplied by T_TyApp at the use sites. *)
Definition subst_nl (Sb : type) (n : nat) (Γ G' : ctx) : Prop :=
  no_local_ty_G Γ (type_var n) = true -> no_local_ty_G G' Sb = true.

Lemma subst_nl_bind_ty : forall Sb n Γ G' B,
  subst_nl Sb n Γ G' ->
  subst_nl (shift_ty 1 0 Sb) (S n) (bind_ty B :: Γ) (bind_ty (subst_ty n Sb B) :: G').
Proof.
  intros Sb n Γ G' B H Hnl.
  apply (no_local_ty_G_InsTy G' Sb 0 (bind_ty (subst_ty n Sb B) :: G') (InsTy_here _ _)).
  apply H. rewrite no_local_ty_G_var_bind_ty_S in Hnl. exact Hnl.
Qed.

Lemma subst_nl_bind_lt : forall Sb n Γ G' D,
  subst_nl Sb n Γ G' ->
  subst_nl (shift_lt_in_ty 1 0 Sb) n (bind_lt D :: Γ) (bind_lt D :: G').
Proof.
  intros Sb n Γ G' D H Hnl.
  apply (no_local_ty_G_InsLt G' Sb 0 (bind_lt D :: G') (InsLt_here _ _)).
  apply H. rewrite no_local_ty_G_var_bind_lt in Hnl. exact Hnl.
Qed.

Lemma subst_nl_bind_tm : forall Sb n Γ G' A,
  subst_nl Sb n Γ G' ->
  subst_nl Sb n (bind_tm A :: Γ) (bind_tm (subst_ty n Sb A) :: G').
Proof.
  intros Sb n Γ G' A H Hnl.
  apply (no_local_ty_G_InsTm G' Sb (bind_tm (subst_ty n Sb A) :: G') (InsTm_here _ _)).
  apply H. cbn in Hnl. exact Hnl.
Qed.

Lemma subst_nl_push_ty_vars : forall k Sb n Γ G',
  subst_nl Sb n Γ G' ->
  subst_nl (shift_ty k 0 Sb) (k + n)
    (push_ty_vars k any_at_free Γ) (push_ty_vars k any_at_free G').
Proof.
  induction k as [|k IH]; intros Sb n Γ G' H; simpl.
  - rewrite shift_ty_zero. replace (0 + n) with n by lia. exact H.
  - replace (shift_ty (S k) 0 Sb) with (shift_ty k 0 (shift_ty 1 0 Sb)).
    2:{ rewrite shift_ty_fuse. replace (k + 1) with (S k) by lia. reflexivity. }
    replace (S (k + n)) with (k + S n) by lia.
    apply IH. rewrite <- (subst_ty_any_at_free n Sb).
    apply subst_nl_bind_ty. exact H.
Qed.

Lemma forallb_no_local_ty_G_subst_ty : forall Ss Sb n Γ G',
  SubstTy Sb n Γ G' -> subst_nl Sb n Γ G' ->
  forallb (no_local_ty_G Γ) Ss = true ->
  forallb (no_local_ty_G G') (List.map (subst_ty n Sb) Ss) = true.
Proof.
  induction Ss as [|S Ss IH]; intros Sb n Γ G' HSub Hnl H; simpl in *; [reflexivity|].
  apply Bool.andb_true_iff in H. destruct H as [HS HSs].
  rewrite (no_local_ty_G_subst_ty S Γ Sb n G' HSub Hnl HS).
  rewrite (IH Sb n Γ G' HSub Hnl HSs). reflexivity.
Qed.

Lemma typing_SubstTy : forall Γ t T,
  Γ ⊢ₜ t : T ->
  forall Sb n G', SubstTy Sb n Γ G' -> subst_nl Sb n Γ G' ->
  G' ⊢ₜ subst_ty_in_tm n Sb t : subst_ty n Sb T.
Proof.
  apply (typing_ind_forall2
    (fun Γ t T => forall Sb n G', SubstTy Sb n Γ G' -> subst_nl Sb n Γ G' ->
       G' ⊢ₜ subst_ty_in_tm n Sb t : subst_ty n Sb T)).
  - (* T_Var *)
    intros Γ x T Hlk HwfT Sb n G' HSub Hnl.
    simpl. apply T_Var.
    + rewrite (SubstTy_lookup_tm Sb n Γ G' HSub x). rewrite Hlk. reflexivity.
    + eapply ty_wf_SubstTy; eauto.
  - (* T_Sub *)
    intros Γ t T U Ht IH Hsub Sb n G' HSub Hnl.
    eapply T_Sub.
    + apply (IH Sb n G' HSub Hnl).
    + eapply sub_SubstTy; eauto.
  - (* T_Lam *)
    intros Γ body A l B HwfA HwfB Hbody IHbody Hcap Sb n G' HSub Hnl.
    simpl. apply T_Lam.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + apply (IHbody Sb n (bind_tm (subst_ty n Sb A) :: G')
        (SubstTy_tm Sb n Γ G' A HSub) (subst_nl_bind_tm Sb n Γ G' A Hnl)).
    + eapply LS_Trans.
      * apply (capture_lt_SubstTy_le Sb n Γ G' HSub body).
        apply (proj1 (lt_sub_wf Γ (capture_lt Γ body) l Hcap)).
      * eapply lt_sub_SubstTy; eauto.
  - (* T_App *)
    intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 Sb n G' HSub Hnl.
    simpl. eapply T_App.
    + apply (IH1 Sb n G' HSub Hnl).
    + apply (IH2 Sb n G' HSub Hnl).
  - (* T_TyLam *)
    intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody Sb n G' HSub Hnl.
    simpl. apply T_TyLam.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; [exact HwfT|]. apply SubstTy_ty. exact HSub.
    + rewrite is_abs_subst_ty_in_tm. exact HisAbs.
    + apply (IHbody (shift_ty 1 0 Sb) (S n) (bind_ty (subst_ty n Sb bound) :: G')
        (SubstTy_ty Sb n Γ G' bound HSub) (subst_nl_bind_ty Sb n Γ G' bound Hnl)).
  - (* T_TyApp *)
    intros Γ t B U S Ht IH HwfS Hsub HnlArg Sb n G' HSub Hnl.
    simpl. rewrite <- subst_ty_subst_ty_comm0.
    eapply T_TyApp.
    + eapply T_Sub.
      * apply (IH Sb n G' HSub Hnl).
      * apply type_ty_all_narrow_bound.
        -- eapply sub_SubstTy; eauto.
        -- pose proof (typing_implies_wf Γ t (type_ty_all B U) Ht) as HwfAll.
           inversion HwfAll; subst.
           eapply ty_wf_SubstTy; [eassumption|].
           apply SubstTy_ty. exact HSub.
    + eapply ty_wf_SubstTy; eauto.
    + apply SA_Refl. eapply ty_wf_SubstTy; eauto.
    + apply ty_app_arg_no_local_self.
  - (* T_LtLam *)
    intros Γ body T HwfT HisAbs Hbody IHbody Sb n G' HSub Hnl.
    simpl. apply T_LtLam.
    + eapply ty_wf_SubstTy; [exact HwfT|]. apply SubstTy_lt. exact HSub.
    + rewrite is_abs_subst_ty_in_tm. exact HisAbs.
    + apply (IHbody (shift_lt_in_ty 1 0 Sb) n (bind_lt lt_local :: G')
        (SubstTy_lt Sb n Γ G' lt_local HSub) (subst_nl_bind_lt Sb n Γ G' lt_local Hnl)).
  - (* T_LtApp *)
    intros Γ t T l Ht IH Hwfl Sb n G' HSub Hnl.
    simpl.
    replace (subst_ty n Sb (subst_lt_in_ty 0 l T))
      with (subst_lt_in_ty 0 l (subst_ty n (shift_lt_in_ty 1 0 Sb) T)).
    2:{ rewrite subst_lt_in_ty_subst_ty_comm. rewrite subst_lt_in_ty_shift_cancel. reflexivity. }
    eapply T_LtApp.
    + apply (IH Sb n G' HSub Hnl).
    + eapply lt_wf_SubstTy; eauto.
  - (* T_Ctor *)
    intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs Hctor Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs
           Hresult Hshape Hresult_eff Hwfl HltSub Hbounded Hlen_vs Hargs IHargs
           Sb n G' HSub Hnl.
    admit.
  - (* T_Match *)
    intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γyes yes_body eta elim_result no_body
           HKne Hctor Heff Hlts Hrho Hlen_Ts HwfTs Hscrut_result Hscrut_shape
           Hresult_eff Hresult_ne HwfDelta Hresult_l Hscrut IHscrut Harity HΓyes
           Hyes IHyes Helim Hno IHno Sb n G' HSub Hnl.
    admit.
  - (* T_Cap *)
    intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff Hlen HwfTs HwfTR Hsig Hret Hop IHop Sb n G' HSub Hnl.
    simpl.
    eapply T_Cap with
      (n_α := n_α) (n_β := n_β)
      (sig := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) sig)
      (ret := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) ret)
      (sig_β := subst_ty (n_β + n) (shift_ty n_β 0 Sb) sig_β)
      (ret_β := subst_ty (n_β + n) (shift_ty n_β 0 Sb) ret_β).
    + rewrite (SubstTy_lookup_eff Sb n Γ G' HSub E_tag). rewrite Heff. reflexivity.
    + change (List.length (List.map (subst_ty n Sb) Ts) = n_α).
      rewrite List.length_map. exact Hlen.
    + eapply types_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + subst sig_β. symmetry. apply inst_op_alpha_subst_ty. exact Hlen.
    + subst ret_β. symmetry. apply inst_op_alpha_subst_ty. exact Hlen.
    + rewrite <- (shift_ty_many_subst_ty_comm0 n_β n Sb T_R).
      replace (n + n_β) with (n_β + n) by lia.
      eapply IHop.
      * apply SubstTy_tm. apply SubstTy_tm. apply SubstTy_push_ty_vars_any_at_free. exact HSub.
      * apply subst_nl_bind_tm. apply subst_nl_bind_tm. apply subst_nl_push_ty_vars. exact Hnl.
  - (* T_Handle *)
    intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hsig Hret Hop IHop Hbody IHbody
           Sb n G' HSub Hnl.
    simpl.
    eapply T_Handle with
      (n_α := n_α) (n_β := n_β)
      (sig := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) sig)
      (ret := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) ret)
      (T_B := subst_ty n Sb T_B)
      (sig_β := subst_ty (n_β + n) (shift_ty n_β 0 Sb) sig_β)
      (ret_β := subst_ty (n_β + n) (shift_ty n_β 0 Sb) ret_β).
    + rewrite (SubstTy_lookup_eff Sb n Γ G' HSub E_tag). rewrite Heff. reflexivity.
    + change (List.length (List.map (subst_ty n Sb) Ts) = n_α).
      rewrite List.length_map. exact Hlen.
    + eapply types_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + eapply no_local_ty_G_subst_ty; [eauto| exact Hnl |eauto].
    + eapply sub_SubstTy; eauto.
    + subst sig_β. symmetry. apply inst_op_alpha_subst_ty. exact Hlen.
    + subst ret_β. symmetry. apply inst_op_alpha_subst_ty. exact Hlen.
    + rewrite <- (shift_ty_many_subst_ty_comm0 n_β n Sb T_R).
      replace (n + n_β) with (n_β + n) by lia.
      eapply IHop.
      * apply SubstTy_tm. apply SubstTy_tm. apply SubstTy_push_ty_vars_any_at_free. exact HSub.
      * apply subst_nl_bind_tm. apply subst_nl_bind_tm. apply subst_nl_push_ty_vars. exact Hnl.
    + apply (IHbody Sb n (bind_tm (subst_ty n Sb (type_ctor E_tag lt_local Ts)) :: G')
        (SubstTy_tm Sb n Γ G' (type_ctor E_tag lt_local Ts) HSub)
        (subst_nl_bind_tm Sb n Γ G' (type_ctor E_tag lt_local Ts) Hnl)).
  - (* T_Perform *)
    intros Γ recv arg E_tag Delta Ts Ss n_α n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg
           Sb n G' HSub Hnl.
    simpl. eapply T_Perform with
      (n_α := n_α) (n_β := n_β)
      (sig := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) sig)
      (ret := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) ret)
      (sig_inst := subst_ty n Sb sig_inst) (ret_inst := subst_ty n Sb ret_inst).
    + apply (IHrecv Sb n G' HSub Hnl).
    + rewrite (SubstTy_lookup_eff Sb n Γ G' HSub E_tag). rewrite Heff. reflexivity.
    + change (List.length (List.map (subst_ty n Sb) Ts) = n_α).
      rewrite List.length_map. exact Hlen_Ts.
    + change (List.length (List.map (subst_ty n Sb) Ss) = n_β).
      rewrite List.length_map. exact Hlen_Ss.
    + eapply types_wf_SubstTy; eauto.
    + eapply forallb_no_local_ty_G_subst_ty; [exact HSub | exact Hnl | exact HnoSs].
    + subst sig_inst. symmetry. apply inst_op_arg_subst_ty; assumption.
    + eapply no_local_ty_G_subst_ty; [eauto| exact Hnl |eauto].
    + subst ret_inst. symmetry. apply inst_op_arg_subst_ty; assumption.
    + eapply ty_wf_SubstTy; eauto.
    + apply (IHarg Sb n G' HSub Hnl).
  - (* T_HandlerM *)
    intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH Sb n G' HSub Hnl.
    simpl. apply T_HandlerM.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + eapply no_local_ty_G_subst_ty; [eauto| exact Hnl |eauto].
    + eapply sub_SubstTy; eauto.
    + apply (IH Sb n G' HSub Hnl).
  - (* T_Resume *)
    intros Γ m b A T_B T_R HwfA HwfTB HwfTR HnoLocal Hsub Hb IHb Sb n G' HSub Hnl.
    simpl. apply T_Resume.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + eapply no_local_ty_G_subst_ty; [eauto| exact Hnl |eauto].
    + eapply sub_SubstTy; eauto.
    + apply (IHb Sb n (bind_tm (subst_ty n Sb A) :: G')
        (SubstTy_tm Sb n Γ G' A HSub) (subst_nl_bind_tm Sb n Γ G' A Hnl)).
Admitted.
