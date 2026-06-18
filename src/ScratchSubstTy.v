Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import SubstitutionTheory.

(* HELPER (to prove): subtyping bound Sb <:: B with B = Any@free forces
   Sb no-local; propagated through SubstTy. *)
Lemma SubstTy_no_local_cond : forall Sb n Γ G',
  SubstTy Sb n Γ G' ->
  no_local_ty_G Γ (type_var n) = true ->
  no_local_ty_G G' Sb = true.
Proof.
Admitted.

Lemma typing_SubstTy : forall Γ t T,
  Γ ⊢ₜ t : T ->
  forall Sb n G', SubstTy Sb n Γ G' ->
  G' ⊢ₜ subst_ty_in_tm n Sb t : subst_ty n Sb T.
Proof.
  apply (typing_ind_forall2
    (fun Γ t T => forall Sb n G', SubstTy Sb n Γ G' ->
       G' ⊢ₜ subst_ty_in_tm n Sb t : subst_ty n Sb T)).
  - (* T_Var *)
    intros Γ x T Hlk HwfT Sb n G' HSub.
    simpl. apply T_Var.
    + rewrite (SubstTy_lookup_tm Sb n Γ G' HSub x). rewrite Hlk. reflexivity.
    + eapply ty_wf_SubstTy; eauto.
  - (* T_Sub *)
    intros Γ t T U Ht IH Hsub Sb n G' HSub.
    eapply T_Sub.
    + apply (IH Sb n G' HSub).
    + eapply sub_SubstTy; eauto.
  - (* T_Lam *)
    intros Γ body A l B HwfA HwfB Hbody IHbody Hcap Sb n G' HSub.
    simpl. apply T_Lam.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + apply (IHbody Sb n (bind_tm (subst_ty n Sb A) :: G')
        (SubstTy_tm Sb n Γ G' A HSub)).
    + eapply LS_Trans.
      * apply (capture_lt_SubstTy_le Sb n Γ G' HSub body).
        apply (proj1 (lt_sub_wf Γ (capture_lt Γ body) l Hcap)).
      * eapply lt_sub_SubstTy; eauto.
  - (* T_App *)
    intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 Sb n G' HSub.
    simpl. eapply T_App.
    + apply (IH1 Sb n G' HSub).
    + apply (IH2 Sb n G' HSub).
  - (* T_TyLam *)
    intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody Sb n G' HSub.
    simpl. apply T_TyLam.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; [exact HwfT|]. apply SubstTy_ty. exact HSub.
    + rewrite is_abs_subst_ty_in_tm. exact HisAbs.
    + apply (IHbody (shift_ty 1 0 Sb) (S n) (bind_ty (subst_ty n Sb bound) :: G')
        (SubstTy_ty Sb n Γ G' bound HSub)).
  - (* T_TyApp *)
    intros Γ t B U S Ht IH HwfS Hsub HnlArg Sb n G' HSub.
    simpl. rewrite <- subst_ty_subst_ty_comm0.
    eapply T_TyApp.
    + eapply T_Sub.
      * apply (IH Sb n G' HSub).
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
    intros Γ body T HwfT HisAbs Hbody IHbody Sb n G' HSub.
    simpl. apply T_LtLam.
    + eapply ty_wf_SubstTy; [exact HwfT|]. apply SubstTy_lt. exact HSub.
    + rewrite is_abs_subst_ty_in_tm. exact HisAbs.
    + apply (IHbody (shift_lt_in_ty 1 0 Sb) n (bind_lt lt_local :: G')
        (SubstTy_lt Sb n Γ G' lt_local HSub)).
  - (* T_LtApp *)
    intros Γ t T l Ht IH Hwfl Sb n G' HSub.
    simpl.
    replace (subst_ty n Sb (subst_lt_in_ty 0 l T))
      with (subst_lt_in_ty 0 l (subst_ty n (shift_lt_in_ty 1 0 Sb) T)).
    2:{ rewrite subst_lt_in_ty_subst_ty_comm. rewrite subst_lt_in_ty_shift_cancel. reflexivity. }
    eapply T_LtApp.
    + apply (IH Sb n G' HSub).
    + eapply lt_wf_SubstTy; eauto.
  - (* T_Ctor *)
    intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs Hctor Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs
           Hresult Hshape Hresult_eff Hwfl HltSub Hbounded Hlen_vs Hargs IHargs
           Sb n G' HSub.
    admit.
  - (* T_Match *)
    intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γyes yes_body eta elim_result no_body
           HKne Hctor Heff Hlts Hrho Hlen_Ts HwfTs Hscrut_result Hscrut_shape
           Hresult_eff Hresult_ne HwfDelta Hresult_l Hscrut IHscrut Harity HΓyes
           Hyes IHyes Helim Hno IHno Sb n G' HSub.
    admit.
  - (* T_Cap *)
    intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff Hlen HwfTs HwfTR Hsig Hret Hop IHop Sb n G' HSub.
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
      apply SubstTy_tm. apply SubstTy_tm. apply SubstTy_push_ty_vars_any_at_free. exact HSub.
  - (* T_Handle *)
    intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hsig Hret Hop IHop Hbody IHbody
           Sb n G' HSub.
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
    + eapply no_local_ty_G_subst_ty; [eauto| |eauto]. apply (SubstTy_no_local_cond Sb n Γ G' HSub).
    + eapply sub_SubstTy; eauto.
    + subst sig_β. symmetry. apply inst_op_alpha_subst_ty. exact Hlen.
    + subst ret_β. symmetry. apply inst_op_alpha_subst_ty. exact Hlen.
    + rewrite <- (shift_ty_many_subst_ty_comm0 n_β n Sb T_R).
      replace (n + n_β) with (n_β + n) by lia.
      eapply IHop.
      apply SubstTy_tm. apply SubstTy_tm. apply SubstTy_push_ty_vars_any_at_free. exact HSub.
    + apply (IHbody Sb n (bind_tm (subst_ty n Sb (type_ctor E_tag lt_local Ts)) :: G')
        (SubstTy_tm Sb n Γ G' (type_ctor E_tag lt_local Ts) HSub)).
  - (* T_Perform *)
    intros Γ recv arg E_tag Delta Ts Ss n_α n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg
           Sb n G' HSub.
    simpl. eapply T_Perform with
      (n_α := n_α) (n_β := n_β)
      (sig := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) sig)
      (ret := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) ret)
      (sig_inst := subst_ty n Sb sig_inst) (ret_inst := subst_ty n Sb ret_inst).
    + apply (IHrecv Sb n G' HSub).
    + rewrite (SubstTy_lookup_eff Sb n Γ G' HSub E_tag). rewrite Heff. reflexivity.
    + change (List.length (List.map (subst_ty n Sb) Ts) = n_α).
      rewrite List.length_map. exact Hlen_Ts.
    + change (List.length (List.map (subst_ty n Sb) Ss) = n_β).
      rewrite List.length_map. exact Hlen_Ss.
    + eapply types_wf_SubstTy; eauto.
    + admit. (* forallb no_local_ty_G of subst Ss *)
    + subst sig_inst. symmetry. apply inst_op_arg_subst_ty; assumption.
    + eapply no_local_ty_G_subst_ty; [eauto| |eauto]. apply (SubstTy_no_local_cond Sb n Γ G' HSub).
    + subst ret_inst. symmetry. apply inst_op_arg_subst_ty; assumption.
    + eapply ty_wf_SubstTy; eauto.
    + apply (IHarg Sb n G' HSub).
  - (* T_HandlerM *)
    intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH Sb n G' HSub.
    simpl. apply T_HandlerM.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + eapply no_local_ty_G_subst_ty; [eauto| |eauto]. apply (SubstTy_no_local_cond Sb n Γ G' HSub).
    + eapply sub_SubstTy; eauto.
    + apply (IH Sb n G' HSub).
  - (* T_Resume *)
    intros Γ m b A T_B T_R HwfA HwfTB HwfTR HnoLocal Hsub Hb IHb Sb n G' HSub.
    simpl. apply T_Resume.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + eapply no_local_ty_G_subst_ty; [eauto| |eauto]. apply (SubstTy_no_local_cond Sb n Γ G' HSub).
    + eapply sub_SubstTy; eauto.
    + apply (IHb Sb n (bind_tm (subst_ty n Sb A) :: G')
        (SubstTy_tm Sb n Γ G' A HSub)).
Admitted.
