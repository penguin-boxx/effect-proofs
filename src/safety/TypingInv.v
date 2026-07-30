Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import Narrowing.
Require Import Narrowing.
Require Import Variance.

(* ================================================================== *)
(* Typing and subtyping inversions.                                   *)
(*                                                                    *)
(* The single home for subsumption-stripping inversions: subtyping    *)
(* shape inversions under an `eval_ctx`, principal-type inversions    *)
(* for every term former (with the residual `<intro type> <:: T`),    *)
(* canonical forms, and the evaluation-context inversion              *)
(* `plug_typing_inv`.  Everything downstream (the marker-invariant    *)
(* modules, Progress,                                                 *)
(* Preservation, Escape) consumes these.                              *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Subtyping shape inversions.                                        *)
(* ------------------------------------------------------------------ *)

(* Constructor-subtyping inversion needs only that the context has no
   type variables (sub_ctor_inv specialises this to eval_ctx). *)
Lemma sub_ctor_inv_noty : forall Γ S K l Ts,
  (forall α, ctx_lookup_ty Γ α = None) ->
  Γ ⊢ S <:: type_ctor K l Ts ->
  K <> any_tag ->
  exists l', S = type_ctor K l' Ts /\ Γ ⊢ₗ l' <: l.
Proof.
  intros Γ S K l Ts Hnoty Hsub HK.
  remember (type_ctor K l Ts) as T eqn:HT.
  revert K l Ts HT HK.
  induction Hsub; intros K0 l0 Ts0 HT HK.
  - inversion HT; subst. inversion H; subst.
    exists l0; split; [reflexivity|apply LS_Refl; assumption].
  - subst T.
    destruct (IHHsub2 Hnoty _ _ _ eq_refl HK) as [l'' [HeqU Hl2]]; subst.
    destruct (IHHsub1 Hnoty _ _ _ eq_refl HK) as [l''' [HeqS Hl1]]; subst.
    exists l'''; split; eauto.
  - subst. rewrite Hnoty in H; discriminate.
  - injection HT; intros; subst. exists l; split; auto.
  - injection HT; intros; subst. contradiction.
  - discriminate HT.
  - discriminate HT.
  - discriminate HT.
Qed.

Lemma sub_ctor_inv : forall Γ S K l Ts,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_ctor K l Ts ->
  K <> any_tag ->
  exists l', S = type_ctor K l' Ts /\ Γ ⊢ₗ l' <: l.
Proof.
  intros Γ S K l Ts Hec.
  apply sub_ctor_inv_noty.
  intro α. apply eval_ctx_no_ty. exact Hec.
Qed.

Lemma sub_fun_inv : forall Γ S A l B,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_fun A l B ->
  exists A' l' B',
    S = type_fun A' l' B' /\
    Γ ⊢ A <:: A' /\
    Γ ⊢ₗ l' <: l /\
    Γ ⊢ B' <:: B.
Proof.
  intros Γ S A l B Hec Hsub.
  remember (type_fun A l B) as T eqn:HT.
  revert A l B HT.
  induction Hsub; intros A0 l0 B0 HT.
  - (* Refl *) inversion HT; subst. inversion H; subst.
    exists A0, l0, B0. repeat split;
      try (apply SA_Refl; assumption);
      try (apply LS_Refl; assumption).
  - (* Trans *) subst T.
    destruct (IHHsub2 Hec _ _ _ eq_refl) as [A1 [l1 [B1 [HeqU [HAa [Hla HBa]]]]]]; subst.
    destruct (IHHsub1 Hec _ _ _ eq_refl) as [A2 [l2 [B2 [HeqS [HAb [Hlb HBb]]]]]]; subst.
    exists A2, l2, B2. repeat split; eauto.
  - (* VarCtx *) subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - (* Data *) discriminate HT.
  - (* Any *) discriminate HT.
  - (* Fun *) injection HT; intros HB0 Hl0 HA0; subst.
    exists A', l, B; repeat split; auto.
  - (* LtAll *) discriminate HT.
  - (* TyAll *) discriminate HT.
Qed.

Lemma sub_lt_all_inv : forall Γ S T,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_lt_all T ->
  exists T', S = type_lt_all T'.
Proof.
  intros Γ S T Hec Hsub.
  remember (type_lt_all T) as U eqn:HU.
  revert T HU.
  induction Hsub; intros T0 HU.
  - (* Refl *) inversion HU; subst. eauto.
  - (* Trans *) subst T.
    destruct (IHHsub2 Hec _ eq_refl) as [T' HeqU]; subst.
    destruct (IHHsub1 Hec _ eq_refl) as [T'' HeqS]; subst. eauto.
  - (* VarCtx *) subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - (* Data *) discriminate HU.
  - (* Any *) discriminate HU.
  - (* Fun *) discriminate HU.
  - (* LtAll *) injection HU; intros; subst. eauto.
  - (* TyAll *) discriminate HU.
Qed.

Lemma sub_ty_all_inv : forall Γ S B T,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_ty_all B T ->
  exists B' T', S = type_ty_all B' T'.
Proof.
  intros Γ S B T Hec Hsub.
  remember (type_ty_all B T) as U eqn:HU.
  revert B T HU.
  induction Hsub; intros B0 T0 HU.
  - (* Refl *) inversion HU; subst. eauto.
  - (* Trans *) subst T.
    destruct (IHHsub2 Hec _ _ eq_refl) as [B' [T' HeqU]]; subst.
    destruct (IHHsub1 Hec _ _ eq_refl) as [B'' [T'' HeqS]]; subst. eauto.
  - (* VarCtx *) subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - (* Data *) discriminate HU.
  - (* Any *) discriminate HU.
  - (* Fun *) discriminate HU.
  - (* LtAll *) discriminate HU.
  - (* TyAll *) injection HU; intros; subst. eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Principal-type inversions: strip subsumption and recover the       *)
(* premises of the introducing rule together with the residual        *)
(* subtyping `<intro type> <:: T`.                                    *)
(* ------------------------------------------------------------------ *)

Lemma app_typing_inv_p : forall Γ f x T,
  Γ ⊢ₜ term_app f x : T ->
  exists A l B, Γ ⊢ₜ f : type_fun A l B /\ Γ ⊢ₜ x : A /\ Γ ⊢ B <:: T.
Proof.
  intros Γ f x T H. remember (term_app f x) as s eqn:Hs.
  induction H; try discriminate Hs.
  - destruct (IHtyping Hs) as [A [l [B [Hf [Hx Hsub]]]]].
    exists A, l, B. split; [exact Hf|]. split; [exact Hx|]. eapply SA_Trans; eassumption.
  - injection Hs; intros; subst.
    exists A, l, B. split; [eassumption|]. split; [eassumption|].
    apply SA_Refl.
    match goal with Hf : _ ⊢ₜ _ : type_fun _ _ _ |- _ =>
      pose proof (typing_implies_wf _ _ _ Hf) as Hwf; inversion Hwf; subst; assumption
    end.
Qed.

Lemma tyapp_typing_inv_p : forall Γ t S T,
  Γ ⊢ₜ term_ty_app t S : T ->
  exists B U, Γ ⊢ₜ t : type_ty_all B U /\ Γ ⊢ S <:: B
    /\ Γ ⊢ subst_ty 0 S U <:: T.
Proof.
  intros Γ t S T H. remember (term_ty_app t S) as s eqn:Hs.
  induction H; try discriminate Hs.
  - destruct (IHtyping Hs) as [B0 [U0 [Ht [HSb Hsub]]]].
    exists B0, U0. split; [exact Ht|]. split; [exact HSb|].
    eapply SA_Trans; eassumption.
  - injection Hs; intros; subst.
    exists B, U. split; [eassumption|]. split; [eassumption|].
    apply SA_Refl. eapply typing_implies_wf. eapply T_TyApp; eassumption.
Qed.

Lemma ltapp_typing_inv_p : forall Γ t l T,
  Γ ⊢ₜ term_lt_app t l : T ->
  exists U, Γ ⊢ₜ t : type_lt_all U /\ lt_wf Γ l /\ Γ ⊢ subst_lt_in_ty 0 l U <:: T.
Proof.
  intros Γ t l T H. remember (term_lt_app t l) as s eqn:Hs.
  induction H; try discriminate Hs.
  - destruct (IHtyping Hs) as [U0 [Ht [Hl Hsub]]].
    exists U0. split; [exact Ht|]. split; [exact Hl|]. eapply SA_Trans; eassumption.
  - injection Hs; intros; subst.
    eexists. split; [eassumption|]. split; [eassumption|].
    apply SA_Refl. eapply typing_implies_wf. eapply T_LtApp; eassumption.
Qed.


Lemma handler_m_typing_inv : forall Γ m T_B T_R t T,
  Γ ⊢ₜ term_handler_m m T_B T_R t : T ->
  Γ ⊢ₜ t : T_B /\ Γ ⊢ T_B <:: T_R /\ Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free /\ Γ ⊢ T_R <:: T.
Proof.
  intros Γ m T_B T_R t T H.
  remember (term_handler_m m T_B T_R t) as s eqn:Hs.
  induction H; try discriminate Hs.
  - (* T_Sub *) destruct (IHtyping Hs) as [Ht [Hbr [Hnl Hrt]]].
    split; [exact Ht|]. split; [exact Hbr|]. split; [exact Hnl|].
    eapply SA_Trans; [exact Hrt | eassumption].
  - (* T_HandlerM *) injection Hs; intros; subst.
    split; [assumption|]. split; [assumption|]. split; [assumption|].
    apply SA_Refl. assumption.
Qed.

Lemma cap_typing_inv : forall Γ E_tag m Ts T_R op_bodies T,
  Γ ⊢ₜ term_cap E_tag m Ts T_R op_bodies : T ->
  exists n_α ops,
    ctx_lookup_eff Γ E_tag = Some (n_α, ops) /\
    List.length Ts = n_α /\
    types_wf Γ Ts /\
    ty_wf Γ T_R /\
    List.map fst op_bodies = List.map op_nb ops /\
    Forall2 (fun ob osig =>
      (op_body_ctx Γ (op_nb osig)
         (inst_op_ty_args n_α Ts (op_nb osig) (op_sig_ty osig))
         (inst_op_ty_args n_α Ts (op_nb osig) (op_ret_ty osig)) T_R)
        ⊢ₜ snd ob : shift_ty (op_nb osig) 0 T_R)
      op_bodies ops /\
    Γ ⊢ type_ctor E_tag lt_local Ts <:: T.
Proof.
  intros Γ E_tag m Ts T_R op_bodies T H.
  remember (term_cap E_tag m Ts T_R op_bodies) as s eqn:Hs.
  induction H; try discriminate Hs.
  - (* T_Sub *)
    destruct (IHtyping Hs) as
      [n_α [ops [Heff [HlenTs [HwfTs [HwfTR [Hfst [Hops Hsub]]]]]]]].
    exists n_α, ops.
    split; [exact Heff|]. split; [exact HlenTs|]. split; [exact HwfTs|].
    split; [exact HwfTR|]. split; [exact Hfst|]. split; [exact Hops|].
    eapply SA_Trans; [exact Hsub | eassumption].
  - (* T_Cap *) injection Hs; intros; subst.
    do 2 eexists. repeat split; try eassumption; try reflexivity.
    + apply typing_ops_Forall2. assumption.
    + apply SA_Refl. apply TWF_Ctor; [apply LWF_Local | assumption].
Qed.

Lemma perform_typing_inv : forall Γ recv op Ss ret_inst arg T,
  Γ ⊢ₜ term_perform recv op Ss ret_inst arg : T ->
  exists E_tag Δ Ts n_α ops n_β sig ret sig_inst,
    Γ ⊢ₜ recv : type_ctor E_tag Δ Ts /\
    ctx_lookup_eff Γ E_tag = Some (n_α, ops) /\
    nth_error ops op = Some (n_β, sig, ret) /\
    List.length Ts = n_α /\
    List.length Ss = n_β /\
    types_wf Γ Ss /\
    Forall (fun S => Γ ⊢ₗ lt_of_ty_G Γ S <: lt_free) Ss /\
    sig_inst = inst_op_all_args n_α Ts n_β Ss sig /\
    Γ ⊢ₗ lt_of_ty_G Γ sig_inst <: lt_free /\
    ret_inst = inst_op_all_args n_α Ts n_β Ss ret /\
    ty_wf Γ ret_inst /\
    Γ ⊢ₜ arg : sig_inst /\
    Γ ⊢ ret_inst <:: T.
Proof.
  intros Γ recv op Ss ret_inst arg T H.
  remember (term_perform recv op Ss ret_inst arg) as s eqn:Hs.
  induction H; try discriminate Hs.
  - (* T_Sub *)
    destruct (IHtyping Hs) as
      [E_tag [Δ [Ts [n_α [ops [n_β [sig [ret [sig_inst
        [Hrecv [Heff [Hnth [HlenTs [HlenSs [HwfSs [HnlSs [Hsi [Hnlsi
          [Hri [HwfRi [Harg Hsub]]]]]]]]]]]]]]]]]]]]].
    exists E_tag, Δ, Ts, n_α, ops, n_β, sig, ret, sig_inst.
    split; [exact Hrecv|]. split; [exact Heff|]. split; [exact Hnth|].
    split; [exact HlenTs|].
    split; [exact HlenSs|]. split; [exact HwfSs|]. split; [exact HnlSs|].
    split; [exact Hsi|]. split; [exact Hnlsi|]. split; [exact Hri|].
    split; [exact HwfRi|]. split; [exact Harg|].
    eapply SA_Trans; [exact Hsub | eassumption].
  - (* T_Perform *) injection Hs; intros; subst.
    do 9 eexists. repeat split; try eassumption; try reflexivity.
    apply SA_Refl. assumption.
Qed.

Lemma handle_typing_inv : forall Γ E_tag Ts T_B T_R op_bodies body T,
  Γ ⊢ₜ term_handle E_tag Ts T_B T_R op_bodies body : T ->
  exists n_α ops,
    ctx_lookup_eff Γ E_tag = Some (n_α, ops) /\
    List.length Ts = n_α /\ types_wf Γ Ts /\
    ty_wf Γ T_B /\ ty_wf Γ T_R /\ Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free /\ Γ ⊢ T_B <:: T_R /\
    List.map fst op_bodies = List.map op_nb ops /\
    Forall2 (fun ob osig =>
      (op_body_ctx Γ (op_nb osig)
         (inst_op_ty_args n_α Ts (op_nb osig) (op_sig_ty osig))
         (inst_op_ty_args n_α Ts (op_nb osig) (op_ret_ty osig)) T_R)
        ⊢ₜ snd ob : shift_ty (op_nb osig) 0 T_R)
      op_bodies ops /\
    (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) ⊢ₜ body : T_B /\
    Γ ⊢ T_R <:: T.
Proof.
  intros Γ E_tag Ts T_B T_R op_bodies body T H.
  remember (term_handle E_tag Ts T_B T_R op_bodies body) as s eqn:Hs.
  induction H; try discriminate Hs.
  - destruct (IHtyping Hs) as
      (n_α & ops & Heff & HlenTs & HwfTs & HwfTB & HwfTR
       & Hnl & Hbr & Hfst & Hops & Hbody & Hsub).
    exists n_α, ops.
    repeat (split; [assumption|]). eapply SA_Trans; eassumption.
  - injection Hs; intros; subst.
    do 2 eexists.
    repeat split; try eassumption; try reflexivity.
    + apply typing_ops_Forall2. assumption.
    + apply SA_Refl. assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Inversion lemmas for T_Match and T_Ctor (with the variance/peel    *)
(* helpers they rest on).                                             *)
(* ------------------------------------------------------------------ *)

Lemma elim_ty_n_sound_pos : forall n Delta lts eta elim_result Γ,
  elim_ty_n n (shift_lt n 0 Delta) var_pos eta = Some elim_result ->
  List.length lts = n ->
  lt_wf Γ Delta ->
  ty_wf (push_match_bound n Delta Γ) eta ->
  Forall (fun l => Γ ⊢ₗ l <: Delta) lts ->
  Γ ⊢ subst_list_lt_in_ty lts eta <:: elim_result.
Proof.
  intros n Delta lts eta elim_result Γ Helim Hlen HwfDelta HwfEta Hfor.
  subst n.
  pose proof (elim_in_ctx_sound (List.length lts) Delta eta elim_result Γ Helim
                HwfDelta HwfEta) as Hctx.
  pose proof (sub_peel_push_match_bound lts Delta eta
                (shift_lt_in_ty (List.length lts) 0 elim_result) Γ Hfor Hctx) as Hpeel.
  rewrite subst_list_lt_in_ty_shift_cancel in Hpeel.
  exact Hpeel.
Qed.

(* TYPING-level peel of the match's [push_match_bound] binders (mirrors the   *)
(* subtyping [sub_peel_push_match_bound]): substituting the constructor's      *)
(* actual lifetimes [lts] (each <: Delta) for the n_lt match lt-vars    *)
(* removes the push_match_bound block, leaving the field (bind_tm) binders     *)
(* with their types lt-substituted.  Each step peels one lt-binder via  *)
(* [typing_SubstLt] + [SubstLt_fold_bind_tm_map] over                   *)
(* [SubstLt_here], using [lt_sub_push_match_bound_weaken] for the bound.       *)
Lemma typing_peel_push_match_bound_fold : forall lts Delta rhos t U Γ,
  Forall (fun l => Γ ⊢ₗ l <: Delta) lts ->
  (List.fold_right (fun rho G => bind_tm rho :: G)
     (push_match_bound (List.length lts) Delta Γ) rhos) ⊢ₜ t : U ->
  (List.fold_right (fun rho G => bind_tm rho :: G) Γ
     (List.map (subst_list_lt_in_ty lts) rhos))
    ⊢ₜ subst_list_lt_in_tm lts t : subst_list_lt_in_ty lts U.
Proof.
  induction lts as [|l0 rest IH]; intros Delta rhos t U Γ Hfor Hty.
  - cbn [List.length push_match_bound] in Hty.
    cbn [subst_list_lt_in_tm subst_list_lt_in_ty].
    erewrite List.map_ext by (intro a; apply subst_list_lt_in_ty_nil).
    rewrite List.map_id. exact Hty.
  - pose proof (Forall_inv Hfor) as Hhead.
    pose proof (Forall_inv_tail Hfor) as Htail.
    cbn [List.length push_match_bound] in Hty.
    cbn [subst_list_lt_in_tm subst_list_lt_in_ty].
    pose proof (typing_SubstLt _ _ _ Hty
      (shift_lt (List.length rest) 0 l0) 0
      (List.fold_right (fun rho G => bind_tm rho :: G)
        (push_match_bound (List.length rest) Delta Γ)
        (List.map (subst_lt_in_ty 0 (shift_lt (List.length rest) 0 l0)) rhos))
      (SubstLt_fold_bind_tm_map rhos (shift_lt (List.length rest) 0 l0) 0
        (bind_lt (shift_lt (List.length rest) 0 Delta) :: push_match_bound (List.length rest) Delta Γ)
        (push_match_bound (List.length rest) Delta Γ)
        (SubstLt_here (push_match_bound (List.length rest) Delta Γ)
          (shift_lt (List.length rest) 0 Delta) (shift_lt (List.length rest) 0 l0)
          (lt_sub_push_match_bound_weaken (List.length rest) Delta Γ l0 Delta Hhead)))) as Hstep.
    pose proof (IH Delta (List.map (subst_lt_in_ty 0 (shift_lt (List.length rest) 0 l0)) rhos)
      (subst_lt_in_tm 0 (shift_lt (List.length rest) 0 l0) t)
      (subst_lt_in_ty 0 (shift_lt (List.length rest) 0 l0) U) Γ Htail Hstep) as Hrec.
    rewrite List.map_map in Hrec.
    exact Hrec.
Qed.

Lemma match_typing_inv : forall Γ scrut K n_lt0 arity yes_body no_body T,
  Γ ⊢ₜ term_match scrut K n_lt0 arity yes_body no_body : T ->
  exists n_lt n_ty sigma_fields result_ty_schema Ts Delta scrut_result_ty
         result_tag result_l eta elim_result,
    K <> any_tag /\
    ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) /\
    ctx_lookup_eff Γ K = None /\
    n_lt0 = n_lt /\
    List.length Ts = n_ty /\
    scrut_result_ty = inst_ctor_type n_lt n_ty (List.repeat Delta n_lt) Ts result_ty_schema /\
    scrut_result_ty = type_ctor result_tag result_l Ts /\
    result_tag <> any_tag /\
    lt_wf Γ Delta /\
    Γ ⊢ₗ result_l <: Delta /\
    Γ ⊢ₜ scrut : type_ctor result_tag Delta Ts /\
    arity = List.length (List.map (inst_ctor_type_open n_lt n_ty Ts) sigma_fields) /\
    (fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
                (push_match_bound n_lt Delta Γ)
                (List.map (inst_ctor_type_open n_lt n_ty Ts) sigma_fields))
       ⊢ₜ yes_body : eta /\
    elim_ty_n n_lt (shift_lt n_lt 0 Delta) var_pos eta = Some elim_result /\
    Γ ⊢ₜ no_body : elim_result /\
    (elim_result = T \/ Γ ⊢ elim_result <:: T).
Proof.
  intros Γ scrut K n_lt0 arity yes_body no_body T Hty.
  remember (term_match scrut K n_lt0 arity yes_body no_body) as t eqn:Ht.
  induction Hty; try discriminate.
  - (* T_Sub *) subst.
    destruct (IHHty eq_refl) as
      [n_lt [n_ty [sig [res [Ts0 [Delta0 [scrut_result_ty0
       [result_tag0 [result_l0 [eta0 [elim_r Hinv]]]]]]]]]]].
    destruct Hinv as
      (HK & Hlk & Heff & Hnlt_eq & HTs & Hscrut_result & Hscrut_shape &
       Hresult_ne & HwfDelta & Hresult_l & Hscrut & Har & Hbody & Helim &
       Hno & HsubOr).
    exists n_lt, n_ty, sig, res, Ts0, Delta0, scrut_result_ty0,
      result_tag0, result_l0, eta0, elim_r.
    repeat split; auto.
    destruct HsubOr as [Heq|Hsub0].
    + subst. right. match goal with H : _ ⊢ _ <:: _ |- _ => exact H end.
    + right. eapply SA_Trans; [exact Hsub0|].
      match goal with H : _ ⊢ _ <:: _ |- _ => exact H end.
  - (* T_Match *)
    injection Ht; intros; subst.
    repeat eexists; repeat split; eauto.
    all: try match goal with
    | Hrho : ?rho = List.map _ ?sigma,
      Harity : ?arity0 = List.length ?rho
      |- ?arity0 = List.length (List.map _ ?sigma) =>
        rewrite Harity, Hrho; reflexivity
    end.
Qed.

Lemma ctor_typing_inv : forall Γ K l lts Ts vs T,
  Γ ⊢ₜ term_ctor K l lts Ts vs : T ->
  exists n_lt n_ty sigma_fields result_ty_schema result_tag,
    ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) /\
    List.length lts = n_lt /\
    List.length Ts = n_ty /\
    inst_ctor_type n_lt n_ty lts Ts result_ty_schema = type_ctor result_tag l Ts /\
    Forall (fun l0 => Γ ⊢ₗ l0 <: l) lts /\
    List.length vs = List.length sigma_fields /\
    Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs
            (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields) /\
    Γ ⊢ type_ctor result_tag l Ts <:: T.
Proof.
  intros Γ K l lts Ts vs T Hty.
  remember (term_ctor K l lts Ts vs) as t eqn:Ht.
  induction Hty; try discriminate.
  - (* T_Sub *) subst.
    destruct (IHHty eq_refl) as
      (n_lt & n_ty & sig & res & result_tag &
       Hlk & Hltlen & HTslen & Hresult & Hlts_bound & Hvslen & Hf2 & Hsub).
    exists n_lt, n_ty, sig, res, result_tag.
    repeat split; auto. eapply SA_Trans; eauto.
  - (* T_Ctor *)
    inversion Ht; subst.
    exists (List.length lts), (List.length Ts), sigma_fields, result_ty_schema, result_tag.
    repeat split; eauto; try reflexivity.
    + match goal with
      | Hlen : List.length vs = List.length (List.map _ sigma_fields) |- _ =>
          rewrite Hlen, List.length_map; reflexivity
      end.
    + apply typings_Forall2. assumption.
    + match goal with
      | Hshape : inst_ctor_type (List.length lts) (List.length Ts) lts Ts result_ty_schema =
                 type_ctor result_tag l Ts |- _ =>
          rewrite Hshape; apply SA_Refl; constructor; assumption
      end.
Qed.

(* ------------------------------------------------------------------ *)
(* Canonical forms                                                    *)
(* ------------------------------------------------------------------ *)

Lemma canonical_fun : forall Γ v A l B,
  eval_ctx Γ ->
  Γ ⊢ₜ v : type_fun A l B ->
  value v ->
  exists body T, v = term_lam body T.
Proof.
  intros Γ v A l B Hec Hty Hval.
  remember (type_fun A l B) as T0 eqn:HT.
  revert A l B HT.
  induction Hty; intros A0 l0 B0 HT; subst;
    try (inversion Hval; fail);
    try discriminate HT.
  - (* T_Sub *)
    destruct (sub_fun_inv _ _ _ _ _ Hec H) as [A' [l' [B' [HeqT _]]]]; subst.
    eapply IHHty; eauto.
  - (* T_Lam *) eauto.
  - (* T_Ctor *)
    match goal with
    | H1 : ?R = type_ctor _ _ _, H2 : ?R = type_fun _ _ _ |- _ => rewrite H1 in H2; discriminate H2
    | H1 : ?R = type_ctor _ _ _, H2 : type_fun _ _ _ = ?R |- _ => rewrite H1 in H2; discriminate H2
    | H1 : type_ctor _ _ _ = ?R, H2 : ?R = type_fun _ _ _ |- _ => rewrite <- H1 in H2; discriminate H2
    | H1 : type_ctor _ _ _ = ?R, H2 : type_fun _ _ _ = ?R |- _ => rewrite <- H1 in H2; discriminate H2
    | H : type_fun _ _ _ = type_ctor _ _ _ |- _ => discriminate H
    | H : type_ctor _ _ _ = type_fun _ _ _ |- _ => discriminate H
    end.
Qed.

(* ------------------------------------------------------------------ *)
(* Evaluation-context typing inversion: typing of `plug P u` yields a *)
(* typing of the plugged sub-term `u` under the same context —        *)
(* evaluation contexts add no binders.                                *)
(* ------------------------------------------------------------------ *)

(* From a `Forall2` typing premise, recover per-element typability. *)
Lemma Forall2_Forall_exists :
  forall (A B : Type) (R : A -> B -> Prop) xs ys,
    Forall2 R xs ys ->
    Forall (fun x => exists y, R x y) xs.
Proof.
  induction 1; constructor; eauto.
Qed.

Lemma plug_typing_inv : forall P Γ u T,
  Γ ⊢ₜ plug P u : T -> exists T', Γ ⊢ₜ u : T'.
Proof.
  induction P; intros Γ u T H; simpl in H.
  - (* EC_hole *) exists T; exact H.
  - (* EC_app1 *)
    apply app_typing_inv_p in H. destruct H as [A [l [B [Hf _]]]].
    eapply IHP; exact Hf.
  - (* EC_app2 *)
    apply app_typing_inv_p in H. destruct H as [A [l [B [_ [Hx _]]]]].
    eapply IHP; exact Hx.
  - (* EC_ty_app *)
    apply tyapp_typing_inv_p in H. destruct H as [B [U [Ht _]]].
    eapply IHP; exact Ht.
  - (* EC_lt_app *)
    apply ltapp_typing_inv_p in H. destruct H as [U [Ht _]].
    eapply IHP; exact Ht.
  - (* EC_ctor *)
    apply ctor_typing_inv in H.
    destruct H as (n_lt & n_ty & sig & res & rtag & _ & _ & _ & _ & _ & _ & Hf2 & _).
    apply Forall2_Forall_exists in Hf2.
    rewrite Forall_app in Hf2. destruct Hf2 as [_ Hf2].
    apply Forall_inv in Hf2. destruct Hf2 as [rho Hrho].
    eapply IHP; exact Hrho.
  - (* EC_match *)
    apply match_typing_inv in H.
    destruct H as (n_lt & n_ty & sig & res & Ts0 & Delta0 & sr & rtag & rl & eta & er
                   & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hscrut & _).
    eapply IHP; exact Hscrut.
  - (* EC_handler_m *)
    apply handler_m_typing_inv in H. destruct H as [Ht _].
    eapply IHP; exact Ht.
  - (* EC_perform_r *)
    apply perform_typing_inv in H.
    destruct H as (E_tag & Δ & Ts0 & n_α & ops & n_β & sig & ret & si & Hr & _).
    eapply IHP; exact Hr.
  - (* EC_perform_a *)
    apply perform_typing_inv in H.
    destruct H as (E_tag & Δ & Ts0 & n_α & ops & n_β & sig & ret & si
                   & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ha & _).
    eapply IHP; exact Ha.
Qed.

Lemma handle_result_closed_from_plug_typing :
  forall Γ E E_tag Ts T_B T_R op_bodies body T,
    eval_ctx Γ ->
    Γ ⊢ₜ plug E (term_handle E_tag Ts T_B T_R op_bodies body) : T ->
    ty_ty_closed 0 T_R /\ ty_lt_closed 0 T_R.
Proof.
  intros Γ E E_tag Ts T_B T_R op_bodies body T Hec Hty.
  destruct (plug_typing_inv E Γ (term_handle E_tag Ts T_B T_R op_bodies body) T Hty)
    as [Th Hhandle].
  apply handle_typing_inv in Hhandle.
  destruct Hhandle as
    (n_α & ops & Heff & HlenTs & HwfTs & HwfTB & HwfTR
     & Hnl & Hbr & Hfst & Hops & Hbody & Hsub).
  split.
  - eapply ty_wf_eval_ctx_ty_closed; eauto.
  - eapply ty_wf_eval_ctx_lt_closed; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Context conversion for the wf judgments.                           *)
(* [ty_wf]/[lt_wf] depend only on the ty/lt-variable lookups, so they *)
(* are invariant under any context change preserving those lookups —  *)
(* in particular under dropping bind_tm binders (which they ignore).  *)
(* ------------------------------------------------------------------ *)

Lemma ctx_lookup_ty_fold_bind_tm : forall rhos G a,
  ctx_lookup_ty (fold_right (fun rho G0 => bind_tm rho :: G0) G rhos) a = ctx_lookup_ty G a.
Proof.
  induction rhos as [|rho rhos IH]; intros G a; simpl; [reflexivity|apply IH].
Qed.

Lemma ctx_lookup_lt_fold_bind_tm : forall rhos G x,
  ctx_lookup_lt (fold_right (fun rho G0 => bind_tm rho :: G0) G rhos) x = ctx_lookup_lt G x.
Proof.
  induction rhos as [|rho rhos IH]; intros G x; simpl; [reflexivity|apply IH].
Qed.

(* [lt_wf] context conversion is [lt_wf_lookup_eq] (Narrowing.v); the
   [ty_wf] analogue below uses the [ty_wf_mutind] scheme (SubstTy.v). *)
Lemma ty_wf_conv : forall G1 T, ty_wf G1 T ->
  forall G2, (forall a, ctx_lookup_ty G1 a = ctx_lookup_ty G2 a) ->
             (forall x, ctx_lookup_lt G1 x = ctx_lookup_lt G2 x) -> ty_wf G2 T.
Proof.
  apply (ty_wf_mutind
    (fun G1 T (_ : ty_wf G1 T) =>
       forall G2, (forall a, ctx_lookup_ty G1 a = ctx_lookup_ty G2 a) ->
                  (forall x, ctx_lookup_lt G1 x = ctx_lookup_lt G2 x) -> ty_wf G2 T)
    (fun G1 Ts (_ : types_wf G1 Ts) =>
       forall G2, (forall a, ctx_lookup_ty G1 a = ctx_lookup_ty G2 a) ->
                  (forall x, ctx_lookup_lt G1 x = ctx_lookup_lt G2 x) -> types_wf G2 Ts)).
  - (* TWF_Var *) intros Γ α B Hlk Hsub IHB G2 Hty Hlt.
    apply TWF_Var with (B := B). rewrite <- (Hty α). exact Hlk. apply IHB; assumption.
  - (* TWF_Fun *) intros Γ A l B HA IHA Hl HB IHB G2 Hty Hlt.
    apply TWF_Fun; [apply IHA | eapply lt_wf_lookup_eq; [exact Hl|exact Hlt] | apply IHB]; assumption.
  - (* TWF_Ctor *) intros Γ K l Ts Hl HTs IHTs G2 Hty Hlt.
    apply TWF_Ctor; [eapply lt_wf_lookup_eq; [exact Hl|exact Hlt] | apply IHTs; assumption].
  - (* TWF_LtAll *) intros Γ A HA IHA G2 Hty Hlt.
    apply TWF_LtAll. apply IHA.
    + intros a. simpl. rewrite Hty. reflexivity.
    + intros x. destruct x as [|x']; simpl; [reflexivity| rewrite Hlt; reflexivity].
  - (* TWF_TyAll *) intros Γ B A HB IHB HA IHA G2 Hty Hlt.
    apply TWF_TyAll.
    + apply IHB; assumption.
    + apply IHA.
      * intros a. destruct a as [|a']; simpl; [reflexivity| rewrite Hty; reflexivity].
      * intros x. simpl. rewrite Hlt. reflexivity.
  - (* TWFs_nil *) intros Γ G2 Hty Hlt. apply TWFs_nil.
  - (* TWFs_cons *) intros Γ T Ts HT IHT HTs IHTs G2 Hty Hlt.
    apply TWFs_cons; [apply IHT | apply IHTs]; assumption.
Qed.

Lemma ty_wf_fold_bind_tm_inv : forall rhos G T,
  ty_wf (fold_right (fun rho G0 => bind_tm rho :: G0) G rhos) T -> ty_wf G T.
Proof.
  intros rhos G T H.
  eapply ty_wf_conv; [exact H| |].
  - intros a. apply ctx_lookup_ty_fold_bind_tm.
  - intros x. apply ctx_lookup_lt_fold_bind_tm.
Qed.
