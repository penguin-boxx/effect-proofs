Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import Markers.
Require Import Progress.
Require Import Narrowing.
Require Import Variance.
Require Import Inversions.
Require Import Frames.

(* ================================================================== *)
(* Shifting commutes with plugging.                                   *)
(*                                                                    *)
(* No evaluation-context hole sits under a term binder (every frame's *)
(* recursive position keeps the shift cutoff fixed — see              *)
(* `shift_ectx_tm`), so the cutoff is identical on both sides.        *)
(* Used by H_Perform to relate the captured context `P` lifted under  *)
(* the resumption binder to the shifted body.                         *)
(* ================================================================== *)

Lemma shift_tm_plug : forall P amount cutoff u,
  shift_tm amount cutoff (plug P u)
  = plug (shift_ectx_tm amount cutoff P) (shift_tm amount cutoff u).
Proof.
  induction P; intros amount cutoff u;
    try (simpl; rewrite IHP; reflexivity).
  - (* EC_hole *) simpl; reflexivity.
  - (* EC_ctor *)
    cbn [plug shift_ectx_tm shift_tm].
    rewrite shift_tm_go_eq_map. rewrite List.map_app. cbn [List.map].
    rewrite IHP. reflexivity.
Qed.

(* ================================================================== *)
(* Principal-type inversions for elimination forms (residual `<:: T`).*)
(* ================================================================== *)

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

(* Fuller resume inversion: also recover the T_Resume well-formedness    *)
(* side-conditions, needed to rebuild a delimiter in the (resume) case.  *)
Lemma resume_typing_inv_full : forall Γ m T_B T_R b T,
  Γ ⊢ₜ term_resume m T_B T_R b : T ->
  exists A,
    ty_wf Γ A /\ ty_wf Γ T_B /\ ty_wf Γ T_R /\
    Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free /\ Γ ⊢ T_B <:: T_R /\
    (bind_tm A :: Γ) ⊢ₜ b : T_B /\
    Γ ⊢ type_fun A lt_local T_R <:: T.
Proof.
  intros Γ m T_B T_R b T H.
  remember (term_resume m T_B T_R b) as s eqn:Hs.
  induction H; try discriminate Hs.
  - destruct (IHtyping Hs) as [A0 [HwfA [HwfB [HwfR [Hnl [Hbr [Hb Hsub]]]]]]].
    exists A0. repeat (split; [assumption|]). eapply SA_Trans; eassumption.
  - injection Hs; intros; subst.
    exists A. repeat (split; [assumption|]).
    apply SA_Refl. constructor; [assumption | constructor | assumption].
Qed.

(* ================================================================== *)
(*                  PRESERVATION (subject reduction)                  *)
(*                                                                    *)
(* The redex-level preservation lemmas (one per head reduction) that  *)
(* feed the main `preservation` theorem: contracting a redex in an    *)
(* `eval_ctx` preserves typing.  They draw on the eval_ctx            *)
(* substitution metatheory in subst/ (typing_SubstTm / SubstLt /      *)
(* SubstTy and the push_match_bound peels).                                  *)
(* ================================================================== *)

(* Term substitution at index 0 preserves typing (typing_SubstTm_eval_ctx). *)
Lemma subst_tm_preserves : forall Γ A t B v,
  eval_ctx Γ ->
  (bind_tm A :: Γ) ⊢ₜ t : B ->
  value v ->
  Γ ⊢ₜ v : A ->
  Γ ⊢ₜ subst_tm 0 v t : B.
Proof. exact typing_SubstTm_eval_ctx. Qed.

Lemma subst_nl_here_from_ty_app_arg : forall Γ bound S,
  ty_app_arg_no_local Γ bound S = true ->
  subst_nl S 0 (bind_ty bound :: Γ) Γ.
Proof. intros; exact I. Qed.

Lemma tybeta_preserves_with_subst_nl : forall Γ bound body S T,
  eval_ctx Γ ->
  subst_nl S 0 (bind_ty bound :: Γ) Γ ->
  Γ ⊢ₜ term_ty_app (term_ty_lam bound body) S : T ->
  Γ ⊢ₜ subst_ty_in_tm 0 S body : T.
Proof.
  intros Γ bound body S T Hec Hnl Hty.
  apply tyapp_typing_inv_p in Hty.
  destruct Hty as [B [U [Hlam [HSB Hres]]]].
  apply ty_lam_typing_inv in Hlam.
  destruct Hlam as [U0 [Hbody Hallsub]].
  destruct (sub_ty_all_inv_full Γ (type_ty_all bound U0) B U Hec Hallsub) as
    [B' [U' [Heq [HBB' HUsub]]]].
  inversion Heq; subst B' U'.
  assert (HSbound : Γ ⊢ S <:: bound).
  { eapply SA_Trans; eassumption. }
  eapply T_Sub.
  - eapply typing_SubstTy.
    + exact Hbody.
    + apply SubstTy_here. exact HSbound.
    + exact Hnl.
    + apply ctor_fields_closed_bind_ty.
      apply eval_ctx_ctor_fields_closed. exact Hec.
  - eapply SA_Trans.
    + apply (sub_subst_ty Γ B U0 U S HUsub HSB).
    + exact Hres.
Qed.

Lemma tybeta_preserves_declared_bound : forall Γ bound body S T,
  eval_ctx Γ ->
  ty_app_arg_no_local Γ bound S = true ->
  Γ ⊢ₜ term_ty_app (term_ty_lam bound body) S : T ->
  Γ ⊢ₜ subst_ty_in_tm 0 S body : T.
Proof.
  intros Γ bound body S T Hec Harg Hty.
  eapply tybeta_preserves_with_subst_nl; [exact Hec| |exact Hty].
  apply subst_nl_here_from_ty_app_arg. exact Harg.
Qed.

Lemma tybeta_preserves : forall Γ bound body S T,
  eval_ctx Γ ->
  Γ ⊢ₜ term_ty_app (term_ty_lam bound body) S : T ->
  Γ ⊢ₜ subst_ty_in_tm 0 S body : T.
Proof.
  intros Γ bound body S T Hec Hty.
  eapply tybeta_preserves_with_subst_nl; [exact Hec | exact I | exact Hty].
Qed.

Lemma ltbeta_preserves : forall Γ body l T,
  eval_ctx Γ ->
  Γ ⊢ₜ term_lt_app (term_lt_lam body) l : T ->
  Γ ⊢ₜ subst_lt_in_tm 0 l body : T.
Proof.
  intros Γ body l T Hec Hty.
  apply ltapp_typing_inv_p in Hty.
  destruct Hty as [U [Hlam [Hl Hres]]].
  apply lt_lam_typing_inv in Hlam.
  destruct Hlam as [U0 [Hbody Hallsub]].
  destruct (sub_lt_all_inv_full Γ (type_lt_all U0) U Hec Hallsub) as [U0' [Heq HU0sub]].
  inversion Heq; subst U0'.
  eapply T_Sub.
  - eapply typing_SubstLt.
    + exact Hbody.
    + apply SubstLt_here. apply LS_Local. exact Hl.
  - eapply SA_Trans; [ | exact Hres].
    exact (sub_SubstLt (bind_lt lt_local :: Γ) U0 U HU0sub l 0 Γ
             (SubstLt_here Γ lt_local l (LS_Local Γ l Hl))).
Qed.

(* Substitute the constructor's lifetimes [lts]                          *)
(* (peeling the match's push_match_bound block, typing_peel_push_match_bound_fold)     *)
(* then its field values [vs] (typing_subst_list_tm_eval_ctx_global).    *)
(* The peeled field types [subst_list_lt lts (inst_ctor_type_open …)]    *)
(* equal the constructor's [inst_ctor_type … lts] because lts are        *)
(* lt-closed in an eval_ctx (subst_list_lt_in_ty_inst_ctor_type_open).   *)
(* The branch result type is reconciled with [T] via elim_ty_n_sound_pos.*)
Lemma matchyes_preserves : forall Γ K l lts Ts vs n_lt yes_body no_body T,
  eval_ctx Γ -> Forall value vs ->
  Γ ⊢ₜ term_match (term_ctor K l lts Ts vs) K n_lt (List.length vs) yes_body no_body : T ->
  Γ ⊢ₜ subst_list_tm vs (subst_list_lt_in_tm lts yes_body) : T.
Proof.
  intros Γ K l lts Ts vs n_lt yes_body no_body T Hec Hvals Hty.
  apply match_typing_inv in Hty.
  destruct Hty as (n_lt' & n_ty & sigma_fields & result_ty_schema & Ts' & Delta &
    scrut_result_ty & result_tag & result_l & eta & elim_result & HKne & Hlk & Heff &
    Hn_lt_eq & HlenTs & Hscrut_result & Hscrut_shape & Hrtne & HwfDelta & Hresult_l &
    Hscrut & Harity & Hyes & Helim & Hno & HsubOr).
  subst n_lt'.
  apply ctor_typing_inv in Hscrut.
  destruct Hscrut as (n_lt2 & n_ty2 & sigma2 & result2 & result_tag2 &
    Hlk2 & Hltlen & HTslen2 & Hresult2 & Hbounded & Hvslen & Hf2 & Hsub2).
  rewrite Hlk in Hlk2. injection Hlk2 as Hn2 Hnty2 Hsig2 Hres2.
  subst n_lt2 n_ty2 sigma2 result2.
  destruct (sub_ctor_inv Γ (type_ctor result_tag2 l Ts) result_tag Delta Ts' Hec Hsub2 Hrtne)
    as (l'' & Heq & Hl_Delta).
  injection Heq as Htag2 Hl'' HTseq. subst result_tag2. subst Ts'. subst l''.
  (* lts are lt-closed (well-formed lifetimes in an eval_ctx). *)
  assert (Hclosed : Forall (fun l0 => lt_lt_closed 0 l0) lts).
  { eapply Forall_impl; [|exact Hbounded]. intros l0 Hl0.
    eapply lt_wf_eval_ctx_lt_closed; [exact Hec|].
    exact (proj1 (lt_sub_wf Γ l0 l Hl0)). }
  (* lts <: Delta (transitively through l). *)
  assert (HboundedD : Forall (fun l0 => Γ ⊢ₗ l0 <: Delta) lts).
  { eapply Forall_impl; [|exact Hbounded]. intros l0 Hl0.
    eapply LS_Trans; [exact Hl0 | exact Hl_Delta]. }
  (* peel the push_match_bound block by substituting lts. *)
  assert (Hyes' :
    (List.fold_right (fun rho G => bind_tm rho :: G)
      (push_match_bound (List.length lts) Delta Γ)
      (List.map (inst_ctor_type_open n_lt n_ty Ts) sigma_fields))
      ⊢ₜ yes_body : eta).
  { rewrite Hltlen. exact Hyes. }
  pose proof (typing_peel_push_match_bound_fold lts Delta
    (List.map (inst_ctor_type_open n_lt n_ty Ts) sigma_fields)
    yes_body eta Γ HboundedD Hyes') as Hpeel.
  (* the peeled field types are exactly the constructor's field types. *)
  assert (Hmapeq :
    List.map (subst_list_lt_in_ty lts)
      (List.map (inst_ctor_type_open n_lt n_ty Ts) sigma_fields) =
    List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields).
  { rewrite List.map_map. apply List.map_ext. intro s.
    apply subst_list_lt_in_ty_inst_ctor_type_open. exact Hclosed. }
  rewrite Hmapeq in Hpeel.
  (* substitute the field values. *)
  pose proof (typing_subst_list_tm_eval_ctx_global Γ vs
    (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields)
    (subst_list_lt_in_tm lts yes_body) (subst_list_lt_in_ty lts eta)
    Hec Hf2 Hvals) as Hsubst.
  assert (Hfree : List.concat (List.map (free_tm_vars 0) vs) = []).
  { clear -Hec Hf2. induction Hf2; simpl; [reflexivity|].
    rewrite (typing_closed _ _ _ Hec H), IHHf2. reflexivity. }
  specialize (Hsubst Hfree Hpeel).
  (* reconcile the branch result type with T via elim soundness. *)
  assert (HwfEta : ty_wf (push_match_bound n_lt Delta Γ) eta).
  { apply (ty_wf_fold_bind_tm_inv (List.map (inst_ctor_type_open n_lt n_ty Ts) sigma_fields)).
    eapply typing_implies_wf. exact Hyes. }
  pose proof (elim_ty_n_sound_pos n_lt Delta lts eta elim_result Γ
    Helim Hltlen HwfDelta HwfEta HboundedD) as HetaSub.
  eapply T_Sub; [exact Hsubst|].
  destruct HsubOr as [Heq | Hsub]; [subst elim_result; exact HetaSub|].
  eapply SA_Trans; [exact HetaSub | exact Hsub].
Qed.

(* ================================================================== *)
(*  perform_preserves.                                                 *)
(*                                                                    *)
(*  Reducing  handler_m m T_B T_R (P[perform (cap …) Ss v]) to         *)
(*  op_body[Ss][v, resume]  preserves typing.  The proof:             *)
(*  (a) handler/plug/perform/cap inversions recover the cap's op_body  *)
(*      typing (under push_ty_vars n_β any_at_free, two bind_tm) and   *)
(*      reconcile the two effect lookups (perform vs cap) via          *)
(*      sub_ctor_inv + lookup determinism;                             *)
(*  (b) the push_ty_vars TYPE peel substitutes Ss into op_body, with   *)
(*      the operation-signature reconciliation                         *)
(*      subst_list_ty Ss (inst_op_ty_args …) = inst_op_all_args … Ss …;       *)
(*  (c) the reified resumption plug (shift P)(var 0) is typed by       *)
(*      weakening + shift_tm_plug + plug_typing_replace, the focus     *)
(*      replacement justified by the perform's principal type ret_inst *)
(*      being unchanged under term-shift (perform_principal_general);  *)
(*  (d) the two term arguments [v; resume] are substituted by          *)
(*      typing_subst_list_tm_eval_ctx_global.                          *)
(* ================================================================== *)

(* ctx_lookup_ty / ctx_lookup_eff ignore a bind_tm prefix. *)
Lemma ctx_lookup_ty_bind_tm : forall A Γ α,
  ctx_lookup_ty (bind_tm A :: Γ) α = ctx_lookup_ty Γ α.
Proof. intros; reflexivity. Qed.

Lemma ctx_lookup_eff_bind_tm : forall A Γ E,
  ctx_lookup_eff (bind_tm A :: Γ) E = ctx_lookup_eff Γ E.
Proof. intros; reflexivity. Qed.

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

(* The perform's principal type is ret_inst; any type it can be given is
   a supertype.  Works in any no-type-var context whose effect lookup at
   any_tag is None (covers Γ and bind_tm _ :: Γ). *)
Lemma perform_principal_general :
  forall G E_tag m n_β Ts T_R op_body Ss arg n_α sig ret ret_inst Tu,
  (forall α, ctx_lookup_ty G α = None) ->
  ctx_lookup_eff G any_tag = None ->
  ctx_lookup_eff G E_tag = Some (n_α, n_β, sig, ret) ->
  ret_inst = inst_op_all_args n_α Ts n_β Ss ret ->
  G ⊢ₜ term_perform (term_cap E_tag m n_β Ts T_R op_body) Ss arg : Tu ->
  G ⊢ ret_inst <:: Tu.
Proof.
  intros G E_tag m n_β Ts T_R op_body Ss arg n_α sig ret ret_inst Tu
         Hnoty Hany Heff Hri Hperf.
  apply perform_typing_inv in Hperf.
  destruct Hperf as
    [E_t1 [Δ1 [Ts1 [n_α1 [n_β1 [sig1 [ret1 [sig_inst1 [ret_inst1
      [Hrecv1 [Heff1 [HlenTs1 [HlenSs1 [HwfSs1 [HnlSs1 [Hsi1 [Hnlsi1
        [Hri1 [HwfRi1 [Harg1 Hsub1]]]]]]]]]]]]]]]]]]]].
  apply cap_typing_inv in Hrecv1.
  destruct Hrecv1 as
    [n_α2 [sig2 [ret2 [sig_β2 [ret_β2 [Heff2 [HlenTs2 [HwfTs2 [HwfTR2
      [Hsigβ2 [Hretβ2 [Hop2 HsubRecv2]]]]]]]]]]]].
  assert (HEt1 : E_t1 <> any_tag).
  { intros Heq; subst E_t1. rewrite Hany in Heff1; discriminate. }
  destruct (sub_ctor_inv_noty G (type_ctor E_tag lt_local Ts) E_t1 Δ1 Ts1
              Hnoty HsubRecv2 HEt1) as [l' [Heqctor Hl']].
  injection Heqctor as HEtag Hl'' HTs. subst E_t1. subst Ts1.
  assert (Hee : n_α1 = n_α /\ n_β1 = n_β /\ sig1 = sig /\ ret1 = ret).
  { rewrite Heff in Heff1. injection Heff1; intros; subst; repeat split; reflexivity. }
  destruct Hee as (Hna & Hnb & Hsg & Hrt).
  rewrite Hna, Hnb, Hrt in Hri1.
  rewrite Hri, <- Hri1. exact Hsub1.
Qed.

(* Type the reified resumption body [plug (shift P)(var 0)]. *)
Lemma perform_resume_body :
  forall Γ ret_inst E_tag m n_β Ts T_R op_body Ss v P T_B n_α sig ret,
  eval_ctx Γ ->
  ty_wf Γ ret_inst ->
  ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
  ret_inst = inst_op_all_args n_α Ts n_β Ss ret ->
  Γ ⊢ₜ plug P (term_perform (term_cap E_tag m n_β Ts T_R op_body) Ss v) : T_B ->
  (bind_tm ret_inst :: Γ) ⊢ₜ plug (shift_ectx_tm 1 0 P) (term_var 0) : T_B.
Proof.
  intros Γ ret_inst E_tag m n_β Ts T_R op_body Ss v P T_B n_α sig ret
         Hec HwfRi Heff Hri Hplug.
  pose proof (typing_weaken_tm_shift Γ ret_inst _ _ Hplug) as Hw.
  rewrite shift_tm_plug in Hw.
  eapply plug_typing_replace; [exact Hw|].
  intros Tu Hu.
  eapply T_Sub.
  - apply T_Var.
    + reflexivity.
    + apply (ty_wf_InsTm Γ ret_inst HwfRi). apply InsTm_here.
  - eapply (perform_principal_general (bind_tm ret_inst :: Γ)
              E_tag m n_β Ts T_R (shift_tm 1 2 op_body) Ss (shift_tm 1 0 v)
              n_α sig ret ret_inst Tu).
    + intros α. rewrite ctx_lookup_ty_bind_tm. apply (eval_ctx_no_ty Γ α Hec).
    + rewrite ctx_lookup_eff_bind_tm. apply (eval_ctx_no_eff_any Γ Hec).
    + rewrite ctx_lookup_eff_bind_tm. exact Heff.
    + exact Hri.
    + exact Hu.
Qed.

Lemma perform_preserves :
  forall Γ E_tag m n_beta Ts T_B T_R op_body Ss v P T,
  eval_ctx Γ -> value v -> pure_ectx_m m P ->
  Γ ⊢ₜ term_handler_m m T_B T_R
        (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v)) : T ->
  Γ ⊢ₜ subst_list_tm
         [v; term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))]
         (subst_list_ty_in_tm Ss op_body) : T.
Proof.
  intros Γ E_tag m n_beta Ts T_B T_R op_body Ss v P T Hec Hval HpureP Hty.
  (* (a) inversions *)
  apply handler_m_typing_inv in Hty.
  destruct Hty as [Hplug [HTBR [HnlTB HTRT]]].
  destruct (plug_typing_inv P Γ _ _ Hplug) as [Tu Hperf].
  apply perform_typing_inv in Hperf.
  destruct Hperf as
    [E_t0 [Δ0 [Ts0 [n_α [n_β [sig [ret [sig_inst [ret_inst
      [Hrecv [Heff0 [HlenTs0 [HlenSs [HwfSs [HnlSs [Hsi [Hnlsi
        [Hri [HwfRi [Harg HsubTu]]]]]]]]]]]]]]]]]]]].
  apply cap_typing_inv in Hrecv.
  destruct Hrecv as
    [n_α' [sig' [ret' [sig_β [ret_β [Heff' [HlenTs [HwfTs [HwfTR
      [Hsigβ [Hretβ [Hop HsubRecv]]]]]]]]]]]].
  (* reconcile tags & effect lookups (in eval_ctx Γ) *)
  assert (HEt0 : E_t0 <> any_tag).
  { intros Heq; subst E_t0. rewrite (eval_ctx_no_eff_any _ Hec) in Heff0; discriminate. }
  destruct (sub_ctor_inv Γ (type_ctor E_tag lt_local Ts) E_t0 Δ0 Ts0 Hec HsubRecv HEt0)
    as [l' [Heqctor Hl']].
  injection Heqctor as HEtag Hl'' HTs. subst E_t0. subst Ts0.
  assert (Hee : n_α' = n_α /\ n_beta = n_β /\ sig' = sig /\ ret' = ret).
  { rewrite Heff' in Heff0. injection Heff0; intros; subst; repeat split; reflexivity. }
  destruct Hee as (Hna & Hnb & Hsg & Hrt). subst sig' ret'.
  rewrite Hna in Hsigβ, Hretβ.
  rewrite <- Hnb in Hsi, Hri, HlenSs, Heff0.
  (* (b) type-peel: substitute Ss into op_body *)
  assert (HallSub : Forall (fun S => Γ ⊢ S <:: any_at_free) Ss).
  { clear -HwfSs HnlSs. revert HwfSs HnlSs. induction Ss as [|S0 rest IH];
      intros HwfSs HnlSs; [constructor|].
    inversion HwfSs as [|? ? ? HwfS0 HwfRest]; subst.
    inversion HnlSs as [|? ? HnlS0 HnlRest]; subst.
    constructor.
    + unfold any_at_free. apply SA_Any; [exact HwfS0 | apply LWF_Free | exact HnlS0].
    + apply IH; assumption. }
  assert (Hpremise :
    (List.fold_right (fun rho G => bind_tm rho :: G)
       (push_ty_vars (List.length Ss) any_at_free Γ)
       [sig_β; type_fun ret_β lt_local (shift_ty n_beta 0 T_R)])
       ⊢ₜ op_body : shift_ty n_beta 0 T_R).
  { cbn [List.fold_right]. rewrite HlenSs. exact Hop. }
  pose proof (typing_peel_push_ty_vars_fold Ss
    [sig_β; type_fun ret_β lt_local (shift_ty n_beta 0 T_R)]
    op_body (shift_ty n_beta 0 T_R) Γ HallSub
    (eval_ctx_ctor_fields_closed Γ Hec) Hpremise) as Hpeel.
  (* operation-signature reconciliations *)
  assert (Hsigeq : subst_list_ty Ss sig_β = sig_inst).
  { rewrite Hsigβ. rewrite (subst_list_ty_inst_op_ty_args n_α Ts n_beta Ss sig HlenSs).
    symmetry; exact Hsi. }
  assert (HTReq : subst_list_ty Ss (shift_ty n_beta 0 T_R) = T_R).
  { rewrite <- HlenSs. apply subst_list_ty_shift_cancel. }
  assert (Hrhokeq : subst_list_ty Ss (type_fun ret_β lt_local (shift_ty n_beta 0 T_R))
                    = type_fun ret_inst lt_local T_R).
  { rewrite subst_list_ty_fun. rewrite HTReq.
    rewrite Hretβ. rewrite (subst_list_ty_inst_op_ty_args n_α Ts n_beta Ss ret HlenSs).
    rewrite <- Hri. reflexivity. }
  cbn [List.map List.fold_right] in Hpeel.
  rewrite Hsigeq, Hrhokeq, HTReq in Hpeel.
  (* (c) type the resumption *)
  assert (Hresume : Γ ⊢ₜ term_resume m T_B T_R
                        (plug (shift_ectx_tm 1 0 P) (term_var 0))
                        : type_fun ret_inst lt_local T_R).
  { apply T_Resume.
    - exact HwfRi.
    - eapply typing_implies_wf; exact Hplug.
    - exact HwfTR.
    - exact HnlTB.
    - exact HTBR.
    - eapply perform_resume_body;
        [exact Hec | exact HwfRi | exact Heff0 | exact Hri | exact Hplug]. }
  (* (d) substitute the two term arguments *)
  eapply T_Sub; [|exact HTRT].
  eapply (typing_subst_list_tm_eval_ctx_global Γ
    [v; term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))]
    [sig_inst; type_fun ret_inst lt_local T_R]
    (subst_list_ty_in_tm Ss op_body) T_R Hec).
  - constructor; [exact Harg | constructor; [exact Hresume | constructor]].
  - constructor; [exact Hval | constructor; [apply value_resume | constructor]].
  - cbn [List.map List.concat].
    rewrite (typing_closed _ _ _ Hec Harg).
    rewrite (typing_closed _ _ _ Hec Hresume). reflexivity.
  - cbn [List.fold_right]. exact Hpeel.
Qed.

(* ================================================================== *)
(* marker_ok preservation for handler-elimination (H_Perform).        *)
(* Lives here (not in Markers.v) so the [v]-confinement can use the   *)
(* typing-side escape lemma [value_no_local_no_rt_cap] +              *)
(* [perform_typing_inv], only importable below Frames.  The reduct's  *)
(* confinement rests on the runtime well-scopedness invariant         *)
(* [well_scoped] (Markers.v): op_body confinement from                *)
(* [well_scoped_step_handler_confinement], the perform argument [v]   *)
(* carries no markers (no-local closed value), and resume re-adds m.  *)
(* ================================================================== *)
Lemma marker_ok_step_handler_elim :
  forall Γ m T_B T_R E_tag n_beta Ts op_body Ss v P Tr ms,
  eval_ctx Γ ->
  value v ->
  pure_ectx_m m P ->
  Γ ⊢ₜ term_handler_m m T_B T_R
        (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v)) : Tr ->
  marker_ok ms (term_handler_m m T_B T_R
        (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))) ->
  well_scoped ms (term_handler_m m T_B T_R
        (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))) ->
  marker_ok ms
    (subst_list_tm
       [v; term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))]
       (subst_list_ty_in_tm Ss op_body)).
Proof.
  intros Γ m T_B T_R E_tag n_beta Ts op_body Ss v P Tr ms Hec Hval Hpure Hty Hok Hws.
  pose proof (well_scoped_step_handler_confinement _ _ _ _ _ _ _ _ _ _ _ _ Hws Hpure)
    as Hopconf.
  assert (Hvmok : forall ms0, marker_ok ms0 v).
  { apply handler_m_typing_inv in Hty.
    destruct Hty as [Hplug [HTBR [HnlTB HTRT]]].
    destruct (plug_typing_inv P Γ _ _ Hplug) as [Tu Hperf].
    apply perform_typing_inv in Hperf.
    destruct Hperf as
      [E_t0 [Δ0 [Ts0 [n_α [n_β [sig [ret [sig_inst [ret_inst
        [Hrecv [Heff0 [HlenTs0 [HlenSs [HwfSs [HnlSs [Hsi [Hnlsi
          [Hri [HwfRi [Harg HsubTu]]]]]]]]]]]]]]]]]]]].
    assert (Hcap : has_rt_cap v = false).
    { eapply value_no_local_no_rt_cap;
        [ exact Hec | exact Harg | exact Hval
        | eapply typing_closed; [exact Hec | exact Harg] | exact Hnlsi ]. }
    intros ms0. apply marker_ok_no_rt_cap. exact Hcap. }
  simpl in Hok.
  apply marker_ok_subst_list_tm.
  - apply Forall_cons.
    + apply Hvmok.
    + apply Forall_cons; [| apply Forall_nil].
      simpl.
      assert (Hvar0 : marker_ok (m :: ms) (plug P (term_var 0))).
      { eapply marker_ok_plug_replace; [exact Hok | intros ms' _; exact I]. }
      pose proof (marker_ok_shift_tm (plug P (term_var 0)) (m :: ms) 1 0 Hvar0) as Hsh.
      rewrite shift_tm_plug_markers in Hsh.
      eapply marker_ok_plug_replace; [exact Hsh | intros ms' _; exact I].
  - apply marker_ok_subst_list_ty_in_tm. exact Hopconf.
Qed.

(* A head step preserves marker_ok uniformly in the scope. *)
Lemma head_step_preserves_marker_ok : forall Γ r r' Tr,
  eval_ctx Γ ->
  Γ ⊢ₜ r : Tr -> marker_types_safe r -> r -->h r' ->
  forall ms, marker_ok ms r -> well_scoped ms r -> marker_ok ms r'.
Proof.
  intros Γ r r' Tr Hec Hr Hsafe Hstep ms Hok Hws. inversion Hstep; subst.
  - (* H_Beta *)
    destruct Hok as [Hbody Hv]. apply marker_ok_subst_tm; [exact Hv | exact Hbody].
  - (* H_TyBeta *)
    apply marker_ok_subst_ty_in_tm. exact Hok.
  - (* H_LtBeta *)
    apply marker_ok_subst_lt_in_tm. exact Hok.
  - (* H_MatchYes *)
    destruct Hok as [Hctor [Hyes Hno]].
    apply marker_ok_subst_list_tm.
    + apply (marker_ok_ctor_args_forall ms K l lts Ts vs Hctor).
    + apply marker_ok_subst_list_lt_in_tm. exact Hyes.
  - (* H_MatchNo *)
    destruct Hok as [Hctor [Hyes Hno]]. exact Hno.
  - (* H_Return *)
    destruct (handler_m_typing_inv_markers _ _ _ _ _ _ Hr) as [Hbody Hnl].
    pose proof (typing_closed _ _ _ Hec Hr) as Hcl. simpl in Hcl.
    eapply marker_ok_handler_return_no_cap; [ | exact Hok ].
    eapply value_no_local_no_rt_cap;
      [ exact Hec | exact Hbody | assumption | exact Hcl | exact Hnl ].
  - (* H_Perform *)
    eapply marker_ok_step_handler_elim;
      [ exact Hec | eassumption | eassumption | exact Hr | exact Hok | exact Hws ].
  - (* H_Resume *)
    destruct Hok as [Hres Hv].
    apply marker_ok_subst_tm.
    + eapply marker_ok_mono; [apply incl_tl; apply incl_refl | exact Hv].
    + exact Hres.
Qed.

(* One reduction step preserves marker_ok [] (given the well-scopedness  *)
(* invariant for the current state).                                     *)
Lemma step_preserves_marker_ok : forall Γ t t' T,
  eval_ctx Γ -> marker_ok [] t -> marker_types_safe t -> Γ ⊢ₜ t : T ->
  well_scoped [] t ->
  t ==> t' -> marker_ok [] t'.
Proof.
  intros Γ t t' T Hec Hmok Hsafe Hty Hws Hstep.
  inversion Hstep as
    [E r r' Hwf Hhead Heq1 Heq2
    | E E_tag n_beta Ts T_B T_R op_body body m Hwf Hfresh Heq1 Heq2]; subst.
  - (* S_step *)
    destruct (plug_typing_inv E Γ r T Hty) as [Tr Hr].
    assert (Hsafe_r : marker_types_safe r).
    { eapply marker_types_safe_incl;
        [ intros p Hp; apply (marker_annots_plug_in E r p Hp) | exact Hsafe ]. }
    eapply marker_ok_well_scoped_plug_replace; [ exact Hmok | exact Hws | ].
    intros ms' Hm Hwm.
    eapply head_step_preserves_marker_ok;
      [ exact Hec | exact Hr | exact Hsafe_r | exact Hhead | exact Hm | exact Hwm ].
  - (* S_HandleCtx *)
    eapply marker_ok_plug_replace; [ exact Hmok | ].
    intros ms' Hm. destruct Hm as [Hop Hbody]. simpl.
    apply marker_ok_subst_tm.
    + simpl. split.
      * left. reflexivity.
      * eapply marker_ok_mono; [ apply incl_tl; apply incl_tl; apply incl_refl | exact Hop ].
    + eapply marker_ok_mono; [ apply incl_tl; apply incl_refl | exact Hbody ].
Qed.

(* Head reductions preserve typing (at any type, under eval_ctx). *)
Lemma head_step_preserves_typing : forall Γ r r' T,
  eval_ctx Γ -> Γ ⊢ₜ r : T -> r -->h r' -> Γ ⊢ₜ r' : T.
Proof.
  intros Γ r r' T Hec Hty Hstep.
  inversion Hstep; subst.
  - (* H_Beta *)
    apply app_typing_inv_p in Hty.
    destruct Hty as [A [l [B [Hlam [Hv Hsub]]]]].
    apply lam_typing_inv in Hlam. destruct Hlam as [l' [B' [Hbody Hfsub]]].
    apply (sub_fun_inv Γ _ A l B Hec) in Hfsub.
    destruct Hfsub as [A'' [l'' [B'' [Heq [HAsub [Hlsub HBsub]]]]]].
    injection Heq; intros; subst.
    eapply T_Sub; [ | eapply SA_Trans; [exact HBsub | exact Hsub] ].
    eapply subst_tm_preserves; [exact Hec | exact Hbody | assumption |].
    eapply T_Sub; [exact Hv | exact HAsub].
  - (* H_TyBeta *)
    eapply tybeta_preserves; eauto.
  - (* H_LtBeta *)
    eapply ltbeta_preserves; eauto.
  - (* H_MatchYes *)
    eapply matchyes_preserves; eauto.
  - (* H_MatchNo *)
    apply match_typing_inv in Hty.
    destruct Hty as [nlt1 [nty1 [sig1 [res1 [Ts1 [Delta1 [srt1 [rtag1 [rl1 [eta1 [elimr1 Hconj]]]]]]]]]]].
    destruct Hconj as (HK & Hlk & Heff & Hnlt & HlenTs & Hsr & Hss & Hrne &
       HwfD & Hrl & Hscrut & Har & Hbody & Helim & Hno & HsubOr).
    destruct HsubOr as [Heq | Hsub].
    + subst. exact Hno.
    + eapply T_Sub; [exact Hno | exact Hsub].
  - (* H_Return *)
    apply handler_m_typing_inv in Hty.
    destruct Hty as [Hv [Hbr [_ Hrt]]].
    eapply T_Sub; [exact Hv | eapply SA_Trans; [exact Hbr | exact Hrt]].
  - (* H_Perform *)
    eapply perform_preserves; eauto.
  - (* H_Resume *)
    apply app_typing_inv_p in Hty.
    destruct Hty as [A [l [B [Hres [Hv Hsub]]]]].
    apply resume_typing_inv_full in Hres.
    destruct Hres as [A0 [HwfA0 [HwfTB [HwfTR [Hnl [Hbr [Hb Hfsub]]]]]]].
    apply (sub_fun_inv Γ _ A l B Hec) in Hfsub.
    destruct Hfsub as [A'' [l'' [B'' [Heq [HAsub [Hlsub HBsub]]]]]].
    injection Heq; intros; subst.
    eapply T_Sub; [ | eapply SA_Trans; [ | exact Hsub] ].
    + apply T_HandlerM; try assumption.
      eapply subst_tm_preserves; [exact Hec | exact Hb | assumption |].
      eapply T_Sub; [exact Hv | exact HAsub].
    + exact HBsub.
Qed.

(* Handle inversion (principal): recover the T_Handle premises + T_R <:: T. *)
Lemma handle_typing_inv : forall Γ E_tag n_beta Ts T_B T_R op_body body T,
  Γ ⊢ₜ term_handle E_tag n_beta Ts T_B T_R op_body body : T ->
  exists n_α sig ret sig_β ret_β,
    ctx_lookup_eff Γ E_tag = Some (n_α, n_beta, sig, ret) /\
    List.length Ts = n_α /\ types_wf Γ Ts /\
    ty_wf Γ T_B /\ ty_wf Γ T_R /\ Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free /\ Γ ⊢ T_B <:: T_R /\
    sig_β = inst_op_ty_args n_α Ts n_beta sig /\
    ret_β = inst_op_ty_args n_α Ts n_beta ret /\
    (bind_tm sig_β
      :: bind_tm (type_fun ret_β lt_local (shift_ty n_beta 0 T_R))
      :: push_ty_vars n_beta any_at_free Γ)
      ⊢ₜ op_body : shift_ty n_beta 0 T_R /\
    (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) ⊢ₜ body : T_B /\
    Γ ⊢ T_R <:: T.
Proof.
  intros Γ E_tag n_beta Ts T_B T_R op_body body T H.
  remember (term_handle E_tag n_beta Ts T_B T_R op_body body) as s eqn:Hs.
  induction H; try discriminate Hs.
  - destruct (IHtyping Hs) as
      (n_α & sig & ret & sig_β & ret_β & Heff & HlenTs & HwfTs & HwfTB & HwfTR
       & Hnl & Hbr & Hsigβ & Hretβ & Hop & Hbody & Hsub).
    exists n_α, sig, ret, sig_β, ret_β.
    repeat (split; [assumption|]). eapply SA_Trans; eassumption.
  - injection Hs; intros; subst.
    do 5 eexists.
    repeat split; try eassumption; try reflexivity.
    apply SA_Refl. assumption.
Qed.

(* Allocating a fresh handler delimiter preserves typing. *)
Lemma handle_step_preserves_typing :
  forall Γ E_tag n_beta Ts T_B T_R op_body body m T,
  eval_ctx Γ ->
  Γ ⊢ₜ term_handle E_tag n_beta Ts T_B T_R op_body body : T ->
  Γ ⊢ₜ term_handler_m m T_B T_R
        (subst_tm 0 (term_cap E_tag m n_beta Ts T_R op_body) body) : T.
Proof.
  intros Γ E_tag n_beta Ts T_B T_R op_body body m T Hec Hty.
  apply handle_typing_inv in Hty.
  destruct Hty as
    (n_α & sig & ret & sig_β & ret_β & Heff & HlenTs & HwfTs & HwfTB & HwfTR
     & Hnl & Hbr & Hsigβ & Hretβ & Hop & Hbody & Hsub).
  assert (Hcap : Γ ⊢ₜ term_cap E_tag m n_beta Ts T_R op_body
                   : type_ctor E_tag lt_local Ts).
  { eapply T_Cap; eassumption. }
  eapply T_Sub; [ | exact Hsub ].
  apply T_HandlerM; try assumption.
  eapply subst_tm_preserves; [ exact Hec | exact Hbody | apply value_cap | exact Hcap ].
Qed.

(* Reduction preserves typing. *)
Lemma step_preserves_typing : forall Γ t t' T,
  eval_ctx Γ -> Γ ⊢ₜ t : T -> t ==> t' -> Γ ⊢ₜ t' : T.
Proof.
  intros Γ t t' T Hec Hty Hstep.
  inversion Hstep as [E r r' Hwf Hhead Heq1 Heq2 | E E_tag n_beta Ts T_B T_R op_body body m Hwf Hfresh Heq1 Heq2]; subst.
  - (* S_step *)
    eapply plug_typing_replace; [ exact Hty | ].
    intros Tu Hu. eapply head_step_preserves_typing; [ exact Hec | exact Hu | exact Hhead ].
  - (* S_HandleCtx *)
    eapply plug_typing_replace; [ exact Hty | ].
    intros Tu Hu. eapply handle_step_preserves_typing; [ exact Hec | exact Hu ].
Qed.

(* Subject reduction (typing preservation under one step). *)
Theorem preservation : forall Γ t t' T,
  eval_ctx Γ -> Γ ⊢ₜ t : T -> t ==> t' -> Γ ⊢ₜ t' : T.
Proof. exact step_preserves_typing. Qed.
