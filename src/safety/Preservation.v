Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import MarkerAnnots.
Require Import WellScoped.
Require Import WsRtLaws.
Require Import Progress.
Require Import Narrowing.
Require Import Variance.
Require Import Frames.
Require Import TypingInv.

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
    rewrite List.map_app. cbn [List.map].
    rewrite IHP. reflexivity.
Qed.


(* ================================================================== *)
(*                  PRESERVATION (subject reduction)                  *)
(*                                                                    *)
(* The redex-level preservation lemmas (one per head reduction) that  *)
(* feed the main `preservation` theorem: contracting a redex in an    *)
(* `eval_ctx` preserves typing.  They draw on the eval_ctx            *)
(* substitution metatheory in subst/ (typing_SubstTm / SubstLt /      *)
(* SubstTy and the push_match_bound peels).                           *)
(* ================================================================== *)

(* Term substitution at index 0 preserves typing (typing_SubstTm_eval_ctx). *)
Lemma subst_tm_preserves : forall Γ A t B v,
  eval_ctx Γ ->
  (bind_tm A :: Γ) ⊢ₜ t : B ->
  value v ->
  Γ ⊢ₜ v : A ->
  Γ ⊢ₜ subst_tm 0 v t : B.
Proof. exact typing_SubstTm_eval_ctx. Qed.

Lemma tybeta_preserves : forall Γ bound body S T,
  eval_ctx Γ ->
  Γ ⊢ₜ term_ty_app (term_ty_lam bound body) S : T ->
  Γ ⊢ₜ subst_ty_in_tm 0 S body : T.
Proof.
  intros Γ bound body S T Hec Hty.
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
    + apply ctor_fields_closed_bind_ty.
      apply eval_ctx_ctor_fields_closed. exact Hec.
  - eapply SA_Trans.
    + apply (sub_subst_ty Γ B U0 U S HUsub HSB).
    + exact Hres.
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
  { clear -Hec Hf2. revert Hec.
    induction Hf2 as [Γ0|Γ0 v0 rho0 vs0 rhos0 Hv0 Hf2 IH]; intros Hec; simpl;
      [reflexivity|].
    rewrite (typing_closed _ _ _ Hec Hv0), (IH Hec). reflexivity. }
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

(* The perform's principal type is its ret_inst annotation; any type it
   can be given is a supertype.  Immediate from perform_typing_inv: the
   annotation is written on the term. *)
Lemma perform_principal_general :
  forall G recv op Ss A arg Tu,
  G ⊢ₜ term_perform recv op Ss A arg : Tu ->
  G ⊢ A <:: Tu.
Proof.
  intros G recv op Ss A arg Tu Hperf.
  apply perform_typing_inv in Hperf.
  destruct Hperf as
    (E_t & Δ & Ts & n_α & ops & n_β & sig & ret & sig_inst
     & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsub).
  exact Hsub.
Qed.

(* Type the captured-continuation body [plug (shift P) (var 0)] under
   the resumption lambda's binder. *)
Lemma perform_resume_body :
  forall Γ ret_inst E_tag m Ts T_R op_bodies op Ss v P T_B,
  eval_ctx Γ ->
  ty_wf Γ ret_inst ->
  Γ ⊢ₜ plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss ret_inst v) : T_B ->
  (bind_tm ret_inst :: Γ) ⊢ₜ plug (shift_ectx_tm 1 0 P) (term_var 0) : T_B.
Proof.
  intros Γ ret_inst E_tag m Ts T_R op_bodies op Ss v P T_B Hec HwfRi Hplug.
  pose proof (typing_weaken_tm_shift Γ ret_inst _ _ Hplug) as Hw.
  rewrite shift_tm_plug in Hw.
  eapply plug_typing_replace; [exact Hw|].
  intros Tu Hu.
  eapply T_Sub.
  - apply T_Var.
    + reflexivity.
    + apply (ty_wf_InsTm Γ ret_inst HwfRi). apply InsTm_here.
  - eapply perform_principal_general. exact Hu.
Qed.

(* ==================================================================== *)
(*  perform_preserves.                                                  *)
(*                                                                      *)
(*  Reducing  handler_m m T_B T_R (P[perform (cap …) Ss v]) to          *)
(*  op_body[Ss][v, resume]  preserves typing.  The proof:               *)
(*  (a) handler/plug/perform/cap inversions recover the cap's op_body   *)
(*      typing (under push_ty_vars n_β any_at_free, two bind_tm) and    *)
(*      reconcile the two effect lookups (perform vs cap) via           *)
(*      sub_ctor_inv + lookup determinism;                              *)
(*  (b) the push_ty_vars TYPE peel substitutes Ss into op_body, with    *)
(*      the operation-signature reconciliation                          *)
(*      subst_list_ty Ss (inst_op_ty_args …) = inst_op_all_args … Ss …; *)
(*  (c) the reified resumption plug (shift P)(var 0) is typed by        *)
(*      weakening + shift_tm_plug + plug_typing_replace, the focus      *)
(*      replacement justified by the perform's principal type ret_inst  *)
(*      being unchanged under term-shift (perform_principal_general);   *)
(*  (d) the two term arguments [v; resume] are substituted by           *)
(*      typing_subst_list_tm_eval_ctx_global.                           *)
(* ==================================================================== *)
Lemma perform_preserves :
  forall Γ E_tag m Ts T_B T_R op_bodies op n_beta op_body Ss A v P T,
  eval_ctx Γ -> value v -> pure_ectx_m m P ->
  nth_error op_bodies op = Some (n_beta, op_body) ->
  Γ ⊢ₜ term_handler_m m T_B T_R
        (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v)) : T ->
  Γ ⊢ₜ subst_list_tm
         [v; term_lam (term_handler_m m T_B T_R
                         (plug (shift_ectx_tm 1 0 P) (term_var 0))) A]
         (subst_list_ty_in_tm Ss op_body) : T.
Proof.
  intros Γ E_tag m Ts T_B T_R op_bodies op n_beta op_body Ss A v P T
         Hec Hval HpureP Hnth Hty.
  (* (a) inversions *)
  apply handler_m_typing_inv in Hty.
  destruct Hty as [Hplug [HTBR [HnlTB HTRT]]].
  destruct (plug_typing_inv P Γ _ _ Hplug) as [Tu Hperf].
  apply perform_typing_inv in Hperf.
  destruct Hperf as
    [E_t0 [Δ0 [Ts0 [n_α [ops [n_β [sig [ret [sig_inst
      [Hrecv [Heff0 [Hnth_ops [HlenTs0 [HlenSs [HwfSs [HnlSs [Hsi [Hnlsi
        [Hri [HwfRi [Harg HsubTu]]]]]]]]]]]]]]]]]]]]].
  apply cap_typing_inv in Hrecv.
  destruct Hrecv as
    [n_α' [ops' [Heff' [HlenTs [HwfTs [HwfTR [Hfst [HopsF2 HsubRecv]]]]]]]].
  (* reconcile tags & effect lookups (in eval_ctx Γ) *)
  assert (HEt0 : E_t0 <> any_tag).
  { intros Heq; subst E_t0. rewrite (eval_ctx_no_eff_any _ Hec) in Heff0; discriminate. }
  destruct (sub_ctor_inv Γ (type_ctor E_tag lt_local Ts) E_t0 Δ0 Ts0 Hec HsubRecv HEt0)
    as [l' [Heqctor Hl']].
  injection Heqctor as HEtag Hl'' HTs. subst E_t0. subst Ts0.
  assert (Hee : n_α' = n_α /\ ops' = ops).
  { rewrite Heff' in Heff0. injection Heff0; intros; subst; split; reflexivity. }
  destruct Hee as (Hna & Hopseq). subst ops'.
  (* select the FIRED clause's typing via typing_ops at the step's index *)
  destruct (typing_ops_nth_error _ _ _ _ _ _ _ _ HopsF2 Hnth)
    as [osig [Hnth_sel Hop]].
  rewrite Hnth_ops in Hnth_sel.
  injection Hnth_sel; intros Hosig; subst osig.
  unfold op_nb, op_sig_ty, op_ret_ty in Hop. simpl in Hop.
  rewrite Hna in Hop.
  set (sig_β := inst_op_ty_args n_α Ts n_β sig) in *.
  set (ret_β := inst_op_ty_args n_α Ts n_β ret) in *.
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
       [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)])
       ⊢ₜ op_body : shift_ty n_β 0 T_R).
  { cbn [List.fold_right]. rewrite HlenSs. exact Hop. }
  pose proof (typing_peel_push_ty_vars_fold Ss
    [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)]
    op_body (shift_ty n_β 0 T_R) Γ HallSub
    (eval_ctx_ctor_fields_closed Γ Hec) Hpremise) as Hpeel.
  (* operation-signature reconciliations *)
  assert (Hsigeq : subst_list_ty Ss sig_β = sig_inst).
  { unfold sig_β. rewrite (subst_list_ty_inst_op_ty_args n_α Ts n_β Ss sig HlenSs).
    symmetry; exact Hsi. }
  assert (HTReq : subst_list_ty Ss (shift_ty n_β 0 T_R) = T_R).
  { rewrite <- HlenSs. apply subst_list_ty_shift_cancel. }
  assert (Hrhokeq : subst_list_ty Ss (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
                    = type_fun A lt_local T_R).
  { rewrite subst_list_ty_fun. rewrite HTReq.
    unfold ret_β. rewrite (subst_list_ty_inst_op_ty_args n_α Ts n_β Ss ret HlenSs).
    rewrite <- Hri. reflexivity. }
  cbn [List.map List.fold_right] in Hpeel.
  rewrite Hsigeq, Hrhokeq, HTReq in Hpeel.
  (* (c) type the resumption lambda: T_Lam over T_HandlerM.  The T_Lam
     capture obligation is trivial — the body carries a literal
     handler_m, so capture_lt is lt_local. *)
  assert (Hresume : Γ ⊢ₜ term_lam (term_handler_m m T_B T_R
                          (plug (shift_ectx_tm 1 0 P) (term_var 0))) A
                        : type_fun A lt_local T_R).
  { apply T_Lam.
    - exact HwfRi.
    - exact HwfTR.
    - apply T_HandlerM.
      + eapply ty_wf_InsTm;
          [eapply typing_implies_wf; exact Hplug | apply InsTm_here].
      + eapply ty_wf_InsTm; [exact HwfTR | apply InsTm_here].
      + eapply sub_free_InsTm; [apply InsTm_here | exact HnlTB].
      + eapply sub_InsTm; [exact HTBR | apply InsTm_here].
      + eapply perform_resume_body; [exact Hec | exact HwfRi | exact Hplug].
    - unfold capture_lt. simpl. apply LS_Refl. apply LWF_Local. }
  (* (d) substitute the two term arguments *)
  eapply T_Sub; [|exact HTRT].
  eapply (typing_subst_list_tm_eval_ctx_global Γ
    [v; term_lam (term_handler_m m T_B T_R
                    (plug (shift_ectx_tm 1 0 P) (term_var 0))) A]
    [sig_inst; type_fun A lt_local T_R]
    (subst_list_ty_in_tm Ss op_body) T_R Hec).
  - constructor; [exact Harg | constructor; [exact Hresume | constructor]].
  - constructor; [exact Hval | constructor; [apply value_lam | constructor]].
  - cbn [List.map List.concat].
    rewrite (typing_closed _ _ _ Hec Harg).
    rewrite (typing_closed _ _ _ Hec Hresume). reflexivity.
  - cbn [List.fold_right]. exact Hpeel.
Qed.

(* ================================================================== *)
(* Step preservation of the fused runtime invariant ws_rt (marker     *)
(* provenance + cap-body term-closedness) — discharges the            *)
(* well-scopedness hypothesis of type_soundness.  One lemma per       *)
(* level; each case threads both conjuncts through the fused          *)
(* traversal laws of WsRtLaws.v.                                      *)
(* ================================================================== *)

(* The H_Perform case: the op-body confinement comes straight from    *)
(* the well_scoped cap clause; the perform argument is rt-free by the *)
(* typing-side escape lemma; the reified resume is well-scoped        *)
(* because the captured frames were, one delimiter up, and rt-closed  *)
(* by reified_continuation_closed_rt.                                 *)
Lemma ws_rt_step_handler_elim :
  forall Γ m T_B T_R E_tag Ts op_bodies op n_beta op_body Ss A v P Tr ms,
  eval_ctx Γ ->
  value v ->
  pure_ectx_m m P ->
  nth_error op_bodies op = Some (n_beta, op_body) ->
  Γ ⊢ₜ term_handler_m m T_B T_R
        (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v)) : Tr ->
  free_tm_vars 0 (term_handler_m m T_B T_R
        (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v))) = [] ->
  ws_rt ms (term_handler_m m T_B T_R
        (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v))) ->
  ws_rt ms
    (subst_list_tm
       [v; term_lam (term_handler_m m T_B T_R
                       (plug (shift_ectx_tm 1 0 P) (term_var 0))) A]
       (subst_list_ty_in_tm Ss op_body)).
Proof.
  intros Γ m T_B T_R E_tag Ts op_bodies op n_beta op_body Ss A v P Tr ms
         Hec Hval Hpure Hnth Hty Hfv [Hws Hrt].
  simpl in Hfv. simpl in Hrt.
  pose proof (well_scoped_step_handler_confinement
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hws Hpure Hnth)
    as Hopconf.
  assert (Hvcap : has_rt_cap v = false).
  { apply handler_m_typing_inv in Hty.
    destruct Hty as [Hplug [HTBR [HnlTB HTRT]]].
    destruct (plug_typing_inv P Γ _ _ Hplug) as [Tu Hperf].
    apply perform_typing_inv in Hperf.
    destruct Hperf as
      [E_t0 [Δ0 [Ts0 [n_α [ops0 [n_β0 [sig [ret [sig_inst
        [Hrecv [Heff0 [Hnth0 [HlenTs0 [HlenSs [HwfSs [HnlSs [Hsi [Hnlsi
          [Hri [HwfRi [Harg HsubTu]]]]]]]]]]]]]]]]]]]]].
    eapply value_no_local_no_rt_cap;
      [ exact Hec | exact Harg | exact Hval
      | eapply typing_closed; [exact Hec | exact Harg] | exact Hnlsi ]. }
  pose proof (free_tm_vars_plug_nil_inv P _ Hfv) as Hfvred.
  simpl in Hfvred. apply app_eq_nil in Hfvred as [Hfvcap Hfvv].
  pose proof (rt_closed_plug_inv P _ Hrt) as Hrtred.
  destruct Hrtred as [Hcapc Hrtv].
  destruct (ops_cap_closed_nth _ _ _ _ Hcapc Hnth) as [Hfv2op Hrtop].
  destruct (reified_continuation_closed_rt P _ Hfv Hrt) as [Hfvb Hrtb].
  assert (Hplugvar : ws_rt (m :: ms) (plug P (term_var 0))).
  { apply (ws_rt_plug_replace P
      (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v)).
    - split; [exact Hws | exact Hrt].
    - intros ms' _. split; exact I. }
  apply ws_rt_subst_list_tm.
  - apply Forall_cons; [exact Hfvv|].
    apply Forall_cons; [|apply Forall_nil].
    simpl. exact Hfvb.
  - apply Forall_cons.
    + apply ws_rt_no_rt_cap. exact Hvcap.
    + apply Forall_cons; [|apply Forall_nil].
      split.
      * change (well_scoped (m :: ms) (plug (shift_ectx_tm 1 0 P) (term_var 0))).
        apply well_scoped_plug_shift_ectx_tm.
        exact (proj1 Hplugvar).
      * exact Hrtb.
  - apply ws_rt_subst_list_ty_in_tm. split; [exact Hopconf | exact Hrtop].
Qed.

Lemma head_step_preserves_ws_rt : forall Γ r r' Tr,
  eval_ctx Γ ->
  Γ ⊢ₜ r : Tr ->
  free_tm_vars 0 r = [] ->
  r -->h r' ->
  forall ms, ws_rt ms r -> ws_rt ms r'.
Proof.
  intros Γ r r' Tr Hec Hty Hfv Hstep ms Hws. inversion Hstep; subst.
  - (* H_Beta *)
    simpl in Hfv. apply app_eq_nil in Hfv as [_ Hfvv].
    destruct Hws as [[Hwb Hwv] [Hrb Hrv]].
    apply ws_rt_subst_tm;
      [split; assumption | exact Hfvv | split; assumption].
  - (* H_TyBeta *)
    apply ws_rt_subst_ty_in_tm. exact Hws.
  - (* H_LtBeta *)
    apply ws_rt_subst_lt_in_tm. exact Hws.
  - (* H_MatchYes *)
    simpl in Hfv. apply app_eq_nil in Hfv as [Hfc _].
    destruct Hws as [[Hwc [Hwy _]] [Hrc [Hry _]]].
    rewrite well_scoped_ctor_eq in Hwc. rewrite rt_closed_ctor_eq in Hrc.
    apply ws_rt_subst_list_tm.
    + apply Forall_of_concat_map_nil. exact Hfc.
    + apply ws_rt_list_Forall; assumption.
    + apply ws_rt_subst_list_lt_in_tm. split; assumption.
  - (* H_MatchNo *)
    destruct Hws as [[_ [_ Hwn]] [_ [_ Hrn]]]. split; assumption.
  - (* H_Return *)
    destruct (handler_m_typing_inv _ _ _ _ _ _ Hty) as [Hbody [_ [Hnl _]]].
    pose proof (typing_closed _ _ _ Hec Hty) as Hcl. simpl in Hcl.
    apply ws_rt_no_rt_cap.
    eapply value_no_local_no_rt_cap;
      [ exact Hec | exact Hbody | assumption | exact Hcl | exact Hnl ].
  - (* H_Perform *)
    eapply ws_rt_step_handler_elim;
      [ exact Hec | eassumption | eassumption | eassumption
      | exact Hty | exact Hfv | exact Hws ].
Qed.

(* The fused runtime invariant is preserved by one step. *)
Theorem step_preserves_ws_rt : forall Γ t t' T,
  eval_ctx Γ -> Γ ⊢ₜ t : T -> ws_rt [] t -> t ==> t' -> ws_rt [] t'.
Proof.
  intros Γ t t' T Hec Hty Hwsrt Hstep.
  inversion Hstep as
    [E r r' Hwf Hhead Heq1 Heq2
    | E E_tag Ts T_B T_R op_bodies body m Hwf Hfresh Heq1 Heq2]; subst.
  - (* S_step *)
    pose proof (typing_closed _ _ _ Hec Hty) as Hcl.
    pose proof (free_tm_vars_plug_nil_inv E r Hcl) as Hfvr.
    destruct (plug_typing_inv E Γ r T Hty) as [Tr Hr].
    eapply ws_rt_plug_replace; [exact Hwsrt|].
    intros ms' Hwsr.
    eapply head_step_preserves_ws_rt; eauto.
  - (* S_HandleCtx *)
    pose proof (typing_closed _ _ _ Hec Hty) as Hcl.
    pose proof (free_tm_vars_plug_nil_inv E _ Hcl) as Hfvh.
    simpl in Hfvh.
    rewrite free_tm_vars_ops_eq_concat in Hfvh.
    apply app_eq_nil in Hfvh as [Hfop Hfb].
    eapply ws_rt_plug_replace; [exact Hwsrt|].
    intros ms' [[Hwop Hwb] [Hrop Hrb]].
    change (ws_rt (m :: ms') (subst_tm 0 (term_cap E_tag m Ts T_R op_bodies) body)).
    apply ws_rt_subst_tm.
    + split; [apply (well_scoped_mono body ms' (m :: ms'));
              [apply se_top; apply se_refl | exact Hwb] | exact Hrb].
    + simpl. rewrite free_tm_vars_ops_eq_concat. exact Hfop.
    + split.
      * split; [left; reflexivity|].
        rewrite scope_below_cons_eq. exact Hwop.
      * apply ops_cap_closed_join;
          [apply Forall_of_concat_map_nil; exact Hfop | exact Hrop].
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
Qed.


(* Allocating a fresh handler delimiter preserves typing. *)
Lemma handle_step_preserves_typing :
  forall Γ E_tag Ts T_B T_R op_bodies body m T,
  eval_ctx Γ ->
  Γ ⊢ₜ term_handle E_tag Ts T_B T_R op_bodies body : T ->
  Γ ⊢ₜ term_handler_m m T_B T_R
        (subst_tm 0 (term_cap E_tag m Ts T_R op_bodies) body) : T.
Proof.
  intros Γ E_tag Ts T_B T_R op_bodies body m T Hec Hty.
  apply handle_typing_inv in Hty.
  destruct Hty as
    (n_α & ops & Heff & HlenTs & HwfTs & HwfTB & HwfTR
     & Hnl & Hbr & Hfst & Hops & Hbody & Hsub).
  assert (Hcap : Γ ⊢ₜ term_cap E_tag m Ts T_R op_bodies
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
  inversion Hstep as [E r r' Hwf Hhead Heq1 Heq2 | E E_tag Ts T_B T_R op_bodies body m Hwf Hfresh Heq1 Heq2]; subst.
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
