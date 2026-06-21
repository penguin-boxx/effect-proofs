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
(* The substitution-preservation facts are abstracted as section      *)
(* hypotheses: they are the residual obligations whose proofs require  *)
(* the closed/eval_ctx substitution metatheory (see typing_SubstTm    *)
(* discussion). Everything else is discharged here.                   *)
(* ================================================================== *)

(* ================================================================== *)
(* Redex-level substitution preservation.                             *)
(*                                                                    *)
(* subst_tm_preserves is discharged directly from the integrated      *)
(* eval_ctx term-substitution lemma (Axiom 3).  The remaining four are *)
(* the residual substitution-metatheory obligations, kept as explicit *)
(* top-level Axioms (per the "all assumptions explicit" directive):    *)
(*                                                                    *)
(*  - tybeta_preserves   needs typing-level F<: NARROWING (narrow a    *)
(*    bind_ty bound to a subtype under a typing derivation).  Only     *)
(*    SUBTYPING narrowing (sub_NT) exists in the codebase; the typing  *)
(*    analogue is a separate mutual-induction theorem (future work).   *)
(*  - ltbeta_preserves   NOW PROVEN (was Axiom).  See below: the       *)
(*    general [typing_SubstLt] (no closed-from premise) is now provable *)
(*    because T_Match was reformulated to push [push_corr] (the         *)
(*    SubstLt-/InsLt-STABLE realisation of the paper's "l'_i <: Delta") *)
(*    instead of the unstable [push_lt_vars]; [SubstLt_here] at index 0 *)
(*    then discharges lifetime-beta directly.                          *)
(*                                                                     *)
(*    ROOT-CAUSE FIX (the reformulation).  T_Match used to push         *)
(*    [push_lt_vars n_lt Delta Γ] — n_lt binders all storing the SINGLE *)
(*    literal outer bound Delta, with [ctx_lookup_lt] re-shifting per   *)
(*    depth.  That is NOT stable under lt-substitution/insertion: those *)
(*    rewrite the stored bound with a per-level-increasing index, so    *)
(*    the n_lt bounds stop coinciding unless Delta is lt-closed.  The   *)
(*    fix pushes [push_corr n_lt Delta Γ] instead, which stores         *)
(*    [shift_lt j 0 Delta] at level j (uniform effective bound          *)
(*    [shift_lt n_lt 0 Delta], the de-Bruijn-correct lifting of the one *)
(*    outer Delta), and IS stable (the per-level shifts commute with    *)
(*    subst/shift via [shift_lt_subst_lt_comm_many0] /                  *)
(*    [shift_lt_lift_many_swap]; see [SubstLt_push_corr],               *)
(*    [InsLt_push_corr]).  push_corr was already the structure the elim *)
(*    soundness used ([elim_in_ctx_sound]); for lt-closed Delta the two *)
(*    coincide, so the examples are unaffected.  This unblocked the     *)
(*    GENERAL [typing_SubstLt] AND [typing_InsLt] (both now proven).    *)
(*                                                                     *)
(*  - typing_SubstTm_eval_ctx   NOW PROVEN (was Axiom; see EvalCtx.v).   *)
(*    The term-substitution lemma [typing_SubstTm] was re-proven to      *)
(*    thread [SubstTm_replacement_typed] as a PER-NODE invariant         *)
(*    (re-established at each binder by weakening — the bind_lt case via *)
(*    the now-proven [typing_InsLt]) instead of the UNSOUND universal    *)
(*    HrepAll (which fails at bind_ctor/bind_eff, where ctx_lookup_ctor  *)
(*    front-shadows).  The base instance is just [Γ ⊢ v : A].            *)
(*                                                                     *)
(*  - matchyes_preserves   NOW PROVEN (was Axiom).  Substitute the       *)
(*    constructor's lifetimes [lts] (peeling the match push_corr block,   *)
(*    [typing_peel_push_corr_fold]) then its field values [vs]            *)
(*    ([typing_subst_list_tm_eval_ctx_global]).  The peeled field types   *)
(*    [subst_list_lt lts (inst_ctor_type_open …)] equal the              *)
(*    constructor's [inst_ctor_type … lts] because the lts are lt-closed  *)
(*    in an eval_ctx (the [subst_list_lt = multi_subst] bridge —          *)
(*    [subst_list_lt_in_ty_inst_ctor_type_open], SubstTm.v).  The branch  *)
(*    result type is reconciled with [T] by [elim_ty_n_sound_pos].        *)
(*                                                                     *)
(*  - perform_preserves   remains an Axiom, but is UNBLOCKED (every tool  *)
(*    is proven).  Remaining assembly: (a) a push_ty_vars TYPE peel       *)
(*    (iterated [typing_SubstTy], subst_nl is vacuous now) substituting   *)
(*    the operation's type-args [Ss] into [op_body]; (b) reconcile        *)
(*    [inst_op_alpha … [Ss]] with [inst_op_arg] (= sig_inst/ret_inst);    *)
(*    (c) type the reified resumption [plug (shift P) (var 0)] via        *)
(*    weakening + [shift_tm_plug] + [plug_typing_replace] (with the       *)
(*    perform's principal type [ret_inst] unchanged under term-shift,     *)
(*    by eff-lookup determinism); (d) the term-list subst                 *)
(*    [typing_subst_list_tm_eval_ctx_global].  No structural blocker.     *)
(* ================================================================== *)

(* Term substitution at index 0 preserves typing — now from the PROVEN *)
(* [typing_SubstTm_eval_ctx] (no longer an axiom).                      *)
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

(* PROVEN (was Axiom): with the paper's escape side condition               *)
(* [lt_of_ty_G Γ T_B <: lt_free] — which is monotone under type substitution *)
(* (see [sub_free_SubstTy]) — type-beta preservation follows directly from    *)
(* [typing_SubstTy].  The old structural [no_local_ty_G] side condition was   *)
(* NOT substitution-monotone, which is exactly what the counterexample in     *)
(* CounterexampleTyBetaHandle.v exploited.                                     *)
Lemma tybeta_preserves : forall Γ bound body S T,
  eval_ctx Γ ->
  Γ ⊢ₜ term_ty_app (term_ty_lam bound body) S : T ->
  Γ ⊢ₜ subst_ty_in_tm 0 S body : T.
Proof.
  intros Γ bound body S T Hec Hty.
  eapply tybeta_preserves_with_subst_nl; [exact Hec | exact I | exact Hty].
Qed.

(* PROVEN (was Axiom): the general binder-removing [typing_SubstLt]    *)
(* (now provable because T_Match pushes the SubstLt-stable [push_corr]) *)
(* discharges lifetime-beta directly, via [SubstLt_here] at index 0.    *)
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
(* (peeling the match's push_corr block, typing_peel_push_corr_fold)     *)
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
  (* peel the push_corr block by substituting lts. *)
  assert (Hyes' :
    (List.fold_right (fun rho G => bind_tm rho :: G)
      (push_corr (List.length lts) Delta Γ)
      (List.map (inst_ctor_type_open n_lt n_ty Ts) sigma_fields))
      ⊢ₜ yes_body : eta).
  { rewrite Hltlen. exact Hyes. }
  pose proof (typing_peel_push_corr_fold lts Delta
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
  assert (HwfEta : ty_wf (push_corr n_lt Delta Γ) eta).
  { apply (ty_wf_fold_bind_tm_inv (List.map (inst_ctor_type_open n_lt n_ty Ts) sigma_fields)).
    eapply typing_implies_wf. exact Hyes. }
  pose proof (elim_ty_n_sound_pos n_lt Delta lts eta elim_result Γ
    Helim Hltlen HwfDelta HwfEta HboundedD) as HetaSub.
  eapply T_Sub; [exact Hsubst|].
  destruct HsubOr as [Heq | Hsub]; [subst elim_result; exact HetaSub|].
  eapply SA_Trans; [exact HetaSub | exact Hsub].
Qed.

Axiom perform_preserves :
  forall Γ E_tag m n_beta Ts T_B T_R op_body Ss v P T,
  eval_ctx Γ -> value v -> pure_ectx_m m P ->
  Γ ⊢ₜ term_handler_m m T_B T_R
        (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v)) : T ->
  Γ ⊢ₜ subst_list_tm
         [v; term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))]
         (subst_list_ty_in_tm Ss op_body) : T.

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
    sig_β = inst_op_alpha n_α Ts n_beta sig /\
    ret_β = inst_op_alpha n_α Ts n_beta ret /\
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
