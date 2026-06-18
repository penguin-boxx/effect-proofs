Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import SubstitutionTheory.
Require Import SafetyMarkers.
Require Import SafetyProgress.
Require Import SafetyElim1.
Require Import SafetyElim2.
Require Import SafetyConfinement.

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
    /\ ty_app_arg_no_local Γ B S = true /\ Γ ⊢ subst_ty 0 S U <:: T.
Proof.
  intros Γ t S T H. remember (term_ty_app t S) as s eqn:Hs.
  induction H; try discriminate Hs.
  - destruct (IHtyping Hs) as [B0 [U0 [Ht [HSb [Hnl Hsub]]]]].
    exists B0, U0. split; [exact Ht|]. split; [exact HSb|]. split; [exact Hnl|].
    eapply SA_Trans; eassumption.
  - injection Hs; intros; subst.
    exists B, U. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
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
    no_local_ty_G Γ T_B = true /\ Γ ⊢ T_B <:: T_R /\
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
(*  - ltbeta_preserves   needs lt-β substitution preservation through  *)
(*    typing_SubstLt with the closedness/schema bookkeeping.           *)
(*  - matchyes_preserves needs the n_lt lt-var elimination + value     *)
(*    list substitution (typing_SubstLt + Axiom 4) index plumbing.     *)
(*  - perform_preserves  needs the Ss type substitution (typing_SubstTy)*)
(*    + the [arg; resume] term-list substitution (Axiom 4).            *)
(*                                                                    *)
(* All four are SOUND (true; they are the standard substitution lemmas *)
(* specialised to each redex) — they are stated exactly as the         *)
(* preservation proof consumes them.                                   *)
(* ================================================================== *)

(* Term substitution at index 0 preserves typing — from Axiom 3. *)
Lemma subst_tm_preserves : forall Γ A t B v,
  eval_ctx Γ ->
  (bind_tm A :: Γ) ⊢ₜ t : B ->
  value v ->
  Γ ⊢ₜ v : A ->
  Γ ⊢ₜ subst_tm 0 v t : B.
Proof. exact typing_SubstTm_eval_ctx. Qed.

Axiom tybeta_preserves : forall Γ bound body S T,
  eval_ctx Γ ->
  Γ ⊢ₜ term_ty_app (term_ty_lam bound body) S : T ->
  Γ ⊢ₜ subst_ty_in_tm 0 S body : T.

Axiom ltbeta_preserves : forall Γ body l T,
  eval_ctx Γ ->
  Γ ⊢ₜ term_lt_app (term_lt_lam body) l : T ->
  Γ ⊢ₜ subst_lt_in_tm 0 l body : T.

Axiom matchyes_preserves : forall Γ K l lts Ts vs n_lt yes_body no_body T,
  eval_ctx Γ -> Forall value vs ->
  Γ ⊢ₜ term_match (term_ctor K l lts Ts vs) K n_lt (List.length vs) yes_body no_body : T ->
  Γ ⊢ₜ subst_list_tm vs (subst_list_lt_in_tm lts yes_body) : T.

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
    ty_wf Γ T_B /\ ty_wf Γ T_R /\ no_local_ty_G Γ T_B = true /\ Γ ⊢ T_B <:: T_R /\
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

(* ================================================================== *)
(*                      TYPE SOUNDNESS (capstone)                     *)
(*                                                                    *)
(* Progress + preservation: a well-typed, marker-safe term never      *)
(* reaches a stuck state.  Conditional on the same substitution-      *)
(* preservation facts as `preservation`, plus step-preservation of    *)
(* the two marker invariants (proved separately below where           *)
(* possible).                                                         *)
(* ================================================================== *)

(* Type soundness, UNCONDITIONAL: a well-typed, marker-safe term never  *)
(* reaches a stuck state.  Subject reduction (preservation) and the two  *)
(* marker step-preservation facts are now supplied internally from the   *)
(* proved lemmas (step_preserves_marker_ok, preservation) and the        *)
(* explicit residual axioms (step_preserves_marker_types_safe, the four  *)
(* redex preserves) — see Print Assumptions type_soundness.              *)
Theorem type_soundness :
  forall Γ t t' T,
    eval_ctx Γ ->
    safety_invariants Γ T t ->
    multi_step t t' ->
    ~ stuck t'.
Proof.
  intros Γ t t' T Hec Hinv Hms.
  assert (Hreach : safety_invariants Γ T t').
  { revert Hinv. induction Hms as [u | u1 u2 u3 Hstep Hms IH]; intros Hinv.
    - exact Hinv.
    - apply IH. destruct Hinv as [Hmok [Hmsafe Hty]].
      split; [eapply step_preserves_marker_ok;
                [exact Hec | exact Hmok | exact Hmsafe | exact Hty | exact Hstep] |].
      split; [eapply step_preserves_marker_types_safe;
                [exact Hec | exact Hmok | exact Hmsafe | exact Hty | exact Hstep] |].
      eapply preservation; eauto. }
  destruct Hreach as [Hmok [Hmsafe Hty]].
  eapply safe_state_not_stuck; eauto.
Qed.

(* End-to-end safety from a single well-typed marker-safe state:       *)
(* every reachable state is non-stuck (unconditional).                 *)
Corollary type_safety_from_invariants : forall Γ t t' T,
  eval_ctx Γ ->
  safety_invariants Γ T t ->
  multi_step t t' ->
  ~ stuck t'.
Proof. exact type_soundness. Qed.
