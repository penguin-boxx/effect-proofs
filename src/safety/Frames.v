Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.

(* ================================================================== *)
(* Frames: preservation infrastructure.                               *)
(*                                                                    *)
(* Principal-type inversions for the runtime effect forms and the     *)
(* evaluation-context congruence ("frame") lemmas.                    *)
(* ================================================================== *)

(* Principal-type inversions for the runtime effect forms, in the     *)
(* style of `resume_typing_inv`: strip subsumption and recover the    *)
(* premises of the introducing rule together with the residual        *)
(* subtyping `<intro type> <:: T`.                                    *)

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

Lemma cap_typing_inv : forall Γ E_tag m n_β Ts T_R op_body T,
  Γ ⊢ₜ term_cap E_tag m n_β Ts T_R op_body : T ->
  exists n_α sig ret sig_β ret_β,
    ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) /\
    List.length Ts = n_α /\
    types_wf Γ Ts /\
    ty_wf Γ T_R /\
    sig_β = inst_op_ty_args n_α Ts n_β sig /\
    ret_β = inst_op_ty_args n_α Ts n_β ret /\
    (bind_tm sig_β
      :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
      :: push_ty_vars n_β any_at_free Γ)
      ⊢ₜ op_body : shift_ty n_β 0 T_R /\
    Γ ⊢ type_ctor E_tag lt_local Ts <:: T.
Proof.
  intros Γ E_tag m n_β Ts T_R op_body T H.
  remember (term_cap E_tag m n_β Ts T_R op_body) as s eqn:Hs.
  induction H; try discriminate Hs.
  - (* T_Sub *)
    destruct (IHtyping Hs) as
      [n_α [sig [ret [sig_β [ret_β [Heff [HlenTs [HwfTs [HwfTR
        [Hsigβ [Hretβ [Hop Hsub]]]]]]]]]]]].
    exists n_α, sig, ret, sig_β, ret_β.
    split; [exact Heff|]. split; [exact HlenTs|]. split; [exact HwfTs|].
    split; [exact HwfTR|]. split; [exact Hsigβ|]. split; [exact Hretβ|].
    split; [exact Hop|]. eapply SA_Trans; [exact Hsub | eassumption].
  - (* T_Cap *) injection Hs; intros; subst.
    do 5 eexists. repeat split; try eassumption; try reflexivity.
    apply SA_Refl. apply TWF_Ctor; [apply LWF_Local | assumption].
Qed.

Lemma perform_typing_inv : forall Γ recv Ss arg T,
  Γ ⊢ₜ term_perform recv Ss arg : T ->
  exists E_tag Δ Ts n_α n_β sig ret sig_inst ret_inst,
    Γ ⊢ₜ recv : type_ctor E_tag Δ Ts /\
    ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) /\
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
  intros Γ recv Ss arg T H.
  remember (term_perform recv Ss arg) as s eqn:Hs.
  induction H; try discriminate Hs.
  - (* T_Sub *)
    destruct (IHtyping Hs) as
      [E_tag [Δ [Ts [n_α [n_β [sig [ret [sig_inst [ret_inst
        [Hrecv [Heff [HlenTs [HlenSs [HwfSs [HnlSs [Hsi [Hnlsi
          [Hri [HwfRi [Harg Hsub]]]]]]]]]]]]]]]]]]]].
    exists E_tag, Δ, Ts, n_α, n_β, sig, ret, sig_inst, ret_inst.
    split; [exact Hrecv|]. split; [exact Heff|]. split; [exact HlenTs|].
    split; [exact HlenSs|]. split; [exact HwfSs|]. split; [exact HnlSs|].
    split; [exact Hsi|]. split; [exact Hnlsi|]. split; [exact Hri|].
    split; [exact HwfRi|]. split; [exact Harg|].
    eapply SA_Trans; [exact Hsub | eassumption].
  - (* T_Perform *) injection Hs; intros; subst.
    do 9 eexists. repeat split; try eassumption; try reflexivity.
    apply SA_Refl. assumption.
Qed.

(* ================================================================== *)
(* Evaluation-context typing recomposition (congruence).              *)
(*                                                                    *)
(* If `plug P u : T` and `u'` can be typed at every type `u` can,     *)
(* then `plug P u' : T`.  Proved frame-by-frame; each frame lemma     *)
(* inducts on the typing derivation to thread the outer type through  *)
(* subsumption.                                                       *)
(* ================================================================== *)

Lemma app1_replace : forall Γ f f' t2 T,
  Γ ⊢ₜ term_app f t2 : T ->
  (forall Tf, Γ ⊢ₜ f : Tf -> Γ ⊢ₜ f' : Tf) ->
  Γ ⊢ₜ term_app f' t2 : T.
Proof.
  intros Γ f f' t2 T H Himpl.
  remember (term_app f t2) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_App; [apply Himpl; eassumption | eassumption].
Qed.

Lemma app2_replace : forall Γ t1 u u' T,
  Γ ⊢ₜ term_app t1 u : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_app t1 u' : T.
Proof.
  intros Γ t1 u u' T H Himpl.
  remember (term_app t1 u) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_App; [eassumption | apply Himpl; eassumption].
Qed.

Lemma ty_app_replace : forall Γ u u' S T,
  Γ ⊢ₜ term_ty_app u S : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_ty_app u' S : T.
Proof.
  intros Γ u u' S T H Himpl.
  remember (term_ty_app u S) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_TyApp; [apply Himpl; eassumption | assumption | assumption].
Qed.

Lemma lt_app_replace : forall Γ u u' l T,
  Γ ⊢ₜ term_lt_app u l : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_lt_app u' l : T.
Proof.
  intros Γ u u' l T H Himpl.
  remember (term_lt_app u l) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_LtApp; [apply Himpl; eassumption | assumption].
Qed.

Lemma match_scrut_replace : forall Γ u u' K nlt ar y n T,
  Γ ⊢ₜ term_match u K nlt ar y n : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_match u' K nlt ar y n : T.
Proof.
  intros Γ u u' K nlt ar y n T H Himpl.
  remember (term_match u K nlt ar y n) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_Match;
      try (apply Himpl; eassumption); try eassumption; try reflexivity.
Qed.

Lemma handler_m_replace : forall Γ m T_B T_R u u' T,
  Γ ⊢ₜ term_handler_m m T_B T_R u : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_handler_m m T_B T_R u' : T.
Proof.
  intros Γ m T_B T_R u u' T H Himpl.
  remember (term_handler_m m T_B T_R u) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_HandlerM; try eassumption.
    apply Himpl; eassumption.
Qed.

Lemma perform_recv_replace : forall Γ u u' Ss arg T,
  Γ ⊢ₜ term_perform u Ss arg : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_perform u' Ss arg : T.
Proof.
  intros Γ u u' Ss arg T H Himpl.
  remember (term_perform u Ss arg) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_Perform;
      try (apply Himpl; eassumption); try eassumption; try reflexivity.
Qed.

Lemma perform_arg_replace : forall Γ recv u u' Ss T,
  Γ ⊢ₜ term_perform recv Ss u : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_perform recv Ss u' : T.
Proof.
  intros Γ recv u u' Ss T H Himpl.
  remember (term_perform recv Ss u) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_Perform;
      try (apply Himpl; eassumption); try eassumption; try reflexivity.
Qed.

Lemma Forall2_focus_replace :
  forall (R : term -> type -> Prop) vs u u' ts rhos,
  Forall2 R (vs ++ u :: ts) rhos ->
  (forall ru, R u ru -> R u' ru) ->
  Forall2 R (vs ++ u' :: ts) rhos.
Proof.
  intros R vs u u' ts rhos H Himpl.
  revert rhos H. induction vs as [|v vs IH]; intros rhos H; simpl in *.
  - inversion H; subst. constructor; [apply Himpl; assumption | assumption].
  - inversion H; subst. constructor; [assumption | apply IH; assumption].
Qed.

Lemma ctor_focus_replace : forall Γ K l lts Ts vs u u' ts T,
  Γ ⊢ₜ term_ctor K l lts Ts (vs ++ u :: ts) : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_ctor K l lts Ts (vs ++ u' :: ts) : T.
Proof.
  intros Γ K l lts Ts vs u u' ts T H Himpl.
  remember (term_ctor K l lts Ts (vs ++ u :: ts)) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    assert (Hlen : length (vs ++ u' :: ts) = length (vs ++ u :: ts))
      by (rewrite !length_app; reflexivity).
    eapply T_Ctor;
      try (rewrite Hlen; eassumption);
      try (eapply Forall2_focus_replace;
           [ eassumption | intros ru Hu; apply Himpl; exact Hu ]);
      try eassumption; try reflexivity.
Qed.

Lemma plug_typing_replace : forall P Γ u u' T,
  Γ ⊢ₜ plug P u : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ plug P u' : T.
Proof.
  induction P; intros Γ u u' T H Himpl; simpl in *.
  - apply Himpl; exact H.
  - eapply app1_replace; [exact H|]. intros Tf Hf. eapply IHP; eauto.
  - eapply app2_replace; [exact H|]. intros Tf Hf. eapply IHP; eauto.
  - eapply ty_app_replace; [exact H|]. intros Tf Hf. eapply IHP; eauto.
  - eapply lt_app_replace; [exact H|]. intros Tf Hf. eapply IHP; eauto.
  - eapply ctor_focus_replace; [exact H|]. intros Tf Hf. eapply IHP; eauto.
  - eapply match_scrut_replace; [exact H|]. intros Tf Hf. eapply IHP; eauto.
  - eapply handler_m_replace; [exact H|]. intros Tf Hf. eapply IHP; eauto.
  - eapply perform_recv_replace; [exact H|]. intros Tf Hf. eapply IHP; eauto.
  - eapply perform_arg_replace; [exact H|]. intros Tf Hf. eapply IHP; eauto.
Qed.

