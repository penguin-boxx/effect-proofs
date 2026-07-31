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
(* Frames: evaluation-context typing recomposition (congruence).      *)
(*                                                                    *)
(* If `plug P u : T` and `u'` can be typed at every type `u` can,     *)
(* then `plug P u' : T`.  Proved frame-by-frame; each frame lemma     *)
(* inducts on the typing derivation to thread the outer type through  *)
(* subsumption.                                                       *)
(* ================================================================== *)

(* The shared skeleton of every frame lemma: remember the frame,
   induct on its typing derivation, discharge the T_Sub case by the
   IH, and expose the frame's own introduction rule (injected and
   substituted).  Each lemma below finishes with just that rule. *)
Ltac frame_replace H Himpl :=
  lazymatch type of H with
  | typing _ ?s _ =>
      let s0 := fresh "s0" in let Hs := fresh "Hs" in
      remember s as s0 eqn:Hs; revert Hs;
      induction H; intros Hs; try discriminate Hs;
      [ eapply T_Sub;
        [ match goal with IH : _ -> _ = _ -> _ |- _ =>
            apply IH; [exact Himpl | exact Hs] end
        | assumption ]
      | injection Hs; intros; subst ]
  end.

Lemma app1_replace : forall Γ f f' t2 T,
  Γ ⊢ₜ term_app f t2 : T ->
  (forall Tf, Γ ⊢ₜ f : Tf -> Γ ⊢ₜ f' : Tf) ->
  Γ ⊢ₜ term_app f' t2 : T.
Proof.
  intros Γ f f' t2 T H Himpl. frame_replace H Himpl.
  eapply T_App; [apply Himpl; eassumption | eassumption].
Qed.

Lemma app2_replace : forall Γ t1 u u' T,
  Γ ⊢ₜ term_app t1 u : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_app t1 u' : T.
Proof.
  intros Γ t1 u u' T H Himpl. frame_replace H Himpl.
  eapply T_App; [eassumption | apply Himpl; eassumption].
Qed.

Lemma ty_app_replace : forall Γ u u' S T,
  Γ ⊢ₜ term_ty_app u S : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_ty_app u' S : T.
Proof.
  intros Γ u u' S T H Himpl. frame_replace H Himpl.
  eapply T_TyApp; [apply Himpl; eassumption | assumption | assumption].
Qed.

Lemma lt_app_replace : forall Γ u u' l T,
  Γ ⊢ₜ term_lt_app u l : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_lt_app u' l : T.
Proof.
  intros Γ u u' l T H Himpl. frame_replace H Himpl.
  eapply T_LtApp; [apply Himpl; eassumption | assumption].
Qed.

Lemma match_scrut_replace : forall Γ u u' K nlt ar y n T,
  Γ ⊢ₜ term_match u K nlt ar y n : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_match u' K nlt ar y n : T.
Proof.
  intros Γ u u' K nlt ar y n T H Himpl. frame_replace H Himpl.
  eapply T_Match;
      try (apply Himpl; eassumption); try eassumption; try reflexivity.
Qed.

Lemma handler_m_replace : forall Γ m T_B T_R u u' T,
  Γ ⊢ₜ term_handler_m m T_B T_R u : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_handler_m m T_B T_R u' : T.
Proof.
  intros Γ m T_B T_R u u' T H Himpl. frame_replace H Himpl.
  eapply T_HandlerM; try eassumption.
  apply Himpl; eassumption.
Qed.

Lemma perform_recv_replace : forall Γ u u' op Ss A arg T,
  Γ ⊢ₜ term_perform u op Ss A arg : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_perform u' op Ss A arg : T.
Proof.
  intros Γ u u' op Ss A arg T H Himpl. frame_replace H Himpl.
  eapply T_Perform;
      try (apply Himpl; eassumption); try eassumption; try reflexivity.
Qed.

Lemma perform_arg_replace : forall Γ recv u u' op Ss A T,
  Γ ⊢ₜ term_perform recv op Ss A u : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_perform recv op Ss A u' : T.
Proof.
  intros Γ recv u u' op Ss A T H Himpl. frame_replace H Himpl.
  eapply T_Perform;
      try (apply Himpl; eassumption); try eassumption; try reflexivity.
Qed.

Lemma ctor_focus_replace : forall Γ K l lts Ts vs u u' ts T,
  Γ ⊢ₜ term_ctor K l lts Ts (vs ++ u :: ts) : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_ctor K l lts Ts (vs ++ u' :: ts) : T.
Proof.
  intros Γ K l lts Ts vs u u' ts T H Himpl. frame_replace H Himpl.
  assert (Hlen : length (vs ++ u' :: ts) = length (vs ++ u :: ts))
      by (rewrite !length_app; reflexivity).
    eapply T_Ctor;
      try (rewrite Hlen; eassumption);
      try (eapply typings_focus_replace;
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

