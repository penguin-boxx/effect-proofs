Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import SubstitutionTheory.
Require Import Safety.

(* Recompose marker_ok through an evaluation context: replacing the hole
   contents by anything that is marker_ok in every marker scope preserves
   marker_ok of the whole plug.  The handler frame extends the scope by m,
   which the uniform (forall ms') replacement condition absorbs. *)
Lemma marker_ok_plug_replace : forall E r r' ms,
  marker_ok ms (plug E r) ->
  (forall ms', marker_ok ms' r -> marker_ok ms' r') ->
  marker_ok ms (plug E r').
Proof.
  induction E as
    [ | E1 IHE ta | ta E1 IHE | E1 IHE Ty | E1 IHE lt
    | tag dl lts Tys vs E1 IHE ts | E1 IHE K nlt ar yes no
    | mk TB TR E1 IHE | E1 IHE Ss ar2 | rcv Ss E1 IHE ];
    intros r r' ms Hok Hrep; cbn [plug] in Hok |- *.
  - apply Hrep. exact Hok.
  - destruct Hok as [H1 H2]. split; [eapply IHE; eauto | exact H2].
  - destruct Hok as [H1 H2]. split; [exact H1 | eapply IHE; eauto].
  - eapply IHE; eauto.
  - eapply IHE; eauto.
  - (* EC_ctor: focus inside the arg list *)
    rewrite marker_ok_ctor_eq in Hok |- *.
    induction vs as [|a vs' IHvs]; cbn [List.app] in Hok |- *.
    + destruct Hok as [Hfoc Hrest]. split; [eapply IHE; eauto | exact Hrest].
    + destruct Hok as [Ha Hrest]. split; [exact Ha | apply IHvs; exact Hrest].
  - destruct Hok as [Hs [Hy Hn]]. repeat split; [eapply IHE; eauto | exact Hy | exact Hn].
  - eapply IHE; eauto.
  - destruct Hok as [H1 H2]. split; [eapply IHE; eauto | exact H2].
  - destruct Hok as [H1 H2]. split; [exact H1 | eapply IHE; eauto].
Qed.

Lemma marker_ok_ctor_args_forall : forall ms K l lts Ts vs,
  marker_ok ms (term_ctor K l lts Ts vs) -> Forall (marker_ok ms) vs.
Proof.
  intros ms K l lts Ts vs H. rewrite marker_ok_ctor_eq in H.
  induction vs as [|v vs IH]; constructor.
  - destruct H as [Hv _]. exact Hv.
  - apply IH. destruct H as [_ Hrest]. exact Hrest.
Qed.

(* Head reduction preserves marker_ok uniformly in the scope — EXCEPT the
   two handler-elimination rules (H_Return, H_Perform), where the deleted
   delimiter m would have to be shown absent from the result, which needs
   the typing/capability-confinement invariant rather than a structural
   argument. *)
Lemma head_step_marker_ok_struct : forall r r',
  r -->h r' ->
  forall ms, marker_ok ms r -> marker_ok ms r'.
Proof.
  intros r r' Hstep ms Hok. inversion Hstep; subst.
  - (* H_Beta *)
    destruct Hok as [Hbody Hv].
    apply marker_ok_subst_tm; [exact Hv | exact Hbody].
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
  - (* H_Return: needs confinement (m absent from returned value) *)
    admit.
  - (* H_Perform: needs confinement / resume-marker reasoning *)
    admit.
  - (* H_Resume *)
    destruct Hok as [Hres Hv].
    apply marker_ok_subst_tm.
    + eapply marker_ok_mono; [apply incl_tl; apply incl_refl | exact Hv].
    + exact Hres.
Admitted.
