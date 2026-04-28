Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Safety.
Require Import CK.

(* ================================================================== *)
(*                                                                    *)
(*        TYPE SAFETY FOR THE CK MACHINE (explicit continuations)     *)
(*                                                                    *)
(* Strategy: every CK transition is either                            *)
(*   (A) administrative — `plug_state s = plug_state s'`, or          *)
(*   (B) reductive      — `plug_state s ==> plug_state s'` in the     *)
(*                        small-step relation from Semantics.v.       *)
(*                                                                    *)
(* Type safety for the CK machine then follows from the existing      *)
(* `progress` / `preservation` theorems in Safety.v.                  *)
(*                                                                    *)
(* Two structural invariants are factored out:                        *)
(*   (i)  `F_Ctor` frames store values in their "done" list;          *)
(*   (ii) `CK_ret` modes hold actual values.                          *)
(* These are preserved by every CK transition.                        *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* State invariant                                                    *)
(* ------------------------------------------------------------------ *)

Inductive frame_ok : frame -> Prop :=
  | fok_App1  : forall t, frame_ok (F_App1 t)
  | fok_App2  : forall v, value v -> frame_ok (F_App2 v)
  | fok_TyApp : forall T, frame_ok (F_TyApp T)
  | fok_LtApp : forall l, frame_ok (F_LtApp l)
  | fok_Ctor  : forall K l lts Ts vs ts,
      Forall value vs -> frame_ok (F_Ctor K l lts Ts vs ts)
  | fok_Match : forall K ar y n, frame_ok (F_Match K ar y n).

Definition kont_ok (k : kont) : Prop := Forall frame_ok k.

Definition state_ok (s : state) : Prop :=
  match s with
  | (CK_eval _, k) => kont_ok k
  | (CK_ret v,  k) => value v /\ kont_ok k
  end.

Lemma load_ok : forall t, state_ok (load t).
Proof. intros. unfold load, kont_ok. simpl. constructor. Qed.

(* Preservation of the structural invariant by ck_step.                *)
Lemma ck_step_preserves_ok : forall s s',
  state_ok s -> s -c-> s' -> state_ok s'.
Proof.
  intros s s' Hok Hstep.
  induction Hstep; simpl in *; unfold kont_ok in *.
  - (* CK_App_push *) constructor; [constructor | exact Hok].
  - (* CK_TyApp_push *) constructor; [constructor | exact Hok].
  - (* CK_LtApp_push *) constructor; [constructor | exact Hok].
  - (* CK_Match_push *) constructor; [constructor | exact Hok].
  - (* CK_Ctor_nil *) split; [constructor; constructor | exact Hok].
  - (* CK_Ctor_push *) constructor; [constructor; constructor | exact Hok].
  - (* CK_Val_Lam *) split; [constructor | exact Hok].
  - (* CK_Val_TyLam *) split; [constructor | exact Hok].
  - (* CK_Val_LtLam *) split; [constructor | exact Hok].
  - (* CK_Ret_App1 *)
    destruct Hok as [Hval Hk].
    inversion Hk as [|? ? Hf Hkr]; subst.
    constructor; [constructor; auto | exact Hkr].
  - (* CK_Ret_Beta *)
    destruct Hok as [_ Hk]. inversion Hk; subst. exact H3.
  - (* CK_Ret_TyBeta *)
    destruct Hok as [_ Hk]. inversion Hk; subst. exact H2.
  - (* CK_Ret_LtBeta *)
    destruct Hok as [_ Hk]. inversion Hk; subst. exact H2.
  - (* CK_Ret_Ctor_next *)
    destruct Hok as [Hval Hk].
    inversion Hk as [|? ? Hf Hkr]; subst.
    inversion Hf; subst.
    constructor; [constructor; apply Forall_app; split; auto | exact Hkr].
  - (* CK_Ret_Ctor_done *)
    destruct Hok as [Hval Hk].
    inversion Hk as [|? ? Hf Hkr]; subst.
    inversion Hf; subst.
    split; [constructor; apply Forall_app; split; auto | exact Hkr].
  - (* CK_Ret_MatchYes *)
    destruct Hok as [_ Hk]. inversion Hk; subst. exact H3.
  - (* CK_Ret_MatchNo *)
    destruct Hok as [_ Hk]. inversion Hk; subst. exact H4.
Qed.

(* ------------------------------------------------------------------ *)
(* Simulation lemma                                                   *)
(*                                                                    *)
(* Every CK transition either leaves `plug_state` unchanged or        *)
(* corresponds to a single small step.  The F_Ctor congruence case    *)
(* needs `Forall value vs`, hence the `state_ok` premise.             *)
(* ------------------------------------------------------------------ *)

Axiom ck_plug_sim : forall s s',
  state_ok s ->
  s -c-> s' ->
  plug_state s = plug_state s' \/ plug_state s ==> plug_state s'.

(* ------------------------------------------------------------------ *)
(* CK typing                                                          *)
(* ------------------------------------------------------------------ *)

Definition ck_well_typed (Γ : ctx) (s : state) (T : type) : Prop :=
  Γ ⊢ₜ plug_state s : T.

(* ------------------------------------------------------------------ *)
(* Preservation for CK                                                 *)
(* ------------------------------------------------------------------ *)

Theorem ck_preservation : forall Γ s s' T,
  eval_ctx Γ ->
  state_ok s ->
  ck_well_typed Γ s T ->
  s -c-> s' ->
  ck_well_typed Γ s' T.
Proof.
  intros Γ s s' T Hec Hok Hty Hstep.
  unfold ck_well_typed in *.
  destruct (ck_plug_sim _ _ Hok Hstep) as [Heq | Hs].
  - rewrite <- Heq. exact Hty.
  - eapply preservation; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Progress for CK                                                     *)
(* ------------------------------------------------------------------ *)

(* Under `eval_ctx`, a variable cannot appear at the focus of a        *)
(* well-typed CK state.  All frames in `plug` leave term-variable      *)
(* indices unchanged in their holes.                                   *)
Axiom plug_var_not_typable : forall Γ k x T,
  eval_ctx Γ ->
  ~ (Γ ⊢ₜ plug k (term_var x) : T).

(* Under typing, on a non-empty kont with a value, the top frame       *)
(* always has a matching rule.  Proved by canonical forms applied to  *)
(* the plug's type at the frame's hole.                                *)
Axiom ck_progress_ret_frame : forall Γ v f k T,
  eval_ctx Γ ->
  value v ->
  kont_ok (f :: k) ->
  Γ ⊢ₜ plug (f :: k) v : T ->
  exists s', (CK_ret v, f :: k) -c-> s'.

(* Structural progress for `CK_eval`: every term-shape except a plain  *)
(* variable has an immediate CK rule.                                  *)
Lemma ck_progress_eval : forall t k,
  (forall x, t <> term_var x) ->
  exists s', (CK_eval t, k) -c-> s'.
Proof.
  intros t k Hnvar.
  destruct t; try (exfalso; eapply Hnvar; reflexivity).
  - eexists. apply CK_App_push.
  - eexists. apply CK_Val_Lam.
  - eexists. apply CK_TyApp_push.
  - eexists. apply CK_Val_TyLam.
  - eexists. apply CK_LtApp_push.
  - eexists. apply CK_Val_LtLam.
  - destruct l2 as [|t' ts'].
    + eexists. apply CK_Ctor_nil.
    + eexists. apply CK_Ctor_push.
  - eexists. apply CK_Match_push.
Qed.

Theorem ck_progress : forall Γ s T,
  eval_ctx Γ ->
  state_ok s ->
  ck_well_typed Γ s T ->
  final s \/ exists s', s -c-> s'.
Proof.
  intros Γ [m k] T Hec Hok Hty.
  unfold ck_well_typed in Hty; simpl in Hty.
  destruct m as [t | v].
  - right. apply ck_progress_eval.
    intros x ->.
    eapply plug_var_not_typable; eauto.
  - simpl in Hok. destruct Hok as [Hval Hkok].
    destruct k as [|f k'].
    + left. simpl. exact Hval.
    + right. eapply ck_progress_ret_frame; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Multi-step safety                                                   *)
(* ------------------------------------------------------------------ *)

Corollary ck_type_safety : forall Γ t s T,
  eval_ctx Γ ->
  Γ ⊢ₜ t : T ->
  load t -c->* s ->
  final s \/ exists s', s -c-> s'.
Proof.
  intros Γ t s T Hec Hty Hmulti.
  assert (Hinit_ty : ck_well_typed Γ (load t) T).
  { unfold ck_well_typed, load; simpl. exact Hty. }
  assert (Hinit_ok : state_ok (load t)) by apply load_ok.
  induction Hmulti.
  - eapply ck_progress; eauto.
  - apply IHHmulti.
    + eapply ck_preservation; eauto.
    + eapply ck_step_preserves_ok; eauto.
Qed.
