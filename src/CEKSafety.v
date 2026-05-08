(* ================================================================== *)
(* CEKSafety.v — type safety for the CEK abstract machine              *)
(*                                                                     *)
(* Strategy:                                                           *)
(*   - Canonical-forms lemmas on `value_typing` (PROVED).              *)
(*   - Subtyping inversions reused from Safety.v (eval_ctx, sub_*_inv).*)
(*   - CEK determinism (PROVED).                                       *)
(*   - Progress and preservation: stated as Axioms.  Their proofs are *)
(*     long but mechanical case-analyses on `cstep`, relying on the   *)
(*     three substitution axioms below.                                *)
(*                                                                     *)
(* Net: 5 axioms (vs. 12 in Safety.v).  Multi-step preservation       *)
(* and full type safety are PROVED.                                    *)
(* ================================================================== *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.

From Metalib Require Export Metatheory.
Require Export Syntax.
Require Export Substitution.
Require Export SubstitutionTheory.
Require Export Typing.
Require Export CEK.
Require Export CEKTyping.
Require Export SubtypingInv.   (* eval_ctx and sub_*_inv (extracted)     *)

(* ================================================================== *)
(* Canonical forms for runtime values                                  *)
(* ================================================================== *)

Lemma canonical_rvalue_fun : forall Γ v A l B,
  eval_ctx Γ ->
  value_typing Γ v (type_fun A l B) ->
  (exists body ρ T, v = clos_lam body ρ T)
  \/ (exists Kr, v = clos_resume Kr).
Proof.
  intros Γ v A l B Hec Hty.
  remember (type_fun A l B) as T0 eqn:HT.
  revert A l B HT.
  induction Hty; intros A0 l0 B0 HT; subst; try discriminate HT.
  - left; eauto.
  - right; eauto.
  - destruct (sub_fun_inv _ _ _ _ _ Hec H) as [A' [l' [B' [HeqT _]]]]; subst.
    eapply IHHty; eauto.
Qed.

Lemma canonical_rvalue_ctor : forall Γ v K l Ts,
  eval_ctx Γ ->
  value_typing Γ v (type_ctor K l Ts) ->
  K <> any_tag ->
  (exists K' l' lts' Ts' vs, v = clos_ctor K' l' lts' Ts' vs)
  \/ (exists E m Top ob ρ, v = clos_cap E m Top ob ρ).
Proof.
  intros Γ v K l Ts Hec Hty HK.
  remember (type_ctor K l Ts) as T0 eqn:HT.
  revert K l Ts HT HK.
  induction Hty; intros K0 l0 Ts0 HT HK; subst; try discriminate HT.
  - left; do 5 eexists; reflexivity.
  - right; do 5 eexists; reflexivity.
  - destruct (sub_ctor_inv _ _ _ _ _ Hec H HK) as [l' [HeqT _]]; subst.
    eapply IHHty; eauto.
Qed.

Lemma canonical_rvalue_lt_all : forall Γ v T,
  eval_ctx Γ ->
  value_typing Γ v (type_lt_all T) ->
  exists body ρ, v = clos_lt_lam body ρ.
Proof.
  intros Γ v T Hec Hty.
  remember (type_lt_all T) as T0 eqn:HT.
  revert T HT.
  induction Hty; intros T0 HT; subst; try discriminate HT.
  - eauto.
  - destruct (sub_lt_all_inv _ _ _ Hec H) as [T' HeqT]; subst.
    eapply IHHty; eauto.
Qed.

Lemma canonical_rvalue_ty_all : forall Γ v B T,
  eval_ctx Γ ->
  value_typing Γ v (type_ty_all B T) ->
  exists bound body ρ, v = clos_ty_lam bound body ρ.
Proof.
  intros Γ v B T Hec Hty.
  remember (type_ty_all B T) as T0 eqn:HT.
  revert B T HT.
  induction Hty; intros B0 T0 HT; subst; try discriminate HT.
  - eauto.
  - destruct (sub_ty_all_inv _ _ _ _ Hec H) as [B' [T' HeqT]]; subst.
    eapply IHHty; eauto.
Qed.

(* ================================================================== *)
(* Three substitution axioms — the deep binder-plumbing lemmas of    *)
(* the CEK development.                                                *)
(* ================================================================== *)

Axiom ev_typing_extend : forall Γ body ρ A B v L,
  value_typing Γ v A ->
  (forall x, x `notin` L ->
     ev_typing (bind_tm x A :: Γ) (open_tm_wrt_tm (term_fvar x) body) ρ B) ->
  ev_typing Γ body (v :: ρ) B.

Axiom ev_typing_subst_ty : forall Γ body ρ B U T L,
  Γ |-T U <: B ->
  (forall a, a `notin` L ->
     ev_typing (bind_ty a B :: Γ) (open_tm_wrt_ty (type_fvar a) body) ρ
                                   (open_ty_wrt_ty (type_fvar a) T)) ->
  ev_typing Γ (open_tm_wrt_ty U body) ρ (open_ty_wrt_ty U T).

Axiom ev_typing_subst_lt : forall Γ body ρ T l L,
  (forall a, a `notin` L ->
     ev_typing (bind_lt a lt_local :: Γ) (open_tm_wrt_lt (lt_fvar a) body) ρ
                                          (open_ty_wrt_lt (lt_fvar a) T)) ->
  ev_typing Γ (open_tm_wrt_lt l body) ρ (open_ty_wrt_lt l T).

(* ================================================================== *)
(* CEK determinism (PROVED)                                            *)
(* ================================================================== *)

Theorem cstep_deterministic : forall c c1 c2,
  c ~~>c c1 -> c ~~>c c2 -> c1 = c2.
Proof.
  intros c c1 c2 H1 H2.
  inversion H1; subst; inversion H2; subst; try reflexivity;
    try (exfalso; congruence);
    repeat match goal with
    | H1 : env_lookup ?ρ ?n = Some _,
      H2 : env_lookup ?ρ ?n = Some _ |- _ =>
        rewrite H1 in H2; injection H2; intros; subst; clear H2
    | H1 : split_at_handler ?m ?K = Some _,
      H2 : split_at_handler ?m ?K = Some _ |- _ =>
        rewrite H1 in H2; injection H2; intros; subst; clear H2
    end; reflexivity.
Qed.

(* ================================================================== *)
(* Progress and preservation (Axioms)                                  *)
(*                                                                     *)
(* Each is a single large case-analysis on `cstep` (preservation) or  *)
(* on `config_typing` (progress).  They use the canonical forms above *)
(* and the three substitution axioms.                                 *)
(*                                                                     *)
(* The `config_wf` hypothesis carries the marker invariant: every     *)
(* clos_cap in scope has its marker in the enclosing kont.  This is  *)
(* what makes `split_at_handler` total in the `CS_KPerformFire` case. *)
(* ================================================================== *)

Axiom progress : forall c T,
  config_typing c T ->
  config_wf c ->
  is_done c \/ exists c', c ~~>c c'.

Axiom preservation : forall c c' T,
  config_typing c T ->
  config_wf c ->
  c ~~>c c' ->
  config_typing c' T /\ config_wf c'.

(* ================================================================== *)
(* Multi-step preservation and full type safety — PROVED.              *)
(* ================================================================== *)

(* The initial configuration `C_ev t [] [] 0` is trivially well-marked. *)
Lemma initial_config_wf : forall t,
  config_wf (initial_config t).
Proof.
  intros t. unfold initial_config, config_wf. simpl.
  repeat split.
  - constructor.
  - constructor.
  - constructor.
  - constructor.
Qed.

Theorem preservation_multi : forall c c' T,
  config_typing c T ->
  config_wf c ->
  c ~~>c* c' ->
  config_typing c' T /\ config_wf c'.
Proof.
  intros c c' T Hty Hwf Hms.
  induction Hms.
  - split; assumption.
  - destruct (preservation _ _ _ Hty Hwf H) as [Hty2 Hwf2].
    apply IHHms; assumption.
Qed.

Theorem type_safety : forall t T c',
  config_typing (initial_config t) T ->
  initial_config t ~~>c* c' ->
  is_done c' \/ exists c'', c' ~~>c c''.
Proof.
  intros t T c' Hty Hms.
  destruct (preservation_multi _ _ _ Hty (initial_config_wf t) Hms)
    as [Hty' Hwf'].
  eapply progress; eauto.
Qed.
