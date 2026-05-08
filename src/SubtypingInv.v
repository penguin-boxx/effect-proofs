(* ================================================================== *)
(* SubtypingInv.v — evaluation contexts (typing-only) and subtyping   *)
(* shape inversion lemmas.                                            *)
(*                                                                    *)
(* Extracted from Safety.v sections 1-2 so that downstream files     *)
(* (notably CEKSafety.v) can use these lemmas without depending on   *)
(* the legacy small-step semantics module.                            *)
(* ================================================================== *)

From Stdlib Require Import List.
Import ListNotations.

From Metalib Require Export Metatheory.
Require Export Syntax.
Require Export Substitution.
Require Export Typing.

(* ================================================================== *)
(* Program-level (evaluation) contexts: a typing context is an        *)
(* "evaluation context" iff it contains only lifetime and constructor*)
(* bindings — no term or type variables.  Such a Γ is what an open   *)
(* runtime configuration types under.                                 *)
(* ================================================================== *)

Inductive eval_ctx : ctx -> Prop :=
  | ec_nil   : eval_ctx []
  | ec_lt    : forall a Δ Γ, eval_ctx Γ -> eval_ctx (bind_lt a Δ :: Γ)
  | ec_ctor  : forall K n_lt n_ty f r Γ,
      eval_ctx Γ -> eval_ctx (bind_ctor K n_lt n_ty f r :: Γ).

Lemma eval_ctx_no_tm : forall Γ x,
  eval_ctx Γ -> ctx_lookup_tm Γ x = None.
Proof. induction 1; intros; simpl; auto. Qed.

Lemma eval_ctx_no_ty : forall Γ a,
  eval_ctx Γ -> ctx_lookup_ty Γ a = None.
Proof. induction 1; intros; simpl; auto. Qed.

Lemma eval_ctx_no_eff : forall Γ E,
  eval_ctx Γ -> ctx_lookup_eff Γ E = None.
Proof. induction 1; intros; simpl; auto. Qed.

(* ================================================================== *)
(* Subtyping shape inversion lemmas (PROVED).                         *)
(* ================================================================== *)

Lemma sub_fun_inv : forall Γ S A l B,
  eval_ctx Γ ->
  Γ |-T S <: type_fun A l B ->
  exists A' l' B',
    S = type_fun A' l' B' /\
    Γ |-T A <: A' /\
    Γ |-l l' <: l /\
    Γ |-T B' <: B.
Proof.
  intros Γ S A l B Hec Hsub.
  remember (type_fun A l B) as T eqn:HT.
  revert A l B HT.
  induction Hsub; intros A0 l0 B0 HT.
  - inversion HT; subst.
    exists A0, l0, B0; repeat split; auto.
  - subst T.
    destruct (IHHsub2 Hec _ _ _ eq_refl) as [A1 [l1 [B1 [HeqU [HAa [Hla HBa]]]]]]; subst.
    destruct (IHHsub1 Hec _ _ _ eq_refl) as [A2 [l2 [B2 [HeqS [HAb [Hlb HBb]]]]]]; subst.
    exists A2, l2, B2. repeat split; eauto.
  - subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - discriminate HT.
  - discriminate HT.
  - injection HT; intros; subst.
    do 3 eexists; repeat split; eauto.
  - discriminate HT.
  - discriminate HT.
Qed.

Lemma sub_ctor_inv : forall Γ S K l Ts,
  eval_ctx Γ ->
  Γ |-T S <: type_ctor K l Ts ->
  K <> any_tag ->
  exists l', S = type_ctor K l' Ts /\ Γ |-l l' <: l.
Proof.
  intros Γ S K l Ts Hec Hsub HK.
  remember (type_ctor K l Ts) as T eqn:HT.
  revert K l Ts HT HK.
  induction Hsub; intros K0 l0 Ts0 HT HK.
  - inversion HT; subst. exists l0; split; auto.
  - subst T.
    destruct (IHHsub2 Hec _ _ _ eq_refl HK) as [l'' [HeqU Hl2]]; subst.
    destruct (IHHsub1 Hec _ _ _ eq_refl HK) as [l''' [HeqS Hl1]]; subst.
    exists l'''; split; eauto.
  - subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - injection HT; intros; subst. exists l; split; auto.
  - injection HT; intros; subst. contradiction.
  - discriminate HT.
  - discriminate HT.
  - discriminate HT.
Qed.

Lemma sub_lt_all_inv : forall Γ S T,
  eval_ctx Γ ->
  Γ |-T S <: type_lt_all T ->
  exists T', S = type_lt_all T'.
Proof.
  intros Γ S T Hec Hsub.
  remember (type_lt_all T) as U eqn:HU.
  revert T HU.
  induction Hsub; intros T0 HU.
  - inversion HU; subst. eauto.
  - subst T.
    destruct (IHHsub2 Hec _ eq_refl) as [T' HeqU]; subst.
    destruct (IHHsub1 Hec _ eq_refl) as [T'' HeqS]; subst. eauto.
  - subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - discriminate HU.
  - discriminate HU.
  - discriminate HU.
  - eauto.
  - discriminate HU.
Qed.

Lemma sub_ty_all_inv : forall Γ S B T,
  eval_ctx Γ ->
  Γ |-T S <: type_ty_all B T ->
  exists B' T', S = type_ty_all B' T'.
Proof.
  intros Γ S B T Hec Hsub.
  remember (type_ty_all B T) as U eqn:HU.
  revert B T HU.
  induction Hsub; intros B0 T0 HU.
  - inversion HU; subst. eauto.
  - subst T.
    destruct (IHHsub2 Hec _ _ eq_refl) as [B' [T' HeqU]]; subst.
    destruct (IHHsub1 Hec _ _ eq_refl) as [B'' [T'' HeqS]]; subst. eauto.
  - subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - discriminate HU.
  - discriminate HU.
  - discriminate HU.
  - discriminate HU.
  - eauto.
Qed.
