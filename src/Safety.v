Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import SubstitutionTheory.

(* ================================================================== *)
(*                                                                    *)
(*                 PROGRESS AND PRESERVATION                          *)
(*                                                                    *)
(* We prove type safety for CoreΔ under a top-level evaluation ctx    *)
(* that contains only lifetime and constructor bindings (no bind_tm,  *)
(* no bind_ty).  This blocks SA_VarCtx at the top level and matches   *)
(* the paper's "program-level" evaluation scenario.                   *)
(*                                                                    *)
(* Substitution-style lemmas (beta for tm/ty/lt and list              *)
(* substitutions used by the match-yes case) are axiomatized; they    *)
(* are standard de Bruijn manipulations orthogonal to the paper's     *)
(* contribution.                                                      *)
(* ================================================================== *)

Inductive eval_ctx : ctx -> Prop :=
  | ec_nil   : eval_ctx []
  | ec_lt    : forall Δ Γ, eval_ctx Γ -> eval_ctx (bind_lt Δ :: Γ)
  | ec_ctor  : forall K n_lt n_ty f r Γ,
      eval_ctx Γ -> eval_ctx (bind_ctor K n_lt n_ty f r :: Γ).

Lemma eval_ctx_no_tm : forall Γ x,
  eval_ctx Γ -> ctx_lookup_tm Γ x = None.
Proof.
  intros Γ x H; revert x; induction H; intros x; simpl; try reflexivity;
    match goal with
    | [ IH : forall _, _ = None |- _ ] => rewrite IH; reflexivity
    end.
Qed.

Lemma eval_ctx_no_ty : forall Γ α,
  eval_ctx Γ -> ctx_lookup_ty Γ α = None.
Proof.
  intros Γ α H; revert α; induction H; intros α; simpl; try reflexivity;
    match goal with
    | [ IH : forall _, _ = None |- _ ] => rewrite IH; reflexivity
    end.
Qed.

Lemma eval_ctx_no_eff : forall Γ E,
  eval_ctx Γ -> ctx_lookup_eff Γ E = None.
Proof.
  intros Γ E H; revert E; induction H; intros E; simpl; try reflexivity.
  - rewrite IHeval_ctx. reflexivity.
  - rewrite IHeval_ctx. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Effect-handler invariant                                           *)
(*                                                                    *)
(* Under an `eval_ctx` (no `bind_eff` entries), `T_Cap` cannot fire,  *)
(* so a well-typed term cannot be a perform of a typed capability.    *)
(* We prove this structurally:                                         *)
(*                                                                    *)
(*   1. A well-typed `term_cap E …` forces `ctx_lookup_eff Γ E` to be *)
(*      `Some …` (recorded by `T_Cap`; `T_Sub` is term-preserving).   *)
(*   2. Every evaluation-context constructor (`ectx`) types its hole  *)
(*      sub-term in the *same* context `Γ` — none introduce binders — *)
(*      so `Γ ⊢ₜ plug P u : T` yields a typing of `u` under `Γ`.       *)
(*   3. Inverting the `term_perform`/`term_cap` typing then collides   *)
(*      with `eval_ctx_no_eff`, giving the contradiction.             *)
(* ------------------------------------------------------------------ *)

(* From a `Forall2` typing premise, recover per-element typability. *)
Lemma Forall2_Forall_exists :
  forall (A B : Type) (R : A -> B -> Prop) xs ys,
    Forall2 R xs ys ->
    Forall (fun x => exists y, R x y) xs.
Proof.
  induction 1; constructor; eauto.
Qed.

(* A well-typed capability value forces its effect tag to be in Γ.    *)
Lemma cap_typed_eff_some : forall Γ E_tag m Ts op_body T,
  Γ ⊢ₜ term_cap E_tag m Ts op_body : T ->
  exists n_α n_β sig0 ret, ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig0, ret).
Proof.
  intros Γ E_tag m Ts op_body T H.
  remember (term_cap E_tag m Ts op_body) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - (* T_Sub *) apply IHtyping; exact Hs.
  - (* T_Cap *) injection Hs; intros; subst. eauto.
Qed.

(* Subsumption-stripping inversions: each gives a typing of the      *)
(* hole-bearing sub-term in the same context Γ.                       *)

Lemma typed_app_inv : forall Γ f x T,
  Γ ⊢ₜ term_app f x : T ->
  exists A l B, Γ ⊢ₜ f : type_fun A l B /\ Γ ⊢ₜ x : A.
Proof.
  intros Γ f x T H.
  remember (term_app f x) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - apply IHtyping; exact Hs.
  - injection Hs; intros; subst. exists A, l, B; split; assumption.
Qed.

Lemma typed_ty_app_inv : forall Γ t S T,
  Γ ⊢ₜ term_ty_app t S : T -> exists T0, Γ ⊢ₜ t : T0.
Proof.
  intros Γ t S T H.
  remember (term_ty_app t S) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - apply IHtyping; exact Hs.
  - injection Hs; intros; subst. eexists; eassumption.
Qed.

Lemma typed_lt_app_inv : forall Γ t l T,
  Γ ⊢ₜ term_lt_app t l : T -> exists T0, Γ ⊢ₜ t : T0.
Proof.
  intros Γ t l T H.
  remember (term_lt_app t l) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - apply IHtyping; exact Hs.
  - injection Hs; intros; subst. eexists; eassumption.
Qed.

Lemma typed_match_inv : forall Γ scrut K arity yes no T,
  Γ ⊢ₜ term_match scrut K arity yes no : T -> exists T0, Γ ⊢ₜ scrut : T0.
Proof.
  intros Γ scrut K arity yes no T H.
  remember (term_match scrut K arity yes no) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - apply IHtyping; exact Hs.
  - injection Hs; intros; subst. eexists; eassumption.
Qed.

Lemma typed_handler_m_inv : forall Γ m t T,
  Γ ⊢ₜ term_handler_m m t : T -> exists T0, Γ ⊢ₜ t : T0.
Proof.
  intros Γ m t T H.
  remember (term_handler_m m t) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - apply IHtyping; exact Hs.
  - injection Hs; intros; subst. eexists; eassumption.
Qed.

Lemma typed_perform_inv : forall Γ recv Ss arg T,
  Γ ⊢ₜ term_perform recv Ss arg : T ->
  exists Tr Ta, Γ ⊢ₜ recv : Tr /\ Γ ⊢ₜ arg : Ta.
Proof.
  intros Γ recv Ss arg T H.
  remember (term_perform recv Ss arg) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - apply IHtyping; exact Hs.
  - injection Hs; intros; subst. eexists; eexists; split; eassumption.
Qed.

Lemma typed_ctor_inv : forall Γ K l lts Ts args T,
  Γ ⊢ₜ term_ctor K l lts Ts args : T ->
  Forall (fun a => exists rho, Γ ⊢ₜ a : rho) args.
Proof.
  intros Γ K l lts Ts args T H.
  remember (term_ctor K l lts Ts args) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - (* T_Sub *) apply IHtyping; exact Hs.
  - (* T_Ctor *) injection Hs; intros; subst.
    match goal with
    | Hf : Forall2 _ _ _ |- _ =>
        exact (Forall2_Forall_exists _ _ _ _ _ Hf)
    end.
Qed.

(* Typing of `plug P u` yields a typing of the plugged sub-term `u`   *)
(* under the same context: evaluation contexts add no binders.        *)
Lemma plug_typing_inv : forall P Γ u T,
  Γ ⊢ₜ plug P u : T -> exists T', Γ ⊢ₜ u : T'.
Proof.
  induction P; intros Γ u T H; simpl in H.
  - (* EC_hole *) exists T; exact H.
  - (* EC_app1 *)
    apply typed_app_inv in H. destruct H as [A [l [B [Hf _]]]].
    eapply IHP; exact Hf.
  - (* EC_app2 *)
    apply typed_app_inv in H. destruct H as [A [l [B [_ Hx]]]].
    eapply IHP; exact Hx.
  - (* EC_ty_app *)
    apply typed_ty_app_inv in H. destruct H as [T0 Ht].
    eapply IHP; exact Ht.
  - (* EC_lt_app *)
    apply typed_lt_app_inv in H. destruct H as [T0 Ht].
    eapply IHP; exact Ht.
  - (* EC_ctor *)
    apply typed_ctor_inv in H.
    rewrite Forall_app in H. destruct H as [_ H].
    apply Forall_inv in H. destruct H as [rho Hrho].
    eapply IHP; exact Hrho.
  - (* EC_match *)
    apply typed_match_inv in H. destruct H as [T0 Ht].
    eapply IHP; exact Ht.
  - (* EC_handler_m *)
    apply typed_handler_m_inv in H. destruct H as [T0 Ht].
    eapply IHP; exact Ht.
  - (* EC_perform_r *)
    apply typed_perform_inv in H. destruct H as [Tr [Ta [Hr _]]].
    eapply IHP; exact Hr.
  - (* EC_perform_a *)
    apply typed_perform_inv in H. destruct H as [Tr [Ta [_ Ha]]].
    eapply IHP; exact Ha.
Qed.

Theorem no_typed_perform_cap_under_eval_ctx :
  forall Γ T E_tag m Ts op_body Ss v P,
    eval_ctx Γ ->
    pure_ectx_m m P ->
    Γ ⊢ₜ plug P (term_perform (term_cap E_tag m Ts op_body) Ss v) : T ->
    False.
Proof.
  intros Γ T E_tag m Ts op_body Ss v P Hec Hpe Hty.
  apply plug_typing_inv in Hty. destruct Hty as [T' Hty].
  apply typed_perform_inv in Hty. destruct Hty as [Tr [Ta [Hr _]]].
  apply cap_typed_eff_some in Hr.
  destruct Hr as [n_α [n_β [sig0 [ret Hlk]]]].
  rewrite (eval_ctx_no_eff _ E_tag Hec) in Hlk. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Subtyping shape inversion under eval_ctx.                          *)
(* ------------------------------------------------------------------ *)

Lemma sub_fun_inv : forall Γ S A l B,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_fun A l B ->
  exists A' l' B',
    S = type_fun A' l' B' /\
    Γ ⊢ A <:: A' /\
    Γ ⊢ₗ l' <: l /\
    Γ ⊢ B' <:: B.
Proof.
  intros Γ S A l B Hec Hsub.
  remember (type_fun A l B) as T eqn:HT.
  revert A l B HT.
  induction Hsub; intros A0 l0 B0 HT.
  - (* Refl *) exists A0, l0, B0; inversion HT; subst; repeat split; auto.
  - (* Trans *) subst T.
    destruct (IHHsub2 Hec _ _ _ eq_refl) as [A1 [l1 [B1 [HeqU [HAa [Hla HBa]]]]]]; subst.
    destruct (IHHsub1 Hec _ _ _ eq_refl) as [A2 [l2 [B2 [HeqS [HAb [Hlb HBb]]]]]]; subst.
    exists A2, l2, B2. repeat split; eauto.
  - (* VarCtx *) subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - (* Data *) discriminate HT.
  - (* Any *) discriminate HT.
  - (* Fun *) injection HT; intros HB0 Hl0 HA0; subst.
    exists A', l, B; repeat split; auto.
  - (* LtAll *) discriminate HT.
  - (* TyAll *) discriminate HT.
Qed.

Lemma sub_ctor_inv : forall Γ S K l Ts,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_ctor K l Ts ->
  K <> any_tag ->
  exists l', S = type_ctor K l' Ts /\ Γ ⊢ₗ l' <: l.
Proof.
  intros Γ S K l Ts Hec Hsub HK.
  remember (type_ctor K l Ts) as T eqn:HT.
  revert K l Ts HT HK.
  induction Hsub; intros K0 l0 Ts0 HT HK.
  - (* Refl *) inversion HT; subst. exists l0; split; auto.
  - (* Trans *) subst T.
    destruct (IHHsub2 Hec _ _ _ eq_refl HK) as [l'' [HeqU Hl2]]; subst.
    destruct (IHHsub1 Hec _ _ _ eq_refl HK) as [l''' [HeqS Hl1]]; subst.
    exists l'''; split; eauto.
  - (* VarCtx *) subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - (* Data *) injection HT; intros; subst. exists l; split; auto.
  - (* Any *) injection HT; intros; subst. contradiction.
  - (* Fun *) discriminate HT.
  - (* LtAll *) discriminate HT.
  - (* TyAll *) discriminate HT.
Qed.

Lemma sub_lt_all_inv : forall Γ S T,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_lt_all T ->
  exists T', S = type_lt_all T'.
Proof.
  intros Γ S T Hec Hsub.
  remember (type_lt_all T) as U eqn:HU.
  revert T HU.
  induction Hsub; intros T0 HU.
  - (* Refl *) inversion HU; subst. eauto.
  - (* Trans *) subst T.
    destruct (IHHsub2 Hec _ eq_refl) as [T' HeqU]; subst.
    destruct (IHHsub1 Hec _ eq_refl) as [T'' HeqS]; subst. eauto.
  - (* VarCtx *) subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - (* Data *) discriminate HU.
  - (* Any *) discriminate HU.
  - (* Fun *) discriminate HU.
  - (* LtAll *) injection HU; intros; subst. eauto.
  - (* TyAll *) discriminate HU.
Qed.

Lemma sub_ty_all_inv : forall Γ S B T,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_ty_all B T ->
  exists B' T', S = type_ty_all B' T'.
Proof.
  intros Γ S B T Hec Hsub.
  remember (type_ty_all B T) as U eqn:HU.
  revert B T HU.
  induction Hsub; intros B0 T0 HU.
  - (* Refl *) inversion HU; subst. eauto.
  - (* Trans *) subst T.
    destruct (IHHsub2 Hec _ _ eq_refl) as [B' [T' HeqU]]; subst.
    destruct (IHHsub1 Hec _ _ eq_refl) as [B'' [T'' HeqS]]; subst. eauto.
  - (* VarCtx *) subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - (* Data *) discriminate HU.
  - (* Any *) discriminate HU.
  - (* Fun *) discriminate HU.
  - (* LtAll *) discriminate HU.
  - (* TyAll *) injection HU; intros; subst. eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Canonical forms                                                    *)
(* ------------------------------------------------------------------ *)

Lemma canonical_fun : forall Γ v A l B,
  eval_ctx Γ ->
  Γ ⊢ₜ v : type_fun A l B ->
  value v ->
  (exists body T, v = term_lam body T)
  \/ (exists m b, v = term_resume m b).
Proof.
  intros Γ v A l B Hec Hty Hval.
  remember (type_fun A l B) as T0 eqn:HT.
  revert A l B HT.
  induction Hty; intros A0 l0 B0 HT; subst;
    try (inversion Hval; fail);
    try discriminate HT.
  - (* T_Sub *)
    destruct (sub_fun_inv _ _ _ _ _ Hec H) as [A' [l' [B' [HeqT _]]]]; subst.
    eapply IHHty; eauto.
  - (* T_Lam *) left; eauto.
  - (* T_Ctor *)
    match goal with
    | H1 : ?R = type_ctor _ _ _, H2 : ?R = type_fun _ _ _ |- _ => rewrite H1 in H2; discriminate H2
    | H1 : ?R = type_ctor _ _ _, H2 : type_fun _ _ _ = ?R |- _ => rewrite H1 in H2; discriminate H2
    | H1 : type_ctor _ _ _ = ?R, H2 : ?R = type_fun _ _ _ |- _ => rewrite <- H1 in H2; discriminate H2
    | H1 : type_ctor _ _ _ = ?R, H2 : type_fun _ _ _ = ?R |- _ => rewrite <- H1 in H2; discriminate H2
    | H : type_fun _ _ _ = type_ctor _ _ _ |- _ => discriminate H
    | H : type_ctor _ _ _ = type_fun _ _ _ |- _ => discriminate H
    end.
  - (* T_Resume *) right; eauto.
Qed.

Lemma canonical_ctor : forall Γ v K l Ts,
  eval_ctx Γ ->
  Γ ⊢ₜ v : type_ctor K l Ts ->
  value v ->
  K <> any_tag ->
  exists K' l' lts' Ts' vs, v = term_ctor K' l' lts' Ts' vs /\ Forall value vs.
Proof.
  intros Γ v K l Ts Hec Hty Hval HK.
  remember (type_ctor K l Ts) as T0 eqn:HT.
  revert K l Ts HT HK.
  induction Hty; intros K0 l0 Ts0 HT HK; subst;
    try (inversion Hval; fail);
    try discriminate HT.
  - (* T_Sub *)
    destruct (sub_ctor_inv _ _ _ _ _ Hec H HK) as [l' [HeqT _]]; subst.
    eapply IHHty; eauto.
  - (* T_Ctor *)
    inversion Hval; subst.
    eexists; eexists; eexists; eexists; eexists; split; eauto.
  - (* T_Cap (NEW: capability values inhabit type_ctor — closed by    *)
    (* contradiction under eval_ctx: T_Cap requires the effect-tag to  *)
    (* be in scope, but eval_ctx has no bind_eff entries.)             *)
    rewrite eval_ctx_no_eff in H; auto; discriminate.
Qed.

Lemma canonical_lt_all : forall Γ v T,
  eval_ctx Γ ->
  Γ ⊢ₜ v : type_lt_all T ->
  value v ->
  exists body, v = term_lt_lam body.
Proof.
  intros Γ v T Hec Hty Hval.
  remember (type_lt_all T) as T0 eqn:HT.
  revert T HT.
  induction Hty; intros T0 HT; subst;
    try (inversion Hval; fail);
    try discriminate HT.
  - (* T_Sub *)
    destruct (sub_lt_all_inv _ _ _ Hec H) as [T' HeqT]; subst.
    eapply IHHty; eauto.
  - (* T_LtLam *) eauto.
  - (* T_Ctor *)
    match goal with
    | H1 : ?R = type_ctor _ _ _, H2 : ?R = type_lt_all _ |- _ => rewrite H1 in H2; discriminate H2
    | H1 : ?R = type_ctor _ _ _, H2 : type_lt_all _ = ?R |- _ => rewrite H1 in H2; discriminate H2
    | H1 : type_ctor _ _ _ = ?R, H2 : ?R = type_lt_all _ |- _ => rewrite <- H1 in H2; discriminate H2
    | H1 : type_ctor _ _ _ = ?R, H2 : type_lt_all _ = ?R |- _ => rewrite <- H1 in H2; discriminate H2
    | H : type_lt_all _ = type_ctor _ _ _ |- _ => discriminate H
    | H : type_ctor _ _ _ = type_lt_all _ |- _ => discriminate H
    end.
Qed.

Lemma canonical_ty_all : forall Γ v B T,
  eval_ctx Γ ->
  Γ ⊢ₜ v : type_ty_all B T ->
  value v ->
  exists bound body, v = term_ty_lam bound body.
Proof.
  intros Γ v B T Hec Hty Hval.
  remember (type_ty_all B T) as T0 eqn:HT.
  revert B T HT.
  induction Hty; intros B0 T0 HT; subst;
    try (inversion Hval; fail);
    try discriminate HT.
  - (* T_Sub *)
    destruct (sub_ty_all_inv _ _ _ _ Hec H) as [B' [T' HeqT]]; subst.
    eapply IHHty; eauto.
  - (* T_TyLam *) eauto.
  - (* T_Ctor *)
    match goal with
    | H1 : ?R = type_ctor _ _ _, H2 : ?R = type_ty_all _ _ |- _ => rewrite H1 in H2; discriminate H2
    | H1 : ?R = type_ctor _ _ _, H2 : type_ty_all _ _ = ?R |- _ => rewrite H1 in H2; discriminate H2
    | H1 : type_ctor _ _ _ = ?R, H2 : ?R = type_ty_all _ _ |- _ => rewrite <- H1 in H2; discriminate H2
    | H1 : type_ctor _ _ _ = ?R, H2 : type_ty_all _ _ = ?R |- _ => rewrite <- H1 in H2; discriminate H2
    | H : type_ty_all _ _ = type_ctor _ _ _ |- _ => discriminate H
    | H : type_ctor _ _ _ = type_ty_all _ _ |- _ => discriminate H
    end.
Qed.

(* ------------------------------------------------------------------ *)
(* PROGRESS                                                           *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------- *)
(* Forall2 plumbing + a Forall2-aware induction principle for `typing` *)
(*                                                                     *)
(* Coq's auto-generated `typing_ind` does NOT thread per-element       *)
(* induction hypotheses through the `Forall2` premise of T_Ctor.       *)
(* `typing_ind2` below augments the T_Ctor case with exactly that      *)
(* `Forall2 (fun v rho => P Γ v rho)` hypothesis, which is what lets   *)
(* `progress` and `preservation` discharge the constructor case        *)
(* without any axioms.                                                 *)
(* ------------------------------------------------------------------- *)

Lemma f2_uncons_l : forall {A B} (R : A -> B -> Prop) x l ys,
  Forall2 R (x :: l) ys ->
  exists y l', ys = y :: l' /\ R x y /\ Forall2 R l l'.
Proof. intros A B R x l ys H. inversion H; subst. eauto. Qed.

Lemma Forall2_Forall_left : forall {A B} (R : A -> Prop) (S : A -> B -> Prop) xs ys,
  Forall2 S xs ys ->
  (forall x y, S x y -> R x) ->
  Forall R xs.
Proof.
  intros A B R S xs ys H Himp; induction H; constructor.
  - eapply Himp; eauto.
  - apply IHForall2; auto.
Qed.

Lemma typing_ind2 :
  forall (P : ctx -> term -> type -> Prop),
  (forall Γ x T, ctx_lookup_tm Γ x = Some T -> P Γ (term_var x) T) ->
  (forall Γ t T U, Γ ⊢ₜ t : T -> P Γ t T -> Γ ⊢ T <:: U -> P Γ t U) ->
  (forall Γ body A l B,
     (bind_tm A :: Γ) ⊢ₜ body : B -> P (bind_tm A :: Γ) body B ->
     Γ ⊢ₗ capture_lt Γ body <: l -> no_local_ty B = true ->
     P Γ (term_lam body A) (type_fun A l B)) ->
  (forall Γ t1 t2 A l B,
     Γ ⊢ₜ t1 : type_fun A l B -> P Γ t1 (type_fun A l B) ->
     Γ ⊢ₜ t2 : A -> P Γ t2 A ->
     P Γ (term_app t1 t2) B) ->
  (forall Γ bound body T,
     (bind_ty bound :: Γ) ⊢ₜ body : T -> P (bind_ty bound :: Γ) body T ->
     P Γ (term_ty_lam bound body) (type_ty_all bound T)) ->
  (forall Γ t B U S,
     Γ ⊢ₜ t : type_ty_all B U -> P Γ t (type_ty_all B U) ->
     Γ ⊢ S <:: B ->
     P Γ (term_ty_app t S) (subst_ty 0 S U)) ->
  (forall Γ body T,
     (bind_lt lt_local :: Γ) ⊢ₜ body : T -> P (bind_lt lt_local :: Γ) body T ->
     P Γ (term_lt_lam body) (type_lt_all T)) ->
  (forall Γ t T l,
     Γ ⊢ₜ t : type_lt_all T -> P Γ t (type_lt_all T) ->
     P Γ (term_lt_app t l) (subst_lt_in_ty 0 l T)) ->
        (forall Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
          result_ty result_tag l vs,
     ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) ->
     ctx_lookup_eff Γ K = None ->
     List.length lts = n_lt ->
     rho_fields = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields ->
     List.length Ts = n_ty ->
      result_ty = inst_ctor_type n_lt n_ty lts Ts result_ty_schema ->
      result_ty = type_ctor result_tag l Ts ->
      Γ ⊢ₗ lt_of_ty_list rho_fields <: l ->
     List.length vs = List.length rho_fields ->
     Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rho_fields ->
     Forall2 (fun v rho => P Γ v rho) vs rho_fields ->
      P Γ (term_ctor K l lts Ts vs) result_ty) ->
        (forall Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
          rho_fields scrut_result_ty result_tag result_l
         Γ' yes_body eta elim_result no_body,
     K <> any_tag ->
     ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) ->
     ctx_lookup_eff Γ K = None ->
     lts = lt_var_list n_lt ->
     rho_fields = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields ->
      List.length Ts = n_ty ->
      scrut_result_ty = inst_ctor_type n_lt n_ty (List.repeat Delta n_lt) Ts result_ty_schema ->
      scrut_result_ty = type_ctor result_tag result_l Ts ->
      result_tag <> any_tag ->
      Γ ⊢ₗ result_l <: Delta ->
      Γ ⊢ₜ scrut : type_ctor result_tag Delta Ts ->
      P Γ scrut (type_ctor result_tag Delta Ts) ->
     arity = List.length rho_fields ->
     Γ' = push_lt_vars n_lt Delta Γ ->
     (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ' rho_fields) ⊢ₜ yes_body : eta ->
     P (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ' rho_fields) yes_body eta ->
     elim_ty_n n_lt (shift_lt n_lt 0 Delta) var_pos eta = Some elim_result ->
     Γ ⊢ₜ no_body : elim_result -> P Γ no_body elim_result ->
     P Γ (term_match scrut K arity yes_body no_body) elim_result) ->
  (forall Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β,
     ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
     List.length Ts = n_α ->
      sig_β = inst_op_alpha n_α Ts n_β sig ->
      ret_β = inst_op_alpha n_α Ts n_β ret ->
     (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) ⊢ₜ op_body : shift_ty n_β 0 T_R ->
     P (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) op_body (shift_ty n_β 0 T_R) ->
     P Γ (term_cap E_tag m Ts op_body) (type_ctor E_tag lt_local Ts)) ->
  (forall Γ E_tag Ts op_body body n_α n_β sig ret T_R sig_β ret_β,
     ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
     List.length Ts = n_α ->
      sig_β = inst_op_alpha n_α Ts n_β sig ->
      ret_β = inst_op_alpha n_α Ts n_β ret ->
     (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) ⊢ₜ op_body : shift_ty n_β 0 T_R ->
     P (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) op_body (shift_ty n_β 0 T_R) ->
     (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) ⊢ₜ body : T_R ->
     P (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) body T_R ->
     P Γ (term_handle E_tag Ts op_body body) T_R) ->
  (forall Γ recv arg E_tag Δ Ts Ss n_α n_β sig ret sig_inst ret_inst,
     Γ ⊢ₜ recv : type_ctor E_tag Δ Ts -> P Γ recv (type_ctor E_tag Δ Ts) ->
     ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
     List.length Ts = n_α ->
     List.length Ss = n_β ->
     sig_inst = inst_op_arg n_α Ts n_β Ss sig ->
     ret_inst = inst_op_arg n_α Ts n_β Ss ret ->
     Γ ⊢ₜ arg : sig_inst -> P Γ arg sig_inst ->
     P Γ (term_perform recv Ss arg) ret_inst) ->
  (forall Γ m t T, Γ ⊢ₜ t : T -> P Γ t T -> P Γ (term_handler_m m t) T) ->
  (forall Γ m b A T_R,
     (bind_tm A :: Γ) ⊢ₜ b : T_R -> P (bind_tm A :: Γ) b T_R ->
     P Γ (term_resume m b) (type_fun A lt_local T_R)) ->
  forall Γ t T, Γ ⊢ₜ t : T -> P Γ t T.
Proof.
  intros P HVar HSub HLam HApp HTyLam HTyApp HLtLam HLtApp HCtor HMatch
         HCap HHandle HPerform HHandlerM HResume.
  fix IH 4.
  intros Γ t T H. destruct H.
  - eapply HVar; (eassumption || (apply IH; eassumption)).
  - eapply HSub; (eassumption || (apply IH; eassumption)).
  - eapply HLam; (eassumption || (apply IH; eassumption)).
  - eapply HApp; (eassumption || (apply IH; eassumption)).
  - eapply HTyLam; (eassumption || (apply IH; eassumption)).
  - eapply HTyApp; (eassumption || (apply IH; eassumption)).
  - eapply HLtLam; (eassumption || (apply IH; eassumption)).
  - eapply HLtApp; (eassumption || (apply IH; eassumption)).
  - (* T_Ctor: build the Forall2 of IHs inline so the recursive calls    *)
    (* stay on structural subterms of the derivation (guardedness).      *)
    eapply HCtor; try (eassumption || (apply IH; eassumption)).
    match goal with
    | HF : Forall2 (fun v rho => _ ⊢ₜ v : rho) ?vs ?rf |- Forall2 _ ?vs ?rf =>
        clear -IH HF; induction HF
    end.
    + constructor.
    + constructor; [ apply IH; assumption | assumption ].
  - eapply HMatch; (eassumption || (apply IH; eassumption)).
  - eapply HCap; (eassumption || (apply IH; eassumption)).
  - eapply HHandle; (eassumption || (apply IH; eassumption)).
  - eapply HPerform; (eassumption || (apply IH; eassumption)).
  - eapply HHandlerM; (eassumption || (apply IH; eassumption)).
  - eapply HResume; (eassumption || (apply IH; eassumption)).
Qed.

(* A well-typed ctor value has |vs| matching its runtime tag's arity. *)
Lemma ctor_value_arity : forall Γ K l lts Ts vs T,
  Γ ⊢ₜ term_ctor K l lts Ts vs : T ->
  exists n_lt n_ty sigma result,
    ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma, result) /\
    List.length vs = List.length sigma.
Proof.
  intros Γ K l lts Ts vs T Hty.
  remember (term_ctor K l lts Ts vs) as t eqn:Ht.
  revert K l lts Ts vs Ht.
  induction Hty; intros K0 l0 lts0 Ts0 vs0 Ht; try discriminate Ht.
  - (* T_Sub *) eapply IHHty; eauto.
  - (* T_Ctor *)
    injection Ht; intros Hvs HTs0 Hlts0 Hl0 HK0.
    subst K0 l0 lts0 Ts0 vs0.
    exists n_lt, n_ty, sigma_fields, result_ty_schema. split; auto.
    match goal with
    | Hlen : List.length ?vs = List.length ?rho,
      Hrho : ?rho = List.map _ ?sigma |- List.length ?vs = List.length ?sigma =>
        rewrite Hlen, Hrho, List.length_map; reflexivity
    end.
Qed.

(* Helper: from Forall (value-or-step) deduce all-values or a step-in-list. *)
Lemma split_values_or_step : forall vs,
  Forall (fun v => value v \/ exists v', v ==> v') vs ->
  Forall value vs \/
  exists vsl t t' vsr,
    Forall value vsl /\ vs = vsl ++ t :: vsr /\ t ==> t'.
Proof.
  induction vs as [| v vs' IH]; intros H.
  { left; constructor. }
  inversion H as [| x xs Hhead Hrest]; subst.
  destruct Hhead as [Hv | [v' Hs]].
  - destruct (IH Hrest) as [Hall | [vsl [t [t' [vsr [Hallvl [Heq Hst]]]]]]].
    + left. constructor; auto.
    + right. exists (v :: vsl), t, t', vsr.
      repeat split; auto. simpl. f_equal; auto.
  - right. exists (@nil term), v, v', vs'. repeat split; auto.
Qed.

Theorem progress : forall Γ t T,
  eval_ctx Γ ->
  Γ ⊢ₜ t : T ->
  value t \/ exists t', t ==> t'.
Proof.
  intros Γ0 t0 T0 Hec0 Hty0. revert Hec0.
  revert Hty0; revert T0; revert t0; revert Γ0.
  apply (typing_ind2 (fun Γ t T => eval_ctx Γ -> value t \/ exists t', t ==> t')).
  - (* T_Var *)
    intros Γ x T Hlk Hec.
    rewrite eval_ctx_no_tm in Hlk; auto; discriminate.
  - (* T_Sub *)
    intros Γ t T U Hty IH Hsub Hec. apply IH; assumption.
  - (* T_Lam *)
    intros Γ body A l B Hbody IHbody Hcap Hnl Hec. left; constructor.
  - (* T_App *)
    intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 Hec.
    specialize (IH1 Hec); specialize (IH2 Hec).
    destruct IH1 as [Hv1 | [t1' Hs1]].
    + destruct IH2 as [Hv2 | [t2' Hs2]].
      * destruct (canonical_fun _ _ _ _ _ Hec Ht1 Hv1) as
          [[body [T0 Heq]] | [m [b Heq]]]; subst.
        -- right. eexists. apply S_Beta; auto.
        -- right. eexists. apply S_Resume; auto.
      * right. eexists. eapply S_App2; eauto.
    + right. eexists. eapply S_App1; eauto.
  - (* T_TyLam *)
    intros Γ bound body T Hbody IHbody Hec. left; constructor.
  - (* T_TyApp *)
    intros Γ t B U S Ht IH Hsub Hec.
    specialize (IH Hec). destruct IH as [Hv | [t' Hs]].
    + destruct (canonical_ty_all _ _ _ _ Hec Ht Hv) as [bnd [body Heq]]; subst.
      right. eexists. apply S_TyBeta.
    + right. eexists. eapply S_TyApp; eauto.
  - (* T_LtLam *)
    intros Γ body T Hbody IHbody Hec. left; constructor.
  - (* T_LtApp *)
    intros Γ t T l Ht IH Hec.
    specialize (IH Hec). destruct IH as [Hv | [t' Hs]].
    + destruct (canonical_lt_all _ _ _ Hec Ht Hv) as [body Heq]; subst.
      right. eexists. apply S_LtBeta.
    + right. eexists. eapply S_LtApp; eauto.
  - (* T_Ctor *)
        intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
          result_ty result_tag l vs
           Hlk Heff Hlen_lts Hrho Hlen_Ts Hresult Hshape Hlt Hlen_vs HF HFP Hec.
    assert (Hforall : Forall (fun v => value v \/ exists v', v ==> v') vs).
    { eapply Forall2_Forall_left; [ exact HFP | ].
      intros a b Hab. apply Hab; exact Hec. }
    destruct (split_values_or_step _ Hforall) as
      [Hall | [vsl [tm [tm' [vsr [Hallvl [Heq Hst]]]]]]].
    + left. constructor; auto.
    + right. subst. eexists. apply S_Ctor; eauto.
  - (* T_Match *)
    intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
      rho_fields scrut_result_ty result_tag result_l
           Γ' yes_body eta elim_result no_body
        HKne Hlk Heff Hlts Hrho HTs Hscrut_result Hscrut_shape
        Hresult_ne Hresult_l Hscrut IHscrut Harity HGamma' Hyes IHyes Helim Hno IHno Hec.
    specialize (IHscrut Hec).
    destruct IHscrut as [Hv | [scrut' Hs]].
      + destruct (canonical_ctor _ _ result_tag Delta Ts Hec Hscrut Hv Hresult_ne)
        as [K' [l' [lts' [Ts' [vs [Heq Hvvs]]]]]]; subst.
      right.
      destruct (Nat.eq_dec K' K) as [HKeq | HKdiff].
      * subst K'.
        destruct (ctor_value_arity _ _ _ _ _ _ _ Hscrut)
          as [n_lt' [n_ty' [sig' [res' [Hlook Hlen]]]]].
        rewrite Hlk in Hlook.
        injection Hlook as Heq1 Heq2 Heq3 Heq4.
        subst n_lt' n_ty' sig' res'.
        eexists.
        match goal with
        | |- term_match _ _ ?a _ _ ==> _ => replace a with (@length term vs)
        end.
        2:{ rewrite List.length_map. exact Hlen. }
        apply S_MatchYes. auto.
      * eexists. eapply S_MatchNo; eauto.
    + right. eexists. eapply S_Match; eauto.
  - (* T_Cap *)
    intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff Hlen Hsb Hrb Hop IHop Hec. left; constructor.
  - (* T_Handle *)
    intros Γ E_tag Ts op_body body n_α n_β sig ret T_R sig_β ret_β
           Heff Hlen Hsb Hrb Hop IHop Hbody IHbody Hec.
    rewrite eval_ctx_no_eff in Heff; auto; discriminate.
  - (* T_Perform *)
    intros Γ recv arg E_tag Δ Ts Ss n_α n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hlen_Ts Hlen_Ss Hsi Hri Harg IHarg Hec.
    rewrite eval_ctx_no_eff in Heff; auto; discriminate.
  - (* T_HandlerM *)
    intros Γ m t T Ht IH Hec.
    specialize (IH Hec). destruct IH as [Hv | [t' Hs]].
    + right. exists t. apply S_Return; auto.
    + right. exists (term_handler_m m t'). apply S_HandlerM; auto.
  - (* T_Resume *)
    intros Γ m b A T_R Hb IHb Hec. left; constructor.
Qed.


(* Substitution-style lemmas (subst_tm_lemma, subst_ty_in_tm_lemma,   *)
(* subst_lt_in_tm_lemma) are now in SubstitutionTheory.v.             *)

(* ------------------------------------------------------------------ *)
(* Typing inversion lemmas                                            *)
(* ------------------------------------------------------------------ *)

Lemma lam_typing_inv : forall Γ body A T,
  Γ ⊢ₜ term_lam body A : T ->
  exists l B,
    (bind_tm A :: Γ) ⊢ₜ body : B /\
    Γ ⊢ type_fun A l B <:: T.
Proof.
  intros Γ body A T Hty.
  remember (term_lam body A) as t eqn:Ht.
  induction Hty; try discriminate.
  - subst. destruct (IHHty eq_refl) as [l0 [B0 [Hbody Hsub]]].
    exists l0, B0; split; auto. eapply SA_Trans; eauto.
  - injection Ht; intros; subst. exists l, B; split; auto.
Qed.

Lemma ty_lam_typing_inv : forall Γ bound body T,
  Γ ⊢ₜ term_ty_lam bound body : T ->
  exists U,
    (bind_ty bound :: Γ) ⊢ₜ body : U /\
    Γ ⊢ type_ty_all bound U <:: T.
Proof.
  intros Γ bound body T Hty.
  remember (term_ty_lam bound body) as t eqn:Ht.
  induction Hty; try discriminate.
  - subst. destruct (IHHty eq_refl) as [U0 [Hbody Hsub]].
    exists U0; split; auto. eapply SA_Trans; eauto.
  - injection Ht; intros; subst. exists T; split; auto.
Qed.

Lemma lt_lam_typing_inv : forall Γ body T,
  Γ ⊢ₜ term_lt_lam body : T ->
  exists U,
    (bind_lt lt_local :: Γ) ⊢ₜ body : U /\
    Γ ⊢ type_lt_all U <:: T.
Proof.
  intros Γ body T Hty.
  remember (term_lt_lam body) as t eqn:Ht.
  induction Hty; try discriminate.
  - subst. destruct (IHHty eq_refl) as [U0 [Hbody Hsub]].
    exists U0; split; auto. eapply SA_Trans; eauto.
  - injection Ht; intros; subst. exists T; split; auto.
Qed.

Lemma resume_typing_inv : forall Γ m b T,
  Γ ⊢ₜ term_resume m b : T ->
  exists A B,
    (bind_tm A :: Γ) ⊢ₜ b : B /\
    Γ ⊢ type_fun A lt_local B <:: T.
Proof.
  intros Γ m b T Hty.
  remember (term_resume m b) as t eqn:Ht.
  induction Hty; try discriminate.
  - subst. destruct (IHHty eq_refl) as [A0 [B0 [Hbody Hsub]]].
    exists A0, B0; split; auto. eapply SA_Trans; eauto.
  - injection Ht; intros; subst. exists A, T_R; split; auto.
Qed.

(* ------------------------------------------------------------------ *)
(* PRESERVATION                                                       *)
(*                                                                    *)
(* Top-level structure is standard; the β-reduction cases rely on     *)
(* shape inversion and the substitution axioms above.  The App case   *)
(* is fully proven; Ty/Lt β-cases need a narrowing-style lemma that   *)
(* recovers the body-subtyping witness — axiomatized as sub_*_body.   *)
(* ------------------------------------------------------------------ *)

(* Narrowing/body-subtyping witnesses extracted from sub_*_inv.       *)
(* Under eval_ctx these follow structurally from the full inversion   *)
(* (including the body-subtype witness); we axiomatize the            *)
(* body-witness part since we stated sub_lt_all_inv / sub_ty_all_inv  *)
(* without it for brevity.                                            *)
Lemma sub_lt_all_inv_full : forall Γ S T,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_lt_all T ->
  exists T', S = type_lt_all T' /\ (bind_lt lt_local :: Γ) ⊢ T' <:: T.
Proof.
  intros Γ S T Hec Hsub.
  remember (type_lt_all T) as U eqn:HU.
  revert T HU.
  induction Hsub; intros T0 HU.
  - (* Refl *) inversion HU; subst. exists T0. split; auto.
  - (* Trans *) subst T.
    destruct (IHHsub2 Hec _ eq_refl) as [U0 [HeqU HsubU]]; subst.
    destruct (IHHsub1 Hec _ eq_refl) as [S0 [HeqS HsubS]]; subst.
    exists S0; split; auto. eapply SA_Trans; eauto.
  - (* VarCtx *) subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - (* Data *) discriminate HU.
  - (* Any *) discriminate HU.
  - (* Fun *) discriminate HU.
  - (* LtAll *) injection HU; intros; subst. exists A; split; auto.
  - (* TyAll *) discriminate HU.
Qed.

(* ------------------------------------------------------------------ *)
(* Kernel-F<: narrowing for subtyping (now a theorem).                 *)
(*                                                                    *)
(* Replacing the bound of a type-variable binder by a *subtype*        *)
(* preserves any subtyping derivation under it.  We prove this by       *)
(* induction on the derivation, generalised over an arbitrary context   *)
(* prefix `Δ` so the binder cases (`SA_LtAll`/`SA_TyAll`) go through.   *)
(*                                                                    *)
(* Three context-level facts are needed:                               *)
(*   (a) lifetime subtyping is invariant under narrowing a `bind_ty`    *)
(*       (proved: `ctx_lookup_lt` skips `bind_ty` entries),             *)
(*   (b) general (no-shift) weakening of `<::` — for the `SA_VarCtx`    *)
(*       case when the looked-up variable *is* the narrowed one,        *)
(*   (c) `lt_of_ty_G` is monotone under narrowing — narrowing a bound   *)
(*       to a subtype can only shrink the computed `lt_∅`.              *)
(* (b) and (c) are standard de Bruijn / lattice facts kept axiomatic,   *)
(* in the same spirit as `sub_weaken_ty`; everything else is proved.    *)
(* ------------------------------------------------------------------ *)

(* (a.0) `ctx_lookup_lt` ignores the narrowed `bind_ty` slot. *)
Lemma ctx_lookup_lt_narrow : forall Δ Γ Bsup Bsub x,
  ctx_lookup_lt (Δ ++ bind_ty Bsub :: Γ) x
  = ctx_lookup_lt (Δ ++ bind_ty Bsup :: Γ) x.
Proof.
  induction Δ as [|b Δ' IH]; intros Γ Bsup Bsub x; simpl.
  - reflexivity.
  - destruct b; simpl.
    all: try apply IH.
    (* bind_lt remains *)
    destruct x; [reflexivity | rewrite (IH Γ Bsup Bsub x); reflexivity].
Qed.

(* (a.1) Lifetime subtyping only depends on the lt-lookup function. *)
Lemma lt_sub_lookup_eq : forall G1 l1 l2,
  G1 ⊢ₗ l1 <: l2 ->
  forall G2, (forall x, ctx_lookup_lt G1 x = ctx_lookup_lt G2 x) ->
  G2 ⊢ₗ l1 <: l2.
Proof.
  intros G1 l1 l2 H.
  induction H; intros G2 Heq.
  - apply LS_Free.
  - apply LS_Local.
  - apply LS_Var. rewrite <- (Heq x). exact H.
  - apply LS_Refl.
  - eapply LS_Trans; eauto.
  - apply LS_MinL; eauto.
  - apply LS_MinR1; eauto.
  - apply LS_MinR2; eauto.
Qed.

(* (a) Lifetime subtyping is invariant under narrowing a `bind_ty`. *)
Lemma lt_sub_narrow : forall Δ Γ Bsup Bsub l1 l2,
  (Δ ++ bind_ty Bsup :: Γ) ⊢ₗ l1 <: l2 ->
  (Δ ++ bind_ty Bsub :: Γ) ⊢ₗ l1 <: l2.
Proof.
  intros Δ Γ Bsup Bsub l1 l2 H.
  eapply lt_sub_lookup_eq; [exact H |].
  intros x. symmetry. apply ctx_lookup_lt_narrow.
Qed.

(* `ctx_lookup_ty` either is unchanged by narrowing or hits the slot.   *)
(* When it hits the slot, both lookups return the *same* shift `s` of   *)
(* the respective bound (the path to the binder is identical in both    *)
(* contexts, so the accumulated shift is identical).                    *)
Lemma ctx_lookup_ty_narrow : forall Δ Γ Bsup Bsub α,
  (ctx_lookup_ty (Δ ++ bind_ty Bsub :: Γ) α
     = ctx_lookup_ty (Δ ++ bind_ty Bsup :: Γ) α)
  \/ (exists s, ctx_lookup_ty (Δ ++ bind_ty Bsup :: Γ) α = Some (s Bsup)
             /\ ctx_lookup_ty (Δ ++ bind_ty Bsub :: Γ) α = Some (s Bsub)).
Proof.
  induction Δ as [|b Δ' IH]; intros Γ Bsup Bsub α; simpl.
  - destruct α.
    + right. exists (shift_ty 1 0). split; reflexivity.
    + left. reflexivity.
  - destruct b; simpl; try apply IH.
    + (* bind_ty *)
      destruct α; [left; reflexivity | ].
      destruct (IH Γ Bsup Bsub α) as [Heq | [s [H1 H2]]].
      * left. rewrite Heq. reflexivity.
      * right. exists (fun T => shift_ty 1 0 (s T)).
        rewrite H1, H2. split; reflexivity.
    + (* bind_lt *)
      destruct (IH Γ Bsup Bsub α) as [Heq | [s [H1 H2]]].
      * left. rewrite Heq. reflexivity.
      * right. exists (fun T => shift_lt_in_ty 1 0 (s T)).
        rewrite H1, H2. split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Lattice helper: `lt_min` is monotone in both arguments.             *)
(* ------------------------------------------------------------------ *)
Lemma lt_min_mono : forall G a a' b b',
  G ⊢ₗ a <: a' -> G ⊢ₗ b <: b' -> G ⊢ₗ lt_min a b <: lt_min a' b'.
Proof.
  intros G a a' b b' Ha Hb.
  apply LS_MinL.
  - eapply LS_Trans; [exact Ha | apply LS_MinR1; apply LS_Refl].
  - eapply LS_Trans; [exact Hb | apply LS_MinR2; apply LS_Refl].
Qed.

(* ------------------------------------------------------------------ *)
(* `lt_of_ty_ctx` is monotone in its fuel argument: with more fuel,    *)
(* type-variable chains are resolved further, which can only *raise*   *)
(* the computed lifetime (chains that run out of fuel bottom out at    *)
(* `lt_free`, the lattice bottom).                                     *)
(* ------------------------------------------------------------------ *)
Lemma lt_of_ty_ctx_fuel_mono_S : forall f G T,
  G ⊢ₗ lt_of_ty_ctx f G T <: lt_of_ty_ctx (S f) G T.
Proof.
  induction f as [|f' IHf]; intros G T.
  - (* f = 0 -> 1 *)
    induction T using type_list_ind with
      (Q := fun Ts => G ⊢ₗ lt_of_ty_ctx_list 0 G Ts <: lt_of_ty_ctx_list 1 G Ts).
    + (* var: LHS bottoms out at lt_free *)
      rewrite (lt_of_ty_ctx_var 0). apply LS_Free.
    + rewrite !lt_of_ty_ctx_fun. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_ctor. apply lt_min_mono; [apply LS_Refl | exact IHT].
    + rewrite !lt_of_ty_ctx_ltall. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_tyall. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_list_cons. apply lt_min_mono; [exact IHT | exact IHT0].
  - (* f = S f' -> S (S f') *)
    induction T using type_list_ind with
      (Q := fun Ts =>
              G ⊢ₗ lt_of_ty_ctx_list (S f') G Ts <: lt_of_ty_ctx_list (S (S f')) G Ts).
    + rewrite (lt_of_ty_ctx_var (S f')), (lt_of_ty_ctx_var (S (S f'))).
      destruct (ctx_lookup_ty G n) as [B|].
      * apply IHf.
      * apply LS_Refl.
    + rewrite !lt_of_ty_ctx_fun. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_ctor. apply lt_min_mono; [apply LS_Refl | exact IHT].
    + rewrite !lt_of_ty_ctx_ltall. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_tyall. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_list_cons. apply lt_min_mono; [exact IHT | exact IHT0].
Qed.

Lemma lt_of_ty_ctx_fuel_mono : forall f1 f2 G T,
  f1 <= f2 ->
  G ⊢ₗ lt_of_ty_ctx f1 G T <: lt_of_ty_ctx f2 G T.
Proof.
  intros f1 f2 G T Hle. induction Hle.
  - apply LS_Refl.
  - eapply LS_Trans; [exact IHHle | apply lt_of_ty_ctx_fuel_mono_S].
Qed.

(* ------------------------------------------------------------------ *)
(* `lt_of_ty_ctx` is monotone under subtyping (fixed context), as long *)
(* as the fuel does not exceed the context length (so the `SA_Any`     *)
(* premise, stated at fuel `|G|`, can be transported down via fuel     *)
(* monotonicity).                                                      *)
(* ------------------------------------------------------------------ *)
Lemma lt_of_ty_ctx_mono_sub : forall f G S T,
  G ⊢ S <:: T ->
  f <= List.length G ->
  G ⊢ₗ lt_of_ty_ctx f G S <: lt_of_ty_ctx f G T.
Proof.
  intros f G S T Hsub. revert f.
  induction Hsub; intros f Hf.
  - (* SA_Refl *) apply LS_Refl.
  - (* SA_Trans *) eapply LS_Trans; [apply IHHsub1 | apply IHHsub2]; exact Hf.
  - (* SA_VarCtx *)
    rewrite (lt_of_ty_ctx_var f). destruct f as [|f'].
    + apply LS_Free.
    + rewrite H. apply lt_of_ty_ctx_fuel_mono_S.
  - (* SA_Data *)
    rewrite !lt_of_ty_ctx_ctor. apply lt_min_mono; [exact H | apply LS_Refl].
  - (* SA_Any *)
    (* lt_of_ty_ctx f Γ T <: Δ <: lt_of_ty_ctx f Γ (any Δ []).          *)
    unfold lt_of_ty_G in H.
    eapply LS_Trans.
    + eapply LS_Trans; [ apply lt_of_ty_ctx_fuel_mono; exact Hf | exact H ].
    + rewrite lt_of_ty_ctx_ctor. apply LS_MinR1. apply LS_Refl.
  - (* SA_Fun *) destruct f as [|f']; simpl; assumption.
  - (* SA_LtAll *) destruct f as [|f']; simpl; apply LS_Refl.
  - (* SA_TyAll *) destruct f as [|f']; simpl; apply LS_Refl.
Qed.

(* ------------------------------------------------------------------ *)
(* (b) sub_weaken_cons / sub_weaken_app are now in SubstitutionTheory.v *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* (c) Narrowing a `bind_ty` bound to a subtype.  Now fully proved via  *)
(* the `NarrowTy` relation, resting only on the (proved) shifting        *)
(* weakening lemmas `sub_weaken_ty_shift` / `sub_weaken_lt_shift`.       *)
(* ------------------------------------------------------------------ *)

(* `G` is the wider (sup) context, `G'` the narrowed (sub) context. *)
Inductive NarrowTy : type -> type -> ctx -> ctx -> Prop :=
| NT_here : forall Bsub Bsup Γ,
    Γ ⊢ Bsub <:: Bsup ->
    NarrowTy Bsub Bsup (bind_ty Bsup :: Γ) (bind_ty Bsub :: Γ)
| NT_ty : forall Bsub Bsup G G' A,
    NarrowTy Bsub Bsup G G' ->
    NarrowTy Bsub Bsup (bind_ty A :: G) (bind_ty A :: G')
| NT_lt : forall Bsub Bsup G G' D,
    NarrowTy Bsub Bsup G G' ->
    NarrowTy Bsub Bsup (bind_lt D :: G) (bind_lt D :: G').

Lemma NT_length : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' -> length G = length G'.
Proof. intros Bsub Bsup G G' H. induction H; simpl; lia. Qed.

(* lt-lookups are unchanged by narrowing a `bind_ty` slot *)
Lemma NT_lookup_lt : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall x, ctx_lookup_lt G x = ctx_lookup_lt G' x.
Proof.
  intros Bsub Bsup G G' H. induction H; intro x.
  - simpl. reflexivity.
  - simpl. apply IHNarrowTy.
  - destruct x as [|x']; simpl.
    + reflexivity.
    + rewrite (IHNarrowTy x'). reflexivity.
Qed.

Lemma lt_sub_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall l1 l2, G ⊢ₗ l1 <: l2 -> G' ⊢ₗ l1 <: l2.
Proof.
  intros Bsub Bsup G G' HN l1 l2 H.
  eapply lt_sub_lookup_eq; [exact H |].
  intros x. apply (NT_lookup_lt Bsub Bsup G G' HN x).
Qed.

(* ty-lookup narrowing: the narrowed bound is a subtype, in both ctxs *)
Lemma NT_lookup_sub : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall α U, ctx_lookup_ty G α = Some U ->
    exists U', ctx_lookup_ty G' α = Some U'
            /\ G ⊢ U' <:: U
            /\ G' ⊢ U' <:: U.
Proof.
  intros Bsub Bsup G G' H. induction H; intros α U Hlk.
  - (* NT_here *) destruct α as [|n].
    + simpl in Hlk. injection Hlk; intros; subst U.
      exists (shift_ty 1 0 Bsub). split; [reflexivity|]. split.
      * apply (sub_weaken_ty_shift Γ Bsup Bsub Bsup H).
      * apply (sub_weaken_ty_shift Γ Bsub Bsub Bsup H).
    + exists U. split; [exact Hlk | split; apply SA_Refl].
  - (* NT_ty *) destruct α as [|n].
    + simpl in Hlk. injection Hlk; intros; subst U.
      exists (shift_ty 1 0 A). simpl. split; [reflexivity|]. split; apply SA_Refl.
    + simpl in Hlk. destruct (ctx_lookup_ty G n) as [W|] eqn:E; simpl in Hlk;
        [|discriminate].
      injection Hlk; intros; subst U.
      destruct (IHNarrowTy n W E) as [W' [HW' [HsubG HsubG']]].
      exists (shift_ty 1 0 W'). simpl. rewrite HW'. simpl.
      split; [reflexivity|]. split.
      * apply (sub_weaken_ty_shift G A W' W HsubG).
      * apply (sub_weaken_ty_shift G' A W' W HsubG').
  - (* NT_lt *) simpl in Hlk.
    destruct (ctx_lookup_ty G α) as [W|] eqn:E; simpl in Hlk; [|discriminate].
    injection Hlk; intros; subst U.
    destruct (IHNarrowTy α W E) as [W' [HW' [HsubG HsubG']]].
    exists (shift_lt_in_ty 1 0 W'). simpl. rewrite HW'. simpl.
    split; [reflexivity|]. split.
    + apply (sub_weaken_lt_shift G D W' W HsubG).
    + apply (sub_weaken_lt_shift G' D W' W HsubG').
Qed.

Lemma NT_lookup_None : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall α, ctx_lookup_ty G α = None -> ctx_lookup_ty G' α = None.
Proof.
  intros Bsub Bsup G G' H. induction H; intros α Hlk.
  - destruct α as [|n]; simpl in *.
    + discriminate.
    + destruct (ctx_lookup_ty Γ n) as [W|] eqn:E; simpl in Hlk; [discriminate|].
      reflexivity.
  - destruct α as [|n]; simpl in *.
    + discriminate.
    + destruct (ctx_lookup_ty G n) as [W|] eqn:E; simpl in Hlk; [discriminate|].
      rewrite (IHNarrowTy n E). reflexivity.
  - simpl in *.
    destruct (ctx_lookup_ty G α) as [W|] eqn:E; simpl in Hlk; [discriminate|].
    rewrite (IHNarrowTy α E). reflexivity.
Qed.

(* lt_of_ty_ctx is monotone under narrowing (computed lt_∅ can only shrink) *)
Lemma lt_of_ty_ctx_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall f T, f <= List.length G ->
    G' ⊢ₗ lt_of_ty_ctx f G' T <: lt_of_ty_ctx f G T.
Proof.
  intros Bsub Bsup G G' HN f.
  induction f as [|f' IHf]; intros T Hf.
  - (* f = 0 *)
    induction T using type_list_ind with
      (Q := fun Ts => G' ⊢ₗ lt_of_ty_ctx_list 0 G' Ts <: lt_of_ty_ctx_list 0 G Ts).
    + rewrite !(lt_of_ty_ctx_var 0). apply LS_Refl.
    + rewrite !lt_of_ty_ctx_fun. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_ctor. apply lt_min_mono; [apply LS_Refl | exact IHT].
    + rewrite !lt_of_ty_ctx_ltall. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_tyall. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_list_cons. apply lt_min_mono; [exact IHT | exact IHT0].
  - (* f = S f' *)
    assert (Hf' : f' <= List.length G) by lia.
    induction T using type_list_ind with
      (Q := fun Ts => G' ⊢ₗ lt_of_ty_ctx_list (S f') G' Ts <: lt_of_ty_ctx_list (S f') G Ts).
    + rewrite (lt_of_ty_ctx_var (S f') G' n), (lt_of_ty_ctx_var (S f') G n).
      destruct (ctx_lookup_ty G n) as [U|] eqn:E.
      * destruct (NT_lookup_sub Bsub Bsup G G' HN n U E) as [U' [HU' [HsubG HsubG']]].
        rewrite HU'.
        eapply LS_Trans.
        -- apply (IHf U' Hf').
        -- apply (lt_sub_NT Bsub Bsup G G' HN).
           apply (lt_of_ty_ctx_mono_sub f' G U' U HsubG Hf').
      * rewrite (NT_lookup_None Bsub Bsup G G' HN n E). apply LS_Refl.
    + rewrite !lt_of_ty_ctx_fun. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_ctor. apply lt_min_mono; [apply LS_Refl | exact IHT].
    + rewrite !lt_of_ty_ctx_ltall. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_tyall. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl.
    + rewrite !lt_of_ty_ctx_list_cons. apply lt_min_mono; [exact IHT | exact IHT0].
Qed.

Lemma lt_of_ty_G_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall T, G' ⊢ₗ lt_of_ty_G G' T <: lt_of_ty_G G T.
Proof.
  intros Bsub Bsup G G' HN T. unfold lt_of_ty_G.
  rewrite <- (NT_length Bsub Bsup G G' HN).
  apply (lt_of_ty_ctx_NT Bsub Bsup G G' HN (List.length G) T (Nat.le_refl _)).
Qed.

Lemma sub_NT : forall G S T, G ⊢ S <:: T ->
  forall Bsub Bsup G', NarrowTy Bsub Bsup G G' -> G' ⊢ S <:: T.
Proof.
  intros G S T H.
  induction H as [Γ T|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk|Γ K l l' Ts Hls
                 |Γ T Δ Hls|Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' H1 IH1 H2 IH2];
    intros Bsub Bsup G' HN.
  - apply SA_Refl.
  - eapply SA_Trans; [apply (IH1 _ _ _ HN) | apply (IH2 _ _ _ HN)].
  - destruct (NT_lookup_sub Bsub Bsup Γ G' HN α B Hlk) as [B' [HB' [_ HsubG']]].
    eapply SA_Trans; [apply SA_VarCtx; exact HB' | exact HsubG'].
  - apply SA_Data. apply (lt_sub_NT Bsub Bsup Γ G' HN _ _ Hls).
  - apply SA_Any.
    eapply LS_Trans.
    + apply (lt_of_ty_G_NT Bsub Bsup Γ G' HN T).
    + apply (lt_sub_NT Bsub Bsup Γ G' HN _ _ Hls).
  - apply SA_Fun.
    + apply (IH1 _ _ _ HN).
    + apply (lt_sub_NT Bsub Bsup Γ G' HN _ _ Hl).
    + apply (IH2 _ _ _ HN).
  - apply SA_LtAll.
    apply (IH1 Bsub Bsup (bind_lt lt_local :: G') (NT_lt Bsub Bsup Γ G' lt_local HN)).
  - apply SA_TyAll.
    + apply (IH1 _ _ _ HN).
    + apply (IH2 Bsub Bsup (bind_ty B' :: G') (NT_ty Bsub Bsup Γ G' B' HN)).
Qed.

Lemma sub_narrow_ty : forall Γ Bsub Bsup T1 T2,
  Γ ⊢ Bsub <:: Bsup ->
  (bind_ty Bsup :: Γ) ⊢ T1 <:: T2 ->
  (bind_ty Bsub :: Γ) ⊢ T1 <:: T2.
Proof.
  intros Γ Bsub Bsup T1 T2 Hb Hsub.
  apply (sub_NT (bind_ty Bsup :: Γ) T1 T2 Hsub Bsub Bsup (bind_ty Bsub :: Γ)).
  apply NT_here. exact Hb.
Qed.

(* Full inversion for `type_ty_all` supertypes, now a theorem: it       *)
(* recovers both the bound-subtyping witness (contravariant) and the    *)
(* body-subtyping witness (covariant, under the tighter bound).  The    *)
(* transitivity case composes the two body witnesses by narrowing the   *)
(* left one down to the common bound `B`.                               *)
Lemma sub_ty_all_inv_full : forall Γ S B T,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_ty_all B T ->
  exists B' T',
    S = type_ty_all B' T' /\
    Γ ⊢ B <:: B' /\
    (bind_ty B :: Γ) ⊢ T' <:: T.
Proof.
  intros Γ S B T Hec Hsub.
  remember (type_ty_all B T) as U eqn:HU.
  revert B T HU.
  induction Hsub; intros B0 T0 HU.
  - (* Refl *) inversion HU; subst.
    exists B0, T0. repeat split; auto.
  - (* Trans: S <:: U0 <:: type_ty_all B0 T0 *)
    subst T.
    destruct (IHHsub2 Hec _ _ eq_refl) as [Bm [Tm [HeqU [HBm HTm]]]]; subst.
    destruct (IHHsub1 Hec _ _ eq_refl) as [B' [T' [HeqS [HB' HT']]]]; subst.
    exists B', T'. repeat split; auto.
    + eapply SA_Trans; eauto.
    + eapply SA_Trans;
        [ eapply sub_narrow_ty; [ exact HBm | exact HT' ] | exact HTm ].
  - (* VarCtx *) subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - (* Data *) discriminate HU.
  - (* Any *) discriminate HU.
  - (* Fun *) discriminate HU.
  - (* LtAll *) discriminate HU.
  - (* TyAll *) injection HU; intros; subst.
    eexists; eexists; repeat split; eauto.
Qed.

(* sub_subst_ty / sub_subst_lt are now in SubstitutionTheory.v.       *)

(* Replacing one stepping argument inside a well-typed constructor    *)
(* argument list preserves the per-element typing.  The per-element    *)
(* preservation comes from the `typing_ind2` IH packaged as the second *)
(* `Forall2` hypothesis below; this lemma is consumed in the T_Ctor    *)
(* case of `preservation`.                                            *)
Lemma ctor_args_preserve :
  forall Γ vsl t0 t0' tsr rho_fields,
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) (vsl ++ t0 :: tsr) rho_fields ->
  Forall2 (fun v rho => eval_ctx Γ -> forall v', v ==> v' -> Γ ⊢ₜ v' : rho)
          (vsl ++ t0 :: tsr) rho_fields ->
  eval_ctx Γ ->
  t0 ==> t0' ->
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) (vsl ++ t0' :: tsr) rho_fields.
Proof.
  intros Γ vsl. induction vsl as [| a vsl' IHvsl];
    intros t0 t0' tsr rho_fields HF HFP Hec Hstep; simpl in *.
  - apply f2_uncons_l in HF.
    destruct HF as [rho0 [rest [Erf [Hhd Htl]]]]. subst rho_fields.
    apply f2_uncons_l in HFP.
    destruct HFP as [rho0' [rest' [Erf' [HPhd HPtl]]]].
    injection Erf'; intros; subst rho0' rest'.
    constructor.
    + apply HPhd; assumption.
    + exact Htl.
  - apply f2_uncons_l in HF.
    destruct HF as [rho0 [rest [Erf [Hhd Htl]]]]. subst rho_fields.
    apply f2_uncons_l in HFP.
    destruct HFP as [rho0' [rest' [Erf' [HPhd HPtl]]]].
    injection Erf'; intros; subst rho0' rest'.
    constructor.
    + exact Hhd.
    + eapply IHvsl with (t0 := t0); eassumption.
Qed.

(* ================================================================== *)
(* Variance soundness for `elim_ty` / `elim_lt`                       *)
(*                                                                    *)
(* This is the central meta-theoretic lemma that justifies eliminating *)
(* fresh lifetime variables from a match-branch result type:           *)
(*                                                                    *)
(*   Provided eta has no invariant occurrence of the eliminated var,   *)
(*   substituting any concrete witness l_0 (with l_0 <: Δ) yields a    *)
(*   subtype of `elim_ty 0 Δ var_pos eta`.                              *)
(*                                                                    *)
(* The proof goes by mutual structural induction on the eliminated     *)
(* type/lifetime, simultaneously varying the variance position.        *)
(* Auxiliary mechanical de Bruijn lemmas are axiomatized: subtyping    *)
(* monotonicity under shift / single-var lt-substitution.             *)
(* ================================================================== *)

(* Mechanical de Bruijn helpers (shift_subst_lt_comm,                 *)
(* subst_lt_in_ty_ctor_eq, sub_weaken_ty) are now in                  *)
(* SubstitutionTheory.v.                                              *)

(* --- Single-step elim soundness for lifetimes --- *)
(* Frame: lvar is the var being eliminated.  Result lives after the    *)
(* binder is closed, which we model by composing with `subst_lt lvar   *)
(* lt_free` on the elim output (this decrements vars ≥ S lvar to       *)
(* match what `subst_lt lvar l_0` does on the original).               *)

Lemma elim_lt_step_sound : forall l lvar bound p l',
  elim_lt lvar bound p l = Some l' ->
  forall Γ l_0,
    Γ ⊢ₗ l_0 <: subst_lt lvar lt_free bound ->
    match p with
    | var_pos => Γ ⊢ₗ subst_lt lvar l_0 l <: subst_lt lvar lt_free l'
    | var_neg => Γ ⊢ₗ subst_lt lvar lt_free l' <: subst_lt lvar l_0 l
    | var_inv => subst_lt lvar lt_free l' = subst_lt lvar l_0 l
    end.
Proof.
  induction l as [n | | | l1 IHl1 l2 IHl2]; intros lvar bound p l' Helim Γ l_0 Hsub; simpl in Helim.
  - (* lt_var n *)
    destruct (Nat.eqb n lvar) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst n.
      destruct p; try discriminate Helim.
      * injection Helim; intros; subst l'.
        simpl. rewrite Nat.eqb_refl. assumption.
      * injection Helim; intros; subst l'.
        simpl. rewrite Nat.eqb_refl. apply LS_Free.
    + injection Helim; intros; subst l'.
      destruct p; simpl; rewrite Heq; try apply LS_Refl;
      destruct (Nat.ltb lvar n); reflexivity.
  - (* lt_free *)
    injection Helim; intros; subst l'.
    destruct p; simpl; try apply LS_Refl. reflexivity.
  - (* lt_local *)
    injection Helim; intros; subst l'.
    destruct p; simpl; try apply LS_Refl. reflexivity.
  - (* lt_min *)
    destruct (elim_lt lvar bound p l1) as [l1'|] eqn:E1; try discriminate.
    destruct (elim_lt lvar bound p l2) as [l2'|] eqn:E2; try discriminate.
    injection Helim; intros; subst l'.
    specialize (IHl1 _ _ _ _ E1 _ _ Hsub).
    specialize (IHl2 _ _ _ _ E2 _ _ Hsub).
    destruct p; simpl.
    + apply LS_MinL; [apply LS_MinR1 | apply LS_MinR2]; assumption.
    + apply LS_MinL; [apply LS_MinR1 | apply LS_MinR2]; assumption.
    + f_equal; assumption.
Qed.

(* --- Custom type induction principle providing per-element IH      *)
(*     for the list-of-types in `type_ctor`.                          *)
Section TypeInd.
  Variable P : type -> Prop.
  Hypotheses
    (Hvar  : forall n, P (type_var n))
    (Hfun  : forall A l B, P A -> P B -> P (type_fun A l B))
    (Hctor : forall K l Ts, Forall P Ts -> P (type_ctor K l Ts))
    (Hltall: forall A, P A -> P (type_lt_all A))
    (Htyall: forall B A, P B -> P A -> P (type_ty_all B A)).

  Fixpoint type_ind' (T : type) : P T :=
    match T with
    | type_var n        => Hvar n
    | type_fun A l B    => Hfun A l B (type_ind' A) (type_ind' B)
    | type_ctor K l Ts  =>
        Hctor K l Ts
          ((fix go (Ts : list type) : Forall P Ts :=
            match Ts return Forall P Ts with
            | []     => Forall_nil _
            | A :: r => Forall_cons _ (type_ind' A) (go r)
            end) Ts)
    | type_lt_all A     => Hltall A (type_ind' A)
    | type_ty_all B A   => Htyall B A (type_ind' B) (type_ind' A)
    end.
End TypeInd.

Fixpoint elim_ty_list (lvar : nat) (bound : lifetime) (p : variance) (Ts : list type)
    : option (list type) :=
  match Ts with
  | [] => Some []
  | A :: rest =>
      match elim_ty lvar bound p A, elim_ty_list lvar bound p rest with
      | Some A', Some rest' => Some (A' :: rest')
      | _, _ => None
      end
  end.

Lemma elim_ty_list_eq_worker : forall lvar bound p Ts,
  (fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
     match Ts0 with
     | [] => Some []
     | A :: rest =>
         match elim_ty lvar bound p' A, go_list p' rest with
         | Some A', Some rest' => Some (A' :: rest')
         | _, _ => None
         end
     end) p Ts = elim_ty_list lvar bound p Ts.
Proof.
  intros lvar bound p Ts. induction Ts as [|A rest IH]; simpl.
  - reflexivity.
  - destruct (elim_ty lvar bound p A); simpl; [rewrite IH |]; reflexivity.
Qed.

Lemma elim_ty_ctor_eq : forall lvar bound p K l Ts,
  elim_ty lvar bound p (type_ctor K l Ts)
  = match elim_lt lvar bound p l, elim_ty_list lvar bound var_inv Ts with
    | Some l', Some Ts' => Some (type_ctor K l' Ts')
    | _, _ => None
    end.
Proof.
  intros lvar bound p K l Ts. simpl.
  rewrite elim_ty_list_eq_worker. reflexivity.
Qed.

(* --- Single-step elim soundness for types --- *)
Lemma elim_ty_step_sound : forall T lvar bound p T',
  elim_ty lvar bound p T = Some T' ->
  forall Γ l_0,
    Γ ⊢ₗ l_0 <: subst_lt lvar lt_free bound ->
    match p with
    | var_pos => Γ ⊢ subst_lt_in_ty lvar l_0 T <:: subst_lt_in_ty lvar lt_free T'
    | var_neg => Γ ⊢ subst_lt_in_ty lvar lt_free T' <:: subst_lt_in_ty lvar l_0 T
    | var_inv => subst_lt_in_ty lvar lt_free T' = subst_lt_in_ty lvar l_0 T
    end.
Proof.
  apply (type_ind'
    (fun T => forall lvar bound p T',
      elim_ty lvar bound p T = Some T' ->
      forall Γ l_0,
        Γ ⊢ₗ l_0 <: subst_lt lvar lt_free bound ->
        match p with
        | var_pos => Γ ⊢ subst_lt_in_ty lvar l_0 T <:: subst_lt_in_ty lvar lt_free T'
        | var_neg => Γ ⊢ subst_lt_in_ty lvar lt_free T' <:: subst_lt_in_ty lvar l_0 T
        | var_inv => subst_lt_in_ty lvar lt_free T' = subst_lt_in_ty lvar l_0 T
        end)); intros.
  - simpl in H. injection H; intros; subst T'. destruct p; simpl; try apply SA_Refl; reflexivity.
  - simpl in H1.
    destruct (elim_ty lvar bound (flip_var p) A) as [A'|] eqn:HA; try discriminate.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; try discriminate.
    destruct (elim_ty lvar bound p B) as [B'|] eqn:HB; try discriminate.
    injection H1; intros; subst T'.
    match goal with
    | Hsub0 : Γ ⊢ₗ l_0 <: subst_lt lvar lt_free bound |- _ => pose proof Hsub0 as Hsub
    end.
    destruct p; simpl.
    + apply SA_Fun.
      * exact (H lvar bound var_neg A' HA Γ l_0 Hsub).
      * pose proof (elim_lt_step_sound l lvar bound var_pos l' Hl Γ l_0 Hsub) as Hlt.
        simpl in Hlt. exact Hlt.
      * exact (H0 lvar bound var_pos B' HB Γ l_0 Hsub).
    + apply SA_Fun.
      * exact (H lvar bound var_pos A' HA Γ l_0 Hsub).
      * pose proof (elim_lt_step_sound l lvar bound var_neg l' Hl Γ l_0 Hsub) as Hlt.
        simpl in Hlt. exact Hlt.
      * exact (H0 lvar bound var_neg B' HB Γ l_0 Hsub).
    + f_equal.
      * exact (H lvar bound var_inv A' HA Γ l_0 Hsub).
      * pose proof (elim_lt_step_sound l lvar bound var_inv l' Hl Γ l_0 Hsub) as Hlt.
        simpl in Hlt. exact Hlt.
      * exact (H0 lvar bound var_inv B' HB Γ l_0 Hsub).
  - rewrite elim_ty_ctor_eq in H0.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; try discriminate.
    destruct (elim_ty_list lvar bound var_inv Ts) as [Ts'|] eqn:HTs; try discriminate.
    injection H0; intros; subst T'.
    match goal with
    | Hsub0 : Γ ⊢ₗ l_0 <: subst_lt lvar lt_free bound |- _ => pose proof Hsub0 as Hsub
    end.
    assert (Hlist : List.map (subst_lt_in_ty lvar lt_free) Ts' =
                    List.map (subst_lt_in_ty lvar l_0) Ts).
    { clear Hl l' p H0.
      revert Ts' HTs.
      induction H as [|A rest HPA HForall IHForall]; intros Ts' HTs; simpl in HTs.
      - injection HTs; intros; subst Ts'. reflexivity.
      - destruct (elim_ty lvar bound var_inv A) as [A'|] eqn:HAelim; try discriminate.
        destruct (elim_ty_list lvar bound var_inv rest) as [rest'|] eqn:HRest; try discriminate.
        injection HTs; intros; subst Ts'. simpl. f_equal.
        + exact (HPA lvar bound var_inv A' HAelim Γ l_0 Hsub).
        + apply IHForall. reflexivity.
    }
    destruct p; rewrite !subst_lt_in_ty_ctor_eq; simpl.
    + rewrite Hlist. apply SA_Data.
      pose proof (elim_lt_step_sound l lvar bound var_pos l' Hl Γ l_0 Hsub) as Hlt.
      simpl in Hlt. exact Hlt.
    + rewrite Hlist. apply SA_Data.
      pose proof (elim_lt_step_sound l lvar bound var_neg l' Hl Γ l_0 Hsub) as Hlt.
      simpl in Hlt. exact Hlt.
    + pose proof (elim_lt_step_sound l lvar bound var_inv l' Hl Γ l_0 Hsub) as Hlt.
      simpl in Hlt. f_equal; assumption.
  - simpl in H0.
    destruct (elim_ty (S lvar) (shift_lt 1 0 bound) p A) as [A'|] eqn:HA; try discriminate.
    injection H0; intros; subst T'.
    match goal with
    | Hsub0 : Γ ⊢ₗ l_0 <: subst_lt lvar lt_free bound |- _ => pose proof Hsub0 as Hsub
    end.
    assert (Hsub' : (bind_lt lt_local :: Γ) ⊢ₗ shift_lt 1 0 l_0
                    <: subst_lt (S lvar) lt_free (shift_lt 1 0 bound)).
    { rewrite <- shift_subst_lt_comm.
      apply (lt_sub_InsLt Γ l_0 (subst_lt lvar lt_free bound) Hsub
               0 (bind_lt lt_local :: Γ) (InsLt_here _ _)). }
    destruct p; simpl.
    + apply SA_LtAll. exact (H (S lvar) (shift_lt 1 0 bound) var_pos A' HA
                              (bind_lt lt_local :: Γ) (shift_lt 1 0 l_0) Hsub').
    + apply SA_LtAll. exact (H (S lvar) (shift_lt 1 0 bound) var_neg A' HA
                              (bind_lt lt_local :: Γ) (shift_lt 1 0 l_0) Hsub').
    + f_equal. exact (H (S lvar) (shift_lt 1 0 bound) var_inv A' HA
                        (bind_lt lt_local :: Γ) (shift_lt 1 0 l_0) Hsub').
  - simpl in H1.
    destruct (elim_ty lvar bound (flip_var p) B) as [B'|] eqn:HB; try discriminate.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HA; try discriminate.
    injection H1; intros; subst T'.
    match goal with
    | Hsub0 : Γ ⊢ₗ l_0 <: subst_lt lvar lt_free bound |- _ => pose proof Hsub0 as Hsub
    end.
    destruct p; simpl.
    + apply SA_TyAll.
      * exact (H lvar bound var_neg B' HB Γ l_0 Hsub).
      * apply (H0 lvar bound var_pos A' HA (bind_ty (subst_lt_in_ty lvar lt_free B') :: Γ) l_0).
        apply (lt_sub_InsTy Γ l_0 (subst_lt lvar lt_free bound) Hsub
                 0 (bind_ty (subst_lt_in_ty lvar lt_free B') :: Γ) (InsTy_here _ _)).
    + apply SA_TyAll.
      * exact (H lvar bound var_pos B' HB Γ l_0 Hsub).
      * apply (H0 lvar bound var_neg A' HA (bind_ty (subst_lt_in_ty lvar l_0 B) :: Γ) l_0).
        apply (lt_sub_InsTy Γ l_0 (subst_lt lvar lt_free bound) Hsub
                 0 (bind_ty (subst_lt_in_ty lvar l_0 B) :: Γ) (InsTy_here _ _)).
    + f_equal.
      * exact (H lvar bound var_inv B' HB Γ l_0 Hsub).
      * exact (H0 lvar bound var_inv A' HA Γ l_0 Hsub).
Qed.

(* ================================================================== *)
(* Sound iterated-elim soundness (binder-removal reformulation).      *)
(*                                                                    *)
(* The old `elim_ty_n_sound` relied on `iter_subst_lt_in_ty_mono`,    *)
(* which is FALSE (lifetime-variable substitution is not monotone in  *)
(* the subtyping order under LS_Var).  We replace it with an          *)
(* over-approximate-in-context + peel construction that never needs   *)
(* monotonicity:                                                      *)
(*   1. `elim_in_ctx_sound`: over-approximate eta entirely in a       *)
(*      context with n fresh lt-binders (no witnesses), giving        *)
(*      eta <:: shift_lt_in_ty n 0 elim_result.                       *)
(*   2. `sub_peel_push_corr`: peel all n binders at once via SubstLt, *)
(*      sound because the context shrinks together with the shift.    *)
(* ================================================================== *)

(* Over-approximation context: n fresh lt-binders, each storing the   *)
(* bound shifted to live at its level (uniform lookup = shift_lt n).  *)
Fixpoint push_corr (n : nat) (Delta : lifetime) (G : ctx) : ctx :=
  match n with
  | O    => G
  | S n' => bind_lt (shift_lt n' 0 Delta) :: push_corr n' Delta G
  end.

Lemma push_corr_lookup0 : forall n' Delta G,
  ctx_lookup_lt (push_corr (S n') Delta G) 0 = Some (shift_lt (S n') 0 Delta).
Proof.
  intros n' Delta G. simpl. f_equal.
  rewrite shift_lt_fuse. reflexivity.
Qed.

(* --- In-context single-step elim soundness (no substitution) ------ *)
(* Mirrors elim_lt_step_sound/elim_ty_step_sound but keeps the        *)
(* eliminated variable in the context and discharges via LS_Var.      *)
Lemma elim_lt_step_ctx : forall l lvar bound p l' G,
  elim_lt lvar bound p l = Some l' ->
  ctx_lookup_lt G lvar = Some bound ->
  match p with
  | var_pos => G ⊢ₗ l <: l'
  | var_neg => G ⊢ₗ l' <: l
  | var_inv => l = l'
  end.
Proof.
  induction l as [n | | | l1 IHl1 l2 IHl2]; intros lvar bound p l' G Helim Hlk; simpl in Helim.
  - (* lt_var n *)
    destruct (Nat.eqb n lvar) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst n.
      destruct p; try discriminate Helim.
      * injection Helim; intros; subst l'. apply LS_Var. exact Hlk.
      * injection Helim; intros; subst l'. apply LS_Free.
    + injection Helim; intros; subst l'.
      destruct p; simpl; try apply LS_Refl. reflexivity.
  - injection Helim; intros; subst l'. destruct p; simpl; try apply LS_Refl. reflexivity.
  - injection Helim; intros; subst l'. destruct p; simpl; try apply LS_Refl. reflexivity.
  - destruct (elim_lt lvar bound p l1) as [l1'|] eqn:E1; try discriminate.
    destruct (elim_lt lvar bound p l2) as [l2'|] eqn:E2; try discriminate.
    injection Helim; intros; subst l'.
    specialize (IHl1 _ _ _ _ _ E1 Hlk).
    specialize (IHl2 _ _ _ _ _ E2 Hlk).
    destruct p; simpl.
    + apply LS_MinL; [apply LS_MinR1 | apply LS_MinR2]; assumption.
    + apply LS_MinL; [apply LS_MinR1 | apply LS_MinR2]; assumption.
    + f_equal; assumption.
Qed.

Lemma elim_ty_step_ctx : forall T lvar bound p T' G,
  elim_ty lvar bound p T = Some T' ->
  ctx_lookup_lt G lvar = Some bound ->
  match p with
  | var_pos => G ⊢ T <:: T'
  | var_neg => G ⊢ T' <:: T
  | var_inv => T = T'
  end.
Proof.
  apply (type_ind'
    (fun T => forall lvar bound p T' G,
      elim_ty lvar bound p T = Some T' ->
      ctx_lookup_lt G lvar = Some bound ->
      match p with
      | var_pos => G ⊢ T <:: T'
      | var_neg => G ⊢ T' <:: T
      | var_inv => T = T'
      end)).
  - (* type_var *)
    intros n lvar bound p T' G Helim Hlk. simpl in Helim.
    injection Helim; intros; subst T'. destruct p; simpl; try apply SA_Refl. reflexivity.
  - (* type_fun A l B *)
    intros A l B IHA IHB lvar bound p T' G Helim Hlk. simpl in Helim.
    destruct (elim_ty lvar bound (flip_var p) A) as [A'|] eqn:HA; try discriminate.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; try discriminate.
    destruct (elim_ty lvar bound p B) as [B'|] eqn:HB; try discriminate.
    injection Helim; intros; subst T'.
    destruct p; simpl.
    + apply SA_Fun.
      * exact (IHA lvar bound var_neg A' G HA Hlk).
      * exact (elim_lt_step_ctx l lvar bound var_pos l' G Hl Hlk).
      * exact (IHB lvar bound var_pos B' G HB Hlk).
    + apply SA_Fun.
      * exact (IHA lvar bound var_pos A' G HA Hlk).
      * exact (elim_lt_step_ctx l lvar bound var_neg l' G Hl Hlk).
      * exact (IHB lvar bound var_neg B' G HB Hlk).
    + f_equal.
      * exact (IHA lvar bound var_inv A' G HA Hlk).
      * exact (elim_lt_step_ctx l lvar bound var_inv l' G Hl Hlk).
      * exact (IHB lvar bound var_inv B' G HB Hlk).
  - (* type_ctor K l Ts *)
    intros K l Ts IHTs lvar bound p T' G Helim Hlk.
    rewrite elim_ty_ctor_eq in Helim.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; try discriminate.
    destruct (elim_ty_list lvar bound var_inv Ts) as [Ts'|] eqn:HTs; try discriminate.
    injection Helim; intros; subst T'.
    assert (Hlist : Ts' = Ts).
    { clear Helim Hl. revert Ts' HTs.
      induction IHTs as [|A rest HPA HFor IHFor]; intros Ts' HTs; simpl in HTs.
      - injection HTs; intros; subst Ts'. reflexivity.
      - destruct (elim_ty lvar bound var_inv A) as [A'|] eqn:HAe; try discriminate.
        destruct (elim_ty_list lvar bound var_inv rest) as [rest'|] eqn:HRe; try discriminate.
        injection HTs; intros; subst Ts'. f_equal.
        + symmetry. exact (HPA lvar bound var_inv A' G HAe Hlk).
        + apply IHFor; reflexivity. }
    subst Ts'.
    destruct p; simpl.
    + apply SA_Data. exact (elim_lt_step_ctx l lvar bound var_pos l' G Hl Hlk).
    + apply SA_Data. exact (elim_lt_step_ctx l lvar bound var_neg l' G Hl Hlk).
    + f_equal. exact (elim_lt_step_ctx l lvar bound var_inv l' G Hl Hlk).
  - (* type_lt_all A *)
    intros A IHA lvar bound p T' G Helim Hlk. simpl in Helim.
    destruct (elim_ty (S lvar) (shift_lt 1 0 bound) p A) as [A'|] eqn:HA; try discriminate.
    injection Helim; intros; subst T'.
    assert (Hlk' : ctx_lookup_lt (bind_lt lt_local :: G) (S lvar) = Some (shift_lt 1 0 bound)).
    { simpl. rewrite Hlk. reflexivity. }
    destruct p; simpl.
    + apply SA_LtAll. exact (IHA (S lvar) (shift_lt 1 0 bound) var_pos A' (bind_lt lt_local :: G) HA Hlk').
    + apply SA_LtAll. exact (IHA (S lvar) (shift_lt 1 0 bound) var_neg A' (bind_lt lt_local :: G) HA Hlk').
    + f_equal. exact (IHA (S lvar) (shift_lt 1 0 bound) var_inv A' (bind_lt lt_local :: G) HA Hlk').
  - (* type_ty_all B A *)
    intros B A IHB IHA lvar bound p T' G Helim Hlk. simpl in Helim.
    destruct (elim_ty lvar bound (flip_var p) B) as [B'|] eqn:HB; try discriminate.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HA; try discriminate.
    injection Helim; intros; subst T'.
    assert (HlkB : forall Bb, ctx_lookup_lt (bind_ty Bb :: G) lvar = Some bound).
    { intro Bb. simpl. exact Hlk. }
    destruct p; simpl.
    + apply SA_TyAll.
      * exact (IHB lvar bound var_neg B' G HB Hlk).
      * exact (IHA lvar bound var_pos A' (bind_ty B' :: G) HA (HlkB B')).
    + apply SA_TyAll.
      * exact (IHB lvar bound var_pos B' G HB Hlk).
      * exact (IHA lvar bound var_neg A' (bind_ty B :: G) HA (HlkB B)).
    + f_equal.
      * exact (IHB lvar bound var_inv B' G HB Hlk).
      * exact (IHA lvar bound var_inv A' G HA Hlk).
Qed.

(* --- Freshness: elim output has no free occurrence of the          *)
(*     eliminated variable.  Encoded via the self-referential         *)
(*     identity shift_lt 1 v (subst_lt v lt_free X) = X.              *)
Lemma elim_lt_closes : forall l lvar bound p l',
  elim_lt lvar bound p l = Some l' ->
  shift_lt 1 lvar (subst_lt lvar lt_free bound) = bound ->
  shift_lt 1 lvar (subst_lt lvar lt_free l') = l'.
Proof.
  induction l as [n | | | l1 IH1 l2 IH2]; intros lvar bound p l' Helim Hb; simpl in Helim.
  - destruct (Nat.eqb n lvar) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst n.
      destruct p; try discriminate Helim.
      * injection Helim; intros; subst l'. exact Hb.
      * injection Helim; intros; subst l'. reflexivity.
    + injection Helim; intros; subst l'. simpl. rewrite Heq.
      destruct (Nat.ltb lvar n) eqn:Hlt.
      * simpl. apply Nat.ltb_lt in Hlt.
        assert (Nat.leb lvar (Nat.pred n) = true) as Hle by (apply Nat.leb_le; lia).
        rewrite Hle. f_equal. lia.
      * simpl. apply Nat.ltb_ge in Hlt. apply Nat.eqb_neq in Heq.
        assert (Nat.leb lvar n = false) as Hle by (apply Nat.leb_gt; lia).
        rewrite Hle. reflexivity.
  - injection Helim; intros; subst l'. reflexivity.
  - injection Helim; intros; subst l'. reflexivity.
  - destruct (elim_lt lvar bound p l1) as [l1'|] eqn:E1; try discriminate.
    destruct (elim_lt lvar bound p l2) as [l2'|] eqn:E2; try discriminate.
    injection Helim; intros; subst l'. simpl. f_equal.
    + exact (IH1 lvar bound p l1' E1 Hb).
    + exact (IH2 lvar bound p l2' E2 Hb).
Qed.

Lemma elim_ty_closes : forall T lvar bound p T',
  elim_ty lvar bound p T = Some T' ->
  shift_lt 1 lvar (subst_lt lvar lt_free bound) = bound ->
  shift_lt_in_ty 1 lvar (subst_lt_in_ty lvar lt_free T') = T'.
Proof.
  apply (type_ind'
    (fun T => forall lvar bound p T',
      elim_ty lvar bound p T = Some T' ->
      shift_lt 1 lvar (subst_lt lvar lt_free bound) = bound ->
      shift_lt_in_ty 1 lvar (subst_lt_in_ty lvar lt_free T') = T')).
  - (* type_var *)
    intros n lvar bound p T' Helim Hb. simpl in Helim.
    injection Helim; intros; subst T'. reflexivity.
  - (* type_fun *)
    intros A l B IHA IHB lvar bound p T' Helim Hb. simpl in Helim.
    destruct (elim_ty lvar bound (flip_var p) A) as [A'|] eqn:HA; try discriminate.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; try discriminate.
    destruct (elim_ty lvar bound p B) as [B'|] eqn:HB; try discriminate.
    injection Helim; intros; subst T'.
    rewrite subst_lt_in_ty_fun_eq, shift_lt_in_ty_fun_eq. f_equal.
    + exact (IHA lvar bound (flip_var p) A' HA Hb).
    + exact (elim_lt_closes l lvar bound p l' Hl Hb).
    + exact (IHB lvar bound p B' HB Hb).
  - (* type_ctor *)
    intros K l Ts IHTs lvar bound p T' Helim Hb.
    rewrite elim_ty_ctor_eq in Helim.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; try discriminate.
    destruct (elim_ty_list lvar bound var_inv Ts) as [Ts'|] eqn:HTs; try discriminate.
    injection Helim; intros; subst T'.
    rewrite subst_lt_in_ty_ctor_eq, shift_lt_in_ty_ctor_eq. f_equal.
    + exact (elim_lt_closes l lvar bound p l' Hl Hb).
    + clear Helim Hl. rewrite List.map_map. revert Ts' HTs.
      induction IHTs as [|A rest HPA HFor IHFor]; intros Ts' HTs; simpl in HTs.
      * injection HTs; intros; subst Ts'. reflexivity.
      * destruct (elim_ty lvar bound var_inv A) as [A'|] eqn:HAe; try discriminate.
        destruct (elim_ty_list lvar bound var_inv rest) as [rest'|] eqn:HRe; try discriminate.
        injection HTs; intros; subst Ts'. simpl. f_equal.
        -- exact (HPA lvar bound var_inv A' HAe Hb).
        -- apply IHFor; reflexivity.
  - (* type_lt_all *)
    intros A IHA lvar bound p T' Helim Hb. simpl in Helim.
    destruct (elim_ty (S lvar) (shift_lt 1 0 bound) p A) as [A'|] eqn:HA; try discriminate.
    injection Helim; intros; subst T'.
    rewrite subst_lt_in_ty_ltall_eq, shift_lt_in_ty_ltall_eq. f_equal.
    apply (IHA (S lvar) (shift_lt 1 0 bound) p A' HA).
    rewrite <- shift_subst_lt_comm. rewrite <- shift_lt_swap_0. rewrite Hb. reflexivity.
  - (* type_ty_all *)
    intros B A IHB IHA lvar bound p T' Helim Hb. simpl in Helim.
    destruct (elim_ty lvar bound (flip_var p) B) as [B'|] eqn:HB; try discriminate.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HA; try discriminate.
    injection Helim; intros; subst T'.
    rewrite subst_lt_in_ty_tyall_eq, shift_lt_in_ty_tyall_eq. f_equal.
    + exact (IHB lvar bound (flip_var p) B' HB Hb).
    + exact (IHA lvar bound p A' HA Hb).
Qed.

(* --- Iterated elim soundness --- *)

(* iter_subst_lt_in_ty, chain_bounded and iter_subst_lt_in_ty_mono are *)
(* now in SubstitutionTheory.v.                                        *)

(* ================================================================== *)
(* Piece 5: over-approximate-in-context soundness.                    *)
(* Eliminating n positive binders, then over-approximating the        *)
(* eliminated variables by a context of n fresh lt-binders, yields    *)
(*   push_corr n Delta G ⊢ eta <:: shift_lt_in_ty n 0 elim_result.    *)
(* No witnesses (and hence no monotonicity) are required.             *)
(* ================================================================== *)
Lemma elim_in_ctx_sound : forall n Delta eta elim_result G,
  elim_ty_n n (shift_lt n 0 Delta) var_pos eta = Some elim_result ->
  push_corr n Delta G ⊢ eta <:: shift_lt_in_ty n 0 elim_result.
Proof.
  induction n as [|n' IH]; intros Delta eta elim_result G Helim.
  - (* n = 0 *)
    simpl in Helim. injection Helim; intros He; subst elim_result.
    simpl. rewrite shift_lt_in_ty_zero. apply SA_Refl.
  - (* n = S n' *)
    simpl in Helim.
    destruct (elim_ty 0 (shift_lt (S n') 0 Delta) var_pos eta) as [T1|] eqn:ET1;
      try discriminate.
    assert (Hb : subst_lt 0 lt_free (shift_lt (S n') 0 Delta) = shift_lt n' 0 Delta).
    { replace (shift_lt (S n') 0 Delta) with (shift_lt 1 0 (shift_lt n' 0 Delta))
        by (rewrite shift_lt_fuse; reflexivity).
      rewrite subst_lt_shift_cancel. reflexivity. }
    rewrite Hb in Helim.
    specialize (IH Delta (subst_lt_in_ty 0 lt_free T1) elim_result G Helim).
    pose proof (elim_ty_step_ctx eta 0 (shift_lt (S n') 0 Delta) var_pos T1
                  (push_corr (S n') Delta G) ET1 (push_corr_lookup0 n' Delta G)) as Hstep.
    simpl in Hstep.
    pose proof (sub_weaken_lt_shift (push_corr n' Delta G) (shift_lt n' 0 Delta)
                  (subst_lt_in_ty 0 lt_free T1) (shift_lt_in_ty n' 0 elim_result) IH) as Hweak.
    assert (Hfresh : shift_lt_in_ty 1 0 (subst_lt_in_ty 0 lt_free T1) = T1).
    { apply (elim_ty_closes eta 0 (shift_lt (S n') 0 Delta) var_pos T1 ET1).
      rewrite Hb. rewrite shift_lt_fuse. reflexivity. }
    rewrite Hfresh in Hweak.
    rewrite shift_lt_in_ty_fuse in Hweak.
    eapply SA_Trans; [exact Hstep | exact Hweak].
Qed.

(* ================================================================== *)
(* Piece 6: peel all n over-approximation binders at once.            *)
(* ================================================================== *)

(* 6a: weakening lifetime subtyping through the push_corr context.    *)
Lemma lt_sub_push_corr_weaken : forall n Delta Γ l1 l2,
  Γ ⊢ₗ l1 <: l2 ->
  push_corr n Delta Γ ⊢ₗ shift_lt n 0 l1 <: shift_lt n 0 l2.
Proof.
  induction n as [|n' IH]; intros Delta Γ l1 l2 Hsub.
  - cbn [push_corr]. rewrite !shift_lt_zero. exact Hsub.
  - cbn [push_corr].
    specialize (IH Delta Γ l1 l2 Hsub).
    pose proof (lt_sub_InsLt (push_corr n' Delta Γ) (shift_lt n' 0 l1) (shift_lt n' 0 l2) IH
                  0 (bind_lt (shift_lt n' 0 Delta) :: push_corr n' Delta Γ)
                  (InsLt_here (shift_lt n' 0 Delta) (push_corr n' Delta Γ))) as Hins.
    rewrite !shift_lt_fuse in Hins.
    exact Hins.
Qed.

(* 6b: peel all binders via SubstLt, sound because the context        *)
(*     shrinks together with each substitution.                       *)
Lemma sub_peel_push_corr : forall lts Delta A B Γ,
  Forall (fun l => Γ ⊢ₗ l <: Delta) lts ->
  push_corr (List.length lts) Delta Γ ⊢ A <:: B ->
  Γ ⊢ subst_list_lt_in_ty lts A <:: subst_list_lt_in_ty lts B.
Proof.
  induction lts as [|l0 rest IH]; intros Delta A B Γ Hfor Hsub.
  - cbn [subst_list_lt_in_ty]. cbn [List.length push_corr] in Hsub. exact Hsub.
  - pose proof (Forall_inv Hfor) as Hhead.
    pose proof (Forall_inv_tail Hfor) as Htail.
    cbn [List.length push_corr] in Hsub.
    cbn [subst_list_lt_in_ty].
    apply (IH Delta (subst_lt_in_ty 0 (shift_lt (List.length rest) 0 l0) A)
                    (subst_lt_in_ty 0 (shift_lt (List.length rest) 0 l0) B) Γ Htail).
    eapply sub_SubstLt.
    2: { apply SubstLt_here.
         exact (lt_sub_push_corr_weaken (List.length rest) Delta Γ l0 Delta Hhead). }
    exact Hsub.
Qed.

(* 6c: the over-approximation target shift-cancels under the peel.    *)
Lemma subst_list_lt_in_ty_shift_cancel : forall lts X,
  subst_list_lt_in_ty lts (shift_lt_in_ty (List.length lts) 0 X) = X.
Proof.
  induction lts as [|l0 rest IH]; intro X.
  - cbn [List.length subst_list_lt_in_ty]. rewrite shift_lt_in_ty_zero. reflexivity.
  - cbn [List.length subst_list_lt_in_ty].
    replace (shift_lt_in_ty (S (List.length rest)) 0 X)
      with (shift_lt_in_ty 1 0 (shift_lt_in_ty (List.length rest) 0 X))
      by (rewrite shift_lt_in_ty_fuse; reflexivity).
    rewrite subst_lt_in_ty_shift_cancel.
    apply IH.
Qed.

(* ================================================================== *)
(* Piece 7: sound positive iterated-elim soundness (assembly).        *)
(* Replaces the old `elim_ty_n_sound` (which depended on the FALSE    *)
(* `iter_subst_lt_in_ty_mono`).                                       *)
(* ================================================================== *)
Lemma elim_ty_n_sound_pos : forall n Delta lts eta elim_result Γ,
  elim_ty_n n (shift_lt n 0 Delta) var_pos eta = Some elim_result ->
  List.length lts = n ->
  Forall (fun l => Γ ⊢ₗ l <: Delta) lts ->
  Γ ⊢ subst_list_lt_in_ty lts eta <:: elim_result.
Proof.
  intros n Delta lts eta elim_result Γ Helim Hlen Hfor.
  subst n.
  pose proof (elim_in_ctx_sound (List.length lts) Delta eta elim_result Γ Helim) as Hctx.
  pose proof (sub_peel_push_corr lts Delta eta
                (shift_lt_in_ty (List.length lts) 0 elim_result) Γ Hfor Hctx) as Hpeel.
  rewrite subst_list_lt_in_ty_shift_cancel in Hpeel.
  exact Hpeel.
Qed.

(* The old `elim_ty_n_sound` (induction on the witness list, depending  *)
(* on the FALSE `iter_subst_lt_in_ty_mono`) has been removed and        *)
(* replaced by the sound `elim_ty_n_sound_pos` above.                   *)

(* The parallel-substitution preservation lemmas (subst_list_lt_in_ty_each, *)
(* subst_list_lt_in_tm_lemma, subst_list_tm_lemma,                     *)
(* subst_list_lt_in_ty_eq_iter, ctor_lts_chain_bounded,                *)
(* inst_ctor_type_subst_eq) are now                                    *)
(* in SubstitutionTheory.v.                                            *)

(* ------------------------------------------------------------------ *)
(* Inversion lemmas for T_Match and T_Ctor                            *)
(* ------------------------------------------------------------------ *)

Lemma match_typing_inv : forall Γ scrut K arity yes_body no_body T,
  Γ ⊢ₜ term_match scrut K arity yes_body no_body : T ->
  exists n_lt n_ty sigma_fields result_ty_schema Ts Delta scrut_result_ty
         result_tag result_l eta elim_result,
    K <> any_tag /\
    ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) /\
    ctx_lookup_eff Γ K = None /\
    List.length Ts = n_ty /\
    scrut_result_ty = inst_ctor_type n_lt n_ty (List.repeat Delta n_lt) Ts result_ty_schema /\
    scrut_result_ty = type_ctor result_tag result_l Ts /\
    result_tag <> any_tag /\
    Γ ⊢ₗ result_l <: Delta /\
    Γ ⊢ₜ scrut : type_ctor result_tag Delta Ts /\
    arity = List.length (List.map (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts) sigma_fields) /\
    (fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
                (push_lt_vars n_lt Delta Γ)
                (List.map (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts) sigma_fields))
       ⊢ₜ yes_body : eta /\
    elim_ty_n n_lt (shift_lt n_lt 0 Delta) var_pos eta = Some elim_result /\
    Γ ⊢ₜ no_body : elim_result /\
    Γ ⊢ elim_result <:: T.
Proof.
  intros Γ scrut K arity yes_body no_body T Hty.
  remember (term_match scrut K arity yes_body no_body) as t eqn:Ht.
  induction Hty; try discriminate.
  - (* T_Sub *) subst.
    destruct (IHHty eq_refl) as
      [n_lt [n_ty [sig [res [Ts0 [Delta0 [scrut_result_ty0
       [result_tag0 [result_l0 [eta0 [elim_r Hinv]]]]]]]]]]].
    destruct Hinv as
      [HK [Hlk [Heff [HTs [Hscrut_result [Hscrut_shape [Hresult_ne
       [Hresult_l [Hscrut [Har [Hbody [Helim [Hno Hsub]]]]]]]]]]]]].
    exists n_lt, n_ty, sig, res, Ts0, Delta0, scrut_result_ty0,
      result_tag0, result_l0, eta0, elim_r.
    repeat split; auto. eapply SA_Trans; eauto.
  - (* T_Match *)
    injection Ht; intros; subst.
    repeat eexists; repeat split; eauto.
    all: try match goal with
    | Hrho : ?rho = List.map _ ?sigma,
      Harity : ?arity0 = List.length ?rho
      |- ?arity0 = List.length (List.map _ ?sigma) =>
        rewrite Harity, Hrho; reflexivity
    end.
Qed.

Lemma ctor_typing_inv : forall Γ K l lts Ts vs T,
  Γ ⊢ₜ term_ctor K l lts Ts vs : T ->
  exists n_lt n_ty sigma_fields result_ty_schema result_tag,
    ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) /\
    List.length lts = n_lt /\
    List.length Ts = n_ty /\
    inst_ctor_type n_lt n_ty lts Ts result_ty_schema = type_ctor result_tag l Ts /\
    Γ ⊢ₗ lt_of_ty_list (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields) <: l /\
    List.length vs = List.length sigma_fields /\
    Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs
            (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields) /\
    Γ ⊢ type_ctor result_tag l Ts <:: T.
Proof.
  intros Γ K l lts Ts vs T Hty.
  remember (term_ctor K l lts Ts vs) as t eqn:Ht.
  induction Hty; try discriminate.
  - (* T_Sub *) subst.
    destruct (IHHty eq_refl) as
      (n_lt & n_ty & sig & res & result_tag &
       Hlk & Hltlen & HTslen & Hresult & Hlt & Hvslen & Hf2 & Hsub).
    exists n_lt, n_ty, sig, res, result_tag.
    repeat split; auto. eapply SA_Trans; eauto.
  - (* T_Ctor *)
    inversion Ht; subst.
    exists (List.length lts), (List.length Ts), sigma_fields, result_ty_schema, result_tag.
    repeat split; eauto; try reflexivity.
    + match goal with
      | Hlen : List.length vs = List.length (List.map _ sigma_fields) |- _ =>
          rewrite Hlen, List.length_map; reflexivity
      end.
    + match goal with
      | Hshape : inst_ctor_type (List.length lts) (List.length Ts) lts Ts result_ty_schema =
                 type_ctor result_tag l Ts |- _ =>
          rewrite Hshape; apply SA_Refl
      end.
Qed.

(* ------------------------------------------------------------------ *)
(* Match-yes preservation                                             *)
(* ------------------------------------------------------------------ *)

Lemma match_yes_preservation : forall Γ K Delta lts Ts vs arity yes_body no_body T,
  eval_ctx Γ ->
  Γ ⊢ₜ term_match (term_ctor K Delta lts Ts vs) K arity yes_body no_body : T ->
  Forall value vs ->
  arity = List.length vs ->
  Γ ⊢ₜ subst_list_tm vs (subst_list_lt_in_tm lts yes_body) : T.
Proof.
  intros Γ K Delta lts Ts vs arity yes_body no_body T Hec Hmatch Hvals Harity_vs.
  destruct (match_typing_inv _ _ _ _ _ _ _ Hmatch) as
    (n_lt & n_ty & sigma & result & Ts_m & Delta_m & scrut_result_ty &
     result_tag & result_l & eta & elim_result & Hinv).
  destruct Hinv as
    (HKne & Hctor_lk & Heff & HTs_len & Hscrut_result & Hscrut_shape &
     Hresult_ne & Hresult_l & Hscrut & Harity_sigma & Hyes & Helim & Hno & HsubT).
  simpl in Hscrut.
  destruct (ctor_typing_inv _ _ _ _ _ _ _ Hscrut) as
    [n_lt' [n_ty' [sigma' [result' [actual_result_tag Hctor_inv]]]]].
  destruct Hctor_inv as
    [Hctor_lk' [Hlts_len [HTs_len_actual [Hactual_result [Hactual_lifetime [Hvs_len [Hfields Hctor_sub]]]]]]].
  rewrite Hctor_lk in Hctor_lk'. injection Hctor_lk' as Hnlt Hnty Hsigma Hresult.
  subst n_lt' n_ty' sigma' result'.
  destruct (sub_ctor_inv _ _ _ _ _ Hec Hctor_sub Hresult_ne) as [Delta0 [Hctor_eq HDelta_sub]].
  injection Hctor_eq as HDelta_eq HTs_eq. subst Delta0 Ts_m.
  assert (Harity_vs_len : List.length vs = List.length sigma) by lia.
  destruct (ctor_lts_chain_bounded Γ lts n_lt n_ty Ts sigma vs
              (lt_of_ty_list (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma)) Delta_m
              Hfields Hlts_len eq_refl
              (LS_Trans _ _ _ _ Hactual_lifetime HDelta_sub)) as
    [Hcb [Hcb_shift [Hbounded_fields Hforall]]].
  assert (Hlt_body :
    (fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
       Γ (subst_list_lt_in_ty_each lts (List.map (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts) sigma)))
      ⊢ₜ subst_list_lt_in_tm lts yes_body : subst_list_lt_in_ty lts eta).
  { eapply (subst_list_lt_in_tm_lemma Γ
              (List.map (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts) sigma)
              n_lt Delta_m lts yes_body eta);
      [exact Hlts_len | exact Hcb | exact Hyes]. }
  rewrite (inst_ctor_type_subst_eq n_lt n_ty lts Ts sigma Hlts_len Hbounded_fields) in Hlt_body.
  assert (Htm_body : Γ ⊢ₜ subst_list_tm vs (subst_list_lt_in_tm lts yes_body) : subst_list_lt_in_ty lts eta).
  { eapply (subst_list_tm_lemma Γ vs
              (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma)
              (subst_list_lt_in_tm lts yes_body) (subst_list_lt_in_ty lts eta)).
    - rewrite List.length_map. exact Hvs_len.
    - exact Hvals.
    - exact Hfields.
    - exact Hlt_body. }
  eapply T_Sub; [exact Htm_body|].
  eapply SA_Trans.
  - exact (elim_ty_n_sound_pos n_lt Delta_m lts eta elim_result Γ Helim Hlts_len Hforall).
  - exact HsubT.
Qed.

Theorem preservation : forall Γ t t' T,
  eval_ctx Γ ->
  Γ ⊢ₜ t : T ->
  t ==> t' ->
  Γ ⊢ₜ t' : T.
Proof.
  intros Γ0 t0 t'0 T0 Hec0 Hty0 Hstep0.
  revert Hstep0; revert t'0; revert Hec0.
  revert Hty0; revert T0; revert t0; revert Γ0.
  apply (typing_ind2
           (fun Γ t T => eval_ctx Γ -> forall t', t ==> t' -> Γ ⊢ₜ t' : T)).
  - (* T_Var *)
    intros Γ x T Hlk Hec t'' Hstep. no_step.
  - (* T_Sub *)
    intros Γ t T U Ht IH Hsub Hec t'' Hstep.
    specialize (IH Hec).
    eapply T_Sub; [ apply IH; exact Hstep | exact Hsub ].
  - (* T_Lam *)
    intros Γ body A l B Hbody IHbody Hcap Hnl Hec t'' Hstep. no_step.
  - (* T_App *)
    intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 Hec t'' Hstep.
    specialize (IH1 Hec); specialize (IH2 Hec).
    apply step_app_inv in Hstep.
    destruct Hstep as [(body0 & T0 & v0 & E1 & E2 & Hv0 & E3)
                      | [ (m0 & b0 & v0 & E1 & E2 & Hv0 & E3)
                      | [ (t1' & Hs1 & E3) | (t2' & Hv1 & Hs2 & E3) ]]].
    + (* S_Beta *)
      subst t1 t2 t''.
      apply lam_typing_inv in Ht1.
      destruct Ht1 as [l' [B' [Hbody Hsub]]].
      destruct (sub_fun_inv _ _ _ _ _ Hec Hsub)
        as [A'' [l'' [B'' [HeqT [HAsub [Hlsub HBsub]]]]]].
      injection HeqT; intros; subst.
      eapply T_Sub; [| exact HBsub].
      eapply subst_tm_lemma; [exact Hbody| exact Hv0 |].
      eapply T_Sub; [exact Ht2 | exact HAsub].
    + (* S_Resume *)
      subst t1 t2 t''.
      apply resume_typing_inv in Ht1.
      destruct Ht1 as [A' [B' [Hbody Hsub]]].
      destruct (sub_fun_inv _ _ _ _ _ Hec Hsub)
        as [A'' [l'' [B'' [HeqT [HAsub [Hlsub HBsub]]]]]].
      injection HeqT; intros; subst.
      apply T_HandlerM.
      eapply T_Sub; [| exact HBsub].
      eapply subst_tm_lemma; [exact Hbody| exact Hv0 |].
      eapply T_Sub; [exact Ht2 | exact HAsub].
    + subst t''. eapply T_App; eauto.
    + subst t''. eapply T_App; eauto.
  - (* T_TyLam *)
    intros Γ bound body T Hbody IHbody Hec t'' Hstep. no_step.
  - (* T_TyApp *)
    intros Γ t B U S Ht IH Hsub Hec t'' Hstep.
    specialize (IH Hec).
    apply step_ty_app_inv in Hstep.
    destruct Hstep as [(bound0 & body0 & E1 & E2) | (t0' & Hs & E2)].
    + (* S_TyBeta *)
      subst t t''.
      apply ty_lam_typing_inv in Ht.
      destruct Ht as [U0 [Hbody Hsub']].
      destruct (sub_ty_all_inv_full _ _ _ _ Hec Hsub')
        as [B0 [U1 [HeqU [HBsub Hsubbody]]]].
      injection HeqU; intros; subst.
      eapply T_Sub.
      * eapply subst_ty_in_tm_lemma; [exact Hbody|]. eapply SA_Trans; eauto.
      * eapply sub_subst_ty; eauto.
    + subst t''. eapply T_TyApp; eauto.
  - (* T_LtLam *)
    intros Γ body T Hbody IHbody Hec t'' Hstep. no_step.
  - (* T_LtApp *)
    intros Γ t T l Ht IH Hec t'' Hstep.
    specialize (IH Hec).
    apply step_lt_app_inv in Hstep.
    destruct Hstep as [(body0 & E1 & E2) | (t0' & Hs & E2)].
    + (* S_LtBeta *)
      subst t t''.
      apply lt_lam_typing_inv in Ht.
      destruct Ht as [U0 [Hbody Hsub']].
      destruct (sub_lt_all_inv_full _ _ _ Hec Hsub') as [U1 [HeqU Hsubbody]].
      injection HeqU; intros; subst.
      eapply T_Sub.
      * eapply subst_lt_in_tm_lemma; [exact Hbody|]. apply LS_Local.
      * eapply sub_subst_lt; [exact Hsubbody | apply LS_Local].
    + subst t''. eapply T_LtApp; eauto.
  - (* T_Ctor *)
      intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
        result_ty result_tag l vs
        Hlk Heff Hlen_lts Hrho Hlen_Ts Hresult Hshape Hlt Hlen_vs HF HFP Hec t'' Hstep.
    apply step_ctor_inv in Hstep.
    destruct Hstep as (vs0 & t0 & t0' & tsr0 & Hvs0 & Eargs & Hs0 & Et).
    subst t''.
    rewrite Eargs in HF, HFP, Hlen_vs.
    assert (HF' : Forall2 (fun v rho => Γ ⊢ₜ v : rho)
                          (vs0 ++ t0' :: tsr0) rho_fields).
    { eapply ctor_args_preserve;
        [ exact HF | exact HFP | exact Hec | exact Hs0 ]. }
    eapply T_Ctor; try eassumption.
    assert (Hlen' : @length term (vs0 ++ t0' :: tsr0)
                  = @length term (vs0 ++ t0 :: tsr0)).
    { rewrite !List.length_app. reflexivity. }
    rewrite Hlen'. exact Hlen_vs.
  - (* T_Match *)
    intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l
           Γ' yes_body eta elim_result no_body
           HKne Hlk Heff Hlts Hrho HTs Hscrut_result Hscrut_shape Hresult_ne
           Hresult_l Hscrut IHscrut Harity HGamma' Hyes IHyes Helim Hno IHno
           Hec t'' Hstep.
    apply step_match_inv in Hstep.
    destruct Hstep as
      [ (K0 & l0 & lts0 & Ts0 & vs0 & Es & Hvs0 & Ear & EK & Et)
      | [ (K0' & l0 & lts0 & Ts0 & vs0 & Es & Hvs0 & Hne & Et)
        | (s' & Hs & Et) ]].
    + (* S_MatchYes *)
      subst K0 scrut arity t''.
      eapply match_yes_preservation; eauto.
    + (* S_MatchNo *) subst t''. exact Hno.
    + (* S_Match *)
      subst t''. specialize (IHscrut Hec). eapply T_Match; eauto.
  - (* T_Cap *)
    intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff Hlen Hsb Hrb Hop IHop Hec t'' Hstep. no_step.
  - (* T_Handle *)
    intros Γ E_tag Ts op_body body n_α n_β sig ret T_R sig_β ret_β
           Heff Hlen Hsb Hrb Hop IHop Hbody IHbody Hec t'' Hstep.
    rewrite eval_ctx_no_eff in Heff; auto; discriminate.
  - (* T_Perform *)
    intros Γ recv arg E_tag Δ Ts Ss n_α n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hlen_Ts Hlen_Ss Hsi Hri Harg IHarg Hec t'' Hstep.
    rewrite eval_ctx_no_eff in Heff; auto; discriminate.
  - (* T_HandlerM *)
    intros Γ m t T Ht IH Hec t'' Hstep.
    specialize (IH Hec).
    apply step_handler_m_inv in Hstep.
    destruct Hstep as
      [(Hv & Et)
      | [(t' & Hs & Et)
      | (E_tag & Ts & op_body & Ss & v & Pr & Hv & Hpe & Edec & Et)]].
    + (* H_Return *) subst t''. exact Ht.
    + (* S_HandlerM *) subst t''. apply T_HandlerM. apply IH; assumption.
    + (* H_Perform *)
      exfalso. subst t.
      eapply no_typed_perform_cap_under_eval_ctx; eauto.
  - (* T_Resume *)
    intros Γ m b A T_R Hb IHb Hec t'' Hstep. no_step.
Qed.

(* ------------------------------------------------------------------ *)
(* Type Safety corollary                                              *)
(* ------------------------------------------------------------------ *)

Inductive multi_step : term -> term -> Prop :=
  | MS_Refl : forall t, multi_step t t
  | MS_Step : forall t1 t2 t3,
      t1 ==> t2 -> multi_step t2 t3 -> multi_step t1 t3.

Definition stuck (t : term) : Prop :=
  ~ value t /\ ~ exists t', t ==> t'.

Corollary type_safety : forall Γ t t' T,
  eval_ctx Γ ->
  Γ ⊢ₜ t : T ->
  multi_step t t' ->
  ~ stuck t'.
Proof.
  intros Γ t t' T Hec Hty Hmulti.
  induction Hmulti as [t | t1 t2 t3 Hs12 Hmulti IH].
  - intros [Hnv Hns].
    destruct (progress _ _ _ Hec Hty) as [Hv | [t'' Hs]]; [contradiction|].
    apply Hns; eauto.
  - apply IH. eapply preservation; eauto.
Qed.

(* ================================================================== *)
(*                                                                    *)
(*                NON-ESCAPING OF LOCAL VALUES                        *)
(*                                                                    *)
(* The lifetime lattice places `lt_free` at the bottom and            *)
(* `lt_local` at the top, with subtyping oriented `free <: local`.    *)
(* A value annotated `local` is confined to its scope: it may be      *)
(* *used where* a `local` value is expected, but it must never flow   *)
(* the other way, into a position demanding a `free` (escapable)      *)
(* lifetime.                                                          *)
(*                                                                    *)
(* The formal content of "local values do not escape" is therefore    *)
(* that subtyping can never relax a `local` lifetime down to `free`:  *)
(* the lattice fact `local <: free` is underivable in *every*         *)
(* context, and consequently a `local`-annotated datum can never be   *)
(* coerced (by subsumption) to its `free` counterpart.                *)
(* ================================================================== *)

(* The boolean `no_local_lt` (defined in Typing.v) is a *downward     *)
(* closed* invariant of the lifetime-subtyping order: if a supertype  *)
(* has no top-level `local`, then neither does any of its subtypes.   *)
(* This is the monotonicity engine behind non-escaping.               *)
Lemma lt_sub_no_local_mono : forall Γ l1 l2,
  Γ ⊢ₗ l1 <: l2 ->
  no_local_lt l2 = true ->
  no_local_lt l1 = true.
Proof.
  intros Γ l1 l2 H. induction H; intros Hsup; simpl in *.
  - (* LS_Free  : free <: l   — free has no local *) reflexivity.
  - (* LS_Local : l <: local  — supertype IS local, premise absurd *)
    discriminate Hsup.
  - (* LS_Var   : lt_var x <: Δ — a bare var has no top-level local *)
    reflexivity.
  - (* LS_Refl  *) exact Hsup.
  - (* LS_Trans *) apply IHlt_sub1. apply IHlt_sub2. exact Hsup.
  - (* LS_MinL  : lt_min l1 l2 <: l *)
    rewrite (IHlt_sub1 Hsup). rewrite (IHlt_sub2 Hsup). reflexivity.
  - (* LS_MinR1 : l <: lt_min l1 l2 *)
    apply IHlt_sub.
    destruct (no_local_lt l1) eqn:E1; simpl in Hsup; [reflexivity | discriminate].
  - (* LS_MinR2 : l <: lt_min l1 l2 *)
    apply IHlt_sub.
    destruct (no_local_lt l2) eqn:E2;
      [reflexivity | destruct (no_local_lt l1); simpl in Hsup; discriminate].
Qed.

(* Lattice form: the top lifetime `local` never outlives the bottom   *)
(* `free`.  Holds in *any* context (no `eval_ctx` needed): even       *)
(* context-bounded lt-variables cannot bridge `local` to `free`.      *)
Theorem lt_local_not_escapes : forall Γ,
  ~ (Γ ⊢ₗ lt_local <: lt_free).
Proof.
  intros Γ H.
  pose proof (lt_sub_no_local_mono _ _ _ H (eq_refl : no_local_lt lt_free = true))
    as Hcontra.
  simpl in Hcontra. discriminate.
Qed.

(* Value/type form: a `local`-annotated data value can never be       *)
(* subsumed to the same data carrying `free`.  This is the            *)
(* "no escape via subtyping" theorem for local values.               *)
Theorem local_data_not_escapes : forall Γ K Ts,
  eval_ctx Γ ->
  K <> any_tag ->
  ~ (Γ ⊢ type_ctor K lt_local Ts <:: type_ctor K lt_free Ts).
Proof.
  intros Γ K Ts Hec HK H.
  destruct (sub_ctor_inv _ _ _ _ _ Hec H HK) as [l' [Heq Hlsub]].
  injection Heq as Hl'. subst l'.
  exact (lt_local_not_escapes _ Hlsub).
Qed.

(* ================================================================== *)
(*                                                                    *)
(*           OPERATIONAL NON-ESCAPE OF LOCAL VALUES                   *)
(*                                                                    *)
(* The lattice/subtyping theorems above forbid *coercing* a `local`   *)
(* datum to `free`.  Transported along the dynamics they deliver the  *)
(* operational guarantee: whatever value a closed program computes    *)
(* at an escapable (`free`) data type is itself annotated with a      *)
(* lifetime that carries no top-level `local`.  A `local`-confined    *)
(* datum can never surface as the result delivered at a `free` type.  *)
(* ================================================================== *)

(* Typing is preserved along an entire reduction sequence. *)
Lemma multi_preservation : forall Γ t t' T,
  eval_ctx Γ ->
  Γ ⊢ₜ t : T ->
  multi_step t t' ->
  Γ ⊢ₜ t' : T.
Proof.
  intros Γ t t' T Hec Hty Hms.
  induction Hms as [t | t1 t2 t3 Hs12 Hms IH].
  - exact Hty.
  - apply IH. eapply preservation; eauto.
Qed.

(* Operational non-escape: a value produced at an escapable `free`    *)
(* data type is a constructor whose *own* lifetime annotation         *)
(* provably contains no top-level `local`.  Equivalently, a value     *)
(* confined to a `local` lifetime is never the result a program       *)
(* hands back at a `free` (escapable) type.                           *)
Theorem local_value_does_not_escape : forall Γ t K Ts v,
  eval_ctx Γ ->
  K <> any_tag ->
  Γ ⊢ₜ t : type_ctor K lt_free Ts ->
  multi_step t v ->
  value v ->
  exists K' l' lts' vs,
    v = term_ctor K' l' lts' Ts vs /\
    no_local_lt l' = true.
Proof.
  intros Γ t K Ts v Hec HK Hty Hms Hval.
  pose proof (multi_preservation _ _ _ _ Hec Hty Hms) as Htyv.
  destruct (canonical_ctor _ _ _ _ _ Hec Htyv Hval HK)
    as [K' [l' [lts' [Ts' [vs [Hveq Hvs]]]]]].
  subst v.
  apply ctor_typing_inv in Htyv.
  destruct Htyv as
    (n_lt & n_ty & sig & res & result_tag & Hlk & Hltlen & HTslen & Hresult &
     Hlt_bound & Hvslen & Hf2 & Hsub).
  destruct (sub_ctor_inv _ _ _ _ _ Hec Hsub HK) as [lx [Heq Hlsub]].
  injection Heq as HKeq Hleq HTseq.
  subst result_tag. subst Ts'.
  exists K', l', lts', vs. split; [reflexivity|].
  rewrite Hleq.
  apply (lt_sub_no_local_mono _ _ _ Hlsub).
  reflexivity.
Qed.

(* ================================================================== *)
(*                                                                    *)
(*                   CAPABILITY CONFINEMENT                           *)
(*                                                                    *)
(* A runtime capability `cap_E^m _ _` is the only construct whose      *)
(* typing rule (`T_Cap`) consults the effect environment: it is       *)
(* well-typed solely in a context that *binds* the effect tag `E`.    *)
(* Capabilities are minted exclusively by `H_Handle`, which wraps     *)
(* each one immediately inside its own `handler_m m` delimiter        *)
(*   handle …  -->h  handler_m m (… cap_E^m …).                       *)
(* In the program-level evaluation scenario the ambient context is an *)
(* `eval_ctx` (no `bind_eff`), so a capability can never inhabit a    *)
(* typed evaluation position: every evaluation context surrounding a  *)
(* (well-typed) capability must pass through its handler.             *)
(* ================================================================== *)

(* Core confinement.  Because `plug E _` types its hole in the *same* *)
(* context (ectx frames introduce no binders), a capability in the    *)
(* hole would force its effect tag into Γ — impossible under          *)
(* `eval_ctx`.  The conclusion is the strongest possible: no such     *)
(* configuration is even well-typed.                                  *)
Theorem capability_confined : forall Γ E E_tag m Ts op_body T,
  eval_ctx Γ ->
  Γ ⊢ₜ plug E (term_cap E_tag m Ts op_body) : T ->
  False.
Proof.
  intros Γ E E_tag m Ts op_body T Hec Hty.
  apply plug_typing_inv in Hty. destruct Hty as [T' Hty].
  apply cap_typed_eff_some in Hty.
  destruct Hty as [n_α [n_β [sig0 [ret Hlk]]]].
  rewrite (eval_ctx_no_eff _ E_tag Hec) in Hlk. discriminate.
Qed.

(* Operational form.  A closed well-typed program never reduces to a  *)
(* configuration that exposes a capability at an evaluation position. *)
Theorem capability_never_exposed : forall Γ t E E_tag m Ts op_body T,
  eval_ctx Γ ->
  Γ ⊢ₜ t : T ->
  multi_step t (plug E (term_cap E_tag m Ts op_body)) ->
  False.
Proof.
  intros Γ t E E_tag m Ts op_body T Hec Hty Hms.
  pose proof (multi_preservation _ _ _ _ Hec Hty Hms) as Hty'.
  eapply capability_confined; eauto.
Qed.

(* The user-facing phrasing: if a closed program does reach `E[cap]`, *)
(* then `E` is *not* delimiter-free for the capability's marker `m` — *)
(* i.e. a matching `handler_m m` always lies above the hole.  (It     *)
(* holds a fortiori, the premise being unreachable in this model.)    *)
Corollary capability_under_handler : forall Γ t E E_tag m Ts op_body T,
  eval_ctx Γ ->
  Γ ⊢ₜ t : T ->
  multi_step t (plug E (term_cap E_tag m Ts op_body)) ->
  ~ pure_ectx_m m E.
Proof.
  intros Γ t E E_tag m Ts op_body T Hec Hty Hms _.
  eapply capability_never_exposed; eauto.
Qed.
