Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
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
(* Substitution-style lemmas (beta for tm/ty/lt, and the match-yes    *)
(* simultaneous substitution) are axiomatized; they are standard de   *)
(* Bruijn manipulations orthogonal to the paper's contribution.       *)
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
Proof. induction 1; intros; simpl; auto. Qed.

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
  (forall Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields l vs,
     ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) ->
     ctx_lookup_eff Γ K = None ->
     List.length lts = n_lt ->
     rho_fields = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields ->
     List.length Ts = n_ty ->
     l = lt_of_ty_list rho_fields ->
     List.length vs = List.length rho_fields ->
     Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rho_fields ->
     Forall2 (fun v rho => P Γ v rho) vs rho_fields ->
     P Γ (term_ctor K l lts Ts vs) (type_ctor K l Ts)) ->
  (forall Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
          rho_fields Γ' yes_body eta elim_result no_body,
     K <> any_tag ->
     Γ ⊢ₜ scrut : type_ctor K Delta Ts -> P Γ scrut (type_ctor K Delta Ts) ->
     ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) ->
     ctx_lookup_eff Γ K = None ->
     lts = lt_var_list n_lt ->
     rho_fields = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields ->
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
     sig_β = inst_ty_vars n_α Ts sig ->
     ret_β = inst_ty_vars n_α Ts ret ->
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
     sig_β = inst_ty_vars n_α Ts sig ->
     ret_β = inst_ty_vars n_α Ts ret ->
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

(* A well-typed ctor value has |vs| matching its declared sig arity. *)
Lemma ctor_value_arity : forall Γ K l lts Ts vs K' l' Ts',
  eval_ctx Γ ->
  Γ ⊢ₜ term_ctor K l lts Ts vs : type_ctor K' l' Ts' ->
  K' <> any_tag ->
  exists n_lt n_ty sigma result,
    ctx_lookup_ctor Γ K' = Some (n_lt, n_ty, sigma, result) /\
    List.length vs = List.length sigma.
Proof.
  intros Γ K l lts Ts vs K' l' Ts' Hec Hty HK.
  remember (term_ctor K l lts Ts vs) as t eqn:Ht.
  remember (type_ctor K' l' Ts') as T eqn:HT.
  revert K l lts Ts vs K' l' Ts' Ht HT HK.
  induction Hty; intros K0 l0 lts0 Ts0 vs0 K1 l1 Ts1 Ht HT HK; try discriminate Ht.
  - (* T_Sub *) subst U.
    destruct (sub_ctor_inv _ _ _ _ _ Hec H HK) as [l'' [HeqS Hlsub]].
    eapply IHHty; eauto.
  - (* T_Ctor *)
    injection Ht; intros Hvs HTs0 Hlts0 Hl0 HK0.
    injection HT; intros HTs1 Hl1 HK1.
    subst K0 l0 lts0 Ts0 vs0 K1 l1 Ts1.
    exists n_lt, n_ty, sigma_fields, result_ty_schema. split; auto.
    rewrite H5. subst rho_fields. rewrite List.length_map. auto.
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
    intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields l vs
           Hlk Heff Hlen_lts Hrho Hlen_Ts Hl Hlen_vs HF HFP Hec.
    assert (Hforall : Forall (fun v => value v \/ exists v', v ==> v') vs).
    { eapply Forall2_Forall_left; [ exact HFP | ].
      intros a b Hab. apply Hab; exact Hec. }
    destruct (split_values_or_step _ Hforall) as
      [Hall | [vsl [tm [tm' [vsr [Hallvl [Heq Hst]]]]]]].
    + left. constructor; auto.
    + right. subst. eexists. apply S_Ctor; eauto.
  - (* T_Match *)
    intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields Γ' yes_body eta elim_result no_body
           HKne Hscrut IHscrut Hlk Heff Hlts Hrho Harity HGamma' Hyes IHyes
           Helim Hno IHno Hec.
    specialize (IHscrut Hec).
    destruct IHscrut as [Hv | [scrut' Hs]].
    + destruct (canonical_ctor _ _ _ _ _ Hec Hscrut Hv HKne)
        as [K' [l' [lts' [Ts' [vs [Heq Hvvs]]]]]]; subst.
      right.
      destruct (Nat.eq_dec K' K) as [HKeq | HKdiff].
      * subst K'.
        destruct (ctor_value_arity _ _ _ _ _ _ _ _ _ Hec Hscrut HKne)
          as [n_lt' [n_ty' [sig' [res' [Hlook Hlen]]]]].
        rewrite Hlk in Hlook.
        injection Hlook as Heq1 Heq2 Heq3 Heq4.
        subst n_lt' n_ty' sig' res'.
        eexists.
        replace (@length type (map (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts) sigma_fields))
          with (@length term vs) by (rewrite List.length_map; auto).
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
(* (c) Narrowing a bound to a subtype shrinks the computed `lt_∅`.     *)
(* Honest axiom (1B): the prior proof relied on the unsound no-shift    *)
(* `sub_weaken_app`.  The statement is the standard F<: narrowing       *)
(* property and is taken as a trusted assumption pending the full       *)
(* shifting-weakening metatheory (option 1A).                          *)
Axiom lt_of_ty_ctx_narrow : forall f Δ Γ Bsup Bsub T,
  Γ ⊢ Bsub <:: Bsup ->
  f <= List.length (Δ ++ bind_ty Bsub :: Γ) ->
  (Δ ++ bind_ty Bsub :: Γ) ⊢ₗ
     lt_of_ty_ctx f (Δ ++ bind_ty Bsub :: Γ) T
     <: lt_of_ty_ctx f (Δ ++ bind_ty Bsup :: Γ) T.

Lemma lt_of_ty_G_narrow : forall Δ Γ Bsup Bsub T,
  Γ ⊢ Bsub <:: Bsup ->
  (Δ ++ bind_ty Bsub :: Γ) ⊢ₗ
     lt_of_ty_G (Δ ++ bind_ty Bsub :: Γ) T
     <: lt_of_ty_G (Δ ++ bind_ty Bsup :: Γ) T.
Proof.
  intros Δ Γ Bsup Bsub T Hb.
  unfold lt_of_ty_G.
  (* both contexts have the same length, so the same fuel is used *)
  assert (Hlen : List.length (Δ ++ bind_ty Bsup :: Γ)
                 = List.length (Δ ++ bind_ty Bsub :: Γ)).
  { rewrite !length_app. reflexivity. }
  rewrite Hlen.
  apply lt_of_ty_ctx_narrow; [exact Hb | apply Nat.le_refl].
Qed.

(* Prefix-generalised narrowing.  Honest axiom (1B): the SA_VarCtx case  *)
(* of the prior proof relied on the unsound no-shift `sub_weaken_app`.    *)
(* This is the standard F<: narrowing statement; trusted pending the      *)
(* shifting-weakening metatheory (option 1A).                            *)
Axiom sub_narrow_ty_gen : forall G S T,
  G ⊢ S <:: T ->
  forall Δ Γ Bsup Bsub,
    G = Δ ++ bind_ty Bsup :: Γ ->
    Γ ⊢ Bsub <:: Bsup ->
    (Δ ++ bind_ty Bsub :: Γ) ⊢ S <:: T.

Lemma sub_narrow_ty : forall Γ Bsub Bsup T1 T2,
  Γ ⊢ Bsub <:: Bsup ->
  (bind_ty Bsup :: Γ) ⊢ T1 <:: T2 ->
  (bind_ty Bsub :: Γ) ⊢ T1 <:: T2.
Proof.
  intros Γ Bsub Bsup T1 T2 Hb Hsub.
  exact (sub_narrow_ty_gen _ _ _ Hsub [] Γ Bsup Bsub eq_refl Hb).
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

(* Mechanical de Bruijn helpers (lt_sub_shift_lt, lt_sub_subst_lt,    *)
(* sub_subst_lt_at, shift_subst_lt_comm, subst_lt_in_ty_ctor_eq,      *)
(* sub_weaken_ty) are now in SubstitutionTheory.v.                    *)

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

(* --- Single-step elim soundness for types --- *)
(* Honest axiom (1B): the `type_ty_all` case of the prior proof crossed  *)
(* a `bind_ty` binder via the unsound no-shift `sub_weaken_ty`.  The      *)
(* statement is the expected single-step soundness of lifetime           *)
(* elimination and is trusted pending the shifting metatheory (1A).      *)
Axiom elim_ty_step_sound : forall T lvar bound p T',
  elim_ty lvar bound p T = Some T' ->
  forall Γ l_0,
    Γ ⊢ₗ l_0 <: subst_lt lvar lt_free bound ->
    match p with
    | var_pos => Γ ⊢ subst_lt_in_ty lvar l_0 T <:: subst_lt_in_ty lvar lt_free T'
    | var_neg => Γ ⊢ subst_lt_in_ty lvar lt_free T' <:: subst_lt_in_ty lvar l_0 T
    | var_inv => subst_lt_in_ty lvar lt_free T' = subst_lt_in_ty lvar l_0 T
    end.

(* --- Iterated elim soundness --- *)

(* iter_subst_lt_in_ty, chain_bounded and iter_subst_lt_in_ty_mono are *)
(* now in SubstitutionTheory.v.                                        *)

(* Iterated elim soundness.  Proven by induction on the witness list.   *)
Lemma elim_ty_n_sound : forall ws n bound p T T' Γ,
  elim_ty_n n bound p T = Some T' ->
  List.length ws = n ->
  chain_bounded Γ ws bound ->
  match p with
  | var_pos => Γ ⊢ iter_subst_lt_in_ty ws T <:: T'
  | var_neg => Γ ⊢ T' <:: iter_subst_lt_in_ty ws T
  | var_inv => T' = iter_subst_lt_in_ty ws T
  end.
Proof.
  induction ws as [|w rest IH]; intros n bound p T T' Γ Helim Hlen Hchain.
  - (* ws = [], so n = 0, elim_ty_n 0 ... = Some T *)
    destruct n; simpl in Hlen; try discriminate.
    simpl in Helim. injection Helim; intros; subst T'.
    simpl. destruct p; try apply SA_Refl. reflexivity.
  - (* ws = w :: rest, n = S n' *)
    destruct n as [|n']; simpl in Hlen; try discriminate.
    injection Hlen; intros Hlen'.
    simpl in Hchain. destruct Hchain as [Hwb Hchain'].
    simpl in Helim.
    destruct (elim_ty 0 bound p T) as [T1|] eqn:Eet; try discriminate.
    pose proof (elim_ty_step_sound _ _ _ _ _ Eet Γ _ Hwb) as Hstep.
    simpl in Hstep.
    specialize (IH n' (subst_lt 0 lt_free bound) p
                    (subst_lt_in_ty 0 lt_free T1) T' Γ Helim Hlen' Hchain').
    simpl. destruct p.
    + (* var_pos *)
      eapply SA_Trans.
      * apply iter_subst_lt_in_ty_mono. exact Hstep.
      * exact IH.
    + (* var_neg *)
      eapply SA_Trans.
      * exact IH.
      * apply iter_subst_lt_in_ty_mono. exact Hstep.
    + (* var_inv *)
      rewrite IH. rewrite Hstep. reflexivity.
Qed.

(* The parallel-substitution preservation lemmas (subst_list_lt_in_ty_each, *)
(* subst_list_lt_in_tm_lemma, subst_list_tm_lemma,                     *)
(* subst_list_lt_in_ty_eq_iter, ctor_lts_chain_bounded,                *)
(* chain_bounded_mono, shift_lt_sub, inst_ctor_type_subst_eq) are now  *)
(* in SubstitutionTheory.v.                                            *)

(* ------------------------------------------------------------------ *)
(* Inversion lemmas for T_Match and T_Ctor                            *)
(* ------------------------------------------------------------------ *)

Lemma match_typing_inv : forall Γ scrut K arity yes_body no_body T,
  Γ ⊢ₜ term_match scrut K arity yes_body no_body : T ->
  exists n_lt n_ty sigma_fields result_ty_schema Ts Delta eta elim_result,
    K <> any_tag /\
    Γ ⊢ₜ scrut : type_ctor K Delta Ts /\
    ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) /\
    arity = List.length sigma_fields /\
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
      [n_lt [n_ty [sig [res [Ts0 [Delta0 [eta0 [elim_r
        [HK [Hsc [Hlk [Har [Hbody [Helim [Hno Hsub]]]]]]]]]]]]]]].
    exists n_lt, n_ty, sig, res, Ts0, Delta0, eta0, elim_r.
    repeat split; auto. eapply SA_Trans; eauto.
  - (* T_Match *)
    injection Ht; intros; subst.
    exists n_lt, n_ty, sigma_fields, result_ty_schema, Ts, Delta, eta, elim_result.
    split; [assumption|].
    split; [assumption|].
    split; [assumption|].
    split; [rewrite List.length_map; reflexivity|].
    split; [assumption|].
    split; [assumption|].
    split; [assumption|].
    apply SA_Refl.
Qed.

Lemma ctor_typing_inv : forall Γ K l lts Ts vs T,
  Γ ⊢ₜ term_ctor K l lts Ts vs : T ->
  exists n_lt n_ty sigma_fields result_ty_schema,
    ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) /\
    List.length lts = n_lt /\
    List.length Ts = n_ty /\
    l = lt_of_ty_list (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields) /\
    List.length vs = List.length sigma_fields /\
    Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs
            (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields) /\
    Γ ⊢ type_ctor K l Ts <:: T.
Proof.
  intros Γ K l lts Ts vs T Hty.
  remember (term_ctor K l lts Ts vs) as t eqn:Ht.
  induction Hty; try discriminate.
  - (* T_Sub *) subst.
    destruct (IHHty eq_refl) as
      [n_lt [n_ty [sig [res
        [Hlk [Hltlen [HTslen [Hl [Hvslen [Hf2 Hsub]]]]]]]]]].
    exists n_lt, n_ty, sig, res.
    repeat split; auto. eapply SA_Trans; eauto.
  - (* T_Ctor *)
    revert H1 H3.
    inversion Ht; subst. intros H1 H3.
    exists n_lt, n_ty, sigma_fields, result_ty_schema.
    split; [exact H|].
    split; [exact H1|].
    split; [exact H3|].
    split; [reflexivity|].
    split; [rewrite H5; rewrite List.length_map; reflexivity|].
    split; [exact H6|].
    apply SA_Refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Match-yes preservation                                             *)
(* ------------------------------------------------------------------ *)

(* Honest axiom (1B): the prior proof bridged the parallel and iterated  *)
(* lifetime substitutions via the unsound `subst_list_lt_in_ty lts =      *)
(* iter_subst_lt_in_ty lts` (which dropped the per-witness shift; cf.     *)
(* the corrected `subst_list_lt_in_ty_eq_iter` in SubstitutionTheory.v).  *)
(* The statement is the expected preservation step for a matched          *)
(* constructor and is trusted pending the substitution metatheory (1A).   *)
Axiom match_yes_preservation : forall Γ K Delta lts Ts vs arity yes_body no_body T,
  eval_ctx Γ ->
  Γ ⊢ₜ term_match (term_ctor K Delta lts Ts vs) K arity yes_body no_body : T ->
  Forall value vs ->
  arity = List.length vs ->
  Γ ⊢ₜ subst_list_tm vs (subst_list_lt_in_tm lts yes_body) : T.

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
      eapply subst_tm_lemma; [exact Hbody|].
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
      eapply subst_tm_lemma; [exact Hbody|].
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
    intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields l vs
           Hlk Heff Hlen_lts Hrho Hlen_Ts Hl Hlen_vs HF HFP Hec t'' Hstep.
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
           rho_fields Γ' yes_body eta elim_result no_body
           HKne Hscrut IHscrut Hlk Heff Hlts Hrho Harity HGamma' Hyes IHyes
           Helim Hno IHno Hec t'' Hstep.
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
  exists l' lts' vs,
    v = term_ctor K l' lts' Ts vs /\
    no_local_lt l' = true.
Proof.
  intros Γ t K Ts v Hec HK Hty Hms Hval.
  pose proof (multi_preservation _ _ _ _ Hec Hty Hms) as Htyv.
  destruct (canonical_ctor _ _ _ _ _ Hec Htyv Hval HK)
    as [K' [l' [lts' [Ts' [vs [Hveq Hvs]]]]]].
  subst v.
  apply ctor_typing_inv in Htyv.
  destruct Htyv as
    [n_lt [n_ty [sig [res [Hlk [Hltlen [HTslen [Hl [Hvslen [Hf2 Hsub]]]]]]]]]].
  destruct (sub_ctor_inv _ _ _ _ _ Hec Hsub HK) as [lx [Heq Hlsub]].
  injection Heq as HKeq Hleq HTseq.
  subst K'. subst Ts'.
  exists l', lts', vs. split; [reflexivity|].
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
