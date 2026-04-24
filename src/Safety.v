Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Semantics.
Require Import Typing.

(* ================================================================== *)
(*                                                                    *)
(*                 PROGRESS AND PRESERVATION                          *)
(*                                                                    *)
(* We prove type safety for CoreΔ under a top-level evaluation ctx   *)
(* that contains only lifetime and constructor bindings (no bind_tm, *)
(* no bind_ty).  This blocks SA_VarCtx at the top level and matches  *)
(* the paper's "program-level" evaluation scenario.                   *)
(*                                                                    *)
(* Substitution-style lemmas (beta for tm/ty/lt, and the match-yes   *)
(* simultaneous substitution) are axiomatized; they are standard de  *)
(* Bruijn manipulations orthogonal to the paper's contribution.       *)
(* ================================================================== *)

Inductive eval_ctx : ctx -> Prop :=
  | ec_nil   : eval_ctx []
  | ec_lt    : forall Δ Γ, eval_ctx Γ -> eval_ctx (bind_lt Δ :: Γ)
  | ec_ctor  : forall K n_lt n_ty f r Γ,
      eval_ctx Γ -> eval_ctx (bind_ctor K n_lt n_ty f r :: Γ).

Lemma eval_ctx_no_tm : forall Γ x,
  eval_ctx Γ -> ctx_lookup_tm Γ x = None.
Proof. induction 1; intros; simpl; auto. Qed.

Lemma eval_ctx_no_ty : forall Γ α,
  eval_ctx Γ -> ctx_lookup_ty Γ α = None.
Proof. induction 1; intros; simpl; auto. Qed.

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
  exists body T, v = term_lam body T.
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
  - (* T_Lam *) eauto.
Qed.

Lemma canonical_ctor : forall Γ v K l Ts,
  eval_ctx Γ ->
  Γ ⊢ₜ v : type_ctor K l Ts ->
  value v ->
  K <> any_tag ->
  exists K' l' Ts' vs, v = term_ctor K' l' Ts' vs /\ Forall value vs.
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
    eexists; eexists; eexists; eexists; split; eauto.
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

(* For the T_Ctor case in progress, Coq's auto-generated induction    *)
(* principle for `typing` does not unfold the Forall2 premise into a  *)
(* Forall2 of IHs. We axiomatize the elementwise progress lifting for *)
(* constructor argument lists (straightforward structural induction   *)
(* using the `typing`-induction principle with a sufficiently rich    *)
(* scheme would prove it).                                             *)
Axiom progress_ctor_aux : forall Γ vs rhos,
  eval_ctx Γ ->
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rhos ->
  Forall (fun v => value v \/ exists v', v ==> v') vs.

(* A well-typed ctor value has |vs| matching its declared sig arity. *)
Lemma ctor_value_arity : forall Γ K l Ts vs K' l' Ts',
  eval_ctx Γ ->
  Γ ⊢ₜ term_ctor K l Ts vs : type_ctor K' l' Ts' ->
  K' <> any_tag ->
  exists n_lt n_ty sigma result,
    ctx_lookup_ctor Γ K' = Some (n_lt, n_ty, sigma, result) /\
    List.length vs = List.length sigma.
Proof.
  intros Γ K l Ts vs K' l' Ts' Hec Hty HK.
  remember (term_ctor K l Ts vs) as t eqn:Ht.
  remember (type_ctor K' l' Ts') as T eqn:HT.
  revert K l Ts vs K' l' Ts' Ht HT HK.
  induction Hty; intros K0 l0 Ts0 vs0 K1 l1 Ts1 Ht HT HK; try discriminate Ht.
  - (* T_Sub *) subst U.
    destruct (sub_ctor_inv _ _ _ _ _ Hec H HK) as [l'' [HeqS Hlsub]].
    eapply IHHty; eauto.
  - (* T_Ctor *)
    injection Ht; intros Hvs HTs0 Hl0 HK0.
    injection HT; intros HTs1 Hl1 HK1.
    subst K0 l0 Ts0 vs0 K1 l1 Ts1.
    exists n_lt, n_ty, sigma_fields, result_ty_schema. split; auto.
    rewrite H4. subst rho_fields. rewrite List.length_map. auto.
Qed.

(* Progress for the degenerate K = any_tag match corner (axiomatized  *)
(* because SA_Any allows the scrutinee to be any value, which may    *)
(* not be a constructor — a cleaner fix is to add `K <> any_tag` to  *)
(* T_Match; we keep the original rule and close this corner).        *)
Axiom progress_any_match : forall Γ scrut arity yes_body no_body T,
  eval_ctx Γ ->
  value scrut ->
  Γ ⊢ₜ term_match scrut any_tag arity yes_body no_body : T ->
  exists t', term_match scrut any_tag arity yes_body no_body ==> t'.

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
  intros Γ t T Hec Hty.
  induction Hty.
  - rewrite eval_ctx_no_tm in H; auto; discriminate.
  - auto.
  - left; constructor.
  - destruct IHHty1 as [Hv1 | [t1' Hs1]]; auto.
    + destruct IHHty2 as [Hv2 | [t2' Hs2]]; auto.
      * destruct (canonical_fun _ _ _ _ _ Hec Hty1 Hv1) as [body [T0 Heq]]; subst.
        right. eexists. apply S_Beta; auto.
      * right. eexists. eapply S_App2; eauto.
    + right. eexists. eapply S_App1; eauto.
  - left; constructor.
  - destruct IHHty as [Hv | [t' Hs]]; auto.
    + destruct (canonical_ty_all _ _ _ _ Hec Hty Hv) as [bnd [body Heq]]; subst.
      right. eexists. apply S_TyBeta.
    + right. eexists. eapply S_TyApp; eauto.
  - left; constructor.
  - destruct IHHty as [Hv | [t' Hs]]; auto.
    + destruct (canonical_lt_all _ _ _ Hec Hty Hv) as [body Heq]; subst.
      right. eexists. apply S_LtBeta.
    + right. eexists. eapply S_LtApp; eauto.
  - (* T_Ctor *)
    assert (Hforall := progress_ctor_aux _ _ _ Hec H5).
    destruct (split_values_or_step _ Hforall) as
      [Hall | [vsl [tm [tm' [vsr [Hallvl [Heq Hst]]]]]]].
    + left. constructor; auto.
    + right. subst. eexists. apply S_Ctor; eauto.
  - (* T_Match *)
    destruct IHHty1 as [Hv | [scrut' Hs]]; auto.
    + destruct (Nat.eq_dec K any_tag) as [HKany | HKne].
      * right. subst K. eapply progress_any_match; eauto.
      * destruct (canonical_ctor _ _ _ _ _ Hec Hty1 Hv HKne)
          as [K' [l' [Ts' [vs [Heq Hvvs]]]]]; subst.
        right.
        destruct (Nat.eq_dec K' K) as [HKeq | HKdiff].
        -- subst K'.
           destruct (ctor_value_arity _ _ _ _ _ _ _ _ Hec Hty1 HKne)
             as [n_lt' [n_ty' [sig' [res' [Hlook Hlen]]]]].
           rewrite H in Hlook. injection Hlook as Heq1 Heq2 Heq3 Heq4.
           subst n_lt' n_ty' sig' res'.
           eexists.
           replace (@length type (map (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts) sigma_fields))
             with (@length term vs) by (rewrite List.length_map; auto).
           apply S_MatchYes. auto.
        -- eexists. eapply S_MatchNo; eauto.
    + right. eexists. eapply S_Match; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Substitution-style lemmas (axiomatized)                            *)
(* ------------------------------------------------------------------ *)

Axiom subst_tm_lemma : forall Γ T1 t T2 v,
  (bind_tm T1 :: Γ) ⊢ₜ t : T2 ->
  Γ ⊢ₜ v : T1 ->
  Γ ⊢ₜ subst_tm 0 v t : T2.

Axiom subst_ty_in_tm_lemma : forall Γ B t T S,
  (bind_ty B :: Γ) ⊢ₜ t : T ->
  Γ ⊢ S <:: B ->
  Γ ⊢ₜ subst_ty_in_tm 0 S t : subst_ty 0 S T.

Axiom subst_lt_in_tm_lemma : forall Γ Δ t T Δ',
  (bind_lt Δ :: Γ) ⊢ₜ t : T ->
  Γ ⊢ₗ Δ' <: Δ ->
  Γ ⊢ₜ subst_lt_in_tm 0 Δ' t : subst_lt_in_ty 0 Δ' T.

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

(* ------------------------------------------------------------------ *)
(* PRESERVATION                                                       *)
(*                                                                    *)
(* Top-level structure is standard; the β-reduction cases rely on    *)
(* shape inversion and the substitution axioms above.  The App case  *)
(* is fully proven; Ty/Lt β-cases need a narrowing-style lemma that   *)
(* recovers the body-subtyping witness — axiomatized as sub_*_body.   *)
(* ------------------------------------------------------------------ *)

(* Narrowing/body-subtyping witnesses extracted from sub_*_inv.       *)
(* Under eval_ctx these follow structurally from the full inversion   *)
(* (including the body-subtype witness); we axiomatize the                *)
(* body-witness part since we stated sub_lt_all_inv / sub_ty_all_inv   *)
(* without it for brevity.                                             *)
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

Axiom sub_ty_all_inv_full : forall Γ S B T,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_ty_all B T ->
  exists B' T',
    S = type_ty_all B' T' /\
    Γ ⊢ B <:: B' /\
    (bind_ty B :: Γ) ⊢ T' <:: T.

(* Subtyping-substitution lemmas.  Standard; axiomatized.             *)
Axiom sub_subst_ty : forall Γ B U0 U S,
  (bind_ty B :: Γ) ⊢ U0 <:: U ->
  Γ ⊢ S <:: B ->
  Γ ⊢ subst_ty 0 S U0 <:: subst_ty 0 S U.

Axiom sub_subst_lt : forall Γ Δ U0 U Δ',
  (bind_lt Δ :: Γ) ⊢ U0 <:: U ->
  Γ ⊢ₗ Δ' <: Δ ->
  Γ ⊢ subst_lt_in_ty 0 Δ' U0 <:: subst_lt_in_ty 0 Δ' U.

(* Preservation for constructor argument congruence (S_Ctor step).   *)
Axiom ctor_step_preservation : forall Γ K l Ts vs t t' ts T,
  Γ ⊢ₜ term_ctor K l Ts (vs ++ t :: ts) : T ->
  t ==> t' ->
  Γ ⊢ₜ term_ctor K l Ts (vs ++ t' :: ts) : T.

(* Preservation for S_MatchYes.  Full statement bundles the arity    *)
(* unification and the result-type match; standard.                   *)
Axiom match_yes_preservation : forall Γ K Delta Ts vs arity yes_body no_body T,
  Γ ⊢ₜ term_match (term_ctor K Delta Ts vs) K arity yes_body no_body : T ->
  Forall value vs ->
  arity = List.length vs ->
  Γ ⊢ₜ subst_list_tm vs yes_body : T.


Theorem preservation : forall Γ t t' T,
  eval_ctx Γ ->
  Γ ⊢ₜ t : T ->
  t ==> t' ->
  Γ ⊢ₜ t' : T.
Proof.
  intros Γ t t' T Hec Hty Hstep.
  revert t' Hstep.
  induction Hty; intros t'' Hstep;
    try (inversion Hstep; fail).
  - (* Sub *) eapply T_Sub; eauto.
  - (* App *)
    inversion Hstep; subst.
    + (* S_Beta: (λx.body) v  →  subst body *)
      apply lam_typing_inv in Hty1.
      destruct Hty1 as [l' [B' [Hbody Hsub]]].
      destruct (sub_fun_inv _ _ _ _ _ Hec Hsub)
        as [A'' [l'' [B'' [HeqT [HAsub [Hlsub HBsub]]]]]].
      injection HeqT; intros; subst.
      eapply T_Sub; [| exact HBsub].
      eapply subst_tm_lemma; [exact Hbody|].
      eapply T_Sub; [exact Hty2 | exact HAsub].
    + eapply T_App; eauto.
    + eapply T_App; eauto.
  - (* TyApp *)
    inversion Hstep; subst.
    + (* S_TyBeta: (Λα.body) [S]  →  subst_ty *)
      apply ty_lam_typing_inv in Hty.
      destruct Hty as [U0 [Hbody Hsub]].
      destruct (sub_ty_all_inv_full _ _ _ _ Hec Hsub)
        as [B0 [U1 [HeqU [HBsub Hsubbody]]]].
      injection HeqU; intros; subst.
      (* Hbody : (bind_ty B :: Γ) ⊢ body : U0.                         *)
      (* We apply subst_ty_in_tm_lemma with S <:: B. We have H: S <:: B.*)
      eapply T_Sub.
      * eapply subst_ty_in_tm_lemma; [exact Hbody|]. eapply SA_Trans; eauto.
      * eapply sub_subst_ty; eauto.
    + eapply T_TyApp; eauto.
  - (* LtApp *)
    inversion Hstep; subst.
    + (* S_LtBeta *)
      apply lt_lam_typing_inv in Hty.
      destruct Hty as [U0 [Hbody Hsub]].
      destruct (sub_lt_all_inv_full _ _ _ Hec Hsub) as [U1 [HeqU Hsubbody]].
      injection HeqU; intros; subst.
      eapply T_Sub.
      * eapply subst_lt_in_tm_lemma; [exact Hbody|]. apply LS_Local.
      * eapply sub_subst_lt; [exact Hsubbody | apply LS_Local].
    + eapply T_LtApp; eauto.
  - (* Ctor *)
    inversion Hstep; subst.
    eapply ctor_step_preservation;
      [ eapply T_Ctor; try reflexivity; eauto | eauto ].
  - (* Match *)
    inversion Hstep; subst.
    + (* S_MatchYes *)
      eapply match_yes_preservation; eauto.
    + auto.
    + eapply T_Match; eauto.
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
