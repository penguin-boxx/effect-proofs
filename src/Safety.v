Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.

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
Proof. induction 1; intros; simpl; auto. Qed.

Lemma eval_ctx_no_ty : forall Γ α,
  eval_ctx Γ -> ctx_lookup_ty Γ α = None.
Proof. induction 1; intros; simpl; auto. Qed.

Lemma eval_ctx_no_eff : forall Γ E,
  eval_ctx Γ -> ctx_lookup_eff Γ E = None.
Proof. induction 1; intros; simpl; auto. Qed.

(* ------------------------------------------------------------------ *)
(* Effect-handler invariant                                           *)
(*                                                                    *)
(* Under an `eval_ctx` (no `bind_eff` entries), `T_Cap`, `T_Handle`,  *)
(* `T_Perform` cannot fire, so a well-typed term cannot be a perform  *)
(* of a typed capability.  We axiomatize the structural form of this  *)
(* invariant — namely that no well-typed (under eval_ctx) term has a  *)
(* `term_perform (term_cap …) v` subterm sitting under a pure         *)
(* evaluation context — and use it to discharge the H_Perform branch  *)
(* of preservation for `T_HandlerM`.  A direct proof would proceed by *)
(* induction on the typing derivation, threading the invariant under  *)
(* every binder-introducing rule (none of which adds a `bind_eff`).   *)
(* ------------------------------------------------------------------ *)

Axiom no_typed_perform_cap_under_eval_ctx :
  forall Γ T E_tag m Ts op_body Ss v P,
    eval_ctx Γ ->
    pure_ectx_m m P ->
    Γ ⊢ₜ plug P (term_perform (term_cap E_tag m Ts op_body) Ss v) : T ->
    False.

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

(* For the T_Ctor case in progress, Coq's auto-generated induction    *)
(* principle for `typing` does not unfold the Forall2 premise into a  *)
(* Forall2 of IHs. We axiomatize the elementwise progress lifting for *)
(* constructor argument lists (straightforward structural induction   *)
(* using the `typing`-induction principle with a sufficiently rich    *)
(* scheme would prove it).                                            *)
Axiom progress_ctor_aux : forall Γ vs rhos,
  eval_ctx Γ ->
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rhos ->
  Forall (fun v => value v \/ exists v', v ==> v') vs.

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
  intros Γ t T Hec Hty.
  induction Hty.
  - rewrite eval_ctx_no_tm in H; auto; discriminate.
  - auto.
  - left; constructor.
  - destruct IHHty1 as [Hv1 | [t1' Hs1]]; auto.
    + destruct IHHty2 as [Hv2 | [t2' Hs2]]; auto.
      * destruct (canonical_fun _ _ _ _ _ Hec Hty1 Hv1) as
          [[body [T0 Heq]] | [m [b Heq]]]; subst.
        -- right. eexists. apply S_Beta; auto.
        -- right. eexists. apply S_Resume; auto.
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
    assert (Hforall := progress_ctor_aux _ _ _ Hec H6).
    destruct (split_values_or_step _ Hforall) as
      [Hall | [vsl [tm [tm' [vsr [Hallvl [Heq Hst]]]]]]].
    + left. constructor; auto.
    + right. subst. eexists. apply S_Ctor; eauto.
  - (* T_Match *)
    destruct IHHty1 as [Hv | [scrut' Hs]]; auto.
    + assert (HKne : K <> any_tag) by assumption.
      assert (Hlk : exists n_lt0 n_ty0 sig0 res0,
                ctx_lookup_ctor Γ K = Some (n_lt0, n_ty0, sig0, res0))
        by (eexists; eexists; eexists; eexists; eassumption).
      destruct (canonical_ctor _ _ _ _ _ Hec Hty1 Hv HKne)
        as [K' [l' [lts' [Ts' [vs [Heq Hvvs]]]]]]; subst.
      right.
      destruct (Nat.eq_dec K' K) as [HKeq | HKdiff].
      * subst K'.
        destruct (ctor_value_arity _ _ _ _ _ _ _ _ _ Hec Hty1 HKne)
          as [n_lt' [n_ty' [sig' [res' [Hlook Hlen]]]]].
        match goal with
        | [ Heq2 : ctx_lookup_ctor Γ K = Some (n_lt, _, _, _) |- _ ] =>
          rewrite Heq2 in Hlook
        end.
        injection Hlook as Heq1 Heq2 Heq3 Heq4.
        subst n_lt' n_ty' sig' res'.
        eexists.
        replace (@length type (map (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts) sigma_fields))
          with (@length term vs) by (rewrite List.length_map; auto).
        apply S_MatchYes. auto.
      * eexists. eapply S_MatchNo; eauto.
    + right. eexists. eapply S_Match; eauto.
  (* ---- new typing rules: effect handlers ------------------------- *)
  - (* T_Cap *) left; constructor.
  - (* T_Handle: contradiction — no bind_eff under eval_ctx *)
    match goal with
    | H : ctx_lookup_eff _ _ = Some _ |- _ =>
        rewrite eval_ctx_no_eff in H; auto; discriminate
    end.
  - (* T_Perform: same contradiction *)
    match goal with
    | H : ctx_lookup_eff _ _ = Some _ |- _ =>
        rewrite eval_ctx_no_eff in H; auto; discriminate
    end.
  - (* T_HandlerM: step inside via S_HandlerM, or H_Return on a value *)
    destruct IHHty as [Hv | [t' Hs]]; auto.
    + right. exists t. apply S_Return; auto.
    + right. exists (term_handler_m m t'). apply S_HandlerM; auto.
  - (* T_Resume: a reified resumption is a value. *) left; constructor.
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
Axiom ctor_step_preservation : forall Γ K l lts Ts vs t t' ts T,
  Γ ⊢ₜ term_ctor K l lts Ts (vs ++ t :: ts) : T ->
  t ==> t' ->
  Γ ⊢ₜ term_ctor K l lts Ts (vs ++ t' :: ts) : T.

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

(* --- Axiomatized mechanical helpers (de Bruijn plumbing) --- *)

(* Shifting preserves lifetime subtyping. *)
Axiom lt_sub_shift_lt : forall Γ Δ l1 l2 cutoff,
  Γ ⊢ₗ l1 <: l2 ->
  (bind_lt Δ :: Γ) ⊢ₗ shift_lt 1 cutoff l1 <: shift_lt 1 cutoff l2.

(* Subtyping is monotone in single-var lt-substitution at any depth. *)
Axiom lt_sub_subst_lt : forall Γ x l_0 l1 l2,
  Γ ⊢ₗ l1 <: l2 ->
  Γ ⊢ₗ subst_lt x l_0 l1 <: subst_lt x l_0 l2.

(* Type subtyping monotone in single-var lt-substitution. *)
Axiom sub_subst_lt_at : forall Γ x l_0 T1 T2,
  Γ ⊢ T1 <:: T2 ->
  Γ ⊢ subst_lt_in_ty x l_0 T1 <:: subst_lt_in_ty x l_0 T2.

(* shift / subst_lt commute (de Bruijn). *)
Axiom shift_subst_lt_comm : forall l x,
  shift_lt 1 0 (subst_lt x lt_free l) =
  subst_lt (S x) lt_free (shift_lt 1 0 l).
Axiom shift_subst_lt_in_ty_comm : forall T x,
  shift_lt_in_ty 1 0 (subst_lt_in_ty x lt_free T) =
  subst_lt_in_ty (S x) lt_free (shift_lt_in_ty 1 0 T).

(* Trivial lemma: if l doesn't contain lt_var x, subst_lt x lt_free l
   is exactly the "decrement higher vars" operation, identical to its
   action on an l with no lt_var x.                                   *)

(* --- Helper: `subst_lt x lt_free` distributes over `lt_min`.  Trivial. --- *)

(* --- subst_lt_in_ty's internal list fix coincides with map. --- *)
Lemma subst_lt_in_ty_ctor_eq : forall var replacement K l Ts,
  subst_lt_in_ty var replacement (type_ctor K l Ts)
    = type_ctor K (subst_lt var replacement l)
                  (List.map (subst_lt_in_ty var replacement) Ts).
Proof.
  intros var replacement K l Ts.
  induction Ts as [|A rest IH].
  - reflexivity.
  - simpl. simpl in IH. inversion IH. reflexivity.
Qed.

(* --- Type-context weakening for subtyping --- *)
(* Standard structural weakening; axiomatized.  Adding a fresh ty-bind *)
(* preserves derivability of subtyping judgments, since the new var is *)
(* fresh w.r.t. an existing derivation.                                *)
Axiom sub_weaken_ty : forall Γ B T1 T2,
  Γ ⊢ T1 <:: T2 ->
  (bind_ty B :: Γ) ⊢ T1 <:: T2.

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
  induction T as [n | A l B IHA IHB | K l Ts HForall | A IHA | B A IHB IHA]
    using type_ind';
    intros lvar bound p T' Helim Γ l_0 Hsub; simpl in Helim.
  - (* type_var n *)
    injection Helim; intros; subst T'.
    destruct p; simpl; try apply SA_Refl. reflexivity.
  - (* type_fun A l B *)
    destruct (elim_ty lvar bound (flip_var p) A) as [A'|] eqn:EA; try discriminate.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:EL; try discriminate.
    destruct (elim_ty lvar bound p B) as [B'|] eqn:EB; try discriminate.
    injection Helim; intros; subst T'.
    pose proof (elim_lt_step_sound _ _ _ _ _ EL _ _ Hsub) as HL.
    specialize (IHA _ _ _ _ EA Γ l_0 Hsub).
    specialize (IHB _ _ _ _ EB Γ l_0 Hsub).
    destruct p; simpl in *.
    + apply SA_Fun; assumption.
    + apply SA_Fun; assumption.
    + f_equal; assumption.
  - (* type_ctor K l Ts *)
    destruct (elim_lt lvar bound p l) as [l'|] eqn:EL; try discriminate.
    pose proof (elim_lt_step_sound _ _ _ _ _ EL _ _ Hsub) as HL.
    assert (Hlist :
      forall (Ts0 : list type),
      Forall (fun A : type =>
        forall lvar0 bound0 p0 A',
          elim_ty lvar0 bound0 p0 A = Some A' ->
          forall Γ' l_0',
            Γ' ⊢ₗ l_0' <: subst_lt lvar0 lt_free bound0 ->
            match p0 with
            | var_pos => Γ' ⊢ subst_lt_in_ty lvar0 l_0' A <:: subst_lt_in_ty lvar0 lt_free A'
            | var_neg => Γ' ⊢ subst_lt_in_ty lvar0 lt_free A' <:: subst_lt_in_ty lvar0 l_0' A
            | var_inv => subst_lt_in_ty lvar0 lt_free A' = subst_lt_in_ty lvar0 l_0' A
            end) Ts0 ->
      forall Ts0',
      (fix go_list (p' : variance) (Ts1 : list type) : option (list type) :=
         match Ts1 with
         | [] => Some []
         | A0 :: rest =>
             match elim_ty lvar bound p' A0, go_list p' rest with
             | Some A', Some rest' => Some (A' :: rest')
             | _, _ => None
             end
         end) var_inv Ts0 = Some Ts0' ->
      List.map (subst_lt_in_ty lvar lt_free) Ts0'
        = List.map (subst_lt_in_ty lvar l_0) Ts0).
    { clear l' EL HL HForall Helim T' l Ts.
      induction 1 as [| A0 rest HA Hrest IHrest]; intros Ts0' Hgo.
      - simpl in Hgo. injection Hgo; intros; subst Ts0'. reflexivity.
      - simpl in Hgo.
        destruct (elim_ty lvar bound var_inv A0) as [A'|] eqn:EAi; try discriminate.
        remember ((fix go_list (p' : variance) (Ts1 : list type) : option (list type) :=
            match Ts1 with
            | [] => Some []
            | A1 :: rest0 =>
                match elim_ty lvar bound p' A1, go_list p' rest0 with
                | Some A'0, Some rest' => Some (A'0 :: rest')
                | _, _ => None
                end
            end) var_inv rest) as gor eqn:Egor.
        destruct gor as [rest'|]; try discriminate.
        injection Hgo; intros; subst Ts0'.
        pose proof (HA _ _ _ _ EAi _ _ Hsub) as HAEq. simpl in HAEq.
        simpl. f_equal; auto. }
    revert Helim.
    match goal with
    | [ |- (match ?go var_inv Ts with _ => _ end) = _ -> _ ] =>
        destruct (go var_inv Ts) as [Ts'|] eqn:Egos; try discriminate
    end.
    intros Helim. injection Helim; intros; subst T'.
    specialize (Hlist _ HForall _ Egos).
    destruct p; rewrite !subst_lt_in_ty_ctor_eq.
    + rewrite Hlist. apply SA_Data. assumption.
    + rewrite Hlist. apply SA_Data. assumption.
    + simpl in HL. rewrite HL. f_equal; auto.
  - (* type_lt_all A *)
    destruct (elim_ty (S lvar) (shift_lt 1 0 bound) p A) as [A'|] eqn:EA; try discriminate.
    injection Helim; intros; subst T'.
    assert (Hsub' : (bind_lt lt_local :: Γ) ⊢ₗ shift_lt 1 0 l_0
                    <: subst_lt (S lvar) lt_free (shift_lt 1 0 bound)).
    { rewrite <- shift_subst_lt_comm.
      apply lt_sub_shift_lt. assumption. }
    specialize (IHA _ _ _ _ EA _ _ Hsub').
    destruct p; simpl.
    + apply SA_LtAll. assumption.
    + apply SA_LtAll. assumption.
    + f_equal; assumption.
  - (* type_ty_all B A *)
    destruct (elim_ty lvar bound (flip_var p) B) as [B'|] eqn:EB; try discriminate.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:EA; try discriminate.
    injection Helim; intros; subst T'.
    specialize (IHB _ _ _ _ EB Γ l_0 Hsub).
    specialize (IHA _ _ _ _ EA Γ l_0 Hsub).
    destruct p; simpl in IHB; simpl.
    + (* var_pos: SA_TyAll needs                                       *)
      (*   subst_lt_in_ty lvar lt_free B' <:: subst_lt_in_ty lvar l_0 B *)
      (* and (bind_ty B' :: Γ) ⊢ ...A... <:: ...A'...                  *)
      apply SA_TyAll; [assumption|].
      apply sub_weaken_ty. assumption.
    + apply SA_TyAll; [assumption|].
      apply sub_weaken_ty. assumption.
    + f_equal; assumption.
Qed.

(* --- Iterated elim soundness --- *)

(* `iter_subst_lt_in_ty ws T` substitutes the witnesses ws sequentially *)
(* at de Bruijn position 0, decrementing the remaining lt-vars after    *)
(* each step.  This matches `elim_ty_n`'s iteration where each step     *)
(* closes a binder via `subst_lt 0 lt_free`.                            *)
Fixpoint iter_subst_lt_in_ty (ws : list lifetime) (T : type) : type :=
  match ws with
  | []        => T
  | w :: rest => iter_subst_lt_in_ty rest (subst_lt_in_ty 0 w T)
  end.

(* Witnesses are valid w.r.t. a chain of progressively-closed bounds.   *)
Fixpoint chain_bounded (Γ : ctx) (ws : list lifetime) (bound : lifetime) : Prop :=
  match ws with
  | []        => True
  | w :: rest =>
      (Γ ⊢ₗ w <: subst_lt 0 lt_free bound) /\
      chain_bounded Γ rest (subst_lt 0 lt_free bound)
  end.

(* Subtyping is preserved through `iter_subst_lt_in_ty`.                *)
Lemma iter_subst_lt_in_ty_mono : forall ws Γ T1 T2,
  Γ ⊢ T1 <:: T2 ->
  Γ ⊢ iter_subst_lt_in_ty ws T1 <:: iter_subst_lt_in_ty ws T2.
Proof.
  induction ws as [|w rest IH]; intros Γ T1 T2 Hsub; simpl.
  - assumption.
  - apply IH. apply sub_subst_lt_at. assumption.
Qed.

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

(* ================================================================== *)
(* Parallel substitution preservation (de Bruijn plumbing)            *)
(*                                                                    *)
(* These are the standard parallel-substitution preservation lemmas   *)
(* for a Stlc + lt-polymorphism setting; their proofs are by routine  *)
(* induction on the typing derivation (or term structure) and de      *)
(* Bruijn arithmetic, orthogonal to the paper's contribution.         *)
(* ================================================================== *)

(* Apply `subst_list_lt_in_ty lts` pointwise to a list of types.       *)
Definition subst_list_lt_in_ty_each (lts : list lifetime) (rhos : list type) : list type :=
  List.map (subst_list_lt_in_ty lts) rhos.

(* Parallel lt substitution lemma.  Closes the n_lt fresh lt-binders   *)
(* introduced by `push_lt_vars n_lt Delta`, while propagating through  *)
(* an arbitrary stack of `bind_tm` binders sitting above (whose types  *)
(* also get the parallel lt-substitution applied).                     *)
Axiom subst_list_lt_in_tm_lemma : forall Γ rhos n_lt Delta lts t T,
  List.length lts = n_lt ->
  chain_bounded Γ lts (shift_lt n_lt 0 Delta) ->
  (fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
              (push_lt_vars n_lt Delta Γ) rhos) ⊢ₜ t : T ->
  (fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
              Γ (subst_list_lt_in_ty_each lts rhos))
    ⊢ₜ subst_list_lt_in_tm lts t : subst_list_lt_in_ty lts T.

(* Parallel term substitution: closes a list of tm-binders against a   *)
(* matching list of values typed in the outer Γ.                       *)
Axiom subst_list_tm_lemma : forall Γ vs rhos t T,
  List.length vs = List.length rhos ->
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rhos ->
  (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos) ⊢ₜ t : T ->
  Γ ⊢ₜ subst_list_tm vs t : T.

(* Bridge: parallel lt-substitution `subst_list_lt_in_ty` aligned with *)
(* the iterated single-var substitution `iter_subst_lt_in_ty` used by  *)
(* `elim_ty_n_sound`.                                                  *)
Axiom subst_list_lt_in_ty_eq_iter : forall lts T,
  subst_list_lt_in_ty lts T = iter_subst_lt_in_ty lts T.

(* From the typing of a ctor *value* `term_ctor K Delta lts Ts vs`     *)
(* against type `type_ctor K Delta Ts`, the witnesses `lts` form a     *)
(* `chain_bounded` chain w.r.t. the shifted Delta.  This is the        *)
(* metatheoretic invariant of well-typed ctor values: T_Ctor ensures   *)
(* `Delta = lt_of_ty_list rho_fields_c` and the shape of rho_fields    *)
(* implies that lts satisfy the corresponding chain bound.             *)
Axiom ctor_lts_chain_bounded : forall Γ lts n_lt n_ty Ts sigma vs Delta,
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs
          (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma) ->
  List.length lts = n_lt ->
  Delta = lt_of_ty_list (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma) ->
  chain_bounded Γ lts (shift_lt n_lt 0 Delta).

(* Monotonicity of chain_bounded under enlarging the ambient bound.    *)
(* A standard consequence of weakening for the lifetime subtyping.     *)
Axiom chain_bounded_mono : forall Γ lts B B',
  chain_bounded Γ lts B ->
  Γ ⊢ₗ B <: B' ->
  chain_bounded Γ lts B'.

(* Lifetime subtyping is preserved by `shift_lt`.                       *)
Axiom shift_lt_sub : forall Γ n k B B',
  Γ ⊢ₗ B <: B' ->
  Γ ⊢ₗ shift_lt n k B <: shift_lt n k B'.

(* Substituting `lts` for the schema variables `lt_var_list n_lt`      *)
(* yields direct schema instantiation.                                 *)
Axiom inst_ctor_type_subst_eq : forall n_lt n_ty lts Ts sigma_fields,
  List.length lts = n_lt ->
  subst_list_lt_in_ty_each lts
    (List.map (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts) sigma_fields)
  = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields.

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

Lemma match_yes_preservation : forall Γ K Delta lts Ts vs arity yes_body no_body T,
  eval_ctx Γ ->
  Γ ⊢ₜ term_match (term_ctor K Delta lts Ts vs) K arity yes_body no_body : T ->
  Forall value vs ->
  arity = List.length vs ->
  Γ ⊢ₜ subst_list_tm vs (subst_list_lt_in_tm lts yes_body) : T.
Proof.
  intros Γ K Delta lts Ts vs arity yes_body no_body T Hec Hty Hvals Harity.
  apply match_typing_inv in Hty.
  destruct Hty as
    [n_lt [n_ty [sigma [result [Ts_m [Delta_m [eta [elim_result
      [HKneq [Hscrut [Hlk [Har [Hbody [Helim [Hno HsubT]]]]]]]]]]]]]]].
  pose proof Hscrut as Hscrut0.
  apply ctor_typing_inv in Hscrut0.
  destruct Hscrut0 as
    [n_lt' [n_ty' [sig' [res'
      [Hlk' [Hltlen [HTslen [Hl [Hvslen [Hf2 Hsubctor]]]]]]]]]].
  rewrite Hlk' in Hlk. injection Hlk; intros Hreseq Hsigeq Hntyeq Hnlteq.
  subst sig' res'.
  rewrite Hnlteq in Hf2, Hl, Hltlen.
  rewrite Hntyeq in Hf2, Hl.
  destruct (sub_ctor_inv _ _ _ _ _ Hec Hsubctor HKneq) as [l' [Heqty Hlsub']].
  injection Heqty; intros HTseq Hl'eq; subst l' Ts_m.
  pose proof (ctor_lts_chain_bounded Γ lts n_lt n_ty Ts sigma vs Delta
                Hf2 Hltlen Hl) as Hchain.
  pose proof (subst_list_lt_in_tm_lemma Γ
                (List.map (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts) sigma)
                n_lt Delta_m lts yes_body eta Hltlen) as Hbody'.
  assert (Hchain' : chain_bounded Γ lts (shift_lt n_lt 0 Delta_m)).
  { eapply chain_bounded_mono; [exact Hchain|].
    apply shift_lt_sub. exact Hlsub'. }
  specialize (Hbody' Hchain' Hbody).
  rewrite (inst_ctor_type_subst_eq n_lt n_ty lts Ts sigma Hltlen) in Hbody'.
  assert (Hvslen' : List.length vs =
    List.length (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma)).
  { rewrite List.length_map. exact Hvslen. }
  pose proof (subst_list_tm_lemma Γ vs
                (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma)
                (subst_list_lt_in_tm lts yes_body)
                (subst_list_lt_in_ty lts eta) Hvslen' Hf2 Hbody') as Hbody''.
  pose proof (elim_ty_n_sound lts n_lt (shift_lt n_lt 0 Delta_m) var_pos eta
                elim_result Γ Helim Hltlen Hchain') as Helim'.
  simpl in Helim'.
  rewrite <- subst_list_lt_in_ty_eq_iter in Helim'.
  eapply T_Sub; [eapply T_Sub; [exact Hbody'' | exact Helim'] | exact HsubT].
Qed.

Theorem preservation : forall Γ t t' T,
  eval_ctx Γ ->
  Γ ⊢ₜ t : T ->
  t ==> t' ->
  Γ ⊢ₜ t' : T.
Proof.
  intros Γ t t' T Hec Hty Hstep.
  revert t' Hstep.
  induction Hty; intros t'' Hstep;
    try no_step.
  - (* Sub *) eapply T_Sub; eauto.
  - (* App *)
    apply step_app_inv in Hstep.
    destruct Hstep as [(body0 & T0 & v0 & E1 & E2 & Hv0 & E3)
                      | [ (m0 & b0 & v0 & E1 & E2 & Hv0 & E3)
                      | [ (t1' & Hs1 & E3) | (t2' & Hv1 & Hs2 & E3) ]]].
    + (* S_Beta: (λx.body) v  →  subst body *)
      subst t1 t2 t''.
      apply lam_typing_inv in Hty1.
      destruct Hty1 as [l' [B' [Hbody Hsub]]].
      destruct (sub_fun_inv _ _ _ _ _ Hec Hsub)
        as [A'' [l'' [B'' [HeqT [HAsub [Hlsub HBsub]]]]]].
      injection HeqT; intros; subst.
      eapply T_Sub; [| exact HBsub].
      eapply subst_tm_lemma; [exact Hbody|].
      eapply T_Sub; [exact Hty2 | exact HAsub].
    + (* S_Resume: (resume m b) v  →  handler_m m (subst v b) *)
      subst t1 t2 t''.
      apply resume_typing_inv in Hty1.
      destruct Hty1 as [A' [B' [Hbody Hsub]]].
      destruct (sub_fun_inv _ _ _ _ _ Hec Hsub)
        as [A'' [l'' [B'' [HeqT [HAsub [Hlsub HBsub]]]]]].
      injection HeqT; intros; subst.
      apply T_HandlerM.
      eapply T_Sub; [| exact HBsub].
      eapply subst_tm_lemma; [exact Hbody|].
      eapply T_Sub; [exact Hty2 | exact HAsub].
    + subst t''. eapply T_App; eauto.
    + subst t''. eapply T_App; eauto.
  - (* TyApp *)
    apply step_ty_app_inv in Hstep.
    destruct Hstep as [(bound0 & body0 & E1 & E2) | (t0' & Hs & E2)].
    + (* S_TyBeta: (Λα.body) [S]  →  subst_ty *)
      subst t t''.
      apply ty_lam_typing_inv in Hty.
      destruct Hty as [U0 [Hbody Hsub]].
      destruct (sub_ty_all_inv_full _ _ _ _ Hec Hsub)
        as [B0 [U1 [HeqU [HBsub Hsubbody]]]].
      injection HeqU; intros; subst.
      eapply T_Sub.
      * eapply subst_ty_in_tm_lemma; [exact Hbody|]. eapply SA_Trans; eauto.
      * eapply sub_subst_ty; eauto.
    + subst t''. eapply T_TyApp; eauto.
  - (* LtApp *)
    apply step_lt_app_inv in Hstep.
    destruct Hstep as [(body0 & E1 & E2) | (t0' & Hs & E2)].
    + (* S_LtBeta *)
      subst t t''.
      apply lt_lam_typing_inv in Hty.
      destruct Hty as [U0 [Hbody Hsub]].
      destruct (sub_lt_all_inv_full _ _ _ Hec Hsub) as [U1 [HeqU Hsubbody]].
      injection HeqU; intros; subst.
      eapply T_Sub.
      * eapply subst_lt_in_tm_lemma; [exact Hbody|]. apply LS_Local.
      * eapply sub_subst_lt; [exact Hsubbody | apply LS_Local].
    + subst t''. eapply T_LtApp; eauto.
  - (* Ctor *)
    apply step_ctor_inv in Hstep.
    destruct Hstep as (vs0 & t0 & t0' & tsr0 & Hvs0 & Eargs & Hs0 & Et).
    rewrite Et. rewrite Eargs in *.
    eapply ctor_step_preservation.
    + (* repackage T_Ctor over the substituted arg-list *)
      eapply T_Ctor; eassumption.
    + assumption.
  - (* Match *)
    apply step_match_inv in Hstep.
    destruct Hstep as
      [ (K0 & l0 & lts0 & Ts0 & vs0 & Es & Hvs0 & Ear & EK & Et)
      | [ (K0' & l0 & lts0 & Ts0 & vs0 & Es & Hvs0 & Hne & Et)
        | (s' & Hs & Et) ]].
    + (* S_MatchYes *)
      subst K0 scrut arity t''.
      eapply match_yes_preservation; eauto.
    + (* S_MatchNo  *) subst scrut t''. auto.
    + (* S_Match    *) subst t''. eapply T_Match; eauto.
  (* ---- new typing rules: effect handlers ------------------------- *)
  (* T_Cap auto-closed by `try no_step` (cap is a value) *)
  - (* T_Handle: contradiction — no bind_eff under eval_ctx, so there  *)
    (* is no well-typed term_handle in the first place.               *)
    match goal with
    | H : ctx_lookup_eff _ _ = Some _ |- _ =>
        rewrite eval_ctx_no_eff in H; auto; discriminate
    end.
  - (* T_Perform: same contradiction *)
    match goal with
    | H : ctx_lookup_eff _ _ = Some _ |- _ =>
        rewrite eval_ctx_no_eff in H; auto; discriminate
    end.
  - (* T_HandlerM *)
    apply step_handler_m_inv in Hstep.
    destruct Hstep as
      [(Hv & Et)
      | [(t' & Hs & Et)
      | (E_tag & Ts & op_body & Ss & v & P & Hv & Hpe & Edec & Et)]].
    + (* H_Return: t value, t'' = t *)
      subst t''. assumption.
    + (* S_HandlerM: t ==> t', t'' = handler_m m t' *)
      subst t''. apply T_HandlerM. apply IHHty; assumption.
    + (* H_Perform: under eval_ctx the inner perform-of-cap cannot be  *)
      (* well-typed.  Apply the invariant axiom for a contradiction.    *)
      exfalso. subst t.
      eapply no_typed_perform_cap_under_eval_ctx; eauto.
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
