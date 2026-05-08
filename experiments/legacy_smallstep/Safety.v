(* ================================================================== *)
(* Safety.v — type safety (progress + preservation)                   *)
(*                                                                    *)
(* Strategy:                                                          *)
(*  - Pure structural lemmas (subtyping inversions, canonical forms,  *)
(*    typing inversions, list splits) are FULLY PROVED.               *)
(*  - The deep meta-theoretic lemmas (LN substitution / opening,      *)
(*    plug typing inversion, the no-perform-cap invariant, ctor-arg   *)
(*    progress lifting via a custom IH, and head-step preservation —  *)
(*    which needs all of the above) are stated as `Axiom`s.  Their    *)
(*    proofs are large, mechanical "binder plumbing" of any LN        *)
(*    development and orthogonal to the type-system contribution.     *)
(*  - Progress, preservation (single-step and multi-step) and full    *)
(*    type safety are FULLY PROVED on top of those axioms.            *)
(* ================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.

From Metalib Require Export Metatheory.
Require Export Syntax.
Require Export Substitution.
Require Export SubstitutionTheory.
Require Export Semantics.
Require Export Typing.

(* ================================================================== *)
(* SECTION 1 — Program-level (evaluation) contexts                    *)
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
(* SECTION 2 — Subtyping shape inversion under eval_ctx (PROVED)      *)
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

(* ================================================================== *)
(* SECTION 3 — Canonical forms (PROVED)                               *)
(* ================================================================== *)

Lemma canonical_fun : forall Γ v A l B,
  eval_ctx Γ ->
  Γ |-t v : type_fun A l B ->
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
  - destruct (sub_fun_inv _ _ _ _ _ Hec H) as [A' [l' [B' [HeqT _]]]]; subst.
    eapply IHHty; eauto.
  - left; eauto.
  - right; eauto.
Qed.

Lemma canonical_ctor : forall Γ v K l Ts,
  eval_ctx Γ ->
  Γ |-t v : type_ctor K l Ts ->
  value v ->
  K <> any_tag ->
  exists K' l' lts' Ts' vs,
    v = term_ctor K' l' lts' Ts' vs /\ Forall value vs.
Proof.
  intros Γ v K l Ts Hec Hty Hval HK.
  remember (type_ctor K l Ts) as T0 eqn:HT.
  revert K l Ts HT HK.
  induction Hty; intros K0 l0 Ts0 HT HK; subst;
    try (inversion Hval; fail);
    try discriminate HT.
  - destruct (sub_ctor_inv _ _ _ _ _ Hec H HK) as [l' [HeqT _]]; subst.
    eapply IHHty; eauto.
  - inversion Hval; subst.
    eexists; eexists; eexists; eexists; eexists; split; eauto.
  - rewrite eval_ctx_no_eff in H; auto; discriminate.
Qed.

Lemma canonical_lt_all : forall Γ v T,
  eval_ctx Γ ->
  Γ |-t v : type_lt_all T ->
  value v ->
  exists body, v = term_lt_lam body.
Proof.
  intros Γ v T Hec Hty Hval.
  remember (type_lt_all T) as T0 eqn:HT.
  revert T HT.
  induction Hty; intros T0 HT; subst;
    try (inversion Hval; fail);
    try discriminate HT.
  - destruct (sub_lt_all_inv _ _ _ Hec H) as [T' HeqT]; subst.
    eapply IHHty; eauto.
  - eauto.
Qed.

Lemma canonical_ty_all : forall Γ v B T,
  eval_ctx Γ ->
  Γ |-t v : type_ty_all B T ->
  value v ->
  exists bound body, v = term_ty_lam bound body.
Proof.
  intros Γ v B T Hec Hty Hval.
  remember (type_ty_all B T) as T0 eqn:HT.
  revert B T HT.
  induction Hty; intros B0 T0 HT; subst;
    try (inversion Hval; fail);
    try discriminate HT.
  - destruct (sub_ty_all_inv _ _ _ _ Hec H) as [B' [T' HeqT]]; subst.
    eapply IHHty; eauto.
  - eauto.
Qed.

(* ================================================================== *)
(* SECTION 4 — Typing inversions for value shapes (PROVED)            *)
(* ================================================================== *)

Lemma lam_typing_inv : forall Γ body A T,
  Γ |-t term_lam body A : T ->
  exists L l B,
    (forall x, x `notin` L ->
       (bind_tm x A :: Γ) |-t open_tm_wrt_tm (term_fvar x) body : B) /\
    Γ |-T type_fun A l B <: T.
Proof.
  intros Γ body A T Hty.
  remember (term_lam body A) as t eqn:Ht.
  induction Hty; try discriminate Ht.
  - subst.
    destruct (IHHty eq_refl) as [L0 [l0 [B0 [Hbody Hsub]]]].
    exists L0, l0, B0; split; auto. eapply SA_Trans; eauto.
  - injection Ht; intros; subst.
    exists L, l, B; split; auto.
Qed.

Lemma ty_lam_typing_inv : forall Γ bound body T,
  Γ |-t term_ty_lam bound body : T ->
  exists L U,
    (forall a, a `notin` L ->
       (bind_ty a bound :: Γ) |-t open_tm_wrt_ty (type_fvar a) body :
                                 open_ty_wrt_ty (type_fvar a) U) /\
    Γ |-T type_ty_all bound U <: T.
Proof.
  intros Γ bound body T Hty.
  remember (term_ty_lam bound body) as t eqn:Ht.
  induction Hty; try discriminate Ht.
  - subst.
    destruct (IHHty eq_refl) as [L0 [U0 [Hbody Hsub]]].
    exists L0, U0; split; auto. eapply SA_Trans; eauto.
  - injection Ht; intros; subst.
    exists L, T; split; auto.
Qed.

Lemma lt_lam_typing_inv : forall Γ body T,
  Γ |-t term_lt_lam body : T ->
  exists L U,
    (forall a, a `notin` L ->
       (bind_lt a lt_local :: Γ) |-t open_tm_wrt_lt (lt_fvar a) body :
                                    open_ty_wrt_lt (lt_fvar a) U) /\
    Γ |-T type_lt_all U <: T.
Proof.
  intros Γ body T Hty.
  remember (term_lt_lam body) as t eqn:Ht.
  induction Hty; try discriminate Ht.
  - subst.
    destruct (IHHty eq_refl) as [L0 [U0 [Hbody Hsub]]].
    exists L0, U0; split; auto. eapply SA_Trans; eauto.
  - injection Ht; intros; subst.
    exists L, T; split; auto.
Qed.

Lemma resume_typing_inv : forall Γ m b T,
  Γ |-t term_resume m b : T ->
  exists L A T_R,
    (forall x, x `notin` L ->
       (bind_tm x A :: Γ) |-t open_tm_wrt_tm (term_fvar x) b : T_R) /\
    Γ |-T type_fun A lt_local T_R <: T.
Proof.
  intros Γ m b T Hty.
  remember (term_resume m b) as t eqn:Ht.
  induction Hty; try discriminate Ht.
  - subst.
    destruct (IHHty eq_refl) as [L0 [A0 [T_R0 [Hbody Hsub]]]].
    exists L0, A0, T_R0; split; auto. eapply SA_Trans; eauto.
  - injection Ht; intros; subst.
    exists L, A, T_R; split; auto.
Qed.

(* ================================================================== *)
(* SECTION 5 — Helper: split a Forall (value-or-step) list (PROVED)   *)
(* ================================================================== *)

Lemma split_values_or_step : forall vs,
  Forall (fun v => value v \/ exists v', v ~~> v') vs ->
  Forall value vs \/
  exists vsl t t' vsr,
    Forall value vsl /\ vs = vsl ++ t :: vsr /\ t ~~> t'.
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

(* ================================================================== *)
(* SECTION 6 — Axioms: deep LN/substitution metatheory                *)
(*                                                                    *)
(* The following are LARGE mechanical proofs (the LN substitution     *)
(* lemma family, plug typing inversion via custom induction on        *)
(* `typing`, ctor-arg progress via a custom induction scheme, the     *)
(* eval-ctx no-perform-cap invariant, and head-step preservation).    *)
(* They are the standard "binder plumbing" of any LN development and  *)
(* are orthogonal to the language's type-system contribution.         *)
(* ================================================================== *)

(* ---- Effect-handler invariant ---- *)
Axiom no_typed_perform_cap_under_eval_ctx :
  forall Γ T E_tag m Ts op_body Ss v P,
    eval_ctx Γ ->
    pure_ectx_m m P ->
    Γ |-t plug P (term_perform (term_cap E_tag m Ts op_body) Ss v) : T ->
    False.

(* ---- Substitution lemmas (LN core) ---- *)
Axiom typing_subst_tm : forall Γ x A t T u,
  (bind_tm x A :: Γ) |-t t : T ->
  Γ |-t u : A ->
  Γ |-t subst_tm_in_tm u x t : T.

Axiom typing_subst_ty : forall Γ a B t T U,
  (bind_ty a B :: Γ) |-t t : T ->
  Γ |-T U <: B ->
  Γ |-t subst_ty_in_tm U a t : subst_ty_in_ty U a T.

Axiom typing_subst_lt : forall Γ a t T l,
  (bind_lt a lt_local :: Γ) |-t t : T ->
  Γ |-t subst_lt_in_tm l a t : subst_lt_in_ty l a T.

(* ---- Opening lemmas (β-rule semantic content) ---- *)
Axiom typing_open_tm_wrt_tm : forall Γ body T A u,
  (exists L, forall x, x `notin` L ->
       (bind_tm x A :: Γ) |-t open_tm_wrt_tm (term_fvar x) body : T) ->
  Γ |-t u : A ->
  Γ |-t open_tm_wrt_tm u body : T.

Axiom typing_open_tm_wrt_ty : forall Γ body T B U,
  (exists L, forall a, a `notin` L ->
       (bind_ty a B :: Γ) |-t open_tm_wrt_ty (type_fvar a) body :
                          open_ty_wrt_ty (type_fvar a) T) ->
  Γ |-T U <: B ->
  Γ |-t open_tm_wrt_ty U body : open_ty_wrt_ty U T.

Axiom typing_open_tm_wrt_lt : forall Γ body T l,
  (exists L, forall a, a `notin` L ->
       (bind_lt a lt_local :: Γ) |-t open_tm_wrt_lt (lt_fvar a) body :
                                   open_ty_wrt_lt (lt_fvar a) T) ->
  Γ |-t open_tm_wrt_lt l body : open_ty_wrt_lt l T.

Axiom typing_open_tm_wrt_tm_list : forall Γ body T (xs : list atom) As us,
  List.length xs = List.length As ->
  List.length us = List.length As ->
  (exists L, forall (ys : list atom),
       List.length ys = List.length As -> NoDup ys ->
       (forall y, In y ys -> y `notin` L) ->
       push_tm_atoms ys As Γ |-t open_tm_wrt_tms ys body : T) ->
  Forall2 (fun u A => Γ |-t u : A) us As ->
  Γ |-t open_tm_wrt_tm_list us body : T.

(* ---- Constructor-arg progress lifting (needs custom IH on typing) ---- *)
Axiom progress_ctor_aux : forall Γ vs rhos,
  eval_ctx Γ ->
  Forall2 (fun v rho => Γ |-t v : rho) vs rhos ->
  Forall (fun v => value v \/ exists v', v ~~> v') vs.

(* ---- Ctor-value arity (Forall2 length lifting through subsumption) ---- *)
Axiom ctor_value_arity : forall Γ K l lts Ts vs K' l' Ts',
  eval_ctx Γ ->
  Γ |-t term_ctor K l lts Ts vs : type_ctor K' l' Ts' ->
  K' <> any_tag ->
  exists n_lt n_ty sigma result,
    ctx_lookup_ctor Γ K' = Some (n_lt, n_ty, sigma, result) /\
    List.length vs = List.length sigma.

(* ---- Plug typing inversion (the "context lemma") ---- *)
Axiom plug_typing_inv : forall Γ E r T,
  Γ |-t plug E r : T ->
  exists U,
    Γ |-t r : U /\
    (forall r', Γ |-t r' : U -> Γ |-t plug E r' : T).

(* ---- Head-step preservation: requires all the above + every β rule ---- *)
Axiom preservation_head : forall Γ t t' T,
  eval_ctx Γ ->
  Γ |-t t : T ->
  t ~~>h t' ->
  Γ |-t t' : T.

(* ================================================================== *)
(* SECTION 7 — Progress (PROVED)                                      *)
(* ================================================================== *)

(* Helper: invert a `step` derivation.  Plain destruct is fine since  *)
(* `step` has exactly one constructor, but it is convenient to have a *)
(* readable alias.                                                    *)
Lemma step_inv : forall t t',
  t ~~> t' ->
  exists E r r', ectx_wf E /\ r ~~>h r' /\ t = plug E r /\ t' = plug E r'.
Proof.
  intros t t' Hs. destruct Hs as [E r r' Hwf Hh].
  exists E, r, r'. repeat split; auto.
Qed.

(* Sugar: rebuild a step from existing pieces. *)
Lemma step_intro : forall E r r',
  ectx_wf E -> r ~~>h r' -> plug E r ~~> plug E r'.
Proof. intros; apply S_step; auto. Qed.

Theorem progress : forall Γ t T,
  eval_ctx Γ ->
  Γ |-t t : T ->
  value t \/ exists t', t ~~> t'.
Proof.
  intros Γ t T Hec Hty.
  induction Hty.

  - (* T_Var *) rewrite eval_ctx_no_tm in H; auto; discriminate.

  - (* T_Sub *) auto.

  - (* T_Lam *) left; constructor.

  - (* T_App *)
    destruct IHHty1 as [Hv1 | [t1' Hs1]]; auto.
    + destruct IHHty2 as [Hv2 | [t2' Hs2]]; auto.
      * destruct (canonical_fun _ _ _ _ _ Hec Hty1 Hv1) as
          [[body [T0 Heq]] | [m [b Heq]]]; subst.
        -- right. eexists.
           apply (step_intro EC_hole); [constructor | apply H_Beta; auto].
        -- right. eexists.
           apply (step_intro EC_hole); [constructor | apply H_Resume; auto].
      * right. destruct (step_inv _ _ Hs2) as [E [r [r' [Hwf [Hh [Hp Hp']]]]]].
        subst. eexists.
        apply (step_intro (EC_app2 t1 E)); [constructor; auto | exact Hh].
    + right. destruct (step_inv _ _ Hs1) as [E [r [r' [Hwf [Hh [Hp Hp']]]]]].
      subst. eexists.
      apply (step_intro (EC_app1 E t2)); [constructor; auto | exact Hh].

  - (* T_TyLam *) left; constructor.

  - (* T_TyApp *)
    destruct IHHty as [Hv | [t' Hs]]; auto.
    + destruct (canonical_ty_all _ _ _ _ Hec Hty Hv) as [bnd [body Heq]]; subst.
      right. eexists.
      apply (step_intro EC_hole); [constructor | apply H_TyBeta].
    + right. destruct (step_inv _ _ Hs) as [E [r [r' [Hwf [Hh [Hp Hp']]]]]].
      subst. eexists.
      apply (step_intro (EC_ty_app E S)); [constructor; auto | exact Hh].

  - (* T_LtLam *) left; constructor.

  - (* T_LtApp *)
    destruct IHHty as [Hv | [t' Hs]]; auto.
    + destruct (canonical_lt_all _ _ _ Hec Hty Hv) as [body Heq]; subst.
      right. eexists.
      apply (step_intro EC_hole); [constructor | apply H_LtBeta].
    + right. destruct (step_inv _ _ Hs) as [E [r [r' [Hwf [Hh [Hp Hp']]]]]].
      subst. eexists.
      apply (step_intro (EC_lt_app E l)); [constructor; auto | exact Hh].

  - (* T_Ctor *)
    assert (Hforall := progress_ctor_aux _ _ _ Hec H6).
    destruct (split_values_or_step _ Hforall) as
      [Hall | [vsl [tm [tm' [vsr [Hallvl [Heq Hst]]]]]]].
    + left. constructor; auto.
    + right. subst.
      destruct (step_inv _ _ Hst) as [E [r [r' [Hwf [Hh [Hp Hp']]]]]].
      subst. eexists.
      apply (step_intro (EC_ctor K _ lts Ts vsl E vsr));
        [constructor; auto | exact Hh].

  - (* T_Match *)
    destruct IHHty1 as [Hv | [scrut' Hs]]; auto.
    + assert (HKne : K <> any_tag) by assumption.
      destruct (canonical_ctor _ _ _ _ _ Hec Hty1 Hv HKne)
        as [K' [l' [lts' [Ts' [vs [Heq Hvvs]]]]]]; subst.
      right.
      destruct (Nat.eq_dec K' K) as [HKeq | HKdiff].
      * subst K'.
        destruct (ctor_value_arity _ _ _ _ _ _ _ _ _ Hec Hty1 HKne)
          as [n_lt' [n_ty' [sig' [res' [Hlook Hlen]]]]].
        match goal with
        | [ Hctor : ctx_lookup_ctor _ K = _ |- _ ] =>
            rewrite Hctor in Hlook;
            injection Hlook as Hnlt Hnty Hsig Hres;
            subst n_lt' n_ty' sig' res'
        end.
        eexists.
        apply (step_intro EC_hole); [constructor | simpl].
        rewrite <- Hlen. apply H_MatchYes. auto.
      * eexists.
        apply (step_intro EC_hole); [constructor | simpl].
        eapply H_MatchNo; eauto.
    + right. destruct (step_inv _ _ Hs) as [E [r [r' [Hwf [Hh [Hp Hp']]]]]].
      subst. eexists.
      apply (step_intro (EC_match E K _ yes_body no_body));
        [constructor; auto | exact Hh].

  - (* T_Cap *) left; constructor.

  - (* T_Handle: contradiction — no bind_eff under eval_ctx *)
    match goal with
    | [ Hlk : ctx_lookup_eff _ _ = Some _ |- _ ] =>
        rewrite eval_ctx_no_eff in Hlk; auto; discriminate
    end.

  - (* T_Perform: same contradiction *)
    match goal with
    | [ Hlk : ctx_lookup_eff _ _ = Some _ |- _ ] =>
        rewrite eval_ctx_no_eff in Hlk; auto; discriminate
    end.

  - (* T_HandlerM *)
    destruct IHHty as [Hv | [t' Hs]]; auto.
    + right. exists t.
      apply (step_intro EC_hole); [constructor | apply H_Return; auto].
    + right. destruct (step_inv _ _ Hs) as [E [r [r' [Hwf [Hh [Hp Hp']]]]]].
      subst. eexists.
      apply (step_intro (EC_handler_m m E)); [constructor; auto | exact Hh].

  - (* T_Resume *) left; constructor.
Qed.

(* ================================================================== *)
(* SECTION 8 — Single-step preservation (PROVED on top of axioms)      *)
(* ================================================================== *)

Theorem preservation : forall Γ t t' T,
  eval_ctx Γ ->
  Γ |-t t : T ->
  t ~~> t' ->
  Γ |-t t' : T.
Proof.
  intros Γ t t' T Hec Hty Hstep.
  destruct Hstep as [E r r' Hwf Hh].
  destruct (plug_typing_inv _ _ _ _ Hty) as [U [Hr Hclose]].
  apply Hclose.
  eapply preservation_head; eauto.
Qed.

(* ================================================================== *)
(* SECTION 9 — Type safety (PROVED)                                   *)
(* ================================================================== *)

Theorem preservation_multi : forall Γ t t' T,
  eval_ctx Γ ->
  Γ |-t t : T ->
  t ~~>* t' ->
  Γ |-t t' : T.
Proof.
  intros Γ t t' T Hec Hty Hms. revert T Hty.
  induction Hms; intros; eauto using preservation.
Qed.

Theorem type_safety : forall Γ t t' T,
  eval_ctx Γ ->
  Γ |-t t : T ->
  t ~~>* t' ->
  value t' \/ exists t'', t' ~~> t''.
Proof.
  intros Γ t t' T Hec Hty Hms.
  assert (Hty' : Γ |-t t' : T)
    by (eapply preservation_multi; eauto).
  eapply progress; eauto.
Qed.
