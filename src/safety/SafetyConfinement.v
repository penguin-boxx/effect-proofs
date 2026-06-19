Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import SubstitutionTheory.
Require Import SafetyMarkers.
Require Import SafetyProgress.
Require Import SafetyElim1.
Require Import SafetyElim2.

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
  eval_ctx Γ ->
  Γ ⊢ₗ l1 <: l2 ->
  no_local_lt l2 = true ->
  no_local_lt l1 = true.
Proof.
  intros Γ l1 l2 Hec H. induction H; intros Hsup; simpl in *.
  - (* LS_Free  : free <: l   — free has no local *) reflexivity.
  - (* LS_Local : l <: local  — supertype IS local, premise absurd *)
    discriminate Hsup.
  - (* LS_Var   : impossible under eval_ctx, which has no lt binders. *)
    rewrite (eval_ctx_no_lt _ x Hec) in H. discriminate.
  - (* LS_Refl  *) exact Hsup.
  - (* LS_Trans *) apply IHlt_sub1. exact Hec. apply IHlt_sub2. exact Hec. exact Hsup.
  - (* LS_MinL  : lt_min l1 l2 <: l *)
    rewrite (IHlt_sub1 Hec Hsup). rewrite (IHlt_sub2 Hec Hsup). reflexivity.
  - (* LS_MinR1 : l <: lt_min l1 l2 *)
    apply IHlt_sub. exact Hec.
    destruct (no_local_lt l1) eqn:E1; simpl in Hsup; [reflexivity | discriminate].
  - (* LS_MinR2 : l <: lt_min l1 l2 *)
    apply IHlt_sub. exact Hec.
    destruct (no_local_lt l2) eqn:E2;
      [reflexivity | destruct (no_local_lt l1); simpl in Hsup; discriminate].
Qed.

(* Lattice form: the top lifetime `local` never outlives the bottom   *)
(* `free`.  Holds in *any* context (no `eval_ctx` needed): even       *)
(* context-bounded lt-variables cannot bridge `local` to `free`.      *)
Theorem lt_local_not_escapes : forall Γ,
  eval_ctx Γ ->
  ~ (Γ ⊢ₗ lt_local <: lt_free).
Proof.
  intros Γ Hec H.
  pose proof (lt_sub_no_local_mono _ _ _ Hec H (eq_refl : no_local_lt lt_free = true))
    as Hcontra.
  simpl in Hcontra. discriminate.
Qed.

(* Value/type form: a `local`-annotated data value can never be       *)
(* subsumed to the same data carrying `free`.  This is the            *)
(* "no escape via subtyping" theorem for local values.                *)
Theorem local_data_not_escapes : forall Γ K Ts,
  eval_ctx Γ ->
  ctx_lookup_eff Γ K = None ->
  K <> any_tag ->
  ~ (Γ ⊢ type_ctor K lt_local Ts <:: type_ctor K lt_free Ts).
Proof.
  intros Γ K Ts Hec Hdata HK H.
  destruct (sub_ctor_inv _ _ _ _ _ Hec H HK) as [l' [Heq Hlsub]].
  injection Heq as Hl'. subst l'.
  exact (lt_local_not_escapes _ Hec Hlsub).
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

(* Operational non-escape: a value produced at an escapable `free`    *)
(* data type is a constructor whose *own* lifetime annotation         *)
(* provably contains no top-level `local`.  Equivalently, a value     *)
(* confined to a `local` lifetime is never the result a program       *)
(* hands back at a `free` (escapable) type.                           *)
Theorem local_value_does_not_escape : forall Γ t K Ts v,
  eval_ctx Γ ->
  ctx_lookup_eff Γ K = None ->
  K <> any_tag ->
  (forall u, multi_step t u -> Γ ⊢ₜ u : type_ctor K lt_free Ts) ->
  multi_step t v ->
  value v ->
  exists K' l' lts' vs,
    v = term_ctor K' l' lts' Ts vs /\
    no_local_lt l' = true.
Proof.
  intros Γ t K Ts v Hec Hdata HK Hty_reachable Hms Hval.
  pose proof (Hty_reachable _ Hms) as Htyv.
  destruct (canonical_ctor_data _ _ _ _ _ Hec Hdata Htyv Hval HK)
    as [K' [l' [lts' [Ts' [vs [Hveq Hvs]]]]]].
  subst v.
  apply ctor_typing_inv in Htyv.
  destruct Htyv as
    (n_lt & n_ty & sig & res & result_tag & Hlk & Hltlen & HTslen & Hresult &
     Hlts_bound & Hvslen & Hf2 & Hsub).
  destruct (sub_ctor_inv _ _ _ _ _ Hec Hsub HK) as [lx [Heq Hlsub]].
  injection Heq as HKeq Hleq HTseq.
  subst result_tag. subst Ts'.
  exists K', l', lts', vs. split; [reflexivity|].
  rewrite Hleq.
  apply (lt_sub_no_local_mono _ _ _ Hec Hlsub).
  reflexivity.
Qed.

(* ================================================================== *)
(*                                                                    *)
(*                   CAPABILITY CONFINEMENT                           *)
(*                                                                    *)
(* A runtime capability `cap_E^m _ _` is the only construct whose     *)
(* typing rule (`T_Cap`) consults the effect environment: it is       *)
(* well-typed solely in a context that *binds* the effect tag `E`.    *)
(* Capabilities are minted by `S_Handle`, which wraps each one        *)
(* immediately inside its own `handler_m m` delimiter.  Under the     *)
(* full effectful calculus, typing alone no longer rules out visible  *)
(* capabilities; the runtime `marker_ok` invariant does.              *)
(* ================================================================== *)

Lemma marker_ok_plug_cap_pure_in : forall ms E E_tag m n_beta Ts T_R op_body,
  pure_ectx_m m E ->
  marker_ok ms (plug E (term_cap E_tag m n_beta Ts T_R op_body)) ->
  In m ms.
Proof.
  intros ms E E_tag m n_beta Ts T_R op_body Hpure.
  revert ms. induction Hpure; simpl; intros ms Hmok.
  - exact (proj1 Hmok).
  - apply IHHpure. exact (proj1 Hmok).
  - apply IHHpure. exact (proj2 Hmok).
  - apply IHHpure. exact Hmok.
  - apply IHHpure. exact Hmok.
  - apply IHHpure.
    induction vs as [|u vs IHvs]; simpl in Hmok; [tauto|].
    apply IHvs. tauto.
  - apply IHHpure. exact (proj1 Hmok).
  - apply (IHHpure (m' :: ms)) in Hmok.
    destruct Hmok as [Heq | Hin]; [subst; contradiction|exact Hin].
  - apply IHHpure. exact (proj1 Hmok).
  - apply IHHpure. exact (proj2 Hmok).
  all: tauto.
Qed.

Theorem capability_confined : forall E E_tag m n_beta Ts T_R op_body,
  marker_ok [] (plug E (term_cap E_tag m n_beta Ts T_R op_body)) ->
  ~ pure_ectx_m m E.
Proof.
  intros E E_tag m n_beta Ts T_R op_body Hmok Hpure.
  pose proof (marker_ok_plug_cap_pure_in [] E E_tag m n_beta Ts T_R op_body Hpure Hmok) as Hin.
  inversion Hin.
Qed.

Theorem capability_never_exposed : forall Γ t E E_tag m n_beta Ts T_R op_body T,
  eval_ctx Γ ->
  (forall u, multi_step t u -> marker_ok [] u) ->
  Γ ⊢ₜ t : T ->
  multi_step t (plug E (term_cap E_tag m n_beta Ts T_R op_body)) ->
  ~ pure_ectx_m m E.
Proof.
  intros Γ t E E_tag m n_beta Ts T_R op_body T Hec Hmok_reachable Hty Hms Hpure.
  pose proof (Hmok_reachable _ Hms) as Hmok'.
  eapply capability_confined; eauto.
Qed.

Corollary capability_under_handler : forall Γ t E E_tag m n_beta Ts T_R op_body T,
  eval_ctx Γ ->
  (forall u, multi_step t u -> marker_ok [] u) ->
  Γ ⊢ₜ t : T ->
  multi_step t (plug E (term_cap E_tag m n_beta Ts T_R op_body)) ->
  ~ pure_ectx_m m E.
Proof.
  intros Γ t E E_tag m n_beta Ts T_R op_body T Hec Hmok Hty Hms Hpure.
  eapply capability_never_exposed; eauto.
Qed.

(* ================================================================== *)
(*            PRESERVATION INFRASTRUCTURE (additive)                  *)
(*                                                                    *)
(* Principal-type inversions for the runtime effect forms, in the     *)
(* style of `resume_typing_inv`: strip subsumption and recover the    *)
(* premises of the introducing rule together with the residual        *)
(* subtyping `<intro type> <:: T`.                                    *)
(* ================================================================== *)

Lemma handler_m_typing_inv : forall Γ m T_B T_R t T,
  Γ ⊢ₜ term_handler_m m T_B T_R t : T ->
  Γ ⊢ₜ t : T_B /\ Γ ⊢ T_B <:: T_R /\ no_local_ty_G Γ T_B = true /\ Γ ⊢ T_R <:: T.
Proof.
  intros Γ m T_B T_R t T H.
  remember (term_handler_m m T_B T_R t) as s eqn:Hs.
  induction H; try discriminate Hs.
  - (* T_Sub *) destruct (IHtyping Hs) as [Ht [Hbr [Hnl Hrt]]].
    split; [exact Ht|]. split; [exact Hbr|]. split; [exact Hnl|].
    eapply SA_Trans; [exact Hrt | eassumption].
  - (* T_HandlerM *) injection Hs; intros; subst.
    split; [assumption|]. split; [assumption|]. split; [assumption|].
    apply SA_Refl. assumption.
Qed.

Lemma cap_typing_inv : forall Γ E_tag m n_β Ts T_R op_body T,
  Γ ⊢ₜ term_cap E_tag m n_β Ts T_R op_body : T ->
  exists n_α sig ret sig_β ret_β,
    ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) /\
    List.length Ts = n_α /\
    types_wf Γ Ts /\
    ty_wf Γ T_R /\
    sig_β = inst_op_alpha n_α Ts n_β sig /\
    ret_β = inst_op_alpha n_α Ts n_β ret /\
    (bind_tm sig_β
      :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
      :: push_ty_vars n_β any_at_free Γ)
      ⊢ₜ op_body : shift_ty n_β 0 T_R /\
    Γ ⊢ type_ctor E_tag lt_local Ts <:: T.
Proof.
  intros Γ E_tag m n_β Ts T_R op_body T H.
  remember (term_cap E_tag m n_β Ts T_R op_body) as s eqn:Hs.
  induction H; try discriminate Hs.
  - (* T_Sub *)
    destruct (IHtyping Hs) as
      [n_α [sig [ret [sig_β [ret_β [Heff [HlenTs [HwfTs [HwfTR
        [Hsigβ [Hretβ [Hop Hsub]]]]]]]]]]]].
    exists n_α, sig, ret, sig_β, ret_β.
    split; [exact Heff|]. split; [exact HlenTs|]. split; [exact HwfTs|].
    split; [exact HwfTR|]. split; [exact Hsigβ|]. split; [exact Hretβ|].
    split; [exact Hop|]. eapply SA_Trans; [exact Hsub | eassumption].
  - (* T_Cap *) injection Hs; intros; subst.
    do 5 eexists. repeat split; try eassumption; try reflexivity.
    apply SA_Refl. apply TWF_Ctor; [apply LWF_Local | assumption].
Qed.

Lemma perform_typing_inv : forall Γ recv Ss arg T,
  Γ ⊢ₜ term_perform recv Ss arg : T ->
  exists E_tag Δ Ts n_α n_β sig ret sig_inst ret_inst,
    Γ ⊢ₜ recv : type_ctor E_tag Δ Ts /\
    ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) /\
    List.length Ts = n_α /\
    List.length Ss = n_β /\
    types_wf Γ Ss /\
    forallb (no_local_ty_G Γ) Ss = true /\
    sig_inst = inst_op_arg n_α Ts n_β Ss sig /\
    no_local_ty_G Γ sig_inst = true /\
    ret_inst = inst_op_arg n_α Ts n_β Ss ret /\
    ty_wf Γ ret_inst /\
    Γ ⊢ₜ arg : sig_inst /\
    Γ ⊢ ret_inst <:: T.
Proof.
  intros Γ recv Ss arg T H.
  remember (term_perform recv Ss arg) as s eqn:Hs.
  induction H; try discriminate Hs.
  - (* T_Sub *)
    destruct (IHtyping Hs) as
      [E_tag [Δ [Ts [n_α [n_β [sig [ret [sig_inst [ret_inst
        [Hrecv [Heff [HlenTs [HlenSs [HwfSs [HnlSs [Hsi [Hnlsi
          [Hri [HwfRi [Harg Hsub]]]]]]]]]]]]]]]]]]]].
    exists E_tag, Δ, Ts, n_α, n_β, sig, ret, sig_inst, ret_inst.
    split; [exact Hrecv|]. split; [exact Heff|]. split; [exact HlenTs|].
    split; [exact HlenSs|]. split; [exact HwfSs|]. split; [exact HnlSs|].
    split; [exact Hsi|]. split; [exact Hnlsi|]. split; [exact Hri|].
    split; [exact HwfRi|]. split; [exact Harg|].
    eapply SA_Trans; [exact Hsub | eassumption].
  - (* T_Perform *) injection Hs; intros; subst.
    do 9 eexists. repeat split; try eassumption; try reflexivity.
    apply SA_Refl. assumption.
Qed.

(* ================================================================== *)
(* Evaluation-context typing recomposition (congruence).              *)
(*                                                                    *)
(* If `plug P u : T` and `u'` can be typed at every type `u` can,     *)
(* then `plug P u' : T`.  Proved frame-by-frame; each frame lemma     *)
(* inducts on the typing derivation to thread the outer type through  *)
(* subsumption.                                                       *)
(* ================================================================== *)

Lemma app1_replace : forall Γ f f' t2 T,
  Γ ⊢ₜ term_app f t2 : T ->
  (forall Tf, Γ ⊢ₜ f : Tf -> Γ ⊢ₜ f' : Tf) ->
  Γ ⊢ₜ term_app f' t2 : T.
Proof.
  intros Γ f f' t2 T H Himpl.
  remember (term_app f t2) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_App; [apply Himpl; eassumption | eassumption].
Qed.

Lemma app2_replace : forall Γ t1 u u' T,
  Γ ⊢ₜ term_app t1 u : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_app t1 u' : T.
Proof.
  intros Γ t1 u u' T H Himpl.
  remember (term_app t1 u) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_App; [eassumption | apply Himpl; eassumption].
Qed.

Lemma ty_app_replace : forall Γ u u' S T,
  Γ ⊢ₜ term_ty_app u S : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_ty_app u' S : T.
Proof.
  intros Γ u u' S T H Himpl.
  remember (term_ty_app u S) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_TyApp; [apply Himpl; eassumption | assumption | assumption | assumption].
Qed.

Lemma lt_app_replace : forall Γ u u' l T,
  Γ ⊢ₜ term_lt_app u l : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_lt_app u' l : T.
Proof.
  intros Γ u u' l T H Himpl.
  remember (term_lt_app u l) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_LtApp; [apply Himpl; eassumption | assumption].
Qed.

Lemma match_scrut_replace : forall Γ u u' K nlt ar y n T,
  Γ ⊢ₜ term_match u K nlt ar y n : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_match u' K nlt ar y n : T.
Proof.
  intros Γ u u' K nlt ar y n T H Himpl.
  remember (term_match u K nlt ar y n) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_Match;
      try (apply Himpl; eassumption); try eassumption; try reflexivity.
Qed.

Lemma handler_m_replace : forall Γ m T_B T_R u u' T,
  Γ ⊢ₜ term_handler_m m T_B T_R u : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_handler_m m T_B T_R u' : T.
Proof.
  intros Γ m T_B T_R u u' T H Himpl.
  remember (term_handler_m m T_B T_R u) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_HandlerM; try eassumption.
    apply Himpl; eassumption.
Qed.

Lemma perform_recv_replace : forall Γ u u' Ss arg T,
  Γ ⊢ₜ term_perform u Ss arg : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_perform u' Ss arg : T.
Proof.
  intros Γ u u' Ss arg T H Himpl.
  remember (term_perform u Ss arg) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_Perform;
      try (apply Himpl; eassumption); try eassumption; try reflexivity.
Qed.

Lemma perform_arg_replace : forall Γ recv u u' Ss T,
  Γ ⊢ₜ term_perform recv Ss u : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_perform recv Ss u' : T.
Proof.
  intros Γ recv u u' Ss T H Himpl.
  remember (term_perform recv Ss u) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    eapply T_Perform;
      try (apply Himpl; eassumption); try eassumption; try reflexivity.
Qed.

Lemma Forall2_focus_replace :
  forall (R : term -> type -> Prop) vs u u' ts rhos,
  Forall2 R (vs ++ u :: ts) rhos ->
  (forall ru, R u ru -> R u' ru) ->
  Forall2 R (vs ++ u' :: ts) rhos.
Proof.
  intros R vs u u' ts rhos H Himpl.
  revert rhos H. induction vs as [|v vs IH]; intros rhos H; simpl in *.
  - inversion H; subst. constructor; [apply Himpl; assumption | assumption].
  - inversion H; subst. constructor; [assumption | apply IH; assumption].
Qed.

Lemma ctor_focus_replace : forall Γ K l lts Ts vs u u' ts T,
  Γ ⊢ₜ term_ctor K l lts Ts (vs ++ u :: ts) : T ->
  (forall Tu, Γ ⊢ₜ u : Tu -> Γ ⊢ₜ u' : Tu) ->
  Γ ⊢ₜ term_ctor K l lts Ts (vs ++ u' :: ts) : T.
Proof.
  intros Γ K l lts Ts vs u u' ts T H Himpl.
  remember (term_ctor K l lts Ts (vs ++ u :: ts)) as s eqn:Hs. revert Hs.
  induction H; intros Hs; try discriminate Hs.
  - eapply T_Sub; [apply IHtyping; try exact Himpl; exact Hs | assumption].
  - injection Hs; intros; subst.
    assert (Hlen : length (vs ++ u' :: ts) = length (vs ++ u :: ts))
      by (rewrite !length_app; reflexivity).
    eapply T_Ctor;
      try (rewrite Hlen; eassumption);
      try (eapply Forall2_focus_replace;
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

