Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import Markers.
Require Import Progress.

(* ================================================================== *)
(* Narrowing: typing/subtyping inversions and F<: narrowing theory.    *)
(*                                                                    *)
(* Split out of Progress: these lemmas (lambda/forall typing          *)
(* inversions, the ∀-subtyping inversions, lt_of_ty monotonicity, and *)
(* the narrowing/replacement theory [NT_*]/[RT_*]/[sub_NT]) are        *)
(* subtyping infrastructure, unrelated to the progress theorem.       *)
(* ================================================================== *)

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
  - injection Ht; intros; subst. exists l, B; split; [assumption|].
    apply SA_Refl. constructor.
    + match goal with HwfA : ty_wf Γ A |- _ => exact HwfA end.
    + match goal with Hcap : Γ ⊢ₗ capture_lt Γ body <: l |- _ =>
        destruct (lt_sub_wf _ _ _ Hcap) as [_ Hwfl]; exact Hwfl
      end.
    + match goal with HwfB : ty_wf Γ B |- _ => exact HwfB end.
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
  - injection Ht; intros; subst. exists T; split; [assumption|].
    apply SA_Refl. constructor.
    + match goal with HwfBound : ty_wf Γ bound |- _ => exact HwfBound end.
    + match goal with HwfT : ty_wf (bind_ty bound :: Γ) T |- _ => exact HwfT end.
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
  - injection Ht; intros; subst. exists T; split; [assumption|].
    apply SA_Refl. constructor.
    match goal with HwfT : ty_wf (bind_lt lt_local :: Γ) T |- _ => exact HwfT end.
Qed.

Lemma resume_typing_inv : forall Γ m T_B T_R b T,
  Γ ⊢ₜ term_resume m T_B T_R b : T ->
  exists A,
    (bind_tm A :: Γ) ⊢ₜ b : T_B /\
    Γ ⊢ type_fun A lt_local T_R <:: T.
Proof.
  intros Γ m T_B T_R b T Hty.
  remember (term_resume m T_B T_R b) as t eqn:Ht.
  induction Hty; try discriminate.
  - subst. destruct (IHHty eq_refl) as [A0 [Hbody Hsub]].
    exists A0; split; auto. eapply SA_Trans; eauto.
  - injection Ht; intros; subst. exists A; split; [assumption|].
    apply SA_Refl. constructor.
    + match goal with HwfA : ty_wf Γ A |- _ => exact HwfA end.
    + constructor.
    + match goal with HwfTR : ty_wf Γ T_R |- _ => exact HwfTR end.
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
  - (* Refl *) inversion HU; subst. inversion H; subst.
    exists T0. split; [reflexivity|apply SA_Refl; assumption].
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
(* Kernel-F<: narrowing for subtyping.                                *)
(*                                                                    *)
(* Replacing the bound of a type-variable binder by a *subtype*       *)
(* preserves any subtyping derivation under it.  We prove this by     *)
(* induction on the derivation, generalised over an arbitrary context *)
(* prefix `Δ` so the binder cases (`SA_LtAll`/`SA_TyAll`) go through. *)
(*                                                                    *)
(* Three context-level facts are needed:                              *)
(*   (a) lifetime subtyping is invariant under narrowing a `bind_ty`  *)
(*       (proved: `ctx_lookup_lt` skips `bind_ty` entries),           *)
(*   (b) general (no-shift) weakening of `<::` — for the `SA_VarCtx`  *)
(*       case when the looked-up variable *is* the narrowed one,      *)
(*   (c) `lt_of_ty_G` is monotone under narrowing — narrowing a bound *)
(*       to a subtype can only shrink the computed `lt_∅`.            *)
(* (b) and (c) are standard de Bruijn / lattice facts kept axiomatic, *)
(* in the same spirit as `sub_weaken_ty`; everything else is proved.  *)
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
Lemma lt_wf_lookup_eq : forall G1 l,
  lt_wf G1 l ->
  forall G2, (forall x, ctx_lookup_lt G1 x = ctx_lookup_lt G2 x) -> lt_wf G2 l.
Proof.
  intros G1 l Hwf. induction Hwf; intros G2 Heq.
  - econstructor. rewrite <- (Heq x). exact H.
  - constructor.
  - constructor.
  - constructor; eauto.
Qed.

Lemma lt_sub_lookup_eq : forall G1 l1 l2,
  G1 ⊢ₗ l1 <: l2 ->
  forall G2, (forall x, ctx_lookup_lt G1 x = ctx_lookup_lt G2 x) ->
  G2 ⊢ₗ l1 <: l2.
Proof.
  intros G1 l1 l2 H.
  induction H as [Γ l Hwf|Γ l Hwf|Γ x Δ Hlk HwfD|Γ l Hwf
                 |Γ l1 l2 l3 H1 IH1 H2 IH2|Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H1 IH1 Hwf2|Γ l l1 l2 H1 IH1 Hwf1]; intros G2 Heq.
  - apply LS_Free. eapply lt_wf_lookup_eq; eauto.
  - apply LS_Local. eapply lt_wf_lookup_eq; eauto.
  - apply LS_Var.
    + rewrite <- (Heq x). exact Hlk.
    + eapply lt_wf_lookup_eq; eauto.
  - apply LS_Refl. eapply lt_wf_lookup_eq; eauto.
  - eapply LS_Trans; eauto.
  - apply LS_MinL; eauto.
  - apply LS_MinR1; eauto. eapply lt_wf_lookup_eq; eauto.
  - apply LS_MinR2; eauto. eapply lt_wf_lookup_eq; eauto.
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
(* Lattice helper: `lt_min` is monotone in both arguments.            *)
(* ------------------------------------------------------------------ *)
Lemma lt_min_mono : forall G a a' b b',
  G ⊢ₗ a <: a' -> G ⊢ₗ b <: b' -> G ⊢ₗ lt_min a b <: lt_min a' b'.
Proof.
  intros G a a' b b' Ha Hb.
  destruct (lt_sub_wf _ _ _ Ha) as [_ Hwfa'].
  destruct (lt_sub_wf _ _ _ Hb) as [_ Hwfb'].
  apply LS_MinL.
  - eapply LS_Trans; [exact Ha |].
    apply LS_MinR1.
    + apply LS_Refl. exact Hwfa'.
    + exact Hwfb'.
  - eapply LS_Trans; [exact Hb |].
    apply LS_MinR2.
    + apply LS_Refl. exact Hwfb'.
    + exact Hwfa'.
Qed.

(* ------------------------------------------------------------------ *)
(* `lt_of_ty_ctx` is monotone in its fuel argument: with more fuel,   *)
(* type-variable chains are resolved further, which can only *raise*  *)
(* the computed lifetime (chains that run out of fuel bottom out at   *)
(* `lt_free`, the lattice bottom).                                    *)
(* ------------------------------------------------------------------ *)
Lemma lt_of_ty_ctx_wf : forall f G T,
  ty_wf G T -> f <= List.length G -> lt_wf G (lt_of_ty_ctx f G T)
with lt_of_ty_ctx_list_wf : forall f G Ts,
  types_wf G Ts -> f <= List.length G -> lt_wf G (lt_of_ty_ctx_list f G Ts).
Proof.
  - intros f G T Hwf. revert f.
    induction Hwf as [Γ α B Hlk HwfB IHB
                     |Γ A l B HwfA IHA Hwfl HwfB IHB
                     |Γ K l Ts Hwfl HwfTs IHTs
                     |Γ A HwfA IHA
                     |Γ B A HwfB IHB HwfA IHA]; intros f Hf.
    + rewrite (lt_of_ty_ctx_var f Γ α). destruct f as [|f']; [constructor|].
      rewrite Hlk. apply IHB. lia.
    + rewrite lt_of_ty_ctx_fun. exact Hwfl.
    + rewrite lt_of_ty_ctx_ctor. constructor; eauto.
    + rewrite lt_of_ty_ctx_ltall. constructor.
    + rewrite lt_of_ty_ctx_tyall. constructor.
  - intros f G Ts Hwf. induction Hwf; intros Hf.
    + rewrite lt_of_ty_ctx_list_nil. constructor.
    + rewrite lt_of_ty_ctx_list_cons. constructor.
      * eapply lt_of_ty_ctx_wf; eauto.
      * apply IHHwf. exact Hf.
Qed.

Lemma lt_of_ty_ctx_fuel_mono_S : forall f G T,
  ty_wf G T -> S f <= List.length G ->
  G ⊢ₗ lt_of_ty_ctx f G T <: lt_of_ty_ctx (S f) G T
with lt_of_ty_ctx_list_fuel_mono_S : forall f G Ts,
  types_wf G Ts -> S f <= List.length G ->
  G ⊢ₗ lt_of_ty_ctx_list f G Ts <: lt_of_ty_ctx_list (S f) G Ts.
Proof.
  - intros f G T Hwf. revert f.
    induction Hwf as [Γ α B Hlk HwfB IHB
                     |Γ A l B HwfA IHA Hwfl HwfB IHB
                     |Γ K l Ts Hwfl HwfTs IHTs
                     |Γ A HwfA IHA
                     |Γ B A HwfB IHB HwfA IHA]; intros f Hf.
    + rewrite (lt_of_ty_ctx_var f Γ α), (lt_of_ty_ctx_var (S f) Γ α).
      destruct f as [|f'].
      * rewrite Hlk. apply LS_Free. eapply lt_of_ty_ctx_wf; eauto. lia.
      * rewrite Hlk. apply IHB. lia.
    + rewrite !lt_of_ty_ctx_fun. apply LS_Refl. exact Hwfl.
    + rewrite !lt_of_ty_ctx_ctor. apply lt_min_mono.
      * apply LS_Refl. exact Hwfl.
      * eapply lt_of_ty_ctx_list_fuel_mono_S; eauto.
    + rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
  - intros f G Ts Hwf. induction Hwf; intros Hf.
    + rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + rewrite !lt_of_ty_ctx_list_cons. apply lt_min_mono.
      * eapply lt_of_ty_ctx_fuel_mono_S; eauto.
      * apply IHHwf. exact Hf.
Qed.

Lemma lt_of_ty_ctx_fuel_mono : forall f1 f2 G T,
  ty_wf G T -> f2 <= List.length G -> f1 <= f2 ->
  G ⊢ₗ lt_of_ty_ctx f1 G T <: lt_of_ty_ctx f2 G T.
Proof.
  intros f1 f2 G T Hwf Hf2. revert f1.
  induction f2 as [|f2 IH]; intros f1 Hle.
  - assert (f1 = 0) by lia. subst.
    apply LS_Refl. eapply lt_of_ty_ctx_wf; eauto.
  - destruct (Nat.eq_dec f1 (S f2)) as [Heq|Hneq].
    + subst. apply LS_Refl. eapply lt_of_ty_ctx_wf; eauto.
    + assert (Hle' : f1 <= f2) by lia.
      eapply LS_Trans.
      * apply IH; [lia|exact Hle'].
      * apply lt_of_ty_ctx_fuel_mono_S; assumption.
Qed.

(* ------------------------------------------------------------------- *)
(* `lt_of_ty_ctx` is monotone under subtyping (fixed context), as long *)
(* as the fuel does not exceed the context length (so the `SA_Any`     *)
(* premise, stated at fuel `|G|`, can be transported down via fuel     *)
(* monotonicity).                                                      *)
(* ------------------------------------------------------------------- *)
Lemma lt_of_ty_ctx_mono_sub : forall f G S T,
  G ⊢ S <:: T ->
  f <= List.length G ->
  G ⊢ₗ lt_of_ty_ctx f G S <: lt_of_ty_ctx f G T.
Proof.
  intros f G S T Hsub. revert f.
  induction Hsub as [Γ T Hwf|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                    |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                    |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                    |Γ A A' H1 IH1|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2]; intros f Hf.
  - (* SA_Refl *) apply LS_Refl. eapply lt_of_ty_ctx_wf; eauto.
  - (* SA_Trans *) eapply LS_Trans; [apply IH1 | apply IH2]; exact Hf.
  - (* SA_VarCtx *)
    rewrite (lt_of_ty_ctx_var f). destruct f as [|f'].
    + apply LS_Free. apply (lt_of_ty_ctx_wf 0 Γ B HwfB). lia.
    + rewrite Hlk. apply lt_of_ty_ctx_fuel_mono_S; [exact HwfB|lia].
  - (* SA_Data *)
    rewrite !lt_of_ty_ctx_ctor. apply lt_min_mono; [exact Hls|].
    apply LS_Refl. eapply lt_of_ty_ctx_list_wf; eauto.
  - (* SA_Any *)
    (* lt_of_ty_ctx f Γ T <: Δ <: lt_of_ty_ctx f Γ (any Δ []).          *)
    unfold lt_of_ty_G in Hls.
    eapply LS_Trans.
    + eapply LS_Trans; [ apply lt_of_ty_ctx_fuel_mono; [exact HwfT|apply Nat.le_refl|exact Hf] | exact Hls ].
    + rewrite lt_of_ty_ctx_ctor. apply LS_MinR1.
      * apply LS_Refl. exact HwfD.
      * constructor.
  - (* SA_Fun *) destruct f as [|f']; simpl; assumption.
  - (* SA_LtAll *) destruct f as [|f']; simpl; apply LS_Refl; constructor.
  - (* SA_TyAll *) destruct f as [|f']; simpl; apply LS_Refl; constructor.
Qed.

(* `G` is the wider (sup) context, `G'` the narrowed (sub) context. *)
Inductive NarrowTy : type -> type -> ctx -> ctx -> Prop :=
| NT_here : forall Bsub Bsup Γ,
    Γ ⊢ Bsub <:: Bsup ->
    NarrowTy Bsub Bsup (bind_ty Bsup :: Γ) (bind_ty Bsub :: Γ)
| NT_ty : forall Bsub Bsup G G' A,
    NarrowTy Bsub Bsup G G' ->
  ty_wf G A ->
  ty_wf G' A ->
    NarrowTy Bsub Bsup (bind_ty A :: G) (bind_ty A :: G')
| NT_lt : forall Bsub Bsup G G' D,
    NarrowTy Bsub Bsup G G' ->
  lt_wf G D ->
  lt_wf G' D ->
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

Lemma ty_wf_unshift_ty : forall Γ B S T,
  Γ ⊢ S <:: B ->
  ty_wf (bind_ty B :: Γ) (shift_ty 1 0 T) ->
  ty_wf Γ T.
Proof.
  intros Γ B S T Hsub Hwf.
  pose proof (ty_wf_SubstTy (bind_ty B :: Γ) (shift_ty 1 0 T) Hwf
               S 0 Γ (SubstTy_here Γ B S Hsub)) as HwfSub.
  rewrite subst_ty_shift_cancel in HwfSub. exact HwfSub.
Qed.

Lemma ty_wf_unshift_lt : forall Γ D R T,
  Γ ⊢ₗ R <: D ->
  ty_wf (bind_lt D :: Γ) (shift_lt_in_ty 1 0 T) ->
  ty_wf Γ T.
Proof.
  intros Γ D R T Hsub Hwf.
  pose proof (ty_wf_SubstLt (bind_lt D :: Γ) (shift_lt_in_ty 1 0 T) Hwf
               R 0 Γ (SubstLt_here Γ D R Hsub)) as HwfSub.
  rewrite subst_lt_in_ty_shift_cancel in HwfSub. exact HwfSub.
Qed.

Lemma lt_wf_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall l, lt_wf G l -> lt_wf G' l.
Proof.
  intros Bsub Bsup G G' HN l Hwf.
  eapply lt_wf_lookup_eq; [exact Hwf|].
  intros x. apply (NT_lookup_lt Bsub Bsup G G' HN x).
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
  forall α U, ctx_lookup_ty G α = Some U -> ty_wf G U ->
    exists U', ctx_lookup_ty G' α = Some U'
            /\ G ⊢ U' <:: U
            /\ G' ⊢ U' <:: U.
Proof.
  intros Bsub Bsup G G' HN.
  induction HN as [Bsub Bsup Γ Hsub
                  |Bsub Bsup G G' A HN IH HwfA HwfA'
                  |Bsub Bsup G G' D HN IH HwfD HwfD']; intros α U Hlk HwfU.
  - (* NT_here *) destruct α as [|n].
    + simpl in Hlk. injection Hlk; intros; subst U.
      exists (shift_ty 1 0 Bsub). split; [reflexivity|]. split.
      * apply (sub_weaken_ty_shift Γ Bsup Bsub Bsup Hsub).
      * apply (sub_weaken_ty_shift Γ Bsub Bsub Bsup Hsub).
    + simpl in Hlk.
      destruct (ctx_lookup_ty Γ n) as [W|] eqn:E; simpl in Hlk; [|discriminate].
      injection Hlk; intros; subst U.
      assert (HwfW : ty_wf Γ W).
      { eapply ty_wf_unshift_ty; [exact Hsub|exact HwfU]. }
      assert (HwfTarget : ty_wf (bind_ty Bsub :: Γ) (shift_ty 1 0 W)).
      { eapply ty_wf_InsTy; [exact HwfW|apply InsTy_here]. }
      exists (shift_ty 1 0 W). split; [simpl; rewrite E; reflexivity|].
      split; apply SA_Refl; assumption.
  - (* NT_ty *) destruct α as [|n].
    + simpl in Hlk. injection Hlk; intros; subst U.
      assert (HwfTarget : ty_wf (bind_ty A :: G') (shift_ty 1 0 A)).
      { eapply ty_wf_InsTy; [exact HwfA'|apply InsTy_here]. }
      exists (shift_ty 1 0 A). simpl. split; [reflexivity|]. split; apply SA_Refl; assumption.
    + simpl in Hlk. destruct (ctx_lookup_ty G n) as [W|] eqn:E; simpl in Hlk;
        [|discriminate].
      injection Hlk; intros; subst U.
      assert (HwfW : ty_wf G W).
      { eapply ty_wf_unshift_ty; [apply SA_Refl; exact HwfA|exact HwfU]. }
      destruct (IH n W E HwfW) as [W' [HW' [HsubG HsubG']]].
      exists (shift_ty 1 0 W'). simpl. rewrite HW'. simpl.
      split; [reflexivity|]. split.
      * apply (sub_weaken_ty_shift G A W' W HsubG).
      * apply (sub_weaken_ty_shift G' A W' W HsubG').
  - (* NT_lt *) simpl in Hlk.
    destruct (ctx_lookup_ty G α) as [W|] eqn:E; simpl in Hlk; [|discriminate].
    injection Hlk; intros; subst U.
    assert (HwfW : ty_wf G W).
    { eapply ty_wf_unshift_lt; [apply LS_Refl; exact HwfD|exact HwfU]. }
    destruct (IH α W E HwfW) as [W' [HW' [HsubG HsubG']]].
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

Scheme ty_wf_mutind := Induction for ty_wf Sort Prop
with types_wf_mutind := Induction for types_wf Sort Prop.
Combined Scheme ty_wf_types_wf_mutind from ty_wf_mutind, types_wf_mutind.

(* lt_of_ty_ctx is monotone under narrowing (computed lt_∅ can only shrink) *)
Lemma lt_of_ty_ctx_NT_all : forall f,
  (forall G T, ty_wf G T -> forall Bsub Bsup G',
      NarrowTy Bsub Bsup G G' -> f <= List.length G ->
      G' ⊢ₗ lt_of_ty_ctx f G' T <: lt_of_ty_ctx f G T) /\
  (forall G Ts, types_wf G Ts -> forall Bsub Bsup G',
      NarrowTy Bsub Bsup G G' -> f <= List.length G ->
      G' ⊢ₗ lt_of_ty_ctx_list f G' Ts <: lt_of_ty_ctx_list f G Ts).
Proof.
  induction f as [|f' IHf].
  - apply (ty_wf_types_wf_mutind
      (fun G T _ => forall Bsub Bsup G', NarrowTy Bsub Bsup G G' ->
        0 <= List.length G -> G' ⊢ₗ lt_of_ty_ctx 0 G' T <: lt_of_ty_ctx 0 G T)
      (fun G Ts _ => forall Bsub Bsup G', NarrowTy Bsub Bsup G G' ->
        0 <= List.length G -> G' ⊢ₗ lt_of_ty_ctx_list 0 G' Ts <: lt_of_ty_ctx_list 0 G Ts)).
    + intros Γ α B Hlk HwfB IHBound Bsub Bsup G' HN Hf.
      rewrite !(lt_of_ty_ctx_var 0). apply LS_Refl. constructor.
    + intros Γ A l B HwfA IHA Hwfl HwfB IHB Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_fun. apply LS_Refl. eapply lt_wf_NT; eauto.
    + intros Γ K l Ts Hwfl HwfTs IHTs Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_ctor. apply lt_min_mono.
      * apply LS_Refl. eapply lt_wf_NT; eauto.
      * apply (IHTs Bsub Bsup G' HN Hf).
    + intros Γ A HwfA IHA Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + intros Γ B A HwfB IHB HwfA IHA Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + intros Γ Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + intros Γ T Ts HwfT IHT HwfTs IHTs Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_list_cons. apply lt_min_mono.
      * apply (IHT Bsub Bsup G' HN Hf).
      * apply (IHTs Bsub Bsup G' HN Hf).
  - destruct IHf as [IHf_ty IHf_tys].
    apply (ty_wf_types_wf_mutind
      (fun G T _ => forall Bsub Bsup G', NarrowTy Bsub Bsup G G' ->
        S f' <= List.length G -> G' ⊢ₗ lt_of_ty_ctx (S f') G' T <: lt_of_ty_ctx (S f') G T)
      (fun G Ts _ => forall Bsub Bsup G', NarrowTy Bsub Bsup G G' ->
        S f' <= List.length G -> G' ⊢ₗ lt_of_ty_ctx_list (S f') G' Ts <: lt_of_ty_ctx_list (S f') G Ts)).
    + intros Γ α B Hlk HwfB IHBound Bsub Bsup G' HN Hf.
      rewrite (lt_of_ty_ctx_var (S f') G' α), (lt_of_ty_ctx_var (S f') Γ α).
      destruct (NT_lookup_sub Bsub Bsup Γ G' HN α B Hlk HwfB)
        as [B' [HB' [HsubG HsubG']]].
      rewrite Hlk, HB'.
      destruct (sub_wf _ _ _ HsubG) as [HwfB' _].
      assert (Hf' : f' <= List.length Γ) by lia.
      eapply LS_Trans.
      * apply (IHf_ty Γ B' HwfB' Bsub Bsup G' HN Hf').
      * apply (lt_sub_NT Bsub Bsup Γ G' HN).
        apply (lt_of_ty_ctx_mono_sub f' Γ B' B HsubG Hf').
    + intros Γ A l B HwfA IHA Hwfl HwfB IHB Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_fun. apply LS_Refl. eapply lt_wf_NT; eauto.
    + intros Γ K l Ts Hwfl HwfTs IHTs Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_ctor. apply lt_min_mono.
      * apply LS_Refl. eapply lt_wf_NT; eauto.
      * apply (IHTs Bsub Bsup G' HN Hf).
    + intros Γ A HwfA IHA Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + intros Γ B A HwfB IHB HwfA IHA Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + intros Γ Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + intros Γ T Ts HwfT IHT HwfTs IHTs Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_list_cons. apply lt_min_mono.
      * apply (IHT Bsub Bsup G' HN Hf).
      * apply (IHTs Bsub Bsup G' HN Hf).
Qed.

Lemma lt_of_ty_ctx_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall f T, ty_wf G T -> f <= List.length G ->
    G' ⊢ₗ lt_of_ty_ctx f G' T <: lt_of_ty_ctx f G T.
Proof.
  intros Bsub Bsup G G' HN f T Hwf Hf.
  exact (proj1 (lt_of_ty_ctx_NT_all f) G T Hwf Bsub Bsup G' HN Hf).
Qed.

Lemma lt_of_ty_ctx_list_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall f Ts, types_wf G Ts -> f <= List.length G ->
    G' ⊢ₗ lt_of_ty_ctx_list f G' Ts <: lt_of_ty_ctx_list f G Ts.
Proof.
  intros Bsub Bsup G G' HN f Ts Hwf Hf.
  exact (proj2 (lt_of_ty_ctx_NT_all f) G Ts Hwf Bsub Bsup G' HN Hf).
Qed.

Lemma lt_of_ty_G_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall T, ty_wf G T -> G' ⊢ₗ lt_of_ty_G G' T <: lt_of_ty_G G T.
Proof.
  intros Bsub Bsup G G' HN T HwfT. unfold lt_of_ty_G.
  rewrite <- (NT_length Bsub Bsup G G' HN).
  apply (lt_of_ty_ctx_NT Bsub Bsup G G' HN (List.length G) T HwfT (Nat.le_refl _)).
Qed.

Lemma ty_wf_NT_all :
  (forall G T, ty_wf G T -> forall Bsub Bsup G',
      NarrowTy Bsub Bsup G G' -> ty_wf G' T) /\
  (forall G Ts, types_wf G Ts -> forall Bsub Bsup G',
      NarrowTy Bsub Bsup G G' -> types_wf G' Ts).
Proof.
  apply (ty_wf_types_wf_mutind
    (fun G T _ => forall Bsub Bsup G', NarrowTy Bsub Bsup G G' -> ty_wf G' T)
    (fun G Ts _ => forall Bsub Bsup G', NarrowTy Bsub Bsup G G' -> types_wf G' Ts)).
  - intros Γ α B Hlk HwfB IHBound Bsub Bsup G' HN.
    destruct (NT_lookup_sub Bsub Bsup Γ G' HN α B Hlk HwfB)
      as [B' [HB' [_ HsubG']]].
    destruct (sub_wf _ _ _ HsubG') as [HwfB' _].
    econstructor; eauto.
  - intros Γ A l B HwfA IHA Hwfl HwfB IHB Bsub Bsup G' HN.
    constructor.
    + apply (IHA Bsub Bsup G' HN).
    + eapply lt_wf_NT; eauto.
    + apply (IHB Bsub Bsup G' HN).
  - intros Γ K l Ts Hwfl HwfTs IHTs Bsub Bsup G' HN.
    constructor.
    + eapply lt_wf_NT; eauto.
    + apply (IHTs Bsub Bsup G' HN).
  - intros Γ A HwfA IHA Bsub Bsup G' HN.
    constructor.
    apply (IHA Bsub Bsup (bind_lt lt_local :: G')).
    apply NT_lt; [exact HN|constructor|constructor].
  - intros Γ B A HwfB IHB HwfA IHA Bsub Bsup G' HN.
    constructor.
    + apply (IHB Bsub Bsup G' HN).
    + apply (IHA Bsub Bsup (bind_ty B :: G')).
      apply NT_ty.
      * exact HN.
      * exact HwfB.
      * apply (IHB Bsub Bsup G' HN).
  - intros Γ Bsub Bsup G' HN. constructor.
  - intros Γ T Ts HwfT IHT HwfTs IHTs Bsub Bsup G' HN.
    constructor.
    + apply (IHT Bsub Bsup G' HN).
    + apply (IHTs Bsub Bsup G' HN).
Qed.

Lemma ty_wf_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' -> forall T, ty_wf G T -> ty_wf G' T.
Proof.
  intros Bsub Bsup G G' HN T Hwf.
  exact (proj1 ty_wf_NT_all G T Hwf Bsub Bsup G' HN).
Qed.

Lemma types_wf_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' -> forall Ts, types_wf G Ts -> types_wf G' Ts.
Proof.
  intros Bsub Bsup G G' HN Ts Hwf.
  exact (proj2 ty_wf_NT_all G Ts Hwf Bsub Bsup G' HN).
Qed.

(* Well-formedness of types does not depend on the subtyping strength of a *)
(* type-variable bound, only on the replacement bound being well-formed.   *)
Inductive ReplaceTy : ctx -> ctx -> Prop :=
  | RT_here : forall Γ B B',
      ty_wf Γ B ->
      ty_wf Γ B' ->
      ReplaceTy (bind_ty B :: Γ) (bind_ty B' :: Γ)
  | RT_ty : forall G G' B,
      ReplaceTy G G' ->
      ty_wf G B ->
      ty_wf G' B ->
      ReplaceTy (bind_ty B :: G) (bind_ty B :: G')
  | RT_lt : forall G G' Δ,
      ReplaceTy G G' ->
      lt_wf G Δ ->
      lt_wf G' Δ ->
      ReplaceTy (bind_lt Δ :: G) (bind_lt Δ :: G').

Lemma RT_lookup_lt : forall G G',
  ReplaceTy G G' -> forall x, ctx_lookup_lt G x = ctx_lookup_lt G' x.
Proof.
  intros G G' H. induction H; intro x; simpl.
  - reflexivity.
  - apply IHReplaceTy.
  - destruct x as [|x']; [reflexivity|]. rewrite (IHReplaceTy x'). reflexivity.
Qed.

Lemma RT_lookup_ty : forall G G',
  ReplaceTy G G' ->
  forall α B, ctx_lookup_ty G α = Some B -> ty_wf G B ->
    exists B', ctx_lookup_ty G' α = Some B' /\ ty_wf G' B'.
Proof.
  intros G G' H. induction H as [Γ B B' HwfB HwfB'
                                |G G' B HRT IH HwfB HwfB'
                                |G G' Δ HRT IH HwfΔ HwfΔ'];
    intros α U Hlk HwfU.
  - destruct α as [|α']; simpl in Hlk.
    + injection Hlk; intros; subst U.
      exists (shift_ty 1 0 B'). split; [reflexivity|].
      eapply ty_wf_InsTy; [exact HwfB'|apply InsTy_here].
    + destruct (ctx_lookup_ty Γ α') as [W|] eqn:E; simpl in Hlk; [|discriminate].
      injection Hlk; intros; subst U.
      assert (HwfW : ty_wf Γ W).
      { eapply ty_wf_unshift_ty; [apply SA_Refl; exact HwfB|exact HwfU]. }
      exists (shift_ty 1 0 W). split.
      * simpl. rewrite E. reflexivity.
      * eapply ty_wf_InsTy; [exact HwfW|apply InsTy_here].
  - destruct α as [|α']; simpl in Hlk.
    + injection Hlk; intros; subst U.
      exists (shift_ty 1 0 B). split; [reflexivity|].
      eapply ty_wf_InsTy; [exact HwfB'|apply InsTy_here].
    + destruct (ctx_lookup_ty G α') as [W|] eqn:E; simpl in Hlk; [|discriminate].
      injection Hlk; intros; subst U.
      assert (HwfW : ty_wf G W).
      { eapply ty_wf_unshift_ty; [apply SA_Refl; exact HwfB|exact HwfU]. }
      destruct (IH α' W E HwfW) as [W' [HW' HwfW']].
      exists (shift_ty 1 0 W'). split.
      * simpl. rewrite HW'. reflexivity.
      * eapply ty_wf_InsTy; [exact HwfW'|apply InsTy_here].
  - simpl in Hlk.
    destruct (ctx_lookup_ty G α) as [W|] eqn:E; simpl in Hlk; [|discriminate].
    injection Hlk; intros; subst U.
    assert (HwfW : ty_wf G W).
    { eapply ty_wf_unshift_lt; [apply LS_Refl; exact HwfΔ|exact HwfU]. }
    destruct (IH α W E HwfW) as [W' [HW' HwfW']].
    exists (shift_lt_in_ty 1 0 W'). split.
    + simpl. rewrite HW'. reflexivity.
    + eapply ty_wf_InsLt; [exact HwfW'|apply InsLt_here].
Qed.

Lemma lt_wf_RT : forall G G',
  ReplaceTy G G' -> forall l, lt_wf G l -> lt_wf G' l.
Proof.
  intros G G' HRT l Hwf.
  eapply lt_wf_lookup_eq; [exact Hwf|].
  intros x. apply (RT_lookup_lt G G' HRT x).
Qed.

Lemma ty_wf_RT_all :
  (forall G T, ty_wf G T -> forall G', ReplaceTy G G' -> ty_wf G' T) /\
  (forall G Ts, types_wf G Ts -> forall G', ReplaceTy G G' -> types_wf G' Ts).
Proof.
  apply (ty_wf_types_wf_mutind
    (fun G T _ => forall G', ReplaceTy G G' -> ty_wf G' T)
    (fun G Ts _ => forall G', ReplaceTy G G' -> types_wf G' Ts)).
  - intros Γ α B Hlk HwfB _ G' HRT.
    destruct (RT_lookup_ty Γ G' HRT α B Hlk HwfB) as [B' [HB' HwfB']].
    econstructor; eauto.
  - intros Γ A l B HwfA IHA Hwfl HwfB IHB G' HRT.
    constructor.
    + apply (IHA G' HRT).
    + eapply lt_wf_RT; eauto.
    + apply (IHB G' HRT).
  - intros Γ K l Ts Hwfl HwfTs IHTs G' HRT.
    constructor.
    + eapply lt_wf_RT; eauto.
    + apply (IHTs G' HRT).
  - intros Γ A HwfA IHA G' HRT.
    constructor.
    apply (IHA (bind_lt lt_local :: G')).
    apply RT_lt; [exact HRT|constructor|constructor].
  - intros Γ B A HwfB IHB HwfA IHA G' HRT.
    constructor.
    + apply (IHB G' HRT).
    + apply (IHA (bind_ty B :: G')).
      apply RT_ty.
      * exact HRT.
      * exact HwfB.
      * apply (IHB G' HRT).
  - intros Γ G' HRT. constructor.
  - intros Γ T Ts HwfT IHT HwfTs IHTs G' HRT.
    constructor.
    + apply (IHT G' HRT).
    + apply (IHTs G' HRT).
Qed.

Lemma ty_wf_RT : forall G G',
  ReplaceTy G G' -> forall T, ty_wf G T -> ty_wf G' T.
Proof.
  intros G G' HRT T Hwf.
  exact (proj1 ty_wf_RT_all G T Hwf G' HRT).
Qed.

Lemma types_wf_RT : forall G G',
  ReplaceTy G G' -> forall Ts, types_wf G Ts -> types_wf G' Ts.
Proof.
  intros G G' HRT Ts Hwf.
  exact (proj2 ty_wf_RT_all G Ts Hwf G' HRT).
Qed.

Lemma sub_NT : forall G S T, G ⊢ S <:: T ->
  forall Bsub Bsup G', NarrowTy Bsub Bsup G G' -> G' ⊢ S <:: T.
Proof.
  intros G S T H.
  induction H as [Γ T Hwf|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                 |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                 |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2];
    intros Bsub Bsup G' HN.
  - apply SA_Refl. eapply ty_wf_NT; eauto.
  - eapply SA_Trans; [apply (IH1 _ _ _ HN) | apply (IH2 _ _ _ HN)].
  - destruct (NT_lookup_sub Bsub Bsup Γ G' HN α B Hlk HwfB) as [B' [HB' [_ HsubG']]].
    destruct (sub_wf _ _ _ HsubG') as [HwfB' _].
    eapply SA_Trans; [apply SA_VarCtx; [exact HB'|exact HwfB'] | exact HsubG'].
  - apply SA_Data.
    + apply (lt_sub_NT Bsub Bsup Γ G' HN _ _ Hls).
    + eapply types_wf_NT; eauto.
  - apply SA_Any.
    + eapply ty_wf_NT; eauto.
    + eapply lt_wf_NT; eauto.
    + eapply LS_Trans.
      * apply (lt_of_ty_G_NT Bsub Bsup Γ G' HN T HwfT).
      * apply (lt_sub_NT Bsub Bsup Γ G' HN _ _ Hls).
  - apply SA_Fun.
    + apply (IH1 _ _ _ HN).
    + apply (lt_sub_NT Bsub Bsup Γ G' HN _ _ Hl).
    + apply (IH2 _ _ _ HN).
  - apply SA_LtAll.
    apply (IH1 Bsub Bsup (bind_lt lt_local :: G')).
    apply NT_lt; [exact HN|constructor|constructor].
  - destruct (sub_wf _ _ _ H1) as [HwfB' HwfB].
    pose proof (IH1 Bsub Bsup G' HN) as H1'.
    destruct (sub_wf _ _ _ H1') as [HwfB'_NT HwfB_NT].
    eapply SA_TyAll.
    + eapply ty_wf_NT; [|exact HwfA].
      apply NT_ty; [exact HN|exact HwfB|exact HwfB_NT].
    + eapply ty_wf_NT; [|exact HwfA'].
      apply NT_ty; [exact HN|exact HwfB'|exact HwfB'_NT].
    + exact H1'.
    + apply (IH2 Bsub Bsup (bind_ty B' :: G')).
      apply NT_ty; [exact HN|exact HwfB'|exact HwfB'_NT].
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
  - (* Refl *) inversion HU; subst. inversion H; subst.
    exists B0, T0. split; [reflexivity|]. split.
    + apply SA_Refl; assumption.
    + apply SA_Refl; assumption.
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

(* Replacing one stepping argument inside a well-typed constructor     *)
(* argument list preserves the per-element typing.  The per-element    *)
(* preservation comes from the `typing_ind2` IH packaged as the second *)
(* `Forall2` hypothesis below; this lemma is consumed in the T_Ctor    *)
(* case of `preservation`.                                             *)
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

