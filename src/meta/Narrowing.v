Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import CtxMap.
Require Import Subst.

(* ================================================================== *)
(* Narrowing: the F<: narrowing and replacement theory.               *)
(*                                                                    *)
(* lt_of_ty monotonicity (in fuel, under subtyping, under narrowing)  *)
(* and the narrowing/replacement theory ([NT_*]/[RT_*]/[sub_NT]/      *)
(* [sub_narrow_ty]) — subtyping infrastructure independent of any     *)
(* particular safety theorem.  The subsumption-stripping inversions   *)
(* this feeds (e.g. [sub_ty_all_inv_full]) live in safety/TypingInv.v.*)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* F<: narrowing for subtyping (the system is full F<:: SA_TyAll has  *)
(* distinct, contravariant bounds).                                   *)
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
(* (b) and (c) are standard de Bruijn / lattice facts (e.g.           *)
(* `sub_weaken_ty_shift`); everything here is proved.                 *)
(* ------------------------------------------------------------------ *)


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
  - apply LS_JoinL; eauto.
  - apply LS_JoinR1; eauto. eapply lt_wf_lookup_eq; eauto.
  - apply LS_JoinR2; eauto. eapply lt_wf_lookup_eq; eauto.
Qed.


(* `lt_join_mono` (lt_join is monotone in both arguments) lives in      *)
(* SubstTy.v and is in scope via Subst.                               *)

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
                     |Γ K l Ts Hwfl HwfTs
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
                     |Γ K l Ts Hwfl HwfTs
                     |Γ A HwfA IHA
                     |Γ B A HwfB IHB HwfA IHA]; intros f Hf.
    + rewrite (lt_of_ty_ctx_var f Γ α), (lt_of_ty_ctx_var (S f) Γ α).
      destruct f as [|f'].
      * rewrite Hlk. apply LS_Free. eapply lt_of_ty_ctx_wf; eauto. lia.
      * rewrite Hlk. apply IHB. lia.
    + rewrite !lt_of_ty_ctx_fun. apply LS_Refl. exact Hwfl.
    + rewrite !lt_of_ty_ctx_ctor. apply lt_join_mono.
      * apply LS_Refl. exact Hwfl.
      * eapply lt_of_ty_ctx_list_fuel_mono_S; eauto.
    + rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
  - intros f G Ts Hwf. induction Hwf; intros Hf.
    + rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + rewrite !lt_of_ty_ctx_list_cons. apply lt_join_mono.
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
    rewrite !lt_of_ty_ctx_ctor. apply lt_join_mono; [exact Hls|].
    apply LS_Refl. eapply lt_of_ty_ctx_list_wf; eauto.
  - (* SA_Any *)
    (* lt_of_ty_ctx f Γ T <: Δ <: lt_of_ty_ctx f Γ (any Δ []).          *)
    unfold lt_of_ty_G in Hls.
    eapply LS_Trans.
    + eapply LS_Trans; [ apply lt_of_ty_ctx_fuel_mono; [exact HwfT|apply Nat.le_refl|exact Hf] | exact Hls ].
    + rewrite lt_of_ty_ctx_ctor. apply LS_JoinR1.
      * apply LS_Refl. exact HwfD.
      * constructor.
  - (* SA_Fun *) destruct f as [|f']; simpl; assumption.
  - (* SA_LtAll *) destruct f as [|f']; simpl; apply LS_Refl; constructor.
  - (* SA_TyAll *) destruct f as [|f']; simpl; apply LS_Refl; constructor.
Qed.

(* The [NarrowTy] relation itself (`G` wider/sup context, `G'` the    *)
(* narrowed/sub context), its lookup lemmas, and the wf-transport     *)
(* lemmas [lt_wf_NT]/[ty_wf_NT]/[ty_wf_NT_all] are defined in         *)
(* SubstTy.v (needed there for [type_ty_all_narrow_bound]) and are in *)
(* scope via Subst.  This file develops the rest of the theory.       *)

Lemma NT_length : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' -> length G = length G'.
Proof. intros Bsub Bsup G G' H. induction H; simpl; lia. Qed.

Lemma lt_sub_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall l1 l2, G ⊢ₗ l1 <: l2 -> G' ⊢ₗ l1 <: l2.
Proof.
  intros Bsub Bsup G G' HN l1 l2 H.
  eapply lt_sub_lookup_eq; [exact H |].
  intros x. apply (NT_lookup_lt Bsub Bsup G G' HN x).
Qed.

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
      rewrite !lt_of_ty_ctx_ctor. apply lt_join_mono.
      * apply LS_Refl. eapply lt_wf_NT; eauto.
      * apply (IHTs Bsub Bsup G' HN Hf).
    + intros Γ A HwfA IHA Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + intros Γ B A HwfB IHB HwfA IHA Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + intros Γ Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + intros Γ T Ts HwfT IHT HwfTs IHTs Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_list_cons. apply lt_join_mono.
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
      rewrite !lt_of_ty_ctx_ctor. apply lt_join_mono.
      * apply LS_Refl. eapply lt_wf_NT; eauto.
      * apply (IHTs Bsub Bsup G' HN Hf).
    + intros Γ A HwfA IHA Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + intros Γ B A HwfB IHB HwfA IHA Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + intros Γ Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + intros Γ T Ts HwfT IHT HwfTs IHTs Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_list_cons. apply lt_join_mono.
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


Lemma lt_of_ty_G_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall T, ty_wf G T -> G' ⊢ₗ lt_of_ty_G G' T <: lt_of_ty_G G T.
Proof.
  intros Bsub Bsup G G' HN T HwfT. unfold lt_of_ty_G.
  rewrite <- (NT_length Bsub Bsup G G' HN).
  apply (lt_of_ty_ctx_NT Bsub Bsup G G' HN (List.length G) T HwfT (Nat.le_refl _)).
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


(* SA_Any side-condition transport for the generic sub payload:       *)
(* narrowing can only SHRINK the computed lifetime, so compose        *)
(* [lt_of_ty_G_NT] with the transported bound by transitivity (the    *)
(* same shape as [sub_any_SubstTy]).                                  *)
Lemma sub_any_NT : forall Bsub Bsup (p : unit) G G' T Δ,
  NarrowTy Bsub Bsup G G' -> ty_wf G T ->
  G' ⊢ₗ lt_of_ty_G G T <: Δ ->
  G' ⊢ₗ lt_of_ty_G G' T <: Δ.
Proof.
  intros Bsub Bsup p G G' T Δ HN HwfT Hle.
  eapply LS_Trans; [apply (lt_of_ty_G_NT Bsub Bsup G G' HN T HwfT)|exact Hle].
Qed.

Lemma sub_NT : forall G S T, G ⊢ S <:: T ->
  forall Bsub Bsup G', NarrowTy Bsub Bsup G G' -> G' ⊢ S <:: T.
Proof.
  intros G S T H Bsub Bsup G' HN.
  exact (sub_ctx_map _ _ _ _ _ _ (CtxMapSpec_NT Bsub Bsup)
           (sub_any_NT Bsub Bsup) G S T H tt G' HN).
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

