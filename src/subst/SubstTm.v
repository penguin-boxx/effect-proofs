Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import ShiftLaws.
Require Import Weakening.
Require Import SubstLt.
Require Import SubstTy.

(* ================================================================== *)
(* SubstTm : substitute a term for a tm-binder at depth n             *)
(*                                                                    *)
(* [SubstTm v n G G'] threads the substituted value v through the     *)
(* binders between the substitution site and the target binder,       *)
(* shifting v at each term binder it crosses.  The typing payload     *)
(* ([typing_SubstTm], in ProgramCtx.v) is proved for CLOSED values    *)
(* under an [eval_ctx]: the syntactic [subst_tm] does not re-shift    *)
(* the value across the type/lifetime binders of match / cap /        *)
(* handle op-bodies, which is only sound because a closed value is    *)
(* fixed by those shifts (see the ProgramCtx.v header).               *)
(* ================================================================== *)

Inductive SubstTm : term -> nat -> ctx -> ctx -> Prop :=
  | SubstTm_here : forall Gamma T v,
      value v ->
      Gamma ⊢ₜ v : T ->
      SubstTm v 0 (bind_tm T :: Gamma) Gamma
  | SubstTm_tm : forall v n G G' A,
      SubstTm v n G G' ->
      SubstTm (shift_tm 1 0 v) (S n) (bind_tm A :: G) (bind_tm A :: G')
  | SubstTm_ty : forall v n G G' B,
      SubstTm v n G G' ->
      SubstTm (shift_ty_in_tm 1 0 v) n (bind_ty B :: G) (bind_ty B :: G')
  | SubstTm_lt : forall v n G G' D,
      SubstTm v n G G' ->
      SubstTm (shift_lt_in_tm 1 0 v) n (bind_lt D :: G) (bind_lt D :: G')
  | SubstTm_ctor : forall v n G G' K n_lt n_ty fields result,
      SubstTm v n G G' ->
      SubstTm v n (bind_ctor K n_lt n_ty fields result :: G)
                  (bind_ctor K n_lt n_ty fields result :: G')
  | SubstTm_eff : forall v n G G' E n_a n_b sig ret,
      SubstTm v n G G' ->
      SubstTm v n (bind_eff E n_a n_b sig ret :: G)
                  (bind_eff E n_a n_b sig ret :: G').

Lemma SubstTm_length : forall v n G G', SubstTm v n G G' -> length G = S (length G').
Proof. intros v n G G' H. induction H; simpl; lia. Qed.


Lemma SubstTm_lookup_tm : forall v n G G', SubstTm v n G G' ->
  forall x, x <> n -> ctx_lookup_tm G' (subst_lt_var n x) = ctx_lookup_tm G x.
Proof.
  intros v n G G' H. induction H; intros x Hne.
  - destruct x as [|x']; [contradiction|]. reflexivity.
  - destruct x as [|x'].
    + reflexivity.
    + assert (x' <> n) by lia.
      rewrite subst_lt_var_S. simpl ctx_lookup_tm. apply IHSubstTm. exact H0.
  - simpl ctx_lookup_tm. rewrite IHSubstTm by exact Hne. reflexivity.
  - simpl ctx_lookup_tm. rewrite IHSubstTm by exact Hne. reflexivity.
  - simpl ctx_lookup_tm. apply IHSubstTm. exact Hne.
  - simpl ctx_lookup_tm. apply IHSubstTm. exact Hne.
Qed.

Lemma SubstTm_lookup_ty : forall v n G G', SubstTm v n G G' ->
  forall a, ctx_lookup_ty G' a = ctx_lookup_ty G a.
Proof.
  intros v n G G' H. induction H; intro a; simpl.
  - reflexivity.
  - apply IHSubstTm.
  - destruct a as [|a']; simpl.
    + reflexivity.
    + rewrite IHSubstTm. reflexivity.
  - rewrite IHSubstTm. reflexivity.
  - apply IHSubstTm.
  - apply IHSubstTm.
Qed.

Lemma SubstTm_lookup_lt : forall v n G G', SubstTm v n G G' ->
  forall x, ctx_lookup_lt G' x = ctx_lookup_lt G x.
Proof.
  intros v n G G' H. induction H; intro x; simpl.
  - reflexivity.
  - apply IHSubstTm.
  - apply IHSubstTm.
  - destruct x as [|x']; simpl.
    + reflexivity.
    + rewrite IHSubstTm. reflexivity.
  - apply IHSubstTm.
  - apply IHSubstTm.
Qed.

Lemma SubstTm_lookup_ctor : forall v n G G', SubstTm v n G G' ->
  forall K, ctx_lookup_ctor G' K = ctx_lookup_ctor G K.
Proof.
  intros v n G G' H.
  induction H as [Gamma T v Hv Hty
                 |v n G G' A H IH
                 |v n G G' B H IH
                 |v n G G' D H IH
                 |v n G G' K0 n_lt n_ty fields result H IH
                 |v n G G' E n_a n_b sig ret H IH]; intro K; simpl.
  - reflexivity.
  - apply IH.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - destruct (Nat.eqb K K0); [reflexivity|apply IH].
  - apply IH.
Qed.

Lemma SubstTm_lookup_eff : forall v n G G', SubstTm v n G G' ->
  forall E, ctx_lookup_eff G' E = ctx_lookup_eff G E.
Proof.
  intros v n G G' H.
  induction H as [Gamma T v Hv Hty
                 |v n G G' A H IH
                 |v n G G' B H IH
                 |v n G G' D H IH
                 |v n G G' K n_lt n_ty fields result H IH
                 |v n G G' E0 n_a n_b sig ret H IH]; intro E; simpl.
  - reflexivity.
  - apply IH.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - apply IH.
  - destruct (Nat.eqb E E0); [reflexivity|apply IH].
Qed.


Lemma lt_of_ty_ctx_SubstTm : forall v n G G', SubstTm v n G G' ->
  forall f T, lt_of_ty_ctx f G' T = lt_of_ty_ctx f G T.
Proof.
  intros v n G G' HSub f. revert G G' HSub.
  induction f as [|f IHf]; intros G G' HSub T.
  - destruct T; reflexivity.
  - revert G G' HSub. induction T using type_list_ind with
      (Q := fun Ts => forall G G', SubstTm v n G G' ->
        lt_of_ty_ctx_list (S f) G' Ts = lt_of_ty_ctx_list (S f) G Ts);
      intros G G' HSub.
    + simpl. rewrite (SubstTm_lookup_ty v n G G' HSub n0).
      destruct (ctx_lookup_ty G n0) as [B|] eqn:HB; [apply (IHf G G' HSub B)|reflexivity].
    + reflexivity.
    + rewrite !lt_of_ty_ctx_ctor. f_equal. apply IHT. exact HSub.
    + reflexivity.
    + reflexivity.
    + rewrite !lt_of_ty_ctx_list_nil. reflexivity.
    + rewrite !lt_of_ty_ctx_list_cons.
      rewrite (IHT G G' HSub), (IHT0 G G' HSub). reflexivity.
Qed.

Lemma lt_of_ty_G_SubstTm : forall v n G G', SubstTm v n G G' ->
  forall T, lt_of_ty_G G' T = lt_of_ty_G G T.
Proof.
  intros v n G G' HSub T. unfold lt_of_ty_G.
  pose proof (SubstTm_length v n G G' HSub) as Hlen.
  rewrite (lt_of_ty_ctx_fuel_irrel (List.length G') (List.length G) T G' 0 (VB_0 T)); try lia.
  apply (lt_of_ty_ctx_SubstTm v n G G' HSub (List.length G) T).
Qed.

Lemma lt_wf_SubstTm : forall G l,
  lt_wf G l -> forall v n G', SubstTm v n G G' -> lt_wf G' l.
Proof.
  intros G l Hwf. induction Hwf; intros v n G' HSub.
  - econstructor. rewrite (SubstTm_lookup_lt v n Γ G' HSub x). exact H.
  - constructor.
  - constructor.
  - constructor.
    + apply (IHHwf1 v n G' HSub).
    + apply (IHHwf2 v n G' HSub).
Qed.

Lemma lifetimes_wf_SubstTm : forall G lts,
  lifetimes_wf G lts -> forall v n G', SubstTm v n G G' -> lifetimes_wf G' lts.
Proof.
  intros G lts Hwf. induction Hwf; intros v n G' HSub.
  - constructor.
  - constructor.
    + eapply lt_wf_SubstTm; eauto.
    + apply (IHHwf v n G' HSub).
Qed.

Definition capture_var_lifetime (G : ctx) (x : nat) : lifetime :=
  match ctx_lookup_tm G x with
  | Some T => lt_of_ty_G G T
  | None => lt_free
  end.

Definition capture_vars (G : ctx) (xs : list nat) : lifetime :=
  fold_right (fun x acc => lt_min (capture_var_lifetime G x) acc) lt_free xs.

Lemma capture_lt_no_cap : forall G t,
  has_rt_cap t = false -> capture_lt G t = capture_vars G (free_tm_vars 1 t).
Proof.
  intros G t Hcap. unfold capture_lt, capture_vars, capture_var_lifetime.
  rewrite Hcap. reflexivity.
Qed.

Lemma capture_var_lifetime_SubstTm_eq : forall v n G G',
  SubstTm v n G G' -> forall x,
  x <> n ->
  capture_var_lifetime G' (subst_lt_var n x) = capture_var_lifetime G x.
Proof.
  intros v n G G' HSub x Hne. unfold capture_var_lifetime.
  rewrite (SubstTm_lookup_tm v n G G' HSub x Hne).
  destruct (ctx_lookup_tm G x) as [T|] eqn:Hlk; [|reflexivity].
  apply (lt_of_ty_G_SubstTm v n G G' HSub T).
Qed.

Lemma capture_vars_contains : forall G xs x,
  In x xs ->
  lt_wf G (capture_vars G xs) ->
  G ⊢ₗ capture_var_lifetime G x <: capture_vars G xs.
Proof.
  induction xs as [|y ys IH]; intros x Hin Hwf; simpl in *; [contradiction|].
  inversion Hwf; subst.
  destruct Hin as [Heq|Hin].
  - subst y. apply LS_MinR1.
    + apply LS_Refl. assumption.
    + assumption.
  - apply LS_MinR2.
    + apply IH; assumption.
    + assumption.
Qed.

Lemma capture_vars_subst_tm_fv_le : forall v n G G' xs,
  SubstTm v n G G' ->
  lt_wf G (capture_vars G xs) ->
  G' ⊢ₗ capture_vars G' (subst_tm_fv n xs) <: capture_vars G xs.
Proof.
  intros v n G G' xs HSub. induction xs as [|x xs IH]; intros Hwf; simpl in *.
  - apply LS_Refl. constructor.
  - inversion Hwf as [| | | ? ? ? Hhead Htail]; subst.
    destruct (Nat.eqb x n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst x.
      apply LS_MinR2.
      * apply IH. exact Htail.
      * eapply lt_wf_SubstTm; eauto.
    + apply Nat.eqb_neq in Heq.
      assert (Heqlife : capture_var_lifetime G' (if Nat.ltb n x then pred x else x) =
        capture_var_lifetime G x).
      { change (capture_var_lifetime G' (subst_lt_var n x) = capture_var_lifetime G x).
        apply (capture_var_lifetime_SubstTm_eq v n G G' HSub x Heq). }
      apply lt_min_mono.
      * rewrite Heqlife. apply LS_Refl.
        exact (lt_wf_SubstTm G (capture_var_lifetime G x) Hhead v n G' HSub).
      * apply IH. exact Htail.
Qed.

Lemma ty_wf_SubstTm : forall G T,
  ty_wf G T -> forall v n G', SubstTm v n G G' -> ty_wf G' T
with types_wf_SubstTm : forall G Ts,
  types_wf G Ts -> forall v n G', SubstTm v n G G' -> types_wf G' Ts.
Proof.
  - intros G T Hwf. induction Hwf; intros v n G' HSub.
    + econstructor.
      * rewrite (SubstTm_lookup_ty v n Γ G' HSub α). exact H.
      * apply (IHHwf v n G' HSub).
    + constructor.
      * apply (IHHwf1 v n G' HSub).
      * eapply lt_wf_SubstTm; eauto.
      * apply (IHHwf2 v n G' HSub).
    + constructor.
      * eapply lt_wf_SubstTm; eauto.
      * eapply types_wf_SubstTm; eauto.
    + constructor. apply (IHHwf (shift_lt_in_tm 1 0 v) n (bind_lt lt_local :: G')). apply SubstTm_lt. exact HSub.
    + constructor.
      * apply (IHHwf1 v n G' HSub).
      * apply (IHHwf2 (shift_ty_in_tm 1 0 v) n (bind_ty B :: G')). apply SubstTm_ty. exact HSub.
  - intros G Ts Hwf. induction Hwf; intros v n G' HSub.
    + constructor.
    + constructor.
      * eapply ty_wf_SubstTm; eauto.
      * apply (IHHwf v n G' HSub).
Qed.

Lemma lt_sub_SubstTm : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall v n G', SubstTm v n G G' -> G' ⊢ₗ l1 <: l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l Hwf|Γ l Hwf|Γ x Δ Hlk Hwf|Γ l Hwf
                 |Γ l1 l2 l3 H12 IH12 H23 IH23
                 |Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H IH Hwf2|Γ l l1 l2 H IH Hwf1]; intros v n G' HSub.
  - apply LS_Free. eapply lt_wf_SubstTm; eauto.
  - apply LS_Local. eapply lt_wf_SubstTm; eauto.
  - apply LS_Var.
    + rewrite (SubstTm_lookup_lt v n Γ G' HSub x). exact Hlk.
    + eapply lt_wf_SubstTm; eauto.
  - apply LS_Refl. eapply lt_wf_SubstTm; eauto.
  - eapply LS_Trans; [apply (IH12 v n G' HSub) | apply (IH23 v n G' HSub)].
  - apply LS_MinL; [apply (IH1 v n G' HSub)|apply (IH2 v n G' HSub)].
  - apply LS_MinR1.
    + apply (IH v n G' HSub).
    + eapply lt_wf_SubstTm; eauto.
  - apply LS_MinR2.
    + apply (IH v n G' HSub).
    + eapply lt_wf_SubstTm; eauto.
Qed.

(* Escape side-condition transport under term substitution (type unchanged). *)
Lemma sub_free_SubstTm : forall v n G G' T,
  SubstTm v n G G' -> G ⊢ₗ lt_of_ty_G G T <: lt_free ->
  G' ⊢ₗ lt_of_ty_G G' T <: lt_free.
Proof.
  intros v n G G' T HS H. rewrite (lt_of_ty_G_SubstTm v n G G' HS T).
  eapply lt_sub_SubstTm; eauto.
Qed.

Lemma sub_free_list_SubstTm : forall v n G G' Ss,
  SubstTm v n G G' -> Forall (fun S => G ⊢ₗ lt_of_ty_G G S <: lt_free) Ss ->
  Forall (fun S => G' ⊢ₗ lt_of_ty_G G' S <: lt_free) Ss.
Proof.
  intros v n G G' Ss HS H. induction H; constructor;
    [eapply sub_free_SubstTm; eauto | auto].
Qed.

Lemma capture_lt_SubstTm_le_closed : forall v n G G',
  SubstTm v n G G' ->
  free_tm_vars 0 v = [] ->
  G' ⊢ₗ capture_lt G' v <: capture_var_lifetime G n ->
  forall body,
  lt_wf G (capture_lt G body) ->
  G' ⊢ₗ capture_lt G' (subst_tm (1 + n) (shift_tm 1 0 v) body) <: capture_lt G body.
Proof.
  intros v n G G' HSub Hfree Hcapv body HwfCap.
  destruct (has_rt_cap body) eqn:HcapBody.
  - unfold capture_lt.
    rewrite (has_rt_cap_subst_tm_source_true body (1 + n) (shift_tm 1 0 v) HcapBody).
    rewrite HcapBody. apply LS_Refl. constructor.
  - destruct (has_rt_cap (subst_tm (1 + n) (shift_tm 1 0 v) body)) eqn:HcapSubst.
    + rewrite (capture_lt_no_cap G body HcapBody) in HwfCap.
      unfold capture_lt at 1. rewrite HcapSubst.
      rewrite (capture_lt_no_cap G body HcapBody).
      destruct (has_rt_cap_subst_tm_intro body 1 n v HcapBody HcapSubst) as [HcapV Hin].
      rewrite (capture_lt_closed G' v Hfree) in Hcapv. rewrite HcapV in Hcapv. simpl in Hcapv.
      eapply LS_Trans.
      * exact Hcapv.
      * assert (Hcontains : G ⊢ₗ capture_var_lifetime G n <:
            capture_vars G (free_tm_vars 1 body)).
        { apply capture_vars_contains; assumption. }
        exact (lt_sub_SubstTm G (capture_var_lifetime G n)
          (capture_vars G (free_tm_vars 1 body)) Hcontains v n G' HSub).
    + rewrite (capture_lt_no_cap G' (subst_tm (1 + n) (shift_tm 1 0 v) body) HcapSubst).
      rewrite (capture_lt_no_cap G body HcapBody) in HwfCap |- *.
      rewrite (free_tm_vars_subst_tm_closed body 1 n v Hfree).
    apply (capture_vars_subst_tm_fv_le v n G G' (free_tm_vars 1 body) HSub HwfCap).
Qed.

Lemma capture_lt_shift_tm_closed0 : forall Γ A v,
  free_tm_vars 0 v = [] ->
  capture_lt (bind_tm A :: Γ) (shift_tm 1 0 v) = capture_lt Γ v.
Proof.
  intros Γ A v Hfree.
  rewrite (capture_lt_closed Γ v Hfree).
  rewrite (capture_lt_closed (bind_tm A :: Γ) (shift_tm 1 0 v)).
  - rewrite has_rt_cap_shift_tm. reflexivity.
  - apply free_tm_vars_closed_shift_tm_any. exact Hfree.
Qed.

Lemma capture_lt_shift_ty_closed0 : forall Γ B v,
  free_tm_vars 0 v = [] ->
  capture_lt (bind_ty B :: Γ) (shift_ty_in_tm 1 0 v) = capture_lt Γ v.
Proof.
  intros Γ B v Hfree.
  rewrite (capture_lt_closed Γ v Hfree).
  rewrite (capture_lt_closed (bind_ty B :: Γ) (shift_ty_in_tm 1 0 v)).
  - rewrite has_rt_cap_shift_ty_in_tm. reflexivity.
  - rewrite free_tm_vars_shift_ty_in_tm. exact Hfree.
Qed.

Lemma capture_lt_shift_lt_closed0 : forall Γ D v,
  free_tm_vars 0 v = [] ->
  capture_lt (bind_lt D :: Γ) (shift_lt_in_tm 1 0 v) = capture_lt Γ v.
Proof.
  intros Γ D v Hfree.
  rewrite (capture_lt_closed Γ v Hfree).
  rewrite (capture_lt_closed (bind_lt D :: Γ) (shift_lt_in_tm 1 0 v)).
  - rewrite has_rt_cap_shift_lt_in_tm. reflexivity.
  - rewrite free_tm_vars_shift_lt_in_tm. exact Hfree.
Qed.

Lemma capture_var_lifetime_bind_tm : forall G A n,
  capture_var_lifetime (bind_tm A :: G) (S n) = capture_var_lifetime G n.
Proof.
  intros G A n. unfold capture_var_lifetime. simpl.
  destruct (ctx_lookup_tm G n) as [T|] eqn:Hlk; [|reflexivity].
  apply (lt_of_ty_G_InsTm G (bind_tm A :: G) (InsTm_here A G) T).
Qed.

Lemma capture_var_lifetime_bind_ty : forall G B n,
  capture_var_lifetime (bind_ty B :: G) n = capture_var_lifetime G n.
Proof.
  intros G B n. unfold capture_var_lifetime. simpl.
  destruct (ctx_lookup_tm G n) as [T|] eqn:Hlk; [|reflexivity].
  apply (lt_of_ty_G_InsTy 0 G (bind_ty B :: G) (InsTy_here B G) T).
Qed.

Lemma capture_var_lifetime_bind_lt : forall G D n,
  capture_var_lifetime (bind_lt D :: G) n = shift_lt 1 0 (capture_var_lifetime G n).
Proof.
  intros G D n. unfold capture_var_lifetime. simpl.
  destruct (ctx_lookup_tm G n) as [T|] eqn:Hlk; [|reflexivity].
  apply (lt_of_ty_G_InsLt 0 G (bind_lt D :: G) (InsLt_here D G) T).
Qed.

Lemma replacement_capture_bound_tm : forall G G' v n A,
  free_tm_vars 0 v = [] ->
  G' ⊢ₗ capture_lt G' v <: capture_var_lifetime G n ->
  (bind_tm A :: G') ⊢ₗ capture_lt (bind_tm A :: G') (shift_tm 1 0 v) <:
    capture_var_lifetime (bind_tm A :: G) (S n).
Proof.
  intros G G' v n A Hfree Hcap.
  rewrite capture_lt_shift_tm_closed0 by exact Hfree.
  rewrite capture_var_lifetime_bind_tm.
  apply (lt_sub_InsTm G' (capture_lt G' v) (capture_var_lifetime G n)
    Hcap (bind_tm A :: G') (InsTm_here A G')).
Qed.

Lemma replacement_capture_bound_ty : forall G G' v n B,
  free_tm_vars 0 v = [] ->
  G' ⊢ₗ capture_lt G' v <: capture_var_lifetime G n ->
  (bind_ty B :: G') ⊢ₗ capture_lt (bind_ty B :: G') (shift_ty_in_tm 1 0 v) <:
    capture_var_lifetime (bind_ty B :: G) n.
Proof.
  intros G G' v n B Hfree Hcap.
  rewrite capture_lt_shift_ty_closed0 by exact Hfree.
  rewrite capture_var_lifetime_bind_ty.
  apply (lt_sub_InsTy G' (capture_lt G' v) (capture_var_lifetime G n)
    Hcap 0 (bind_ty B :: G') (InsTy_here B G')).
Qed.

Lemma replacement_capture_bound_lt : forall G G' v n D,
  free_tm_vars 0 v = [] ->
  G' ⊢ₗ capture_lt G' v <: capture_var_lifetime G n ->
  (bind_lt D :: G') ⊢ₗ capture_lt (bind_lt D :: G') (shift_lt_in_tm 1 0 v) <:
    capture_var_lifetime (bind_lt D :: G) n.
Proof.
  intros G G' v n D Hfree Hcap.
  rewrite capture_lt_shift_lt_closed0 by exact Hfree.
  rewrite capture_var_lifetime_bind_lt.
  assert (Hshift : shift_lt 1 0 (capture_lt G' v) = capture_lt G' v).
  { rewrite (capture_lt_closed G' v Hfree). destruct (has_rt_cap v); reflexivity. }
  rewrite <- Hshift.
  apply (lt_sub_InsLt G' (capture_lt G' v) (capture_var_lifetime G n)
    Hcap 0 (bind_lt D :: G') (InsLt_here D G')).
Qed.


Lemma replacement_capture_bound_push_match_bound : forall k Delta G G' v n,
  free_tm_vars 0 v = [] ->
  G' ⊢ₗ capture_lt G' v <: capture_var_lifetime G n ->
  push_match_bound k Delta G' ⊢ₗ
    capture_lt (push_match_bound k Delta G') (shift_lt_in_tm k 0 v) <:
    capture_var_lifetime (push_match_bound k Delta G) n.
Proof.
  induction k as [|k IH]; intros Delta G G' v n Hfree Hcap; simpl.
  - rewrite shift_lt_in_tm_zero. exact Hcap.
  - replace (shift_lt_in_tm (S k) 0 v)
      with (shift_lt_in_tm 1 0 (shift_lt_in_tm k 0 v)).
    2:{ rewrite shift_lt_in_tm_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    apply replacement_capture_bound_lt.
    + rewrite free_tm_vars_shift_lt_in_tm_any. exact Hfree.
    + apply IH; assumption.
Qed.

Lemma replacement_capture_bound_push_ty_vars_any_at_free : forall k G G' v n,
  free_tm_vars 0 v = [] ->
  G' ⊢ₗ capture_lt G' v <: capture_var_lifetime G n ->
  push_ty_vars k any_at_free G' ⊢ₗ
    capture_lt (push_ty_vars k any_at_free G') (shift_ty_in_tm k 0 v) <:
    capture_var_lifetime (push_ty_vars k any_at_free G) n.
Proof.
  induction k as [|k IH]; intros G G' v n Hfree Hcap; simpl.
  - rewrite shift_ty_in_tm_zero. exact Hcap.
  - replace (shift_ty_in_tm (S k) 0 v)
      with (shift_ty_in_tm k 0 (shift_ty_in_tm 1 0 v)).
    2:{ rewrite shift_ty_in_tm_fuse. replace (k + 1) with (S k) by lia. reflexivity. }
    apply IH.
    + rewrite free_tm_vars_shift_ty_in_tm. exact Hfree.
    + apply replacement_capture_bound_ty; assumption.
Qed.

Lemma replacement_capture_bound_fold_bind_tm : forall rhos G G' v n,
  free_tm_vars 0 v = [] ->
  G' ⊢ₗ capture_lt G' v <: capture_var_lifetime G n ->
  List.fold_right (fun rho G0 => bind_tm rho :: G0) G' rhos ⊢ₗ
    capture_lt (List.fold_right (fun rho G0 => bind_tm rho :: G0) G' rhos)
      (shift_tm (List.length rhos) 0 v) <:
    capture_var_lifetime
      (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
      (n + List.length rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros G G' v n Hfree Hcap; simpl.
  - rewrite shift_tm_zero. replace (n + 0) with n by lia. exact Hcap.
  - replace (shift_tm (S (List.length rhos)) 0 v)
      with (shift_tm 1 0 (shift_tm (List.length rhos) 0 v)).
    2:{ rewrite shift_tm_fuse. replace (1 + List.length rhos) with (S (List.length rhos)) by lia. reflexivity. }
    replace (n + S (List.length rhos)) with (S (n + List.length rhos)) by lia.
    apply replacement_capture_bound_tm.
    + apply free_tm_vars_closed_shift_tm_any. exact Hfree.
    + apply IH; assumption.
Qed.

Lemma lt_sub_fold_bind_tm : forall rhos G l1 l2,
  G ⊢ₗ l1 <: l2 ->
  List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos ⊢ₗ l1 <: l2.
Proof.
  induction rhos as [|rho rhos IH]; intros G l1 l2 Hsub; simpl.
  - exact Hsub.
  - apply lt_sub_InsTm with (G := List.fold_right (fun rho0 G0 => bind_tm rho0 :: G0) G rhos).
    + apply IH. exact Hsub.
    + apply InsTm_here.
Qed.

Lemma sub_SubstTm : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall v n G', SubstTm v n G G' -> G' ⊢ T1 <:: T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T Hwf|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                 |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                 |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H IH|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2]; intros v n G' HSub.
  - apply SA_Refl. eapply ty_wf_SubstTm; eauto.
  - eapply SA_Trans; [apply (IH1 v n G' HSub)|apply (IH2 v n G' HSub)].
  - apply SA_VarCtx.
    + rewrite (SubstTm_lookup_ty v n Γ G' HSub α). exact Hlk.
    + eapply ty_wf_SubstTm; eauto.
  - apply SA_Data.
    + eapply lt_sub_SubstTm; eauto.
    + eapply types_wf_SubstTm; eauto.
  - apply SA_Any.
    + eapply ty_wf_SubstTm; eauto.
    + eapply lt_wf_SubstTm; eauto.
    + rewrite (lt_of_ty_G_SubstTm v n Γ G' HSub T).
      eapply lt_sub_SubstTm; eauto.
  - apply SA_Fun; [apply (IH1 v n G' HSub)|eapply lt_sub_SubstTm|apply (IH2 v n G' HSub)]; eauto.
  - apply SA_LtAll. apply (IH (shift_lt_in_tm 1 0 v) n (bind_lt lt_local :: G')). apply SubstTm_lt. exact HSub.
  - eapply SA_TyAll.
    + eapply ty_wf_SubstTm; [exact HwfA|]. apply SubstTm_ty. exact HSub.
    + eapply ty_wf_SubstTm; [exact HwfA'|]. apply SubstTm_ty. exact HSub.
    + apply (IH1 v n G' HSub).
    + apply (IH2 (shift_ty_in_tm 1 0 v) n (bind_ty B' :: G')). apply SubstTm_ty. exact HSub.
Qed.


(* Term substitution crosses [push_match_bound] exactly as it crosses         *)
(* [push_lt_vars] — SubstTm_lt keeps each bind_lt bound (term subst     *)
(* does not touch lt-bounds), so the per-level shifted bounds are       *)
(* irrelevant; no closedness on Delta is needed.                        *)
Lemma SubstTm_push_match_bound : forall k Delta v n G G',
  SubstTm v n G G' ->
  SubstTm (shift_lt_in_tm k 0 v) n
    (push_match_bound k Delta G) (push_match_bound k Delta G').
Proof.
  induction k as [|k IH]; intros Delta v n G G' HSub; simpl.
  - rewrite shift_lt_in_tm_zero. exact HSub.
  - replace (shift_lt_in_tm (S k) 0 v)
      with (shift_lt_in_tm 1 0 (shift_lt_in_tm k 0 v)).
    2:{ rewrite shift_lt_in_tm_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    apply SubstTm_lt. apply IH. exact HSub.
Qed.

Lemma SubstTm_push_ty_vars_any_at_free : forall k v n G G',
  SubstTm v n G G' ->
  SubstTm (shift_ty_in_tm k 0 v) n
    (push_ty_vars k any_at_free G) (push_ty_vars k any_at_free G').
Proof.
  induction k as [|k IH]; intros v n G G' HSub; simpl.
  - rewrite shift_ty_in_tm_zero. exact HSub.
  - replace (shift_ty_in_tm (S k) 0 v)
      with (shift_ty_in_tm k 0 (shift_ty_in_tm 1 0 v)).
    2:{ rewrite shift_ty_in_tm_fuse. replace (k + 1) with (S k) by lia. reflexivity. }
    apply IH. apply SubstTm_ty. exact HSub.
Qed.


Lemma SubstTm_fold_bind_tm : forall rhos v n G G',
  SubstTm v n G G' ->
  SubstTm (shift_tm (List.length rhos) 0 v) (n + List.length rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G' rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros v n G G' HSub; simpl.
  - rewrite shift_tm_zero. replace (n + 0) with n by lia. exact HSub.
  - replace (shift_tm (S (List.length rhos)) 0 v)
      with (shift_tm 1 0 (shift_tm (List.length rhos) 0 v)).
    2:{ rewrite shift_tm_fuse. replace (1 + List.length rhos) with (S (List.length rhos)) by lia. reflexivity. }
    replace (n + S (List.length rhos)) with (S (n + List.length rhos)) by lia.
    apply SubstTm_tm. apply IH. exact HSub.
Qed.


Lemma multi_subst_lt_in_ty_go_eq_map : forall cutoff lts Ts,
  (fix go Ts := match Ts with [] => [] | A :: rest => multi_subst_lt_in_ty cutoff lts A :: go rest end) Ts =
  List.map (multi_subst_lt_in_ty cutoff lts) Ts.
Proof.
  intros cutoff lts Ts. induction Ts as [|A rest IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

(* ===================================================================== *)
(* Bridge: for lt-CLOSED (ground) witnesses, the telescoping             *)
(* [subst_list_lt_in_ty] coincides with the parallel                     *)
(* [multi_subst_lt_in_ty 0] (= [inst_lt_vars]).  This connects the       *)
(* match operational substitution (subst_list, peeled by                 *)
(* [typing_peel_push_match_bound_fold]) to the constructor instantiation *)
(* [inst_ctor_type] (multi_subst).  Witnesses are closed because in an   *)
(* eval_ctx every lifetime is ground.                                    *)
(* ===================================================================== *)

Lemma multi_subst_lt_closed_id : forall lts c l,
  lt_lt_closed 0 l -> multi_subst_lt c lts l = l.
Proof.
  intros lts c l. revert c. induction l as [y| | |l1 IH1 l2 IH2]; intros c Hcl; simpl in *.
  - exfalso; lia.
  - reflexivity.
  - reflexivity.
  - destruct Hcl as [H1 H2]. rewrite IH1 by exact H1. rewrite IH2 by exact H2. reflexivity.
Qed.

Lemma multi_subst_lt_cons_closed : forall rest l c y,
  lt_lt_closed 0 l ->
  multi_subst_lt c (l :: rest) y = multi_subst_lt c rest (subst_lt c l y).
Proof.
  intros rest l c y Hcl. revert c.
  induction y as [x| | |y1 IH1 y2 IH2]; intros c; simpl.
  2,3: reflexivity.
  2:{ rewrite IH1, IH2. reflexivity. }
  (* lt_var x *)
  destruct (Nat.eqb x c) eqn:Exeqc.
  - (* x = c *)
    apply Nat.eqb_eq in Exeqc. subst x.
    rewrite (proj2 (Nat.ltb_ge c c) (Nat.le_refl c)).
    replace (c - c) with 0 by lia. simpl.
    rewrite shift_lt_closed_lifetime by (eapply lt_lt_closed_mono; [|exact Hcl]; lia).
    rewrite multi_subst_lt_closed_id by exact Hcl. reflexivity.
  - apply Nat.eqb_neq in Exeqc.
    destruct (Nat.ltb c x) eqn:Ecx.
    + (* c < x : subst_lt = lt_var (pred x) *)
      apply Nat.ltb_lt in Ecx. simpl.
      rewrite (proj2 (Nat.ltb_ge x c) ltac:(lia)).
      rewrite (proj2 (Nat.ltb_ge (Init.Nat.pred x) c) ltac:(lia)).
      destruct (Nat.ltb (x - c) (S (List.length rest))) eqn:E1.
      * apply Nat.ltb_lt in E1.
        replace (x - c) with (S (Init.Nat.pred x - c)) by lia. simpl.
        rewrite (proj2 (Nat.ltb_lt (Init.Nat.pred x - c) (List.length rest)) ltac:(lia)).
        reflexivity.
      * apply Nat.ltb_ge in E1.
        rewrite (proj2 (Nat.ltb_ge (Init.Nat.pred x - c) (List.length rest)) ltac:(lia)).
        f_equal. lia.
    + (* x < c : subst_lt = lt_var x *)
      apply Nat.ltb_ge in Ecx.
      assert (Hxc : Nat.ltb x c = true) by (apply Nat.ltb_lt; lia).
      rewrite Hxc. simpl. rewrite Hxc. reflexivity.
Qed.

Lemma multi_subst_lt_in_ty_cons_closed : forall T c w rest,
  lt_lt_closed 0 w ->
  multi_subst_lt_in_ty c (w :: rest) T = multi_subst_lt_in_ty c rest (subst_lt_in_ty c w T).
Proof.
  intros T.
  induction T using type_list_ind with
    (Q := fun Ts => forall c w rest, lt_lt_closed 0 w ->
       List.map (multi_subst_lt_in_ty c (w :: rest)) Ts =
       List.map (multi_subst_lt_in_ty c rest) (List.map (subst_lt_in_ty c w) Ts));
    intros c w rest Hcl.
  - reflexivity.
  - simpl. rewrite IHT1, IHT2 by exact Hcl.
    rewrite multi_subst_lt_cons_closed by exact Hcl. reflexivity.
  - simpl. rewrite !multi_subst_lt_in_ty_go_eq_map.
    rewrite multi_subst_lt_cons_closed by exact Hcl.
    rewrite IHT by exact Hcl. reflexivity.
  - simpl. rewrite shift_lt_closed_lifetime by (eapply lt_lt_closed_mono; [|exact Hcl]; lia).
    rewrite IHT by exact Hcl. reflexivity.
  - simpl. rewrite IHT1, IHT2 by exact Hcl. reflexivity.
  - reflexivity.
  - simpl. rewrite IHT by exact Hcl. rewrite IHT0 by exact Hcl. reflexivity.
Qed.

Lemma multi_subst_lt_nil : forall c l, multi_subst_lt c [] l = l.
Proof.
  intros c l. induction l as [x| | |l1 IH1 l2 IH2]; simpl; try reflexivity.
  - destruct (Nat.ltb x c) eqn:E; [reflexivity|].
    cbn [List.length]. replace (x - 0) with x by lia. reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma multi_subst_lt_in_ty_nil : forall c T, multi_subst_lt_in_ty c [] T = T.
Proof.
  intros c T. revert c.
  induction T using type_list_ind with
    (Q := fun Ts => forall c, List.map (multi_subst_lt_in_ty c []) Ts = Ts);
    intros c; simpl.
  - reflexivity.
  - rewrite IHT1, IHT2, multi_subst_lt_nil. reflexivity.
  - rewrite multi_subst_lt_in_ty_go_eq_map, IHT, multi_subst_lt_nil. reflexivity.
  - rewrite IHT. reflexivity.
  - rewrite IHT1, IHT2. reflexivity.
  - reflexivity.
  - rewrite IHT, IHT0. reflexivity.
Qed.

Lemma multi_subst_lt_in_ty_eq_iter_closed : forall lts T,
  Forall (fun l => lt_lt_closed 0 l) lts ->
  multi_subst_lt_in_ty 0 lts T = iter_subst_lt_in_ty lts T.
Proof.
  induction lts as [|l rest IH]; intros T Hcl; simpl.
  - apply multi_subst_lt_in_ty_nil.
  - inversion Hcl; subst.
    rewrite multi_subst_lt_in_ty_cons_closed by assumption.
    rewrite IH by assumption. reflexivity.
Qed.

Lemma shift_each_lt_closed : forall lts,
  Forall (fun l => lt_lt_closed 0 l) lts -> shift_each_lt lts = lts.
Proof.
  induction lts as [|l rest IH]; intros Hcl; simpl; [reflexivity|].
  inversion Hcl; subst.
  rewrite shift_lt_closed_lifetime by (eapply lt_lt_closed_mono; [|eassumption]; lia).
  rewrite IH by assumption. reflexivity.
Qed.

Lemma subst_list_lt_in_ty_eq_multi_closed : forall lts T,
  Forall (fun l => lt_lt_closed 0 l) lts ->
  subst_list_lt_in_ty lts T = multi_subst_lt_in_ty 0 lts T.
Proof.
  intros lts T Hcl.
  rewrite subst_list_lt_in_ty_eq_iter.
  rewrite shift_each_lt_closed by exact Hcl.
  symmetry. apply multi_subst_lt_in_ty_eq_iter_closed. exact Hcl.
Qed.

(* The matchyes reconciliation: substituting the (closed) constructor   *)
(* lifetimes [lts] into the match field type [inst_ctor_type_open] gives *)
(* exactly the constructor's instantiated field type [inst_ctor_type].  *)
Lemma subst_list_lt_in_ty_inst_ctor_type_open : forall lts n_lt n_ty Ts sigma,
  Forall (fun l => lt_lt_closed 0 l) lts ->
  subst_list_lt_in_ty lts (inst_ctor_type_open n_lt n_ty Ts sigma) =
  inst_ctor_type n_lt n_ty lts Ts sigma.
Proof.
  intros lts n_lt n_ty Ts sigma Hcl.
  rewrite subst_list_lt_in_ty_eq_multi_closed by exact Hcl.
  unfold inst_ctor_type, inst_lt_vars, inst_ctor_type_open. reflexivity.
Qed.


(* ---- chain_bounded witnesses + iteration monotonicity ---------- *)


(* ---- Substitution preservation (typing) ------------------------ *)

