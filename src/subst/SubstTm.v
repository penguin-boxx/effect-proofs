Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import ShiftLaws.
Require Import Insertions.
Require Import SubstLt.
Require Import SubstTy.

(* ================================================================== *)
(* SubstTm : substitute a term for a tm-binder at depth n             *)
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

Lemma SubstTm_value : forall v n G G', SubstTm v n G G' -> value v.
Proof.
  intros v n G G' H. induction H.
  - exact H.
  - apply value_shift_tm. exact IHSubstTm.
  - apply value_shift_ty_in_tm. exact IHSubstTm.
  - apply value_shift_lt_in_tm. exact IHSubstTm.
  - exact IHSubstTm.
  - exact IHSubstTm.
Qed.

Lemma SubstTm_lookup_tm : forall v n G G', SubstTm v n G G' ->
  forall x, x <> n -> ctx_lookup_tm G' (slv n x) = ctx_lookup_tm G x.
Proof.
  intros v n G G' H. induction H; intros x Hne.
  - destruct x as [|x']; [contradiction|]. reflexivity.
  - destruct x as [|x'].
    + reflexivity.
    + assert (x' <> n) by lia.
      rewrite slv_S. simpl ctx_lookup_tm. apply IHSubstTm. exact H0.
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

Lemma SubstTm_to_InsTm : forall v n G G',
  SubstTm v n G G' -> InsTm G' G.
Proof.
  intros v n G G' H. induction H; constructor; exact IHSubstTm.
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
  capture_var_lifetime G' (slv n x) = capture_var_lifetime G x.
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
      { change (capture_var_lifetime G' (slv n x) = capture_var_lifetime G x).
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

Lemma replacement_capture_bound_push_lt_vars : forall k Delta G G' v n,
  free_tm_vars 0 v = [] ->
  G' ⊢ₗ capture_lt G' v <: capture_var_lifetime G n ->
  push_lt_vars k Delta G' ⊢ₗ
    capture_lt (push_lt_vars k Delta G') (shift_lt_in_tm k 0 v) <:
    capture_var_lifetime (push_lt_vars k Delta G) n.
Proof.
  induction k as [|k IH]; intros Delta G G' v n Hfree Hcap; simpl.
  - rewrite shift_lt_in_tm_zero. exact Hcap.
  - replace (shift_lt_in_tm (S k) 0 v)
      with (shift_lt_in_tm k 0 (shift_lt_in_tm 1 0 v)).
    2:{ rewrite shift_lt_in_tm_fuse. replace (k + 1) with (S k) by lia. reflexivity. }
    apply IH.
    + rewrite free_tm_vars_shift_lt_in_tm. exact Hfree.
    + apply replacement_capture_bound_lt; assumption.
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

Lemma no_local_ty_G_SubstTm : forall Γ T v n G',
  SubstTm v n Γ G' ->
  no_local_ty_G Γ T = true ->
  no_local_ty_G G' T = true.
Proof.
  intros Γ T. revert Γ.
  apply (type_list_ind
    (fun T => forall Γ v n G', SubstTm v n Γ G' ->
      no_local_ty_G Γ T = true -> no_local_ty_G G' T = true)
    (fun Ts => forall Γ v n G', SubstTm v n Γ G' ->
      fold_right (fun A acc => andb (no_local_ty_G Γ A) acc) true Ts = true ->
      fold_right (fun A acc => andb (no_local_ty_G G' A) acc) true Ts = true)).
  - intros x Γ v n G' HSub Hnl. simpl in *.
    rewrite (SubstTm_lookup_ty v n Γ G' HSub x). exact Hnl.
  - intros A l B IHA IHB Γ v n G' HSub Hnl. simpl in *.
    repeat rewrite Bool.andb_true_iff in Hnl.
    destruct Hnl as [HnlA [Hnll HnlB]].
    rewrite (IHA Γ v n G' HSub HnlA), (IHB Γ v n G' HSub HnlB), Hnll. reflexivity.
  - intros K l Ts IHTs Γ v n G' HSub Hnl. simpl in *.
    rewrite !no_local_ty_G_go_eq_fold in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [Hnll HnlTs].
    rewrite Hnll, (IHTs Γ v n G' HSub HnlTs). reflexivity.
  - intros A IHA Γ v n G' HSub Hnl. simpl in *.
    apply IHA with (Γ := bind_lt lt_local :: Γ) (v := shift_lt_in_tm 1 0 v) (n := n).
    + apply SubstTm_lt. exact HSub.
    + exact Hnl.
  - intros B A IHB IHA Γ v n G' HSub Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlB HnlA].
    rewrite (IHB Γ v n G' HSub HnlB).
    rewrite (IHA (bind_ty B :: Γ) (shift_ty_in_tm 1 0 v) n (bind_ty B :: G')
              (SubstTm_ty v n Γ G' B HSub) HnlA).
    reflexivity.
  - intros Γ v n G' HSub Hnl. reflexivity.
  - intros A Ts IHA IHTs Γ v n G' HSub Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlA HnlTs].
    rewrite (IHA Γ v n G' HSub HnlA), (IHTs Γ v n G' HSub HnlTs). reflexivity.
Qed.

Lemma ty_app_arg_no_local_SubstTm : forall Γ B S v n G',
  SubstTm v n Γ G' ->
  ty_app_arg_no_local Γ B S = true ->
  ty_app_arg_no_local G' B S = true.
Proof.
  intros Γ B S v n G' HSub Hnl. unfold ty_app_arg_no_local in *.
  destruct (is_any_at_free_bound B) eqn:HB; [|exact Hnl].
  eapply no_local_ty_G_SubstTm; eauto.
Qed.

Lemma forallb_no_local_ty_G_SubstTm : forall Γ Ss v n G',
  SubstTm v n Γ G' ->
  forallb (no_local_ty_G Γ) Ss = true ->
  forallb (no_local_ty_G G') Ss = true.
Proof.
  intros Γ Ss. induction Ss as [|S Ss IH]; intros v n G' HSub Hnl; simpl in *; [reflexivity|].
  apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlS HnlSs].
  rewrite (no_local_ty_G_SubstTm Γ S v n G' HSub HnlS), (IH v n G' HSub HnlSs). reflexivity.
Qed.

Lemma SubstTm_push_lt_vars : forall k Delta v n G G',
  SubstTm v n G G' ->
  SubstTm (shift_lt_in_tm k 0 v) n
    (push_lt_vars k Delta G) (push_lt_vars k Delta G').
Proof.
  induction k as [|k IH]; intros Delta v n G G' HSub; simpl.
  - rewrite shift_lt_in_tm_zero. exact HSub.
  - replace (shift_lt_in_tm (S k) 0 v)
      with (shift_lt_in_tm k 0 (shift_lt_in_tm 1 0 v)).
    2:{ rewrite shift_lt_in_tm_fuse. replace (k + 1) with (S k) by lia. reflexivity. }
    apply IH. apply SubstTm_lt. exact HSub.
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

Lemma SubstTm_push_ty_vars : forall k B v n G G',
  SubstTm v n G G' ->
  SubstTm (shift_ty_in_tm k 0 v) n
    (push_ty_vars k B G) (push_ty_vars k B G').
Proof.
  induction k as [|k IH]; intros B v n G G' HSub; simpl.
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

Lemma Forall2_typing_SubstTm : forall Γ vs rhos,
  Forall2 (fun v rho => forall repl n G', SubstTm repl n Γ G' ->
    G' ⊢ₜ subst_tm n repl v : rho) vs rhos ->
  forall repl n G', SubstTm repl n Γ G' ->
  Forall2 (fun v rho => G' ⊢ₜ v : rho)
           (List.map (subst_tm n repl) vs) rhos.
Proof.
  intros Γ vs rhos H. induction H; intros repl n G' HSub; simpl.
  - constructor.
  - constructor.
    + apply H. exact HSub.
    + apply IHForall2. exact HSub.
Qed.

Fixpoint subst_list_lt (lts : list lifetime) (l : lifetime) : lifetime :=
  match lts with
  | [] => l
  | w :: rest => subst_list_lt rest (subst_lt 0 (shift_lt (List.length rest) 0 w) l)
  end.

Lemma subst_list_lt_shift_cancel : forall lts l,
  subst_list_lt lts (shift_lt (List.length lts) 0 l) = l.
Proof.
  induction lts as [|w rest IH]; intros l; simpl.
  - rewrite shift_lt_zero. reflexivity.
  - replace (S (List.length rest)) with (1 + List.length rest) by lia.
    rewrite <- shift_lt_fuse.
    rewrite subst_lt_shift_cancel.
    apply IH.
Qed.

Lemma subst_list_lt_var_nth : forall lts x,
  x < List.length lts ->
  subst_list_lt lts (lt_var x) = List.nth x lts lt_free.
Proof.
  induction lts as [|w rest IH]; intros x Hx; simpl in *; [lia|].
  destruct x as [|x'].
  - simpl. apply subst_list_lt_shift_cancel.
  - simpl subst_lt. destruct (Nat.eqb_spec (S x') 0) as [E|E]; [lia|].
    destruct (Nat.ltb_spec 0 (S x')) as [_|Hbad]; [|lia].
    apply IH. lia.
Qed.

Lemma subst_list_lt_free : forall lts,
  subst_list_lt lts lt_free = lt_free.
Proof. induction lts as [|w rest IH]; simpl; [reflexivity|exact IH]. Qed.

Lemma subst_list_lt_local : forall lts,
  subst_list_lt lts lt_local = lt_local.
Proof. induction lts as [|w rest IH]; simpl; [reflexivity|exact IH]. Qed.

Lemma subst_list_lt_min : forall lts l1 l2,
  subst_list_lt lts (lt_min l1 l2) =
  lt_min (subst_list_lt lts l1) (subst_list_lt lts l2).
Proof.
  induction lts as [|w rest IH]; intros l1 l2; simpl; [reflexivity|].
  apply IH.
Qed.

Fixpoint lt_bounded_lt (k : nat) (l : lifetime) : Prop :=
  match l with
  | lt_var x => x < k
  | lt_min l1 l2 => lt_bounded_lt k l1 /\ lt_bounded_lt k l2
  | _ => True
  end.

Lemma lt_var_list_length : forall n,
  List.length (lt_var_list n) = n.
Proof.
  intros n. unfold lt_var_list. rewrite List.length_map, List.length_seq. reflexivity.
Qed.

Lemma nth_lt_var_list : forall n x,
  x < n ->
  List.nth x (lt_var_list n) lt_free = lt_var x.
Proof.
  intros n x Hx.
  apply List.nth_error_nth with (d := lt_free).
  unfold lt_var_list.
  rewrite List.nth_error_map.
  rewrite List.nth_error_seq.
  destruct (Nat.ltb_spec x n) as [Hlt|Hge]; [|lia].
  replace (0 + x) with x by lia.
  reflexivity.
Qed.

Lemma subst_lt_lt_var_list_above : forall k n R,
  List.map (subst_lt (k + n) (shift_lt k 0 R)) (lt_var_list k) = lt_var_list k.
Proof.
  intros k n R. unfold lt_var_list. rewrite List.map_map.
  apply List.map_ext_in. intros x Hin.
  apply List.in_seq in Hin. destruct Hin as [_ Hx]. simpl.
  destruct (Nat.eqb_spec x (k + n)); [lia|].
  destruct (Nat.ltb_spec (k + n) x); [lia|reflexivity].
Qed.

Lemma subst_list_lt_multi_var_list : forall k lts l,
  List.length lts = k ->
  lt_bounded_lt k l ->
  subst_list_lt lts (multi_subst_lt 0 (lt_var_list k) l) = multi_subst_lt 0 lts l.
Proof.
  intros k lts l. revert k lts.
  induction l as [x| | |l1 IH1 l2 IH2]; intros k lts Hlen Hb; simpl in *.
  - rewrite lt_var_list_length.
    destruct (Nat.ltb x k) eqn:Hxk.
    + apply Nat.ltb_lt in Hxk.
      replace (x - 0) with x by lia.
      rewrite nth_lt_var_list by exact Hxk.
      rewrite shift_lt_zero.
      rewrite (proj2 (Nat.ltb_lt x k) Hxk).
      rewrite subst_list_lt_var_nth by lia.
      rewrite Hlen, (proj2 (Nat.ltb_lt x k) Hxk). rewrite shift_lt_zero. reflexivity.
    + apply Nat.ltb_ge in Hxk. lia.
  - apply subst_list_lt_free.
  - apply subst_list_lt_local.
  - destruct Hb as [Hb1 Hb2].
    pose proof (IH1 k lts Hlen Hb1) as H1.
    pose proof (IH2 k lts Hlen Hb2) as H2.
    rewrite subst_list_lt_min. rewrite H1, H2. reflexivity.
Qed.

Lemma ty_lt_closed_subst_ty : forall T c n Sb,
  ty_lt_closed c T -> ty_lt_closed c Sb -> ty_lt_closed c (subst_ty n Sb T).
Proof.
  apply (type_list_ind
    (fun T => forall c n Sb,
       ty_lt_closed c T -> ty_lt_closed c Sb -> ty_lt_closed c (subst_ty n Sb T))
    (fun Ts => forall c n Sb,
       tys_lt_closed c Ts -> ty_lt_closed c Sb ->
       tys_lt_closed c (List.map (subst_ty n Sb) Ts))).
  - intros m c n Sb _ HSb. rewrite subst_ty_var_eq.
    destruct (Nat.eqb m n); [exact HSb|]. destruct (Nat.ltb n m); exact I.
  - intros A l B IHA IHB c n Sb Hclosed HSb. rewrite subst_ty_fun_eq. simpl in *.
    destruct Hclosed as [HA [Hl HB]]. repeat split.
    + apply IHA; assumption.
    + exact Hl.
    + apply IHB; assumption.
  - intros K l Ts IHTs c n Sb Hclosed HSb. rewrite subst_ty_ctor_eq. simpl in *.
    destruct Hclosed as [Hl HTs]. split.
    + exact Hl.
    + apply IHTs; assumption.
  - intros A IHA c n Sb Hclosed HSb. rewrite subst_ty_ltall_eq. simpl in *.
    apply IHA.
    + exact Hclosed.
    + replace (S c) with (1 + c) by lia.
      eapply ty_lt_closed_shift_lt_below; [lia|exact HSb].
  - intros B A IHB IHA c n Sb Hclosed HSb. rewrite subst_ty_tyall_eq. simpl in *.
    destruct Hclosed as [HB HA]. split.
    + apply IHB; assumption.
    + apply IHA.
      * exact HA.
      * apply ty_lt_closed_shift_ty. exact HSb.
  - intros c n Sb _ _. exact I.
  - intros A Ts IHA IHTs c n Sb Hclosed HSb. simpl in *.
    destruct Hclosed as [HA HTs]. split.
    + apply IHA; assumption.
    + apply IHTs; assumption.
Qed.

Lemma tys_lt_closed_subst_ty : forall Ts c n Sb,
  tys_lt_closed c Ts -> ty_lt_closed c Sb ->
  tys_lt_closed c (List.map (subst_ty n Sb) Ts).
Proof.
  induction Ts as [|T Ts IH]; intros c n Sb Hclosed HSb; simpl in *.
  - exact I.
  - destruct Hclosed as [HT HTs]. split.
    + eapply ty_lt_closed_subst_ty; eauto.
    + apply IH; assumption.
Qed.

Lemma inst_ty_vars_lt_closed : forall n Ts T c,
  List.length Ts = n ->
  tys_lt_closed c Ts ->
  ty_lt_closed c T ->
  ty_lt_closed c (inst_ty_vars n Ts T).
Proof.
  induction n as [|n IH]; intros Ts T c Hlen HTs HT.
  - exact HT.
  - destruct Ts as [|U rest]; [simpl in Hlen; discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    simpl. simpl in HTs. destruct HTs as [HU Hrest].
    apply IH; [exact Hlen|exact Hrest|].
    apply ty_lt_closed_subst_ty.
    + exact HT.
    + apply ty_lt_closed_shift_ty. exact HU.
Qed.

Lemma multi_subst_lt_lt_var_list_closed : forall l cutoff schema_n c,
  lt_lt_closed (cutoff + schema_n + c) l ->
  lt_lt_closed (cutoff + schema_n + c) (multi_subst_lt cutoff (lt_var_list schema_n) l).
Proof.
  induction l as [idx| | |l1 IH1 l2 IH2]; intros cutoff schema_n c Hclosed; simpl in *; try exact I.
  - destruct (Nat.ltb idx cutoff) eqn:Hbefore.
    + apply Nat.ltb_lt in Hbefore.
      eapply Nat.lt_le_trans; [exact Hbefore|lia].
    + apply Nat.ltb_ge in Hbefore.
      rewrite lt_var_list_length.
      destruct (Nat.ltb (idx - cutoff) schema_n) eqn:Hschema.
      * apply Nat.ltb_lt in Hschema.
        rewrite nth_lt_var_list by exact Hschema.
        simpl. lia.
      * apply Nat.ltb_ge in Hschema.
        simpl. lia.
  - destruct Hclosed as [H1 H2]. split.
    + apply IH1. exact H1.
    + apply IH2. exact H2.
Qed.

Lemma multi_subst_lt_in_ty_go_eq_map_early : forall cutoff lts Ts,
  (fix go Ts := match Ts with [] => [] | A :: rest => multi_subst_lt_in_ty cutoff lts A :: go rest end) Ts =
  List.map (multi_subst_lt_in_ty cutoff lts) Ts.
Proof.
  intros cutoff lts Ts. induction Ts as [|A rest IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma multi_subst_lt_in_ty_lt_var_list_closed : forall T cutoff n c,
  ty_lt_closed (cutoff + n + c) T ->
  ty_lt_closed (cutoff + n + c) (multi_subst_lt_in_ty cutoff (lt_var_list n) T).
Proof.
  apply (type_list_ind
    (fun T => forall cutoff n c,
       ty_lt_closed (cutoff + n + c) T ->
       ty_lt_closed (cutoff + n + c) (multi_subst_lt_in_ty cutoff (lt_var_list n) T))
    (fun Ts => forall cutoff n c,
       tys_lt_closed (cutoff + n + c) Ts ->
       tys_lt_closed (cutoff + n + c)
         (List.map (multi_subst_lt_in_ty cutoff (lt_var_list n)) Ts))).
  - intros m cutoff n c Hclosed. exact I.
  - intros A l B IHA IHB cutoff n c Hclosed. simpl in *.
    destruct Hclosed as [HA [Hl HB]]. repeat split.
    + apply IHA. exact HA.
    + apply multi_subst_lt_lt_var_list_closed. exact Hl.
    + apply IHB. exact HB.
  - intros K l Ts IHTs cutoff n c Hclosed. simpl in *.
    destruct Hclosed as [Hl HTs]. rewrite multi_subst_lt_in_ty_go_eq_map_early. split.
    + apply multi_subst_lt_lt_var_list_closed. exact Hl.
    + apply IHTs. exact HTs.
  - intros A IHA cutoff n c Hclosed. simpl in *.
    replace (S (cutoff + n + c)) with (S cutoff + n + c) by lia.
    apply IHA. exact Hclosed.
  - intros B A IHB IHA cutoff n c Hclosed. simpl in *.
    destruct Hclosed as [HB HA]. split.
    + apply IHB. exact HB.
    + apply IHA. exact HA.
  - intros cutoff n c Hclosed. exact I.
  - intros A Ts IHA IHTs cutoff n c Hclosed. simpl in *.
    destruct Hclosed as [HA HTs]. split.
    + apply IHA. exact HA.
    + apply IHTs. exact HTs.
Qed.

Lemma inst_ctor_type_lt_var_list_lt_closed : forall n_lt n_ty Ts T c,
  List.length Ts = n_ty ->
  tys_lt_closed c Ts ->
  ty_lt_closed (n_lt + c) T ->
  ty_lt_closed (n_lt + c) (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts T).
Proof.
  intros n_lt n_ty Ts T c Hlen HTs HT.
  unfold inst_ctor_type, inst_lt_vars.
  change (ty_lt_closed (0 + n_lt + c)
    (multi_subst_lt_in_ty 0 (lt_var_list n_lt)
      (inst_ty_vars n_ty (List.map (shift_lt_in_ty n_lt 0) Ts) T))).
  apply multi_subst_lt_in_ty_lt_var_list_closed.
  apply inst_ty_vars_lt_closed.
  - rewrite List.length_map. exact Hlen.
  - change (List.map (shift_lt_in_ty n_lt 0) Ts) with (shift_lt_in_ty_list n_lt 0 Ts).
    eapply tys_lt_closed_shift_lt_below; [lia|exact HTs].
  - exact HT.
Qed.

Lemma inst_ctor_type_list_lt_var_list_lt_closed : forall n_lt n_ty Ts fields c,
  List.length Ts = n_ty ->
  tys_lt_closed c Ts ->
  tys_lt_closed (n_lt + c) fields ->
  tys_lt_closed (n_lt + c)
    (List.map (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts) fields).
Proof.
  induction fields as [|field fields IH]; intros c Hlen HTs Hfields; simpl in *.
  - exact I.
  - destruct Hfields as [Hfield Hrest]. split.
    + eapply inst_ctor_type_lt_var_list_lt_closed; eauto.
    + apply IH; assumption.
Qed.

(* MATCH-variant lt-closedness: [inst_ctor_type_open] (no inst_lt_vars).    *)
Lemma inst_ctor_type_open_lt_closed : forall n_lt n_ty Ts T c,
  List.length Ts = n_ty ->
  tys_lt_closed c Ts ->
  ty_lt_closed (n_lt + c) T ->
  ty_lt_closed (n_lt + c) (inst_ctor_type_open n_lt n_ty Ts T).
Proof.
  intros n_lt n_ty Ts T c Hlen HTs HT.
  unfold inst_ctor_type_open.
  apply inst_ty_vars_lt_closed.
  - rewrite List.length_map. exact Hlen.
  - change (List.map (shift_lt_in_ty n_lt 0) Ts) with (shift_lt_in_ty_list n_lt 0 Ts).
    eapply tys_lt_closed_shift_lt_below; [lia|exact HTs].
  - exact HT.
Qed.

Lemma inst_ctor_type_open_list_lt_closed : forall n_lt n_ty Ts fields c,
  List.length Ts = n_ty ->
  tys_lt_closed c Ts ->
  tys_lt_closed (n_lt + c) fields ->
  tys_lt_closed (n_lt + c)
    (List.map (inst_ctor_type_open n_lt n_ty Ts) fields).
Proof.
  induction fields as [|field fields IH]; intros c Hlen HTs Hfields; simpl in *.
  - exact I.
  - destruct Hfields as [Hfield Hrest]. split.
    + eapply inst_ctor_type_open_lt_closed; eauto.
    + apply IH; assumption.
Qed.

Lemma inst_op_alpha_lt_closed : forall n_α Ts n_β T c,
  List.length Ts = n_α ->
  tys_lt_closed c Ts ->
  ty_lt_closed c T ->
  ty_lt_closed c (inst_op_alpha n_α Ts n_β T).
Proof.
  intros n_α Ts n_β T c Hlen HTs HT.
  unfold inst_op_alpha.
  apply inst_ty_vars_lt_closed.
  - rewrite List.length_map. exact Hlen.
  - apply tys_lt_closed_shift_ty. exact HTs.
  - exact HT.
Qed.

Lemma inst_op_arg_lt_closed : forall n_α Ts n_β Ss T c,
  List.length Ts = n_α ->
  List.length Ss = n_β ->
  tys_lt_closed c Ts ->
  tys_lt_closed c Ss ->
  ty_lt_closed c T ->
  ty_lt_closed c (inst_op_arg n_α Ts n_β Ss T).
Proof.
  intros n_α Ts n_β Ss T c HlenTs HlenSs HTs HSs HT.
  unfold inst_op_arg.
  apply inst_ty_vars_lt_closed.
  - exact HlenSs.
  - exact HSs.
  - eapply inst_op_alpha_lt_closed; eauto.
Qed.

Fixpoint ctor_field_bounded_ty (k : nat) (T : type) : Prop :=
  let fix all (Ts : list type) : Prop :=
    match Ts with
    | [] => True
    | A :: rest => ctor_field_bounded_ty k A /\ all rest
    end
  in
  match T with
  | type_var _ => True
  | type_fun A l B => ctor_field_bounded_ty k A /\ lt_bounded_lt k l /\ ctor_field_bounded_ty k B
  | type_ctor _ l Ts => lt_bounded_lt k l /\ all Ts
  | type_lt_all _ => False
  | type_ty_all B A => ctor_field_bounded_ty k B /\ ctor_field_bounded_ty k A
  end.

Definition ctor_field_bounded_tys (k : nat) (Ts : list type) : Prop :=
  fold_right (fun A acc => ctor_field_bounded_ty k A /\ acc) True Ts.

Lemma subst_list_lt_in_ty_fun_flat : forall lts A l B,
  subst_list_lt_in_ty lts (type_fun A l B) =
  type_fun (subst_list_lt_in_ty lts A) (subst_list_lt lts l) (subst_list_lt_in_ty lts B).
Proof.
  induction lts as [|w rest IH]; intros A l B; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma subst_list_lt_in_ty_var_flat : forall lts n,
  subst_list_lt_in_ty lts (type_var n) = type_var n.
Proof. induction lts as [|w rest IH]; intros n; simpl; [reflexivity|apply IH]. Qed.

Lemma subst_list_lt_in_ty_tyall_flat : forall lts B A,
  subst_list_lt_in_ty lts (type_ty_all B A) =
  type_ty_all (subst_list_lt_in_ty lts B) (subst_list_lt_in_ty lts A).
Proof.
  induction lts as [|w rest IH]; intros B A; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma subst_list_lt_in_ty_ctor_flat : forall lts K l Ts,
  subst_list_lt_in_ty lts (type_ctor K l Ts) =
  type_ctor K (subst_list_lt lts l) (List.map (subst_list_lt_in_ty lts) Ts).
Proof.
  induction lts as [|w rest IH]; intros K l Ts.
  - simpl. rewrite List.map_id. reflexivity.
  - cbn [subst_list_lt subst_list_lt_in_ty].
    rewrite subst_lt_in_ty_ctor_eq. rewrite IH. rewrite List.map_map. reflexivity.
Qed.

Lemma multi_subst_lt_in_ty_go_eq_map : forall cutoff lts Ts,
  (fix go Ts := match Ts with [] => [] | A :: rest => multi_subst_lt_in_ty cutoff lts A :: go rest end) Ts =
  List.map (multi_subst_lt_in_ty cutoff lts) Ts.
Proof.
  intros cutoff lts Ts. induction Ts as [|A rest IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma bounded_ctor_inst_type_core : forall k lts T,
  List.length lts = k ->
  ctor_field_bounded_ty k T ->
  subst_list_lt_in_ty lts (multi_subst_lt_in_ty 0 (lt_var_list k) T) =
  multi_subst_lt_in_ty 0 lts T.
Proof.
  intros k lts T. revert k lts.
  induction T using type_list_ind with
    (Q := fun Ts => forall k lts,
       List.length lts = k ->
       ctor_field_bounded_tys k Ts ->
       List.map (subst_list_lt_in_ty lts)
         (List.map (multi_subst_lt_in_ty 0 (lt_var_list k)) Ts) =
       List.map (multi_subst_lt_in_ty 0 lts) Ts);
    intros k lts Hlen Hb; simpl in *.
  - apply subst_list_lt_in_ty_var_flat.
  - destruct Hb as [HBA [Hbl HBB]].
    rewrite subst_list_lt_in_ty_fun_flat.
    rewrite IHT1 by assumption.
    rewrite IHT2 by assumption.
    rewrite subst_list_lt_multi_var_list with (k := k) by assumption.
    reflexivity.
  - destruct Hb as [Hbl HBTs].
    rewrite subst_list_lt_in_ty_ctor_flat.
    rewrite !multi_subst_lt_in_ty_go_eq_map.
    rewrite IHT by assumption.
    rewrite subst_list_lt_multi_var_list with (k := k) by assumption.
    reflexivity.
  - contradiction.
  - destruct Hb as [HBB HBA].
    rewrite subst_list_lt_in_ty_tyall_flat.
    rewrite IHT1 by assumption.
    rewrite IHT2 by assumption.
    reflexivity.
  - reflexivity.
  - destruct Hb as [HBA HBTs]. simpl.
    rewrite IHT by assumption.
    f_equal. apply IHT0; assumption.
Qed.

(* ---- chain_bounded witnesses + iteration monotonicity ---------- *)

(* Witnesses are valid w.r.t. a chain of progressively-closed bounds.   *)
Fixpoint chain_bounded (Γ : ctx) (ws : list lifetime) (bound : lifetime) : Prop :=
  match ws with
  | []        => True
  | w :: rest =>
      (Γ ⊢ₗ w <: subst_lt 0 lt_free bound) /\
      chain_bounded Γ rest (subst_lt 0 lt_free bound)
  end.

(* ---- Substitution preservation (typing) ------------------------ *)

(* Shifting a term-closed value leaves it term-closed.  Used to keep    *)
(* the closedness side-condition of `subst_tm_lemma` available across   *)
(* the shifts performed by parallel term substitution.                  *)
Lemma free_tm_vars_closed_shift : forall a v,
  free_tm_vars 0 v = [] ->
  free_tm_vars 0 (shift_tm a 0 v) = [].
Proof.
  induction a as [|n IH]; intros v Hcl.
  - rewrite shift_tm_zero. exact Hcl.
  - replace (S n) with (1 + n) by lia.
    rewrite <- shift_tm_fuse.
    pose proof (free_tm_vars_shift_tm_1 (shift_tm n 0 v) 0 0) as H1.
    cbn [Nat.add] in H1.
    rewrite (IH v Hcl) in H1.
    cbn [List.map] in H1.
    exact H1.
Qed.

Lemma shift_tm_closed_at : forall t cutoff a,
  free_tm_vars cutoff t = [] -> shift_tm a cutoff t = t.
Proof.
  apply (term_list_ind
    (fun t => forall cutoff a, free_tm_vars cutoff t = [] -> shift_tm a cutoff t = t)
    (fun ts => forall cutoff a,
       List.concat (List.map (free_tm_vars cutoff) ts) = [] ->
       List.map (shift_tm a cutoff) ts = ts)).
  - intros x cutoff a Hfree. simpl in *.
    destruct (Nat.ltb x cutoff) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      rewrite (proj2 (Nat.leb_gt cutoff x)) by lia. reflexivity.
    + discriminate.
  - intros t1 t2 IH1 IH2 cutoff a Hfree. simpl in *.
    apply List.app_eq_nil in Hfree as [H1 H2].
    rewrite (IH1 cutoff a H1), (IH2 cutoff a H2). reflexivity.
  - intros body T IH cutoff a Hfree. simpl in *.
    rewrite (IH (S cutoff) a Hfree). reflexivity.
  - intros t T IH cutoff a Hfree. simpl in *.
    rewrite (IH cutoff a Hfree). reflexivity.
  - intros bound body IH cutoff a Hfree. simpl in *.
    rewrite (IH cutoff a Hfree). reflexivity.
  - intros t l IH cutoff a Hfree. simpl in *.
    rewrite (IH cutoff a Hfree). reflexivity.
  - intros body IH cutoff a Hfree. simpl in *.
    rewrite (IH cutoff a Hfree). reflexivity.
  - intros K l lts Ts ts IH cutoff a Hfree. simpl in *.
    rewrite shift_tm_go_eq_map. f_equal. apply IH. rewrite free_tm_vars_go_eq_concat in Hfree. exact Hfree.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn cutoff a Hfree. simpl in *.
    apply List.app_eq_nil in Hfree as [Hs Hrest].
    apply List.app_eq_nil in Hrest as [Hy Hn].
    rewrite (IHs cutoff a Hs), (IHy (cutoff + arity) a Hy), (IHn cutoff a Hn). reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody cutoff a Hfree. simpl in *.
    apply List.app_eq_nil in Hfree as [Hop Hbody].
    rewrite (IHop (cutoff + 2) a Hop), (IHbody (S cutoff) a Hbody). reflexivity.
  - intros t Ss arg IHt IHarg cutoff a Hfree. simpl in *.
    apply List.app_eq_nil in Hfree as [Ht Harg].
    rewrite (IHt cutoff a Ht), (IHarg cutoff a Harg). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff a Hfree. simpl in *.
    rewrite (IHop (cutoff + 2) a Hfree). reflexivity.
  - intros m T_B T_R t IH cutoff a Hfree. simpl in *.
    rewrite (IH cutoff a Hfree). reflexivity.
  - intros m T_B T_R b IH cutoff a Hfree. simpl in *.
    rewrite (IH (S cutoff) a Hfree). reflexivity.
  - intros cutoff a Hfree. reflexivity.
  - intros t ts IHt IHts cutoff a Hfree. simpl in *.
    apply List.app_eq_nil in Hfree as [Ht Hts].
    rewrite (IHt cutoff a Ht), (IHts cutoff a Hts). reflexivity.
Qed.

Lemma shift_tm_closed : forall t a,
  free_tm_vars 0 t = [] -> shift_tm a 0 t = t.
Proof.
  intros t a Hfree. apply shift_tm_closed_at. exact Hfree.
Qed.

Lemma shift_tm_shift_lt_in_tm_closed0 : forall t a k,
  free_tm_vars 0 t = [] ->
  tm_lt_closed 0 t ->
  shift_tm a 0 (shift_lt_in_tm k 0 t) = t.
Proof.
  intros t a k Hfree Hlt.
  rewrite shift_lt_in_tm_closed by exact Hlt.
  apply shift_tm_closed. exact Hfree.
Qed.

Lemma shift_tm_shift_ty_in_tm_closed0 : forall t a k,
  free_tm_vars 0 t = [] ->
  tm_ty_closed 0 t ->
  shift_tm a 0 (shift_ty_in_tm k 0 t) = t.
Proof.
  intros t a k Hfree Hty.
  rewrite shift_ty_in_tm_closed by exact Hty.
  apply shift_tm_closed. exact Hfree.
Qed.

