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
Require Import ProgramCtx.
Require Import SubstTactics.

(* ================================================================== *)
(* SubstTm : substitute a term for a tm-binder at depth n             *)
(*                                                                    *)
(* [SubstTm v n G G'] threads the substituted value v through the     *)
(* binders between the substitution site and the target binder,       *)
(* shifting v at each term binder it crosses.  The typing payload     *)
(* ([typing_SubstTm], below) is proved for CLOSED values              *)
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
  | SubstTm_eff : forall v n G G' E n_a ops,
      SubstTm v n G G' ->
      SubstTm v n (bind_eff E n_a ops :: G)
                  (bind_eff E n_a ops :: G').

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
                 |v n G G' E n_a ops H IH]; intro K; simpl.
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
                 |v n G G' E0 n_a ops H IH]; intro E; simpl.
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
#[export] Hint Resolve lt_wf_SubstTm : ctxmap.

Lemma lifetimes_wf_SubstTm : forall G lts,
  lifetimes_wf G lts -> forall v n G', SubstTm v n G G' -> lifetimes_wf G' lts.
Proof.
  intros G lts Hwf. induction Hwf; intros v n G' HSub.
  - constructor.
  - constructor.
    + wf_transport.
    + apply (IHHwf v n G' HSub).
Qed.
#[export] Hint Resolve lifetimes_wf_SubstTm : ctxmap.

Definition capture_var_lifetime (G : ctx) (x : nat) : lifetime :=
  match ctx_lookup_tm G x with
  | Some T => lt_of_ty_G G T
  | None => lt_free
  end.

Definition capture_vars (G : ctx) (xs : list nat) : lifetime :=
  fold_right (fun x acc => lt_join (capture_var_lifetime G x) acc) lt_free xs.

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
  - subst y. apply LS_JoinR1.
    + apply LS_Refl. assumption.
    + assumption.
  - apply LS_JoinR2.
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
      apply LS_JoinR2.
      * apply IH. exact Htail.
      * wf_transport.
    + apply Nat.eqb_neq in Heq.
      assert (Heqlife : capture_var_lifetime G' (if Nat.ltb n x then pred x else x) =
        capture_var_lifetime G x).
      { change (capture_var_lifetime G' (subst_lt_var n x) = capture_var_lifetime G x).
        apply (capture_var_lifetime_SubstTm_eq v n G G' HSub x Heq). }
      apply lt_join_mono.
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
      * wf_transport.
      * apply (IHHwf2 v n G' HSub).
    + constructor.
      * wf_transport.
      * wf_transport.
    + constructor. apply (IHHwf (shift_lt_in_tm 1 0 v) n (bind_lt lt_local :: G')). apply SubstTm_lt. exact HSub.
    + constructor.
      * apply (IHHwf1 v n G' HSub).
      * apply (IHHwf2 (shift_ty_in_tm 1 0 v) n (bind_ty B :: G')). apply SubstTm_ty. exact HSub.
  - intros G Ts Hwf. induction Hwf; intros v n G' HSub.
    + constructor.
    + constructor.
      * wf_transport.
      * apply (IHHwf v n G' HSub).
Qed.
#[export] Hint Resolve types_wf_SubstTm : ctxmap.
#[export] Hint Resolve ty_wf_SubstTm : ctxmap.

Lemma lt_sub_SubstTm : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall v n G', SubstTm v n G G' -> G' ⊢ₗ l1 <: l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l Hwf|Γ l Hwf|Γ x Δ Hlk Hwf|Γ l Hwf
                 |Γ l1 l2 l3 H12 IH12 H23 IH23
                 |Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H IH Hwf2|Γ l l1 l2 H IH Hwf1]; intros v n G' HSub.
  - apply LS_Free. wf_transport.
  - apply LS_Local. wf_transport.
  - apply LS_Var.
    + rewrite (SubstTm_lookup_lt v n Γ G' HSub x). exact Hlk.
    + wf_transport.
  - apply LS_Refl. wf_transport.
  - eapply LS_Trans; [apply (IH12 v n G' HSub) | apply (IH23 v n G' HSub)].
  - apply LS_JoinL; [apply (IH1 v n G' HSub)|apply (IH2 v n G' HSub)].
  - apply LS_JoinR1.
    + apply (IH v n G' HSub).
    + wf_transport.
  - apply LS_JoinR2.
    + apply (IH v n G' HSub).
    + wf_transport.
Qed.
#[export] Hint Resolve lt_sub_SubstTm : ctxmap.

(* Escape side-condition transport under term substitution (type unchanged). *)
Lemma sub_free_SubstTm : forall v n G G' T,
  SubstTm v n G G' -> G ⊢ₗ lt_of_ty_G G T <: lt_free ->
  G' ⊢ₗ lt_of_ty_G G' T <: lt_free.
Proof.
  intros v n G G' T HS H. rewrite (lt_of_ty_G_SubstTm v n G G' HS T).
  wf_transport.
Qed.
#[export] Hint Resolve sub_free_SubstTm : ctxmap.

Lemma sub_free_list_SubstTm : forall v n G G' Ss,
  SubstTm v n G G' -> Forall (fun S => G ⊢ₗ lt_of_ty_G G S <: lt_free) Ss ->
  Forall (fun S => G' ⊢ₗ lt_of_ty_G G' S <: lt_free) Ss.
Proof.
  intros v n G G' Ss HS H. induction H; constructor;
    [eapply sub_free_SubstTm; eauto | auto].
Qed.
#[export] Hint Resolve sub_free_list_SubstTm : ctxmap.

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
  - apply SA_Refl. wf_transport.
  - eapply SA_Trans; [apply (IH1 v n G' HSub)|apply (IH2 v n G' HSub)].
  - apply SA_VarCtx.
    + rewrite (SubstTm_lookup_ty v n Γ G' HSub α). exact Hlk.
    + wf_transport.
  - apply SA_Data.
    + wf_transport.
    + wf_transport.
  - apply SA_Any.
    + wf_transport.
    + wf_transport.
    + rewrite (lt_of_ty_G_SubstTm v n Γ G' HSub T).
      wf_transport.
  - apply SA_Fun; [apply (IH1 v n G' HSub)|eapply lt_sub_SubstTm|apply (IH2 v n G' HSub)]; eauto.
  - apply SA_LtAll. apply (IH (shift_lt_in_tm 1 0 v) n (bind_lt lt_local :: G')). apply SubstTm_lt. exact HSub.
  - eapply SA_TyAll.
    + eapply ty_wf_SubstTm; [exact HwfA|]. apply SubstTm_ty. exact HSub.
    + eapply ty_wf_SubstTm; [exact HwfA'|]. apply SubstTm_ty. exact HSub.
    + apply (IH1 v n G' HSub).
    + apply (IH2 (shift_ty_in_tm 1 0 v) n (bind_ty B' :: G')). apply SubstTm_ty. exact HSub.
Qed.
#[export] Hint Resolve sub_SubstTm : ctxmap.


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
  - simpl.
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
  - rewrite IHT, multi_subst_lt_nil. reflexivity.
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

(* ================================================================== *)
(* The typing payload: term substitution preserves typing.            *)
(* the SubstTm_replacement_typed / target-closedness invariants,      *)
(* [typing_SubstTm], the typed-value                                  *)
(* capture/escape facts it rests on, and the eval_ctx corollaries.    *)
(* (Moved here from ProgramCtx.v, which owns the eval_ctx and         *)
(* closed-from theory this payload builds on.)                        *)
(* ================================================================== *)

Definition SubstTm_replacement_typed (v : term) (n : nat) (G G' : ctx) : Prop :=
  forall T, ctx_lookup_tm G n = Some T -> G' ⊢ₜ v : T.

Definition SubstTm_target_ty_closed0 (n : nat) (G : ctx) : Prop :=
  forall T, ctx_lookup_tm G n = Some T -> ty_ty_closed 0 T.

Definition SubstTm_target_lt_closed0 (n : nat) (G : ctx) : Prop :=
  forall T, ctx_lookup_tm G n = Some T -> ty_lt_closed 0 T.


Lemma SubstTm_replacement_typed_fold_bind_tm : forall rhos v n G G',
  SubstTm_replacement_typed v n G G' ->
  SubstTm_replacement_typed (shift_tm (List.length rhos) 0 v) (n + List.length rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G' rhos).
Proof.
  intros rhos v n G G' Hrep T Hlk.
  rewrite lookup_tm_skip_bind_tm_many in Hlk.
  apply typing_weaken_tm_shift_many. apply Hrep. exact Hlk.
Qed.

(* ----- single-binder replacement-typed preservation ---------------- *)
(* Going under one bind_tm / bind_ty / bind_lt preserves the typed-     *)
(* replacement property, by weakening the replacement through that      *)
(* binder.  The bind_lt case uses the GENERAL [typing_InsLt] (no        *)
(* closedness) — this is what lets [typing_SubstTm] thread              *)
(* replacement-typing as a per-node invariant instead of the UNSOUND    *)
(* universal HrepAll (which fails at bind_ctor/bind_eff: ctx_lookup_ctor *)
(* front-shadows).                                                       *)
Lemma SubstTm_replacement_typed_bind_tm : forall A v n G G',
  SubstTm_replacement_typed v n G G' ->
  SubstTm_replacement_typed (shift_tm 1 0 v) (S n) (bind_tm A :: G) (bind_tm A :: G').
Proof.
  intros A v n G G' Hrep T Hlk. simpl in Hlk.
  apply typing_weaken_tm_shift. apply Hrep. exact Hlk.
Qed.

Lemma SubstTm_replacement_typed_bind_ty : forall B v n G G',
  SubstTm_replacement_typed v n G G' ->
  SubstTm_replacement_typed (shift_ty_in_tm 1 0 v) n (bind_ty B :: G) (bind_ty B :: G').
Proof.
  intros B v n G G' Hrep T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm G n) as [T0|] eqn:Hbase; simpl in Hlk; [|discriminate].
  inversion Hlk; subst T; clear Hlk.
  apply typing_weaken_ty_shift. apply Hrep. exact Hbase.
Qed.

Lemma SubstTm_replacement_typed_bind_lt : forall D v n G G',
  SubstTm_replacement_typed v n G G' ->
  SubstTm_replacement_typed (shift_lt_in_tm 1 0 v) n (bind_lt D :: G) (bind_lt D :: G').
Proof.
  intros D v n G G' Hrep T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm G n) as [T0|] eqn:Hbase; simpl in Hlk; [|discriminate].
  inversion Hlk; subst T; clear Hlk.
  exact (typing_InsLt G' v T0 (Hrep T0 Hbase) 0 (bind_lt D :: G') (InsLt_here D G')).
Qed.

Lemma SubstTm_replacement_typed_push_match_bound : forall k Delta v n G G',
  SubstTm_replacement_typed v n G G' ->
  SubstTm_replacement_typed (shift_lt_in_tm k 0 v) n
    (push_match_bound k Delta G) (push_match_bound k Delta G').
Proof.
  induction k as [|k IH]; intros Delta v n G G' Hrep; simpl.
  - rewrite shift_lt_in_tm_zero. exact Hrep.
  - replace (shift_lt_in_tm (S k) 0 v) with (shift_lt_in_tm 1 0 (shift_lt_in_tm k 0 v)).
    2:{ rewrite shift_lt_in_tm_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    apply SubstTm_replacement_typed_bind_lt. apply IH. exact Hrep.
Qed.

Lemma SubstTm_replacement_typed_push_ty_vars : forall k B v n G G',
  SubstTm_replacement_typed v n G G' ->
  SubstTm_replacement_typed (shift_ty_in_tm k 0 v) n
    (push_ty_vars k B G) (push_ty_vars k B G').
Proof.
  intros k B v n G G' Hrep T Hlk.
  rewrite ctx_lookup_tm_push_ty_vars in Hlk.
  destruct (ctx_lookup_tm G n) as [T0|] eqn:Hbase; [|discriminate].
  simpl in Hlk. inversion Hlk; subst T; clear Hlk.
  apply typing_push_ty_vars_shift. apply Hrep. exact Hbase.
Qed.


Lemma SubstTm_target_ty_closed0_tm : forall n G A,
  SubstTm_target_ty_closed0 n G ->
  SubstTm_target_ty_closed0 (S n) (bind_tm A :: G).
Proof.
  intros n G A Htarget T Hlk. simpl in Hlk. apply Htarget. exact Hlk.
Qed.

Lemma SubstTm_target_ty_closed0_ty : forall n G B,
  SubstTm_target_ty_closed0 n G ->
  SubstTm_target_ty_closed0 n (bind_ty B :: G).
Proof.
  intros n G B Htarget T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm G n) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst; clear Hlk.
  rewrite shift_ty_in_ty_closed by (apply Htarget; exact Hbase).
  apply Htarget. exact Hbase.
Qed.

Lemma SubstTm_target_ty_closed0_lt : forall n G D,
  SubstTm_target_ty_closed0 n G ->
  SubstTm_target_ty_closed0 n (bind_lt D :: G).
Proof.
  intros n G D Htarget T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm G n) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst; clear Hlk.
  apply ty_ty_closed_shift_lt. apply Htarget. exact Hbase.
Qed.

Lemma SubstTm_target_lt_closed0_tm : forall n G A,
  SubstTm_target_lt_closed0 n G ->
  SubstTm_target_lt_closed0 (S n) (bind_tm A :: G).
Proof.
  intros n G A Htarget T Hlk. simpl in Hlk. apply Htarget. exact Hlk.
Qed.

Lemma SubstTm_target_lt_closed0_ty : forall n G B,
  SubstTm_target_lt_closed0 n G ->
  SubstTm_target_lt_closed0 n (bind_ty B :: G).
Proof.
  intros n G B Htarget T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm G n) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst; clear Hlk.
  apply ty_lt_closed_shift_ty. apply Htarget. exact Hbase.
Qed.

Lemma SubstTm_target_lt_closed0_lt : forall n G D,
  SubstTm_target_lt_closed0 n G ->
  SubstTm_target_lt_closed0 n (bind_lt D :: G).
Proof.
  intros n G D Htarget T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm G n) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst; clear Hlk.
  rewrite shift_lt_in_type_closed by (apply Htarget; exact Hbase).
  apply Htarget. exact Hbase.
Qed.


Lemma SubstTm_target_ty_closed0_push_match_bound : forall k Delta n G,
  SubstTm_target_ty_closed0 n G ->
  SubstTm_target_ty_closed0 n (push_match_bound k Delta G).
Proof.
  induction k as [|k IH]; intros Delta n G Htarget; simpl.
  - exact Htarget.
  - apply SubstTm_target_ty_closed0_lt. apply IH. exact Htarget.
Qed.

Lemma SubstTm_target_lt_closed0_push_match_bound : forall k Delta n G,
  SubstTm_target_lt_closed0 n G ->
  SubstTm_target_lt_closed0 n (push_match_bound k Delta G).
Proof.
  induction k as [|k IH]; intros Delta n G Htarget; simpl.
  - exact Htarget.
  - apply SubstTm_target_lt_closed0_lt. apply IH. exact Htarget.
Qed.

Lemma SubstTm_target_ty_closed0_push_ty_vars : forall k B n G,
  SubstTm_target_ty_closed0 n G ->
  SubstTm_target_ty_closed0 n (push_ty_vars k B G).
Proof.
  induction k as [|k IH]; intros B n G Htarget; simpl.
  - exact Htarget.
  - apply IH. apply SubstTm_target_ty_closed0_ty. exact Htarget.
Qed.

Lemma SubstTm_target_lt_closed0_push_ty_vars : forall k B n G,
  SubstTm_target_lt_closed0 n G ->
  SubstTm_target_lt_closed0 n (push_ty_vars k B G).
Proof.
  induction k as [|k IH]; intros B n G Htarget; simpl.
  - exact Htarget.
  - apply IH. apply SubstTm_target_lt_closed0_ty. exact Htarget.
Qed.

Lemma SubstTm_target_ty_closed0_fold_bind_tm : forall rhos n G,
  SubstTm_target_ty_closed0 n G ->
  SubstTm_target_ty_closed0 (n + List.length rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos).
Proof.
  intros rhos n G Htarget T Hlk.
  rewrite lookup_tm_skip_bind_tm_many in Hlk.
  apply Htarget. exact Hlk.
Qed.

Lemma SubstTm_target_lt_closed0_fold_bind_tm : forall rhos n G,
  SubstTm_target_lt_closed0 n G ->
  SubstTm_target_lt_closed0 (n + List.length rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos).
Proof.
  intros rhos n G Htarget T Hlk.
  rewrite lookup_tm_skip_bind_tm_many in Hlk.
  apply Htarget. exact Hlk.
Qed.


Lemma Forall2_typing_SubstTm_global : forall Γ vs rhos,
  Forall2 (fun v rho => forall repl n G',
    SubstTm repl n Γ G' ->
    free_tm_vars 0 repl = [] ->
    tm_ty_closed 0 repl ->
    tm_lt_closed 0 repl ->
    SubstTm_target_ty_closed0 n Γ ->
    SubstTm_target_lt_closed0 n Γ ->
    SubstTm_replacement_typed repl n Γ G' ->
    forall c,
    ctx_lt_closed_from c G' ->
    ctx_schemas_lt_closed_from c G' ->
    G' ⊢ₗ capture_lt G' repl <: capture_var_lifetime Γ n ->
    G' ⊢ₜ subst_tm n repl v : rho) vs rhos ->
  forall repl n G',
    SubstTm repl n Γ G' ->
    free_tm_vars 0 repl = [] ->
    tm_ty_closed 0 repl ->
    tm_lt_closed 0 repl ->
    SubstTm_target_ty_closed0 n Γ ->
    SubstTm_target_lt_closed0 n Γ ->
    SubstTm_replacement_typed repl n Γ G' ->
    forall c,
    ctx_lt_closed_from c G' ->
    ctx_schemas_lt_closed_from c G' ->
    G' ⊢ₗ capture_lt G' repl <: capture_var_lifetime Γ n ->
    Forall2 (fun v rho => G' ⊢ₜ v : rho)
             (List.map (subst_tm n repl) vs) rhos.
Proof.
  intros Γ vs rhos H. induction H; intros repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap; simpl.
  - constructor.
  - constructor.
    + apply (H repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    + apply (IHForall2 repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
Qed.

Lemma typing_SubstTm : forall Γ t T,
  Γ ⊢ₜ t : T ->
  forall repl n G',
    SubstTm repl n Γ G' ->
    free_tm_vars 0 repl = [] ->
    tm_ty_closed 0 repl ->
    tm_lt_closed 0 repl ->
    SubstTm_target_ty_closed0 n Γ ->
    SubstTm_target_lt_closed0 n Γ ->
    SubstTm_replacement_typed repl n Γ G' ->
    forall c,
    ctx_lt_closed_from c G' ->
    ctx_schemas_lt_closed_from c G' ->
    G' ⊢ₗ capture_lt G' repl <: capture_var_lifetime Γ n ->
    G' ⊢ₜ subst_tm n repl t : T.
Proof.
  apply (typing_ind_forall2
    (fun Γ t T => forall repl n G',
      SubstTm repl n Γ G' ->
      free_tm_vars 0 repl = [] ->
      tm_ty_closed 0 repl ->
      tm_lt_closed 0 repl ->
      SubstTm_target_ty_closed0 n Γ ->
      SubstTm_target_lt_closed0 n Γ ->
      SubstTm_replacement_typed repl n Γ G' ->
      forall c,
      ctx_lt_closed_from c G' ->
      ctx_schemas_lt_closed_from c G' ->
      G' ⊢ₗ capture_lt G' repl <: capture_var_lifetime Γ n ->
      G' ⊢ₜ subst_tm n repl t : T)).
  - intros Γ x T Hlk HwfT repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. destruct (Nat.eqb x n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst x.
      exact (HrepAll T Hlk).
    + apply Nat.eqb_neq in Heq.
      destruct (Nat.ltb n x) eqn:Hltx.
      * apply T_Var.
        -- assert (Hidx : subst_lt_var n x = pred x) by (unfold subst_lt_var; rewrite Hltx; reflexivity).
          rewrite <- Hidx.
          rewrite (SubstTm_lookup_tm repl n Γ G' HSub x Heq). exact Hlk.
        -- wf_transport.
      * apply T_Var.
        -- assert (Hidx : subst_lt_var n x = x) by (unfold subst_lt_var; rewrite Hltx; reflexivity).
          rewrite <- Hidx.
          rewrite (SubstTm_lookup_tm repl n Γ G' HSub x Heq). exact Hlk.
        -- wf_transport.
  - intros Γ t T U Ht IH Hsub repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    eapply T_Sub.
    + apply (IH repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    + wf_transport.
  - intros Γ body A l B HwfA HwfB Hbody IHbody HcapLam repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas HcapRepl.
    simpl. apply T_Lam.
    + wf_transport.
    + wf_transport.
    + apply (IHbody (shift_tm 1 0 repl) (S n) (bind_tm A :: G')
      (SubstTm_tm repl n Γ G' A HSub)
      (free_tm_vars_closed_shift_tm_any 1 repl Hfree)
      (tm_ty_closed_shift_tm repl 0 1 0 HtmTy)
      (tm_lt_closed_shift_tm repl 0 1 0 HtmLt)
      (SubstTm_target_ty_closed0_tm n Γ A HtargetTy)
      (SubstTm_target_lt_closed0_tm n Γ A HtargetLt)
      (SubstTm_replacement_typed_bind_tm A repl n Γ G' HrepAll) c).
      * apply ctx_lt_closed_from_bind_tm. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_tm. exact Hschemas.
      * apply replacement_capture_bound_tm; assumption.
    + destruct (lt_sub_wf _ _ _ HcapLam) as [HwfCap _].
      eapply LS_Trans.
      * eapply capture_lt_SubstTm_le_closed; eauto.
      * wf_transport.
  - intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. eapply T_App.
    + apply (IH1 repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    + apply (IH2 repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
  - intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. apply T_TyLam.
    + wf_transport.
    + eapply ty_wf_SubstTm; [exact HwfT|]. apply SubstTm_ty. exact HSub.
    + apply is_abs_subst_tm_true. exact HisAbs.
    + apply (IHbody (shift_ty_in_tm 1 0 repl) n (bind_ty bound :: G')
      (SubstTm_ty repl n Γ G' bound HSub)
      ltac:(rewrite free_tm_vars_shift_ty_in_tm; exact Hfree)
      (tm_ty_closed_shift_ty_closed0 repl 1 HtmTy)
      (tm_lt_closed_shift_ty repl 0 1 0 HtmLt)
      (SubstTm_target_ty_closed0_ty n Γ bound HtargetTy)
      (SubstTm_target_lt_closed0_ty n Γ bound HtargetLt)
      (SubstTm_replacement_typed_bind_ty bound repl n Γ G' HrepAll) c).
      * apply ctx_lt_closed_from_bind_ty. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_ty. exact Hschemas.
      * apply replacement_capture_bound_ty; assumption.
  - intros Γ t B U S Ht IH HwfS Hsub repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. eapply T_TyApp.
    + apply (IH repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    + wf_transport.
    + wf_transport.
  - intros Γ body T HwfT HisAbs Hbody IHbody repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. apply T_LtLam.
    + eapply ty_wf_SubstTm; [exact HwfT|]. apply SubstTm_lt. exact HSub.
    + apply is_abs_subst_tm_true. exact HisAbs.
    + apply (IHbody (shift_lt_in_tm 1 0 repl) n (bind_lt lt_local :: G')
      (SubstTm_lt repl n Γ G' lt_local HSub)
      ltac:(rewrite free_tm_vars_shift_lt_in_tm; exact Hfree)
      (tm_ty_closed_shift_lt repl 0 1 0 HtmTy)
      (tm_lt_closed_shift_lt_closed0 repl 1 HtmLt)
      (SubstTm_target_ty_closed0_lt n Γ lt_local HtargetTy)
      (SubstTm_target_lt_closed0_lt n Γ lt_local HtargetLt)
      (SubstTm_replacement_typed_bind_lt lt_local repl n Γ G' HrepAll) (S c)).
      * apply ctx_lt_closed_from_bind_lt. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_lt. exact Hschemas.
      * apply replacement_capture_bound_lt; assumption.
  - intros Γ t T l Ht IH Hwfl repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. eapply T_LtApp.
    + apply (IH repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    + wf_transport.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
      result_ty result_tag l vs Hctor Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs Hresult Hshape
      Hresult_eff Hwfl HltSub Hbounded Hlen_vs Hargs IHargs repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl.    eapply T_Ctor with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := sigma_fields) (result_ty_schema := result_ty_schema)
      (lts := lts) (rho_fields := rho_fields) (result_tag := result_tag).
    + rewrite (SubstTm_lookup_ctor repl n Γ G' HSub K). exact Hctor.
    + rewrite (SubstTm_lookup_eff repl n Γ G' HSub K). exact Heff.
    + exact Hlen_lts.
    + wf_transport.
    + exact Hrho.
    + exact Hlen_Ts.
    + wf_transport.
    + exact Hresult.
    + exact Hshape.
    + rewrite (SubstTm_lookup_eff repl n Γ G' HSub result_tag). exact Hresult_eff.
    + wf_transport.
    + wf_transport.
    + eapply Forall_impl.
      * intros l0 Hl0. exact (lt_sub_SubstTm Γ l0 l Hl0 repl n G' HSub).
      * exact Hbounded.
    + rewrite length_map. exact Hlen_vs.
    + apply typings_Forall2.
      exact (Forall2_typing_SubstTm_global Γ vs rho_fields IHargs
      repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    all: try solve [eauto].
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
      rho_fields scrut_result_ty result_tag result_l Γyes yes_body eta elim_result no_body
      HKne Hctor Heff Hlts Hrho Hlen_Ts HwfTs Hscrut_result Hscrut_shape Hresult_eff Hresult_ne
      HwfDelta Hresult_l Hscrut IHscrut Harity HΓyes Hyes IHyes Helim Hno IHno repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    subst Γyes. simpl.
    eapply T_Match with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := sigma_fields) (result_ty_schema := result_ty_schema)
      (lts := lts) (rho_fields := rho_fields)
      (scrut_result_ty := scrut_result_ty)
      (result_tag := result_tag) (result_l := result_l)
      (Γ' := push_match_bound n_lt Delta G') (eta := eta).
    + exact HKne.
    + rewrite (SubstTm_lookup_ctor repl n Γ G' HSub K). exact Hctor.
    + rewrite (SubstTm_lookup_eff repl n Γ G' HSub K). exact Heff.
    + exact Hlts.
    + exact Hrho.
    + exact Hlen_Ts.
    + wf_transport.
    + exact Hscrut_result.
    + exact Hscrut_shape.
    + rewrite (SubstTm_lookup_eff repl n Γ G' HSub result_tag). exact Hresult_eff.
    + exact Hresult_ne.
    + wf_transport.
    + wf_transport.
    + apply (IHscrut repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    + exact Harity.
    + reflexivity.
    + replace (subst_tm (n + arity) (shift_tm arity 0 (shift_lt_in_tm n_lt 0 repl)) yes_body)
        with (subst_tm (n + List.length rho_fields)
          (shift_tm (List.length rho_fields) 0 (shift_lt_in_tm n_lt 0 repl)) yes_body)
        by (rewrite Harity; reflexivity).
      refine (IHyes (shift_tm (List.length rho_fields) 0 (shift_lt_in_tm n_lt 0 repl))
        (n + List.length rho_fields)
        (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) (push_match_bound n_lt Delta G') rho_fields)
        _ _ _ _ _ _
        (SubstTm_replacement_typed_fold_bind_tm rho_fields (shift_lt_in_tm n_lt 0 repl) n
          (push_match_bound n_lt Delta Γ) (push_match_bound n_lt Delta G')
          (SubstTm_replacement_typed_push_match_bound n_lt Delta repl n Γ G' HrepAll))
        (c + n_lt) _ _ _).
      * apply SubstTm_fold_bind_tm. apply SubstTm_push_match_bound. exact HSub.
      * apply free_tm_vars_closed_shift_tm_any. rewrite free_tm_vars_shift_lt_in_tm_any. exact Hfree.
      * apply tm_ty_closed_shift_tm. apply tm_ty_closed_shift_lt. exact HtmTy.
      * apply tm_lt_closed_shift_tm. apply tm_lt_closed_shift_lt_closed0. exact HtmLt.
      * apply SubstTm_target_ty_closed0_fold_bind_tm. apply SubstTm_target_ty_closed0_push_match_bound. exact HtargetTy.
      * apply SubstTm_target_lt_closed0_fold_bind_tm. apply SubstTm_target_lt_closed0_push_match_bound. exact HtargetLt.
      * apply ctx_lt_closed_from_fold_bind_tm. apply ctx_lt_closed_from_push_match_bound. exact Hlt.
      * apply ctx_schemas_lt_closed_from_fold_bind_tm. apply ctx_schemas_lt_closed_from_push_match_bound. exact Hschemas.
      * apply replacement_capture_bound_fold_bind_tm.
        -- rewrite free_tm_vars_shift_lt_in_tm_any. exact Hfree.
        -- apply replacement_capture_bound_push_match_bound; assumption.
    + exact Helim.
    + apply (IHno repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
  - intros Γ E_tag m Ts op_bodies n_α ops T_R
      Heff Hlen HwfTs HwfTR Hfst Hops IHops repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. rewrite subst_tm_ops_eq_map.
    eapply T_Cap with (ops := ops).
    + rewrite (SubstTm_lookup_eff repl n Γ G' HSub E_tag). exact Heff.
    + exact Hlen.
    + wf_transport.
    + wf_transport.
    + rewrite List.map_map. exact Hfst.
    + apply typing_ops_Forall2. clear Hops Heff Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IH]; simpl.
      * constructor.
      * constructor; [| exact IH].
        simpl.
        set (sig_b := inst_op_ty_args n_α Ts (op_nb osig) (op_sig_ty osig)).
        set (ret_b := inst_op_ty_args n_α Ts (op_nb osig) (op_ret_ty osig)).
        set (rho_k := type_fun ret_b lt_local (shift_ty (op_nb osig) 0 T_R)).
        replace (subst_tm (n + 2) (shift_tm 2 0 repl) (snd ob))
          with (subst_tm (n + List.length [sig_b; rho_k])
            (shift_tm (List.length [sig_b; rho_k]) 0 (shift_ty_in_tm (op_nb osig) 0 repl)) (snd ob)).
        2:{ simpl. rewrite shift_ty_in_tm_closed by exact HtmTy. reflexivity. }
        refine (Hone (shift_tm (List.length [sig_b; rho_k]) 0
            (shift_ty_in_tm (op_nb osig) 0 repl)) (n + List.length [sig_b; rho_k])
          (fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
            (push_ty_vars (op_nb osig) any_at_free G') [sig_b; rho_k])
          _ _ _ _ _ _
          (SubstTm_replacement_typed_fold_bind_tm
            [sig_b; rho_k] (shift_ty_in_tm (op_nb osig) 0 repl) n
            (push_ty_vars (op_nb osig) any_at_free Γ) (push_ty_vars (op_nb osig) any_at_free G')
            (SubstTm_replacement_typed_push_ty_vars (op_nb osig) any_at_free repl n Γ G' HrepAll))
          c _ _ _).
        -- exact (SubstTm_fold_bind_tm [sig_b; rho_k]
             (shift_ty_in_tm (op_nb osig) 0 repl) n
             (push_ty_vars (op_nb osig) any_at_free Γ)
             (push_ty_vars (op_nb osig) any_at_free G')
             (SubstTm_push_ty_vars_any_at_free (op_nb osig) repl n Γ G' HSub)).
        -- apply free_tm_vars_closed_shift_tm_any. rewrite free_tm_vars_shift_ty_in_tm_any. exact Hfree.
        -- apply tm_ty_closed_shift_tm. apply tm_ty_closed_shift_ty_closed0. exact HtmTy.
        -- apply tm_lt_closed_shift_tm. apply tm_lt_closed_shift_ty. exact HtmLt.
        -- exact (SubstTm_target_ty_closed0_fold_bind_tm [sig_b; rho_k] n
             (push_ty_vars (op_nb osig) any_at_free Γ)
             (SubstTm_target_ty_closed0_push_ty_vars (op_nb osig) any_at_free n Γ HtargetTy)).
        -- exact (SubstTm_target_lt_closed0_fold_bind_tm [sig_b; rho_k] n
             (push_ty_vars (op_nb osig) any_at_free Γ)
             (SubstTm_target_lt_closed0_push_ty_vars (op_nb osig) any_at_free n Γ HtargetLt)).
        -- apply ctx_lt_closed_from_fold_bind_tm. apply ctx_lt_closed_from_push_ty_vars. exact Hlt.
        -- apply ctx_schemas_lt_closed_from_fold_bind_tm. apply ctx_schemas_lt_closed_from_push_ty_vars. exact Hschemas.
        -- exact (replacement_capture_bound_fold_bind_tm [sig_b; rho_k]
             (push_ty_vars (op_nb osig) any_at_free Γ)
             (push_ty_vars (op_nb osig) any_at_free G')
             (shift_ty_in_tm (op_nb osig) 0 repl) n
             ltac:(rewrite free_tm_vars_shift_ty_in_tm_any; exact Hfree)
             (replacement_capture_bound_push_ty_vars_any_at_free
               (op_nb osig) Γ G' repl n Hfree Hcap)).
  - intros Γ E_tag Ts op_bodies body n_α ops T_B T_R
      Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hfst Hops IHops Hbody IHbody repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. rewrite subst_tm_ops_eq_map.
    eapply T_Handle with (ops := ops) (T_B := T_B).
    + rewrite (SubstTm_lookup_eff repl n Γ G' HSub E_tag). exact Heff.
    + exact Hlen.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + rewrite List.map_map. exact Hfst.
    + apply typing_ops_Forall2. clear Hops Heff Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IH]; simpl.
      * constructor.
      * constructor; [| exact IH].
        simpl.
        set (sig_b := inst_op_ty_args n_α Ts (op_nb osig) (op_sig_ty osig)).
        set (ret_b := inst_op_ty_args n_α Ts (op_nb osig) (op_ret_ty osig)).
        set (rho_k := type_fun ret_b lt_local (shift_ty (op_nb osig) 0 T_R)).
        replace (subst_tm (n + 2) (shift_tm 2 0 repl) (snd ob))
          with (subst_tm (n + List.length [sig_b; rho_k])
            (shift_tm (List.length [sig_b; rho_k]) 0 (shift_ty_in_tm (op_nb osig) 0 repl)) (snd ob)).
        2:{ simpl. rewrite shift_ty_in_tm_closed by exact HtmTy. reflexivity. }
        refine (Hone (shift_tm (List.length [sig_b; rho_k]) 0
            (shift_ty_in_tm (op_nb osig) 0 repl)) (n + List.length [sig_b; rho_k])
          (fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
            (push_ty_vars (op_nb osig) any_at_free G') [sig_b; rho_k])
          _ _ _ _ _ _
          (SubstTm_replacement_typed_fold_bind_tm
            [sig_b; rho_k] (shift_ty_in_tm (op_nb osig) 0 repl) n
            (push_ty_vars (op_nb osig) any_at_free Γ) (push_ty_vars (op_nb osig) any_at_free G')
            (SubstTm_replacement_typed_push_ty_vars (op_nb osig) any_at_free repl n Γ G' HrepAll))
          c _ _ _).
        -- exact (SubstTm_fold_bind_tm [sig_b; rho_k]
             (shift_ty_in_tm (op_nb osig) 0 repl) n
             (push_ty_vars (op_nb osig) any_at_free Γ)
             (push_ty_vars (op_nb osig) any_at_free G')
             (SubstTm_push_ty_vars_any_at_free (op_nb osig) repl n Γ G' HSub)).
        -- apply free_tm_vars_closed_shift_tm_any. rewrite free_tm_vars_shift_ty_in_tm_any. exact Hfree.
        -- apply tm_ty_closed_shift_tm. apply tm_ty_closed_shift_ty_closed0. exact HtmTy.
        -- apply tm_lt_closed_shift_tm. apply tm_lt_closed_shift_ty. exact HtmLt.
        -- exact (SubstTm_target_ty_closed0_fold_bind_tm [sig_b; rho_k] n
             (push_ty_vars (op_nb osig) any_at_free Γ)
             (SubstTm_target_ty_closed0_push_ty_vars (op_nb osig) any_at_free n Γ HtargetTy)).
        -- exact (SubstTm_target_lt_closed0_fold_bind_tm [sig_b; rho_k] n
             (push_ty_vars (op_nb osig) any_at_free Γ)
             (SubstTm_target_lt_closed0_push_ty_vars (op_nb osig) any_at_free n Γ HtargetLt)).
        -- apply ctx_lt_closed_from_fold_bind_tm. apply ctx_lt_closed_from_push_ty_vars. exact Hlt.
        -- apply ctx_schemas_lt_closed_from_fold_bind_tm. apply ctx_schemas_lt_closed_from_push_ty_vars. exact Hschemas.
        -- exact (replacement_capture_bound_fold_bind_tm [sig_b; rho_k]
             (push_ty_vars (op_nb osig) any_at_free Γ)
             (push_ty_vars (op_nb osig) any_at_free G')
             (shift_ty_in_tm (op_nb osig) 0 repl) n
             ltac:(rewrite free_tm_vars_shift_ty_in_tm_any; exact Hfree)
             (replacement_capture_bound_push_ty_vars_any_at_free
               (op_nb osig) Γ G' repl n Hfree Hcap)).
    + refine (IHbody (shift_tm 1 0 repl) (S n) (bind_tm (type_ctor E_tag lt_local Ts) :: G')
      _ _ _ _ _ _
      (SubstTm_replacement_typed_bind_tm (type_ctor E_tag lt_local Ts) repl n Γ G' HrepAll)
      c _ _ _).
      * apply SubstTm_tm. exact HSub.
      * apply free_tm_vars_closed_shift_tm_any. exact Hfree.
      * apply tm_ty_closed_shift_tm. exact HtmTy.
      * apply tm_lt_closed_shift_tm. exact HtmLt.
      * apply SubstTm_target_ty_closed0_tm. exact HtargetTy.
      * apply SubstTm_target_lt_closed0_tm. exact HtargetLt.
      * apply ctx_lt_closed_from_bind_tm. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_tm. exact Hschemas.
      * apply replacement_capture_bound_tm; assumption.
  - intros Γ recv op arg E_tag Delta Ts Ss n_α ops n_β sig ret sig_inst ret_inst
      Hrecv IHrecv Heff Hnth Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. eapply T_Perform with
      (n_α := n_α) (ops := ops) (n_β := n_β) (sig := sig) (ret := ret)
      (sig_inst := sig_inst) (ret_inst := ret_inst).
    + apply (IHrecv repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    + rewrite (SubstTm_lookup_eff repl n Γ G' HSub E_tag). exact Heff.
    + exact Hnth.
    + exact Hlen_Ts.
    + exact Hlen_Ss.
    + wf_transport.
    + wf_transport.
    + exact Hsig.
    + wf_transport.
    + exact Hret.
    + wf_transport.
    + apply (IHarg repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. apply T_HandlerM.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + apply (IH repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
Qed.

Fixpoint has_rt_cap_list (ts : list term) : bool :=
  match ts with
  | [] => false
  | t :: rest => orb (has_rt_cap t) (has_rt_cap_list rest)
  end.

Lemma Forall2_typing_lt_of_ty_list_wf : forall Γ vs rhos,
  eval_ctx Γ ->
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rhos ->
  lt_wf Γ (lt_of_ty_list rhos).
Proof.
  intros Γ vs rhos Hec Hty. induction Hty; simpl.
  - constructor.
  - constructor.
    + pose proof (typing_implies_wf Γ x y H) as Hwf.
      pose proof (ty_wf_eval_ctx_ty_closed Γ y Hec Hwf) as Hclosed.
      rewrite <- (lt_of_ty_G_ty_closed_eq Γ y Hclosed).
      apply lt_of_ty_G_wf. exact Hwf.
    + exact IHHty.
Qed.

Lemma Forall2_value_capture_has_rt_cap_list : forall Γ vs rhos,
  eval_ctx Γ ->
  Forall2 (fun v rho =>
    eval_ctx Γ -> value v -> free_tm_vars 0 v = [] ->
    Γ ⊢ₗ capture_lt Γ v <: lt_of_ty_G Γ rho) vs rhos ->
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rhos ->
  Forall value vs ->
  List.concat (List.map (free_tm_vars 0) vs) = [] ->
  has_rt_cap_list vs = true ->
  Γ ⊢ₗ lt_local <: lt_of_ty_list rhos.
Proof.
  intros Γ vs rhos Hec HcapF HtyF HvalF Hfree HcapList.
  induction HcapF as [|v rho vs rhos Hcap IHcapF IHHcapF].
  - simpl in HcapList. discriminate.
  - inversion HtyF as [|v' rho' vs' rhos' Hty HtyTail Heq1 Heq2]; subst.
    inversion HvalF as [|v0 vs0 Hv Hvals Heq]; subst.
    simpl in Hfree. apply List.app_eq_nil in Hfree as [HfreeV HfreeVs].
    simpl in HcapList. apply Bool.orb_true_iff in HcapList as [HcapV | HcapVs].
    + apply LS_JoinR1.
      * specialize (Hcap Hec Hv HfreeV).
        rewrite (capture_lt_closed Γ v HfreeV) in Hcap. rewrite HcapV in Hcap. simpl in Hcap.
        pose proof (typing_implies_wf Γ v rho Hty) as Hwf.
        pose proof (ty_wf_eval_ctx_ty_closed Γ rho Hec Hwf) as Hclosed.
        rewrite <- (lt_of_ty_G_ty_closed_eq Γ rho Hclosed). exact Hcap.
      * eapply Forall2_typing_lt_of_ty_list_wf; eauto.
    + apply LS_JoinR2.
      * apply IHHcapF; assumption.
      * pose proof (typing_implies_wf Γ v rho Hty) as Hwf.
        pose proof (ty_wf_eval_ctx_ty_closed Γ rho Hec Hwf) as Hclosed.
        rewrite <- (lt_of_ty_G_ty_closed_eq Γ rho Hclosed).
        apply lt_of_ty_G_wf. exact Hwf.
Qed.

Lemma typing_value_capture_lt_le_type : forall Γ v T,
  Γ ⊢ₜ v : T ->
  eval_ctx Γ ->
  value v ->
  free_tm_vars 0 v = [] ->
  Γ ⊢ₗ capture_lt Γ v <: lt_of_ty_G Γ T.
Proof.
  apply (typing_ind_forall2
    (fun Γ v T => eval_ctx Γ -> value v -> free_tm_vars 0 v = [] ->
      Γ ⊢ₗ capture_lt Γ v <: lt_of_ty_G Γ T)).
  - intros Γ x T Hlk HwfT Hec Hval Hfree. inversion Hval.
  - intros Γ t T U Ht IH Hsub Hec Hval Hfree.
    eapply LS_Trans.
    + apply IH; assumption.
    + apply lt_of_ty_G_mono_sub. exact Hsub.
  - intros Γ body A l B HwfA HwfB Hbody IHbody Hcap Hec Hval Hfree.
    inversion Hval; subst. simpl in Hfree.
    rewrite (capture_lt_closed Γ (term_lam body A) Hfree). simpl.
    unfold lt_of_ty_G. rewrite lt_of_ty_ctx_fun.
    destruct (has_rt_cap body) eqn:HcapBody.
    + unfold capture_lt in Hcap. rewrite HcapBody in Hcap. exact Hcap.
    + apply LS_Free. destruct (lt_sub_wf _ _ _ Hcap) as [_ Hwfl]. exact Hwfl.
  - intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 Hec Hval Hfree. inversion Hval.
  - intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody Hec Hval Hfree.
    inversion Hval; subst.
    rewrite (capture_lt_closed Γ (term_ty_lam bound body) Hfree). simpl.
    unfold lt_of_ty_G. rewrite lt_of_ty_ctx_tyall.
    destruct (has_rt_cap body) eqn:HcapBody.
    + apply LS_Refl. constructor.
    + apply LS_Free. constructor.
  - intros Γ t B U S Ht IH HwfS Hsub Hec Hval Hfree. inversion Hval.
  - intros Γ body T HwfT HisAbs Hbody IHbody Hec Hval Hfree.
    inversion Hval; subst.
    rewrite (capture_lt_closed Γ (term_lt_lam body) Hfree). simpl.
    unfold lt_of_ty_G. rewrite lt_of_ty_ctx_ltall.
    destruct (has_rt_cap body) eqn:HcapBody.
    + apply LS_Refl. constructor.
    + apply LS_Free. constructor.
  - intros Γ t T l Ht IH Hwfl Hec Hval Hfree. inversion Hval.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
           Hlk Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs Hresult Hshape
           Hresult_eff Hwfl Hlt Hforall Hlen_vs Hfields IHfields Hec Hval Hfree.
    inversion Hval as [| | |K0 l0 lts0 Ts0 vs0 Hvals Heq|]; subst.
    rewrite (capture_lt_closed Γ (term_ctor K l lts Ts vs) Hfree). simpl.
    change (existsb has_rt_cap vs) with (has_rt_cap_list vs).
    destruct (has_rt_cap_list vs) eqn:HcapVs.
    + rewrite Hshape. unfold lt_of_ty_G. rewrite lt_of_ty_ctx_ctor.
      match type of Hfields with
      | Forall2 _ vs ?rhos =>
          assert (HlocalFields : Γ ⊢ₗ lt_local <: lt_of_ty_list rhos)
            by (eapply Forall2_value_capture_has_rt_cap_list;
                [exact Hec|exact IHfields|exact Hfields|exact Hvals|
                 simpl in Hfree; exact Hfree|
                 exact HcapVs])
      end.
      rewrite Hshape in Hlt. rewrite lt_of_ty_ctor_eq in Hlt.
      eapply LS_Trans; [exact HlocalFields|].
      eapply LS_Trans; [exact Hlt|].
      apply lt_join_mono; [apply LS_Refl; exact Hwfl|].
      eapply lt_of_ty_list_le_lt_of_ty_ctx_list. exact HwfTs.
    + apply LS_Free. apply lt_of_ty_G_wf. rewrite Hshape. constructor; assumption.
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γ' yes_body eta
           elim_result no_body HKne Hlk Heff Hlts Hrho Hlen_Ts HwfTs
           Hscrut_result Hscrut_shape Hresult_eff Hresult_ne HwfDelta Hresult_l Hscrut IHscrut
           Harity HGamma' Hyes IHyes Helim Hno IHno Hec Hval Hfree. inversion Hval.
  - intros Γ E_tag m Ts op_bodies n_α ops T_R
           Heff Hlen HwfTs HwfTR Hfst Hops IHops Hec Hval Hfree.
    inversion Hval; subst.
    rewrite (capture_lt_closed Γ (term_cap E_tag m Ts T_R op_bodies) Hfree). simpl.
    unfold lt_of_ty_G. rewrite lt_of_ty_ctx_ctor.
    apply LS_JoinR1.
    + apply LS_Refl. constructor.
    + eapply lt_of_ty_G_list_wf; eauto.
  - intros Γ E_tag Ts op_bodies body n_α ops T_B T_R
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hfst Hops IHops Hbody IHbody Hec Hval Hfree.
    inversion Hval.
  - intros Γ recv op arg E_tag Delta Ts Ss n_α ops n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hnth Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg Hec Hval Hfree.
    inversion Hval.
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH Hec Hval Hfree.
    inversion Hval.
Qed.

(* The boolean [no_local_lt] is downward-closed along lifetime          *)
(* subtyping in an eval_ctx (no lt-binders to bridge local↦free).       *)
(* (Consumed by safety/Escape.v; placed here so the marker              *)
(* confinement lemma below — needed before the safety-tier marker       *)
(* invariants (WellScoped.v) — can use it.)                             *)
Lemma lt_sub_no_local_mono : forall Γ l1 l2,
  eval_ctx Γ ->
  Γ ⊢ₗ l1 <: l2 ->
  no_local_lt l2 = true ->
  no_local_lt l1 = true.
Proof.
  intros Γ l1 l2 Hec H. induction H; intros Hsup; simpl in *.
  - reflexivity.
  - discriminate Hsup.
  - rewrite (eval_ctx_no_lt _ x Hec) in H. discriminate.
  - exact Hsup.
  - apply IHlt_sub1. exact Hec. apply IHlt_sub2. exact Hec. exact Hsup.
  - rewrite (IHlt_sub1 Hec Hsup). rewrite (IHlt_sub2 Hec Hsup). reflexivity.
  - apply IHlt_sub. exact Hec.
    destruct (no_local_lt l1) eqn:E1; simpl in Hsup; [reflexivity | discriminate].
  - apply IHlt_sub. exact Hec.
    destruct (no_local_lt l2) eqn:E2;
      [reflexivity | destruct (no_local_lt l1); simpl in Hsup; discriminate].
Qed.

Theorem lt_local_not_escapes : forall Γ,
  eval_ctx Γ ->
  ~ (Γ ⊢ₗ lt_local <: lt_free).
Proof.
  intros Γ Hec H.
  pose proof (lt_sub_no_local_mono _ _ _ Hec H (eq_refl : no_local_lt lt_free = true))
    as Hcontra.
  simpl in Hcontra. discriminate.
Qed.

(* CAPABILITY CONFINEMENT FROM TYPING.  A closed value typed at an       *)
(* escapable type ([lt_of_ty_G T <: lt_free] — the no-local              *)
(* side condition) carries no runtime capability.  Immediate from the    *)
(* capture-lifetime bound: a runtime cap forces [capture_lt v = lt_local] *)
(* (capture_lt_closed), but [capture_lt v <: lt_of_ty_G T <: lt_free]     *)
(* would make [lt_local <: lt_free], impossible.  This is what makes the  *)
(* handler-elimination marker invariant (safety/WellScoped.v)             *)
(* structural.                                                            *)
Lemma value_no_local_no_rt_cap : forall Γ v T,
  eval_ctx Γ ->
  Γ ⊢ₜ v : T ->
  value v ->
  free_tm_vars 0 v = [] ->
  Γ ⊢ₗ lt_of_ty_G Γ T <: lt_free ->
  has_rt_cap v = false.
Proof.
  intros Γ v T Hec Hty Hval Hfree Hsub.
  destruct (has_rt_cap v) eqn:Hcap; [exfalso | reflexivity].
  pose proof (typing_value_capture_lt_le_type Γ v T Hty Hec Hval Hfree) as Hle.
  rewrite (capture_lt_closed Γ v Hfree) in Hle. rewrite Hcap in Hle.
  apply (lt_local_not_escapes Γ Hec). eapply LS_Trans; [exact Hle | exact Hsub].
Qed.

(* ================================================================== *)
(* Term-substitution preservation under an evaluation context.        *)
(* [typing_SubstTm] threads [SubstTm_replacement_typed] as a          *)
(* per-node invariant, re-established at each binder by weakening     *)
(* (the bind_lt case via [typing_InsLt]); the base instance is        *)
(* exactly [G |- v : A].  A per-node invariant (not one universal     *)
(* replacement premise) is needed because the universal form fails    *)
(* at bind_ctor/bind_eff, where ctx_lookup_ctor front-shadows.        *)
(* ================================================================== *)

(* [typing_SubstTm] specialised to a value substituted at index 0 in    *)
(* an eval_ctx; the base instance is exactly [G |- v : A].              *)
Lemma typing_SubstTm_eval_ctx_global : forall Γ A t B v,
  eval_ctx Γ ->
  (bind_tm A :: Γ) ⊢ₜ t : B ->
  value v ->
  Γ ⊢ₜ v : A ->
  Γ ⊢ₜ subst_tm 0 v t : B.
Proof.
  intros Γ A t B v Hec Ht Hval Hv.
  pose proof (typing_closed Γ v A Hec Hv) as Hfree.
  pose proof (typing_eval_ctx_tm_ty_closed Γ v A Hec Hv) as HtmTy.
  pose proof (typing_eval_ctx_tm_lt_closed Γ v A Hec Hv) as HtmLt.
  pose proof (typing_implies_wf Γ v A Hv) as HwfA.
  pose proof (ty_wf_eval_ctx_ty_closed Γ A Hec HwfA) as HAty.
  pose proof (ty_wf_eval_ctx_lt_closed Γ A Hec HwfA) as HAlt.
  eapply (typing_SubstTm (bind_tm A :: Γ) t B Ht v 0 Γ).
  - apply SubstTm_here; assumption.
  - exact Hfree.
  - exact HtmTy.
  - exact HtmLt.
  - intros T Hlk. simpl in Hlk. inversion Hlk; subst. exact HAty.
  - intros T Hlk. simpl in Hlk. inversion Hlk; subst. exact HAlt.
  - intros T Hlk. simpl in Hlk. inversion Hlk; subst. exact Hv.
  - apply eval_ctx_lt_closed_from. exact Hec.
  - apply eval_ctx_schemas_lt_closed_from. exact Hec.
  - unfold capture_var_lifetime. simpl.
    rewrite lt_of_ty_G_weaken_tm.
    eapply typing_value_capture_lt_le_type; eauto.
Qed.

(* The single-step eval_ctx term-substitution lemma, an immediate       *)
(* corollary of the global form above.                                  *)
Lemma typing_SubstTm_eval_ctx : forall Γ A t B v,
  eval_ctx Γ ->
  (bind_tm A :: Γ) ⊢ₜ t : B ->
  value v ->
  Γ ⊢ₜ v : A ->
  Γ ⊢ₜ subst_tm 0 v t : B.
Proof. exact typing_SubstTm_eval_ctx_global. Qed.

Lemma typing_subst_list_tm_eval_ctx_global : forall Γ vs rhos t T,
  eval_ctx Γ ->
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rhos ->
  Forall value vs ->
  List.concat (List.map (free_tm_vars 0) vs) = [] ->
  (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos) ⊢ₜ t : T ->
  Γ ⊢ₜ subst_list_tm vs t : T.
Proof.
  intros Γ vs rhos t T Hec Hargs.
  revert t T.
  induction Hargs as [|v rho vs rhos Hv Hargs IHHargs]; intros t T Hvals Hfree Ht; simpl in *.
  - exact Ht.
  - inversion Hvals as [|v0 vs0 HvVal HvalsTail Heq]; subst.
    apply List.app_eq_nil in Hfree as [HfreeV HfreeTail].
    pose proof (typing_implies_wf Γ v rho Hv) as HwfRho.
    pose proof (ty_wf_eval_ctx_ty_closed Γ rho Hec HwfRho) as HrhoTy.
    pose proof (ty_wf_eval_ctx_lt_closed Γ rho Hec HwfRho) as HrhoLt.
    pose proof (typing_eval_ctx_tm_ty_closed Γ v rho Hec Hv) as HvTy.
    pose proof (typing_eval_ctx_tm_lt_closed Γ v rho Hec Hv) as HvLt.
    set (Grest := List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos).
    assert (HfreeShift : free_tm_vars 0 (shift_tm (List.length rhos) 0 v) = []).
    { apply free_tm_vars_closed_shift_tm_any. exact HfreeV. }
    assert (Hcap : Grest ⊢ₗ
      capture_lt Grest (shift_tm (List.length rhos) 0 v) <:
      capture_var_lifetime (bind_tm rho :: Grest) 0).
    { pose proof (typing_value_capture_lt_le_type Γ v rho Hv Hec HvVal HfreeV) as HcapBase.
      subst Grest. unfold capture_var_lifetime. simpl.
      rewrite lt_of_ty_G_weaken_tm.
      rewrite (lt_of_ty_G_ty_closed_eq (List.fold_right (fun rho0 Γ0 => bind_tm rho0 :: Γ0) Γ rhos) rho HrhoTy).
      rewrite <- (lt_of_ty_G_ty_closed_eq Γ rho HrhoTy).
      rewrite (capture_lt_closed (List.fold_right (fun rho0 Γ0 => bind_tm rho0 :: Γ0) Γ rhos)
        (shift_tm (List.length rhos) 0 v) HfreeShift).
      rewrite has_rt_cap_shift_tm.
      rewrite <- (capture_lt_closed Γ v HfreeV).
      apply lt_sub_fold_bind_tm. exact HcapBase. }
    assert (Ht' : Grest ⊢ₜ subst_tm 0 (shift_tm (List.length rhos) 0 v) t : T).
    { subst Grest.
      eapply (typing_SubstTm (bind_tm rho :: List.fold_right (fun rho0 Γ0 => bind_tm rho0 :: Γ0) Γ rhos)
        t T Ht (shift_tm (List.length rhos) 0 v) 0
        (List.fold_right (fun rho0 Γ0 => bind_tm rho0 :: Γ0) Γ rhos)).
      - apply SubstTm_here.
        + apply value_shift_tm. exact HvVal.
        + apply typing_weaken_tm_shift_many. exact Hv.
      - exact HfreeShift.
      - apply tm_ty_closed_shift_tm. exact HvTy.
      - apply tm_lt_closed_shift_tm. exact HvLt.
      - intros U Hlk. simpl in Hlk. inversion Hlk; subst U; clear Hlk. exact HrhoTy.
      - intros U Hlk. simpl in Hlk. inversion Hlk; subst U; clear Hlk. exact HrhoLt.
      - intros U Hlk. simpl in Hlk. inversion Hlk; subst U; clear Hlk.
        apply typing_weaken_tm_shift_many. exact Hv.
      - apply ctx_lt_closed_from_fold_bind_tm. apply eval_ctx_lt_closed_from. exact Hec.
      - apply ctx_schemas_lt_closed_from_fold_bind_tm. apply eval_ctx_schemas_lt_closed_from. exact Hec.
      - exact Hcap. }
    rewrite (Forall2_length Hargs).
    apply (IHHargs (subst_tm 0 (shift_tm (List.length rhos) 0 v) t) T
      HvalsTail HfreeTail Ht').
Qed.
