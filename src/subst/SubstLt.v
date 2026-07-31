Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import ShiftLaws.
Require Import CtxMap.
Require Import Weakening.
Require Import SubstTactics.

(* ================================================================== *)
(* SubstLt : substitute a lifetime for an lt-binder at depth n.       *)
(*                                                                    *)
(* Also home to the lt/ty WEAKENING payloads [typing_InsTy] /         *)
(* [typing_InsLt] (their T_Match cases need this file's elim and      *)
(* multi_subst theory — see the Weakening.v header) and to the        *)
(* elim-shift commutation family they rest on.                        *)
(* ================================================================== *)

Definition subst_lt_var (n a : nat) : nat := if Nat.ltb n a then pred a else a.

Lemma subst_lt_var_S : forall n a, subst_lt_var (S n) (S a) = S (subst_lt_var n a).
Proof.
  intros n a. unfold subst_lt_var.
  replace (Nat.ltb (S n) (S a)) with (Nat.ltb n a) by reflexivity.
  destruct (Nat.ltb_spec n a) as [H|H]; simpl; [lia | reflexivity].
Qed.

Lemma subst_lt_var_neq : forall n R x,
  x <> n -> subst_lt n R (lt_var x) = lt_var (subst_lt_var n x).
Proof.
  intros n R x H. rewrite subst_lt_var_eq.
  destruct (Nat.eqb_spec x n); [contradiction|]. unfold subst_lt_var.
  destruct (Nat.ltb n x); reflexivity.
Qed.

Definition subst_lt_eff_sig (n : nat) (R : lifetime)
    (decl : nat * list (nat * type * type)) : nat * list (nat * type * type) :=
  let '(n_α, ops) := decl in
  (n_α,
   List.map (fun '(n_β, sig_ty, ret_ty) =>
       (n_β, subst_lt_in_ty n R sig_ty, subst_lt_in_ty n R ret_ty)) ops).

Definition subst_lt_ctor_sig (n : nat) (R : lifetime)
    (sig : nat * nat * list type * type) : nat * nat * list type * type :=
  let '(n_lt, n_ty, fields, result) := sig in
  (n_lt, n_ty,
   List.map (subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R)) fields,
   subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R) result).

Ltac sig_extra_unfold ::= unfold subst_lt_ctor_sig, subst_lt_eff_sig.

Lemma subst_lt_eff_sig_shift_cancel : forall R sig,
  subst_lt_eff_sig 0 R (shift_lt_eff_sig 1 0 sig) = sig.
Proof.
  intros R (n_α, ops).
  unfold subst_lt_eff_sig, shift_lt_eff_sig. simpl.
  f_equal. rewrite List.map_map.
  erewrite List.map_ext; [apply List.map_id|].
  intros [[n_β sig_ty] ret_ty]. simpl.
  rewrite !subst_lt_in_ty_shift_cancel. reflexivity.
Qed.

Lemma subst_lt_ctor_sig_shift_cancel : forall R sig,
  subst_lt_ctor_sig 0 R (shift_lt_ctor_sig 1 0 sig) = sig.
Proof.
  intros R (((n_lt, n_ty), fields), result).
  unfold subst_lt_ctor_sig, shift_lt_ctor_sig. simpl.
  assert (Hfields :
    List.map (subst_lt_in_ty (n_lt + 0) (shift_lt n_lt 0 R))
      (List.map (shift_lt_in_ty 1 (n_lt + 0)) fields) = fields).
  { induction fields as [|T fields IH]; simpl.
    - reflexivity.
    - rewrite subst_lt_in_ty_shift_cancel. f_equal. exact IH. }
  rewrite Hfields, subst_lt_in_ty_shift_cancel. reflexivity.
Qed.

Lemma shift_lt_lift_outer_one : forall k R,
  shift_lt 1 k (shift_lt k 0 R) = shift_lt k 0 (shift_lt 1 0 R).
Proof.
  intros k R. revert k. induction R as [x| | |l1 IH1 l2 IH2]; intros k; simpl.
  - destruct (Nat.leb k (x + k)) eqn:Hle.
    + f_equal. lia.
    + apply Nat.leb_gt in Hle. lia.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma shift_lt_eff_sig_subst_lt_eff_sig_comm0 : forall n R sig,
  shift_lt_eff_sig 1 0 (subst_lt_eff_sig n R sig) =
  subst_lt_eff_sig (S n) (shift_lt 1 0 R) (shift_lt_eff_sig 1 0 sig).
Proof. sig_congr shift_lt_in_ty_subst_lt_in_ty_comm0. Qed.

Lemma shift_ty_eff_sig_subst_lt_eff_sig_comm : forall n R sig,
  shift_ty_eff_sig 1 0 (subst_lt_eff_sig n R sig) =
  subst_lt_eff_sig n R (shift_ty_eff_sig 1 0 sig).
Proof. sig_congr shift_ty_subst_lt_in_ty_commute. Qed.

Lemma shift_ty_ctor_sig_subst_lt_ctor_sig_comm : forall n R sig,
  shift_ty_ctor_sig 1 0 (subst_lt_ctor_sig n R sig) =
  subst_lt_ctor_sig n R (shift_ty_ctor_sig 1 0 sig).
Proof. sig_congr shift_ty_subst_lt_in_ty_commute. Qed.

Lemma shift_lt_ctor_sig_subst_lt_ctor_sig_comm0 : forall n R sig,
  shift_lt_ctor_sig 1 0 (subst_lt_ctor_sig n R sig) =
  subst_lt_ctor_sig (S n) (shift_lt 1 0 R) (shift_lt_ctor_sig 1 0 sig).
Proof.
  intros n R (((n_lt, n_ty), fields), result).
  unfold subst_lt_ctor_sig, shift_lt_ctor_sig. simpl.
  assert (Hfields :
    List.map (shift_lt_in_ty 1 (n_lt + 0))
      (List.map (subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R)) fields) =
    List.map (subst_lt_in_ty (n_lt + S n) (shift_lt n_lt 0 (shift_lt 1 0 R)))
      (List.map (shift_lt_in_ty 1 (n_lt + 0)) fields)).
  { induction fields as [|T fields IH]; simpl.
    - reflexivity.
    - rewrite shift_lt_in_ty_subst_lt_in_ty_comm by lia.
      replace (n_lt + 0) with n_lt by lia.
      rewrite shift_lt_lift_outer_one.
      replace (S (n_lt + n)) with (n_lt + S n) by lia.
      replace (n_lt + 0) with n_lt in IH by lia.
      f_equal. exact IH. }
  rewrite Hfields.
  rewrite shift_lt_in_ty_subst_lt_in_ty_comm by lia.
  replace (n_lt + 0) with n_lt by lia.
  rewrite shift_lt_lift_outer_one.
  replace (S (n_lt + n)) with (n_lt + S n) by lia.
  reflexivity.
Qed.

Inductive SubstLt : lifetime -> nat -> ctx -> ctx -> Prop :=
| SubstLt_here : forall Gamma Delta R,
    Gamma ⊢ₗ R <: Delta ->
    SubstLt R 0 (bind_lt Delta :: Gamma) Gamma
| SubstLt_lt : forall R n G G' Delta,
    SubstLt R n G G' ->
    SubstLt (shift_lt 1 0 R) (S n)
            (bind_lt Delta :: G)
            (bind_lt (subst_lt n R Delta) :: G')
| SubstLt_ty : forall R n G G' B,
    SubstLt R n G G' ->
  SubstLt R n (bind_ty B :: G) (bind_ty (subst_lt_in_ty n R B) :: G')
| SubstLt_tm : forall R n G G' A,
  SubstLt R n G G' ->
  SubstLt R n (bind_tm A :: G) (bind_tm (subst_lt_in_ty n R A) :: G').

Lemma SubstLt_length : forall R n G G', SubstLt R n G G' -> length G = S (length G').
Proof. intros R n G G' H. induction H; simpl; lia. Qed.


Lemma SubstLt_lookup_ty : forall R n G G', SubstLt R n G G' ->
  forall a, ctx_lookup_ty G' a = option_map (subst_lt_in_ty n R) (ctx_lookup_ty G a).
Proof.
  intros R n G G' H. induction H; intro a.
  - simpl ctx_lookup_ty.
    destruct (ctx_lookup_ty Gamma a) as [X|]; simpl;
      [rewrite subst_lt_in_ty_shift_cancel; reflexivity | reflexivity].
  - specialize (IHSubstLt a). simpl ctx_lookup_ty. rewrite IHSubstLt.
    destruct (ctx_lookup_ty G a) as [X|]; simpl;
      [rewrite shift_lt_in_ty_subst_lt_in_ty_comm0; reflexivity | reflexivity].
  - destruct a as [|a'].
    + simpl ctx_lookup_ty. rewrite shift_ty_subst_lt_in_ty_commute. reflexivity.
    + specialize (IHSubstLt a'). simpl ctx_lookup_ty. rewrite IHSubstLt.
      destruct (ctx_lookup_ty G a') as [X|]; simpl;
        [rewrite shift_ty_subst_lt_in_ty_commute; reflexivity | reflexivity].
  - simpl ctx_lookup_ty. apply IHSubstLt.
Qed.

Lemma SubstLt_lookup_lt : forall R n G G', SubstLt R n G G' ->
  forall a, a <> n ->
  ctx_lookup_lt G' (subst_lt_var n a) = option_map (subst_lt n R) (ctx_lookup_lt G a).
Proof.
  intros R n G G' H. induction H; intros a Hne.
  - destruct a as [|a']; [contradiction|].
    unfold subst_lt_var. simpl Nat.ltb. simpl pred. simpl ctx_lookup_lt.
    destruct (ctx_lookup_lt Gamma a') as [X|]; simpl;
      [rewrite subst_lt_shift_cancel; reflexivity | reflexivity].
  - destruct a as [|a'].
    + unfold subst_lt_var. simpl Nat.ltb. simpl ctx_lookup_lt.
      rewrite shift_lt_subst_lt_comm0. reflexivity.
    + assert (a' <> n) by lia.
      rewrite subst_lt_var_S. simpl ctx_lookup_lt. rewrite (IHSubstLt a' H0).
      destruct (ctx_lookup_lt G a') as [X|]; simpl;
        [rewrite shift_lt_subst_lt_comm0; reflexivity | reflexivity].
  - specialize (IHSubstLt a Hne). simpl ctx_lookup_lt. apply IHSubstLt.
  - specialize (IHSubstLt a Hne). simpl ctx_lookup_lt. apply IHSubstLt.
Qed.

Lemma SubstLt_lookup_tm : forall R n G G', SubstLt R n G G' ->
  forall x, ctx_lookup_tm G' x = option_map (subst_lt_in_ty n R) (ctx_lookup_tm G x).
Proof.
  intros R n G G' H. induction H; intro x.
  - simpl ctx_lookup_tm.
    destruct (ctx_lookup_tm Gamma x) as [X|]; simpl;
      [rewrite subst_lt_in_ty_shift_cancel; reflexivity | reflexivity].
  - simpl ctx_lookup_tm. rewrite IHSubstLt.
    destruct (ctx_lookup_tm G x) as [X|]; simpl;
      [rewrite shift_lt_in_ty_subst_lt_in_ty_comm0; reflexivity | reflexivity].
  - simpl ctx_lookup_tm. rewrite IHSubstLt.
    destruct (ctx_lookup_tm G x) as [X|]; simpl;
      [rewrite shift_ty_subst_lt_in_ty_commute; reflexivity | reflexivity].
  - destruct x as [|x'].
    + reflexivity.
    + simpl ctx_lookup_tm. apply IHSubstLt.
Qed.

Lemma SubstLt_lookup_eff : forall R n G G', SubstLt R n G G' ->
  forall E, ctx_lookup_eff G' E = option_map (subst_lt_eff_sig n R) (ctx_lookup_eff G E).
Proof.
  intros R n G G' H.
  induction H as [Gamma Delta R Hsub
                 |R n G G' Delta HS IH
                 |R n G G' B HS IH
                 |R n G G' A HS IH]; intro E; simpl ctx_lookup_eff.
  - destruct (ctx_lookup_eff Gamma E) as [sig|] eqn:Heq; simpl;
      [rewrite subst_lt_eff_sig_shift_cancel |]; reflexivity.
  - rewrite IH. destruct (ctx_lookup_eff G E) as [sig|] eqn:Heq; simpl;
      [rewrite shift_lt_eff_sig_subst_lt_eff_sig_comm0 |]; reflexivity.
  - rewrite IH. destruct (ctx_lookup_eff G E) as [sig|] eqn:Heq; simpl;
      [rewrite shift_ty_eff_sig_subst_lt_eff_sig_comm |]; reflexivity.
  - apply IH.
Qed.

Lemma SubstLt_lookup_ctor : forall R n G G', SubstLt R n G G' ->
  forall K, ctx_lookup_ctor G' K = option_map (subst_lt_ctor_sig n R) (ctx_lookup_ctor G K).
Proof.
  intros R n G G' H.
  induction H as [Gamma Delta R Hsub
                 |R n G G' Delta HS IH
                 |R n G G' B HS IH
                 |R n G G' A HS IH]; intro K; simpl ctx_lookup_ctor.
  - destruct (ctx_lookup_ctor Gamma K) as [sig|] eqn:Heq; simpl;
      [rewrite subst_lt_ctor_sig_shift_cancel |]; reflexivity.
  - rewrite IH. destruct (ctx_lookup_ctor G K) as [sig|] eqn:Heq; simpl;
      [rewrite shift_lt_ctor_sig_subst_lt_ctor_sig_comm0 |]; reflexivity.
  - rewrite IH. destruct (ctx_lookup_ctor G K) as [sig|] eqn:Heq; simpl;
      [rewrite shift_ty_ctor_sig_subst_lt_ctor_sig_comm |]; reflexivity.
  - apply IH.
Qed.

Lemma SubstLt_replacement_wf : forall R n G G',
  SubstLt R n G G' -> lt_wf G' R.
Proof.
  intros R n G G' H. induction H.
  - destruct (lt_sub_wf _ _ _ H) as [Hwf _]. exact Hwf.
  - eapply lt_wf_InsLt; [exact IHSubstLt|]. apply InsLt_here.
  - eapply lt_wf_InsTy; [exact IHSubstLt|]. apply InsTy_here.
  - eapply lt_wf_InsTm; [exact IHSubstLt|]. apply InsTm_here.
Qed.

Lemma SubstLt_target : forall R n G G', SubstLt R n G G' ->
  exists Delta, ctx_lookup_lt G n = Some Delta /\ G' ⊢ₗ R <: subst_lt n R Delta.
Proof.
  intros R n G G' H. induction H.
  - exists (shift_lt 1 0 Delta). split.
    + reflexivity.
    + rewrite subst_lt_shift_cancel. exact H.
  - destruct IHSubstLt as [Delta0 [Hlk Hsub]].
    exists (shift_lt 1 0 Delta0). split.
    + simpl ctx_lookup_lt. rewrite Hlk. reflexivity.
    + rewrite <- shift_lt_subst_lt_comm0.
      apply (lt_sub_InsLt G' R (subst_lt n R Delta0) Hsub 0
               (bind_lt (subst_lt n R Delta) :: G') (InsLt_here _ _)).
  - destruct IHSubstLt as [Delta0 [Hlk Hsub]].
    exists Delta0. split.
    + simpl ctx_lookup_lt. exact Hlk.
    + apply (lt_sub_InsTy G' R (subst_lt n R Delta0) Hsub 0
               (bind_ty (subst_lt_in_ty n R B) :: G') (InsTy_here _ _)).
  - destruct IHSubstLt as [Delta0 [Hlk Hsub]].
    exists Delta0. split.
    + simpl ctx_lookup_lt. exact Hlk.
    + apply (lt_sub_InsTm G' R (subst_lt n R Delta0) Hsub
               (bind_tm (subst_lt_in_ty n R A) :: G') (InsTm_here _ _)).
Qed.

(* SubstLt as a context map: lifetimes get [subst_lt n R], types get  *)
(* [subst_lt_in_ty n R]; crossing an lt binder shifts the payload and *)
(* bumps the depth, crossing a ty binder leaves both untouched.       *)
Lemma CtxMapSpec_SubstLt :
  CtxMapSpec (lifetime * nat)
    (fun p => subst_lt_in_ty (snd p) (fst p))
    (fun p => subst_lt (snd p) (fst p))
    (fun p => (shift_lt 1 0 (fst p), S (snd p)))
    (fun p => p)
    (fun p G G' => SubstLt (fst p) (snd p) G G').
Proof.
  constructor.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; apply subst_lt_in_ty_ctor_eq.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros p G G' D HS. apply SubstLt_lt. exact HS.
  - intros p G G' B HS. apply SubstLt_ty. exact HS.
  - intros [R n] G G' x Δ HS Hlk. simpl fst in *. simpl snd in *.
    destruct (Nat.eq_dec x n) as [Hx|Hx].
    + subst x. rewrite subst_lt_var_eq, Nat.eqb_refl.
      eapply SubstLt_replacement_wf; eauto.
    + rewrite (subst_lt_var_neq n R x Hx). econstructor.
      rewrite (SubstLt_lookup_lt R n G G' HS x Hx). rewrite Hlk. reflexivity.
  - intros [R n] G G' x Δ HS Hlk Hwf. simpl fst in *. simpl snd in *.
    destruct (Nat.eq_dec x n) as [Hx|Hx].
    + subst x. rewrite subst_lt_var_eq, Nat.eqb_refl.
      destruct (SubstLt_target R n G G' HS) as [Δt [Hlkt Hsubt]].
      rewrite Hlk in Hlkt. inversion Hlkt; subst Δt. exact Hsubt.
    + rewrite (subst_lt_var_neq n R x Hx). apply LS_Var.
      * rewrite (SubstLt_lookup_lt R n G G' HS x Hx). rewrite Hlk. reflexivity.
      * exact Hwf.
  - intros [R n] G G' α B HS Hlk _ HwfB'. simpl fst in *. simpl snd in *.
    rewrite subst_lt_in_ty_var_eq. econstructor.
    + rewrite (SubstLt_lookup_ty R n G G' HS α). rewrite Hlk. reflexivity.
    + exact HwfB'.
  - intros [R n] G G' α B HS Hlk _ HwfB'. simpl fst in *. simpl snd in *.
    rewrite subst_lt_in_ty_var_eq. apply SA_VarCtx.
    + rewrite (SubstLt_lookup_ty R n G G' HS α). rewrite Hlk. reflexivity.
    + exact HwfB'.
Qed.

Lemma lt_wf_SubstLt : forall G l,
  lt_wf G l -> forall R n G', SubstLt R n G G' -> lt_wf G' (subst_lt n R l).
Proof.
  intros G l Hwf R n G' HS.
  exact (lt_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_SubstLt G l Hwf (R, n) G' HS).
Qed.
#[export] Hint Resolve lt_wf_SubstLt : ctxmap.

Lemma lifetimes_wf_SubstLt : forall G lts,
  lifetimes_wf G lts -> forall R n G', SubstLt R n G G' ->
    lifetimes_wf G' (List.map (subst_lt n R) lts).
Proof.
  intros G lts Hwf R n G' HS.
  exact (lifetimes_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_SubstLt
           G lts Hwf (R, n) G' HS).
Qed.
#[export] Hint Resolve lifetimes_wf_SubstLt : ctxmap.

Lemma ty_wf_SubstLt : forall G T,
  ty_wf G T -> forall R n G', SubstLt R n G G' -> ty_wf G' (subst_lt_in_ty n R T).
Proof.
  intros G T Hwf R n G' HS.
  exact (ty_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_SubstLt G T Hwf (R, n) G' HS).
Qed.

Lemma types_wf_SubstLt : forall G Ts,
  types_wf G Ts -> forall R n G', SubstLt R n G G' ->
    types_wf G' (List.map (subst_lt_in_ty n R) Ts).
Proof.
  intros G Ts Hwf R n G' HS.
  exact (types_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_SubstLt G Ts Hwf (R, n) G' HS).
Qed.
#[export] Hint Resolve types_wf_SubstLt : ctxmap.
#[export] Hint Resolve ty_wf_SubstLt : ctxmap.

Lemma lt_sub_SubstLt : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall R n G', SubstLt R n G G' ->
  G' ⊢ₗ subst_lt n R l1 <: subst_lt n R l2.
Proof.
  intros G l1 l2 H R n G' HS.
  exact (lt_sub_ctx_map _ _ _ _ _ _ CtxMapSpec_SubstLt G l1 l2 H (R, n) G' HS).
Qed.
#[export] Hint Resolve lt_sub_SubstLt : ctxmap.

Lemma lt_of_ty_ctx_SubstLt : forall R n G G', SubstLt R n G G' ->
  forall f T, lt_of_ty_ctx f G' (subst_lt_in_ty n R T)
              = subst_lt n R (lt_of_ty_ctx f G T).
Proof.
  intros R n G G' HS f. induction f as [|f' IHf]; intro T.
  - induction T using type_list_ind with
      (Q := fun Ts => lt_of_ty_ctx_list 0 G' (List.map (subst_lt_in_ty n R) Ts)
                      = subst_lt n R (lt_of_ty_ctx_list 0 G Ts)).
    + rewrite subst_lt_in_ty_var_eq. rewrite !(lt_of_ty_ctx_var 0). reflexivity.
    + rewrite subst_lt_in_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. reflexivity.
    + rewrite subst_lt_in_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor.
      simpl subst_lt. f_equal. exact IHT.
    + rewrite subst_lt_in_ty_ltall_eq. rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + rewrite subst_lt_in_ty_tyall_eq. rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. simpl subst_lt.
      rewrite IHT, IHT0. reflexivity.
  - induction T using type_list_ind with
      (Q := fun Ts => lt_of_ty_ctx_list (S f') G' (List.map (subst_lt_in_ty n R) Ts)
                      = subst_lt n R (lt_of_ty_ctx_list (S f') G Ts)).
    + rewrite subst_lt_in_ty_var_eq.
      rewrite (lt_of_ty_ctx_var (S f') G' n0), (lt_of_ty_ctx_var (S f') G n0).
      rewrite (SubstLt_lookup_ty R n G G' HS n0).
      destruct (ctx_lookup_ty G n0) as [B|] eqn:E; simpl.
      * apply IHf.
      * reflexivity.
    + rewrite subst_lt_in_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. reflexivity.
    + rewrite subst_lt_in_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor.
      simpl subst_lt. f_equal. exact IHT.
    + rewrite subst_lt_in_ty_ltall_eq. rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + rewrite subst_lt_in_ty_tyall_eq. rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. simpl subst_lt.
      rewrite IHT, IHT0. reflexivity.
Qed.

Lemma lt_of_ty_G_SubstLt : forall R n G G', SubstLt R n G G' ->
  forall T, lt_of_ty_G G' (subst_lt_in_ty n R T) = subst_lt n R (lt_of_ty_G G T).
Proof.
  intros R n G G' HS T. unfold lt_of_ty_G.
  pose proof (SubstLt_length R n G G' HS) as HL.
  rewrite (lt_of_ty_ctx_fuel_irrel (length G') (length G)
             (subst_lt_in_ty n R T) G' 0 (VB_0 _) ltac:(lia) ltac:(lia)).
  apply (lt_of_ty_ctx_SubstLt R n G G' HS (length G) T).
Qed.

Lemma capture_lt_SubstLt : forall R n G G', SubstLt R n G G' ->
  forall body, capture_lt G' (subst_lt_in_tm n R body) = subst_lt n R (capture_lt G body).
Proof.
  intros R n G G' HS body. unfold capture_lt.
  rewrite has_rt_cap_subst_lt_in_tm.
  destruct (has_rt_cap body) eqn:Hcap; [reflexivity|].
  rewrite free_tm_vars_subst_lt_in_tm.
  induction (free_tm_vars 1 body) as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite (SubstLt_lookup_tm R n G G' HS x).
    destruct (ctx_lookup_tm G x) as [T|] eqn:Hlk; simpl.
    + rewrite (lt_of_ty_G_SubstLt R n G G' HS T). rewrite IH. reflexivity.
    + rewrite IH. reflexivity.
Qed.

(* SA_Any side-condition transport for the generic sub payload:      *)
(* [lt_of_ty_G] commutes with [subst_lt_in_ty n R] as an equality.   *)
Lemma sub_any_SubstLt : forall R n G G' T Δ,
  SubstLt R n G G' -> ty_wf G T ->
  G' ⊢ₗ subst_lt n R (lt_of_ty_G G T) <: subst_lt n R Δ ->
  G' ⊢ₗ lt_of_ty_G G' (subst_lt_in_ty n R T) <: subst_lt n R Δ.
Proof.
  intros R n G G' T Δ HS _ Hle.
  rewrite (lt_of_ty_G_SubstLt R n G G' HS T). exact Hle.
Qed.

Lemma sub_SubstLt : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall R n G', SubstLt R n G G' ->
  G' ⊢ subst_lt_in_ty n R T1 <:: subst_lt_in_ty n R T2.
Proof.
  intros G T1 T2 H R n G' HS.
  exact (sub_ctx_map _ _ _ _ _ _ CtxMapSpec_SubstLt
           (fun p => sub_any_SubstLt (fst p) (snd p))
           G T1 T2 H (R, n) G' HS).
Qed.
#[export] Hint Resolve sub_SubstLt : ctxmap.

Lemma subst_lt_in_ty_any_at_free : forall n R,
  subst_lt_in_ty n R any_at_free = any_at_free.
Proof. reflexivity. Qed.

Lemma SubstLt_push_ty_vars_any_at_free : forall m R n G G',
  SubstLt R n G G' ->
  SubstLt R n (push_ty_vars m any_at_free G) (push_ty_vars m any_at_free G').
Proof.
  induction m as [|m IH]; intros R n G G' HS; simpl.
  - exact HS.
  - apply IH. rewrite <- (subst_lt_in_ty_any_at_free n R).
    apply SubstLt_ty. exact HS.
Qed.


(* Map form: target is [fold_right bind_tm G' (map (subst n R) rhos)], *)
(* matching the reconstructed yes-branch context of the general        *)
(* [typing_SubstLt] T_Match case.                                       *)
Lemma SubstLt_fold_bind_tm_map : forall rhos R n G G',
  SubstLt R n G G' ->
  SubstLt R n
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G'
       (List.map (subst_lt_in_ty n R) rhos)).
Proof.
  induction rhos as [|rho rhos IH]; intros R n G G' HS; simpl.
  - exact HS.
  - apply SubstLt_tm. apply IH. exact HS.
Qed.

Lemma subst_lt_closed_lifetime : forall l c R,
  lt_lt_closed c l -> subst_lt c R l = l.
Proof.
  induction l as [x| | |l1 IH1 l2 IH2]; intros c R Hclosed; simpl in *.
  - destruct (Nat.eqb_spec x c); [lia|].
    destruct (Nat.ltb_spec c x); [lia|reflexivity].
  - reflexivity.
  - reflexivity.
  - destruct Hclosed as [H1 H2]. rewrite (IH1 c R H1), (IH2 c R H2). reflexivity.
Qed.

Lemma subst_lt_in_type_closed : forall T c R,
  ty_lt_closed c T -> subst_lt_in_ty c R T = T.
Proof.
  apply (type_list_ind
    (fun T => forall c R, ty_lt_closed c T -> subst_lt_in_ty c R T = T)
    (fun Ts => forall c R, tys_lt_closed c Ts ->
      List.map (subst_lt_in_ty c R) Ts = Ts)).
  - reflexivity.
  - intros A l B IHA IHB c R Hclosed. rewrite subst_lt_in_ty_fun_eq. simpl in Hclosed.
    destruct Hclosed as [HA [Hl HB]]. rewrite IHA by exact HA.
    rewrite subst_lt_closed_lifetime by exact Hl.
    rewrite IHB by exact HB. reflexivity.
  - intros K l Ts IHTs c R Hclosed. rewrite subst_lt_in_ty_ctor_eq.
    simpl in Hclosed. destruct Hclosed as [Hl HTs].
    rewrite subst_lt_closed_lifetime by exact Hl. rewrite IHTs by exact HTs. reflexivity.
  - intros A IHA c R Hclosed. rewrite subst_lt_in_ty_ltall_eq. simpl in *.
    rewrite IHA by exact Hclosed. reflexivity.
  - intros B A IHB IHA c R Hclosed. rewrite subst_lt_in_ty_tyall_eq. simpl in Hclosed. destruct Hclosed as [HB HA].
    rewrite IHB by exact HB. rewrite IHA by exact HA. reflexivity.
  - reflexivity.
  - intros A Ts IHA IHTs c R Hclosed. simpl in Hclosed. destruct Hclosed as [HA HTs].
    cbn [List.map]. rewrite IHA by exact HA. rewrite IHTs by exact HTs. reflexivity.
Qed.


Lemma SubstLt_bind_lt_closed : forall Delta R n G G',
  SubstLt R n G G' ->
  lt_lt_closed n Delta ->
  SubstLt (shift_lt 1 0 R) (S n) (bind_lt Delta :: G) (bind_lt Delta :: G').
Proof.
  intros Delta R n G G' HSub Hclosed.
  assert (Hctx : bind_lt (subst_lt n R Delta) :: G' = bind_lt Delta :: G').
  { rewrite subst_lt_closed_lifetime by exact Hclosed. reflexivity. }
  rewrite <- Hctx. apply SubstLt_lt. exact HSub.
Qed.


(* [push_match_bound] is STABLE under lt-substitution, with NO closedness on  *)
(* Delta (UNLIKE [SubstLt_push_lt_vars_closed]).  The per-level bound   *)
(* [shift_lt j 0 Delta] is substituted to [shift_lt j 0 (subst_lt n R   *)
(* Delta)] uniformly, because [SubstLt_lt]'s per-level subst commutes   *)
(* with the level shift via [shift_lt_subst_lt_comm_many0].  This is    *)
(* the lemma that makes the general [typing_SubstLt] go through.        *)
Lemma SubstLt_push_match_bound : forall k Delta R n G G',
  SubstLt R n G G' ->
  SubstLt (shift_lt k 0 R) (k + n)
    (push_match_bound k Delta G) (push_match_bound k (subst_lt n R Delta) G').
Proof.
  induction k as [|k IH]; intros Delta R n G G' HSub; simpl.
  - rewrite shift_lt_zero. replace (0 + n) with n by lia. exact HSub.
  - replace (shift_lt (S k) 0 R) with (shift_lt 1 0 (shift_lt k 0 R))
      by (rewrite shift_lt_fuse; replace (k + 1) with (S k) by lia; reflexivity).
    replace (S k + n) with (S (k + n)) by lia.
    replace (shift_lt k 0 (subst_lt n R Delta))
      with (subst_lt (k + n) (shift_lt k 0 R) (shift_lt k 0 Delta))
      by (symmetry; apply shift_lt_subst_lt_comm_many0).
    apply SubstLt_lt. apply IH. exact HSub.
Qed.


Lemma typings_SubstLt : forall Γ vs rhos,
  Forall2 (fun v rho => forall R n G', SubstLt R n Γ G' ->
    G' ⊢ₜ subst_lt_in_tm n R v : subst_lt_in_ty n R rho) vs rhos ->
  forall R n G', SubstLt R n Γ G' ->
  typings G' (List.map (subst_lt_in_tm n R) vs)
             (List.map (subst_lt_in_ty n R) rhos).
Proof.
  intros Γ vs rhos H. induction H; intros R n G' HS; simpl.
  - constructor.
  - constructor.
    + apply H. exact HS.
    + apply IHForall2. exact HS.
Qed.


(* ================================================================== *)
(* subst_ty rewrite equations                                         *)
(* ================================================================== *)


Lemma subst_ty_var_eq : forall v Sb n,
  subst_ty v Sb (type_var n)
  = if Nat.eqb n v then Sb else if Nat.ltb v n then type_var (pred n) else type_var n.
Proof. reflexivity. Qed.

Lemma subst_ty_fun_eq : forall v Sb A l B,
  subst_ty v Sb (type_fun A l B) = type_fun (subst_ty v Sb A) l (subst_ty v Sb B).
Proof. reflexivity. Qed.

Lemma subst_ty_ctor_eq : forall v Sb K l Ts,
  subst_ty v Sb (type_ctor K l Ts) = type_ctor K l (List.map (subst_ty v Sb) Ts).
Proof. reflexivity. Qed.

Lemma subst_ty_ltall_eq : forall v Sb A,
  subst_ty v Sb (type_lt_all A) = type_lt_all (subst_ty v (shift_lt_in_ty 1 0 Sb) A).
Proof. reflexivity. Qed.

Lemma subst_ty_tyall_eq : forall v Sb B A,
  subst_ty v Sb (type_ty_all B A)
  = type_ty_all (subst_ty v Sb B) (subst_ty (S v) (shift_ty 1 0 Sb) A).
Proof. reflexivity. Qed.


(* ================================================================== *)
(* subst_ty cancel + commutation with shifts                          *)
(* ================================================================== *)

Lemma subst_ty_shift_cancel : forall T c Sb,
  subst_ty c Sb (shift_ty 1 c T) = T.
Proof.
  intros T. apply (type_list_ind
    (fun T => forall c Sb, subst_ty c Sb (shift_ty 1 c T) = T)
    (fun Ts => forall c Sb, List.map (subst_ty c Sb) (List.map (shift_ty 1 c) Ts) = Ts)).
  - intros n c Sb. rewrite shift_ty_var_eq, subst_ty_var_eq.
    destruct (Nat.leb c n) eqn:E.
    + apply Nat.leb_le in E.
      destruct (Nat.eqb_spec (n+1) c); [lia|].
      destruct (Nat.ltb_spec c (n+1)); [f_equal; lia | lia].
    + apply Nat.leb_gt in E.
      destruct (Nat.eqb_spec n c); [lia|].
      destruct (Nat.ltb_spec c n); [lia | reflexivity].
  - intros A l B HA HB c Sb. rewrite shift_ty_fun_eq, subst_ty_fun_eq. rewrite HA, HB. reflexivity.
  - intros K l Ts HTs c Sb. rewrite shift_ty_ctor_eq, subst_ty_ctor_eq. f_equal. apply HTs.
  - intros A HA c Sb. rewrite shift_ty_ltall_eq, subst_ty_ltall_eq. rewrite HA. reflexivity.
  - intros B A HB HA c Sb. rewrite shift_ty_tyall_eq, subst_ty_tyall_eq. rewrite HB, HA. reflexivity.
  - intros c Sb. reflexivity.
  - intros A Ts HA HTs c Sb. cbn [List.map]. rewrite HA. f_equal. apply HTs.
Qed.

Lemma shift_ty_subst_ty_comm : forall T c n Sb,
  c <= n ->
  shift_ty 1 c (subst_ty n Sb T) = subst_ty (S n) (shift_ty 1 c Sb) (shift_ty 1 c T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall c n Sb, c <= n ->
       shift_ty 1 c (subst_ty n Sb T) = subst_ty (S n) (shift_ty 1 c Sb) (shift_ty 1 c T))
    (fun Ts => forall c n Sb, c <= n ->
       List.map (shift_ty 1 c) (List.map (subst_ty n Sb) Ts)
       = List.map (subst_ty (S n) (shift_ty 1 c Sb)) (List.map (shift_ty 1 c) Ts))).
  - intros m c n Sb Hle. rewrite subst_ty_var_eq.
    destruct (Nat.eqb_spec m n).
    + subst m. rewrite shift_ty_var_eq.
      rewrite (proj2 (Nat.leb_le c n) Hle). rewrite subst_ty_var_eq.
      rewrite Nat.add_1_r. rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.ltb_spec n m).
      * rewrite shift_ty_var_eq.
        assert (c <= pred m) by lia. rewrite (proj2 (Nat.leb_le c (pred m)) H0).
        rewrite shift_ty_var_eq. rewrite (proj2 (Nat.leb_le c m) ltac:(lia)).
        rewrite subst_ty_var_eq.
        destruct (Nat.eqb_spec (m+1) (S n)); [lia|].
        destruct (Nat.ltb_spec (S n) (m+1)); [|lia]. f_equal. lia.
      * rewrite !shift_ty_var_eq.
        destruct (Nat.leb c m) eqn:E.
        -- apply Nat.leb_le in E. rewrite subst_ty_var_eq.
           destruct (Nat.eqb_spec (m+1) (S n)); [lia|].
           destruct (Nat.ltb_spec (S n) (m+1)); [lia|]. reflexivity.
        -- apply Nat.leb_gt in E. rewrite subst_ty_var_eq.
           destruct (Nat.eqb_spec m (S n)); [lia|].
           destruct (Nat.ltb_spec (S n) m); [lia|]. reflexivity.
  - intros A l B HA HB c n Sb Hle.
    rewrite subst_ty_fun_eq, shift_ty_fun_eq, shift_ty_fun_eq, subst_ty_fun_eq.
    rewrite HA by lia. rewrite HB by lia. reflexivity.
  - intros K l Ts HTs c n Sb Hle.
    rewrite subst_ty_ctor_eq, shift_ty_ctor_eq, shift_ty_ctor_eq, subst_ty_ctor_eq.
    f_equal. apply HTs. lia.
  - intros A HA c n Sb Hle.
    rewrite subst_ty_ltall_eq, shift_ty_ltall_eq, shift_ty_ltall_eq, subst_ty_ltall_eq.
    f_equal. rewrite HA by lia. f_equal.
    apply shift_ty_shift_lt_in_ty_commute.
  - intros B A HB HA c n Sb Hle.
    rewrite subst_ty_tyall_eq, shift_ty_tyall_eq, shift_ty_tyall_eq, subst_ty_tyall_eq.
    rewrite HB by lia. f_equal.
    rewrite HA by lia. f_equal.
    symmetry. apply shift_ty_swap_0.
  - intros c n Sb Hle. reflexivity.
  - intros A Ts HA HTs c n Sb Hle.
    cbn [List.map]. rewrite HA by lia. f_equal. apply HTs. lia.
Qed.

Lemma shift_ty_subst_ty_comm0 : forall T n Sb,
  shift_ty 1 0 (subst_ty n Sb T) = subst_ty (S n) (shift_ty 1 0 Sb) (shift_ty 1 0 T).
Proof. intros. apply shift_ty_subst_ty_comm. lia. Qed.

Lemma shift_ty_subst_ty_comm_ge : forall T c n Sb,
  n <= c ->
  shift_ty 1 c (subst_ty n Sb T) =
  subst_ty n (shift_ty 1 c Sb) (shift_ty 1 (S c) T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall c n Sb, n <= c ->
       shift_ty 1 c (subst_ty n Sb T) =
       subst_ty n (shift_ty 1 c Sb) (shift_ty 1 (S c) T))
    (fun Ts => forall c n Sb, n <= c ->
       List.map (shift_ty 1 c) (List.map (subst_ty n Sb) Ts) =
       List.map (subst_ty n (shift_ty 1 c Sb)) (List.map (shift_ty 1 (S c)) Ts))).
  - intros m c n Sb Hle. rewrite subst_ty_var_eq.
    destruct (Nat.eqb_spec m n) as [Heq|Hneq].
    + subst m. rewrite !shift_ty_var_eq.
      rewrite (proj2 (Nat.leb_gt (S c) n)) by lia.
      rewrite subst_ty_var_eq, Nat.eqb_refl. reflexivity.
    + destruct (Nat.ltb_spec n m) as [Hlt|Hge].
      * destruct (Nat.leb (S c) m) eqn:Em.
        -- apply Nat.leb_le in Em. rewrite !shift_ty_var_eq.
           rewrite (proj2 (Nat.leb_le c (pred m))) by lia.
           rewrite (proj2 (Nat.leb_le (S c) m)) by lia.
           rewrite subst_ty_var_eq.
           destruct (Nat.eqb_spec (m + 1) n); [lia|].
           destruct (Nat.ltb_spec n (m + 1)); [f_equal; lia|lia].
        -- apply Nat.leb_gt in Em. rewrite !shift_ty_var_eq.
           rewrite (proj2 (Nat.leb_gt c (pred m))) by lia.
           rewrite (proj2 (Nat.leb_gt (S c) m)) by lia.
           rewrite subst_ty_var_eq.
           destruct (Nat.eqb_spec m n); [lia|].
           destruct (Nat.ltb_spec n m); [reflexivity|lia].
      * rewrite !shift_ty_var_eq.
        rewrite (proj2 (Nat.leb_gt c m)) by lia.
        rewrite (proj2 (Nat.leb_gt (S c) m)) by lia.
        rewrite subst_ty_var_eq.
        destruct (Nat.eqb_spec m n); [lia|].
        destruct (Nat.ltb_spec n m); [lia|reflexivity].
  - intros A l B HA HB c n Sb Hle.
    rewrite subst_ty_fun_eq, shift_ty_fun_eq, shift_ty_fun_eq, subst_ty_fun_eq.
    rewrite HA by lia. rewrite HB by lia. reflexivity.
  - intros K l Ts HTs c n Sb Hle.
    rewrite subst_ty_ctor_eq, shift_ty_ctor_eq, shift_ty_ctor_eq, subst_ty_ctor_eq.
    f_equal. apply HTs. lia.
  - intros A HA c n Sb Hle.
    rewrite subst_ty_ltall_eq, shift_ty_ltall_eq, shift_ty_ltall_eq, subst_ty_ltall_eq.
    f_equal. rewrite HA by lia. f_equal.
    apply shift_ty_shift_lt_in_ty_commute.
  - intros B A HB HA c n Sb Hle.
    rewrite subst_ty_tyall_eq, shift_ty_tyall_eq, shift_ty_tyall_eq, subst_ty_tyall_eq.
    rewrite HB by lia. f_equal.
    rewrite HA by lia. f_equal.
    symmetry. apply shift_ty_swap_0.
  - intros c n Sb Hle. reflexivity.
  - intros A Ts HA HTs c n Sb Hle.
    cbn [List.map]. rewrite HA by lia. f_equal. apply HTs. lia.
Qed.

Lemma shift_ty_subst_ty_comm_ge0 : forall T c Sb,
  shift_ty 1 c (subst_ty 0 Sb T) =
  subst_ty 0 (shift_ty 1 c Sb) (shift_ty 1 (S c) T).
Proof. intros. apply shift_ty_subst_ty_comm_ge. lia. Qed.

Lemma inst_ty_vars_shift_ty : forall n Ts T c,
  List.length Ts = n ->
  inst_ty_vars n (List.map (shift_ty 1 c) Ts) (shift_ty 1 (n + c) T) =
  shift_ty 1 c (inst_ty_vars n Ts T).
Proof.
  induction n as [|n IH]; intros Ts T c Hlen.
  - destruct Ts as [|U rest]; [|simpl in Hlen; discriminate].
    simpl. replace (0 + c) with c by lia. reflexivity.
  - destruct Ts as [|U rest]; [simpl in Hlen; discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    simpl. rewrite shift_ty_lift_shift.
    replace (S n + c) with (S (n + c)) by lia.
    rewrite <- shift_ty_subst_ty_comm_ge0.
    rewrite IH by exact Hlen. reflexivity.
Qed.

Lemma multi_subst_lt_in_ty_shift_ty : forall T cutoff lts c,
  multi_subst_lt_in_ty cutoff lts (shift_ty 1 c T) =
  shift_ty 1 c (multi_subst_lt_in_ty cutoff lts T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall cutoff lts c,
      multi_subst_lt_in_ty cutoff lts (shift_ty 1 c T) =
      shift_ty 1 c (multi_subst_lt_in_ty cutoff lts T))
    (fun Ts => forall cutoff lts c,
      List.map (multi_subst_lt_in_ty cutoff lts) (List.map (shift_ty 1 c) Ts) =
      List.map (shift_ty 1 c) (List.map (multi_subst_lt_in_ty cutoff lts) Ts))).
  - intros n cutoff lts c. reflexivity.
  - intros A l B HA HB cutoff lts c. simpl. rewrite HA, HB. reflexivity.
  - intros K l Ts HTs cutoff lts c.
    simpl. f_equal. apply HTs.
  - intros A HA cutoff lts c. simpl. rewrite HA. reflexivity.
  - intros B A HB HA cutoff lts c. simpl. rewrite HB, HA. reflexivity.
  - intros cutoff lts c. reflexivity.
  - intros A Ts HA HTs cutoff lts c. cbn [List.map]. rewrite HA. f_equal. apply HTs.
Qed.

Lemma multi_subst_lt_shift_lt_comm : forall cutoff k lts c l,
  List.length lts = k ->
  multi_subst_lt cutoff (List.map (shift_lt 1 c) lts)
    (shift_lt 1 (cutoff + k + c) l) =
  shift_lt 1 (cutoff + c) (multi_subst_lt cutoff lts l).
Proof.
  intros cutoff k lts c l Hlen. revert cutoff k lts c Hlen.
  induction l as [x| | |l1 IH1 l2 IH2]; intros cutoff k lts c Hlen; simpl.
  - destruct (Nat.leb (cutoff + k + c) x) eqn:Hshift.
    + apply Nat.leb_le in Hshift.
      destruct (Nat.ltb x cutoff) eqn:Hbelow.
      * apply Nat.ltb_lt in Hbelow. lia.
      * apply Nat.ltb_ge in Hbelow.
        rewrite List.length_map, Hlen.
        assert (Hschema1 : (x + 1 - cutoff <? k) = false) by (apply Nat.ltb_ge; lia).
        rewrite Hschema1.
        assert (Hschema2 : (x - cutoff <? k) = false) by (apply Nat.ltb_ge; lia).
        rewrite Hschema2.
        destruct (Nat.leb (cutoff + c) (x - k)) eqn:Hrhs.
          -- assert (Hrhs_bool := Hrhs). apply Nat.leb_le in Hrhs.
            assert (Hbelow1 : (x + 1 <? cutoff) = false) by (apply Nat.ltb_ge; lia).
            rewrite Hbelow1. simpl. rewrite Hrhs_bool. f_equal. lia.
        -- apply Nat.leb_gt in Hrhs. lia.
    + apply Nat.leb_gt in Hshift.
      destruct (Nat.ltb x cutoff) eqn:Hbelow.
      * apply Nat.ltb_lt in Hbelow.
        destruct (Nat.leb (cutoff + c) x) eqn:Hrhs.
        -- apply Nat.leb_le in Hrhs. lia.
        -- simpl. rewrite Hrhs. reflexivity.
      * apply Nat.ltb_ge in Hbelow.
        rewrite List.length_map, Hlen.
        destruct (Nat.ltb (x - cutoff) k) eqn:Hschema.
        -- apply Nat.ltb_lt in Hschema.
            change lt_free with (shift_lt 1 c lt_free) at 1.
            rewrite map_nth.
           replace (cutoff + c) with (c + cutoff) by lia.
           symmetry. apply shift_lt_lift_many_swap.
        -- apply Nat.ltb_ge in Hschema.
           destruct (Nat.leb (cutoff + c) (x - k)) eqn:Hrhs.
           ++ apply Nat.leb_le in Hrhs. lia.
           ++ simpl. rewrite Hrhs. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1 with (k := k) (lts := lts) by exact Hlen.
    rewrite IH2 with (k := k) (lts := lts) by exact Hlen.
    reflexivity.
Qed.

Lemma multi_subst_lt_in_ty_shift_lt_comm : forall T cutoff k lts c,
  List.length lts = k ->
  multi_subst_lt_in_ty cutoff (List.map (shift_lt 1 c) lts)
    (shift_lt_in_ty 1 (cutoff + k + c) T) =
  shift_lt_in_ty 1 (cutoff + c) (multi_subst_lt_in_ty cutoff lts T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall cutoff k lts c,
      List.length lts = k ->
      multi_subst_lt_in_ty cutoff (List.map (shift_lt 1 c) lts)
        (shift_lt_in_ty 1 (cutoff + k + c) T) =
      shift_lt_in_ty 1 (cutoff + c) (multi_subst_lt_in_ty cutoff lts T))
    (fun Ts => forall cutoff k lts c,
      List.length lts = k ->
      List.map (multi_subst_lt_in_ty cutoff (List.map (shift_lt 1 c) lts))
        (List.map (shift_lt_in_ty 1 (cutoff + k + c)) Ts) =
      List.map (shift_lt_in_ty 1 (cutoff + c))
        (List.map (multi_subst_lt_in_ty cutoff lts) Ts))).
  - reflexivity.
  - intros A lt B HA HB cutoff k lts c Hlen. simpl.
    rewrite HA by exact Hlen. rewrite HB by exact Hlen.
    rewrite multi_subst_lt_shift_lt_comm with (k := k) by exact Hlen.
    reflexivity.
  - intros K lt Ts HTs cutoff k lts c Hlen. rewrite shift_lt_in_ty_ctor_eq. simpl.
    rewrite multi_subst_lt_shift_lt_comm with (k := k) by exact Hlen.
    f_equal. apply HTs. exact Hlen.
  - intros A HA cutoff k lts c Hlen. simpl.
    replace (S (cutoff + k + c)) with (S cutoff + k + c) by lia.
    replace (S (cutoff + c)) with (S cutoff + c) by lia.
    rewrite HA by exact Hlen. reflexivity.
  - intros B A HB HA cutoff k lts c Hlen. simpl.
    rewrite HB by exact Hlen. rewrite HA by exact Hlen. reflexivity.
  - reflexivity.
  - intros A Ts HA HTs cutoff k lts c Hlen. cbn [List.map].
    rewrite HA by exact Hlen. f_equal. apply HTs. exact Hlen.
Qed.

Lemma multi_subst_lt_shift_cancel : forall cutoff k lts l,
  List.length lts = k ->
  multi_subst_lt cutoff lts (shift_lt k cutoff l) = l.
Proof.
  intros cutoff k lts l Hlen. revert cutoff k lts Hlen.
  induction l as [x| | |l1 IH1 l2 IH2]; intros cutoff k lts Hlen; simpl.
  - destruct (Nat.leb cutoff x) eqn:Hle.
    + apply Nat.leb_le in Hle.
      rewrite Hlen.
      replace (x + k - cutoff) with ((x - cutoff) + k) by lia.
      destruct (Nat.ltb (x - cutoff + k) k) eqn:Hlt.
      * apply Nat.ltb_lt in Hlt. lia.
      * assert (Hge : (x + k <? cutoff) = false) by (apply Nat.ltb_ge; lia).
        rewrite Hge. replace (x + k - k) with x by lia. reflexivity.
    + apply Nat.leb_gt in Hle.
      assert (Hlt : (x <? cutoff) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hlt. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1 with (cutoff := cutoff) (k := k) (lts := lts) by exact Hlen.
    rewrite IH2 with (cutoff := cutoff) (k := k) (lts := lts) by exact Hlen.
    reflexivity.
Qed.

Lemma multi_subst_lt_in_ty_shift_lt_cancel : forall T cutoff k lts,
  List.length lts = k ->
  multi_subst_lt_in_ty cutoff lts (shift_lt_in_ty k cutoff T) = T.
Proof.
  intros T. apply (type_list_ind
    (fun T => forall cutoff k lts,
      List.length lts = k ->
      multi_subst_lt_in_ty cutoff lts (shift_lt_in_ty k cutoff T) = T)
    (fun Ts => forall cutoff k lts,
      List.length lts = k ->
      List.map (multi_subst_lt_in_ty cutoff lts) (List.map (shift_lt_in_ty k cutoff) Ts) = Ts)).
  - reflexivity.
  - intros A lt B HA HB cutoff k lts Hlen. simpl.
    rewrite HA by exact Hlen. rewrite HB by exact Hlen.
    rewrite multi_subst_lt_shift_cancel by exact Hlen. reflexivity.
  - intros K lt Ts HTs cutoff k lts Hlen. rewrite shift_lt_in_ty_ctor_eq. simpl.
    rewrite multi_subst_lt_shift_cancel by exact Hlen. f_equal. apply HTs. exact Hlen.
  - intros A HA cutoff k lts Hlen. simpl. rewrite HA by exact Hlen. reflexivity.
  - intros B A HB HA cutoff k lts Hlen. simpl.
    rewrite HB by exact Hlen. rewrite HA by exact Hlen. reflexivity.
  - intros cutoff k lts Hlen. reflexivity.
  - intros A Ts HA HTs cutoff k lts Hlen. cbn [List.map].
    rewrite HA by exact Hlen. f_equal. apply HTs. exact Hlen.
Qed.

(* Specialized zero-cutoff shapes, derived from the generalized theorem. *)
Lemma multi_subst_lt_shift_cancel0 : forall k lts l,
  List.length lts = k ->
  multi_subst_lt 0 lts (shift_lt k 0 l) = l.
Proof. intros k lts l Hlen. apply multi_subst_lt_shift_cancel. exact Hlen. Qed.

Lemma multi_subst_lt_in_ty_shift_lt_cancel0 : forall T k lts,
  List.length lts = k ->
  multi_subst_lt_in_ty 0 lts (shift_lt_in_ty k 0 T) = T.
Proof. intros T k lts Hlen. apply multi_subst_lt_in_ty_shift_lt_cancel. exact Hlen. Qed.

Lemma shift_lt_lift_outer_many : forall cutoff k R,
  shift_lt k cutoff (shift_lt cutoff 0 R) = shift_lt (cutoff + k) 0 R.
Proof.
  intros cutoff k R. revert cutoff k.
  induction R as [x| | |l1 IH1 l2 IH2]; intros cutoff k; simpl.
  - destruct (Nat.leb cutoff (x + cutoff)) eqn:Hle.
    + f_equal. lia.
    + apply Nat.leb_gt in Hle. lia.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma multi_subst_lt_subst_lt_comm : forall cutoff k lts l n R,
  List.length lts = k ->
  multi_subst_lt cutoff (List.map (subst_lt n R) lts)
    (subst_lt (cutoff + k + n) (shift_lt (cutoff + k) 0 R) l) =
  subst_lt (cutoff + n) (shift_lt cutoff 0 R)
    (multi_subst_lt cutoff lts l).
Proof.
  intros cutoff k lts l n R Hlen. revert cutoff k lts n R Hlen.
  induction l as [x| | |l1 IH1 l2 IH2]; intros cutoff k lts n R Hlen.
  - rewrite subst_lt_var_eq.
    destruct (Nat.eqb_spec x (cutoff + k + n)) as [Heq|Hneq].
    + subst x.
      rewrite <- shift_lt_lift_outer_many.
      rewrite multi_subst_lt_shift_cancel by (rewrite List.length_map; exact Hlen).
      simpl.
      destruct (Nat.ltb (cutoff + k + n) cutoff) eqn:Hlt; [apply Nat.ltb_lt in Hlt; lia|].
      rewrite Hlen.
      replace (cutoff + k + n - cutoff) with (k + n) by lia.
      destruct (Nat.ltb (k + n) k) eqn:Hbad; [apply Nat.ltb_lt in Hbad; lia|].
      replace (cutoff + k + n - k) with (cutoff + n) by lia.
      rewrite subst_lt_var_eq, Nat.eqb_refl. reflexivity.
    + destruct (Nat.ltb_spec (cutoff + k + n) x) as [Hgt|Hle].
      * simpl.
        destruct (Nat.ltb x cutoff) eqn:Hxc.
        { apply Nat.ltb_lt in Hxc. lia. }
        rewrite List.length_map, Hlen.
        assert (Hpred_ge : (pred x <? cutoff) = false) by (apply Nat.ltb_ge; lia).
        rewrite Hpred_ge.
        assert (Hxk : (x - cutoff <? k) = false) by (apply Nat.ltb_ge; lia).
        assert (Hpredk : (pred x - cutoff <? k) = false) by (apply Nat.ltb_ge; lia).
        rewrite Hxk, Hpredk.
        rewrite subst_lt_var_eq.
        destruct (Nat.eqb_spec (x - k) (cutoff + n)) as [Heq2|Hneq2]; [lia|].
        destruct (Nat.ltb_spec (cutoff + n) (x - k)) as [Hlt2|Hge2].
        -- replace (pred x - k) with (pred (x - k)) by lia. reflexivity.
        -- lia.
      * simpl.
        destruct (Nat.ltb x cutoff) eqn:Hxc.
        { apply Nat.ltb_lt in Hxc.
          rewrite subst_lt_var_eq.
          destruct (Nat.eqb_spec x (cutoff + n)); [lia|].
          destruct (Nat.ltb_spec (cutoff + n) x); [lia|reflexivity]. }
        apply Nat.ltb_ge in Hxc.
        rewrite List.length_map, Hlen.
        destruct (Nat.ltb_spec (x - cutoff) k) as [Hschema|Houter].
          -- change lt_free with (subst_lt n R lt_free).
            rewrite map_nth. rewrite shift_lt_subst_lt_comm_many0.
           replace (cutoff + n) with (cutoff + n) by lia. reflexivity.
          -- rewrite subst_lt_var_eq.
           destruct (Nat.eqb_spec (x - k) (cutoff + n)) as [Heq2|Hneq2]; [lia|].
           destruct (Nat.ltb_spec (cutoff + n) (x - k)) as [Hlt2|Hge2].
           ++ lia.
           ++ reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IH1 with (k := k) (lts := lts) by exact Hlen.
    rewrite IH2 with (k := k) (lts := lts) by exact Hlen.
    reflexivity.
Qed.

Lemma multi_subst_lt_in_ty_subst_lt_comm : forall T cutoff k lts n R,
  List.length lts = k ->
  multi_subst_lt_in_ty cutoff (List.map (subst_lt n R) lts)
    (subst_lt_in_ty (cutoff + k + n) (shift_lt (cutoff + k) 0 R) T) =
  subst_lt_in_ty (cutoff + n) (shift_lt cutoff 0 R)
    (multi_subst_lt_in_ty cutoff lts T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall cutoff k lts n R,
      List.length lts = k ->
      multi_subst_lt_in_ty cutoff (List.map (subst_lt n R) lts)
        (subst_lt_in_ty (cutoff + k + n) (shift_lt (cutoff + k) 0 R) T) =
      subst_lt_in_ty (cutoff + n) (shift_lt cutoff 0 R)
        (multi_subst_lt_in_ty cutoff lts T))
    (fun Ts => forall cutoff k lts n R,
      List.length lts = k ->
      List.map (multi_subst_lt_in_ty cutoff (List.map (subst_lt n R) lts))
        (List.map (subst_lt_in_ty (cutoff + k + n) (shift_lt (cutoff + k) 0 R)) Ts) =
      List.map (subst_lt_in_ty (cutoff + n) (shift_lt cutoff 0 R))
        (List.map (multi_subst_lt_in_ty cutoff lts) Ts))).
  - reflexivity.
  - intros A lt B HA HB cutoff k lts n R Hlen. simpl.
    rewrite HA by exact Hlen. rewrite HB by exact Hlen.
    rewrite multi_subst_lt_subst_lt_comm with (k := k) (lts := lts) by exact Hlen.
    reflexivity.
  - intros K lt Ts HTs cutoff k lts n R Hlen. rewrite subst_lt_in_ty_ctor_eq. simpl.
    rewrite multi_subst_lt_subst_lt_comm with (k := k) (lts := lts) by exact Hlen.
    f_equal. apply HTs. exact Hlen.
  - intros A HA cutoff k lts n R Hlen. simpl.
    replace (S (cutoff + k + n)) with (S cutoff + k + n) by lia.
    replace (S (cutoff + n)) with (S cutoff + n) by lia.
    rewrite !shift_lt_fuse.
    replace (1 + (cutoff + k)) with (S cutoff + k) by lia.
    replace (1 + cutoff) with (S cutoff) by lia.
    rewrite HA with (k := k) (lts := lts) by exact Hlen.
    reflexivity.
  - intros B A HB HA cutoff k lts n R Hlen. simpl.
    rewrite HB by exact Hlen. rewrite HA by exact Hlen. reflexivity.
  - intros cutoff k lts n R Hlen. reflexivity.
  - intros A Ts HA HTs cutoff k lts n R Hlen. cbn [List.map].
    rewrite HA by exact Hlen. f_equal. apply HTs. exact Hlen.
Qed.

Lemma inst_ctor_type_shift_ty : forall n_lt n_ty lts Ts T c,
  List.length Ts = n_ty ->
  inst_ctor_type n_lt n_ty lts (List.map (shift_ty 1 c) Ts) (shift_ty 1 (n_ty + c) T) =
  shift_ty 1 c (inst_ctor_type n_lt n_ty lts Ts T).
Proof.
  intros n_lt n_ty lts Ts T c Hlen.
  unfold inst_ctor_type, inst_lt_vars.
  replace (List.map (shift_lt_in_ty n_lt 0) (List.map (shift_ty 1 c) Ts)) with
    (List.map (shift_ty 1 c) (List.map (shift_lt_in_ty n_lt 0) Ts)).
  rewrite inst_ty_vars_shift_ty by (rewrite List.length_map; exact Hlen).
  apply multi_subst_lt_in_ty_shift_ty.
  rewrite !List.map_map. apply List.map_ext.
  intro U. rewrite shift_ty_shift_lt_in_ty_commute. reflexivity.
Qed.

(* MATCH-variant commutation: [inst_ctor_type_open] (no inst_lt_vars) vs    *)
(* type-variable shift.  Type-var shift does not interact with the n_lt     *)
(* pushed lt-binders, so the output shift index stays [c].                  *)
Lemma inst_ctor_type_open_shift_ty : forall n_lt n_ty Ts T c,
  List.length Ts = n_ty ->
  inst_ctor_type_open n_lt n_ty (List.map (shift_ty 1 c) Ts) (shift_ty 1 (n_ty + c) T) =
  shift_ty 1 c (inst_ctor_type_open n_lt n_ty Ts T).
Proof.
  intros n_lt n_ty Ts T c Hlen. unfold inst_ctor_type_open.
  replace (List.map (shift_lt_in_ty n_lt 0) (List.map (shift_ty 1 c) Ts)) with
    (List.map (shift_ty 1 c) (List.map (shift_lt_in_ty n_lt 0) Ts)).
  rewrite inst_ty_vars_shift_ty by (rewrite List.length_map; exact Hlen). reflexivity.
  rewrite !List.map_map. apply List.map_ext.
  intro U. rewrite shift_ty_shift_lt_in_ty_commute. reflexivity.
Qed.

Lemma inst_op_ty_args_shift_ty : forall n_α Ts n_β T c,
  List.length Ts = n_α ->
  inst_op_ty_args n_α (List.map (shift_ty 1 c) Ts) n_β
    (shift_ty 1 (n_α + n_β + c) T) =
  shift_ty 1 (n_β + c) (inst_op_ty_args n_α Ts n_β T).
Proof.
  intros n_α Ts n_β T c Hlen. unfold inst_op_ty_args.
  replace (List.map (shift_ty n_β 0) (List.map (shift_ty 1 c) Ts)) with
    (List.map (shift_ty 1 (n_β + c)) (List.map (shift_ty n_β 0) Ts)).
  - replace (n_α + n_β + c) with (n_α + (n_β + c)) by lia.
    rewrite inst_ty_vars_shift_ty by (rewrite List.length_map; exact Hlen).
    reflexivity.
  - rewrite !List.map_map. apply List.map_ext. intro U.
    symmetry. apply shift_ty_lift_shift.
Qed.

Lemma inst_op_all_args_shift_ty : forall n_α Ts n_β Ss T c,
  List.length Ts = n_α ->
  List.length Ss = n_β ->
  inst_op_all_args n_α (List.map (shift_ty 1 c) Ts)
    n_β (List.map (shift_ty 1 c) Ss)
    (shift_ty 1 (n_α + n_β + c) T) =
  shift_ty 1 c (inst_op_all_args n_α Ts n_β Ss T).
Proof.
  intros n_α Ts n_β Ss T c HlenTs HlenSs. unfold inst_op_all_args.
  rewrite inst_op_ty_args_shift_ty by exact HlenTs.
  rewrite inst_ty_vars_shift_ty by exact HlenSs.
  reflexivity.
Qed.


Lemma fold_bind_tm_shift_ty_map : forall rhos c G,
  fold_right (fun rho Γ0 => bind_tm rho :: Γ0) G (List.map (shift_ty 1 c) rhos) =
  fold_right (fun rho Γ0 => bind_tm (shift_ty 1 c rho) :: Γ0) G rhos.
Proof.
  induction rhos as [|rho rhos IH]; intros c G; simpl.
  - reflexivity.
  - f_equal. apply IH.
Qed.

Lemma lt_of_ty_shift_ty : forall T c,
  lt_of_ty (shift_ty 1 c T) = lt_of_ty T.
Proof.
  apply (type_list_ind
    (fun T => forall c, lt_of_ty (shift_ty 1 c T) = lt_of_ty T)
    (fun Ts => forall c,
      lt_of_ty_list (List.map (shift_ty 1 c) Ts) = lt_of_ty_list Ts));
    go_traverse.
Qed.

Lemma lt_of_ty_list_shift_ty : forall Ts c,
  lt_of_ty_list (List.map (shift_ty 1 c) Ts) = lt_of_ty_list Ts.
Proof.
  intros Ts c. induction Ts as [|T Ts IH]; simpl; [reflexivity|].
  rewrite lt_of_ty_shift_ty, IH. reflexivity.
Qed.

Lemma lt_of_ty_shift_lt : forall T c,
  lt_of_ty (shift_lt_in_ty 1 c T) = shift_lt 1 c (lt_of_ty T).
Proof.
  apply (type_list_ind
    (fun T => forall c, lt_of_ty (shift_lt_in_ty 1 c T) = shift_lt 1 c (lt_of_ty T))
    (fun Ts => forall c,
      lt_of_ty_list (List.map (shift_lt_in_ty 1 c) Ts) = shift_lt 1 c (lt_of_ty_list Ts)));
    go_traverse.
Qed.

Lemma lt_of_ty_list_shift_lt : forall Ts c,
  lt_of_ty_list (List.map (shift_lt_in_ty 1 c) Ts) = shift_lt 1 c (lt_of_ty_list Ts).
Proof.
  intros Ts c. induction Ts as [|T Ts IH]; simpl; [reflexivity|].
  rewrite lt_of_ty_shift_lt, IH. rewrite <- shift_lt_join_eq. reflexivity.
Qed.

Lemma elim_ty_shift_ty : forall T lvar bound p c,
  elim_ty lvar bound p (shift_ty 1 c T) =
  option_map (shift_ty 1 c) (elim_ty lvar bound p T).
Proof.
  apply (type_list_ind
    (fun T => forall lvar bound p c,
      elim_ty lvar bound p (shift_ty 1 c T) =
      option_map (shift_ty 1 c) (elim_ty lvar bound p T))
    (fun Ts => forall lvar bound p c,
      (fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
         match Ts0 with
         | [] => Some []
         | A :: rest =>
             match elim_ty lvar bound p' A, go_list p' rest with
             | Some A', Some rest' => Some (A' :: rest')
             | _, _ => None
             end
         end) p (List.map (shift_ty 1 c) Ts) =
      option_map (List.map (shift_ty 1 c))
        ((fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
          match Ts0 with
          | [] => Some []
          | A :: rest =>
              match elim_ty lvar bound p' A, go_list p' rest with
              | Some A', Some rest' => Some (A' :: rest')
              | _, _ => None
              end
          end) p Ts))).
  - intros n lvar bound p c. reflexivity.
  - intros A l B HA HB lvar bound p c. simpl.
    rewrite HA, HB. destruct (elim_ty lvar bound (flip_variance p) A);
      destruct (elim_lt lvar bound p l); destruct (elim_ty lvar bound p B); reflexivity.
  - intros K l Ts HTs lvar bound p c. simpl.
    destruct (elim_lt lvar bound p l); [|reflexivity].
    pose proof (HTs lvar bound var_inv c) as HTs'. simpl in HTs'.
    rewrite HTs'. destruct ((fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
      match Ts0 with
      | [] => Some []
      | A :: rest =>
          match elim_ty lvar bound p' A, go_list p' rest with
          | Some A', Some rest' => Some (A' :: rest')
          | _, _ => None
          end
      end) var_inv Ts); reflexivity.
  - intros A HA lvar bound p c. simpl.
    rewrite HA. destruct (elim_ty (S lvar) (shift_lt 1 0 bound) p A); reflexivity.
  - intros B A HB HA lvar bound p c. simpl.
    rewrite HB, HA. destruct (elim_ty lvar bound (flip_variance p) B);
      destruct (elim_ty lvar bound p A); reflexivity.
  - intros lvar bound p c. reflexivity.
  - intros A Ts HA HTs lvar bound p c. cbn [List.map]. simpl.
    pose proof (HA lvar bound p c) as HA'.
    pose proof (HTs lvar bound p c) as HTs'. simpl in HTs'.
    rewrite HA', HTs'. destruct (elim_ty lvar bound p A);
      destruct ((fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
        match Ts0 with
        | [] => Some []
        | A0 :: rest =>
            match elim_ty lvar bound p' A0, go_list p' rest with
            | Some A', Some rest' => Some (A' :: rest')
            | _, _ => None
            end
        end) p Ts); reflexivity.
Qed.

Lemma elim_ty_n_shift_ty : forall n bound p T T' c,
  elim_ty_n n bound p T = Some T' ->
  elim_ty_n n bound p (shift_ty 1 c T) = Some (shift_ty 1 c T').
Proof.
  induction n as [|n IH]; intros bound p T T' c H.
  - simpl in *. injection H as H; subst T'. reflexivity.
  - simpl in *. destruct (elim_ty 0 bound p T) as [U|] eqn:HU; [|discriminate].
    rewrite elim_ty_shift_ty. rewrite HU. simpl.
    rewrite <- shift_ty_subst_lt_in_ty_commute.
    apply IH. exact H.
Qed.

Lemma elim_lt_shift_lt_above : forall l lvar bound p c l',
  lvar < c ->
  elim_lt lvar bound p l = Some l' ->
  elim_lt lvar (shift_lt 1 c bound) p (shift_lt 1 c l) = Some (shift_lt 1 c l').
Proof.
  induction l as [x| | |l1 IH1 l2 IH2]; intros lvar bound p c l' Hlt H; simpl in *.
  - destruct (Nat.eqb_spec x lvar) as [Heq|Hneq].
    + subst x. simpl in H.
      destruct (Nat.leb c lvar) eqn:Hle; [apply Nat.leb_le in Hle; lia|].
      rewrite Nat.eqb_refl.
      destruct p; inversion H; subst; reflexivity.
    + destruct (Nat.leb_spec c x) as [Hcx|Hxc].
      * simpl. destruct (Nat.eqb (x + 1) lvar) eqn:Heq;
          [apply Nat.eqb_eq in Heq; lia|]. inversion H; subst.
        destruct (Nat.leb c x) eqn:Hle; [simpl; rewrite Hle; reflexivity|apply Nat.leb_gt in Hle; lia].
      * simpl. destruct (Nat.eqb x lvar) eqn:Heq;
          [apply Nat.eqb_eq in Heq; contradiction|]. inversion H; subst.
        destruct (Nat.leb c x) eqn:Hle; [apply Nat.leb_le in Hle; lia|simpl; rewrite Hle; reflexivity].
  - inversion H; subst. reflexivity.
  - inversion H; subst. reflexivity.
  - destruct (elim_lt lvar bound p l1) as [l1'|] eqn:H1; [|discriminate].
    destruct (elim_lt lvar bound p l2) as [l2'|] eqn:H2; [|discriminate].
    inversion H; subst; clear H.
    rewrite (IH1 lvar bound p c l1' Hlt H1).
    rewrite (IH2 lvar bound p c l2' Hlt H2).
    reflexivity.
Qed.

Lemma elim_ty_shift_lt_above : forall T lvar bound p c T',
  lvar < c ->
  elim_ty lvar bound p T = Some T' ->
  elim_ty lvar (shift_lt 1 c bound) p (shift_lt_in_ty 1 c T) = Some (shift_lt_in_ty 1 c T').
Proof.
  enough (H : forall T, forall lvar bound p c T',
    lvar < c ->
    elim_ty lvar bound p T = Some T' ->
    elim_ty lvar (shift_lt 1 c bound) p (shift_lt_in_ty 1 c T) = Some (shift_lt_in_ty 1 c T')).
  { intros T. apply H. }
  apply (type_list_ind
    (fun T => forall lvar bound p c T',
      lvar < c ->
      elim_ty lvar bound p T = Some T' ->
      elim_ty lvar (shift_lt 1 c bound) p (shift_lt_in_ty 1 c T) = Some (shift_lt_in_ty 1 c T'))
    (fun Ts => forall lvar bound p c Ts',
      lvar < c ->
      (fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
        match Ts0 with
        | [] => Some []
        | A :: rest =>
            match elim_ty lvar bound p' A, go_list p' rest with
            | Some A', Some rest' => Some (A' :: rest')
            | _, _ => None
            end
        end) p Ts = Some Ts' ->
      (fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
        match Ts0 with
        | [] => Some []
        | A :: rest =>
            match elim_ty lvar (shift_lt 1 c bound) p' A, go_list p' rest with
            | Some A', Some rest' => Some (A' :: rest')
            | _, _ => None
            end
        end) p (List.map (shift_lt_in_ty 1 c) Ts) = Some (List.map (shift_lt_in_ty 1 c) Ts'))).
  - intros n lvar bound p c T' Hlt H. inversion H; subst. reflexivity.
  - intros A l B IHA IHB lvar bound p c T' Hlt H. simpl in *.
    destruct (elim_ty lvar bound (flip_variance p) A) as [A'|] eqn:HA; [|discriminate].
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; [|discriminate].
    destruct (elim_ty lvar bound p B) as [B'|] eqn:HB; [|discriminate].
    inversion H; subst; clear H.
    rewrite (IHA lvar bound (flip_variance p) c A' Hlt HA).
    rewrite (elim_lt_shift_lt_above l lvar bound p c l' Hlt Hl).
    rewrite (IHB lvar bound p c B' Hlt HB).
    reflexivity.
  - intros K l Ts IHTs lvar bound p c T' Hlt H. simpl in *.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; [|discriminate].
    destruct ((fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
      match Ts0 with
      | [] => Some []
      | A :: rest =>
          match elim_ty lvar bound p' A, go_list p' rest with
          | Some A', Some rest' => Some (A' :: rest')
          | _, _ => None
          end
      end) var_inv Ts) as [Ts'|] eqn:HTs; [|discriminate].
    inversion H; subst; clear H.
    rewrite (elim_lt_shift_lt_above l lvar bound p c l' Hlt Hl).
    rewrite (IHTs lvar bound var_inv c Ts' Hlt HTs).
    reflexivity.
  - intros A IHA lvar bound p c T' Hlt H. simpl in *.
    destruct (elim_ty (S lvar) (shift_lt 1 0 bound) p A) as [A'|] eqn:HA; [|discriminate].
    inversion H; subst; clear H.
    replace (shift_lt 1 0 (shift_lt 1 c bound)) with (shift_lt 1 (S c) (shift_lt 1 0 bound)).
    2:{ symmetry. apply shift_lt_swap_0. }
    rewrite (IHA (S lvar) (shift_lt 1 0 bound) p (S c) A' ltac:(lia) HA).
    reflexivity.
  - intros B A IHB IHA lvar bound p c T' Hlt H. simpl in *.
    destruct (elim_ty lvar bound (flip_variance p) B) as [B'|] eqn:HB; [|discriminate].
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HA; [|discriminate].
    inversion H; subst; clear H.
    rewrite (IHB lvar bound (flip_variance p) c B' Hlt HB).
    rewrite (IHA lvar bound p c A' Hlt HA).
    reflexivity.
  - intros lvar bound p c Ts' Hlt H. inversion H; subst. reflexivity.
  - intros A Ts IHA IHTs lvar bound p c Ts' Hlt H. simpl in *.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HA; [|discriminate].
    destruct ((fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
      match Ts0 with
      | [] => Some []
      | A0 :: rest =>
          match elim_ty lvar bound p' A0, go_list p' rest with
          | Some A', Some rest' => Some (A' :: rest')
          | _, _ => None
          end
      end) p Ts) as [Ts''|] eqn:HTs; [|discriminate].
    inversion H; subst; clear H.
    rewrite (IHA lvar bound p c A' Hlt HA).
    rewrite (IHTs lvar bound p c Ts'' Hlt HTs).
    reflexivity.
Qed.

Lemma subst_lt_shift_lt_free_above : forall l c,
  subst_lt 0 lt_free (shift_lt 1 (S c) l) =
  shift_lt 1 c (subst_lt 0 lt_free l).
Proof.
  intros l c.
  pose proof (shift_lt_subst_lt_above_comm l 0 c lt_free) as H.
  simpl in H. replace (0 + c) with c in H by lia.
  symmetry. exact H.
Qed.

Lemma subst_lt_in_ty_shift_lt_free_above : forall T c,
  subst_lt_in_ty 0 lt_free (shift_lt_in_ty 1 (S c) T) =
  shift_lt_in_ty 1 c (subst_lt_in_ty 0 lt_free T).
Proof.
  intros T c.
  pose proof (shift_lt_in_ty_subst_lt_in_ty_above_comm T 0 c lt_free) as H.
  simpl in H. replace (0 + c) with c in H by lia.
  symmetry. exact H.
Qed.

Lemma elim_ty_n_shift_lt_above : forall n bound p T T' c,
  elim_ty_n n bound p T = Some T' ->
  elim_ty_n n (shift_lt 1 (n + c) bound) p (shift_lt_in_ty 1 (n + c) T) =
    Some (shift_lt_in_ty 1 c T').
Proof.
  induction n as [|n IH]; intros bound p T T' c H.
  - simpl in *. inversion H; subst. reflexivity.
  - simpl in H. destruct (elim_ty 0 bound p T) as [U|] eqn:HU; [|discriminate].
    simpl.
    replace (S n + c) with (S (n + c)) by lia.
    rewrite (elim_ty_shift_lt_above T 0 bound p (S (n + c)) U ltac:(lia) HU).
    simpl.
    rewrite subst_lt_in_ty_shift_lt_free_above.
    rewrite subst_lt_shift_lt_free_above.
    replace (0 + (n + c)) with (n + c) by lia.
    apply IH. exact H.
Qed.

Lemma typing_InsTy : forall G t T, G ⊢ₜ t : T ->
  forall c G', InsTy c G G' -> G' ⊢ₜ shift_ty_in_tm 1 c t : shift_ty 1 c T.
Proof.
  apply (typing_ind_forall2
    (fun G t T => forall c G', InsTy c G G' ->
       G' ⊢ₜ shift_ty_in_tm 1 c t : shift_ty 1 c T)).
  - intros Γ x T Hlk Hwf c G' HIns. simpl.
    apply T_Var.
    + rewrite (InsTy_lookup_tm c Γ G' HIns x), Hlk. reflexivity.
    + wf_transport.
  - intros Γ t T U Ht IHt Hsub c G' HIns. simpl.
    eapply T_Sub.
    + apply IHt. exact HIns.
    + apply (sub_InsTy Γ T U Hsub c G' HIns).
  - intros Γ body A l B HwfA HwfB Hbody IHbody Hcap c G' HIns. simpl.
    apply T_Lam.
    + wf_transport.
    + wf_transport.
    + apply IHbody. apply InsTy_tm. exact HIns.
    + rewrite (capture_lt_InsTy c Γ G' HIns body).
      apply (lt_sub_InsTy Γ (capture_lt Γ body) l Hcap c G' HIns).
  - intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 c G' HIns. simpl.
    eapply T_App; [apply IH1|apply IH2]; exact HIns.
  - intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody c G' HIns. simpl.
    apply T_TyLam.
    + wf_transport.
    + eapply ty_wf_InsTy; [exact HwfT|]. apply InsTy_ty. exact HIns.
    + rewrite is_abs_shift_ty_in_tm. exact HisAbs.
    + apply IHbody. apply InsTy_ty. exact HIns.
  - intros Γ t B U S Ht IHt HwfS Hsub c G' HIns. simpl.
    rewrite shift_ty_subst_ty_comm_ge0.
    eapply T_TyApp.
    + apply IHt. exact HIns.
    + wf_transport.
    + apply (sub_InsTy Γ S B Hsub c G' HIns).
  - intros Γ body T HwfT HisAbs Hbody IHbody c G' HIns. simpl.
    apply T_LtLam.
    + eapply ty_wf_InsTy; [exact HwfT|]. apply InsTy_lt. exact HIns.
    + rewrite is_abs_shift_ty_in_tm. exact HisAbs.
    + apply IHbody. apply InsTy_lt. exact HIns.
  - intros Γ t T l Ht IHt Hwfl c G' HIns. simpl.
    rewrite shift_ty_subst_lt_in_ty_commute.
    eapply T_LtApp.
    + apply IHt. exact HIns.
    + wf_transport.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
           Hctor Heff Hlts Hwflts Hrho HTs HwfTs Hresult Hshape Hresult_eff Hwfl Hlt Hbounded Hlen Hargs IHargs c G' HIns.
    simpl. unfold map_shift_ty.    eapply T_Ctor with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := List.map (shift_ty 1 (n_ty + c)) sigma_fields)
      (result_ty_schema := shift_ty 1 (n_ty + c) result_ty_schema)
      (rho_fields := List.map (shift_ty 1 c) rho_fields)
      (result_tag := result_tag).
    + rewrite (InsTy_lookup_ctor c Γ G' HIns K). rewrite Hctor. reflexivity.
    + rewrite (InsTy_lookup_eff c Γ G' HIns K). rewrite Heff. reflexivity.
    + exact Hlts.
    + wf_transport.
    + rewrite Hrho. rewrite !List.map_map. apply List.map_ext. intro sigma.
      exact (eq_sym (inst_ctor_type_shift_ty n_lt n_ty lts Ts sigma c HTs)).
    + rewrite List.length_map. exact HTs.
    + wf_transport.
    + rewrite Hresult.
      exact (eq_sym (inst_ctor_type_shift_ty n_lt n_ty lts Ts result_ty_schema c HTs)).
    + rewrite Hshape. reflexivity.
    + rewrite (InsTy_lookup_eff c Γ G' HIns result_tag). rewrite Hresult_eff. reflexivity.
    + wf_transport.
    + rewrite (lt_of_ty_list_shift_ty rho_fields c).
      rewrite (lt_of_ty_shift_ty result_ty c).
      apply (lt_sub_InsTy Γ (lt_of_ty_list rho_fields) (lt_of_ty result_ty) Hlt c G' HIns).
    + eapply Forall_impl; [|exact Hbounded]. intros l0 Hsub.
      apply (lt_sub_InsTy Γ l0 l Hsub c G' HIns).
    + rewrite !List.length_map. exact Hlen.
    + apply (typings_InsTy Γ vs rho_fields IHargs c G' HIns).
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γyes yes_body eta elim_result no_body
           Hneq Hctor Heff Hlts Hrho HTs HwfTs Hscrut_result Hscrut_shape Hresult_eff Hresult_ne
           HwfDelta Hresult_l Hscrut IHscrut Harity HΓyes Hyes IHyes Helim Hno IHno c G' HIns.
    simpl. unfold map_shift_ty. subst Γyes.
    eapply T_Match with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := List.map (shift_ty 1 (n_ty + c)) sigma_fields)
      (result_ty_schema := shift_ty 1 (n_ty + c) result_ty_schema)
      (lts := lts) (rho_fields := List.map (shift_ty 1 c) rho_fields)
      (scrut_result_ty := shift_ty 1 c scrut_result_ty)
      (result_tag := result_tag) (result_l := result_l)
      (Γ' := push_match_bound n_lt Delta G') (eta := shift_ty 1 c eta).
    + exact Hneq.
    + rewrite (InsTy_lookup_ctor c Γ G' HIns K). rewrite Hctor. reflexivity.
    + rewrite (InsTy_lookup_eff c Γ G' HIns K). rewrite Heff. reflexivity.
    + exact Hlts.
    + rewrite Hrho. rewrite !List.map_map. apply List.map_ext. intro sigma.
      exact (eq_sym (inst_ctor_type_open_shift_ty n_lt n_ty Ts sigma c HTs)).
    + rewrite List.length_map. exact HTs.
    + wf_transport.
    + rewrite Hscrut_result.
      exact (eq_sym (inst_ctor_type_shift_ty n_lt n_ty (List.repeat Delta n_lt) Ts result_ty_schema c HTs)).
    + rewrite Hscrut_shape. reflexivity.
    + rewrite (InsTy_lookup_eff c Γ G' HIns result_tag). rewrite Hresult_eff. reflexivity.
    + exact Hresult_ne.
    + wf_transport.
    + apply (lt_sub_InsTy Γ result_l Delta Hresult_l c G' HIns).
    + apply IHscrut. exact HIns.
    + rewrite List.length_map. exact Harity.
    + reflexivity.
    + apply IHyes.
      rewrite fold_bind_tm_shift_ty_map.
      apply InsTy_fold_bind_tm.
      apply InsTy_push_match_bound. exact HIns.
    + apply elim_ty_n_shift_ty. exact Helim.
    + apply IHno. exact HIns.
  - intros Γ E_tag m Ts op_bodies n_α ops T_R
           Heff HTs HwfTs HwfTR Hfst Hops IHops c G' HIns.
    simpl. unfold map_shift_ty.
    rewrite shift_ty_in_tm_ops_eq_map.
    eapply T_Cap with
      (n_α := n_α)
      (ops := List.map (fun osig =>
                 (op_nb osig,
                  shift_ty 1 (n_α + op_nb osig + c) (op_sig_ty osig),
                  shift_ty 1 (n_α + op_nb osig + c) (op_ret_ty osig))) ops)
      (T_R := shift_ty 1 c T_R).
    + rewrite (InsTy_lookup_eff c Γ G' HIns E_tag). rewrite Heff. simpl.
      do 2 f_equal. apply List.map_ext. intros [[nβ sg] rt]. reflexivity.
    + rewrite List.length_map. exact HTs.
    + wf_transport.
    + wf_transport.
    + rewrite !List.map_map. exact Hfst.
    + clear Hops Heff. revert Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IHrest]; intros Hfst; simpl.
      * constructor.
      * simpl in Hfst. injection Hfst as Hnb Hfstrest.
        constructor; [| apply IHrest; exact Hfstrest ].
        destruct osig as [[nβ sg] rt].
        unfold op_nb, op_sig_ty, op_ret_ty in *. simpl in *.
        rewrite Hnb.
        unfold op_body_ctx.
        rewrite (inst_op_ty_args_shift_ty n_α Ts nβ sg c HTs).
        rewrite (inst_op_ty_args_shift_ty n_α Ts nβ rt c HTs).
        replace (c + nβ) with (nβ + c) by lia.
        rewrite shift_ty_lift_shift.
        apply Hone.
        apply InsTy_tm. apply InsTy_tm. apply InsTy_push_ty_vars_any_at_free. exact HIns.
  - intros Γ E_tag Ts op_bodies body n_α ops T_B T_R
           Heff HTs HwfTs HwfTB HwfTR Hnolocal Hsub Hfst Hops IHops Hbody IHbody c G' HIns.
    simpl. unfold map_shift_ty.
    rewrite shift_ty_in_tm_ops_eq_map.
    eapply T_Handle with
      (n_α := n_α)
      (ops := List.map (fun osig =>
                 (op_nb osig,
                  shift_ty 1 (n_α + op_nb osig + c) (op_sig_ty osig),
                  shift_ty 1 (n_α + op_nb osig + c) (op_ret_ty osig))) ops)
      (T_B := shift_ty 1 c T_B)
      (T_R := shift_ty 1 c T_R).
    + rewrite (InsTy_lookup_eff c Γ G' HIns E_tag). rewrite Heff. simpl.
      do 2 f_equal. apply List.map_ext. intros [[nβ sg] rt]. reflexivity.
    + rewrite List.length_map. exact HTs.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + apply (sub_InsTy Γ T_B T_R Hsub c G' HIns).
    + rewrite !List.map_map. exact Hfst.
    + clear Hops Heff. revert Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IHrest]; intros Hfst; simpl.
      * constructor.
      * simpl in Hfst. injection Hfst as Hnb Hfstrest.
        constructor; [| apply IHrest; exact Hfstrest ].
        destruct osig as [[nβ sg] rt].
        unfold op_nb, op_sig_ty, op_ret_ty in *. simpl in *.
        rewrite Hnb.
        unfold op_body_ctx.
        rewrite (inst_op_ty_args_shift_ty n_α Ts nβ sg c HTs).
        rewrite (inst_op_ty_args_shift_ty n_α Ts nβ rt c HTs).
        replace (c + nβ) with (nβ + c) by lia.
        rewrite shift_ty_lift_shift.
        apply Hone.
        apply InsTy_tm. apply InsTy_tm. apply InsTy_push_ty_vars_any_at_free. exact HIns.
    + apply IHbody. apply InsTy_tm. exact HIns.
  - intros Γ recv op arg E_tag Delta Ts Ss n_α ops n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hnth HTs HSs HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg c G' HIns.
    simpl. unfold map_shift_ty.
    eapply T_Perform with
      (n_α := n_α)
      (ops := List.map (fun osig =>
                 (op_nb osig,
                  shift_ty 1 (n_α + op_nb osig + c) (op_sig_ty osig),
                  shift_ty 1 (n_α + op_nb osig + c) (op_ret_ty osig))) ops)
      (n_β := n_β)
      (sig := shift_ty 1 (n_α + n_β + c) sig)
      (ret := shift_ty 1 (n_α + n_β + c) ret)
      (sig_inst := shift_ty 1 c sig_inst)
      (ret_inst := shift_ty 1 c ret_inst).
    + apply IHrecv. exact HIns.
    + rewrite (InsTy_lookup_eff c Γ G' HIns E_tag). rewrite Heff. simpl.
      do 2 f_equal. apply List.map_ext. intros [[nβ sg] rt]. reflexivity.
    + rewrite (map_nth_error _ _ _ Hnth). reflexivity.
    + lazymatch goal with
      | |- length Ts = n_α => exact HTs
      | |- length (List.map _ Ts) = n_α => rewrite List.length_map; exact HTs
      | |- _ => change (length (List.map (shift_ty 1 c) Ts) = n_α);
                rewrite List.length_map; exact HTs
      end.
    + lazymatch goal with
      | |- length Ss = n_β => exact HSs
      | |- length (List.map _ Ss) = n_β => rewrite List.length_map; exact HSs
      | |- _ => change (length (List.map (shift_ty 1 c) Ss) = n_β);
                rewrite List.length_map; exact HSs
      end.
    + wf_transport.
    + wf_transport.
    + rewrite Hsig. symmetry. apply inst_op_all_args_shift_ty; assumption.
    + wf_transport.
    + rewrite Hret. symmetry. apply inst_op_all_args_shift_ty; assumption.
    + wf_transport.
    + apply IHarg. exact HIns.
  - intros Γ m T_B T_R t HwfTB HwfTR Hnolocal Hsub Ht IH c G' HIns. simpl.
    apply T_HandlerM.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + apply (sub_InsTy Γ T_B T_R Hsub c G' HIns).
    + apply IH. exact HIns.
Qed.

Lemma shift_lt_in_ty_subst_ty_comm : forall T c n Sb,
  shift_lt_in_ty 1 c (subst_ty n Sb T)
  = subst_ty n (shift_lt_in_ty 1 c Sb) (shift_lt_in_ty 1 c T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall c n Sb,
       shift_lt_in_ty 1 c (subst_ty n Sb T)
       = subst_ty n (shift_lt_in_ty 1 c Sb) (shift_lt_in_ty 1 c T))
    (fun Ts => forall c n Sb,
       List.map (shift_lt_in_ty 1 c) (List.map (subst_ty n Sb) Ts)
       = List.map (subst_ty n (shift_lt_in_ty 1 c Sb)) (List.map (shift_lt_in_ty 1 c) Ts))).
  - intros m c n Sb. rewrite subst_ty_var_eq.
    destruct (Nat.eqb_spec m n).
    + subst m. rewrite shift_lt_in_ty_var_eq. rewrite subst_ty_var_eq.
      rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.ltb_spec n m).
      * rewrite shift_lt_in_ty_var_eq, shift_lt_in_ty_var_eq, subst_ty_var_eq.
        destruct (Nat.eqb_spec m n); [lia|].
        destruct (Nat.ltb_spec n m); [reflexivity|lia].
      * rewrite !shift_lt_in_ty_var_eq, subst_ty_var_eq.
        destruct (Nat.eqb_spec m n); [lia|].
        destruct (Nat.ltb_spec n m); [lia|reflexivity].
  - intros A l B HA HB c n Sb.
    rewrite subst_ty_fun_eq, !shift_lt_in_ty_fun_eq, subst_ty_fun_eq.
    rewrite HA, HB. reflexivity.
  - intros K l Ts HTs c n Sb.
    rewrite subst_ty_ctor_eq, !shift_lt_in_ty_ctor_eq, subst_ty_ctor_eq.
    f_equal. apply HTs.
  - intros A HA c n Sb.
    rewrite subst_ty_ltall_eq, shift_lt_in_ty_ltall_eq, shift_lt_in_ty_ltall_eq, subst_ty_ltall_eq.
    f_equal. rewrite HA. f_equal.
    symmetry. apply shift_lt_in_ty_swap_0.
  - intros B A HB HA c n Sb.
    rewrite subst_ty_tyall_eq, shift_lt_in_ty_tyall_eq, shift_lt_in_ty_tyall_eq, subst_ty_tyall_eq.
    rewrite HB. f_equal.
    rewrite HA. f_equal.
    symmetry. apply shift_ty_shift_lt_in_ty_commute.
  - intros c n Sb. reflexivity.
  - intros A Ts HA HTs c n Sb.
    cbn [List.map]. rewrite HA. f_equal. apply HTs.
Qed.

Lemma inst_ty_vars_shift_lt : forall n Ts T c,
  List.length Ts = n ->
  inst_ty_vars n (List.map (shift_lt_in_ty 1 c) Ts) (shift_lt_in_ty 1 c T) =
  shift_lt_in_ty 1 c (inst_ty_vars n Ts T).
Proof.
  induction n as [|n IH]; intros Ts T c Hlen.
  - destruct Ts as [|U rest]; [|simpl in Hlen; discriminate].
    reflexivity.
  - destruct Ts as [|U rest]; [simpl in Hlen; discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    simpl. rewrite shift_ty_shift_lt_in_ty_commute.
    rewrite <- shift_lt_in_ty_subst_ty_comm.
    rewrite IH by exact Hlen. reflexivity.
Qed.

(* lt-insertion commutes with [inst_ctor_type_open]: the field-type     *)
(* result lives under the n_lt match lt-binders, so its outer cutoff is  *)
(* [n_lt + c] while the [Ts] arguments (in the outer context) shift at   *)
(* [c].  Needed by the T_Match case of [typing_InsLt].                   *)
Lemma inst_ctor_type_open_shift_lt : forall n_lt n_ty Ts T c,
  List.length Ts = n_ty ->
  inst_ctor_type_open n_lt n_ty (List.map (shift_lt_in_ty 1 c) Ts)
    (shift_lt_in_ty 1 (n_lt + c) T) =
  shift_lt_in_ty 1 (n_lt + c) (inst_ctor_type_open n_lt n_ty Ts T).
Proof.
  intros n_lt n_ty Ts T c Hlen. unfold inst_ctor_type_open.
  replace (List.map (shift_lt_in_ty n_lt 0) (List.map (shift_lt_in_ty 1 c) Ts))
    with (List.map (shift_lt_in_ty 1 (n_lt + c)) (List.map (shift_lt_in_ty n_lt 0) Ts)).
  - rewrite (inst_ty_vars_shift_lt n_ty
      (List.map (shift_lt_in_ty n_lt 0) Ts) T (n_lt + c)
      ltac:(rewrite List.length_map; exact Hlen)).
    reflexivity.
  - rewrite !List.map_map. apply List.map_ext. intro U.
    replace (n_lt + c) with (c + n_lt) by lia.
    apply shift_lt_in_ty_lift_many_swap.
Qed.

Lemma inst_ctor_type_shift_lt : forall n_lt n_ty lts Ts T c,
  List.length lts = n_lt ->
  List.length Ts = n_ty ->
  inst_ctor_type n_lt n_ty (List.map (shift_lt 1 c) lts)
    (List.map (shift_lt_in_ty 1 c) Ts)
    (shift_lt_in_ty 1 (n_lt + c) T) =
  shift_lt_in_ty 1 c (inst_ctor_type n_lt n_ty lts Ts T).
Proof.
  intros n_lt n_ty lts Ts T c Hlen_lts Hlen_Ts.
  unfold inst_ctor_type, inst_lt_vars.
  rewrite <- (map_shift_lt_in_ty_lift_many_swap n_lt c Ts).
  replace (c + n_lt) with (n_lt + c) by lia.
  rewrite (inst_ty_vars_shift_lt n_ty
    (List.map (shift_lt_in_ty n_lt 0) Ts) T (n_lt + c)).
  2:{ rewrite List.length_map. exact Hlen_Ts. }
  rewrite multi_subst_lt_in_ty_shift_lt_comm with (k := n_lt) by exact Hlen_lts.
  replace (0 + c) with c by lia.
  reflexivity.
Qed.

Lemma inst_op_ty_args_shift_lt : forall n_α Ts n_β T c,
  List.length Ts = n_α ->
  inst_op_ty_args n_α (List.map (shift_lt_in_ty 1 c) Ts) n_β
    (shift_lt_in_ty 1 c T) =
  shift_lt_in_ty 1 c (inst_op_ty_args n_α Ts n_β T).
Proof.
  intros n_α Ts n_β T c Hlen. unfold inst_op_ty_args.
  replace (List.map (shift_ty n_β 0) (List.map (shift_lt_in_ty 1 c) Ts)) with
    (List.map (shift_lt_in_ty 1 c) (List.map (shift_ty n_β 0) Ts)).
  - rewrite inst_ty_vars_shift_lt by (rewrite List.length_map; exact Hlen).
    reflexivity.
  - rewrite !List.map_map. apply List.map_ext. intro U.
    symmetry. apply shift_ty_shift_lt_in_ty_commute.
Qed.

Lemma inst_op_all_args_shift_lt : forall n_α Ts n_β Ss T c,
  List.length Ts = n_α ->
  List.length Ss = n_β ->
  inst_op_all_args n_α (List.map (shift_lt_in_ty 1 c) Ts)
    n_β (List.map (shift_lt_in_ty 1 c) Ss)
    (shift_lt_in_ty 1 c T) =
  shift_lt_in_ty 1 c (inst_op_all_args n_α Ts n_β Ss T).
Proof.
  intros n_α Ts n_β Ss T c HlenTs HlenSs. unfold inst_op_all_args.
  rewrite inst_op_ty_args_shift_lt by exact HlenTs.
  rewrite inst_ty_vars_shift_lt by exact HlenSs.
  reflexivity.
Qed.

Lemma Forall_lt_sub_InsLt_map : forall Γ lts l,
  Forall (fun l0 => Γ ⊢ₗ l0 <: l) lts ->
  forall c G', InsLt c Γ G' ->
  Forall (fun l0 => G' ⊢ₗ l0 <: shift_lt 1 c l)
    (List.map (shift_lt 1 c) lts).
Proof.
  intros Γ lts l Hbounded c G' HIns.
  induction Hbounded as [|l0 lts0 Hsub0 Hbounded0 IH]; simpl.
  - constructor.
  - constructor.
    + apply (lt_sub_InsLt Γ l0 l Hsub0 c G' HIns).
    + exact IH.
Qed.

(* Generic (no-closedness) [typing_InsLt]: a bind_lt weakening at any   *)
(* cutoff.  Its T_Match case is stable because T_Match pushes the       *)
(* InsLt-stable [push_match_bound] (see [InsLt_push_match_bound]).  This is the       *)
(* bind_lt case that [typing_SubstTm_eval_ctx] needs.                   *)
Lemma typing_InsLt : forall G t T, G ⊢ₜ t : T ->
  forall c G', InsLt c G G' -> G' ⊢ₜ shift_lt_in_tm 1 c t : shift_lt_in_ty 1 c T.
Proof.
  apply (typing_ind_forall2
    (fun G t T => forall c G', InsLt c G G' ->
      G' ⊢ₜ shift_lt_in_tm 1 c t : shift_lt_in_ty 1 c T)).
  - intros Γ x T Hlk Hwf c G' HIns. simpl.
    apply T_Var.
    + rewrite (InsLt_lookup_tm c Γ G' HIns x), Hlk. reflexivity.
    + wf_transport.
  - intros Γ t T U Ht IH Hsub c G' HIns. simpl.
    eapply T_Sub.
    + apply IH. exact HIns.
    + apply (sub_InsLt Γ T U Hsub c G' HIns).
  - intros Γ body A l B HwfA HwfB Hbody IHbody Hcap c G' HIns. simpl.
    apply T_Lam.
    + wf_transport.
    + wf_transport.
    + apply IHbody. apply InsLt_tm. exact HIns.
    + rewrite (capture_lt_InsLt c Γ G' HIns body).
      apply (lt_sub_InsLt Γ (capture_lt Γ body) l Hcap c G' HIns).
  - intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 c G' HIns. simpl.
    eapply T_App; [apply IH1|apply IH2]; exact HIns.
  - intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody c G' HIns. simpl.
    apply T_TyLam.
    + wf_transport.
    + eapply ty_wf_InsLt; [exact HwfT|]. apply InsLt_ty. exact HIns.
    + rewrite is_abs_shift_lt_in_tm. exact HisAbs.
    + apply IHbody. apply InsLt_ty. exact HIns.
  - intros Γ t B U S Ht IH HwfS Hsub c G' HIns. simpl.
    rewrite shift_lt_in_ty_subst_ty_comm.
    eapply T_TyApp.
    + apply IH. exact HIns.
    + wf_transport.
    + apply (sub_InsLt Γ S B Hsub c G' HIns).
  - intros Γ body T HwfT HisAbs Hbody IHbody c G' HIns. simpl.
    apply T_LtLam.
    + eapply ty_wf_InsLt; [exact HwfT|]. apply InsLt_lt. exact HIns.
    + rewrite is_abs_shift_lt_in_tm. exact HisAbs.
    + apply IHbody. apply InsLt_lt. exact HIns.
  - intros Γ t T l Ht IH Hwfl c G' HIns. simpl.
    rewrite shift_lt_in_ty_subst_lt_in_ty_bound0_comm.
    eapply T_LtApp.
    + apply IH. exact HIns.
    + wf_transport.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
           Hctor Heff Hlts Hwflts Hrho HTs HwfTs Hresult Hshape Hresult_eff Hwfl Hlt Hbounded Hlen Hargs IHargs c G' HIns.
    simpl. unfold map_shift_lt_in_ty.
    eapply T_Ctor with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := List.map (shift_lt_in_ty 1 (n_lt + c)) sigma_fields)
      (result_ty_schema := shift_lt_in_ty 1 (n_lt + c) result_ty_schema)
      (lts := List.map (shift_lt 1 c) lts)
      (Ts := List.map (shift_lt_in_ty 1 c) Ts)
      (rho_fields := List.map (shift_lt_in_ty 1 c) rho_fields)
      (result_tag := result_tag).
    + rewrite (InsLt_lookup_ctor c Γ G' HIns K). rewrite Hctor. reflexivity.
    + rewrite (InsLt_lookup_eff c Γ G' HIns K). rewrite Heff. reflexivity.
    + rewrite List.length_map. exact Hlts.
    + wf_transport.
    + rewrite Hrho. rewrite !List.map_map. apply List.map_ext. intro sigma.
      exact (eq_sym (inst_ctor_type_shift_lt n_lt n_ty lts Ts sigma c Hlts HTs)).
    + rewrite List.length_map. exact HTs.
    + wf_transport.
    + rewrite Hresult.
      exact (eq_sym (inst_ctor_type_shift_lt n_lt n_ty lts Ts result_ty_schema c Hlts HTs)).
    + rewrite Hshape. reflexivity.
    + rewrite (InsLt_lookup_eff c Γ G' HIns result_tag). rewrite Hresult_eff. reflexivity.
    + wf_transport.
    + rewrite (lt_of_ty_list_shift_lt rho_fields c).
      rewrite (lt_of_ty_shift_lt result_ty c).
      apply (lt_sub_InsLt Γ (lt_of_ty_list rho_fields) (lt_of_ty result_ty) Hlt c G' HIns).
    + exact (Forall_lt_sub_InsLt_map Γ lts l Hbounded c G' HIns).
    + rewrite !List.length_map. exact Hlen.
    + apply (typings_InsLt Γ vs rho_fields IHargs c G' HIns).
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γyes yes_body eta elim_result no_body
           HKne Hctor Heff Hlts Hrho HTs HwfTs Hscrut_result Hscrut_shape Hresult_eff Hresult_ne
           HwfDelta Hresult_l Hscrut IHscrut Harity HΓyes Hyes IHyes Helim Hno IHno c G' HIns.
    simpl. subst Γyes. unfold map_shift_lt_in_ty.
    eapply T_Match with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := List.map (shift_lt_in_ty 1 (n_lt + c)) sigma_fields)
      (result_ty_schema := shift_lt_in_ty 1 (n_lt + c) result_ty_schema)
      (lts := lts) (rho_fields := List.map (shift_lt_in_ty 1 (n_lt + c)) rho_fields)
      (scrut_result_ty := shift_lt_in_ty 1 c scrut_result_ty)
      (Delta := shift_lt 1 c Delta)
      (result_tag := result_tag) (result_l := shift_lt 1 c result_l)
      (Γ' := push_match_bound n_lt (shift_lt 1 c Delta) G')
      (eta := shift_lt_in_ty 1 (n_lt + c) eta).
    + exact HKne.
    + rewrite (InsLt_lookup_ctor c Γ G' HIns K). rewrite Hctor. reflexivity.
    + rewrite (InsLt_lookup_eff c Γ G' HIns K). rewrite Heff. reflexivity.
    + exact Hlts.
    + rewrite Hrho. rewrite !List.map_map. apply List.map_ext. intro sigma.
      exact (eq_sym (inst_ctor_type_open_shift_lt n_lt n_ty Ts sigma c HTs)).
    + rewrite List.length_map. exact HTs.
    + wf_transport.
    + rewrite Hscrut_result.
      rewrite <- (inst_ctor_type_shift_lt n_lt n_ty (List.repeat Delta n_lt) Ts result_ty_schema c
        (List.repeat_length Delta n_lt) HTs).
      rewrite List.map_repeat. reflexivity.
    + rewrite Hscrut_shape. reflexivity.
    + rewrite (InsLt_lookup_eff c Γ G' HIns result_tag). rewrite Hresult_eff. reflexivity.
    + exact Hresult_ne.
    + wf_transport.
    + apply (lt_sub_InsLt Γ result_l Delta Hresult_l c G' HIns).
    + apply IHscrut. exact HIns.
    + rewrite List.length_map. exact Harity.
    + reflexivity.
    + replace (n_lt + c) with (c + n_lt) by lia.
      apply IHyes.
      replace (c + n_lt) with (n_lt + c) by lia.
      apply InsLt_fold_bind_tm_map.
      apply InsLt_push_match_bound. exact HIns.
    + replace (shift_lt n_lt 0 (shift_lt 1 c Delta)) with
        (shift_lt 1 (n_lt + c) (shift_lt n_lt 0 Delta)).
      * apply elim_ty_n_shift_lt_above. exact Helim.
      * replace (n_lt + c) with (c + n_lt) by lia.
        apply shift_lt_lift_many_swap.
    + apply IHno. exact HIns.
  - intros Γ E_tag m Ts op_bodies n_α ops T_R
           Heff HTs HwfTs HwfTR Hfst Hops IHops c G' HIns.
    simpl. unfold map_shift_lt_in_ty.
    rewrite shift_lt_in_tm_ops_eq_map.
    eapply T_Cap with
      (n_α := n_α)
      (ops := List.map (fun osig =>
                 (op_nb osig,
                  shift_lt_in_ty 1 c (op_sig_ty osig),
                  shift_lt_in_ty 1 c (op_ret_ty osig))) ops)
      (T_R := shift_lt_in_ty 1 c T_R).
    + rewrite (InsLt_lookup_eff c Γ G' HIns E_tag). rewrite Heff. simpl.
      do 2 f_equal. apply List.map_ext. intros [[nβ sg] rt]. reflexivity.
    + rewrite List.length_map. exact HTs.
    + wf_transport.
    + wf_transport.
    + rewrite !List.map_map. exact Hfst.
    + clear Hops Heff. revert Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IHrest]; intros Hfst; simpl.
      * constructor.
      * simpl in Hfst. injection Hfst as Hnb Hfstrest.
        constructor; [| apply IHrest; exact Hfstrest ].
        destruct osig as [[nβ sg] rt].
        unfold op_nb, op_sig_ty, op_ret_ty in *. simpl in *.
        rewrite (inst_op_ty_args_shift_lt n_α Ts nβ sg c HTs).
        rewrite (inst_op_ty_args_shift_lt n_α Ts nβ rt c HTs).
        unfold op_body_ctx.
        rewrite !shift_ty_shift_lt_in_ty_commute.
        apply Hone. apply InsLt_tm. apply InsLt_tm. apply InsLt_push_ty_vars_any_at_free. exact HIns.
  - intros Γ E_tag Ts op_bodies body n_α ops T_B T_R
           Heff HTs HwfTs HwfTB HwfTR HnoLocal Hsub Hfst Hops IHops Hbody IHbody c G' HIns.
    simpl. unfold map_shift_lt_in_ty.
    rewrite shift_lt_in_tm_ops_eq_map.
    eapply T_Handle with
      (n_α := n_α)
      (ops := List.map (fun osig =>
                 (op_nb osig,
                  shift_lt_in_ty 1 c (op_sig_ty osig),
                  shift_lt_in_ty 1 c (op_ret_ty osig))) ops)
      (T_B := shift_lt_in_ty 1 c T_B) (T_R := shift_lt_in_ty 1 c T_R).
    + rewrite (InsLt_lookup_eff c Γ G' HIns E_tag). rewrite Heff. simpl.
      do 2 f_equal. apply List.map_ext. intros [[nβ sg] rt]. reflexivity.
    + rewrite List.length_map. exact HTs.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + apply (sub_InsLt Γ T_B T_R Hsub c G' HIns).
    + rewrite !List.map_map. exact Hfst.
    + clear Hops Heff. revert Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IHrest]; intros Hfst; simpl.
      * constructor.
      * simpl in Hfst. injection Hfst as Hnb Hfstrest.
        constructor; [| apply IHrest; exact Hfstrest ].
        destruct osig as [[nβ sg] rt].
        unfold op_nb, op_sig_ty, op_ret_ty in *. simpl in *.
        rewrite (inst_op_ty_args_shift_lt n_α Ts nβ sg c HTs).
        rewrite (inst_op_ty_args_shift_lt n_α Ts nβ rt c HTs).
        unfold op_body_ctx.
        rewrite !shift_ty_shift_lt_in_ty_commute.
        apply Hone. apply InsLt_tm. apply InsLt_tm. apply InsLt_push_ty_vars_any_at_free. exact HIns.
    + apply IHbody. apply InsLt_tm. exact HIns.
  - intros Γ recv op arg E_tag Delta Ts Ss n_α ops n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hnth HTs HSs HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg c G' HIns.
    simpl. unfold map_shift_lt_in_ty.
    eapply T_Perform with
      (n_α := n_α)
      (ops := List.map (fun osig =>
                 (op_nb osig,
                  shift_lt_in_ty 1 c (op_sig_ty osig),
                  shift_lt_in_ty 1 c (op_ret_ty osig))) ops)
      (n_β := n_β)
      (sig := shift_lt_in_ty 1 c sig) (ret := shift_lt_in_ty 1 c ret)
      (sig_inst := shift_lt_in_ty 1 c sig_inst) (ret_inst := shift_lt_in_ty 1 c ret_inst).
    + apply IHrecv. exact HIns.
    + rewrite (InsLt_lookup_eff c Γ G' HIns E_tag). rewrite Heff. simpl.
      do 2 f_equal. apply List.map_ext. intros [[nβ sg] rt]. reflexivity.
    + rewrite (map_nth_error _ _ _ Hnth). reflexivity.
    + rewrite List.length_map. exact HTs.
    + rewrite List.length_map. exact HSs.
    + wf_transport.
    + wf_transport.
    + rewrite Hsig. symmetry. apply inst_op_all_args_shift_lt; assumption.
    + wf_transport.
    + rewrite Hret. symmetry. apply inst_op_all_args_shift_lt; assumption.
    + wf_transport.
    + apply IHarg. exact HIns.
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH c G' HIns. simpl.
    apply T_HandlerM.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + apply (sub_InsLt Γ T_B T_R Hsub c G' HIns).
    + apply IH. exact HIns.
Qed.

Lemma shift_lt_in_ty_subst_ty_comm0 : forall T n Sb,
  shift_lt_in_ty 1 0 (subst_ty n Sb T)
  = subst_ty n (shift_lt_in_ty 1 0 Sb) (shift_lt_in_ty 1 0 T).
Proof. intros. apply shift_lt_in_ty_subst_ty_comm. Qed.


Lemma subst_lt_in_ty_subst_ty_comm : forall T l R n Sb,
  subst_lt_in_ty l R (subst_ty n Sb T) =
  subst_ty n (subst_lt_in_ty l R Sb) (subst_lt_in_ty l R T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall l R n Sb,
       subst_lt_in_ty l R (subst_ty n Sb T) =
       subst_ty n (subst_lt_in_ty l R Sb) (subst_lt_in_ty l R T))
    (fun Ts => forall l R n Sb,
       List.map (subst_lt_in_ty l R) (List.map (subst_ty n Sb) Ts) =
       List.map (subst_ty n (subst_lt_in_ty l R Sb))
                (List.map (subst_lt_in_ty l R) Ts))).
  - intros m l R n Sb.
    rewrite subst_ty_var_eq, subst_lt_in_ty_var_eq, subst_ty_var_eq.
    destruct (Nat.eqb m n); destruct (Nat.ltb n m); reflexivity.
  - intros A lt B HA HB l R n Sb.
    rewrite subst_ty_fun_eq, !subst_lt_in_ty_fun_eq, subst_ty_fun_eq.
    rewrite HA, HB. reflexivity.
  - intros K lt Ts HTs l R n Sb.
    rewrite subst_ty_ctor_eq, !subst_lt_in_ty_ctor_eq, subst_ty_ctor_eq.
    f_equal. apply HTs.
  - intros A HA l R n Sb.
    rewrite subst_ty_ltall_eq, !subst_lt_in_ty_ltall_eq, subst_ty_ltall_eq.
    f_equal. rewrite HA. f_equal. symmetry. apply shift_lt_in_ty_subst_lt_in_ty_comm0.
  - intros B A HB HA l R n Sb.
    rewrite subst_ty_tyall_eq, !subst_lt_in_ty_tyall_eq, subst_ty_tyall_eq.
    rewrite HB. f_equal. rewrite HA. f_equal. symmetry. apply shift_ty_subst_lt_in_ty_commute.
  - intros l R n Sb. reflexivity.
  - intros A Ts HA HTs l R n Sb.
    cbn [List.map]. rewrite HA. f_equal. apply HTs.
Qed.

Lemma inst_ty_vars_subst_lt : forall n Ts T l R,
  inst_ty_vars n (List.map (subst_lt_in_ty l R) Ts) (subst_lt_in_ty l R T) =
  subst_lt_in_ty l R (inst_ty_vars n Ts T).
Proof.
  induction n as [|n IH]; intros Ts T l R.
  - destruct Ts as [|U rest]; reflexivity.
  - destruct Ts as [|U rest]; simpl.
    + reflexivity.
    + rewrite <- IH.
      rewrite subst_lt_in_ty_subst_ty_comm.
      rewrite shift_ty_subst_lt_in_ty_commute.
      reflexivity.
Qed.

Lemma inst_op_ty_args_subst_lt : forall n_α Ts n_β T l R,
  inst_op_ty_args n_α (List.map (subst_lt_in_ty l R) Ts) n_β (subst_lt_in_ty l R T) =
  subst_lt_in_ty l R (inst_op_ty_args n_α Ts n_β T).
Proof.
  intros n_α Ts n_β T l R. unfold inst_op_ty_args.
  rewrite <- inst_ty_vars_subst_lt.
  f_equal.
  induction Ts as [|T0 Ts IH]; simpl.
  - reflexivity.
  - rewrite shift_ty_subst_lt_in_ty_commute. f_equal. exact IH.
Qed.

Lemma inst_op_all_args_subst_lt : forall n_α Ts n_β Ss T l R,
  inst_op_all_args n_α (List.map (subst_lt_in_ty l R) Ts)
              n_β (List.map (subst_lt_in_ty l R) Ss)
              (subst_lt_in_ty l R T) =
  subst_lt_in_ty l R (inst_op_all_args n_α Ts n_β Ss T).
Proof.
  intros n_α Ts n_β Ss T l R. unfold inst_op_all_args.
  rewrite <- inst_ty_vars_subst_lt.
  rewrite inst_op_ty_args_subst_lt.
  reflexivity.
Qed.


Lemma inst_ctor_type_subst_lt : forall n_lt n_ty lts Ts T l R,
  List.length lts = n_lt ->
  inst_ctor_type n_lt n_ty (List.map (subst_lt l R) lts)
                 (List.map (subst_lt_in_ty l R) Ts)
                 (subst_lt_in_ty (n_lt + l) (shift_lt n_lt 0 R) T) =
  subst_lt_in_ty l R (inst_ctor_type n_lt n_ty lts Ts T).
Proof.
  intros n_lt n_ty lts Ts T l R Hlen.
  unfold inst_ctor_type, inst_lt_vars.
  rewrite map_shift_lt_in_ty_subst_lt_in_ty_comm_many0.
  rewrite inst_ty_vars_subst_lt.
  rewrite multi_subst_lt_in_ty_subst_lt_comm with (k := n_lt) (lts := lts) by exact Hlen.
  replace (0 + l) with l by lia.
  rewrite shift_lt_zero.
  reflexivity.
Qed.

(* lt-substitution commutes with [inst_ctor_type_open] (the match       *)
(* field-type instantiation): substituting at the outer index [l] of    *)
(* [Ts] corresponds to substituting at [n_lt + l] (under the n_lt match  *)
(* lt-binders, with R lifted) in the body/result.  No [lts] argument and *)
(* no [multi_subst] step (unlike [inst_ctor_type_subst_lt]) — this is    *)
(* exactly what the GENERAL [typing_SubstLt] T_Match case needs.         *)
Lemma inst_ctor_type_open_subst_lt : forall n_lt n_ty Ts T l R,
  inst_ctor_type_open n_lt n_ty
                 (List.map (subst_lt_in_ty l R) Ts)
                 (subst_lt_in_ty (n_lt + l) (shift_lt n_lt 0 R) T) =
  subst_lt_in_ty (n_lt + l) (shift_lt n_lt 0 R) (inst_ctor_type_open n_lt n_ty Ts T).
Proof.
  intros n_lt n_ty Ts T l R.
  unfold inst_ctor_type_open.
  rewrite map_shift_lt_in_ty_subst_lt_in_ty_comm_many0.
  rewrite inst_ty_vars_subst_lt.
  reflexivity.
Qed.
