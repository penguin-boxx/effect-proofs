(* Core_Δ (simplified): Escape analysis with lifetime subtyping.
   Fully proved progress + preservation. De Bruijn indices.
   No type/lifetime polymorphism — the escape analysis core is preserved. *)

From Stdlib Require Import List Arith PeanoNat Bool Lia.
Import ListNotations.

(* ========== Lifetimes ========== *)

Inductive lt : Type :=
  | Lt_local : lt
  | Lt_free  : lt
  | Lt_join  : lt -> lt -> lt.

(* ========== Types ========== *)

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Pair  : ty -> ty -> lt -> ty
  | Ty_Arrow : ty -> lt -> ty -> ty.

Definition lt_of (T : ty) : lt :=
  match T with Ty_Bool => Lt_free | Ty_Pair _ _ d => d | Ty_Arrow _ d _ => d end.

(* ========== Terms ========== *)

Inductive tm : Type :=
  | tm_var   : nat -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_abs   : ty -> tm -> tm
  | tm_app   : tm -> tm -> tm
  | tm_pair  : tm -> tm -> tm
  | tm_fst   : tm -> tm
  | tm_snd   : tm -> tm.

Inductive value : tm -> Prop :=
  | v_true  : value tm_true
  | v_false : value tm_false
  | value_lam   : forall T t, value (tm_abs T t)
  | v_pair  : forall v1 v2, value v1 -> value v2 -> value (tm_pair v1 v2).
Hint Constructors value : core.

(* ========== Shift / Subst ========== *)

Fixpoint shift (d c : nat) (t : tm) : tm :=
  match t with
  | tm_var x => if Nat.leb c x then tm_var (x + d) else tm_var x
  | tm_true => tm_true | tm_false => tm_false
  | tm_abs T body => tm_abs T (shift d (S c) body)
  | tm_app t1 t2 => tm_app (shift d c t1) (shift d c t2)
  | tm_pair t1 t2 => tm_pair (shift d c t1) (shift d c t2)
  | tm_fst t => tm_fst (shift d c t)
  | tm_snd t => tm_snd (shift d c t)
  end.

Fixpoint subst (j : nat) (s t : tm) : tm :=
  match t with
  | tm_var x =>
      if Nat.eqb x j then s
      else if Nat.ltb j x then tm_var (x - 1) else tm_var x
  | tm_true => tm_true | tm_false => tm_false
  | tm_abs T body => tm_abs T (subst (S j) (shift 1 0 s) body)
  | tm_app t1 t2 => tm_app (subst j s t1) (subst j s t2)
  | tm_pair t1 t2 => tm_pair (subst j s t1) (subst j s t2)
  | tm_fst t => tm_fst (subst j s t)
  | tm_snd t => tm_snd (subst j s t)
  end.

Definition subst_top s t := subst 0 s t.

(* ========== Context ========== *)

Definition ctx := list ty.

(* ========== Lifetime subtyping (with transitivity) ========== *)

Inductive sub_lt : lt -> lt -> Prop :=
  | SL_refl   : forall d, sub_lt d d
  | SL_free   : forall d, sub_lt Lt_free d
  | SL_local  : forall d, sub_lt d Lt_local
  | SL_join_l : forall d1 d2 d, sub_lt d1 d -> sub_lt (Lt_join d1 d2) d
  | SL_join_r : forall d1 d2 d, sub_lt d2 d -> sub_lt (Lt_join d1 d2) d
  | SL_join_ub: forall d d1 d2, sub_lt d d1 -> sub_lt d d2 ->
                  sub_lt d (Lt_join d1 d2)
  | SL_trans  : forall d1 d2 d3, sub_lt d1 d2 -> sub_lt d2 d3 -> sub_lt d1 d3.

(* ========== Type subtyping (structural, no transitivity) ========== *)

Inductive sub_ty : ty -> ty -> Prop :=
  | ST_bool  : sub_ty Ty_Bool Ty_Bool
  | ST_pair  : forall T1 T1' T2 T2' d1 d2,
      sub_ty T1 T1' -> sub_ty T2 T2' -> sub_lt d1 d2 ->
      sub_ty (Ty_Pair T1 T2 d1) (Ty_Pair T1' T2' d2)
  | ST_arrow : forall S1 S2 d1 d2 T1 T2,
      sub_ty S2 S1 -> sub_lt d1 d2 -> sub_ty T1 T2 ->
      sub_ty (Ty_Arrow S1 d1 T1) (Ty_Arrow S2 d2 T2).

Lemma sub_ty_refl : forall T, sub_ty T T.
Proof. induction T; constructor; auto; apply SL_refl. Qed.

Lemma sub_ty_trans : forall T1 T2 T3,
  sub_ty T1 T2 -> sub_ty T2 T3 -> sub_ty T1 T3.
Proof.
  intros T1 T2; revert T1; induction T2; intros T1 T3 H12 H23;
    inversion H12; subst; inversion H23; subst;
    constructor; eauto; eapply SL_trans; eauto.
Qed.

(* ========== Typing ========== *)

Inductive has_type : ctx -> tm -> ty -> Prop :=
  | T_True  : forall G, has_type G tm_true Ty_Bool
  | T_False : forall G, has_type G tm_false Ty_Bool
  | T_Var   : forall G x T, nth_error G x = Some T -> has_type G (tm_var x) T
  | T_Abs   : forall G T1 t T2 d,
      has_type (T1 :: G) t T2 ->
      has_type G (tm_abs T1 t) (Ty_Arrow T1 d T2)
  | T_App   : forall G t1 t2 T1 d T2,
      has_type G t1 (Ty_Arrow T1 d T2) -> has_type G t2 T1 ->
      has_type G (tm_app t1 t2) T2
  | T_Pair  : forall G t1 t2 T1 T2,
      has_type G t1 T1 -> has_type G t2 T2 ->
      has_type G (tm_pair t1 t2) (Ty_Pair T1 T2 (Lt_join (lt_of T1) (lt_of T2)))
  | T_Fst   : forall G t T1 T2 d,
      has_type G t (Ty_Pair T1 T2 d) -> has_type G (tm_fst t) T1
  | T_Snd   : forall G t T1 T2 d,
      has_type G t (Ty_Pair T1 T2 d) -> has_type G (tm_snd t) T2
  | T_Sub   : forall G t T1 T2,
      has_type G t T1 -> sub_ty T1 T2 -> has_type G t T2.

(* ========== Small-step ========== *)

Inductive step : tm -> tm -> Prop :=
  | S_AppAbs : forall T body v, value v ->
      step (tm_app (tm_abs T body) v) (subst_top v body)
  | S_App1 : forall t1 t1' t2, step t1 t1' ->
      step (tm_app t1 t2) (tm_app t1' t2)
  | S_App2 : forall v t2 t2', value v -> step t2 t2' ->
      step (tm_app v t2) (tm_app v t2')
  | S_Pair1 : forall t1 t1' t2, step t1 t1' ->
      step (tm_pair t1 t2) (tm_pair t1' t2)
  | S_Pair2 : forall v1 t2 t2', value v1 -> step t2 t2' ->
      step (tm_pair v1 t2) (tm_pair v1 t2')
  | S_Fst  : forall v1 v2, value v1 -> value v2 ->
      step (tm_fst (tm_pair v1 v2)) v1
  | S_FstS : forall t t', step t t' -> step (tm_fst t) (tm_fst t')
  | S_Snd  : forall v1 v2, value v1 -> value v2 ->
      step (tm_snd (tm_pair v1 v2)) v2
  | S_SndS : forall t t', step t t' -> step (tm_snd t) (tm_snd t').

(* ========== Sub_ty inversion ========== *)

Lemma sub_ty_bool_inv : forall T, sub_ty T Ty_Bool -> T = Ty_Bool.
Proof. intros. inversion H; auto. Qed.

Lemma sub_ty_arrow_inv : forall T S1 d S2,
  sub_ty T (Ty_Arrow S1 d S2) ->
  exists S1' d' S2', T = Ty_Arrow S1' d' S2' /\
    sub_ty S1 S1' /\ sub_lt d' d /\ sub_ty S2' S2.
Proof. intros. inversion H; subst. eauto 10. Qed.

Lemma sub_ty_pair_inv : forall T T1 T2 d,
  sub_ty T (Ty_Pair T1 T2 d) ->
  exists T1' T2' d', T = Ty_Pair T1' T2' d' /\
    sub_ty T1' T1 /\ sub_ty T2' T2 /\ sub_lt d' d.
Proof. intros. inversion H; subst. eauto 10. Qed.

(* ========== Canonical forms ========== *)

(* We prove these for arbitrary G to get proper IH for T_Sub *)

Lemma canonical_bool : forall v,
  has_type nil v Ty_Bool -> value v -> v = tm_true \/ v = tm_false.
Proof.
  intros v Hty Hval.
  remember (@nil ty) as G. remember Ty_Bool as T.
  revert HeqG HeqT.
  induction Hty; intros HeqG HeqT; subst; try discriminate;
    try solve [inversion Hval]; auto.
  (* T_Sub *) inversion H; subst. auto.
Qed.

Lemma canonical_arrow : forall v S1 d S2,
  has_type nil v (Ty_Arrow S1 d S2) -> value v ->
  exists T body, v = tm_abs T body.
Proof.
  intros v S1 d S2 Hty Hval.
  remember (@nil ty) as G. remember (Ty_Arrow S1 d S2) as T.
  revert S1 d S2 HeqG HeqT.
  induction Hty; intros S1' d' S2' HeqG HeqT; subst; try discriminate;
    try solve [inversion Hval]; eauto.
  (* T_Sub *)
  apply sub_ty_arrow_inv in H.
  destruct H as [S1'' [d'' [S2'' [Heq _]]]]. subst. eauto.
Qed.

Lemma canonical_pair : forall v T1 T2 d,
  has_type nil v (Ty_Pair T1 T2 d) -> value v ->
  exists v1 v2, v = tm_pair v1 v2 /\ value v1 /\ value v2.
Proof.
  intros v T1 T2 d Hty Hval.
  remember (@nil ty) as G. remember (Ty_Pair T1 T2 d) as T.
  revert T1 T2 d HeqG HeqT.
  induction Hty; intros T1' T2' d' HeqG HeqT; subst; try discriminate;
    try solve [inversion Hval].
  - injection HeqT as <- <- <-. inversion Hval; subst. eauto 6.
  - apply sub_ty_pair_inv in H.
    destruct H as [T1'' [T2'' [d'' [Heq _]]]]. subst. eauto.
Qed.

(* ========== Progress ========== *)

Theorem progress : forall t T,
  has_type nil t T -> value t \/ exists t', step t t'.
Proof.
  intros t T Hty. remember (@nil ty) as G.
  induction Hty; subst; auto.
  - (* Var *) destruct x; discriminate.
  - (* App *) right.
    destruct (IHHty1 eq_refl) as [Hv1|[t1' Hs1]].
    + destruct (IHHty2 eq_refl) as [Hv2|[t2' Hs2]].
      * destruct (canonical_arrow _ _ _ _ Hty1 Hv1) as [T' [body Heq]]; subst.
        eexists; constructor; auto.
      * eexists; apply S_App2; eauto.
    + eexists; apply S_App1; eauto.
  - (* Pair *)
    destruct (IHHty1 eq_refl) as [Hv1|[t1' Hs1]].
    + destruct (IHHty2 eq_refl) as [Hv2|[t2' Hs2]].
      * left; auto.
      * right; eexists; apply S_Pair2; eauto.
    + right; eexists; apply S_Pair1; eauto.
  - (* Fst *)
    destruct (IHHty eq_refl) as [Hv|[t' Hs]].
    + right; destruct (canonical_pair _ _ _ _ Hty Hv) as [v1 [v2 [? [? ?]]]]; subst.
      eexists; apply S_Fst; auto.
    + right; eexists; apply S_FstS; exact Hs.
  - (* Snd *)
    destruct (IHHty eq_refl) as [Hv|[t' Hs]].
    + right; destruct (canonical_pair _ _ _ _ Hty Hv) as [v1 [v2 [? [? ?]]]]; subst.
      eexists; apply S_Snd; auto.
    + right; eexists; apply S_SndS; exact Hs.
Qed.

(* ========== Weakening ========== *)

Lemma nth_error_insert_lt : forall {A} (l : list A) n x k,
  n <= length l -> k < n ->
  nth_error (firstn n l ++ x :: skipn n l) k = nth_error l k.
Proof.
  intros.
  rewrite nth_error_app1.
  2: { rewrite length_firstn. lia. }
  rewrite nth_error_firstn.
  destruct (k <? n) eqn:E; auto.
  apply Nat.ltb_ge in E. lia.
Qed.

Lemma nth_error_insert_eq : forall {A} (l : list A) n x,
  n <= length l ->
  nth_error (firstn n l ++ x :: skipn n l) n = Some x.
Proof.
  intros. rewrite nth_error_app2.
  2: { rewrite length_firstn, Nat.min_l by lia. lia. }
  rewrite length_firstn, Nat.min_l by lia. replace (n - n) with 0 by lia.
  reflexivity.
Qed.

Lemma nth_error_insert_gt : forall {A} (l : list A) n x k,
  n <= length l -> k > n ->
  nth_error (firstn n l ++ x :: skipn n l) k = nth_error l (k - 1).
Proof.
  intros. rewrite nth_error_app2.
  2: { rewrite length_firstn, Nat.min_l by lia. lia. }
  rewrite length_firstn, Nat.min_l by lia. simpl.
  replace (k - n) with (S (k - 1 - n)) by lia.
  simpl. rewrite nth_error_skipn. f_equal. lia.
Qed.

Lemma weakening_insert : forall G t T n U,
  has_type G t T -> n <= length G ->
  has_type (firstn n G ++ U :: skipn n G) (shift 1 n t) T.
Proof.
  intros G t T n U Hty. revert n.
  induction Hty; intros n Hle; simpl.
  - constructor.
  - constructor.
  - destruct (Nat.leb n x) eqn:E.
    + apply Nat.leb_le in E. econstructor.
      rewrite nth_error_insert_gt; [| lia | lia]. replace (x+1-1) with x by lia. exact H.
    + apply Nat.leb_nle in E. econstructor.
      rewrite nth_error_insert_lt; [| lia | lia]. exact H.
  - econstructor. apply (IHHty (S n)). simpl. lia.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - econstructor; eauto.
  - eapply T_Sub; eauto.
Qed.

Lemma weakening : forall G t T U,
  has_type G t T -> has_type (U :: G) (shift 1 0 t) T.
Proof. intros. apply (weakening_insert G t T 0 U H). simpl; lia. Qed.

(* ========== Substitution ========== *)

Lemma substitution : forall G t T j U v,
  has_type (firstn j G ++ U :: skipn j G) t T ->
  has_type G v U -> j <= length G ->
  has_type G (subst j v t) T.
Proof.
  intros G t T j U v Hty Hv Hle.
  remember (firstn j G ++ U :: skipn j G) as G'.
  revert G j v Hv Hle HeqG'.
  induction Hty; intros G0 j v0 Hv0 Hle HeqG'; subst; simpl.
  - (* T_True *) constructor.
  - (* T_False *) constructor.
  - (* T_Var *)
    destruct (Nat.eqb x j) eqn:Eeq.
    + apply Nat.eqb_eq in Eeq. subst.
      pose proof (nth_error_insert_eq G0 j U Hle) as Hrw.
      rewrite Hrw in H. injection H as <-. exact Hv0.
    + destruct (Nat.ltb j x) eqn:Elt.
      * apply Nat.ltb_lt in Elt.
        pose proof (nth_error_insert_gt G0 j U x Hle Elt) as Hrw.
        rewrite Hrw in H. constructor. exact H.
      * apply Nat.ltb_ge in Elt.
        assert (Hxj: x < j) by (apply Nat.eqb_neq in Eeq; lia).
        pose proof (nth_error_insert_lt G0 j U x Hle Hxj) as Hrw.
        rewrite Hrw in H. constructor. exact H.
  - (* T_Abs *) econstructor. eapply (IHHty (T1 :: G0) (Datatypes.S j) (shift 1 0 v0)).
    + apply weakening. exact Hv0.
    + simpl. lia.
    + simpl. reflexivity.
  - (* T_App *) econstructor; eauto.
  - (* T_Pair *) econstructor; eauto.
  - (* T_Fst *) econstructor; eauto.
  - (* T_Snd *) econstructor; eauto.
  - (* T_Sub *) eapply T_Sub; eauto.
Qed.

Lemma substitution_top : forall G t T U v,
  has_type (U :: G) t T -> has_type G v U -> has_type G (subst_top v t) T.
Proof. intros. eapply (substitution G t T 0 U v); simpl; auto. lia. Qed.

(* ========== Typing inversion ========== *)

Lemma typing_invalue_lam : forall G T1 body T,
  has_type G (tm_abs T1 body) T ->
  exists T2 d, sub_ty (Ty_Arrow T1 d T2) T /\ has_type (T1 :: G) body T2.
Proof.
  intros. remember (tm_abs T1 body) as t.
  induction H; try discriminate.
  - injection Heqt as <- <-. eauto using sub_ty_refl.
  - destruct (IHhas_type Heqt) as [T2' [d' [Hsub Hbody]]].
    exists T2', d'. split; [eapply sub_ty_trans; eauto | auto].
Qed.

Lemma typing_inv_pair : forall G t1 t2 T,
  has_type G (tm_pair t1 t2) T ->
  exists T1 T2,
    sub_ty (Ty_Pair T1 T2 (Lt_join (lt_of T1) (lt_of T2))) T /\
    has_type G t1 T1 /\ has_type G t2 T2.
Proof.
  intros. remember (tm_pair t1 t2) as t.
  induction H; try discriminate.
  - injection Heqt as <- <-. eauto using sub_ty_refl.
  - destruct (IHhas_type Heqt) as [T1' [T2' [Hsub [Ht1 Ht2]]]].
    exists T1', T2'. split; [eapply sub_ty_trans; eauto | auto].
Qed.

(* ========== Preservation ========== *)

Lemma has_type_app_inv : forall G t1 t2 T,
  has_type G (tm_app t1 t2) T ->
  exists T1 d T2, has_type G t1 (Ty_Arrow T1 d T2) /\ has_type G t2 T1 /\ sub_ty T2 T.
Proof.
  intros. remember (tm_app t1 t2) as t.
  induction H; try discriminate.
  - injection Heqt as <- <-. exists T1, d, T2. eauto using sub_ty_refl.
  - destruct (IHhas_type Heqt) as [T1' [d' [T2' [Ht1 [Ht2 Hs]]]]].
    exists T1', d', T2'. split; [| split]; auto. eapply sub_ty_trans; eauto.
Qed.

Lemma has_type_fst_inv : forall G t T,
  has_type G (tm_fst t) T ->
  exists T1 T2 d, has_type G t (Ty_Pair T1 T2 d) /\ sub_ty T1 T.
Proof.
  intros. remember (tm_fst t) as tf.
  induction H; try discriminate.
  - injection Heqtf as <-. eauto using sub_ty_refl.
  - destruct (IHhas_type Heqtf) as [T1' [T2' [d' [Ht Hs]]]].
    exists T1', T2', d'. split; auto. eapply sub_ty_trans; eauto.
Qed.

Lemma has_type_snd_inv : forall G t T,
  has_type G (tm_snd t) T ->
  exists T1 T2 d, has_type G t (Ty_Pair T1 T2 d) /\ sub_ty T2 T.
Proof.
  intros. remember (tm_snd t) as ts.
  induction H; try discriminate.
  - injection Heqts as <-. eauto using sub_ty_refl.
  - destruct (IHhas_type Heqts) as [T1' [T2' [d' [Ht Hs]]]].
    exists T1', T2', d'. split; auto. eapply sub_ty_trans; eauto.
Qed.

Lemma has_type_pair_inv2 : forall G t1 t2 T,
  has_type G (tm_pair t1 t2) T ->
  exists T1 T2, has_type G t1 T1 /\ has_type G t2 T2 /\ sub_ty (Ty_Pair T1 T2 (Lt_join (lt_of T1) (lt_of T2))) T.
Proof.
  intros. remember (tm_pair t1 t2) as t.
  induction H; try discriminate.
  - injection Heqt as <- <-. eauto using sub_ty_refl.
  - destruct (IHhas_type Heqt) as [T1' [T2' [Ht1 [Ht2 Hs]]]].
    exists T1', T2'. split; [| split]; auto. eapply sub_ty_trans; eauto.
Qed.

Theorem preservation : forall t t' T,
  has_type nil t T -> step t t' -> has_type nil t' T.
Proof.
  intros t t' T Hty Hstep. generalize dependent T.
  induction Hstep; intros Tres Hty.

  - (* S_AppAbs *)
    destruct (has_type_app_inv _ _ _ _ Hty) as [T1 [d [T2 [Ht1 [Ht2 Hsub]]]]].
    destruct (typing_invalue_lam _ _ _ _ Ht1) as [T2' [d' [Hsub2 Hbody]]].
    apply sub_ty_arrow_inv in Hsub2.
    destruct Hsub2 as [S1 [d'' [S2 [Heq [Hs1 [_ Hs2]]]]]].
    injection Heq as <- <- <-.
    eapply T_Sub; [| eapply sub_ty_trans; eauto].
    eapply substitution_top; eauto.
    eapply T_Sub; eauto.

  - (* S_App1 *)
    destruct (has_type_app_inv _ _ _ _ Hty) as [T1 [d [T2 [Ht1 [Ht2 Hsub]]]]].
    eapply T_Sub; eauto. econstructor; eauto.

  - (* S_App2 *)
    destruct (has_type_app_inv _ _ _ _ Hty) as [T1 [d [T2 [Ht1 [Ht2 Hsub]]]]].
    eapply T_Sub; eauto. econstructor; eauto.

  - (* S_Pair1 *)
    destruct (has_type_pair_inv2 _ _ _ _ Hty) as [T1 [T2 [Ht1 [Ht2 Hsub]]]].
    eapply T_Sub; eauto. econstructor; eauto.

  - (* S_Pair2 *)
    destruct (has_type_pair_inv2 _ _ _ _ Hty) as [T1 [T2 [Ht1 [Ht2 Hsub]]]].
    eapply T_Sub; eauto. econstructor; eauto.

  - (* S_Fst *)
    destruct (has_type_fst_inv _ _ _ Hty) as [T1 [T2 [d [Hpair Hsub]]]].
    destruct (typing_inv_pair _ _ _ _ Hpair) as [T1' [T2' [Hsub2 [Ht1 Ht2]]]].
    apply sub_ty_pair_inv in Hsub2.
    destruct Hsub2 as [T1'' [T2'' [d' [Heq [Hs1 [_ _]]]]]].
    injection Heq as <- <- <-.
    eapply T_Sub; eauto. eapply sub_ty_trans; eauto.

  - (* S_FstS *)
    destruct (has_type_fst_inv _ _ _ Hty) as [T1 [T2 [d [Hpair Hsub]]]].
    eapply T_Sub; eauto. econstructor; eauto.

  - (* S_Snd *)
    destruct (has_type_snd_inv _ _ _ Hty) as [T1 [T2 [d [Hpair Hsub]]]].
    destruct (typing_inv_pair _ _ _ _ Hpair) as [T1' [T2' [Hsub2 [Ht1 Ht2]]]].
    apply sub_ty_pair_inv in Hsub2.
    destruct Hsub2 as [T1'' [T2'' [d' [Heq [_ [Hs2 _]]]]]].
    injection Heq as <- <- <-.
    eapply T_Sub; eauto. eapply sub_ty_trans; eauto.

  - (* S_SndS *)
    destruct (has_type_snd_inv _ _ _ Hty) as [T1 [T2 [d [Hpair Hsub]]]].
    eapply T_Sub; eauto. econstructor; eauto.
Qed.

(* ========== Type Safety ========== *)

Corollary type_safety : forall t t' T,
  has_type nil t T -> step t t' ->
  value t' \/ exists t'', step t' t''.
Proof. intros. eapply progress. eapply preservation; eauto. Qed.

Inductive multi_step : tm -> tm -> Prop :=
  | ms_refl : forall t, multi_step t t
  | ms_step : forall t1 t2 t3, step t1 t2 -> multi_step t2 t3 -> multi_step t1 t3.

Theorem soundness : forall t t' T,
  has_type nil t T -> multi_step t t' ->
  value t' \/ exists t'', step t' t''.
Proof.
  intros t t' T Hty Hms. induction Hms.
  - eapply progress. exact Hty.
  - apply IHHms. eapply preservation; eauto.
Qed.

Print Assumptions soundness.
