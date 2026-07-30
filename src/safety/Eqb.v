Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Import ListNotations.
Require Import Syntax.
Require Import ShiftLaws.

(* ================================================================== *)
(* Boolean equality on lifetimes and types, with its spec lemmas.     *)
(*                                                                    *)
(* Shared by the certified evaluator (Stepf.v: H_Perform only fires   *)
(* when the capability's answer-type annotation coincides             *)
(* syntactically with the delimiter's T_R), the reflected deciders    *)
(* (Decide.v), and the determinism development (Determinism.v).       *)
(* ================================================================== *)

Fixpoint lt_eqb (l1 l2 : lifetime) : bool :=
  match l1, l2 with
  | lt_var n1, lt_var n2 => Nat.eqb n1 n2
  | lt_free, lt_free => true
  | lt_local, lt_local => true
  | lt_join a1 b1, lt_join a2 b2 => andb (lt_eqb a1 a2) (lt_eqb b1 b2)
  | _, _ => false
  end.

Lemma lt_eqb_eq : forall l1 l2, lt_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [n| | |a IHa b IHb]; destruct l2; simpl; intros H;
    try discriminate H; try reflexivity.
  - apply Nat.eqb_eq in H. subst. reflexivity.
  - apply Bool.andb_true_iff in H as [H1 H2].
    rewrite (IHa _ H1), (IHb _ H2). reflexivity.
Qed.

Lemma lt_eqb_refl : forall l, lt_eqb l l = true.
Proof.
  induction l; simpl.
  - apply Nat.eqb_refl.
  - reflexivity.
  - reflexivity.
  - rewrite IHl1, IHl2. reflexivity.
Qed.

Lemma lt_eqb_spec : forall a b, reflect (a = b) (lt_eqb a b).
Proof.
  induction a; destruct b; simpl;
    try (apply ReflectF; discriminate).
  - destruct (Nat.eqb_spec n n0); constructor; congruence.
  - apply ReflectT; reflexivity.
  - apply ReflectT; reflexivity.
  - destruct (IHa1 b1); [destruct (IHa2 b2)|];
      constructor; congruence.
Qed.

Fixpoint ty_eqb (T1 T2 : type) : bool :=
  let fix go (Ts1 Ts2 : list type) : bool :=
    match Ts1, Ts2 with
    | [], [] => true
    | A :: r1, B :: r2 => andb (ty_eqb A B) (go r1 r2)
    | _, _ => false
    end
  in
  match T1, T2 with
  | type_var n1, type_var n2 => Nat.eqb n1 n2
  | type_fun A1 l1 B1, type_fun A2 l2 B2 =>
      andb (ty_eqb A1 A2) (andb (lt_eqb l1 l2) (ty_eqb B1 B2))
  | type_ctor K1 l1 Ts1, type_ctor K2 l2 Ts2 =>
      andb (Nat.eqb K1 K2) (andb (lt_eqb l1 l2) (go Ts1 Ts2))
  | type_lt_all A1, type_lt_all A2 => ty_eqb A1 A2
  | type_ty_all B1 A1, type_ty_all B2 A2 =>
      andb (ty_eqb B1 B2) (ty_eqb A1 A2)
  | _, _ => false
  end.

Fixpoint ty_list_eqb (Ts1 Ts2 : list type) : bool :=
  match Ts1, Ts2 with
  | [], [] => true
  | A :: r1, B :: r2 => andb (ty_eqb A B) (ty_list_eqb r1 r2)
  | _, _ => false
  end.

(* go_eq bridge for ty_eqb's inline list fix (cf. the go_ops bridges in ShiftLaws.v). *)
Lemma ty_eqb_go_eq : forall Ts1 Ts2,
  (fix go (Ts1 Ts2 : list type) : bool :=
     match Ts1, Ts2 with
     | [], [] => true
     | A :: r1, B :: r2 => andb (ty_eqb A B) (go r1 r2)
     | _, _ => false
     end) Ts1 Ts2 = ty_list_eqb Ts1 Ts2.
Proof.
  intros Ts1 Ts2. reflexivity.
Qed.

Lemma ty_eqb_eq : forall T1 T2, ty_eqb T1 T2 = true -> T1 = T2.
Proof.
  apply (type_list_ind
    (fun T1 => forall T2, ty_eqb T1 T2 = true -> T1 = T2)
    (fun Ts1 => forall Ts2, ty_list_eqb Ts1 Ts2 = true -> Ts1 = Ts2)).
  - intros n T2 H; destruct T2; simpl in H; try discriminate.
    apply Nat.eqb_eq in H; subst; reflexivity.
  - intros A l B IHA IHB T2 H; destruct T2; simpl in H; try discriminate.
    apply Bool.andb_true_iff in H as [H1 H23].
    apply Bool.andb_true_iff in H23 as [H2 H3].
    rewrite (IHA _ H1), (lt_eqb_eq _ _ H2), (IHB _ H3). reflexivity.
  - intros K l Ts IHTs T2 H; destruct T2 as [| |K2 l2 Ts2| |]; simpl in H;
      try discriminate.
    rewrite ty_eqb_go_eq in H.
    apply Bool.andb_true_iff in H as [H1 H23].
    apply Bool.andb_true_iff in H23 as [H2 H3].
    apply Nat.eqb_eq in H1.
    rewrite H1, (lt_eqb_eq _ _ H2), (IHTs _ H3). reflexivity.
  - intros A IHA T2 H; destruct T2; simpl in H; try discriminate.
    rewrite (IHA _ H). reflexivity.
  - intros B A IHB IHA T2 H; destruct T2; simpl in H; try discriminate.
    apply Bool.andb_true_iff in H as [H1 H2].
    rewrite (IHB _ H1), (IHA _ H2). reflexivity.
  - intros Ts2 H; destruct Ts2; simpl in H; [reflexivity | discriminate].
  - intros A Ts IHA IHTs Ts2 H; destruct Ts2; simpl in H; try discriminate.
    apply Bool.andb_true_iff in H as [H1 H2].
    rewrite (IHA _ H1), (IHTs _ H2). reflexivity.
Qed.

Lemma ty_eqb_refl : forall T, ty_eqb T T = true.
Proof.
  apply (type_list_ind
    (fun T => ty_eqb T T = true)
    (fun Ts => ty_list_eqb Ts Ts = true)).
  - intros n. apply Nat.eqb_refl.
  - intros A l B IHA IHB. simpl. rewrite IHA, lt_eqb_refl, IHB. reflexivity.
  - intros K l Ts IHTs. simpl.
    rewrite ty_eqb_go_eq, Nat.eqb_refl, lt_eqb_refl, IHTs. reflexivity.
  - intros A IHA. simpl. exact IHA.
  - intros B A IHB IHA. simpl. rewrite IHB, IHA. reflexivity.
  - reflexivity.
  - intros A Ts IHA IHTs. simpl. rewrite IHA, IHTs. reflexivity.
Qed.
