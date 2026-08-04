Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import SubstTactics.
Require Import Typing.


(* ================================================================== *)
(*                                                                    *)
(*    LEMMAS ABOUT shift_X / subst_X (statements only)                *)
(*                                                                    *)
(* The lemmas below state the standard de-Bruijn / σ-calculus laws    *)
(* governing shifting and substitution.  Only the laws actually used  *)
(* in the metatheory are kept here, and all of them are proved        *)
(* (`*_zero`, `*_fuse`, the cross-sort `*_commute` lemmas and the     *)
(* list-substitution laws below).                                     *)
(*                                                                    *)
(* Naming convention                                                  *)
(* ------------------------------------------------------------------ *)
(*   <op>_<sort>              — single-sort version (e.g. shift_lt)   *)
(*   <op>_<sort>_in_<carrier> — cross-sort version                    *)
(*                                                                    *)
(* For every fixpoint in Substitution.v, where applicable:            *)
(*                                                                    *)
(*   *_zero          : shifting by 0 is identity                      *)
(*   *_fuse          : two shifts at the same cutoff combine          *)
(*   *_swap          : two shifts at different cutoffs commute        *)
(*   *_subst_cancel  : subst c v (shift 1 c t) = t                    *)
(*   shift_subst_*   : shift distributes over subst                   *)
(*   subst_subst_*   : two substs commute (substitution lemma)        *)
(*   *_independent   : a shift/subst on sort X is the identity on a   *)
(*                     term/type that contains no free X-variables    *)
(*                                                                    *)
(* ================================================================== *)


(* ================================================================== *)
(* Sanity examples (unit tests)                                       *)
(* ================================================================== *)

Section UnitTests.

(* shift_tm respects the cutoff under term_lam: var 0 in the body is
   bound (cutoff becomes 1) so it is not incremented. *)
Example shift_tm_under_lam :
  shift_tm 1 0 (term_lam (term_var 0) (type_var 0))
    = term_lam (term_var 0) (type_var 0).
Proof. reflexivity. Qed.

Example shift_tm_free_var :
  shift_tm 2 0 (term_var 5) = term_var 7.
Proof. reflexivity. Qed.

Example shift_tm_below_cutoff :
  shift_tm 2 3 (term_var 1) = term_var 1.
Proof. reflexivity. Qed.

(* yes_body is shifted at cutoff (0+arity) = 2.  Variable 1 < 2, so
   it is bound by the match and is NOT shifted; outer free var 0
   (in scrut and no_body, shifted at cutoff 0) becomes 1. *)
Example shift_tm_match_arity :
  shift_tm 1 0 (term_match (term_var 0) 1 0 2 (term_var 1) (term_var 0))
    = term_match (term_var 1) 1 0 2 (term_var 1) (term_var 1).
Proof. reflexivity. Qed.

(* Free variable inside yes_body (index >= arity) IS shifted. *)
Example shift_tm_match_arity_free :
  shift_tm 1 0 (term_match (term_var 0) 1 0 2 (term_var 2) (term_var 0))
    = term_match (term_var 1) 1 0 2 (term_var 3) (term_var 1).
Proof. reflexivity. Qed.

(* subst_tm at variable 0 returns the replacement (after proper    *)
(* shifting) and decrements higher indices.                        *)
Example subst_tm_var_0 :
  subst_tm 0 (term_var 42) (term_var 0) = term_var 42.
Proof. reflexivity. Qed.

Example subst_tm_var_higher :
  subst_tm 0 (term_var 42) (term_var 3) = term_var 2.
Proof. reflexivity. Qed.

Example subst_tm_var_below :
  subst_tm 2 (term_var 42) (term_var 1) = term_var 1.
Proof. reflexivity. Qed.

(* subst_list_tm picks vs[i] for variable i, outermost-first. *)
Example subst_list_tm_pick0 :
  subst_list_tm [term_var 10; term_var 20; term_var 30] (term_var 0)
    = term_var 10.
Proof. vm_compute. reflexivity. Qed.

Example subst_list_tm_pick1 :
  subst_list_tm [term_var 10; term_var 20; term_var 30] (term_var 1)
    = term_var 20.
Proof. vm_compute. reflexivity. Qed.

Example subst_list_tm_pick2 :
  subst_list_tm [term_var 10; term_var 20; term_var 30] (term_var 2)
    = term_var 30.
Proof. vm_compute. reflexivity. Qed.

End UnitTests.


(* ================================================================== *)
(* Custom induction principles (with IH for list elements)            *)
(* ================================================================== *)

Section TypeListInd.
  Variable P : type -> Prop.
  Variable Q : list type -> Prop.
  Hypothesis Hvar     : forall n, P (type_var n).
  Hypothesis Hfun     : forall A l B, P A -> P B -> P (type_fun A l B).
  Hypothesis Hctor    : forall K l Ts, Q Ts -> P (type_ctor K l Ts).
  Hypothesis Hlt_all  : forall A, P A -> P (type_lt_all A).
  Hypothesis Hty_all  : forall B A, P B -> P A -> P (type_ty_all B A).
  Hypothesis Hnil     : Q [].
  Hypothesis Hcons    : forall A Ts, P A -> Q Ts -> Q (A :: Ts).
  Fixpoint type_list_ind (T : type) : P T :=
    match T with
    | type_var n => Hvar n
    | type_fun A l B => Hfun A l B (type_list_ind A) (type_list_ind B)
    | type_ctor K l Ts =>
        Hctor K l Ts
          ((fix go Ts : Q Ts :=
              match Ts return Q Ts with
              | [] => Hnil
              | A :: rest => Hcons A rest (type_list_ind A) (go rest)
              end) Ts)
    | type_lt_all A => Hlt_all A (type_list_ind A)
    | type_ty_all B A => Hty_all B A (type_list_ind B) (type_list_ind A)
    end.
End TypeListInd.

Section TermListInd.
  Variable P : term -> Prop.
  Variable Q : list term -> Prop.
  Variable R : list (nat * term) -> Prop.
  Hypothesis Hvar        : forall n, P (term_var n).
  Hypothesis Happ        : forall t1 t2, P t1 -> P t2 -> P (term_app t1 t2).
  Hypothesis Hlam        : forall body T, P body -> P (term_lam body T).
  Hypothesis Hty_app     : forall t T, P t -> P (term_ty_app t T).
  Hypothesis Hty_lam     : forall bound body, P body -> P (term_ty_lam bound body).
  Hypothesis Hlt_app     : forall t l, P t -> P (term_lt_app t l).
  Hypothesis Hlt_lam     : forall body, P body -> P (term_lt_lam body).
  Hypothesis Hctor       : forall K l lts Ts ts, Q ts -> P (term_ctor K l lts Ts ts).
  Hypothesis Hmatch      : forall scrut tag n_lt arity yes_body no_body,
    P scrut -> P yes_body -> P no_body ->
    P (term_match scrut tag n_lt arity yes_body no_body).
  Hypothesis Hhandle     : forall E Ts T_B T_R op_bodies body,
    R op_bodies -> P body -> P (term_handle E Ts T_B T_R op_bodies body).
  Hypothesis Hperform    : forall t op Ss A arg, P t -> P arg -> P (term_perform t op Ss A arg).
  Hypothesis Hcap        : forall E m Ts T_R op_bodies, R op_bodies -> P (term_cap E m Ts T_R op_bodies).
  Hypothesis Hhandler_m  : forall m T_B T_R t, P t -> P (term_handler_m m T_B T_R t).
  Hypothesis Hnil        : Q [].
  Hypothesis Hcons       : forall t ts, P t -> Q ts -> Q (t :: ts).
  Hypothesis Hops_nil    : R [].
  Hypothesis Hops_cons   : forall nb ob obs, P ob -> R obs -> R ((nb, ob) :: obs).
  Fixpoint term_list_ind (t : term) : P t :=
    match t with
    | term_var n => Hvar n
    | term_app t1 t2 => Happ t1 t2 (term_list_ind t1) (term_list_ind t2)
    | term_lam body T => Hlam body T (term_list_ind body)
    | term_ty_app t T => Hty_app t T (term_list_ind t)
    | term_ty_lam bound body => Hty_lam bound body (term_list_ind body)
    | term_lt_app t l => Hlt_app t l (term_list_ind t)
    | term_lt_lam body => Hlt_lam body (term_list_ind body)
    | term_ctor K l lts Ts ts =>
        Hctor K l lts Ts ts
          ((fix go ts : Q ts :=
              match ts return Q ts with
              | [] => Hnil
              | u :: rest => Hcons u rest (term_list_ind u) (go rest)
              end) ts)
    | term_match scrut tag n_lt arity yes_body no_body =>
      Hmatch scrut tag n_lt arity yes_body no_body
          (term_list_ind scrut) (term_list_ind yes_body) (term_list_ind no_body)
    | term_handle E Ts T_B T_R op_bodies body =>
      Hhandle E Ts T_B T_R op_bodies body
        ((fix go_ops obs : R obs :=
            match obs return R obs with
            | [] => Hops_nil
            | (nb, ob) :: rest =>
                Hops_cons nb ob rest (term_list_ind ob) (go_ops rest)
            end) op_bodies)
        (term_list_ind body)
    | term_perform t op Ss A arg =>
        Hperform t op Ss A arg (term_list_ind t) (term_list_ind arg)
    | term_cap E m Ts T_R op_bodies =>
        Hcap E m Ts T_R op_bodies
          ((fix go_ops obs : R obs :=
              match obs return R obs with
              | [] => Hops_nil
              | (nb, ob) :: rest =>
                  Hops_cons nb ob rest (term_list_ind ob) (go_ops rest)
              end) op_bodies)
    | term_handler_m m T_B T_R t => Hhandler_m m T_B T_R t (term_list_ind t)
    end.
End TermListInd.


(* The op-bodies traversals of each term function, as maps over pairs. *)
Lemma shift_tm_ops_eq_map : forall (amount cutoff : nat) (obs : list (nat * term)),
  List.map (fun '(nb, ob) => (nb, shift_tm amount (cutoff + 2) ob)) obs =
  List.map (fun p => (fst p, shift_tm amount (cutoff + 2) (snd p))) obs.
Proof. intros; induction obs as [|[nb ob] rest IH]; simpl; congruence. Qed.
#[export] Hint Rewrite shift_tm_ops_eq_map : subst_go.

Lemma shift_ty_in_tm_ops_eq_map : forall (amount cutoff : nat) (obs : list (nat * term)),
  List.map (fun '(nb, ob) => (nb, shift_ty_in_tm amount (cutoff + nb) ob)) obs =
  List.map (fun p => (fst p, shift_ty_in_tm amount (cutoff + fst p) (snd p))) obs.
Proof. intros; induction obs as [|[nb ob] rest IH]; simpl; congruence. Qed.
#[export] Hint Rewrite shift_ty_in_tm_ops_eq_map : subst_go.

Lemma shift_lt_in_tm_ops_eq_map : forall (amount cutoff : nat) (obs : list (nat * term)),
  List.map (fun '(nb, ob) => (nb, shift_lt_in_tm amount cutoff ob)) obs =
  List.map (fun p => (fst p, shift_lt_in_tm amount cutoff (snd p))) obs.
Proof. intros; induction obs as [|[nb ob] rest IH]; simpl; congruence. Qed.
#[export] Hint Rewrite shift_lt_in_tm_ops_eq_map : subst_go.

Lemma subst_tm_ops_eq_map : forall (var : nat) (replacement : term) (obs : list (nat * term)),
  List.map (fun '(nb, ob) => (nb, subst_tm (var + 2) (shift_tm 2 0 replacement) ob)) obs =
  List.map (fun p => (fst p, subst_tm (var + 2) (shift_tm 2 0 replacement) (snd p))) obs.
Proof. intros; induction obs as [|[nb ob] rest IH]; simpl; congruence. Qed.
#[export] Hint Rewrite subst_tm_ops_eq_map : subst_go.


Lemma subst_ty_in_tm_ops_eq_map : forall (var : nat) (replacement : type) (obs : list (nat * term)),
  List.map (fun '(nb, ob) => (nb, subst_ty_in_tm (var + nb) (shift_ty nb 0 replacement) ob)) obs =
  List.map (fun p => (fst p, subst_ty_in_tm (var + fst p) (shift_ty (fst p) 0 replacement) (snd p))) obs.
Proof. intros; induction obs as [|[nb ob] rest IH]; simpl; congruence. Qed.
#[export] Hint Rewrite subst_ty_in_tm_ops_eq_map : subst_go.

Lemma subst_lt_in_tm_ops_eq_map : forall (var : nat) (replacement : lifetime) (obs : list (nat * term)),
  List.map (fun '(nb, ob) => (nb, subst_lt_in_tm var replacement ob)) obs =
  List.map (fun p => (fst p, subst_lt_in_tm var replacement (snd p))) obs.
Proof. intros; induction obs as [|[nb ob] rest IH]; simpl; congruence. Qed.
#[export] Hint Rewrite subst_lt_in_tm_ops_eq_map : subst_go.



(* ================================================================== *)
(* shift_zero                                                         *)
(*                                                                    *)
(* Shifting by zero is the identity.                                  *)
(* ================================================================== *)

Lemma shift_lt_zero : forall c l,
  shift_lt 0 c l = l.
Proof.
  intros c l. induction l; simpl; auto.
  - destruct (Nat.leb c n); auto.
  - rewrite IHl1, IHl2; auto.
Qed.
#[export] Hint Rewrite shift_lt_zero : subst_norm.

Lemma shift_lt_in_ty_zero : forall c T,
  shift_lt_in_ty 0 c T = T.
Proof.
  enough (H : forall T, forall c, shift_lt_in_ty 0 c T = T).
  { intros c T; apply H. }
  apply (type_list_ind
    (fun T => forall c, shift_lt_in_ty 0 c T = T)
    (fun Ts => forall c, List.map (shift_lt_in_ty 0 c) Ts = Ts));
    go_traverse_norm.
Qed.

Lemma shift_ty_zero : forall c T,
  shift_ty 0 c T = T.
Proof.
  enough (H : forall T, forall c, shift_ty 0 c T = T).
  { intros c T; apply H. }
  apply (type_list_ind
    (fun T => forall c, shift_ty 0 c T = T)
    (fun Ts => forall c, List.map (shift_ty 0 c) Ts = Ts)).
  - intros n c; simpl; destruct (Nat.leb c n); simpl; f_equal; lia.
  - intros A l B HA HB c; simpl; rewrite HA, HB; reflexivity.
  - intros K l Ts HTs c; simpl; f_equal; apply HTs.
  - intros A HA c; simpl; rewrite HA; reflexivity.
  - intros B A HB HA c; simpl; rewrite HB, HA; reflexivity.
  - intro c; reflexivity.
  - intros A Ts HA HTs c; simpl; rewrite HA; f_equal; apply HTs.
Qed.

Lemma shift_tm_zero : forall c t,
  shift_tm 0 c t = t.
Proof.
  enough (H : forall t, forall c, shift_tm 0 c t = t).
  { intros c t; apply H. }
  apply (term_list_ind
    (fun t => forall c, shift_tm 0 c t = t)
    (fun ts => forall c, List.map (shift_tm 0 c) ts = ts)
    (fun obs => forall c,
       List.map (fun p => (fst p, shift_tm 0 c (snd p))) obs = obs)).
  - intros n c; simpl; destruct (Nat.leb c n); simpl; f_equal; lia.
  - intros t1 t2 H1 H2 c; simpl; rewrite H1, H2; reflexivity.
  - intros body T H c; simpl; rewrite H; reflexivity.
  - intros t T H c; simpl; rewrite H; reflexivity.
  - intros bound body H c; simpl; rewrite H; reflexivity.
  - intros t l H c; simpl; rewrite H; reflexivity.
  - intros body H c; simpl; rewrite H; reflexivity.
  - intros K l lts Ts ts Hts c; simpl; f_equal; apply Hts.
  - intros scrut tag n_lt arity yes_body no_body Hs Hy Hn c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E Ts T_B T_R op_bodies body Hops Hb c; simpl;
    rewrite shift_tm_ops_eq_map, Hops, Hb; reflexivity.
  - intros t op Ss A_ret arg Ht Ha c; simpl; rewrite Ht, Ha; reflexivity.
  - intros E m Ts T_R op_bodies Hops c; simpl;
    rewrite shift_tm_ops_eq_map, Hops; reflexivity.
  - intros m T_B T_R t H c; simpl; rewrite H; reflexivity.
  - intro c; reflexivity.
  - intros t ts Ht Hts c; simpl; rewrite Ht; f_equal; apply Hts.
  - intro c; reflexivity.
  - intros nb ob obs Hob Hobs c; simpl; rewrite Hob, Hobs; reflexivity.
Qed.

Lemma shift_ty_in_tm_zero : forall c t,
  shift_ty_in_tm 0 c t = t.
Proof.
  enough (H : forall t, forall c, shift_ty_in_tm 0 c t = t).
  { intros c t; apply H. }
  apply (term_list_ind
    (fun t => forall c, shift_ty_in_tm 0 c t = t)
    (fun ts => forall c, List.map (shift_ty_in_tm 0 c) ts = ts)
    (fun obs => forall c,
       List.map (fun p => (fst p, shift_ty_in_tm 0 (c + fst p) (snd p))) obs
       = obs)).
  - intro c; reflexivity.
  - intros t1 t2 H1 H2 c; simpl; rewrite H1, H2; reflexivity.
  - intros body T H c; simpl; rewrite H, shift_ty_zero; reflexivity.
  - intros t T H c; simpl; rewrite H, shift_ty_zero; reflexivity.
  - intros bound body H c; simpl; rewrite H, shift_ty_zero; reflexivity.
  - intros t l H c; simpl; rewrite H; reflexivity.
  - intros body H c; simpl; rewrite H; reflexivity.
  - intros K l lts Ts ts Hts c; simpl.
    unfold map_shift_ty. rewrite List.map_ext with (g := id).
    + rewrite List.map_id; f_equal; apply Hts.
    + intro T; apply shift_ty_zero.
  - intros scrut tag n_lt arity yes_body no_body Hs Hy Hn c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E Ts T_B T_R op_bodies body Hops Hb c; simpl.
    rewrite shift_ty_in_tm_ops_eq_map.
    unfold map_shift_ty. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, !shift_ty_zero, Hops, Hb; reflexivity.
    + intro T; apply shift_ty_zero.
  - intros t op Ss A_ret arg Ht Ha c; simpl.
    unfold map_shift_ty. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, shift_ty_zero, Ht, Ha; reflexivity.
    + intro T; apply shift_ty_zero.
  - intros E m Ts T_R op_bodies Hops c; simpl.
    rewrite shift_ty_in_tm_ops_eq_map.
    unfold map_shift_ty. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, shift_ty_zero, Hops; reflexivity.
    + intro T; apply shift_ty_zero.
  - intros m T_B T_R t H c; simpl; rewrite !shift_ty_zero, H; reflexivity.
  - intro c; reflexivity.
  - intros t ts Ht Hts c; simpl; rewrite Ht; f_equal; apply Hts.
  - intro c; reflexivity.
  - intros nb ob obs Hob Hobs c; simpl; rewrite Hob, Hobs; reflexivity.
Qed.

Lemma shift_lt_in_tm_zero : forall c t,
  shift_lt_in_tm 0 c t = t.
Proof.
  enough (H : forall t, forall c, shift_lt_in_tm 0 c t = t).
  { intros c t; apply H. }
  apply (term_list_ind
    (fun t => forall c, shift_lt_in_tm 0 c t = t)
    (fun ts => forall c, List.map (shift_lt_in_tm 0 c) ts = ts)
    (fun obs => forall c,
       List.map (fun p => (fst p, shift_lt_in_tm 0 c (snd p))) obs = obs)).
  - intro c; reflexivity.
  - intros t1 t2 H1 H2 c; simpl; rewrite H1, H2; reflexivity.
  - intros body T H c; simpl; rewrite H, shift_lt_in_ty_zero; reflexivity.
  - intros t T H c; simpl; rewrite H, shift_lt_in_ty_zero; reflexivity.
  - intros bound body H c; simpl; rewrite H, shift_lt_in_ty_zero; reflexivity.
  - intros t l H c; simpl; rewrite H, shift_lt_zero; reflexivity.
  - intros body H c; simpl; rewrite H; reflexivity.
  - intros K l lts Ts ts Hts c; simpl.
    rewrite shift_lt_zero.
    rewrite List.map_ext with (g := id).
    + rewrite List.map_id.
      unfold map_shift_lt_in_ty. rewrite List.map_ext with (g := id).
      * rewrite List.map_id; f_equal; apply Hts.
      * intro T; apply shift_lt_in_ty_zero.
    + intro l0; apply shift_lt_zero.
  - intros scrut tag n_lt arity yes_body no_body Hs Hy Hn c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E Ts T_B T_R op_bodies body Hops Hb c; simpl.
    rewrite shift_lt_in_tm_ops_eq_map.
    unfold map_shift_lt_in_ty. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, !shift_lt_in_ty_zero, Hops, Hb; reflexivity.
    + intro T; apply shift_lt_in_ty_zero.
  - intros t op Ss A_ret arg Ht Ha c; simpl.
    unfold map_shift_lt_in_ty. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, shift_lt_in_ty_zero, Ht, Ha; reflexivity.
    + intro T; apply shift_lt_in_ty_zero.
  - intros E m Ts T_R op_bodies Hops c; simpl.
    rewrite shift_lt_in_tm_ops_eq_map.
    unfold map_shift_lt_in_ty. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, shift_lt_in_ty_zero, Hops; reflexivity.
    + intro T; apply shift_lt_in_ty_zero.
  - intros m T_B T_R t H c; simpl; rewrite !shift_lt_in_ty_zero, H; reflexivity.
  - intro c; reflexivity.
  - intros t ts Ht Hts c; simpl; rewrite Ht; f_equal; apply Hts.
  - intro c; reflexivity.
  - intros nb ob obs Hob Hobs c; simpl; rewrite Hob, Hobs; reflexivity.
Qed.


(* ================================================================== *)
(* shift_fuse                                                         *)
(*                                                                    *)
(* Two consecutive shifts at the same cutoff combine into one.        *)
(* ================================================================== *)

Lemma shift_lt_fuse : forall a b c l,
  shift_lt a c (shift_lt b c l) = shift_lt (a + b) c l.
Proof.
  intros a b c l. induction l; simpl.
  - destruct (Nat.leb c n) eqn:H1.
    + assert (Nat.leb c (n + b) = true) as H2.
      { apply Nat.leb_le. apply Nat.leb_le in H1. lia. }
      rewrite H2. f_equal. lia.
    + rewrite H1. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHl1, IHl2; reflexivity.
Qed.
#[export] Hint Rewrite shift_lt_fuse : subst_norm.

Lemma shift_lt_in_ty_fuse : forall a b c T,
  shift_lt_in_ty a c (shift_lt_in_ty b c T) = shift_lt_in_ty (a + b) c T.
Proof.
  enough (H : forall T, forall a b c, shift_lt_in_ty a c (shift_lt_in_ty b c T) = shift_lt_in_ty (a + b) c T).
  { intros a b c T; apply H. }
  apply (type_list_ind
    (fun T => forall a b c, shift_lt_in_ty a c (shift_lt_in_ty b c T) = shift_lt_in_ty (a + b) c T)
    (fun Ts => forall a b c, List.map (shift_lt_in_ty a c) (List.map (shift_lt_in_ty b c) Ts) = List.map (shift_lt_in_ty (a + b) c) Ts));
    go_traverse_norm.
Qed.

Lemma shift_ty_fuse : forall a b c T,
  shift_ty a c (shift_ty b c T) = shift_ty (a + b) c T.
Proof.
  enough (H : forall T, forall a b c, shift_ty a c (shift_ty b c T) = shift_ty (a + b) c T).
  { intros a b c T; apply H. }
  apply (type_list_ind
    (fun T => forall a b c, shift_ty a c (shift_ty b c T) = shift_ty (a + b) c T)
    (fun Ts => forall a b c, List.map (shift_ty a c) (List.map (shift_ty b c) Ts) = List.map (shift_ty (a + b) c) Ts)).
  - intros n a b c; simpl.
    destruct (Nat.leb c n) eqn:H1.
    + assert (Nat.leb c (n + b) = true) as H2.
      { apply Nat.leb_le. apply Nat.leb_le in H1. lia. }
      rewrite H2. f_equal. lia.
    + rewrite H1. reflexivity.
  - intros A l B HA HB a b c; simpl; rewrite HA, HB; reflexivity.
  - intros K l Ts HTs a b c; simpl.
    f_equal.
    apply HTs.
  - intros A HA a b c; simpl; rewrite HA; reflexivity.
  - intros B A HB HA a b c; simpl; rewrite HB, HA; reflexivity.
  - intros a b c; reflexivity.
  - intros A Ts HA HTs a b c; simpl; rewrite HA; f_equal; apply HTs.
Qed.

Lemma shift_tm_fuse : forall a b c t,
  shift_tm a c (shift_tm b c t) = shift_tm (a + b) c t.
Proof.
  enough (H : forall t, forall a b c, shift_tm a c (shift_tm b c t) = shift_tm (a + b) c t).
  { intros a b c t; apply H. }
  apply (term_list_ind
    (fun t => forall a b c, shift_tm a c (shift_tm b c t) = shift_tm (a + b) c t)
    (fun ts => forall a b c, List.map (shift_tm a c) (List.map (shift_tm b c) ts) = List.map (shift_tm (a + b) c) ts)
    (fun obs => forall a b c,
       List.map (fun p => (fst p, shift_tm a c (snd p)))
         (List.map (fun p => (fst p, shift_tm b c (snd p))) obs)
       = List.map (fun p => (fst p, shift_tm (a + b) c (snd p))) obs)).
  - intros n a b c; simpl.
    destruct (Nat.leb c n) eqn:H1.
    + assert (Nat.leb c (n + b) = true) as H2.
      { apply Nat.leb_le. apply Nat.leb_le in H1. lia. }
      rewrite H2. f_equal. lia.
    + rewrite H1. reflexivity.
  - intros t1 t2 H1 H2 a b c; simpl; rewrite H1, H2; reflexivity.
  - intros body T H a b c; simpl; rewrite H; reflexivity.
  - intros t T H a b c; simpl; rewrite H; reflexivity.
  - intros bound body H a b c; simpl; rewrite H; reflexivity.
  - intros t l H a b c; simpl; rewrite H; reflexivity.
  - intros body H a b c; simpl; rewrite H; reflexivity.
  - intros K l lts Ts ts Hts a b c; simpl.
    f_equal.
    apply Hts.
  - intros scrut tag n_lt arity yes_body no_body Hs Hy Hn a b c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E Ts T_B T_R op_bodies body Hops Hb a b c; simpl.
    rewrite !shift_tm_ops_eq_map, Hops, Hb; reflexivity.
  - intros t op Ss A_ret arg Ht Ha a b c; simpl; rewrite Ht, Ha; reflexivity.
  - intros E m Ts T_R op_bodies Hops a b c; simpl.
    rewrite !shift_tm_ops_eq_map, Hops; reflexivity.
  - intros m T_B T_R t H a b c; simpl; rewrite H; reflexivity.
  - intros a b c; reflexivity.
  - intros t ts Ht Hts a b c; simpl; rewrite Ht; f_equal; apply Hts.
  - intros a b c; reflexivity.
  - intros nb ob obs Hob Hobs a b c; simpl; rewrite Hob, Hobs; reflexivity.
Qed.

Lemma shift_ty_in_tm_fuse : forall a b c t,
  shift_ty_in_tm a c (shift_ty_in_tm b c t) = shift_ty_in_tm (a + b) c t.
Proof.
  enough (H : forall t, forall a b c, shift_ty_in_tm a c (shift_ty_in_tm b c t) = shift_ty_in_tm (a + b) c t).
  { intros a b c t; apply H. }
  apply (term_list_ind
    (fun t => forall a b c, shift_ty_in_tm a c (shift_ty_in_tm b c t) = shift_ty_in_tm (a + b) c t)
    (fun ts => forall a b c, List.map (shift_ty_in_tm a c) (List.map (shift_ty_in_tm b c) ts) = List.map (shift_ty_in_tm (a + b) c) ts)
    (fun obs => forall a b c,
       List.map (fun p => (fst p, shift_ty_in_tm a (c + fst p) (snd p)))
         (List.map (fun p => (fst p, shift_ty_in_tm b (c + fst p) (snd p))) obs)
       = List.map (fun p => (fst p, shift_ty_in_tm (a + b) (c + fst p) (snd p))) obs)).
  - intros n a b c; reflexivity.
  - intros t1 t2 H1 H2 a b c; simpl; rewrite H1, H2; reflexivity.
  - intros body T H a b c; simpl; rewrite H, shift_ty_fuse; reflexivity.
  - intros t T H a b c; simpl; rewrite H, shift_ty_fuse; reflexivity.
  - intros bound body H a b c; simpl; rewrite H, shift_ty_fuse; reflexivity.
  - intros t l H a b c; simpl; rewrite H; reflexivity.
  - intros body H a b c; simpl; rewrite H; reflexivity.
  - intros K l lts Ts ts Hts a b c; simpl.
    unfold map_shift_ty.
    f_equal.
    + rewrite List.map_map.
      apply List.map_ext; intro T; apply shift_ty_fuse.
    + apply Hts.
  - intros scrut tag n_lt arity yes_body no_body Hs Hy Hn a b c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E Ts T_B T_R op_bodies body Hops Hb a b c; simpl.
    rewrite !shift_ty_in_tm_ops_eq_map.
    unfold map_shift_ty.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_ty (a + b) c) by (intro T; apply shift_ty_fuse).
    rewrite !shift_ty_fuse, Hops, Hb; reflexivity.
  - intros t op Ss A_ret arg Ht Ha a b c; simpl.
    unfold map_shift_ty.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_ty (a + b) c) by (intro T; apply shift_ty_fuse).
    rewrite shift_ty_fuse, Ht, Ha; reflexivity.
  - intros E m Ts T_R op_bodies Hops a b c; simpl.
    rewrite !shift_ty_in_tm_ops_eq_map.
    unfold map_shift_ty.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_ty (a + b) c) by (intro T; apply shift_ty_fuse).
    rewrite shift_ty_fuse, Hops; reflexivity.
  - intros m T_B T_R t H a b c; simpl; rewrite !shift_ty_fuse, H; reflexivity.
  - intros a b c; reflexivity.
  - intros t ts Ht Hts a b c; simpl; rewrite Ht; f_equal; apply Hts.
  - intros a b c; reflexivity.
  - intros nb ob obs Hob Hobs a b c; simpl; rewrite Hob, Hobs; reflexivity.
Qed.

Lemma shift_lt_in_tm_fuse : forall a b c t,
  shift_lt_in_tm a c (shift_lt_in_tm b c t) = shift_lt_in_tm (a + b) c t.
Proof.
  enough (H : forall t, forall a b c, shift_lt_in_tm a c (shift_lt_in_tm b c t) = shift_lt_in_tm (a + b) c t).
  { intros a b c t; apply H. }
  apply (term_list_ind
    (fun t => forall a b c, shift_lt_in_tm a c (shift_lt_in_tm b c t) = shift_lt_in_tm (a + b) c t)
    (fun ts => forall a b c, List.map (shift_lt_in_tm a c) (List.map (shift_lt_in_tm b c) ts) = List.map (shift_lt_in_tm (a + b) c) ts)
    (fun obs => forall a b c,
       List.map (fun p => (fst p, shift_lt_in_tm a c (snd p)))
         (List.map (fun p => (fst p, shift_lt_in_tm b c (snd p))) obs)
       = List.map (fun p => (fst p, shift_lt_in_tm (a + b) c (snd p))) obs)).
  - intros n a b c; reflexivity.
  - intros t1 t2 H1 H2 a b c; simpl; rewrite H1, H2; reflexivity.
  - intros body T H a b c; simpl; rewrite H, shift_lt_in_ty_fuse; reflexivity.
  - intros t T H a b c; simpl; rewrite H, shift_lt_in_ty_fuse; reflexivity.
  - intros bound body H a b c; simpl; rewrite H, shift_lt_in_ty_fuse; reflexivity.
  - intros t l H a b c; simpl; rewrite H, shift_lt_fuse; reflexivity.
  - intros body H a b c; simpl; rewrite H; reflexivity.
  - intros K l lts Ts ts Hts a b c; simpl.
    f_equal.
    + apply shift_lt_fuse.
    + rewrite List.map_map.
      apply List.map_ext; intro l0; apply shift_lt_fuse.
    + unfold map_shift_lt_in_ty.
      rewrite List.map_map.
      apply List.map_ext; intro T; apply shift_lt_in_ty_fuse.
    + apply Hts.
  - intros scrut tag n_lt arity yes_body no_body Hs Hy Hn a b c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E Ts T_B T_R op_bodies body Hops Hb a b c; simpl.
    rewrite !shift_lt_in_tm_ops_eq_map.
    unfold map_shift_lt_in_ty.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_lt_in_ty (a + b) c) by (intro T; apply shift_lt_in_ty_fuse).
    rewrite !shift_lt_in_ty_fuse, Hops, Hb; reflexivity.
  - intros t op Ss A_ret arg Ht Ha a b c; simpl.
    unfold map_shift_lt_in_ty.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_lt_in_ty (a + b) c) by (intro T; apply shift_lt_in_ty_fuse).
    rewrite shift_lt_in_ty_fuse, Ht, Ha; reflexivity.
  - intros E m Ts T_R op_bodies Hops a b c; simpl.
    rewrite !shift_lt_in_tm_ops_eq_map.
    unfold map_shift_lt_in_ty.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_lt_in_ty (a + b) c) by (intro T; apply shift_lt_in_ty_fuse).
    rewrite shift_lt_in_ty_fuse, Hops; reflexivity.
  - intros m T_B T_R t H a b c; simpl; rewrite !shift_lt_in_ty_fuse, H; reflexivity.
  - intros a b c; reflexivity.
  - intros t ts Ht Hts a b c; simpl; rewrite Ht; f_equal; apply Hts.
  - intros a b c; reflexivity.
  - intros nb ob obs Hob Hobs a b c; simpl; rewrite Hob, Hobs; reflexivity.
Qed.


(* ================================================================== *)
(* shift_independent (cross-sort: same carrier,                       *)
(*             unrelated index sorts commute trivially)               *)
(*                                                                    *)
(* Shifts on different sorts in the same carrier commute without any  *)
(* cutoff adjustment: a tm-shift and a ty-shift on a term, etc.       *)
(* ================================================================== *)

Lemma shift_tm_shift_ty_in_tm_commute : forall a1 c1 a2 c2 t,
  shift_tm a1 c1 (shift_ty_in_tm a2 c2 t)
    = shift_ty_in_tm a2 c2 (shift_tm a1 c1 t).
Proof.
  enough (H : forall t, forall a1 c1 a2 c2,
    shift_tm a1 c1 (shift_ty_in_tm a2 c2 t) = shift_ty_in_tm a2 c2 (shift_tm a1 c1 t)).
  { intros; apply H. }
  apply (term_list_ind
    (fun t => forall a1 c1 a2 c2, shift_tm a1 c1 (shift_ty_in_tm a2 c2 t) = shift_ty_in_tm a2 c2 (shift_tm a1 c1 t))
    (fun ts => forall a1 c1 a2 c2, List.map (shift_tm a1 c1) (List.map (shift_ty_in_tm a2 c2) ts) = List.map (shift_ty_in_tm a2 c2) (List.map (shift_tm a1 c1) ts))
    (fun obs => forall a1 c1 a2 c2,
       List.map (fun p => (fst p, shift_tm a1 c1 (snd p)))
         (List.map (fun p => (fst p, shift_ty_in_tm a2 (c2 + fst p) (snd p))) obs)
       = List.map (fun p => (fst p, shift_ty_in_tm a2 (c2 + fst p) (snd p)))
           (List.map (fun p => (fst p, shift_tm a1 c1 (snd p))) obs)));
    go_traverse.
Qed.

Lemma shift_tm_shift_lt_in_tm_commute : forall a1 c1 a2 c2 t,
  shift_tm a1 c1 (shift_lt_in_tm a2 c2 t)
    = shift_lt_in_tm a2 c2 (shift_tm a1 c1 t).
Proof.
  enough (H : forall t, forall a1 c1 a2 c2,
    shift_tm a1 c1 (shift_lt_in_tm a2 c2 t) = shift_lt_in_tm a2 c2 (shift_tm a1 c1 t)).
  { intros; apply H. }
  apply (term_list_ind
    (fun t => forall a1 c1 a2 c2, shift_tm a1 c1 (shift_lt_in_tm a2 c2 t) = shift_lt_in_tm a2 c2 (shift_tm a1 c1 t))
    (fun ts => forall a1 c1 a2 c2, List.map (shift_tm a1 c1) (List.map (shift_lt_in_tm a2 c2) ts) = List.map (shift_lt_in_tm a2 c2) (List.map (shift_tm a1 c1) ts))
    (fun obs => forall a1 c1 a2 c2,
       List.map (fun p => (fst p, shift_tm a1 c1 (snd p)))
         (List.map (fun p => (fst p, shift_lt_in_tm a2 c2 (snd p))) obs)
       = List.map (fun p => (fst p, shift_lt_in_tm a2 c2 (snd p)))
           (List.map (fun p => (fst p, shift_tm a1 c1 (snd p))) obs)));
    go_traverse.
Qed.

Lemma shift_ty_shift_lt_in_ty_commute : forall a1 c1 a2 c2 T,
  shift_ty a1 c1 (shift_lt_in_ty a2 c2 T)
    = shift_lt_in_ty a2 c2 (shift_ty a1 c1 T).
Proof.
  enough (H : forall T, forall a1 c1 a2 c2,
    shift_ty a1 c1 (shift_lt_in_ty a2 c2 T) = shift_lt_in_ty a2 c2 (shift_ty a1 c1 T)).
  { intros; apply H. }
  apply (type_list_ind
    (fun T => forall a1 c1 a2 c2, shift_ty a1 c1 (shift_lt_in_ty a2 c2 T) = shift_lt_in_ty a2 c2 (shift_ty a1 c1 T))
    (fun Ts => forall a1 c1 a2 c2, List.map (shift_ty a1 c1) (List.map (shift_lt_in_ty a2 c2) Ts) = List.map (shift_lt_in_ty a2 c2) (List.map (shift_ty a1 c1) Ts)));
    go_traverse.
Qed.


Fixpoint ty_ty_closed (c : nat) (T : type) : Prop :=
  match T with
  | type_var a => a < c
  | type_fun A _ B => ty_ty_closed c A /\ ty_ty_closed c B
  | type_ctor _ _ Ts => fold_right (fun A acc => ty_ty_closed c A /\ acc) True Ts
  | type_lt_all A => ty_ty_closed c A
  | type_ty_all B A => ty_ty_closed c B /\ ty_ty_closed (S c) A
  end.

Definition tys_ty_closed (c : nat) (Ts : list type) : Prop :=
  fold_right (fun A acc => ty_ty_closed c A /\ acc) True Ts.

Fixpoint lt_lt_closed (c : nat) (l : lifetime) : Prop :=
  match l with
  | lt_var x => x < c
  | lt_free => True
  | lt_local => True
  | lt_join l1 l2 => lt_lt_closed c l1 /\ lt_lt_closed c l2
  end.

Fixpoint ty_lt_closed (c : nat) (T : type) : Prop :=
  match T with
  | type_var _ => True
  | type_fun A l B => ty_lt_closed c A /\ lt_lt_closed c l /\ ty_lt_closed c B
  | type_ctor _ l Ts => lt_lt_closed c l /\ fold_right (fun A acc => ty_lt_closed c A /\ acc) True Ts
  | type_lt_all A => ty_lt_closed (S c) A
  | type_ty_all B A => ty_lt_closed c B /\ ty_lt_closed c A
  end.

Definition tys_lt_closed (c : nat) (Ts : list type) : Prop :=
  fold_right (fun A acc => ty_lt_closed c A /\ acc) True Ts.

Fixpoint tm_ty_closed (c : nat) (t : term) : Prop :=
  let fix go (ts : list term) : Prop :=
      match ts with
      | [] => True
      | u :: rest => tm_ty_closed c u /\ go rest
      end in
  match t with
  | term_var _ => True
  | term_app t1 t2 => tm_ty_closed c t1 /\ tm_ty_closed c t2
  | term_lam body T => tm_ty_closed c body /\ ty_ty_closed c T
  | term_ty_app t T => tm_ty_closed c t /\ ty_ty_closed c T
  | term_ty_lam bound body => ty_ty_closed c bound /\ tm_ty_closed (S c) body
  | term_lt_app t _ => tm_ty_closed c t
  | term_lt_lam body => tm_ty_closed c body
  | term_ctor _ _ _ Ts ts => tys_ty_closed c Ts /\ go ts
  | term_match scrut _ _ _ yes_body no_body =>
      tm_ty_closed c scrut /\ tm_ty_closed c yes_body /\ tm_ty_closed c no_body
  | term_handle _ Ts T_B T_R op_bodies body =>
      tys_ty_closed c Ts /\ ty_ty_closed c T_B /\ ty_ty_closed c T_R /\
      (fix go_ops (obs : list (nat * term)) : Prop :=
         match obs with
         | []               => True
         | (nb, ob) :: rest => tm_ty_closed (c + nb) ob /\ go_ops rest
         end) op_bodies /\ tm_ty_closed c body
  | term_perform t _ Ss A arg =>
      tm_ty_closed c t /\ tys_ty_closed c Ss /\ ty_ty_closed c A /\ tm_ty_closed c arg
  | term_cap _ _ Ts T_R op_bodies =>
      tys_ty_closed c Ts /\ ty_ty_closed c T_R /\
      (fix go_ops (obs : list (nat * term)) : Prop :=
         match obs with
         | []               => True
         | (nb, ob) :: rest => tm_ty_closed (c + nb) ob /\ go_ops rest
         end) op_bodies
  | term_handler_m _ T_B T_R t =>
      ty_ty_closed c T_B /\ ty_ty_closed c T_R /\ tm_ty_closed c t
  end.


Fixpoint lts_lt_closed (c : nat) (lts : list lifetime) : Prop :=
  match lts with
  | [] => True
  | l :: rest => lt_lt_closed c l /\ lts_lt_closed c rest
  end.

Fixpoint tm_lt_closed (c : nat) (t : term) : Prop :=
  let fix go (ts : list term) : Prop :=
      match ts with
      | [] => True
      | u :: rest => tm_lt_closed c u /\ go rest
      end in
  match t with
  | term_var _ => True
  | term_app t1 t2 => tm_lt_closed c t1 /\ tm_lt_closed c t2
  | term_lam body T => tm_lt_closed c body /\ ty_lt_closed c T
  | term_ty_app t T => tm_lt_closed c t /\ ty_lt_closed c T
  | term_ty_lam bound body => ty_lt_closed c bound /\ tm_lt_closed c body
  | term_lt_app t l => tm_lt_closed c t /\ lt_lt_closed c l
  | term_lt_lam body => tm_lt_closed (S c) body
  | term_ctor _ l lts Ts ts =>
      lt_lt_closed c l /\ lts_lt_closed c lts /\ tys_lt_closed c Ts /\ go ts
  | term_match scrut _ n_lt _ yes_body no_body =>
      tm_lt_closed c scrut /\ tm_lt_closed (c + n_lt) yes_body /\ tm_lt_closed c no_body
  | term_handle _ Ts T_B T_R op_bodies body =>
      tys_lt_closed c Ts /\ ty_lt_closed c T_B /\ ty_lt_closed c T_R /\
      (fix go_ops (obs : list (nat * term)) : Prop :=
         match obs with
         | []               => True
         | (_, ob) :: rest => tm_lt_closed c ob /\ go_ops rest
         end) op_bodies /\ tm_lt_closed c body
  | term_perform t _ Ss A arg =>
      tm_lt_closed c t /\ tys_lt_closed c Ss /\ ty_lt_closed c A /\ tm_lt_closed c arg
  | term_cap _ _ Ts T_R op_bodies =>
      tys_lt_closed c Ts /\ ty_lt_closed c T_R /\
      (fix go_ops (obs : list (nat * term)) : Prop :=
         match obs with
         | []               => True
         | (_, ob) :: rest => tm_lt_closed c ob /\ go_ops rest
         end) op_bodies
  | term_handler_m _ T_B T_R t =>
      ty_lt_closed c T_B /\ ty_lt_closed c T_R /\ tm_lt_closed c t
  end.


Lemma shift_ty_in_ty_closed : forall T c a,
  ty_ty_closed c T -> shift_ty a c T = T.
Proof.
  apply (type_list_ind
    (fun T => forall c a, ty_ty_closed c T -> shift_ty a c T = T)
    (fun Ts => forall c a, tys_ty_closed c Ts -> map_shift_ty a c Ts = Ts)); simpl; intros; try reflexivity.
  - destruct (Nat.leb c n) eqn:Hle; [apply Nat.leb_le in Hle; lia|reflexivity].
  - destruct H1 as [HA HB]. rewrite H by exact HA. rewrite H0 by exact HB. reflexivity.
  - f_equal. unfold map_shift_ty in H. apply H. exact H0.
  - rewrite H by exact H0. reflexivity.
  - destruct H1 as [HB HA]. rewrite H by exact HB. rewrite H0 by exact HA. reflexivity.
  - destruct H1 as [HA HTs]. cbn [map_shift_ty List.map].
    rewrite H by exact HA.
    f_equal.
    match goal with
    | |- List.map (shift_ty ?amount ?cutoff) ?tail = ?tail =>
        change (List.map (shift_ty amount cutoff) tail) with (map_shift_ty amount cutoff tail)
    | |- map_shift_ty _ _ _ = _ => idtac
    end.
    rewrite H0 by exact HTs. reflexivity.
Qed.

Lemma map_shift_ty_closed : forall Ts c a,
  tys_ty_closed c Ts -> map_shift_ty a c Ts = Ts.
Proof.
  induction Ts as [|T Ts IH]; intros c a H; simpl in *; [reflexivity|].
  destruct H as [HT HTs]. cbn [map_shift_ty List.map].
  rewrite shift_ty_in_ty_closed by exact HT.
  change (List.map (shift_ty a c) Ts) with (map_shift_ty a c Ts).
  rewrite IH by exact HTs. reflexivity.
Qed.

Lemma shift_lt_closed_lifetime : forall l c a,
  lt_lt_closed c l -> shift_lt a c l = l.
Proof.
  induction l; intros c a H; simpl in *; try reflexivity.
  - destruct (Nat.leb c n) eqn:Hle; [apply Nat.leb_le in Hle; lia|reflexivity].
  - destruct H as [H1 H2]. rewrite IHl1 by exact H1. rewrite IHl2 by exact H2. reflexivity.
Qed.

Lemma shift_lt_in_type_closed : forall T c a,
  ty_lt_closed c T -> shift_lt_in_ty a c T = T.
Proof.
  apply (type_list_ind
    (fun T => forall c a, ty_lt_closed c T -> shift_lt_in_ty a c T = T)
    (fun Ts => forall c a, tys_lt_closed c Ts -> map_shift_lt_in_ty a c Ts = Ts)); simpl; intros; try reflexivity.
  - destruct H1 as [HA [Hl HB]]. rewrite H by exact HA. rewrite H0 by exact HB.
    rewrite shift_lt_closed_lifetime by exact Hl. reflexivity.
  - destruct H0 as [Hl HTs]. rewrite shift_lt_closed_lifetime by exact Hl.
    f_equal. unfold map_shift_lt_in_ty in H. apply H. exact HTs.
  - rewrite H by exact H0. reflexivity.
  - destruct H1 as [HB HA]. rewrite H by exact HB. rewrite H0 by exact HA. reflexivity.
  - destruct H1 as [HA HTs]. cbn [map_shift_lt_in_ty List.map].
    rewrite H by exact HA.
    f_equal.
    match goal with
    | |- List.map (shift_lt_in_ty ?amount ?cutoff) ?tail = ?tail =>
        change (List.map (shift_lt_in_ty amount cutoff) tail) with (map_shift_lt_in_ty amount cutoff tail)
    | |- map_shift_lt_in_ty _ _ _ = _ => idtac
    end.
    rewrite H0 by exact HTs. reflexivity.
Qed.

Lemma map_shift_lt_in_ty_closed : forall Ts c a,
  tys_lt_closed c Ts -> map_shift_lt_in_ty a c Ts = Ts.
Proof.
  induction Ts as [|T Ts IH]; intros c a H; simpl in *; [reflexivity|].
  destruct H as [HT HTs]. cbn [map_shift_lt_in_ty List.map].
  rewrite shift_lt_in_type_closed by exact HT.
  change (List.map (shift_lt_in_ty a c) Ts) with (map_shift_lt_in_ty a c Ts).
  rewrite IH by exact HTs. reflexivity.
Qed.

Lemma lt_lt_closed_mono : forall l c d,
  c <= d -> lt_lt_closed c l -> lt_lt_closed d l.
Proof.
  induction l; intros c d Hle Hclosed; simpl in *; try exact I.
  - lia.
  - destruct Hclosed as [H1 H2]. split; [eapply IHl1|eapply IHl2]; eauto.
Qed.


Lemma ty_lt_closed_mono : forall T c d,
  c <= d -> ty_lt_closed c T -> ty_lt_closed d T.
Proof.
  apply (type_list_ind
    (fun T => forall c d, c <= d -> ty_lt_closed c T -> ty_lt_closed d T)
    (fun Ts => forall c d, c <= d -> tys_lt_closed c Ts -> tys_lt_closed d Ts)).
  - intros n c d Hle Hclosed. exact I.
  - intros A l B IHA IHB c d Hle Hclosed. simpl in *.
    destruct Hclosed as [HA [Hl HB]]. repeat split.
    + apply IHA with (c := c); assumption.
    + eapply lt_lt_closed_mono; eauto.
    + apply IHB with (c := c); assumption.
  - intros K l Ts IHTs c d Hle Hclosed. simpl in *.
    destruct Hclosed as [Hl HTs]. split.
    + eapply lt_lt_closed_mono; eauto.
    + apply IHTs with (c := c); assumption.
  - intros A IHA c d Hle Hclosed. simpl in *.
    apply IHA with (c := S c); [lia|exact Hclosed].
  - intros B A IHB IHA c d Hle Hclosed. simpl in *.
    destruct Hclosed as [HB HA]. split.
    + apply IHB with (c := c); assumption.
    + apply IHA with (c := c); assumption.
  - intros c d Hle Hclosed. exact I.
  - intros A Ts IHA IHTs c d Hle Hclosed. simpl in *.
    destruct Hclosed as [HA HTs]. split.
    + apply IHA with (c := c); assumption.
    + apply IHTs with (c := c); assumption.
Qed.


Lemma ty_ty_closed_mono : forall T c d,
  c <= d -> ty_ty_closed c T -> ty_ty_closed d T.
Proof.
  apply (type_list_ind
    (fun T => forall c d, c <= d -> ty_ty_closed c T -> ty_ty_closed d T)
    (fun Ts => forall c d, c <= d -> tys_ty_closed c Ts -> tys_ty_closed d Ts)).
  - intros n c d Hle Hclosed. simpl in *. lia.
  - intros A l B IHA IHB c d Hle Hclosed. simpl in *.
    destruct Hclosed as [HA HB]. split.
    + apply IHA with (c := c); assumption.
    + apply IHB with (c := c); assumption.
  - intros K l Ts IHTs c d Hle Hclosed. simpl in *.
    apply IHTs with (c := c); assumption.
  - intros A IHA c d Hle Hclosed. simpl in *.
    apply IHA with (c := c); assumption.
  - intros B A IHB IHA c d Hle Hclosed. simpl in *.
    destruct Hclosed as [HB HA]. split.
    + apply IHB with (c := c); assumption.
    + apply IHA with (c := S c); [lia|exact HA].
  - intros c d Hle Hclosed. exact I.
  - intros A Ts IHA IHTs c d Hle Hclosed. simpl in *.
    destruct Hclosed as [HA HTs]. split.
    + apply IHA with (c := c); assumption.
    + apply IHTs with (c := c); assumption.
Qed.


(* Wrappers alpha-equal to the closedness predicates' inline op-body   *)
(* fixes: motives stated through these are convertible with the        *)
(* predicates' own go_ops occurrences (fold_right is NOT — its         *)
(* conjunction sits outside the pair match).                           *)
Definition ops_tm_ty_closed (c : nat) (obs : list (nat * term)) : Prop :=
  (fix go_ops (obs : list (nat * term)) : Prop :=
     match obs with
     | []               => True
     | (nb, ob) :: rest => tm_ty_closed (c + nb) ob /\ go_ops rest
     end) obs.

Definition ops_tm_lt_closed (c : nat) (obs : list (nat * term)) : Prop :=
  (fix go_ops (obs : list (nat * term)) : Prop :=
     match obs with
     | []               => True
     | (_, ob) :: rest => tm_lt_closed c ob /\ go_ops rest
     end) obs.

Lemma tm_ty_closed_shift_tm : forall t c amount cutoff,
  tm_ty_closed c t -> tm_ty_closed c (shift_tm amount cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall c amount cutoff,
      tm_ty_closed c t -> tm_ty_closed c (shift_tm amount cutoff t))
    (fun ts => forall c amount cutoff,
       fold_right (fun t acc => tm_ty_closed c t /\ acc) True ts ->
       fold_right (fun t acc => tm_ty_closed c t /\ acc) True
         (List.map (shift_tm amount cutoff) ts))
    (fun obs => forall c amount cutoff,
       ops_tm_ty_closed c obs ->
       ops_tm_ty_closed c
         (List.map (fun p => (fst p, shift_tm amount (cutoff + 2) (snd p))) obs))).
  - intros n c amount cutoff Hclosed. exact I.
  - intros t1 t2 IH1 IH2 c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht1 Ht2]. split; [apply IH1|apply IH2]; assumption.
  - intros body T IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Hbody HT]. split; [apply IH; exact Hbody|exact HT].
  - intros t T IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht HT]. split; [apply IH; exact Ht|exact HT].
  - intros bound body IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Hbound Hbody]. split; [exact Hbound|apply IH; exact Hbody].
  - intros t l IH c amount cutoff Hclosed. simpl in *. apply IH. exact Hclosed.
  - intros body IH c amount cutoff Hclosed. simpl in *. apply IH. exact Hclosed.
  - intros K l lts Ts ts IHts c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HTs Hts]. split; [exact HTs|].
    apply IHts. exact Hts.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Hs [Hy Hn]]. repeat split.
    + apply IHs. exact Hs.
    + apply IHy. exact Hy.
    + apply IHn. exact Hn.
  - intros E Ts T_B T_R op_bodies body IHops IHbody c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HTs [HTB [HTR [Hops Hbody]]]]. repeat split; try assumption.
    + rewrite shift_tm_ops_eq_map. apply IHops. exact Hops.
    + apply IHbody. exact Hbody.
  - intros t op Ss A_ret arg IHt IHarg c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht [HSs [HA Harg]]]. repeat split; try assumption.
    + apply IHt. exact Ht.
    + apply IHarg. exact Harg.
  - intros E m Ts T_R op_bodies IHops c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HTs [HTR Hops]]. repeat split; try assumption.
    rewrite shift_tm_ops_eq_map. apply IHops. exact Hops.
  - intros m T_B T_R t IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HTB [HTR Ht]]. repeat split; try assumption.
    apply IH. exact Ht.
  - intros c amount cutoff Hclosed. exact I.
  - intros t ts IHt IHts c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht Hts]. split.
    + apply IHt. exact Ht.
    + apply IHts. exact Hts.
  - intros c amount cutoff Hclosed. exact I.
  - intros nb ob obs IHob IHobs c amount cutoff Hclosed.
    unfold ops_tm_ty_closed, ops_tm_lt_closed in *. simpl in *.
    destruct Hclosed as [Hob Hobs]. split.
    + apply IHob. exact Hob.
    + apply IHobs. exact Hobs.
Qed.

Lemma tm_lt_closed_shift_tm : forall t c amount cutoff,
  tm_lt_closed c t -> tm_lt_closed c (shift_tm amount cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall c amount cutoff,
      tm_lt_closed c t -> tm_lt_closed c (shift_tm amount cutoff t))
    (fun ts => forall c amount cutoff,
       fold_right (fun t acc => tm_lt_closed c t /\ acc) True ts ->
       fold_right (fun t acc => tm_lt_closed c t /\ acc) True
         (List.map (shift_tm amount cutoff) ts))
    (fun obs => forall c amount cutoff,
       ops_tm_lt_closed c obs ->
       ops_tm_lt_closed c
         (List.map (fun p => (fst p, shift_tm amount (cutoff + 2) (snd p))) obs))).
  - intros n c amount cutoff Hclosed. exact I.
  - intros t1 t2 IH1 IH2 c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht1 Ht2]. split; [apply IH1|apply IH2]; assumption.
  - intros body T IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Hbody HT]. split; [apply IH; exact Hbody|exact HT].
  - intros t T IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht HT]. split; [apply IH; exact Ht|exact HT].
  - intros bound body IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Hbound Hbody]. split; [exact Hbound|apply IH; exact Hbody].
  - intros t l IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht Hl]. split; [apply IH; exact Ht|exact Hl].
  - intros body IH c amount cutoff Hclosed. simpl in *. apply IH. exact Hclosed.
  - intros K l lts Ts ts IHts c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Hl [Hlts [HTs Hts]]]. repeat split; try assumption.
    apply IHts. exact Hts.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Hs [Hy Hn]]. repeat split.
    + apply IHs. exact Hs.
    + apply IHy. exact Hy.
    + apply IHn. exact Hn.
  - intros E Ts T_B T_R op_bodies body IHops IHbody c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HTs [HTB [HTR [Hops Hbody]]]]. repeat split; try assumption.
    + rewrite shift_tm_ops_eq_map. apply IHops. exact Hops.
    + apply IHbody. exact Hbody.
  - intros t op Ss A_ret arg IHt IHarg c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht [HSs [HA Harg]]]. repeat split; try assumption.
    + apply IHt. exact Ht.
    + apply IHarg. exact Harg.
  - intros E m Ts T_R op_bodies IHops c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HTs [HTR Hops]]. repeat split; try assumption.
    rewrite shift_tm_ops_eq_map. apply IHops. exact Hops.
  - intros m T_B T_R t IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HTB [HTR Ht]]. repeat split; try assumption.
    apply IH. exact Ht.
  - intros c amount cutoff Hclosed. exact I.
  - intros t ts IHt IHts c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht Hts]. split.
    + apply IHt. exact Ht.
    + apply IHts. exact Hts.
  - intros c amount cutoff Hclosed. exact I.
  - intros nb ob obs IHob IHobs c amount cutoff Hclosed.
    unfold ops_tm_ty_closed, ops_tm_lt_closed in *. simpl in *.
    destruct Hclosed as [Hob Hobs]. split.
    + apply IHob. exact Hob.
    + apply IHobs. exact Hobs.
Qed.

Lemma ty_lt_closed_shift_ty : forall T c_lt a c_ty,
  ty_lt_closed c_lt T -> ty_lt_closed c_lt (shift_ty a c_ty T).
Proof.
  apply (type_list_ind
    (fun T => forall c_lt a c_ty,
       ty_lt_closed c_lt T -> ty_lt_closed c_lt (shift_ty a c_ty T))
    (fun Ts => forall c_lt a c_ty,
       tys_lt_closed c_lt Ts -> tys_lt_closed c_lt (List.map (shift_ty a c_ty) Ts)));
    simpl; intros; try exact I.
  - destruct H1 as [HA [Hl HB]]. repeat split.
    + apply H. exact HA.
    + exact Hl.
    + apply H0. exact HB.
  - destruct H0 as [Hl HTs]. split.
    + exact Hl.
    + apply H. exact HTs.
  - apply H. exact H0.
  - destruct H1 as [HB HA]. split.
    + apply H. exact HB.
    + apply H0. exact HA.
  - destruct H1 as [HA HTs]. split.
    + apply H. exact HA.
    + apply H0. exact HTs.
Qed.

Lemma tys_lt_closed_shift_ty : forall Ts c_lt a c_ty,
  tys_lt_closed c_lt Ts -> tys_lt_closed c_lt (List.map (shift_ty a c_ty) Ts).
Proof.
  induction Ts as [|T Ts IH]; intros c_lt a c_ty Hclosed; simpl in *.
  - exact I.
  - destruct Hclosed as [HT HTs]. split.
    + apply ty_lt_closed_shift_ty. exact HT.
    + apply IH. exact HTs.
Qed.


Lemma lt_lt_closed_shift_lt_below : forall l cutoff c a,
  cutoff <= c -> lt_lt_closed c l -> lt_lt_closed (a + c) (shift_lt a cutoff l).
Proof.
  induction l; intros cutoff c a Hle Hclosed; simpl in *; try exact I.
  - destruct (Nat.leb cutoff n) eqn:Hcut.
    + apply Nat.leb_le in Hcut. lia.
    + apply Nat.leb_gt in Hcut. lia.
  - destruct Hclosed as [H1 H2]. split.
    + eapply IHl1; eauto.
    + eapply IHl2; eauto.
Qed.

Lemma ty_lt_closed_shift_lt_below : forall T cutoff c a,
  cutoff <= c -> ty_lt_closed c T -> ty_lt_closed (a + c) (shift_lt_in_ty a cutoff T).
Proof.
  apply (type_list_ind
    (fun T => forall cutoff c a,
       cutoff <= c -> ty_lt_closed c T -> ty_lt_closed (a + c) (shift_lt_in_ty a cutoff T))
    (fun Ts => forall cutoff c a,
       cutoff <= c -> tys_lt_closed c Ts ->
       tys_lt_closed (a + c) (List.map (shift_lt_in_ty a cutoff) Ts))).
  - intros n cutoff c a Hle Hclosed. exact I.
  - intros A l B IHA IHB cutoff c a Hle Hclosed. simpl in *.
    destruct Hclosed as [HA [Hl HB]]. repeat split.
    + apply IHA; assumption.
    + eapply lt_lt_closed_shift_lt_below; eauto.
    + apply IHB; assumption.
  - intros K l Ts IHTs cutoff c a Hle Hclosed. simpl in *.
    destruct Hclosed as [Hl HTs]. split.
    + eapply lt_lt_closed_shift_lt_below; eauto.
    + apply IHTs; assumption.
  - intros A IHA cutoff c a Hle Hclosed. simpl in *.
    replace (S (a + c)) with (a + S c) by lia.
    apply IHA; [lia|exact Hclosed].
  - intros B A IHB IHA cutoff c a Hle Hclosed. simpl in *.
    destruct Hclosed as [HB HA]. split.
    + apply IHB; assumption.
    + apply IHA; assumption.
  - intros cutoff c a Hle Hclosed. exact I.
  - intros A Ts IHA IHTs cutoff c a Hle Hclosed. simpl in *.
    destruct Hclosed as [HA HTs]. split.
    + apply IHA; assumption.
    + apply IHTs; assumption.
Qed.

Lemma tys_lt_closed_shift_lt_below : forall Ts cutoff c a,
  cutoff <= c -> tys_lt_closed c Ts ->
  tys_lt_closed (a + c) (List.map (shift_lt_in_ty a cutoff) Ts).
Proof.
  induction Ts as [|T Ts IH]; intros cutoff c a Hle Hclosed; simpl in *.
  - exact I.
  - destruct Hclosed as [HT HTs]. split.
    + eapply ty_lt_closed_shift_lt_below; eauto.
    + eapply IH; eauto.
Qed.


Lemma ty_ty_closed_shift_lt : forall T c amount cutoff,
  ty_ty_closed c T -> ty_ty_closed c (shift_lt_in_ty amount cutoff T).
Proof.
  apply (type_list_ind
    (fun T => forall c amount cutoff,
      ty_ty_closed c T -> ty_ty_closed c (shift_lt_in_ty amount cutoff T))
    (fun Ts => forall c amount cutoff,
      tys_ty_closed c Ts -> tys_ty_closed c (List.map (shift_lt_in_ty amount cutoff) Ts))).
  - intros n c amount cutoff Hclosed. exact Hclosed.
  - intros A l B IHA IHB c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HA HB]. split; [apply IHA|apply IHB]; assumption.
  - intros K l Ts IHTs c amount cutoff Hclosed. simpl in *.
    apply IHTs. exact Hclosed.
  - intros A IHA c amount cutoff Hclosed. simpl in *.
    apply IHA. exact Hclosed.
  - intros B A IHB IHA c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HB HA]. split; [apply IHB|apply IHA]; assumption.
  - intros c amount cutoff Hclosed. exact I.
  - intros A Ts IHA IHTs c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HA HTs]. split.
    + apply IHA. exact HA.
    + apply IHTs. exact HTs.
Qed.

Lemma tys_ty_closed_shift_lt : forall Ts c amount cutoff,
  tys_ty_closed c Ts -> tys_ty_closed c (List.map (shift_lt_in_ty amount cutoff) Ts).
Proof.
  induction Ts as [|T Ts IH]; intros c amount cutoff Hclosed; simpl in *.
  - exact I.
  - destruct Hclosed as [HT HTs]. split.
    + apply ty_ty_closed_shift_lt. exact HT.
    + apply IH. exact HTs.
Qed.

Lemma tm_ty_closed_shift_lt : forall t c amount cutoff,
  tm_ty_closed c t -> tm_ty_closed c (shift_lt_in_tm amount cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall c amount cutoff,
      tm_ty_closed c t -> tm_ty_closed c (shift_lt_in_tm amount cutoff t))
    (fun ts => forall c amount cutoff,
      fold_right (fun t acc => tm_ty_closed c t /\ acc) True ts ->
      fold_right (fun t acc => tm_ty_closed c t /\ acc) True
        (List.map (shift_lt_in_tm amount cutoff) ts))
    (fun obs => forall c amount cutoff,
       ops_tm_ty_closed c obs ->
       ops_tm_ty_closed c
         (List.map (fun p => (fst p, shift_lt_in_tm amount cutoff (snd p))) obs))).
  - intros n c amount cutoff Hclosed. exact I.
  - intros t1 t2 IH1 IH2 c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht1 Ht2]. split; [apply IH1|apply IH2]; assumption.
  - intros body T IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Hbody HT]. split.
    + apply IH. exact Hbody.
    + apply ty_ty_closed_shift_lt. exact HT.
  - intros t T IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht HT]. split.
    + apply IH. exact Ht.
    + apply ty_ty_closed_shift_lt. exact HT.
  - intros bound body IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Hbound Hbody]. split.
    + apply ty_ty_closed_shift_lt. exact Hbound.
    + apply IH. exact Hbody.
  - intros t l IH c amount cutoff Hclosed. simpl in *. apply IH. exact Hclosed.
  - intros body IH c amount cutoff Hclosed. simpl in *. apply IH. exact Hclosed.
  - intros K l lts Ts ts IHts c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HTs Hts]. split.
    + apply tys_ty_closed_shift_lt. exact HTs.
    + apply IHts. exact Hts.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Hs [Hy Hn]]. repeat split.
    + apply IHs. exact Hs.
    + apply IHy. exact Hy.
    + apply IHn. exact Hn.
  - intros E Ts T_B T_R op_bodies body IHops IHbody c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HTs [HTB [HTR [Hops Hbody]]]]. repeat split.
    + apply tys_ty_closed_shift_lt. exact HTs.
    + apply ty_ty_closed_shift_lt. exact HTB.
    + apply ty_ty_closed_shift_lt. exact HTR.
    + rewrite shift_lt_in_tm_ops_eq_map. apply IHops. exact Hops.
    + apply IHbody. exact Hbody.
  - intros t op Ss A_ret arg IHt IHarg c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht [HSs [HA Harg]]]. repeat split.
    + apply IHt. exact Ht.
    + apply tys_ty_closed_shift_lt. exact HSs.
    + apply ty_ty_closed_shift_lt. exact HA.
    + apply IHarg. exact Harg.
  - intros E m Ts T_R op_bodies IHops c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HTs [HTR Hops]]. repeat split.
    + apply tys_ty_closed_shift_lt. exact HTs.
    + apply ty_ty_closed_shift_lt. exact HTR.
    + rewrite shift_lt_in_tm_ops_eq_map. apply IHops. exact Hops.
  - intros m T_B T_R t IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HTB [HTR Ht]]. repeat split.
    + apply ty_ty_closed_shift_lt. exact HTB.
    + apply ty_ty_closed_shift_lt. exact HTR.
    + apply IH. exact Ht.
  - intros c amount cutoff Hclosed. exact I.
  - intros t ts IHt IHts c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht Hts]. split.
    + apply IHt. exact Ht.
    + apply IHts. exact Hts.
  - intros c amount cutoff Hclosed. exact I.
  - intros nb ob obs IHob IHobs c amount cutoff Hclosed.
    unfold ops_tm_ty_closed in *. simpl in *.
    destruct Hclosed as [Hob Hobs]. split.
    + apply IHob. exact Hob.
    + apply IHobs. exact Hobs.
Qed.

Lemma tm_lt_closed_shift_ty : forall t c amount cutoff,
  tm_lt_closed c t -> tm_lt_closed c (shift_ty_in_tm amount cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall c amount cutoff,
      tm_lt_closed c t -> tm_lt_closed c (shift_ty_in_tm amount cutoff t))
    (fun ts => forall c amount cutoff,
      fold_right (fun t acc => tm_lt_closed c t /\ acc) True ts ->
      fold_right (fun t acc => tm_lt_closed c t /\ acc) True
        (List.map (shift_ty_in_tm amount cutoff) ts))
    (fun obs => forall c amount cutoff,
       ops_tm_lt_closed c obs ->
       ops_tm_lt_closed c
         (List.map (fun p => (fst p, shift_ty_in_tm amount (cutoff + fst p) (snd p))) obs))).
  - intros n c amount cutoff Hclosed. exact I.
  - intros t1 t2 IH1 IH2 c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht1 Ht2]. split; [apply IH1|apply IH2]; assumption.
  - intros body T IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Hbody HT]. split.
    + apply IH. exact Hbody.
    + apply ty_lt_closed_shift_ty. exact HT.
  - intros t T IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht HT]. split.
    + apply IH. exact Ht.
    + apply ty_lt_closed_shift_ty. exact HT.
  - intros bound body IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Hbound Hbody]. split.
    + apply ty_lt_closed_shift_ty. exact Hbound.
    + apply IH. exact Hbody.
  - intros t l IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht Hl]. split; [apply IH; exact Ht|exact Hl].
  - intros body IH c amount cutoff Hclosed. simpl in *. apply IH. exact Hclosed.
  - intros K l lts Ts ts IHts c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Hl [Hlts [HTs Hts]]]. repeat split; try assumption.
    + apply tys_lt_closed_shift_ty. exact HTs.
    + apply IHts. exact Hts.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Hs [Hy Hn]]. repeat split.
    + apply IHs. exact Hs.
    + apply IHy. exact Hy.
    + apply IHn. exact Hn.
  - intros E Ts T_B T_R op_bodies body IHops IHbody c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HTs [HTB [HTR [Hops Hbody]]]]. repeat split.
    + apply tys_lt_closed_shift_ty. exact HTs.
    + apply ty_lt_closed_shift_ty. exact HTB.
    + apply ty_lt_closed_shift_ty. exact HTR.
    + rewrite shift_ty_in_tm_ops_eq_map. apply IHops. exact Hops.
    + apply IHbody. exact Hbody.
  - intros t op Ss A_ret arg IHt IHarg c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht [HSs [HA Harg]]]. repeat split.
    + apply IHt. exact Ht.
    + apply tys_lt_closed_shift_ty. exact HSs.
    + apply ty_lt_closed_shift_ty. exact HA.
    + apply IHarg. exact Harg.
  - intros E m Ts T_R op_bodies IHops c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HTs [HTR Hops]]. repeat split.
    + apply tys_lt_closed_shift_ty. exact HTs.
    + apply ty_lt_closed_shift_ty. exact HTR.
    + rewrite shift_ty_in_tm_ops_eq_map. apply IHops. exact Hops.
  - intros m T_B T_R t IH c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [HTB [HTR Ht]]. repeat split.
    + apply ty_lt_closed_shift_ty. exact HTB.
    + apply ty_lt_closed_shift_ty. exact HTR.
    + apply IH. exact Ht.
  - intros c amount cutoff Hclosed. exact I.
  - intros t ts IHt IHts c amount cutoff Hclosed. simpl in *.
    destruct Hclosed as [Ht Hts]. split.
    + apply IHt. exact Ht.
    + apply IHts. exact Hts.
  - intros c amount cutoff Hclosed. exact I.
  - intros nb ob obs IHob IHobs c amount cutoff Hclosed.
    unfold ops_tm_lt_closed in *. simpl in *.
    destruct Hclosed as [Hob Hobs]. split.
    + apply IHob. exact Hob.
    + apply IHobs. exact Hobs.
Qed.


Lemma shift_lt_list_closed : forall lts c a,
  lts_lt_closed c lts -> List.map (shift_lt a c) lts = lts.
Proof.
  induction lts as [|l lts IH]; intros c a H; simpl in *; [reflexivity|].
  destruct H as [Hl Hlts]. rewrite shift_lt_closed_lifetime by exact Hl. rewrite IH by exact Hlts. reflexivity.
Qed.

Lemma shift_ty_in_tm_closed : forall t c a,
  tm_ty_closed c t -> shift_ty_in_tm a c t = t.
Proof.
  apply (term_list_ind
    (fun t => forall c a, tm_ty_closed c t -> shift_ty_in_tm a c t = t)
    (fun ts => forall c a,
      (fix go ts := match ts with [] => True | u :: rest => tm_ty_closed c u /\ go rest end) ts ->
      List.map (shift_ty_in_tm a c) ts = ts)
    (fun obs => forall c a,
       ops_tm_ty_closed c obs ->
       List.map (fun p => (fst p, shift_ty_in_tm a (c + fst p) (snd p))) obs
       = obs)); simpl; intros; try reflexivity.
  - destruct H1 as [H1 H2]. rewrite H by exact H1. rewrite H0 by exact H2. reflexivity.
  - destruct H0 as [Hb HT]. rewrite H by exact Hb. rewrite shift_ty_in_ty_closed by exact HT. reflexivity.
  - destruct H0 as [Ht HT]. rewrite H by exact Ht. rewrite shift_ty_in_ty_closed by exact HT. reflexivity.
  - destruct H0 as [HB Hb]. rewrite shift_ty_in_ty_closed by exact HB. rewrite H by exact Hb. reflexivity.
  - rewrite H by exact H0. reflexivity.
  - rewrite H by exact H0. reflexivity.
  - destruct H0 as [HTs Hts]. rewrite map_shift_ty_closed by exact HTs.
    rewrite H by exact Hts. reflexivity.
  - destruct H2 as [Hs [Hy Hn]]. rewrite H by exact Hs. rewrite H0 by exact Hy. rewrite H1 by exact Hn. reflexivity.
  - destruct H1 as [HTs [HTB [HTR [Hops Hb]]]]. rewrite map_shift_ty_closed by exact HTs.
    rewrite shift_ty_in_ty_closed by exact HTB. rewrite shift_ty_in_ty_closed by exact HTR.
    rewrite shift_ty_in_tm_ops_eq_map.
    rewrite H by exact Hops. rewrite H0 by exact Hb. reflexivity.
  - destruct H1 as [Ht [HSs [HA Ha]]]. rewrite H by exact Ht.
    rewrite map_shift_ty_closed by exact HSs.
    rewrite shift_ty_in_ty_closed by exact HA.
    rewrite H0 by exact Ha. reflexivity.
  - destruct H0 as [HTs [HTR Hops]]. rewrite map_shift_ty_closed by exact HTs.
    rewrite shift_ty_in_ty_closed by exact HTR.
    rewrite shift_ty_in_tm_ops_eq_map. rewrite H by exact Hops. reflexivity.
  - destruct H0 as [HTB [HTR Ht]]. rewrite shift_ty_in_ty_closed by exact HTB.
    rewrite shift_ty_in_ty_closed by exact HTR. rewrite H by exact Ht. reflexivity.
  - destruct H1 as [Ht Hts]. rewrite H by exact Ht. rewrite H0 by exact Hts. reflexivity.
  - unfold ops_tm_ty_closed in H1. simpl in H1.
    destruct H1 as [Hob Hobs]. rewrite H by exact Hob. rewrite H0 by exact Hobs.
    reflexivity.
Qed.


Lemma tm_ty_closed_shift_ty_closed0 : forall t amount,
  tm_ty_closed 0 t -> tm_ty_closed 0 (shift_ty_in_tm amount 0 t).
Proof.
  intros t amount Hclosed.
  rewrite shift_ty_in_tm_closed by exact Hclosed. exact Hclosed.
Qed.


Lemma shift_lt_in_tm_closed : forall t c a,
  tm_lt_closed c t -> shift_lt_in_tm a c t = t.
Proof.
  apply (term_list_ind
    (fun t => forall c a, tm_lt_closed c t -> shift_lt_in_tm a c t = t)
    (fun ts => forall c a,
      (fix go ts := match ts with [] => True | u :: rest => tm_lt_closed c u /\ go rest end) ts ->
      List.map (shift_lt_in_tm a c) ts = ts)
    (fun obs => forall c a,
       ops_tm_lt_closed c obs ->
       List.map (fun p => (fst p, shift_lt_in_tm a c (snd p))) obs = obs));
    simpl; intros; try reflexivity.
  - destruct H1 as [H1 H2]. rewrite H by exact H1. rewrite H0 by exact H2. reflexivity.
  - destruct H0 as [Hb HT]. rewrite H by exact Hb. rewrite shift_lt_in_type_closed by exact HT. reflexivity.
  - destruct H0 as [Ht HT]. rewrite H by exact Ht. rewrite shift_lt_in_type_closed by exact HT. reflexivity.
  - destruct H0 as [HB Hb]. rewrite shift_lt_in_type_closed by exact HB. rewrite H by exact Hb. reflexivity.
  - destruct H0 as [Ht Hl]. rewrite H by exact Ht. rewrite shift_lt_closed_lifetime by exact Hl. reflexivity.
  - rewrite H by exact H0. reflexivity.
  - destruct H0 as [Hl [Hlts [HTs Hts]]]. rewrite shift_lt_closed_lifetime by exact Hl.
    rewrite shift_lt_list_closed by exact Hlts. rewrite map_shift_lt_in_ty_closed by exact HTs.
    rewrite H by exact Hts. reflexivity.
  - destruct H2 as [Hs [Hy Hn]]. rewrite H by exact Hs. rewrite H0 by exact Hy. rewrite H1 by exact Hn. reflexivity.
  - destruct H1 as [HTs [HTB [HTR [Hops Hb]]]]. rewrite map_shift_lt_in_ty_closed by exact HTs.
    rewrite shift_lt_in_type_closed by exact HTB. rewrite shift_lt_in_type_closed by exact HTR.
    rewrite shift_lt_in_tm_ops_eq_map.
    rewrite H by exact Hops. rewrite H0 by exact Hb. reflexivity.
  - destruct H1 as [Ht [HSs [HA Ha]]]. rewrite H by exact Ht.
    rewrite map_shift_lt_in_ty_closed by exact HSs.
    rewrite shift_lt_in_type_closed by exact HA.
    rewrite H0 by exact Ha. reflexivity.
  - destruct H0 as [HTs [HTR Hops]]. rewrite map_shift_lt_in_ty_closed by exact HTs.
    rewrite shift_lt_in_type_closed by exact HTR.
    rewrite shift_lt_in_tm_ops_eq_map. rewrite H by exact Hops. reflexivity.
  - destruct H0 as [HTB [HTR Ht]]. rewrite shift_lt_in_type_closed by exact HTB.
    rewrite shift_lt_in_type_closed by exact HTR. rewrite H by exact Ht. reflexivity.
  - destruct H1 as [Ht Hts]. rewrite H by exact Ht. rewrite H0 by exact Hts. reflexivity.
  - unfold ops_tm_lt_closed in H1. simpl in H1.
    destruct H1 as [Hob Hobs]. rewrite H by exact Hob. rewrite H0 by exact Hobs.
    reflexivity.
Qed.


Lemma tm_lt_closed_shift_lt_closed0 : forall t amount,
  tm_lt_closed 0 t -> tm_lt_closed 0 (shift_lt_in_tm amount 0 t).
Proof.
  intros t amount Hclosed.
  rewrite shift_lt_in_tm_closed by exact Hclosed. exact Hclosed.
Qed.


(* ================================================================== *)
(* list-substitution properties                                       *)
(*                                                                    *)
(* Connect the simultaneous list-substitution operations with their   *)
(* iterated single-substitution counterparts, and prove the obvious   *)
(* lookup laws used in the match-yes preservation argument.           *)
(* ================================================================== *)


Lemma subst_list_lt_in_ty_nil : forall T, subst_list_lt_in_ty [] T = T.
Proof. reflexivity. Qed.


(* ================================================================== *)
(*                                                                    *)
(*   TYPING-DEPENDENT SUBSTITUTION / WEAKENING / SHIFT LEMMAS         *)
(*                                                                    *)
(* These lemmas mention the typing (`⊢ₜ`) and subtyping (`<::`, `<:`) *)
(* judgments, so they live here — after `Require Import Typing` —     *)
(* rather than in the syntax-only σ-law section above.  Their content *)
(* is the standard de Bruijn plumbing of a System-F₊-with-lifetimes   *)
(* metatheory.                                                        *)
(* ================================================================== *)

(* ---- Pure de Bruijn σ-laws (shift / subst commutation) ---------- *)

(* shift / subst_lt commute (de Bruijn).  Proven by induction on the  *)
(* lifetime, with case analysis on the de Bruijn index comparisons.   *)
Lemma shift_subst_lt_comm : forall l x,
  shift_lt 1 0 (subst_lt x lt_free l) =
  subst_lt (S x) lt_free (shift_lt 1 0 l).
Proof.
  induction l as [y | | | l1 IH1 l2 IH2]; intro x; try reflexivity.
  - (* lt_var y *)
    simpl.
    destruct (Nat.eqb_spec y x) as [Hyx | Hyx].
    + subst y. simpl.
      destruct (Nat.eqb_spec (x + 1) (S x)) as [_ | Hcon].
      * reflexivity.
      * exfalso. apply Hcon. lia.
    + destruct (Nat.ltb_spec x y) as [Hlt | Hge].
      * simpl.
        destruct (Nat.eqb_spec (y + 1) (S x)) as [Heq | _].
        -- exfalso. lia.
        -- destruct (Nat.ltb_spec (S x) (y + 1)) as [_ | Hge2].
           ++ simpl. f_equal. lia.
           ++ exfalso. lia.
      * simpl.
        destruct (Nat.eqb_spec (y + 1) (S x)) as [Heq | _].
        -- exfalso. lia.
        -- destruct (Nat.ltb_spec (S x) (y + 1)) as [Hlt2 | _].
           ++ exfalso. lia.
           ++ reflexivity.
  - (* lt_join *)
    simpl. rewrite IH1, IH2. reflexivity.
Qed.

(* subst_lt_in_ty's internal list fix coincides with map. *)
Lemma subst_lt_in_ty_ctor_eq : forall var replacement K l Ts,
  subst_lt_in_ty var replacement (type_ctor K l Ts)
    = type_ctor K (subst_lt var replacement l)
                  (List.map (subst_lt_in_ty var replacement) Ts).
Proof.
  intros var replacement K l Ts.
  induction Ts as [|A rest IH].
  - reflexivity.
  - simpl. simpl in IH. inversion IH. reflexivity.
Qed.

(* `iter_subst_lt_in_ty ws T` substitutes the witnesses ws sequentially *)
(* at de Bruijn position 0, decrementing the remaining lt-vars after    *)
(* each step.  This matches `elim_ty_n`'s iteration where each step     *)
(* closes a binder via `subst_lt 0 lt_free`.                            *)
Fixpoint iter_subst_lt_in_ty (ws : list lifetime) (T : type) : type :=
  match ws with
  | []        => T
  | w :: rest => iter_subst_lt_in_ty rest (subst_lt_in_ty 0 w T)
  end.


(* Bridge: parallel lt-substitution `subst_list_lt_in_ty` is exactly    *)
(* the iterated single-var substitution `iter_subst_lt_in_ty` applied   *)
(* to the *pre-shifted* witness list.  `subst_list_lt_in_ty` shifts     *)
(* each witness by the number of remaining witnesses before             *)
(* substituting at position 0; the faithful bridge threads that         *)
(* shift through.                                                       *)
Fixpoint shift_each_lt (lts : list lifetime) : list lifetime :=
  match lts with
  | []        => []
  | l :: rest => shift_lt (List.length rest) 0 l :: shift_each_lt rest
  end.


Lemma subst_list_lt_in_ty_eq_iter : forall lts T,
  subst_list_lt_in_ty lts T = iter_subst_lt_in_ty (shift_each_lt lts) T.
Proof.
  intros lts; induction lts as [|l rest IH]; intros T; simpl.
  - reflexivity.
  - apply IH.
Qed.

(* =================================================================== *)
(*  lt_of_ty_ctx: rewrite equations, var-bound invariant, fuel         *)
(*  sufficiency, and shift commutation.                                *)
(*                                                                     *)
(*  The shift-on-lookup discipline makes EVERY context structurally    *)
(*  acyclic (a bound looked up across k binders is var-bounded by k),  *)
(*  so fuel = |Γ| always suffices: the computed lt_∅ is independent    *)
(*  of any fuel ≥ |Γ|.  This is what lets context weakening go through *)
(*  at the `SA_Any` rule without a separate well-formedness premise.   *)
(* =================================================================== *)

(* External per-field minimum, matching the internal field fold. *)
Definition lt_of_ty_ctx_list (f : nat) (G : ctx) (Ts : list type) : lifetime :=
  fold_right (fun A acc => lt_join (lt_of_ty_ctx f G A) acc) lt_free Ts.

Lemma lt_of_ty_ctx_list_nil : forall f G, lt_of_ty_ctx_list f G [] = lt_free.
Proof. reflexivity. Qed.
Lemma lt_of_ty_ctx_list_cons : forall f G A Ts,
  lt_of_ty_ctx_list f G (A :: Ts)
  = lt_join (lt_of_ty_ctx f G A) (lt_of_ty_ctx_list f G Ts).
Proof. reflexivity. Qed.

(* Clean rewrite equations for each head constructor. *)
Lemma lt_of_ty_ctx_var : forall f G a,
  lt_of_ty_ctx f G (type_var a)
  = match f with
    | O => lt_free
    | S f' => match ctx_lookup_ty G a with
              | Some B => lt_of_ty_ctx f' G B
              | None => lt_free end
    end.
Proof. intros f G a. destruct f; reflexivity. Qed.

Lemma lt_of_ty_ctx_fun : forall f G A l B, lt_of_ty_ctx f G (type_fun A l B) = l.
Proof. intros f G A l B. destruct f; reflexivity. Qed.

Lemma lt_of_ty_ctx_ltall : forall f G A, lt_of_ty_ctx f G (type_lt_all A) = lt_local.
Proof. intros f G A. destruct f; reflexivity. Qed.

Lemma lt_of_ty_ctx_tyall : forall f G B A, lt_of_ty_ctx f G (type_ty_all B A) = lt_local.
Proof. intros f G B A. destruct f; reflexivity. Qed.

Lemma lt_of_ty_ctx_ctor : forall f G K l Ts,
  lt_of_ty_ctx f G (type_ctor K l Ts) = lt_join l (lt_of_ty_ctx_list f G Ts).
Proof.
  intros f G K l Ts. unfold lt_of_ty_ctx_list.
  destruct f as [|f']; simpl; f_equal;
    induction Ts as [|A rest IH]; simpl; try reflexivity; rewrite IH; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Unfolding equations for shifts on type constructors.               *)
(* ------------------------------------------------------------------ *)

Lemma shift_ty_var_eq : forall a c n,
  shift_ty a c (type_var n) = type_var (if Nat.leb c n then n + a else n).
Proof. reflexivity. Qed.
Lemma shift_ty_ctor_eq : forall a c K l Ts,
  shift_ty a c (type_ctor K l Ts) = type_ctor K l (List.map (shift_ty a c) Ts).
Proof. reflexivity. Qed.
Lemma shift_lt_in_ty_var_eq : forall a c n,
  shift_lt_in_ty a c (type_var n) = type_var n.
Proof. reflexivity. Qed.
Lemma shift_lt_in_ty_ctor_eq : forall a c K l Ts,
  shift_lt_in_ty a c (type_ctor K l Ts)
  = type_ctor K (shift_lt a c l) (List.map (shift_lt_in_ty a c) Ts).
Proof. reflexivity. Qed.

(* shift_ty 1 0 (insert a bind_ty at the front) leaves the computed lt
   unchanged at equal fuel. *)
Lemma lt_of_ty_ctx_shift_ty : forall f G B T,
  lt_of_ty_ctx f (bind_ty B :: G) (shift_ty 1 0 T) = lt_of_ty_ctx f G T.
Proof.
  induction f as [|f' IHf]; intros G B T.
  - induction T using type_list_ind with
      (Q := fun Ts => lt_of_ty_ctx_list 0 (bind_ty B::G) (List.map (shift_ty 1 0) Ts)
                      = lt_of_ty_ctx_list 0 G Ts).
    + simpl shift_ty. rewrite !(lt_of_ty_ctx_var 0). reflexivity.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_fun. reflexivity.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_ctor. f_equal. exact IHT.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite IHT, IHT0. reflexivity.
  - induction T using type_list_ind with
      (Q := fun Ts => lt_of_ty_ctx_list (S f') (bind_ty B::G) (List.map (shift_ty 1 0) Ts)
                      = lt_of_ty_ctx_list (S f') G Ts).
    + simpl shift_ty. rewrite Nat.add_1_r.
      rewrite (lt_of_ty_ctx_var (S f')). rewrite (lt_of_ty_ctx_var (S f')).
      simpl ctx_lookup_ty.
      destruct (ctx_lookup_ty G n) as [B'|] eqn:E; simpl.
      * apply IHf.
      * reflexivity.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_fun. reflexivity.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_ctor. f_equal. exact IHT.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite IHT, IHT0. reflexivity.
Qed.

(* "var-bounded by k": every type-var inspected by lt_of_ty_ctx (head or
   in ctor fields, never under a binder) has index >= k. *)
Fixpoint VB (k : nat) (T : type) : Prop :=
  match T with
  | type_var a => k <= a
  | type_fun _ _ _ => True
  | type_ctor _ _ Ts =>
      (fix all (l : list type) : Prop :=
         match l with [] => True | A :: r => VB k A /\ all r end) Ts
  | type_lt_all _ => True
  | type_ty_all _ _ => True
  end.

Definition VBL (k : nat) (Ts : list type) : Prop :=
  fold_right (fun A acc => VB k A /\ acc) True Ts.

Lemma VB_ctor : forall k K l Ts, VB k (type_ctor K l Ts) = VBL k Ts.
Proof. reflexivity. Qed.
Lemma VBL_cons : forall k A Ts, VBL k (A :: Ts) = (VB k A /\ VBL k Ts).
Proof. reflexivity. Qed.

Lemma shift_ty_VB : forall T k, VB k T -> VB (S k) (shift_ty 1 0 T).
Proof.
  intros T. induction T using type_list_ind with
    (Q := fun Ts => forall k, VBL k Ts -> VBL (S k) (List.map (shift_ty 1 0) Ts));
    intros k H.
  - rewrite shift_ty_var_eq. simpl Nat.leb. simpl in H. simpl. rewrite Nat.add_1_r. lia.
  - exact I.
  - rewrite shift_ty_ctor_eq. rewrite VB_ctor. rewrite VB_ctor in H. apply IHT. exact H.
  - exact I.
  - exact I.
  - exact I.
  - rewrite VBL_cons in H. destruct H as [Ha Hr].
    cbn [List.map]. rewrite VBL_cons. split; [apply IHT; exact Ha | apply IHT0; exact Hr].
Qed.

Lemma shift_lt_in_ty_VB : forall T k, VB k T -> VB k (shift_lt_in_ty 1 0 T).
Proof.
  intros T. induction T using type_list_ind with
    (Q := fun Ts => forall k, VBL k Ts -> VBL k (List.map (shift_lt_in_ty 1 0) Ts));
    intros k H.
  - rewrite shift_lt_in_ty_var_eq. exact H.
  - exact I.
  - rewrite shift_lt_in_ty_ctor_eq. rewrite VB_ctor. rewrite VB_ctor in H. apply IHT. exact H.
  - exact I.
  - exact I.
  - exact I.
  - rewrite VBL_cons in H. destruct H as [Ha Hr].
    cbn [List.map]. rewrite VBL_cons. split; [apply IHT; exact Ha | apply IHT0; exact Hr].
Qed.

Lemma VB_0 : forall T, VB 0 T.
Proof.
  intros T. induction T using type_list_ind with (Q := fun Ts => VBL 0 Ts).
  - simpl. apply Nat.le_0_l.
  - exact I.
  - rewrite VB_ctor. exact IHT.
  - exact I.
  - exact I.
  - exact I.
  - rewrite VBL_cons. split; [exact IHT | exact IHT0].
Qed.

(* The acyclicity invariant holds for ARBITRARY contexts, purely because
   ctx_lookup_ty shifts the looked-up bound up past the binders crossed. *)
Lemma ctx_inv_all : forall G a B, ctx_lookup_ty G a = Some B -> VB (S a) B.
Proof.
  induction G as [|b rest IH]; intros a B H.
  - simpl in H. discriminate.
  - destruct b as [C|C|D|tg n1 n2 Ts Tr|eg n_a ops]; simpl in H.
    + apply IH. exact H.
    + destruct a as [|a'].
      * injection H as H. subst B. apply (shift_ty_VB C 0). apply VB_0.
      * destruct (ctx_lookup_ty rest a') as [B'|] eqn:E; simpl in H; try discriminate.
        injection H as H. subst B. apply (shift_ty_VB B' (S a')). apply IH. exact E.
    + destruct (ctx_lookup_ty rest a) as [B'|] eqn:E; simpl in H; try discriminate.
      injection H as H. subst B. apply shift_lt_in_ty_VB. apply IH. exact E.
    + apply IH. exact H.
    + apply IH. exact H.
Qed.

Lemma ctx_lookup_ty_None : forall G a, length G <= a -> ctx_lookup_ty G a = None.
Proof.
  induction G as [|b rest IH]; intros a H.
  - reflexivity.
  - simpl in H. destruct b as [C|C|D|tg n1 n2 Ts Tr|eg n_a ops].
    + simpl. apply IH. lia.
    + simpl. destruct a as [|a'].
      * exfalso. lia.
      * rewrite IH by lia. reflexivity.
    + simpl. rewrite IH by lia. reflexivity.
    + simpl. apply IH. lia.
    + simpl. apply IH. lia.
Qed.

Lemma lt_of_ty_ctx_var_oob : forall f G a,
  ctx_lookup_ty G a = None -> lt_of_ty_ctx f G (type_var a) = lt_free.
Proof.
  intros f G a H. rewrite lt_of_ty_ctx_var.
  destruct f; [reflexivity | rewrite H; reflexivity].
Qed.

(* Fuel irrelevance above the threshold (|G| - k). *)
Lemma lt_of_ty_ctx_fuel_irrel : forall f g T G k,
  VB k T -> length G <= k + f -> length G <= k + g ->
  lt_of_ty_ctx f G T = lt_of_ty_ctx g G T.
Proof.
  induction f as [|f' IHf]; intros g T G k HVB Hf Hg.
  - revert HVB.
    induction T using type_list_ind with
      (Q := fun Ts => VBL k Ts -> lt_of_ty_ctx_list 0 G Ts = lt_of_ty_ctx_list g G Ts);
      intro HVB.
    + simpl in HVB.
      assert (Hoob : ctx_lookup_ty G n = None) by (apply ctx_lookup_ty_None; lia).
      rewrite !(lt_of_ty_ctx_var_oob _ _ _ Hoob). reflexivity.
    + rewrite !lt_of_ty_ctx_fun. reflexivity.
    + rewrite !lt_of_ty_ctx_ctor. rewrite VB_ctor in HVB. f_equal. apply IHT. exact HVB.
    + rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + rewrite VBL_cons in HVB. destruct HVB as [Ha Hr].
      rewrite !lt_of_ty_ctx_list_cons. rewrite IHT by exact Ha. rewrite IHT0 by exact Hr.
      reflexivity.
  - revert HVB.
    induction T using type_list_ind with
      (Q := fun Ts => VBL k Ts -> lt_of_ty_ctx_list (S f') G Ts = lt_of_ty_ctx_list g G Ts);
      intro HVB.
    + simpl in HVB.
      destruct (ctx_lookup_ty G n) as [B|] eqn:E.
      * assert (Hlt : n < length G).
        { destruct (Nat.le_gt_cases (length G) n) as [Hle|Hgt]; [|exact Hgt].
          rewrite ctx_lookup_ty_None in E by exact Hle. discriminate. }
        destruct g as [|g']. { exfalso. lia. }
        rewrite (lt_of_ty_ctx_var (S f') G n), (lt_of_ty_ctx_var (S g') G n), E.
        apply (IHf g' B G (S n)).
        -- exact (ctx_inv_all G n B E).
        -- lia.
        -- lia.
      * rewrite !(lt_of_ty_ctx_var_oob _ _ _ E). reflexivity.
    + rewrite !lt_of_ty_ctx_fun. reflexivity.
    + rewrite !lt_of_ty_ctx_ctor. rewrite VB_ctor in HVB. f_equal. apply IHT. exact HVB.
    + rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + rewrite VBL_cons in HVB. destruct HVB as [Ha Hr].
      rewrite !lt_of_ty_ctx_list_cons. rewrite IHT by exact Ha. rewrite IHT0 by exact Hr.
      reflexivity.
Qed.

Lemma shift_lt_join_eq : forall a c l1 l2,
  shift_lt a c (lt_join l1 l2) = lt_join (shift_lt a c l1) (shift_lt a c l2).
Proof. reflexivity. Qed.
Lemma shift_lt_in_ty_fun_eq : forall a c A l B,
  shift_lt_in_ty a c (type_fun A l B)
  = type_fun (shift_lt_in_ty a c A) (shift_lt a c l) (shift_lt_in_ty a c B).
Proof. reflexivity. Qed.

(* shift_lt_in_ty commutation: lifetimes shift, then computing lt_∅ equals
   computing lt_∅ then shifting the resulting lifetime. *)
Lemma lt_of_ty_ctx_shift_lt_in_ty : forall f G D T,
  lt_of_ty_ctx f (bind_lt D :: G) (shift_lt_in_ty 1 0 T)
  = shift_lt 1 0 (lt_of_ty_ctx f G T).
Proof.
  induction f as [|f' IHf]; intros G D T.
  - induction T using type_list_ind with
      (Q := fun Ts => lt_of_ty_ctx_list 0 (bind_lt D::G) (List.map (shift_lt_in_ty 1 0) Ts)
                      = shift_lt 1 0 (lt_of_ty_ctx_list 0 G Ts)).
    + rewrite shift_lt_in_ty_var_eq. rewrite !(lt_of_ty_ctx_var 0). reflexivity.
    + rewrite shift_lt_in_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. reflexivity.
    + rewrite shift_lt_in_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor. rewrite shift_lt_join_eq.
      f_equal. exact IHT.
    + rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite shift_lt_join_eq.
      rewrite IHT, IHT0. reflexivity.
  - induction T using type_list_ind with
      (Q := fun Ts => lt_of_ty_ctx_list (S f') (bind_lt D::G) (List.map (shift_lt_in_ty 1 0) Ts)
                      = shift_lt 1 0 (lt_of_ty_ctx_list (S f') G Ts)).
    + rewrite shift_lt_in_ty_var_eq.
      rewrite (lt_of_ty_ctx_var (S f') (bind_lt D::G) n), (lt_of_ty_ctx_var (S f') G n).
      simpl ctx_lookup_ty.
      destruct (ctx_lookup_ty G n) as [B|] eqn:E; simpl.
      * apply IHf.
      * reflexivity.
    + rewrite shift_lt_in_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. reflexivity.
    + rewrite shift_lt_in_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor. rewrite shift_lt_join_eq.
      f_equal. exact IHT.
    + rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite shift_lt_join_eq.
      rewrite IHT, IHT0. reflexivity.
Qed.

(* Weakening corollaries for lt_of_ty_G (= lt_of_ty_ctx (length Γ) Γ). *)
Lemma lt_of_ty_G_weaken_ty : forall G B T,
  lt_of_ty_G (bind_ty B :: G) (shift_ty 1 0 T) = lt_of_ty_G G T.
Proof.
  intros G B T. unfold lt_of_ty_G. simpl length. rewrite lt_of_ty_ctx_shift_ty.
  apply (lt_of_ty_ctx_fuel_irrel (S (length G)) (length G) T G 0).
  - apply VB_0.
  - simpl; lia.
  - simpl; lia.
Qed.

Lemma lt_of_ty_G_weaken_lt : forall G D T,
  lt_of_ty_G (bind_lt D :: G) (shift_lt_in_ty 1 0 T) = shift_lt 1 0 (lt_of_ty_G G T).
Proof.
  intros G D T. unfold lt_of_ty_G. simpl length. rewrite lt_of_ty_ctx_shift_lt_in_ty.
  f_equal.
  apply (lt_of_ty_ctx_fuel_irrel (S (length G)) (length G) T G 0).
  - apply VB_0.
  - simpl; lia.
  - simpl; lia.
Qed.

Lemma lt_of_ty_ctx_weaken_tm : forall f G A T,
  lt_of_ty_ctx f (bind_tm A :: G) T = lt_of_ty_ctx f G T.
Proof.
  induction f as [|f IHf].
  - intros G A T. revert G A.
    induction T using type_list_ind with
      (P := fun T => forall G A,
        lt_of_ty_ctx 0 (bind_tm A :: G) T = lt_of_ty_ctx 0 G T)
      (Q := fun Ts => forall G A,
        (let fix gol (Ts : list type) : lifetime :=
           match Ts with
           | [] => lt_free
           | T :: rest => lt_join (lt_of_ty_ctx 0 (bind_tm A :: G) T) (gol rest)
           end in gol Ts) =
        (let fix gol (Ts : list type) : lifetime :=
           match Ts with
           | [] => lt_free
           | T :: rest => lt_join (lt_of_ty_ctx 0 G T) (gol rest)
          end in gol Ts)); intros; simpl; try reflexivity;
        try (f_equal; match goal with H : forall _ _, _ = _ |- _ => apply H end).
  - intros G A T. revert G A.
    induction T using type_list_ind with
      (P := fun T => forall G A,
        lt_of_ty_ctx (S f) (bind_tm A :: G) T = lt_of_ty_ctx (S f) G T)
      (Q := fun Ts => forall G A,
        (let fix gol (Ts : list type) : lifetime :=
           match Ts with
           | [] => lt_free
           | T :: rest => lt_join (lt_of_ty_ctx (S f) (bind_tm A :: G) T) (gol rest)
           end in gol Ts) =
        (let fix gol (Ts : list type) : lifetime :=
           match Ts with
           | [] => lt_free
           | T :: rest => lt_join (lt_of_ty_ctx (S f) G T) (gol rest)
              end in gol Ts)); intros; simpl; try reflexivity;
            try (f_equal; match goal with H : forall _ _, _ = _ |- _ => apply H end).
            destruct (ctx_lookup_ty G n) as [B|]; [apply IHf|reflexivity].
Qed.

Lemma lt_of_ty_G_weaken_tm : forall G A T,
  lt_of_ty_G (bind_tm A :: G) T = lt_of_ty_G G T.
Proof.
  intros G A T. unfold lt_of_ty_G. simpl length.
  rewrite lt_of_ty_ctx_weaken_tm.
  symmetry.
  apply (lt_of_ty_ctx_fuel_irrel (length G) (S (length G)) T G 0).
  - apply VB_0.
  - lia.
  - lia.
Qed.
