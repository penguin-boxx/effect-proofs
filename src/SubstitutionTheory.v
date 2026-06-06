Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
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
(* ----------------                                                   *)
(*   <op>_<sort>          — single-sort version (e.g. shift_lt)       *)
(*   <op>_<sort>_in_<carrier> — cross-sort version                    *)
(*                                                                    *)
(* For every fixpoint in Substitution.v we state, where applicable:   *)
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
(* SECTION 1 — Sanity examples (unit tests)                           *)
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
  shift_tm 1 0 (term_match (term_var 0) 1 2 (term_var 1) (term_var 0))
    = term_match (term_var 1) 1 2 (term_var 1) (term_var 1).
Proof. reflexivity. Qed.

(* Free variable inside yes_body (index >= arity) IS shifted. *)
Example shift_tm_match_arity_free :
  shift_tm 1 0 (term_match (term_var 0) 1 2 (term_var 2) (term_var 0))
    = term_match (term_var 1) 1 2 (term_var 3) (term_var 1).
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
  Hypothesis Hvar        : forall n, P (term_var n).
  Hypothesis Happ        : forall t1 t2, P t1 -> P t2 -> P (term_app t1 t2).
  Hypothesis Hlam        : forall body T, P body -> P (term_lam body T).
  Hypothesis Hty_app     : forall t T, P t -> P (term_ty_app t T).
  Hypothesis Hty_lam     : forall bound body, P body -> P (term_ty_lam bound body).
  Hypothesis Hlt_app     : forall t l, P t -> P (term_lt_app t l).
  Hypothesis Hlt_lam     : forall body, P body -> P (term_lt_lam body).
  Hypothesis Hctor       : forall K l lts Ts ts, Q ts -> P (term_ctor K l lts Ts ts).
  Hypothesis Hmatch      : forall scrut tag arity yes_body no_body,
    P scrut -> P yes_body -> P no_body ->
    P (term_match scrut tag arity yes_body no_body).
  Hypothesis Hhandle     : forall E Ts op_body body,
    P op_body -> P body -> P (term_handle E Ts op_body body).
  Hypothesis Hperform    : forall t Ss arg, P t -> P arg -> P (term_perform t Ss arg).
  Hypothesis Hcap        : forall E m Ts op_body, P op_body -> P (term_cap E m Ts op_body).
  Hypothesis Hhandler_m  : forall m t, P t -> P (term_handler_m m t).
  Hypothesis Hresume     : forall m b, P b -> P (term_resume m b).
  Hypothesis Hnil        : Q [].
  Hypothesis Hcons       : forall t ts, P t -> Q ts -> Q (t :: ts).
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
    | term_match scrut tag arity yes_body no_body =>
        Hmatch scrut tag arity yes_body no_body
          (term_list_ind scrut) (term_list_ind yes_body) (term_list_ind no_body)
    | term_handle E Ts op_body body =>
        Hhandle E Ts op_body body (term_list_ind op_body) (term_list_ind body)
    | term_perform t Ss arg => Hperform t Ss arg (term_list_ind t) (term_list_ind arg)
    | term_cap E m Ts op_body => Hcap E m Ts op_body (term_list_ind op_body)
    | term_handler_m m t => Hhandler_m m t (term_list_ind t)
    | term_resume m b => Hresume m b (term_list_ind b)
    end.
End TermListInd.

(* Helper: the inline 'go' fixpoint in each shift equals List.map *)
Lemma shift_lt_in_ty_go_eq_map : forall amount cutoff Ts,
  (fix go Ts := match Ts with [] => [] | A :: rest => shift_lt_in_ty amount cutoff A :: go rest end) Ts =
  List.map (shift_lt_in_ty amount cutoff) Ts.
Proof. intros; induction Ts; simpl; congruence. Qed.

Lemma shift_ty_go_eq_map : forall amount cutoff Ts,
  (fix go Ts := match Ts with [] => [] | A :: rest => shift_ty amount cutoff A :: go rest end) Ts =
  List.map (shift_ty amount cutoff) Ts.
Proof. intros; induction Ts; simpl; congruence. Qed.

Lemma shift_tm_go_eq_map : forall amount cutoff ts,
  (fix go ts := match ts with [] => [] | u :: rest => shift_tm amount cutoff u :: go rest end) ts =
  List.map (shift_tm amount cutoff) ts.
Proof. intros; induction ts; simpl; congruence. Qed.

Lemma shift_ty_in_tm_go_eq_map : forall amount cutoff ts,
  (fix go ts := match ts with [] => [] | u :: rest => shift_ty_in_tm amount cutoff u :: go rest end) ts =
  List.map (shift_ty_in_tm amount cutoff) ts.
Proof. intros; induction ts; simpl; congruence. Qed.

Lemma shift_lt_in_tm_go_eq_map : forall amount cutoff ts,
  (fix go ts := match ts with [] => [] | u :: rest => shift_lt_in_tm amount cutoff u :: go rest end) ts =
  List.map (shift_lt_in_tm amount cutoff) ts.
Proof. intros; induction ts; simpl; congruence. Qed.

(* ================================================================== *)
(* SECTION 2 — shift_zero                                             *)
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

Lemma shift_lt_in_ty_zero : forall c T,
  shift_lt_in_ty 0 c T = T.
Proof.
  enough (H : forall T, forall c, shift_lt_in_ty 0 c T = T).
  { intros c T; apply H. }
  apply (type_list_ind
    (fun T => forall c, shift_lt_in_ty 0 c T = T)
    (fun Ts => forall c, List.map (shift_lt_in_ty 0 c) Ts = Ts)).
  - intro c; reflexivity.
  - intros A l B HA HB c; simpl; rewrite shift_lt_zero, HA, HB; reflexivity.
  - intros K l Ts HTs c; simpl; rewrite shift_lt_zero, shift_lt_in_ty_go_eq_map;
    f_equal; apply HTs.
  - intros A HA c; simpl; rewrite HA; reflexivity.
  - intros B A HB HA c; simpl; rewrite HB, HA; reflexivity.
  - intro c; reflexivity.
  - intros A Ts HA HTs c; simpl; rewrite HA; f_equal; apply HTs.
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
  - intros K l Ts HTs c; simpl; rewrite shift_ty_go_eq_map; f_equal; apply HTs.
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
    (fun ts => forall c, List.map (shift_tm 0 c) ts = ts)).
  - intros n c; simpl; destruct (Nat.leb c n); simpl; f_equal; lia.
  - intros t1 t2 H1 H2 c; simpl; rewrite H1, H2; reflexivity.
  - intros body T H c; simpl; rewrite H; reflexivity.
  - intros t T H c; simpl; rewrite H; reflexivity.
  - intros bound body H c; simpl; rewrite H; reflexivity.
  - intros t l H c; simpl; rewrite H; reflexivity.
  - intros body H c; simpl; rewrite H; reflexivity.
  - intros K l lts Ts ts Hts c; simpl; rewrite shift_tm_go_eq_map; f_equal; apply Hts.
  - intros scrut tag arity yes_body no_body Hs Hy Hn c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E Ts op_body body Hop Hb c; simpl;
    rewrite Hop, Hb; reflexivity.
  - intros t Ss arg Ht Ha c; simpl; rewrite Ht, Ha; reflexivity.
  - intros E m Ts op_body Hop c; simpl; rewrite Hop; reflexivity.
  - intros m t H c; simpl; rewrite H; reflexivity.
  - intros m b H c; simpl; rewrite H; reflexivity.
  - intro c; reflexivity.
  - intros t ts Ht Hts c; simpl; rewrite Ht; f_equal; apply Hts.
Qed.

Lemma shift_ty_in_tm_zero : forall c t,
  shift_ty_in_tm 0 c t = t.
Proof.
  enough (H : forall t, forall c, shift_ty_in_tm 0 c t = t).
  { intros c t; apply H. }
  apply (term_list_ind
    (fun t => forall c, shift_ty_in_tm 0 c t = t)
    (fun ts => forall c, List.map (shift_ty_in_tm 0 c) ts = ts)).
  - intro c; reflexivity.
  - intros t1 t2 H1 H2 c; simpl; rewrite H1, H2; reflexivity.
  - intros body T H c; simpl; rewrite H, shift_ty_zero; reflexivity.
  - intros t T H c; simpl; rewrite H, shift_ty_zero; reflexivity.
  - intros bound body H c; simpl; rewrite H, shift_ty_zero; reflexivity.
  - intros t l H c; simpl; rewrite H; reflexivity.
  - intros body H c; simpl; rewrite H; reflexivity.
  - intros K l lts Ts ts Hts c; simpl.
    unfold shift_ty_list. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, shift_ty_in_tm_go_eq_map; f_equal; apply Hts.
    + intro T; apply shift_ty_zero.
  - intros scrut tag arity yes_body no_body Hs Hy Hn c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E Ts op_body body Hop Hb c; simpl.
    unfold shift_ty_list. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, Hop, Hb; reflexivity.
    + intro T; apply shift_ty_zero.
  - intros t Ss arg Ht Ha c; simpl.
    unfold shift_ty_list. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, Ht, Ha; reflexivity.
    + intro T; apply shift_ty_zero.
  - intros E m Ts op_body Hop c; simpl.
    unfold shift_ty_list. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, Hop; reflexivity.
    + intro T; apply shift_ty_zero.
  - intros m t H c; simpl; rewrite H; reflexivity.
  - intros m b H c; simpl; rewrite H; reflexivity.
  - intro c; reflexivity.
  - intros t ts Ht Hts c; simpl; rewrite Ht; f_equal; apply Hts.
Qed.

Lemma shift_lt_in_tm_zero : forall c t,
  shift_lt_in_tm 0 c t = t.
Proof.
  enough (H : forall t, forall c, shift_lt_in_tm 0 c t = t).
  { intros c t; apply H. }
  apply (term_list_ind
    (fun t => forall c, shift_lt_in_tm 0 c t = t)
    (fun ts => forall c, List.map (shift_lt_in_tm 0 c) ts = ts)).
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
      unfold shift_lt_in_ty_list. rewrite List.map_ext with (g := id).
      * rewrite List.map_id, shift_lt_in_tm_go_eq_map; f_equal; apply Hts.
      * intro T; apply shift_lt_in_ty_zero.
    + intro l0; apply shift_lt_zero.
  - intros scrut tag arity yes_body no_body Hs Hy Hn c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E Ts op_body body Hop Hb c; simpl.
    unfold shift_lt_in_ty_list. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, Hop, Hb; reflexivity.
    + intro T; apply shift_lt_in_ty_zero.
  - intros t Ss arg Ht Ha c; simpl.
    unfold shift_lt_in_ty_list. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, Ht, Ha; reflexivity.
    + intro T; apply shift_lt_in_ty_zero.
  - intros E m Ts op_body Hop c; simpl.
    unfold shift_lt_in_ty_list. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, Hop; reflexivity.
    + intro T; apply shift_lt_in_ty_zero.
  - intros m t H c; simpl; rewrite H; reflexivity.
  - intros m b H c; simpl; rewrite H; reflexivity.
  - intro c; reflexivity.
  - intros t ts Ht Hts c; simpl; rewrite Ht; f_equal; apply Hts.
Qed.


(* ================================================================== *)
(* SECTION 3 — shift_fuse                                             *)
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

Lemma shift_lt_in_ty_fuse : forall a b c T,
  shift_lt_in_ty a c (shift_lt_in_ty b c T) = shift_lt_in_ty (a + b) c T.
Proof.
  enough (H : forall T, forall a b c, shift_lt_in_ty a c (shift_lt_in_ty b c T) = shift_lt_in_ty (a + b) c T).
  { intros a b c T; apply H. }
  apply (type_list_ind
    (fun T => forall a b c, shift_lt_in_ty a c (shift_lt_in_ty b c T) = shift_lt_in_ty (a + b) c T)
    (fun Ts => forall a b c, List.map (shift_lt_in_ty a c) (List.map (shift_lt_in_ty b c) Ts) = List.map (shift_lt_in_ty (a + b) c) Ts)).
  - intros n a b c; reflexivity.
  - intros A l B HA HB a b c; simpl; rewrite shift_lt_fuse, HA, HB; reflexivity.
  - intros K l Ts HTs a b c; simpl.
    f_equal.
    + apply shift_lt_fuse.
    + rewrite (shift_lt_in_ty_go_eq_map b c Ts).
      rewrite shift_lt_in_ty_go_eq_map.
      rewrite shift_lt_in_ty_go_eq_map.
      apply HTs.
  - intros A HA a b c; simpl; rewrite HA; reflexivity.
  - intros B A HB HA a b c; simpl; rewrite HB, HA; reflexivity.
  - intros a b c; reflexivity.
  - intros A Ts HA HTs a b c; simpl; rewrite HA; f_equal; apply HTs.
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
    rewrite (shift_ty_go_eq_map b c Ts).
    rewrite shift_ty_go_eq_map.
    rewrite shift_ty_go_eq_map.
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
    (fun ts => forall a b c, List.map (shift_tm a c) (List.map (shift_tm b c) ts) = List.map (shift_tm (a + b) c) ts)).
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
    rewrite (shift_tm_go_eq_map b c ts).
    rewrite shift_tm_go_eq_map.
    rewrite shift_tm_go_eq_map.
    apply Hts.
  - intros scrut tag arity yes_body no_body Hs Hy Hn a b c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E Ts op_body body Hop Hb a b c; simpl; rewrite Hop, Hb; reflexivity.
  - intros t Ss arg Ht Ha a b c; simpl; rewrite Ht, Ha; reflexivity.
  - intros E m Ts op_body Hop a b c; simpl; rewrite Hop; reflexivity.
  - intros m t H a b c; simpl; rewrite H; reflexivity.
  - intros m bdy H a b c; simpl; rewrite H; reflexivity.
  - intros a b c; reflexivity.
  - intros t ts Ht Hts a b c; simpl; rewrite Ht; f_equal; apply Hts.
Qed.

Lemma shift_ty_in_tm_fuse : forall a b c t,
  shift_ty_in_tm a c (shift_ty_in_tm b c t) = shift_ty_in_tm (a + b) c t.
Proof.
  enough (H : forall t, forall a b c, shift_ty_in_tm a c (shift_ty_in_tm b c t) = shift_ty_in_tm (a + b) c t).
  { intros a b c t; apply H. }
  apply (term_list_ind
    (fun t => forall a b c, shift_ty_in_tm a c (shift_ty_in_tm b c t) = shift_ty_in_tm (a + b) c t)
    (fun ts => forall a b c, List.map (shift_ty_in_tm a c) (List.map (shift_ty_in_tm b c) ts) = List.map (shift_ty_in_tm (a + b) c) ts)).
  - intros n a b c; reflexivity.
  - intros t1 t2 H1 H2 a b c; simpl; rewrite H1, H2; reflexivity.
  - intros body T H a b c; simpl; rewrite H, shift_ty_fuse; reflexivity.
  - intros t T H a b c; simpl; rewrite H, shift_ty_fuse; reflexivity.
  - intros bound body H a b c; simpl; rewrite H, shift_ty_fuse; reflexivity.
  - intros t l H a b c; simpl; rewrite H; reflexivity.
  - intros body H a b c; simpl; rewrite H; reflexivity.
  - intros K l lts Ts ts Hts a b c; simpl.
    unfold shift_ty_list.
    f_equal.
    + rewrite List.map_map.
      apply List.map_ext; intro T; apply shift_ty_fuse.
    + rewrite (shift_ty_in_tm_go_eq_map b c ts).
      rewrite shift_ty_in_tm_go_eq_map.
      rewrite shift_ty_in_tm_go_eq_map.
      apply Hts.
  - intros scrut tag arity yes_body no_body Hs Hy Hn a b c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E Ts op_body body Hop Hb a b c; simpl.
    unfold shift_ty_list.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_ty (a + b) c) by (intro T; apply shift_ty_fuse).
    rewrite Hop, Hb; reflexivity.
  - intros t Ss arg Ht Ha a b c; simpl.
    unfold shift_ty_list.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_ty (a + b) c) by (intro T; apply shift_ty_fuse).
    rewrite Ht, Ha; reflexivity.
  - intros E m Ts op_body Hop a b c; simpl.
    unfold shift_ty_list.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_ty (a + b) c) by (intro T; apply shift_ty_fuse).
    rewrite Hop; reflexivity.
  - intros m t H a b c; simpl; rewrite H; reflexivity.
  - intros m bdy H a b c; simpl; rewrite H; reflexivity.
  - intros a b c; reflexivity.
  - intros t ts Ht Hts a b c; simpl; rewrite Ht; f_equal; apply Hts.
Qed.

Lemma shift_lt_in_tm_fuse : forall a b c t,
  shift_lt_in_tm a c (shift_lt_in_tm b c t) = shift_lt_in_tm (a + b) c t.
Proof.
  enough (H : forall t, forall a b c, shift_lt_in_tm a c (shift_lt_in_tm b c t) = shift_lt_in_tm (a + b) c t).
  { intros a b c t; apply H. }
  apply (term_list_ind
    (fun t => forall a b c, shift_lt_in_tm a c (shift_lt_in_tm b c t) = shift_lt_in_tm (a + b) c t)
    (fun ts => forall a b c, List.map (shift_lt_in_tm a c) (List.map (shift_lt_in_tm b c) ts) = List.map (shift_lt_in_tm (a + b) c) ts)).
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
    + unfold shift_lt_in_ty_list.
      rewrite List.map_map.
      apply List.map_ext; intro T; apply shift_lt_in_ty_fuse.
    + rewrite (shift_lt_in_tm_go_eq_map b c ts).
      rewrite shift_lt_in_tm_go_eq_map.
      rewrite shift_lt_in_tm_go_eq_map.
      apply Hts.
  - intros scrut tag arity yes_body no_body Hs Hy Hn a b c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E Ts op_body body Hop Hb a b c; simpl.
    unfold shift_lt_in_ty_list.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_lt_in_ty (a + b) c) by (intro T; apply shift_lt_in_ty_fuse).
    rewrite Hop, Hb; reflexivity.
  - intros t Ss arg Ht Ha a b c; simpl.
    unfold shift_lt_in_ty_list.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_lt_in_ty (a + b) c) by (intro T; apply shift_lt_in_ty_fuse).
    rewrite Ht, Ha; reflexivity.
  - intros E m Ts op_body Hop a b c; simpl.
    unfold shift_lt_in_ty_list.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_lt_in_ty (a + b) c) by (intro T; apply shift_lt_in_ty_fuse).
    rewrite Hop; reflexivity.
  - intros m t H a b c; simpl; rewrite H; reflexivity.
  - intros m bdy H a b c; simpl; rewrite H; reflexivity.
  - intros a b c; reflexivity.
  - intros t ts Ht Hts a b c; simpl; rewrite Ht; f_equal; apply Hts.
Qed.


(* ================================================================== *)
(* SECTION 5 — shift_independent (cross-sort: same carrier,           *)
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
    (fun ts => forall a1 c1 a2 c2, List.map (shift_tm a1 c1) (List.map (shift_ty_in_tm a2 c2) ts) = List.map (shift_ty_in_tm a2 c2) (List.map (shift_tm a1 c1) ts))).
  - intros n a1 c1 a2 c2; reflexivity.
  - intros t1 t2 H1 H2 a1 c1 a2 c2; simpl; rewrite H1, H2; reflexivity.
  - intros body T H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros t T H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros bound body H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros t l H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros body H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros K l lts Ts ts Hts a1 c1 a2 c2; simpl.
    f_equal.
    rewrite (shift_ty_in_tm_go_eq_map a2 c2 ts).
    rewrite shift_tm_go_eq_map.
    rewrite shift_ty_in_tm_go_eq_map.
    apply Hts.
  - intros scrut tag arity yes_body no_body Hs Hy Hn a1 c1 a2 c2; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E Ts op_body body Hop Hb a1 c1 a2 c2; simpl; rewrite Hop, Hb; reflexivity.
  - intros t Ss arg Ht Ha a1 c1 a2 c2; simpl; rewrite Ht, Ha; reflexivity.
  - intros E m Ts op_body Hop a1 c1 a2 c2; simpl; rewrite Hop; reflexivity.
  - intros m t H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros m bdy H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros a1 c1 a2 c2; reflexivity.
  - intros t ts Ht Hts a1 c1 a2 c2; simpl; rewrite Ht; f_equal; apply Hts.
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
    (fun ts => forall a1 c1 a2 c2, List.map (shift_tm a1 c1) (List.map (shift_lt_in_tm a2 c2) ts) = List.map (shift_lt_in_tm a2 c2) (List.map (shift_tm a1 c1) ts))).
  - intros n a1 c1 a2 c2; reflexivity.
  - intros t1 t2 H1 H2 a1 c1 a2 c2; simpl; rewrite H1, H2; reflexivity.
  - intros body T H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros t T H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros bound body H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros t l H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros body H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros K l lts Ts ts Hts a1 c1 a2 c2; simpl.
    f_equal.
    rewrite (shift_lt_in_tm_go_eq_map a2 c2 ts).
    rewrite shift_tm_go_eq_map.
    rewrite shift_lt_in_tm_go_eq_map.
    apply Hts.
  - intros scrut tag arity yes_body no_body Hs Hy Hn a1 c1 a2 c2; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E Ts op_body body Hop Hb a1 c1 a2 c2; simpl; rewrite Hop, Hb; reflexivity.
  - intros t Ss arg Ht Ha a1 c1 a2 c2; simpl; rewrite Ht, Ha; reflexivity.
  - intros E m Ts op_body Hop a1 c1 a2 c2; simpl; rewrite Hop; reflexivity.
  - intros m t H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros m bdy H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros a1 c1 a2 c2; reflexivity.
  - intros t ts Ht Hts a1 c1 a2 c2; simpl; rewrite Ht; f_equal; apply Hts.
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
    (fun Ts => forall a1 c1 a2 c2, List.map (shift_ty a1 c1) (List.map (shift_lt_in_ty a2 c2) Ts) = List.map (shift_lt_in_ty a2 c2) (List.map (shift_ty a1 c1) Ts))).
  - intros n a1 c1 a2 c2; reflexivity.
  - intros A l B HA HB a1 c1 a2 c2; simpl; rewrite HA, HB; reflexivity.
  - intros K l Ts HTs a1 c1 a2 c2; simpl.
    f_equal.
    rewrite (shift_lt_in_ty_go_eq_map a2 c2 Ts).
    rewrite shift_ty_go_eq_map.
    rewrite shift_ty_go_eq_map.
    rewrite shift_lt_in_ty_go_eq_map.
    apply HTs.
  - intros A HA a1 c1 a2 c2; simpl; rewrite HA; reflexivity.
  - intros B A HB HA a1 c1 a2 c2; simpl; rewrite HB, HA; reflexivity.
  - intros a1 c1 a2 c2; reflexivity.
  - intros A Ts HA HTs a1 c1 a2 c2; simpl; rewrite HA; f_equal; apply HTs.
Qed.


(* ================================================================== *)
(* SECTION 10 — list-substitution properties                          *)
(*                                                                    *)
(* Connect the simultaneous list-substitution operations with their   *)
(* iterated single-substitution counterparts, and prove the obvious   *)
(* lookup laws used in the match-yes preservation argument.           *)
(* ================================================================== *)

(* Empty-list neutrality (sanity). *)
Lemma subst_list_tm_nil : forall t, subst_list_tm [] t = t.
Proof. reflexivity. Qed.

Lemma subst_list_lt_in_tm_nil : forall t, subst_list_lt_in_tm [] t = t.
Proof. reflexivity. Qed.

Lemma subst_list_ty_in_tm_nil : forall t, subst_list_ty_in_tm [] t = t.
Proof. reflexivity. Qed.

Lemma subst_list_lt_in_ty_nil : forall T, subst_list_lt_in_ty [] T = T.
Proof. reflexivity. Qed.

Lemma subst_list_ty_nil : forall T, subst_list_ty [] T = T.
Proof. reflexivity. Qed.

(* On a free variable above the substituted segment, list-subst       *)
(* decrements the index by the list length.                           *)
Lemma subst_list_tm_var_above : forall vs i,
  subst_list_tm vs (term_var (i + List.length vs)) = term_var i.
Proof.
  induction vs as [| v rest IH]; intro i.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite Nat.add_succ_r.
    simpl subst_tm.
    apply IH.
Qed.


(* ================================================================== *)
(*                                                                    *)
(*   TYPING-DEPENDENT SUBSTITUTION / WEAKENING / SHIFT LEMMAS         *)
(*   (relocated from Safety.v)                                        *)
(*                                                                    *)
(* These lemmas mention the typing (`⊢ₜ`) and subtyping (`<::`, `<:`) *)
(* judgments, so they live here — after `Require Import Typing` —     *)
(* rather than in the syntax-only σ-law section above.  Their content *)
(* is the standard de Bruijn plumbing of a System-F₊-with-lifetimes   *)
(* metatheory, orthogonal to the paper's contribution.                *)
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
  - (* lt_min *)
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

(* Apply `subst_list_lt_in_ty lts` pointwise to a list of types.       *)
Definition subst_list_lt_in_ty_each (lts : list lifetime) (rhos : list type) : list type :=
  List.map (subst_list_lt_in_ty lts) rhos.

(* Bridge: parallel lt-substitution `subst_list_lt_in_ty` is exactly    *)
(* the iterated single-var substitution `iter_subst_lt_in_ty` applied   *)
(* to the *pre-shifted* witness list.  `subst_list_lt_in_ty` shifts      *)
(* each witness by the number of remaining witnesses before             *)
(* substituting at position 0; the faithful bridge threads that shift    *)
(* through.  This is the corrected form of the previously-unsound        *)
(* `subst_list_lt_in_ty lts T = iter_subst_lt_in_ty lts T` axiom         *)
(* (which dropped the shift) and is now a theorem.                      *)
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

(* ---- Subtyping weakening (correctly shifted) -------------------- *)

(* Correct context weakening for subtyping.  Inserting a `bind_ty`      *)
(* binding at the front shifts the type-variable namespace by one, so    *)
(* the related types must be shifted by `shift_ty 1 0`.  (The earlier    *)
(* no-shift `sub_weaken_cons` omitted this shift and was unsound:         *)
(* prepending a binding silently re-captured the de Bruijn indices.)     *)
(* Standard weakening metatheory; axiomatized.                          *)
Axiom sub_weaken_ty_shift : forall Γ B T1 T2,
  Γ ⊢ T1 <:: T2 ->
  (bind_ty B :: Γ) ⊢ shift_ty 1 0 T1 <:: shift_ty 1 0 T2.

(* Likewise, inserting a `bind_lt` binding shifts the lifetime          *)
(* namespace inside types by one.                                       *)
Axiom sub_weaken_lt_shift : forall Γ D T1 T2,
  Γ ⊢ T1 <:: T2 ->
  (bind_lt D :: Γ) ⊢ shift_lt_in_ty 1 0 T1 <:: shift_lt_in_ty 1 0 T2.

(* Subtyping-substitution lemmas.  Standard; axiomatized.             *)
Axiom sub_subst_ty : forall Γ B U0 U S,
  (bind_ty B :: Γ) ⊢ U0 <:: U ->
  Γ ⊢ S <:: B ->
  Γ ⊢ subst_ty 0 S U0 <:: subst_ty 0 S U.

Axiom sub_subst_lt : forall Γ Δ U0 U Δ',
  (bind_lt Δ :: Γ) ⊢ U0 <:: U ->
  Γ ⊢ₗ Δ' <: Δ ->
  Γ ⊢ subst_lt_in_ty 0 Δ' U0 <:: subst_lt_in_ty 0 Δ' U.

(* Shifting preserves lifetime subtyping. *)
Axiom lt_sub_shift_lt : forall Γ Δ l1 l2 cutoff,
  Γ ⊢ₗ l1 <: l2 ->
  (bind_lt Δ :: Γ) ⊢ₗ shift_lt 1 cutoff l1 <: shift_lt 1 cutoff l2.

(* Subtyping is monotone in single-var lt-substitution at any depth. *)
Axiom lt_sub_subst_lt : forall Γ x l_0 l1 l2,
  Γ ⊢ₗ l1 <: l2 ->
  Γ ⊢ₗ subst_lt x l_0 l1 <: subst_lt x l_0 l2.

(* Type subtyping monotone in single-var lt-substitution. *)
Axiom sub_subst_lt_at : forall Γ x l_0 T1 T2,
  Γ ⊢ T1 <:: T2 ->
  Γ ⊢ subst_lt_in_ty x l_0 T1 <:: subst_lt_in_ty x l_0 T2.

(* Lifetime subtyping is preserved by `shift_lt`.                       *)
Axiom shift_lt_sub : forall Γ n k B B',
  Γ ⊢ₗ B <: B' ->
  Γ ⊢ₗ shift_lt n k B <: shift_lt n k B'.

(* ---- chain_bounded witnesses + iteration monotonicity ---------- *)

(* Witnesses are valid w.r.t. a chain of progressively-closed bounds.   *)
Fixpoint chain_bounded (Γ : ctx) (ws : list lifetime) (bound : lifetime) : Prop :=
  match ws with
  | []        => True
  | w :: rest =>
      (Γ ⊢ₗ w <: subst_lt 0 lt_free bound) /\
      chain_bounded Γ rest (subst_lt 0 lt_free bound)
  end.

(* Subtyping is preserved through `iter_subst_lt_in_ty`.                *)
Lemma iter_subst_lt_in_ty_mono : forall ws Γ T1 T2,
  Γ ⊢ T1 <:: T2 ->
  Γ ⊢ iter_subst_lt_in_ty ws T1 <:: iter_subst_lt_in_ty ws T2.
Proof.
  induction ws as [|w rest IH]; intros Γ T1 T2 Hsub; simpl.
  - assumption.
  - apply IH. apply sub_subst_lt_at. assumption.
Qed.

(* Monotonicity of chain_bounded under enlarging the ambient bound.    *)
Lemma chain_bounded_mono : forall Γ lts B B',
  chain_bounded Γ lts B ->
  Γ ⊢ₗ B <: B' ->
  chain_bounded Γ lts B'.
Proof.
  intros Γ lts. induction lts as [|w rest IH]; intros B B' Hcb Hsub.
  - exact I.
  - simpl in Hcb. destruct Hcb as [Hw Hrest]. simpl. split.
    + eapply LS_Trans; [exact Hw |]. apply lt_sub_subst_lt. exact Hsub.
    + eapply IH; [exact Hrest |]. apply lt_sub_subst_lt. exact Hsub.
Qed.

(* From the typing of a ctor *value* `term_ctor K Delta lts Ts vs`     *)
(* against type `type_ctor K Delta Ts`, the witnesses `lts` form a     *)
(* `chain_bounded` chain w.r.t. the shifted Delta.                     *)
Axiom ctor_lts_chain_bounded : forall Γ lts n_lt n_ty Ts sigma vs Delta,
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs
          (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma) ->
  List.length lts = n_lt ->
  Delta = lt_of_ty_list (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma) ->
  chain_bounded Γ lts (shift_lt n_lt 0 Delta).

(* ---- Substitution preservation (typing) ------------------------ *)

Axiom subst_tm_lemma : forall Γ T1 t T2 v,
  (bind_tm T1 :: Γ) ⊢ₜ t : T2 ->
  Γ ⊢ₜ v : T1 ->
  Γ ⊢ₜ subst_tm 0 v t : T2.

Axiom subst_ty_in_tm_lemma : forall Γ B t T S,
  (bind_ty B :: Γ) ⊢ₜ t : T ->
  Γ ⊢ S <:: B ->
  Γ ⊢ₜ subst_ty_in_tm 0 S t : subst_ty 0 S T.

Axiom subst_lt_in_tm_lemma : forall Γ Δ t T Δ',
  (bind_lt Δ :: Γ) ⊢ₜ t : T ->
  Γ ⊢ₗ Δ' <: Δ ->
  Γ ⊢ₜ subst_lt_in_tm 0 Δ' t : subst_lt_in_ty 0 Δ' T.

(* Parallel lt substitution lemma.  Closes the n_lt fresh lt-binders   *)
(* introduced by `push_lt_vars n_lt Delta`, while propagating through  *)
(* an arbitrary stack of `bind_tm` binders sitting above.              *)
Axiom subst_list_lt_in_tm_lemma : forall Γ rhos n_lt Delta lts t T,
  List.length lts = n_lt ->
  chain_bounded Γ lts (shift_lt n_lt 0 Delta) ->
  (fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
              (push_lt_vars n_lt Delta Γ) rhos) ⊢ₜ t : T ->
  (fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
              Γ (subst_list_lt_in_ty_each lts rhos))
    ⊢ₜ subst_list_lt_in_tm lts t : subst_list_lt_in_ty lts T.

(* Parallel term substitution: closes a list of tm-binders against a   *)
(* matching list of values typed in the outer Γ.                       *)
Axiom subst_list_tm_lemma : forall Γ vs rhos t T,
  List.length vs = List.length rhos ->
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rhos ->
  (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos) ⊢ₜ t : T ->
  Γ ⊢ₜ subst_list_tm vs t : T.

(* Substituting `lts` for the schema variables `lt_var_list n_lt`      *)
(* yields direct schema instantiation.                                 *)
Axiom inst_ctor_type_subst_eq : forall n_lt n_ty lts Ts sigma_fields,
  List.length lts = n_lt ->
  subst_list_lt_in_ty_each lts
    (List.map (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts) sigma_fields)
  = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields.
