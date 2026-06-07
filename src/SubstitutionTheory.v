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

Lemma shift_each_lt_length : forall lts,
  List.length (shift_each_lt lts) = List.length lts.
Proof.
  induction lts as [|l rest IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma subst_list_lt_in_ty_eq_iter : forall lts T,
  subst_list_lt_in_ty lts T = iter_subst_lt_in_ty (shift_each_lt lts) T.
Proof.
  intros lts; induction lts as [|l rest IH]; intros T; simpl.
  - reflexivity.
  - apply IH.
Qed.

(* ================================================================== *)
(*  lt_of_ty_ctx: rewrite equations, var-bound invariant, fuel        *)
(*  sufficiency, and shift commutation.                               *)
(*                                                                    *)
(*  The shift-on-lookup discipline makes EVERY context structurally   *)
(*  acyclic (a bound looked up across k binders is var-bounded by k),  *)
(*  so fuel = |Γ| always suffices: the computed lt_∅ is independent    *)
(*  of any fuel ≥ |Γ|.  This is what lets context weakening go through *)
(*  at the `SA_Any` rule without a separate well-formedness premise.   *)
(* ================================================================== *)

(* External per-field minimum, matching the internal field fold. *)
Definition lt_of_ty_ctx_list (f : nat) (G : ctx) (Ts : list type) : lifetime :=
  fold_right (fun A acc => lt_min (lt_of_ty_ctx f G A) acc) lt_free Ts.

Lemma lt_of_ty_ctx_list_nil : forall f G, lt_of_ty_ctx_list f G [] = lt_free.
Proof. reflexivity. Qed.
Lemma lt_of_ty_ctx_list_cons : forall f G A Ts,
  lt_of_ty_ctx_list f G (A :: Ts)
  = lt_min (lt_of_ty_ctx f G A) (lt_of_ty_ctx_list f G Ts).
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

Lemma lt_of_ty_ctx_ltall : forall f G A, lt_of_ty_ctx f G (type_lt_all A) = lt_free.
Proof. intros f G A. destruct f; reflexivity. Qed.

Lemma lt_of_ty_ctx_tyall : forall f G B A, lt_of_ty_ctx f G (type_ty_all B A) = lt_free.
Proof. intros f G B A. destruct f; reflexivity. Qed.

Lemma lt_of_ty_ctx_ctor : forall f G K l Ts,
  lt_of_ty_ctx f G (type_ctor K l Ts) = lt_min l (lt_of_ty_ctx_list f G Ts).
Proof.
  intros f G K l Ts. unfold lt_of_ty_ctx_list.
  destruct f as [|f']; simpl; f_equal;
    induction Ts as [|A rest IH]; simpl; try reflexivity; rewrite IH; reflexivity.
Qed.

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
  - destruct b as [C|C|D|tg n1 n2 Ts Tr|eg m1 m2 Ts Tr]; simpl in H.
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
  - simpl in H. destruct b as [C|C|D|tg n1 n2 Ts Tr|eg m1 m2 Ts Tr].
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

Lemma shift_lt_min_eq : forall a c l1 l2,
  shift_lt a c (lt_min l1 l2) = lt_min (shift_lt a c l1) (shift_lt a c l2).
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
    + rewrite shift_lt_in_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor. rewrite shift_lt_min_eq.
      f_equal. exact IHT.
    + rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite shift_lt_min_eq.
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
    + rewrite shift_lt_in_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor. rewrite shift_lt_min_eq.
      f_equal. exact IHT.
    + rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite shift_lt_min_eq.
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

(* ================================================================== *)
(* Depth-general bind_ty weakening for subtyping.                     *)
(*                                                                    *)
(* InsTy c G G' : G' is G with one bind_ty inserted after c ty-binders *)
(* (counted from the head).  Subtyping is closed under InsTy, with     *)
(* types shifted by `shift_ty 1 c`.  `sub_weaken_ty_shift` is the      *)
(* front (c = 0) instance.                                             *)
(* ================================================================== *)

(* Shift swap law (different cutoffs); needed for the head bind_ty case. *)
Lemma shift_ty_swap : forall T c1 c2, c1 <= c2 ->
  shift_ty 1 c1 (shift_ty 1 c2 T) = shift_ty 1 (S c2) (shift_ty 1 c1 T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall c1 c2, c1 <= c2 ->
      shift_ty 1 c1 (shift_ty 1 c2 T) = shift_ty 1 (S c2) (shift_ty 1 c1 T))
    (fun Ts => forall c1 c2, c1 <= c2 ->
      List.map (shift_ty 1 c1) (List.map (shift_ty 1 c2) Ts)
      = List.map (shift_ty 1 (S c2)) (List.map (shift_ty 1 c1) Ts))).
  - intros n c1 c2 Hle.
    rewrite !shift_ty_var_eq. f_equal.
    destruct (Nat.leb c2 n) eqn:E2.
    + apply Nat.leb_le in E2.
      rewrite (proj2 (Nat.leb_le c1 n)) by lia.
      rewrite (proj2 (Nat.leb_le c1 (n+1))) by lia.
      rewrite (proj2 (Nat.leb_le (S c2) (n+1))) by lia.
      reflexivity.
    + apply Nat.leb_gt in E2.
      destruct (Nat.leb c1 n) eqn:E1.
      * apply Nat.leb_le in E1.
        rewrite (proj2 (Nat.leb_gt (S c2) (n+1))) by lia. reflexivity.
      * apply Nat.leb_gt in E1.
        rewrite (proj2 (Nat.leb_gt (S c2) n)) by lia. reflexivity.
  - intros A l B HA HB c1 c2 Hle.
    simpl. rewrite HA by lia. rewrite HB by lia. reflexivity.
  - intros K l Ts HTs c1 c2 Hle.
    rewrite !shift_ty_ctor_eq. f_equal. apply HTs. lia.
  - intros A HA c1 c2 Hle.
    simpl. rewrite HA by lia. reflexivity.
  - intros B A HB HA c1 c2 Hle.
    simpl. rewrite HB by lia. rewrite HA by lia. reflexivity.
  - intros c1 c2 Hle. reflexivity.
  - intros A Ts HA HTs c1 c2 Hle.
    simpl. rewrite HA by lia. f_equal. apply HTs. lia.
Qed.

Lemma shift_ty_swap_0 : forall T c,
  shift_ty 1 0 (shift_ty 1 c T) = shift_ty 1 (S c) (shift_ty 1 0 T).
Proof. intros T c. apply shift_ty_swap. lia. Qed.

Inductive InsTy : nat -> ctx -> ctx -> Prop :=
| InsTy_here : forall B G, InsTy 0 G (bind_ty B :: G)
| InsTy_ty : forall c G G' A,
    InsTy c G G' -> InsTy (S c) (bind_ty A :: G) (bind_ty (shift_ty 1 c A) :: G')
| InsTy_lt : forall c G G' D,
    InsTy c G G' -> InsTy c (bind_lt D :: G) (bind_lt D :: G')
| InsTy_tm : forall c G G' T,
    InsTy c G G' -> InsTy c (bind_tm T :: G) (bind_tm (shift_ty 1 c T) :: G')
| InsTy_ctor : forall c G G' tg n1 n2 Ts Tr,
    InsTy c G G' ->
    InsTy c (bind_ctor tg n1 n2 Ts Tr :: G)
            (bind_ctor tg n1 n2 (List.map (shift_ty 1 c) Ts) (shift_ty 1 c Tr) :: G')
| InsTy_eff : forall c G G' eg m1 m2 Ts Tr,
    InsTy c G G' ->
    InsTy c (bind_eff eg m1 m2 Ts Tr :: G)
            (bind_eff eg m1 m2 (shift_ty 1 c Ts) (shift_ty 1 c Tr) :: G').

Definition shv (c a : nat) : nat := if Nat.leb c a then S a else a.

Lemma InsTy_lookup_ty : forall c G G', InsTy c G G' ->
  forall a, ctx_lookup_ty G' (shv c a)
            = option_map (shift_ty 1 c) (ctx_lookup_ty G a).
Proof.
  intros c G G' H. induction H; intro a.
  - unfold shv; simpl Nat.leb.
    destruct a as [|a']; reflexivity.
  - destruct a as [|a'].
    + unfold shv; simpl Nat.leb. simpl ctx_lookup_ty.
      rewrite shift_ty_swap_0. reflexivity.
    + specialize (IHInsTy a').
      destruct (Nat.leb c a') eqn:E.
      * assert (E2 : shv (S c) (S a') = S (S a')).
        { unfold shv. apply Nat.leb_le in E. rewrite (proj2 (Nat.leb_le (S c)(S a'))) by lia. reflexivity. }
        rewrite E2. unfold shv in IHInsTy. rewrite E in IHInsTy.
        simpl ctx_lookup_ty.
        rewrite IHInsTy.
        destruct (ctx_lookup_ty G a') as [X|]; simpl; [rewrite shift_ty_swap_0; reflexivity | reflexivity].
      * apply Nat.leb_gt in E.
        assert (E2 : shv (S c) (S a') = S a').
        { unfold shv. rewrite (proj2 (Nat.leb_gt (S c)(S a'))) by lia. reflexivity. }
        rewrite E2. unfold shv in IHInsTy. rewrite (proj2 (Nat.leb_gt c a')) in IHInsTy by lia.
        simpl ctx_lookup_ty.
        rewrite IHInsTy.
        destruct (ctx_lookup_ty G a') as [X|]; simpl; [rewrite shift_ty_swap_0; reflexivity | reflexivity].
  - specialize (IHInsTy a). simpl ctx_lookup_ty. rewrite IHInsTy.
    destruct (ctx_lookup_ty G a) as [X|]; simpl;
      [rewrite shift_ty_shift_lt_in_ty_commute; reflexivity | reflexivity].
  - specialize (IHInsTy a). simpl ctx_lookup_ty. apply IHInsTy.
  - specialize (IHInsTy a). simpl ctx_lookup_ty. apply IHInsTy.
  - specialize (IHInsTy a). simpl ctx_lookup_ty. apply IHInsTy.
Qed.

Lemma InsTy_lookup_lt : forall c G G', InsTy c G G' ->
  forall x, ctx_lookup_lt G' x = ctx_lookup_lt G x.
Proof.
  intros c G G' H. induction H; intro x; simpl; try (apply IHInsTy).
  - reflexivity.
  - destruct x as [|x']; simpl.
    + reflexivity.
    + rewrite IHInsTy. reflexivity.
Qed.

Lemma shift_ty_fun_eq : forall a c A l B,
  shift_ty a c (type_fun A l B) = type_fun (shift_ty a c A) l (shift_ty a c B).
Proof. reflexivity. Qed.
Lemma shift_ty_ltall_eq : forall a c A,
  shift_ty a c (type_lt_all A) = type_lt_all (shift_ty a c A).
Proof. reflexivity. Qed.
Lemma shift_ty_tyall_eq : forall a c B A,
  shift_ty a c (type_ty_all B A) = type_ty_all (shift_ty a c B) (shift_ty a (S c) A).
Proof. reflexivity. Qed.

Lemma shv_shift : forall c n, shift_ty 1 c (type_var n) = type_var (shv c n).
Proof.
  intros c n. rewrite shift_ty_var_eq. unfold shv.
  destruct (Nat.leb c n); [rewrite Nat.add_1_r|]; reflexivity.
Qed.

Lemma InsTy_length : forall c G G', InsTy c G G' -> length G' = S (length G).
Proof. intros c G G' H. induction H; simpl; lia. Qed.

Lemma lt_of_ty_ctx_InsTy : forall c G G', InsTy c G G' ->
  forall f T, lt_of_ty_ctx f G' (shift_ty 1 c T) = lt_of_ty_ctx f G T.
Proof.
  intros c G G' HIns f. induction f as [|f' IHf]; intro T.
  - induction T using type_list_ind with
      (Q := fun Ts => lt_of_ty_ctx_list 0 G' (List.map (shift_ty 1 c) Ts)
                      = lt_of_ty_ctx_list 0 G Ts).
    + rewrite shv_shift. rewrite !(lt_of_ty_ctx_var 0). reflexivity.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_fun. reflexivity.
    + rewrite shift_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor. f_equal. exact IHT.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite IHT, IHT0. reflexivity.
  - induction T using type_list_ind with
      (Q := fun Ts => lt_of_ty_ctx_list (S f') G' (List.map (shift_ty 1 c) Ts)
                      = lt_of_ty_ctx_list (S f') G Ts).
    + rewrite shv_shift.
      rewrite (lt_of_ty_ctx_var (S f') G' (shv c n)), (lt_of_ty_ctx_var (S f') G n).
      rewrite (InsTy_lookup_ty c G G' HIns n).
      destruct (ctx_lookup_ty G n) as [B|] eqn:E; simpl.
      * apply IHf.
      * reflexivity.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_fun. reflexivity.
    + rewrite shift_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor. f_equal. exact IHT.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite IHT, IHT0. reflexivity.
Qed.

Lemma lt_of_ty_G_InsTy : forall c G G', InsTy c G G' ->
  forall T, lt_of_ty_G G' (shift_ty 1 c T) = lt_of_ty_G G T.
Proof.
  intros c G G' HIns T. unfold lt_of_ty_G.
  rewrite (InsTy_length c G G' HIns).
  rewrite (lt_of_ty_ctx_InsTy c G G' HIns (S (length G)) T).
  apply (lt_of_ty_ctx_fuel_irrel (S (length G)) (length G) T G 0).
  - apply VB_0.
  - simpl; lia.
  - simpl; lia.
Qed.

Lemma lt_sub_InsTy : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall c G', InsTy c G G' -> G' ⊢ₗ l1 <: l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l|Γ l|Γ x Δ Hlk|Γ l
                 |Γ l1 l2 l3 H1 IH1 H2 IH2|Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H1 IH1|Γ l l1 l2 H1 IH1];
    intros c G' HIns.
  - apply LS_Free.
  - apply LS_Local.
  - apply LS_Var. rewrite (InsTy_lookup_lt c Γ G' HIns x). exact Hlk.
  - apply LS_Refl.
  - eapply LS_Trans; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - apply LS_MinL; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - apply LS_MinR1; apply (IH1 c G' HIns).
  - apply LS_MinR2; apply (IH1 c G' HIns).
Qed.

Lemma sub_InsTy : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall c G', InsTy c G G' -> G' ⊢ shift_ty 1 c T1 <:: shift_ty 1 c T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk|Γ K l l' Ts Hls
                 |Γ T Δ Hls|Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' H1 IH1 H2 IH2];
    intros c G' HIns.
  - apply SA_Refl.
  - eapply SA_Trans; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - rewrite shv_shift. apply SA_VarCtx.
    rewrite (InsTy_lookup_ty c Γ G' HIns α). rewrite Hlk. reflexivity.
  - rewrite !shift_ty_ctor_eq. apply SA_Data. apply (lt_sub_InsTy Γ l l' Hls c G' HIns).
  - rewrite shift_ty_ctor_eq. cbn [List.map]. apply SA_Any.
    rewrite (lt_of_ty_G_InsTy c Γ G' HIns T).
    apply (lt_sub_InsTy Γ (lt_of_ty_G Γ T) Δ Hls c G' HIns).
  - rewrite !shift_ty_fun_eq. apply SA_Fun.
    + apply (IH1 c G' HIns).
    + apply (lt_sub_InsTy Γ l l' Hl c G' HIns).
    + apply (IH2 c G' HIns).
  - rewrite !shift_ty_ltall_eq. apply SA_LtAll.
    apply (IH1 c (bind_lt lt_local :: G') (InsTy_lt c Γ G' lt_local HIns)).
  - rewrite !shift_ty_tyall_eq. apply SA_TyAll.
    + apply (IH1 c G' HIns).
    + apply (IH2 (S c) (bind_ty (shift_ty 1 c B') :: G') (InsTy_ty c Γ G' B' HIns)).
Qed.

(* ---- Subtyping weakening (correctly shifted) -------------------- *)

(* Correct context weakening for subtyping.  Inserting a `bind_ty`      *)
(* binding at the front shifts the type-variable namespace by one, so    *)
(* the related types must be shifted by `shift_ty 1 0`.  (The earlier    *)
(* no-shift `sub_weaken_cons` omitted this shift and was unsound:         *)
(* prepending a binding silently re-captured the de Bruijn indices.)     *)
(* Standard weakening metatheory; now derived from `sub_InsTy`.        *)
Lemma sub_weaken_ty_shift : forall Γ B T1 T2,
  Γ ⊢ T1 <:: T2 ->
  (bind_ty B :: Γ) ⊢ shift_ty 1 0 T1 <:: shift_ty 1 0 T2.
Proof.
  intros Γ B T1 T2 H. apply (sub_InsTy Γ T1 T2 H 0 (bind_ty B :: Γ)). apply InsTy_here.
Qed.

(* Likewise, inserting a `bind_lt` binding shifts the lifetime          *)
(* namespace inside types by one.  Derived from `sub_InsLt`.           *)

(* ===== InsLt: depth-general bind_lt weakening ===== *)

Lemma shift_lt_var_eq : forall a c n,
  shift_lt a c (lt_var n) = lt_var (if Nat.leb c n then n + a else n).
Proof. reflexivity. Qed.

(* swap law for shift_lt (lifetimes) *)
Lemma shift_lt_swap : forall l c1 c2, c1 <= c2 ->
  shift_lt 1 c1 (shift_lt 1 c2 l) = shift_lt 1 (S c2) (shift_lt 1 c1 l).
Proof.
  induction l as [n| | |l1 IH1 l2 IH2]; intros c1 c2 Hle.
  - rewrite !shift_lt_var_eq. f_equal.
    destruct (Nat.leb c2 n) eqn:E2.
    + apply Nat.leb_le in E2.
      rewrite (proj2 (Nat.leb_le c1 n)) by lia.
      rewrite (proj2 (Nat.leb_le c1 (n+1))) by lia.
      rewrite (proj2 (Nat.leb_le (S c2) (n+1))) by lia.
      reflexivity.
    + apply Nat.leb_gt in E2.
      destruct (Nat.leb c1 n) eqn:E1.
      * apply Nat.leb_le in E1.
        rewrite (proj2 (Nat.leb_gt (S c2) (n+1))) by lia. reflexivity.
      * apply Nat.leb_gt in E1.
        rewrite (proj2 (Nat.leb_gt (S c2) n)) by lia. reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IH1 by lia. rewrite IH2 by lia. reflexivity.
Qed.

Lemma shift_lt_swap_0 : forall l c,
  shift_lt 1 0 (shift_lt 1 c l) = shift_lt 1 (S c) (shift_lt 1 0 l).
Proof. intros l c. apply shift_lt_swap. lia. Qed.

(* swap law for shift_lt_in_ty (types) *)
Lemma shift_lt_in_ty_swap : forall T c1 c2, c1 <= c2 ->
  shift_lt_in_ty 1 c1 (shift_lt_in_ty 1 c2 T)
  = shift_lt_in_ty 1 (S c2) (shift_lt_in_ty 1 c1 T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall c1 c2, c1 <= c2 ->
      shift_lt_in_ty 1 c1 (shift_lt_in_ty 1 c2 T)
      = shift_lt_in_ty 1 (S c2) (shift_lt_in_ty 1 c1 T))
    (fun Ts => forall c1 c2, c1 <= c2 ->
      List.map (shift_lt_in_ty 1 c1) (List.map (shift_lt_in_ty 1 c2) Ts)
      = List.map (shift_lt_in_ty 1 (S c2)) (List.map (shift_lt_in_ty 1 c1) Ts))).
  - intros n c1 c2 Hle. reflexivity.
  - intros A l B HA HB c1 c2 Hle.
    simpl. rewrite HA by lia. rewrite HB by lia. rewrite shift_lt_swap by lia. reflexivity.
  - intros K l Ts HTs c1 c2 Hle.
    rewrite !shift_lt_in_ty_ctor_eq. rewrite shift_lt_swap by lia. f_equal. apply HTs. lia.
  - intros A HA c1 c2 Hle.
    simpl. rewrite HA by lia. reflexivity.
  - intros B A HB HA c1 c2 Hle.
    simpl. rewrite HB by lia. rewrite HA by lia. reflexivity.
  - intros c1 c2 Hle. reflexivity.
  - intros A Ts HA HTs c1 c2 Hle.
    simpl. rewrite HA by lia. f_equal. apply HTs. lia.
Qed.

Lemma shift_lt_in_ty_swap_0 : forall T c,
  shift_lt_in_ty 1 0 (shift_lt_in_ty 1 c T)
  = shift_lt_in_ty 1 (S c) (shift_lt_in_ty 1 0 T).
Proof. intros T c. apply shift_lt_in_ty_swap. lia. Qed.

Inductive InsLt : nat -> ctx -> ctx -> Prop :=
| InsLt_here : forall D G, InsLt 0 G (bind_lt D :: G)
| InsLt_lt : forall c G G' D,
    InsLt c G G' -> InsLt (S c) (bind_lt D :: G) (bind_lt (shift_lt 1 c D) :: G')
| InsLt_ty : forall c G G' A,
    InsLt c G G' -> InsLt c (bind_ty A :: G) (bind_ty (shift_lt_in_ty 1 c A) :: G')
| InsLt_tm : forall c G G' T,
    InsLt c G G' -> InsLt c (bind_tm T :: G) (bind_tm (shift_lt_in_ty 1 c T) :: G')
| InsLt_ctor : forall c G G' tg n1 n2 Ts Tr,
    InsLt c G G' ->
    InsLt c (bind_ctor tg n1 n2 Ts Tr :: G)
            (bind_ctor tg n1 n2 (List.map (shift_lt_in_ty 1 c) Ts) (shift_lt_in_ty 1 c Tr) :: G')
| InsLt_eff : forall c G G' eg m1 m2 Ts Tr,
    InsLt c G G' ->
    InsLt c (bind_eff eg m1 m2 Ts Tr :: G)
            (bind_eff eg m1 m2 (shift_lt_in_ty 1 c Ts) (shift_lt_in_ty 1 c Tr) :: G').

Lemma InsLt_length : forall c G G', InsLt c G G' -> length G' = S (length G).
Proof. intros c G G' H. induction H; simpl; lia. Qed.

(* lt-lookups shift by shift_lt 1 c at the renamed index shv c x *)
Lemma InsLt_lookup_lt : forall c G G', InsLt c G G' ->
  forall x, ctx_lookup_lt G' (shv c x)
            = option_map (shift_lt 1 c) (ctx_lookup_lt G x).
Proof.
  intros c G G' H. induction H; intro x.
  - unfold shv; simpl Nat.leb. destruct x as [|x']; reflexivity.
  - destruct x as [|x'].
    + unfold shv; simpl Nat.leb. simpl ctx_lookup_lt.
      rewrite shift_lt_swap_0. reflexivity.
    + specialize (IHInsLt x').
      destruct (Nat.leb c x') eqn:E.
      * assert (E2 : shv (S c) (S x') = S (S x')).
        { unfold shv. apply Nat.leb_le in E. rewrite (proj2 (Nat.leb_le (S c)(S x'))) by lia. reflexivity. }
        rewrite E2. unfold shv in IHInsLt. rewrite E in IHInsLt.
        simpl ctx_lookup_lt. rewrite IHInsLt.
        destruct (ctx_lookup_lt G x') as [X|]; simpl; [rewrite shift_lt_swap_0; reflexivity | reflexivity].
      * apply Nat.leb_gt in E.
        assert (E2 : shv (S c) (S x') = S x').
        { unfold shv. rewrite (proj2 (Nat.leb_gt (S c)(S x'))) by lia. reflexivity. }
        rewrite E2. unfold shv in IHInsLt. rewrite (proj2 (Nat.leb_gt c x')) in IHInsLt by lia.
        simpl ctx_lookup_lt. rewrite IHInsLt.
        destruct (ctx_lookup_lt G x') as [X|]; simpl; [rewrite shift_lt_swap_0; reflexivity | reflexivity].
  - specialize (IHInsLt x). simpl ctx_lookup_lt. apply IHInsLt.
  - specialize (IHInsLt x). simpl ctx_lookup_lt. apply IHInsLt.
  - specialize (IHInsLt x). simpl ctx_lookup_lt. apply IHInsLt.
  - specialize (IHInsLt x). simpl ctx_lookup_lt. apply IHInsLt.
Qed.

(* ty-lookups shift by shift_lt_in_ty 1 c (index unchanged) *)
Lemma InsLt_lookup_ty : forall c G G', InsLt c G G' ->
  forall a, ctx_lookup_ty G' a
            = option_map (shift_lt_in_ty 1 c) (ctx_lookup_ty G a).
Proof.
  intros c G G' H. induction H; intro a.
  - (* InsLt_here *) simpl ctx_lookup_ty.
    destruct (ctx_lookup_ty G a) as [X|]; simpl; reflexivity.
  - (* InsLt_lt *) specialize (IHInsLt a). simpl ctx_lookup_ty. rewrite IHInsLt.
    destruct (ctx_lookup_ty G a) as [X|]; simpl;
      [rewrite shift_lt_in_ty_swap_0; reflexivity | reflexivity].
  - (* InsLt_ty *) destruct a as [|a'].
    + simpl ctx_lookup_ty. rewrite shift_ty_shift_lt_in_ty_commute. reflexivity.
    + specialize (IHInsLt a'). simpl ctx_lookup_ty. rewrite IHInsLt.
      destruct (ctx_lookup_ty G a') as [X|]; simpl;
        [rewrite shift_ty_shift_lt_in_ty_commute; reflexivity | reflexivity].
  - specialize (IHInsLt a). simpl ctx_lookup_ty. apply IHInsLt.
  - specialize (IHInsLt a). simpl ctx_lookup_ty. apply IHInsLt.
  - specialize (IHInsLt a). simpl ctx_lookup_ty. apply IHInsLt.
Qed.

Lemma shv_shift_lt : forall c n, shift_lt 1 c (lt_var n) = lt_var (shv c n).
Proof.
  intros c n. simpl. unfold shv.
  destruct (Nat.leb c n); [rewrite Nat.add_1_r|]; reflexivity.
Qed.

(* lt_of_ty_ctx commutes with shift_lt_in_ty under InsLt *)
Lemma lt_of_ty_ctx_InsLt : forall c G G', InsLt c G G' ->
  forall f T, lt_of_ty_ctx f G' (shift_lt_in_ty 1 c T) = shift_lt 1 c (lt_of_ty_ctx f G T).
Proof.
  intros c G G' HIns f. induction f as [|f' IHf]; intro T.
  - induction T using type_list_ind with
      (Q := fun Ts => lt_of_ty_ctx_list 0 G' (List.map (shift_lt_in_ty 1 c) Ts)
                      = shift_lt 1 c (lt_of_ty_ctx_list 0 G Ts)).
    + rewrite shift_lt_in_ty_var_eq. rewrite !(lt_of_ty_ctx_var 0). reflexivity.
    + rewrite shift_lt_in_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. reflexivity.
    + rewrite shift_lt_in_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor. rewrite shift_lt_min_eq.
      f_equal. exact IHT.
    + rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite shift_lt_min_eq. rewrite IHT, IHT0. reflexivity.
  - induction T using type_list_ind with
      (Q := fun Ts => lt_of_ty_ctx_list (S f') G' (List.map (shift_lt_in_ty 1 c) Ts)
                      = shift_lt 1 c (lt_of_ty_ctx_list (S f') G Ts)).
    + rewrite shift_lt_in_ty_var_eq.
      rewrite (lt_of_ty_ctx_var (S f') G' n), (lt_of_ty_ctx_var (S f') G n).
      rewrite (InsLt_lookup_ty c G G' HIns n).
      destruct (ctx_lookup_ty G n) as [B|] eqn:E; simpl.
      * apply IHf.
      * reflexivity.
    + rewrite shift_lt_in_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. reflexivity.
    + rewrite shift_lt_in_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor. rewrite shift_lt_min_eq.
      f_equal. exact IHT.
    + rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite shift_lt_min_eq. rewrite IHT, IHT0. reflexivity.
Qed.

Lemma lt_of_ty_G_InsLt : forall c G G', InsLt c G G' ->
  forall T, lt_of_ty_G G' (shift_lt_in_ty 1 c T) = shift_lt 1 c (lt_of_ty_G G T).
Proof.
  intros c G G' HIns T. unfold lt_of_ty_G.
  rewrite (InsLt_length c G G' HIns).
  rewrite (lt_of_ty_ctx_InsLt c G G' HIns (S (length G)) T).
  f_equal.
  apply (lt_of_ty_ctx_fuel_irrel (S (length G)) (length G) T G 0).
  - apply VB_0.
  - simpl; lia.
  - simpl; lia.
Qed.

Lemma lt_sub_InsLt : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall c G', InsLt c G G' -> G' ⊢ₗ shift_lt 1 c l1 <: shift_lt 1 c l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l|Γ l|Γ x Δ Hlk|Γ l
                 |Γ l1 l2 l3 H1 IH1 H2 IH2|Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H1 IH1|Γ l l1 l2 H1 IH1];
    intros c G' HIns; simpl.
  - apply LS_Free.
  - apply LS_Local.
  - replace (if Nat.leb c x then x + 1 else x) with (shv c x)
      by (unfold shv; destruct (Nat.leb c x); [rewrite Nat.add_1_r|]; reflexivity).
    apply LS_Var.
    rewrite (InsLt_lookup_lt c Γ G' HIns x). rewrite Hlk. reflexivity.
  - apply LS_Refl.
  - eapply LS_Trans; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - apply LS_MinL; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - apply LS_MinR1; apply (IH1 c G' HIns).
  - apply LS_MinR2; apply (IH1 c G' HIns).
Qed.

Lemma shift_lt_in_ty_ltall_eq : forall a c A,
  shift_lt_in_ty a c (type_lt_all A) = type_lt_all (shift_lt_in_ty a (S c) A).
Proof. reflexivity. Qed.
Lemma shift_lt_in_ty_tyall_eq : forall a c B A,
  shift_lt_in_ty a c (type_ty_all B A)
  = type_ty_all (shift_lt_in_ty a c B) (shift_lt_in_ty a c A).
Proof. reflexivity. Qed.

Lemma sub_InsLt : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall c G', InsLt c G G' -> G' ⊢ shift_lt_in_ty 1 c T1 <:: shift_lt_in_ty 1 c T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk|Γ K l l' Ts Hls
                 |Γ T Δ Hls|Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' H1 IH1 H2 IH2];
    intros c G' HIns.
  - apply SA_Refl.
  - eapply SA_Trans; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - simpl. apply SA_VarCtx.
    rewrite (InsLt_lookup_ty c Γ G' HIns α). rewrite Hlk. reflexivity.
  - rewrite !shift_lt_in_ty_ctor_eq. apply SA_Data. apply (lt_sub_InsLt Γ l l' Hls c G' HIns).
  - rewrite shift_lt_in_ty_ctor_eq. cbn [List.map]. apply SA_Any.
    rewrite (lt_of_ty_G_InsLt c Γ G' HIns T).
    apply (lt_sub_InsLt Γ (lt_of_ty_G Γ T) Δ Hls c G' HIns).
  - rewrite !shift_lt_in_ty_fun_eq. apply SA_Fun.
    + apply (IH1 c G' HIns).
    + apply (lt_sub_InsLt Γ l l' Hl c G' HIns).
    + apply (IH2 c G' HIns).
  - rewrite !shift_lt_in_ty_ltall_eq. apply SA_LtAll.
    apply (IH1 (S c) (bind_lt (shift_lt 1 c lt_local) :: G') (InsLt_lt c Γ G' lt_local HIns)).
  - rewrite !shift_lt_in_ty_tyall_eq. apply SA_TyAll.
    + apply (IH1 c G' HIns).
    + apply (IH2 c (bind_ty (shift_lt_in_ty 1 c B') :: G') (InsLt_ty c Γ G' B' HIns)).
Qed.

Lemma sub_weaken_lt_shift : forall Γ D T1 T2,
  Γ ⊢ T1 <:: T2 ->
  (bind_lt D :: Γ) ⊢ shift_lt_in_ty 1 0 T1 <:: shift_lt_in_ty 1 0 T2.
Proof.
  intros Γ D T1 T2 H. apply (sub_InsLt Γ T1 T2 H 0 (bind_lt D :: Γ)). apply InsLt_here.
Qed.

(* ============================================================ *)
(* subst_lt_in_ty head-constructor rewrite equations             *)
(* ============================================================ *)
Lemma subst_lt_in_ty_var_eq : forall v R n,
  subst_lt_in_ty v R (type_var n) = type_var n.
Proof. reflexivity. Qed.
Lemma subst_lt_in_ty_fun_eq : forall v R A l B,
  subst_lt_in_ty v R (type_fun A l B)
  = type_fun (subst_lt_in_ty v R A) (subst_lt v R l) (subst_lt_in_ty v R B).
Proof. reflexivity. Qed.
Lemma subst_lt_in_ty_ltall_eq : forall v R A,
  subst_lt_in_ty v R (type_lt_all A)
  = type_lt_all (subst_lt_in_ty (S v) (shift_lt 1 0 R) A).
Proof. reflexivity. Qed.
Lemma subst_lt_in_ty_tyall_eq : forall v R B A,
  subst_lt_in_ty v R (type_ty_all B A)
  = type_ty_all (subst_lt_in_ty v R B) (subst_lt_in_ty v R A).
Proof. reflexivity. Qed.

Lemma subst_lt_var_eq : forall v R y,
  subst_lt v R (lt_var y) =
    if Nat.eqb y v then R else if Nat.ltb v y then lt_var (pred y) else lt_var y.
Proof. reflexivity. Qed.

(* ============================================================ *)
(* subst_lt / shift_lt : cancel and commute                     *)
(* ============================================================ *)

Lemma subst_lt_shift_cancel : forall l c R,
  subst_lt c R (shift_lt 1 c l) = l.
Proof.
  induction l as [y| | |l1 IH1 l2 IH2]; intros c R.
  - rewrite shift_lt_var_eq. destruct (Nat.leb c y) eqn:E.
    + apply Nat.leb_le in E. simpl subst_lt.
      destruct (Nat.eqb_spec (y+1) c); [lia|].
      destruct (Nat.ltb_spec c (y+1)); [|lia]. f_equal. lia.
    + apply Nat.leb_gt in E. simpl subst_lt.
      destruct (Nat.eqb_spec y c); [lia|].
      destruct (Nat.ltb_spec c y); [lia|]. reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IH1, IH2. reflexivity.
Qed.

Lemma subst_lt_in_ty_shift_cancel : forall T c R,
  subst_lt_in_ty c R (shift_lt_in_ty 1 c T) = T.
Proof.
  intros T. apply (type_list_ind
    (fun T => forall c R, subst_lt_in_ty c R (shift_lt_in_ty 1 c T) = T)
    (fun Ts => forall c R,
       List.map (subst_lt_in_ty c R) (List.map (shift_lt_in_ty 1 c) Ts) = Ts)).
  - intros n c R. reflexivity.
  - intros A l B HA HB c R.
    rewrite shift_lt_in_ty_fun_eq. simpl subst_lt_in_ty.
    rewrite HA, HB, subst_lt_shift_cancel. reflexivity.
  - intros K l Ts HTs c R.
    rewrite shift_lt_in_ty_ctor_eq, subst_lt_in_ty_ctor_eq.
    rewrite subst_lt_shift_cancel. f_equal. apply HTs.
  - intros A HA c R.
    rewrite shift_lt_in_ty_ltall_eq. simpl subst_lt_in_ty. rewrite HA. reflexivity.
  - intros B A HB HA c R.
    rewrite shift_lt_in_ty_tyall_eq. simpl subst_lt_in_ty. rewrite HB, HA. reflexivity.
  - intros c R. reflexivity.
  - intros A Ts HA HTs c R. cbn [List.map]. rewrite HA. f_equal. apply HTs.
Qed.

(* general-cutoff commute: shift below the subst point *)
Lemma shift_lt_subst_lt_comm : forall l n c R,
  c <= n ->
  shift_lt 1 c (subst_lt n R l) = subst_lt (S n) (shift_lt 1 c R) (shift_lt 1 c l).
Proof.
  induction l as [y| | |l1 IH1 l2 IH2]; intros n c R Hcn.
  - rewrite subst_lt_var_eq. rewrite (shift_lt_var_eq 1 c y).
    rewrite subst_lt_var_eq.
    destruct (Nat.eqb_spec y n) as [Hy|Hy].
    + subst y. destruct (Nat.leb c n) eqn:Ecn.
      * destruct (Nat.eqb_spec (n+1) (S n)); [reflexivity|lia].
      * apply Nat.leb_gt in Ecn. lia.
    + destruct (Nat.ltb_spec n y) as [Hlt|Hge].
      * rewrite (shift_lt_var_eq 1 c (pred y)).
        destruct (Nat.leb c y) eqn:E2; destruct (Nat.leb c (pred y)) eqn:E1.
        -- destruct (Nat.eqb_spec (y+1) (S n)); [lia|].
           destruct (Nat.ltb_spec (S n) (y+1)); [|lia]. f_equal. lia.
        -- apply Nat.leb_le in E2. apply Nat.leb_gt in E1. lia.
        -- apply Nat.leb_gt in E2. lia.
        -- apply Nat.leb_gt in E2. lia.
      * rewrite (shift_lt_var_eq 1 c y).
        destruct (Nat.leb c y) eqn:E2.
        -- destruct (Nat.eqb_spec (y+1) (S n)); [lia|].
           destruct (Nat.ltb_spec (S n) (y+1)); [lia|]. reflexivity.
        -- destruct (Nat.eqb_spec y (S n)); [lia|].
           destruct (Nat.ltb_spec (S n) y); [lia|]. reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IH1 by lia. rewrite IH2 by lia. reflexivity.
Qed.

Lemma shift_lt_subst_lt_comm0 : forall l n R,
  shift_lt 1 0 (subst_lt n R l) = subst_lt (S n) (shift_lt 1 0 R) (shift_lt 1 0 l).
Proof. intros l n R. apply shift_lt_subst_lt_comm. lia. Qed.

Lemma shift_lt_in_ty_subst_lt_in_ty_comm : forall T n c R,
  c <= n ->
  shift_lt_in_ty 1 c (subst_lt_in_ty n R T)
  = subst_lt_in_ty (S n) (shift_lt 1 c R) (shift_lt_in_ty 1 c T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall n c R, c <= n ->
       shift_lt_in_ty 1 c (subst_lt_in_ty n R T)
       = subst_lt_in_ty (S n) (shift_lt 1 c R) (shift_lt_in_ty 1 c T))
    (fun Ts => forall n c R, c <= n ->
       List.map (shift_lt_in_ty 1 c) (List.map (subst_lt_in_ty n R) Ts)
       = List.map (subst_lt_in_ty (S n) (shift_lt 1 c R)) (List.map (shift_lt_in_ty 1 c) Ts))).
  - intros m n c R Hcn. reflexivity.
  - intros A l B HA HB n c R Hcn.
    simpl subst_lt_in_ty. rewrite !shift_lt_in_ty_fun_eq. simpl subst_lt_in_ty.
    rewrite HA by lia. rewrite HB by lia. rewrite shift_lt_subst_lt_comm by lia. reflexivity.
  - intros K l Ts HTs n c R Hcn.
    rewrite subst_lt_in_ty_ctor_eq, !shift_lt_in_ty_ctor_eq, subst_lt_in_ty_ctor_eq.
    rewrite shift_lt_subst_lt_comm by lia. f_equal. apply HTs. lia.
  - intros A HA n c R Hcn.
    rewrite subst_lt_in_ty_ltall_eq, !shift_lt_in_ty_ltall_eq, subst_lt_in_ty_ltall_eq.
    f_equal.
    rewrite (HA (S n) (S c) (shift_lt 1 0 R) ltac:(lia)).
    f_equal. symmetry. apply shift_lt_swap. lia.
  - intros B A HB HA n c R Hcn.
    rewrite subst_lt_in_ty_tyall_eq, !shift_lt_in_ty_tyall_eq, subst_lt_in_ty_tyall_eq.
    rewrite HB by lia. rewrite HA by lia. reflexivity.
  - intros n c R Hcn. reflexivity.
  - intros A Ts HA HTs n c R Hcn.
    cbn [List.map]. rewrite HA by lia. f_equal. apply HTs. lia.
Qed.

Lemma shift_lt_in_ty_subst_lt_in_ty_comm0 : forall T n R,
  shift_lt_in_ty 1 0 (subst_lt_in_ty n R T)
  = subst_lt_in_ty (S n) (shift_lt 1 0 R) (shift_lt_in_ty 1 0 T).
Proof. intros T n R. apply shift_lt_in_ty_subst_lt_in_ty_comm. lia. Qed.

Lemma shift_ty_subst_lt_in_ty_commute : forall T a1 c1 n R,
  shift_ty a1 c1 (subst_lt_in_ty n R T)
  = subst_lt_in_ty n R (shift_ty a1 c1 T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall a1 c1 n R,
       shift_ty a1 c1 (subst_lt_in_ty n R T) = subst_lt_in_ty n R (shift_ty a1 c1 T))
    (fun Ts => forall a1 c1 n R,
       List.map (shift_ty a1 c1) (List.map (subst_lt_in_ty n R) Ts)
       = List.map (subst_lt_in_ty n R) (List.map (shift_ty a1 c1) Ts))).
  - intros m a1 c1 n R. reflexivity.
  - intros A l B HA HB a1 c1 n R.
    simpl subst_lt_in_ty. simpl shift_ty. simpl subst_lt_in_ty.
    rewrite HA, HB. reflexivity.
  - intros K l Ts HTs a1 c1 n R.
    rewrite subst_lt_in_ty_ctor_eq, shift_ty_ctor_eq, shift_ty_ctor_eq, subst_lt_in_ty_ctor_eq.
    f_equal. apply HTs.
  - intros A HA a1 c1 n R.
    simpl subst_lt_in_ty. simpl shift_ty. simpl subst_lt_in_ty. rewrite HA. reflexivity.
  - intros B A HB HA a1 c1 n R.
    simpl subst_lt_in_ty. simpl shift_ty. simpl subst_lt_in_ty. rewrite HB, HA. reflexivity.
  - intros a1 c1 n R. reflexivity.
  - intros A Ts HA HTs a1 c1 n R. cbn [List.map]. rewrite HA. f_equal. apply HTs.
Qed.

(* ============================================================ *)
(* SubstLt : substitute a lifetime for an lt-binder at depth n   *)
(* ============================================================ *)

Definition slv (n a : nat) : nat := if Nat.ltb n a then pred a else a.

Lemma slv_S : forall n a, slv (S n) (S a) = S (slv n a).
Proof.
  intros n a. unfold slv.
  replace (Nat.ltb (S n) (S a)) with (Nat.ltb n a) by reflexivity.
  destruct (Nat.ltb_spec n a) as [H|H]; simpl; [lia | reflexivity].
Qed.

Lemma subst_lt_var_neq : forall n R x,
  x <> n -> subst_lt n R (lt_var x) = lt_var (slv n x).
Proof.
  intros n R x H. rewrite subst_lt_var_eq.
  destruct (Nat.eqb_spec x n); [contradiction|]. unfold slv.
  destruct (Nat.ltb n x); reflexivity.
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
    SubstLt R n (bind_ty B :: G) (bind_ty (subst_lt_in_ty n R B) :: G').

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
Qed.

Lemma SubstLt_lookup_lt : forall R n G G', SubstLt R n G G' ->
  forall a, a <> n ->
  ctx_lookup_lt G' (slv n a) = option_map (subst_lt n R) (ctx_lookup_lt G a).
Proof.
  intros R n G G' H. induction H; intros a Hne.
  - destruct a as [|a']; [contradiction|].
    unfold slv. simpl Nat.ltb. simpl pred. simpl ctx_lookup_lt.
    destruct (ctx_lookup_lt Gamma a') as [X|]; simpl;
      [rewrite subst_lt_shift_cancel; reflexivity | reflexivity].
  - destruct a as [|a'].
    + unfold slv. simpl Nat.ltb. simpl ctx_lookup_lt.
      rewrite shift_lt_subst_lt_comm0. reflexivity.
    + assert (a' <> n) by lia.
      rewrite slv_S. simpl ctx_lookup_lt. rewrite (IHSubstLt a' H0).
      destruct (ctx_lookup_lt G a') as [X|]; simpl;
        [rewrite shift_lt_subst_lt_comm0; reflexivity | reflexivity].
  - specialize (IHSubstLt a Hne). simpl ctx_lookup_lt. apply IHSubstLt.
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
Qed.

Lemma lt_sub_SubstLt : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall R n G', SubstLt R n G G' ->
  G' ⊢ₗ subst_lt n R l1 <: subst_lt n R l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l|Γ l|Γ x Δ Hlk|Γ l
                 |Γ l1 l2 l3 H1 IH1 H2 IH2|Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H1 IH1|Γ l l1 l2 H1 IH1];
    intros R n G' HS.
  - apply LS_Free.
  - apply LS_Local.
  - destruct (Nat.eq_dec x n) as [Hx|Hx].
    + subst x. rewrite subst_lt_var_eq. rewrite Nat.eqb_refl.
      destruct (SubstLt_target R n Γ G' HS) as [Δt [Hlkt Hsubt]].
      rewrite Hlk in Hlkt. inversion Hlkt; subst Δt. exact Hsubt.
    + rewrite (subst_lt_var_neq n R x Hx). apply LS_Var.
      rewrite (SubstLt_lookup_lt R n Γ G' HS x Hx). rewrite Hlk. reflexivity.
  - apply LS_Refl.
  - eapply LS_Trans; [apply (IH1 R n G' HS) | apply (IH2 R n G' HS)].
  - apply LS_MinL; [apply (IH1 R n G' HS) | apply (IH2 R n G' HS)].
  - apply LS_MinR1; apply (IH1 R n G' HS).
  - apply LS_MinR2; apply (IH1 R n G' HS).
Qed.

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

Lemma sub_SubstLt : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall R n G', SubstLt R n G G' ->
  G' ⊢ subst_lt_in_ty n R T1 <:: subst_lt_in_ty n R T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk|Γ K l l' Ts Hls
                 |Γ T Δ Hls|Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' H1 IH1 H2 IH2];
    intros R n G' HS.
  - apply SA_Refl.
  - eapply SA_Trans; [apply (IH1 R n G' HS) | apply (IH2 R n G' HS)].
  - rewrite subst_lt_in_ty_var_eq. apply SA_VarCtx.
    rewrite (SubstLt_lookup_ty R n Γ G' HS α). rewrite Hlk. reflexivity.
  - rewrite !subst_lt_in_ty_ctor_eq. apply SA_Data.
    apply (lt_sub_SubstLt Γ l l' Hls R n G' HS).
  - rewrite subst_lt_in_ty_ctor_eq. cbn [List.map]. apply SA_Any.
    rewrite (lt_of_ty_G_SubstLt R n Γ G' HS T).
    apply (lt_sub_SubstLt Γ (lt_of_ty_G Γ T) Δ Hls R n G' HS).
  - rewrite !subst_lt_in_ty_fun_eq. apply SA_Fun.
    + apply (IH1 R n G' HS).
    + apply (lt_sub_SubstLt Γ l l' Hl R n G' HS).
    + apply (IH2 R n G' HS).
  - rewrite !subst_lt_in_ty_ltall_eq. apply SA_LtAll.
    apply (IH1 (shift_lt 1 0 R) (S n) (bind_lt lt_local :: G')
             (SubstLt_lt R n Γ G' lt_local HS)).
  - rewrite !subst_lt_in_ty_tyall_eq. apply SA_TyAll.
    + apply (IH1 R n G' HS).
    + apply (IH2 R n (bind_ty (subst_lt_in_ty n R B') :: G')
               (SubstLt_ty R n Γ G' B' HS)).
Qed.

(* ================================================================== *)
(* subst_ty rewrite equations                                         *)
(* ================================================================== *)

Lemma subst_ty_go_eq_map : forall v Sb Ts,
  (fix go Ts := match Ts with [] => [] | A :: rest => subst_ty v Sb A :: go rest end) Ts
  = List.map (subst_ty v Sb) Ts.
Proof. intros; induction Ts; simpl; congruence. Qed.

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
    rewrite subst_ty_fun_eq, shift_lt_in_ty_fun_eq, shift_lt_in_ty_fun_eq, subst_ty_fun_eq.
    rewrite HA, HB. reflexivity.
  - intros K l Ts HTs c n Sb.
    rewrite subst_ty_ctor_eq, shift_lt_in_ty_ctor_eq, shift_lt_in_ty_ctor_eq, subst_ty_ctor_eq.
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

Lemma shift_lt_in_ty_subst_ty_comm0 : forall T n Sb,
  shift_lt_in_ty 1 0 (subst_ty n Sb T)
  = subst_ty n (shift_lt_in_ty 1 0 Sb) (shift_lt_in_ty 1 0 T).
Proof. intros. apply shift_lt_in_ty_subst_ty_comm. Qed.

(* ================================================================== *)
(* SubstTy : substitute a type for a ty-binder at depth n             *)
(* ================================================================== *)

Lemma lt_min_mono : forall G a1 a2 b1 b2,
  G ⊢ₗ a1 <: a2 -> G ⊢ₗ b1 <: b2 -> G ⊢ₗ lt_min a1 b1 <: lt_min a2 b2.
Proof.
  intros G a1 a2 b1 b2 Ha Hb. apply LS_MinL.
  - eapply LS_Trans; [exact Ha | apply LS_MinR1; apply LS_Refl].
  - eapply LS_Trans; [exact Hb | apply LS_MinR2; apply LS_Refl].
Qed.

Lemma subst_ty_var_neq : forall n Sb x,
  x <> n -> subst_ty n Sb (type_var x) = type_var (slv n x).
Proof.
  intros n Sb x H. rewrite subst_ty_var_eq.
  destruct (Nat.eqb_spec x n); [contradiction|]. unfold slv.
  destruct (Nat.ltb n x); reflexivity.
Qed.

Inductive SubstTy : type -> nat -> ctx -> ctx -> Prop :=
| SubstTy_here : forall Gamma B Sb,
    Gamma ⊢ Sb <:: B ->
    SubstTy Sb 0 (bind_ty B :: Gamma) Gamma
| SubstTy_ty : forall Sb n G G' B,
    SubstTy Sb n G G' ->
    SubstTy (shift_ty 1 0 Sb) (S n)
            (bind_ty B :: G)
            (bind_ty (subst_ty n Sb B) :: G')
| SubstTy_lt : forall Sb n G G' D,
    SubstTy Sb n G G' ->
    SubstTy (shift_lt_in_ty 1 0 Sb) n
            (bind_lt D :: G)
            (bind_lt D :: G').

Lemma SubstTy_length : forall Sb n G G', SubstTy Sb n G G' -> length G = S (length G').
Proof. intros Sb n G G' H. induction H; simpl; lia. Qed.

Lemma SubstTy_n_lt : forall Sb n G G', SubstTy Sb n G G' -> n < length G.
Proof. intros Sb n G G' H. induction H; simpl; lia. Qed.

Lemma SubstTy_S_VB : forall Sb n G G', SubstTy Sb n G G' -> VB n Sb.
Proof.
  intros Sb n G G' H. induction H.
  - apply VB_0.
  - apply shift_ty_VB. exact IHSubstTy.
  - apply shift_lt_in_ty_VB. exact IHSubstTy.
Qed.

Lemma SubstTy_lookup_ty : forall Sb n G G', SubstTy Sb n G G' ->
  forall a, a <> n ->
  ctx_lookup_ty G' (slv n a) = option_map (subst_ty n Sb) (ctx_lookup_ty G a).
Proof.
  intros Sb n G G' H. induction H; intros a Hne.
  - destruct a as [|a']; [contradiction|].
    unfold slv. simpl Nat.ltb. simpl pred. simpl ctx_lookup_ty.
    destruct (ctx_lookup_ty Gamma a') as [X|]; simpl;
      [rewrite subst_ty_shift_cancel; reflexivity | reflexivity].
  - destruct a as [|a'].
    + unfold slv. simpl Nat.ltb. simpl ctx_lookup_ty.
      rewrite shift_ty_subst_ty_comm0. reflexivity.
    + assert (a' <> n) by lia.
      rewrite slv_S. simpl ctx_lookup_ty. rewrite (IHSubstTy a' H0).
      destruct (ctx_lookup_ty G a') as [X|]; simpl;
        [rewrite shift_ty_subst_ty_comm0; reflexivity | reflexivity].
  - specialize (IHSubstTy a Hne). simpl ctx_lookup_ty. rewrite IHSubstTy.
    destruct (ctx_lookup_ty G a) as [X|]; simpl;
      [rewrite shift_lt_in_ty_subst_ty_comm0; reflexivity | reflexivity].
Qed.

Lemma SubstTy_lookup_lt : forall Sb n G G', SubstTy Sb n G G' ->
  forall x, ctx_lookup_lt G' x = ctx_lookup_lt G x.
Proof.
  intros Sb n G G' H. induction H; intro x.
  - simpl ctx_lookup_lt. reflexivity.
  - simpl ctx_lookup_lt. apply IHSubstTy.
  - destruct x as [|x']; simpl ctx_lookup_lt.
    + reflexivity.
    + rewrite (IHSubstTy x'). reflexivity.
Qed.

Lemma lt_sub_SubstTy_ctx : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall Sb n G', SubstTy Sb n G G' -> G' ⊢ₗ l1 <: l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l|Γ l|Γ x Δ Hlk|Γ l
                 |Γ l1 l2 l3 H1 IH1 H2 IH2|Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H1 IH1|Γ l l1 l2 H1 IH1];
    intros Sb n G' HS.
  - apply LS_Free.
  - apply LS_Local.
  - apply LS_Var. rewrite (SubstTy_lookup_lt Sb n Γ G' HS x). exact Hlk.
  - apply LS_Refl.
  - eapply LS_Trans; [apply (IH1 Sb n G' HS) | apply (IH2 Sb n G' HS)].
  - apply LS_MinL; [apply (IH1 Sb n G' HS) | apply (IH2 Sb n G' HS)].
  - apply LS_MinR1; apply (IH1 Sb n G' HS).
  - apply LS_MinR2; apply (IH1 Sb n G' HS).
Qed.

Lemma lt_of_ty_G_mono_sub : forall G T1 T2, G ⊢ T1 <:: T2 ->
  G ⊢ₗ lt_of_ty_G G T1 <: lt_of_ty_G G T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T|Γ S0 U T H1 IH1 H2 IH2|Γ α B Hlk|Γ K l l' Ts Hls
                 |Γ T Δ Hls|Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' H1 IH1 H2 IH2].
  - apply LS_Refl.
  - eapply LS_Trans; [exact IH1 | exact IH2].
  - unfold lt_of_ty_G.
    assert (Hlt: α < length Γ).
    { destruct (Nat.le_gt_cases (length Γ) α) as [Hle|Hgt]; [|exact Hgt].
      rewrite ctx_lookup_ty_None in Hlk by exact Hle; discriminate. }
    rewrite (lt_of_ty_ctx_var (length Γ) Γ α).
    destruct (length Γ) as [|m] eqn:HL; [lia|].
    rewrite Hlk.
    rewrite (lt_of_ty_ctx_fuel_irrel m (S m) B Γ (S α)
               (ctx_inv_all Γ α B Hlk) ltac:(lia) ltac:(lia)).
    apply LS_Refl.
  - unfold lt_of_ty_G. rewrite !lt_of_ty_ctx_ctor.
    apply lt_min_mono; [exact Hls | apply LS_Refl].
  - replace (lt_of_ty_G Γ (type_ctor any_tag Δ [])) with (lt_min Δ lt_free).
    + eapply LS_Trans; [exact Hls | apply LS_MinR1; apply LS_Refl].
    + unfold lt_of_ty_G. rewrite lt_of_ty_ctx_ctor, lt_of_ty_ctx_list_nil. reflexivity.
  - unfold lt_of_ty_G. rewrite !lt_of_ty_ctx_fun. exact Hl.
  - unfold lt_of_ty_G. rewrite !lt_of_ty_ctx_ltall. apply LS_Refl.
  - unfold lt_of_ty_G. rewrite !lt_of_ty_ctx_tyall. apply LS_Refl.
Qed.

Lemma SubstTy_target : forall Sb n G G', SubstTy Sb n G G' ->
  exists B, ctx_lookup_ty G n = Some B /\
    G' ⊢ₗ lt_of_ty_G G' Sb <: lt_of_ty_G G B.
Proof.
  intros Sb n G G' H. induction H.
  - exists (shift_ty 1 0 B). split.
    + reflexivity.
    + rewrite lt_of_ty_G_weaken_ty. apply lt_of_ty_G_mono_sub. exact H.
  - destruct IHSubstTy as [B0 [Hlk Hsub]].
    exists (shift_ty 1 0 B0). split.
    + simpl ctx_lookup_ty. rewrite Hlk. reflexivity.
    + rewrite lt_of_ty_G_weaken_ty. rewrite lt_of_ty_G_weaken_ty.
      apply (lt_sub_InsTy G' (lt_of_ty_G G' Sb) (lt_of_ty_G G B0) Hsub
               0 (bind_ty (subst_ty n Sb B) :: G') (InsTy_here _ _)).
  - destruct IHSubstTy as [B0 [Hlk Hsub]].
    exists (shift_lt_in_ty 1 0 B0). split.
    + simpl ctx_lookup_ty. rewrite Hlk. reflexivity.
    + rewrite lt_of_ty_G_weaken_lt. rewrite lt_of_ty_G_weaken_lt.
      apply (lt_sub_InsLt G' (lt_of_ty_G G' Sb) (lt_of_ty_G G B0) Hsub
               0 (bind_lt D :: G') (InsLt_here _ _)).
Qed.

Lemma SubstTy_sub_target : forall Sb n G G', SubstTy Sb n G G' ->
  forall B, ctx_lookup_ty G n = Some B ->
  G' ⊢ Sb <:: subst_ty n Sb B.
Proof.
  intros Sb n G G' H. induction H; intros B0 HB.
  - simpl in HB. injection HB as HB; subst B0.
    rewrite subst_ty_shift_cancel. exact H.
  - simpl in HB. destruct (ctx_lookup_ty G n) as [B'|] eqn:E; simpl in HB; [|discriminate].
    injection HB as HB; subst B0.
    rewrite <- shift_ty_subst_ty_comm0. apply sub_weaken_ty_shift. apply (IHSubstTy B' eq_refl).
  - simpl in HB. destruct (ctx_lookup_ty G n) as [B'|] eqn:E; simpl in HB; [|discriminate].
    injection HB as HB; subst B0.
    rewrite <- shift_lt_in_ty_subst_ty_comm0. apply sub_weaken_lt_shift. apply (IHSubstTy B' eq_refl).
Qed.

Lemma lt_of_ty_ctx_SubstTy_le : forall Sb n G G', SubstTy Sb n G G' ->
  forall f T k, VB k T -> length G <= k + f ->
  G' ⊢ₗ lt_of_ty_ctx f G' (subst_ty n Sb T) <: lt_of_ty_ctx f G T.
Proof.
  intros Sb n G G' HS.
  pose proof (SubstTy_n_lt Sb n G G' HS) as Hn.
  pose proof (SubstTy_S_VB Sb n G G' HS) as HSVB.
  pose proof (SubstTy_length Sb n G G' HS) as HLen.
  destruct (SubstTy_target Sb n G G' HS) as [Btgt [Htgt Hsubtgt]].
  induction f as [|f' IHf]; intros T k HVB Hlen.
  - rewrite Nat.add_0_r in Hlen. revert k HVB Hlen.
    induction T using type_list_ind with
      (Q := fun Ts => forall k, VBL k Ts -> length G <= k ->
              G' ⊢ₗ lt_of_ty_ctx_list 0 G' (List.map (subst_ty n Sb) Ts)
                  <: lt_of_ty_ctx_list 0 G Ts);
      intros k HVB Hlen.
    + simpl in HVB.
      assert (Hane : n0 <> n) by lia.
      rewrite (subst_ty_var_neq n Sb n0 Hane).
      rewrite !(lt_of_ty_ctx_var 0). apply LS_Refl.
    + rewrite subst_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. apply LS_Refl.
    + rewrite subst_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor.
      rewrite VB_ctor in HVB.
      apply lt_min_mono; [apply LS_Refl | apply (IHT k); [exact HVB | exact Hlen]].
    + rewrite subst_ty_ltall_eq. rewrite !lt_of_ty_ctx_ltall. apply LS_Refl.
    + rewrite subst_ty_tyall_eq. rewrite !lt_of_ty_ctx_tyall. apply LS_Refl.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl.
    + rewrite VBL_cons in HVB. destruct HVB as [Ha Hr].
      cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons.
      apply lt_min_mono; [apply (IHT k); [exact Ha|exact Hlen] | apply (IHT0 k); [exact Hr|exact Hlen]].
  - revert k HVB Hlen.
    induction T using type_list_ind with
      (Q := fun Ts => forall k, VBL k Ts -> length G <= k + S f' ->
              G' ⊢ₗ lt_of_ty_ctx_list (S f') G' (List.map (subst_ty n Sb) Ts)
                  <: lt_of_ty_ctx_list (S f') G Ts);
      intros k HVB Hlen.
    + simpl in HVB.
      destruct (Nat.eq_dec n0 n) as [Hae|Hane].
      * subst n0. rewrite subst_ty_var_eq, Nat.eqb_refl.
        rewrite (lt_of_ty_ctx_fuel_irrel (S f') (length G') Sb G' n HSVB ltac:(lia) ltac:(lia)).
        replace (lt_of_ty_ctx (S f') G (type_var n)) with (lt_of_ty_ctx (length G) G Btgt).
        -- unfold lt_of_ty_G in Hsubtgt. exact Hsubtgt.
        -- rewrite (lt_of_ty_ctx_var (S f') G n), Htgt.
           apply (lt_of_ty_ctx_fuel_irrel (length G) f' Btgt G (S n)
                    (ctx_inv_all G n Btgt Htgt) ltac:(lia) ltac:(lia)).
      * rewrite (subst_ty_var_neq n Sb n0 Hane).
        rewrite (lt_of_ty_ctx_var (S f') G' (slv n n0)).
        rewrite (lt_of_ty_ctx_var (S f') G n0).
        rewrite (SubstTy_lookup_ty Sb n G G' HS n0 Hane).
        destruct (ctx_lookup_ty G n0) as [B0|] eqn:E; simpl.
        -- apply (IHf B0 (S n0) (ctx_inv_all G n0 B0 E)). lia.
        -- apply LS_Refl.
    + rewrite subst_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. apply LS_Refl.
    + rewrite subst_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor.
      rewrite VB_ctor in HVB.
      apply lt_min_mono; [apply LS_Refl | apply (IHT k); [exact HVB|exact Hlen]].
    + rewrite subst_ty_ltall_eq. rewrite !lt_of_ty_ctx_ltall. apply LS_Refl.
    + rewrite subst_ty_tyall_eq. rewrite !lt_of_ty_ctx_tyall. apply LS_Refl.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl.
    + rewrite VBL_cons in HVB. destruct HVB as [Ha Hr].
      cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons.
      apply lt_min_mono; [apply (IHT k); [exact Ha|exact Hlen] | apply (IHT0 k); [exact Hr|exact Hlen]].
Qed.

Lemma lt_of_ty_G_SubstTy_le : forall Sb n G G', SubstTy Sb n G G' ->
  forall T, G' ⊢ₗ lt_of_ty_G G' (subst_ty n Sb T) <: lt_of_ty_G G T.
Proof.
  intros Sb n G G' HS T. unfold lt_of_ty_G.
  pose proof (SubstTy_length Sb n G G' HS) as HL.
  rewrite (lt_of_ty_ctx_fuel_irrel (length G') (length G)
             (subst_ty n Sb T) G' 0 (VB_0 _) ltac:(lia) ltac:(lia)).
  apply (lt_of_ty_ctx_SubstTy_le Sb n G G' HS (length G) T 0 (VB_0 T) ltac:(lia)).
Qed.

Lemma sub_SubstTy : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall Sb n G', SubstTy Sb n G G' ->
  G' ⊢ subst_ty n Sb T1 <:: subst_ty n Sb T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T|Γ S0 U T H1 IH1 H2 IH2|Γ α B Hlk|Γ K l l' Ts Hls
                 |Γ T Δ Hls|Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' H1 IH1 H2 IH2];
    intros Sb n G' HS.
  - apply SA_Refl.
  - eapply SA_Trans; [apply (IH1 Sb n G' HS) | apply (IH2 Sb n G' HS)].
  - destruct (Nat.eq_dec α n) as [Hae|Hane].
    + subst α. rewrite subst_ty_var_eq, Nat.eqb_refl.
      apply (SubstTy_sub_target Sb n Γ G' HS B Hlk).
    + rewrite (subst_ty_var_neq n Sb α Hane). apply SA_VarCtx.
      rewrite (SubstTy_lookup_ty Sb n Γ G' HS α Hane). rewrite Hlk. reflexivity.
  - rewrite !subst_ty_ctor_eq. apply SA_Data.
    apply (lt_sub_SubstTy_ctx Γ l l' Hls Sb n G' HS).
  - rewrite subst_ty_ctor_eq. cbn [List.map]. apply SA_Any.
    eapply LS_Trans.
    + apply (lt_of_ty_G_SubstTy_le Sb n Γ G' HS T).
    + apply (lt_sub_SubstTy_ctx Γ (lt_of_ty_G Γ T) Δ Hls Sb n G' HS).
  - rewrite !subst_ty_fun_eq. apply SA_Fun.
    + apply (IH1 Sb n G' HS).
    + apply (lt_sub_SubstTy_ctx Γ l l' Hl Sb n G' HS).
    + apply (IH2 Sb n G' HS).
  - rewrite !subst_ty_ltall_eq. apply SA_LtAll.
    apply (IH1 (shift_lt_in_ty 1 0 Sb) n (bind_lt lt_local :: G')
             (SubstTy_lt Sb n Γ G' lt_local HS)).
  - rewrite !subst_ty_tyall_eq. apply SA_TyAll.
    + apply (IH1 Sb n G' HS).
    + apply (IH2 (shift_ty 1 0 Sb) (S n) (bind_ty (subst_ty n Sb B') :: G')
               (SubstTy_ty Sb n Γ G' B' HS)).
Qed.

(* Subtyping is preserved by type-substitution at the head binder.    *)
Lemma sub_subst_ty : forall Γ B U0 U S,
  (bind_ty B :: Γ) ⊢ U0 <:: U ->
  Γ ⊢ S <:: B ->
  Γ ⊢ subst_ty 0 S U0 <:: subst_ty 0 S U.
Proof.
  intros Γ B U0 U S Hsub HSsub.
  apply (sub_SubstTy (bind_ty B :: Γ) U0 U Hsub S 0 Γ
           (SubstTy_here Γ B S HSsub)).
Qed.

Lemma sub_subst_lt : forall Γ Δ U0 U Δ',
  (bind_lt Δ :: Γ) ⊢ U0 <:: U ->
  Γ ⊢ₗ Δ' <: Δ ->
  Γ ⊢ subst_lt_in_ty 0 Δ' U0 <:: subst_lt_in_ty 0 Δ' U.
Proof.
  intros Γ Δ U0 U Δ' Hsub HltΔ.
  apply (sub_SubstLt (bind_lt Δ :: Γ) U0 U Hsub Δ' 0 Γ).
  apply SubstLt_here. exact HltΔ.
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

(* Bounded witnesses preserve subtyping through the iterated           *)
(* substitution sequence used by `elim_ty_n_sound`.                    *)
Axiom iter_subst_lt_in_ty_mono : forall ws Γ bound T1 T2,
  chain_bounded Γ ws bound ->
  Γ ⊢ T1 <:: T2 ->
  Γ ⊢ iter_subst_lt_in_ty ws T1 <:: iter_subst_lt_in_ty ws T2.

(* From the typing of a ctor *value* `term_ctor K Delta lts Ts vs`     *)
(* against type `type_ctor K Delta Ts`, the witnesses form both the    *)
(* raw chain used by term substitution and the `shift_each_lt` chain   *)
(* used by the corrected subst-list/iterated-subst bridge.             *)
Axiom ctor_lts_chain_bounded : forall Γ lts n_lt n_ty Ts sigma vs Delta Delta',
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs
          (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma) ->
  List.length lts = n_lt ->
  Delta = lt_of_ty_list (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma) ->
  Γ ⊢ₗ Delta <: Delta' ->
  chain_bounded Γ lts (shift_lt n_lt 0 Delta') /\
  chain_bounded Γ (shift_each_lt lts) (shift_lt n_lt 0 Delta') /\
  Forall (ctor_field_bounded_ty n_lt)
         (List.map (inst_ty_vars n_ty Ts) sigma).

(* ---- Substitution preservation (typing) ------------------------ *)

Axiom subst_tm_lemma : forall Γ T1 t T2 v,
  (bind_tm T1 :: Γ) ⊢ₜ t : T2 ->
  value v ->
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
  Forall value vs ->
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rhos ->
  (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos) ⊢ₜ t : T ->
  Γ ⊢ₜ subst_list_tm vs t : T.

(* Substituting `lts` for bounded schema variables `lt_var_list n_lt`  *)
(* yields direct schema instantiation.                                 *)
Lemma inst_ctor_type_subst_eq : forall n_lt n_ty lts Ts sigma_fields,
  List.length lts = n_lt ->
  Forall (ctor_field_bounded_ty n_lt)
         (List.map (inst_ty_vars n_ty Ts) sigma_fields) ->
  subst_list_lt_in_ty_each lts
    (List.map (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts) sigma_fields)
  = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields.
Proof.
  intros n_lt n_ty lts Ts sigma_fields Hlen Hbounded.
  unfold subst_list_lt_in_ty_each.
  induction sigma_fields as [|sigma rest IH]; simpl in *.
  - reflexivity.
  - pose proof Hlen as Hlen0.
    inversion Hbounded as [|T Ts' Hhead Htail Heq]; subst.
    simpl. f_equal.
    + unfold inst_ctor_type, inst_lt_vars.
      apply bounded_ctor_inst_type_core; [exact Hlen0 | exact Hhead].
    + apply IH. exact Htail.
Qed.
