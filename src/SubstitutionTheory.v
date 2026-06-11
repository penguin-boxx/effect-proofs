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
  Hypothesis Hhandle     : forall E n_beta Ts T_B T_R op_body body,
    P op_body -> P body -> P (term_handle E n_beta Ts T_B T_R op_body body).
  Hypothesis Hperform    : forall t Ss arg, P t -> P arg -> P (term_perform t Ss arg).
  Hypothesis Hcap        : forall E m n_beta Ts T_R op_body, P op_body -> P (term_cap E m n_beta Ts T_R op_body).
  Hypothesis Hhandler_m  : forall m T_B T_R t, P t -> P (term_handler_m m T_B T_R t).
  Hypothesis Hresume     : forall m T_B T_R b, P b -> P (term_resume m T_B T_R b).
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
    | term_match scrut tag n_lt arity yes_body no_body =>
      Hmatch scrut tag n_lt arity yes_body no_body
          (term_list_ind scrut) (term_list_ind yes_body) (term_list_ind no_body)
    | term_handle E n_beta Ts T_B T_R op_body body =>
      Hhandle E n_beta Ts T_B T_R op_body body (term_list_ind op_body) (term_list_ind body)
    | term_perform t Ss arg => Hperform t Ss arg (term_list_ind t) (term_list_ind arg)
    | term_cap E m n_beta Ts T_R op_body => Hcap E m n_beta Ts T_R op_body (term_list_ind op_body)
    | term_handler_m m T_B T_R t => Hhandler_m m T_B T_R t (term_list_ind t)
    | term_resume m T_B T_R b => Hresume m T_B T_R b (term_list_ind b)
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
  - intros scrut tag n_lt arity yes_body no_body Hs Hy Hn c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E n_beta Ts T_B T_R op_body body Hop Hb c; simpl;
    rewrite Hop, Hb; reflexivity.
  - intros t Ss arg Ht Ha c; simpl; rewrite Ht, Ha; reflexivity.
  - intros E m n_beta Ts T_R op_body Hop c; simpl; rewrite Hop; reflexivity.
  - intros m T_B T_R t H c; simpl; rewrite H; reflexivity.
  - intros m T_B T_R b H c; simpl; rewrite H; reflexivity.
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
  - intros scrut tag n_lt arity yes_body no_body Hs Hy Hn c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E n_beta Ts T_B T_R op_body body Hop Hb c; simpl.
    unfold shift_ty_list. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, !shift_ty_zero, Hop, Hb; reflexivity.
    + intro T; apply shift_ty_zero.
  - intros t Ss arg Ht Ha c; simpl.
    unfold shift_ty_list. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, Ht, Ha; reflexivity.
    + intro T; apply shift_ty_zero.
  - intros E m n_beta Ts T_R op_body Hop c; simpl.
    unfold shift_ty_list. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, shift_ty_zero, Hop; reflexivity.
    + intro T; apply shift_ty_zero.
  - intros m T_B T_R t H c; simpl; rewrite !shift_ty_zero, H; reflexivity.
  - intros m T_B T_R b H c; simpl; rewrite !shift_ty_zero, H; reflexivity.
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
  - intros scrut tag n_lt arity yes_body no_body Hs Hy Hn c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E n_beta Ts T_B T_R op_body body Hop Hb c; simpl.
    unfold shift_lt_in_ty_list. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, !shift_lt_in_ty_zero, Hop, Hb; reflexivity.
    + intro T; apply shift_lt_in_ty_zero.
  - intros t Ss arg Ht Ha c; simpl.
    unfold shift_lt_in_ty_list. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, Ht, Ha; reflexivity.
    + intro T; apply shift_lt_in_ty_zero.
  - intros E m n_beta Ts T_R op_body Hop c; simpl.
    unfold shift_lt_in_ty_list. rewrite List.map_ext with (g := id).
    + rewrite List.map_id, shift_lt_in_ty_zero, Hop; reflexivity.
    + intro T; apply shift_lt_in_ty_zero.
  - intros m T_B T_R t H c; simpl; rewrite !shift_lt_in_ty_zero, H; reflexivity.
  - intros m T_B T_R b H c; simpl; rewrite !shift_lt_in_ty_zero, H; reflexivity.
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
  - intros scrut tag n_lt arity yes_body no_body Hs Hy Hn a b c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E n_beta Ts T_B T_R op_body body Hop Hb a b c; simpl; rewrite Hop, Hb; reflexivity.
  - intros t Ss arg Ht Ha a b c; simpl; rewrite Ht, Ha; reflexivity.
  - intros E m n_beta Ts T_R op_body Hop a b c; simpl; rewrite Hop; reflexivity.
  - intros m T_B T_R t H a b c; simpl; rewrite H; reflexivity.
  - intros m T_B T_R bdy H a b c; simpl; rewrite H; reflexivity.
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
  - intros scrut tag n_lt arity yes_body no_body Hs Hy Hn a b c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E n_beta Ts T_B T_R op_body body Hop Hb a b c; simpl.
    unfold shift_ty_list.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_ty (a + b) c) by (intro T; apply shift_ty_fuse).
    rewrite !shift_ty_fuse, Hop, Hb; reflexivity.
  - intros t Ss arg Ht Ha a b c; simpl.
    unfold shift_ty_list.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_ty (a + b) c) by (intro T; apply shift_ty_fuse).
    rewrite Ht, Ha; reflexivity.
  - intros E m n_beta Ts T_R op_body Hop a b c; simpl.
    unfold shift_ty_list.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_ty (a + b) c) by (intro T; apply shift_ty_fuse).
    rewrite shift_ty_fuse, Hop; reflexivity.
  - intros m T_B T_R t H a b c; simpl; rewrite !shift_ty_fuse, H; reflexivity.
  - intros m T_B T_R bdy H a b c; simpl; rewrite !shift_ty_fuse, H; reflexivity.
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
  - intros scrut tag n_lt arity yes_body no_body Hs Hy Hn a b c; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E n_beta Ts T_B T_R op_body body Hop Hb a b c; simpl.
    unfold shift_lt_in_ty_list.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_lt_in_ty (a + b) c) by (intro T; apply shift_lt_in_ty_fuse).
    rewrite !shift_lt_in_ty_fuse, Hop, Hb; reflexivity.
  - intros t Ss arg Ht Ha a b c; simpl.
    unfold shift_lt_in_ty_list.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_lt_in_ty (a + b) c) by (intro T; apply shift_lt_in_ty_fuse).
    rewrite Ht, Ha; reflexivity.
  - intros E m n_beta Ts T_R op_body Hop a b c; simpl.
    unfold shift_lt_in_ty_list.
    rewrite List.map_map.
    rewrite List.map_ext with (g := shift_lt_in_ty (a + b) c) by (intro T; apply shift_lt_in_ty_fuse).
    rewrite shift_lt_in_ty_fuse, Hop; reflexivity.
  - intros m T_B T_R t H a b c; simpl; rewrite !shift_lt_in_ty_fuse, H; reflexivity.
  - intros m T_B T_R bdy H a b c; simpl; rewrite !shift_lt_in_ty_fuse, H; reflexivity.
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
  - intros scrut tag n_lt arity yes_body no_body Hs Hy Hn a1 c1 a2 c2; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E n_beta Ts T_B T_R op_body body Hop Hb a1 c1 a2 c2; simpl; rewrite Hop, Hb; reflexivity.
  - intros t Ss arg Ht Ha a1 c1 a2 c2; simpl; rewrite Ht, Ha; reflexivity.
  - intros E m n_beta Ts T_R op_body Hop a1 c1 a2 c2; simpl; rewrite Hop; reflexivity.
  - intros m T_B T_R t H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros m T_B T_R bdy H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
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
  - intros scrut tag n_lt arity yes_body no_body Hs Hy Hn a1 c1 a2 c2; simpl;
    rewrite Hs, Hy, Hn; reflexivity.
  - intros E n_beta Ts T_B T_R op_body body Hop Hb a1 c1 a2 c2; simpl; rewrite Hop, Hb; reflexivity.
  - intros t Ss arg Ht Ha a1 c1 a2 c2; simpl; rewrite Ht, Ha; reflexivity.
  - intros E m n_beta Ts T_R op_body Hop a1 c1 a2 c2; simpl; rewrite Hop; reflexivity.
  - intros m T_B T_R t H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
  - intros m T_B T_R bdy H a1 c1 a2 c2; simpl; rewrite H; reflexivity.
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

Lemma lt_of_ty_ctx_ltall : forall f G A, lt_of_ty_ctx f G (type_lt_all A) = lt_local.
Proof. intros f G A. destruct f; reflexivity. Qed.

Lemma lt_of_ty_ctx_tyall : forall f G B A, lt_of_ty_ctx f G (type_ty_all B A) = lt_local.
Proof. intros f G B A. destruct f; reflexivity. Qed.

Lemma lt_of_ty_ctx_ctor : forall f G K l Ts,
  lt_of_ty_ctx f G (type_ctor K l Ts) = lt_min l (lt_of_ty_ctx_list f G Ts).
Proof.
  intros f G K l Ts. unfold lt_of_ty_ctx_list.
  destruct f as [|f']; simpl; f_equal;
    induction Ts as [|A rest IH]; simpl; try reflexivity; rewrite IH; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Unfolding equations for shifts on type constructors.                *)
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
           | T :: rest => lt_min (lt_of_ty_ctx 0 (bind_tm A :: G) T) (gol rest)
           end in gol Ts) =
        (let fix gol (Ts : list type) : lifetime :=
           match Ts with
           | [] => lt_free
           | T :: rest => lt_min (lt_of_ty_ctx 0 G T) (gol rest)
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
           | T :: rest => lt_min (lt_of_ty_ctx (S f) (bind_tm A :: G) T) (gol rest)
           end in gol Ts) =
        (let fix gol (Ts : list type) : lifetime :=
           match Ts with
           | [] => lt_free
           | T :: rest => lt_min (lt_of_ty_ctx (S f) G T) (gol rest)
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

Lemma shift_ty_lift_shift : forall a c T,
  shift_ty a 0 (shift_ty 1 c T) = shift_ty 1 (a + c) (shift_ty a 0 T).
Proof.
  induction a as [|a IH]; intros c T.
  - rewrite !shift_ty_zero. reflexivity.
  - replace (shift_ty (S a) 0 (shift_ty 1 c T))
      with (shift_ty 1 0 (shift_ty a 0 (shift_ty 1 c T))).
    2:{ rewrite shift_ty_fuse. replace (1 + a) with (S a) by lia. reflexivity. }
    rewrite IH.
    rewrite shift_ty_swap_0.
    replace (S (a + c)) with (S a + c) by lia.
    rewrite shift_ty_fuse. replace (1 + a) with (S a) by lia. reflexivity.
Qed.

Lemma shift_ty_ctor_sig_swap_0 : forall sig c,
  shift_ty_ctor_sig 1 0 (shift_ty_ctor_sig 1 c sig) =
  shift_ty_ctor_sig 1 (S c) (shift_ty_ctor_sig 1 0 sig).
Proof.
  intros [[[n_lt n_ty] fields] result] c. unfold shift_ty_ctor_sig. simpl.
  f_equal.
  - f_equal. rewrite !List.map_map. apply List.map_ext. intro T.
    replace (n_ty + 0) with n_ty by lia.
    replace (n_ty + S c) with (S (n_ty + c)) by lia.
    apply shift_ty_swap. lia.
  - replace (n_ty + 0) with n_ty by lia.
    replace (n_ty + S c) with (S (n_ty + c)) by lia.
    apply shift_ty_swap. lia.
Qed.

Lemma shift_ty_eff_sig_swap_0 : forall sig c,
  shift_ty_eff_sig 1 0 (shift_ty_eff_sig 1 c sig) =
  shift_ty_eff_sig 1 (S c) (shift_ty_eff_sig 1 0 sig).
Proof.
  intros [[[n_α n_β] sig_ty] ret_ty] c. unfold shift_ty_eff_sig. simpl.
  f_equal.
  - f_equal. replace (n_α + n_β + 0) with (n_α + n_β) by lia.
    replace (n_α + n_β + S c) with (S (n_α + n_β + c)) by lia.
    apply shift_ty_swap. lia.
  - replace (n_α + n_β + 0) with (n_α + n_β) by lia.
    replace (n_α + n_β + S c) with (S (n_α + n_β + c)) by lia.
    apply shift_ty_swap. lia.
Qed.

Lemma shift_ty_ctor_sig_shift_lt_comm : forall sig c,
  shift_lt_ctor_sig 1 0 (shift_ty_ctor_sig 1 c sig) =
  shift_ty_ctor_sig 1 c (shift_lt_ctor_sig 1 0 sig).
Proof.
  intros [[[n_lt n_ty] fields] result] c. unfold shift_lt_ctor_sig, shift_ty_ctor_sig. simpl.
  f_equal.
  - f_equal. rewrite !List.map_map. apply List.map_ext. intro T.
    symmetry. apply shift_ty_shift_lt_in_ty_commute.
  - symmetry. apply shift_ty_shift_lt_in_ty_commute.
Qed.

Lemma shift_ty_eff_sig_shift_lt_comm : forall sig c,
  shift_lt_eff_sig 1 0 (shift_ty_eff_sig 1 c sig) =
  shift_ty_eff_sig 1 c (shift_lt_eff_sig 1 0 sig).
Proof.
  intros [[[n_α n_β] sig_ty] ret_ty] c. unfold shift_lt_eff_sig, shift_ty_eff_sig. simpl.
  f_equal; [f_equal|]; symmetry; apply shift_ty_shift_lt_in_ty_commute.
Qed.

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
      (bind_ctor tg n1 n2 (List.map (shift_ty 1 (n2 + c)) Ts)
                (shift_ty 1 (n2 + c) Tr) :: G')
| InsTy_eff : forall c G G' eg m1 m2 Ts Tr,
    InsTy c G G' ->
    InsTy c (bind_eff eg m1 m2 Ts Tr :: G)
      (bind_eff eg m1 m2 (shift_ty 1 (m1 + m2 + c) Ts)
                (shift_ty 1 (m1 + m2 + c) Tr) :: G').

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

Lemma InsTy_lookup_tm : forall c G G', InsTy c G G' ->
  forall x, ctx_lookup_tm G' x = option_map (shift_ty 1 c) (ctx_lookup_tm G x).
Proof.
  intros c G G' H. induction H; intro x.
  - simpl ctx_lookup_tm. reflexivity.
  - simpl ctx_lookup_tm. rewrite IHInsTy.
    destruct (ctx_lookup_tm G x) as [T|]; simpl;
      [rewrite shift_ty_swap_0|]; reflexivity.
  - simpl ctx_lookup_tm. rewrite IHInsTy.
    destruct (ctx_lookup_tm G x) as [T|]; simpl;
      [rewrite shift_ty_shift_lt_in_ty_commute|]; reflexivity.
  - destruct x as [|x']; simpl ctx_lookup_tm.
    + reflexivity.
    + apply IHInsTy.
  - simpl ctx_lookup_tm. apply IHInsTy.
  - simpl ctx_lookup_tm. apply IHInsTy.
Qed.

Lemma InsTy_lookup_ctor : forall c G G', InsTy c G G' ->
  forall K, ctx_lookup_ctor G' K = option_map (shift_ty_ctor_sig 1 c) (ctx_lookup_ctor G K).
Proof.
  intros c G G' H. induction H; intro K.
  - simpl. reflexivity.
  - simpl. rewrite IHInsTy. destruct (ctx_lookup_ctor G K) as [sig|] eqn:E; cbn [option_map].
    + rewrite shift_ty_ctor_sig_swap_0. reflexivity.
    + reflexivity.
  - simpl. rewrite IHInsTy. destruct (ctx_lookup_ctor G K) as [sig|] eqn:E; cbn [option_map].
    + rewrite shift_ty_ctor_sig_shift_lt_comm. reflexivity.
    + reflexivity.
  - simpl. apply IHInsTy.
  - simpl. destruct (Nat.eqb K tg); [reflexivity|apply IHInsTy].
  - simpl. apply IHInsTy.
Qed.

Lemma InsTy_lookup_eff : forall c G G', InsTy c G G' ->
  forall E, ctx_lookup_eff G' E = option_map (shift_ty_eff_sig 1 c) (ctx_lookup_eff G E).
Proof.
  intros c G G' H. induction H; intro E.
  - simpl. reflexivity.
  - simpl. rewrite IHInsTy. destruct (ctx_lookup_eff G E) as [sig|] eqn:Ef; cbn [option_map].
    + rewrite shift_ty_eff_sig_swap_0. reflexivity.
    + reflexivity.
  - simpl. rewrite IHInsTy. destruct (ctx_lookup_eff G E) as [sig|] eqn:Ef; cbn [option_map].
    + rewrite shift_ty_eff_sig_shift_lt_comm. reflexivity.
    + reflexivity.
  - simpl. apply IHInsTy.
  - simpl. apply IHInsTy.
  - simpl. destruct (Nat.eqb E eg); [reflexivity|apply IHInsTy].
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

Lemma lt_wf_InsTy : forall G l,
  lt_wf G l -> forall c G', InsTy c G G' -> lt_wf G' l.
Proof.
  intros G l Hwf. induction Hwf; intros c G' HIns.
  - econstructor. rewrite (InsTy_lookup_lt c Γ G' HIns x). exact H.
  - constructor.
  - constructor.
  - constructor.
    + apply (IHHwf1 c G' HIns).
    + apply (IHHwf2 c G' HIns).
Qed.

Lemma lifetimes_wf_InsTy : forall G lts,
  lifetimes_wf G lts -> forall c G', InsTy c G G' -> lifetimes_wf G' lts.
Proof.
  intros G lts Hwf. induction Hwf; intros c G' HIns.
  - constructor.
  - constructor.
    + eapply lt_wf_InsTy; eauto.
    + apply (IHHwf c G' HIns).
Qed.

Lemma ty_wf_InsTy : forall G T,
  ty_wf G T -> forall c G', InsTy c G G' -> ty_wf G' (shift_ty 1 c T)
with types_wf_InsTy : forall G Ts,
  types_wf G Ts -> forall c G', InsTy c G G' -> types_wf G' (List.map (shift_ty 1 c) Ts).
Proof.
  - intros G T Hwf. induction Hwf; intros c G' HIns.
    + rewrite shv_shift. econstructor.
      * rewrite (InsTy_lookup_ty c Γ G' HIns α). rewrite H. reflexivity.
      * apply IHHwf. exact HIns.
    + rewrite shift_ty_fun_eq. constructor.
      * apply IHHwf1. exact HIns.
      * eapply lt_wf_InsTy; eauto.
      * apply IHHwf2. exact HIns.
    + rewrite shift_ty_ctor_eq. constructor.
      * eapply lt_wf_InsTy; eauto.
      * eapply types_wf_InsTy; eauto.
    + rewrite shift_ty_ltall_eq. constructor.
      apply IHHwf. apply InsTy_lt. exact HIns.
    + rewrite shift_ty_tyall_eq. constructor.
      * apply IHHwf1. exact HIns.
      * apply IHHwf2. apply InsTy_ty. exact HIns.
  - intros G Ts Hwf. induction Hwf; intros c G' HIns; cbn [List.map].
    + constructor.
    + constructor.
      * eapply ty_wf_InsTy; eauto.
      * auto.
Qed.

Lemma lt_sub_InsTy : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall c G', InsTy c G G' -> G' ⊢ₗ l1 <: l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l Hwf|Γ l Hwf|Γ x Δ Hlk Hwf|Γ l Hwf
                 |Γ l1 l2 l3 H1 IH1 H2 IH2|Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H1 IH1 Hwf2|Γ l l1 l2 H1 IH1 Hwf1];
    intros c G' HIns.
  - apply LS_Free. eapply lt_wf_InsTy; eauto.
  - apply LS_Local. eapply lt_wf_InsTy; eauto.
  - apply LS_Var.
    + rewrite (InsTy_lookup_lt c Γ G' HIns x). exact Hlk.
    + eapply lt_wf_InsTy; eauto.
  - apply LS_Refl. eapply lt_wf_InsTy; eauto.
  - eapply LS_Trans; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - apply LS_MinL; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - apply LS_MinR1.
    + apply (IH1 c G' HIns).
    + eapply lt_wf_InsTy; eauto.
  - apply LS_MinR2.
    + apply (IH1 c G' HIns).
    + eapply lt_wf_InsTy; eauto.
Qed.

Lemma sub_InsTy : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall c G', InsTy c G G' -> G' ⊢ shift_ty 1 c T1 <:: shift_ty 1 c T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T Hwf|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                 |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                 |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2];
    intros c G' HIns.
  - apply SA_Refl. eapply ty_wf_InsTy; eauto.
  - eapply SA_Trans; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - rewrite shv_shift. apply SA_VarCtx.
    + rewrite (InsTy_lookup_ty c Γ G' HIns α). rewrite Hlk. reflexivity.
    + eapply ty_wf_InsTy; eauto.
  - rewrite !shift_ty_ctor_eq. apply SA_Data.
    + apply (lt_sub_InsTy Γ l l' Hls c G' HIns).
    + eapply types_wf_InsTy; eauto.
  - rewrite shift_ty_ctor_eq. cbn [List.map]. apply SA_Any.
    + eapply ty_wf_InsTy; eauto.
    + eapply lt_wf_InsTy; eauto.
    + rewrite (lt_of_ty_G_InsTy c Γ G' HIns T).
      apply (lt_sub_InsTy Γ (lt_of_ty_G Γ T) Δ Hls c G' HIns).
  - rewrite !shift_ty_fun_eq. apply SA_Fun.
    + apply (IH1 c G' HIns).
    + apply (lt_sub_InsTy Γ l l' Hl c G' HIns).
    + apply (IH2 c G' HIns).
  - rewrite !shift_ty_ltall_eq. apply SA_LtAll.
    apply (IH1 c (bind_lt lt_local :: G') (InsTy_lt c Γ G' lt_local HIns)).
  - rewrite !shift_ty_tyall_eq. eapply SA_TyAll.
    + eapply ty_wf_InsTy; [exact HwfA|]. apply InsTy_ty. exact HIns.
    + eapply ty_wf_InsTy; [exact HwfA'|]. apply InsTy_ty. exact HIns.
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

Lemma shift_lt_ctor_sig_swap_0 : forall sig c,
  shift_lt_ctor_sig 1 0 (shift_lt_ctor_sig 1 c sig) =
  shift_lt_ctor_sig 1 (S c) (shift_lt_ctor_sig 1 0 sig).
Proof.
  intros [[[n_lt n_ty] fields] result] c. unfold shift_lt_ctor_sig. simpl.
  f_equal.
  - f_equal. rewrite !List.map_map. apply List.map_ext. intro T.
    replace (n_lt + 0) with n_lt by lia.
    replace (n_lt + S c) with (S (n_lt + c)) by lia.
    apply shift_lt_in_ty_swap. lia.
  - replace (n_lt + 0) with n_lt by lia.
    replace (n_lt + S c) with (S (n_lt + c)) by lia.
    apply shift_lt_in_ty_swap. lia.
Qed.

Lemma shift_lt_eff_sig_swap_0 : forall sig c,
  shift_lt_eff_sig 1 0 (shift_lt_eff_sig 1 c sig) =
  shift_lt_eff_sig 1 (S c) (shift_lt_eff_sig 1 0 sig).
Proof.
  intros [[[n_α n_β] sig_ty] ret_ty] c. unfold shift_lt_eff_sig. simpl.
  f_equal; [f_equal|]; apply shift_lt_in_ty_swap_0.
Qed.

Lemma shift_lt_ctor_sig_shift_ty_comm : forall sig c,
  shift_ty_ctor_sig 1 0 (shift_lt_ctor_sig 1 c sig) =
  shift_lt_ctor_sig 1 c (shift_ty_ctor_sig 1 0 sig).
Proof.
  intros [[[n_lt n_ty] fields] result] c. unfold shift_lt_ctor_sig, shift_ty_ctor_sig. simpl.
  f_equal.
  - f_equal. rewrite !List.map_map. apply List.map_ext. intro T.
    apply shift_ty_shift_lt_in_ty_commute.
  - apply shift_ty_shift_lt_in_ty_commute.
Qed.

Lemma shift_lt_eff_sig_shift_ty_comm : forall sig c,
  shift_ty_eff_sig 1 0 (shift_lt_eff_sig 1 c sig) =
  shift_lt_eff_sig 1 c (shift_ty_eff_sig 1 0 sig).
Proof.
  intros [[[n_α n_β] sig_ty] ret_ty] c. unfold shift_lt_eff_sig, shift_ty_eff_sig. simpl.
  f_equal; [f_equal|]; apply shift_ty_shift_lt_in_ty_commute.
Qed.

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
      (bind_ctor tg n1 n2 (List.map (shift_lt_in_ty 1 (n1 + c)) Ts)
                (shift_lt_in_ty 1 (n1 + c) Tr) :: G')
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

Lemma InsLt_lookup_tm : forall c G G', InsLt c G G' ->
  forall x, ctx_lookup_tm G' x = option_map (shift_lt_in_ty 1 c) (ctx_lookup_tm G x).
Proof.
  intros c G G' H. induction H; intro x.
  - simpl ctx_lookup_tm. reflexivity.
  - simpl ctx_lookup_tm. rewrite IHInsLt.
    destruct (ctx_lookup_tm G x) as [T|]; simpl;
      [rewrite shift_lt_in_ty_swap_0|]; reflexivity.
  - simpl ctx_lookup_tm. rewrite IHInsLt.
    destruct (ctx_lookup_tm G x) as [T|]; simpl;
      [rewrite shift_ty_shift_lt_in_ty_commute|]; reflexivity.
  - destruct x as [|x']; simpl ctx_lookup_tm.
    + reflexivity.
    + apply IHInsLt.
  - simpl ctx_lookup_tm. apply IHInsLt.
  - simpl ctx_lookup_tm. apply IHInsLt.
Qed.

Lemma InsLt_lookup_ctor : forall c G G', InsLt c G G' ->
  forall K, ctx_lookup_ctor G' K = option_map (shift_lt_ctor_sig 1 c) (ctx_lookup_ctor G K).
Proof.
  intros c G G' H. induction H; intro K.
  - simpl. reflexivity.
  - simpl. rewrite IHInsLt. destruct (ctx_lookup_ctor G K) as [sig|] eqn:E; cbn [option_map].
    + rewrite shift_lt_ctor_sig_swap_0. reflexivity.
    + reflexivity.
  - simpl. rewrite IHInsLt. destruct (ctx_lookup_ctor G K) as [sig|] eqn:E; cbn [option_map].
    + rewrite shift_lt_ctor_sig_shift_ty_comm. reflexivity.
    + reflexivity.
  - simpl. apply IHInsLt.
  - simpl. destruct (Nat.eqb K tg); [reflexivity|apply IHInsLt].
  - simpl. apply IHInsLt.
Qed.

Lemma InsLt_lookup_eff : forall c G G', InsLt c G G' ->
  forall E, ctx_lookup_eff G' E = option_map (shift_lt_eff_sig 1 c) (ctx_lookup_eff G E).
Proof.
  intros c G G' H. induction H; intro E.
  - simpl. reflexivity.
  - simpl. rewrite IHInsLt. destruct (ctx_lookup_eff G E) as [sig|] eqn:Ef; cbn [option_map].
    + rewrite shift_lt_eff_sig_swap_0. reflexivity.
    + reflexivity.
  - simpl. rewrite IHInsLt. destruct (ctx_lookup_eff G E) as [sig|] eqn:Ef; cbn [option_map].
    + rewrite shift_lt_eff_sig_shift_ty_comm. reflexivity.
    + reflexivity.
  - simpl. apply IHInsLt.
  - simpl. apply IHInsLt.
  - simpl. destruct (Nat.eqb E eg); [reflexivity|apply IHInsLt].
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

Lemma shift_lt_in_ty_ltall_eq : forall a c A,
  shift_lt_in_ty a c (type_lt_all A) = type_lt_all (shift_lt_in_ty a (S c) A).
Proof. reflexivity. Qed.
Lemma shift_lt_in_ty_tyall_eq : forall a c B A,
  shift_lt_in_ty a c (type_ty_all B A)
  = type_ty_all (shift_lt_in_ty a c B) (shift_lt_in_ty a c A).
Proof. reflexivity. Qed.

Lemma lt_wf_InsLt : forall G l,
  lt_wf G l -> forall c G', InsLt c G G' -> lt_wf G' (shift_lt 1 c l).
Proof.
  intros G l Hwf. induction Hwf; intros c G' HIns; simpl.
  - replace (if Nat.leb c x then x + 1 else x) with (shv c x)
      by (unfold shv; destruct (Nat.leb c x); [rewrite Nat.add_1_r|]; reflexivity).
    econstructor. rewrite (InsLt_lookup_lt c Γ G' HIns x). rewrite H. reflexivity.
  - constructor.
  - constructor.
  - constructor.
    + apply (IHHwf1 c G' HIns).
    + apply (IHHwf2 c G' HIns).
Qed.

Lemma lifetimes_wf_InsLt : forall G lts,
  lifetimes_wf G lts -> forall c G', InsLt c G G' ->
    lifetimes_wf G' (List.map (shift_lt 1 c) lts).
Proof.
  intros G lts Hwf. induction Hwf; intros c G' HIns; cbn [List.map].
  - constructor.
  - constructor.
    + eapply lt_wf_InsLt; eauto.
    + apply (IHHwf c G' HIns).
Qed.

Lemma ty_wf_InsLt : forall G T,
  ty_wf G T -> forall c G', InsLt c G G' -> ty_wf G' (shift_lt_in_ty 1 c T)
with types_wf_InsLt : forall G Ts,
  types_wf G Ts -> forall c G', InsLt c G G' -> types_wf G' (List.map (shift_lt_in_ty 1 c) Ts).
Proof.
  - intros G T Hwf. induction Hwf; intros c G' HIns.
    + simpl. econstructor.
      * rewrite (InsLt_lookup_ty c Γ G' HIns α). rewrite H. reflexivity.
      * apply IHHwf. exact HIns.
    + rewrite shift_lt_in_ty_fun_eq. constructor.
      * apply IHHwf1. exact HIns.
      * eapply lt_wf_InsLt; eauto.
      * apply IHHwf2. exact HIns.
    + rewrite shift_lt_in_ty_ctor_eq. constructor.
      * eapply lt_wf_InsLt; eauto.
      * eapply types_wf_InsLt; eauto.
    + rewrite shift_lt_in_ty_ltall_eq. constructor.
      apply IHHwf. apply InsLt_lt. exact HIns.
    + rewrite shift_lt_in_ty_tyall_eq. constructor.
      * apply IHHwf1. exact HIns.
      * apply IHHwf2. apply InsLt_ty. exact HIns.
  - intros G Ts Hwf. induction Hwf; intros c G' HIns; cbn [List.map].
    + constructor.
    + constructor.
      * eapply ty_wf_InsLt; eauto.
      * apply (IHHwf c G' HIns).
Qed.

Lemma lt_sub_InsLt : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall c G', InsLt c G G' -> G' ⊢ₗ shift_lt 1 c l1 <: shift_lt 1 c l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l Hwf|Γ l Hwf|Γ x Δ Hlk Hwf|Γ l Hwf
                 |Γ l1 l2 l3 H1 IH1 H2 IH2|Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H1 IH1 Hwf2|Γ l l1 l2 H1 IH1 Hwf1];
    intros c G' HIns; simpl.
  - apply LS_Free. eapply lt_wf_InsLt; eauto.
  - apply LS_Local. eapply lt_wf_InsLt; eauto.
  - replace (if Nat.leb c x then x + 1 else x) with (shv c x)
      by (unfold shv; destruct (Nat.leb c x); [rewrite Nat.add_1_r|]; reflexivity).
    apply LS_Var.
    + rewrite (InsLt_lookup_lt c Γ G' HIns x). rewrite Hlk. reflexivity.
    + eapply lt_wf_InsLt; eauto.
  - apply LS_Refl. eapply lt_wf_InsLt; eauto.
  - eapply LS_Trans; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - apply LS_MinL; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - apply LS_MinR1.
    + apply (IH1 c G' HIns).
    + eapply lt_wf_InsLt; eauto.
  - apply LS_MinR2.
    + apply (IH1 c G' HIns).
    + eapply lt_wf_InsLt; eauto.
Qed.

Lemma sub_InsLt : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall c G', InsLt c G G' -> G' ⊢ shift_lt_in_ty 1 c T1 <:: shift_lt_in_ty 1 c T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T Hwf|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                 |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                 |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2];
    intros c G' HIns.
  - apply SA_Refl. eapply ty_wf_InsLt; eauto.
  - eapply SA_Trans; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - simpl. apply SA_VarCtx.
    + rewrite (InsLt_lookup_ty c Γ G' HIns α). rewrite Hlk. reflexivity.
    + eapply ty_wf_InsLt; eauto.
  - rewrite !shift_lt_in_ty_ctor_eq. apply SA_Data.
    + apply (lt_sub_InsLt Γ l l' Hls c G' HIns).
    + eapply types_wf_InsLt; eauto.
  - rewrite shift_lt_in_ty_ctor_eq. cbn [List.map]. apply SA_Any.
    + eapply ty_wf_InsLt; eauto.
    + eapply lt_wf_InsLt; eauto.
    + rewrite (lt_of_ty_G_InsLt c Γ G' HIns T).
      apply (lt_sub_InsLt Γ (lt_of_ty_G Γ T) Δ Hls c G' HIns).
  - rewrite !shift_lt_in_ty_fun_eq. apply SA_Fun.
    + apply (IH1 c G' HIns).
    + apply (lt_sub_InsLt Γ l l' Hl c G' HIns).
    + apply (IH2 c G' HIns).
  - rewrite !shift_lt_in_ty_ltall_eq. apply SA_LtAll.
    apply (IH1 (S c) (bind_lt (shift_lt 1 c lt_local) :: G') (InsLt_lt c Γ G' lt_local HIns)).
  - rewrite !shift_lt_in_ty_tyall_eq. eapply SA_TyAll.
    + eapply ty_wf_InsLt; [exact HwfA|]. apply InsLt_ty. exact HIns.
    + eapply ty_wf_InsLt; [exact HwfA'|]. apply InsLt_ty. exact HIns.
    + apply (IH1 c G' HIns).
    + apply (IH2 c (bind_ty (shift_lt_in_ty 1 c B') :: G') (InsLt_ty c Γ G' B' HIns)).
Qed.

Lemma sub_weaken_lt_shift : forall Γ D T1 T2,
  Γ ⊢ T1 <:: T2 ->
  (bind_lt D :: Γ) ⊢ shift_lt_in_ty 1 0 T1 <:: shift_lt_in_ty 1 0 T2.
Proof.
  intros Γ D T1 T2 H. apply (sub_InsLt Γ T1 T2 H 0 (bind_lt D :: Γ)). apply InsLt_here.
Qed.

(* ===== InsTm: depth-general bind_tm weakening =================== *)

Inductive InsTm : ctx -> ctx -> Prop :=
| InsTm_here : forall A G, InsTm G (bind_tm A :: G)
| InsTm_tm : forall A G G',
    InsTm G G' -> InsTm (bind_tm A :: G) (bind_tm A :: G')
| InsTm_ty : forall B G G',
    InsTm G G' -> InsTm (bind_ty B :: G) (bind_ty B :: G')
| InsTm_lt : forall D G G',
    InsTm G G' -> InsTm (bind_lt D :: G) (bind_lt D :: G')
| InsTm_ctor : forall K n_lt n_ty f r G G',
    InsTm G G' -> InsTm (bind_ctor K n_lt n_ty f r :: G) (bind_ctor K n_lt n_ty f r :: G')
| InsTm_eff : forall E n_a n_b sig ret G G',
    InsTm G G' -> InsTm (bind_eff E n_a n_b sig ret :: G) (bind_eff E n_a n_b sig ret :: G').

Lemma InsTm_length : forall G G', InsTm G G' -> List.length G' = S (List.length G).
Proof. induction 1; simpl; lia. Qed.

Lemma InsTm_lookup_ty : forall G G', InsTm G G' ->
  forall a, ctx_lookup_ty G' a = ctx_lookup_ty G a.
Proof.
  intros G G' H. induction H; intro a; simpl; try apply IHInsTm.
  - reflexivity.
  - destruct a as [|a']; simpl.
    + reflexivity.
    + rewrite IHInsTm. reflexivity.
  - rewrite IHInsTm. reflexivity.
Qed.

Lemma InsTm_lookup_lt : forall G G', InsTm G G' ->
  forall x, ctx_lookup_lt G' x = ctx_lookup_lt G x.
Proof.
  intros G G' H. induction H; intro x; simpl; try apply IHInsTm.
  - reflexivity.
  - destruct x as [|x']; simpl.
    + reflexivity.
    + rewrite IHInsTm. reflexivity.
Qed.

Lemma InsTm_lookup_ctor : forall G G', InsTm G G' ->
  forall K, ctx_lookup_ctor G' K = ctx_lookup_ctor G K.
Proof.
  intros G G' H.
  induction H as [A G|A G G' H IH|B G G' H IH|D G G' H IH
                 |K0 n_lt n_ty f r G G' H IH|E n_a n_b sig ret G G' H IH];
    intro K; simpl.
  - reflexivity.
  - apply IH.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - destruct (Nat.eqb K K0); [reflexivity|apply IH].
  - apply IH.
Qed.

Lemma InsTm_lookup_eff : forall G G', InsTm G G' ->
  forall E, ctx_lookup_eff G' E = ctx_lookup_eff G E.
Proof.
  intros G G' H.
  induction H as [A G|A G G' H IH|B G G' H IH|D G G' H IH
                 |K n_lt n_ty f r G G' H IH|E0 n_a n_b sig ret G G' H IH];
    intro E; simpl.
  - reflexivity.
  - apply IH.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - apply IH.
  - destruct (Nat.eqb E E0); [reflexivity|apply IH].
Qed.

Lemma lt_of_ty_ctx_InsTm : forall G G', InsTm G G' ->
  forall f T, lt_of_ty_ctx f G' T = lt_of_ty_ctx f G T.
Proof.
  intros G G' HIns f. revert G G' HIns.
  induction f as [|f IH]; intros G G' HIns T.
  - destruct T; reflexivity.
  - revert G G' HIns. induction T using type_list_ind with
      (Q := fun Ts => forall G G', InsTm G G' ->
        lt_of_ty_ctx_list (S f) G' Ts = lt_of_ty_ctx_list (S f) G Ts);
      intros G G' HIns.
    + simpl. rewrite (InsTm_lookup_ty G G' HIns n).
      destruct (ctx_lookup_ty G n) as [B|] eqn:HB; [apply (IH G G' HIns B)|reflexivity].
    + reflexivity.
    + rewrite !lt_of_ty_ctx_ctor. f_equal. apply IHT. exact HIns.
    + reflexivity.
    + reflexivity.
    + rewrite !lt_of_ty_ctx_list_nil. reflexivity.
    + rewrite !lt_of_ty_ctx_list_cons.
      rewrite (IHT G G' HIns), (IHT0 G G' HIns). reflexivity.
Qed.

Lemma lt_of_ty_G_InsTm : forall G G', InsTm G G' ->
  forall T, lt_of_ty_G G' T = lt_of_ty_G G T.
Proof.
  intros G G' HIns T. unfold lt_of_ty_G.
  rewrite (lt_of_ty_ctx_InsTm G G' HIns (List.length G') T).
  rewrite (lt_of_ty_ctx_fuel_irrel (List.length G') (List.length G) T G 0 (VB_0 T));
    [reflexivity| |].
  - pose proof (InsTm_length G G' HIns). lia.
  - lia.
Qed.

Lemma lt_wf_InsTm : forall G l,
  lt_wf G l -> forall G', InsTm G G' -> lt_wf G' l.
Proof.
  intros G l Hwf. induction Hwf; intros G' HIns.
  - econstructor. rewrite (InsTm_lookup_lt Γ G' HIns x). exact H.
  - constructor.
  - constructor.
  - constructor.
    + apply (IHHwf1 G' HIns).
    + apply (IHHwf2 G' HIns).
Qed.

Lemma lifetimes_wf_InsTm : forall G lts,
  lifetimes_wf G lts -> forall G', InsTm G G' -> lifetimes_wf G' lts.
Proof.
  intros G lts Hwf. induction Hwf; intros G' HIns.
  - constructor.
  - constructor.
    + eapply lt_wf_InsTm; eauto.
    + apply (IHHwf G' HIns).
Qed.

Lemma ty_wf_InsTm : forall G T,
  ty_wf G T -> forall G', InsTm G G' -> ty_wf G' T
with types_wf_InsTm : forall G Ts,
  types_wf G Ts -> forall G', InsTm G G' -> types_wf G' Ts.
Proof.
  - intros G T Hwf. induction Hwf; intros G' HIns.
    + econstructor.
      * rewrite (InsTm_lookup_ty Γ G' HIns α). exact H.
      * apply IHHwf. exact HIns.
    + constructor.
      * apply IHHwf1. exact HIns.
      * eapply lt_wf_InsTm; eauto.
      * apply IHHwf2. exact HIns.
    + constructor.
      * eapply lt_wf_InsTm; eauto.
      * eapply types_wf_InsTm; eauto.
    + constructor. apply IHHwf. apply InsTm_lt. exact HIns.
    + constructor.
      * apply IHHwf1. exact HIns.
      * apply IHHwf2. apply InsTm_ty. exact HIns.
  - intros G Ts Hwf. induction Hwf; intros G' HIns.
    + constructor.
    + constructor.
      * eapply ty_wf_InsTm; eauto.
      * apply (IHHwf G' HIns).
Qed.

Lemma lt_sub_InsTm : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall G', InsTm G G' -> G' ⊢ₗ l1 <: l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l Hwf|Γ l Hwf|Γ x Δ Hlk Hwf|Γ l Hwf
                 |Γ l1 l2 l3 H12 IH12 H23 IH23
                 |Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H IH Hwf2|Γ l l1 l2 H IH Hwf1]; intros G' HIns.
  - apply LS_Free. eapply lt_wf_InsTm; eauto.
  - apply LS_Local. eapply lt_wf_InsTm; eauto.
  - apply LS_Var.
    + rewrite (InsTm_lookup_lt Γ G' HIns x). exact Hlk.
    + eapply lt_wf_InsTm; eauto.
  - apply LS_Refl. eapply lt_wf_InsTm; eauto.
  - eapply LS_Trans; [apply IH12 | apply IH23]; exact HIns.
  - apply LS_MinL; [apply IH1|apply IH2]; exact HIns.
  - apply LS_MinR1.
    + apply IH. exact HIns.
    + eapply lt_wf_InsTm; eauto.
  - apply LS_MinR2.
    + apply IH. exact HIns.
    + eapply lt_wf_InsTm; eauto.
Qed.

Lemma sub_InsTm : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall G', InsTm G G' -> G' ⊢ T1 <:: T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T Hwf|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                 |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                 |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H IH|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2]; intros G' HIns.
  - apply SA_Refl. eapply ty_wf_InsTm; eauto.
  - eapply SA_Trans; [apply IH1|apply IH2]; exact HIns.
  - apply SA_VarCtx.
    + rewrite (InsTm_lookup_ty Γ G' HIns α). exact Hlk.
    + eapply ty_wf_InsTm; eauto.
  - apply SA_Data.
    + eapply lt_sub_InsTm; eauto.
    + eapply types_wf_InsTm; eauto.
  - apply SA_Any.
    + eapply ty_wf_InsTm; eauto.
    + eapply lt_wf_InsTm; eauto.
    + rewrite lt_of_ty_G_InsTm with (G := Γ) (G' := G') by exact HIns.
      eapply lt_sub_InsTm; eauto.
  - apply SA_Fun; [apply IH1|eapply lt_sub_InsTm|apply IH2]; eauto.
  - apply SA_LtAll. apply IH. apply InsTm_lt. exact HIns.
  - eapply SA_TyAll.
    + eapply ty_wf_InsTm; [exact HwfA|]. apply InsTm_ty. exact HIns.
    + eapply ty_wf_InsTm; [exact HwfA'|]. apply InsTm_ty. exact HIns.
    + apply IH1. exact HIns.
    + apply IH2. apply InsTm_ty. exact HIns.
Qed.

Lemma lt_sub_wf : forall Γ l1 l2,
  Γ ⊢ₗ l1 <: l2 -> lt_wf Γ l1 /\ lt_wf Γ l2.
Proof.
  intros Γ l1 l2 H. induction H.
  - split; [constructor|exact H].
  - split; [exact H|constructor].
  - split; [econstructor; exact H|exact H0].
  - split; exact H.
  - destruct IHlt_sub1 as [Hwf1 _]. destruct IHlt_sub2 as [_ Hwf3].
    split; assumption.
  - destruct IHlt_sub1 as [Hwf1 Hwfl]. destruct IHlt_sub2 as [Hwf2 _].
    split; [constructor; assumption|exact Hwfl].
  - destruct IHlt_sub as [Hwfl Hwfl1]. split.
    + exact Hwfl.
    + constructor; assumption.
  - destruct IHlt_sub as [Hwfl Hwfl2]. split.
    + exact Hwfl.
    + constructor; assumption.
Qed.

Lemma sub_wf : forall Γ T1 T2,
  Γ ⊢ T1 <:: T2 -> ty_wf Γ T1 /\ ty_wf Γ T2.
Proof.
  intros Γ T1 T2 H.
  induction H as [Γ T Hwf
                 |Γ S U T HSU IHSU HUT IHUT
                 |Γ α B Hlk HwfB
                 |Γ K l l' Ts Hlt HwfTs
                 |Γ T Δ HwfT HwfD Hlt
                 |Γ A A' l l' B B' HA IHA Hl HB IHB
                 |Γ A A' HAA IHAA
                 |Γ B B' A A' HwfA HwfA' HB IHB HA IHA].
  - split; exact Hwf.
  - destruct IHSU as [HwfS _]. destruct IHUT as [_ HwfT]. split; assumption.
  - split.
    + econstructor; eauto.
    + exact HwfB.
  - destruct (lt_sub_wf _ _ _ Hlt) as [Hwfl Hwfl'].
    split; constructor; assumption.
  - split.
    + exact HwfT.
    + constructor; [exact HwfD|constructor].
  - destruct IHA as [HwfA HwfA'].
    destruct IHB as [HwfB HwfB'].
    destruct (lt_sub_wf _ _ _ Hl) as [Hwfl Hwfl'].
    split; constructor; assumption.
  - destruct IHAA as [HwfA HwfA'].
    split; constructor; assumption.
  - destruct IHB as [HwfB' HwfB].
    split; constructor; assumption.
Qed.

Inductive InsTmAt : nat -> ctx -> ctx -> Prop :=
| InsTmAt_here : forall A G, InsTmAt 0 G (bind_tm A :: G)
| InsTmAt_tm : forall c A G G',
    InsTmAt c G G' -> InsTmAt (S c) (bind_tm A :: G) (bind_tm A :: G')
| InsTmAt_ty : forall c B G G',
    InsTmAt c G G' -> InsTmAt c (bind_ty B :: G) (bind_ty B :: G')
| InsTmAt_lt : forall c D G G',
    InsTmAt c G G' -> InsTmAt c (bind_lt D :: G) (bind_lt D :: G')
| InsTmAt_ctor : forall c K n_lt n_ty f r G G',
    InsTmAt c G G' -> InsTmAt c (bind_ctor K n_lt n_ty f r :: G)
                              (bind_ctor K n_lt n_ty f r :: G')
| InsTmAt_eff : forall c E n_a n_b sig ret G G',
    InsTmAt c G G' -> InsTmAt c (bind_eff E n_a n_b sig ret :: G)
                              (bind_eff E n_a n_b sig ret :: G').

Lemma InsTmAt_to_InsTm : forall c G G', InsTmAt c G G' -> InsTm G G'.
Proof.
  intros c G G' H. induction H; constructor; exact IHInsTmAt.
Qed.

Lemma InsTmAt_lookup_tm : forall c G G', InsTmAt c G G' ->
  forall x, ctx_lookup_tm G' (shv c x) = ctx_lookup_tm G x.
Proof.
  intros c G G' H. induction H; intro x.
  - unfold shv. simpl Nat.leb. destruct x; reflexivity.
  - destruct x as [|x'].
    + unfold shv. simpl Nat.leb. reflexivity.
    + simpl ctx_lookup_tm. rewrite <- (IHInsTmAt x').
      unfold shv.
      destruct (Nat.leb c x') eqn:E.
      * apply Nat.leb_le in E.
        rewrite (proj2 (Nat.leb_le (S c) (S x'))) by lia. reflexivity.
      * apply Nat.leb_gt in E.
        rewrite (proj2 (Nat.leb_gt (S c) (S x'))) by lia. reflexivity.
  - simpl ctx_lookup_tm. rewrite IHInsTmAt. reflexivity.
  - simpl ctx_lookup_tm. rewrite IHInsTmAt. reflexivity.
  - simpl ctx_lookup_tm. apply IHInsTmAt.
  - simpl ctx_lookup_tm. apply IHInsTmAt.
Qed.

Lemma shift_tm_var_eq : forall a c n,
  shift_tm a c (term_var n) = term_var (if Nat.leb c n then n + a else n).
Proof. reflexivity. Qed.

Lemma typing_var_InsTmAt : forall c G G' x T,
  InsTmAt c G G' ->
  ctx_lookup_tm G x = Some T ->
  ty_wf G T ->
  G' ⊢ₜ shift_tm 1 c (term_var x) : T.
Proof.
  intros c G G' x T HIns Hlk Hwf.
  rewrite shift_tm_var_eq. rewrite Nat.add_1_r.
  apply T_Var.
  - change (ctx_lookup_tm G' (shv c x) = Some T).
    rewrite (InsTmAt_lookup_tm c G G' HIns x). exact Hlk.
  - eapply ty_wf_InsTm; [exact Hwf|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
Qed.

Lemma free_tm_vars_go_eq_concat : forall cutoff ts,
  (fix go ts := match ts with [] => [] | u :: rest => free_tm_vars cutoff u ++ go rest end) ts =
  List.concat (List.map (free_tm_vars cutoff) ts).
Proof.
  intros cutoff ts. induction ts as [|t ts IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma free_tm_vars_shift_ty_in_tm : forall t cutoff c,
  free_tm_vars cutoff (shift_ty_in_tm 1 c t) = free_tm_vars cutoff t.
Proof.
  apply (term_list_ind
    (fun t => forall cutoff c, free_tm_vars cutoff (shift_ty_in_tm 1 c t) = free_tm_vars cutoff t)
    (fun ts => forall cutoff c,
      List.concat (List.map (free_tm_vars cutoff) (List.map (shift_ty_in_tm 1 c) ts)) =
      List.concat (List.map (free_tm_vars cutoff) ts))).
  - reflexivity.
  - intros t1 t2 IH1 IH2 cutoff c. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH cutoff c. simpl. apply IH.
  - intros t T IH cutoff c. simpl. apply IH.
  - intros bound body IH cutoff c. simpl. apply IH.
  - intros t l IH cutoff c. simpl. apply IH.
  - intros body IH cutoff c. simpl. apply IH.
  - intros K l lts Ts ts IH cutoff c. simpl. rewrite shift_ty_in_tm_go_eq_map.
    rewrite !free_tm_vars_go_eq_concat. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn cutoff c. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff c. simpl. rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa cutoff c. simpl. rewrite IHt, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff c. simpl. apply IHop.
  - intros m T_B T_R t IH cutoff c. simpl. apply IH.
  - intros m T_B T_R b IH cutoff c. simpl. apply IH.
  - reflexivity.
  - intros t ts IHt IHts cutoff c. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma free_tm_vars_shift_lt_in_tm : forall t cutoff c,
  free_tm_vars cutoff (shift_lt_in_tm 1 c t) = free_tm_vars cutoff t.
Proof.
  apply (term_list_ind
    (fun t => forall cutoff c, free_tm_vars cutoff (shift_lt_in_tm 1 c t) = free_tm_vars cutoff t)
    (fun ts => forall cutoff c,
      List.concat (List.map (free_tm_vars cutoff) (List.map (shift_lt_in_tm 1 c) ts)) =
      List.concat (List.map (free_tm_vars cutoff) ts))).
  - reflexivity.
  - intros t1 t2 IH1 IH2 cutoff c. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH cutoff c. simpl. apply IH.
  - intros t T IH cutoff c. simpl. apply IH.
  - intros bound body IH cutoff c. simpl. apply IH.
  - intros t l IH cutoff c. simpl. apply IH.
  - intros body IH cutoff c. simpl. apply IH.
  - intros K l lts Ts ts IH cutoff c. simpl. rewrite shift_lt_in_tm_go_eq_map.
    rewrite !free_tm_vars_go_eq_concat. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn cutoff c. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff c. simpl. rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa cutoff c. simpl. rewrite IHt, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff c. simpl. apply IHop.
  - intros m T_B T_R t IH cutoff c. simpl. apply IH.
  - intros m T_B T_R b IH cutoff c. simpl. apply IH.
  - reflexivity.
  - intros t ts IHt IHts cutoff c. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma subst_lt_in_tm_go_eq_map : forall n R ts,
  (fix go ts := match ts with [] => [] | u :: rest => subst_lt_in_tm n R u :: go rest end) ts =
  List.map (subst_lt_in_tm n R) ts.
Proof.
  intros n R ts. induction ts as [|t ts IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma free_tm_vars_subst_lt_in_tm : forall t cutoff n R,
  free_tm_vars cutoff (subst_lt_in_tm n R t) = free_tm_vars cutoff t.
Proof.
  apply (term_list_ind
    (fun t => forall cutoff n R,
      free_tm_vars cutoff (subst_lt_in_tm n R t) = free_tm_vars cutoff t)
    (fun ts => forall cutoff n R,
      List.concat (List.map (free_tm_vars cutoff) (List.map (subst_lt_in_tm n R) ts)) =
      List.concat (List.map (free_tm_vars cutoff) ts))).
  - reflexivity.
  - intros t1 t2 IH1 IH2 cutoff n R. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH cutoff n R. simpl. apply IH.
  - intros t T IH cutoff n R. simpl. apply IH.
  - intros bound body IH cutoff n R. simpl. apply IH.
  - intros t l IH cutoff n R. simpl. apply IH.
  - intros body IH cutoff n R. simpl. apply IH.
  - intros K l lts Ts ts IH cutoff n R. simpl. rewrite subst_lt_in_tm_go_eq_map.
    rewrite !free_tm_vars_go_eq_concat. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn cutoff n R. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff n R. simpl. rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa cutoff n R. simpl. rewrite IHt, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff n R. simpl. apply IHop.
  - intros m T_B T_R t IH cutoff n R. simpl. apply IH.
  - intros m T_B T_R b IH cutoff n R. simpl. apply IH.
  - reflexivity.
  - intros t ts IHt IHts cutoff n R. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma no_local_lt_shift : forall l c,
  no_local_lt (shift_lt 1 c l) = no_local_lt l.
Proof.
  induction l as [n| | |l1 IH1 l2 IH2]; intro c; simpl; try reflexivity.
  rewrite IH1, IH2. reflexivity.
Qed.

Lemma no_local_ty_go_eq_fold : forall Ts,
  (fix go Ts := match Ts with [] => true | A :: rest => andb (no_local_ty A) (go rest) end) Ts =
  fold_right (fun A acc => andb (no_local_ty A) acc) true Ts.
Proof.
  induction Ts as [|A Ts IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma no_local_ty_shift_ty : forall T c,
  no_local_ty (shift_ty 1 c T) = no_local_ty T.
Proof.
  apply (type_list_ind
    (fun T => forall c, no_local_ty (shift_ty 1 c T) = no_local_ty T)
    (fun Ts => forall c,
      fold_right (fun A acc => andb (no_local_ty A) acc) true (List.map (shift_ty 1 c) Ts) =
      fold_right (fun A acc => andb (no_local_ty A) acc) true Ts)).
  - reflexivity.
  - intros A l B IHA IHB c. simpl. rewrite IHA, IHB. reflexivity.
  - intros K l Ts IHTs c. rewrite shift_ty_ctor_eq. simpl.
    rewrite !no_local_ty_go_eq_fold. rewrite IHTs. reflexivity.
  - intros A IHA c. simpl. apply IHA.
  - intros B A IHB IHA c. simpl. rewrite IHB, IHA. reflexivity.
  - reflexivity.
  - intros A Ts IHA IHTs c. simpl. rewrite IHA, IHTs. reflexivity.
Qed.

Lemma no_local_ty_shift_lt : forall T c,
  no_local_ty (shift_lt_in_ty 1 c T) = no_local_ty T.
Proof.
  apply (type_list_ind
    (fun T => forall c, no_local_ty (shift_lt_in_ty 1 c T) = no_local_ty T)
    (fun Ts => forall c,
      fold_right (fun A acc => andb (no_local_ty A) acc) true (List.map (shift_lt_in_ty 1 c) Ts) =
      fold_right (fun A acc => andb (no_local_ty A) acc) true Ts)).
  - reflexivity.
  - intros A l B IHA IHB c. simpl. rewrite IHA, IHB, no_local_lt_shift. reflexivity.
  - intros K l Ts IHTs c. rewrite shift_lt_in_ty_ctor_eq. simpl.
    rewrite no_local_lt_shift. rewrite !no_local_ty_go_eq_fold. rewrite IHTs. reflexivity.
  - intros A IHA c. simpl. apply IHA.
  - intros B A IHB IHA c. simpl. rewrite IHB, IHA. reflexivity.
  - reflexivity.
  - intros A Ts IHA IHTs c. simpl. rewrite IHA, IHTs. reflexivity.
Qed.

Lemma no_local_lt_subst_lt : forall l n R,
  no_local_lt l = true ->
  no_local_lt (subst_lt n R l) = true.
Proof.
  induction l as [x| | |l1 IH1 l2 IH2]; intros n R Hnl; simpl in *.
  - discriminate Hnl.
  - reflexivity.
  - discriminate Hnl.
  - apply andb_prop in Hnl. destruct Hnl as [H1 H2].
    rewrite (IH1 n R H1), (IH2 n R H2). reflexivity.
Qed.

Lemma no_local_ty_subst_lt : forall T n R,
  no_local_ty T = true ->
  no_local_ty (subst_lt_in_ty n R T) = true.
Proof.
  intros T. apply (type_list_ind
    (fun T => forall n R,
      no_local_ty T = true -> no_local_ty (subst_lt_in_ty n R T) = true)
    (fun Ts => forall n R,
      fold_right (fun A acc => andb (no_local_ty A) acc) true Ts = true ->
      fold_right (fun A acc => andb (no_local_ty A) acc) true
        (List.map (subst_lt_in_ty n R) Ts) = true)).
  - intros x n R Hnl. exact Hnl.
  - intros A l B HA HB n R Hnl. simpl in *.
    repeat rewrite Bool.andb_true_iff in Hnl.
    destruct Hnl as [HnlA [Hnll HnlB]].
    rewrite (HA n R HnlA), (HB n R HnlB), (no_local_lt_subst_lt l n R Hnll).
    reflexivity.
  - intros K l Ts HTs n R Hnl. rewrite subst_lt_in_ty_ctor_eq. simpl in *.
    rewrite !no_local_ty_go_eq_fold in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [Hnll HnlTs].
    rewrite (no_local_lt_subst_lt l n R Hnll), (HTs n R HnlTs). reflexivity.
  - intros A HA n R Hnl. simpl in *. apply HA. exact Hnl.
  - intros B A HB HA n R Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlB HnlA].
    rewrite (HB n R HnlB), (HA n R HnlA). reflexivity.
  - intros n R Hnl. reflexivity.
  - intros A Ts HA HTs n R Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlA HnlTs].
    rewrite (HA n R HnlA), (HTs n R HnlTs). reflexivity.
Qed.

Lemma free_tm_vars_shift_tm_1 : forall t cutoff c,
  free_tm_vars cutoff (shift_tm 1 (cutoff + c) t) =
  List.map (shv c) (free_tm_vars cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall cutoff c,
      free_tm_vars cutoff (shift_tm 1 (cutoff + c) t) =
      List.map (shv c) (free_tm_vars cutoff t))
    (fun ts => forall cutoff c,
      List.concat (List.map (free_tm_vars cutoff) (List.map (shift_tm 1 (cutoff + c)) ts)) =
      List.map (shv c) (List.concat (List.map (free_tm_vars cutoff) ts)))).
  - intros x cutoff c. simpl.
    destruct (Nat.ltb x cutoff) eqn:Ex0.
    + assert (Hlt : x < cutoff) by (apply Nat.ltb_lt; exact Ex0).
      rewrite (proj2 (Nat.leb_gt (cutoff + c) x)) by lia.
      rewrite Ex0. reflexivity.
    + assert (Hge0 : cutoff <= x) by (apply Nat.ltb_ge; exact Ex0).
      destruct (Nat.leb (cutoff + c) x) eqn:Ex.
      * apply Nat.leb_le in Ex. rewrite Nat.add_1_r.
        rewrite (proj2 (Nat.ltb_ge (S x) cutoff)) by lia.
        unfold shv. cbn [List.map]. destruct (Nat.leb c (x - cutoff)) eqn:Ec.
        -- f_equal. rewrite Nat.sub_succ_l by lia. reflexivity.
        -- apply Nat.leb_gt in Ec. lia.
      * apply Nat.leb_gt in Ex.
        unfold shv. cbn [List.map]. destruct (Nat.leb c (x - cutoff)) eqn:Ec.
        -- apply Nat.leb_le in Ec. lia.
        -- rewrite Ex0. reflexivity.
  - intros t1 t2 IH1 IH2 cutoff c. simpl. rewrite IH1, IH2. rewrite List.map_app. reflexivity.
  - intros body T IH cutoff c. simpl. replace (S (cutoff + c)) with (S cutoff + c) by lia. apply IH.
  - intros t T IH cutoff c. simpl. apply IH.
  - intros bound body IH cutoff c. simpl. apply IH.
  - intros t l IH cutoff c. simpl. apply IH.
  - intros body IH cutoff c. simpl. apply IH.
  - intros K l lts Ts ts IH cutoff c. simpl. rewrite shift_tm_go_eq_map.
    rewrite !free_tm_vars_go_eq_concat. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn cutoff c. simpl.
    rewrite IHs, IHn.
    replace (cutoff + c + arity) with (cutoff + arity + c) by lia.
    rewrite IHy. rewrite !List.map_app. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff c. simpl.
    replace (cutoff + c + 2) with (cutoff + 2 + c) by lia.
    rewrite IHop.
    replace (S (cutoff + c)) with (S cutoff + c) by lia.
    rewrite IHb. rewrite List.map_app. reflexivity.
  - intros t Ss arg IHt IHa cutoff c. simpl. rewrite IHt, IHa. rewrite List.map_app. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff c. simpl.
    replace (cutoff + c + 2) with (cutoff + 2 + c) by lia. apply IHop.
  - intros m T_B T_R t IH cutoff c. simpl. apply IH.
  - intros m T_B T_R b IH cutoff c. simpl. replace (S (cutoff + c)) with (S cutoff + c) by lia. apply IH.
  - intros cutoff c. reflexivity.
  - intros t ts IHt IHts cutoff c. simpl. rewrite IHt, IHts. rewrite List.map_app. reflexivity.
Qed.

Lemma has_rt_cap_shift_tm : forall t amount cutoff,
  has_rt_cap (shift_tm amount cutoff t) = has_rt_cap t.
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
      has_rt_cap (shift_tm amount cutoff t) = has_rt_cap t)
    (fun ts => forall amount cutoff,
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end)
        (List.map (shift_tm amount cutoff) ts) =
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts)).
  - reflexivity.
  - intros t1 t2 IH1 IH2 amount cutoff. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH amount cutoff. simpl. apply IH.
  - intros t T IH amount cutoff. simpl. apply IH.
  - intros bound body IH amount cutoff. simpl. apply IH.
  - intros t l IH amount cutoff. simpl. apply IH.
  - intros body IH amount cutoff. simpl. apply IH.
  - intros K l lts Ts ts IH amount cutoff. simpl. rewrite shift_tm_go_eq_map. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn amount cutoff. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb amount cutoff. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa amount cutoff. simpl. rewrite IHt, IHa. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros t ts IHt IHts amount cutoff. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma has_rt_cap_shift_ty_in_tm : forall t amount cutoff,
  has_rt_cap (shift_ty_in_tm amount cutoff t) = has_rt_cap t.
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
      has_rt_cap (shift_ty_in_tm amount cutoff t) = has_rt_cap t)
    (fun ts => forall amount cutoff,
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end)
        (List.map (shift_ty_in_tm amount cutoff) ts) =
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts)).
  - reflexivity.
  - intros t1 t2 IH1 IH2 amount cutoff. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH amount cutoff. simpl. apply IH.
  - intros t T IH amount cutoff. simpl. apply IH.
  - intros bound body IH amount cutoff. simpl. apply IH.
  - intros t l IH amount cutoff. simpl. apply IH.
  - intros body IH amount cutoff. simpl. apply IH.
  - intros K l lts Ts ts IH amount cutoff. simpl. rewrite shift_ty_in_tm_go_eq_map. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn amount cutoff. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb amount cutoff. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa amount cutoff. simpl. rewrite IHt, IHa. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros t ts IHt IHts amount cutoff. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma has_rt_cap_shift_lt_in_tm : forall t amount cutoff,
  has_rt_cap (shift_lt_in_tm amount cutoff t) = has_rt_cap t.
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
      has_rt_cap (shift_lt_in_tm amount cutoff t) = has_rt_cap t)
    (fun ts => forall amount cutoff,
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end)
        (List.map (shift_lt_in_tm amount cutoff) ts) =
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts)).
  - reflexivity.
  - intros t1 t2 IH1 IH2 amount cutoff. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH amount cutoff. simpl. apply IH.
  - intros t T IH amount cutoff. simpl. apply IH.
  - intros bound body IH amount cutoff. simpl. apply IH.
  - intros t l IH amount cutoff. simpl. apply IH.
  - intros body IH amount cutoff. simpl. apply IH.
  - intros K l lts Ts ts IH amount cutoff. simpl. rewrite shift_lt_in_tm_go_eq_map. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn amount cutoff. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb amount cutoff. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa amount cutoff. simpl. rewrite IHt, IHa. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros t ts IHt IHts amount cutoff. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma is_abs_shift_tm : forall t amount cutoff,
  is_abs (shift_tm amount cutoff t) = is_abs t.
Proof. destruct t; reflexivity. Qed.

Lemma is_abs_shift_ty_in_tm : forall t amount cutoff,
  is_abs (shift_ty_in_tm amount cutoff t) = is_abs t.
Proof. destruct t; reflexivity. Qed.

Lemma is_abs_shift_lt_in_tm : forall t amount cutoff,
  is_abs (shift_lt_in_tm amount cutoff t) = is_abs t.
Proof. destruct t; reflexivity. Qed.

Lemma is_abs_subst_ty_in_tm : forall t var replacement,
  is_abs (subst_ty_in_tm var replacement t) = is_abs t.
Proof. destruct t; reflexivity. Qed.

Lemma is_abs_subst_lt_in_tm : forall t var replacement,
  is_abs (subst_lt_in_tm var replacement t) = is_abs t.
Proof. destruct t; reflexivity. Qed.

Lemma has_rt_cap_subst_lt_in_tm : forall t var replacement,
  has_rt_cap (subst_lt_in_tm var replacement t) = has_rt_cap t.
Proof.
  apply (term_list_ind
    (fun t => forall var replacement,
      has_rt_cap (subst_lt_in_tm var replacement t) = has_rt_cap t)
    (fun ts => forall var replacement,
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end)
        (List.map (subst_lt_in_tm var replacement) ts) =
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts)).
  - reflexivity.
  - intros t1 t2 IH1 IH2 var replacement. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH var replacement. simpl. apply IH.
  - intros t T IH var replacement. simpl. apply IH.
  - intros bound body IH var replacement. simpl. apply IH.
  - intros t l IH var replacement. simpl. apply IH.
  - intros body IH var replacement. simpl. apply IH.
  - intros K l lts Ts ts IH var replacement. simpl. rewrite subst_lt_in_tm_go_eq_map. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn var replacement. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb var replacement. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa var replacement. simpl. rewrite IHt, IHa. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros t ts IHt IHts var replacement. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma capture_lt_InsTmAt : forall c G G', InsTmAt c G G' ->
  forall body, capture_lt G' (shift_tm 1 (S c) body) = capture_lt G body.
Proof.
  intros c G G' HIns body. unfold capture_lt.
  replace (S c) with (1 + c) by lia.
  rewrite has_rt_cap_shift_tm.
  destruct (has_rt_cap body) eqn:Hcap; [reflexivity|].
  rewrite free_tm_vars_shift_tm_1.
  induction (free_tm_vars 1 body) as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite (InsTmAt_lookup_tm c G G' HIns x).
    destruct (ctx_lookup_tm G x) as [T|] eqn:Hlk;
      [rewrite (lt_of_ty_G_InsTm G G' (InsTmAt_to_InsTm c G G' HIns) T)|];
      rewrite IH; reflexivity.
Qed.

Lemma capture_lt_InsTy : forall c G G', InsTy c G G' ->
  forall body, capture_lt G' (shift_ty_in_tm 1 c body) = capture_lt G body.
Proof.
  intros c G G' HIns body. unfold capture_lt.
  rewrite has_rt_cap_shift_ty_in_tm.
  destruct (has_rt_cap body) eqn:Hcap; [reflexivity|].
  rewrite free_tm_vars_shift_ty_in_tm.
  induction (free_tm_vars 1 body) as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite (InsTy_lookup_tm c G G' HIns x).
    destruct (ctx_lookup_tm G x) as [T|] eqn:Hlk; simpl.
    + rewrite (lt_of_ty_G_InsTy c G G' HIns T). rewrite IH. reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma capture_lt_InsLt : forall c G G', InsLt c G G' ->
  forall body, capture_lt G' (shift_lt_in_tm 1 c body) = shift_lt 1 c (capture_lt G body).
Proof.
  intros c G G' HIns body. unfold capture_lt.
  rewrite has_rt_cap_shift_lt_in_tm.
  destruct (has_rt_cap body) eqn:Hcap; [reflexivity|].
  rewrite free_tm_vars_shift_lt_in_tm.
  induction (free_tm_vars 1 body) as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite (InsLt_lookup_tm c G G' HIns x).
    destruct (ctx_lookup_tm G x) as [T|] eqn:Hlk; simpl.
    + rewrite (lt_of_ty_G_InsLt c G G' HIns T). rewrite IH. reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma typing_ind_forall2 :
  forall (P : ctx -> term -> type -> Prop),
  (forall Γ x T, ctx_lookup_tm Γ x = Some T -> ty_wf Γ T -> P Γ (term_var x) T) ->
  (forall Γ t T U, Γ ⊢ₜ t : T -> P Γ t T -> Γ ⊢ T <:: U -> P Γ t U) ->
  (forall Γ body A l B,
      ty_wf Γ A ->
      ty_wf Γ B ->
     (bind_tm A :: Γ) ⊢ₜ body : B -> P (bind_tm A :: Γ) body B ->
      Γ ⊢ₗ capture_lt Γ body <: l ->
     P Γ (term_lam body A) (type_fun A l B)) ->
  (forall Γ t1 t2 A l B,
     Γ ⊢ₜ t1 : type_fun A l B -> P Γ t1 (type_fun A l B) ->
     Γ ⊢ₜ t2 : A -> P Γ t2 A ->
     P Γ (term_app t1 t2) B) ->
  (forall Γ bound body T,
      ty_wf Γ bound ->
      ty_wf (bind_ty bound :: Γ) T ->
      is_abs body = true ->
     (bind_ty bound :: Γ) ⊢ₜ body : T -> P (bind_ty bound :: Γ) body T ->
     P Γ (term_ty_lam bound body) (type_ty_all bound T)) ->
  (forall Γ t B U S,
     Γ ⊢ₜ t : type_ty_all B U -> P Γ t (type_ty_all B U) ->
      ty_wf Γ S ->
     Γ ⊢ S <:: B ->
      ty_app_arg_no_local Γ B S = true ->
     P Γ (term_ty_app t S) (subst_ty 0 S U)) ->
  (forall Γ body T,
      ty_wf (bind_lt lt_local :: Γ) T ->
      is_abs body = true ->
     (bind_lt lt_local :: Γ) ⊢ₜ body : T -> P (bind_lt lt_local :: Γ) body T ->
     P Γ (term_lt_lam body) (type_lt_all T)) ->
  (forall Γ t T l,
     Γ ⊢ₜ t : type_lt_all T -> P Γ t (type_lt_all T) ->
      lt_wf Γ l ->
     P Γ (term_lt_app t l) (subst_lt_in_ty 0 l T)) ->
        (forall Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
          result_ty result_tag l vs,
     ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) ->
     ctx_lookup_eff Γ K = None ->
     List.length lts = n_lt ->
    lifetimes_wf Γ lts ->
     rho_fields = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields ->
     List.length Ts = n_ty ->
    types_wf Γ Ts ->
      result_ty = inst_ctor_type n_lt n_ty lts Ts result_ty_schema ->
      result_ty = type_ctor result_tag l Ts ->
      ctx_lookup_eff Γ result_tag = None ->
     lt_wf Γ l ->
      Γ ⊢ₗ lt_of_ty_list rho_fields <: l ->
      Forall (fun l0 => Γ ⊢ₗ l0 <: l) lts ->
     List.length vs = List.length rho_fields ->
     Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rho_fields ->
     Forall2 (fun v rho => P Γ v rho) vs rho_fields ->
      P Γ (term_ctor K l lts Ts vs) result_ty) ->
      (forall Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
        rho_fields scrut_result_ty result_tag result_l
         Γ' yes_body eta elim_result no_body,
     K <> any_tag ->
     ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) ->
     ctx_lookup_eff Γ K = None ->
     lts = lt_var_list n_lt ->
     rho_fields = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields ->
      List.length Ts = n_ty ->
      types_wf Γ Ts ->
         scrut_result_ty = inst_ctor_type n_lt n_ty (List.repeat Delta n_lt) Ts result_ty_schema ->
        scrut_result_ty = type_ctor result_tag result_l Ts ->
      ctx_lookup_eff Γ result_tag = None ->
      result_tag <> any_tag ->
        lt_wf Γ Delta ->
         Γ ⊢ₗ result_l <: Delta ->
        Γ ⊢ₜ scrut : type_ctor result_tag Delta Ts ->
        P Γ scrut (type_ctor result_tag Delta Ts) ->
     arity = List.length rho_fields ->
     Γ' = push_lt_vars n_lt Delta Γ ->
     (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ' rho_fields) ⊢ₜ yes_body : eta ->
     P (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ' rho_fields) yes_body eta ->
     elim_ty_n n_lt (shift_lt n_lt 0 Delta) var_pos eta = Some elim_result ->
     Γ ⊢ₜ no_body : elim_result -> P Γ no_body elim_result ->
    P Γ (term_match scrut K n_lt arity yes_body no_body) elim_result) ->
  (forall Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β,
     ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
     List.length Ts = n_α ->
    types_wf Γ Ts ->
    ty_wf Γ T_R ->
      sig_β = inst_op_alpha n_α Ts n_β sig ->
      ret_β = inst_op_alpha n_α Ts n_β ret ->
     (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) ⊢ₜ op_body : shift_ty n_β 0 T_R ->
     P (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) op_body (shift_ty n_β 0 T_R) ->
    P Γ (term_cap E_tag m n_β Ts T_R op_body) (type_ctor E_tag lt_local Ts)) ->
  (forall Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β,
     ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
     List.length Ts = n_α ->
    types_wf Γ Ts ->
    ty_wf Γ T_B ->
    ty_wf Γ T_R ->
    no_local_ty_G Γ T_B = true ->
    Γ ⊢ T_B <:: T_R ->
      sig_β = inst_op_alpha n_α Ts n_β sig ->
      ret_β = inst_op_alpha n_α Ts n_β ret ->
     (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) ⊢ₜ op_body : shift_ty n_β 0 T_R ->
     P (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) op_body (shift_ty n_β 0 T_R) ->
      (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) ⊢ₜ body : T_B ->
      P (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) body T_B ->
     P Γ (term_handle E_tag n_β Ts T_B T_R op_body body) T_R) ->
  (forall Γ recv arg E_tag Delta Ts Ss n_α n_β sig ret sig_inst ret_inst,
     Γ ⊢ₜ recv : type_ctor E_tag Delta Ts -> P Γ recv (type_ctor E_tag Delta Ts) ->
     ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
     List.length Ts = n_α ->
     List.length Ss = n_β ->
    types_wf Γ Ss ->
    forallb (no_local_ty_G Γ) Ss = true ->
     sig_inst = inst_op_arg n_α Ts n_β Ss sig ->
      no_local_ty_G Γ sig_inst = true ->
     ret_inst = inst_op_arg n_α Ts n_β Ss ret ->
    ty_wf Γ ret_inst ->
     Γ ⊢ₜ arg : sig_inst -> P Γ arg sig_inst ->
     P Γ (term_perform recv Ss arg) ret_inst) ->
  (forall Γ m T_B T_R t,
      ty_wf Γ T_B ->
      ty_wf Γ T_R ->
      no_local_ty_G Γ T_B = true ->
      Γ ⊢ T_B <:: T_R ->
      Γ ⊢ₜ t : T_B -> P Γ t T_B ->
      P Γ (term_handler_m m T_B T_R t) T_R) ->
  (forall Γ m b A T_B T_R,
      ty_wf Γ A ->
      ty_wf Γ T_B ->
      ty_wf Γ T_R ->
      no_local_ty_G Γ T_B = true ->
      Γ ⊢ T_B <:: T_R ->
     (bind_tm A :: Γ) ⊢ₜ b : T_B -> P (bind_tm A :: Γ) b T_B ->
    P Γ (term_resume m T_B T_R b) (type_fun A lt_local T_R)) ->
  forall Γ t T, Γ ⊢ₜ t : T -> P Γ t T.
Proof.
  intros P HVar HSub HLam HApp HTyLam HTyApp HLtLam HLtApp HCtor HMatch
         HCap HHandle HPerform HHandlerM HResume.
  fix IH 4.
  intros Γ t T H. destruct H.
  - eapply HVar; (eassumption || (apply IH; eassumption)).
  - eapply HSub; (eassumption || (apply IH; eassumption)).
  - eapply HLam; (eassumption || (apply IH; eassumption)).
  - eapply HApp; (eassumption || (apply IH; eassumption)).
  - eapply HTyLam; (eassumption || (apply IH; eassumption)).
  - eapply HTyApp; (eassumption || (apply IH; eassumption)).
  - eapply HLtLam; (eassumption || (apply IH; eassumption)).
  - eapply HLtApp; (eassumption || (apply IH; eassumption)).
  - eapply HCtor; try (eassumption || (apply IH; eassumption)).
    match goal with
    | HF : Forall2 (fun v rho => _ ⊢ₜ v : rho) ?vs ?rf |- Forall2 _ ?vs ?rf =>
        clear -IH HF; induction HF
    end.
    + constructor.
    + constructor; [apply IH; assumption | assumption].
  - eapply HMatch; (eassumption || (apply IH; eassumption)).
  - eapply HCap; (eassumption || (apply IH; eassumption)).
  - eapply HHandle; (eassumption || (apply IH; eassumption)).
  - eapply HPerform; (eassumption || (apply IH; eassumption)).
  - eapply HHandlerM; (eassumption || (apply IH; eassumption)).
  - eapply HResume; (eassumption || (apply IH; eassumption)).
Qed.

Lemma InsTmAt_push_lt_vars : forall n Delta c G G',
  InsTmAt c G G' -> InsTmAt c (push_lt_vars n Delta G) (push_lt_vars n Delta G').
Proof.
  induction n as [|n IH]; intros Delta c G G' H; simpl.
  - exact H.
  - apply IH. apply InsTmAt_lt. exact H.
Qed.

Lemma InsTmAt_push_ty_vars : forall n B c G G',
  InsTmAt c G G' -> InsTmAt c (push_ty_vars n B G) (push_ty_vars n B G').
Proof.
  induction n as [|n IH]; intros B c G G' H; simpl.
  - exact H.
  - apply IH. apply InsTmAt_ty. exact H.
Qed.

Lemma InsTy_push_lt_vars : forall n Delta c G G',
  InsTy c G G' -> InsTy c (push_lt_vars n Delta G) (push_lt_vars n Delta G').
Proof.
  induction n as [|n IH]; intros Delta c G G' H; simpl.
  - exact H.
  - apply IH. apply InsTy_lt. exact H.
Qed.

(* ================================================================== *)
(* Stability of the context-sensitive no-local checks under weakening  *)
(*                                                                    *)
(* The new typing premises ([no_local_ty_G], [ty_app_arg_no_local],   *)
(* [forallb no_local_ty_G ...]) read the bound of each type variable  *)
(* from the context, so weakening lemmas must show they are preserved *)
(* when a binder is inserted ([InsTm]/[InsTy]/[InsLt]).  The two      *)
(* [is_any_at_free_bound_shift_*] lemmas establish that shifting an    *)
(* inserted bound does not change whether it is [Any]'free, and        *)
(* [no_local_ty_G_go_eq_fold] re-exposes the inner [go] fixpoint as a  *)
(* [fold_right] so it can be reasoned about by [Forall]/induction.     *)
(* ================================================================== *)

Lemma shift_ty_any_at_free : forall c, shift_ty 1 c any_at_free = any_at_free.
Proof. intros c. reflexivity. Qed.

Lemma shift_lt_any_at_free : forall c, shift_lt_in_ty 1 c any_at_free = any_at_free.
Proof. intros c. reflexivity. Qed.

Lemma is_any_at_free_bound_shift_ty : forall T c,
  is_any_at_free_bound (shift_ty 1 c T) = is_any_at_free_bound T.
Proof.
  destruct T as [n|A l B|K l Ts|A|B A]; intros c; simpl; try reflexivity.
  destruct l; destruct Ts; reflexivity.
Qed.

Lemma is_any_at_free_bound_shift_lt : forall T c,
  is_any_at_free_bound (shift_lt_in_ty 1 c T) = is_any_at_free_bound T.
Proof.
  destruct T as [n|A l B|K l Ts|A|B A]; intros c; simpl; try reflexivity.
  destruct l; destruct Ts; reflexivity.
Qed.

Lemma no_local_ty_G_go_eq_fold : forall Γ Ts,
  (fix go (Γ0 : ctx) (Ts0 : list type) {struct Ts0} : bool :=
     match Ts0 with
     | [] => true
     | A :: rest => andb (no_local_ty_G Γ0 A) (go Γ0 rest)
     end) Γ Ts =
  fold_right (fun A acc => andb (no_local_ty_G Γ A) acc) true Ts.
Proof.
  intros Gamma Ts. induction Ts as [|A Ts IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma no_local_ty_G_InsTm : forall Γ T G',
  InsTm Γ G' ->
  no_local_ty_G Γ T = true ->
  no_local_ty_G G' T = true.
Proof.
  intros Γ T. revert Γ.
  apply (type_list_ind
    (fun T => forall Γ G', InsTm Γ G' ->
      no_local_ty_G Γ T = true -> no_local_ty_G G' T = true)
    (fun Ts => forall Γ G', InsTm Γ G' ->
      fold_right (fun A acc => andb (no_local_ty_G Γ A) acc) true Ts = true ->
      fold_right (fun A acc => andb (no_local_ty_G G' A) acc) true Ts = true)).
  - intros x Γ G' HIns Hnl. simpl in *. rewrite (InsTm_lookup_ty Γ G' HIns x). exact Hnl.
  - intros A l B IHA IHB Γ G' HIns Hnl. simpl in *.
    repeat rewrite Bool.andb_true_iff in Hnl.
    destruct Hnl as [HnlA [Hnll HnlB]].
    rewrite (IHA Γ G' HIns HnlA), (IHB Γ G' HIns HnlB), Hnll. reflexivity.
  - intros K l Ts IHTs Γ G' HIns Hnl. simpl in *.
    rewrite !no_local_ty_G_go_eq_fold in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [Hnll HnlTs].
    rewrite Hnll, (IHTs Γ G' HIns HnlTs). reflexivity.
  - intros A IHA Γ G' HIns Hnl. simpl in *.
    apply IHA with (Γ := bind_lt lt_local :: Γ).
    + apply InsTm_lt. exact HIns.
    + exact Hnl.
  - intros B A IHB IHA Γ G' HIns Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlB HnlA].
    rewrite (IHB Γ G' HIns HnlB).
    rewrite (IHA (bind_ty B :: Γ) (bind_ty B :: G') (InsTm_ty B Γ G' HIns) HnlA).
    reflexivity.
  - intros Γ G' HIns Hnl. reflexivity.
  - intros A Ts IHA IHTs Γ G' HIns Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlA HnlTs].
    rewrite (IHA Γ G' HIns HnlA), (IHTs Γ G' HIns HnlTs). reflexivity.
Qed.

Lemma no_local_ty_G_InsTy : forall Γ T c G',
  InsTy c Γ G' ->
  no_local_ty_G Γ T = true ->
  no_local_ty_G G' (shift_ty 1 c T) = true.
Proof.
  intros Γ T. revert Γ.
  apply (type_list_ind
    (fun T => forall Γ c G', InsTy c Γ G' ->
      no_local_ty_G Γ T = true -> no_local_ty_G G' (shift_ty 1 c T) = true)
    (fun Ts => forall Γ c G', InsTy c Γ G' ->
      fold_right (fun A acc => andb (no_local_ty_G Γ A) acc) true Ts = true ->
      fold_right (fun A acc => andb (no_local_ty_G G' A) acc) true (List.map (shift_ty 1 c) Ts) = true)).
  - intros x Γ c G' HIns Hnl. simpl in *.
    replace (if c <=? x then x + 1 else x) with (shv c x) by (unfold shv; destruct (c <=? x); lia).
    rewrite (InsTy_lookup_ty c Γ G' HIns x).
    destruct (ctx_lookup_ty Γ x) as [B|] eqn:HB; simpl in *; [|discriminate].
    rewrite is_any_at_free_bound_shift_ty. exact Hnl.
  - intros A l B IHA IHB Γ c G' HIns Hnl. simpl in *.
    repeat rewrite Bool.andb_true_iff in Hnl.
    destruct Hnl as [HnlA [Hnll HnlB]].
    rewrite (IHA Γ c G' HIns HnlA), (IHB Γ c G' HIns HnlB), Hnll. reflexivity.
  - intros K l Ts IHTs Γ c G' HIns Hnl. rewrite shift_ty_ctor_eq. simpl in *.
    rewrite !no_local_ty_G_go_eq_fold in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [Hnll HnlTs].
    rewrite Hnll, (IHTs Γ c G' HIns HnlTs). reflexivity.
  - intros A IHA Γ c G' HIns Hnl. simpl in *.
    apply IHA with (Γ := bind_lt lt_local :: Γ).
    + apply InsTy_lt. exact HIns.
    + exact Hnl.
  - intros B A IHB IHA Γ c G' HIns Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlB HnlA].
    rewrite (IHB Γ c G' HIns HnlB).
    rewrite (IHA (bind_ty B :: Γ) (S c) (bind_ty (shift_ty 1 c B) :: G')
              (InsTy_ty c Γ G' B HIns) HnlA).
    reflexivity.
  - intros Γ c G' HIns Hnl. reflexivity.
  - intros A Ts IHA IHTs Γ c G' HIns Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlA HnlTs].
    rewrite (IHA Γ c G' HIns HnlA), (IHTs Γ c G' HIns HnlTs). reflexivity.
Qed.

Lemma no_local_ty_G_InsLt : forall Γ T c G',
  InsLt c Γ G' ->
  no_local_ty_G Γ T = true ->
  no_local_ty_G G' (shift_lt_in_ty 1 c T) = true.
Proof.
  intros Γ T. revert Γ.
  apply (type_list_ind
    (fun T => forall Γ c G', InsLt c Γ G' ->
      no_local_ty_G Γ T = true -> no_local_ty_G G' (shift_lt_in_ty 1 c T) = true)
    (fun Ts => forall Γ c G', InsLt c Γ G' ->
      fold_right (fun A acc => andb (no_local_ty_G Γ A) acc) true Ts = true ->
      fold_right (fun A acc => andb (no_local_ty_G G' A) acc) true (List.map (shift_lt_in_ty 1 c) Ts) = true)).
  - intros x Γ c G' HIns Hnl. simpl in *.
    rewrite (InsLt_lookup_ty c Γ G' HIns x).
    destruct (ctx_lookup_ty Γ x) as [B|] eqn:HB; simpl in *; [|discriminate].
    rewrite is_any_at_free_bound_shift_lt. exact Hnl.
  - intros A l B IHA IHB Γ c G' HIns Hnl. simpl in *.
    repeat rewrite Bool.andb_true_iff in Hnl.
    destruct Hnl as [HnlA [Hnll HnlB]].
    rewrite (IHA Γ c G' HIns HnlA), (IHB Γ c G' HIns HnlB).
    rewrite no_local_lt_shift, Hnll. reflexivity.
  - intros K l Ts IHTs Γ c G' HIns Hnl. rewrite shift_lt_in_ty_ctor_eq. simpl in *.
    rewrite !no_local_ty_G_go_eq_fold in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [Hnll HnlTs].
    rewrite no_local_lt_shift, Hnll, (IHTs Γ c G' HIns HnlTs). reflexivity.
  - intros A IHA Γ c G' HIns Hnl. simpl in *.
    apply IHA with (Γ := bind_lt lt_local :: Γ).
    + apply InsLt_lt. exact HIns.
    + exact Hnl.
  - intros B A IHB IHA Γ c G' HIns Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlB HnlA].
    rewrite (IHB Γ c G' HIns HnlB).
    rewrite (IHA (bind_ty B :: Γ) c (bind_ty (shift_lt_in_ty 1 c B) :: G')
              (InsLt_ty c Γ G' B HIns) HnlA).
    reflexivity.
  - intros Γ c G' HIns Hnl. reflexivity.
  - intros A Ts IHA IHTs Γ c G' HIns Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlA HnlTs].
    rewrite (IHA Γ c G' HIns HnlA), (IHTs Γ c G' HIns HnlTs). reflexivity.
Qed.

Lemma ty_app_arg_no_local_InsTm : forall Γ B S G',
  InsTm Γ G' ->
  ty_app_arg_no_local Γ B S = true ->
  ty_app_arg_no_local G' B S = true.
Proof.
  intros Γ B S G' HIns Hnl. unfold ty_app_arg_no_local in *.
  destruct (is_any_at_free_bound B) eqn:HB; [|exact Hnl].
  eapply no_local_ty_G_InsTm; eauto.
Qed.

Lemma ty_app_arg_no_local_InsTy : forall Γ B S c G',
  InsTy c Γ G' ->
  ty_app_arg_no_local Γ B S = true ->
  ty_app_arg_no_local G' (shift_ty 1 c B) (shift_ty 1 c S) = true.
Proof.
  intros Γ B S c G' HIns Hnl. unfold ty_app_arg_no_local in *.
  rewrite is_any_at_free_bound_shift_ty.
  destruct (is_any_at_free_bound B) eqn:HB; [|exact Hnl].
  eapply no_local_ty_G_InsTy; eauto.
Qed.

Lemma ty_app_arg_no_local_InsLt : forall Γ B S c G',
  InsLt c Γ G' ->
  ty_app_arg_no_local Γ B S = true ->
  ty_app_arg_no_local G' (shift_lt_in_ty 1 c B) (shift_lt_in_ty 1 c S) = true.
Proof.
  intros Γ B S c G' HIns Hnl. unfold ty_app_arg_no_local in *.
  rewrite is_any_at_free_bound_shift_lt.
  destruct (is_any_at_free_bound B) eqn:HB; [|exact Hnl].
  eapply no_local_ty_G_InsLt; eauto.
Qed.

Lemma forallb_no_local_ty_G_InsTm : forall Γ Ss G',
  InsTm Γ G' ->
  forallb (no_local_ty_G Γ) Ss = true ->
  forallb (no_local_ty_G G') Ss = true.
Proof.
  intros Gamma Ss. induction Ss as [|S Ss IH]; intros G' HIns Hnl; simpl in *; [reflexivity|].
  apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlS HnlSs].
  rewrite (no_local_ty_G_InsTm Gamma S G' HIns HnlS), (IH G' HIns HnlSs). reflexivity.
Qed.

Lemma forallb_no_local_ty_G_InsTy : forall Γ Ss c G',
  InsTy c Γ G' ->
  forallb (no_local_ty_G Γ) Ss = true ->
  forallb (no_local_ty_G G') (List.map (shift_ty 1 c) Ss) = true.
Proof.
  intros Gamma Ss. induction Ss as [|S Ss IH]; intros c G' HIns Hnl; simpl in *; [reflexivity|].
  apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlS HnlSs].
  rewrite (no_local_ty_G_InsTy Gamma S c G' HIns HnlS), (IH c G' HIns HnlSs). reflexivity.
Qed.

Lemma forallb_no_local_ty_G_InsLt : forall Γ Ss c G',
  InsLt c Γ G' ->
  forallb (no_local_ty_G Γ) Ss = true ->
  forallb (no_local_ty_G G') (List.map (shift_lt_in_ty 1 c) Ss) = true.
Proof.
  intros Gamma Ss. induction Ss as [|S Ss IH]; intros c G' HIns Hnl; simpl in *; [reflexivity|].
  apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlS HnlSs].
  rewrite (no_local_ty_G_InsLt Gamma S c G' HIns HnlS), (IH c G' HIns HnlSs). reflexivity.
Qed.

Lemma InsTy_push_ty_vars_any_at_free : forall n c G G',
  InsTy c G G' ->
  InsTy (n + c) (push_ty_vars n any_at_free G) (push_ty_vars n any_at_free G').
Proof.
  induction n as [|n IH]; intros c G G' H; simpl.
  - replace (0 + c) with c by lia. exact H.
  - replace (S (n + c)) with (n + S c) by lia.
    apply IH. rewrite <- (shift_ty_any_at_free c).
    apply InsTy_ty. exact H.
Qed.

Lemma InsLt_push_ty_vars_any_at_free : forall n c G G',
  InsLt c G G' ->
  InsLt c (push_ty_vars n any_at_free G) (push_ty_vars n any_at_free G').
Proof.
  induction n as [|n IH]; intros c G G' H; simpl.
  - exact H.
  - apply IH. rewrite <- (shift_lt_any_at_free c).
    apply InsLt_ty. exact H.
Qed.

Lemma InsTmAt_fold_bind_tm : forall rhos c G G',
  InsTmAt c G G' ->
  InsTmAt (c + List.length rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G' rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros c G G' H; simpl.
  - replace (c + 0) with c by lia. exact H.
  - replace (c + S (List.length rhos)) with (S (c + List.length rhos)) by lia.
    apply InsTmAt_tm. apply IH. exact H.
Qed.

Lemma InsTy_fold_bind_tm : forall rhos c G G',
  InsTy c G G' ->
  InsTy c
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm (shift_ty 1 c rho) :: G0) G' rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros c G G' H; simpl.
  - exact H.
  - apply InsTy_tm. apply IH. exact H.
Qed.

Lemma InsLt_fold_bind_tm : forall rhos c G G',
  InsLt c G G' ->
  InsLt c
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm (shift_lt_in_ty 1 c rho) :: G0) G' rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros c G G' H; simpl.
  - exact H.
  - apply InsLt_tm. apply IH. exact H.
Qed.

Lemma Forall2_typing_InsTmAt : forall Γ vs rhos,
  Forall2 (fun v rho => forall c G', InsTmAt c Γ G' -> G' ⊢ₜ shift_tm 1 c v : rho) vs rhos ->
  forall c G', InsTmAt c Γ G' ->
  Forall2 (fun v rho => G' ⊢ₜ v : rho) (List.map (shift_tm 1 c) vs) rhos.
Proof.
  intros Γ vs rhos H. induction H; intros c G' HIns; simpl.
  - constructor.
  - constructor.
    + apply H. exact HIns.
    + apply IHForall2. exact HIns.
Qed.

Lemma Forall2_typing_InsTy : forall Γ vs rhos,
  Forall2 (fun v rho => forall c G', InsTy c Γ G' -> G' ⊢ₜ shift_ty_in_tm 1 c v : shift_ty 1 c rho) vs rhos ->
  forall c G', InsTy c Γ G' ->
  Forall2 (fun v rho => G' ⊢ₜ v : rho)
           (List.map (shift_ty_in_tm 1 c) vs) (List.map (shift_ty 1 c) rhos).
Proof.
  intros Γ vs rhos H. induction H; intros c G' HIns; simpl.
  - constructor.
  - constructor.
    + apply H. exact HIns.
    + apply IHForall2. exact HIns.
Qed.

Lemma Forall2_typing_InsLt : forall Γ vs rhos,
  Forall2 (fun v rho => forall c G', InsLt c Γ G' -> G' ⊢ₜ shift_lt_in_tm 1 c v : shift_lt_in_ty 1 c rho) vs rhos ->
  forall c G', InsLt c Γ G' ->
  Forall2 (fun v rho => G' ⊢ₜ v : rho)
           (List.map (shift_lt_in_tm 1 c) vs) (List.map (shift_lt_in_ty 1 c) rhos).
Proof.
  intros Γ vs rhos H. induction H; intros c G' HIns; simpl.
  - constructor.
  - constructor.
    + apply H. exact HIns.
    + apply IHForall2. exact HIns.
Qed.

Lemma typing_InsTmAt : forall G t T, G ⊢ₜ t : T ->
  forall c G', InsTmAt c G G' -> G' ⊢ₜ shift_tm 1 c t : T.
Proof.
  apply (typing_ind_forall2 (fun G t T => forall c G', InsTmAt c G G' -> G' ⊢ₜ shift_tm 1 c t : T)).
  - intros Γ x T Hlk Hwf c G' HIns. simpl. eapply typing_var_InsTmAt; eauto.
  - intros Γ t T U Ht IHt Hsub c G' HIns. simpl.
    eapply T_Sub.
    + apply IHt. exact HIns.
    + apply (sub_InsTm Γ T U Hsub G' (InsTmAt_to_InsTm c Γ G' HIns)).
  - intros Γ body A l B HwfA HwfB Hbody IHbody Hcap c G' HIns. simpl.
    apply T_Lam.
    + eapply ty_wf_InsTm; [exact HwfA|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfB|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + apply IHbody. apply InsTmAt_tm. exact HIns.
    + rewrite (capture_lt_InsTmAt c Γ G' HIns body).
      apply (lt_sub_InsTm Γ (capture_lt Γ body) l Hcap G' (InsTmAt_to_InsTm c Γ G' HIns)).
  - intros Γ t1 t2 A l B Ht1 IHt1 Ht2 IHt2 c G' HIns. simpl.
    eapply T_App; [apply IHt1|apply IHt2]; exact HIns.
  - intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody c G' HIns. simpl.
    apply T_TyLam.
    + eapply ty_wf_InsTm; [exact HwfBound|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfT|]. apply InsTm_ty. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + rewrite is_abs_shift_tm. exact HisAbs.
    + apply IHbody. apply InsTmAt_ty. exact HIns.
  - intros Γ t B U S Ht IHt HwfS Hsub HnlArg c G' HIns. simpl.
    eapply T_TyApp.
    + apply IHt. exact HIns.
    + eapply ty_wf_InsTm; [exact HwfS|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + apply (sub_InsTm Γ S B Hsub G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + eapply ty_app_arg_no_local_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact HnlArg].
  - intros Γ body T HwfT HisAbs Hbody IHbody c G' HIns. simpl.
    apply T_LtLam.
    + eapply ty_wf_InsTm; [exact HwfT|]. apply InsTm_lt. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + rewrite is_abs_shift_tm. exact HisAbs.
    + apply IHbody. apply InsTmAt_lt. exact HIns.
  - intros Γ t T l Ht IHt Hwfl c G' HIns. simpl.
    eapply T_LtApp.
    + apply IHt. exact HIns.
    + eapply lt_wf_InsTm; [exact Hwfl|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
            Hctor Heff Hlts Hwflts Hrho HTs HwfTs Hresult Hshape Hresult_eff Hwfl Hlt Hbounded Hlen Hargs IHargs c G' HIns.
    simpl. rewrite shift_tm_go_eq_map.
    eapply T_Ctor with
      (rho_fields := rho_fields) (result_ty_schema := result_ty_schema)
      (result_tag := result_tag); eauto.
    + rewrite (InsTm_lookup_ctor Γ G' (InsTmAt_to_InsTm c Γ G' HIns) K). exact Hctor.
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) K). exact Heff.
            + eapply lifetimes_wf_InsTm; [exact Hwflts|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
            + eapply types_wf_InsTm; [exact HwfTs|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) result_tag). exact Hresult_eff.
            + eapply lt_wf_InsTm; [exact Hwfl|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + apply (lt_sub_InsTm Γ (lt_of_ty_list rho_fields) l Hlt
           G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + eapply Forall_impl; [|exact Hbounded].
      intros l0 Hsub.
      apply (lt_sub_InsTm Γ l0 l Hsub G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + rewrite !List.length_map. exact Hlen.
    + apply (Forall2_typing_InsTmAt Γ vs rho_fields IHargs c G' HIns).
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l
           Γyes yes_body eta elim_result no_body
           Hneq Hctor Heff Hlts Hrho HTs HwfTs Hscrut_result Hscrut_shape
           Hresult_eff Hresult_ne HwfDelta Hresult_l Hscrut IHscrut Harity HΓyes Hyes IHyes Helim Hno IHno c G' HIns.
    simpl. subst Γyes.
    eapply T_Match with
      (n_lt := n_lt) (n_ty := n_ty) (sigma_fields := sigma_fields)
      (result_ty_schema := result_ty_schema) (lts := lts) (rho_fields := rho_fields)
      (scrut_result_ty := scrut_result_ty)
      (result_tag := result_tag) (result_l := result_l)
      (Γ' := push_lt_vars n_lt Delta G') (eta := eta).
    + exact Hneq.
    + rewrite (InsTm_lookup_ctor Γ G' (InsTmAt_to_InsTm c Γ G' HIns) K). exact Hctor.
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) K). exact Heff.
    + exact Hlts.
    + exact Hrho.
    + exact HTs.
    + eapply types_wf_InsTm; [exact HwfTs|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + exact Hscrut_result.
    + exact Hscrut_shape.
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) result_tag). exact Hresult_eff.
    + exact Hresult_ne.
    + eapply lt_wf_InsTm; [exact HwfDelta|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + apply (lt_sub_InsTm Γ result_l Delta Hresult_l
           G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + apply IHscrut. exact HIns.
    + exact Harity.
    + reflexivity.
    + apply IHyes.
      rewrite Harity.
      apply InsTmAt_fold_bind_tm.
      apply InsTmAt_push_lt_vars. exact HIns.
    + exact Helim.
    + apply IHno. exact HIns.
  - intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff HTs HwfTs HwfTR Hsig Hret Hop IHop c G' HIns.
    simpl.
    eapply T_Cap with (n_α := n_α) (n_β := n_β) (sig := sig) (ret := ret)
      (sig_β := sig_β) (ret_β := ret_β).
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) E_tag). exact Heff.
    + exact HTs.
    + eapply types_wf_InsTm; [exact HwfTs|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTR|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + exact Hsig.
    + exact Hret.
    + apply IHop.
      replace (c + 2) with (S (S c)) by lia.
      apply InsTmAt_tm. apply InsTmAt_tm. apply InsTmAt_push_ty_vars. exact HIns.
  - intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
           Heff HTs HwfTs HwfTB HwfTR Hnolocal Hsub Hsig Hret Hop IHop Hbody IHbody c G' HIns.
    simpl.
    eapply T_Handle with (n_α := n_α) (n_β := n_β) (sig := sig) (ret := ret)
      (T_B := T_B) (sig_β := sig_β) (ret_β := ret_β).
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) E_tag). exact Heff.
    + exact HTs.
    + eapply types_wf_InsTm; [exact HwfTs|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTB|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTR|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply no_local_ty_G_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact Hnolocal].
    + apply (sub_InsTm Γ T_B T_R Hsub G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + exact Hsig.
    + exact Hret.
    + apply IHop.
      replace (c + 2) with (S (S c)) by lia.
      apply InsTmAt_tm. apply InsTmAt_tm. apply InsTmAt_push_ty_vars. exact HIns.
    + apply IHbody. apply InsTmAt_tm. exact HIns.
  - intros Γ recv arg E_tag Delta Ts Ss n_α n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff HTs HSs HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg c G' HIns.
    simpl.
    eapply T_Perform with (n_α := n_α) (n_β := n_β) (sig := sig) (ret := ret)
      (sig_inst := sig_inst) (ret_inst := ret_inst).
    + apply IHrecv. exact HIns.
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) E_tag). exact Heff.
    + exact HTs.
    + exact HSs.
    + eapply types_wf_InsTm; [exact HwfSs|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply forallb_no_local_ty_G_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact HnoSs].
    + exact Hsig.
    + eapply no_local_ty_G_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact HnoSig].
    + exact Hret.
    + eapply ty_wf_InsTm; [exact HwfRet|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + apply IHarg. exact HIns.
  - intros Γ m T_B T_R t HwfTB HwfTR Hnolocal Hsub Ht IHt c G' HIns. simpl.
    apply T_HandlerM.
    + eapply ty_wf_InsTm; [exact HwfTB|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTR|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply no_local_ty_G_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact Hnolocal].
    + apply (sub_InsTm Γ T_B T_R Hsub G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + apply IHt. exact HIns.
  - intros Γ m b A T_B T_R HwfA HwfTB HwfTR Hnolocal Hsub Hb IHb c G' HIns. simpl.
    apply T_Resume.
    + eapply ty_wf_InsTm; [exact HwfA|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTB|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTR|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply no_local_ty_G_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact Hnolocal].
    + apply (sub_InsTm Γ T_B T_R Hsub G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + apply IHb. apply InsTmAt_tm. exact HIns.
Qed.

Lemma typing_weaken_tm_shift : forall Γ A t T,
  Γ ⊢ₜ t : T -> (bind_tm A :: Γ) ⊢ₜ shift_tm 1 0 t : T.
Proof.
  intros Γ A t T H. eapply typing_InsTmAt; [exact H|apply InsTmAt_here].
Qed.

Lemma typing_weaken_tm_shift_many : forall Γ rhos t T,
  Γ ⊢ₜ t : T ->
  (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos)
    ⊢ₜ shift_tm (List.length rhos) 0 t : T.
Proof.
  intros Γ rhos. induction rhos as [|rho rhos IH]; intros t T Hty; simpl.
  - rewrite shift_tm_zero. exact Hty.
  - replace (shift_tm (S (List.length rhos)) 0 t)
      with (shift_tm 1 0 (shift_tm (List.length rhos) 0 t)).
    + apply typing_weaken_tm_shift. apply IH. exact Hty.
    + rewrite shift_tm_fuse.
      replace (1 + List.length rhos) with (S (List.length rhos)) by lia.
      reflexivity.
Qed.

Lemma value_shift_tm : forall v,
  value v -> forall amount cutoff, value (shift_tm amount cutoff v).
Proof.
  fix IH 2.
  intros v Hv amount cutoff. destruct Hv; simpl.
  - constructor.
  - constructor.
  - constructor.
  - rewrite shift_tm_go_eq_map. constructor.
    induction H as [|v vs Hv Hvs IHvs]; simpl.
    + constructor.
    + constructor; [apply (IH v Hv amount cutoff)|exact IHvs].
  - constructor.
  - constructor.
Qed.

Lemma value_shift_ty_in_tm : forall v,
  value v -> forall amount cutoff, value (shift_ty_in_tm amount cutoff v).
Proof.
  fix IH 2.
  intros v Hv amount cutoff. destruct Hv; simpl.
  - constructor.
  - constructor.
  - constructor.
  - rewrite shift_ty_in_tm_go_eq_map. constructor.
    induction H as [|v vs Hv Hvs IHvs]; simpl.
    + constructor.
    + constructor; [apply (IH v Hv amount cutoff)|exact IHvs].
  - constructor.
  - constructor.
Qed.

Lemma value_shift_lt_in_tm : forall v,
  value v -> forall amount cutoff, value (shift_lt_in_tm amount cutoff v).
Proof.
  fix IH 2.
  intros v Hv amount cutoff. destruct Hv; simpl.
  - constructor.
  - constructor.
  - constructor.
  - rewrite shift_lt_in_tm_go_eq_map. constructor.
    induction H as [|v vs Hv Hvs IHvs]; simpl.
    + constructor.
    + constructor; [apply (IH v Hv amount cutoff)|exact IHvs].
  - constructor.
  - constructor.
Qed.

Lemma subst_tm_go_eq_map : forall var replacement ts,
  (fix go ts := match ts with [] => [] | u :: rest => subst_tm var replacement u :: go rest end) ts =
  List.map (subst_tm var replacement) ts.
Proof.
  intros var replacement ts. induction ts as [|t ts IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma subst_tm_var_eq : forall var replacement y,
  subst_tm var replacement (term_var y) =
    if Nat.eqb y var then replacement else if Nat.ltb var y then term_var (pred y) else term_var y.
Proof. reflexivity. Qed.

Lemma subst_tm_shift_cancel : forall t c replacement,
  subst_tm c replacement (shift_tm 1 c t) = t.
Proof.
  enough (H : forall t, forall c replacement,
    subst_tm c replacement (shift_tm 1 c t) = t).
  { intros; apply H. }
  apply (term_list_ind
    (fun t => forall c replacement, subst_tm c replacement (shift_tm 1 c t) = t)
    (fun ts => forall c replacement,
      List.map (subst_tm c replacement) (List.map (shift_tm 1 c) ts) = ts)).
  - intros n c replacement. rewrite shift_tm_var_eq, subst_tm_var_eq.
    destruct (Nat.leb c n) eqn:E.
    + apply Nat.leb_le in E.
      destruct (Nat.eqb_spec (n + 1) c); [lia|].
      destruct (Nat.ltb_spec c (n + 1)); [f_equal; lia|lia].
    + apply Nat.leb_gt in E.
      destruct (Nat.eqb_spec n c); [lia|].
      destruct (Nat.ltb_spec c n); [lia|reflexivity].
  - intros t1 t2 IH1 IH2 c replacement. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH c replacement. simpl. rewrite IH. reflexivity.
  - intros t T IH c replacement. simpl. rewrite IH. reflexivity.
  - intros bound body IH c replacement. simpl. rewrite IH. reflexivity.
  - intros t l IH c replacement. simpl. rewrite IH. reflexivity.
  - intros body IH c replacement. simpl. rewrite IH. reflexivity.
  - intros K l lts Ts ts IH c replacement. simpl.
    rewrite shift_tm_go_eq_map, subst_tm_go_eq_map. rewrite IH. reflexivity.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn c replacement. simpl.
    rewrite IHs.
    replace (c + arity) with (c + arity) by reflexivity.
    rewrite IHy.
    rewrite IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb c replacement. simpl.
    rewrite IHop. rewrite IHb. reflexivity.
  - intros t Ss arg IHt IHa c replacement. simpl. rewrite IHt, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop c replacement. simpl. rewrite IHop. reflexivity.
  - intros m T_B T_R t IH c replacement. simpl. rewrite IH. reflexivity.
  - intros m T_B T_R b IH c replacement. simpl. rewrite IH. reflexivity.
  - intros c replacement. reflexivity.
  - intros t ts IHt IHts c replacement. simpl. rewrite IHt, IHts. reflexivity.
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

Lemma subst_lt_var_same : forall v R,
  subst_lt v R (lt_var v) = R.
Proof.
  intros v R. rewrite subst_lt_var_eq, Nat.eqb_refl. reflexivity.
Qed.

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

Lemma shift_lt_subst_lt_above_comm : forall l n c R,
  shift_lt 1 (n + c) (subst_lt n R l) =
  subst_lt n (shift_lt 1 (n + c) R) (shift_lt 1 (S (n + c)) l).
Proof.
  induction l as [x| | |l1 IH1 l2 IH2]; intros n c R.
  - rewrite subst_lt_var_eq, !shift_lt_var_eq, subst_lt_var_eq.
    destruct (Nat.eqb_spec x n) as [Heq|Hneq].
    + subst x. rewrite (proj2 (Nat.leb_gt (S (n + c)) n)) by lia.
      rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.ltb_spec n x) as [Hgt|Hle].
      * rewrite (shift_lt_var_eq 1 (n + c) (pred x)).
        destruct (Nat.leb (S (n + c)) x) eqn:Hshift.
        -- apply Nat.leb_le in Hshift.
           rewrite (proj2 (Nat.leb_le (n + c) (pred x))) by lia.
           destruct (Nat.eqb_spec (x + 1) n); [lia|].
           destruct (Nat.ltb_spec n (x + 1)); [f_equal; lia|lia].
        -- apply Nat.leb_gt in Hshift.
           rewrite (proj2 (Nat.leb_gt (n + c) (pred x))) by lia.
           destruct (Nat.eqb_spec x n); [lia|].
           destruct (Nat.ltb_spec n x); [reflexivity|lia].
      * destruct (Nat.eqb_spec x n); [lia|].
        destruct (Nat.ltb_spec n x); [lia|].
        destruct x as [|x'].
        -- destruct n as [|n']; [lia|]. reflexivity.
        -- simpl.
           assert (Hcut_pred : (n + c <=? x') = false) by (apply Nat.leb_gt; lia).
           assert (Hcut_x : (n + c <=? S x') = false) by (apply Nat.leb_gt; lia).
           rewrite Hcut_pred, Hcut_x.
           destruct (Nat.eqb_spec (S x') n); [lia|].
           destruct (Nat.ltb_spec n (S x')); [lia|reflexivity].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IH1, IH2. reflexivity.
Qed.

Lemma shift_lt_in_ty_subst_lt_in_ty_above_comm : forall T n c R,
  shift_lt_in_ty 1 (n + c) (subst_lt_in_ty n R T) =
  subst_lt_in_ty n (shift_lt 1 (n + c) R) (shift_lt_in_ty 1 (S (n + c)) T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall n c R,
      shift_lt_in_ty 1 (n + c) (subst_lt_in_ty n R T) =
      subst_lt_in_ty n (shift_lt 1 (n + c) R) (shift_lt_in_ty 1 (S (n + c)) T))
    (fun Ts => forall n c R,
      List.map (shift_lt_in_ty 1 (n + c)) (List.map (subst_lt_in_ty n R) Ts) =
      List.map (subst_lt_in_ty n (shift_lt 1 (n + c) R))
        (List.map (shift_lt_in_ty 1 (S (n + c))) Ts))).
  - reflexivity.
  - intros A l B HA HB n c R. simpl.
    rewrite HA, HB, shift_lt_subst_lt_above_comm. reflexivity.
  - intros K l Ts HTs n c R. rewrite subst_lt_in_ty_ctor_eq, !shift_lt_in_ty_ctor_eq, subst_lt_in_ty_ctor_eq.
    rewrite shift_lt_subst_lt_above_comm. f_equal. apply HTs.
  - intros A HA n c R. rewrite subst_lt_in_ty_ltall_eq, !shift_lt_in_ty_ltall_eq, subst_lt_in_ty_ltall_eq.
    replace (S (n + c)) with (S n + c) by lia.
    rewrite HA.
    replace (S (S n + c)) with (S (S (n + c))) by lia.
    f_equal. rewrite shift_lt_swap_0. reflexivity.
  - intros B A HB HA n c R. rewrite subst_lt_in_ty_tyall_eq, !shift_lt_in_ty_tyall_eq, subst_lt_in_ty_tyall_eq.
    rewrite HB, HA. reflexivity.
  - reflexivity.
  - intros A Ts HA HTs n c R. cbn [List.map]. rewrite HA. f_equal. apply HTs.
Qed.

Lemma shift_lt_in_ty_subst_lt_in_ty_bound0_comm : forall T c R,
  shift_lt_in_ty 1 c (subst_lt_in_ty 0 R T) =
  subst_lt_in_ty 0 (shift_lt 1 c R) (shift_lt_in_ty 1 (S c) T).
Proof.
  intros T c R.
  replace c with (0 + c) by lia.
  apply shift_lt_in_ty_subst_lt_in_ty_above_comm.
Qed.

Lemma subst_lt_shift_many_cancel : forall cutoff Q R,
  subst_lt cutoff Q (shift_lt (S cutoff) 0 R) = shift_lt cutoff 0 R.
Proof.
  intros cutoff Q R. revert cutoff Q.
  induction R as [x| | |l1 IH1 l2 IH2]; intros cutoff Q; simpl.
  - destruct (Nat.leb cutoff (x + S cutoff)) eqn:Hle.
    + destruct (Nat.eqb_spec (x + S cutoff) cutoff); [lia|].
      destruct (Nat.ltb_spec cutoff (x + S cutoff)); [f_equal; lia|lia].
    + apply Nat.leb_gt in Hle. lia.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma subst_lt_subst_lt_comm0_var : forall x cutoff n R Q,
  subst_lt cutoff
    (subst_lt (cutoff + n) (shift_lt cutoff 0 R) (shift_lt cutoff 0 Q))
    (subst_lt (S (cutoff + n)) (shift_lt (S cutoff) 0 R) (lt_var x)) =
  subst_lt (cutoff + n) (shift_lt cutoff 0 R)
    (subst_lt cutoff (shift_lt cutoff 0 Q) (lt_var x)).
Proof.
  intros x cutoff n R Q; simpl.
  repeat match goal with
    | |- context[Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); subst; simpl
    | |- context[Nat.ltb ?a ?b] => destruct (Nat.ltb_spec a b); subst; simpl
    end; try lia; try rewrite subst_lt_shift_cancel;
      try rewrite subst_lt_shift_many_cancel; try reflexivity; try (f_equal; lia);
      try (rewrite subst_lt_shift_many_cancel;
           destruct cutoff as [|cutoff']; simpl;
           [rewrite Nat.eqb_refl; reflexivity|
            destruct (Nat.eqb_spec (S cutoff' + n) cutoff'); [lia|];
            rewrite Nat.eqb_refl; reflexivity]);
      try (destruct cutoff as [|cutoff']; simpl;
           [rewrite Nat.eqb_refl; reflexivity|
            destruct (Nat.eqb_spec (S cutoff' + n) cutoff'); [lia|];
            rewrite Nat.eqb_refl; reflexivity]).
  destruct cutoff as [|cutoff'].
  - change (shift_lt 0 0 R =
      subst_lt (0 + n) (shift_lt 0 0 R) (lt_var (0 + n))).
    rewrite subst_lt_var_same. reflexivity.
  - change (shift_lt (S cutoff') 0 R =
      subst_lt (S cutoff' + n) (shift_lt (S cutoff') 0 R)
        (if S cutoff' + n =? cutoff'
         then shift_lt (S cutoff') 0 Q
         else lt_var (S cutoff' + n))).
    destruct (Nat.eqb_spec (S cutoff' + n) cutoff'); [lia|].
    rewrite subst_lt_var_same. reflexivity.
Qed.

Lemma subst_lt_subst_lt_comm0 : forall l cutoff n R Q,
  subst_lt cutoff
    (subst_lt (cutoff + n) (shift_lt cutoff 0 R) (shift_lt cutoff 0 Q))
    (subst_lt (S (cutoff + n)) (shift_lt (S cutoff) 0 R) l) =
  subst_lt (cutoff + n) (shift_lt cutoff 0 R)
    (subst_lt cutoff (shift_lt cutoff 0 Q) l).
Proof.
  induction l as [x| | |l1 IH1 l2 IH2]; intros cutoff n R Q; simpl.
  - apply subst_lt_subst_lt_comm0_var.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IH1, IH2. reflexivity.
Qed.

Lemma subst_lt_in_ty_subst_lt_in_ty_comm0 : forall T cutoff n R Q,
  subst_lt_in_ty cutoff
    (subst_lt (cutoff + n) (shift_lt cutoff 0 R) (shift_lt cutoff 0 Q))
    (subst_lt_in_ty (S (cutoff + n)) (shift_lt (S cutoff) 0 R) T) =
  subst_lt_in_ty (cutoff + n) (shift_lt cutoff 0 R)
    (subst_lt_in_ty cutoff (shift_lt cutoff 0 Q) T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall cutoff n R Q,
      subst_lt_in_ty cutoff
        (subst_lt (cutoff + n) (shift_lt cutoff 0 R) (shift_lt cutoff 0 Q))
        (subst_lt_in_ty (S (cutoff + n)) (shift_lt (S cutoff) 0 R) T) =
      subst_lt_in_ty (cutoff + n) (shift_lt cutoff 0 R)
        (subst_lt_in_ty cutoff (shift_lt cutoff 0 Q) T))
    (fun Ts => forall cutoff n R Q,
      List.map (subst_lt_in_ty cutoff
        (subst_lt (cutoff + n) (shift_lt cutoff 0 R) (shift_lt cutoff 0 Q)))
        (List.map (subst_lt_in_ty (S (cutoff + n)) (shift_lt (S cutoff) 0 R)) Ts) =
      List.map (subst_lt_in_ty (cutoff + n) (shift_lt cutoff 0 R))
        (List.map (subst_lt_in_ty cutoff (shift_lt cutoff 0 Q)) Ts))).
  - reflexivity.
  - intros A l B HA HB cutoff n R Q. simpl.
    rewrite HA, HB, subst_lt_subst_lt_comm0. reflexivity.
  - intros K l Ts HTs cutoff n R Q. rewrite subst_lt_in_ty_ctor_eq. simpl.
    rewrite subst_lt_subst_lt_comm0. f_equal. apply HTs.
  - intros A HA cutoff n R Q. simpl.
    rewrite shift_lt_subst_lt_comm0.
    rewrite !shift_lt_fuse.
    replace (1 + S cutoff) with (S (S cutoff)) by lia.
    replace (1 + cutoff) with (S cutoff) by lia.
    replace (S (cutoff + n)) with (S cutoff + n) by lia.
    replace (S (S (cutoff + n))) with (S (S cutoff + n)) by lia.
    rewrite HA.
    reflexivity.
  - intros B A HB HA cutoff n R Q. simpl. rewrite HB, HA. reflexivity.
  - intros cutoff n R Q. reflexivity.
  - intros A Ts HA HTs cutoff n R Q. cbn [List.map]. rewrite HA. f_equal. apply HTs.
Qed.

Lemma subst_lt_in_ty_subst_lt_in_ty_comm_head : forall T n R Q,
  subst_lt_in_ty 0 (subst_lt n R Q)
    (subst_lt_in_ty (S n) (shift_lt 1 0 R) T) =
  subst_lt_in_ty n R (subst_lt_in_ty 0 Q T).
Proof.
  intros T n R Q.
  pose proof (subst_lt_in_ty_subst_lt_in_ty_comm0 T 0 n R Q) as H.
  simpl in H. rewrite !shift_lt_zero in H. exact H.
Qed.

Lemma shift_lt_subst_lt_comm_many0 : forall k l n R,
  shift_lt k 0 (subst_lt n R l) =
  subst_lt (k + n) (shift_lt k 0 R) (shift_lt k 0 l).
Proof.
  induction k as [|k IH]; intros l n R.
  - rewrite !shift_lt_zero. replace (0 + n) with n by lia. reflexivity.
  - replace (S k) with (1 + k) by lia.
    rewrite <- !shift_lt_fuse.
    rewrite IH.
    rewrite shift_lt_subst_lt_comm0.
    replace (S (k + n)) with (S k + n) by lia.
    rewrite !shift_lt_fuse.
    replace (1 + k) with (S k) by lia.
    reflexivity.
Qed.

Lemma shift_lt_in_ty_subst_lt_in_ty_comm_many0 : forall k T n R,
  shift_lt_in_ty k 0 (subst_lt_in_ty n R T) =
  subst_lt_in_ty (k + n) (shift_lt k 0 R) (shift_lt_in_ty k 0 T).
Proof.
  induction k as [|k IH]; intros T n R.
  - rewrite !shift_lt_in_ty_zero, shift_lt_zero. replace (0 + n) with n by lia. reflexivity.
  - replace (S k) with (1 + k) by lia.
    rewrite <- !shift_lt_in_ty_fuse.
    rewrite IH.
    rewrite shift_lt_in_ty_subst_lt_in_ty_comm0.
    replace (S (k + n)) with (S k + n) by lia.
    rewrite shift_lt_fuse.
    rewrite !shift_lt_in_ty_fuse.
    replace (1 + k) with (S k) by lia.
    reflexivity.
Qed.

Lemma map_shift_lt_in_ty_subst_lt_in_ty_comm_many0 : forall k Ts n R,
  List.map (shift_lt_in_ty k 0) (List.map (subst_lt_in_ty n R) Ts) =
  List.map (subst_lt_in_ty (k + n) (shift_lt k 0 R))
           (List.map (shift_lt_in_ty k 0) Ts).
Proof.
  induction Ts as [|T Ts IH]; intros n R; simpl.
  - reflexivity.
  - rewrite shift_lt_in_ty_subst_lt_in_ty_comm_many0. f_equal. apply IH.
Qed.

Lemma map_shift_lt_subst_lt_comm : forall lts n c R,
  c <= n ->
  List.map (shift_lt 1 c) (List.map (subst_lt n R) lts) =
  List.map (subst_lt (S n) (shift_lt 1 c R)) (List.map (shift_lt 1 c) lts).
Proof.
  induction lts as [|l lts IH]; intros n c R Hcn; simpl.
  - reflexivity.
  - rewrite shift_lt_subst_lt_comm by lia. f_equal. apply IH. lia.
Qed.

Lemma map_shift_lt_in_ty_subst_lt_in_ty_comm : forall Ts n c R,
  c <= n ->
  List.map (shift_lt_in_ty 1 c) (List.map (subst_lt_in_ty n R) Ts) =
  List.map (subst_lt_in_ty (S n) (shift_lt 1 c R))
           (List.map (shift_lt_in_ty 1 c) Ts).
Proof.
  induction Ts as [|T Ts IH]; intros n c R Hcn; simpl.
  - reflexivity.
  - rewrite shift_lt_in_ty_subst_lt_in_ty_comm by lia. f_equal. apply IH. lia.
Qed.

Lemma shift_lt_lift_many_swap : forall k c R,
  shift_lt 1 (c + k) (shift_lt k 0 R) =
  shift_lt k 0 (shift_lt 1 c R).
Proof.
  induction k as [|k IH]; intros c R.
  - rewrite !shift_lt_zero. replace (c + 0) with c by lia. reflexivity.
  - replace (c + S k) with (S (c + k)) by lia.
    replace (shift_lt (S k) 0 R) with (shift_lt 1 0 (shift_lt k 0 R)).
    2:{ rewrite shift_lt_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    rewrite <- (shift_lt_swap (shift_lt k 0 R) 0 (c + k)) by lia.
    rewrite IH.
    rewrite shift_lt_fuse.
    replace (1 + k) with (S k) by lia.
    reflexivity.
Qed.

Lemma shift_lt_in_ty_lift_many_swap : forall k c T,
  shift_lt_in_ty 1 (c + k) (shift_lt_in_ty k 0 T) =
  shift_lt_in_ty k 0 (shift_lt_in_ty 1 c T).
Proof.
  induction k as [|k IH]; intros c T.
  - rewrite !shift_lt_in_ty_zero. replace (c + 0) with c by lia. reflexivity.
  - replace (c + S k) with (S (c + k)) by lia.
    replace (shift_lt_in_ty (S k) 0 T) with (shift_lt_in_ty 1 0 (shift_lt_in_ty k 0 T)).
    2:{ rewrite shift_lt_in_ty_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    rewrite <- (shift_lt_in_ty_swap (shift_lt_in_ty k 0 T) 0 (c + k)) by lia.
    rewrite IH.
    rewrite shift_lt_in_ty_fuse.
    replace (1 + k) with (S k) by lia.
    reflexivity.
Qed.

Lemma map_shift_lt_in_ty_lift_many_swap : forall k c Ts,
  List.map (shift_lt_in_ty 1 (c + k)) (List.map (shift_lt_in_ty k 0) Ts) =
  List.map (shift_lt_in_ty k 0) (List.map (shift_lt_in_ty 1 c) Ts).
Proof.
  intros k c Ts. induction Ts as [|T Ts IH]; simpl.
  - reflexivity.
  - rewrite shift_lt_in_ty_lift_many_swap. f_equal. apply IH.
Qed.

Lemma shift_lt_in_tm_subst_lt_in_tm_comm : forall t n c R,
  c <= n ->
  shift_lt_in_tm 1 c (subst_lt_in_tm n R t) =
  subst_lt_in_tm (S n) (shift_lt 1 c R) (shift_lt_in_tm 1 c t).
Proof.
  intros t. apply (term_list_ind
    (fun t => forall n c R, c <= n ->
       shift_lt_in_tm 1 c (subst_lt_in_tm n R t) =
       subst_lt_in_tm (S n) (shift_lt 1 c R) (shift_lt_in_tm 1 c t))
    (fun ts => forall n c R, c <= n ->
       List.map (shift_lt_in_tm 1 c) (List.map (subst_lt_in_tm n R) ts) =
       List.map (subst_lt_in_tm (S n) (shift_lt 1 c R))
                (List.map (shift_lt_in_tm 1 c) ts))).
  - intros x n c R Hcn. reflexivity.
  - intros t1 t2 IH1 IH2 n c R Hcn. simpl. rewrite IH1 by lia. rewrite IH2 by lia. reflexivity.
  - intros body T IH n c R Hcn. simpl.
    rewrite IH by lia. rewrite shift_lt_in_ty_subst_lt_in_ty_comm by lia. reflexivity.
  - intros tm T IH n c R Hcn. simpl.
    rewrite IH by lia. rewrite shift_lt_in_ty_subst_lt_in_ty_comm by lia. reflexivity.
  - intros bound body IH n c R Hcn. simpl.
    rewrite shift_lt_in_ty_subst_lt_in_ty_comm by lia. rewrite IH by lia. reflexivity.
  - intros tm l IH n c R Hcn. simpl.
    rewrite IH by lia. rewrite shift_lt_subst_lt_comm by lia. reflexivity.
  - intros body IH n c R Hcn. simpl.
    rewrite (IH (S n) (S c) (shift_lt 1 0 R)) by lia.
    rewrite (shift_lt_swap R 0 c) by lia. reflexivity.
  - intros K l lts Ts ts IH n c R Hcn. simpl.
    f_equal.
    + apply shift_lt_subst_lt_comm. lia.
    + change (List.map (shift_lt 1 c) (List.map (subst_lt n R) lts) =
              List.map (subst_lt (S n) (shift_lt 1 c R)) (List.map (shift_lt 1 c) lts)).
      apply map_shift_lt_subst_lt_comm. lia.
    + change (List.map (shift_lt_in_ty 1 c) (List.map (subst_lt_in_ty n R) Ts) =
              List.map (subst_lt_in_ty (S n) (shift_lt 1 c R))
                       (List.map (shift_lt_in_ty 1 c) Ts)).
      apply map_shift_lt_in_ty_subst_lt_in_ty_comm. lia.
    + apply IH. lia.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn n c R Hcn. simpl.
    rewrite IHs by lia.
    rewrite (IHy (n_lt + n) (c + n_lt) (shift_lt n_lt 0 R)) by lia.
    replace (S (n_lt + n)) with (n_lt + S n) by lia.
    rewrite shift_lt_lift_many_swap.
    rewrite IHn by lia.
    reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody n c R Hcn. simpl.
    f_equal.
    + change (List.map (shift_lt_in_ty 1 c) (List.map (subst_lt_in_ty n R) Ts) =
              List.map (subst_lt_in_ty (S n) (shift_lt 1 c R))
                       (List.map (shift_lt_in_ty 1 c) Ts)).
      apply map_shift_lt_in_ty_subst_lt_in_ty_comm. lia.
    + apply shift_lt_in_ty_subst_lt_in_ty_comm. lia.
    + apply shift_lt_in_ty_subst_lt_in_ty_comm. lia.
    + apply IHop. lia.
    + apply IHbody. lia.
  - intros tm Ss arg IHt IHa n c R Hcn. simpl.
    f_equal.
    + apply IHt. lia.
    + change (List.map (shift_lt_in_ty 1 c) (List.map (subst_lt_in_ty n R) Ss) =
              List.map (subst_lt_in_ty (S n) (shift_lt 1 c R))
                       (List.map (shift_lt_in_ty 1 c) Ss)).
      apply map_shift_lt_in_ty_subst_lt_in_ty_comm. lia.
    + apply IHa. lia.
  - intros E m n_beta Ts T_R op_body IHop n c R Hcn. simpl.
    f_equal.
    + change (List.map (shift_lt_in_ty 1 c) (List.map (subst_lt_in_ty n R) Ts) =
              List.map (subst_lt_in_ty (S n) (shift_lt 1 c R))
                       (List.map (shift_lt_in_ty 1 c) Ts)).
      apply map_shift_lt_in_ty_subst_lt_in_ty_comm. lia.
    + apply shift_lt_in_ty_subst_lt_in_ty_comm. lia.
    + apply IHop. lia.
  - intros m T_B T_R tm IH n c R Hcn. simpl.
    rewrite !shift_lt_in_ty_subst_lt_in_ty_comm by lia. rewrite IH by lia. reflexivity.
  - intros m T_B T_R b IH n c R Hcn. simpl.
    rewrite !shift_lt_in_ty_subst_lt_in_ty_comm by lia. rewrite IH by lia. reflexivity.
  - intros n c R Hcn. reflexivity.
  - intros tm ts IHt IHts n c R Hcn. simpl. rewrite IHt by lia. f_equal. apply IHts. lia.
Qed.

Lemma shift_lt_in_tm_subst_lt_in_tm_comm0 : forall t n R,
  shift_lt_in_tm 1 0 (subst_lt_in_tm n R t) =
  subst_lt_in_tm (S n) (shift_lt 1 0 R) (shift_lt_in_tm 1 0 t).
Proof. intros t n R. apply shift_lt_in_tm_subst_lt_in_tm_comm. lia. Qed.

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

Definition subst_lt_eff_sig (n : nat) (R : lifetime)
    (sig : nat * nat * type * type) : nat * nat * type * type :=
  let '(n_α, n_β, sig_ty, ret_ty) := sig in
  (n_α, n_β, subst_lt_in_ty n R sig_ty, subst_lt_in_ty n R ret_ty).

Definition subst_lt_ctor_sig (n : nat) (R : lifetime)
    (sig : nat * nat * list type * type) : nat * nat * list type * type :=
  let '(n_lt, n_ty, fields, result) := sig in
  (n_lt, n_ty,
   List.map (subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R)) fields,
   subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R) result).

Lemma subst_lt_eff_sig_shift_cancel : forall R sig,
  subst_lt_eff_sig 0 R (shift_lt_eff_sig 1 0 sig) = sig.
Proof.
  intros R (((n_α, n_β), sig_ty), ret_ty).
  unfold subst_lt_eff_sig, shift_lt_eff_sig. simpl.
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
Proof.
  intros n R (((n_α, n_β), sig_ty), ret_ty).
  unfold subst_lt_eff_sig, shift_lt_eff_sig. simpl.
  rewrite !shift_lt_in_ty_subst_lt_in_ty_comm0. reflexivity.
Qed.

Lemma shift_ty_eff_sig_subst_lt_eff_sig_comm : forall n R sig,
  shift_ty_eff_sig 1 0 (subst_lt_eff_sig n R sig) =
  subst_lt_eff_sig n R (shift_ty_eff_sig 1 0 sig).
Proof.
  intros n R (((n_α, n_β), sig_ty), ret_ty).
  unfold subst_lt_eff_sig, shift_ty_eff_sig. simpl.
  rewrite !shift_ty_subst_lt_in_ty_commute. reflexivity.
Qed.

Lemma shift_ty_ctor_sig_subst_lt_ctor_sig_comm : forall n R sig,
  shift_ty_ctor_sig 1 0 (subst_lt_ctor_sig n R sig) =
  subst_lt_ctor_sig n R (shift_ty_ctor_sig 1 0 sig).
Proof.
  intros n R (((n_lt, n_ty), fields), result).
  unfold subst_lt_ctor_sig, shift_ty_ctor_sig. simpl.
  assert (Hfields :
    List.map (shift_ty 1 (n_ty + 0))
      (List.map (subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R)) fields) =
    List.map (subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R))
      (List.map (shift_ty 1 (n_ty + 0)) fields)).
  { induction fields as [|T fields IH]; simpl.
    - reflexivity.
    - rewrite shift_ty_subst_lt_in_ty_commute. f_equal. exact IH. }
  rewrite Hfields, shift_ty_subst_lt_in_ty_commute. reflexivity.
Qed.

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

Lemma lt_wf_SubstLt : forall G l,
  lt_wf G l -> forall R n G', SubstLt R n G G' -> lt_wf G' (subst_lt n R l).
Proof.
  intros G l Hwf. induction Hwf; intros R n G' HS.
  - destruct (Nat.eq_dec x n) as [Hx|Hx].
    + subst x. rewrite subst_lt_var_eq, Nat.eqb_refl.
      eapply SubstLt_replacement_wf; eauto.
    + rewrite (subst_lt_var_neq n R x Hx). econstructor.
      rewrite (SubstLt_lookup_lt R n Γ G' HS x Hx). rewrite H. reflexivity.
  - constructor.
  - constructor.
  - simpl. constructor.
    + apply (IHHwf1 R n G' HS).
    + apply (IHHwf2 R n G' HS).
Qed.

Lemma lifetimes_wf_SubstLt : forall G lts,
  lifetimes_wf G lts -> forall R n G', SubstLt R n G G' ->
    lifetimes_wf G' (List.map (subst_lt n R) lts).
Proof.
  intros G lts Hwf. induction Hwf; intros R n G' HS; cbn [List.map].
  - constructor.
  - constructor.
    + eapply lt_wf_SubstLt; eauto.
    + apply (IHHwf R n G' HS).
Qed.

Lemma ty_wf_SubstLt : forall G T,
  ty_wf G T -> forall R n G', SubstLt R n G G' -> ty_wf G' (subst_lt_in_ty n R T)
with types_wf_SubstLt : forall G Ts,
  types_wf G Ts -> forall R n G', SubstLt R n G G' ->
    types_wf G' (List.map (subst_lt_in_ty n R) Ts).
Proof.
  - intros G T Hwf. induction Hwf; intros R n G' HS.
    + simpl. econstructor.
      * rewrite (SubstLt_lookup_ty R n Γ G' HS α). rewrite H. reflexivity.
      * apply IHHwf. exact HS.
    + rewrite subst_lt_in_ty_fun_eq. constructor.
      * apply IHHwf1. exact HS.
      * eapply lt_wf_SubstLt; eauto.
      * apply IHHwf2. exact HS.
    + rewrite subst_lt_in_ty_ctor_eq. constructor.
      * eapply lt_wf_SubstLt; eauto.
      * eapply types_wf_SubstLt; eauto.
    + rewrite subst_lt_in_ty_ltall_eq. constructor.
      apply IHHwf. apply SubstLt_lt. exact HS.
    + rewrite subst_lt_in_ty_tyall_eq. constructor.
      * apply IHHwf1. exact HS.
      * apply IHHwf2. apply SubstLt_ty. exact HS.
  - intros G Ts Hwf. induction Hwf; intros R n G' HS; cbn [List.map].
    + constructor.
    + constructor.
      * eapply ty_wf_SubstLt; eauto.
      * apply (IHHwf R n G' HS).
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

Lemma lt_sub_SubstLt : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall R n G', SubstLt R n G G' ->
  G' ⊢ₗ subst_lt n R l1 <: subst_lt n R l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l Hwf|Γ l Hwf|Γ x Δ Hlk HwfD|Γ l Hwf
                 |Γ l1 l2 l3 H1 IH1 H2 IH2|Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H1 IH1 Hwf2|Γ l l1 l2 H1 IH1 Hwf1];
    intros R n G' HS.
  - apply LS_Free. eapply lt_wf_SubstLt; eauto.
  - apply LS_Local. eapply lt_wf_SubstLt; eauto.
  - destruct (Nat.eq_dec x n) as [Hx|Hx].
    + subst x. rewrite subst_lt_var_eq. rewrite Nat.eqb_refl.
      destruct (SubstLt_target R n Γ G' HS) as [Δt [Hlkt Hsubt]].
      rewrite Hlk in Hlkt. inversion Hlkt; subst Δt. exact Hsubt.
    + rewrite (subst_lt_var_neq n R x Hx). apply LS_Var.
      * rewrite (SubstLt_lookup_lt R n Γ G' HS x Hx). rewrite Hlk. reflexivity.
      * eapply lt_wf_SubstLt; eauto.
  - apply LS_Refl. eapply lt_wf_SubstLt; eauto.
  - eapply LS_Trans; [apply (IH1 R n G' HS) | apply (IH2 R n G' HS)].
  - apply LS_MinL; [apply (IH1 R n G' HS) | apply (IH2 R n G' HS)].
  - apply LS_MinR1.
    + apply (IH1 R n G' HS).
    + eapply lt_wf_SubstLt; eauto.
  - apply LS_MinR2.
    + apply (IH1 R n G' HS).
    + eapply lt_wf_SubstLt; eauto.
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

Lemma sub_SubstLt : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall R n G', SubstLt R n G G' ->
  G' ⊢ subst_lt_in_ty n R T1 <:: subst_lt_in_ty n R T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T Hwf|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                 |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                 |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2];
    intros R n G' HS.
  - apply SA_Refl. eapply ty_wf_SubstLt; eauto.
  - eapply SA_Trans; [apply (IH1 R n G' HS) | apply (IH2 R n G' HS)].
  - rewrite subst_lt_in_ty_var_eq. apply SA_VarCtx.
    + rewrite (SubstLt_lookup_ty R n Γ G' HS α). rewrite Hlk. reflexivity.
    + eapply ty_wf_SubstLt; eauto.
  - rewrite !subst_lt_in_ty_ctor_eq. apply SA_Data.
    + apply (lt_sub_SubstLt Γ l l' Hls R n G' HS).
    + eapply types_wf_SubstLt; eauto.
  - rewrite subst_lt_in_ty_ctor_eq. cbn [List.map]. apply SA_Any.
    + eapply ty_wf_SubstLt; eauto.
    + eapply lt_wf_SubstLt; eauto.
    + rewrite (lt_of_ty_G_SubstLt R n Γ G' HS T).
      apply (lt_sub_SubstLt Γ (lt_of_ty_G Γ T) Δ Hls R n G' HS).
  - rewrite !subst_lt_in_ty_fun_eq. apply SA_Fun.
    + apply (IH1 R n G' HS).
    + apply (lt_sub_SubstLt Γ l l' Hl R n G' HS).
    + apply (IH2 R n G' HS).
  - rewrite !subst_lt_in_ty_ltall_eq. apply SA_LtAll.
    apply (IH1 (shift_lt 1 0 R) (S n) (bind_lt lt_local :: G')
             (SubstLt_lt R n Γ G' lt_local HS)).
  - rewrite !subst_lt_in_ty_tyall_eq. eapply SA_TyAll.
    + eapply ty_wf_SubstLt; [exact HwfA|]. apply SubstLt_ty. exact HS.
    + eapply ty_wf_SubstLt; [exact HwfA'|]. apply SubstLt_ty. exact HS.
    + apply (IH1 R n G' HS).
    + apply (IH2 R n (bind_ty (subst_lt_in_ty n R B') :: G')
               (SubstLt_ty R n Γ G' B' HS)).
Qed.

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

Lemma SubstLt_fold_bind_tm : forall rhos R n G G',
  SubstLt R n G G' ->
  SubstLt R n
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm (subst_lt_in_ty n R rho) :: G0) G' rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros R n G G' HS; simpl.
  - exact HS.
  - apply SubstLt_tm. apply IH. exact HS.
Qed.

Lemma Forall2_typing_SubstLt : forall Γ vs rhos,
  Forall2 (fun v rho => forall R n G', SubstLt R n Γ G' ->
    G' ⊢ₜ subst_lt_in_tm n R v : subst_lt_in_ty n R rho) vs rhos ->
  forall R n G', SubstLt R n Γ G' ->
  Forall2 (fun v rho => G' ⊢ₜ v : rho)
           (List.map (subst_lt_in_tm n R) vs)
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

Lemma no_local_ty_subst_ty : forall T n Sb,
  no_local_ty T = true ->
  no_local_ty (subst_ty n Sb T) = true.
Proof.
  intros T. apply (type_list_ind
    (fun T => forall n Sb,
      no_local_ty T = true -> no_local_ty (subst_ty n Sb T) = true)
    (fun Ts => forall n Sb,
      fold_right (fun A acc => andb (no_local_ty A) acc) true Ts = true ->
      fold_right (fun A acc => andb (no_local_ty A) acc) true
        (List.map (subst_ty n Sb) Ts) = true)).
  - intros x n Sb Hnl. discriminate Hnl.
  - intros A l B HA HB n Sb Hnl. simpl in *.
    repeat rewrite Bool.andb_true_iff in Hnl.
    destruct Hnl as [HnlA [Hnll HnlB]].
    rewrite (HA n Sb HnlA), Hnll, (HB n Sb HnlB). reflexivity.
  - intros K l Ts HTs n Sb Hnl. rewrite subst_ty_ctor_eq. simpl in *.
    rewrite !no_local_ty_go_eq_fold in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [Hnll HnlTs].
    rewrite Hnll, (HTs n Sb HnlTs). reflexivity.
  - intros A HA n Sb Hnl. simpl in *. apply HA. exact Hnl.
  - intros B A HB HA n Sb Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlB HnlA].
    rewrite (HB n Sb HnlB), (HA (S n) (shift_ty 1 0 Sb) HnlA). reflexivity.
  - intros n Sb Hnl. reflexivity.
  - intros A Ts HA HTs n Sb Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlA HnlTs].
    rewrite (HA n Sb HnlA), (HTs n Sb HnlTs). reflexivity.
Qed.

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

(* Deprecated specialized shape kept via the generalized theorem. *)
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

Lemma inst_op_alpha_shift_ty : forall n_α Ts n_β T c,
  List.length Ts = n_α ->
  inst_op_alpha n_α (List.map (shift_ty 1 c) Ts) n_β
    (shift_ty 1 (n_α + n_β + c) T) =
  shift_ty 1 (n_β + c) (inst_op_alpha n_α Ts n_β T).
Proof.
  intros n_α Ts n_β T c Hlen. unfold inst_op_alpha.
  replace (List.map (shift_ty n_β 0) (List.map (shift_ty 1 c) Ts)) with
    (List.map (shift_ty 1 (n_β + c)) (List.map (shift_ty n_β 0) Ts)).
  - replace (n_α + n_β + c) with (n_α + (n_β + c)) by lia.
    rewrite inst_ty_vars_shift_ty by (rewrite List.length_map; exact Hlen).
    reflexivity.
  - rewrite !List.map_map. apply List.map_ext. intro U.
    symmetry. apply shift_ty_lift_shift.
Qed.

Lemma inst_op_arg_shift_ty : forall n_α Ts n_β Ss T c,
  List.length Ts = n_α ->
  List.length Ss = n_β ->
  inst_op_arg n_α (List.map (shift_ty 1 c) Ts)
    n_β (List.map (shift_ty 1 c) Ss)
    (shift_ty 1 (n_α + n_β + c) T) =
  shift_ty 1 c (inst_op_arg n_α Ts n_β Ss T).
Proof.
  intros n_α Ts n_β Ss T c HlenTs HlenSs. unfold inst_op_arg.
  rewrite inst_op_alpha_shift_ty by exact HlenTs.
  rewrite inst_ty_vars_shift_ty by exact HlenSs.
  reflexivity.
Qed.

Lemma lt_of_ty_shift_ty_for_typing_InsTy : forall T c,
  lt_of_ty (shift_ty 1 c T) = lt_of_ty T.
Proof.
  apply (type_list_ind
    (fun T => forall c, lt_of_ty (shift_ty 1 c T) = lt_of_ty T)
    (fun Ts => forall c,
      lt_of_ty_list (List.map (shift_ty 1 c) Ts) = lt_of_ty_list Ts)).
  - reflexivity.
  - intros A l B HA HB c. simpl. reflexivity.
  - intros K l Ts HTs c. rewrite shift_ty_ctor_eq. simpl. f_equal. apply HTs.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros A Ts HA HTs c. cbn [List.map]. unfold lt_of_ty_list in *. simpl.
    rewrite HA, HTs. reflexivity.
Qed.

Lemma lt_of_ty_list_shift_ty_for_typing_InsTy : forall Ts c,
  lt_of_ty_list (List.map (shift_ty 1 c) Ts) = lt_of_ty_list Ts.
Proof.
  intros Ts c. induction Ts as [|T Ts IH]; simpl; [reflexivity|].
  rewrite lt_of_ty_shift_ty_for_typing_InsTy, IH. reflexivity.
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
      lt_of_ty_list (List.map (shift_ty 1 c) Ts) = lt_of_ty_list Ts)).
  - reflexivity.
  - intros A l B HA HB c. simpl. reflexivity.
  - intros K l Ts HTs c. rewrite shift_ty_ctor_eq. simpl. f_equal. apply HTs.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros A Ts HA HTs c. cbn [List.map]. unfold lt_of_ty_list in *. simpl.
    rewrite HA, HTs. reflexivity.
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
      lt_of_ty_list (List.map (shift_lt_in_ty 1 c) Ts) = shift_lt 1 c (lt_of_ty_list Ts))).
  - reflexivity.
  - reflexivity.
  - intros K l Ts HTs c. rewrite shift_lt_in_ty_ctor_eq. simpl.
    rewrite HTs. rewrite <- shift_lt_min_eq. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros A Ts HA HTs c. cbn [List.map]. unfold lt_of_ty_list in *. simpl.
    rewrite HA, HTs. rewrite <- shift_lt_min_eq. reflexivity.
Qed.

Lemma lt_of_ty_list_shift_lt : forall Ts c,
  lt_of_ty_list (List.map (shift_lt_in_ty 1 c) Ts) = shift_lt 1 c (lt_of_ty_list Ts).
Proof.
  intros Ts c. induction Ts as [|T Ts IH]; simpl; [reflexivity|].
  rewrite lt_of_ty_shift_lt, IH. rewrite <- shift_lt_min_eq. reflexivity.
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
    rewrite HA, HB. destruct (elim_ty lvar bound (flip_var p) A);
      destruct (elim_lt lvar bound p l); destruct (elim_ty lvar bound p B); reflexivity.
  - intros K l Ts HTs lvar bound p c. simpl.
    destruct (elim_lt lvar bound p l); [|reflexivity].
    rewrite shift_ty_go_eq_map.
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
    rewrite HB, HA. destruct (elim_ty lvar bound (flip_var p) B);
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

Lemma typing_InsTy : forall G t T, G ⊢ₜ t : T ->
  forall c G', InsTy c G G' -> G' ⊢ₜ shift_ty_in_tm 1 c t : shift_ty 1 c T.
Proof.
  apply (typing_ind_forall2
    (fun G t T => forall c G', InsTy c G G' ->
       G' ⊢ₜ shift_ty_in_tm 1 c t : shift_ty 1 c T)).
  - intros Γ x T Hlk Hwf c G' HIns. simpl.
    apply T_Var.
    + rewrite (InsTy_lookup_tm c Γ G' HIns x), Hlk. reflexivity.
    + eapply ty_wf_InsTy; eauto.
  - intros Γ t T U Ht IHt Hsub c G' HIns. simpl.
    eapply T_Sub.
    + apply IHt. exact HIns.
    + apply (sub_InsTy Γ T U Hsub c G' HIns).
  - intros Γ body A l B HwfA HwfB Hbody IHbody Hcap c G' HIns. simpl.
    apply T_Lam.
    + eapply ty_wf_InsTy; eauto.
    + eapply ty_wf_InsTy; eauto.
    + apply IHbody. apply InsTy_tm. exact HIns.
    + rewrite (capture_lt_InsTy c Γ G' HIns body).
      apply (lt_sub_InsTy Γ (capture_lt Γ body) l Hcap c G' HIns).
  - intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 c G' HIns. simpl.
    eapply T_App; [apply IH1|apply IH2]; exact HIns.
  - intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody c G' HIns. simpl.
    apply T_TyLam.
    + eapply ty_wf_InsTy; eauto.
    + eapply ty_wf_InsTy; [exact HwfT|]. apply InsTy_ty. exact HIns.
    + rewrite is_abs_shift_ty_in_tm. exact HisAbs.
    + apply IHbody. apply InsTy_ty. exact HIns.
  - intros Γ t B U S Ht IHt HwfS Hsub HnlArg c G' HIns. simpl.
    rewrite shift_ty_subst_ty_comm_ge0.
    eapply T_TyApp.
    + apply IHt. exact HIns.
    + eapply ty_wf_InsTy; eauto.
    + apply (sub_InsTy Γ S B Hsub c G' HIns).
    + eapply ty_app_arg_no_local_InsTy; eauto.
  - intros Γ body T HwfT HisAbs Hbody IHbody c G' HIns. simpl.
    apply T_LtLam.
    + eapply ty_wf_InsTy; [exact HwfT|]. apply InsTy_lt. exact HIns.
    + rewrite is_abs_shift_ty_in_tm. exact HisAbs.
    + apply IHbody. apply InsTy_lt. exact HIns.
  - intros Γ t T l Ht IHt Hwfl c G' HIns. simpl.
    rewrite shift_ty_subst_lt_in_ty_commute.
    eapply T_LtApp.
    + apply IHt. exact HIns.
    + eapply lt_wf_InsTy; eauto.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
           Hctor Heff Hlts Hwflts Hrho HTs HwfTs Hresult Hshape Hresult_eff Hwfl Hlt Hbounded Hlen Hargs IHargs c G' HIns.
    simpl. unfold shift_ty_list. rewrite shift_ty_in_tm_go_eq_map.
    eapply T_Ctor with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := List.map (shift_ty 1 (n_ty + c)) sigma_fields)
      (result_ty_schema := shift_ty 1 (n_ty + c) result_ty_schema)
      (rho_fields := List.map (shift_ty 1 c) rho_fields)
      (result_tag := result_tag).
    + rewrite (InsTy_lookup_ctor c Γ G' HIns K). rewrite Hctor. reflexivity.
    + rewrite (InsTy_lookup_eff c Γ G' HIns K). rewrite Heff. reflexivity.
    + exact Hlts.
    + eapply lifetimes_wf_InsTy; eauto.
    + rewrite Hrho. rewrite !List.map_map. apply List.map_ext. intro sigma.
      exact (eq_sym (inst_ctor_type_shift_ty n_lt n_ty lts Ts sigma c HTs)).
    + rewrite List.length_map. exact HTs.
    + eapply types_wf_InsTy; eauto.
    + rewrite Hresult.
      exact (eq_sym (inst_ctor_type_shift_ty n_lt n_ty lts Ts result_ty_schema c HTs)).
    + rewrite Hshape. reflexivity.
    + rewrite (InsTy_lookup_eff c Γ G' HIns result_tag). rewrite Hresult_eff. reflexivity.
    + eapply lt_wf_InsTy; eauto.
    + rewrite (lt_of_ty_list_shift_ty rho_fields c).
      apply (lt_sub_InsTy Γ (lt_of_ty_list rho_fields) l Hlt c G' HIns).
    + eapply Forall_impl; [|exact Hbounded]. intros l0 Hsub.
      apply (lt_sub_InsTy Γ l0 l Hsub c G' HIns).
    + rewrite !List.length_map. exact Hlen.
    + apply (Forall2_typing_InsTy Γ vs rho_fields IHargs c G' HIns).
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γyes yes_body eta elim_result no_body
           Hneq Hctor Heff Hlts Hrho HTs HwfTs Hscrut_result Hscrut_shape Hresult_eff Hresult_ne
           HwfDelta Hresult_l Hscrut IHscrut Harity HΓyes Hyes IHyes Helim Hno IHno c G' HIns.
    simpl. unfold shift_ty_list. subst Γyes.
    eapply T_Match with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := List.map (shift_ty 1 (n_ty + c)) sigma_fields)
      (result_ty_schema := shift_ty 1 (n_ty + c) result_ty_schema)
      (lts := lts) (rho_fields := List.map (shift_ty 1 c) rho_fields)
      (scrut_result_ty := shift_ty 1 c scrut_result_ty)
      (result_tag := result_tag) (result_l := result_l)
      (Γ' := push_lt_vars n_lt Delta G') (eta := shift_ty 1 c eta).
    + exact Hneq.
    + rewrite (InsTy_lookup_ctor c Γ G' HIns K). rewrite Hctor. reflexivity.
    + rewrite (InsTy_lookup_eff c Γ G' HIns K). rewrite Heff. reflexivity.
    + exact Hlts.
    + rewrite Hrho. rewrite !List.map_map. apply List.map_ext. intro sigma.
      exact (eq_sym (inst_ctor_type_shift_ty n_lt n_ty lts Ts sigma c HTs)).
    + rewrite List.length_map. exact HTs.
    + eapply types_wf_InsTy; eauto.
    + rewrite Hscrut_result.
      exact (eq_sym (inst_ctor_type_shift_ty n_lt n_ty (List.repeat Delta n_lt) Ts result_ty_schema c HTs)).
    + rewrite Hscrut_shape. reflexivity.
    + rewrite (InsTy_lookup_eff c Γ G' HIns result_tag). rewrite Hresult_eff. reflexivity.
    + exact Hresult_ne.
    + eapply lt_wf_InsTy; eauto.
    + apply (lt_sub_InsTy Γ result_l Delta Hresult_l c G' HIns).
    + apply IHscrut. exact HIns.
    + rewrite List.length_map. exact Harity.
    + reflexivity.
    + apply IHyes.
      rewrite fold_bind_tm_shift_ty_map.
      apply InsTy_fold_bind_tm.
      apply InsTy_push_lt_vars. exact HIns.
    + apply elim_ty_n_shift_ty. exact Helim.
    + apply IHno. exact HIns.
  - intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff HTs HwfTs HwfTR Hsig Hret Hop IHop c G' HIns.
    simpl. rewrite shift_ty_go_eq_map. unfold shift_ty_list.
    eapply T_Cap with
      (n_α := n_α) (n_β := n_β)
      (sig := shift_ty 1 (n_α + n_β + c) sig)
      (ret := shift_ty 1 (n_α + n_β + c) ret)
      (T_R := shift_ty 1 c T_R)
      (sig_β := shift_ty 1 (n_β + c) sig_β)
      (ret_β := shift_ty 1 (n_β + c) ret_β).
    + rewrite (InsTy_lookup_eff c Γ G' HIns E_tag). rewrite Heff. reflexivity.
    + rewrite List.length_map. exact HTs.
    + eapply types_wf_InsTy; eauto.
    + eapply ty_wf_InsTy; eauto.
    + rewrite Hsig. symmetry. apply inst_op_alpha_shift_ty. exact HTs.
    + rewrite Hret. symmetry. apply inst_op_alpha_shift_ty. exact HTs.
    + replace (c + n_β) with (n_β + c) by lia.
      rewrite shift_ty_lift_shift.
      apply IHop.
      apply InsTy_tm. apply InsTy_tm. apply InsTy_push_ty_vars_any_at_free. exact HIns.
  - intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
           Heff HTs HwfTs HwfTB HwfTR Hnolocal Hsub Hsig Hret Hop IHop Hbody IHbody c G' HIns.
    simpl. unfold shift_ty_list.
    eapply T_Handle with
      (n_α := n_α) (n_β := n_β)
      (sig := shift_ty 1 (n_α + n_β + c) sig)
      (ret := shift_ty 1 (n_α + n_β + c) ret)
      (T_B := shift_ty 1 c T_B)
      (T_R := shift_ty 1 c T_R)
      (sig_β := shift_ty 1 (n_β + c) sig_β)
      (ret_β := shift_ty 1 (n_β + c) ret_β).
    + rewrite (InsTy_lookup_eff c Γ G' HIns E_tag). rewrite Heff. reflexivity.
    + rewrite List.length_map. exact HTs.
    + eapply types_wf_InsTy; eauto.
    + eapply ty_wf_InsTy; eauto.
    + eapply ty_wf_InsTy; eauto.
    + eapply no_local_ty_G_InsTy; eauto.
    + apply (sub_InsTy Γ T_B T_R Hsub c G' HIns).
    + rewrite Hsig. symmetry. apply inst_op_alpha_shift_ty. exact HTs.
    + rewrite Hret. symmetry. apply inst_op_alpha_shift_ty. exact HTs.
    + replace (c + n_β) with (n_β + c) by lia.
      rewrite shift_ty_lift_shift.
      apply IHop.
      apply InsTy_tm. apply InsTy_tm. apply InsTy_push_ty_vars_any_at_free. exact HIns.
    + apply IHbody. apply InsTy_tm. exact HIns.
  - intros Γ recv arg E_tag Delta Ts Ss n_α n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff HTs HSs HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg c G' HIns.
    simpl. unfold shift_ty_list.
    eapply T_Perform with
      (n_α := n_α) (n_β := n_β)
      (sig := shift_ty 1 (n_α + n_β + c) sig)
      (ret := shift_ty 1 (n_α + n_β + c) ret)
      (sig_inst := shift_ty 1 c sig_inst)
      (ret_inst := shift_ty 1 c ret_inst).
    + apply IHrecv. exact HIns.
    + rewrite (InsTy_lookup_eff c Γ G' HIns E_tag). rewrite Heff. reflexivity.
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
    + eapply types_wf_InsTy; eauto.
    + eapply forallb_no_local_ty_G_InsTy; eauto.
    + rewrite !shift_ty_go_eq_map. rewrite Hsig. symmetry. apply inst_op_arg_shift_ty; assumption.
    + eapply no_local_ty_G_InsTy; eauto.
    + rewrite !shift_ty_go_eq_map. rewrite Hret. symmetry. apply inst_op_arg_shift_ty; assumption.
    + eapply ty_wf_InsTy; eauto.
    + apply IHarg. exact HIns.
  - intros Γ m T_B T_R t HwfTB HwfTR Hnolocal Hsub Ht IH c G' HIns. simpl.
    apply T_HandlerM.
    + eapply ty_wf_InsTy; eauto.
    + eapply ty_wf_InsTy; eauto.
    + eapply no_local_ty_G_InsTy; eauto.
    + apply (sub_InsTy Γ T_B T_R Hsub c G' HIns).
    + apply IH. exact HIns.
  - intros Γ m b A T_B T_R HwfA HwfTB HwfTR Hnolocal Hsub Hb IHb c G' HIns. simpl.
    apply T_Resume.
    + eapply ty_wf_InsTy; eauto.
    + eapply ty_wf_InsTy; eauto.
    + eapply ty_wf_InsTy; eauto.
    + eapply no_local_ty_G_InsTy; eauto.
    + apply (sub_InsTy Γ T_B T_R Hsub c G' HIns).
    + apply IHb. apply InsTy_tm. exact HIns.
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
  rewrite (inst_ty_vars_shift_lt n_ty (List.map (shift_lt_in_ty n_lt 0) Ts) T (n_lt + c)).
  2:{ rewrite List.length_map. exact Hlen_Ts. }
  rewrite multi_subst_lt_in_ty_shift_lt_comm with (k := n_lt) by exact Hlen_lts.
  replace (0 + c) with c by lia.
  reflexivity.
Qed.

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

Lemma inst_op_alpha_subst_lt : forall n_α Ts n_β T l R,
  inst_op_alpha n_α (List.map (subst_lt_in_ty l R) Ts) n_β (subst_lt_in_ty l R T) =
  subst_lt_in_ty l R (inst_op_alpha n_α Ts n_β T).
Proof.
  intros n_α Ts n_β T l R. unfold inst_op_alpha.
  rewrite <- inst_ty_vars_subst_lt.
  f_equal.
  induction Ts as [|T0 Ts IH]; simpl.
  - reflexivity.
  - rewrite shift_ty_subst_lt_in_ty_commute. f_equal. exact IH.
Qed.

Lemma inst_op_arg_subst_lt : forall n_α Ts n_β Ss T l R,
  inst_op_arg n_α (List.map (subst_lt_in_ty l R) Ts)
              n_β (List.map (subst_lt_in_ty l R) Ss)
              (subst_lt_in_ty l R T) =
  subst_lt_in_ty l R (inst_op_arg n_α Ts n_β Ss T).
Proof.
  intros n_α Ts n_β Ss T l R. unfold inst_op_arg.
  rewrite <- inst_ty_vars_subst_lt.
  rewrite inst_op_alpha_subst_lt.
  reflexivity.
Qed.

Lemma inst_op_alpha_shift_lt : forall n_α Ts n_β T c,
  List.length Ts = n_α ->
  inst_op_alpha n_α (List.map (shift_lt_in_ty 1 c) Ts) n_β
    (shift_lt_in_ty 1 c T) =
  shift_lt_in_ty 1 c (inst_op_alpha n_α Ts n_β T).
Proof.
  intros n_α Ts n_β T c Hlen. unfold inst_op_alpha.
  replace (List.map (shift_ty n_β 0) (List.map (shift_lt_in_ty 1 c) Ts)) with
    (List.map (shift_lt_in_ty 1 c) (List.map (shift_ty n_β 0) Ts)).
  - rewrite inst_ty_vars_shift_lt by (rewrite List.length_map; exact Hlen).
    reflexivity.
  - rewrite !List.map_map. apply List.map_ext. intro U.
    symmetry. apply shift_ty_shift_lt_in_ty_commute.
Qed.

Lemma inst_op_arg_shift_lt : forall n_α Ts n_β Ss T c,
  List.length Ts = n_α ->
  List.length Ss = n_β ->
  inst_op_arg n_α (List.map (shift_lt_in_ty 1 c) Ts)
    n_β (List.map (shift_lt_in_ty 1 c) Ss)
    (shift_lt_in_ty 1 c T) =
  shift_lt_in_ty 1 c (inst_op_arg n_α Ts n_β Ss T).
Proof.
  intros n_α Ts n_β Ss T c HlenTs HlenSs. unfold inst_op_arg.
  rewrite inst_op_alpha_shift_lt by exact HlenTs.
  rewrite inst_ty_vars_shift_lt by exact HlenSs.
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

(* ================================================================== *)
(* SubstTy : substitute a type for a ty-binder at depth n             *)
(* ================================================================== *)

Lemma lt_min_mono : forall G a1 a2 b1 b2,
  G ⊢ₗ a1 <: a2 -> G ⊢ₗ b1 <: b2 -> G ⊢ₗ lt_min a1 b1 <: lt_min a2 b2.
Proof.
  intros G a1 a2 b1 b2 Ha Hb.
  destruct (lt_sub_wf _ _ _ Ha) as [_ Hwfa2].
  destruct (lt_sub_wf _ _ _ Hb) as [_ Hwfb2].
  apply LS_MinL.
  - eapply LS_Trans; [exact Ha |].
    apply LS_MinR1.
    + apply LS_Refl. exact Hwfa2.
    + exact Hwfb2.
  - eapply LS_Trans; [exact Hb |].
    apply LS_MinR2.
    + apply LS_Refl. exact Hwfb2.
    + exact Hwfa2.
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
      (bind_lt D :: G')
| SubstTy_tm : forall Sb n G G' A,
  SubstTy Sb n G G' ->
  SubstTy Sb n
      (bind_tm A :: G)
      (bind_tm (subst_ty n Sb A) :: G').

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
  - exact IHSubstTy.
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
  - apply IHSubstTy. exact Hne.
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
  - apply IHSubstTy.
Qed.

Lemma lt_wf_SubstTy_ctx : forall G l,
  lt_wf G l -> forall Sb n G', SubstTy Sb n G G' -> lt_wf G' l.
Proof.
  intros G l Hwf. induction Hwf; intros Sb n G' HS.
  - econstructor. rewrite (SubstTy_lookup_lt Sb n Γ G' HS x). exact H.
  - constructor.
  - constructor.
  - constructor.
    + apply (IHHwf1 Sb n G' HS).
    + apply (IHHwf2 Sb n G' HS).
Qed.

Lemma lt_sub_SubstTy_ctx : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall Sb n G', SubstTy Sb n G G' -> G' ⊢ₗ l1 <: l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l Hwf|Γ l Hwf|Γ x Δ Hlk HwfD|Γ l Hwf
                 |Γ l1 l2 l3 H1 IH1 H2 IH2|Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H1 IH1 Hwf2|Γ l l1 l2 H1 IH1 Hwf1];
    intros Sb n G' HS.
  - apply LS_Free. eapply lt_wf_SubstTy_ctx; eauto.
  - apply LS_Local. eapply lt_wf_SubstTy_ctx; eauto.
  - apply LS_Var.
    + rewrite (SubstTy_lookup_lt Sb n Γ G' HS x). exact Hlk.
    + eapply lt_wf_SubstTy_ctx; eauto.
  - apply LS_Refl. eapply lt_wf_SubstTy_ctx; eauto.
  - eapply LS_Trans; [apply (IH1 Sb n G' HS) | apply (IH2 Sb n G' HS)].
  - apply LS_MinL; [apply (IH1 Sb n G' HS) | apply (IH2 Sb n G' HS)].
  - apply LS_MinR1.
    + apply (IH1 Sb n G' HS).
    + eapply lt_wf_SubstTy_ctx; eauto.
  - apply LS_MinR2.
    + apply (IH1 Sb n G' HS).
    + eapply lt_wf_SubstTy_ctx; eauto.
Qed.

Lemma lt_of_ty_G_wf : forall G T,
  ty_wf G T -> lt_wf G (lt_of_ty_G G T)
with lt_of_ty_G_list_wf : forall G Ts,
  types_wf G Ts -> lt_wf G (lt_of_ty_ctx_list (List.length G) G Ts).
Proof.
  - intros G T Hwf.
    induction Hwf as [Γ α B Hlk HwfB IHBound
                     |Γ A l B HwfA IHA Hwfl HwfB IHB
                     |Γ K l Ts Hwfl HwfTs IHTs
                     |Γ A HwfA IHA
                     |Γ B A HwfB IHB HwfA IHA].
    + unfold lt_of_ty_G.
      assert (Hlt: α < length Γ).
      { destruct (Nat.le_gt_cases (length Γ) α) as [Hle|Hgt]; [|exact Hgt].
        rewrite ctx_lookup_ty_None in Hlk by exact Hle. discriminate. }
      rewrite (lt_of_ty_ctx_var (length Γ) Γ α).
      destruct (length Γ) as [|m] eqn:HL; [lia|].
      rewrite Hlk.
      rewrite (lt_of_ty_ctx_fuel_irrel m (S m) B Γ (S α)
                 (ctx_inv_all Γ α B Hlk) ltac:(lia) ltac:(lia)).
      unfold lt_of_ty_G in IHBound. rewrite HL in IHBound. exact IHBound.
    + unfold lt_of_ty_G. rewrite lt_of_ty_ctx_fun. exact Hwfl.
    + unfold lt_of_ty_G. rewrite lt_of_ty_ctx_ctor. constructor.
      * exact Hwfl.
      * eapply lt_of_ty_G_list_wf; eauto.
    + unfold lt_of_ty_G. rewrite lt_of_ty_ctx_ltall. constructor.
    + unfold lt_of_ty_G. rewrite lt_of_ty_ctx_tyall. constructor.
  - intros G Ts Hwf.
    induction Hwf.
    + rewrite lt_of_ty_ctx_list_nil. constructor.
    + rewrite lt_of_ty_ctx_list_cons. constructor.
      * change (lt_wf Γ (lt_of_ty_G Γ T)). eapply lt_of_ty_G_wf; eauto.
      * assumption.
Qed.

Lemma lt_of_ty_G_mono_sub : forall G T1 T2, G ⊢ T1 <:: T2 ->
  G ⊢ₗ lt_of_ty_G G T1 <: lt_of_ty_G G T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T Hwf|Γ S0 U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                 |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                 |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2].
  - apply LS_Refl. apply lt_of_ty_G_wf. exact Hwf.
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
    apply LS_Refl. rewrite <- HL. apply lt_of_ty_G_wf. exact HwfB.
  - unfold lt_of_ty_G. rewrite !lt_of_ty_ctx_ctor.
    apply lt_min_mono; [exact Hls |].
    apply LS_Refl. eapply lt_of_ty_G_list_wf; eauto.
  - replace (lt_of_ty_G Γ (type_ctor any_tag Δ [])) with (lt_min Δ lt_free).
    + eapply LS_Trans; [exact Hls |].
      apply LS_MinR1.
      * apply LS_Refl. exact HwfD.
      * constructor.
    + unfold lt_of_ty_G. rewrite lt_of_ty_ctx_ctor, lt_of_ty_ctx_list_nil. reflexivity.
  - unfold lt_of_ty_G. rewrite !lt_of_ty_ctx_fun. exact Hl.
  - unfold lt_of_ty_G. rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
  - unfold lt_of_ty_G. rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
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
  - destruct IHSubstTy as [B0 [Hlk Hsub]].
    exists B0. split.
    + simpl ctx_lookup_ty. exact Hlk.
    + rewrite lt_of_ty_G_weaken_tm. rewrite lt_of_ty_G_weaken_tm.
      apply (lt_sub_InsTm G' (lt_of_ty_G G' Sb) (lt_of_ty_G G B0) Hsub
               (bind_tm (subst_ty n Sb A) :: G') (InsTm_here _ _)).
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
  - simpl in HB. apply IHSubstTy in HB.
    apply (sub_InsTm G' Sb (subst_ty n Sb B0) HB
             (bind_tm (subst_ty n Sb A) :: G') (InsTm_here _ _)).
Qed.

Lemma SubstTy_replacement_wf : forall Sb n G G',
  SubstTy Sb n G G' -> ty_wf G' Sb.
Proof.
  intros Sb n G G' H. induction H.
  - destruct (sub_wf _ _ _ H) as [HwfSb _]. exact HwfSb.
  - eapply ty_wf_InsTy; [exact IHSubstTy|]. apply InsTy_here.
  - eapply ty_wf_InsLt; [exact IHSubstTy|]. apply InsLt_here.
  - eapply ty_wf_InsTm; [exact IHSubstTy|]. apply InsTm_here.
Qed.

Lemma ty_wf_SubstTy : forall G T,
  ty_wf G T -> forall Sb n G', SubstTy Sb n G G' -> ty_wf G' (subst_ty n Sb T)
with types_wf_SubstTy : forall G Ts,
  types_wf G Ts -> forall Sb n G', SubstTy Sb n G G' ->
    types_wf G' (List.map (subst_ty n Sb) Ts).
Proof.
  - intros G T Hwf. induction Hwf; intros Sb n G' HS.
    + destruct (Nat.eq_dec α n) as [Hα|Hα].
      * subst α. rewrite subst_ty_var_eq, Nat.eqb_refl.
        eapply SubstTy_replacement_wf; eauto.
      * rewrite (subst_ty_var_neq n Sb α Hα). econstructor.
        -- rewrite (SubstTy_lookup_ty Sb n Γ G' HS α Hα). rewrite H. reflexivity.
        -- apply (IHHwf Sb n G' HS).
    + rewrite subst_ty_fun_eq. constructor.
      * apply IHHwf1. exact HS.
      * eapply lt_wf_SubstTy_ctx; eauto.
      * apply IHHwf2. exact HS.
    + rewrite subst_ty_ctor_eq. constructor.
      * eapply lt_wf_SubstTy_ctx; eauto.
      * eapply types_wf_SubstTy; eauto.
    + rewrite subst_ty_ltall_eq. constructor.
      apply IHHwf. apply SubstTy_lt. exact HS.
    + rewrite subst_ty_tyall_eq. constructor.
      * apply IHHwf1. exact HS.
      * apply IHHwf2. apply SubstTy_ty. exact HS.
  - intros G Ts Hwf. induction Hwf; intros Sb n G' HS; cbn [List.map].
    + constructor.
    + constructor.
      * eapply ty_wf_SubstTy; eauto.
      * apply (IHHwf Sb n G' HS).
Qed.

Lemma lt_of_ty_ctx_SubstTy_le : forall Sb n G G', SubstTy Sb n G G' ->
  forall f T k, ty_wf G T -> VB k T -> length G <= k + f ->
  G' ⊢ₗ lt_of_ty_ctx f G' (subst_ty n Sb T) <: lt_of_ty_ctx f G T.
Proof.
  intros Sb n G G' HS.
  pose proof (SubstTy_n_lt Sb n G G' HS) as Hn.
  pose proof (SubstTy_S_VB Sb n G G' HS) as HSVB.
  pose proof (SubstTy_length Sb n G G' HS) as HLen.
  destruct (SubstTy_target Sb n G G' HS) as [Btgt [Htgt Hsubtgt]].
  induction f as [|f' IHf]; intros T k HwfT HVB Hlen.
  - rewrite Nat.add_0_r in Hlen. revert k HwfT HVB Hlen.
    induction T using type_list_ind with
      (Q := fun Ts => forall k, types_wf G Ts -> VBL k Ts -> length G <= k ->
              G' ⊢ₗ lt_of_ty_ctx_list 0 G' (List.map (subst_ty n Sb) Ts)
                  <: lt_of_ty_ctx_list 0 G Ts);
      intros k HwfT HVB Hlen.
    + simpl in HVB.
      assert (Hane : n0 <> n) by lia.
      rewrite (subst_ty_var_neq n Sb n0 Hane).
      rewrite !(lt_of_ty_ctx_var 0). apply LS_Refl. constructor.
    + inversion HwfT; subst.
      rewrite subst_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. apply LS_Refl.
      eapply lt_wf_SubstTy_ctx; eauto.
    + rewrite subst_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor.
      inversion HwfT; subst. rewrite VB_ctor in HVB.
      apply lt_min_mono.
      * apply LS_Refl. eapply lt_wf_SubstTy_ctx; eauto.
      * eapply IHT; eauto.
    + rewrite subst_ty_ltall_eq. rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + rewrite subst_ty_tyall_eq. rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + rewrite VBL_cons in HVB. destruct HVB as [Ha Hr].
      inversion HwfT; subst.
      cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons.
      apply lt_min_mono; [eapply IHT; eauto | eapply IHT0; eauto].
  - revert k HwfT HVB Hlen.
    induction T using type_list_ind with
      (Q := fun Ts => forall k, types_wf G Ts -> VBL k Ts -> length G <= k + S f' ->
              G' ⊢ₗ lt_of_ty_ctx_list (S f') G' (List.map (subst_ty n Sb) Ts)
                  <: lt_of_ty_ctx_list (S f') G Ts);
      intros k HwfT HVB Hlen.
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
        -- assert (HwfB0 : ty_wf G B0).
           { inversion HwfT; subst.
             match goal with
             | Hlookup : ctx_lookup_ty G n0 = Some ?B,
               Hbound : ty_wf G ?B |- _ =>
                 rewrite E in Hlookup; inversion Hlookup; subst; exact Hbound
             end. }
           apply (IHf B0 (S n0) HwfB0 (ctx_inv_all G n0 B0 E)). lia.
        -- apply LS_Refl. constructor.
    + inversion HwfT; subst.
      rewrite subst_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. apply LS_Refl.
      eapply lt_wf_SubstTy_ctx; eauto.
    + rewrite subst_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor.
      inversion HwfT; subst. rewrite VB_ctor in HVB.
      apply lt_min_mono.
      * apply LS_Refl. eapply lt_wf_SubstTy_ctx; eauto.
      * eapply IHT; eauto.
    + rewrite subst_ty_ltall_eq. rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + rewrite subst_ty_tyall_eq. rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + rewrite VBL_cons in HVB. destruct HVB as [Ha Hr].
      inversion HwfT; subst.
      cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons.
      apply lt_min_mono; [eapply IHT; eauto | eapply IHT0; eauto].
Qed.

Lemma lt_of_ty_G_SubstTy_le : forall Sb n G G', SubstTy Sb n G G' ->
  forall T, ty_wf G T -> G' ⊢ₗ lt_of_ty_G G' (subst_ty n Sb T) <: lt_of_ty_G G T.
Proof.
  intros Sb n G G' HS T HwfT. unfold lt_of_ty_G.
  pose proof (SubstTy_length Sb n G G' HS) as HL.
  rewrite (lt_of_ty_ctx_fuel_irrel (length G') (length G)
             (subst_ty n Sb T) G' 0 (VB_0 _) ltac:(lia) ltac:(lia)).
  apply (lt_of_ty_ctx_SubstTy_le Sb n G G' HS (length G) T 0 HwfT (VB_0 T) ltac:(lia)).
Qed.

Lemma sub_SubstTy : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall Sb n G', SubstTy Sb n G G' ->
  G' ⊢ subst_ty n Sb T1 <:: subst_ty n Sb T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T Hwf|Γ S0 U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                 |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                 |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2];
    intros Sb n G' HS.
  - apply SA_Refl. eapply ty_wf_SubstTy; eauto.
  - eapply SA_Trans; [apply (IH1 Sb n G' HS) | apply (IH2 Sb n G' HS)].
  - destruct (Nat.eq_dec α n) as [Hae|Hane].
    + subst α. rewrite subst_ty_var_eq, Nat.eqb_refl.
      apply (SubstTy_sub_target Sb n Γ G' HS B Hlk).
    + rewrite (subst_ty_var_neq n Sb α Hane). apply SA_VarCtx.
      * rewrite (SubstTy_lookup_ty Sb n Γ G' HS α Hane). rewrite Hlk. reflexivity.
      * eapply ty_wf_SubstTy; eauto.
  - rewrite !subst_ty_ctor_eq. apply SA_Data.
    + apply (lt_sub_SubstTy_ctx Γ l l' Hls Sb n G' HS).
    + eapply types_wf_SubstTy; eauto.
  - rewrite subst_ty_ctor_eq. cbn [List.map]. apply SA_Any.
    + eapply ty_wf_SubstTy; eauto.
    + eapply lt_wf_SubstTy_ctx; eauto.
    + eapply LS_Trans.
      * apply (lt_of_ty_G_SubstTy_le Sb n Γ G' HS T HwfT).
      * apply (lt_sub_SubstTy_ctx Γ (lt_of_ty_G Γ T) Δ Hls Sb n G' HS).
  - rewrite !subst_ty_fun_eq. apply SA_Fun.
    + apply (IH1 Sb n G' HS).
    + apply (lt_sub_SubstTy_ctx Γ l l' Hl Sb n G' HS).
    + apply (IH2 Sb n G' HS).
  - rewrite !subst_ty_ltall_eq. apply SA_LtAll.
    apply (IH1 (shift_lt_in_ty 1 0 Sb) n (bind_lt lt_local :: G')
             (SubstTy_lt Sb n Γ G' lt_local HS)).
  - rewrite !subst_ty_tyall_eq. apply SA_TyAll.
    + eapply ty_wf_SubstTy; [exact HwfA|]. apply SubstTy_ty. exact HS.
    + eapply ty_wf_SubstTy; [exact HwfA'|]. apply SubstTy_ty. exact HS.
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

(* ---- Substitution preservation (typing) ------------------------ *)

(* Shifting a term-closed value leaves it term-closed.  Used to keep   *)
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

(* ================================================================== *)
(* Evaluation contexts (program-level typing contexts).               *)
(*                                                                    *)
(* An `eval_ctx` contains ONLY constructor/effect bindings: no        *)
(* `bind_tm`, `bind_ty`, or `bind_lt`.  Consequently a term typed     *)
(* under an `eval_ctx` has no free term, type, or lifetime variables  *)
(* (it is fully closed).  This is exactly the invariant the term      *)
(* substitution lemma needs: the value being inlined is fully closed, *)
(* so the cross-binder shifts performed by `subst_tm` (which does NOT *)
(* re-shift the value across the lifetime/type binders introduced by  *)
(* `term_match` / `term_cap` / `term_handle`) act as the identity and *)
(* the statement is sound.                                            *)
(*                                                                    *)
(* `eval_ctx` lives here (rather than in `Safety.v`) so that          *)
(* `subst_tm_lemma` can be stated directly in terms of the real       *)
(* program-level invariant.                                           *)
(* ================================================================== *)
Inductive eval_ctx : ctx -> Prop :=
  | ec_nil   : eval_ctx []
  | ec_ctor  : forall K n_lt n_ty f r Γ,
    eval_ctx Γ -> eval_ctx (bind_ctor K n_lt n_ty f r :: Γ)
  | ec_eff   : forall E n_α n_β sig ret Γ,
    E <> any_tag ->
    eval_ctx Γ -> eval_ctx (bind_eff E n_α n_β sig ret :: Γ).

Lemma eval_ctx_no_tm : forall Γ x,
  eval_ctx Γ -> ctx_lookup_tm Γ x = None.
Proof.
  intros Γ x H; revert x; induction H; intros x; simpl; try reflexivity.
  - rewrite IHeval_ctx; reflexivity.
  - rewrite IHeval_ctx; reflexivity.
Qed.

Lemma eval_ctx_no_ty : forall Γ α,
  eval_ctx Γ -> ctx_lookup_ty Γ α = None.
Proof.
  intros Γ α H; revert α; induction H; intros α; simpl; try reflexivity.
  - rewrite IHeval_ctx; reflexivity.
  - rewrite IHeval_ctx; reflexivity.
Qed.

Lemma eval_ctx_no_lt : forall Γ x,
  eval_ctx Γ -> ctx_lookup_lt Γ x = None.
Proof.
  intros Γ x H; revert x; induction H; intros x; simpl; try reflexivity.
  - rewrite IHeval_ctx; reflexivity.
  - rewrite IHeval_ctx; reflexivity.
Qed.

(* The reserved Any tag is never registered as an effect in an        *)
(* `eval_ctx`: `ec_eff` forbids `E = any_tag`.                         *)
Lemma eval_ctx_no_eff_any : forall Γ,
  eval_ctx Γ -> ctx_lookup_eff Γ any_tag = None.
Proof.
  intros Γ H; induction H.
  - reflexivity.
  - cbn [ctx_lookup_eff]. exact IHeval_ctx.
  - cbn [ctx_lookup_eff].
    assert (Nat.eqb any_tag E = false) as ->.
    { apply Nat.eqb_neq. congruence. }
    exact IHeval_ctx.
Qed.

Lemma typing_implies_wf : forall Γ t T,
  Γ ⊢ₜ t : T -> ty_wf Γ T.
Proof.
  apply (typing_ind_forall2 (fun Γ t T => ty_wf Γ T)).
  - intros Γ x T Hlk HwfT. exact HwfT.
  - intros Γ t T U Ht IH Hsub.
    destruct (sub_wf _ _ _ Hsub) as [_ HwfU]. exact HwfU.
  - intros Γ body A l B HwfA HwfB Hbody IH Hcap.
    destruct (lt_sub_wf _ _ _ Hcap) as [_ Hwfl]. constructor; assumption.
  - intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2.
    inversion IH1; subst. assumption.
  - intros Γ bound body T HwfBound HwfT Hbody IHbody.
    constructor; assumption.
  - intros Γ t B U S Ht IH HwfS Hsub HnlArg.
    inversion IH; subst.
    eapply ty_wf_SubstTy; [exact H3|]. apply SubstTy_here. exact Hsub.
  - intros Γ body T HwfT Hbody IHbody.
    constructor. exact HwfT.
  - intros Γ t T l Ht IH Hwfl.
    inversion IH; subst.
    eapply ty_wf_SubstLt; [exact H1|].
    apply SubstLt_here. apply LS_Local. exact Hwfl.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
           Hlk Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs Hresult Hshape
           Hresult_eff Hwfl Hlt Hforall Hlen_vs Hfields IHfields.
            rewrite Hshape. constructor; assumption.
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γ' yes_body eta
           elim_result no_body HKne Hlk Heff Hlts Hrho Hlen_Ts HwfTs
           Hscrut_result Hscrut_shape Hresult_eff Hresult_ne HwfDelta Hresult_l Hscrut IHscrut
           Harity HGamma' Hyes IHyes Helim Hno IHno.
    exact IHno.
  - intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff Hlen HwfTs HwfTR Hsig Hret Hop IHop.
    constructor; [constructor|exact HwfTs].
  - intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hsig Hret Hop IHop Hbody IHbody.
    exact HwfTR.
  - intros Γ recv arg E_tag Δ Ts Ss n_α n_β sig ret sig_inst ret_inst
      Hrecv IHrecv Heff Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg.
    exact HwfRet.
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH. exact HwfTR.
  - intros Γ m b A T_B T_R HwfA HwfTB HwfTR HnoLocal Hsub Hb IHb.
    constructor; [exact HwfA|constructor|exact HwfTR].
Qed.

(* ================================================================== *)
(* typing_SubstTy : type-substitution preserves typing.               *)
(* Discharges `subst_ty_in_tm_lemma` (it is the depth-0 instance with  *)
(* `SubstTy_here`).  Mirrors `typing_InsTy`, swapping shift→subst.     *)
(* ================================================================== *)

(* ---- schema-level type substitution ---- *)
(* A ctor schema's fields/result live under n_lt lifetime binders then  *)
(* n_ty type binders, so the replacement type must be lifted past both. *)
Definition subst_ty_ctor_sig (n : nat) (Sb : type)
    (sig : nat * nat * list type * type) : nat * nat * list type * type :=
  let '(n_lt, n_ty, fields, result) := sig in
  let Sb' := shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb) in
  (n_lt, n_ty,
   List.map (subst_ty (n_ty + n) Sb') fields,
   subst_ty (n_ty + n) Sb' result).

(* An effect schema's sig/ret live under n_α + n_β type binders only.   *)
Definition subst_ty_eff_sig (n : nat) (Sb : type)
    (sig : nat * nat * type * type) : nat * nat * type * type :=
  let '(n_α, n_β, sig_ty, ret_ty) := sig in
  let Sb' := shift_ty (n_α + n_β) 0 Sb in
  (n_α, n_β,
   subst_ty (n_α + n_β + n) Sb' sig_ty,
   subst_ty (n_α + n_β + n) Sb' ret_ty).

Lemma subst_ty_eff_sig_shift_cancel : forall Sb sig,
  subst_ty_eff_sig 0 Sb (shift_ty_eff_sig 1 0 sig) = sig.
Proof.
  intros Sb (((n_α, n_β), sig_ty), ret_ty).
  unfold subst_ty_eff_sig, shift_ty_eff_sig. simpl.
  rewrite !subst_ty_shift_cancel. reflexivity.
Qed.

Lemma subst_ty_ctor_sig_shift_cancel : forall Sb sig,
  subst_ty_ctor_sig 0 Sb (shift_ty_ctor_sig 1 0 sig) = sig.
Proof.
  intros Sb (((n_lt, n_ty), fields), result).
  unfold subst_ty_ctor_sig, shift_ty_ctor_sig. simpl.
  assert (Hfields :
    List.map (subst_ty (n_ty + 0) (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb)))
      (List.map (shift_ty 1 (n_ty + 0)) fields) = fields).
  { induction fields as [|T fields IH]; simpl.
    - reflexivity.
    - rewrite subst_ty_shift_cancel. f_equal. exact IH. }
  rewrite Hfields, subst_ty_shift_cancel. reflexivity.
Qed.

Lemma shift_ty_eff_sig_subst_ty_eff_sig_comm0 : forall n Sb sig,
  shift_ty_eff_sig 1 0 (subst_ty_eff_sig n Sb sig) =
  subst_ty_eff_sig (S n) (shift_ty 1 0 Sb) (shift_ty_eff_sig 1 0 sig).
Proof.
  intros n Sb (((n_α, n_β), sig_ty), ret_ty).
  unfold subst_ty_eff_sig, shift_ty_eff_sig. simpl.
  assert (Hc : forall T,
    shift_ty 1 (n_α + n_β + 0) (subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) T)
    = subst_ty (n_α + n_β + S n) (shift_ty (n_α + n_β) 0 (shift_ty 1 0 Sb))
        (shift_ty 1 (n_α + n_β + 0) T)).
  { intro T. rewrite shift_ty_subst_ty_comm by lia.
    replace (S (n_α + n_β + n)) with (n_α + n_β + S n) by lia.
    f_equal. rewrite <- shift_ty_lift_shift. reflexivity. }
  rewrite !Hc. reflexivity.
Qed.

Lemma shift_ty_ctor_sig_subst_ty_ctor_sig_comm0 : forall n Sb sig,
  shift_ty_ctor_sig 1 0 (subst_ty_ctor_sig n Sb sig) =
  subst_ty_ctor_sig (S n) (shift_ty 1 0 Sb) (shift_ty_ctor_sig 1 0 sig).
Proof.
  intros n Sb (((n_lt, n_ty), fields), result).
  unfold subst_ty_ctor_sig, shift_ty_ctor_sig. simpl.
  assert (Hc : forall T,
    shift_ty 1 (n_ty + 0)
      (subst_ty (n_ty + n) (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb)) T)
    = subst_ty (n_ty + S n)
        (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 (shift_ty 1 0 Sb)))
        (shift_ty 1 (n_ty + 0) T)).
  { intro T. rewrite shift_ty_subst_ty_comm by lia.
    replace (S (n_ty + n)) with (n_ty + S n) by lia.
    f_equal. rewrite shift_ty_shift_lt_in_ty_commute.
    f_equal. rewrite <- shift_ty_lift_shift. reflexivity. }
  rewrite !List.map_map.
  f_equal; [f_equal | exact (Hc result)].
  apply List.map_ext. exact Hc.
Qed.

Lemma shift_lt_eff_sig_subst_ty_eff_sig_comm : forall n Sb sig,
  shift_lt_eff_sig 1 0 (subst_ty_eff_sig n Sb sig) =
  subst_ty_eff_sig n (shift_lt_in_ty 1 0 Sb) (shift_lt_eff_sig 1 0 sig).
Proof.
  intros n Sb (((n_α, n_β), sig_ty), ret_ty).
  unfold subst_ty_eff_sig, shift_lt_eff_sig. simpl.
  assert (Hc : forall T,
    shift_lt_in_ty 1 0 (subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) T)
    = subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 (shift_lt_in_ty 1 0 Sb))
        (shift_lt_in_ty 1 0 T)).
  { intro T. rewrite shift_lt_in_ty_subst_ty_comm. f_equal.
    rewrite shift_ty_shift_lt_in_ty_commute. reflexivity. }
  rewrite !Hc. reflexivity.
Qed.

Lemma shift_lt_ctor_sig_subst_ty_ctor_sig_comm : forall n Sb sig,
  shift_lt_ctor_sig 1 0 (subst_ty_ctor_sig n Sb sig) =
  subst_ty_ctor_sig n (shift_lt_in_ty 1 0 Sb) (shift_lt_ctor_sig 1 0 sig).
Proof.
  intros n Sb (((n_lt, n_ty), fields), result).
  unfold subst_ty_ctor_sig, shift_lt_ctor_sig. simpl.
  assert (Hc : forall T,
    shift_lt_in_ty 1 (n_lt + 0)
      (subst_ty (n_ty + n) (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb)) T)
    = subst_ty (n_ty + n)
        (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 (shift_lt_in_ty 1 0 Sb)))
        (shift_lt_in_ty 1 (n_lt + 0) T)).
  { intro T. rewrite shift_lt_in_ty_subst_ty_comm. f_equal.
    replace (n_lt + 0) with (0 + n_lt) by lia.
    rewrite shift_lt_in_ty_lift_many_swap.
    f_equal. rewrite shift_ty_shift_lt_in_ty_commute. reflexivity. }
  rewrite !List.map_map.
  f_equal; [f_equal | exact (Hc result)].
  apply List.map_ext. exact Hc.
Qed.

(* ---- SubstTy lookups for the remaining context entry kinds ---- *)
Lemma SubstTy_lookup_tm : forall Sb n G G', SubstTy Sb n G G' ->
  forall x, ctx_lookup_tm G' x = option_map (subst_ty n Sb) (ctx_lookup_tm G x).
Proof.
  intros Sb n G G' H. induction H; intro x.
  - simpl ctx_lookup_tm.
    destruct (ctx_lookup_tm Gamma x) as [T|]; simpl;
      [rewrite subst_ty_shift_cancel|]; reflexivity.
  - simpl ctx_lookup_tm. rewrite IHSubstTy.
    destruct (ctx_lookup_tm G x) as [T|]; simpl;
      [rewrite shift_ty_subst_ty_comm0|]; reflexivity.
  - simpl ctx_lookup_tm. rewrite IHSubstTy.
    destruct (ctx_lookup_tm G x) as [T|]; simpl;
      [rewrite shift_lt_in_ty_subst_ty_comm0|]; reflexivity.
  - destruct x as [|x']; simpl ctx_lookup_tm.
    + reflexivity.
    + apply IHSubstTy.
Qed.

Lemma SubstTy_lookup_ctor : forall Sb n G G', SubstTy Sb n G G' ->
  forall K, ctx_lookup_ctor G' K
            = option_map (subst_ty_ctor_sig n Sb) (ctx_lookup_ctor G K).
Proof.
  intros Sb n G G' H. induction H; intro K.
  - simpl ctx_lookup_ctor.
    destruct (ctx_lookup_ctor Gamma K) as [sig|]; simpl;
      [rewrite subst_ty_ctor_sig_shift_cancel|]; reflexivity.
  - simpl ctx_lookup_ctor. rewrite IHSubstTy.
    destruct (ctx_lookup_ctor G K) as [sig|] eqn:E; cbn [option_map].
    + rewrite shift_ty_ctor_sig_subst_ty_ctor_sig_comm0. reflexivity.
    + reflexivity.
  - simpl ctx_lookup_ctor. rewrite IHSubstTy.
    destruct (ctx_lookup_ctor G K) as [sig|] eqn:E; cbn [option_map].
    + rewrite shift_lt_ctor_sig_subst_ty_ctor_sig_comm. reflexivity.
    + reflexivity.
  - simpl ctx_lookup_ctor. apply IHSubstTy.
Qed.

Lemma SubstTy_lookup_eff : forall Sb n G G', SubstTy Sb n G G' ->
  forall E, ctx_lookup_eff G' E
            = option_map (subst_ty_eff_sig n Sb) (ctx_lookup_eff G E).
Proof.
  intros Sb n G G' H. induction H; intro E.
  - simpl ctx_lookup_eff.
    destruct (ctx_lookup_eff Gamma E) as [sig|]; simpl;
      [rewrite subst_ty_eff_sig_shift_cancel|]; reflexivity.
  - simpl ctx_lookup_eff. rewrite IHSubstTy.
    destruct (ctx_lookup_eff G E) as [sig|] eqn:Ef; cbn [option_map].
    + rewrite shift_ty_eff_sig_subst_ty_eff_sig_comm0. reflexivity.
    + reflexivity.
  - simpl ctx_lookup_eff. rewrite IHSubstTy.
    destruct (ctx_lookup_eff G E) as [sig|] eqn:Ef; cbn [option_map].
    + rewrite shift_lt_eff_sig_subst_ty_eff_sig_comm. reflexivity.
    + reflexivity.
  - simpl ctx_lookup_eff. apply IHSubstTy.
Qed.

(* ---- type-substitution algebra used by typing_SubstTy ---- *)
Lemma subst_ty_subst_ty_comm : forall T c n Sb U,
  c <= n ->
  subst_ty c (subst_ty n Sb U) (subst_ty (S n) (shift_ty 1 c Sb) T) =
  subst_ty n Sb (subst_ty c U T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall c n Sb U,
      c <= n ->
      subst_ty c (subst_ty n Sb U) (subst_ty (S n) (shift_ty 1 c Sb) T) =
      subst_ty n Sb (subst_ty c U T))
    (fun Ts => forall c n Sb U,
      c <= n ->
      List.map (subst_ty c (subst_ty n Sb U))
        (List.map (subst_ty (S n) (shift_ty 1 c Sb)) Ts) =
      List.map (subst_ty n Sb) (List.map (subst_ty c U) Ts))).
  - intros m c n Sb U Hle.
    destruct (Nat.eqb_spec m (S n)) as [HeqSn|HneSn].
    + subst m.
      replace (subst_ty (S n) (shift_ty 1 c Sb) (type_var (S n)))
        with (shift_ty 1 c Sb).
      2:{ rewrite subst_ty_var_eq, Nat.eqb_refl. reflexivity. }
      rewrite subst_ty_shift_cancel.
      replace (subst_ty c U (type_var (S n))) with (type_var n).
      2:{ rewrite subst_ty_var_eq.
          destruct (Nat.eqb_spec (S n) c); [lia|].
          destruct (Nat.ltb_spec c (S n)); [f_equal; lia|lia]. }
      rewrite subst_ty_var_eq, Nat.eqb_refl. reflexivity.
    + destruct (Nat.ltb_spec (S n) m) as [Hgt|Hngt].
      * replace (subst_ty (S n) (shift_ty 1 c Sb) (type_var m))
          with (type_var (pred m)).
        2:{ rewrite subst_ty_var_eq.
            destruct (Nat.eqb_spec m (S n)); [lia|].
            destruct (Nat.ltb_spec (S n) m); [reflexivity|lia]. }
        replace (subst_ty c U (type_var m)) with (type_var (pred m)).
        2:{ rewrite subst_ty_var_eq.
            destruct (Nat.eqb_spec m c); [lia|].
            destruct (Nat.ltb_spec c m); [reflexivity|lia]. }
        replace (subst_ty c (subst_ty n Sb U) (type_var (pred m)))
          with (type_var (pred (pred m))).
        2:{ rewrite subst_ty_var_eq.
            destruct (Nat.eqb_spec (pred m) c); [lia|].
            destruct (Nat.ltb_spec c (pred m)); [reflexivity|lia]. }
        replace (subst_ty n Sb (type_var (pred m)))
          with (type_var (pred (pred m))).
        2:{ rewrite subst_ty_var_eq.
            destruct (Nat.eqb_spec (pred m) n); [lia|].
            destruct (Nat.ltb_spec n (pred m)); [reflexivity|lia]. }
        reflexivity.
      * assert (Hmle : m <= n) by lia.
        destruct (Nat.eqb_spec m c) as [Heqc|Hneqc].
        -- subst m.
           replace (subst_ty (S n) (shift_ty 1 c Sb) (type_var c))
             with (type_var c).
           2:{ rewrite subst_ty_var_eq.
               destruct (Nat.eqb_spec c (S n)); [lia|].
               destruct (Nat.ltb_spec (S n) c); [lia|reflexivity]. }
           rewrite subst_ty_var_eq, Nat.eqb_refl.
           rewrite subst_ty_var_eq, Nat.eqb_refl. reflexivity.
        -- destruct (Nat.ltb_spec c m) as [Hclt|Hcge].
           ++ replace (subst_ty (S n) (shift_ty 1 c Sb) (type_var m))
                with (type_var m).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec m (S n)); [lia|].
                  destruct (Nat.ltb_spec (S n) m); [lia|reflexivity]. }
              replace (subst_ty c U (type_var m)) with (type_var (pred m)).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec m c); [lia|].
                  destruct (Nat.ltb_spec c m); [reflexivity|lia]. }
              replace (subst_ty c (subst_ty n Sb U) (type_var m))
                with (type_var (pred m)).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec m c); [lia|].
                  destruct (Nat.ltb_spec c m); [reflexivity|lia]. }
              replace (subst_ty n Sb (type_var (pred m)))
                with (type_var (pred m)).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec (pred m) n); [lia|].
                  destruct (Nat.ltb_spec n (pred m)); [lia|reflexivity]. }
              reflexivity.
           ++ replace (subst_ty (S n) (shift_ty 1 c Sb) (type_var m))
                with (type_var m).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec m (S n)); [lia|].
                  destruct (Nat.ltb_spec (S n) m); [lia|reflexivity]. }
              replace (subst_ty c U (type_var m)) with (type_var m).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec m c); [lia|].
                  destruct (Nat.ltb_spec c m); [lia|reflexivity]. }
              replace (subst_ty c (subst_ty n Sb U) (type_var m))
                with (type_var m).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec m c); [lia|].
                  destruct (Nat.ltb_spec c m); [lia|reflexivity]. }
              replace (subst_ty n Sb (type_var m)) with (type_var m).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec m n); [lia|].
                  destruct (Nat.ltb_spec n m); [lia|reflexivity]. }
              reflexivity.
  - intros A l B HA HB c n Sb U Hle.
    rewrite subst_ty_fun_eq, subst_ty_fun_eq, subst_ty_fun_eq, subst_ty_fun_eq.
    rewrite HA by exact Hle. rewrite HB by exact Hle. reflexivity.
  - intros K l Ts HTs c n Sb U Hle.
    rewrite subst_ty_ctor_eq, subst_ty_ctor_eq, subst_ty_ctor_eq, subst_ty_ctor_eq.
    f_equal. apply HTs. exact Hle.
  - intros A HA c n Sb U Hle.
    rewrite subst_ty_ltall_eq, subst_ty_ltall_eq, subst_ty_ltall_eq, subst_ty_ltall_eq.
    f_equal.
    replace (shift_lt_in_ty 1 0 (subst_ty n Sb U))
      with (subst_ty n (shift_lt_in_ty 1 0 Sb) (shift_lt_in_ty 1 0 U)).
    2:{ symmetry. apply shift_lt_in_ty_subst_ty_comm0. }
    replace (shift_lt_in_ty 1 0 (shift_ty 1 c Sb))
      with (shift_ty 1 c (shift_lt_in_ty 1 0 Sb)).
    2:{ rewrite shift_ty_shift_lt_in_ty_commute. reflexivity. }
    rewrite HA by exact Hle. reflexivity.
  - intros B A HB HA c n Sb U Hle.
    rewrite subst_ty_tyall_eq, subst_ty_tyall_eq, subst_ty_tyall_eq, subst_ty_tyall_eq.
    rewrite HB by exact Hle. f_equal.
    replace (shift_ty 1 0 (subst_ty n Sb U))
      with (subst_ty (S n) (shift_ty 1 0 Sb) (shift_ty 1 0 U)).
    2:{ symmetry. apply shift_ty_subst_ty_comm0. }
    replace (shift_ty 1 0 (shift_ty 1 c Sb))
      with (shift_ty 1 (S c) (shift_ty 1 0 Sb)).
    2:{ symmetry. apply shift_ty_swap_0. }
    rewrite HA by lia. reflexivity.
  - intros c n Sb U Hle. reflexivity.
  - intros A Ts HA HTs c n Sb U Hle.
    cbn [List.map]. rewrite HA by exact Hle. f_equal. apply HTs. exact Hle.
Qed.

Lemma subst_ty_subst_ty_comm0 : forall T n Sb U,
  subst_ty 0 (subst_ty n Sb U) (subst_ty (S n) (shift_ty 1 0 Sb) T) =
  subst_ty n Sb (subst_ty 0 U T).
Proof.
  intros T n Sb U. apply subst_ty_subst_ty_comm. lia.
Qed.

Lemma shift_ty_many_subst_ty_comm0 : forall k n Sb U,
  subst_ty (k + n) (shift_ty k 0 Sb) (shift_ty k 0 U) =
  shift_ty k 0 (subst_ty n Sb U).
Proof.
  induction k as [|k IH]; intros n Sb U.
  - rewrite !shift_ty_zero. simpl. reflexivity.
  - replace (S k + n) with (S (k + n)) by lia.
    replace (shift_ty (S k) 0 Sb) with (shift_ty 1 0 (shift_ty k 0 Sb)).
    2:{ rewrite shift_ty_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    replace (shift_ty (S k) 0 U) with (shift_ty 1 0 (shift_ty k 0 U)).
    2:{ rewrite shift_ty_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    rewrite <- shift_ty_subst_ty_comm0.
    rewrite IH. rewrite shift_ty_fuse.
    replace (1 + k) with (S k) by lia. reflexivity.
Qed.

Lemma inst_ty_vars_subst_ty : forall k Ts T n Sb,
  List.length Ts = k ->
  inst_ty_vars k (List.map (subst_ty n Sb) Ts)
    (subst_ty (k + n) (shift_ty k 0 Sb) T) =
  subst_ty n Sb (inst_ty_vars k Ts T).
Proof.
  induction k as [|k IH]; intros Ts T n Sb Hlen.
  - destruct Ts as [|U rest]; [|simpl in Hlen; discriminate].
    rewrite shift_ty_zero. simpl. replace (0 + n) with n by lia. reflexivity.
  - destruct Ts as [|U rest]; [simpl in Hlen; discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    simpl.
    rewrite <- shift_ty_many_subst_ty_comm0.
    replace (S k + n) with (S (k + n)) by lia.
    replace (shift_ty (S k) 0 Sb) with (shift_ty 1 0 (shift_ty k 0 Sb)).
    2:{ rewrite shift_ty_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    rewrite subst_ty_subst_ty_comm0.
    rewrite IH by exact Hlen. reflexivity.
Qed.

Lemma inst_op_alpha_subst_ty : forall n_alpha Ts n_beta T n Sb,
  List.length Ts = n_alpha ->
  inst_op_alpha n_alpha (List.map (subst_ty n Sb) Ts) n_beta
    (subst_ty (n_alpha + n_beta + n) (shift_ty (n_alpha + n_beta) 0 Sb) T) =
  subst_ty (n_beta + n) (shift_ty n_beta 0 Sb)
    (inst_op_alpha n_alpha Ts n_beta T).
Proof.
  intros n_alpha Ts n_beta T n Sb Hlen. unfold inst_op_alpha.
  replace (List.map (shift_ty n_beta 0) (List.map (subst_ty n Sb) Ts)) with
    (List.map (subst_ty (n_beta + n) (shift_ty n_beta 0 Sb))
      (List.map (shift_ty n_beta 0) Ts)).
  - replace (n_alpha + n_beta + n) with (n_alpha + (n_beta + n)) by lia.
    replace (shift_ty (n_alpha + n_beta) 0 Sb)
      with (shift_ty n_alpha 0 (shift_ty n_beta 0 Sb)).
    2:{ rewrite shift_ty_fuse. reflexivity. }
    rewrite inst_ty_vars_subst_ty by (rewrite List.length_map; exact Hlen).
    reflexivity.
  - rewrite !List.map_map. apply List.map_ext. intro U.
    rewrite shift_ty_many_subst_ty_comm0. reflexivity.
Qed.

Lemma inst_op_arg_subst_ty : forall n_alpha Ts n_beta Ss T n Sb,
  List.length Ts = n_alpha ->
  List.length Ss = n_beta ->
  inst_op_arg n_alpha (List.map (subst_ty n Sb) Ts)
              n_beta (List.map (subst_ty n Sb) Ss)
              (subst_ty (n_alpha + n_beta + n)
                (shift_ty (n_alpha + n_beta) 0 Sb) T) =
  subst_ty n Sb (inst_op_arg n_alpha Ts n_beta Ss T).
Proof.
  intros n_alpha Ts n_beta Ss T n Sb HlenTs HlenSs.
  unfold inst_op_arg.
  rewrite inst_op_alpha_subst_ty by exact HlenTs.
  rewrite inst_ty_vars_subst_ty by exact HlenSs.
  reflexivity.
Qed.

Lemma shift_lt_in_ty_subst_ty_comm_many : forall T k c n Sb,
  shift_lt_in_ty k c (subst_ty n Sb T) =
  subst_ty n (shift_lt_in_ty k c Sb) (shift_lt_in_ty k c T).
Proof.
  intros T k. revert T.
  induction k as [|k IH]; intros T c n Sb.
  - rewrite !shift_lt_in_ty_zero. reflexivity.
  - replace (shift_lt_in_ty (S k) c (subst_ty n Sb T))
      with (shift_lt_in_ty 1 c (shift_lt_in_ty k c (subst_ty n Sb T))).
    2:{ rewrite shift_lt_in_ty_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    rewrite IH.
    rewrite shift_lt_in_ty_subst_ty_comm.
    rewrite shift_lt_in_ty_fuse.
    rewrite shift_lt_in_ty_fuse.
    replace (1 + k) with (S k) by lia. reflexivity.
Qed.

Lemma shift_lt_lift_lower : forall l off d k,
  d <= k ->
  shift_lt 1 (off + d) (shift_lt k off l) = shift_lt (S k) off l.
Proof.
  intros l. induction l as [x| | |l1 IH1 l2 IH2]; intros off d k Hle; simpl.
  - destruct (Nat.leb off x) eqn:Hx.
    + apply Nat.leb_le in Hx.
      rewrite (proj2 (Nat.leb_le (off + d) (x + k))) by lia.
      f_equal. lia.
    + apply Nat.leb_gt in Hx.
      rewrite (proj2 (Nat.leb_gt (off + d) x)) by lia.
      reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1 by exact Hle. rewrite IH2 by exact Hle. reflexivity.
Qed.

Lemma shift_lt_in_ty_lift_lower : forall T off d k,
  d <= k ->
  shift_lt_in_ty 1 (off + d) (shift_lt_in_ty k off T) =
  shift_lt_in_ty (S k) off T.
Proof.
  intros T. apply (type_list_ind
    (fun T => forall off d k,
      d <= k ->
      shift_lt_in_ty 1 (off + d) (shift_lt_in_ty k off T) =
      shift_lt_in_ty (S k) off T)
    (fun Ts => forall off d k,
      d <= k ->
      List.map (shift_lt_in_ty 1 (off + d))
        (List.map (shift_lt_in_ty k off) Ts) =
      List.map (shift_lt_in_ty (S k) off) Ts)).
  - reflexivity.
  - intros A l B HA HB off d k Hle. simpl.
    rewrite HA by exact Hle. rewrite HB by exact Hle.
    rewrite shift_lt_lift_lower by exact Hle. reflexivity.
  - intros K l Ts HTs off d k Hle. simpl.
    rewrite shift_lt_lift_lower by exact Hle. f_equal. apply HTs. exact Hle.
  - intros A HA off d k Hle. simpl.
    replace (S (off + d)) with (S off + d) by lia.
    rewrite HA by exact Hle. reflexivity.
  - intros B A HB HA off d k Hle. simpl.
    rewrite HB by exact Hle. rewrite HA by exact Hle. reflexivity.
  - reflexivity.
  - intros A Ts HA HTs off d k Hle. cbn [List.map].
    rewrite HA by exact Hle. f_equal. apply HTs. exact Hle.
Qed.

Lemma multi_subst_lt_shift_lt_above : forall l cutoff d lts,
  d <= cutoff ->
  multi_subst_lt (S cutoff) lts (shift_lt 1 d l) =
  shift_lt 1 d (multi_subst_lt cutoff lts l).
Proof.
  intros l. induction l as [x| | |l1 IH1 l2 IH2]; intros cutoff d lts Hle; simpl.
  - destruct (Nat.leb d x) eqn:Hshift.
    + apply Nat.leb_le in Hshift.
      destruct (Nat.ltb_spec x cutoff) as [Hbelow|Hge].
      * assert (Hlt1 : (x + 1 <? S cutoff) = true) by (apply Nat.ltb_lt; lia).
        rewrite Hlt1.
        simpl. assert (Hdb : (d <=? x) = true) by (apply Nat.leb_le; lia).
        rewrite Hdb. reflexivity.
      * assert (Hge1 : (x + 1 <? S cutoff) = false) by (apply Nat.ltb_ge; lia).
        assert (Hge0 : (x <? cutoff) = false) by (apply Nat.ltb_ge; lia).
        rewrite Hge1.
        replace (x + 1 - S cutoff) with (x - cutoff) by lia.
        destruct (Nat.ltb_spec (x - cutoff) (List.length lts)) as [Hin|Hout].
        -- assert (Hinb : (x - cutoff <? List.length lts) = true) by (apply Nat.ltb_lt; lia).
            replace d with (0 + d) by lia.
           rewrite shift_lt_lift_lower by exact Hle. reflexivity.
        -- assert (Houtb : (x - cutoff <? List.length lts) = false) by (apply Nat.ltb_ge; lia).
           simpl. assert (Hdb : (d <=? x - List.length lts) = true) by (apply Nat.leb_le; lia).
           rewrite Hdb.
           f_equal. lia.
    + apply Nat.leb_gt in Hshift.
      assert (Hbelow : x < cutoff) by lia.
      assert (Hlt0 : (x <? cutoff) = true) by (apply Nat.ltb_lt; lia).
      assert (Hlt1 : (x <? S cutoff) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hlt0, Hlt1.
      simpl. assert (Hdb : (d <=? x) = false) by (apply Nat.leb_gt; lia).
      rewrite Hdb. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1 by exact Hle. rewrite IH2 by exact Hle. reflexivity.
Qed.

Lemma multi_subst_lt_in_ty_shift_lt_above : forall T cutoff d lts,
  d <= cutoff ->
  multi_subst_lt_in_ty (S cutoff) lts (shift_lt_in_ty 1 d T) =
  shift_lt_in_ty 1 d (multi_subst_lt_in_ty cutoff lts T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall cutoff d lts,
      d <= cutoff ->
      multi_subst_lt_in_ty (S cutoff) lts (shift_lt_in_ty 1 d T) =
      shift_lt_in_ty 1 d (multi_subst_lt_in_ty cutoff lts T))
    (fun Ts => forall cutoff d lts,
      d <= cutoff ->
      List.map (multi_subst_lt_in_ty (S cutoff) lts)
        (List.map (shift_lt_in_ty 1 d) Ts) =
      List.map (shift_lt_in_ty 1 d)
        (List.map (multi_subst_lt_in_ty cutoff lts) Ts))).
  - reflexivity.
  - intros A l B HA HB cutoff d lts Hle. simpl.
    rewrite HA by exact Hle. rewrite HB by exact Hle.
    rewrite multi_subst_lt_shift_lt_above by exact Hle. reflexivity.
  - intros K l Ts HTs cutoff d lts Hle. simpl.
    rewrite multi_subst_lt_shift_lt_above by exact Hle.
    f_equal. apply HTs. exact Hle.
  - intros A HA cutoff d lts Hle. simpl.
    rewrite HA by lia. reflexivity.
  - intros B A HB HA cutoff d lts Hle. simpl.
    rewrite HB by exact Hle. rewrite HA by exact Hle. reflexivity.
  - reflexivity.
  - intros A Ts HA HTs cutoff d lts Hle. cbn [List.map].
    rewrite HA by exact Hle. f_equal. apply HTs. exact Hle.
Qed.

Lemma multi_subst_lt_in_ty_subst_ty : forall T cutoff lts n Sb,
  multi_subst_lt_in_ty cutoff lts (subst_ty n Sb T) =
  subst_ty n (multi_subst_lt_in_ty cutoff lts Sb)
    (multi_subst_lt_in_ty cutoff lts T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall cutoff lts n Sb,
      multi_subst_lt_in_ty cutoff lts (subst_ty n Sb T) =
      subst_ty n (multi_subst_lt_in_ty cutoff lts Sb)
        (multi_subst_lt_in_ty cutoff lts T))
    (fun Ts => forall cutoff lts n Sb,
      List.map (multi_subst_lt_in_ty cutoff lts) (List.map (subst_ty n Sb) Ts) =
      List.map (subst_ty n (multi_subst_lt_in_ty cutoff lts Sb))
        (List.map (multi_subst_lt_in_ty cutoff lts) Ts))).
  - intros m cutoff lts n Sb. simpl.
    destruct (Nat.eqb m n); destruct (Nat.ltb n m); reflexivity.
  - intros A l B HA HB cutoff lts n Sb. simpl.
    rewrite HA, HB. reflexivity.
  - intros K l Ts HTs cutoff lts n Sb. simpl. f_equal. apply HTs.
  - intros A HA cutoff lts n Sb. simpl. f_equal.
    rewrite HA. f_equal.
    rewrite multi_subst_lt_in_ty_shift_lt_above by lia. reflexivity.
  - intros B A HB HA cutoff lts n Sb. simpl.
    rewrite HB. f_equal. rewrite HA. f_equal.
    rewrite multi_subst_lt_in_ty_shift_ty. reflexivity.
  - intros cutoff lts n Sb. reflexivity.
  - intros A Ts HA HTs cutoff lts n Sb. cbn [List.map].
    rewrite HA. f_equal. apply HTs.
Qed.

Lemma inst_ctor_type_subst_ty : forall n_lt n_ty lts Ts T n Sb,
  List.length lts = n_lt ->
  List.length Ts = n_ty ->
  inst_ctor_type n_lt n_ty lts (List.map (subst_ty n Sb) Ts)
    (subst_ty (n_ty + n) (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb)) T) =
  subst_ty n Sb (inst_ctor_type n_lt n_ty lts Ts T).
Proof.
  intros n_lt n_ty lts Ts T n Sb HlenL HlenT.
  unfold inst_ctor_type, inst_lt_vars.
  replace (List.map (shift_lt_in_ty n_lt 0) (List.map (subst_ty n Sb) Ts))
    with (List.map (subst_ty n (shift_lt_in_ty n_lt 0 Sb))
      (List.map (shift_lt_in_ty n_lt 0) Ts)).
  2:{ rewrite !List.map_map. apply List.map_ext. intro U.
      rewrite shift_lt_in_ty_subst_ty_comm_many. reflexivity. }
  replace (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb))
    with (shift_ty n_ty 0 (shift_lt_in_ty n_lt 0 Sb)).
  2:{ rewrite shift_ty_shift_lt_in_ty_commute. reflexivity. }
  rewrite inst_ty_vars_subst_ty by (rewrite List.length_map; exact HlenT).
  rewrite multi_subst_lt_in_ty_subst_ty.
  rewrite multi_subst_lt_in_ty_shift_lt_cancel0 by exact HlenL.
  reflexivity.
Qed.

Lemma subst_ty_in_tm_go_eq_map_local : forall n Sb ts,
  (fix go ts := match ts with [] => [] | u :: rest => subst_ty_in_tm n Sb u :: go rest end) ts =
  List.map (subst_ty_in_tm n Sb) ts.
Proof.
  intros n Sb ts. induction ts as [|t ts IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma free_tm_vars_subst_ty_in_tm : forall t cutoff n Sb,
  free_tm_vars cutoff (subst_ty_in_tm n Sb t) = free_tm_vars cutoff t.
Proof.
  apply (term_list_ind
    (fun t => forall cutoff n Sb,
      free_tm_vars cutoff (subst_ty_in_tm n Sb t) = free_tm_vars cutoff t)
    (fun ts => forall cutoff n Sb,
      List.concat (List.map (free_tm_vars cutoff) (List.map (subst_ty_in_tm n Sb) ts)) =
      List.concat (List.map (free_tm_vars cutoff) ts))).
  - reflexivity.
  - intros t1 t2 IH1 IH2 cutoff n Sb. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH cutoff n Sb. simpl. apply IH.
  - intros t T IH cutoff n Sb. simpl. apply IH.
  - intros bound body IH cutoff n Sb. simpl. apply IH.
  - intros t l IH cutoff n Sb. simpl. apply IH.
  - intros body IH cutoff n Sb. simpl. apply IH.
  - intros K l lts Ts ts IH cutoff n Sb. simpl. rewrite subst_ty_in_tm_go_eq_map_local.
    rewrite !free_tm_vars_go_eq_concat. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn cutoff n Sb. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff n Sb. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa cutoff n Sb. simpl. rewrite IHt, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff n Sb. simpl. apply IHop.
  - intros m T_B T_R t IH cutoff n Sb. simpl. apply IH.
  - intros m T_B T_R b IH cutoff n Sb. simpl. apply IH.
  - reflexivity.
  - intros t ts IHt IHts cutoff n Sb. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma has_rt_cap_subst_ty_in_tm : forall t n Sb,
  has_rt_cap (subst_ty_in_tm n Sb t) = has_rt_cap t.
Proof.
  apply (term_list_ind
    (fun t => forall n Sb,
      has_rt_cap (subst_ty_in_tm n Sb t) = has_rt_cap t)
    (fun ts => forall n Sb,
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end)
        (List.map (subst_ty_in_tm n Sb) ts) =
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts)).
  - reflexivity.
  - intros t1 t2 IH1 IH2 n Sb. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH n Sb. simpl. apply IH.
  - intros t T IH n Sb. simpl. apply IH.
  - intros bound body IH n Sb. simpl. apply IH.
  - intros t l IH n Sb. simpl. apply IH.
  - intros body IH n Sb. simpl. apply IH.
  - intros K l lts Ts ts IH n Sb. simpl. rewrite subst_ty_in_tm_go_eq_map_local. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn n Sb. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb n Sb. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa n Sb. simpl. rewrite IHt, IHa. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros t ts IHt IHts n Sb. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma lt_of_ty_ctx_SubstTy_le_wf : forall Sb n G G', SubstTy Sb n G G' ->
  forall f T k, lt_wf G (lt_of_ty_ctx f G T) -> VB k T -> length G <= k + f ->
  G' ⊢ₗ lt_of_ty_ctx f G' (subst_ty n Sb T) <: lt_of_ty_ctx f G T.
Proof.
  intros Sb n G G' HS.
  pose proof (SubstTy_n_lt Sb n G G' HS) as Hn.
  pose proof (SubstTy_S_VB Sb n G G' HS) as HSVB.
  pose proof (SubstTy_length Sb n G G' HS) as HLen.
  destruct (SubstTy_target Sb n G G' HS) as [Btgt [Htgt Hsubtgt]].
  induction f as [|f' IHf]; intros T k HwfLt HVB Hlen.
  - rewrite Nat.add_0_r in Hlen. revert k HwfLt HVB Hlen.
    induction T using type_list_ind with
      (Q := fun Ts => forall k,
              lt_wf G (lt_of_ty_ctx_list 0 G Ts) -> VBL k Ts -> length G <= k ->
              G' ⊢ₗ lt_of_ty_ctx_list 0 G' (List.map (subst_ty n Sb) Ts)
                  <: lt_of_ty_ctx_list 0 G Ts);
      intros k HwfLt HVB Hlen.
    + simpl in HVB.
      assert (Hane : n0 <> n) by lia.
      rewrite (subst_ty_var_neq n Sb n0 Hane).
      rewrite !(lt_of_ty_ctx_var 0). apply LS_Refl. constructor.
    + rewrite subst_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. apply LS_Refl.
      eapply lt_wf_SubstTy_ctx; eauto.
    + rewrite subst_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor.
      rewrite VB_ctor in HVB. inversion HwfLt; subst.
      apply lt_min_mono.
      * apply LS_Refl. eapply lt_wf_SubstTy_ctx; eauto.
      * eapply IHT; eauto.
    + rewrite subst_ty_ltall_eq. rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + rewrite subst_ty_tyall_eq. rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + rewrite VBL_cons in HVB. destruct HVB as [Ha Hr].
      cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons.
      inversion HwfLt; subst.
      apply lt_min_mono; [eapply IHT; eauto | eapply IHT0; eauto].
  - revert k HwfLt HVB Hlen.
    induction T using type_list_ind with
      (Q := fun Ts => forall k,
              lt_wf G (lt_of_ty_ctx_list (S f') G Ts) -> VBL k Ts -> length G <= k + S f' ->
              G' ⊢ₗ lt_of_ty_ctx_list (S f') G' (List.map (subst_ty n Sb) Ts)
                  <: lt_of_ty_ctx_list (S f') G Ts);
      intros k HwfLt HVB Hlen.
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
          -- assert (HwfB0 : lt_wf G (lt_of_ty_ctx f' G B0)).
            { rewrite (lt_of_ty_ctx_var (S f') G n0), E in HwfLt. exact HwfLt. }
            apply (IHf B0 (S n0) HwfB0 (ctx_inv_all G n0 B0 E)). lia.
        -- apply LS_Refl. constructor.
    + rewrite subst_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. apply LS_Refl.
      eapply lt_wf_SubstTy_ctx; eauto.
    + rewrite subst_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor.
      rewrite VB_ctor in HVB. inversion HwfLt; subst.
      apply lt_min_mono.
      * apply LS_Refl. eapply lt_wf_SubstTy_ctx; eauto.
      * eapply IHT; eauto.
    + rewrite subst_ty_ltall_eq. rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + rewrite subst_ty_tyall_eq. rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + rewrite VBL_cons in HVB. destruct HVB as [Ha Hr].
      cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons.
      inversion HwfLt; subst.
      apply lt_min_mono; [eapply IHT; eauto | eapply IHT0; eauto].
Qed.

Lemma lt_of_ty_G_SubstTy_le_wf : forall Sb n G G', SubstTy Sb n G G' ->
  forall T, lt_wf G (lt_of_ty_G G T) ->
  G' ⊢ₗ lt_of_ty_G G' (subst_ty n Sb T) <: lt_of_ty_G G T.
Proof.
  intros Sb n G G' HS T HwfLt. unfold lt_of_ty_G in *.
  pose proof (SubstTy_length Sb n G G' HS) as HL.
  rewrite (lt_of_ty_ctx_fuel_irrel (length G') (length G)
             (subst_ty n Sb T) G' 0 (VB_0 _) ltac:(lia) ltac:(lia)).
  apply (lt_of_ty_ctx_SubstTy_le_wf Sb n G G' HS (length G) T 0 HwfLt (VB_0 T) ltac:(lia)).
Qed.

Lemma capture_lt_SubstTy_le : forall Sb n G G', SubstTy Sb n G G' ->
  forall body, lt_wf G (capture_lt G body) ->
  G' ⊢ₗ capture_lt G' (subst_ty_in_tm n Sb body) <: capture_lt G body.
Proof.
  intros Sb n G G' HS body HwfCap. unfold capture_lt in *.
  rewrite has_rt_cap_subst_ty_in_tm.
  destruct (has_rt_cap body) eqn:Hcap.
  - apply LS_Refl. constructor.
  - rewrite free_tm_vars_subst_ty_in_tm.
    induction (free_tm_vars 1 body) as [|x xs IH]; simpl in *.
    + apply LS_Refl. constructor.
    + inversion HwfCap; subst.
      rewrite (SubstTy_lookup_tm Sb n G G' HS x).
      destruct (ctx_lookup_tm G x) as [T|] eqn:Hlk; simpl.
      * apply lt_min_mono.
        -- match goal with
          | Hh : lt_wf G (lt_of_ty_G G T) |-
            G' ⊢ₗ lt_of_ty_G G' (subst_ty n Sb T) <: lt_of_ty_G G T =>
            apply (lt_of_ty_G_SubstTy_le_wf Sb n G G' HS T Hh)
          end.
        -- match goal with
          | Ht : lt_wf G (fold_right _ _ xs) |- _ => apply IH; exact Ht
          end.
      * apply lt_min_mono.
        -- apply LS_Refl. constructor.
        -- match goal with
          | Ht : lt_wf G (fold_right _ _ xs) |- _ => apply IH; exact Ht
          end.
Qed.

Lemma lifetimes_wf_SubstTy : forall G lts,
  lifetimes_wf G lts -> forall Sb n G', SubstTy Sb n G G' -> lifetimes_wf G' lts.
Proof.
  intros G lts Hwf. induction Hwf; intros Sb n G' HS.
  - constructor.
  - constructor.
    + eapply lt_wf_SubstTy_ctx; eauto.
    + apply (IHHwf Sb n G' HS).
Qed.

Lemma subst_ty_any_at_free : forall n Sb, subst_ty n Sb any_at_free = any_at_free.
Proof. intros n Sb. reflexivity. Qed.

Lemma SubstTy_push_lt_vars : forall k Delta Sb n G G',
  SubstTy Sb n G G' ->
  SubstTy (shift_lt_in_ty k 0 Sb) n
    (push_lt_vars k Delta G) (push_lt_vars k Delta G').
Proof.
  induction k as [|k IH]; intros Delta Sb n G G' HS; simpl.
  - rewrite shift_lt_in_ty_zero. exact HS.
  - replace (shift_lt_in_ty (S k) 0 Sb)
      with (shift_lt_in_ty k 0 (shift_lt_in_ty 1 0 Sb)).
    2:{ rewrite shift_lt_in_ty_fuse. replace (k + 1) with (S k) by lia. reflexivity. }
    apply IH. apply SubstTy_lt. exact HS.
Qed.

Lemma SubstTy_push_ty_vars_any_at_free : forall k Sb n G G',
  SubstTy Sb n G G' ->
  SubstTy (shift_ty k 0 Sb) (k + n)
    (push_ty_vars k any_at_free G) (push_ty_vars k any_at_free G').
Proof.
  induction k as [|k IH]; intros Sb n G G' HS; simpl.
  - rewrite shift_ty_zero. replace (0 + n) with n by lia. exact HS.
  - replace (shift_ty (S k) 0 Sb) with (shift_ty k 0 (shift_ty 1 0 Sb)).
    2:{ rewrite shift_ty_fuse. replace (k + 1) with (S k) by lia. reflexivity. }
    replace (S (k + n)) with (k + S n) by lia.
    apply IH. rewrite <- (subst_ty_any_at_free n Sb).
    apply SubstTy_ty. exact HS.
Qed.

Lemma SubstTy_fold_bind_tm : forall rhos Sb n G G',
  SubstTy Sb n G G' ->
  SubstTy Sb n
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm (subst_ty n Sb rho) :: G0) G' rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros Sb n G G' HS; simpl.
  - exact HS.
  - apply SubstTy_tm. apply IH. exact HS.
Qed.

Lemma Forall2_typing_SubstTy : forall Γ vs rhos,
  Forall2 (fun v rho => forall Sb n G', SubstTy Sb n Γ G' ->
    G' ⊢ₜ subst_ty_in_tm n Sb v : subst_ty n Sb rho) vs rhos ->
  forall Sb n G', SubstTy Sb n Γ G' ->
  Forall2 (fun v rho => G' ⊢ₜ v : rho)
           (List.map (subst_ty_in_tm n Sb) vs) (List.map (subst_ty n Sb) rhos).
Proof.
  intros Γ vs rhos H. induction H; intros Sb n G' HS; simpl.
  - constructor.
  - constructor.
    + apply H. exact HS.
    + apply IHForall2. exact HS.
Qed.

Lemma elim_lt_shift_miss : forall l lvar bound p,
  elim_lt lvar bound p (shift_lt 1 lvar l) = Some (shift_lt 1 lvar l).
Proof.
  induction l as [x| | |l1 IH1 l2 IH2]; intros lvar bound p; simpl.
  - destruct (Nat.leb lvar x) eqn:Hle.
    + apply Nat.leb_le in Hle.
      assert (Hneq : (x + 1 =? lvar) = false) by (apply Nat.eqb_neq; lia).
      rewrite Hneq. reflexivity.
    + apply Nat.leb_gt in Hle.
      assert (Hneq : (x =? lvar) = false) by (apply Nat.eqb_neq; lia).
      rewrite Hneq. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma elim_ty_shift_miss : forall T lvar bound p,
  elim_ty lvar bound p (shift_lt_in_ty 1 lvar T) = Some (shift_lt_in_ty 1 lvar T).
Proof.
  apply (type_list_ind
    (fun T => forall lvar bound p,
      elim_ty lvar bound p (shift_lt_in_ty 1 lvar T) = Some (shift_lt_in_ty 1 lvar T))
    (fun Ts => forall lvar bound p,
      (fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
         match Ts0 with
         | [] => Some []
         | A :: rest =>
             match elim_ty lvar bound p' A, go_list p' rest with
             | Some A', Some rest' => Some (A' :: rest')
             | _, _ => None
             end
         end) p (List.map (shift_lt_in_ty 1 lvar) Ts) =
      Some (List.map (shift_lt_in_ty 1 lvar) Ts))).
  - reflexivity.
  - intros A l B HA HB lvar bound p. simpl.
    rewrite HA, HB, elim_lt_shift_miss. reflexivity.
  - intros K l Ts HTs lvar bound p. rewrite shift_lt_in_ty_ctor_eq. simpl.
    rewrite elim_lt_shift_miss. rewrite HTs. reflexivity.
  - intros A HA lvar bound p. simpl.
    rewrite HA. reflexivity.
  - intros B A HB HA lvar bound p. simpl.
    rewrite HB, HA. reflexivity.
  - reflexivity.
  - intros A Ts HA HTs lvar bound p. cbn [List.map]. simpl.
    rewrite HA, HTs. reflexivity.
Qed.

Lemma elim_ty_subst_ty_shifted : forall T lvar bound p T' c Sb,
  elim_ty lvar bound p T = Some T' ->
  elim_ty lvar bound p (subst_ty c (shift_lt_in_ty 1 lvar Sb) T) =
  Some (subst_ty c (shift_lt_in_ty 1 lvar Sb) T').
Proof.
  apply (type_list_ind
    (fun T => forall lvar bound p T' c Sb,
      elim_ty lvar bound p T = Some T' ->
      elim_ty lvar bound p (subst_ty c (shift_lt_in_ty 1 lvar Sb) T) =
      Some (subst_ty c (shift_lt_in_ty 1 lvar Sb) T'))
    (fun Ts => forall lvar bound p Ts' c Sb,
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
             match elim_ty lvar bound p' A, go_list p' rest with
             | Some A', Some rest' => Some (A' :: rest')
             | _, _ => None
             end
         end) p (List.map (subst_ty c (shift_lt_in_ty 1 lvar Sb)) Ts) =
      Some (List.map (subst_ty c (shift_lt_in_ty 1 lvar Sb)) Ts'))).
  - intros m lvar bound p T' c Sb H. simpl in H. injection H as H; subst T'.
    rewrite subst_ty_var_eq.
    destruct (Nat.eqb m c) eqn:Heq.
    + apply elim_ty_shift_miss.
    + simpl. destruct (Nat.ltb c m); reflexivity.
  - intros A l B HA HB lvar bound p T' c Sb H. simpl in H.
    destruct (elim_ty lvar bound (flip_var p) A) as [A'|] eqn:HAe; try discriminate.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hle; try discriminate.
    destruct (elim_ty lvar bound p B) as [B'|] eqn:HBe; try discriminate.
    injection H as H; subst T'. simpl.
    rewrite (HA lvar bound (flip_var p) A' c Sb HAe).
    rewrite Hle.
    rewrite (HB lvar bound p B' c Sb HBe). reflexivity.
  - intros K l Ts HTs lvar bound p T' c Sb H. simpl in H.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hle; try discriminate.
    destruct ((fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
      match Ts0 with
      | [] => Some []
      | A :: rest =>
          match elim_ty lvar bound p' A, go_list p' rest with
          | Some A', Some rest' => Some (A' :: rest')
          | _, _ => None
          end
      end) var_inv Ts) as [Ts'|] eqn:HTse; try discriminate.
    injection H as H; subst T'. simpl. rewrite subst_ty_go_eq_map. rewrite Hle.
    rewrite (HTs lvar bound var_inv Ts' c Sb HTse). reflexivity.
  - intros A HA lvar bound p T' c Sb H. simpl in H.
    destruct (elim_ty (S lvar) (shift_lt 1 0 bound) p A) as [A'|] eqn:HAe; try discriminate.
    injection H as H; subst T'. simpl.
    replace (shift_lt_in_ty 1 0 (shift_lt_in_ty 1 lvar Sb))
      with (shift_lt_in_ty 1 (S lvar) (shift_lt_in_ty 1 0 Sb)).
    2:{ rewrite shift_lt_in_ty_swap_0. reflexivity. }
    rewrite (HA (S lvar) (shift_lt 1 0 bound) p A' c (shift_lt_in_ty 1 0 Sb) HAe).
    reflexivity.
  - intros B A HB HA lvar bound p T' c Sb H. simpl in H.
    destruct (elim_ty lvar bound (flip_var p) B) as [B'|] eqn:HBe; try discriminate.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HAe; try discriminate.
    injection H as H; subst T'. simpl.
    rewrite (HB lvar bound (flip_var p) B' c Sb HBe).
    replace (shift_ty 1 0 (shift_lt_in_ty 1 lvar Sb))
      with (shift_lt_in_ty 1 lvar (shift_ty 1 0 Sb)).
    2:{ rewrite shift_ty_shift_lt_in_ty_commute. reflexivity. }
    rewrite (HA lvar bound p A' (S c) (shift_ty 1 0 Sb) HAe).
    reflexivity.
  - intros lvar bound p Ts' c Sb H. simpl in H. injection H as H; subst Ts'. reflexivity.
  - intros A Ts HA HTs lvar bound p Ts' c Sb H. simpl in H.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HAe; try discriminate.
    destruct ((fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
      match Ts0 with
      | [] => Some []
      | A0 :: rest =>
          match elim_ty lvar bound p' A0, go_list p' rest with
          | Some A'', Some rest' => Some (A'' :: rest')
          | _, _ => None
          end
      end) p Ts) as [Ts0'|] eqn:HTse; try discriminate.
    injection H as H; subst Ts'. simpl.
    rewrite (HA lvar bound p A' c Sb HAe).
    rewrite (HTs lvar bound p Ts0' c Sb HTse). reflexivity.
Qed.

Lemma elim_ty_n_subst_ty_shifted : forall k bound p T T' c Sb,
  elim_ty_n k bound p T = Some T' ->
  elim_ty_n k bound p (subst_ty c (shift_lt_in_ty k 0 Sb) T) =
  Some (subst_ty c Sb T').
Proof.
  induction k as [|k IH]; intros bound p T T' c Sb H.
  - simpl in H. injection H as H; subst T'.
    rewrite shift_lt_in_ty_zero. reflexivity.
  - simpl in H. destruct (elim_ty 0 bound p T) as [T1|] eqn:HE; try discriminate.
    simpl.
    replace (shift_lt_in_ty (S k) 0 Sb)
      with (shift_lt_in_ty 1 0 (shift_lt_in_ty k 0 Sb)).
    2:{ rewrite shift_lt_in_ty_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    rewrite (elim_ty_subst_ty_shifted T 0 bound p T1 c (shift_lt_in_ty k 0 Sb) HE).
    rewrite subst_lt_in_ty_subst_ty_comm.
    replace (subst_lt_in_ty 0 lt_free (shift_lt_in_ty 1 0 (shift_lt_in_ty k 0 Sb)))
      with (shift_lt_in_ty k 0 Sb).
    2:{ rewrite subst_lt_in_ty_shift_cancel. reflexivity. }
    apply IH. exact H.
Qed.

(* Substituting `lts` for bounded schema variables `lt_var_list n_lt`  *)
(* yields direct schema instantiation.                                 *)
Lemma inst_ctor_type_subst_eq : forall n_lt n_ty lts Ts sigma_fields,
  List.length lts = n_lt ->
  Forall (ctor_field_bounded_ty n_lt)
         (List.map (inst_ty_vars n_ty (List.map (shift_lt_in_ty n_lt 0) Ts)) sigma_fields) ->
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
