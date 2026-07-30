Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.

(* ================================================================== *)
(* The substitution-tier tactic library.                              *)
(*                                                                    *)
(* Placed FIRST in the tier so every subst module can use it.  The    *)
(* hint databases are created here; their entries are registered at   *)
(* the defining sites across the tier (end of ShiftLaws.v,            *)
(* Weakening.v, SubstLt.v, SubstTy.v, SubstTm.v, TypingSubst.v).      *)
(*                                                                    *)
(*   subst_go       Hint Rewrite database normalizing the inline      *)
(*                  [fix go]/[fix go_ops] traversals to their named   *)
(*                  List.map/concat forms (the *_go_eq_* bridge       *)
(*                  lemmas): [autorewrite with subst_go].  The        *)
(*                  safety-tier marker bridges register here too.     *)
(*                                                                    *)
(*   ctxmap         Hint Resolve database with the judgment-transport *)
(*                  lemmas of the context-map relations               *)
(*                  (InsTy/InsLt/InsTm/SubstLt/SubstTy/SubstTm);      *)
(*                  [wf_transport] is [solve [eauto with ctxmap]] —   *)
(*                  the standard discharge of a one-step transport.   *)
(*                                                                    *)
(*   go_traverse    close one constructor case of a purely structural *)
(*                  traversal equation (normalize, fold IHs, refl).   *)
(*                                                                    *)
(*   dbi            decide every visible [Nat.eqb]/[Nat.ltb]/         *)
(*                  [Nat.leb] comparison, then close arithmetic       *)
(*                  side-goals with [lia].  Currently forward-facing: *)
(*                  the existing var-case proofs interleave           *)
(*                  branch-dependent rewrites with their comparison   *)
(*                  splits, so none was mechanically convertible.     *)
(* ================================================================== *)

Create HintDb subst_go.
Create HintDb ctxmap.

Ltac wf_transport := solve [eauto with ctxmap].

(* Decide every nat comparison visible in the goal or hypotheses,
   substituting on equality, then normalize. *)
Ltac dbi_case :=
  repeat match goal with
  | |- context[Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); subst
  | |- context[Nat.ltb ?a ?b] => destruct (Nat.ltb_spec a b)
  | |- context[Nat.leb ?a ?b] => destruct (Nat.leb_spec a b)
  | H : context[Nat.eqb ?a ?b] |- _ => destruct (Nat.eqb_spec a b); subst
  | H : context[Nat.ltb ?a ?b] |- _ => destruct (Nat.ltb_spec a b)
  | H : context[Nat.leb ?a ?b] |- _ => destruct (Nat.leb_spec a b)
  end; simpl.

(* The var-case finisher: case on the comparisons, then the branch is
   either arithmetic-absurd, reflexivity, or f_equal + arithmetic. *)
Ltac dbi := dbi_case; try lia; try reflexivity; try (f_equal; lia).

(* Close one constructor case of a purely structural traversal
   equation: normalize the inline go-fixpoints, fold every inductive
   hypothesis, and finish by reflexivity. *)
Ltac go_traverse :=
  intros; simpl; autorewrite with subst_go;
  repeat match goal with IH : forall _, _ |- _ => rewrite IH; clear IH end;
  reflexivity.

(* [sig_congr law] closes a ctor/eff signature congruence: destruct
   the signature tuple, unfold the sig operations, then close every
   component by index normalization + the single core [law]. *)
(* Extension hook: files defining further sig operations redefine
   this (Ltac ::=) so [sig_congr] unfolds them too. *)
Ltac sig_extra_unfold := idtac.

(* Two-law variant for signature congruences whose components close  *)
(* by different core laws (the cancel/comm mixed cases).              *)
Ltac sig_congr2 law1 law2 :=
  intros; simpl;
  repeat match goal with p : _ * _ |- _ => destruct p end;
  unfold shift_ty_ctor_sig, shift_lt_ctor_sig,
         shift_ty_eff_sig, shift_lt_eff_sig;
  sig_extra_unfold;
  simpl;
  solve [ repeat first
    [ solve [ apply law1; lia ] | solve [ apply law1 ]
    | solve [ symmetry; apply law1; lia ] | solve [ symmetry; apply law1 ]
    | solve [ apply law2; lia ] | solve [ apply law2 ]
    | solve [ symmetry; apply law2; lia ] | solve [ symmetry; apply law2 ]
    | rewrite Nat.add_0_r
    | rewrite Nat.add_succ_r
    | (rewrite !List.map_map; apply List.map_ext; intros ?p;
       repeat match goal with p : _ * _ |- _ => destruct p end; simpl)
    | progress f_equal ] ].

Ltac sig_congr law :=
  intros; simpl;
  repeat match goal with p : _ * _ |- _ => destruct p end;
  unfold shift_ty_ctor_sig, shift_lt_ctor_sig,
         shift_ty_eff_sig, shift_lt_eff_sig;
  sig_extra_unfold;
  simpl;
  solve [ repeat first
    [ solve [ apply law; lia ]
    | solve [ apply law ]
    | solve [ symmetry; apply law; lia ]
    | solve [ symmetry; apply law ]
    | rewrite Nat.add_0_r
    | rewrite Nat.add_succ_r
    | (rewrite !List.map_map; apply List.map_ext; intros ?p;
       repeat match goal with p : _ * _ |- _ => destruct p end; simpl)
    | progress f_equal ] ].
