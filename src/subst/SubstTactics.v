Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import ShiftLaws.
Require Import Weakening.
Require Import SubstLt.
Require Import SubstTy.
Require Import SubstTm.
Require Import ProgramCtx.
Require Import TypingSubst.

(* ================================================================== *)
(* The substitution-tier tactic library.                              *)
(*                                                                    *)
(* Shared automation for the de Bruijn metatheory:                    *)
(*                                                                    *)
(*   subst_go       Hint Rewrite database normalizing the inline      *)
(*                  [fix go]/[fix go_ops] traversals to their named   *)
(*                  List.map/concat forms (the *_go_eq_* bridge       *)
(*                  lemmas), so traversal proofs can start with       *)
(*                  [autorewrite with subst_go].                      *)
(*                                                                    *)
(* This library is FORWARD-FACING: the pre-existing proofs have not   *)
(* been retrofitted onto it (they spell their rewrites out); new      *)
(* proofs in this tier should prefer these tactics.                   *)
(*                                                                    *)
(*   ctxmap         Hint Resolve database with every judgment-        *)
(*                  transport lemma of the context-map relations      *)
(*                  (InsTy/InsLt/InsTm/SubstLt/SubstTy/SubstTm);      *)
(*                  [wf_transport] is [solve [eauto with ctxmap]].    *)
(*                                                                    *)
(*   dbi            decide every visible [Nat.eqb]/[Nat.ltb]/         *)
(*                  [Nat.leb] comparison, then close arithmetic       *)
(*                  side-goals with [lia] — the standard var-case     *)
(*                  finisher of the shift/subst commutation laws.     *)
(* ================================================================== *)

Create HintDb subst_go.
#[export] Hint Rewrite
  shift_lt_in_ty_go_eq_map shift_ty_go_eq_map shift_tm_go_eq_map
  shift_ty_in_tm_go_eq_map shift_lt_in_tm_go_eq_map
  subst_ty_go_eq_map subst_tm_go_eq_map subst_lt_in_tm_go_eq_map
  subst_ty_in_tm_go_eq_map
  multi_subst_lt_in_ty_go_eq_map
  shift_tm_go_ops_eq_map shift_ty_in_tm_go_ops_eq_map
  shift_lt_in_tm_go_ops_eq_map subst_tm_go_ops_eq_map
  subst_ty_in_tm_go_ops_eq_map subst_lt_in_tm_go_ops_eq_map
  free_tm_vars_go_eq_concat free_tm_vars_go_ops_eq_concat
  has_rt_cap_go_ops_eq
  : subst_go.

Create HintDb ctxmap.
#[export] Hint Resolve
  lt_wf_InsTy lt_wf_InsLt lt_wf_InsTm
  lt_wf_SubstLt lt_wf_SubstTy lt_wf_SubstTm
  ty_wf_InsTy ty_wf_InsLt ty_wf_InsTm
  ty_wf_SubstLt ty_wf_SubstTy ty_wf_SubstTm
  lifetimes_wf_InsTy lifetimes_wf_InsLt lifetimes_wf_InsTm
  lifetimes_wf_SubstLt lifetimes_wf_SubstTy lifetimes_wf_SubstTm
  lt_sub_InsTy lt_sub_InsLt lt_sub_InsTm
  lt_sub_SubstLt lt_sub_SubstTy lt_sub_SubstTm
  sub_InsTy sub_InsLt sub_InsTm
  sub_SubstLt sub_SubstTy sub_SubstTm
  sub_free_InsTy sub_free_InsLt sub_free_InsTm
  sub_free_SubstLt sub_free_SubstTy sub_free_SubstTm
  sub_free_list_InsTy sub_free_list_InsLt sub_free_list_InsTm
  sub_free_list_SubstLt sub_free_list_SubstTy sub_free_list_SubstTm
  : ctxmap.

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
