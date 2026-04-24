Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.

(* ================================================================== *)
(* Small-step call-by-value operational semantics                     *)
(*                                                                    *)
(*  (β)     (λ(x:T). t) v   ==>  [0↦v] t                              *)
(*  (β_ty)  (Λα. t) [T]     ==>  [0↦T] t                              *)
(*  (β_lt)  (Λl. t) {Δ}     ==>  [0↦Δ] t                              *)
(*  plus congruence rules for the call-by-value evaluation context    *)
(* ================================================================== *)

Reserved Notation "t '==>' t'" (at level 40).

Inductive step : term -> term -> Prop :=

  (* ---- β-reduction rules ----------------------------------------- *)

  | S_Beta : forall body T v,
      value v ->
      term_app (term_lam body T) v ==> subst_tm 0 v body

  | S_TyBeta : forall bound body T,
      term_ty_app (term_ty_lam bound body) T ==> subst_ty_in_tm 0 T body

  | S_LtBeta : forall body l,
      term_lt_app (term_lt_lam body) l ==> subst_lt_in_tm 0 l body

  (* ---- congruence: function application --------------------------- *)

  | S_App1 : forall t1 t1' t2,
      t1 ==> t1' ->
      term_app t1 t2 ==> term_app t1' t2

  | S_App2 : forall v t2 t2',
      value v ->
      t2 ==> t2' ->
      term_app v t2 ==> term_app v t2'

  (* ---- congruence: type application ------------------------------- *)

  | S_TyApp : forall t t' T,
      t ==> t' ->
      term_ty_app t T ==> term_ty_app t' T

  (* ---- congruence: lifetime application --------------------------- *)

  | S_LtApp : forall t t' l,
      t ==> t' ->
      term_lt_app t l ==> term_lt_app t' l

  (* ---- congruence: constructor arguments (left-to-right) ---------- *)
  (* vs are already-evaluated (value) arguments to the left of the     *)
  (* redex; ts are the remaining unevaluated arguments to the right.   *)

  | S_Ctor : forall K l Ts vs t t' ts,
      Forall value vs ->
      t ==> t' ->
      term_ctor K l Ts (vs ++ t :: ts) ==> term_ctor K l Ts (vs ++ t' :: ts)

  (* ---- match β-rules -------------------------------------------- *)
  (* The matched constructor value is substituted for variable 0 in  *)
  (* yes_body; no_body has no new binders.                           *)

  | S_MatchYes : forall K l Ts vs yes_body no_body,
      Forall value vs ->
      term_match (term_ctor K l Ts vs) K (List.length vs) yes_body no_body
        ==> subst_list_tm vs yes_body

  | S_MatchNo : forall K K' l Ts vs arity yes_body no_body,
      Forall value vs ->
      K <> K' ->
      term_match (term_ctor K' l Ts vs) K arity yes_body no_body ==> no_body

  (* ---- congruence: match scrutinee ------------------------------- *)

  | S_Match : forall scrutinee scrutinee' tag arity yes_body no_body,
      scrutinee ==> scrutinee' ->
      term_match scrutinee tag arity yes_body no_body
        ==> term_match scrutinee' tag arity yes_body no_body

where "t '==>' t'" := (step t t').

Hint Constructors step : core.
