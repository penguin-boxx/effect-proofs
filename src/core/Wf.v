Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Context.

(* ================================================================== *)
(* Well-formedness judgments: lt_wf / lifetimes_wf / ty_wf / types_wf *)
(* ================================================================== *)

Inductive lt_wf : ctx -> lifetime -> Prop :=
  | LWF_Var : forall Γ x Δ,
      ctx_lookup_lt Γ x = Some Δ ->
      lt_wf Γ (lt_var x)
  | LWF_Free : forall Γ,
      lt_wf Γ lt_free
  | LWF_Local : forall Γ,
      lt_wf Γ lt_local
  | LWF_Join : forall Γ l1 l2,
      lt_wf Γ l1 ->
      lt_wf Γ l2 ->
      lt_wf Γ (lt_join l1 l2).

Inductive lifetimes_wf : ctx -> list lifetime -> Prop :=
  | LWFs_nil : forall Γ,
      lifetimes_wf Γ []
  | LWFs_cons : forall Γ l lts,
      lt_wf Γ l ->
      lifetimes_wf Γ lts ->
      lifetimes_wf Γ (l :: lts).

Inductive ty_wf : ctx -> type -> Prop :=
  | TWF_Var : forall Γ α B,
      ctx_lookup_ty Γ α = Some B ->
      ty_wf Γ B ->
      ty_wf Γ (type_var α)
  | TWF_Fun : forall Γ A l B,
      ty_wf Γ A ->
      lt_wf Γ l ->
      ty_wf Γ B ->
      ty_wf Γ (type_fun A l B)
  | TWF_Ctor : forall Γ K l Ts,
      lt_wf Γ l ->
      types_wf Γ Ts ->
      ty_wf Γ (type_ctor K l Ts)
  | TWF_LtAll : forall Γ A,
      ty_wf (bind_lt lt_local :: Γ) A ->
      ty_wf Γ (type_lt_all A)
  | TWF_TyAll : forall Γ B A,
      ty_wf Γ B ->
      ty_wf (bind_ty B :: Γ) A ->
      ty_wf Γ (type_ty_all B A)
with types_wf : ctx -> list type -> Prop :=
  | TWFs_nil : forall Γ,
      types_wf Γ []
  | TWFs_cons : forall Γ T Ts,
      ty_wf Γ T ->
      types_wf Γ Ts ->
      types_wf Γ (T :: Ts).
