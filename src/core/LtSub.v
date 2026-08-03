Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Context.
Require Import Wf.

Reserved Notation "G '⊢ₗ' l1 '<:' l2" (at level 40, l1 at next level).

(* ================================================================== *)
(* Lifetime subtyping                                                 *)
(*                                                                    *)
(* Γ ⊢ₗ Δ' <: Δ  means Δ' "outlives" Δ in the         lattice:        *)
(*   free (bottom) <: local (top)                                     *)
(*   lt_join l1 l2 is the join (= least upper bound) of l1 and l2      *)
(*                                                                    *)
(* Rules:                                                             *)
(*   LS_Free    :  Γ ⊢ₗ free  <: Δ          (free is bottom)          *)
(*   LS_Local   :  Γ ⊢ₗ Δ <: local          (local is top)            *)
(*   LS_Var     :  (l <: Δ) ∈ Γ → Γ ⊢ₗ l <: Δ  (SubCtx_Δ)             *)
(*   LS_Refl    :  Γ ⊢ₗ Δ <: Δ                                        *)
(*   LS_Trans   :  transitivity                                       *)
(*   LS_JoinL    :  Γ ⊢ₗ l1 <: l → Γ ⊢ₗ l2 <: l →                      *)
(*                  Γ ⊢ₗ lt_join l1 l2 <: l    (Sub+: join ≤ upper bd) *)
(*   LS_JoinR1   :  Γ ⊢ₗ l <: l1 → Γ ⊢ₗ l <: lt_join l1 l2              *)
(*   LS_JoinR2   :  Γ ⊢ₗ l <: l2 → Γ ⊢ₗ l <: lt_join l1 l2              *)
(* ================================================================== *)

Inductive lt_sub : ctx -> lifetime -> lifetime -> Prop :=

  | LS_Free  : forall Γ l,
      lt_wf Γ l ->
      Γ ⊢ₗ lt_free <: l

  | LS_Local : forall Γ l,
      lt_wf Γ l ->
      Γ ⊢ₗ l <: lt_local

  | LS_Var   : forall Γ x Δ,
      ctx_lookup_lt Γ x = Some Δ ->
      lt_wf Γ Δ ->
      Γ ⊢ₗ lt_var x <: Δ

  | LS_Refl  : forall Γ l,
      lt_wf Γ l ->
      Γ ⊢ₗ l <: l

  | LS_Trans : forall Γ l1 l2 l3,
      Γ ⊢ₗ l1 <: l2 ->
      Γ ⊢ₗ l2 <: l3 ->
      Γ ⊢ₗ l1 <: l3

  (* lt_join l1 l2 is the join; it lies above both l1 and l2,           *)
  (* and is the least such: if both l1 <: l and l2 <: l then           *)
  (* lt_join l1 l2 <: l.                                                *)
  | LS_JoinL  : forall Γ l1 l2 l,
      Γ ⊢ₗ l1 <: l ->
      Γ ⊢ₗ l2 <: l ->
      Γ ⊢ₗ lt_join l1 l2 <: l

  | LS_JoinR1 : forall Γ l l1 l2,
      Γ ⊢ₗ l <: l1 ->
      lt_wf Γ l2 ->
      Γ ⊢ₗ l <: lt_join l1 l2

  | LS_JoinR2 : forall Γ l l1 l2,
      Γ ⊢ₗ l <: l2 ->
      lt_wf Γ l1 ->
      Γ ⊢ₗ l <: lt_join l1 l2

where "G '⊢ₗ' l1 '<:' l2" := (lt_sub G l1 l2).

Hint Constructors lt_sub : core.

(* Regularity: both sides of a lifetime-subtyping judgment are wf.    *)
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
