Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.

(* Lifetimes: Δ ::= free | local | Δ₁ + Δ₂                            *)
(* In the paper, + denotes the minimum (= least upper bound in the    *)
(* lattice where free <: local). lt_min D1 D2 corresponds to D1 + D2. *)
Inductive lifetime : Type :=
  | lt_var   : nat -> lifetime  (* lifetime variable *)
  | lt_free  : lifetime  (* free — bottom of lattice *)
  | lt_local : lifetime  (* local — top of lattice *)
  | lt_min   : lifetime -> lifetime -> lifetime  (* Δ₁ + Δ₂ *)
  .

Definition ctor_tag := nat.

(* Reserved constructor tag for the Any type.  An "Any@Δ" type is      *)
(* encoded as (type_ctor any_tag Δ []).  The SubAny rule allows any    *)
(* type τ to be upcast to Any@Δ provided lt_Γ(τ) <: Δ.                 *)
Definition any_tag : ctor_tag := 0.

Inductive type : Type :=
  | type_var : nat -> type
  | type_fun : type -> lifetime -> type -> type
  | type_ctor : ctor_tag -> lifetime -> list type -> type
  | type_lt_all : type -> type
  | type_ty_all : type -> type -> type  (* bound, body *)
  .

Inductive term : Type :=
  | term_var : nat -> term
  | term_app : term -> term -> term
  | term_lam : term -> type -> term
  | term_ty_app : term -> type -> term
  | term_ty_lam : type -> term -> term  (* bound, body *)
  | term_lt_app : term -> lifetime -> term
  | term_lt_lam : term -> term
  | term_ctor : ctor_tag -> lifetime -> list lifetime -> list type -> list term -> term
  (* match scrutinee against one constructor; yes_body binds each       *)
  (* constructor argument (variables 0..arity-1, outermost-first);      *)
  (* no_body is the else branch (no new binders).                       *)
  | term_match : term -> ctor_tag -> nat -> term -> term -> term
  .

(* ================================================================== *)
(* Values                                                             *)
(*                                                                    *)
(* v ::= λ(x:T). t  |  Λα. t  |  Λl. t  |  K[l; T̄](v̄)                 *)
(* ================================================================== *)

Inductive value : term -> Prop :=
  | value_lam    : forall body T,     value (term_lam body T)
  | value_ty_lam : forall bound body, value (term_ty_lam bound body)
  | value_lt_lam : forall body,       value (term_lt_lam body)
  | value_ctor   : forall K l lts Ts vs,
      Forall value vs ->
      value (term_ctor K l lts Ts vs).

Hint Constructors value : core.

(* ================================================================== *)
(* Decidable value predicate                                          *)
(*                                                                    *)
(* is_value t = true  iff  value t holds.                             *)
(* The nested go helper handles the list of constructor arguments     *)
(* (same guard-checker pattern used throughout this file).            *)
(* ================================================================== *)

Fixpoint is_value (t : term) : bool :=
  let fix go (ts : list term) : bool :=
    match ts with
    | []        => true
    | u :: rest => andb (is_value u) (go rest)
    end
  in
  match t with
  | term_lam _ _        => true
  | term_ty_lam _ _     => true
  | term_lt_lam _       => true
  | term_ctor _ _ _ _ vs  => go vs
  | _                   => false
  end.
