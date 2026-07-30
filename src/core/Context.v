Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.

(* =================================================================== *)
(* Typing Context                                                      *)
(*                                                                     *)
(* Γ ::= ∅  |  x:T, Γ  |  α<:B, Γ  |  l<:Δ, Γ                          *)
(*                                                                     *)
(* Each namespace uses independent de Bruijn indices.                  *)
(* Bounds are stored relative to the context *below* their binder, so  *)
(* a lookup must re-interpret the bound at the use site (the head of   *)
(* Γ).  Walking past a `bind_ty` shifts the type-variable namespace by *)
(* one (`shift_ty 1 0`); walking past a `bind_lt` shifts the lifetime  *)
(* namespace by one (`shift_lt`/`shift_lt_in_ty 1 0`).  `bind_tm`,     *)
(* `bind_ctor`, `bind_eff` introduce no ty/lt binder, so they shift    *)
(* nothing.                                                            *)

Inductive binding : Type :=
  | bind_tm  : type     -> binding  (* x : T  *)
  | bind_ty  : type     -> binding  (* α <: B *)
  | bind_lt  : lifetime -> binding  (* l <: Δ *)
  (* K : ∀ l̄(n_lt vars) ᾱ(n_ty vars). τ̄ → T@(+lt_∅(τ̄))@ᾱ               *)
  (* n_lt    : number of existential lifetime binders                  *)
  (* n_ty    : number of type binders                                  *)
  (* fields  : argument types under those binders (de Bruijn)          *)
  (* result  : result type under those binders (de Bruijn)             *)
  | bind_ctor : ctor_tag -> nat -> nat -> list type -> type -> binding
  (* Effect declaration (multi-operation, single-argument ops):        *)
  (*   effect E<n_α type-params> { opᵢ : ∀n_βᵢ type-params. sigᵢ → retᵢ } *)
  (* Each operation is a triple (n_β, sig, ret), identified by its     *)
  (* index in the list; sig is the parameter type and ret the return   *)
  (* type, both under (n_α + n_β) type-binders with α-vars innermost   *)
  (* (indices 0..n_α-1) and that op's β-vars above them.               *)
  | bind_eff : eff_tag -> nat -> list (nat * type * type) -> binding
  .

Definition ctx := list binding.

Fixpoint ctx_lookup_tm (Γ : ctx) (x : nat) : option type :=
  match Γ with
  | []                => None
  | bind_tm T :: rest =>
      match x with
      | O   => Some T
      | S n => ctx_lookup_tm rest n
      end
  | bind_ty _ :: rest => option_map (shift_ty 1 0) (ctx_lookup_tm rest x)
  | bind_lt _ :: rest => option_map (shift_lt_in_ty 1 0) (ctx_lookup_tm rest x)
  | _ :: rest         => ctx_lookup_tm rest x
  end.

Fixpoint ctx_lookup_ty (Γ : ctx) (α : nat) : option type :=
  match Γ with
  | []                => None
  | bind_ty B :: rest =>
      match α with
      | O   => Some (shift_ty 1 0 B)
      | S n => option_map (shift_ty 1 0) (ctx_lookup_ty rest n)
      end
  | bind_lt _ :: rest => option_map (shift_lt_in_ty 1 0) (ctx_lookup_ty rest α)
  | _ :: rest         => ctx_lookup_ty rest α
  end.

Fixpoint ctx_lookup_lt (Γ : ctx) (l : nat) : option lifetime :=
  match Γ with
  | []                => None
  | bind_lt Δ :: rest =>
      match l with
      | O   => Some (shift_lt 1 0 Δ)
      | S n => option_map (shift_lt 1 0) (ctx_lookup_lt rest n)
      end
  | _ :: rest         => ctx_lookup_lt rest l
  end.

Definition shift_ty_ctor_sig (amount cutoff : nat)
    (sig : nat * nat * list type * type) : nat * nat * list type * type :=
  let '(n_lt, n_ty, fields, result) := sig in
  (n_lt, n_ty,
   List.map (shift_ty amount (n_ty + cutoff)) fields,
   shift_ty amount (n_ty + cutoff) result).

Definition shift_lt_ctor_sig (amount cutoff : nat)
    (sig : nat * nat * list type * type) : nat * nat * list type * type :=
  let '(n_lt, n_ty, fields, result) := sig in
  (n_lt, n_ty,
   List.map (shift_lt_in_ty amount (n_lt + cutoff)) fields,
   shift_lt_in_ty amount (n_lt + cutoff) result).

Definition shift_ty_eff_sig (amount cutoff : nat)
    (decl : nat * list (nat * type * type)) : nat * list (nat * type * type) :=
  let '(n_α, ops) := decl in
  (n_α,
   List.map (fun '(n_β, sig_ty, ret_ty) =>
       (n_β,
        shift_ty amount (n_α + n_β + cutoff) sig_ty,
        shift_ty amount (n_α + n_β + cutoff) ret_ty)) ops).

Definition shift_lt_eff_sig (amount cutoff : nat)
    (decl : nat * list (nat * type * type)) : nat * list (nat * type * type) :=
  let '(n_α, ops) := decl in
  (n_α,
   List.map (fun '(n_β, sig_ty, ret_ty) =>
       (n_β,
        shift_lt_in_ty amount cutoff sig_ty,
        shift_lt_in_ty amount cutoff ret_ty)) ops).

(* Look up a constructor signature by tag.  Returns                   *)
(*   Some (n_lt, n_ty, fields, result)                                *)
(* where n_lt / n_ty are the numbers of lifetime / type binders, and  *)
(* fields / result use de Bruijn indices under those binders.         *)
(* Walking past ambient type/lifetime binders shifts only variables   *)
(* outside the schema binders.                                        *)
Fixpoint ctx_lookup_ctor (Γ : ctx) (K : ctor_tag)
    : option (nat * nat * list type * type) :=
  match Γ with
  | [] => None
  | bind_ctor K' n_lt n_ty fields result :: rest =>
      if Nat.eqb K K' then Some (n_lt, n_ty, fields, result)
      else ctx_lookup_ctor rest K
  | bind_ty _ :: rest => option_map (shift_ty_ctor_sig 1 0) (ctx_lookup_ctor rest K)
  | bind_lt _ :: rest => option_map (shift_lt_ctor_sig 1 0) (ctx_lookup_ctor rest K)
  | _ :: rest => ctx_lookup_ctor rest K
  end.

(* Look up an effect declaration by tag. Returns                      *)
(*   Some (n_α, ops)  with ops the per-operation (n_β, sig, ret)      *)
(* triples in declaration order.                                      *)
(* Type binders are shifted outside the α/β schema binders; lifetime  *)
(* binders shift throughout because effect schemas bind no lifetimes. *)
Fixpoint ctx_lookup_eff (Γ : ctx) (E : eff_tag)
    : option (nat * list (nat * type * type)) :=
  match Γ with
  | [] => None
  | bind_eff E' n_α ops :: rest =>
      if Nat.eqb E E' then Some (n_α, ops)
      else ctx_lookup_eff rest E
  | bind_ty _ :: rest => option_map (shift_ty_eff_sig 1 0) (ctx_lookup_eff rest E)
  | bind_lt _ :: rest => option_map (shift_lt_eff_sig 1 0) (ctx_lookup_eff rest E)
  | _ :: rest => ctx_lookup_eff rest E
  end.
