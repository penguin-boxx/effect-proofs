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
(* type τ to be upcast to Any@Δ provided lt_Γ(τ) <: Δ.                *)
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
  | term_ctor : ctor_tag -> lifetime -> list type -> list term -> term
  (* match scrutinee against one constructor; yes_body binds each       *)
  (* constructor argument (variables 0..arity-1, outermost-first);      *)
  (* no_body is the else branch (no new binders).                       *)
  | term_match : term -> ctor_tag -> nat -> term -> term -> term
  .

(* ================================================================== *)
(* Lifting (shifting) of de Bruijn indices                            *)
(*                                                                    *)
(* shift_X d c t  increments every free X-variable with index ≥ c    *)
(* in t by d.  The cutoff c grows by 1 each time we pass under a    *)
(* binder of kind X.                                                  *)
(* ================================================================== *)

(* --- Lifetimes --- *)

Fixpoint shift_lt (amount cutoff : nat) (l : lifetime) : lifetime :=
  match l with
  | lt_var x     => lt_var (if Nat.leb cutoff x then x + amount else x)
  | lt_free      => lt_free
  | lt_local     => lt_local
  | lt_min l1 l2 => lt_min (shift_lt amount cutoff l1) (shift_lt amount cutoff l2)
  end.

(* --- Types: shift lifetime variables --- *)

Fixpoint shift_lt_in_ty (amount cutoff : nat) (T : type) : type :=
  let fix go Ts :=
    match Ts with
    | []        => []
    | A :: rest => shift_lt_in_ty amount cutoff A :: go rest
    end
  in
  match T with
  | type_var n        => type_var n
  | type_fun A l B    => type_fun (shift_lt_in_ty amount cutoff A)
                                  (shift_lt amount cutoff l)
                                  (shift_lt_in_ty amount cutoff B)
  | type_ctor K l Ts  => type_ctor K (shift_lt amount cutoff l) (go Ts)
  | type_lt_all A     => type_lt_all (shift_lt_in_ty amount (S cutoff) A)
  | type_ty_all B A   => type_ty_all (shift_lt_in_ty amount cutoff B)
                                     (shift_lt_in_ty amount cutoff A)
  end.

Definition shift_lt_in_ty_list (amount cutoff : nat) (Ts : list type) : list type :=
  List.map (shift_lt_in_ty amount cutoff) Ts.

(* --- Types: shift type variables --- *)

Fixpoint shift_ty (amount cutoff : nat) (T : type) : type :=
  let fix go Ts :=
    match Ts with
    | []        => []
    | A :: rest => shift_ty amount cutoff A :: go rest
    end
  in
  match T with
  | type_var n        => type_var (if Nat.leb cutoff n then n + amount else n)
  | type_fun A l B    => type_fun (shift_ty amount cutoff A) l (shift_ty amount cutoff B)
  | type_ctor K l Ts  => type_ctor K l (go Ts)
  | type_lt_all A     => type_lt_all (shift_ty amount cutoff A)
  | type_ty_all B A   => type_ty_all (shift_ty amount cutoff B)
                                     (shift_ty amount (S cutoff) A)
  end.

Definition shift_ty_list (amount cutoff : nat) (Ts : list type) : list type :=
  List.map (shift_ty amount cutoff) Ts.

(* --- Terms: shift term variables --- *)

Fixpoint shift_tm (amount cutoff : nat) (t : term) : term :=
  let fix go ts :=
    match ts with
    | []        => []
    | u :: rest => shift_tm amount cutoff u :: go rest
    end
  in
  match t with
  | term_var x           => term_var (if Nat.leb cutoff x then x + amount else x)
  | term_app t1 t2       => term_app (shift_tm amount cutoff t1) (shift_tm amount cutoff t2)
  (* term_lam: body is under a term binder, cutoff grows *)
  | term_lam body T      => term_lam (shift_tm amount (S cutoff) body) T
  | term_ty_app t T      => term_ty_app (shift_tm amount cutoff t) T
  (* type/lt binders do not bind term variables *)
  | term_ty_lam bound body => term_ty_lam bound (shift_tm amount cutoff body)
  | term_lt_app t l        => term_lt_app (shift_tm amount cutoff t) l
  | term_lt_lam body     => term_lt_lam (shift_tm amount cutoff body)
  | term_ctor K l Ts ts  => term_ctor K l Ts (go ts)
  (* yes_body is under arity extra term binders; no_body is not *)
  | term_match scrut tag arity yes_body no_body =>
      term_match (shift_tm amount cutoff scrut) tag arity
                 (shift_tm amount (cutoff + arity) yes_body)
                 (shift_tm amount cutoff no_body)
  end.

(* --- Terms: shift type variables --- *)

Fixpoint shift_ty_in_tm (amount cutoff : nat) (t : term) : term :=
  let fix go ts :=
    match ts with
    | []        => []
    | u :: rest => shift_ty_in_tm amount cutoff u :: go rest
    end
  in
  match t with
  | term_var x           => term_var x
  | term_app t1 t2       => term_app (shift_ty_in_tm amount cutoff t1)
                                     (shift_ty_in_tm amount cutoff t2)
  | term_lam body T      => term_lam (shift_ty_in_tm amount cutoff body)
                                     (shift_ty amount cutoff T)
  | term_ty_app t T      => term_ty_app (shift_ty_in_tm amount cutoff t)
                                        (shift_ty amount cutoff T)
  (* term_ty_lam binds a type variable: cutoff for type vars grows *)
  (* bound is NOT under the type binder: shift at current cutoff *)
  | term_ty_lam bound body => term_ty_lam (shift_ty amount cutoff bound)
                                          (shift_ty_in_tm amount (S cutoff) body)
  | term_lt_app t l        => term_lt_app (shift_ty_in_tm amount cutoff t) l
  (* lt binder does not bind type vars *)
  | term_lt_lam body     => term_lt_lam (shift_ty_in_tm amount cutoff body)
  | term_ctor K l Ts ts  => term_ctor K l (shift_ty_list amount cutoff Ts) (go ts)
  (* match introduces no type binder; arity term binders do not affect type indices *)
  | term_match scrut tag arity yes_body no_body =>
      term_match (shift_ty_in_tm amount cutoff scrut) tag arity
                 (shift_ty_in_tm amount cutoff yes_body)
                 (shift_ty_in_tm amount cutoff no_body)
  end.

(* --- Terms: shift lifetime variables --- *)

Fixpoint shift_lt_in_tm (amount cutoff : nat) (t : term) : term :=
  let fix go ts :=
    match ts with
    | []        => []
    | u :: rest => shift_lt_in_tm amount cutoff u :: go rest
    end
  in
  match t with
  | term_var x           => term_var x
  | term_app t1 t2       => term_app (shift_lt_in_tm amount cutoff t1)
                                     (shift_lt_in_tm amount cutoff t2)
  | term_lam body T      => term_lam (shift_lt_in_tm amount cutoff body)
                                     (shift_lt_in_ty amount cutoff T)
  | term_ty_app t T      => term_ty_app (shift_lt_in_tm amount cutoff t)
                                        (shift_lt_in_ty amount cutoff T)
  (* ty binder does not bind lifetime vars *)
  | term_ty_lam bound body => term_ty_lam (shift_lt_in_ty amount cutoff bound)
                                          (shift_lt_in_tm amount cutoff body)
  | term_lt_app t l        => term_lt_app (shift_lt_in_tm amount cutoff t)
                                        (shift_lt amount cutoff l)
  (* term_lt_lam binds a lifetime variable: cutoff for lt vars grows *)
  | term_lt_lam body     => term_lt_lam (shift_lt_in_tm amount (S cutoff) body)
  | term_ctor K l Ts ts  => term_ctor K (shift_lt amount cutoff l)
                                        (shift_lt_in_ty_list amount cutoff Ts)
                                        (go ts)
  (* match introduces no lifetime binder; arity term binders do not affect lifetime indices *)
  | term_match scrut tag arity yes_body no_body =>
      term_match (shift_lt_in_tm amount cutoff scrut) tag arity
                 (shift_lt_in_tm amount cutoff yes_body)
                 (shift_lt_in_tm amount cutoff no_body)
  end.

(* ================================================================== *)
(* Substitution                                                        *)
(*                                                                    *)
(* subst_X x s t  replaces free occurrences of X-variable x in t     *)
(* with s, decrementing higher indices to close the gap.              *)
(* ================================================================== *)

(* --- Lifetime variable substitution in lifetimes --- *)

Fixpoint subst_lt (var : nat) (replacement l : lifetime) : lifetime :=
  match l with
  | lt_var y =>
      if Nat.eqb y var then replacement
      else if Nat.ltb var y then lt_var (pred y)
      else lt_var y
  | lt_free      => lt_free
  | lt_local     => lt_local
  | lt_min l1 l2 => lt_min (subst_lt var replacement l1) (subst_lt var replacement l2)
  end.

(* --- Lifetime variable substitution in types --- *)

Fixpoint subst_lt_in_ty (var : nat) (replacement : lifetime) (T : type) : type :=
  let fix go Ts :=
    match Ts with
    | []        => []
    | A :: rest => subst_lt_in_ty var replacement A :: go rest
    end
  in
  match T with
  | type_var n        => type_var n
  | type_fun A lt B   => type_fun (subst_lt_in_ty var replacement A)
                                  (subst_lt var replacement lt)
                                  (subst_lt_in_ty var replacement B)
  | type_ctor K lt Ts => type_ctor K (subst_lt var replacement lt) (go Ts)
  (* under lt_all: var shifts up, free lt vars in replacement shift up *)
  | type_lt_all A     => type_lt_all
                           (subst_lt_in_ty (S var) (shift_lt 1 0 replacement) A)
  | type_ty_all B A   => type_ty_all (subst_lt_in_ty var replacement B)
                                     (subst_lt_in_ty var replacement A)
  end.

Definition subst_lt_in_ty_list (var : nat) (replacement : lifetime) (Ts : list type)
    : list type :=
  List.map (subst_lt_in_ty var replacement) Ts.

(* --- Type variable substitution in types --- *)

Fixpoint subst_ty (var : nat) (replacement T : type) : type :=
  let fix go Ts :=
    match Ts with
    | []        => []
    | A :: rest => subst_ty var replacement A :: go rest
    end
  in
  match T with
  | type_var n =>
      if Nat.eqb n var then replacement
      else if Nat.ltb var n then type_var (pred n)
      else type_var n
  | type_fun A l B    => type_fun (subst_ty var replacement A) l (subst_ty var replacement B)
  | type_ctor K l Ts  => type_ctor K l (go Ts)
  | type_lt_all A     => type_lt_all (subst_ty var replacement A)
  (* under ty_all: var shifts up, free ty vars in replacement shift up *)
  (* bound is NOT under the binder: substitute with current var *)
  | type_ty_all B A   => type_ty_all (subst_ty var replacement B)
                                     (subst_ty (S var) (shift_ty 1 0 replacement) A)
  end.

Definition subst_ty_list (var : nat) (replacement : type) (Ts : list type) : list type :=
  List.map (subst_ty var replacement) Ts.

(* --- Term variable substitution in terms ---                              *)
(*                                                                         *)
(* When passing under a binder of kind X, the index var is unchanged       *)
(* (X ≠ term) or incremented (X = term), and free X-vars in               *)
(* replacement are shifted up by 1 to avoid capture.                       *)

Fixpoint subst_tm (var : nat) (replacement t : term) : term :=
  let fix go ts :=
    match ts with
    | []        => []
    | u :: rest => subst_tm var replacement u :: go rest
    end
  in
  match t with
  | term_var y =>
      if Nat.eqb y var then replacement
      else if Nat.ltb var y then term_var (pred y)
      else term_var y
  (* term binder: var↑1, term vars in replacement↑1 *)
  | term_lam body T     => term_lam (subst_tm (S var) (shift_tm 1 0 replacement) body) T
  | term_app t1 t2      => term_app (subst_tm var replacement t1) (subst_tm var replacement t2)
  | term_ty_app t T     => term_ty_app (subst_tm var replacement t) T
  (* type binder: var unchanged, type vars in replacement↑1 *)
  | term_ty_lam bound body => term_ty_lam bound
                               (subst_tm var (shift_ty_in_tm 1 0 replacement) body)
  | term_lt_app t l        => term_lt_app (subst_tm var replacement t) l
  (* lt binder: var unchanged, lt vars in replacement↑1 *)
  | term_lt_lam body    => term_lt_lam (subst_tm var (shift_lt_in_tm 1 0 replacement) body)
  | term_ctor K l Ts ts => term_ctor K l Ts (go ts)
  (* yes_body is under arity term binders: var shifts up by arity,       *)
  (* and term vars in replacement shift up by arity to avoid capture     *)
  | term_match scrut tag arity yes_body no_body =>
      term_match (subst_tm var replacement scrut) tag arity
                 (subst_tm (var + arity) (shift_tm arity 0 replacement) yes_body)
                 (subst_tm var replacement no_body)
  end.

(* --- Type variable substitution in terms --- *)

Fixpoint subst_ty_in_tm (var : nat) (replacement : type) (t : term) : term :=
  let fix go ts :=
    match ts with
    | []        => []
    | u :: rest => subst_ty_in_tm var replacement u :: go rest
    end
  in
  match t with
  | term_var y          => term_var y
  | term_app t1 t2      => term_app (subst_ty_in_tm var replacement t1)
                                    (subst_ty_in_tm var replacement t2)
  (* term binder: types have no term vars, so replacement unchanged *)
  | term_lam body T     => term_lam (subst_ty_in_tm var replacement body)
                                    (subst_ty var replacement T)
  | term_ty_app t T     => term_ty_app (subst_ty_in_tm var replacement t)
                                       (subst_ty var replacement T)
  (* type binder: var↑1, type vars in replacement↑1 *)
  (* bound is NOT under the binder: substitute with current var *)
  | term_ty_lam bound body => term_ty_lam (subst_ty var replacement bound)
                               (subst_ty_in_tm (S var) (shift_ty 1 0 replacement) body)
  | term_lt_app t l        => term_lt_app (subst_ty_in_tm var replacement t) l
  (* lt binder: var unchanged, lt vars in replacement↑1 *)
  | term_lt_lam body    => term_lt_lam
                             (subst_ty_in_tm var (shift_lt_in_ty 1 0 replacement) body)
  | term_ctor K l Ts ts => term_ctor K l (subst_ty_list var replacement Ts) (go ts)
  (* match introduces no type binder; arity term binders do not affect type var index *)
  | term_match scrut tag arity yes_body no_body =>
      term_match (subst_ty_in_tm var replacement scrut) tag arity
                 (subst_ty_in_tm var replacement yes_body)
                 (subst_ty_in_tm var replacement no_body)
  end.

(* --- Lifetime variable substitution in terms --- *)

Fixpoint subst_lt_in_tm (var : nat) (replacement : lifetime) (t : term) : term :=
  let fix go ts :=
    match ts with
    | []        => []
    | u :: rest => subst_lt_in_tm var replacement u :: go rest
    end
  in
  match t with
  | term_var y          => term_var y
  | term_app t1 t2      => term_app (subst_lt_in_tm var replacement t1)
                                    (subst_lt_in_tm var replacement t2)
  (* term/type binders do not bind lt vars; replacement needs no adjustment *)
  | term_lam body T     => term_lam (subst_lt_in_tm var replacement body)
                                    (subst_lt_in_ty var replacement T)
  | term_ty_app t T     => term_ty_app (subst_lt_in_tm var replacement t)
                                       (subst_lt_in_ty var replacement T)
  | term_ty_lam bound body => term_ty_lam (subst_lt_in_ty var replacement bound)
                               (subst_lt_in_tm var replacement body)
  | term_lt_app t l        => term_lt_app (subst_lt_in_tm var replacement t)
                                       (subst_lt var replacement l)
  (* lt binder: var↑1, lt vars in replacement↑1 *)
  | term_lt_lam body    => term_lt_lam
                             (subst_lt_in_tm (S var) (shift_lt 1 0 replacement) body)
  | term_ctor K l Ts ts => term_ctor K (subst_lt var replacement l)
                                       (subst_lt_in_ty_list var replacement Ts)
                                       (go ts)
  (* match introduces no lifetime binder; arity term binders do not affect lifetime var index *)
  | term_match scrut tag arity yes_body no_body =>
      term_match (subst_lt_in_tm var replacement scrut) tag arity
                 (subst_lt_in_tm var replacement yes_body)
                 (subst_lt_in_tm var replacement no_body)
  end.

(* ================================================================== *)
(* Simultaneous substitution of constructor arguments                  *)
(*                                                                     *)
(* subst_list_tm vs t  substitutes vs[0] for variable 0, vs[1] for    *)
(* variable 1, ..., vs[n-1] for variable n-1 in t, which is assumed   *)
(* to be under exactly n = length vs term binders.  Variables 0..n-1  *)
(* correspond to constructor arguments outermost-first.                *)
(*                                                                     *)
(* Implementation: substitute each argument from outermost (index 0)  *)
(* to innermost.  When substituting vs[i] (the head of the remaining  *)
(* list) for variable 0, we first shift vs[i] by (length rest) to     *)
(* compensate for the remaining open binders; each substitution closes *)
(* one binder and decrements the remaining variable indices by one.    *)
(* ================================================================== *)

Fixpoint subst_list_tm (vs : list term) (t : term) : term :=
  match vs with
  | []         => t
  | v :: rest  =>
      subst_list_tm rest
        (subst_tm 0 (shift_tm (List.length rest) 0 v) t)
  end.

(* ================================================================== *)
(* Values                                                             *)
(*                                                                    *)
(* v ::= λ(x:T). t  |  Λα. t  |  Λl. t  |  K[l; T̄](v̄)             *)
(* ================================================================== *)

Inductive value : term -> Prop :=
  | V_Abs   : forall body T,    value (term_lam body T)
  | V_TyLam : forall bound body, value (term_ty_lam bound body)
  | V_LtLam : forall body,       value (term_lt_lam body)
  | V_Ctor  : forall K l Ts vs,
      Forall value vs ->
      value (term_ctor K l Ts vs).

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
  | term_ctor _ _ _ vs  => go vs
  | _                   => false
  end.

(* ================================================================== *)
(* Small-step call-by-value operational semantics                     *)
(*                                                                    *)
(*  (β)     (λ(x:T). t) v   ==>  [0↦v] t                            *)
(*  (β_ty)  (Λα. t) [T]     ==>  [0↦T] t                            *)
(*  (β_lt)  (Λl. t) {Δ}     ==>  [0↦Δ] t                            *)
(*  plus congruence rules for the call-by-value evaluation context    *)
