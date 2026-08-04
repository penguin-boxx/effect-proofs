Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Context.

(* ================================================================== *)
(* lt_of_ty : compute lt_∅(τ)                                         *)
(*                                                                    *)
(* lt_∅(τ) is the minimum of all lifetime restrictions in τ when      *)
(* evaluated at the empty context (type variables have no bound →     *)
(* contribute nothing).                                               *)
(*                                                                    *)
(*   lt_∅(α)           = free          (no bound in empty ctx)        *)
(*   lt_∅(T Δ τ̄)       = lt_join Δ     (lt_join of lt_∅(τ̄))           *)
(*   lt_∅(τ̄ Δ → σ)     = Δ             (only the closure lt matters)  *)
(*   lt_∅(∀l.τ)        = local         (conservative top)             *)
(*   lt_∅(∀(α<:B).τ)   = local         (conservative top)             *)
(* ================================================================== *)

Fixpoint lt_of_ty (T : type) : lifetime :=
  match T with
  | type_var _        => lt_free
  | type_fun _ l _    => l
  | type_ctor _ l Ts  =>
      lt_join l (List.fold_right (fun A acc => lt_join (lt_of_ty A) acc) lt_free Ts)
  | type_lt_all A     => lt_local
  | type_ty_all _ A   => lt_local
  end.

Definition lt_of_ty_list (Ts : list type) : lifetime :=
  List.fold_right (fun T acc => lt_join (lt_of_ty T) acc) lt_free Ts.

(* ================================================================== *)
(* Γ-aware lt_Γ(τ)                                                    *)
(*                                                                    *)
(*   lt_Γ(α) = lt_Γ(B)    if (α <: B) ∈ Γ                             *)
(*   lt_Γ(α) = free       otherwise                                   *)
(*                                                                    *)
(* Fuel is used to guarantee termination; calling with fuel = |Γ|     *)
(* bounds the chain length through type variables.                    *)
(* ================================================================== *)

Fixpoint lt_of_ty_ctx (fuel : nat) (Γ : ctx) (T : type) : lifetime :=
  let fix go (T : type) : lifetime :=
    match T with
    | type_var α =>
        match fuel with
        | O => lt_free
        | S fuel' =>
            match ctx_lookup_ty Γ α with
            | Some B => lt_of_ty_ctx fuel' Γ B
            | None   => lt_free
            end
        end
    | type_fun _ l _    => l
    | type_ctor _ l Ts  =>
        lt_join l (List.fold_right (fun A acc => lt_join (go A) acc) lt_free Ts)
    | type_lt_all A     => lt_local
    | type_ty_all _ A   => lt_local
    end
  in go T.

Definition lt_of_ty_G (Γ : ctx) (T : type) : lifetime :=
  lt_of_ty_ctx (List.length Γ) Γ T.

(* DESIGN NOTE — why two escape-lifetime families.                     *)
(* [lt_of_ty]/[lt_of_ty_list] are context-free (a type variable        *)
(* contributes [free], i.e. no constraint); [lt_of_ty_ctx]/[lt_of_ty_G]*)
(* consult the variable's bound in Γ.  The context-free family is used *)
(* ONLY by T_Ctor, on the already-instantiated field types: demanding  *)
(* the Γ-aware lifetime there would strengthen the premise on          *)
(* polymorphic constructor fields (a variable bounded by a local type  *)
(* would suddenly count as local) and lose source programs.  All other *)
(* rules (T_Lam's capture, T_Handle/T_HandlerM's answer check,         *)
(* T_Perform's boundary check) use the Γ-aware [lt_of_ty_G].  The two  *)
(* are reconciled where needed by the bridge lemmas                    *)
(* [lt_of_ty_list_le_lt_of_ty_ctx_list] (SubstTy.v) — context-free is  *)
(* below context-aware — and [lt_of_ty_G_ty_closed_eq] (Weakening.v) — *)
(* they agree on closed types.                                         *)

(* ================================================================== *)
(* "no local in l" — syntactic absence of [lt_local] in a lifetime.   *)
(* Conservative on lifetime variables.  The typing rules do not       *)
(* consult it; the deep-escape theorems (safety/Escape.v) and the     *)
(* boundary theorems (safety/Boundary.v) use it to state their        *)
(* conclusions.                                                       *)
(* ================================================================== *)

Fixpoint no_local_lt (l : lifetime) : bool :=
  match l with
  | lt_var _      => false
  | lt_local      => false
  | lt_join l1 l2  => andb (no_local_lt l1) (no_local_lt l2)
  | _             => true
  end.


(* ================================================================== *)
(* Free term variables and capture lifetime                           *)
(*                                                                    *)
(* free_tm_vars c t : indices of free term vars in t that lie         *)
(*   ≥ c (with c subtracted).  Used with c = 1 inside T_Lam (the      *)
(*   lambda's own binder is "consumed").                              *)
(*                                                                    *)
(* capture_lt Γ body : +lt_Γ(τ̄) over captured variables' types —      *)
(* the closure-lifetime bound in the Lam rule.                        *)
(*   Marker-aware: a literal runtime marker form (term_cap /          *)
(*   term_handler_m) anywhere in the body forces the                  *)
(*   closure lifetime to lt_local, since free_tm_vars cannot see      *)
(*   literal marker forms.                                            *)
(* ================================================================== *)

Fixpoint free_tm_vars (cutoff : nat) (t : term) : list nat :=
  match t with
  | term_var x =>
      if Nat.ltb x cutoff then [] else [x - cutoff]
  | term_app t1 t2       => free_tm_vars cutoff t1 ++ free_tm_vars cutoff t2
  | term_lam body _      => free_tm_vars (S cutoff) body
  | term_ty_app t _      => free_tm_vars cutoff t
  | term_ty_lam _ body   => free_tm_vars cutoff body
  | term_lt_app t _      => free_tm_vars cutoff t
  | term_lt_lam body     => free_tm_vars cutoff body
  | term_ctor _ _ _ _ ts => List.concat (List.map (free_tm_vars cutoff) ts)
  | term_match scrut _ _ arity y n =>
      free_tm_vars cutoff scrut
        ++ free_tm_vars (cutoff + arity) y
        ++ free_tm_vars cutoff n
  | term_handle _ _ _ _ op_bodies body =>
      List.concat (List.map (fun '(_, ob) => free_tm_vars (cutoff + 2) ob) op_bodies)
        ++ free_tm_vars (S cutoff) body
  | term_perform t _ _ _ arg =>
      free_tm_vars cutoff t ++ free_tm_vars cutoff arg
  | term_cap _ _ _ _ op_bodies =>
      List.concat (List.map (fun '(_, ob) => free_tm_vars (cutoff + 2) ob) op_bodies)
  | term_handler_m _ _ _ t => free_tm_vars cutoff t
  end.

Definition capture_lt (Γ : ctx) (body : term) : lifetime :=
  if has_rt_marker body then lt_local
  else
    fold_right (fun x acc =>
      lt_join
        match ctx_lookup_tm Γ x with
        | Some T => lt_of_ty_G Γ T
        | None   => lt_free
        end
        acc)
      lt_free
      (free_tm_vars 1 body).
