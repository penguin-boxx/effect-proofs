Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Context.

(* ================================================================== *)
(* Helpers for constructor typing and match elimination               *)
(*                                                                    *)
(* These must be defined before `typing` so T_Ctor / T_Match can use  *)
(* them as proper inductive constructors rather than Axioms.          *)
(* ================================================================== *)

(* Instantiate n_ty type-binders (outermost-first) by substituting Ts.  *)
(* Each head argument is lifted over the remaining schema binders so    *)
(* later substitutions cannot capture its free type variables.          *)
Fixpoint inst_ty_vars (n : nat) (Ts : list type) (T : type) : type :=
  match n, Ts with
  | O, _            => T
  | S n', U :: rest => inst_ty_vars n' rest (subst_ty 0 (shift_ty n' 0 U) T)
  | S _, []         => T
  end.

(* ------------------------------------------------------------------- *)
(* Parallel substitution of lifetime schema variables.                 *)
(*                                                                     *)
(* `multi_subst_lt cutoff lts l` and `multi_subst_lt_in_ty` walk under *)
(* binders and replace `lt_var i` (with i ≥ cutoff) by either:         *)
(*   - lts[i - cutoff], lifted under `cutoff` extra binders, when      *)
(*     i - cutoff < |lts|, or                                          *)
(*   - lt_var (i - |lts|), otherwise (closing |lts| schema binders).   *)
(*                                                                     *)
(* This gives a clean semantics: lts[k] replaces schema-var-k, and     *)
(* lts[k] itself is read in the *outer* (post-instantiation) ctx —     *)
(* the user does NOT need to pre-shift entries.                        *)
(* ------------------------------------------------------------------- *)

Fixpoint multi_subst_lt (cutoff : nat) (lts : list lifetime) (l : lifetime)
    : lifetime :=
  match l with
  | lt_free       => lt_free
  | lt_local      => lt_local
  | lt_join l1 l2  => lt_join (multi_subst_lt cutoff lts l1)
                            (multi_subst_lt cutoff lts l2)
  | lt_var x =>
      if Nat.ltb x cutoff then lt_var x
      else
        let x' := x - cutoff in
        if Nat.ltb x' (List.length lts) then
          shift_lt cutoff 0 (List.nth x' lts lt_free)
        else
          lt_var (x - List.length lts)
  end.

Fixpoint multi_subst_lt_in_ty (cutoff : nat) (lts : list lifetime) (T : type)
    : type :=
  match T with
  | type_var n        => type_var n
  | type_fun A l B    => type_fun (multi_subst_lt_in_ty cutoff lts A)
                                  (multi_subst_lt cutoff lts l)
                                  (multi_subst_lt_in_ty cutoff lts B)
  | type_ctor K l Ts  => type_ctor K (multi_subst_lt cutoff lts l)
                                   (List.map (multi_subst_lt_in_ty cutoff lts) Ts)
  | type_lt_all A     => type_lt_all (multi_subst_lt_in_ty (S cutoff) lts A)
  | type_ty_all B A   => type_ty_all (multi_subst_lt_in_ty cutoff lts B)
                                     (multi_subst_lt_in_ty cutoff lts A)
  end.

(* Instantiate the n_lt lt-binders of a schema by parallel substitution. *)
(* lts[k] replaces schema-var-k and lives in the outer context (no       *)
(* pre-shifting required). The `n` parameter is kept for documentation   *)
(* and is intended to satisfy `n = length lts` at all call sites.        *)
Definition inst_lt_vars (_n : nat) (lts : list lifetime) (T : type) : type :=
  multi_subst_lt_in_ty 0 lts T.

(* Instantiate a constructor field/result type: first type vars, then  *)
(* lt vars. Type arguments live outside the constructor's lifetime     *)
(* schema binders, so lift them over that binder block before type     *)
(* substitution; otherwise the later lifetime substitution would       *)
(* capture free lifetimes in the type arguments.                       *)
Definition inst_ctor_type (n_lt n_ty : nat) (lts : list lifetime) (Ts : list type)
    (T : type) : type :=
  inst_lt_vars n_lt lts (inst_ty_vars n_ty (List.map (shift_lt_in_ty n_lt 0) Ts) T).

(* MATCH variant of [inst_ctor_type].  In the yes-branch the schema's      *)
(* n_lt lt-binders ARE the freshly pushed match lt-vars (lt_var 0..n_lt-1),*)
(* so they need no instantiation — only the n_ty type arguments are filled *)
(* (lifted over the n_lt lt-binders).  Using the full [inst_ctor_type]     *)
(* here would apply [inst_lt_vars (lt_var_list n_lt)], whose only net      *)
(* effect is a spurious down-shift (multi_subst_lt's [lt_var (x-|lts|)]    *)
(* branch) that ALIASES Ts-derived field lifetimes with the fresh match    *)
(* lt-vars — breaking type-substitution commutation.  Keeping the schema   *)
(* lt-vars abstract leaves rho_fields living consistently in the pushed    *)
(* context Γ'.                                                             *)
Definition inst_ctor_type_open (n_lt n_ty : nat) (Ts : list type)
    (T : type) : type :=
  inst_ty_vars n_ty (List.map (shift_lt_in_ty n_lt 0) Ts) T.

(* Push n fresh bind_lt entries (all bounded by `bound`) onto Γ.      *)
Fixpoint push_lt_vars (n : nat) (bound : lifetime) (Γ : ctx) : ctx :=
  match n with
  | O    => Γ
  | S n' => push_lt_vars n' bound (bind_lt bound :: Γ)
  end.

(* Push n fresh bind_ty entries (all bounded by `bound`) onto Γ.      *)
Fixpoint push_ty_vars (n : nat) (bound : type) (Γ : ctx) : ctx :=
  match n with
  | O    => Γ
  | S n' => push_ty_vars n' bound (bind_ty bound :: Γ)
  end.

(* Push n fresh bind_lt entries for a match/destructuring, each        *)
(* bounded by the scrutinee lifetime `Delta` (which lives in the       *)
(* OUTER Γ).  Unlike [push_lt_vars], the bound stored at level j is     *)
(* [shift_lt j 0 Delta], i.e. Delta lifted into that level's scope, so  *)
(* that EVERY pushed variable has the same effective upper bound        *)
(* [shift_lt n 0 Delta] = the one outer Delta (no per-level meaning     *)
(* drift).  This is the de-Bruijn-correct realisation of the            *)
(* match rule premise "l'_i <: Delta": the n fresh lifetimes            *)
(* are INDEPENDENTLY bounded by Delta, with no spurious inter-variable  *)
(* constraints.  Crucially it is STABLE under lt-substitution and       *)
(* lt-insertion of an outer binder (the per-level shifts commute with   *)
(* subst/shift — see [shift_lt_subst_lt_comm_many0]), which             *)
(* [push_lt_vars] is not.  For lt-closed Delta the two coincide.        *)
Fixpoint push_match_bound (n : nat) (Delta : lifetime) (Γ : ctx) : ctx :=
  match n with
  | O    => Γ
  | S n' => bind_lt (shift_lt n' 0 Delta) :: push_match_bound n' Delta Γ
  end.

(* The β-bound used for polymorphic operations: `Any@free`.            *)
(* We pick `lt_free` so that β-types may not contain `local`-tagged    *)
(* values, ensuring escape-analysis safety.                            *)
Definition any_at_free : type := type_ctor any_tag lt_free [].

(* Instantiate the α part of an op schema while β-vars remain bound.  *)
(* α arguments must be lifted over the remaining β binders so ambient *)
(* type variables in Ts cannot be captured by β instantiation later.  *)
Definition inst_op_ty_args (n_α : nat) (Ts : list type)
                         (n_β : nat) (T : type) : type :=
  inst_ty_vars n_α (List.map (shift_ty n_β 0) Ts) T.

(* Instantiate an op schema: substitute α-vars first, then β-vars.    *)
(* Convention: in the schema, α-vars are innermost (indices 0..n_α-1) *)
(* and β-vars are outermost (indices n_α..n_α+n_β-1).                 *)
Definition inst_op_all_args (n_α : nat) (Ts : list type)
                       (n_β : nat) (Ss : list type)
                       (T : type) : type :=
  inst_ty_vars n_β Ss (inst_op_ty_args n_α Ts n_β T).

(* [lt_var 0; lt_var 1; ...; lt_var (n-1)] — de Bruijn indices of the *)
(* n freshly pushed lt-vars in the order matching `inst_lt_vars`:     *)
(* schema-var-k is replaced by lt_var k (lt_var 0 is innermost).      *)
Definition lt_var_list (n : nat) : list lifetime :=
  List.map lt_var (List.seq 0 n).
