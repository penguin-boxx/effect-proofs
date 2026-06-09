Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.

(* Lifetimes: Δ ::= free | local | Δ₁ + Δ₂                            *)
(* + denotes the minimum (= least upper bound in the lattice where    *)
(* free <: local). lt_min D1 D2 corresponds to D1 + D2.               *)
Inductive lifetime : Type :=
  | lt_var   : nat -> lifetime  (* lifetime variable *)
  | lt_free  : lifetime  (* free — bottom of lattice *)
  | lt_local : lifetime  (* local — top of lattice *)
  | lt_min   : lifetime -> lifetime -> lifetime  (* Δ₁ + Δ₂ *)
  .

Definition ctor_tag := nat.

(* Reserved constructor tag for the Any type.  An "Any'Δ" type is      *)
(* encoded as (type_ctor any_tag Δ []).  The SubAny rule allows any    *)
(* type τ to be upcast to Any@Δ provided lt_Γ(τ) <: Δ.                 *)
Definition any_tag : ctor_tag := 0.

(* ================================================================== *)
(* Effect handlers                                                    *)
(*                                                                    *)
(* Capabilities reuse the existing data-constructor machinery: a      *)
(* capability for effect E with type-args T̄ has type                  *)
(*    type_ctor E_tag local T̄                                         *)
(* The effect declaration                                             *)
(*    effect E<ᾱ> { op_i : ∀β̄ᵢ. σ̄ᵢ → σ'ᵢ }                            *)
(* registers a capability constructor                                 *)
(*    K_cap_E : ∀ᾱ. sig_E → E local ᾱ                                 *)
(* (encoded in Γ as a `bind_eff` entry; see Typing.v).                *)
(*                                                                    *)
(* eff_tag is a ctor_tag used by capability type_ctor's; we keep the  *)
(* alias for documentation. The disjointness of effect-tags from      *)
(* data-constructor-tags is enforced at typing time by side conditions*)
(* on T_Ctor / T_Match (`ctx_lookup_eff Γ K = None`).                 *)
(*                                                                    *)
(* SIMPLIFICATION: each effect declares exactly one operation.        *)
(* Hence there is no `op_tag`, `term_handle` carries a single         *)
(* op-body, and `term_perform` takes no op-tag.                       *)
(* ================================================================== *)

Definition eff_tag := nat.
Definition marker  := nat.

Inductive type : Type :=
  | type_var : nat -> type
  | type_fun : type -> lifetime -> type -> type
  | type_ctor : ctor_tag -> lifetime -> list type -> type
  | type_lt_all : type -> type  (* bound *)
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
  (* ctor, resulting lifetime (min of all), argument lifetimes, argument types, argument terms *)
  | term_ctor : ctor_tag -> lifetime -> list lifetime -> list type -> list term -> term
  (* match scrutinee against one constructor. yes_body binds n_lt      *)
  (* constructor lifetime parameters and arity constructor arguments   *)
  (* (term variables 0..arity-1, outermost-first). no_body has no new  *)
  (* binders.                                                          *)
  | term_match : term -> ctor_tag -> nat -> nat -> term -> term -> term
  (* ----- effect handlers -----                                       *)
  (* handle cap : E n_β Ts { op_body } in body                         *)
  (* The body has 1 extra term-binder for the cap value (variable 0).  *)
  (* op_body has n_β type-binders (outermost) followed by 2 term-      *)
  (* binders:                                                          *)
  (*   index 0 = the (single) op argument                              *)
  (*   index 1 = the resumption k                                      *)
  | term_handle : eff_tag -> nat -> list type -> term -> term -> term
  (* perform x Ss arg — Ss instantiates the operation's β-args.        *)
  | term_perform : term -> list type -> term -> term
  (* runtime-only: capability value (paper's K_cap τ̄ m h).             *)
  (* Carries effect tag, marker, β-arity, α-type-args, and op_body.    *)
  | term_cap : eff_tag -> marker -> nat -> list type -> term -> term
  (* runtime-only: continuation delimiter (paper's handler_m t).       *)
  | term_handler_m : marker -> term -> term
  (* runtime-only: reified resumption value. `term_resume m b` is the  *)
  (* one-argument resumption produced by H_Perform; `b` has +1 term    *)
  (* binder (the slot for the resumed value).                          *)
  | term_resume : marker -> term -> term
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
      value (term_ctor K l lts Ts vs)
    | value_cap    : forall E m n_β Ts op_body,
      value (term_cap E m n_β Ts op_body)
  | value_resume : forall m b,
      value (term_resume m b)
  .

Hint Constructors value : core.

(* ================================================================== *)
(* Decidable value predicate                                          *)
(*                                                                    *)
(* is_value t = true  iff  value t holds.                             *)
(* The nested go helper handles the list of constructor arguments.    *)
(* ================================================================== *)

Fixpoint is_value (t : term) : bool :=
  let fix go (ts : list term) : bool :=
    match ts with
    | []        => true
    | u :: rest => andb (is_value u) (go rest)
    end
  in
  match t with
  | term_lam _ _          => true
  | term_ty_lam _ _       => true
  | term_lt_lam _         => true
  | term_ctor _ _ _ _ vs  => go vs
  | term_cap _ _ _ _ _    => true
  | term_resume _ _       => true
  | _                     => false
  end.
