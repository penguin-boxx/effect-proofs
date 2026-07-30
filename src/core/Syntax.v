Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.

(* Lifetimes: Δ ::= free | local | Δ₁ + Δ₂                            *)
(* `lt_join D1 D2` (written Δ₁ + Δ₂) is the lattice JOIN (least upper *)
(* bound) in the subtyping order, where `free <: local` (free at the  *)
(* bottom, local at the top): LS_JoinL / LS_JoinR1 / LS_JoinR2 in     *)
(* Typing.v place it above both operands.  Duration-wise the join is  *)
(* the SHORTER of the two lifetimes — the more restrictive one.       *)
Inductive lifetime : Type :=
  | lt_var   : nat -> lifetime  (* lifetime variable *)
  | lt_free  : lifetime  (* free — bottom of lattice *)
  | lt_local : lifetime  (* local — top of lattice *)
  | lt_join  : lifetime -> lifetime -> lifetime  (* Δ₁ + Δ₂ *)
  .

Definition ctor_tag := nat.

(* Reserved constructor tag for the Any type.  An "Any'Δ" type is      *)
(* encoded as (type_ctor any_tag Δ []).  The SubAny rule allows any    *)
(* type τ to be upcast to Any@Δ provided lt_Γ(τ) <: Δ.                 *)
Definition any_tag : ctor_tag := 0.

(* =================================================================== *)
(* Effect handlers                                                     *)
(*                                                                     *)
(* Capabilities reuse the existing data-constructor machinery: a       *)
(* capability for effect E with type-args T̄ has type                   *)
(*    type_ctor E_tag local T̄                                          *)
(* The effect declaration                                              *)
(*    effect E<ᾱ> { op_i : ∀β̄ᵢ. σ̄ᵢ → σ'ᵢ }                             *)
(* registers a capability constructor                                  *)
(*    K_cap_E : ∀ᾱ. sig_E → E local ᾱ                                  *)
(* (encoded in Γ as a `bind_eff` entry; see Typing.v).                 *)
(*                                                                     *)
(* eff_tag is a ctor_tag used by capability type_ctor's; we keep the   *)
(* alias for documentation. The disjointness of effect-tags from       *)
(* data-constructor-tags is enforced at typing time by side conditions *)
(* on T_Ctor / T_Match (`ctx_lookup_eff Γ K = None`).                  *)
(*                                                                     *)
(* Effects declare a LIST of operations; an operation is identified    *)
(* by its declaration index, which `term_perform` carries.             *)
(* =================================================================== *)

Definition eff_tag := nat.
Definition marker  := nat.

Inductive type : Type :=
  | type_var : nat -> type
  | type_fun : type -> lifetime -> type -> type
  | type_ctor : ctor_tag -> lifetime -> list type -> type
  | type_lt_all : type -> type          (* bound       *)
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
  (* handle cap : E Ts { op_bodies } in body                           *)
  (* The body has 1 extra term-binder for the cap value (variable 0).  *)
  (* op_bodies is one (n_β, body) pair PER OPERATION of the effect,    *)
  (* in declaration order; operation i's body has n_β_i type-binders   *)
  (* (outermost) followed by 2 term-binders:                           *)
  (*   index 0 = the op argument                                       *)
  (*   index 1 = the resumption k                                      *)
  (* The per-op n_β annotation is what lets the type-substitution      *)
  (* functions know how many type binders they are crossing.           *)
  (* effect, effect type parameters, body's no-local type, public      *)
  (* result type, per-op (n_β, body) list, handler's body.             *)
  | term_handle : eff_tag -> list type -> type -> type
                    -> list (nat * term) -> term -> term
  (* perform x op Ss A arg — op selects the effect's operation by      *)
  (* declaration index; Ss instantiates that operation's β-args; A is  *)
  (* the instantiated operation result type (T_Perform pins it to      *)
  (* ret_inst).  H_Perform reads it off the redex to annotate the      *)
  (* continuation lambda it reifies.                                   *)
  | term_perform : term -> nat -> list type -> type -> term -> term
  (* runtime-only: capability value.                                   *)
  (* Carries effect tag, marker, α-type-args, the delimiter's public   *)
  (* answer type, and the per-op (n_β, body) list.                     *)
  | term_cap : eff_tag -> marker -> list type -> type
                 -> list (nat * term) -> term
  (* runtime-only: continuation delimiter with body/public answers.    *)
  | term_handler_m : marker -> type -> type -> term -> term
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
  | value_cap    : forall E m Ts T_R op_bodies,
      value (term_cap E m Ts T_R op_bodies)
  .

Hint Constructors value : core.

(* ================================================================== *)
(* Abstraction head check (the "prenex-Λ" value restriction)          *)
(*                                                                    *)
(* is_abs t = true iff t is a term/type/lifetime abstraction.         *)
(* T_TyLam / T_LtLam (Typing.v) require their body to satisfy is_abs, *)
(* so every maximal Λ-chain bottoms out at a λ.  This keeps Λ-bodies  *)
(* values under weak reduction, and routes every capability captured  *)
(* under a Λ-chain through the innermost λ's (cap-aware) capture_lt,  *)
(* which records it in the closure-lifetime slot of the type.         *)
(* ================================================================== *)

Definition is_abs (t : term) : bool :=
  match t with
  | term_lam _ _    => true
  | term_ty_lam _ _ => true
  | term_lt_lam _   => true
  | _               => false
  end.

(* ================================================================== *)
(* Runtime-capability occurrence check                                *)
(*                                                                    *)
(* has_rt_cap t = true iff a literal runtime form that mentions a     *)
(* marker — term_cap or term_handler_m — occurs                       *)
(* anywhere syntactically in t (under all binders).  These are        *)
(* exactly the constructors counted by markers_in (Semantics.v).      *)
(* Source programs never contain them; they arise only at runtime.    *)
(* Used by capture_lt (Typing.v) to make closure lifetimes account    *)
(* for literal capabilities, which free_tm_vars cannot see.           *)
(* ================================================================== *)

Fixpoint has_rt_cap (t : term) : bool :=
  match t with
  | term_var _                  => false
  | term_app t1 t2              => orb (has_rt_cap t1) (has_rt_cap t2)
  | term_lam body _             => has_rt_cap body
  | term_ty_app t' _            => has_rt_cap t'
  | term_ty_lam _ body          => has_rt_cap body
  | term_lt_app t' _            => has_rt_cap t'
  | term_lt_lam body            => has_rt_cap body
  | term_ctor _ _ _ _ ts        => existsb has_rt_cap ts
  | term_match scrut _ _ _ y n  =>
      orb (has_rt_cap scrut) (orb (has_rt_cap y) (has_rt_cap n))
  | term_handle _ _ _ _ op_bodies body =>
      orb (existsb (fun '(_, ob) => has_rt_cap ob) op_bodies)
          (has_rt_cap body)
  | term_perform t' _ _ _ arg   => orb (has_rt_cap t') (has_rt_cap arg)
  | term_cap _ _ _ _ _          => true
  | term_handler_m _ _ _ _      => true
  end.

(* [lang]: an opt-in hint database collecting the constructors of the
   judgments of the calculus (registered here, in Semantics.v, and in
   Typing.v).  New downstream proofs can use [eauto with lang] instead
   of relying on the historical [core] registrations. *)
Create HintDb lang.
#[export] Hint Constructors value : lang.
