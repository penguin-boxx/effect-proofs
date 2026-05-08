(* ================================================================== *)
(* Syntax.v — locally nameless representation                         *)
(*                                                                    *)
(* Free variables are atoms (from Metalib).  Bound variables remain   *)
(* de Bruijn indices, but they are only ever opened with fresh atoms  *)
(* at binders.                                                        *)
(*                                                                    *)
(* Three variable sorts: lifetime (lt), type (ty), term (tm). Each    *)
(* has its own atom namespace.                                        *)
(* ================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.

From Metalib Require Export Metatheory.

(* ================================================================== *)
(* Lifetimes                                                          *)
(* ================================================================== *)

Inductive lifetime : Type :=
  | lt_bvar  : nat   -> lifetime  (* bound de Bruijn index *)
  | lt_fvar  : atom  -> lifetime  (* free atom *)
  | lt_free  : lifetime           (* ⊥ of lattice *)
  | lt_local : lifetime           (* ⊤ of lattice *)
  | lt_min   : lifetime -> lifetime -> lifetime
  .

(* ================================================================== *)
(* Tags                                                               *)
(* ================================================================== *)

Definition ctor_tag := nat.
Definition any_tag : ctor_tag := 0.
Definition eff_tag := nat.
Definition marker  := nat.

(* ================================================================== *)
(* Types                                                              *)
(* ================================================================== *)

Inductive type : Type :=
  | type_bvar   : nat  -> type
  | type_fvar   : atom -> type
  | type_fun    : type -> lifetime -> type -> type
  | type_ctor   : ctor_tag -> lifetime -> list type -> type
  | type_lt_all : type -> type             (* binds 1 lt    *)
  | type_ty_all : type -> type -> type     (* (bound, body) — body binds 1 ty *)
  .

(* ================================================================== *)
(* Terms                                                              *)
(*                                                                    *)
(* Term-level binders:                                                *)
(*   term_lam       : binds 1 tm                                      *)
(*   term_ty_lam    : binds 1 ty                                      *)
(*   term_lt_lam    : binds 1 lt                                      *)
(*   term_match     : yes_body binds `arity` tm vars                  *)
(*   term_handle    : body binds 1 tm; op_body binds 2 tm + n_β ty    *)
(*   term_cap       : op_body binds 2 tm + n_β ty                     *)
(*   term_resume    : binds 1 tm                                      *)
(*                                                                    *)
(* Note on multi-binders (term_match arity, term_handle/cap):         *)
(*   We open type binders FIRST (outermost), then term binders.       *)
(*   Iterated `open_term_wrt_*` with a list of atoms handles this.    *)
(* ================================================================== *)

Inductive term : Type :=
  | term_bvar      : nat -> term
  | term_fvar      : atom -> term
  | term_app       : term -> term -> term
  | term_lam       : term -> type -> term                 (* body, type *)
  | term_ty_app    : term -> type -> term
  | term_ty_lam    : type -> term -> term                 (* bound, body *)
  | term_lt_app    : term -> lifetime -> term
  | term_lt_lam    : term -> term                         (* body *)
  | term_ctor      : ctor_tag -> lifetime -> list lifetime ->
                     list type -> list term -> term
  (* match scrut against ctor of given arity: yes_body binds `arity`  *)
  (* term variables; no_body has no new binders.                      *)
  | term_match     : term -> ctor_tag -> nat -> term -> term -> term
  (* handle cap : E Ts { op_body } in body                            *)
  | term_handle    : eff_tag -> list type -> term -> term -> term
  (* perform t Ss arg                                                 *)
  | term_perform   : term -> list type -> term -> term
  (* runtime capability value                                         *)
  | term_cap       : eff_tag -> marker -> list type -> term -> term
  (* runtime continuation delimiter                                   *)
  | term_handler_m : marker -> term -> term
  (* runtime resumption: b binds 1 tm                                 *)
  | term_resume    : marker -> term -> term
  .

(* ================================================================== *)
(* Values                                                             *)
(*                                                                    *)
(* Note: lc-ness is enforced separately (see Substitution.v).         *)
(* ================================================================== *)

Inductive value : term -> Prop :=
  | value_lam    : forall body T,     value (term_lam body T)
  | value_ty_lam : forall bound body, value (term_ty_lam bound body)
  | value_lt_lam : forall body,       value (term_lt_lam body)
  | value_ctor   : forall K l lts Ts vs,
      Forall value vs ->
      value (term_ctor K l lts Ts vs)
  | value_cap    : forall E m Ts op_body,
      value (term_cap E m Ts op_body)
  | value_resume : forall m b,
      value (term_resume m b)
  .

#[export] Hint Constructors value : core.
