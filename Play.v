From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Strings.String.
Require Import Coq.Unicode.Utf8.

Inductive term : Type :=
  | bvar (i : nat) (* bound var *)
  | fvar (x : nat) (* free var *)
  | app (lhs : term) (rhs : term)
  | lam (body : term).

Inductive type : Type :=
  | ftvar (x : nat) (* free type variable *)
  | tfun (arg : type) (res : type).

Declare Custom Entry mylang.
Notation "<{ e }>" := e (e custom mylang at level 99).
Notation "( x )" := x (in custom mylang, x at level 99).
Notation "'\f' ( A1 , .. , An ) -> T" := (tfun (cons A1 .. (cons An nil) ..) T) 
  (in custom mylang at level 50, 
    A1 custom mylang at level 99,
    An custom mylang at level 99,
    right associativity).
(* Coercion ftvar : nat >-> type. *)

Example term0 : type := <{ \f ( (ftvar 1) ) -> (ftvar 3) }>.



Definition ctx := partial_map

(* Inductive typing : ctx -> syntax -> type :=
  in_ctx :  *)
