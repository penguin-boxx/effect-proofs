Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Context.
Require Import LtAnalysis.

(* ================================================================== *)
(* Variance positions for elim                                        *)
(* ================================================================== *)

Inductive variance : Type :=
  | var_pos : variance   (* covariant / positive *)
  | var_neg : variance   (* contravariant / negative *)
  | var_inv : variance   (* invariant *)
  .

Definition flip_variance (p : variance) : variance :=
  match p with
  | var_pos => var_neg
  | var_neg => var_pos
  | var_inv => var_inv
  end.

(* ================================================================== *)
(* elim_lt / elim_ty : eliminate a single fresh lifetime variable     *)
(* from a type.                                                       *)
(*                                                                    *)
(* elim_ty lvar Δ p T                                                 *)
(*   eliminates lt_var lvar from T, approximating with:               *)
(*     Δ     in positive (covariant) positions                        *)
(*     free  in negative (contravariant) positions                    *)
(*     error (returns None) in invariant positions                    *)
(*                                                                    *)
(* We return option type; None = error.                               *)
(* We eliminate multiple vars by folding over the list.               *)
(* ================================================================== *)

Fixpoint elim_lt (lvar : nat) (bound : lifetime) (p : variance) (l : lifetime)
    : option lifetime :=
  match l with
  | lt_var x =>
      if Nat.eqb x lvar then
        match p with
        | var_pos => Some bound
        | var_neg => Some lt_free
        | var_inv => None
        end
      else Some (lt_var x)
  | lt_free      => Some lt_free
  | lt_local     => Some lt_local
  | lt_join l1 l2 =>
      match elim_lt lvar bound p l1, elim_lt lvar bound p l2 with
      | Some l1', Some l2' => Some (lt_join l1' l2')
      | _, _               => None
      end
  end.

Fixpoint elim_ty (lvar : nat) (bound : lifetime) (p : variance) (T : type)
    : option type :=
  let fix go_list p' Ts :=
    match Ts with
    | [] => Some []
    | A :: rest =>
        match elim_ty lvar bound p' A, go_list p' rest with
        | Some A', Some rest' => Some (A' :: rest')
        | _, _ => None
        end
    end
  in
  match T with
  | type_var n => Some (type_var n)
  | type_fun A l B =>
      match elim_ty lvar bound (flip_variance p) A,
            elim_lt lvar bound p l,
            elim_ty lvar bound p B with
      | Some A', Some l', Some B' => Some (type_fun A' l' B')
      | _, _, _ => None
      end
  | type_ctor K l Ts =>
      match elim_lt lvar bound p l, go_list var_inv Ts with
      | Some l', Some Ts' => Some (type_ctor K l' Ts')
      | _, _ => None
      end
  | type_lt_all A =>
      match elim_ty (S lvar) (shift_lt 1 0 bound) p A with
      | Some A' => Some (type_lt_all A')
      | None    => None
      end
  | type_ty_all B A =>
      match elim_ty lvar bound (flip_variance p) B, elim_ty lvar bound p A with
      | Some B', Some A' => Some (type_ty_all B' A')
      | _, _ => None
      end
  end.

(* Eliminate all lifetime vars in the range [0, n) from a type.        *)
(* Callers pass `bound` already shifted up by n so that it lives       *)
(* under the n eliminated binders.  Each iteration closes one binder,  *)
(* so `bound` gets closed/shrunk by `subst_lt 0 lt_free bound`.        *)
Fixpoint elim_ty_n (n : nat) (bound : lifetime) (p : variance) (T : type)
    : option type :=
  match n with
  | O    => Some T
  | S n' =>
      match elim_ty 0 bound p T with
      | None    => None
      | Some T' =>
          let T''     := subst_lt_in_ty 0 lt_free T' in
          let bound'  := subst_lt 0 lt_free bound in
          elim_ty_n n' bound' p T''
      end
  end.
