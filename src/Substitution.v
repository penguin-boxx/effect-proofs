Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.

(* ================================================================== *)
(* Shifting and substitution of de Bruijn indices.                    *)
(* ================================================================== *)

(* ================================================================== *)
(* Lifting (shifting) of de Bruijn indices                            *)
(*                                                                    *)
(* shift_X d c t  increments every free X-variable with index ≥ c     *)
(* in t by d.  The cutoff c grows by 1 each time we pass under a      *)
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
  | term_ctor K l lts Ts ts  => term_ctor K l lts Ts (go ts)
  (* yes_body is under arity extra term binders; no_body is not *)
  | term_match scrut tag arity yes_body no_body =>
      term_match (shift_tm amount cutoff scrut) tag arity
                 (shift_tm amount (cutoff + arity) yes_body)
                 (shift_tm amount cutoff no_body)
  (* handle: body under +1 term binder; op_body under +2 (arg + k) *)
  | term_handle E Ts sig op_body body =>
      term_handle E Ts sig
                  (shift_tm amount (cutoff + 2) op_body)
                  (shift_tm amount (S cutoff) body)
  | term_perform t arg =>
      term_perform (shift_tm amount cutoff t) (shift_tm amount cutoff arg)
  | term_cap E m Ts sig op_body =>
      term_cap E m Ts sig (shift_tm amount (cutoff + 2) op_body)
  | term_handler_m m t => term_handler_m m (shift_tm amount cutoff t)
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
  | term_ctor K l lts Ts ts  => term_ctor K l lts (shift_ty_list amount cutoff Ts) (go ts)
  (* match introduces no type binder; arity term binders do not affect type indices *)
  | term_match scrut tag arity yes_body no_body =>
      term_match (shift_ty_in_tm amount cutoff scrut) tag arity
                 (shift_ty_in_tm amount cutoff yes_body)
                 (shift_ty_in_tm amount cutoff no_body)
  (* handle/perform/cap: shift Ts and recurse; no type binder *)
  | term_handle E Ts sig op_body body =>
      term_handle E (shift_ty_list amount cutoff Ts)
                  (shift_ty amount cutoff sig)
                  (shift_ty_in_tm amount cutoff op_body)
                  (shift_ty_in_tm amount cutoff body)
  | term_perform t arg =>
      term_perform (shift_ty_in_tm amount cutoff t)
                   (shift_ty_in_tm amount cutoff arg)
  | term_cap E m Ts sig op_body =>
      term_cap E m (shift_ty_list amount cutoff Ts)
               (shift_ty amount cutoff sig)
               (shift_ty_in_tm amount cutoff op_body)
  | term_handler_m m t => term_handler_m m (shift_ty_in_tm amount cutoff t)
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
  | term_ctor K l lts Ts ts  => term_ctor K (shift_lt amount cutoff l)
                                        (List.map (shift_lt amount cutoff) lts)
                                        (shift_lt_in_ty_list amount cutoff Ts)
                                        (go ts)
  (* match introduces no lifetime binder; arity term binders do not affect lifetime indices *)
  | term_match scrut tag arity yes_body no_body =>
      term_match (shift_lt_in_tm amount cutoff scrut) tag arity
                 (shift_lt_in_tm amount cutoff yes_body)
                 (shift_lt_in_tm amount cutoff no_body)
  | term_handle E Ts sig op_body body =>
      term_handle E (shift_lt_in_ty_list amount cutoff Ts)
                  (shift_lt_in_ty amount cutoff sig)
                  (shift_lt_in_tm amount cutoff op_body)
                  (shift_lt_in_tm amount cutoff body)
  | term_perform t arg =>
      term_perform (shift_lt_in_tm amount cutoff t)
                   (shift_lt_in_tm amount cutoff arg)
  | term_cap E m Ts sig op_body =>
      term_cap E m (shift_lt_in_ty_list amount cutoff Ts)
               (shift_lt_in_ty amount cutoff sig)
               (shift_lt_in_tm amount cutoff op_body)
  | term_handler_m m t => term_handler_m m (shift_lt_in_tm amount cutoff t)
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

(* --- Term variable substitution in terms ---                            *)
(*                                                                        *)
(* When passing under a binder of kind X, the index var is unchanged      *)
(* (X ≠ term) or incremented (X = term), and free X-vars in               *)
(* replacement are shifted up by 1 to avoid capture.                      *)

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
  | term_ctor K l lts Ts ts => term_ctor K l lts Ts (go ts)
  (* yes_body is under arity term binders: var shifts up by arity,       *)
  (* and term vars in replacement shift up by arity to avoid capture     *)
  | term_match scrut tag arity yes_body no_body =>
      term_match (subst_tm var replacement scrut) tag arity
                 (subst_tm (var + arity) (shift_tm arity 0 replacement) yes_body)
                 (subst_tm var replacement no_body)
  | term_handle E Ts sig op_body body =>
      term_handle E Ts sig
                  (subst_tm (var + 2) (shift_tm 2 0 replacement) op_body)
                  (subst_tm (S var) (shift_tm 1 0 replacement) body)
  | term_perform t arg =>
      term_perform (subst_tm var replacement t) (subst_tm var replacement arg)
  | term_cap E m Ts sig op_body =>
      term_cap E m Ts sig
               (subst_tm (var + 2) (shift_tm 2 0 replacement) op_body)
  | term_handler_m m t => term_handler_m m (subst_tm var replacement t)
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
  | term_ctor K l lts Ts ts => term_ctor K l lts (subst_ty_list var replacement Ts) (go ts)
  (* match introduces no type binder; arity term binders do not affect type var index *)
  | term_match scrut tag arity yes_body no_body =>
      term_match (subst_ty_in_tm var replacement scrut) tag arity
                 (subst_ty_in_tm var replacement yes_body)
                 (subst_ty_in_tm var replacement no_body)
  | term_handle E Ts sig op_body body =>
      term_handle E (subst_ty_list var replacement Ts)
                  (subst_ty var replacement sig)
                  (subst_ty_in_tm var replacement op_body)
                  (subst_ty_in_tm var replacement body)
  | term_perform t arg =>
      term_perform (subst_ty_in_tm var replacement t)
                   (subst_ty_in_tm var replacement arg)
  | term_cap E m Ts sig op_body =>
      term_cap E m (subst_ty_list var replacement Ts)
               (subst_ty var replacement sig)
               (subst_ty_in_tm var replacement op_body)
  | term_handler_m m t => term_handler_m m (subst_ty_in_tm var replacement t)
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
  | term_ctor K l lts Ts ts => term_ctor K (subst_lt var replacement l)
                                       (List.map (subst_lt var replacement) lts)
                                       (subst_lt_in_ty_list var replacement Ts)
                                       (go ts)
  (* match introduces no lifetime binder; arity term binders do not affect lifetime var index *)
  | term_match scrut tag arity yes_body no_body =>
      term_match (subst_lt_in_tm var replacement scrut) tag arity
                 (subst_lt_in_tm var replacement yes_body)
                 (subst_lt_in_tm var replacement no_body)
  | term_handle E Ts sig op_body body =>
      term_handle E (subst_lt_in_ty_list var replacement Ts)
                  (subst_lt_in_ty var replacement sig)
                  (subst_lt_in_tm var replacement op_body)
                  (subst_lt_in_tm var replacement body)
  | term_perform t arg =>
      term_perform (subst_lt_in_tm var replacement t)
                   (subst_lt_in_tm var replacement arg)
  | term_cap E m Ts sig op_body =>
      term_cap E m (subst_lt_in_ty_list var replacement Ts)
               (subst_lt_in_ty var replacement sig)
               (subst_lt_in_tm var replacement op_body)
  | term_handler_m m t => term_handler_m m (subst_lt_in_tm var replacement t)
  end.

(* ================================================================== *)
(* Simultaneous substitution of constructor arguments                 *)
(*                                                                    *)
(* subst_list_tm vs t  substitutes vs[0] for variable 0, vs[1] for    *)
(* variable 1, ..., vs[n-1] for variable n-1 in t, which is assumed   *)
(* to be under exactly n = length vs term binders.  Variables 0..n-1  *)
(* correspond to constructor arguments outermost-first.               *)
(*                                                                    *)
(* Implementation: substitute each argument from outermost (index 0)  *)
(* to innermost.  When substituting vs[i] (the head of the remaining  *)
(* list) for variable 0, we first shift vs[i] by (length rest) to     *)
(* compensate for the remaining open binders; each substitution closes*)
(* one binder and decrements the remaining variable indices by one.   *)
(* ================================================================== *)

Fixpoint subst_list_tm (vs : list term) (t : term) : term :=
  match vs with
  | []         => t
  | v :: rest  =>
      subst_list_tm rest
        (subst_tm 0 (shift_tm (List.length rest) 0 v) t)
  end.

(* ================================================================== *)
(* Simultaneous substitution of n_lt lifetime witnesses               *)
(*                                                                    *)
(* subst_list_lt_in_tm lts t  substitutes lts[0] for lt-var 0,        *)
(* lts[1] for lt-var 1, ..., lts[n-1] for lt-var (n-1) in t,          *)
(* assumed to live under exactly n = length lts lt-binders.           *)
(*                                                                    *)
(* Same telescoping discipline as subst_list_tm: shift each entry by  *)
(* the number of remaining open lt-binders before substituting at 0.  *)
(* ================================================================== *)

Fixpoint subst_list_lt_in_tm (lts : list lifetime) (t : term) : term :=
  match lts with
  | []          => t
  | l :: rest   =>
      subst_list_lt_in_tm rest
        (subst_lt_in_tm 0 (shift_lt (List.length rest) 0 l) t)
  end.

Fixpoint subst_list_lt_in_ty (lts : list lifetime) (T : type) : type :=
  match lts with
  | []          => T
  | l :: rest   =>
      subst_list_lt_in_ty rest
        (subst_lt_in_ty 0 (shift_lt (List.length rest) 0 l) T)
  end.
