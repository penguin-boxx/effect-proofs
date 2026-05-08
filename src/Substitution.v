(* ================================================================== *)
(* Substitution.v — locally nameless operations                       *)
(*                                                                    *)
(* For each binder/sort pair we provide:                              *)
(*   open_X_wrt_Y_rec  : nat -> Y -> X -> X    (raw, with depth)      *)
(*   open_X_wrt_Y      : Y -> X -> X           (depth 0)              *)
(*   close_X_wrt_Y_rec : nat -> atom -> X -> X                        *)
(*   close_X_wrt_Y     : atom -> X -> X                               *)
(*   subst_X_in_Y      : Y -> atom -> X -> X   (free-atom subst)      *)
(*   fv_X_in_Y         : Y -> atoms                                   *)
(*                                                                    *)
(* Sort pairs needed:                                                 *)
(*   lt-in-lt, ty-in-lt, ty-in-ty,                                    *)
(*   tm-in-tm, ty-in-tm, lt-in-tm                                     *)
(*                                                                    *)
(* Plus the locally-closed predicates lc_lifetime / lc_type / lc_term *)
(* using cofinite quantification at binders.                          *)
(* ================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.

From Metalib Require Export Metatheory.
Require Export Syntax.

(* ================================================================== *)
(* SECTION 1 — fv (free atoms)                                        *)
(* ================================================================== *)

(* Free lt-atoms in a lifetime *)
Fixpoint fv_lt_in_lt (l : lifetime) : atoms :=
  match l with
  | lt_bvar _    => empty
  | lt_fvar a    => singleton a
  | lt_free      => empty
  | lt_local     => empty
  | lt_min l1 l2 => union (fv_lt_in_lt l1) (fv_lt_in_lt l2)
  end.

(* Free lt-atoms in a type *)
Fixpoint fv_lt_in_ty (T : type) : atoms :=
  let fix go (Ts : list type) : atoms :=
    match Ts with
    | []        => empty
    | A :: rest => union (fv_lt_in_ty A) (go rest)
    end
  in
  match T with
  | type_bvar _      => empty
  | type_fvar _      => empty
  | type_fun A l B   => union (fv_lt_in_ty A) (union (fv_lt_in_lt l) (fv_lt_in_ty B))
  | type_ctor _ l Ts => union (fv_lt_in_lt l) (go Ts)
  | type_lt_all A    => fv_lt_in_ty A
  | type_ty_all B A  => union (fv_lt_in_ty B) (fv_lt_in_ty A)
  end.

(* Free ty-atoms in a type *)
Fixpoint fv_ty_in_ty (T : type) : atoms :=
  let fix go (Ts : list type) : atoms :=
    match Ts with
    | []        => empty
    | A :: rest => union (fv_ty_in_ty A) (go rest)
    end
  in
  match T with
  | type_bvar _      => empty
  | type_fvar a      => singleton a
  | type_fun A _ B   => union (fv_ty_in_ty A) (fv_ty_in_ty B)
  | type_ctor _ _ Ts => go Ts
  | type_lt_all A    => fv_ty_in_ty A
  | type_ty_all B A  => union (fv_ty_in_ty B) (fv_ty_in_ty A)
  end.

(* Free tm-atoms in a term *)
Fixpoint fv_tm_in_tm (t : term) : atoms :=
  let fix go (ts : list term) : atoms :=
    match ts with
    | []        => empty
    | u :: rest => union (fv_tm_in_tm u) (go rest)
    end
  in
  match t with
  | term_bvar _              => empty
  | term_fvar a              => singleton a
  | term_app t1 t2           => union (fv_tm_in_tm t1) (fv_tm_in_tm t2)
  | term_lam body _          => fv_tm_in_tm body
  | term_ty_app t _          => fv_tm_in_tm t
  | term_ty_lam _ body       => fv_tm_in_tm body
  | term_lt_app t _          => fv_tm_in_tm t
  | term_lt_lam body         => fv_tm_in_tm body
  | term_ctor _ _ _ _ ts     => go ts
  | term_match s _ _ y n     =>
      union (fv_tm_in_tm s) (union (fv_tm_in_tm y) (fv_tm_in_tm n))
  | term_handle _ _ ob body  => union (fv_tm_in_tm ob) (fv_tm_in_tm body)
  | term_perform t _ a       => union (fv_tm_in_tm t) (fv_tm_in_tm a)
  | term_cap _ _ _ ob        => fv_tm_in_tm ob
  | term_handler_m _ t       => fv_tm_in_tm t
  | term_resume _ b          => fv_tm_in_tm b
  end.

(* Free ty-atoms in a term *)
Fixpoint fv_ty_in_tm (t : term) : atoms :=
  let fix go_tm (ts : list term) : atoms :=
    match ts with
    | []        => empty
    | u :: rest => union (fv_ty_in_tm u) (go_tm rest)
    end
  in
  let fix go_ty (Ts : list type) : atoms :=
    match Ts with
    | []        => empty
    | A :: rest => union (fv_ty_in_ty A) (go_ty rest)
    end
  in
  match t with
  | term_bvar _              => empty
  | term_fvar _              => empty
  | term_app t1 t2           => union (fv_ty_in_tm t1) (fv_ty_in_tm t2)
  | term_lam body T          => union (fv_ty_in_tm body) (fv_ty_in_ty T)
  | term_ty_app t T          => union (fv_ty_in_tm t) (fv_ty_in_ty T)
  | term_ty_lam bd body      => union (fv_ty_in_ty bd) (fv_ty_in_tm body)
  | term_lt_app t _          => fv_ty_in_tm t
  | term_lt_lam body         => fv_ty_in_tm body
  | term_ctor _ _ _ Ts ts    => union (go_ty Ts) (go_tm ts)
  | term_match s _ _ y n     =>
      union (fv_ty_in_tm s) (union (fv_ty_in_tm y) (fv_ty_in_tm n))
  | term_handle _ Ts ob body =>
      union (go_ty Ts) (union (fv_ty_in_tm ob) (fv_ty_in_tm body))
  | term_perform t Ss a      =>
      union (fv_ty_in_tm t) (union (go_ty Ss) (fv_ty_in_tm a))
  | term_cap _ _ Ts ob       => union (go_ty Ts) (fv_ty_in_tm ob)
  | term_handler_m _ t       => fv_ty_in_tm t
  | term_resume _ b          => fv_ty_in_tm b
  end.

(* Free lt-atoms in a term *)
Fixpoint fv_lt_in_tm (t : term) : atoms :=
  let fix go_tm (ts : list term) : atoms :=
    match ts with
    | []        => empty
    | u :: rest => union (fv_lt_in_tm u) (go_tm rest)
    end
  in
  let fix go_ty (Ts : list type) : atoms :=
    match Ts with
    | []        => empty
    | A :: rest => union (fv_lt_in_ty A) (go_ty rest)
    end
  in
  let fix go_lt (ls : list lifetime) : atoms :=
    match ls with
    | []        => empty
    | l :: rest => union (fv_lt_in_lt l) (go_lt rest)
    end
  in
  match t with
  | term_bvar _              => empty
  | term_fvar _              => empty
  | term_app t1 t2           => union (fv_lt_in_tm t1) (fv_lt_in_tm t2)
  | term_lam body T          => union (fv_lt_in_tm body) (fv_lt_in_ty T)
  | term_ty_app t T          => union (fv_lt_in_tm t) (fv_lt_in_ty T)
  | term_ty_lam bd body      => union (fv_lt_in_ty bd) (fv_lt_in_tm body)
  | term_lt_app t l          => union (fv_lt_in_tm t) (fv_lt_in_lt l)
  | term_lt_lam body         => fv_lt_in_tm body
  | term_ctor _ l ls Ts ts   =>
      union (fv_lt_in_lt l)
            (union (go_lt ls) (union (go_ty Ts) (go_tm ts)))
  | term_match s _ _ y n     =>
      union (fv_lt_in_tm s) (union (fv_lt_in_tm y) (fv_lt_in_tm n))
  | term_handle _ Ts ob body =>
      union (go_ty Ts) (union (fv_lt_in_tm ob) (fv_lt_in_tm body))
  | term_perform t Ss a      =>
      union (fv_lt_in_tm t) (union (go_ty Ss) (fv_lt_in_tm a))
  | term_cap _ _ Ts ob       => union (go_ty Ts) (fv_lt_in_tm ob)
  | term_handler_m _ t       => fv_lt_in_tm t
  | term_resume _ b          => fv_lt_in_tm b
  end.

(* ================================================================== *)
(* SECTION 2 — open (replace bvar k with replacement)                 *)
(* ================================================================== *)

(* --- open lifetime with lifetime --- *)
Fixpoint open_lt_wrt_lt_rec (k : nat) (u : lifetime) (l : lifetime) : lifetime :=
  match l with
  | lt_bvar n =>
      match Nat.compare n k with
      | Lt => lt_bvar n
      | Eq => u
      | Gt => lt_bvar (pred n)
      end
  | lt_fvar _    => l
  | lt_free      => l
  | lt_local     => l
  | lt_min l1 l2 => lt_min (open_lt_wrt_lt_rec k u l1) (open_lt_wrt_lt_rec k u l2)
  end.

Definition open_lt_wrt_lt (u : lifetime) (l : lifetime) : lifetime :=
  open_lt_wrt_lt_rec 0 u l.

(* --- open type with lifetime --- *)
Fixpoint open_ty_wrt_lt_rec (k : nat) (u : lifetime) (T : type) : type :=
  let fix go (Ts : list type) : list type :=
    match Ts with
    | []        => []
    | A :: rest => open_ty_wrt_lt_rec k u A :: go rest
    end
  in
  match T with
  | type_bvar _      => T
  | type_fvar _      => T
  | type_fun A l B   =>
      type_fun (open_ty_wrt_lt_rec k u A)
               (open_lt_wrt_lt_rec k u l)
               (open_ty_wrt_lt_rec k u B)
  | type_ctor K l Ts =>
      type_ctor K (open_lt_wrt_lt_rec k u l) (go Ts)
  | type_lt_all A    =>
      (* binds 1 lt: increase index *)
      type_lt_all (open_ty_wrt_lt_rec (S k) u A)
  | type_ty_all B A  =>
      type_ty_all (open_ty_wrt_lt_rec k u B) (open_ty_wrt_lt_rec k u A)
  end.

Definition open_ty_wrt_lt (u : lifetime) (T : type) : type :=
  open_ty_wrt_lt_rec 0 u T.

(* --- open type with type --- *)
Fixpoint open_ty_wrt_ty_rec (k : nat) (U : type) (T : type) : type :=
  let fix go (Ts : list type) : list type :=
    match Ts with
    | []        => []
    | A :: rest => open_ty_wrt_ty_rec k U A :: go rest
    end
  in
  match T with
  | type_bvar n =>
      match Nat.compare n k with
      | Lt => type_bvar n
      | Eq => U
      | Gt => type_bvar (pred n)
      end
  | type_fvar _      => T
  | type_fun A l B   =>
      type_fun (open_ty_wrt_ty_rec k U A) l (open_ty_wrt_ty_rec k U B)
  | type_ctor K l Ts => type_ctor K l (go Ts)
  | type_lt_all A    => type_lt_all (open_ty_wrt_ty_rec k U A)
  | type_ty_all B A  =>
      type_ty_all (open_ty_wrt_ty_rec k U B)
                  (open_ty_wrt_ty_rec (S k) U A)
  end.

Definition open_ty_wrt_ty (U : type) (T : type) : type :=
  open_ty_wrt_ty_rec 0 U T.

(* --- open term with term --- *)
Fixpoint open_tm_wrt_tm_rec (k : nat) (u : term) (t : term) : term :=
  let fix go (ts : list term) : list term :=
    match ts with
    | []        => []
    | x :: rest => open_tm_wrt_tm_rec k u x :: go rest
    end
  in
  match t with
  | term_bvar n =>
      match Nat.compare n k with
      | Lt => term_bvar n
      | Eq => u
      | Gt => term_bvar (pred n)
      end
  | term_fvar _              => t
  | term_app t1 t2           =>
      term_app (open_tm_wrt_tm_rec k u t1) (open_tm_wrt_tm_rec k u t2)
  | term_lam body T          =>
      term_lam (open_tm_wrt_tm_rec (S k) u body) T
  | term_ty_app t1 T         => term_ty_app (open_tm_wrt_tm_rec k u t1) T
  | term_ty_lam bd body      => term_ty_lam bd (open_tm_wrt_tm_rec k u body)
  | term_lt_app t1 l         => term_lt_app (open_tm_wrt_tm_rec k u t1) l
  | term_lt_lam body         => term_lt_lam (open_tm_wrt_tm_rec k u body)
  | term_ctor K l ls Ts ts   => term_ctor K l ls Ts (go ts)
  | term_match s K ar y n    =>
      (* yes_body binds `ar` term vars; bump index by ar *)
      term_match (open_tm_wrt_tm_rec k u s) K ar
                 (open_tm_wrt_tm_rec (k + ar) u y)
                 (open_tm_wrt_tm_rec k u n)
  | term_handle E Ts ob body =>
      (* op_body has 2 tm binders (ty binders unchanged); body has 1 tm binder *)
      term_handle E Ts (open_tm_wrt_tm_rec (k + 2) u ob)
                       (open_tm_wrt_tm_rec (S k) u body)
  | term_perform t1 Ss a     =>
      term_perform (open_tm_wrt_tm_rec k u t1) Ss (open_tm_wrt_tm_rec k u a)
  | term_cap E m Ts ob       =>
      term_cap E m Ts (open_tm_wrt_tm_rec (k + 2) u ob)
  | term_handler_m m t1      => term_handler_m m (open_tm_wrt_tm_rec k u t1)
  | term_resume m b          => term_resume m (open_tm_wrt_tm_rec (S k) u b)
  end.

Definition open_tm_wrt_tm (u : term) (t : term) : term :=
  open_tm_wrt_tm_rec 0 u t.

(* --- open term with type --- *)
Fixpoint open_tm_wrt_ty_rec (k : nat) (U : type) (t : term) : term :=
  let fix go_tm (ts : list term) : list term :=
    match ts with
    | []        => []
    | x :: rest => open_tm_wrt_ty_rec k U x :: go_tm rest
    end
  in
  let fix go_ty (Ts : list type) : list type :=
    match Ts with
    | []        => []
    | A :: rest => open_ty_wrt_ty_rec k U A :: go_ty rest
    end
  in
  match t with
  | term_bvar _              => t
  | term_fvar _              => t
  | term_app t1 t2           =>
      term_app (open_tm_wrt_ty_rec k U t1) (open_tm_wrt_ty_rec k U t2)
  | term_lam body T          =>
      term_lam (open_tm_wrt_ty_rec k U body) (open_ty_wrt_ty_rec k U T)
  | term_ty_app t1 T         =>
      term_ty_app (open_tm_wrt_ty_rec k U t1) (open_ty_wrt_ty_rec k U T)
  | term_ty_lam bd body      =>
      term_ty_lam (open_ty_wrt_ty_rec k U bd) (open_tm_wrt_ty_rec (S k) U body)
  | term_lt_app t1 l         => term_lt_app (open_tm_wrt_ty_rec k U t1) l
  | term_lt_lam body         => term_lt_lam (open_tm_wrt_ty_rec k U body)
  | term_ctor K l ls Ts ts   => term_ctor K l ls (go_ty Ts) (go_tm ts)
  | term_match s K ar y n    =>
      term_match (open_tm_wrt_ty_rec k U s) K ar
                 (open_tm_wrt_ty_rec k U y)
                 (open_tm_wrt_ty_rec k U n)
  | term_handle E Ts ob body =>
      (* op_body has n_β ty binders — but n_β is implicit in op_body's bvars. *)
      (* Convention: ty-args are opened OUTERMOST; here we open the slots not   *)
      (* yet bound by op_body's own ty-lams.  See SECTION on multi-binders.    *)
      term_handle E (go_ty Ts) (open_tm_wrt_ty_rec k U ob)
                               (open_tm_wrt_ty_rec k U body)
  | term_perform t1 Ss a     =>
      term_perform (open_tm_wrt_ty_rec k U t1) (go_ty Ss)
                   (open_tm_wrt_ty_rec k U a)
  | term_cap E m Ts ob       =>
      term_cap E m (go_ty Ts) (open_tm_wrt_ty_rec k U ob)
  | term_handler_m m t1      => term_handler_m m (open_tm_wrt_ty_rec k U t1)
  | term_resume m b          => term_resume m (open_tm_wrt_ty_rec k U b)
  end.

Definition open_tm_wrt_ty (U : type) (t : term) : term :=
  open_tm_wrt_ty_rec 0 U t.

(* --- open term with lifetime --- *)
Fixpoint open_tm_wrt_lt_rec (k : nat) (u : lifetime) (t : term) : term :=
  let fix go_tm (ts : list term) : list term :=
    match ts with
    | []        => []
    | x :: rest => open_tm_wrt_lt_rec k u x :: go_tm rest
    end
  in
  let fix go_ty (Ts : list type) : list type :=
    match Ts with
    | []        => []
    | A :: rest => open_ty_wrt_lt_rec k u A :: go_ty rest
    end
  in
  let fix go_lt (ls : list lifetime) : list lifetime :=
    match ls with
    | []        => []
    | l :: rest => open_lt_wrt_lt_rec k u l :: go_lt rest
    end
  in
  match t with
  | term_bvar _              => t
  | term_fvar _              => t
  | term_app t1 t2           =>
      term_app (open_tm_wrt_lt_rec k u t1) (open_tm_wrt_lt_rec k u t2)
  | term_lam body T          =>
      term_lam (open_tm_wrt_lt_rec k u body) (open_ty_wrt_lt_rec k u T)
  | term_ty_app t1 T         =>
      term_ty_app (open_tm_wrt_lt_rec k u t1) (open_ty_wrt_lt_rec k u T)
  | term_ty_lam bd body      =>
      term_ty_lam (open_ty_wrt_lt_rec k u bd) (open_tm_wrt_lt_rec k u body)
  | term_lt_app t1 l         =>
      term_lt_app (open_tm_wrt_lt_rec k u t1) (open_lt_wrt_lt_rec k u l)
  | term_lt_lam body         =>
      term_lt_lam (open_tm_wrt_lt_rec (S k) u body)
  | term_ctor K l ls Ts ts   =>
      term_ctor K (open_lt_wrt_lt_rec k u l) (go_lt ls) (go_ty Ts) (go_tm ts)
  | term_match s K ar y n    =>
      term_match (open_tm_wrt_lt_rec k u s) K ar
                 (open_tm_wrt_lt_rec k u y)
                 (open_tm_wrt_lt_rec k u n)
  | term_handle E Ts ob body =>
      term_handle E (go_ty Ts) (open_tm_wrt_lt_rec k u ob)
                               (open_tm_wrt_lt_rec k u body)
  | term_perform t1 Ss a     =>
      term_perform (open_tm_wrt_lt_rec k u t1) (go_ty Ss)
                   (open_tm_wrt_lt_rec k u a)
  | term_cap E m Ts ob       =>
      term_cap E m (go_ty Ts) (open_tm_wrt_lt_rec k u ob)
  | term_handler_m m t1      => term_handler_m m (open_tm_wrt_lt_rec k u t1)
  | term_resume m b          => term_resume m (open_tm_wrt_lt_rec k u b)
  end.

Definition open_tm_wrt_lt (u : lifetime) (t : term) : term :=
  open_tm_wrt_lt_rec 0 u t.

(* ================================================================== *)
(* SECTION 3 — close (replace fvar a with bvar k)                     *)
(* ================================================================== *)

Fixpoint close_lt_wrt_lt_rec (k : nat) (a : atom) (l : lifetime) : lifetime :=
  match l with
  | lt_bvar n    => if Nat.leb k n then lt_bvar (S n) else lt_bvar n
  | lt_fvar b    => if a == b then lt_bvar k else lt_fvar b
  | lt_free      => lt_free
  | lt_local     => lt_local
  | lt_min l1 l2 => lt_min (close_lt_wrt_lt_rec k a l1) (close_lt_wrt_lt_rec k a l2)
  end.

Definition close_lt_wrt_lt (a : atom) (l : lifetime) : lifetime :=
  close_lt_wrt_lt_rec 0 a l.

Fixpoint close_ty_wrt_lt_rec (k : nat) (a : atom) (T : type) : type :=
  let fix go (Ts : list type) : list type :=
    match Ts with
    | []        => []
    | A :: rest => close_ty_wrt_lt_rec k a A :: go rest
    end
  in
  match T with
  | type_bvar _      => T
  | type_fvar _      => T
  | type_fun A l B   =>
      type_fun (close_ty_wrt_lt_rec k a A)
               (close_lt_wrt_lt_rec k a l)
               (close_ty_wrt_lt_rec k a B)
  | type_ctor K l Ts => type_ctor K (close_lt_wrt_lt_rec k a l) (go Ts)
  | type_lt_all A    => type_lt_all (close_ty_wrt_lt_rec (S k) a A)
  | type_ty_all B A  =>
      type_ty_all (close_ty_wrt_lt_rec k a B) (close_ty_wrt_lt_rec k a A)
  end.

Definition close_ty_wrt_lt (a : atom) (T : type) : type :=
  close_ty_wrt_lt_rec 0 a T.

Fixpoint close_ty_wrt_ty_rec (k : nat) (a : atom) (T : type) : type :=
  let fix go (Ts : list type) : list type :=
    match Ts with
    | []        => []
    | A :: rest => close_ty_wrt_ty_rec k a A :: go rest
    end
  in
  match T with
  | type_bvar n      => if Nat.leb k n then type_bvar (S n) else type_bvar n
  | type_fvar b      => if a == b then type_bvar k else type_fvar b
  | type_fun A l B   =>
      type_fun (close_ty_wrt_ty_rec k a A) l (close_ty_wrt_ty_rec k a B)
  | type_ctor K l Ts => type_ctor K l (go Ts)
  | type_lt_all A    => type_lt_all (close_ty_wrt_ty_rec k a A)
  | type_ty_all B A  =>
      type_ty_all (close_ty_wrt_ty_rec k a B) (close_ty_wrt_ty_rec (S k) a A)
  end.

Definition close_ty_wrt_ty (a : atom) (T : type) : type :=
  close_ty_wrt_ty_rec 0 a T.

Fixpoint close_tm_wrt_tm_rec (k : nat) (a : atom) (t : term) : term :=
  let fix go (ts : list term) : list term :=
    match ts with
    | []        => []
    | x :: rest => close_tm_wrt_tm_rec k a x :: go rest
    end
  in
  match t with
  | term_bvar n              => if Nat.leb k n then term_bvar (S n) else term_bvar n
  | term_fvar b              => if a == b then term_bvar k else term_fvar b
  | term_app t1 t2           =>
      term_app (close_tm_wrt_tm_rec k a t1) (close_tm_wrt_tm_rec k a t2)
  | term_lam body T          => term_lam (close_tm_wrt_tm_rec (S k) a body) T
  | term_ty_app t1 T         => term_ty_app (close_tm_wrt_tm_rec k a t1) T
  | term_ty_lam bd body      => term_ty_lam bd (close_tm_wrt_tm_rec k a body)
  | term_lt_app t1 l         => term_lt_app (close_tm_wrt_tm_rec k a t1) l
  | term_lt_lam body         => term_lt_lam (close_tm_wrt_tm_rec k a body)
  | term_ctor K l ls Ts ts   => term_ctor K l ls Ts (go ts)
  | term_match s K ar y n    =>
      term_match (close_tm_wrt_tm_rec k a s) K ar
                 (close_tm_wrt_tm_rec (k + ar) a y)
                 (close_tm_wrt_tm_rec k a n)
  | term_handle E Ts ob body =>
      term_handle E Ts (close_tm_wrt_tm_rec (k + 2) a ob)
                       (close_tm_wrt_tm_rec (S k) a body)
  | term_perform t1 Ss a'    =>
      term_perform (close_tm_wrt_tm_rec k a t1) Ss (close_tm_wrt_tm_rec k a a')
  | term_cap E m Ts ob       =>
      term_cap E m Ts (close_tm_wrt_tm_rec (k + 2) a ob)
  | term_handler_m m t1      => term_handler_m m (close_tm_wrt_tm_rec k a t1)
  | term_resume m b          => term_resume m (close_tm_wrt_tm_rec (S k) a b)
  end.

Definition close_tm_wrt_tm (a : atom) (t : term) : term :=
  close_tm_wrt_tm_rec 0 a t.

Fixpoint close_tm_wrt_ty_rec (k : nat) (a : atom) (t : term) : term :=
  let fix go_tm (ts : list term) : list term :=
    match ts with
    | []        => []
    | x :: rest => close_tm_wrt_ty_rec k a x :: go_tm rest
    end
  in
  let fix go_ty (Ts : list type) : list type :=
    match Ts with
    | []        => []
    | A :: rest => close_ty_wrt_ty_rec k a A :: go_ty rest
    end
  in
  match t with
  | term_bvar _              => t
  | term_fvar _              => t
  | term_app t1 t2           =>
      term_app (close_tm_wrt_ty_rec k a t1) (close_tm_wrt_ty_rec k a t2)
  | term_lam body T          =>
      term_lam (close_tm_wrt_ty_rec k a body) (close_ty_wrt_ty_rec k a T)
  | term_ty_app t1 T         =>
      term_ty_app (close_tm_wrt_ty_rec k a t1) (close_ty_wrt_ty_rec k a T)
  | term_ty_lam bd body      =>
      term_ty_lam (close_ty_wrt_ty_rec k a bd) (close_tm_wrt_ty_rec (S k) a body)
  | term_lt_app t1 l         => term_lt_app (close_tm_wrt_ty_rec k a t1) l
  | term_lt_lam body         => term_lt_lam (close_tm_wrt_ty_rec k a body)
  | term_ctor K l ls Ts ts   => term_ctor K l ls (go_ty Ts) (go_tm ts)
  | term_match s K ar y n    =>
      term_match (close_tm_wrt_ty_rec k a s) K ar
                 (close_tm_wrt_ty_rec k a y)
                 (close_tm_wrt_ty_rec k a n)
  | term_handle E Ts ob body =>
      term_handle E (go_ty Ts) (close_tm_wrt_ty_rec k a ob)
                               (close_tm_wrt_ty_rec k a body)
  | term_perform t1 Ss a'    =>
      term_perform (close_tm_wrt_ty_rec k a t1) (go_ty Ss)
                   (close_tm_wrt_ty_rec k a a')
  | term_cap E m Ts ob       =>
      term_cap E m (go_ty Ts) (close_tm_wrt_ty_rec k a ob)
  | term_handler_m m t1      => term_handler_m m (close_tm_wrt_ty_rec k a t1)
  | term_resume m b          => term_resume m (close_tm_wrt_ty_rec k a b)
  end.

Definition close_tm_wrt_ty (a : atom) (t : term) : term :=
  close_tm_wrt_ty_rec 0 a t.

Fixpoint close_tm_wrt_lt_rec (k : nat) (a : atom) (t : term) : term :=
  let fix go_tm (ts : list term) : list term :=
    match ts with
    | []        => []
    | x :: rest => close_tm_wrt_lt_rec k a x :: go_tm rest
    end
  in
  let fix go_ty (Ts : list type) : list type :=
    match Ts with
    | []        => []
    | A :: rest => close_ty_wrt_lt_rec k a A :: go_ty rest
    end
  in
  let fix go_lt (ls : list lifetime) : list lifetime :=
    match ls with
    | []        => []
    | l :: rest => close_lt_wrt_lt_rec k a l :: go_lt rest
    end
  in
  match t with
  | term_bvar _              => t
  | term_fvar _              => t
  | term_app t1 t2           =>
      term_app (close_tm_wrt_lt_rec k a t1) (close_tm_wrt_lt_rec k a t2)
  | term_lam body T          =>
      term_lam (close_tm_wrt_lt_rec k a body) (close_ty_wrt_lt_rec k a T)
  | term_ty_app t1 T         =>
      term_ty_app (close_tm_wrt_lt_rec k a t1) (close_ty_wrt_lt_rec k a T)
  | term_ty_lam bd body      =>
      term_ty_lam (close_ty_wrt_lt_rec k a bd) (close_tm_wrt_lt_rec k a body)
  | term_lt_app t1 l         =>
      term_lt_app (close_tm_wrt_lt_rec k a t1) (close_lt_wrt_lt_rec k a l)
  | term_lt_lam body         =>
      term_lt_lam (close_tm_wrt_lt_rec (S k) a body)
  | term_ctor K l ls Ts ts   =>
      term_ctor K (close_lt_wrt_lt_rec k a l) (go_lt ls) (go_ty Ts) (go_tm ts)
  | term_match s K ar y n    =>
      term_match (close_tm_wrt_lt_rec k a s) K ar
                 (close_tm_wrt_lt_rec k a y)
                 (close_tm_wrt_lt_rec k a n)
  | term_handle E Ts ob body =>
      term_handle E (go_ty Ts) (close_tm_wrt_lt_rec k a ob)
                               (close_tm_wrt_lt_rec k a body)
  | term_perform t1 Ss a'    =>
      term_perform (close_tm_wrt_lt_rec k a t1) (go_ty Ss)
                   (close_tm_wrt_lt_rec k a a')
  | term_cap E m Ts ob       =>
      term_cap E m (go_ty Ts) (close_tm_wrt_lt_rec k a ob)
  | term_handler_m m t1      => term_handler_m m (close_tm_wrt_lt_rec k a t1)
  | term_resume m b          => term_resume m (close_tm_wrt_lt_rec k a b)
  end.

Definition close_tm_wrt_lt (a : atom) (t : term) : term :=
  close_tm_wrt_lt_rec 0 a t.

(* ================================================================== *)
(* SECTION 4 — subst (replace fvar a with replacement)                *)
(* ================================================================== *)

Fixpoint subst_lt_in_lt (u : lifetime) (a : atom) (l : lifetime) : lifetime :=
  match l with
  | lt_bvar _    => l
  | lt_fvar b    => if a == b then u else lt_fvar b
  | lt_free      => lt_free
  | lt_local     => lt_local
  | lt_min l1 l2 => lt_min (subst_lt_in_lt u a l1) (subst_lt_in_lt u a l2)
  end.

Fixpoint subst_lt_in_ty (u : lifetime) (a : atom) (T : type) : type :=
  let fix go (Ts : list type) : list type :=
    match Ts with
    | []        => []
    | A :: rest => subst_lt_in_ty u a A :: go rest
    end
  in
  match T with
  | type_bvar _      => T
  | type_fvar _      => T
  | type_fun A l B   =>
      type_fun (subst_lt_in_ty u a A) (subst_lt_in_lt u a l) (subst_lt_in_ty u a B)
  | type_ctor K l Ts => type_ctor K (subst_lt_in_lt u a l) (go Ts)
  | type_lt_all A    => type_lt_all (subst_lt_in_ty u a A)
  | type_ty_all B A  => type_ty_all (subst_lt_in_ty u a B) (subst_lt_in_ty u a A)
  end.

Fixpoint subst_ty_in_ty (U : type) (a : atom) (T : type) : type :=
  let fix go (Ts : list type) : list type :=
    match Ts with
    | []        => []
    | A :: rest => subst_ty_in_ty U a A :: go rest
    end
  in
  match T with
  | type_bvar _      => T
  | type_fvar b      => if a == b then U else type_fvar b
  | type_fun A l B   => type_fun (subst_ty_in_ty U a A) l (subst_ty_in_ty U a B)
  | type_ctor K l Ts => type_ctor K l (go Ts)
  | type_lt_all A    => type_lt_all (subst_ty_in_ty U a A)
  | type_ty_all B A  => type_ty_all (subst_ty_in_ty U a B) (subst_ty_in_ty U a A)
  end.

Fixpoint subst_tm_in_tm (u : term) (a : atom) (t : term) : term :=
  let fix go (ts : list term) : list term :=
    match ts with
    | []        => []
    | x :: rest => subst_tm_in_tm u a x :: go rest
    end
  in
  match t with
  | term_bvar _              => t
  | term_fvar b              => if a == b then u else term_fvar b
  | term_app t1 t2           => term_app (subst_tm_in_tm u a t1) (subst_tm_in_tm u a t2)
  | term_lam body T          => term_lam (subst_tm_in_tm u a body) T
  | term_ty_app t1 T         => term_ty_app (subst_tm_in_tm u a t1) T
  | term_ty_lam bd body      => term_ty_lam bd (subst_tm_in_tm u a body)
  | term_lt_app t1 l         => term_lt_app (subst_tm_in_tm u a t1) l
  | term_lt_lam body         => term_lt_lam (subst_tm_in_tm u a body)
  | term_ctor K l ls Ts ts   => term_ctor K l ls Ts (go ts)
  | term_match s K ar y n    =>
      term_match (subst_tm_in_tm u a s) K ar
                 (subst_tm_in_tm u a y) (subst_tm_in_tm u a n)
  | term_handle E Ts ob body =>
      term_handle E Ts (subst_tm_in_tm u a ob) (subst_tm_in_tm u a body)
  | term_perform t1 Ss a'    =>
      term_perform (subst_tm_in_tm u a t1) Ss (subst_tm_in_tm u a a')
  | term_cap E m Ts ob       => term_cap E m Ts (subst_tm_in_tm u a ob)
  | term_handler_m m t1      => term_handler_m m (subst_tm_in_tm u a t1)
  | term_resume m b          => term_resume m (subst_tm_in_tm u a b)
  end.

Fixpoint subst_ty_in_tm (U : type) (a : atom) (t : term) : term :=
  let fix go_tm (ts : list term) : list term :=
    match ts with
    | []        => []
    | x :: rest => subst_ty_in_tm U a x :: go_tm rest
    end
  in
  let fix go_ty (Ts : list type) : list type :=
    match Ts with
    | []        => []
    | A :: rest => subst_ty_in_ty U a A :: go_ty rest
    end
  in
  match t with
  | term_bvar _              => t
  | term_fvar _              => t
  | term_app t1 t2           => term_app (subst_ty_in_tm U a t1) (subst_ty_in_tm U a t2)
  | term_lam body T          => term_lam (subst_ty_in_tm U a body) (subst_ty_in_ty U a T)
  | term_ty_app t1 T         => term_ty_app (subst_ty_in_tm U a t1) (subst_ty_in_ty U a T)
  | term_ty_lam bd body      => term_ty_lam (subst_ty_in_ty U a bd) (subst_ty_in_tm U a body)
  | term_lt_app t1 l         => term_lt_app (subst_ty_in_tm U a t1) l
  | term_lt_lam body         => term_lt_lam (subst_ty_in_tm U a body)
  | term_ctor K l ls Ts ts   => term_ctor K l ls (go_ty Ts) (go_tm ts)
  | term_match s K ar y n    =>
      term_match (subst_ty_in_tm U a s) K ar
                 (subst_ty_in_tm U a y) (subst_ty_in_tm U a n)
  | term_handle E Ts ob body =>
      term_handle E (go_ty Ts) (subst_ty_in_tm U a ob) (subst_ty_in_tm U a body)
  | term_perform t1 Ss a'    =>
      term_perform (subst_ty_in_tm U a t1) (go_ty Ss) (subst_ty_in_tm U a a')
  | term_cap E m Ts ob       => term_cap E m (go_ty Ts) (subst_ty_in_tm U a ob)
  | term_handler_m m t1      => term_handler_m m (subst_ty_in_tm U a t1)
  | term_resume m b          => term_resume m (subst_ty_in_tm U a b)
  end.

Fixpoint subst_lt_in_tm (u : lifetime) (a : atom) (t : term) : term :=
  let fix go_tm (ts : list term) : list term :=
    match ts with
    | []        => []
    | x :: rest => subst_lt_in_tm u a x :: go_tm rest
    end
  in
  let fix go_ty (Ts : list type) : list type :=
    match Ts with
    | []        => []
    | A :: rest => subst_lt_in_ty u a A :: go_ty rest
    end
  in
  let fix go_lt (ls : list lifetime) : list lifetime :=
    match ls with
    | []        => []
    | l :: rest => subst_lt_in_lt u a l :: go_lt rest
    end
  in
  match t with
  | term_bvar _              => t
  | term_fvar _              => t
  | term_app t1 t2           => term_app (subst_lt_in_tm u a t1) (subst_lt_in_tm u a t2)
  | term_lam body T          => term_lam (subst_lt_in_tm u a body) (subst_lt_in_ty u a T)
  | term_ty_app t1 T         => term_ty_app (subst_lt_in_tm u a t1) (subst_lt_in_ty u a T)
  | term_ty_lam bd body      => term_ty_lam (subst_lt_in_ty u a bd) (subst_lt_in_tm u a body)
  | term_lt_app t1 l         => term_lt_app (subst_lt_in_tm u a t1) (subst_lt_in_lt u a l)
  | term_lt_lam body         => term_lt_lam (subst_lt_in_tm u a body)
  | term_ctor K l ls Ts ts   =>
      term_ctor K (subst_lt_in_lt u a l) (go_lt ls) (go_ty Ts) (go_tm ts)
  | term_match s K ar y n    =>
      term_match (subst_lt_in_tm u a s) K ar
                 (subst_lt_in_tm u a y) (subst_lt_in_tm u a n)
  | term_handle E Ts ob body =>
      term_handle E (go_ty Ts) (subst_lt_in_tm u a ob) (subst_lt_in_tm u a body)
  | term_perform t1 Ss a'    =>
      term_perform (subst_lt_in_tm u a t1) (go_ty Ss) (subst_lt_in_tm u a a')
  | term_cap E m Ts ob       => term_cap E m (go_ty Ts) (subst_lt_in_tm u a ob)
  | term_handler_m m t1      => term_handler_m m (subst_lt_in_tm u a t1)
  | term_resume m b          => term_resume m (subst_lt_in_tm u a b)
  end.

(* ================================================================== *)
(* SECTION 5 — iterated open with a list of atoms (multi-binders)     *)
(*                                                                    *)
(* For term_match yes_body (binds `arity` tm vars) and term_handle/   *)
(* term_cap op_body (binds 2 tm + n_β ty vars).                       *)
(*                                                                    *)
(* Convention: the FIRST atom in the list opens the OUTERMOST binder  *)
(* (highest bvar index after all others have been opened).            *)
(* We implement this as fold from RIGHT: opening the last atom first  *)
(* at index 0, then each subsequent open uses index 0 again because   *)
(* every previous open shifts the indices down by one.                *)
(* ================================================================== *)

Fixpoint open_tm_wrt_tms (xs : list atom) (t : term) : term :=
  match xs with
  | []      => t
  | x :: rest => open_tm_wrt_tm (term_fvar x) (open_tm_wrt_tms rest t)
  end.

Fixpoint open_tm_wrt_tys (xs : list atom) (t : term) : term :=
  match xs with
  | []      => t
  | x :: rest => open_tm_wrt_ty (type_fvar x) (open_tm_wrt_tys rest t)
  end.

(* Iterated open with a list of TERMS (not atoms).  Used by reduction *)
(* to plug real runtime values into the body of a multi-arg binder    *)
(* (term_match yes-branch, term_handle/term_cap op-body).             *)
Fixpoint open_tm_wrt_tm_list (us : list term) (t : term) : term :=
  match us with
  | []        => t
  | u :: rest => open_tm_wrt_tm u (open_tm_wrt_tm_list rest t)
  end.

(* Iterated open with a list of TYPES.  Used to instantiate β-type    *)
(* binders of an op-body at perform-time.                             *)
Fixpoint open_tm_wrt_ty_list (Us : list type) (t : term) : term :=
  match Us with
  | []        => t
  | U :: rest => open_tm_wrt_ty U (open_tm_wrt_ty_list rest t)
  end.

(* Iterated open of a TYPE with a list of TYPES.  Used to instantiate *)
(* the n_ty type-binders of a constructor schema.                     *)
Fixpoint open_ty_wrt_ty_list (Us : list type) (T : type) : type :=
  match Us with
  | []        => T
  | U :: rest => open_ty_wrt_ty U (open_ty_wrt_ty_list rest T)
  end.

(* Iterated open of a TYPE with a list of LIFETIMES.                  *)
Fixpoint open_ty_wrt_lt_list (us : list lifetime) (T : type) : type :=
  match us with
  | []        => T
  | u :: rest => open_ty_wrt_lt u (open_ty_wrt_lt_list rest T)
  end.

(* Iterated open of a TERM with a list of LIFETIMES.                  *)
Fixpoint open_tm_wrt_lt_list (us : list lifetime) (t : term) : term :=
  match us with
  | []        => t
  | u :: rest => open_tm_wrt_lt u (open_tm_wrt_lt_list rest t)
  end.

(* ================================================================== *)
(* SECTION 6 — locally closed predicates                              *)
(*                                                                    *)
(* Cofinite quantification at every binder.                           *)
(* ================================================================== *)

Inductive lc_lifetime : lifetime -> Prop :=
  | lc_lt_fvar  : forall a, lc_lifetime (lt_fvar a)
  | lc_lt_free  : lc_lifetime lt_free
  | lc_lt_local : lc_lifetime lt_local
  | lc_lt_min   : forall l1 l2,
      lc_lifetime l1 -> lc_lifetime l2 -> lc_lifetime (lt_min l1 l2)
  .

Inductive lc_type : type -> Prop :=
  | lc_type_fvar : forall a, lc_type (type_fvar a)
  | lc_type_fun  : forall A l B,
      lc_type A -> lc_lifetime l -> lc_type B -> lc_type (type_fun A l B)
  | lc_type_ctor : forall K l Ts,
      lc_lifetime l -> Forall lc_type Ts -> lc_type (type_ctor K l Ts)
  | lc_type_lt_all : forall (L : atoms) A,
      (forall a, a `notin` L -> lc_type (open_ty_wrt_lt (lt_fvar a) A)) ->
      lc_type (type_lt_all A)
  | lc_type_ty_all : forall (L : atoms) B A,
      lc_type B ->
      (forall a, a `notin` L -> lc_type (open_ty_wrt_ty (type_fvar a) A)) ->
      lc_type (type_ty_all B A)
  .

Inductive lc_term : term -> Prop :=
  | lc_term_fvar      : forall a, lc_term (term_fvar a)
  | lc_term_app       : forall t1 t2,
      lc_term t1 -> lc_term t2 -> lc_term (term_app t1 t2)
  | lc_term_lam       : forall (L : atoms) body T,
      lc_type T ->
      (forall x, x `notin` L -> lc_term (open_tm_wrt_tm (term_fvar x) body)) ->
      lc_term (term_lam body T)
  | lc_term_ty_app    : forall t T, lc_term t -> lc_type T -> lc_term (term_ty_app t T)
  | lc_term_ty_lam    : forall (L : atoms) bd body,
      lc_type bd ->
      (forall a, a `notin` L -> lc_term (open_tm_wrt_ty (type_fvar a) body)) ->
      lc_term (term_ty_lam bd body)
  | lc_term_lt_app    : forall t l,
      lc_term t -> lc_lifetime l -> lc_term (term_lt_app t l)
  | lc_term_lt_lam    : forall (L : atoms) body,
      (forall a, a `notin` L -> lc_term (open_tm_wrt_lt (lt_fvar a) body)) ->
      lc_term (term_lt_lam body)
  | lc_term_ctor      : forall K l ls Ts ts,
      lc_lifetime l ->
      Forall lc_lifetime ls ->
      Forall lc_type Ts ->
      Forall lc_term ts ->
      lc_term (term_ctor K l ls Ts ts)
  | lc_term_match     : forall (L : atoms) s K ar y n,
      lc_term s ->
      (forall xs, length xs = ar -> NoDup xs ->
         (forall x, In x xs -> x `notin` L) ->
         lc_term (open_tm_wrt_tms xs y)) ->
      lc_term n ->
      lc_term (term_match s K ar y n)
  | lc_term_handle    : forall (L : atoms) E Ts ob body,
      Forall lc_type Ts ->
      (* op_body binds 2 tm; the n_β ty binders are part of ob's bvars *)
      (forall x k, x `notin` L -> k `notin` L -> x <> k ->
         lc_term (open_tm_wrt_tm (term_fvar x)
                   (open_tm_wrt_tm (term_fvar k) ob))) ->
      (forall x, x `notin` L -> lc_term (open_tm_wrt_tm (term_fvar x) body)) ->
      lc_term (term_handle E Ts ob body)
  | lc_term_perform   : forall t Ss a,
      lc_term t -> Forall lc_type Ss -> lc_term a -> lc_term (term_perform t Ss a)
  | lc_term_cap       : forall (L : atoms) E m Ts ob,
      Forall lc_type Ts ->
      (forall x k, x `notin` L -> k `notin` L -> x <> k ->
         lc_term (open_tm_wrt_tm (term_fvar x)
                   (open_tm_wrt_tm (term_fvar k) ob))) ->
      lc_term (term_cap E m Ts ob)
  | lc_term_handler_m : forall m t, lc_term t -> lc_term (term_handler_m m t)
  | lc_term_resume    : forall (L : atoms) m b,
      (forall x, x `notin` L -> lc_term (open_tm_wrt_tm (term_fvar x) b)) ->
      lc_term (term_resume m b)
  .

#[export] Hint Constructors lc_lifetime lc_type lc_term : core.

(* ================================================================== *)
(* SECTION 7 — gather_atoms tactic                                    *)
(*                                                                    *)
(* Used with Metalib's `pick fresh x` to obtain an atom not in any of *)
(* the free-variable sets currently in scope.                         *)
(* ================================================================== *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C1 := gather_atoms_with (fun x : lifetime => fv_lt_in_lt x) in
  let C2 := gather_atoms_with (fun x : type => fv_lt_in_ty x) in
  let C3 := gather_atoms_with (fun x : type => fv_ty_in_ty x) in
  let C4 := gather_atoms_with (fun x : term => fv_tm_in_tm x) in
  let C5 := gather_atoms_with (fun x : term => fv_ty_in_tm x) in
  let C6 := gather_atoms_with (fun x : term => fv_lt_in_tm x) in
  constr:(A \u B \u C1 \u C2 \u C3 \u C4 \u C5 \u C6).
