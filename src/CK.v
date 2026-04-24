Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.

(* ================================================================== *)
(* CK-machine: small-step reduction with explicit continuations       *)
(*                                                                    *)
(* A state is a pair (mode, kont) where the continuation is a stack  *)
(* of evaluation frames representing the "rest of the computation".  *)
(* The mode is either:                                                *)
(*   - CK_eval t   : evaluate t under the current continuation       *)
(*   - CK_ret  v   : hand value v to the topmost frame               *)
(*                                                                    *)
(* Frames mirror the congruence rules of the small-step relation:    *)
(*   F_App1     □ t2        (evaluate function, arg pending)         *)
(*   F_App2     v □         (function is a value, evaluate arg)      *)
(*   F_TyApp    □ [T]                                                 *)
(*   F_LtApp    □ {l}                                                 *)
(*   F_Ctor     K l Ts vs □ ts  (vs done, ts pending)                *)
(*   F_Match    match □ with K arity yes | _ => no                   *)
(* ================================================================== *)

Inductive frame : Type :=
  | F_App1  : term -> frame
      (* expects a function value; argument term pending *)
  | F_App2  : term -> frame
      (* stored function value; expects argument value *)
  | F_TyApp : type -> frame
  | F_LtApp : lifetime -> frame
  | F_Ctor  : ctor_tag -> lifetime -> list type
              -> list term     (* already-evaluated args (values), left-to-right *)
              -> list term     (* pending args, left-to-right *)
              -> frame
  | F_Match : ctor_tag -> nat -> term -> term -> frame
      (* tag, arity, yes_body, no_body *)
  .

Definition kont : Type := list frame.

(* ---- States ----------------------------------------------------- *)

Inductive mode : Type :=
  | CK_eval : term -> mode
  | CK_ret  : term -> mode.  (* term is a value at this point *)

Definition state : Type := mode * kont.

(* ---- Plug: reconstruct a term from a frame + inner term --------- *)

Definition plug_frame (f : frame) (inner : term) : term :=
  match f with
  | F_App1 t2          => term_app inner t2
  | F_App2 v           => term_app v inner
  | F_TyApp T          => term_ty_app inner T
  | F_LtApp l          => term_lt_app inner l
  | F_Ctor K l Ts vs ts =>
      term_ctor K l Ts (vs ++ inner :: ts)
  | F_Match K ar y n   => term_match inner K ar y n
  end.

Fixpoint plug (k : kont) (t : term) : term :=
  match k with
  | []      => t
  | f :: k' => plug k' (plug_frame f t)
  end.

Definition plug_state (s : state) : term :=
  match s with
  | (CK_eval t, k) => plug k t
  | (CK_ret  v, k) => plug k v
  end.

(* ---- CK transition relation ------------------------------------- *)

Reserved Notation "s '-c->' s'" (at level 40).

Inductive ck_step : state -> state -> Prop :=

  (* ========= decomposition: descend into evaluation contexts ===== *)

  | CK_App_push : forall t1 t2 k,
      (CK_eval (term_app t1 t2), k)
        -c-> (CK_eval t1, F_App1 t2 :: k)

  | CK_TyApp_push : forall t T k,
      (CK_eval (term_ty_app t T), k)
        -c-> (CK_eval t, F_TyApp T :: k)

  | CK_LtApp_push : forall t l k,
      (CK_eval (term_lt_app t l), k)
        -c-> (CK_eval t, F_LtApp l :: k)

  | CK_Match_push : forall scrut K ar y n k,
      (CK_eval (term_match scrut K ar y n), k)
        -c-> (CK_eval scrut, F_Match K ar y n :: k)

  (* Ctor: no args → immediate value *)
  | CK_Ctor_nil : forall K l Ts k,
      (CK_eval (term_ctor K l Ts []), k)
        -c-> (CK_ret (term_ctor K l Ts []), k)

  (* Ctor: start evaluating the first pending argument *)
  | CK_Ctor_push : forall K l Ts t ts k,
      (CK_eval (term_ctor K l Ts (t :: ts)), k)
        -c-> (CK_eval t, F_Ctor K l Ts [] ts :: k)

  (* ========= values: report via CK_ret =========================== *)

  | CK_Val_Lam : forall body T k,
      (CK_eval (term_lam body T), k) -c-> (CK_ret (term_lam body T), k)

  | CK_Val_TyLam : forall bound body k,
      (CK_eval (term_ty_lam bound body), k)
        -c-> (CK_ret (term_ty_lam bound body), k)

  | CK_Val_LtLam : forall body k,
      (CK_eval (term_lt_lam body), k)
        -c-> (CK_ret (term_lt_lam body), k)

  (* ========= return: frame-directed β-reduction ================== *)

  (* Function application: got the function value, now evaluate arg *)
  | CK_Ret_App1 : forall v t2 k,
      value v ->
      (CK_ret v, F_App1 t2 :: k)
        -c-> (CK_eval t2, F_App2 v :: k)

  (* Got the argument value; if function is a λ, do β; else stuck    *)
  (* (in well-typed code the function will always be a λ here).      *)
  | CK_Ret_Beta : forall body T v k,
      value v ->
      (CK_ret v, F_App2 (term_lam body T) :: k)
        -c-> (CK_eval (subst_tm 0 v body), k)

  (* Type application β *)
  | CK_Ret_TyBeta : forall bound body T k,
      (CK_ret (term_ty_lam bound body), F_TyApp T :: k)
        -c-> (CK_eval (subst_ty_in_tm 0 T body), k)

  (* Lifetime application β *)
  | CK_Ret_LtBeta : forall body l k,
      (CK_ret (term_lt_lam body), F_LtApp l :: k)
        -c-> (CK_eval (subst_lt_in_tm 0 l body), k)

  (* Constructor: argument done; advance or finish *)
  | CK_Ret_Ctor_next : forall K l Ts vs t ts v k,
      value v ->
      (CK_ret v, F_Ctor K l Ts vs (t :: ts) :: k)
        -c-> (CK_eval t, F_Ctor K l Ts (vs ++ [v]) ts :: k)

  | CK_Ret_Ctor_done : forall K l Ts vs v k,
      value v ->
      (CK_ret v, F_Ctor K l Ts vs [] :: k)
        -c-> (CK_ret (term_ctor K l Ts (vs ++ [v])), k)

  (* Match on a ctor value *)
  | CK_Ret_MatchYes : forall K l Ts vs y n k,
      Forall value vs ->
      (CK_ret (term_ctor K l Ts vs), F_Match K (List.length vs) y n :: k)
        -c-> (CK_eval (subst_list_tm vs y), k)

  | CK_Ret_MatchNo : forall K K' ar l Ts vs y n k,
      Forall value vs ->
      K <> K' ->
      (CK_ret (term_ctor K' l Ts vs), F_Match K ar y n :: k)
        -c-> (CK_eval n, k)

where "s '-c->' s'" := (ck_step s s').

Hint Constructors ck_step : core.

(* ---- Reflexive-transitive closure ------------------------------- *)

Inductive ck_multi : state -> state -> Prop :=
  | ckm_refl : forall s, ck_multi s s
  | ckm_step : forall s1 s2 s3,
      s1 -c-> s2 -> ck_multi s2 s3 -> ck_multi s1 s3.

Notation "s '-c->*' s'" := (ck_multi s s') (at level 40).

(* ---- Initial / final states ------------------------------------- *)

Definition load (t : term) : state := (CK_eval t, []).

Definition final (s : state) : Prop :=
  match s with
  | (CK_ret v, []) => value v
  | _              => False
  end.

(* ---- Plug correctness ------------------------------------------- *)

Lemma plug_state_load : forall t, plug_state (load t) = t.
Proof. reflexivity. Qed.

Lemma plug_frame_app : forall f t, plug_frame f t = plug_frame f t.
Proof. reflexivity. Qed.
