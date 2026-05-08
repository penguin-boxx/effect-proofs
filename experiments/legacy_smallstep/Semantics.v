(* ================================================================== *)
(* Semantics.v — small-step reduction (locally nameless)              *)
(*                                                                    *)
(* Layered presentation:                                              *)
(*   1. head_step (-->h) — local rewrite rules, no congruence.        *)
(*   2. ectx / plug      — call-by-value evaluation contexts.         *)
(*   3. step (==>)       — head_step under any well-formed ectx.      *)
(*                                                                    *)
(* Differences from the legacy de Bruijn version:                     *)
(*   - All single-binder substitutions become opens with a value:     *)
(*       subst_tm 0 v body          ↦ open_tm_wrt_tm v body           *)
(*       subst_ty_in_tm 0 T body    ↦ open_tm_wrt_ty T body           *)
(*       subst_lt_in_tm 0 l body    ↦ open_tm_wrt_lt l body           *)
(*   - Multi-binder forms use the `open_*_list` helpers.              *)
(*   - The H_Perform rule no longer needs `shift_ectx_tm` because LN  *)
(*     ectx contents are locally closed (no de Bruijn indices to      *)
(*     adjust).  Instead we close the captured ectx on a fresh atom   *)
(*     to obtain the resumption's body.                               *)
(* ================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.

From Metalib Require Export Metatheory.
Require Export Syntax.
Require Export Substitution.

(* ================================================================== *)
(* Evaluation contexts                                                *)
(* ================================================================== *)

Inductive ectx : Type :=
  | EC_hole       : ectx
  | EC_app1       : ectx -> term -> ectx
  | EC_app2       : term -> ectx -> ectx
  | EC_ty_app     : ectx -> type -> ectx
  | EC_lt_app     : ectx -> lifetime -> ectx
  | EC_ctor       : ctor_tag -> lifetime -> list lifetime -> list type ->
                    list term -> ectx -> list term -> ectx
  | EC_match      : ectx -> ctor_tag -> nat -> term -> term -> ectx
  | EC_handler_m  : marker -> ectx -> ectx
  | EC_perform_r  : ectx -> list type -> term -> ectx
  | EC_perform_a  : term -> list type -> ectx -> ectx
  .

Fixpoint plug (E : ectx) (t : term) : term :=
  match E with
  | EC_hole                       => t
  | EC_app1 E1 t2                 => term_app (plug E1 t) t2
  | EC_app2 v E2                  => term_app v (plug E2 t)
  | EC_ty_app E1 T                => term_ty_app (plug E1 t) T
  | EC_lt_app E1 l                => term_lt_app (plug E1 t) l
  | EC_ctor K l lts Ts vs E1 ts   => term_ctor K l lts Ts (vs ++ plug E1 t :: ts)
  | EC_match E1 K ar y n          => term_match (plug E1 t) K ar y n
  | EC_handler_m m E1             => term_handler_m m (plug E1 t)
  | EC_perform_r E1 Ss arg        => term_perform (plug E1 t) Ss arg
  | EC_perform_a v Ss E1          => term_perform v Ss (plug E1 t)
  end.

(* Free term-atoms appearing in an evaluation context (everywhere     *)
(* except in the hole). Used to pick a fresh atom in H_Perform.       *)
Fixpoint fv_tm_in_ectx (E : ectx) : atoms :=
  match E with
  | EC_hole                       => empty
  | EC_app1 E1 t2                 => union (fv_tm_in_ectx E1) (fv_tm_in_tm t2)
  | EC_app2 v E2                  => union (fv_tm_in_tm v) (fv_tm_in_ectx E2)
  | EC_ty_app E1 _                => fv_tm_in_ectx E1
  | EC_lt_app E1 _                => fv_tm_in_ectx E1
  | EC_ctor _ _ _ _ vs E1 ts      =>
      union (fold_right (fun u acc => union (fv_tm_in_tm u) acc) empty vs)
            (union (fv_tm_in_ectx E1)
                   (fold_right (fun u acc => union (fv_tm_in_tm u) acc) empty ts))
  | EC_match E1 _ _ y n           =>
      union (fv_tm_in_ectx E1) (union (fv_tm_in_tm y) (fv_tm_in_tm n))
  | EC_handler_m _ E1             => fv_tm_in_ectx E1
  | EC_perform_r E1 _ arg         => union (fv_tm_in_ectx E1) (fv_tm_in_tm arg)
  | EC_perform_a v _ E1           => union (fv_tm_in_tm v) (fv_tm_in_ectx E1)
  end.

(* Marker-pure evaluation contexts.  Same shape as legacy: every form *)
Inductive pure_ectx_m (m : marker) : ectx -> Prop :=
  | pem_hole       : pure_ectx_m m EC_hole
  | pem_app1       : forall E t,
      pure_ectx_m m E -> pure_ectx_m m (EC_app1 E t)
  | pem_app2       : forall v E,
      pure_ectx_m m E -> pure_ectx_m m (EC_app2 v E)
  | pem_ty_app     : forall E T,
      pure_ectx_m m E -> pure_ectx_m m (EC_ty_app E T)
  | pem_lt_app     : forall E l,
      pure_ectx_m m E -> pure_ectx_m m (EC_lt_app E l)
  | pem_ctor       : forall K l lts Ts vs E ts,
      pure_ectx_m m E -> pure_ectx_m m (EC_ctor K l lts Ts vs E ts)
  | pem_match      : forall E K ar y n,
      pure_ectx_m m E -> pure_ectx_m m (EC_match E K ar y n)
  | pem_handler_m  : forall m' E,
      m <> m' ->
      pure_ectx_m m E -> pure_ectx_m m (EC_handler_m m' E)
  | pem_perform_r  : forall E Ss arg,
      pure_ectx_m m E -> pure_ectx_m m (EC_perform_r E Ss arg)
  | pem_perform_a  : forall v Ss E,
      pure_ectx_m m E -> pure_ectx_m m (EC_perform_a v Ss E)
  .

#[export] Hint Constructors pure_ectx_m : core.

(* ================================================================== *)
(* Head reductions                                                    *)
(* ================================================================== *)

Reserved Notation "t '~~>h' t'" (at level 55).

Inductive head_step : term -> term -> Prop :=

  | H_Beta : forall body T v,
      value v ->
      term_app (term_lam body T) v ~~>h open_tm_wrt_tm v body

  | H_TyBeta : forall bound body T,
      term_ty_app (term_ty_lam bound body) T ~~>h open_tm_wrt_ty T body

  | H_LtBeta : forall body l,
      term_lt_app (term_lt_lam body) l ~~>h open_tm_wrt_lt l body

  (* Pattern match success.                                            *)
  (* The yes-branch binds `length vs` term variables.  In the order    *)
  (* used by `open_tm_wrt_tm_list`, the FIRST element of `vs` opens    *)
  (* the OUTERMOST binder.  Lifetime args `lts` are opened first       *)
  (* (innermost in the schema's structure).                            *)
  | H_MatchYes : forall K l lts Ts vs yes_body no_body,
      Forall value vs ->
      term_match (term_ctor K l lts Ts vs) K (List.length vs) yes_body no_body
        ~~>h open_tm_wrt_tm_list vs (open_tm_wrt_lt_list lts yes_body)

  | H_MatchNo : forall K K' l lts Ts vs arity yes_body no_body,
      Forall value vs ->
      K <> K' ->
      term_match (term_ctor K' l lts Ts vs) K arity yes_body no_body ~~>h no_body

  (* (handle): allocate a fresh marker m, install a delimiter, and    *)
  (* substitute the capability for the body's tm-binder.              *)
  | H_Handle : forall E_tag Ts op_body body m,
      term_handle E_tag Ts op_body body
        ~~>h term_handler_m m
              (open_tm_wrt_tm (term_cap E_tag m Ts op_body) body)

  (* (return): a delimiter around a value collapses. *)
  | H_Return : forall m v,
      value v ->
      term_handler_m m v ~~>h v

  (* (perform): the operation argument and the reified resumption are *)
  (* substituted into op_body's two tm-binders, after the n_β type    *)
  (* arguments Ss are opened.                                         *)
  (*                                                                  *)
  (* The resumption's body re-installs the delimiter around the       *)
  (* captured pure context P with a hole filled by a fresh atom x;    *)
  (* we then close on x to obtain a function body that, when applied, *)
  (* opens that hole with the supplied value.                         *)
  (*                                                                  *)
  (* Convention (matching the legacy [v; resume] order):              *)
  (*   index 0 (innermost)  ↦ v        (operation argument)           *)
  (*   index 1              ↦ resume   (resumption k)                 *)
  | H_Perform : forall E_tag m Ts op_body Ss v P x,
      value v ->
      pure_ectx_m m P ->
      x `notin` union (fv_tm_in_ectx P) (fv_tm_in_tm v) ->
      let resume_body :=
        close_tm_wrt_tm x
          (term_handler_m m (plug P (term_fvar x))) in
      term_handler_m m
        (plug P (term_perform (term_cap E_tag m Ts op_body) Ss v))
        ~~>h
          open_tm_wrt_tm_list
            [v; term_resume m resume_body]
            (open_tm_wrt_ty_list Ss op_body)

  (* (resume): apply a reified resumption to a value. *)
  | H_Resume : forall m b v,
      value v ->
      term_app (term_resume m b) v ~~>h open_tm_wrt_tm v b

where "t '~~>h' t'" := (head_step t t').

#[export] Hint Constructors head_step : core.

(* ================================================================== *)
(* Evaluation context well-formedness                                 *)
(* ================================================================== *)

Inductive ectx_wf : ectx -> Prop :=
  | wf_hole       : ectx_wf EC_hole
  | wf_app1       : forall E t,
      ectx_wf E -> ectx_wf (EC_app1 E t)
  | wf_app2       : forall v E,
      value v -> ectx_wf E -> ectx_wf (EC_app2 v E)
  | wf_ty_app     : forall E T,
      ectx_wf E -> ectx_wf (EC_ty_app E T)
  | wf_lt_app     : forall E l,
      ectx_wf E -> ectx_wf (EC_lt_app E l)
  | wf_ctor       : forall K l lts Ts vs E ts,
      Forall value vs -> ectx_wf E ->
      ectx_wf (EC_ctor K l lts Ts vs E ts)
  | wf_match      : forall E K ar y n,
      ectx_wf E -> ectx_wf (EC_match E K ar y n)
  | wf_handler_m  : forall m E,
      ectx_wf E -> ectx_wf (EC_handler_m m E)
  | wf_perform_r  : forall E Ss arg,
      ectx_wf E -> ectx_wf (EC_perform_r E Ss arg)
  | wf_perform_a  : forall v Ss E,
      value v -> ectx_wf E ->
      ectx_wf (EC_perform_a v Ss E)
  .

#[export] Hint Constructors ectx_wf : core.

(* ================================================================== *)
(* Step relation                                                      *)
(* ================================================================== *)

Reserved Notation "t '~~>' t'" (at level 55).

Inductive step : term -> term -> Prop :=
  | S_step : forall E r r',
      ectx_wf E ->
      r ~~>h r' ->
      plug E r ~~> plug E r'
where "t '~~>' t'" := (step t t').

#[export] Hint Constructors step : core.

(* ================================================================== *)
(* Reflexive-transitive closure                                       *)
(* ================================================================== *)

Reserved Notation "t '~~>*' t'" (at level 55).

Inductive multi_step : term -> term -> Prop :=
  | MS_refl : forall t, t ~~>* t
  | MS_step : forall t1 t2 t3,
      t1 ~~> t2 -> t2 ~~>* t3 -> t1 ~~>* t3
where "t '~~>*' t'" := (multi_step t t').

#[export] Hint Constructors multi_step : core.
