Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.

(* ================================================================== *)
(* Reduction semantics, layered presentation.                         *)
(*                                                                    *)
(*   1. `head_step` (`-->h`) — the local rewrite rules (β, match,     *)
(*      handle, return) with NO congruence.                           *)
(*   2. `ectx`/`plug`         — call-by-value evaluation contexts.    *)
(*   3. `step` (`==>`)        — head step under any well-formed       *)
(*      evaluation context: `plug E r ==> plug E r'` whenever         *)
(*      `r -->h r'` and `ectx_wf E`.                                  *)
(*                                                                    *)
(* The familiar structural rules (`S_Beta`, `S_App1`, `S_App2`, ...)  *)
(* are then derived as lemmas, so existing client proofs that pattern *)
(* on those names continue to work; structural-inversion lemmas       *)
(* (`step_app_inv`, ...) recover the case-analysis principle.         *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Evaluation contexts (defined first so head_step can reference plug,*)
(* pure_ectx and shift_ectx_tm in the H_Perform rule).                *)
(* ------------------------------------------------------------------ *)

Inductive ectx : Type :=
  | EC_hole       : ectx
  | EC_app1       : ectx -> term -> ectx
  | EC_app2       : term -> ectx -> ectx
  | EC_ty_app     : ectx -> type -> ectx
  | EC_lt_app     : ectx -> lifetime -> ectx
  | EC_ctor       : ctor_tag -> lifetime -> list lifetime -> list type ->
                    list term -> ectx -> list term -> ectx
  | EC_match      : ectx -> ctor_tag -> nat -> nat -> term -> term -> ectx
  | EC_handler_m  : marker -> ectx -> ectx
  | EC_perform_r  : ectx -> list type -> term -> ectx
  | EC_perform_a  : term -> list type -> ectx -> ectx.

Fixpoint plug (E : ectx) (t : term) : term :=
  match E with
  | EC_hole                       => t
  | EC_app1 E1 t2                 => term_app (plug E1 t) t2
  | EC_app2 v E2                  => term_app v (plug E2 t)
  | EC_ty_app E1 T                => term_ty_app (plug E1 t) T
  | EC_lt_app E1 l                => term_lt_app (plug E1 t) l
  | EC_ctor K l lts Ts vs E1 ts   => term_ctor K l lts Ts (vs ++ plug E1 t :: ts)
  | EC_match E1 K nlt ar y n      => term_match (plug E1 t) K nlt ar y n
  | EC_handler_m m E1             => term_handler_m m (plug E1 t)
  | EC_perform_r E1 Ss arg        => term_perform (plug E1 t) Ss arg
  | EC_perform_a v Ss E1          => term_perform v Ss (plug E1 t)
  end.

(* Marker-pure evaluation contexts for marker m:  all ectx shapes     *)
(* are allowed EXCEPT EC_handler_m with the *same* marker m.          *)
(* Handlers with a *different* marker m' ≠ m are transparent and      *)
(* may sit in the hole, so that H_Perform can look past inner         *)
(* handlers for different effects and find the correct matching       *)
(* delimiter outside.                                                 *)
Inductive pure_ectx_m (m : marker) : ectx -> Prop :=
  | pem_hole      : pure_ectx_m m EC_hole
  | pem_app1      : forall E t,
      pure_ectx_m m E -> pure_ectx_m m (EC_app1 E t)
  | pem_app2      : forall v E,
      pure_ectx_m m E -> pure_ectx_m m (EC_app2 v E)
  | pem_ty_app    : forall E T,
      pure_ectx_m m E -> pure_ectx_m m (EC_ty_app E T)
  | pem_lt_app    : forall E l,
      pure_ectx_m m E -> pure_ectx_m m (EC_lt_app E l)
  | pem_ctor      : forall K l lts Ts vs E ts,
      pure_ectx_m m E -> pure_ectx_m m (EC_ctor K l lts Ts vs E ts)
  | pem_match     : forall E K nlt ar y n,
      pure_ectx_m m E -> pure_ectx_m m (EC_match E K nlt ar y n)
  | pem_handler_m : forall m' E,
      m <> m' ->
      pure_ectx_m m E -> pure_ectx_m m (EC_handler_m m' E)
  | pem_perform_r : forall E Ss arg,
      pure_ectx_m m E -> pure_ectx_m m (EC_perform_r E Ss arg)
  | pem_perform_a : forall v Ss E,
      pure_ectx_m m E -> pure_ectx_m m (EC_perform_a v Ss E).

Hint Constructors pure_ectx_m : core.

(* Term-variable shift into the subterms of an ectx.  Used by the      *)
(* H_Perform rule to lift the captured pure context under the          *)
(* resumption binder.                                                  *)
Fixpoint shift_ectx_tm (amount cutoff : nat) (E : ectx) : ectx :=
  match E with
  | EC_hole                     => EC_hole
  | EC_app1 E1 t2               => EC_app1 (shift_ectx_tm amount cutoff E1)
                                           (shift_tm amount cutoff t2)
  | EC_app2 v E2                => EC_app2 (shift_tm amount cutoff v)
                                           (shift_ectx_tm amount cutoff E2)
  | EC_ty_app E1 T              => EC_ty_app (shift_ectx_tm amount cutoff E1) T
  | EC_lt_app E1 l              => EC_lt_app (shift_ectx_tm amount cutoff E1) l
  | EC_ctor K l lts Ts vs E1 ts => EC_ctor K l lts Ts
                                    (List.map (shift_tm amount cutoff) vs)
                                    (shift_ectx_tm amount cutoff E1)
                                    (List.map (shift_tm amount cutoff) ts)
  | EC_match E1 K nlt ar y n    => EC_match (shift_ectx_tm amount cutoff E1) K nlt ar
                                    (shift_tm amount (cutoff + ar) y)
                                    (shift_tm amount cutoff n)
  | EC_handler_m m E1           => EC_handler_m m (shift_ectx_tm amount cutoff E1)
  | EC_perform_r E1 Ss arg      => EC_perform_r (shift_ectx_tm amount cutoff E1)
                                                 Ss
                                                 (shift_tm amount cutoff arg)
  | EC_perform_a v Ss E1        => EC_perform_a (shift_tm amount cutoff v)
                                                 Ss
                                                 (shift_ectx_tm amount cutoff E1)
  end.

(* Runtime markers occurring in a term.  This is used only to choose a
   fresh delimiter marker when a source-level handle reduces. *)
Fixpoint markers_in (t : term) : list marker :=
  let fix markers_in_list_local (ts : list term) : list marker :=
    match ts with
    | [] => []
    | u :: rest => markers_in u ++ markers_in_list_local rest
    end
  in
  match t with
  | term_var _ => []
  | term_app t1 t2 => markers_in t1 ++ markers_in t2
  | term_lam body _ => markers_in body
  | term_ty_app t1 _ => markers_in t1
  | term_ty_lam _ body => markers_in body
  | term_lt_app t1 _ => markers_in t1
  | term_lt_lam body => markers_in body
  | term_ctor _ _ _ _ ts => markers_in_list_local ts
  | term_match scrut _ _ _ yes_body no_body =>
      markers_in scrut ++ markers_in yes_body ++ markers_in no_body
  | term_handle _ _ op_body body => markers_in op_body ++ markers_in body
  | term_perform recv _ arg => markers_in recv ++ markers_in arg
  | term_cap _ m _ op_body => m :: markers_in op_body
  | term_handler_m m body => m :: markers_in body
  | term_resume m body => m :: markers_in body
  end.

Fixpoint markers_in_list (ts : list term) : list marker :=
  match ts with
  | [] => []
  | u :: rest => markers_in u ++ markers_in_list rest
  end.

Lemma markers_in_ctor : forall K l lts Ts ts,
  markers_in (term_ctor K l lts Ts ts) = markers_in_list ts.
Proof.
  intros K l lts Ts ts. induction ts as [|t ts IH]; simpl.
  - reflexivity.
  - reflexivity.
Qed.

Definition marker_bound (t : term) : marker :=
  S (fold_right Nat.max 0 (markers_in t)).

Lemma in_fold_max_le : forall m ms,
  In m ms -> m <= fold_right Nat.max 0 ms.
Proof.
  intros m ms Hin. induction ms as [|x xs IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst. apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma markers_in_lt_bound : forall t m,
  In m (markers_in t) -> m < marker_bound t.
Proof.
  intros t m Hin. unfold marker_bound.
  apply Nat.lt_succ_r. apply in_fold_max_le. exact Hin.
Qed.

Lemma marker_bound_fresh : forall t,
  ~ In (marker_bound t) (markers_in t).
Proof.
  intros t Hin.
  pose proof (markers_in_lt_bound t (marker_bound t) Hin) as Hlt.
  apply (Nat.lt_irrefl (marker_bound t)); exact Hlt.
Qed.

Lemma markers_in_list_app : forall xs ys,
  markers_in_list (xs ++ ys) = markers_in_list xs ++ markers_in_list ys.
Proof.
  intros xs ys. induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite IH. rewrite List.app_assoc. reflexivity.
Qed.

Lemma markers_in_list_focus : forall vs t ts m,
  In m (markers_in t) ->
  In m (markers_in_list (vs ++ t :: ts)).
Proof.
  intros vs t ts m Hin.
  rewrite markers_in_list_app. rewrite List.in_app_iff.
  right. simpl. rewrite List.in_app_iff. left. exact Hin.
Qed.

(* ------------------------------------------------------------------ *)
(* 1. Head reductions                                                 *)
(* ------------------------------------------------------------------ *)

Reserved Notation "t '-->h' t'" (at level 40).

Inductive head_step : term -> term -> Prop :=

  | H_Beta : forall body T v,
      value v ->
      term_app (term_lam body T) v -->h subst_tm 0 v body

  | H_TyBeta : forall bound body T,
      term_ty_app (term_ty_lam bound body) T -->h subst_ty_in_tm 0 T body

  | H_LtBeta : forall body l,
      term_lt_app (term_lt_lam body) l -->h subst_lt_in_tm 0 l body

    | H_MatchYes : forall K l lts Ts vs n_lt yes_body no_body,
      Forall value vs ->
      term_match (term_ctor K l lts Ts vs) K n_lt (List.length vs) yes_body no_body
        -->h subst_list_tm vs (subst_list_lt_in_tm lts yes_body)

    | H_MatchNo : forall K K' l lts Ts vs n_lt arity yes_body no_body,
      Forall value vs ->
      K <> K' ->
      term_match (term_ctor K' l lts Ts vs) K n_lt arity yes_body no_body -->h no_body

  (* (return): a delimiter around a value collapses. *)
  | H_Return : forall m v,
      value v ->
      term_handler_m m v -->h v

  (* (perform): a `perform (cap E_tag m Ts op_body) Ss v` inside a    *)
  (* matching handler delimiter `term_handler_m m _` reduces by       *)
  (*   1) capturing the surrounding pure (delimiter-free) ectx P;     *)
  (*   2) reifying the resumption as `term_resume m _` re-installing  *)
  (*      the delimiter around `plug P [hole]`;                       *)
  (*   3) instantiating the op-body's β-type-binders with Ss, then    *)
  (*      substituting [arg, resumption] for its term-binders.        *)
  (* The shift on P accounts for the new term-binder introduced by    *)
  (* the resumption.                                                  *)
  | H_Perform : forall E_tag m Ts op_body Ss v P,
      value v -> pure_ectx_m m P ->
      term_handler_m m
        (plug P (term_perform (term_cap E_tag m Ts op_body) Ss v))
        -->h
          subst_list_tm [v; term_resume m (plug (shift_ectx_tm 1 0 P) (term_var 0))]
            (subst_list_ty_in_tm Ss
              op_body)

  (* (resume): apply a reified resumption to a value. *)
  | H_Resume : forall m b v,
      value v ->
      term_app (term_resume m b) v
        -->h
          term_handler_m m (subst_tm 0 v b)

where "t '-->h' t'" := (head_step t t').

Hint Constructors head_step : core.

(* ------------------------------------------------------------------ *)
(* 2. Evaluation context well-formedness                               *)
(* ------------------------------------------------------------------ *)

(* Well-formedness: arguments to the left of an evaluation hole must  *)
(* already be values (call-by-value, left-to-right).                  *)
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
  | wf_match      : forall E K nlt ar y n,
      ectx_wf E -> ectx_wf (EC_match E K nlt ar y n)
  | wf_handler_m  : forall m E,
      ectx_wf E -> ectx_wf (EC_handler_m m E)
  | wf_perform_r  : forall E Ss arg,
      ectx_wf E -> ectx_wf (EC_perform_r E Ss arg)
  | wf_perform_a  : forall v Ss E,
      value v -> ectx_wf E ->
      ectx_wf (EC_perform_a v Ss E).

Hint Constructors ectx_wf : core.

(* ------------------------------------------------------------------ *)
(* 3. Reduction = head step under any well-formed evaluation context   *)
(* ------------------------------------------------------------------ *)

Reserved Notation "t '==>' t'" (at level 40).

Inductive step : term -> term -> Prop :=
  | S_step : forall E r r',
      ectx_wf E ->
      r -->h r' ->
      plug E r ==> plug E r'
  | S_HandleCtx : forall E E_tag Ts op_body body m,
      ectx_wf E ->
      ~ In m (markers_in (plug E (term_handle E_tag Ts op_body body))) ->
      plug E (term_handle E_tag Ts op_body body)
        ==> plug E (term_handler_m m (subst_tm 0 (term_cap E_tag m Ts op_body) body))
where "t '==>' t'" := (step t t').

Hint Constructors step : core.

(* ================================================================== *)
(* Derived structural rules                                           *)
(*                                                                    *)
(* These are the familiar S_* rules of a structural small-step        *)
(* presentation, here proven from the layered (head + plug) form.     *)
(* They allow client code to keep using `apply S_Beta`, `apply        *)
(* S_App1`, ... without exposing the underlying ectx machinery.       *)
(* ================================================================== *)

Lemma S_Beta : forall body T v,
  value v ->
  term_app (term_lam body T) v ==> subst_tm 0 v body.
Proof. intros. apply (S_step EC_hole); auto. Qed.

Lemma S_TyBeta : forall bound body T,
  term_ty_app (term_ty_lam bound body) T ==> subst_ty_in_tm 0 T body.
Proof. intros. apply (S_step EC_hole); auto. Qed.

Lemma S_LtBeta : forall body l,
  term_lt_app (term_lt_lam body) l ==> subst_lt_in_tm 0 l body.
Proof. intros. apply (S_step EC_hole); auto. Qed.

Lemma S_App1 : forall t1 t2,
  (exists t1', t1 ==> t1') ->
  exists t', term_app t1 t2 ==> t'.
Proof.
  intros t1 t2 [t1' H]. inversion H; subst.
  - exists (term_app (plug E r') t2). apply (S_step (EC_app1 E t2)); auto.
  - exists (term_app
      (plug E (term_handler_m (marker_bound (term_app (plug E (term_handle E_tag Ts op_body body)) t2))
        (subst_tm 0 (term_cap E_tag (marker_bound (term_app (plug E (term_handle E_tag Ts op_body body)) t2)) Ts op_body) body)))
      t2).
    apply (S_HandleCtx (EC_app1 E t2)); auto.
    apply marker_bound_fresh.
Qed.

Lemma S_App2 : forall v t2,
  value v ->
  (exists t2', t2 ==> t2') ->
  exists t', term_app v t2 ==> t'.
Proof.
  intros v t2 Hv [t2' H]. inversion H; subst.
  - exists (term_app v (plug E r')). apply (S_step (EC_app2 v E)); auto.
  - exists (term_app v
      (plug E (term_handler_m (marker_bound (term_app v (plug E (term_handle E_tag Ts op_body body))))
        (subst_tm 0 (term_cap E_tag (marker_bound (term_app v (plug E (term_handle E_tag Ts op_body body)))) Ts op_body) body)))).
    apply (S_HandleCtx (EC_app2 v E)); auto.
    apply marker_bound_fresh.
Qed.

Lemma S_TyApp : forall t T,
  (exists t', t ==> t') ->
  exists u, term_ty_app t T ==> u.
Proof.
  intros t T [t' H]. inversion H; subst.
  - exists (term_ty_app (plug E r') T). apply (S_step (EC_ty_app E T)); auto.
  - exists (term_ty_app
      (plug E (term_handler_m (marker_bound (term_ty_app (plug E (term_handle E_tag Ts op_body body)) T))
        (subst_tm 0 (term_cap E_tag (marker_bound (term_ty_app (plug E (term_handle E_tag Ts op_body body)) T)) Ts op_body) body)))
      T).
    apply (S_HandleCtx (EC_ty_app E T)); auto.
    apply marker_bound_fresh.
Qed.

Lemma S_LtApp : forall t l,
  (exists t', t ==> t') ->
  exists u, term_lt_app t l ==> u.
Proof.
  intros t l [t' H]. inversion H; subst.
  - exists (term_lt_app (plug E r') l). apply (S_step (EC_lt_app E l)); auto.
  - exists (term_lt_app
      (plug E (term_handler_m (marker_bound (term_lt_app (plug E (term_handle E_tag Ts op_body body)) l))
        (subst_tm 0 (term_cap E_tag (marker_bound (term_lt_app (plug E (term_handle E_tag Ts op_body body)) l)) Ts op_body) body)))
      l).
    apply (S_HandleCtx (EC_lt_app E l)); auto.
    apply marker_bound_fresh.
Qed.

Lemma S_Ctor : forall K l lts Ts vs t ts,
  Forall value vs ->
  (exists t', t ==> t') ->
  exists u, term_ctor K l lts Ts (vs ++ t :: ts) ==> u.
Proof.
  intros K l lts Ts vs t ts Hvs [t' H]. inversion H; subst.
  - exists (term_ctor K l lts Ts (vs ++ plug E r' :: ts)).
    apply (S_step (EC_ctor K l lts Ts vs E ts)); auto.
  - exists (term_ctor K l lts Ts
      (vs ++ plug E (term_handler_m
        (marker_bound (term_ctor K l lts Ts (vs ++ plug E (term_handle E_tag Ts0 op_body body) :: ts)))
        (subst_tm 0 (term_cap E_tag
          (marker_bound (term_ctor K l lts Ts (vs ++ plug E (term_handle E_tag Ts0 op_body body) :: ts)))
          Ts0 op_body) body)) :: ts)).
    apply (S_HandleCtx (EC_ctor K l lts Ts vs E ts)); auto.
    apply marker_bound_fresh.
Qed.

Lemma S_MatchYes : forall K l lts Ts vs n_lt yes_body no_body,
  Forall value vs ->
  term_match (term_ctor K l lts Ts vs) K n_lt (List.length vs) yes_body no_body
    ==> subst_list_tm vs (subst_list_lt_in_tm lts yes_body).
Proof.
  intros. apply (S_step EC_hole).
  - constructor.
  - apply H_MatchYes; auto.
Qed.

Lemma S_MatchNo : forall K K' l lts Ts vs n_lt arity yes_body no_body,
  Forall value vs ->
  K <> K' ->
  term_match (term_ctor K' l lts Ts vs) K n_lt arity yes_body no_body ==> no_body.
Proof.
  intros. apply (S_step EC_hole).
  - constructor.
  - apply H_MatchNo; auto.
Qed.

Lemma S_Match : forall scrutinee tag n_lt arity yes_body no_body,
  (exists scrutinee', scrutinee ==> scrutinee') ->
  exists u,
    term_match scrutinee tag n_lt arity yes_body no_body ==> u.
Proof.
  intros s tag nlt ar y n [s' H]. inversion H; subst.
  - exists (term_match (plug E r') tag nlt ar y n).
    apply (S_step (EC_match E tag nlt ar y n)); auto.
  - exists (term_match
      (plug E (term_handler_m
        (marker_bound (term_match (plug E (term_handle E_tag Ts op_body body)) tag nlt ar y n))
        (subst_tm 0 (term_cap E_tag
          (marker_bound (term_match (plug E (term_handle E_tag Ts op_body body)) tag nlt ar y n))
          Ts op_body) body)))
      tag nlt ar y n).
    apply (S_HandleCtx (EC_match E tag nlt ar y n)); auto.
    apply marker_bound_fresh.
Qed.

Lemma S_Handle : forall E_tag Ts op_body body m,
  ~ In m (markers_in (term_handle E_tag Ts op_body body)) ->
  term_handle E_tag Ts op_body body
    ==> term_handler_m m (subst_tm 0 (term_cap E_tag m Ts op_body) body).
Proof.
  intros E_tag Ts op_body body m Hfresh.
  apply (S_HandleCtx EC_hole E_tag Ts op_body body m); [constructor | exact Hfresh].
Qed.

Lemma S_Return : forall m v,
  value v -> term_handler_m m v ==> v.
Proof. intros. apply (S_step EC_hole); auto. Qed.

Lemma S_HandlerM : forall m t,
  (exists t', t ==> t') ->
  exists u, term_handler_m m t ==> u.
Proof.
  intros m t [t' H]. inversion H; subst.
  - exists (term_handler_m m (plug E r')). apply (S_step (EC_handler_m m E)); auto.
  - exists (term_handler_m m
      (plug E (term_handler_m
        (marker_bound (term_handler_m m (plug E (term_handle E_tag Ts op_body body))))
        (subst_tm 0 (term_cap E_tag
          (marker_bound (term_handler_m m (plug E (term_handle E_tag Ts op_body body))))
          Ts op_body) body)))).
    apply (S_HandleCtx (EC_handler_m m E)); auto.
    apply marker_bound_fresh.
Qed.

Lemma S_PerformRecv : forall t Ss arg,
  (exists t', t ==> t') ->
  exists u, term_perform t Ss arg ==> u.
Proof.
  intros t Ss arg [t' H]. inversion H; subst.
  - exists (term_perform (plug E r') Ss arg). apply (S_step (EC_perform_r E Ss arg)); auto.
  - exists (term_perform
      (plug E (term_handler_m
        (marker_bound (term_perform (plug E (term_handle E_tag Ts op_body body)) Ss arg))
        (subst_tm 0 (term_cap E_tag
          (marker_bound (term_perform (plug E (term_handle E_tag Ts op_body body)) Ss arg))
          Ts op_body) body)))
      Ss arg).
    apply (S_HandleCtx (EC_perform_r E Ss arg)); auto.
    apply marker_bound_fresh.
Qed.

Lemma S_PerformArg : forall v Ss t,
  value v ->
  (exists t', t ==> t') ->
  exists u, term_perform v Ss t ==> u.
Proof.
  intros v Ss t Hv [t' H]. inversion H; subst.
  - exists (term_perform v Ss (plug E r')). apply (S_step (EC_perform_a v Ss E)); auto.
  - exists (term_perform v Ss
      (plug E (term_handler_m
        (marker_bound (term_perform v Ss (plug E (term_handle E_tag Ts op_body body))))
        (subst_tm 0 (term_cap E_tag
          (marker_bound (term_perform v Ss (plug E (term_handle E_tag Ts op_body body))))
          Ts op_body) body)))).
    apply (S_HandleCtx (EC_perform_a v Ss E)); auto.
    apply marker_bound_fresh.
Qed.

Lemma S_Resume : forall m b v,
  value v ->
  term_app (term_resume m b) v
    ==> term_handler_m m (subst_tm 0 v b).
Proof. intros. apply (S_step EC_hole); auto. Qed.

(* ================================================================== *)
(* Structural inversion                                                *)
(*                                                                    *)
(* Recover the case-analysis principle of the classical structural    *)
(* small-step relation. Each lemma converts a step on a particular    *)
(* term shape into the disjunction of the rules that could have       *)
(* produced it, naming the resulting sub-derivations.                  *)
(* ================================================================== *)

(* No step from a value (or from a variable). *)

Lemma no_step_var : forall x t', term_var x ==> t' -> False.
Proof.
  intros x t' H. remember (term_var x) as t eqn:Ht.
  induction H; subst.
  - destruct E; simpl in Ht; try discriminate.
    subst. match goal with Hh : _ -->h _ |- _ => inversion Hh end.
  - destruct E; simpl in Ht; discriminate.
Qed.

Lemma no_step_lam : forall body T t',
  term_lam body T ==> t' -> False.
Proof.
  intros body T t' H. remember (term_lam body T) as t eqn:Ht.
  induction H; subst.
  - destruct E; simpl in Ht; try discriminate.
    subst. match goal with Hh : _ -->h _ |- _ => inversion Hh end.
  - destruct E; simpl in Ht; discriminate.
Qed.

Lemma no_step_ty_lam : forall bound body t',
  term_ty_lam bound body ==> t' -> False.
Proof.
  intros bound body t' H. remember (term_ty_lam bound body) as t eqn:Ht.
  induction H; subst.
  - destruct E; simpl in Ht; try discriminate.
    subst. match goal with Hh : _ -->h _ |- _ => inversion Hh end.
  - destruct E; simpl in Ht; discriminate.
Qed.

Lemma no_step_lt_lam : forall body t',
  term_lt_lam body ==> t' -> False.
Proof.
  intros body t' H. remember (term_lt_lam body) as t eqn:Ht.
  induction H; subst.
  - destruct E; simpl in Ht; try discriminate.
    subst. match goal with Hh : _ -->h _ |- _ => inversion Hh end.
  - destruct E; simpl in Ht; discriminate.
Qed.

Lemma no_step_cap : forall E_tag m Ts op_body t',
  term_cap E_tag m Ts op_body ==> t' -> False.
Proof.
  intros Et m Ts ob t' H. remember (term_cap Et m Ts ob) as t eqn:Ht.
  induction H; subst.
  - destruct E; simpl in Ht; try discriminate.
    subst. match goal with Hh : _ -->h _ |- _ => inversion Hh end.
  - destruct E; simpl in Ht; discriminate.
Qed.

Lemma no_step_resume : forall m b t',
  term_resume m b ==> t' -> False.
Proof.
  intros m b t' H. remember (term_resume m b) as t eqn:Ht.
  induction H; subst.
  - destruct E; simpl in Ht; try discriminate.
    subst. match goal with Hh : _ -->h _ |- _ => inversion Hh end.
  - destruct E; simpl in Ht; discriminate.
Qed.

Lemma Forall_value_focus : forall vs t ts,
  Forall value (vs ++ t :: ts) -> value t.
Proof.
  induction vs as [|v vs IH]; intros t ts H; simpl in H.
  - inversion H; subst. assumption.
  - inversion H; subst.
    match goal with
    | Hrest : Forall value (vs ++ t :: ts) |- _ => exact (IH t ts Hrest)
    end.
Qed.

Lemma plug_value_inv : forall E r,
  ectx_wf E ->
  value (plug E r) ->
  value r.
Proof.
  induction E; simpl; intros r Hwf Hv; auto.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv; subst.
    inversion Hwf; subst.
    apply IHE; auto.
    eapply Forall_value_focus; eauto.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
  - inversion Hv.
Qed.

Lemma head_step_not_value : forall r r',
  value r ->
  r -->h r' ->
  False.
Proof.
  intros r r' Hv Hh. inversion Hh; subst; inversion Hv.
Qed.

Lemma no_step_value : forall v t',
  value v ->
  v ==> t' ->
  False.
Proof.
  intros v t' Hv Hs. inversion Hs; subst.
  - eapply head_step_not_value; [|eauto].
    eapply plug_value_inv; eauto.
  - pose proof (plug_value_inv E (term_handle E_tag Ts op_body body) H Hv) as Hhandle.
    inversion Hhandle.
Qed.

(* App-shape inversion: an `term_app t1 t2` step is exactly one of
   - β-reduction (t1 a lambda, t2 a value);
   - resumption application (t1 = term_resume m b, t2 a value);
   - left-congruence (t1 stepped); or
   - right-congruence (t1 a value, t2 stepped).                         *)
Lemma step_app_inv : forall t1 t2 t',
  term_app t1 t2 ==> t' ->
    (exists body T v,
        t1 = term_lam body T /\ t2 = v /\ value v
        /\ t' = subst_tm 0 v body)
    \/ (exists m b v,
        t1 = term_resume m b /\ t2 = v /\ value v
        /\ t' = term_handler_m m (subst_tm 0 v b))
    \/ (exists t1', t1 ==> t1' /\ t' = term_app t1' t2)
    \/ (exists t2', value t1 /\ t2 ==> t2' /\ t' = term_app t1 t2').
Proof.
  intros t1 t2 t' H.
  inversion H as
    [E r r' Hwf Hh Heq Heq'
    | E Et Ts ob bd m Hwf Hfresh Heq Heq']; subst.
  - destruct E; simpl in Heq; try discriminate.
    + (* hole *) subst r. inversion Hh; subst.
      * (* H_Beta *)
        left. exists body, T, t2. repeat split; auto.
      * (* H_Resume *)
        right. left. exists m, b, t2. repeat split; auto.
    + (* EC_app1 *)
      inversion Heq; subst.
      inversion Hwf; subst.
      right. right. left. exists (plug E r').
      split; [apply (S_step E); auto | reflexivity].
    + (* EC_app2 *)
      inversion Heq; subst.
      inversion Hwf; subst.
      right. right. right. exists (plug E r').
      split; [auto | split; [apply (S_step E); auto | reflexivity]].
  - destruct E; simpl in Heq; try discriminate.
    + (* EC_app1 *)
      inversion Heq; subst. inversion Hwf; subst.
      right. right. left.
      exists (plug E (term_handler_m m (subst_tm 0 (term_cap Et m Ts ob) bd))).
      split.
      * apply (S_HandleCtx E Et Ts ob bd m); auto.
        intro Hin. apply Hfresh. simpl. rewrite List.in_app_iff. left. exact Hin.
      * reflexivity.
    + (* EC_app2 *)
      inversion Heq; subst. inversion Hwf; subst.
      right. right. right.
      exists (plug E (term_handler_m m (subst_tm 0 (term_cap Et m Ts ob) bd))).
      split; [auto | split; [|reflexivity]].
      apply (S_HandleCtx E Et Ts ob bd m); auto.
      intro Hin. apply Hfresh. simpl. rewrite List.in_app_iff. right. exact Hin.
Qed.

Lemma step_ty_app_inv : forall t T t',
  term_ty_app t T ==> t' ->
    (exists bound body, t = term_ty_lam bound body
        /\ t' = subst_ty_in_tm 0 T body)
    \/ (exists t'', t ==> t'' /\ t' = term_ty_app t'' T).
Proof.
  intros t T t' H.
  inversion H as
    [E r r' Hwf Hh Heq Heq'
    | E Et Ts ob bd m Hwf Hfresh Heq Heq']; subst.
  - destruct E; simpl in Heq; try discriminate.
    + subst r. inversion Hh; subst.
      left. exists bound, body. split; reflexivity.
    + inversion Heq; subst. inversion Hwf; subst.
      right. exists (plug E r').
      split; [apply (S_step E); auto | reflexivity].
  - destruct E; simpl in Heq; try discriminate.
    inversion Heq; subst. inversion Hwf; subst.
    right. exists (plug E (term_handler_m m (subst_tm 0 (term_cap Et m Ts ob) bd))).
    split.
    + apply (S_HandleCtx E Et Ts ob bd m); auto.
    + reflexivity.
Qed.

Lemma step_lt_app_inv : forall t l t',
  term_lt_app t l ==> t' ->
    (exists body, t = term_lt_lam body /\ t' = subst_lt_in_tm 0 l body)
    \/ (exists t'', t ==> t'' /\ t' = term_lt_app t'' l).
Proof.
  intros t l t' H.
  inversion H as
    [E r r' Hwf Hh Heq Heq'
    | E Et Ts ob bd m Hwf Hfresh Heq Heq']; subst.
  - destruct E; simpl in Heq; try discriminate.
    + subst r. inversion Hh; subst.
      left. exists body. split; reflexivity.
    + inversion Heq; subst. inversion Hwf; subst.
      right. exists (plug E r').
      split; [apply (S_step E); auto | reflexivity].
  - destruct E; simpl in Heq; try discriminate.
    inversion Heq; subst. inversion Hwf; subst.
    right. exists (plug E (term_handler_m m (subst_tm 0 (term_cap Et m Ts ob) bd))).
    split.
    + apply (S_HandleCtx E Et Ts ob bd m); auto.
    + reflexivity.
Qed.

Lemma step_ctor_inv : forall K l lts Ts ts t',
  term_ctor K l lts Ts ts ==> t' ->
    exists vs t t'' tsr,
      Forall value vs /\ ts = vs ++ t :: tsr /\ t ==> t''
      /\ t' = term_ctor K l lts Ts (vs ++ t'' :: tsr).
Proof.
  intros K l lts Ts ts t' H.
  inversion H as
    [E r r' Hwf Hh Heq Heq'
    | E Et TsH ob bd m Hwf Hfresh Heq Heq']; subst.
  - destruct E as [ | | | | | K0 l0 lts0 Ts0 vs E0 tsr | | | | ]; simpl in Heq.
    + (* EC_hole *) subst r. inversion Hh.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
    + (* EC_ctor *)
      inversion Heq; subst. inversion Hwf; subst.
      exists vs, (plug E0 r), (plug E0 r'), tsr. repeat split; auto.
    + discriminate.
    + discriminate.
    + discriminate.
    + discriminate.
  - destruct E as [ | | | | | K0 l0 lts0 Ts0 vs E0 tsr | | | | ]; simpl in Heq; try discriminate.
    inversion Heq; subst. inversion Hwf; subst.
    exists vs,
      (plug E0 (term_handle Et TsH ob bd)),
      (plug E0 (term_handler_m m (subst_tm 0 (term_cap Et m TsH ob) bd))),
      tsr.
    repeat split; auto.
    apply (S_HandleCtx E0 Et TsH ob bd m); auto.
    intro Hin. apply Hfresh.
      change (In m (markers_in
        (term_ctor K l lts Ts (vs ++ plug E0 (term_handle Et TsH ob bd) :: tsr)))).
      rewrite markers_in_ctor. apply markers_in_list_focus. exact Hin.
Qed.

Lemma step_match_inv : forall scrut tag n_lt ar y n t',
  term_match scrut tag n_lt ar y n ==> t' ->
    (exists K l lts Ts vs,
       scrut = term_ctor K l lts Ts vs
       /\ Forall value vs
       /\ ar = List.length vs
       /\ K = tag
       /\ t' = subst_list_tm vs (subst_list_lt_in_tm lts y))
    \/ (exists K' l lts Ts vs,
       scrut = term_ctor K' l lts Ts vs
       /\ Forall value vs
       /\ tag <> K'
       /\ t' = n)
    \/ (exists scrut',
       scrut ==> scrut'
       /\ t' = term_match scrut' tag n_lt ar y n).
Proof.
  intros scrut tag n_lt ar y n t' H.
  inversion H as
    [E r r' Hwf Hh Heq Heq'
    | E Et Ts ob bd m Hwf Hfresh Heq Heq']; subst.
  - destruct E as [ | | | | | | E0 K0 nlt0 ar0 y0 n0 | | | ]; simpl in Heq; try discriminate.
    + (* EC_hole *) subst r. inversion Hh; subst.
      * left. do 5 eexists. repeat split; eauto.
      * right. left. do 5 eexists. repeat split; eauto.
    + (* EC_match *)
      inversion Heq; subst. inversion Hwf; subst.
      right. right. exists (plug E0 r').
      split; [apply (S_step E0); auto | reflexivity].
  - destruct E as [ | | | | | | E0 K0 nlt0 ar0 y0 n0 | | | ]; simpl in Heq; try discriminate.
    inversion Heq; subst. inversion Hwf; subst.
    right. right.
    exists (plug E0 (term_handler_m m (subst_tm 0 (term_cap Et m Ts ob) bd))).
    split.
    + apply (S_HandleCtx E0 Et Ts ob bd m); auto.
      intro Hin. apply Hfresh. simpl. rewrite !List.in_app_iff. left. exact Hin.
    + reflexivity.
Qed.

(* Handler-marker delimiter inversion: a step on `term_handler_m m t` *)
(* is exactly one of                                                  *)
(*   - H_Return  (t already a value),                                 *)
(*   - inside-step under EC_handler_m, or                             *)
(*   - H_Perform on a matching cap inside a pure surrounding context. *)
Lemma step_handler_m_inv : forall m t t'',
  term_handler_m m t ==> t'' ->
    (value t /\ t'' = t)
    \/ (exists t', t ==> t' /\ t'' = term_handler_m m t')
    \/ (exists E_tag Ts op_body Ss v P,
          value v /\ pure_ectx_m m P /\
          t = plug P (term_perform (term_cap E_tag m Ts op_body) Ss v) /\
          t'' = subst_list_tm
                  [v;
                   term_resume m
                     (plug (shift_ectx_tm 1 0 P) (term_var 0))]
                  (subst_list_ty_in_tm Ss op_body)).
Proof.
  intros m t t'' H.
  inversion H as
    [E r r' Hwf Hh Heq Heq'
    | E Et Ts ob bd mh Hwf Hfresh Heq Heq']; subst.
  - destruct E; simpl in Heq; try discriminate.
    + (* EC_hole *) subst r. inversion Hh; subst.
      * (* H_Return *) left; split; auto.
      * (* H_Perform *)
        right. right.
        exists E_tag, Ts, op_body, Ss, v, P.
        repeat split; auto.
    + (* EC_handler_m m0 E0 *)
      inversion Heq; subst.
      inversion Hwf; subst.
      right. left. exists (plug E r').
      split; [apply (S_step E); auto | reflexivity].
  - destruct E; simpl in Heq; try discriminate.
    inversion Heq; subst. inversion Hwf; subst.
    right. left.
    exists (plug E (term_handler_m mh (subst_tm 0 (term_cap Et mh Ts ob) bd))).
    split.
    + apply (S_HandleCtx E Et Ts ob bd mh); auto.
      intro Hin. apply Hfresh. simpl. right. exact Hin.
    + reflexivity.
Qed.

(* Perform shape inversion. *)
Lemma step_perform_inv : forall t Ss arg t',
  term_perform t Ss arg ==> t' ->
    (exists t1', t ==> t1' /\ t' = term_perform t1' Ss arg)
    \/ (exists arg', value t /\ arg ==> arg' /\ t' = term_perform t Ss arg').
Proof.
  intros t Ss arg t' H.
  inversion H as
    [E r r' Hwf Hh Heq Heq'
    | E Et Ts ob bd m Hwf Hfresh Heq Heq']; subst.
  - destruct E; simpl in Heq; try discriminate.
    + (* EC_hole *) subst r. inversion Hh.
    + (* EC_perform_r *)
      inversion Heq; subst. inversion Hwf; subst.
      left. exists (plug E r'). split; [apply (S_step E); auto | reflexivity].
    + (* EC_perform_a *)
      inversion Heq; subst. inversion Hwf; subst.
      right. exists (plug E r').
      split; [auto |].
      split; [apply (S_step E); auto | reflexivity].
  - destruct E; simpl in Heq; try discriminate.
    + (* EC_perform_r *)
      inversion Heq; subst. inversion Hwf; subst.
      left. exists (plug E (term_handler_m m (subst_tm 0 (term_cap Et m Ts ob) bd))).
      split.
      * apply (S_HandleCtx E Et Ts ob bd m); auto.
        intro Hin. apply Hfresh. simpl. rewrite List.in_app_iff. left. exact Hin.
      * reflexivity.
    + (* EC_perform_a *)
      inversion Heq; subst. inversion Hwf; subst.
      right. exists (plug E (term_handler_m m (subst_tm 0 (term_cap Et m Ts ob) bd))).
      split; [auto | split; [|reflexivity]].
      apply (S_HandleCtx E Et Ts ob bd m); auto.
      intro Hin. apply Hfresh. simpl. rewrite List.in_app_iff. right. exact Hin.
Qed.

(* Handle steps by allocating a fresh marker at the step level. *)
Lemma step_handle_inv : forall E_tag Ts op_body body t',
  term_handle E_tag Ts op_body body ==> t' ->
  exists m, t' = term_handler_m m (subst_tm 0 (term_cap E_tag m Ts op_body) body).
Proof.
  intros Et Ts ob bd t' H.
  inversion H as
    [E r r' Hwf Hh Heq Heq'
    | E Et0 Ts0 ob0 bd0 m Hwf Hfresh Heq Heq']; subst.
  - destruct E; simpl in Heq; try discriminate.
    subst r. inversion Hh.
  - destruct E; simpl in Heq; try discriminate.
    inversion Heq; subst. exists m. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Tactic: close a typing branch when the head term is a value-shape   *)
(* (lambda, ty-lam, lt-lam, cap) or a variable, by appealing to the    *)
(* corresponding `no_step_*` lemma.                                    *)
(* ------------------------------------------------------------------ *)

Ltac no_step :=
  match goal with
  | H : term_var _       ==> _ |- _ => exfalso; eapply no_step_var; exact H
  | H : term_lam _ _     ==> _ |- _ => exfalso; eapply no_step_lam; exact H
  | H : term_ty_lam _ _  ==> _ |- _ => exfalso; eapply no_step_ty_lam; exact H
  | H : term_lt_lam _    ==> _ |- _ => exfalso; eapply no_step_lt_lam; exact H
  | H : term_cap _ _ _ _ ==> _ |- _ => exfalso; eapply no_step_cap; exact H
  | H : term_resume _ _  ==> _ |- _ => exfalso; eapply no_step_resume; exact H
  end.
