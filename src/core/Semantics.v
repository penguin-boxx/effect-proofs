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
(* are then derived as one-line lemmas over the single congruence     *)
(* lemma `step_in_ctx` (context composition `comp_ectx`).             *)
(*                                                                    *)
(* Marker discipline: `S_HandleCtx` allocates the delimiter marker    *)
(* for a reducing source `handle`, with a GLOBAL freshness side       *)
(* condition (`~ In m (markers_in <whole term>)`).  Proofs that need  *)
(* to exhibit a step pick the witness `marker_bound t` (one past the  *)
(* largest marker in t), fresh by `marker_bound_fresh`.               *)
(* ================================================================== *)

(* ------------------------------------------------------------------- *)
(* Evaluation contexts (defined first so head_step can reference plug, *)
(* pure_ectx_m and shift_ectx_tm in the H_Perform rule).               *)
(* ------------------------------------------------------------------- *)

Inductive ectx : Type :=
  | EC_hole       : ectx
  | EC_app1       : ectx -> term -> ectx
  | EC_app2       : term -> ectx -> ectx
  | EC_ty_app     : ectx -> type -> ectx
  | EC_lt_app     : ectx -> lifetime -> ectx
  | EC_ctor       : ctor_tag -> lifetime -> list lifetime -> list type ->
                    list term -> ectx -> list term -> ectx
  | EC_match      : ectx -> ctor_tag -> nat -> nat -> term -> term -> ectx
  | EC_handler_m  : marker -> type -> type -> ectx -> ectx
  | EC_perform_r  : ectx -> nat -> list type -> type -> term -> ectx
  | EC_perform_a  : term -> nat -> list type -> type -> ectx -> ectx.

Fixpoint plug (E : ectx) (t : term) : term :=
  match E with
  | EC_hole                       => t
  | EC_app1 E1 t2                 => term_app (plug E1 t) t2
  | EC_app2 v E2                  => term_app v (plug E2 t)
  | EC_ty_app E1 T                => term_ty_app (plug E1 t) T
  | EC_lt_app E1 l                => term_lt_app (plug E1 t) l
  | EC_ctor K l lts Ts vs E1 ts   => term_ctor K l lts Ts (vs ++ plug E1 t :: ts)
  | EC_match E1 K nlt ar y n      => term_match (plug E1 t) K nlt ar y n
  | EC_handler_m m T_B T_R E1     => term_handler_m m T_B T_R (plug E1 t)
  | EC_perform_r E1 op Ss A arg   => term_perform (plug E1 t) op Ss A arg
  | EC_perform_a v op Ss A E1     => term_perform v op Ss A (plug E1 t)
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
    | pem_handler_m : forall m' T_B T_R E,
      m <> m' ->
      pure_ectx_m m E -> pure_ectx_m m (EC_handler_m m' T_B T_R E)
  | pem_perform_r : forall E op Ss A arg,
      pure_ectx_m m E -> pure_ectx_m m (EC_perform_r E op Ss A arg)
  | pem_perform_a : forall v op Ss A E,
      pure_ectx_m m E -> pure_ectx_m m (EC_perform_a v op Ss A E).

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
  | EC_handler_m m T_B T_R E1   => EC_handler_m m T_B T_R (shift_ectx_tm amount cutoff E1)
  | EC_perform_r E1 op Ss A arg => EC_perform_r (shift_ectx_tm amount cutoff E1)
                                                 op Ss A
                                                 (shift_tm amount cutoff arg)
  | EC_perform_a v op Ss A E1   => EC_perform_a (shift_tm amount cutoff v)
                                                 op Ss A
                                                 (shift_ectx_tm amount cutoff E1)
  end.

(* Runtime markers occurring in a term.  This is used only to choose a *)
(* fresh delimiter marker when a source-level handle reduces.          *)
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
  | term_handle _ _ _ _ op_bodies body =>
      (fix go_ops (obs : list (nat * term)) : list marker :=
         match obs with
         | []              => []
         | (_, ob) :: rest => markers_in ob ++ go_ops rest
         end) op_bodies ++ markers_in body
  | term_perform recv _ _ _ arg => markers_in recv ++ markers_in arg
  | term_cap _ m _ _ op_bodies =>
      m :: (fix go_ops (obs : list (nat * term)) : list marker :=
              match obs with
              | []              => []
              | (_, ob) :: rest => markers_in ob ++ go_ops rest
              end) op_bodies
  | term_handler_m m _ _ body => m :: markers_in body
  end.

Fixpoint markers_in_list (ts : list term) : list marker :=
  match ts with
  | [] => []
  | u :: rest => markers_in u ++ markers_in_list rest
  end.


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


(* ------------------------------------------------------------------ *)
(* 1a. Evaluation context well-formedness                             *)
(* ------------------------------------------------------------------ *)

(* Well-formedness: arguments to the left of an evaluation hole must  *)
(* already be values (call-by-value, left-to-right).  Defined BEFORE  *)
(* head_step because H_Perform requires the captured context to be    *)
(* value-disciplined too: capture may not skip a pending redex.       *)
Inductive ectx_wf : ectx -> Prop :=
  | EWF_Hole       : ectx_wf EC_hole
  | EWF_App1       : forall E t,
      ectx_wf E -> ectx_wf (EC_app1 E t)
  | EWF_App2       : forall v E,
      value v -> ectx_wf E -> ectx_wf (EC_app2 v E)
  | EWF_TyApp     : forall E T,
      ectx_wf E -> ectx_wf (EC_ty_app E T)
  | EWF_LtApp     : forall E l,
      ectx_wf E -> ectx_wf (EC_lt_app E l)
  | EWF_Ctor       : forall K l lts Ts vs E ts,
      Forall value vs -> ectx_wf E ->
      ectx_wf (EC_ctor K l lts Ts vs E ts)
  | EWF_Match      : forall E K nlt ar y n,
      ectx_wf E -> ectx_wf (EC_match E K nlt ar y n)
    | EWF_HandlerM  : forall m T_B T_R E,
      ectx_wf E -> ectx_wf (EC_handler_m m T_B T_R E)
  | EWF_PerformR  : forall E op Ss A arg,
      ectx_wf E -> ectx_wf (EC_perform_r E op Ss A arg)
  | EWF_PerformA  : forall v op Ss A E,
      value v -> ectx_wf E ->
      ectx_wf (EC_perform_a v op Ss A E).

Hint Constructors ectx_wf : core.

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
    | H_Return : forall m T_B T_R v,
      value v ->
      term_handler_m m T_B T_R v -->h v

  (* (perform): a `perform (cap E_tag m Ts op_body) Ss A v` inside a  *)
  (* matching handler delimiter `term_handler_m m _` reduces by       *)
  (*   1) capturing the surrounding pure (delimiter-free) AND         *)
  (*      value-disciplined ectx P — `ectx_wf P` forbids capturing    *)
  (*      past a pending redex, which is what makes reduction         *)
  (*      deterministic modulo the fresh-marker choice;               *)
  (*   2) reifying the resumption as an ordinary lambda (annotated    *)
  (*      with the perform's instantiated result type A) whose body   *)
  (*      re-installs the delimiter around `plug P [hole]`;           *)
  (*   3) instantiating the op-body's β-type-binders with Ss, then    *)
  (*      substituting [arg, resumption] for its term-binders.        *)
  (* The shift on P accounts for the new term-binder introduced by    *)
  (* the resumption lambda.  Applying the resumption is ordinary      *)
  (* H_Beta: it substitutes the value into the delimited body.        *)
  | H_Perform : forall E_tag m Ts T_B T_R op_bodies op n_beta op_body Ss A v P,
      value v -> pure_ectx_m m P -> ectx_wf P ->
      nth_error op_bodies op = Some (n_beta, op_body) ->
      term_handler_m m T_B T_R
        (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v))
        -->h
          subst_list_tm
            [v; term_lam (term_handler_m m T_B T_R
                            (plug (shift_ectx_tm 1 0 P) (term_var 0))) A]
            (subst_list_ty_in_tm Ss
              op_body)

where "t '-->h' t'" := (head_step t t').

Hint Constructors head_step : core.


(* ------------------------------------------------------------------ *)
(* 3. Reduction = head step under any well-formed evaluation context  *)
(* ------------------------------------------------------------------ *)

Reserved Notation "t '==>' t'" (at level 40).

Inductive step : term -> term -> Prop :=
  | S_step : forall E r r',
      ectx_wf E ->
      r -->h r' ->
      plug E r ==> plug E r'
  | S_HandleCtx : forall E E_tag Ts T_B T_R op_bodies body m,
      ectx_wf E ->
      ~ In m (markers_in (plug E (term_handle E_tag Ts T_B T_R op_bodies body))) ->
      plug E (term_handle E_tag Ts T_B T_R op_bodies body)
        ==> plug E (term_handler_m m T_B T_R (subst_tm 0 (term_cap E_tag m Ts T_R op_bodies) body))
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

(* Context composition: `comp_ectx E1 E2` plugs E2 into E1's hole,    *)
(* so that `plug (comp_ectx E1 E2) u = plug E1 (plug E2 u)`.           *)
Fixpoint comp_ectx (E1 E2 : ectx) : ectx :=
  match E1 with
  | EC_hole                     => E2
  | EC_app1 E t                 => EC_app1 (comp_ectx E E2) t
  | EC_app2 v E                 => EC_app2 v (comp_ectx E E2)
  | EC_ty_app E T               => EC_ty_app (comp_ectx E E2) T
  | EC_lt_app E l               => EC_lt_app (comp_ectx E E2) l
  | EC_ctor K l lts Ts vs E ts  => EC_ctor K l lts Ts vs (comp_ectx E E2) ts
  | EC_match E K nlt ar y n     => EC_match (comp_ectx E E2) K nlt ar y n
  | EC_handler_m m T_B T_R E    => EC_handler_m m T_B T_R (comp_ectx E E2)
  | EC_perform_r E op Ss A arg  => EC_perform_r (comp_ectx E E2) op Ss A arg
  | EC_perform_a v op Ss A E    => EC_perform_a v op Ss A (comp_ectx E E2)
  end.

Lemma plug_comp_ectx : forall E1 E2 u,
  plug (comp_ectx E1 E2) u = plug E1 (plug E2 u).
Proof.
  intros E1 E2; induction E1; intros u; simpl; try rewrite IHE1; reflexivity.
Qed.

Lemma ectx_wf_comp : forall E1 E2,
  ectx_wf E1 -> ectx_wf E2 -> ectx_wf (comp_ectx E1 E2).
Proof.
  intros E1 E2 H1 H2; induction H1; simpl; try (constructor; auto); auto.
Qed.

(* The one congruence lemma behind every S_* structural rule below: a  *)
(* step inside a well-formed frame is a step of the whole term.  For   *)
(* the S_HandleCtx branch the fresh marker is re-chosen for the        *)
(* composed term via `marker_bound_fresh`.                             *)
Lemma step_in_ctx : forall F t,
  ectx_wf F ->
  (exists t', t ==> t') ->
  exists u, plug F t ==> u.
Proof.
  intros F t HF [t' Hstep]. inversion Hstep; subst.
  - exists (plug (comp_ectx F E) r').
    rewrite <- !plug_comp_ectx.
    apply S_step; [apply ectx_wf_comp; assumption | assumption].
  - eexists.
    rewrite <- !plug_comp_ectx.
    eapply (S_HandleCtx (comp_ectx F E));
      [apply ectx_wf_comp; assumption | apply marker_bound_fresh].
Qed.

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
Proof. intros t1 t2. apply (step_in_ctx (EC_app1 EC_hole t2)); auto. Qed.

Lemma S_App2 : forall v t2,
  value v ->
  (exists t2', t2 ==> t2') ->
  exists t', term_app v t2 ==> t'.
Proof. intros v t2 Hv. apply (step_in_ctx (EC_app2 v EC_hole)); auto. Qed.

Lemma S_TyApp : forall t T,
  (exists t', t ==> t') ->
  exists u, term_ty_app t T ==> u.
Proof. intros t T. apply (step_in_ctx (EC_ty_app EC_hole T)); auto. Qed.

Lemma S_LtApp : forall t l,
  (exists t', t ==> t') ->
  exists u, term_lt_app t l ==> u.
Proof. intros t l. apply (step_in_ctx (EC_lt_app EC_hole l)); auto. Qed.

Lemma S_Ctor : forall K l lts Ts vs t ts,
  Forall value vs ->
  (exists t', t ==> t') ->
  exists u, term_ctor K l lts Ts (vs ++ t :: ts) ==> u.
Proof.
  intros K l lts Ts vs t ts Hvs.
  apply (step_in_ctx (EC_ctor K l lts Ts vs EC_hole ts)); auto.
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
  intros s tag nlt ar y n.
  apply (step_in_ctx (EC_match EC_hole tag nlt ar y n)); auto.
Qed.

Lemma S_Handle : forall E_tag Ts T_B T_R op_bodies body m,
  ~ In m (markers_in (term_handle E_tag Ts T_B T_R op_bodies body)) ->
  term_handle E_tag Ts T_B T_R op_bodies body
    ==> term_handler_m m T_B T_R (subst_tm 0 (term_cap E_tag m Ts T_R op_bodies) body).
Proof.
  intros E_tag Ts T_B T_R op_bodies body m Hfresh.
  apply (S_HandleCtx EC_hole E_tag Ts T_B T_R op_bodies body m); [constructor | exact Hfresh].
Qed.

Lemma S_Return : forall m T_B T_R v,
  value v -> term_handler_m m T_B T_R v ==> v.
Proof. intros. apply (S_step EC_hole); auto. Qed.

Lemma S_HandlerM : forall m T_B T_R t,
  (exists t', t ==> t') ->
  exists u, term_handler_m m T_B T_R t ==> u.
Proof. intros m T_B T_R t. apply (step_in_ctx (EC_handler_m m T_B T_R EC_hole)); auto. Qed.

Lemma S_PerformRecv : forall t op Ss A arg,
  (exists t', t ==> t') ->
  exists u, term_perform t op Ss A arg ==> u.
Proof. intros t op Ss A arg. apply (step_in_ctx (EC_perform_r EC_hole op Ss A arg)); auto. Qed.

Lemma S_PerformArg : forall v op Ss A t,
  value v ->
  (exists t', t ==> t') ->
  exists u, term_perform v op Ss A t ==> u.
Proof. intros v op Ss A t Hv. apply (step_in_ctx (EC_perform_a v op Ss A EC_hole)); auto. Qed.

(* ------------------------------------------------------------------ *)
(* Reflexive-transitive closure of the step relation.                 *)
(* ------------------------------------------------------------------ *)

Inductive multi_step : term -> term -> Prop :=
  | MS_Refl : forall t, multi_step t t
  | MS_Step : forall t1 t2 t3,
      t1 ==> t2 -> multi_step t2 t3 -> multi_step t1 t3.

#[export] Hint Constructors pure_ectx_m ectx_wf head_step step multi_step : lang.
