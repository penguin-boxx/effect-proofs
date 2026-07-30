Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import ShiftLaws.
Require Import Weakening.
Require Import ProgramCtx.
Require Import SubstTm.
Require Import MarkerAnnots.
Require Import WellScoped.
Require Import WsRtLaws.
Require Import Stepf.

(* ================================================================== *)
(* Marker-renaming invariance (equivariance) and determinism modulo   *)
(* freshness.                                                         *)
(*                                                                    *)
(* S_HandleCtx (Semantics.v) allocates an ARBITRARY globally fresh    *)
(* delimiter marker, so the step relation is not literally            *)
(* deterministic.  This file shows the marker choice is semantically  *)
(* irrelevant:                                                        *)
(*                                                                    *)
(*   1. [rename_marker f t] renames the marker FIELDS of term_cap /   *)
(*      term_handler_m (and nothing else).  It commutes with          *)
(*      markers_in, shifts, substitutions and plug.                   *)
(*   2. Typing never inspects marker values:                          *)
(*      [typing_rename_markers].                                      *)
(*   3. Well-scopedness is equivariant under injective renamings:     *)
(*      [well_scoped_rename_markers].                                 *)
(*   4. Reduction is equivariant under injective renamings:           *)
(*      [step_rename_markers].                                        *)
(*   5. [marker_alpha_equiv] — equality up to a marker BIJECTION      *)
(*      (a renaming with an explicit two-sided inverse) — is a        *)
(*      genuine equivalence: [marker_alpha_equiv_refl] / [_sym] /     *)
(*      [_trans].                                                     *)
(*   6. The fresh-marker choice of S_HandleCtx is irrelevant up to    *)
(*      [marker_alpha_equiv]: [handle_choice_irrelevant].             *)
(*                                                                    *)
(* H_Perform additionally requires its captured context to be         *)
(* value-disciplined ([ectx_wf], Semantics.v), so the fresh-marker    *)
(* choice is the ONLY one-step nondeterminism in the semantics; the   *)
(* general determinism-modulo-markers statements are delivered in     *)
(* Determinism.v on top of this file's equivalence.                   *)
(* ================================================================== *)

(* Injectivity of a marker renaming.  All equivariance results below  *)
(* use GLOBAL injectivity: it is the cleanest hypothesis that makes   *)
(* [pure_ectx_m] (m <> m'), [scope_below] (first-occurrence scan) and *)
(* the S_HandleCtx freshness side condition transport.                *)
Definition marker_inj (f : marker -> marker) : Prop :=
  forall m1 m2, f m1 = f m2 -> m1 = m2.

(* ------------------------------------------------------------------ *)
(* The renaming traversal                                             *)
(* ------------------------------------------------------------------ *)

Fixpoint rename_marker (f : marker -> marker) (t : term) : term :=
  let fix go (ts : list term) : list term :=
    match ts with
    | [] => []
    | u :: rest => rename_marker f u :: go rest
    end
  in
  match t with
  | term_var x => term_var x
  | term_app t1 t2 => term_app (rename_marker f t1) (rename_marker f t2)
  | term_lam body T => term_lam (rename_marker f body) T
  | term_ty_app t1 T => term_ty_app (rename_marker f t1) T
  | term_ty_lam bound body => term_ty_lam bound (rename_marker f body)
  | term_lt_app t1 l => term_lt_app (rename_marker f t1) l
  | term_lt_lam body => term_lt_lam (rename_marker f body)
  | term_ctor K l lts Ts ts => term_ctor K l lts Ts (go ts)
  | term_match scrut K n_lt arity yes_body no_body =>
      term_match (rename_marker f scrut) K n_lt arity
                 (rename_marker f yes_body) (rename_marker f no_body)
  | term_handle E Ts T_B T_R op_bodies body =>
      term_handle E Ts T_B T_R
                  ((fix go_ops (obs : list (nat * term)) : list (nat * term) :=
                      match obs with
                      | [] => []
                      | (nb, ob) :: rest => (nb, rename_marker f ob) :: go_ops rest
                      end) op_bodies)
                  (rename_marker f body)
  | term_perform recv op Ss A arg =>
      term_perform (rename_marker f recv) op Ss A (rename_marker f arg)
  | term_cap E m Ts T_R op_bodies =>
      term_cap E (f m) Ts T_R
               ((fix go_ops (obs : list (nat * term)) : list (nat * term) :=
                   match obs with
                   | [] => []
                   | (nb, ob) :: rest => (nb, rename_marker f ob) :: go_ops rest
                   end) op_bodies)
  | term_handler_m m T_B T_R body =>
      term_handler_m (f m) T_B T_R (rename_marker f body)
  end.

Lemma rename_marker_go_eq_map : forall f ts,
  (fix go (ts : list term) : list term :=
     match ts with
     | [] => []
     | u :: rest => rename_marker f u :: go rest
     end) ts = List.map (rename_marker f) ts.
Proof. intros f ts; induction ts; simpl; congruence. Qed.

Lemma rename_marker_ctor_eq : forall f K l lts Ts ts,
  rename_marker f (term_ctor K l lts Ts ts)
    = term_ctor K l lts Ts (List.map (rename_marker f) ts).
Proof. intros. simpl. rewrite rename_marker_go_eq_map. reflexivity. Qed.

Lemma rename_marker_go_ops_eq_map : forall f obs,
  (fix go_ops (obs : list (nat * term)) : list (nat * term) :=
     match obs with
     | [] => []
     | (nb, ob) :: rest => (nb, rename_marker f ob) :: go_ops rest
     end) obs
  = List.map (fun p => (fst p, rename_marker f (snd p))) obs.
Proof. intros f obs; induction obs as [|[nb ob] rest IH]; simpl; congruence. Qed.

(* The ectx version of the traversal. *)
Fixpoint rename_ectx (f : marker -> marker) (E : ectx) : ectx :=
  match E with
  | EC_hole => EC_hole
  | EC_app1 E1 t2 => EC_app1 (rename_ectx f E1) (rename_marker f t2)
  | EC_app2 v E2 => EC_app2 (rename_marker f v) (rename_ectx f E2)
  | EC_ty_app E1 T => EC_ty_app (rename_ectx f E1) T
  | EC_lt_app E1 l => EC_lt_app (rename_ectx f E1) l
  | EC_ctor K l lts Ts vs E1 ts =>
      EC_ctor K l lts Ts (List.map (rename_marker f) vs)
              (rename_ectx f E1) (List.map (rename_marker f) ts)
  | EC_match E1 K nlt ar y n =>
      EC_match (rename_ectx f E1) K nlt ar
               (rename_marker f y) (rename_marker f n)
  | EC_handler_m m T_B T_R E1 =>
      EC_handler_m (f m) T_B T_R (rename_ectx f E1)
  | EC_perform_r E1 op Ss A arg =>
      EC_perform_r (rename_ectx f E1) op Ss A (rename_marker f arg)
  | EC_perform_a v op Ss A E1 =>
      EC_perform_a (rename_marker f v) op Ss A (rename_ectx f E1)
  end.

(* ------------------------------------------------------------------ *)
(* markers_in commutation                                             *)
(* ------------------------------------------------------------------ *)

Lemma markers_in_rename_marker : forall f t,
  markers_in (rename_marker f t) = List.map f (markers_in t).
Proof.
  intros f.
  apply (term_list_ind
    (fun t => markers_in (rename_marker f t) = List.map f (markers_in t))
    (fun ts => markers_in_list (List.map (rename_marker f) ts)
               = List.map f (markers_in_list ts))
    (fun obs =>
       List.concat (List.map (fun p => markers_in (snd p))
         (List.map (fun p => (fst p, rename_marker f (snd p))) obs))
       = List.map f (List.concat (List.map (fun p => markers_in (snd p)) obs)))).
  - intros n. reflexivity.
  - intros t1 t2 IH1 IH2. simpl. rewrite IH1, IH2, List.map_app. reflexivity.
  - intros body T IH. simpl. exact IH.
  - intros t T IH. simpl. exact IH.
  - intros bound body IH. simpl. exact IH.
  - intros t l IH. simpl. exact IH.
  - intros body IH. simpl. exact IH.
  - intros K l lts Ts ts IH. rewrite rename_marker_ctor_eq, !markers_in_ctor_eq.
    exact IH.
  - intros scrut tag n_lt arity yes no IHs IHy IHn. simpl.
    rewrite IHs, IHy, IHn, !List.map_app. reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb. simpl.
    rewrite rename_marker_go_ops_eq_map, !markers_in_go_ops_eq_concat.
    rewrite IHops, IHb, List.map_app. reflexivity.
  - intros recv op Ss A arg IHr IHa. simpl.
    rewrite IHr, IHa, List.map_app. reflexivity.
  - intros E m Ts T_R op_bodies IHops. simpl.
    rewrite rename_marker_go_ops_eq_map, !markers_in_go_ops_eq_concat.
    rewrite IHops. reflexivity.
  - intros m T_B T_R body IH. simpl. rewrite IH. reflexivity.
  - reflexivity.
  - intros t ts IHt IHts. simpl. rewrite IHt, IHts, List.map_app. reflexivity.
  - reflexivity.
  - intros nb ob obs IHob IHobs. simpl. rewrite IHob, IHobs, List.map_app. reflexivity.
Qed.

(* The membership form of the commutation. *)
Corollary in_markers_in_rename_marker : forall f t m',
  In m' (markers_in (rename_marker f t))
    <-> exists m, In m (markers_in t) /\ m' = f m.
Proof.
  intros f t m'. rewrite markers_in_rename_marker, in_map_iff.
  split; intros [m [H1 H2]]; exists m; auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Renaming does not disturb the term skeleton: the classifiers used  *)
(* by the typing rules (is_abs, has_rt_cap, free_tm_vars, capture_lt) *)
(* are all invariant.                                                 *)
(* ------------------------------------------------------------------ *)

Lemma is_abs_rename_marker : forall f t,
  is_abs (rename_marker f t) = is_abs t.
Proof. intros f t; destruct t; reflexivity. Qed.

Lemma has_rt_cap_rename_marker : forall f t,
  has_rt_cap (rename_marker f t) = has_rt_cap t.
Proof.
  intros f.
  apply (term_list_ind
    (fun t => has_rt_cap (rename_marker f t) = has_rt_cap t)
    (fun ts => has_rt_cap_list (List.map (rename_marker f) ts)
               = has_rt_cap_list ts)
    (fun obs =>
       existsb (fun p => has_rt_cap (snd p))
         (List.map (fun p => (fst p, rename_marker f (snd p))) obs)
       = existsb (fun p => has_rt_cap (snd p)) obs)).
  - intros n. reflexivity.
  - intros t1 t2 IH1 IH2. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH. simpl. exact IH.
  - intros t T IH. simpl. exact IH.
  - intros bound body IH. simpl. exact IH.
  - intros t l IH. simpl. exact IH.
  - intros body IH. simpl. exact IH.
  - intros K l lts Ts ts IH. rewrite rename_marker_ctor_eq, !has_rt_cap_ctor_eq.
    exact IH.
  - intros scrut tag n_lt arity yes no IHs IHy IHn. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb. simpl.
    rewrite rename_marker_go_ops_eq_map, !has_rt_cap_go_ops_eq.
    rewrite IHops, IHb. reflexivity.
  - intros recv op Ss A arg IHr IHa. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m Ts T_R op_bodies IHops. reflexivity.
  - intros m T_B T_R body IH. reflexivity.
  - reflexivity.
  - intros t ts IHt IHts. simpl. rewrite IHt, IHts. reflexivity.
  - reflexivity.
  - intros nb ob obs IHob IHobs. simpl. rewrite IHob, IHobs. reflexivity.
Qed.

Lemma free_tm_vars_rename_marker : forall f t cutoff,
  free_tm_vars cutoff (rename_marker f t) = free_tm_vars cutoff t.
Proof.
  intros f.
  apply (term_list_ind
    (fun t => forall cutoff,
       free_tm_vars cutoff (rename_marker f t) = free_tm_vars cutoff t)
    (fun ts => forall cutoff,
       List.concat (List.map (free_tm_vars cutoff)
                             (List.map (rename_marker f) ts))
       = List.concat (List.map (free_tm_vars cutoff) ts))
    (fun obs => forall cutoff,
       List.concat (List.map (fun p => free_tm_vars cutoff (snd p))
         (List.map (fun p => (fst p, rename_marker f (snd p))) obs))
       = List.concat (List.map (fun p => free_tm_vars cutoff (snd p)) obs))).
  - intros n cutoff. reflexivity.
  - intros t1 t2 IH1 IH2 cutoff. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH cutoff. simpl. apply IH.
  - intros t T IH cutoff. simpl. apply IH.
  - intros bound body IH cutoff. simpl. apply IH.
  - intros t l IH cutoff. simpl. apply IH.
  - intros body IH cutoff. simpl. apply IH.
  - intros K l lts Ts ts IH cutoff. simpl.
    rewrite rename_marker_go_eq_map, !free_tm_vars_go_eq_concat. apply IH.
  - intros scrut tag n_lt arity yes no IHs IHy IHn cutoff. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb cutoff. simpl.
    rewrite rename_marker_go_ops_eq_map, !free_tm_vars_go_ops_eq_concat.
    rewrite IHops, IHb. reflexivity.
  - intros recv op Ss A arg IHr IHa cutoff. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m Ts T_R op_bodies IHops cutoff. simpl.
    rewrite rename_marker_go_ops_eq_map, !free_tm_vars_go_ops_eq_concat.
    apply IHops.
  - intros m T_B T_R body IH cutoff. simpl. apply IH.
  - intros cutoff. reflexivity.
  - intros t ts IHt IHts cutoff. simpl. rewrite IHt, IHts. reflexivity.
  - intros cutoff. reflexivity.
  - intros nb ob obs IHob IHobs cutoff. simpl. rewrite IHob, IHobs. reflexivity.
Qed.

Lemma capture_lt_rename_marker : forall f G t,
  capture_lt G (rename_marker f t) = capture_lt G t.
Proof.
  intros f G t. unfold capture_lt.
  rewrite has_rt_cap_rename_marker, free_tm_vars_rename_marker. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Typing never inspects marker VALUES (T_Cap / T_HandlerM place no   *)
(* constraint on the m field), so typing is preserved by ANY marker   *)
(* renaming — injectivity is not needed here.                         *)
(* ------------------------------------------------------------------ *)

(* Proven by a guarded fix on the derivation (same pattern as          *)
(* typing_ind2's own proof) because typing_ind2 does not thread the    *)
(* is_abs premises of T_TyLam / T_LtLam, which the renamed term needs. *)
Theorem typing_rename_markers : forall f G t T,
  G ⊢ₜ t : T -> G ⊢ₜ rename_marker f t : T.
Proof.
  intros f. fix IH 4. intros G t T H. destruct H.
  - (* T_Var *) simpl. apply T_Var; assumption.
  - (* T_Sub *) eapply T_Sub; [apply IH; eassumption | assumption].
  - (* T_Lam *) simpl. apply T_Lam; try assumption.
    + apply IH. assumption.
    + rewrite capture_lt_rename_marker. assumption.
  - (* T_App *) simpl. eapply T_App; apply IH; eassumption.
  - (* T_TyLam *) simpl. apply T_TyLam; try assumption.
    + rewrite is_abs_rename_marker. assumption.
    + apply IH. assumption.
  - (* T_TyApp *) simpl. eapply T_TyApp; try eassumption.
    apply IH. eassumption.
  - (* T_LtLam *) simpl. apply T_LtLam; try assumption.
    + rewrite is_abs_rename_marker. assumption.
    + apply IH. assumption.
  - (* T_LtApp *) simpl. eapply T_LtApp; try eassumption.
    apply IH. eassumption.
  - (* T_Ctor *)
    rewrite rename_marker_ctor_eq.
    eapply T_Ctor; try eassumption.
    + rewrite List.length_map. assumption.
    + match goal with
      | HF : Forall2 (fun v rho => _ ⊢ₜ v : rho) ?vs ?rf |- Forall2 _ _ ?rf =>
          clear -IH HF; induction HF
      end.
      * constructor.
      * simpl. constructor; [apply IH; assumption | assumption].
  - (* T_Match *) simpl. eapply T_Match; try eassumption;
      apply IH; eassumption.
  - (* T_Cap *) simpl. rewrite rename_marker_go_ops_eq_map.
    eapply T_Cap; try eassumption.
    + match goal with HF : List.map fst _ = List.map op_nb _ |- _ =>
        rewrite List.map_map; exact HF end.
    + match goal with
      | HF : Forall2 _ ?obs ?ops |- Forall2 _ _ ?ops =>
          clear -IH HF; induction HF
      end.
      * constructor.
      * simpl. constructor; [apply IH; assumption | assumption].
  - (* T_Handle *) simpl. rewrite rename_marker_go_ops_eq_map.
    eapply T_Handle; try eassumption.
    + match goal with HF : List.map fst _ = List.map op_nb _ |- _ =>
        rewrite List.map_map; exact HF end.
    + match goal with
      | HF : Forall2 _ ?obs ?ops |- Forall2 _ _ ?ops =>
          clear -IH HF; induction HF
      end.
      * constructor.
      * simpl. constructor; [apply IH; assumption | assumption].
    + apply IH; assumption.
  - (* T_Perform *) simpl. eapply T_Perform; try eassumption;
      apply IH; eassumption.
  - (* T_HandlerM *) simpl. apply T_HandlerM; try assumption.
    apply IH. assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* well_scoped equivariance.                                          *)
(*                                                                    *)
(* [scope_below] scans for the FIRST occurrence of the cap's marker,  *)
(* so the renaming must be injective for the scan to commute.         *)
(* ------------------------------------------------------------------ *)

Lemma scope_below_map : forall f, marker_inj f ->
  forall m ms, scope_below (f m) (List.map f ms) = List.map f (scope_below m ms).
Proof.
  intros f Hinj m ms. induction ms as [|a rest IH]; simpl.
  - reflexivity.
  - destruct (Nat.eqb_spec a m) as [-> | Hne].
    + rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.eqb_spec (f a) (f m)) as [Heq | Hne'].
      * exfalso. apply Hne. apply Hinj. exact Heq.
      * exact IH.
Qed.

Theorem well_scoped_rename_markers : forall f, marker_inj f ->
  forall t ms, well_scoped ms t ->
  well_scoped (List.map f ms) (rename_marker f t).
Proof.
  intros f Hinj.
  apply (term_list_ind
    (fun t => forall ms, well_scoped ms t ->
       well_scoped (List.map f ms) (rename_marker f t))
    (fun ts => forall ms, well_scoped_list ms ts ->
       well_scoped_list (List.map f ms) (List.map (rename_marker f) ts))
    (fun obs => forall ms, ops_well_scoped ms obs ->
       ops_well_scoped (List.map f ms)
         (List.map (fun p => (fst p, rename_marker f (snd p))) obs))).
  - intros n ms _. exact I.
  - intros t1 t2 IH1 IH2 ms [H1 H2]. simpl.
    split; [apply IH1 | apply IH2]; assumption.
  - intros body T IH ms H. simpl. apply IH. exact H.
  - intros t T IH ms H. simpl. apply IH. exact H.
  - intros bound body IH ms H. simpl. apply IH. exact H.
  - intros t l IH ms H. simpl. apply IH. exact H.
  - intros body IH ms H. simpl. apply IH. exact H.
  - intros K l lts Ts ts IH ms H.
    rewrite rename_marker_ctor_eq, well_scoped_ctor_eq.
    apply IH. rewrite well_scoped_ctor_eq in H. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn ms [Hs [Hy Hn]]. simpl.
    split; [apply IHs; assumption
           | split; [apply IHy | apply IHn]; assumption].
  - intros E Ts T_B T_R op_bodies body IHops IHb ms [Hop Hb]. simpl.
    rewrite rename_marker_go_ops_eq_map.
    split; [apply IHops | apply IHb]; assumption.
  - intros recv op Ss A arg IHr IHa ms [Hr Ha]. simpl.
    split; [apply IHr | apply IHa]; assumption.
  - intros E m Ts T_R op_bodies IHops ms [Hm Hop]. simpl.
    rewrite rename_marker_go_ops_eq_map.
    split.
    + apply in_map. exact Hm.
    + rewrite scope_below_map by exact Hinj. apply IHops. exact Hop.
  - intros m T_B T_R body IH ms H. simpl.
    change (f m :: List.map f ms) with (List.map f (m :: ms)).
    apply IH. exact H.
  - intros ms _. exact I.
  - intros t ts IHt IHts ms [Ht Hts]. simpl.
    split; [apply IHt | apply IHts]; assumption.
  - intros ms _. exact I.
  - intros nb ob obs IHob IHobs ms [Hob Hobs]. simpl.
    split; [apply IHob; exact Hob | apply IHobs; exact Hobs].
Qed.

(* ------------------------------------------------------------------ *)
(* Commutation with shifts and substitutions.                         *)
(*                                                                    *)
(* rename_marker only rewrites the marker FIELDS of term_cap /        *)
(* term_handler_m; it never touches variables, types or lifetimes,    *)
(* so it commutes syntactically with the whole shift/subst matrix.    *)
(* ------------------------------------------------------------------ *)

Lemma rename_marker_shift_tm : forall f amount t cutoff,
  rename_marker f (shift_tm amount cutoff t)
    = shift_tm amount cutoff (rename_marker f t).
Proof.
  intros f amount.
  apply (term_list_ind
    (fun t => forall cutoff,
       rename_marker f (shift_tm amount cutoff t)
       = shift_tm amount cutoff (rename_marker f t))
    (fun ts => forall cutoff,
       List.map (rename_marker f) (List.map (shift_tm amount cutoff) ts)
       = List.map (shift_tm amount cutoff) (List.map (rename_marker f) ts))
    (fun obs => forall cutoff,
       List.map (fun p => (fst p, rename_marker f (snd p)))
         (List.map (fun p => (fst p, shift_tm amount cutoff (snd p))) obs)
       = List.map (fun p => (fst p, shift_tm amount cutoff (snd p)))
         (List.map (fun p => (fst p, rename_marker f (snd p))) obs))).
  - intros n cutoff. reflexivity.
  - intros t1 t2 IH1 IH2 cutoff. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH cutoff. simpl. rewrite IH. reflexivity.
  - intros t T IH cutoff. simpl. rewrite IH. reflexivity.
  - intros bound body IH cutoff. simpl. rewrite IH. reflexivity.
  - intros t l IH cutoff. simpl. rewrite IH. reflexivity.
  - intros body IH cutoff. simpl. rewrite IH. reflexivity.
  - intros K l lts Ts ts IH cutoff. simpl.
    rewrite !shift_tm_go_eq_map, !rename_marker_go_eq_map.
    rewrite IH. reflexivity.
  - intros scrut tag n_lt arity yes no IHs IHy IHn cutoff. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb cutoff. simpl.
    rewrite !shift_tm_go_ops_eq_map, !rename_marker_go_ops_eq_map.
    rewrite IHops, IHb. reflexivity.
  - intros recv op Ss A arg IHr IHa cutoff. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m Ts T_R op_bodies IHops cutoff. simpl.
    rewrite !shift_tm_go_ops_eq_map, !rename_marker_go_ops_eq_map.
    rewrite IHops. reflexivity.
  - intros m T_B T_R body IH cutoff. simpl. rewrite IH. reflexivity.
  - intros cutoff. reflexivity.
  - intros t ts IHt IHts cutoff. simpl. rewrite IHt, IHts. reflexivity.
  - intros cutoff. reflexivity.
  - intros nb ob obs IHob IHobs cutoff. simpl. rewrite IHob, IHobs. reflexivity.
Qed.

Lemma rename_marker_shift_ty_in_tm : forall f amount t cutoff,
  rename_marker f (shift_ty_in_tm amount cutoff t)
    = shift_ty_in_tm amount cutoff (rename_marker f t).
Proof.
  intros f amount.
  apply (term_list_ind
    (fun t => forall cutoff,
       rename_marker f (shift_ty_in_tm amount cutoff t)
       = shift_ty_in_tm amount cutoff (rename_marker f t))
    (fun ts => forall cutoff,
       List.map (rename_marker f) (List.map (shift_ty_in_tm amount cutoff) ts)
       = List.map (shift_ty_in_tm amount cutoff)
                  (List.map (rename_marker f) ts))
    (fun obs => forall cutoff,
       List.map (fun p => (fst p, rename_marker f (snd p)))
         (List.map (fun p => (fst p, shift_ty_in_tm amount (cutoff + fst p) (snd p))) obs)
       = List.map (fun p => (fst p, shift_ty_in_tm amount (cutoff + fst p) (snd p)))
         (List.map (fun p => (fst p, rename_marker f (snd p))) obs))).
  - intros n cutoff. reflexivity.
  - intros t1 t2 IH1 IH2 cutoff. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH cutoff. simpl. rewrite IH. reflexivity.
  - intros t T IH cutoff. simpl. rewrite IH. reflexivity.
  - intros bound body IH cutoff. simpl. rewrite IH. reflexivity.
  - intros t l IH cutoff. simpl. rewrite IH. reflexivity.
  - intros body IH cutoff. simpl. rewrite IH. reflexivity.
  - intros K l lts Ts ts IH cutoff. simpl.
    rewrite !shift_ty_in_tm_go_eq_map, !rename_marker_go_eq_map.
    rewrite IH. reflexivity.
  - intros scrut tag n_lt arity yes no IHs IHy IHn cutoff. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb cutoff. simpl.
    rewrite !shift_ty_in_tm_go_ops_eq_map, !rename_marker_go_ops_eq_map.
    rewrite IHops, IHb. reflexivity.
  - intros recv op Ss A arg IHr IHa cutoff. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m Ts T_R op_bodies IHops cutoff. simpl.
    rewrite !shift_ty_in_tm_go_ops_eq_map, !rename_marker_go_ops_eq_map.
    rewrite IHops. reflexivity.
  - intros m T_B T_R body IH cutoff. simpl. rewrite IH. reflexivity.
  - intros cutoff. reflexivity.
  - intros t ts IHt IHts cutoff. simpl. rewrite IHt, IHts. reflexivity.
  - intros cutoff. reflexivity.
  - intros nb ob obs IHob IHobs cutoff. simpl. rewrite IHob, IHobs. reflexivity.
Qed.

Lemma rename_marker_shift_lt_in_tm : forall f amount t cutoff,
  rename_marker f (shift_lt_in_tm amount cutoff t)
    = shift_lt_in_tm amount cutoff (rename_marker f t).
Proof.
  intros f amount.
  apply (term_list_ind
    (fun t => forall cutoff,
       rename_marker f (shift_lt_in_tm amount cutoff t)
       = shift_lt_in_tm amount cutoff (rename_marker f t))
    (fun ts => forall cutoff,
       List.map (rename_marker f) (List.map (shift_lt_in_tm amount cutoff) ts)
       = List.map (shift_lt_in_tm amount cutoff)
                  (List.map (rename_marker f) ts))
    (fun obs => forall cutoff,
       List.map (fun p => (fst p, rename_marker f (snd p)))
         (List.map (fun p => (fst p, shift_lt_in_tm amount cutoff (snd p))) obs)
       = List.map (fun p => (fst p, shift_lt_in_tm amount cutoff (snd p)))
         (List.map (fun p => (fst p, rename_marker f (snd p))) obs))).
  - intros n cutoff. reflexivity.
  - intros t1 t2 IH1 IH2 cutoff. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH cutoff. simpl. rewrite IH. reflexivity.
  - intros t T IH cutoff. simpl. rewrite IH. reflexivity.
  - intros bound body IH cutoff. simpl. rewrite IH. reflexivity.
  - intros t l IH cutoff. simpl. rewrite IH. reflexivity.
  - intros body IH cutoff. simpl. rewrite IH. reflexivity.
  - intros K l lts Ts ts IH cutoff. simpl.
    rewrite !shift_lt_in_tm_go_eq_map, !rename_marker_go_eq_map.
    rewrite IH. reflexivity.
  - intros scrut tag n_lt arity yes no IHs IHy IHn cutoff. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb cutoff. simpl.
    rewrite !shift_lt_in_tm_go_ops_eq_map, !rename_marker_go_ops_eq_map.
    rewrite IHops, IHb. reflexivity.
  - intros recv op Ss A arg IHr IHa cutoff. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m Ts T_R op_bodies IHops cutoff. simpl.
    rewrite !shift_lt_in_tm_go_ops_eq_map, !rename_marker_go_ops_eq_map.
    rewrite IHops. reflexivity.
  - intros m T_B T_R body IH cutoff. simpl. rewrite IH. reflexivity.
  - intros cutoff. reflexivity.
  - intros t ts IHt IHts cutoff. simpl. rewrite IHt, IHts. reflexivity.
  - intros cutoff. reflexivity.
  - intros nb ob obs IHob IHobs cutoff. simpl. rewrite IHob, IHobs. reflexivity.
Qed.

Lemma rename_marker_subst_tm : forall f t x s,
  rename_marker f (subst_tm x s t)
    = subst_tm x (rename_marker f s) (rename_marker f t).
Proof.
  intros f.
  apply (term_list_ind
    (fun t => forall x s,
       rename_marker f (subst_tm x s t)
       = subst_tm x (rename_marker f s) (rename_marker f t))
    (fun ts => forall x s,
       List.map (rename_marker f) (List.map (subst_tm x s) ts)
       = List.map (subst_tm x (rename_marker f s))
                  (List.map (rename_marker f) ts))
    (fun obs => forall x s,
       List.map (fun p => (fst p, rename_marker f (snd p)))
         (List.map (fun p => (fst p, subst_tm (x + 2) (shift_tm 2 0 s) (snd p))) obs)
       = List.map (fun p => (fst p, subst_tm (x + 2) (shift_tm 2 0 (rename_marker f s)) (snd p)))
         (List.map (fun p => (fst p, rename_marker f (snd p))) obs))).
  - intros n x s. simpl.
    destruct (Nat.eqb n x); [reflexivity|].
    destruct (Nat.ltb x n); reflexivity.
  - intros t1 t2 IH1 IH2 x s. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH x s. simpl.
    rewrite IH, rename_marker_shift_tm. reflexivity.
  - intros t T IH x s. simpl. rewrite IH. reflexivity.
  - intros bound body IH x s. simpl.
    rewrite IH, rename_marker_shift_ty_in_tm. reflexivity.
  - intros t l IH x s. simpl. rewrite IH. reflexivity.
  - intros body IH x s. simpl.
    rewrite IH, rename_marker_shift_lt_in_tm. reflexivity.
  - intros K l lts Ts ts IH x s. simpl.
    rewrite !subst_tm_go_eq_map, !rename_marker_go_eq_map.
    rewrite IH. reflexivity.
  - intros scrut tag n_lt arity yes no IHs IHy IHn x s. simpl.
    rewrite IHs, IHy, IHn,
            rename_marker_shift_tm, rename_marker_shift_lt_in_tm.
    reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb x s. simpl.
    rewrite !subst_tm_go_ops_eq_map, !rename_marker_go_ops_eq_map.
    rewrite IHops, IHb, !rename_marker_shift_tm. reflexivity.
  - intros recv op Ss A arg IHr IHa x s. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m Ts T_R op_bodies IHops x s. simpl.
    rewrite !subst_tm_go_ops_eq_map, !rename_marker_go_ops_eq_map.
    rewrite IHops. reflexivity.
  - intros m T_B T_R body IH x s. simpl. rewrite IH. reflexivity.
  - intros x s. reflexivity.
  - intros t ts IHt IHts x s. simpl. rewrite IHt, IHts. reflexivity.
  - intros x s. reflexivity.
  - intros nb ob obs IHob IHobs x s. simpl.
    rewrite IHob, IHobs, rename_marker_shift_tm. reflexivity.
Qed.

Lemma rename_marker_subst_ty_in_tm : forall f t x T,
  rename_marker f (subst_ty_in_tm x T t)
    = subst_ty_in_tm x T (rename_marker f t).
Proof.
  intros f.
  apply (term_list_ind
    (fun t => forall x T,
       rename_marker f (subst_ty_in_tm x T t)
       = subst_ty_in_tm x T (rename_marker f t))
    (fun ts => forall x T,
       List.map (rename_marker f) (List.map (subst_ty_in_tm x T) ts)
       = List.map (subst_ty_in_tm x T) (List.map (rename_marker f) ts))
    (fun obs => forall x T,
       List.map (fun p => (fst p, rename_marker f (snd p)))
         (List.map (fun p => (fst p, subst_ty_in_tm (x + fst p) (shift_ty (fst p) 0 T) (snd p))) obs)
       = List.map (fun p => (fst p, subst_ty_in_tm (x + fst p) (shift_ty (fst p) 0 T) (snd p)))
         (List.map (fun p => (fst p, rename_marker f (snd p))) obs))).
  - intros n x T. reflexivity.
  - intros t1 t2 IH1 IH2 x T. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T0 IH x T. simpl. rewrite IH. reflexivity.
  - intros t T0 IH x T. simpl. rewrite IH. reflexivity.
  - intros bound body IH x T. simpl. rewrite IH. reflexivity.
  - intros t l IH x T. simpl. rewrite IH. reflexivity.
  - intros body IH x T. simpl. rewrite IH. reflexivity.
  - intros K l lts Ts ts IH x T. simpl.
    rewrite !subst_ty_in_tm_go_eq_map, !rename_marker_go_eq_map.
    rewrite IH. reflexivity.
  - intros scrut tag n_lt arity yes no IHs IHy IHn x T. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb x T. simpl.
    rewrite !subst_ty_in_tm_go_ops_eq_map, !rename_marker_go_ops_eq_map.
    rewrite IHops, IHb. reflexivity.
  - intros recv op Ss A arg IHr IHa x T. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m Ts T_R op_bodies IHops x T. simpl.
    rewrite !subst_ty_in_tm_go_ops_eq_map, !rename_marker_go_ops_eq_map.
    rewrite IHops. reflexivity.
  - intros m T_B T_R body IH x T. simpl. rewrite IH. reflexivity.
  - intros x T. reflexivity.
  - intros t ts IHt IHts x T. simpl. rewrite IHt, IHts. reflexivity.
  - intros x T. reflexivity.
  - intros nb ob obs IHob IHobs x T. simpl. rewrite IHob, IHobs. reflexivity.
Qed.

Lemma rename_marker_subst_lt_in_tm : forall f t x l,
  rename_marker f (subst_lt_in_tm x l t)
    = subst_lt_in_tm x l (rename_marker f t).
Proof.
  intros f.
  apply (term_list_ind
    (fun t => forall x l,
       rename_marker f (subst_lt_in_tm x l t)
       = subst_lt_in_tm x l (rename_marker f t))
    (fun ts => forall x l,
       List.map (rename_marker f) (List.map (subst_lt_in_tm x l) ts)
       = List.map (subst_lt_in_tm x l) (List.map (rename_marker f) ts))
    (fun obs => forall x l,
       List.map (fun p => (fst p, rename_marker f (snd p)))
         (List.map (fun p => (fst p, subst_lt_in_tm x l (snd p))) obs)
       = List.map (fun p => (fst p, subst_lt_in_tm x l (snd p)))
         (List.map (fun p => (fst p, rename_marker f (snd p))) obs))).
  - intros n x l. reflexivity.
  - intros t1 t2 IH1 IH2 x l. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH x l. simpl. rewrite IH. reflexivity.
  - intros t T IH x l. simpl. rewrite IH. reflexivity.
  - intros bound body IH x l. simpl. rewrite IH. reflexivity.
  - intros t l0 IH x l. simpl. rewrite IH. reflexivity.
  - intros body IH x l. simpl. rewrite IH. reflexivity.
  - intros K l0 lts Ts ts IH x l. simpl.
    rewrite !subst_lt_in_tm_go_eq_map, !rename_marker_go_eq_map.
    rewrite IH. reflexivity.
  - intros scrut tag n_lt arity yes no IHs IHy IHn x l. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb x l. simpl.
    rewrite !subst_lt_in_tm_go_ops_eq_map, !rename_marker_go_ops_eq_map.
    rewrite IHops, IHb. reflexivity.
  - intros recv op Ss A arg IHr IHa x l. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m Ts T_R op_bodies IHops x l. simpl.
    rewrite !subst_lt_in_tm_go_ops_eq_map, !rename_marker_go_ops_eq_map.
    rewrite IHops. reflexivity.
  - intros m T_B T_R body IH x l. simpl. rewrite IH. reflexivity.
  - intros x l. reflexivity.
  - intros t ts IHt IHts x l. simpl. rewrite IHt, IHts. reflexivity.
  - intros x l. reflexivity.
  - intros nb ob obs IHob IHobs x l. simpl. rewrite IHob, IHobs. reflexivity.
Qed.

Lemma rename_marker_subst_list_tm : forall f vs t,
  rename_marker f (subst_list_tm vs t)
    = subst_list_tm (List.map (rename_marker f) vs) (rename_marker f t).
Proof.
  intros f. induction vs as [|v rest IH]; intros t; simpl.
  - reflexivity.
  - rewrite IH, rename_marker_subst_tm, rename_marker_shift_tm,
            List.length_map.
    reflexivity.
Qed.

Lemma rename_marker_subst_list_ty_in_tm : forall f Ss t,
  rename_marker f (subst_list_ty_in_tm Ss t)
    = subst_list_ty_in_tm Ss (rename_marker f t).
Proof.
  intros f. induction Ss as [|S0 rest IH]; intros t; simpl.
  - reflexivity.
  - rewrite IH, rename_marker_subst_ty_in_tm. reflexivity.
Qed.

Lemma rename_marker_subst_list_lt_in_tm : forall f lts t,
  rename_marker f (subst_list_lt_in_tm lts t)
    = subst_list_lt_in_tm lts (rename_marker f t).
Proof.
  intros f. induction lts as [|l rest IH]; intros t; simpl.
  - reflexivity.
  - rewrite IH, rename_marker_subst_lt_in_tm. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Commutation with plug / shift_ectx_tm; preservation of the         *)
(* context predicates.                                                *)
(* ------------------------------------------------------------------ *)

Lemma rename_marker_plug : forall f E t,
  rename_marker f (plug E t) = plug (rename_ectx f E) (rename_marker f t).
Proof.
  intros f E. induction E; intros u; simpl; try (rewrite IHE; reflexivity).
  - reflexivity.
  - (* EC_ctor *)
    rewrite rename_marker_go_eq_map, List.map_app. simpl.
    rewrite IHE. reflexivity.
Qed.

Lemma rename_ectx_shift_ectx_tm : forall f amount cutoff E,
  rename_ectx f (shift_ectx_tm amount cutoff E)
    = shift_ectx_tm amount cutoff (rename_ectx f E).
Proof.
  intros f amount cutoff E. revert cutoff.
  induction E; intros cutoff; simpl;
    rewrite ?IHE, ?rename_marker_shift_tm; try reflexivity.
  (* EC_ctor *)
  rewrite !List.map_map. f_equal.
  - apply List.map_ext. intros u. apply rename_marker_shift_tm.
  - apply List.map_ext. intros u. apply rename_marker_shift_tm.
Qed.

Lemma value_rename_marker : forall f t, value t -> value (rename_marker f t).
Proof.
  intros f.
  apply (term_list_ind
    (fun t => value t -> value (rename_marker f t))
    (fun ts => Forall value ts ->
               Forall value (List.map (rename_marker f) ts))
    (fun _ => True)).
  - intros n H; inversion H.
  - intros t1 t2 _ _ H; inversion H.
  - intros body T _ _; simpl; constructor.
  - intros t T _ H; inversion H.
  - intros bound body _ _; simpl; constructor.
  - intros t l _ H; inversion H.
  - intros body _ _; simpl; constructor.
  - intros K l lts Ts ts IH H. rewrite rename_marker_ctor_eq.
    inversion H; subst. constructor. apply IH. assumption.
  - intros scrut tag n_lt arity yes no _ _ _ H; inversion H.
  - intros E Ts T_B T_R op_bodies body _ _ H; inversion H.
  - intros recv op Ss A arg _ _ H; inversion H.
  - intros E m Ts T_R op_bodies _ _; simpl; constructor.
  - intros m T_B T_R body _ H; inversion H.
  - intros _; constructor.
  - intros t ts IHt IHts H. inversion H; subst. simpl.
    constructor; [apply IHt | apply IHts]; assumption.
  - exact I.
  - intros; exact I.
Qed.

Lemma Forall_value_rename_marker : forall f vs,
  Forall value vs -> Forall value (List.map (rename_marker f) vs).
Proof.
  intros f vs H. induction H; simpl; constructor;
    auto using value_rename_marker.
Qed.

Lemma ectx_wf_rename_ectx : forall f E,
  ectx_wf E -> ectx_wf (rename_ectx f E).
Proof.
  intros f E H. induction H; simpl; constructor;
    auto using value_rename_marker, Forall_value_rename_marker.
Qed.

Lemma pure_ectx_m_rename_ectx : forall f, marker_inj f ->
  forall m E, pure_ectx_m m E -> pure_ectx_m (f m) (rename_ectx f E).
Proof.
  intros f Hinj m E H. induction H; simpl; constructor; try assumption.
  (* EC_handler_m: m <> m' transports along injectivity *)
  intro Heq. apply H. apply Hinj. exact Heq.
Qed.

(* ------------------------------------------------------------------ *)
(* Equivariance of head reduction and of the full step relation.      *)
(* ------------------------------------------------------------------ *)

Theorem head_step_rename_markers : forall f, marker_inj f ->
  forall r r', r -->h r' -> rename_marker f r -->h rename_marker f r'.
Proof.
  intros f Hinj r r' Hstep. destruct Hstep.
  - (* H_Beta *)
    simpl. rewrite rename_marker_subst_tm.
    apply H_Beta. apply value_rename_marker. assumption.
  - (* H_TyBeta *)
    simpl. rewrite rename_marker_subst_ty_in_tm. apply H_TyBeta.
  - (* H_LtBeta *)
    simpl. rewrite rename_marker_subst_lt_in_tm. apply H_LtBeta.
  - (* H_MatchYes *)
    simpl. rewrite rename_marker_go_eq_map.
    rewrite rename_marker_subst_list_tm, rename_marker_subst_list_lt_in_tm.
    replace (List.length vs) with (List.length (List.map (rename_marker f) vs))
      by apply List.length_map.
    apply H_MatchYes. apply Forall_value_rename_marker. assumption.
  - (* H_MatchNo *)
    simpl. rewrite rename_marker_go_eq_map.
    apply H_MatchNo; [apply Forall_value_rename_marker|]; assumption.
  - (* H_Return *)
    simpl. apply H_Return. apply value_rename_marker. assumption.
  - (* H_Perform *)
    cbn [rename_marker].
    rewrite rename_marker_subst_list_tm.
    cbn [List.map rename_marker].
    rewrite !rename_marker_plug.
    cbn [rename_marker].
    rewrite rename_ectx_shift_ectx_tm.
    rewrite rename_marker_subst_list_ty_in_tm.
    rewrite rename_marker_go_ops_eq_map.
    eapply H_Perform.
    + apply value_rename_marker. assumption.
    + apply pure_ectx_m_rename_ectx; assumption.
    + apply ectx_wf_rename_ectx. assumption.
    + match goal with Hn : nth_error _ _ = Some _ |- _ =>
        rewrite (map_nth_error _ _ _ Hn); reflexivity end.
Qed.

Theorem step_rename_markers : forall f, marker_inj f ->
  forall t u, t ==> u -> rename_marker f t ==> rename_marker f u.
Proof.
  intros f Hinj t u Hstep. inversion Hstep; subst.
  - (* S_step *)
    rewrite !rename_marker_plug.
    apply S_step.
    + apply ectx_wf_rename_ectx. assumption.
    + apply head_step_rename_markers; assumption.
  - (* S_HandleCtx *)
    assert (Hfr : ~ In (f m)
      (markers_in (rename_marker f
        (plug E (term_handle E_tag Ts T_B T_R op_bodies body))))).
    { rewrite markers_in_rename_marker. intro Hin.
      apply in_map_iff in Hin. destruct Hin as [m' [Heqm Hin']].
      apply Hinj in Heqm. subst m'. contradiction. }
    rewrite rename_marker_plug in Hfr. simpl in Hfr.
    rewrite !rename_marker_plug. simpl.
    rewrite rename_marker_subst_tm. simpl.
    apply S_HandleCtx.
    + apply ectx_wf_rename_ectx. assumption.
    + exact Hfr.
Qed.

(* ================================================================== *)
(* Marker alpha-equivalence and determinism modulo                    *)
(* freshness.                                                         *)
(* ================================================================== *)

(* Two terms are equal modulo a marker BIJECTION: a renaming carrying *)
(* an explicit two-sided inverse.  Carrying the inverse (rather than  *)
(* bare injectivity) is what makes symmetry and transitivity          *)
(* provable, turning the relation into a genuine equivalence;         *)
(* injectivity — the hypothesis of the equivariance theorems above —  *)
(* is recovered by [marker_alpha_equiv_inj] below.                    *)
Definition marker_alpha_equiv (u1 u2 : term) : Prop :=
  exists f g,
    (forall m, g (f m) = m) /\
    (forall m, f (g m) = m) /\
    rename_marker f u1 = u2.

(* A renaming that fixes every marker occurring in t fixes t. *)
Lemma rename_marker_fixes : forall f t,
  (forall m, In m (markers_in t) -> f m = m) ->
  rename_marker f t = t.
Proof.
  intros f.
  apply (term_list_ind
    (fun t => (forall m, In m (markers_in t) -> f m = m) ->
              rename_marker f t = t)
    (fun ts => (forall m, In m (markers_in_list ts) -> f m = m) ->
               List.map (rename_marker f) ts = ts)
    (fun obs =>
       (forall m, In m (List.concat (List.map (fun p => markers_in (snd p)) obs)) -> f m = m) ->
       List.map (fun p => (fst p, rename_marker f (snd p))) obs = obs)).
  - intros n _. reflexivity.
  - intros t1 t2 IH1 IH2 Hf. simpl.
    rewrite IH1 by (intros m Hm; apply Hf; simpl; apply in_or_app; left;
                    exact Hm).
    rewrite IH2 by (intros m Hm; apply Hf; simpl; apply in_or_app; right;
                    exact Hm).
    reflexivity.
  - intros body T IH Hf. simpl. rewrite IH by exact Hf. reflexivity.
  - intros t T IH Hf. simpl. rewrite IH by exact Hf. reflexivity.
  - intros bound body IH Hf. simpl. rewrite IH by exact Hf. reflexivity.
  - intros t l IH Hf. simpl. rewrite IH by exact Hf. reflexivity.
  - intros body IH Hf. simpl. rewrite IH by exact Hf. reflexivity.
  - intros K l lts Ts ts IH Hf. rewrite rename_marker_ctor_eq.
    rewrite IH by (intros m Hm; apply Hf; rewrite markers_in_ctor_eq;
                   exact Hm).
    reflexivity.
  - intros scrut tag n_lt arity yes no IHs IHy IHn Hf. simpl.
    rewrite IHs by (intros m Hm; apply Hf; simpl; apply in_or_app; left;
                    exact Hm).
    rewrite IHy by (intros m Hm; apply Hf; simpl; apply in_or_app; right;
                    apply in_or_app; left; exact Hm).
    rewrite IHn by (intros m Hm; apply Hf; simpl; apply in_or_app; right;
                    apply in_or_app; right; exact Hm).
    reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb Hf. simpl.
    rewrite rename_marker_go_ops_eq_map.
    rewrite IHops by (intros m Hm; apply Hf; simpl;
                      rewrite markers_in_go_ops_eq_concat;
                      apply in_or_app; left; exact Hm).
    rewrite IHb by (intros m Hm; apply Hf; simpl;
                    rewrite markers_in_go_ops_eq_concat;
                    apply in_or_app; right; exact Hm).
    reflexivity.
  - intros recv op Ss A arg IHr IHa Hf. simpl.
    rewrite IHr by (intros m Hm; apply Hf; simpl; apply in_or_app; left;
                    exact Hm).
    rewrite IHa by (intros m Hm; apply Hf; simpl; apply in_or_app; right;
                    exact Hm).
    reflexivity.
  - intros E m0 Ts T_R op_bodies IHops Hf. simpl.
    rewrite rename_marker_go_ops_eq_map.
    rewrite IHops by (intros m Hm; apply Hf; simpl; right;
                      rewrite markers_in_go_ops_eq_concat; exact Hm).
    rewrite (Hf m0) by (simpl; left; reflexivity).
    reflexivity.
  - intros m0 T_B T_R body IH Hf. simpl.
    rewrite IH by (intros m Hm; apply Hf; simpl; right; exact Hm).
    rewrite (Hf m0) by (simpl; left; reflexivity).
    reflexivity.
  - intros _. reflexivity.
  - intros t ts IHt IHts Hf. simpl.
    rewrite IHt by (intros m Hm; apply Hf; simpl; apply in_or_app; left;
                    exact Hm).
    rewrite IHts by (intros m Hm; apply Hf; simpl; apply in_or_app; right;
                     exact Hm).
    reflexivity.
  - intros _. reflexivity.
  - intros nb ob obs IHob IHobs Hf. simpl.
    rewrite IHob by (intros m Hm; apply Hf; simpl; apply in_or_app; left;
                     exact Hm).
    rewrite IHobs by (intros m Hm; apply Hf; simpl; apply in_or_app; right;
                      exact Hm).
    reflexivity.
Qed.

Lemma rename_marker_id : forall t, rename_marker (fun m => m) t = t.
Proof.
  intros t. apply rename_marker_fixes. intros m _. reflexivity.
Qed.

(* Two renamings in a row fuse into their composition. *)
Lemma rename_marker_compose : forall f g t,
  rename_marker f (rename_marker g t) = rename_marker (fun m => f (g m)) t.
Proof.
  intros f g.
  apply (term_list_ind
    (fun t => rename_marker f (rename_marker g t)
              = rename_marker (fun m => f (g m)) t)
    (fun ts => List.map (rename_marker f) (List.map (rename_marker g) ts)
               = List.map (rename_marker (fun m => f (g m))) ts)
    (fun obs =>
       List.map (fun p => (fst p, rename_marker f (snd p)))
         (List.map (fun p => (fst p, rename_marker g (snd p))) obs)
       = List.map (fun p => (fst p, rename_marker (fun m => f (g m)) (snd p))) obs)).
  - intros n. reflexivity.
  - intros t1 t2 IH1 IH2. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH. simpl. rewrite IH. reflexivity.
  - intros t T IH. simpl. rewrite IH. reflexivity.
  - intros bound body IH. simpl. rewrite IH. reflexivity.
  - intros t l IH. simpl. rewrite IH. reflexivity.
  - intros body IH. simpl. rewrite IH. reflexivity.
  - intros K l lts Ts ts IH. rewrite !rename_marker_ctor_eq, IH. reflexivity.
  - intros scrut tag n_lt arity yes no IHs IHy IHn. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb. simpl.
    rewrite !rename_marker_go_ops_eq_map, IHops, IHb. reflexivity.
  - intros recv op Ss A arg IHr IHa. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m Ts T_R op_bodies IHops. simpl.
    rewrite !rename_marker_go_ops_eq_map, IHops. reflexivity.
  - intros m T_B T_R body IH. simpl. rewrite IH. reflexivity.
  - reflexivity.
  - intros t ts IHt IHts. simpl. rewrite IHt, IHts. reflexivity.
  - reflexivity.
  - intros nb ob obs IHob IHobs. simpl. rewrite IHob, IHobs. reflexivity.
Qed.

(* A left inverse forces injectivity: the bridge from the bijection   *)
(* form of [marker_alpha_equiv] back to the [marker_inj] hypotheses   *)
(* of the equivariance theorems above.                                *)
Lemma marker_left_inverse_inj : forall f g,
  (forall m, g (f m) = m) -> marker_inj f.
Proof.
  intros f g Hgf m1 m2 Heq.
  rewrite <- (Hgf m1), <- (Hgf m2), Heq. reflexivity.
Qed.

Lemma marker_alpha_equiv_inj : forall u1 u2,
  marker_alpha_equiv u1 u2 ->
  exists f, marker_inj f /\ rename_marker f u1 = u2.
Proof.
  intros u1 u2 (f & g & Hgf & _ & Heq).
  exists f. split; [exact (marker_left_inverse_inj f g Hgf) | exact Heq].
Qed.

(* ------------------------------------------------------------------ *)
(* [marker_alpha_equiv] is an equivalence relation.                   *)
(* ------------------------------------------------------------------ *)

Theorem marker_alpha_equiv_refl : forall t, marker_alpha_equiv t t.
Proof.
  intros t. exists (fun m => m), (fun m => m).
  split; [intros m; reflexivity|].
  split; [intros m; reflexivity|].
  apply rename_marker_id.
Qed.

Theorem marker_alpha_equiv_sym : forall u1 u2,
  marker_alpha_equiv u1 u2 -> marker_alpha_equiv u2 u1.
Proof.
  intros u1 u2 (f & g & Hgf & Hfg & Heq).
  exists g, f.
  split; [exact Hfg|]. split; [exact Hgf|].
  subst u2. rewrite rename_marker_compose.
  apply rename_marker_fixes. intros m _. apply Hgf.
Qed.

Theorem marker_alpha_equiv_trans : forall u1 u2 u3,
  marker_alpha_equiv u1 u2 -> marker_alpha_equiv u2 u3 ->
  marker_alpha_equiv u1 u3.
Proof.
  intros u1 u2 u3 (f1 & g1 & Hgf1 & Hfg1 & Heq1) (f2 & g2 & Hgf2 & Hfg2 & Heq2).
  exists (fun m => f2 (f1 m)), (fun m => g1 (g2 m)).
  split; [intros m; rewrite Hgf2; apply Hgf1|].
  split; [intros m; rewrite Hfg1; apply Hfg2|].
  subst. symmetry. apply rename_marker_compose.
Qed.

(* ------------------------------------------------------------------ *)
(* Markers of an evaluation context; the components of a plug embed   *)
(* into the markers of the whole.                                     *)
(* ------------------------------------------------------------------ *)

Lemma markers_in_list_app : forall xs ys,
  markers_in_list (xs ++ ys) = markers_in_list xs ++ markers_in_list ys.
Proof.
  induction xs as [|x xs IH]; intros ys; simpl.
  - reflexivity.
  - rewrite IH, app_assoc. reflexivity.
Qed.

Fixpoint markers_in_ectx (E : ectx) : list marker :=
  match E with
  | EC_hole => []
  | EC_app1 E1 t2 => markers_in_ectx E1 ++ markers_in t2
  | EC_app2 v E2 => markers_in v ++ markers_in_ectx E2
  | EC_ty_app E1 _ => markers_in_ectx E1
  | EC_lt_app E1 _ => markers_in_ectx E1
  | EC_ctor _ _ _ _ vs E1 ts =>
      markers_in_list vs ++ markers_in_ectx E1 ++ markers_in_list ts
  | EC_match E1 _ _ _ y n =>
      markers_in_ectx E1 ++ markers_in y ++ markers_in n
  | EC_handler_m m _ _ E1 => m :: markers_in_ectx E1
  | EC_perform_r E1 _ _ _ arg => markers_in_ectx E1 ++ markers_in arg
  | EC_perform_a v _ _ _ E1 => markers_in v ++ markers_in_ectx E1
  end.

Lemma markers_in_plug_ectx_incl : forall E t m,
  In m (markers_in_ectx E) -> In m (markers_in (plug E t)).
Proof.
  induction E; intros u m0 Hm.
  - simpl in Hm. contradiction.
  - simpl in *. apply in_app_or in Hm. apply in_or_app.
    destruct Hm as [Hm | Hm]; [left; apply IHE; exact Hm | right; exact Hm].
  - simpl in *. apply in_app_or in Hm. apply in_or_app.
    destruct Hm as [Hm | Hm]; [left; exact Hm | right; apply IHE; exact Hm].
  - simpl in *. apply IHE. exact Hm.
  - simpl in *. apply IHE. exact Hm.
  - (* EC_ctor *)
    simpl in Hm. cbn [plug].
    rewrite markers_in_ctor_eq, markers_in_list_app. simpl.
    rewrite !in_app_iff. rewrite !in_app_iff in Hm.
    destruct Hm as [Hm | [Hm | Hm]];
      [left; exact Hm | right; left; apply IHE; exact Hm
      | right; right; exact Hm].
  - simpl in *. rewrite !in_app_iff. rewrite !in_app_iff in Hm.
    destruct Hm as [Hm | [Hm | Hm]];
      [left; apply IHE; exact Hm | right; left; exact Hm
      | right; right; exact Hm].
  - simpl in *.
    destruct Hm as [Hm | Hm]; [left; exact Hm | right; apply IHE; exact Hm].
  - simpl in *. apply in_app_or in Hm. apply in_or_app.
    destruct Hm as [Hm | Hm]; [left; apply IHE; exact Hm | right; exact Hm].
  - simpl in *. apply in_app_or in Hm. apply in_or_app.
    destruct Hm as [Hm | Hm]; [left; exact Hm | right; apply IHE; exact Hm].
Qed.

Lemma markers_in_plug_hole_incl : forall E t m,
  In m (markers_in t) -> In m (markers_in (plug E t)).
Proof.
  induction E; intros u m0 Hm.
  - exact Hm.
  - simpl. apply in_or_app. left. apply IHE. exact Hm.
  - simpl. apply in_or_app. right. apply IHE. exact Hm.
  - simpl. apply IHE. exact Hm.
  - simpl. apply IHE. exact Hm.
  - cbn [plug]. rewrite markers_in_ctor_eq, markers_in_list_app. simpl.
    rewrite !in_app_iff. right. left. apply IHE. exact Hm.
  - simpl. apply in_or_app. left. apply IHE. exact Hm.
  - simpl. right. apply IHE. exact Hm.
  - simpl. apply in_or_app. left. apply IHE. exact Hm.
  - simpl. apply in_or_app. right. apply IHE. exact Hm.
Qed.

Lemma rename_marker_list_fixes : forall f ts,
  (forall m, In m (markers_in_list ts) -> f m = m) ->
  List.map (rename_marker f) ts = ts.
Proof.
  intros f. induction ts as [|t ts IH]; intros Hf; simpl.
  - reflexivity.
  - rewrite rename_marker_fixes
      by (intros m Hm; apply Hf; simpl; apply in_or_app; left; exact Hm).
    rewrite IH
      by (intros m Hm; apply Hf; simpl; apply in_or_app; right; exact Hm).
    reflexivity.
Qed.

Lemma rename_ectx_fixes : forall f E,
  (forall m, In m (markers_in_ectx E) -> f m = m) ->
  rename_ectx f E = E.
Proof.
  intros f. induction E; intros Hf; simpl.
  - reflexivity.
  - f_equal.
    + apply IHE. intros m Hm. apply Hf. simpl. apply in_or_app. left.
      exact Hm.
    + apply rename_marker_fixes. intros m Hm. apply Hf. simpl.
      apply in_or_app. right. exact Hm.
  - f_equal.
    + apply rename_marker_fixes. intros m Hm. apply Hf. simpl.
      apply in_or_app. left. exact Hm.
    + apply IHE. intros m Hm. apply Hf. simpl. apply in_or_app. right.
      exact Hm.
  - f_equal. apply IHE. exact Hf.
  - f_equal. apply IHE. exact Hf.
  - (* EC_ctor *)
    f_equal.
    + apply rename_marker_list_fixes. intros m Hm. apply Hf. simpl.
      rewrite !in_app_iff. left. exact Hm.
    + apply IHE. intros m Hm. apply Hf. simpl.
      rewrite !in_app_iff. right. left. exact Hm.
    + apply rename_marker_list_fixes. intros m Hm. apply Hf. simpl.
      rewrite !in_app_iff. right. right. exact Hm.
  - f_equal.
    + apply IHE. intros m Hm. apply Hf. simpl.
      rewrite !in_app_iff. left. exact Hm.
    + apply rename_marker_fixes. intros m Hm. apply Hf. simpl.
      rewrite !in_app_iff. right. left. exact Hm.
    + apply rename_marker_fixes. intros m Hm. apply Hf. simpl.
      rewrite !in_app_iff. right. right. exact Hm.
  - f_equal.
    + apply Hf. simpl. left. reflexivity.
    + apply IHE. intros m0 Hm. apply Hf. simpl. right. exact Hm.
  - f_equal.
    + apply IHE. intros m Hm. apply Hf. simpl. apply in_or_app. left.
      exact Hm.
    + apply rename_marker_fixes. intros m Hm. apply Hf. simpl.
      apply in_or_app. right. exact Hm.
  - f_equal.
    + apply rename_marker_fixes. intros m Hm. apply Hf. simpl.
      apply in_or_app. left. exact Hm.
    + apply IHE. intros m Hm. apply Hf. simpl. apply in_or_app. right.
      exact Hm.
Qed.

(* ------------------------------------------------------------------ *)
(* Transpositions: the injective renaming used to align two fresh     *)
(* marker choices.                                                    *)
(* ------------------------------------------------------------------ *)

Definition marker_swap (m1 m2 : marker) (x : marker) : marker :=
  if Nat.eqb x m1 then m2 else if Nat.eqb x m2 then m1 else x.

Lemma marker_swap_l : forall m1 m2, marker_swap m1 m2 m1 = m2.
Proof.
  intros m1 m2. unfold marker_swap. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma marker_swap_other : forall m1 m2 x,
  x <> m1 -> x <> m2 -> marker_swap m1 m2 x = x.
Proof.
  intros m1 m2 x H1 H2. unfold marker_swap.
  rewrite (proj2 (Nat.eqb_neq x m1) H1), (proj2 (Nat.eqb_neq x m2) H2).
  reflexivity.
Qed.

Lemma marker_swap_r : forall m1 m2, marker_swap m1 m2 m2 = m1.
Proof.
  intros m1 m2. unfold marker_swap.
  destruct (Nat.eqb_spec m2 m1) as [-> | Hne].
  - reflexivity.
  - rewrite Nat.eqb_refl. reflexivity.
Qed.

(* Transpositions are their own inverse — so the bijection form of    *)
(* [marker_alpha_equiv] costs nothing for the freshness argument.     *)
Lemma marker_swap_invol : forall m1 m2 x,
  marker_swap m1 m2 (marker_swap m1 m2 x) = x.
Proof.
  intros m1 m2 x.
  destruct (Nat.eqb_spec x m1) as [-> | Hx1].
  - rewrite marker_swap_l. apply marker_swap_r.
  - destruct (Nat.eqb_spec x m2) as [-> | Hx2].
    + rewrite marker_swap_r. apply marker_swap_l.
    + rewrite !(marker_swap_other m1 m2 x Hx1 Hx2). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* THE determinism-modulo-freshness result: the two S_HandleCtx       *)
(* reducts of the SAME handle redex in the SAME context under two     *)
(* different fresh markers are marker-alpha-equivalent (via the       *)
(* transposition m1 <-> m2, which fixes everything else because both  *)
(* markers are globally fresh).                                       *)
(* ------------------------------------------------------------------ *)

Lemma rename_marker_ops_fixes : forall f (obs : list (nat * term)),
  (forall m, In m (List.concat (List.map (fun p => markers_in (snd p)) obs)) -> f m = m) ->
  List.map (fun p => (fst p, rename_marker f (snd p))) obs = obs.
Proof.
  intros f obs Hf. induction obs as [|[nb ob] obs IH]; simpl; [reflexivity|].
  rewrite rename_marker_fixes
    by (intros m Hm; apply Hf; simpl; apply in_or_app; left; exact Hm).
  rewrite IH by (intros m Hm; apply Hf; simpl; apply in_or_app; right; exact Hm).
  reflexivity.
Qed.

Theorem handle_choice_irrelevant :
  forall E E_tag Ts T_B T_R op_bodies body m1 m2,
    ~ In m1 (markers_in
        (plug E (term_handle E_tag Ts T_B T_R op_bodies body))) ->
    ~ In m2 (markers_in
        (plug E (term_handle E_tag Ts T_B T_R op_bodies body))) ->
    marker_alpha_equiv
      (plug E (term_handler_m m1 T_B T_R
                 (subst_tm 0 (term_cap E_tag m1 Ts T_R op_bodies) body)))
      (plug E (term_handler_m m2 T_B T_R
                 (subst_tm 0 (term_cap E_tag m2 Ts T_R op_bodies) body))).
Proof.
  intros E E_tag Ts T_B T_R op_bodies body m1 m2 Hf1 Hf2.
  assert (Hfix : forall m,
    In m (markers_in (plug E (term_handle E_tag Ts T_B T_R op_bodies body))) ->
    marker_swap m1 m2 m = m).
  { intros m Hm. apply marker_swap_other; intro Heq; subst m;
      [exact (Hf1 Hm) | exact (Hf2 Hm)]. }
  exists (marker_swap m1 m2), (marker_swap m1 m2).
  split; [exact (marker_swap_invol m1 m2)|].
  split; [exact (marker_swap_invol m1 m2)|].
  rewrite rename_marker_plug.
  rewrite rename_ectx_fixes
    by (intros m Hm; apply Hfix; apply markers_in_plug_ectx_incl; exact Hm).
  cbn [rename_marker].
  rewrite rename_marker_subst_tm.
  cbn [rename_marker].
  rewrite marker_swap_l.
  rewrite rename_marker_go_ops_eq_map.
  rewrite (rename_marker_ops_fixes (marker_swap m1 m2) op_bodies)
    by (intros m Hm; apply Hfix; apply markers_in_plug_hole_incl; simpl;
        rewrite markers_in_go_ops_eq_concat;
        apply in_or_app; left; exact Hm).
  rewrite (rename_marker_fixes (marker_swap m1 m2) body)
    by (intros m Hm; apply Hfix; apply markers_in_plug_hole_incl; simpl;
        rewrite markers_in_go_ops_eq_concat;
        apply in_or_app; right; exact Hm).
  reflexivity.
Qed.

(* ================================================================== *)
(* DETERMINISM MODULO MARKERS.                                        *)
(*                                                                    *)
(* H_Perform requires the captured context to be BOTH marker-pure     *)
(* ([pure_ectx_m]) and value-disciplined ([ectx_wf]): capture may     *)
(* not skip a pending redex.  Under that rule the only one-step       *)
(* nondeterminism left in the semantics is S_HandleCtx's choice of    *)
(* fresh marker, which [handle_choice_irrelevant] above shows to be   *)
(* irrelevant up to [marker_alpha_equiv].  The general statements     *)
(*   step_deterministic_modulo_markers                                *)
(*   stepf_complete_modulo_markers                                    *)
(* are proved in Determinism.v.                                       *)
(* ================================================================== *)
