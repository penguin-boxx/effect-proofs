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
Require Import Markers.
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
(*   5. The fresh-marker choice of S_HandleCtx is irrelevant up to    *)
(*      [marker_alpha_equiv]: [handle_choice_irrelevant].             *)
(*                                                                    *)
(* The GENERAL statement "step is deterministic modulo markers" is    *)
(* FALSE, for a reason unrelated to markers: H_Perform's captured     *)
(* context [pure_ectx_m] imposes no left-to-right value discipline,   *)
(* so a perform can fire past an unevaluated redex that the           *)
(* congruence rules could also reduce.  See                           *)
(* [step_not_deterministic_modulo_markers] /                          *)
(* [head_step_not_deterministic] /                                    *)
(* [stepf_not_complete_modulo_markers] at the end of this file.       *)
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
  | term_handle E n_beta Ts T_B T_R op_body body =>
      term_handle E n_beta Ts T_B T_R
                  (rename_marker f op_body) (rename_marker f body)
  | term_perform recv Ss A arg =>
      term_perform (rename_marker f recv) Ss A (rename_marker f arg)
  | term_cap E m n_beta Ts T_R op_body =>
      term_cap E (f m) n_beta Ts T_R (rename_marker f op_body)
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
  | EC_perform_r E1 Ss A arg =>
      EC_perform_r (rename_ectx f E1) Ss A (rename_marker f arg)
  | EC_perform_a v Ss A E1 =>
      EC_perform_a (rename_marker f v) Ss A (rename_ectx f E1)
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
               = List.map f (markers_in_list ts))).
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
  - intros E n_beta Ts T_B T_R op_body body IHop IHb. simpl.
    rewrite IHop, IHb, List.map_app. reflexivity.
  - intros recv Ss A arg IHr IHa. simpl.
    rewrite IHr, IHa, List.map_app. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop. simpl. rewrite IHop. reflexivity.
  - intros m T_B T_R body IH. simpl. rewrite IH. reflexivity.
  - reflexivity.
  - intros t ts IHt IHts. simpl. rewrite IHt, IHts, List.map_app. reflexivity.
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
               = has_rt_cap_list ts)).
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
  - intros E n_beta Ts T_B T_R op_body body IHop IHb. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros recv Ss A arg IHr IHa. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop. reflexivity.
  - intros m T_B T_R body IH. reflexivity.
  - reflexivity.
  - intros t ts IHt IHts. simpl. rewrite IHt, IHts. reflexivity.
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
       = List.concat (List.map (free_tm_vars cutoff) ts))).
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
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros recv Ss A arg IHr IHa cutoff. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff. simpl. apply IHop.
  - intros m T_B T_R body IH cutoff. simpl. apply IH.
  - intros cutoff. reflexivity.
  - intros t ts IHt IHts cutoff. simpl. rewrite IHt, IHts. reflexivity.
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
  - (* T_Cap *) simpl. eapply T_Cap; try eassumption.
    apply IH. eassumption.
  - (* T_Handle *) simpl. eapply T_Handle; try eassumption;
      apply IH; eassumption.
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
       well_scoped_list (List.map f ms) (List.map (rename_marker f) ts))).
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
  - intros E n_beta Ts T_B T_R op_body body IHop IHb ms [Hop Hb]. simpl.
    split; [apply IHop | apply IHb]; assumption.
  - intros recv Ss A arg IHr IHa ms [Hr Ha]. simpl.
    split; [apply IHr | apply IHa]; assumption.
  - intros E m n_beta Ts T_R op_body IHop ms [Hm Hop]. simpl.
    split.
    + apply in_map. exact Hm.
    + rewrite scope_below_map by exact Hinj. apply IHop. exact Hop.
  - intros m T_B T_R body IH ms H. simpl.
    change (f m :: List.map f ms) with (List.map f (m :: ms)).
    apply IH. exact H.
  - intros ms _. exact I.
  - intros t ts IHt IHts ms [Ht Hts]. simpl.
    split; [apply IHt | apply IHts]; assumption.
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
       = List.map (shift_tm amount cutoff) (List.map (rename_marker f) ts))).
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
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros recv Ss A arg IHr IHa cutoff. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff. simpl.
    rewrite IHop. reflexivity.
  - intros m T_B T_R body IH cutoff. simpl. rewrite IH. reflexivity.
  - intros cutoff. reflexivity.
  - intros t ts IHt IHts cutoff. simpl. rewrite IHt, IHts. reflexivity.
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
                  (List.map (rename_marker f) ts))).
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
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros recv Ss A arg IHr IHa cutoff. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff. simpl.
    rewrite IHop. reflexivity.
  - intros m T_B T_R body IH cutoff. simpl. rewrite IH. reflexivity.
  - intros cutoff. reflexivity.
  - intros t ts IHt IHts cutoff. simpl. rewrite IHt, IHts. reflexivity.
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
                  (List.map (rename_marker f) ts))).
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
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros recv Ss A arg IHr IHa cutoff. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff. simpl.
    rewrite IHop. reflexivity.
  - intros m T_B T_R body IH cutoff. simpl. rewrite IH. reflexivity.
  - intros cutoff. reflexivity.
  - intros t ts IHt IHts cutoff. simpl. rewrite IHt, IHts. reflexivity.
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
                  (List.map (rename_marker f) ts))).
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
  - intros E n_beta Ts T_B T_R op_body body IHop IHb x s. simpl.
    rewrite IHop, IHb, !rename_marker_shift_tm. reflexivity.
  - intros recv Ss A arg IHr IHa x s. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop x s. simpl.
    rewrite IHop, rename_marker_shift_tm. reflexivity.
  - intros m T_B T_R body IH x s. simpl. rewrite IH. reflexivity.
  - intros x s. reflexivity.
  - intros t ts IHt IHts x s. simpl. rewrite IHt, IHts. reflexivity.
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
       = List.map (subst_ty_in_tm x T) (List.map (rename_marker f) ts))).
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
  - intros E n_beta Ts T_B T_R op_body body IHop IHb x T. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros recv Ss A arg IHr IHa x T. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop x T. simpl.
    rewrite IHop. reflexivity.
  - intros m T_B T_R body IH x T. simpl. rewrite IH. reflexivity.
  - intros x T. reflexivity.
  - intros t ts IHt IHts x T. simpl. rewrite IHt, IHts. reflexivity.
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
       = List.map (subst_lt_in_tm x l) (List.map (rename_marker f) ts))).
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
  - intros E n_beta Ts T_B T_R op_body body IHop IHb x l. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros recv Ss A arg IHr IHa x l. simpl. rewrite IHr, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop x l. simpl.
    rewrite IHop. reflexivity.
  - intros m T_B T_R body IH x l. simpl. rewrite IH. reflexivity.
  - intros x l. reflexivity.
  - intros t ts IHt IHts x l. simpl. rewrite IHt, IHts. reflexivity.
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
               Forall value (List.map (rename_marker f) ts))).
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
  - intros E n_beta Ts T_B T_R op_body body _ _ H; inversion H.
  - intros recv Ss A arg _ _ H; inversion H.
  - intros E m n_beta Ts T_R op_body _ _; simpl; constructor.
  - intros m T_B T_R body _ H; inversion H.
  - intros _; constructor.
  - intros t ts IHt IHts H. inversion H; subst. simpl.
    constructor; [apply IHt | apply IHts]; assumption.
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
    apply H_Perform.
    + apply value_rename_marker. assumption.
    + apply pure_ectx_m_rename_ectx; assumption.
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
        (plug E (term_handle E_tag n_beta Ts T_B T_R op_body body))))).
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
