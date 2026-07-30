Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import ShiftLaws.
Require Import Eqb.
Require Import Stepf.
Require Import MarkerRename.

(* ================================================================== *)
(*                                                                    *)
(*        DETERMINISM MODULO MARKER RENAMING, AND                     *)
(*        COMPLETENESS OF THE CERTIFIED EVALUATOR                     *)
(*                                                                    *)
(* H_Perform requires its captured context to be both marker-pure     *)
(* and value-disciplined (Semantics.v), so the ONLY one-step          *)
(* nondeterminism in the semantics is S_HandleCtx's choice of a       *)
(* globally fresh marker.  This file closes the story:                *)
(*                                                                    *)
(*   head_step_deterministic         head reduction is a partial      *)
(*                                   function — no modulo needed;     *)
(*   stepf_complete_modulo_markers   every step the relation can      *)
(*                                   take, [stepf] takes too, up to   *)
(*                                   the fresh-marker choice;         *)
(*   step_deterministic_modulo_markers                                *)
(*                                   any two steps from one state     *)
(*                                   agree up to a marker bijection.  *)
(*                                                                    *)
(* Method: instead of a standalone unique-decomposition lemma, we     *)
(* prove the evaluator EXACT on redexes ([stepf_go_head_step]:        *)
(* stepf_go returns precisely the head reduct — the escape            *)
(* decomposition of a delimiter body is unique because [ectx_wf]      *)
(* forces every position left of the hole to be a value) and          *)
(* propagate exactness up any well-formed spine                       *)
(* ([stepf_go_plug_step]).  Determinism is then two applications of   *)
(* completeness glued by the [marker_alpha_equiv] equivalence laws    *)
(* (MarkerRename.v).                                                  *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Constructor-spine plumbing: a value prefix passes through the      *)
(* list descent untouched.                                            *)
(* ------------------------------------------------------------------ *)

Lemma stepf_list_vals : forall fresh ts,
  Forall value ts -> stepf_list fresh ts = LR_vals.
Proof.
  intros fresh ts H; induction H as [|x l Hx Hl IH]; simpl.
  - reflexivity.
  - rewrite (stepf_go_value fresh x Hx), IH. reflexivity.
Qed.

Lemma stepf_list_vals_prefix_step : forall fresh vsl u u' vsr,
  Forall value vsl ->
  stepf_go fresh u = SR_step u' ->
  stepf_list fresh (vsl ++ u :: vsr) = LR_step (vsl ++ u' :: vsr).
Proof.
  intros fresh vsl u u' vsr Hvals Hu.
  induction Hvals as [|v vsl' Hv Hvals' IH]; simpl.
  - rewrite Hu. reflexivity.
  - rewrite (stepf_go_value fresh v Hv), IH. reflexivity.
Qed.

Lemma stepf_list_vals_prefix_esc : forall fresh vsl u e P vsr,
  Forall value vsl ->
  stepf_go fresh u = SR_esc e P ->
  stepf_list fresh (vsl ++ u :: vsr) = LR_esc e vsl P vsr.
Proof.
  intros fresh vsl u e P vsr Hvals Hu.
  induction Hvals as [|v vsl' Hv Hvals' IH]; simpl.
  - rewrite Hu. reflexivity.
  - rewrite (stepf_go_value fresh v Hv), IH. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Escape decomposition is computed exactly: on a marker-pure,        *)
(* value-disciplined context around a perform-on-capability redex     *)
(* with a value argument, the descent returns precisely that          *)
(* decomposition.  This is the uniqueness content the new [ectx_wf]   *)
(* premise of H_Perform buys: left of every hole sits a value, so     *)
(* the descent has no choice.                                         *)
(* ------------------------------------------------------------------ *)

Lemma stepf_go_esc_plug : forall fresh Et m Ts TR ops opix Ss A arg P,
  pure_ectx_m m P ->
  ectx_wf P ->
  value arg ->
  stepf_go fresh
    (plug P (term_perform (term_cap Et m Ts TR ops) opix Ss A arg))
  = SR_esc (mk_esc Et m Ts TR ops opix Ss A arg) P.
Proof.
  intros fresh Et m Ts TR ops opix Ss A arg P Hpure.
  induction Hpure; intros Hwf Hval; inversion Hwf; subst; simpl.
  - (* hole *)
    rewrite (stepf_go_value fresh arg Hval). reflexivity.
  - (* app1 *)
    rewrite IHHpure by assumption. reflexivity.
  - (* app2 *)
    rewrite (stepf_go_value fresh v) by assumption.
    rewrite IHHpure by assumption. reflexivity.
  - (* ty_app *)
    rewrite IHHpure by assumption. reflexivity.
  - (* lt_app *)
    rewrite IHHpure by assumption. reflexivity.
  - (* ctor *)
    rewrite stepf_go_list_eq.
    match goal with
    | HF : Forall value _, HE : ectx_wf _ |- _ =>
        rewrite (stepf_list_vals_prefix_esc fresh _ _ _ _ _ HF
                   (IHHpure HE Hval))
    end.
    reflexivity.
  - (* match *)
    rewrite IHHpure by assumption. reflexivity.
  - (* handler_m, m' <> m *)
    rewrite IHHpure by assumption. simpl.
    assert (Hne : Nat.eqb m m' = false) by (apply Nat.eqb_neq; congruence).
    rewrite Hne. reflexivity.
  - (* perform_r *)
    rewrite IHHpure by assumption. reflexivity.
  - (* perform_a *)
    rewrite (stepf_go_value fresh v) by assumption.
    rewrite IHHpure by assumption. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The evaluator is EXACT on head redexes: it returns precisely the   *)
(* head reduct.  (The [fresh] parameter is irrelevant — only a        *)
(* [term_handle] consults it, and handles are not head redexes.)      *)
(* ------------------------------------------------------------------ *)

Lemma stepf_go_head_step : forall fresh r r',
  r -->h r' -> stepf_go fresh r = SR_step r'.
Proof.
  intros fresh r r' Hstep. destruct Hstep; simpl.
  - (* H_Beta *)
    rewrite (stepf_go_value fresh v) by assumption. reflexivity.
  - (* H_TyBeta *)
    reflexivity.
  - (* H_LtBeta *)
    reflexivity.
  - (* H_MatchYes *)
    rewrite stepf_go_list_eq.
    rewrite (stepf_list_vals fresh vs) by assumption.
    rewrite !Nat.eqb_refl. reflexivity.
  - (* H_MatchNo *)
    rewrite stepf_go_list_eq.
    rewrite (stepf_list_vals fresh vs) by assumption.
    assert (Hne : Nat.eqb K' K = false) by (apply Nat.eqb_neq; congruence).
    rewrite Hne. reflexivity.
  - (* H_Return *)
    rewrite (stepf_go_value fresh v) by assumption. reflexivity.
  - (* H_Perform *)
    rewrite (stepf_go_esc_plug fresh E_tag m Ts T_R op_bodies op Ss A v P)
      by assumption.
    simpl. rewrite Nat.eqb_refl, ty_eqb_refl.
    match goal with Hn : nth_error _ _ = Some _ |- _ => rewrite Hn end.
    reflexivity.
Qed.

(* Head reduction is a genuine partial function — no modulo needed.   *)
Theorem head_step_deterministic : forall r u1 u2,
  r -->h u1 -> r -->h u2 -> u1 = u2.
Proof.
  intros r u1 u2 H1 H2.
  pose proof (stepf_go_head_step 0 _ _ H1) as E1.
  pose proof (stepf_go_head_step 0 _ _ H2) as E2.
  rewrite E1 in E2. injection E2 as <-. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Exactness propagates up any well-formed evaluation spine.          *)
(* ------------------------------------------------------------------ *)

Lemma stepf_go_plug_step : forall fresh E r u,
  ectx_wf E ->
  stepf_go fresh r = SR_step u ->
  stepf_go fresh (plug E r) = SR_step (plug E u).
Proof.
  intros fresh E r u Hwf Hr.
  induction Hwf; simpl.
  - (* hole *)
    exact Hr.
  - (* app1 *)
    rewrite IHHwf. reflexivity.
  - (* app2 *)
    rewrite (stepf_go_value fresh v) by assumption.
    rewrite IHHwf. reflexivity.
  - (* ty_app *)
    rewrite IHHwf. reflexivity.
  - (* lt_app *)
    rewrite IHHwf. reflexivity.
  - (* ctor *)
    rewrite stepf_go_list_eq.
    match goal with
    | HF : Forall value _ |- _ =>
        rewrite (stepf_list_vals_prefix_step fresh _ _ _ _ HF IHHwf)
    end.
    reflexivity.
  - (* match *)
    rewrite IHHwf. reflexivity.
  - (* handler_m *)
    rewrite IHHwf. reflexivity.
  - (* perform_r *)
    rewrite IHHwf. reflexivity.
  - (* perform_a *)
    rewrite (stepf_go_value fresh v) by assumption.
    rewrite IHHwf. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Completeness modulo the fresh-marker choice                        *)
(* ------------------------------------------------------------------ *)

Theorem stepf_complete_modulo_markers : forall t u,
  t ==> u ->
  exists u', stepf t = Some u' /\ marker_alpha_equiv u u'.
Proof.
  intros t u Hstep. inversion Hstep; subst.
  - (* S_step: the evaluator takes exactly this step *)
    exists (plug E r'). split.
    + unfold stepf.
      rewrite (stepf_go_plug_step _ _ _ _ H (stepf_go_head_step _ _ _ H0)).
      reflexivity.
    + apply marker_alpha_equiv_refl.
  - (* S_HandleCtx: the evaluator allocates marker_bound instead *)
    match goal with
    | |- context [plug ?E0 (term_handle ?Et ?Ts0 ?TB ?TR ?ob ?bd)] =>
        set (t0 := plug E0 (term_handle Et Ts0 TB TR ob bd))
    end.
    exists (plug E (term_handler_m (marker_bound t0) T_B T_R
              (subst_tm 0
                 (term_cap E_tag (marker_bound t0) Ts T_R op_bodies)
                 body))).
    split.
    + unfold stepf. unfold t0 at 2.
      assert (Hh : stepf_go (marker_bound t0)
                     (term_handle E_tag Ts T_B T_R op_bodies body)
                   = SR_step (term_handler_m (marker_bound t0) T_B T_R
                        (subst_tm 0
                           (term_cap E_tag (marker_bound t0) Ts T_R
                                     op_bodies)
                           body)))
        by reflexivity.
      rewrite (stepf_go_plug_step _ _ _ _ H Hh).
      reflexivity.
    + apply handle_choice_irrelevant.
      * exact H0.
      * apply marker_bound_fresh.
Qed.

(* ------------------------------------------------------------------ *)
(* One-step determinism modulo marker renaming                        *)
(* ------------------------------------------------------------------ *)

Theorem step_deterministic_modulo_markers : forall t u1 u2,
  t ==> u1 -> t ==> u2 -> marker_alpha_equiv u1 u2.
Proof.
  intros t u1 u2 H1 H2.
  destruct (stepf_complete_modulo_markers _ _ H1) as [w  [Hw  A1]].
  destruct (stepf_complete_modulo_markers _ _ H2) as [w' [Hw' A2]].
  rewrite Hw in Hw'. injection Hw' as <-.
  eapply marker_alpha_equiv_trans; [exact A1|].
  apply marker_alpha_equiv_sym. exact A2.
Qed.
