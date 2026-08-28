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

(* ------------------------------------------------------------------ *)
(* The stuck verdict's specification                                  *)
(*                                                                    *)
(* [go_spec] (Stepf.v) certifies the value / step / escape verdicts;  *)
(* SR_stuck carried no claim there because its meaning is NEGATIVE —  *)
(* no value, no step, no escape decomposition — and the "no step"     *)
(* half is exactly evaluator completeness, which lives here.  Each    *)
(* conjunct is the contrapositive of an exactness lemma:              *)
(* [stepf_go_value], [stepf_complete_modulo_markers],                 *)
(* [stepf_go_esc_plug].                                               *)
(* ------------------------------------------------------------------ *)

Theorem stepf_go_stuck_sound : forall t,
  stepf_go (marker_bound t) t = SR_stuck ->
  ~ value t /\
  (forall u, ~ t ==> u) /\
  (forall e P, esc_ok e P -> t <> plug P (esc_redex e)).
Proof.
  intros t Hgo.
  split; [|split].
  - intros Hv.
    rewrite (stepf_go_value (marker_bound t) t Hv) in Hgo. discriminate.
  - intros u Hs.
    destruct (stepf_complete_modulo_markers _ _ Hs) as [u' [Hsome _]].
    unfold stepf in Hsome. rewrite Hgo in Hsome. discriminate.
  - intros e P Hok Heq.
    destruct e as [Et m Ts TR ops opix Ss A arg].
    destruct Hok as (Hpure & Hwf & Hval).
    simpl in Hpure, Hval.
    unfold esc_redex in Heq. simpl in Heq.
    rewrite Heq in Hgo.
    rewrite (stepf_go_esc_plug _ _ _ _ _ _ _ _ _ _ _ Hpure Hwf Hval)
      in Hgo.
    discriminate.
Qed.

(* The four-way certified classification: EVERY verdict the evaluator *)
(* can return now carries its meaning.  (The stuck arm restates       *)
(* [stepf_go_stuck_sound]; the others come from [stepf_go_sound] and  *)
(* [stepf_sound], Stepf.v.)                                           *)
Theorem stepf_classification : forall t,
  match stepf_go (marker_bound t) t with
  | SR_val     => value t
  | SR_step u  => t ==> u
  | SR_esc e P => esc_ok e P /\ t = plug P (esc_redex e)
  | SR_stuck   => ~ value t /\
                  (forall u, ~ t ==> u) /\
                  (forall e P, esc_ok e P -> t <> plug P (esc_redex e))
  end.
Proof.
  intros t.
  destruct (stepf_go (marker_bound t) t) as [|u|e P|] eqn:Hgo.
  - destruct (stepf_go_sound (marker_bound t) t) as [Hv _]. auto.
  - apply stepf_sound. unfold stepf. rewrite Hgo. reflexivity.
  - destruct (stepf_go_sound (marker_bound t) t) as [_ [_ Hesc]].
    exact (Hesc _ _ Hgo).
  - exact (stepf_go_stuck_sound t Hgo).
Qed.

(* ================================================================== *)
(* Multi-step determinism, unique normal forms, and evaluator         *)
(* adequacy — all modulo the fresh-marker choice.                     *)
(*                                                                    *)
(* The missing piece was "alpha-equivalence is a simulation".  With   *)
(* [marker_alpha_equiv] carrying an explicit two-sided bijection      *)
(* (MarkerRename.v), the simulation is [step_rename_markers] applied  *)
(* to THE SAME bijection — no fresh diagram chase is needed, and the  *)
(* bijection compositions are exactly the equivalence laws.           *)
(* ================================================================== *)

(* Alpha-equivalence is a (one-step) simulation: an equivalent state  *)
(* can answer any step with an equivalent step.                       *)
Theorem step_marker_alpha_simulation : forall t t' u,
  marker_alpha_equiv t t' ->
  t ==> u ->
  exists u', t' ==> u' /\ marker_alpha_equiv u u'.
Proof.
  intros t t' u (f & g & Hgf & Hfg & Heq) Hstep.
  exists (rename_marker f u). split.
  - subst t'.
    apply step_rename_markers;
      [ exact (marker_left_inverse_inj f g Hgf) | exact Hstep ].
  - exists f, g. auto.
Qed.

(* The multi-step closure of the simulation.                          *)
Theorem multi_step_marker_alpha_simulation : forall t t' u,
  marker_alpha_equiv t t' ->
  multi_step t u ->
  exists u', multi_step t' u' /\ marker_alpha_equiv u u'.
Proof.
  intros t t' u Halpha Hms. revert t' Halpha.
  induction Hms as [t | t w u Hstep Hms IH]; intros t' Halpha.
  - exists t'. split; [apply MS_Refl | exact Halpha].
  - destruct (step_marker_alpha_simulation _ _ _ Halpha Hstep)
      as [w' [Hs' Ha']].
    destruct (IH _ Ha') as [u' [Hms' Ha'']].
    exists u'. split; [eapply MS_Step; eassumption | exact Ha''].
Qed.

(* ------------------------------------------------------------------ *)
(* Normal forms.  A normal form is a state with no successor; values  *)
(* are normal forms (evaluator completeness turns [stepf_value_none]  *)
(* into "values do not step"), and normal-form-ness transports along  *)
(* the simulation.                                                    *)
(* ------------------------------------------------------------------ *)

Definition normal_form (t : term) : Prop := forall u, ~ t ==> u.

Lemma value_no_step : forall t u, value t -> ~ t ==> u.
Proof.
  intros t u Hv Hs.
  destruct (stepf_complete_modulo_markers _ _ Hs) as [u' [Hsome _]].
  rewrite (stepf_value_none _ Hv) in Hsome. discriminate.
Qed.

Lemma value_normal_form : forall t, value t -> normal_form t.
Proof. intros t Hv u. apply value_no_step. exact Hv. Qed.

Lemma normal_form_marker_alpha : forall t t',
  marker_alpha_equiv t t' -> normal_form t -> normal_form t'.
Proof.
  intros t t' Halpha Hnf u' Hstep.
  destruct (step_marker_alpha_simulation t' t u'
              (marker_alpha_equiv_sym _ _ Halpha) Hstep) as [w [Hs _]].
  exact (Hnf w Hs).
Qed.

Lemma multi_step_normal_form_refl : forall t u,
  normal_form t -> multi_step t u -> u = t.
Proof.
  intros t u Hnf Hms. inversion Hms; subst.
  - reflexivity.
  - exfalso. eapply Hnf. eassumption.
Qed.

(* The kernel diagram chase, generalized over an alpha-equivalence    *)
(* between the two starting states: one-step determinism modulo       *)
(* markers aligns the first steps, the simulation transports the      *)
(* alignment, transitivity composes the bijections.                   *)
Lemma multi_step_normal_form_alpha : forall t1 v1,
  multi_step t1 v1 ->
  normal_form v1 ->
  forall t2 v2,
  marker_alpha_equiv t1 t2 ->
  multi_step t2 v2 ->
  normal_form v2 ->
  marker_alpha_equiv v1 v2.
Proof.
  intros t1 v1 Hms1.
  induction Hms1 as [t1 | t1 u1 v1 Hstep1 Hms1 IH];
    intros Hnf1 t2 v2 Halpha Hms2 Hnf2.
  - (* t1 itself is normal, so t2 is too and v2 = t2 *)
    pose proof (normal_form_marker_alpha _ _ Halpha Hnf1) as Hnf2'.
    rewrite (multi_step_normal_form_refl _ _ Hnf2' Hms2). exact Halpha.
  - (* t1 steps; t2 answers with an equivalent step, and one-step     *)
    (* determinism aligns it with t2's own reduction *)
    destruct (step_marker_alpha_simulation _ _ _ Halpha Hstep1)
      as [u2 [Hstep2 Halpha_u]].
    inversion Hms2; subst.
    + exfalso. exact (Hnf2 _ Hstep2).
    + match goal with
      | Hs : t2 ==> ?w0, Hm : multi_step ?w0 v2 |- _ =>
          exact (IH Hnf1 w0 v2
                   (marker_alpha_equiv_trans _ _ _ Halpha_u
                      (step_deterministic_modulo_markers _ _ _ Hstep2 Hs))
                   Hm Hnf2)
      end.
Qed.

(* Evaluation is a partial function up to marker permutation: any two *)
(* normal forms reached from one state agree modulo a marker          *)
(* bijection.                                                         *)
Theorem multi_step_deterministic_modulo_markers : forall t u1 u2,
  multi_step t u1 -> normal_form u1 ->
  multi_step t u2 -> normal_form u2 ->
  marker_alpha_equiv u1 u2.
Proof.
  intros t u1 u2 Hms1 Hnf1 Hms2 Hnf2.
  exact (multi_step_normal_form_alpha _ _ Hms1 Hnf1 _ _
           (marker_alpha_equiv_refl t) Hms2 Hnf2).
Qed.

(* The value form: results are unique modulo the fresh-marker choice. *)
Corollary value_unique_modulo_markers : forall t v1 v2,
  multi_step t v1 -> value v1 ->
  multi_step t v2 -> value v2 ->
  marker_alpha_equiv v1 v2.
Proof.
  intros t v1 v2 Hms1 Hv1 Hms2 Hv2.
  apply (multi_step_deterministic_modulo_markers t);
    auto using value_normal_form.
Qed.

(* ------------------------------------------------------------------ *)
(* Evaluator adequacy: the bounded driver reaches every value the     *)
(* RELATION can reach, up to a marker bijection — [stepf_run] is not  *)
(* just sound (stepf_run_sound) but complete for value results.       *)
(* ------------------------------------------------------------------ *)

Lemma stepf_run_reaches_alpha : forall t v,
  multi_step t v ->
  normal_form v ->
  forall t', marker_alpha_equiv t t' ->
  exists n, marker_alpha_equiv v (stepf_run n t').
Proof.
  intros t v Hms.
  induction Hms as [t | t u v Hstep Hms IH]; intros Hnf t' Halpha.
  - exists 0. exact Halpha.
  - destruct (step_marker_alpha_simulation _ _ _ Halpha Hstep)
      as [u'' [Hstep' Halpha_u]].
    destruct (stepf_complete_modulo_markers _ _ Hstep')
      as [w [Hsome Halpha_w]].
    destruct (IH Hnf w
                (marker_alpha_equiv_trans _ _ _ Halpha_u Halpha_w))
      as [n Hn].
    exists (S n). simpl. rewrite Hsome. exact Hn.
Qed.

Theorem stepf_run_complete_modulo_markers : forall t v,
  multi_step t v ->
  value v ->
  exists n, marker_alpha_equiv v (stepf_run n t).
Proof.
  intros t v Hms Hv.
  apply (stepf_run_reaches_alpha t v Hms (value_normal_form v Hv) t).
  apply marker_alpha_equiv_refl.
Qed.
