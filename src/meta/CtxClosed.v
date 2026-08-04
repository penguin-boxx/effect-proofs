Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import ShiftLaws.
Require Import ProgramCtx.

(* ================================================================== *)
(* CtxClosed: the context-closedness bookkeeping over [eval_ctx].     *)
(*                                                                    *)
(* The closedness predicates on contexts — [ctor_fields_closed],      *)
(* [ctx_schemas_lt_closed_from], [ctx_ty_closed_from] /               *)
(* [ctx_lt_closed_from] — with their binder-preservation families,    *)
(* the wf-to-closed transports, and the typing-level corollaries      *)
(* ([typing_tm_ty_closed_from] / [typing_tm_lt_closed_from] and       *)
(* their eval_ctx front instances).  These are the hypothesis         *)
(* packages threaded through [typing_SubstTm] (SubstTm.v) and         *)
(* [typing_SubstTy] (TypingSubst.v); the [eval_ctx] invariant itself  *)
(* lives in ProgramCtx.v.                                             *)
(* ================================================================== *)

Lemma eval_ctx_lookup_ctor_lt_closed : forall Γ K n_lt n_ty fields result,
  eval_ctx Γ ->
  ctx_lookup_ctor Γ K = Some (n_lt, n_ty, fields, result) ->
  tys_lt_closed n_lt fields /\ ty_lt_closed n_lt result.
Proof.
  intros Γ K n_lt n_ty fields result Hec.
  induction Hec as
      [|K0 n_lt0 n_ty0 fields0 result0 Γ Hfields0 Hresult0 Htyc0 Hec IH
       |E0 n_α ops0 Γ Hne Hops0 Hec IH]; intro Hlk; simpl in Hlk.
  - discriminate.
  - destruct (Nat.eqb K K0) eqn:Heq.
    + inversion Hlk; subst. split; assumption.
    + apply IH. exact Hlk.
  - apply IH. exact Hlk.
Qed.

Lemma eval_ctx_lookup_eff_lt_closed : forall Γ E n_α ops,
  eval_ctx Γ ->
  ctx_lookup_eff Γ E = Some (n_α, ops) ->
  Forall (fun osig => ty_lt_closed 0 (op_sig_ty osig) /\
                      ty_lt_closed 0 (op_ret_ty osig)) ops.
Proof.
  intros Γ E n_α ops Hec.
  induction Hec as
      [|K0 n_lt n_ty fields result Γ Hfields Hresult Htyc Hec IH
       |E0 n_α0 ops0 Γ Hne Hops0 Hec IH]; intro Hlk; simpl in Hlk.
  - discriminate.
  - apply IH. exact Hlk.
  - destruct (Nat.eqb E E0) eqn:Heq.
    + inversion Hlk; subst. exact Hops0.
    + apply IH. exact Hlk.
Qed.

(* Extract field ty-closedness from eval_ctx (mirrors the lt version).  *)
Lemma eval_ctx_lookup_ctor_ty_closed : forall Γ K n_lt n_ty fields result,
  eval_ctx Γ ->
  ctx_lookup_ctor Γ K = Some (n_lt, n_ty, fields, result) ->
  tys_ty_closed n_ty fields.
Proof.
  intros Γ K n_lt n_ty fields result Hec.
  induction Hec as
      [|K0 n_lt0 n_ty0 fields0 result0 Γ Hfields0 Hresult0 Htyc0 Hec IH
       |E0 n_α ops0 Γ Hne Hops0 Hec IH]; intro Hlk; simpl in Hlk.
  - discriminate.
  - destruct (Nat.eqb K K0) eqn:Heq.
    + inversion Hlk; subst. exact Htyc0.
    + apply IH. exact Hlk.
  - apply IH. exact Hlk.
Qed.

(* Maps of (lt-/ty-)closed types are fixed by shifts at the closedness  *)
(* bound (the constructor-signature shifts sit above the schema params). *)
Lemma map_shift_ty_closed : forall f c a,
  tys_ty_closed c f -> List.map (shift_ty a c) f = f.
Proof.
  induction f as [|T f IH]; intros c a Hc; simpl in *; [reflexivity|].
  destruct Hc as [HT Hf]. rewrite shift_ty_in_ty_closed by exact HT.
  rewrite IH by exact Hf. reflexivity.
Qed.

Lemma map_shift_lt_closed : forall f c a,
  tys_lt_closed c f -> List.map (shift_lt_in_ty a c) f = f.
Proof.
  induction f as [|T f IH]; intros c a Hc; simpl in *; [reflexivity|].
  destruct Hc as [HT Hf]. rewrite shift_lt_in_type_closed by exact HT.
  rewrite IH by exact Hf. reflexivity.
Qed.

(* The constructor-field-closedness invariant threaded through           *)
(* typing_SubstTy (needed for the T_Ctor escape-premise alignment).      *)
Definition ctor_fields_closed (Γ : ctx) : Prop :=
  forall K n_lt n_ty fields result,
    ctx_lookup_ctor Γ K = Some (n_lt, n_ty, fields, result) ->
    tys_lt_closed n_lt fields /\ tys_ty_closed n_ty fields.

Lemma eval_ctx_ctor_fields_closed : forall Γ, eval_ctx Γ -> ctor_fields_closed Γ.
Proof.
  intros Γ Hec K n_lt n_ty fields result Hlk. split.
  - destruct (eval_ctx_lookup_ctor_lt_closed Γ K n_lt n_ty fields result Hec Hlk) as [Hf _]. exact Hf.
  - apply (eval_ctx_lookup_ctor_ty_closed Γ K n_lt n_ty fields result Hec Hlk).
Qed.

Lemma ctor_fields_closed_bind_tm : forall A Γ,
  ctor_fields_closed Γ -> ctor_fields_closed (bind_tm A :: Γ).
Proof. intros A Γ H K n_lt n_ty f r Hlk. simpl in Hlk. apply (H K n_lt n_ty f r Hlk). Qed.

Lemma ctor_fields_closed_bind_ty : forall B Γ,
  ctor_fields_closed Γ -> ctor_fields_closed (bind_ty B :: Γ).
Proof.
  intros B Γ H K n_lt n_ty fields result Hlk. simpl in Hlk.
  destruct (ctx_lookup_ctor Γ K) as [[[[n_lt0 n_ty0] f0] r0]|] eqn:E; [|discriminate].
  destruct (H K n_lt0 n_ty0 f0 r0 E) as [Hlt Hty].
  cbn [option_map] in Hlk. unfold shift_ty_ctor_sig in Hlk. inversion Hlk; subst.
  rewrite Nat.add_0_r. rewrite (map_shift_ty_closed f0 n_ty 1 Hty).
  split; [exact Hlt | exact Hty].
Qed.

Lemma ctor_fields_closed_bind_lt : forall D Γ,
  ctor_fields_closed Γ -> ctor_fields_closed (bind_lt D :: Γ).
Proof.
  intros D Γ H K n_lt n_ty fields result Hlk. simpl in Hlk.
  destruct (ctx_lookup_ctor Γ K) as [[[[n_lt0 n_ty0] f0] r0]|] eqn:E; [|discriminate].
  destruct (H K n_lt0 n_ty0 f0 r0 E) as [Hlt Hty].
  cbn [option_map] in Hlk. unfold shift_lt_ctor_sig in Hlk. inversion Hlk; subst.
  rewrite Nat.add_0_r. rewrite (map_shift_lt_closed f0 n_lt 1 Hlt).
  split; [exact Hlt | exact Hty].
Qed.

Lemma ctor_fields_closed_push_ty_vars : forall k B Γ,
  ctor_fields_closed Γ -> ctor_fields_closed (push_ty_vars k B Γ).
Proof.
  induction k; intros B Γ H; simpl; [exact H|].
  apply IHk. apply ctor_fields_closed_bind_ty. exact H.
Qed.


Lemma ctor_fields_closed_fold_bind_tm : forall rhos Γ,
  ctor_fields_closed Γ ->
  ctor_fields_closed (List.fold_right (fun rho G0 => bind_tm rho :: G0) Γ rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros Γ H; simpl; [exact H|].
  apply ctor_fields_closed_bind_tm. apply IH. exact H.
Qed.

(* Bridge to the per-field Forall used by the escape alignment.          *)
Lemma tys_closed_Forall_and : forall n_lt n_ty f,
  tys_lt_closed n_lt f -> tys_ty_closed n_ty f ->
  Forall (fun S => ty_lt_closed n_lt S /\ ty_ty_closed n_ty S) f.
Proof.
  induction f as [|T f IH]; intros Hlt Hty; [constructor|].
  simpl in Hlt, Hty. destruct Hlt as [HltT Hltf], Hty as [HtyT Htyf].
  constructor; [split; assumption | apply IH; assumption].
Qed.


Definition ctx_ctor_schemas_lt_closed_from (c : nat) (Γ : ctx) : Prop :=
  forall K n_lt n_ty fields result,
    ctx_lookup_ctor Γ K = Some (n_lt, n_ty, fields, result) ->
    tys_lt_closed (n_lt + c) fields /\ ty_lt_closed (n_lt + c) result.

Definition ctx_eff_schemas_lt_closed_from (c : nat) (Γ : ctx) : Prop :=
  forall E n_α ops,
    ctx_lookup_eff Γ E = Some (n_α, ops) ->
    Forall (fun osig => ty_lt_closed c (op_sig_ty osig) /\
                        ty_lt_closed c (op_ret_ty osig)) ops.

Definition ctx_schemas_lt_closed_from (c : nat) (Γ : ctx) : Prop :=
  ctx_ctor_schemas_lt_closed_from c Γ /\ ctx_eff_schemas_lt_closed_from c Γ.

Lemma eval_ctx_schemas_lt_closed_from : forall Γ,
  eval_ctx Γ -> ctx_schemas_lt_closed_from 0 Γ.
Proof.
  intros Γ Hec. split.
  - intros K n_lt n_ty fields result Hlk.
    destruct (eval_ctx_lookup_ctor_lt_closed Γ K n_lt n_ty fields result Hec Hlk) as [Hfields Hresult].
    replace (n_lt + 0) with n_lt by lia. split; assumption.
  - intros E n_α ops Hlk.
    eapply eval_ctx_lookup_eff_lt_closed; eauto.
Qed.

Lemma ctx_schemas_lt_closed_from_bind_tm : forall c Γ A,
  ctx_schemas_lt_closed_from c Γ ->
  ctx_schemas_lt_closed_from c (bind_tm A :: Γ).
Proof.
  intros c Γ A [Hctor Heff]. split.
  - intros K n_lt n_ty fields result Hlk. simpl in Hlk. eapply Hctor; eauto.
  - intros E n_α ops Hlk. simpl in Hlk. eapply Heff; eauto.
Qed.

Lemma ctx_schemas_lt_closed_from_bind_ty : forall c Γ B,
  ctx_schemas_lt_closed_from c Γ ->
  ctx_schemas_lt_closed_from c (bind_ty B :: Γ).
Proof.
  intros c Γ B [Hctor Heff]. split.
  - intros K n_lt n_ty fields result Hlk. simpl in Hlk.
    destruct (ctx_lookup_ctor Γ K) as [[[[n_lt0 n_ty0] fields0] result0]|] eqn:Hbase; [|discriminate].
    destruct (Hctor K n_lt0 n_ty0 fields0 result0 Hbase) as [Hfields Hresult].
    inversion Hlk; subst; clear Hlk.
    split.
    + apply tys_lt_closed_shift_ty. exact Hfields.
    + apply ty_lt_closed_shift_ty. exact Hresult.
  - intros E n_α ops Hlk. simpl in Hlk.
    destruct (ctx_lookup_eff Γ E) as [[n_α0 ops0]|] eqn:Hbase; [|discriminate].
    specialize (Heff E n_α0 ops0 Hbase).
    inversion Hlk; subst; clear Hlk.
    clear - Heff.
    induction Heff as [|[[nβ s] r] ops0' [Hs Hr] Hrest IH]; simpl.
    + constructor.
    + constructor; [| exact IH].
      unfold op_sig_ty, op_ret_ty in *; simpl in *.
      split; apply ty_lt_closed_shift_ty; assumption.
Qed.

Lemma ctx_schemas_lt_closed_from_bind_lt : forall c Γ D,
  ctx_schemas_lt_closed_from c Γ ->
  ctx_schemas_lt_closed_from (S c) (bind_lt D :: Γ).
Proof.
  intros c Γ D [Hctor Heff]. split.
  - intros K n_lt n_ty fields result Hlk. simpl in Hlk.
    destruct (ctx_lookup_ctor Γ K) as [[[[n_lt0 n_ty0] fields0] result0]|] eqn:Hbase; [|discriminate].
    destruct (Hctor K n_lt0 n_ty0 fields0 result0 Hbase) as [Hfields Hresult].
    inversion Hlk; subst; clear Hlk.
    replace (n_lt + S c) with (1 + (n_lt + c)) by lia.
    split.
    + eapply tys_lt_closed_shift_lt_below; [lia|exact Hfields].
    + eapply ty_lt_closed_shift_lt_below; [lia|exact Hresult].
  - intros E n_α ops Hlk. simpl in Hlk.
    destruct (ctx_lookup_eff Γ E) as [[n_α0 ops0]|] eqn:Hbase; [|discriminate].
    specialize (Heff E n_α0 ops0 Hbase).
    inversion Hlk; subst; clear Hlk.
    clear - Heff.
    induction Heff as [|[[nβ s] r] ops0' [Hs Hr] Hrest IH]; simpl.
    + constructor.
    + constructor; [| exact IH].
      unfold op_sig_ty, op_ret_ty in *; simpl in *.
      replace (S c) with (1 + c) by lia.
      split; (eapply ty_lt_closed_shift_lt_below; [lia|assumption]).
Qed.


Lemma ctx_schemas_lt_closed_from_push_ty_vars : forall k B c Γ,
  ctx_schemas_lt_closed_from c Γ ->
  ctx_schemas_lt_closed_from c (push_ty_vars k B Γ).
Proof.
  induction k as [|k IH]; intros B c Γ Hctx; simpl.
  - exact Hctx.
  - apply IH. apply ctx_schemas_lt_closed_from_bind_ty. exact Hctx.
Qed.

Lemma ctx_schemas_lt_closed_from_fold_bind_tm : forall rhos c Γ,
  ctx_schemas_lt_closed_from c Γ ->
  ctx_schemas_lt_closed_from c (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros c Γ Hctx; simpl.
  - exact Hctx.
  - apply ctx_schemas_lt_closed_from_bind_tm. apply IH. exact Hctx.
Qed.


Definition ctx_ty_closed_from (c : nat) (Γ : ctx) : Prop :=
  forall x, c <= x -> ctx_lookup_ty Γ x = None.

Definition ctx_lt_closed_from (c : nat) (Γ : ctx) : Prop :=
  forall x, c <= x -> ctx_lookup_lt Γ x = None.


Lemma eval_ctx_ty_closed_from : forall Γ,
  eval_ctx Γ -> ctx_ty_closed_from 0 Γ.
Proof.
  intros Γ Hec x _. apply eval_ctx_no_ty. exact Hec.
Qed.

Lemma eval_ctx_lt_closed_from : forall Γ,
  eval_ctx Γ -> ctx_lt_closed_from 0 Γ.
Proof.
  intros Γ Hec x _. apply eval_ctx_no_lt. exact Hec.
Qed.


Lemma ctx_ty_closed_from_bind_tm : forall c Γ A,
  ctx_ty_closed_from c Γ -> ctx_ty_closed_from c (bind_tm A :: Γ).
Proof. intros c Γ A H x Hle. simpl. apply H. exact Hle. Qed.

Lemma ctx_ty_closed_from_bind_ty : forall c Γ B,
  ctx_ty_closed_from c Γ -> ctx_ty_closed_from (S c) (bind_ty B :: Γ).
Proof.
  intros c Γ B H x Hle. destruct x as [|x']; [lia|].
  simpl. rewrite H by lia. reflexivity.
Qed.

Lemma ctx_ty_closed_from_bind_lt : forall c Γ D,
  ctx_ty_closed_from c Γ -> ctx_ty_closed_from c (bind_lt D :: Γ).
Proof.
  intros c Γ D H x Hle. simpl. rewrite H by exact Hle. reflexivity.
Qed.

Lemma ctx_lt_closed_from_bind_tm : forall c Γ A,
  ctx_lt_closed_from c Γ -> ctx_lt_closed_from c (bind_tm A :: Γ).
Proof. intros c Γ A H x Hle. simpl. apply H. exact Hle. Qed.

Lemma ctx_lt_closed_from_bind_ty : forall c Γ B,
  ctx_lt_closed_from c Γ -> ctx_lt_closed_from c (bind_ty B :: Γ).
Proof. intros c Γ B H x Hle. simpl. apply H. exact Hle. Qed.

Lemma ctx_lt_closed_from_bind_lt : forall c Γ D,
  ctx_lt_closed_from c Γ -> ctx_lt_closed_from (S c) (bind_lt D :: Γ).
Proof.
  intros c Γ D H x Hle. destruct x as [|x']; [lia|].
  simpl. rewrite H by lia. reflexivity.
Qed.


Lemma lt_wf_closed_from : forall Γ l,
  lt_wf Γ l -> forall c, ctx_lt_closed_from c Γ -> lt_lt_closed c l.
Proof.
  intros Γ l Hwf. induction Hwf; intros c Hctx; simpl.
  - destruct (Nat.lt_ge_cases x c) as [Hlt|Hge]; [exact Hlt|].
    exfalso. specialize (Hctx x Hge). rewrite H in Hctx. discriminate.
  - exact I.
  - exact I.
  - split; [apply IHHwf1|apply IHHwf2]; exact Hctx.
Qed.

Lemma lifetimes_wf_lt_closed_from : forall Γ lts,
  lifetimes_wf Γ lts -> forall c, ctx_lt_closed_from c Γ -> lts_lt_closed c lts.
Proof.
  intros Γ lts Hwf. induction Hwf; intros c Hctx; simpl.
  - exact I.
  - split.
    + eapply lt_wf_closed_from; eauto.
    + apply IHHwf. exact Hctx.
Qed.

Lemma ty_wf_ty_closed_from : forall Γ T,
  ty_wf Γ T -> forall c, ctx_ty_closed_from c Γ -> ty_ty_closed c T
with types_wf_ty_closed_from : forall Γ Ts,
  types_wf Γ Ts -> forall c, ctx_ty_closed_from c Γ -> tys_ty_closed c Ts.
Proof.
  - intros Γ T Hwf. induction Hwf; intros c Hctx; simpl.
    + destruct (Nat.lt_ge_cases α c) as [Hlt|Hge]; [exact Hlt|].
      exfalso. specialize (Hctx α Hge). rewrite H in Hctx. discriminate.
    + split; [apply IHHwf1|apply IHHwf2]; exact Hctx.
    + eapply types_wf_ty_closed_from; eauto.
    + apply IHHwf. apply ctx_ty_closed_from_bind_lt. exact Hctx.
    + split.
      * apply IHHwf1. exact Hctx.
      * apply IHHwf2. apply ctx_ty_closed_from_bind_ty. exact Hctx.
  - intros Γ Ts Hwf. induction Hwf; intros c Hctx; simpl.
    + exact I.
    + split.
      * eapply ty_wf_ty_closed_from; eauto.
      * apply IHHwf. exact Hctx.
Qed.

Lemma ty_wf_lt_closed_from : forall Γ T,
  ty_wf Γ T -> forall c, ctx_lt_closed_from c Γ -> ty_lt_closed c T
with types_wf_lt_closed_from : forall Γ Ts,
  types_wf Γ Ts -> forall c, ctx_lt_closed_from c Γ -> tys_lt_closed c Ts.
Proof.
  - intros Γ T Hwf. induction Hwf; intros c Hctx; simpl.
    + exact I.
    + repeat split.
      * apply IHHwf1. exact Hctx.
      * eapply lt_wf_closed_from; eauto.
      * apply IHHwf2. exact Hctx.
    + split.
      * eapply lt_wf_closed_from; eauto.
      * eapply types_wf_lt_closed_from; eauto.
    + apply IHHwf. apply ctx_lt_closed_from_bind_lt. exact Hctx.
    + split.
      * apply IHHwf1. exact Hctx.
      * apply IHHwf2. apply ctx_lt_closed_from_bind_ty. exact Hctx.
  - intros Γ Ts Hwf. induction Hwf; intros c Hctx; simpl.
    + exact I.
    + split.
      * eapply ty_wf_lt_closed_from; eauto.
      * apply IHHwf. exact Hctx.
Qed.

Lemma ty_wf_eval_ctx_ty_closed : forall Γ T,
  eval_ctx Γ -> ty_wf Γ T -> ty_ty_closed 0 T.
Proof.
  intros Γ T Hec Hwf. eapply ty_wf_ty_closed_from; [exact Hwf|].
  apply eval_ctx_ty_closed_from. exact Hec.
Qed.

Lemma ty_wf_eval_ctx_lt_closed : forall Γ T,
  eval_ctx Γ -> ty_wf Γ T -> ty_lt_closed 0 T.
Proof.
  intros Γ T Hec Hwf. eapply ty_wf_lt_closed_from; [exact Hwf|].
  apply eval_ctx_lt_closed_from. exact Hec.
Qed.


Lemma lt_wf_eval_ctx_lt_closed : forall Γ l,
  eval_ctx Γ -> lt_wf Γ l -> lt_lt_closed 0 l.
Proof.
  intros Γ l Hec Hwf. eapply lt_wf_closed_from; [exact Hwf|].
  apply eval_ctx_lt_closed_from. exact Hec.
Qed.


Lemma ctx_ty_closed_from_push_ty_vars : forall k B c Γ,
  ctx_ty_closed_from c Γ -> ctx_ty_closed_from (c + k) (push_ty_vars k B Γ).
Proof.
  induction k as [|k IH]; intros B c Γ Hctx; simpl.
  - replace (c + 0) with c by lia. exact Hctx.
  - replace (c + S k) with (S c + k) by lia.
    apply IH. apply ctx_ty_closed_from_bind_ty. exact Hctx.
Qed.

Lemma ctx_ty_closed_from_fold_bind_tm : forall rhos c Γ,
  ctx_ty_closed_from c Γ ->
  ctx_ty_closed_from c (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros c Γ Hctx; simpl.
  - exact Hctx.
  - apply ctx_ty_closed_from_bind_tm. apply IH. exact Hctx.
Qed.


Lemma ctx_lt_closed_from_push_ty_vars : forall k B c Γ,
  ctx_lt_closed_from c Γ -> ctx_lt_closed_from c (push_ty_vars k B Γ).
Proof.
  induction k as [|k IH]; intros B c Γ Hctx; simpl.
  - exact Hctx.
  - apply IH. apply ctx_lt_closed_from_bind_ty. exact Hctx.
Qed.

Lemma ctx_lt_closed_from_fold_bind_tm : forall rhos c Γ,
  ctx_lt_closed_from c Γ ->
  ctx_lt_closed_from c (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros c Γ Hctx; simpl.
  - exact Hctx.
  - apply ctx_lt_closed_from_bind_tm. apply IH. exact Hctx.
Qed.

(* ----- push_match_bound versions of the closedness-preservation lemmas ---- *)
(* [push_match_bound] adds the same k bind_lt entries as [push_lt_vars]; the   *)
(* per-level bound value is irrelevant to every closed-from predicate   *)
(* (they read lookups, which ignore bind_lt bounds, or non-bind_lt      *)
(* binding contents), so each proof mirrors its [push_lt_vars] sibling, *)
(* peeling the prepended bind_lt with the corresponding _bind_lt step.  *)
Lemma ctx_ty_closed_from_push_match_bound : forall k Delta c Γ,
  ctx_ty_closed_from c Γ -> ctx_ty_closed_from c (push_match_bound k Delta Γ).
Proof.
  induction k as [|k IH]; intros Delta c Γ Hctx; simpl.
  - exact Hctx.
  - apply ctx_ty_closed_from_bind_lt. apply IH. exact Hctx.
Qed.

Lemma ctx_lt_closed_from_push_match_bound : forall k Delta c Γ,
  ctx_lt_closed_from c Γ -> ctx_lt_closed_from (c + k) (push_match_bound k Delta Γ).
Proof.
  induction k as [|k IH]; intros Delta c Γ Hctx; simpl.
  - replace (c + 0) with c by lia. exact Hctx.
  - replace (c + S k) with (S (c + k)) by lia.
    apply ctx_lt_closed_from_bind_lt. apply IH. exact Hctx.
Qed.

Lemma ctx_schemas_lt_closed_from_push_match_bound : forall k Delta c Γ,
  ctx_schemas_lt_closed_from c Γ ->
  ctx_schemas_lt_closed_from (c + k) (push_match_bound k Delta Γ).
Proof.
  induction k as [|k IH]; intros Delta c Γ Hctx; simpl.
  - replace (c + 0) with c by lia. exact Hctx.
  - replace (c + S k) with (S (c + k)) by lia.
    apply ctx_schemas_lt_closed_from_bind_lt. apply IH. exact Hctx.
Qed.


Lemma ctor_fields_closed_push_match_bound : forall k D Γ,
  ctor_fields_closed Γ -> ctor_fields_closed (push_match_bound k D Γ).
Proof.
  induction k as [|k IH]; intros D Γ H; simpl; [exact H|].
  apply ctor_fields_closed_bind_lt. apply IH. exact H.
Qed.


Lemma Forall2_tm_ty_closed_from : forall Γ (vs : list term) (rhos : list type),
  Forall2 (fun v rho => forall c, ctx_ty_closed_from c Γ -> tm_ty_closed c v) vs rhos ->
  forall c, ctx_ty_closed_from c Γ ->
  (fix go (ts : list term) : Prop :=
     match ts with
     | [] => True
     | u :: rest => tm_ty_closed c u /\ go rest
     end) vs.
Proof.
  intros Γ vs rhos H. induction H; intros c Hctx; simpl.
  - exact I.
  - split.
    + apply H. exact Hctx.
    + apply IHForall2. exact Hctx.
Qed.

Lemma Forall2_tm_lt_closed_from : forall Γ (vs : list term) (rhos : list type),
  Forall2 (fun v rho => forall c, ctx_lt_closed_from c Γ -> tm_lt_closed c v) vs rhos ->
  forall c, ctx_lt_closed_from c Γ ->
  (fix go (ts : list term) : Prop :=
     match ts with
     | [] => True
     | u :: rest => tm_lt_closed c u /\ go rest
     end) vs.
Proof.
  intros Γ vs rhos H. induction H; intros c Hctx; simpl.
  - exact I.
  - split.
    + apply H. exact Hctx.
    + apply IHForall2. exact Hctx.
Qed.


Lemma typing_tm_ty_closed_from : forall Γ t T,
  Γ ⊢ₜ t : T -> forall c, ctx_ty_closed_from c Γ -> tm_ty_closed c t.
Proof.
  apply (typing_ind_forall2
    (fun Γ t T => forall c, ctx_ty_closed_from c Γ -> tm_ty_closed c t)).
  - intros Γ x T Hlk HwfT c Hctx. exact I.
  - intros Γ t T U Ht IH Hsub c Hctx. apply IH. exact Hctx.
  - intros Γ body A l B HwfA HwfB Hbody IHbody Hcap c Hctx. simpl.
    split.
    + apply IHbody. apply ctx_ty_closed_from_bind_tm. exact Hctx.
    + eapply ty_wf_ty_closed_from; eauto.
  - intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 c Hctx. simpl.
    split; [apply IH1|apply IH2]; exact Hctx.
  - intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody c Hctx. simpl.
    split.
    + eapply ty_wf_ty_closed_from; eauto.
    + apply IHbody. apply ctx_ty_closed_from_bind_ty. exact Hctx.
  - intros Γ t B U S Ht IH HwfS Hsub c Hctx. simpl.
    split.
    + apply IH. exact Hctx.
    + eapply ty_wf_ty_closed_from; eauto.
  - intros Γ body T HwfT HisAbs Hbody IHbody c Hctx. simpl.
    apply IHbody. apply ctx_ty_closed_from_bind_lt. exact Hctx.
  - intros Γ t T l Ht IH Hwfl c Hctx. simpl. apply IH. exact Hctx.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
           Hlk Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs Hresult Hshape
           Hresult_eff Hwfl Hlt Hforall Hlen_vs Hfields IHfields c Hctx.
    simpl. split.
    + eapply types_wf_ty_closed_from; eauto.
    + eapply Forall2_tm_ty_closed_from; eauto.
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γ' yes_body eta
           elim_result no_body HKne Hlk Heff Hlts Hrho Hlen_Ts HwfTs
           Hscrut_result Hscrut_shape Hresult_eff Hresult_ne HwfDelta Hresult_l Hscrut IHscrut
           Harity HGamma' Hyes IHyes Helim Hno IHno c Hctx.
    subst Γ'. simpl. repeat split.
    + apply IHscrut. exact Hctx.
    + apply IHyes. apply ctx_ty_closed_from_fold_bind_tm.
      apply ctx_ty_closed_from_push_match_bound. exact Hctx.
    + apply IHno. exact Hctx.
  - intros Γ E_tag m Ts op_bodies n_α ops T_R
           Heff Hlen HwfTs HwfTR Hfst Hops IHops c Hctx.
    simpl. repeat split.
    + eapply types_wf_ty_closed_from; eauto.
    + eapply ty_wf_ty_closed_from; eauto.
    + clear Hops Heff. revert Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IH]; intros Hfst; simpl.
      * exact I.
      * simpl in Hfst. injection Hfst as Hnb Hfstrest.
        destruct ob as [nb obt]. simpl in Hnb. subst nb.
        split; [| apply IH; exact Hfstrest].
        apply Hone. repeat apply ctx_ty_closed_from_bind_tm.
        apply ctx_ty_closed_from_push_ty_vars. exact Hctx.
  - intros Γ E_tag Ts op_bodies body n_α ops T_B T_R
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hfst Hops IHops Hbody IHbody c Hctx.
    simpl. repeat split.
    + eapply types_wf_ty_closed_from; eauto.
    + eapply ty_wf_ty_closed_from; eauto.
    + eapply ty_wf_ty_closed_from; eauto.
    + clear Hops Heff. revert Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IH]; intros Hfst; simpl.
      * exact I.
      * simpl in Hfst. injection Hfst as Hnb Hfstrest.
        destruct ob as [nb obt]. simpl in Hnb. subst nb.
        split; [| apply IH; exact Hfstrest].
        apply Hone. repeat apply ctx_ty_closed_from_bind_tm.
        apply ctx_ty_closed_from_push_ty_vars. exact Hctx.
    + apply IHbody. apply ctx_ty_closed_from_bind_tm. exact Hctx.
  - intros Γ recv op arg E_tag Delta Ts Ss n_α ops n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hnth Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg c Hctx.
    simpl. repeat split.
    + apply IHrecv. exact Hctx.
    + eapply types_wf_ty_closed_from; eauto.
    + eapply ty_wf_ty_closed_from; eauto.
    + apply IHarg. exact Hctx.
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH c Hctx. simpl.
    repeat split.
    + eapply ty_wf_ty_closed_from; eauto.
    + eapply ty_wf_ty_closed_from; eauto.
    + apply IH. exact Hctx.
Qed.

Lemma typing_tm_lt_closed_from : forall Γ t T,
  Γ ⊢ₜ t : T -> forall c, ctx_lt_closed_from c Γ -> tm_lt_closed c t.
Proof.
  apply (typing_ind_forall2
    (fun Γ t T => forall c, ctx_lt_closed_from c Γ -> tm_lt_closed c t)).
  - intros Γ x T Hlk HwfT c Hctx. exact I.
  - intros Γ t T U Ht IH Hsub c Hctx. apply IH. exact Hctx.
  - intros Γ body A l B HwfA HwfB Hbody IHbody Hcap c Hctx. simpl.
    split.
    + apply IHbody. apply ctx_lt_closed_from_bind_tm. exact Hctx.
    + eapply ty_wf_lt_closed_from; eauto.
  - intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 c Hctx. simpl.
    split; [apply IH1|apply IH2]; exact Hctx.
  - intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody c Hctx. simpl.
    split.
    + eapply ty_wf_lt_closed_from; eauto.
    + apply IHbody. apply ctx_lt_closed_from_bind_ty. exact Hctx.
  - intros Γ t B U S Ht IH HwfS Hsub c Hctx. simpl.
    split.
    + apply IH. exact Hctx.
    + eapply ty_wf_lt_closed_from; eauto.
  - intros Γ body T HwfT HisAbs Hbody IHbody c Hctx. simpl.
    apply IHbody. apply ctx_lt_closed_from_bind_lt. exact Hctx.
  - intros Γ t T l Ht IH Hwfl c Hctx. simpl.
    split.
    + apply IH. exact Hctx.
    + eapply lt_wf_closed_from; eauto.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
           Hlk Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs Hresult Hshape
           Hresult_eff Hwfl Hlt Hforall Hlen_vs Hfields IHfields c Hctx.
    simpl. repeat split.
    + eapply lt_wf_closed_from; eauto.
    + eapply lifetimes_wf_lt_closed_from; eauto.
    + eapply types_wf_lt_closed_from; eauto.
    + eapply Forall2_tm_lt_closed_from; eauto.
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γ' yes_body eta
           elim_result no_body HKne Hlk Heff Hlts Hrho Hlen_Ts HwfTs
           Hscrut_result Hscrut_shape Hresult_eff Hresult_ne HwfDelta Hresult_l Hscrut IHscrut
           Harity HGamma' Hyes IHyes Helim Hno IHno c Hctx.
    subst Γ'. simpl. repeat split.
    + apply IHscrut. exact Hctx.
    + apply IHyes. apply ctx_lt_closed_from_fold_bind_tm.
      apply ctx_lt_closed_from_push_match_bound. exact Hctx.
    + apply IHno. exact Hctx.
  - intros Γ E_tag m Ts op_bodies n_α ops T_R
           Heff Hlen HwfTs HwfTR Hfst Hops IHops c Hctx.
    simpl. repeat split.
    + eapply types_wf_lt_closed_from; eauto.
    + eapply ty_wf_lt_closed_from; eauto.
    + clear Hops Heff Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IH]; simpl.
      * exact I.
      * destruct ob as [nb obt].
        split; [| exact IH].
        apply Hone. repeat apply ctx_lt_closed_from_bind_tm.
        apply ctx_lt_closed_from_push_ty_vars. exact Hctx.
  - intros Γ E_tag Ts op_bodies body n_α ops T_B T_R
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hfst Hops IHops Hbody IHbody c Hctx.
    simpl. repeat split.
    + eapply types_wf_lt_closed_from; eauto.
    + eapply ty_wf_lt_closed_from; eauto.
    + eapply ty_wf_lt_closed_from; eauto.
    + clear Hops Heff Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IH]; simpl.
      * exact I.
      * destruct ob as [nb obt].
        split; [| exact IH].
        apply Hone. repeat apply ctx_lt_closed_from_bind_tm.
        apply ctx_lt_closed_from_push_ty_vars. exact Hctx.
    + apply IHbody. apply ctx_lt_closed_from_bind_tm. exact Hctx.
  - intros Γ recv op arg E_tag Delta Ts Ss n_α ops n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hnth Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg c Hctx.
    simpl. repeat split.
    + apply IHrecv. exact Hctx.
    + eapply types_wf_lt_closed_from; eauto.
    + eapply ty_wf_lt_closed_from; eauto.
    + apply IHarg. exact Hctx.
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH c Hctx. simpl.
    repeat split.
    + eapply ty_wf_lt_closed_from; eauto.
    + eapply ty_wf_lt_closed_from; eauto.
    + apply IH. exact Hctx.
Qed.

Lemma typing_eval_ctx_tm_ty_closed : forall Γ t T,
  eval_ctx Γ -> Γ ⊢ₜ t : T -> tm_ty_closed 0 t.
Proof.
  intros Γ t T Hec Hty. eapply typing_tm_ty_closed_from; [exact Hty|].
  apply eval_ctx_ty_closed_from. exact Hec.
Qed.

Lemma typing_eval_ctx_tm_lt_closed : forall Γ t T,
  eval_ctx Γ -> Γ ⊢ₜ t : T -> tm_lt_closed 0 t.
Proof.
  intros Γ t T Hec Hty. eapply typing_tm_lt_closed_from; [exact Hty|].
  apply eval_ctx_lt_closed_from. exact Hec.
Qed.
