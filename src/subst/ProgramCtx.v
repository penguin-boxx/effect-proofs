Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import ShiftLaws.
Require Import Weakening.
Require Import SubstLt.
Require Import SubstTy.

(* ================================================================== *)
(* Program-level typing contexts: the `eval_ctx` predicate (NOT       *)
(* `ectx`, the evaluation context in Semantics.v).                    *)
(*                                                                    *)
(* An `eval_ctx` contains ONLY constructor/effect bindings: no        *)
(* `bind_tm`, `bind_ty`, or `bind_lt`.  Consequently a term typed     *)
(* under an `eval_ctx` has no free term, type, or lifetime variables  *)
(* (it is fully closed).  This is exactly the invariant the term      *)
(* substitution lemma needs: the value being inlined is fully closed, *)
(* so the cross-binder shifts performed by `subst_tm` (which does NOT *)
(* re-shift the value across the lifetime/type binders introduced by  *)
(* `term_match` / `term_cap` / `term_handle`) act as the identity and *)
(* the statement is sound.                                            *)
(*                                                                    *)
(* `eval_ctx` lives here (rather than in the safety tier) so that     *)
(* the term-substitution payload ([typing_SubstTm], SubstTm.v) can be *)
(* stated directly in terms of the real program-level invariant.      *)
(* ================================================================== *)
Inductive eval_ctx : ctx -> Prop :=
  | ec_nil   : eval_ctx []
  | ec_ctor  : forall K n_lt n_ty f r Γ,
      tys_lt_closed n_lt f ->
      ty_lt_closed n_lt r ->
      tys_ty_closed n_ty f ->
      eval_ctx Γ -> eval_ctx (bind_ctor K n_lt n_ty f r :: Γ)
  | ec_eff   : forall E n_α ops Γ,
      E <> any_tag ->
      Forall (fun osig => ty_lt_closed 0 (op_sig_ty osig) /\
                          ty_lt_closed 0 (op_ret_ty osig)) ops ->
      eval_ctx Γ -> eval_ctx (bind_eff E n_α ops :: Γ).

Lemma eval_ctx_no_tm : forall Γ x,
  eval_ctx Γ -> ctx_lookup_tm Γ x = None.
Proof.
  intros Γ x H; revert x; induction H; intros x; simpl; try reflexivity.
  - rewrite IHeval_ctx; reflexivity.
  - rewrite IHeval_ctx; reflexivity.
Qed.

Lemma eval_ctx_no_ty : forall Γ α,
  eval_ctx Γ -> ctx_lookup_ty Γ α = None.
Proof.
  intros Γ α H; revert α; induction H; intros α; simpl; try reflexivity.
  - rewrite IHeval_ctx; reflexivity.
  - rewrite IHeval_ctx; reflexivity.
Qed.

Lemma eval_ctx_no_lt : forall Γ x,
  eval_ctx Γ -> ctx_lookup_lt Γ x = None.
Proof.
  intros Γ x H; revert x; induction H; intros x; simpl; try reflexivity.
  - rewrite IHeval_ctx; reflexivity.
  - rewrite IHeval_ctx; reflexivity.
Qed.

Lemma fv_succ : forall t c y,
  In y (free_tm_vars (S c) t) -> In (S y) (free_tm_vars c t).
Proof.
  apply (term_list_ind
    (fun t => forall c y, In y (free_tm_vars (S c) t) -> In (S y) (free_tm_vars c t))
    (fun ts => forall c y,
       In y (List.concat (List.map (free_tm_vars (S c)) ts)) ->
       In (S y) (List.concat (List.map (free_tm_vars c) ts)))
    (fun obs => forall c y,
       In y (List.concat (List.map (fun p => free_tm_vars (S c) (snd p)) obs)) ->
       In (S y) (List.concat (List.map (fun p => free_tm_vars c (snd p)) obs)))).
  - intros x c y. simpl.
    destruct (Nat.ltb x (S c)) eqn:E1.
    + intros [].
    + apply Nat.ltb_ge in E1.
      assert (E2 : Nat.ltb x c = false) by (apply Nat.ltb_ge; lia).
      rewrite E2. simpl. intros [Hy | []]. subst y. left. lia.
  - intros t1 t2 IH1 IH2 c y. simpl. rewrite !List.in_app_iff.
    intros [H|H]; [left; apply IH1; exact H | right; apply IH2; exact H].
  - intros body T IH c y. simpl. apply IH.
  - intros t T IH c y. simpl. apply IH.
  - intros bound body IH c y. simpl. apply IH.
  - intros t l IH c y. simpl. apply IH.
  - intros body IH c y. simpl. apply IH.
  - intros K l lts Ts ts IH c y. simpl.
    apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn c y. simpl.
    rewrite !List.in_app_iff. intros [H|[H|H]].
    + left. apply IHs. exact H.
    + right; left. apply IHy. exact H.
    + right; right. apply IHn. exact H.
  - intros E Ts T_B T_R op_bodies body IHops IHb c y. simpl.
    rewrite !free_tm_vars_ops_eq_concat.
    rewrite !List.in_app_iff. intros [H|H].
    + left. apply IHops. exact H.
    + right. apply IHb. exact H.
  - intros t op Ss A_ret arg IHt IHa c y. simpl.
    rewrite !List.in_app_iff. intros [H|H]; [left; apply IHt; exact H | right; apply IHa; exact H].
  - intros E m Ts T_R op_bodies IHops c y. simpl.
    rewrite !free_tm_vars_ops_eq_concat. apply IHops.
  - intros m T_B T_R t IH c y. simpl. apply IH.
  - intros c y. simpl. intros [].
  - intros t ts IHt IHts c y. simpl.
    rewrite !List.in_app_iff. intros [H|H]; [left; apply IHt; exact H | right; apply IHts; exact H].
  - intros c y. simpl. intros [].
  - intros nb ob obs IHob IHobs c y. simpl.
    rewrite !List.in_app_iff. intros [H|H]; [left; apply IHob; exact H | right; apply IHobs; exact H].
Qed.

Lemma fv_add : forall k t c y,
  In y (free_tm_vars (c + k) t) -> In (y + k) (free_tm_vars c t).
Proof.
  induction k as [|k IH]; intros t c y Hin.
  - rewrite Nat.add_0_r in Hin. rewrite Nat.add_0_r. exact Hin.
  - replace (c + S k) with (S (c + k)) in Hin by lia.
    apply fv_succ in Hin.
    apply IH in Hin.
    replace (y + S k) with (S y + k) by lia.
    exact Hin.
Qed.

(* [ctx_lookup_tm] ignores bind_lt bounds, so [push_match_bound] behaves      *)
(* identically to [push_lt_vars] for term-variable lookups.            *)
Lemma lookup_tm_push_match_bound_None : forall n Delta Γ x,
  ctx_lookup_tm Γ x = None ->
  ctx_lookup_tm (push_match_bound n Delta Γ) x = None.
Proof.
  induction n as [|n IH]; intros Delta Γ x H; simpl.
  - exact H.
  - rewrite IH by exact H. reflexivity.
Qed.


Lemma lookup_tm_push_ty_None : forall n bound Γ x,
  ctx_lookup_tm Γ x = None ->
  ctx_lookup_tm (push_ty_vars n bound Γ) x = None.
Proof.
  induction n as [|n IH]; intros bound Γ x H; simpl.
  - exact H.
  - apply IH. simpl. rewrite H. reflexivity.
Qed.

Lemma ctx_lookup_tm_push_ty_vars : forall n bound Γ x,
  ctx_lookup_tm (push_ty_vars n bound Γ) x =
  option_map (shift_ty n 0) (ctx_lookup_tm Γ x).
Proof.
  induction n as [|n IH]; intros bound Γ x; simpl.
  - destruct (ctx_lookup_tm Γ x) as [T|]; simpl;
      [rewrite shift_ty_zero|]; reflexivity.
  - rewrite IH. simpl.
    destruct (ctx_lookup_tm Γ x) as [T|]; simpl; [|reflexivity].
    rewrite shift_ty_fuse.
    replace (n + 1) with (S n) by lia.
    reflexivity.
Qed.

Lemma lookup_tm_skip_bind_tm_many : forall rhos Γ x,
  ctx_lookup_tm (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos)
                (x + List.length rhos)
  = ctx_lookup_tm Γ x.
Proof.
  induction rhos as [|rho rhos IH]; intros Γ x.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - cbn [fold_right List.length].
    replace (x + S (List.length rhos)) with (S (x + List.length rhos)) by lia.
    cbn [ctx_lookup_tm]. apply IH.
Qed.

Lemma typing_fv_bound : forall Γ t T,
  Γ ⊢ₜ t : T ->
  forall x, In x (free_tm_vars 0 t) -> ctx_lookup_tm Γ x <> None.
Proof.
  apply (typing_ind_forall2
    (fun Γ t T => forall x, In x (free_tm_vars 0 t) -> ctx_lookup_tm Γ x <> None)).
  - intros Γ x T Hlk HwfT y Hin. simpl in Hin. rewrite Nat.sub_0_r in Hin.
    destruct Hin as [Hy | []]. subst y. rewrite Hlk. discriminate.
  - intros Γ t T U Ht IH Hsub x Hin. apply IH. exact Hin.
  - intros Γ body A l B HwfA HwfB Hbody IH Hcap x Hin.
    simpl in Hin. apply fv_succ in Hin. specialize (IH (S x) Hin).
    simpl in IH. exact IH.
  - intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 x Hin.
    simpl in Hin. rewrite List.in_app_iff in Hin.
    destruct Hin as [H|H]; [apply IH1 | apply IH2]; exact H.
  - intros Γ bound body T HwfBound HwfT HisAbs Hbody IH x Hin.
    simpl in Hin. specialize (IH x Hin).
    intros Hnone. apply IH. simpl. rewrite Hnone. reflexivity.
  - intros Γ t B U S Ht IH HwfS Hsub x Hin. apply IH. exact Hin.
  - intros Γ body T HwfT HisAbs Hbody IH x Hin.
    simpl in Hin. specialize (IH x Hin).
    intros Hnone. apply IH. simpl. rewrite Hnone. reflexivity.
  - intros Γ t T l Ht IH Hwfl x Hin. apply IH. exact Hin.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
           Hlk Heff Hlts HwfLts Hrho HTs HwfTs Hres Hshape Hresult_eff Hwfl Hltsub Hforall
           Hvslen Hf2ty Hf2IH x Hin.
    clear - Hf2IH Hin.
    revert Hin. induction Hf2IH as [|v rho vs0 rhos0 Hp Hf2P' IH]; intros Hin.
    + simpl in Hin. contradiction.
    + simpl in Hin. rewrite List.in_app_iff in Hin.
      destruct Hin as [H|H]; [apply Hp; exact H | apply IH; exact H].
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γ' yes_body eta
           elim_result no_body
           HKne Hlk Heff Hlts Hrho HTs HwfTs Hsrt Hshape Hresult_eff Hrtne HwfDelta Hrl Hscrut IHscrut
           Harity HΓ' Hyes IHyes Helim Hno IHno x Hin.
    simpl in Hin. rewrite !List.in_app_iff in Hin.
    destruct Hin as [Hs | [Hy | Hn]].
    + apply IHscrut. exact Hs.
    + apply (fv_add arity yes_body 0 x) in Hy.
      specialize (IHyes (x + arity) Hy). subst Γ'.
      rewrite Harity in IHyes.
      rewrite lookup_tm_skip_bind_tm_many in IHyes.
      intros Hnone. apply IHyes. apply lookup_tm_push_match_bound_None. exact Hnone.
    + apply IHno. exact Hn.
  - intros Γ E_tag m Ts op_bodies n_α ops T_R
           Heff Hlen HwfTs HwfTR Hfst Hops IHops x Hin.
    simpl in Hin.
    rewrite free_tm_vars_ops_eq_concat in Hin.
    clear - IHops Hin.
    revert Hin. induction IHops as [|ob osig obs' ops' Hp Hrest IH]; intros Hin.
    + simpl in Hin. contradiction.
    + simpl in Hin. rewrite List.in_app_iff in Hin.
      destruct Hin as [H|H]; [| apply IH; exact H].
      apply (fv_add 2 (snd ob) 0 x) in H.
      specialize (Hp (x + 2) H).
      replace (x + 2) with (S (S x)) in Hp by lia. simpl in Hp.
      intros Hnone. apply Hp. apply lookup_tm_push_ty_None. exact Hnone.
  - intros Γ E_tag Ts op_bodies body n_α ops T_B T_R
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hfst Hops IHops Hbody IHbody x Hin.
    simpl in Hin.
    rewrite free_tm_vars_ops_eq_concat in Hin.
    rewrite List.in_app_iff in Hin. destruct Hin as [HopsFree | HbodyFree].
    + clear - IHops HopsFree.
      revert HopsFree. induction IHops as [|ob osig obs' ops' Hp Hrest IH]; intros Hin.
      * simpl in Hin. contradiction.
      * simpl in Hin. rewrite List.in_app_iff in Hin.
        destruct Hin as [H|H]; [| apply IH; exact H].
        apply (fv_add 2 (snd ob) 0 x) in H.
        specialize (Hp (x + 2) H).
        replace (x + 2) with (S (S x)) in Hp by lia. simpl in Hp.
        intros Hnone. apply Hp. apply lookup_tm_push_ty_None. exact Hnone.
    + apply fv_succ in HbodyFree. specialize (IHbody (S x) HbodyFree).
      simpl in IHbody. exact IHbody.
  - intros Γ recv op arg E_tag Delta Ts Ss n_α ops n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hnth Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg x Hin.
    simpl in Hin. rewrite List.in_app_iff in Hin.
    destruct Hin as [H|H]; [apply IHrecv | apply IHarg]; exact H.
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH x Hin. apply IH. exact Hin.
Qed.

Lemma typing_closed : forall Γ t T,
  eval_ctx Γ -> Γ ⊢ₜ t : T -> free_tm_vars 0 t = [].
Proof.
  intros Γ t T Hec Hty.
  destruct (free_tm_vars 0 t) as [|x xs] eqn:E.
  - reflexivity.
  - exfalso.
    assert (Hin : In x (free_tm_vars 0 t)) by (rewrite E; left; reflexivity).
    apply (typing_fv_bound Γ t T Hty x) in Hin.
    apply Hin. apply eval_ctx_no_tm. exact Hec.
Qed.

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


(* The reserved Any tag is never registered as an effect in an        *)
(* `eval_ctx`: `ec_eff` forbids `E = any_tag`.                         *)
Lemma eval_ctx_no_eff_any : forall Γ,
  eval_ctx Γ -> ctx_lookup_eff Γ any_tag = None.
Proof.
  intros Γ H; induction H.
  - reflexivity.
  - cbn [ctx_lookup_eff]. exact IHeval_ctx.
  - cbn [ctx_lookup_eff].
    assert (Nat.eqb any_tag E = false) as ->.
    { apply Nat.eqb_neq. congruence. }
    exact IHeval_ctx.
Qed.

Lemma typing_implies_wf : forall Γ t T,
  Γ ⊢ₜ t : T -> ty_wf Γ T.
Proof.
  apply (typing_ind_forall2 (fun Γ t T => ty_wf Γ T)).
  - intros Γ x T Hlk HwfT. exact HwfT.
  - intros Γ t T U Ht IH Hsub.
    destruct (sub_wf _ _ _ Hsub) as [_ HwfU]. exact HwfU.
  - intros Γ body A l B HwfA HwfB Hbody IH Hcap.
    destruct (lt_sub_wf _ _ _ Hcap) as [_ Hwfl]. constructor; assumption.
  - intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2.
    inversion IH1; subst. assumption.
  - intros Γ bound body T HwfBound HwfT Hbody IHbody.
    constructor; assumption.
  - intros Γ t B U S Ht IH HwfS Hsub.
    inversion IH; subst.
    eapply ty_wf_SubstTy; [exact H3|]. apply SubstTy_here. exact Hsub.
  - intros Γ body T HwfT Hbody IHbody.
    constructor. exact HwfT.
  - intros Γ t T l Ht IH Hwfl.
    inversion IH; subst.
    eapply ty_wf_SubstLt; [exact H1|].
    apply SubstLt_here. apply LS_Local. exact Hwfl.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
           Hlk Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs Hresult Hshape
           Hresult_eff Hwfl Hlt Hforall Hlen_vs Hfields IHfields.
            rewrite Hshape. constructor; assumption.
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γ' yes_body eta
           elim_result no_body HKne Hlk Heff Hlts Hrho Hlen_Ts HwfTs
           Hscrut_result Hscrut_shape Hresult_eff Hresult_ne HwfDelta Hresult_l Hscrut IHscrut
           Harity HGamma' Hyes IHyes Helim Hno IHno.
    exact IHno.
  - intros Γ E_tag m Ts op_bodies n_α ops T_R
           Heff Hlen HwfTs HwfTR Hfst Hops IHops.
    constructor; [constructor|exact HwfTs].
  - intros Γ E_tag Ts op_bodies body n_α ops T_B T_R
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hfst Hops IHops Hbody IHbody.
    exact HwfTR.
  - intros Γ recv op arg E_tag Δ Ts Ss n_α ops n_β sig ret sig_inst ret_inst
      Hrecv IHrecv Heff Hnth Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg.
    exact HwfRet.
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH. exact HwfTR.
Qed.


Lemma typing_weaken_ty_shift : forall Γ B t T,
  Γ ⊢ₜ t : T ->
  (bind_ty B :: Γ) ⊢ₜ shift_ty_in_tm 1 0 t : shift_ty 1 0 T.
Proof.
  intros Γ B t T Hty.
  eapply (typing_InsTy Γ t T Hty 0 (bind_ty B :: Γ)).
  apply InsTy_here.
Qed.

Lemma typing_push_ty_vars_shift : forall Γ t T,
  Γ ⊢ₜ t : T ->
  forall k B,
    push_ty_vars k B Γ ⊢ₜ shift_ty_in_tm k 0 t : shift_ty k 0 T.
Proof.
  intros Γ t T Hty k. revert Γ t T Hty.
  induction k as [|k IH]; intros Γ t T Hty B; simpl.
  - rewrite shift_ty_in_tm_zero, shift_ty_zero. exact Hty.
  - pose proof (typing_weaken_ty_shift Γ B t T Hty) as Hone.
    assert (Hstep : push_ty_vars k B (bind_ty B :: Γ) ⊢ₜ
      shift_ty_in_tm k 0 (shift_ty_in_tm 1 0 t) :
      shift_ty k 0 (shift_ty 1 0 T)).
    { apply (IH (bind_ty B :: Γ) (shift_ty_in_tm 1 0 t) (shift_ty 1 0 T) Hone B). }
    replace (shift_ty_in_tm k 0 (shift_ty_in_tm 1 0 t))
      with (shift_ty_in_tm (S k) 0 t) in Hstep.
    2:{ rewrite shift_ty_in_tm_fuse. replace (k + 1) with (S k) by lia. reflexivity. }
    replace (shift_ty k 0 (shift_ty 1 0 T))
      with (shift_ty (S k) 0 T) in Hstep.
    2:{ rewrite shift_ty_fuse. replace (k + 1) with (S k) by lia. reflexivity. }
    exact Hstep.
Qed.
