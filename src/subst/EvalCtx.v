Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import ShiftLaws.
Require Import Insertions.
Require Import SubstLt.
Require Import SubstTy.
Require Import SubstTm.

(* ================================================================== *)
(* Evaluation contexts (program-level typing contexts).               *)
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
(* `eval_ctx` lives here (rather than in `Safety.v`) so that          *)
(* `subst_tm_lemma` can be stated directly in terms of the real       *)
(* program-level invariant.                                           *)
(* ================================================================== *)
Inductive eval_ctx : ctx -> Prop :=
  | ec_nil   : eval_ctx []
  | ec_ctor  : forall K n_lt n_ty f r Γ,
      tys_lt_closed n_lt f ->
      ty_lt_closed n_lt r ->
      tys_ty_closed n_ty f ->
      eval_ctx Γ -> eval_ctx (bind_ctor K n_lt n_ty f r :: Γ)
  | ec_eff   : forall E n_α n_β sig ret Γ,
      E <> any_tag ->
      ty_lt_closed 0 sig ->
      ty_lt_closed 0 ret ->
      eval_ctx Γ -> eval_ctx (bind_eff E n_α n_β sig ret :: Γ).

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
       In (S y) (List.concat (List.map (free_tm_vars c) ts)))).
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
    rewrite !free_tm_vars_go_eq_concat. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn c y. simpl.
    rewrite !List.in_app_iff. intros [H|[H|H]].
    + left. apply IHs. exact H.
    + right; left. apply IHy. exact H.
    + right; right. apply IHn. exact H.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb c y. simpl.
    rewrite !List.in_app_iff. intros [H|H].
    + left. apply IHop. exact H.
    + right. apply IHb. exact H.
  - intros t Ss arg IHt IHa c y. simpl.
    rewrite !List.in_app_iff. intros [H|H]; [left; apply IHt; exact H | right; apply IHa; exact H].
  - intros E m n_beta Ts T_R op_body IHop c y. simpl. apply IHop.
  - intros m T_B T_R t IH c y. simpl. apply IH.
  - intros m T_B T_R b IH c y. simpl. apply IH.
  - intros c y. simpl. intros [].
  - intros t ts IHt IHts c y. simpl.
    rewrite !List.in_app_iff. intros [H|H]; [left; apply IHt; exact H | right; apply IHts; exact H].
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

Lemma lookup_tm_push_lt_None : forall n bound Γ x,
  ctx_lookup_tm Γ x = None ->
  ctx_lookup_tm (push_lt_vars n bound Γ) x = None.
Proof.
  induction n as [|n IH]; intros bound Γ x H; simpl.
  - exact H.
  - apply IH. simpl. rewrite H. reflexivity.
Qed.

Lemma ctx_lookup_tm_push_lt_vars : forall n bound Γ x,
  ctx_lookup_tm (push_lt_vars n bound Γ) x =
  option_map (shift_lt_in_ty n 0) (ctx_lookup_tm Γ x).
Proof.
  induction n as [|n IH]; intros bound Γ x; simpl.
  - destruct (ctx_lookup_tm Γ x) as [T|]; simpl;
      [rewrite shift_lt_in_ty_zero|]; reflexivity.
  - rewrite IH. simpl.
    destruct (ctx_lookup_tm Γ x) as [T|]; simpl; [|reflexivity].
    rewrite shift_lt_in_ty_fuse.
    replace (n + 1) with (S n) by lia.
    reflexivity.
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
  - intros Γ t B U S Ht IH HwfS Hsub HnlArg x Hin. apply IH. exact Hin.
  - intros Γ body T HwfT HisAbs Hbody IH x Hin.
    simpl in Hin. specialize (IH x Hin).
    intros Hnone. apply IH. simpl. rewrite Hnone. reflexivity.
  - intros Γ t T l Ht IH Hwfl x Hin. apply IH. exact Hin.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
           Hlk Heff Hlts HwfLts Hrho HTs HwfTs Hres Hshape Hresult_eff Hwfl Hltsub Hforall
           Hvslen Hf2ty Hf2IH x Hin.
    change (In x ((fix go ts :=
      match ts with
      | [] => []
      | u :: rest => free_tm_vars 0 u ++ go rest
      end) vs)) in Hin.
    rewrite free_tm_vars_go_eq_concat in Hin.
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
      intros Hnone. apply IHyes. apply lookup_tm_push_lt_None. exact Hnone.
    + apply IHno. exact Hn.
  - intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff Hlen HwfTs HwfTR Hsig Hret Hop IHop x Hin.
    simpl in Hin. apply (fv_add 2 op_body 0 x) in Hin.
    specialize (IHop (x + 2) Hin).
    replace (x + 2) with (S (S x)) in IHop by lia. simpl in IHop.
    intros Hnone. apply IHop. apply lookup_tm_push_ty_None. exact Hnone.
  - intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hsig Hret Hop IHop Hbody IHbody x Hin.
    simpl in Hin. rewrite List.in_app_iff in Hin. destruct Hin as [HopFree | HbodyFree].
    + apply (fv_add 2 op_body 0 x) in HopFree. specialize (IHop (x + 2) HopFree).
      replace (x + 2) with (S (S x)) in IHop by lia. simpl in IHop.
      intros Hnone. apply IHop. apply lookup_tm_push_ty_None. exact Hnone.
    + apply fv_succ in HbodyFree. specialize (IHbody (S x) HbodyFree).
      simpl in IHbody. exact IHbody.
  - intros Γ recv arg E_tag Delta Ts Ss n_α n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg x Hin.
    simpl in Hin. rewrite List.in_app_iff in Hin.
    destruct Hin as [H|H]; [apply IHrecv | apply IHarg]; exact H.
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH x Hin. apply IH. exact Hin.
  - intros Γ m b A T_B T_R HwfA HwfTB HwfTR HnoLocal Hsub Hb IH x Hin.
    simpl in Hin. apply fv_succ in Hin. specialize (IH (S x) Hin).
    simpl in IH. exact IH.
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
       |E0 n_α n_β sig ret Γ Hne Hsig Hret Hec IH]; intro Hlk; simpl in Hlk.
  - discriminate.
  - destruct (Nat.eqb K K0) eqn:Heq.
    + inversion Hlk; subst. split; assumption.
    + apply IH. exact Hlk.
  - apply IH. exact Hlk.
Qed.

Lemma eval_ctx_lookup_eff_lt_closed : forall Γ E n_α n_β sig ret,
  eval_ctx Γ ->
  ctx_lookup_eff Γ E = Some (n_α, n_β, sig, ret) ->
  ty_lt_closed 0 sig /\ ty_lt_closed 0 ret.
Proof.
  intros Γ E n_α n_β sig ret Hec.
  induction Hec as
      [|K0 n_lt n_ty fields result Γ Hfields Hresult Htyc Hec IH
       |E0 n_α0 n_β0 sig0 ret0 Γ Hne Hsig0 Hret0 Hec IH]; intro Hlk; simpl in Hlk.
  - discriminate.
  - apply IH. exact Hlk.
  - destruct (Nat.eqb E E0) eqn:Heq.
    + inversion Hlk; subst. split; assumption.
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
       |E0 n_α n_β sig ret Γ Hne Hsig Hret Hec IH]; intro Hlk; simpl in Hlk.
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

Lemma ctor_fields_closed_push_lt_vars : forall k D Γ,
  ctor_fields_closed Γ -> ctor_fields_closed (push_lt_vars k D Γ).
Proof.
  induction k; intros D Γ H; simpl; [exact H|].
  apply IHk. apply ctor_fields_closed_bind_lt. exact H.
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

Lemma InsLt_lookup_ctor_eval_ctx_closed : forall Γ Γ' c K n_lt n_ty fields result,
  eval_ctx Γ ->
  InsLt c Γ Γ' ->
  ctx_lookup_ctor Γ K = Some (n_lt, n_ty, fields, result) ->
  ctx_lookup_ctor Γ' K = Some (n_lt, n_ty, fields, result).
Proof.
  intros Γ Γ' c K n_lt n_ty fields result Hec HIns Hlk.
  rewrite (InsLt_lookup_ctor c Γ Γ' HIns K). rewrite Hlk. cbn [option_map].
  destruct (eval_ctx_lookup_ctor_lt_closed Γ K n_lt n_ty fields result Hec Hlk) as [Hfields Hresult].
  rewrite (shift_lt_ctor_sig_closed n_lt n_ty fields result c Hfields Hresult).
  reflexivity.
Qed.

Lemma InsLt_lookup_eff_eval_ctx_closed : forall Γ Γ' c E n_α n_β sig ret,
  eval_ctx Γ ->
  InsLt c Γ Γ' ->
  ctx_lookup_eff Γ E = Some (n_α, n_β, sig, ret) ->
  ctx_lookup_eff Γ' E = Some (n_α, n_β, sig, ret).
Proof.
  intros Γ Γ' c E n_α n_β sig ret Hec HIns Hlk.
  rewrite (InsLt_lookup_eff c Γ Γ' HIns E). rewrite Hlk. cbn [option_map].
  destruct (eval_ctx_lookup_eff_lt_closed Γ E n_α n_β sig ret Hec Hlk) as [Hsig Hret].
  rewrite (shift_lt_eff_sig_closed n_α n_β sig ret c Hsig Hret).
  reflexivity.
Qed.

Definition ctx_ctor_schemas_lt_closed_from (c : nat) (Γ : ctx) : Prop :=
  forall K n_lt n_ty fields result,
    ctx_lookup_ctor Γ K = Some (n_lt, n_ty, fields, result) ->
    tys_lt_closed (n_lt + c) fields /\ ty_lt_closed (n_lt + c) result.

Definition ctx_eff_schemas_lt_closed_from (c : nat) (Γ : ctx) : Prop :=
  forall E n_α n_β sig ret,
    ctx_lookup_eff Γ E = Some (n_α, n_β, sig, ret) ->
    ty_lt_closed c sig /\ ty_lt_closed c ret.

Definition ctx_schemas_lt_closed_from (c : nat) (Γ : ctx) : Prop :=
  ctx_ctor_schemas_lt_closed_from c Γ /\ ctx_eff_schemas_lt_closed_from c Γ.

Lemma eval_ctx_schemas_lt_closed_from : forall Γ,
  eval_ctx Γ -> ctx_schemas_lt_closed_from 0 Γ.
Proof.
  intros Γ Hec. split.
  - intros K n_lt n_ty fields result Hlk.
    destruct (eval_ctx_lookup_ctor_lt_closed Γ K n_lt n_ty fields result Hec Hlk) as [Hfields Hresult].
    replace (n_lt + 0) with n_lt by lia. split; assumption.
  - intros E n_α n_β sig ret Hlk.
    eapply eval_ctx_lookup_eff_lt_closed; eauto.
Qed.

Lemma ctx_schemas_lt_closed_from_bind_tm : forall c Γ A,
  ctx_schemas_lt_closed_from c Γ ->
  ctx_schemas_lt_closed_from c (bind_tm A :: Γ).
Proof.
  intros c Γ A [Hctor Heff]. split.
  - intros K n_lt n_ty fields result Hlk. simpl in Hlk. eapply Hctor; eauto.
  - intros E n_α n_β sig ret Hlk. simpl in Hlk. eapply Heff; eauto.
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
  - intros E n_α n_β sig ret Hlk. simpl in Hlk.
    destruct (ctx_lookup_eff Γ E) as [[[[n_α0 n_β0] sig0] ret0]|] eqn:Hbase; [|discriminate].
    destruct (Heff E n_α0 n_β0 sig0 ret0 Hbase) as [Hsig Hret].
    inversion Hlk; subst; clear Hlk.
    split.
    + apply ty_lt_closed_shift_ty. exact Hsig.
    + apply ty_lt_closed_shift_ty. exact Hret.
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
  - intros E n_α n_β sig ret Hlk. simpl in Hlk.
    destruct (ctx_lookup_eff Γ E) as [[[[n_α0 n_β0] sig0] ret0]|] eqn:Hbase; [|discriminate].
    destruct (Heff E n_α0 n_β0 sig0 ret0 Hbase) as [Hsig Hret].
    inversion Hlk; subst; clear Hlk.
    replace (S c) with (1 + c) by lia.
    split.
    + eapply ty_lt_closed_shift_lt_below; [lia|exact Hsig].
    + eapply ty_lt_closed_shift_lt_below; [lia|exact Hret].
Qed.

Lemma ctx_schemas_lt_closed_from0_bind_lt : forall Γ D,
  ctx_schemas_lt_closed_from 0 Γ ->
  ctx_schemas_lt_closed_from 0 (bind_lt D :: Γ).
Proof.
  intros Γ D [Hctor Heff]. split.
  - intros K n_lt n_ty fields result Hlk. simpl in Hlk.
    destruct (ctx_lookup_ctor Γ K) as [[[[n_lt0 n_ty0] fields0] result0]|] eqn:Hbase; [|discriminate].
    destruct (Hctor K n_lt0 n_ty0 fields0 result0 Hbase) as [Hfields Hresult].
    inversion Hlk; subst; clear Hlk.
    replace (n_lt + 0) with n_lt in Hfields by lia.
    replace (n_lt + 0) with n_lt in Hresult by lia.
    replace (n_lt + 0) with n_lt by lia.
    split.
    + change (List.map (shift_lt_in_ty 1 n_lt) fields0)
      with (shift_lt_in_ty_list 1 n_lt fields0).
      rewrite shift_lt_in_ty_list_closed by exact Hfields. exact Hfields.
    + rewrite shift_lt_in_type_closed by exact Hresult. exact Hresult.
  - intros E n_α n_β sig ret Hlk. simpl in Hlk.
    destruct (ctx_lookup_eff Γ E) as [[[[n_α0 n_β0] sig0] ret0]|] eqn:Hbase; [|discriminate].
    destruct (Heff E n_α0 n_β0 sig0 ret0 Hbase) as [Hsig Hret].
    inversion Hlk; subst; clear Hlk.
    split.
    + rewrite shift_lt_in_type_closed by exact Hsig. exact Hsig.
    + rewrite shift_lt_in_type_closed by exact Hret. exact Hret.
Qed.

Lemma ctx_schemas_lt_closed_from0_push_lt_vars : forall k Delta Γ,
  ctx_schemas_lt_closed_from 0 Γ ->
  ctx_schemas_lt_closed_from 0 (push_lt_vars k Delta Γ).
Proof.
  induction k as [|k IH]; intros Delta Γ Hctx; simpl.
  - exact Hctx.
  - apply IH. apply ctx_schemas_lt_closed_from0_bind_lt. exact Hctx.
Qed.

Lemma ctx_schemas_lt_closed_from_push_lt_vars : forall k Delta c Γ,
  ctx_schemas_lt_closed_from c Γ ->
  ctx_schemas_lt_closed_from (c + k) (push_lt_vars k Delta Γ).
Proof.
  induction k as [|k IH]; intros Delta c Γ Hctx; simpl.
  - replace (c + 0) with c by lia. exact Hctx.
  - replace (c + S k) with (S c + k) by lia.
    apply IH. apply ctx_schemas_lt_closed_from_bind_lt. exact Hctx.
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

Lemma InsLt_lookup_ctor_schemas_closed : forall Γ Γ' c K n_lt n_ty fields result,
  ctx_schemas_lt_closed_from c Γ ->
  InsLt c Γ Γ' ->
  ctx_lookup_ctor Γ K = Some (n_lt, n_ty, fields, result) ->
  ctx_lookup_ctor Γ' K = Some (n_lt, n_ty, fields, result).
Proof.
  intros Γ Γ' c K n_lt n_ty fields result [Hctor _] HIns Hlk.
  rewrite (InsLt_lookup_ctor c Γ Γ' HIns K). rewrite Hlk. cbn [option_map].
  destruct (Hctor K n_lt n_ty fields result Hlk) as [Hfields Hresult].
  rewrite (shift_lt_ctor_sig_closed_from n_lt n_ty fields result c Hfields Hresult).
  reflexivity.
Qed.

Lemma InsLt_lookup_eff_schemas_closed : forall Γ Γ' c E n_α n_β sig ret,
  ctx_schemas_lt_closed_from c Γ ->
  InsLt c Γ Γ' ->
  ctx_lookup_eff Γ E = Some (n_α, n_β, sig, ret) ->
  ctx_lookup_eff Γ' E = Some (n_α, n_β, sig, ret).
Proof.
  intros Γ Γ' c E n_α n_β sig ret [_ Heff] HIns Hlk.
  rewrite (InsLt_lookup_eff c Γ Γ' HIns E). rewrite Hlk. cbn [option_map].
  destruct (Heff E n_α n_β sig ret Hlk) as [Hsig Hret].
  rewrite (shift_lt_eff_sig_closed_from n_α n_β sig ret c Hsig Hret).
  reflexivity.
Qed.

Definition ctx_ty_closed_from (c : nat) (Γ : ctx) : Prop :=
  forall x, c <= x -> ctx_lookup_ty Γ x = None.

Definition ctx_lt_closed_from (c : nat) (Γ : ctx) : Prop :=
  forall x, c <= x -> ctx_lookup_lt Γ x = None.

Lemma SubstLt_ctx_lt_closed_from_absurd : forall R n G G',
  SubstLt R n G G' ->
  ctx_lt_closed_from n G -> False.
Proof.
  intros R n G G' HSub Hclosed.
  destruct (SubstLt_lookup_lt_removed R n G G' HSub) as [Delta Hlk].
  rewrite (Hclosed n (Nat.le_refl n)) in Hlk. discriminate.
Qed.

Definition ctx_tm_lt_closed_from (c : nat) (Γ : ctx) : Prop :=
  forall x T, ctx_lookup_tm Γ x = Some T -> ty_lt_closed c T.

Definition ctx_ty_bound_lt_closed_from (c : nat) (Γ : ctx) : Prop :=
  forall x T, ctx_lookup_ty Γ x = Some T -> ty_lt_closed c T.

Definition ctx_tm_ty_closed_from (c : nat) (Γ : ctx) : Prop :=
  forall x T, ctx_lookup_tm Γ x = Some T -> ty_ty_closed c T.

Definition ctx_ty_bound_ty_closed_from (c : nat) (Γ : ctx) : Prop :=
  forall x T, ctx_lookup_ty Γ x = Some T -> ty_ty_closed c T.

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

Lemma eval_ctx_tm_lt_closed_from : forall c Γ,
  eval_ctx Γ -> ctx_tm_lt_closed_from c Γ.
Proof.
  intros c Γ Hec x T Hlk.
  rewrite (eval_ctx_no_tm Γ x Hec) in Hlk. discriminate.
Qed.

Lemma eval_ctx_ty_bound_lt_closed_from : forall c Γ,
  eval_ctx Γ -> ctx_ty_bound_lt_closed_from c Γ.
Proof.
  intros c Γ Hec x T Hlk.
  rewrite (eval_ctx_no_ty Γ x Hec) in Hlk. discriminate.
Qed.

Lemma eval_ctx_tm_ty_closed_from : forall c Γ,
  eval_ctx Γ -> ctx_tm_ty_closed_from c Γ.
Proof.
  intros c Γ Hec x T Hlk.
  rewrite (eval_ctx_no_tm Γ x Hec) in Hlk. discriminate.
Qed.

Lemma eval_ctx_ty_bound_ty_closed_from : forall c Γ,
  eval_ctx Γ -> ctx_ty_bound_ty_closed_from c Γ.
Proof.
  intros c Γ Hec x T Hlk.
  rewrite (eval_ctx_no_ty Γ x Hec) in Hlk. discriminate.
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

Lemma ctx_tm_lt_closed_from_bind_tm : forall c Γ A,
  ty_lt_closed c A ->
  ctx_tm_lt_closed_from c Γ ->
  ctx_tm_lt_closed_from c (bind_tm A :: Γ).
Proof.
  intros c Γ A HA Hctx x T Hlk. destruct x as [|x']; simpl in Hlk.
  - inversion Hlk; subst. exact HA.
  - apply (Hctx x'). exact Hlk.
Qed.

Lemma ctx_tm_lt_closed_from_bind_ty : forall c Γ B,
  ctx_tm_lt_closed_from c Γ ->
  ctx_tm_lt_closed_from c (bind_ty B :: Γ).
Proof.
  intros c Γ B Hctx x T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm Γ x) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst. apply ty_lt_closed_shift_ty. apply (Hctx x T0 Hbase).
Qed.

Lemma ctx_tm_lt_closed_from_bind_lt : forall c Γ D,
  ctx_tm_lt_closed_from c Γ ->
  ctx_tm_lt_closed_from (S c) (bind_lt D :: Γ).
Proof.
  intros c Γ D Hctx x T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm Γ x) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst.
  replace (S c) with (1 + c) by lia.
  eapply ty_lt_closed_shift_lt_below; [lia|]. apply (Hctx x T0 Hbase).
Qed.

Lemma ctx_tm_lt_closed_from0_bind_lt : forall Γ D,
  ctx_tm_lt_closed_from 0 Γ ->
  ctx_tm_lt_closed_from 0 (bind_lt D :: Γ).
Proof.
  intros Γ D Hctx x T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm Γ x) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst; clear Hlk.
  pose proof (Hctx x T0 Hbase) as HT0.
  rewrite shift_lt_in_type_closed by exact HT0. exact HT0.
Qed.

Lemma ctx_tm_lt_closed_from0_push_lt_vars : forall k Delta Γ,
  ctx_tm_lt_closed_from 0 Γ ->
  ctx_tm_lt_closed_from 0 (push_lt_vars k Delta Γ).
Proof.
  induction k as [|k IH]; intros Delta Γ Hctx; simpl.
  - exact Hctx.
  - apply IH. apply ctx_tm_lt_closed_from0_bind_lt. exact Hctx.
Qed.

Lemma ctx_tm_ty_closed_from_bind_tm : forall c Γ A,
  ty_ty_closed c A ->
  ctx_tm_ty_closed_from c Γ ->
  ctx_tm_ty_closed_from c (bind_tm A :: Γ).
Proof.
  intros c Γ A HA Hctx x T Hlk. destruct x as [|x']; simpl in Hlk.
  - inversion Hlk; subst. exact HA.
  - apply (Hctx x'). exact Hlk.
Qed.

Lemma ctx_tm_ty_closed_from_bind_ty : forall c Γ B,
  ctx_tm_ty_closed_from c Γ ->
  ctx_tm_ty_closed_from (S c) (bind_ty B :: Γ).
Proof.
  intros c Γ B Hctx x T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm Γ x) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst.
  replace (S c) with (1 + c) by lia.
  eapply ty_ty_closed_shift_ty_below; [lia|]. apply (Hctx x T0 Hbase).
Qed.

Lemma ctx_tm_ty_closed_from0_bind_ty : forall Γ B,
  ctx_tm_ty_closed_from 0 Γ ->
  ctx_tm_ty_closed_from 0 (bind_ty B :: Γ).
Proof.
  intros Γ B Hctx x T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm Γ x) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst; clear Hlk.
  pose proof (Hctx x T0 Hbase) as HT0.
  rewrite shift_ty_in_ty_closed by exact HT0. exact HT0.
Qed.

Lemma ctx_tm_ty_closed_from_bind_lt : forall c Γ D,
  ctx_tm_ty_closed_from c Γ ->
  ctx_tm_ty_closed_from c (bind_lt D :: Γ).
Proof.
  intros c Γ D Hctx x T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm Γ x) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst. apply ty_ty_closed_shift_lt. apply (Hctx x T0 Hbase).
Qed.

Lemma ctx_tm_ty_closed_from_push_lt_vars : forall k Delta c Γ,
  ctx_tm_ty_closed_from c Γ ->
  ctx_tm_ty_closed_from c (push_lt_vars k Delta Γ).
Proof.
  induction k as [|k IH]; intros Delta c Γ Hctx; simpl.
  - exact Hctx.
  - apply IH. apply ctx_tm_ty_closed_from_bind_lt. exact Hctx.
Qed.

Lemma ctx_tm_ty_closed_from_push_ty_vars : forall k B c Γ,
  ctx_tm_ty_closed_from c Γ ->
  ctx_tm_ty_closed_from (c + k) (push_ty_vars k B Γ).
Proof.
  induction k as [|k IH]; intros B c Γ Hctx; simpl.
  - replace (c + 0) with c by lia. exact Hctx.
  - replace (c + S k) with (S c + k) by lia.
    apply IH. apply ctx_tm_ty_closed_from_bind_ty. exact Hctx.
Qed.

Lemma ctx_tm_ty_closed_from0_push_ty_vars : forall k B Γ,
  ctx_tm_ty_closed_from 0 Γ ->
  ctx_tm_ty_closed_from 0 (push_ty_vars k B Γ).
Proof.
  induction k as [|k IH]; intros B Γ Hctx; simpl.
  - exact Hctx.
  - apply IH. apply ctx_tm_ty_closed_from0_bind_ty. exact Hctx.
Qed.

Lemma ctx_tm_ty_closed_from_fold_bind_tm : forall rhos c Γ,
  tys_ty_closed c rhos ->
  ctx_tm_ty_closed_from c Γ ->
  ctx_tm_ty_closed_from c (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros c Γ Hclosed Hctx; simpl in *.
  - exact Hctx.
  - destruct Hclosed as [Hrho Hrhos].
    apply ctx_tm_ty_closed_from_bind_tm.
    + exact Hrho.
    + apply IH; assumption.
Qed.

Lemma ctx_ty_bound_lt_closed_from_bind_tm : forall c Γ A,
  ctx_ty_bound_lt_closed_from c Γ ->
  ctx_ty_bound_lt_closed_from c (bind_tm A :: Γ).
Proof.
  intros c Γ A Hctx x T Hlk. simpl in Hlk. eapply Hctx; eauto.
Qed.

Lemma ctx_ty_bound_lt_closed_from_bind_ty : forall c Γ B,
  ty_lt_closed c B ->
  ctx_ty_bound_lt_closed_from c Γ ->
  ctx_ty_bound_lt_closed_from c (bind_ty B :: Γ).
Proof.
  intros c Γ B HB Hctx x T Hlk. destruct x as [|x']; simpl in Hlk.
  - inversion Hlk; subst. apply ty_lt_closed_shift_ty. exact HB.
  - destruct (ctx_lookup_ty Γ x') as [B0|] eqn:Hbase; [|discriminate].
    inversion Hlk; subst. apply ty_lt_closed_shift_ty. apply (Hctx x' B0 Hbase).
Qed.

Lemma ctx_ty_bound_lt_closed_from_bind_lt : forall c Γ D,
  ctx_ty_bound_lt_closed_from c Γ ->
  ctx_ty_bound_lt_closed_from (S c) (bind_lt D :: Γ).
Proof.
  intros c Γ D Hctx x T Hlk. simpl in Hlk.
  destruct (ctx_lookup_ty Γ x) as [B0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst.
  replace (S c) with (1 + c) by lia.
  eapply ty_lt_closed_shift_lt_below; [lia|]. apply (Hctx x B0 Hbase).
Qed.

Lemma ctx_ty_bound_lt_closed_from0_bind_lt : forall Γ D,
  ctx_ty_bound_lt_closed_from 0 Γ ->
  ctx_ty_bound_lt_closed_from 0 (bind_lt D :: Γ).
Proof.
  intros Γ D Hctx x T Hlk. simpl in Hlk.
  destruct (ctx_lookup_ty Γ x) as [B0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst; clear Hlk.
  pose proof (Hctx x B0 Hbase) as HB0.
  rewrite shift_lt_in_type_closed by exact HB0. exact HB0.
Qed.

Lemma ctx_ty_bound_ty_closed_from_bind_tm : forall c Γ A,
  ctx_ty_bound_ty_closed_from c Γ ->
  ctx_ty_bound_ty_closed_from c (bind_tm A :: Γ).
Proof.
  intros c Γ A Hctx x T Hlk. simpl in Hlk. eapply Hctx; eauto.
Qed.

Lemma ctx_ty_bound_ty_closed_from_bind_ty : forall c Γ B,
  ty_ty_closed c B ->
  ctx_ty_bound_ty_closed_from c Γ ->
  ctx_ty_bound_ty_closed_from (S c) (bind_ty B :: Γ).
Proof.
  intros c Γ B HB Hctx x T Hlk. destruct x as [|x']; simpl in Hlk.
  - inversion Hlk; subst.
    replace (S c) with (1 + c) by lia.
    eapply ty_ty_closed_shift_ty_below; [lia|exact HB].
  - destruct (ctx_lookup_ty Γ x') as [B0|] eqn:Hbase; [|discriminate].
    inversion Hlk; subst.
    replace (S c) with (1 + c) by lia.
    eapply ty_ty_closed_shift_ty_below; [lia|]. apply (Hctx x' B0 Hbase).
Qed.

Lemma ctx_ty_bound_ty_closed_from0_bind_ty : forall Γ B,
  ty_ty_closed 0 B ->
  ctx_ty_bound_ty_closed_from 0 Γ ->
  ctx_ty_bound_ty_closed_from 0 (bind_ty B :: Γ).
Proof.
  intros Γ B HB Hctx x T Hlk. destruct x as [|x']; simpl in Hlk.
  - inversion Hlk; subst. rewrite shift_ty_in_ty_closed by exact HB. exact HB.
  - destruct (ctx_lookup_ty Γ x') as [B0|] eqn:Hbase; [|discriminate].
    inversion Hlk; subst; clear Hlk.
    pose proof (Hctx x' B0 Hbase) as HB0.
    rewrite shift_ty_in_ty_closed by exact HB0. exact HB0.
Qed.

Lemma ctx_ty_bound_ty_closed_from_bind_lt : forall c Γ D,
  ctx_ty_bound_ty_closed_from c Γ ->
  ctx_ty_bound_ty_closed_from c (bind_lt D :: Γ).
Proof.
  intros c Γ D Hctx x T Hlk. simpl in Hlk.
  destruct (ctx_lookup_ty Γ x) as [B0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst. apply ty_ty_closed_shift_lt. apply (Hctx x B0 Hbase).
Qed.

Lemma ctx_ty_bound_ty_closed_from_bind_ctor : forall c Γ K n_lt n_ty fields result,
  ctx_ty_bound_ty_closed_from c Γ ->
  ctx_ty_bound_ty_closed_from c (bind_ctor K n_lt n_ty fields result :: Γ).
Proof.
  intros c Γ K n_lt n_ty fields result Hctx x T Hlk. simpl in Hlk. eapply Hctx; eauto.
Qed.

Lemma ctx_ty_bound_ty_closed_from_bind_eff : forall c Γ E n_a n_b sig ret,
  ctx_ty_bound_ty_closed_from c Γ ->
  ctx_ty_bound_ty_closed_from c (bind_eff E n_a n_b sig ret :: Γ).
Proof.
  intros c Γ E n_a n_b sig ret Hctx x T Hlk. simpl in Hlk. eapply Hctx; eauto.
Qed.

Lemma ctx_ty_bound_ty_closed_from_push_lt_vars : forall k Delta c Γ,
  ctx_ty_bound_ty_closed_from c Γ ->
  ctx_ty_bound_ty_closed_from c (push_lt_vars k Delta Γ).
Proof.
  induction k as [|k IH]; intros Delta c Γ Hctx; simpl.
  - exact Hctx.
  - apply IH. apply ctx_ty_bound_ty_closed_from_bind_lt. exact Hctx.
Qed.

Lemma ctx_ty_bound_ty_closed_from_push_ty_vars : forall k B c Γ,
  ty_ty_closed c B ->
  ctx_ty_bound_ty_closed_from c Γ ->
  ctx_ty_bound_ty_closed_from (c + k) (push_ty_vars k B Γ).
Proof.
  induction k as [|k IH]; intros B c Γ HB Hctx; simpl.
  - replace (c + 0) with c by lia. exact Hctx.
  - replace (c + S k) with (S c + k) by lia.
    apply IH.
    + eapply ty_ty_closed_mono; [|exact HB]. lia.
    + apply ctx_ty_bound_ty_closed_from_bind_ty; assumption.
Qed.

Lemma ctx_ty_bound_ty_closed_from0_push_ty_vars : forall k B Γ,
  ty_ty_closed 0 B ->
  ctx_ty_bound_ty_closed_from 0 Γ ->
  ctx_ty_bound_ty_closed_from 0 (push_ty_vars k B Γ).
Proof.
  induction k as [|k IH]; intros B Γ HB Hctx; simpl.
  - exact Hctx.
  - apply IH.
    + exact HB.
    + apply ctx_ty_bound_ty_closed_from0_bind_ty; assumption.
Qed.

Lemma ctx_ty_bound_ty_closed_from_fold_bind_tm : forall rhos c Γ,
  ctx_ty_bound_ty_closed_from c Γ ->
  ctx_ty_bound_ty_closed_from c (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros c Γ Hctx; simpl.
  - exact Hctx.
  - apply ctx_ty_bound_ty_closed_from_bind_tm. apply IH. exact Hctx.
Qed.

Lemma ctx_ty_bound_lt_closed_from_bind_ctor : forall c Γ K n_lt n_ty fields result,
  ctx_ty_bound_lt_closed_from c Γ ->
  ctx_ty_bound_lt_closed_from c (bind_ctor K n_lt n_ty fields result :: Γ).
Proof.
  intros c Γ K n_lt n_ty fields result Hctx x T Hlk. simpl in Hlk. eapply Hctx; eauto.
Qed.

Lemma ctx_ty_bound_lt_closed_from_bind_eff : forall c Γ E n_a n_b sig ret,
  ctx_ty_bound_lt_closed_from c Γ ->
  ctx_ty_bound_lt_closed_from c (bind_eff E n_a n_b sig ret :: Γ).
Proof.
  intros c Γ E n_a n_b sig ret Hctx x T Hlk. simpl in Hlk. eapply Hctx; eauto.
Qed.

Lemma ctx_ty_bound_lt_closed_from_push_lt_vars : forall k Delta c Γ,
  ctx_ty_bound_lt_closed_from c Γ ->
  ctx_ty_bound_lt_closed_from (c + k) (push_lt_vars k Delta Γ).
Proof.
  induction k as [|k IH]; intros Delta c Γ Hctx; simpl.
  - replace (c + 0) with c by lia. exact Hctx.
  - replace (c + S k) with (S c + k) by lia.
    apply IH. apply ctx_ty_bound_lt_closed_from_bind_lt. exact Hctx.
Qed.

Lemma ctx_ty_bound_lt_closed_from0_push_lt_vars : forall k Delta Γ,
  ctx_ty_bound_lt_closed_from 0 Γ ->
  ctx_ty_bound_lt_closed_from 0 (push_lt_vars k Delta Γ).
Proof.
  induction k as [|k IH]; intros Delta Γ Hctx; simpl.
  - exact Hctx.
  - apply IH. apply ctx_ty_bound_lt_closed_from0_bind_lt. exact Hctx.
Qed.

Lemma ctx_ty_bound_lt_closed_from_push_ty_vars : forall k B c Γ,
  ty_lt_closed c B ->
  ctx_ty_bound_lt_closed_from c Γ ->
  ctx_ty_bound_lt_closed_from c (push_ty_vars k B Γ).
Proof.
  induction k as [|k IH]; intros B c Γ HB Hctx; simpl.
  - exact Hctx.
  - apply IH.
    + exact HB.
    + apply ctx_ty_bound_lt_closed_from_bind_ty; assumption.
Qed.

Lemma ctx_ty_bound_lt_closed_from_fold_bind_tm : forall rhos c Γ,
  ctx_ty_bound_lt_closed_from c Γ ->
  ctx_ty_bound_lt_closed_from c (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros c Γ Hctx; simpl.
  - exact Hctx.
  - apply ctx_ty_bound_lt_closed_from_bind_tm. apply IH. exact Hctx.
Qed.

Lemma ctx_tm_lt_closed_from_bind_ctor : forall c Γ K n_lt n_ty fields result,
  ctx_tm_lt_closed_from c Γ ->
  ctx_tm_lt_closed_from c (bind_ctor K n_lt n_ty fields result :: Γ).
Proof.
  intros c Γ K n_lt n_ty fields result Hctx x T Hlk.
  simpl in Hlk. apply (Hctx x T Hlk).
Qed.

Lemma ctx_tm_lt_closed_from_bind_eff : forall c Γ E n_a n_b sig ret,
  ctx_tm_lt_closed_from c Γ ->
  ctx_tm_lt_closed_from c (bind_eff E n_a n_b sig ret :: Γ).
Proof.
  intros c Γ E n_a n_b sig ret Hctx x T Hlk.
  simpl in Hlk. apply (Hctx x T Hlk).
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

Lemma types_wf_eval_ctx_ty_closed : forall Γ Ts,
  eval_ctx Γ -> types_wf Γ Ts -> tys_ty_closed 0 Ts.
Proof.
  intros Γ Ts Hec Hwf. eapply types_wf_ty_closed_from; [exact Hwf|].
  apply eval_ctx_ty_closed_from. exact Hec.
Qed.

Lemma types_wf_eval_ctx_lt_closed : forall Γ Ts,
  eval_ctx Γ -> types_wf Γ Ts -> tys_lt_closed 0 Ts.
Proof.
  intros Γ Ts Hec Hwf. eapply types_wf_lt_closed_from; [exact Hwf|].
  apply eval_ctx_lt_closed_from. exact Hec.
Qed.

Lemma lt_wf_eval_ctx_lt_closed : forall Γ l,
  eval_ctx Γ -> lt_wf Γ l -> lt_lt_closed 0 l.
Proof.
  intros Γ l Hec Hwf. eapply lt_wf_closed_from; [exact Hwf|].
  apply eval_ctx_lt_closed_from. exact Hec.
Qed.

Lemma lifetimes_wf_eval_ctx_lt_closed : forall Γ lts,
  eval_ctx Γ -> lifetimes_wf Γ lts -> lts_lt_closed 0 lts.
Proof.
  intros Γ lts Hec Hwf. eapply lifetimes_wf_lt_closed_from; [exact Hwf|].
  apply eval_ctx_lt_closed_from. exact Hec.
Qed.

Lemma ctx_ty_closed_from_push_lt_vars : forall k Delta c Γ,
  ctx_ty_closed_from c Γ -> ctx_ty_closed_from c (push_lt_vars k Delta Γ).
Proof.
  induction k as [|k IH]; intros Delta c Γ Hctx; simpl.
  - exact Hctx.
  - apply IH. apply ctx_ty_closed_from_bind_lt. exact Hctx.
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

Lemma ctx_lt_closed_from_push_lt_vars : forall k Delta c Γ,
  ctx_lt_closed_from c Γ -> ctx_lt_closed_from (c + k) (push_lt_vars k Delta Γ).
Proof.
  induction k as [|k IH]; intros Delta c Γ Hctx; simpl.
  - replace (c + 0) with c by lia. exact Hctx.
  - replace (c + S k) with (S c + k) by lia.
    apply IH. apply ctx_lt_closed_from_bind_lt. exact Hctx.
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

Lemma ctx_tm_lt_closed_from_push_lt_vars : forall k Delta c Γ,
  ctx_tm_lt_closed_from c Γ ->
  ctx_tm_lt_closed_from (c + k) (push_lt_vars k Delta Γ).
Proof.
  induction k as [|k IH]; intros Delta c Γ Hctx; simpl.
  - replace (c + 0) with c by lia. exact Hctx.
  - replace (c + S k) with (S c + k) by lia.
    apply IH. apply ctx_tm_lt_closed_from_bind_lt. exact Hctx.
Qed.

Lemma ctx_tm_lt_closed_from_push_ty_vars : forall k B c Γ,
  ctx_tm_lt_closed_from c Γ ->
  ctx_tm_lt_closed_from c (push_ty_vars k B Γ).
Proof.
  induction k as [|k IH]; intros B c Γ Hctx; simpl.
  - exact Hctx.
  - apply IH. apply ctx_tm_lt_closed_from_bind_ty. exact Hctx.
Qed.

Lemma ctx_tm_lt_closed_from_fold_bind_tm : forall rhos c Γ,
  tys_lt_closed c rhos ->
  ctx_tm_lt_closed_from c Γ ->
  ctx_tm_lt_closed_from c (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros c Γ Hclosed Hctx; simpl in *.
  - exact Hctx.
  - destruct Hclosed as [Hrho Hrhos].
    apply ctx_tm_lt_closed_from_bind_tm.
    + exact Hrho.
    + apply IH; assumption.
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

Lemma Forall2_typing_InsLt_closed_from : forall Γ vs rhos,
  Forall2 (fun v rho => forall c G',
    InsLt c Γ G' ->
    ctx_lt_closed_from c Γ ->
    ctx_schemas_lt_closed_from c Γ ->
    G' ⊢ₜ v : rho) vs rhos ->
  forall c G',
    InsLt c Γ G' ->
    ctx_lt_closed_from c Γ ->
    ctx_schemas_lt_closed_from c Γ ->
    Forall2 (fun v rho => G' ⊢ₜ v : rho) vs rhos.
Proof.
  intros Γ vs rhos H. induction H; intros c G' HIns Hlt Hschemas; simpl.
  - constructor.
  - constructor.
    + apply (H c G'); assumption.
    + apply (IHForall2 c G'); assumption.
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
  - intros Γ t B U S Ht IH HwfS Hsub HnlArg c Hctx. simpl.
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
      apply ctx_ty_closed_from_push_lt_vars. exact Hctx.
    + apply IHno. exact Hctx.
  - intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff Hlen HwfTs HwfTR Hsig Hret Hop IHop c Hctx.
    simpl. repeat split.
    + eapply types_wf_ty_closed_from; eauto.
    + eapply ty_wf_ty_closed_from; eauto.
    + apply IHop. repeat apply ctx_ty_closed_from_bind_tm.
      apply ctx_ty_closed_from_push_ty_vars. exact Hctx.
  - intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hsig Hret Hop IHop Hbody IHbody c Hctx.
    simpl. repeat split.
    + eapply types_wf_ty_closed_from; eauto.
    + eapply ty_wf_ty_closed_from; eauto.
    + eapply ty_wf_ty_closed_from; eauto.
    + apply IHop. repeat apply ctx_ty_closed_from_bind_tm.
      apply ctx_ty_closed_from_push_ty_vars. exact Hctx.
    + apply IHbody. apply ctx_ty_closed_from_bind_tm. exact Hctx.
  - intros Γ recv arg E_tag Delta Ts Ss n_α n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg c Hctx.
    simpl. repeat split.
    + apply IHrecv. exact Hctx.
    + eapply types_wf_ty_closed_from; eauto.
    + apply IHarg. exact Hctx.
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH c Hctx. simpl.
    repeat split.
    + eapply ty_wf_ty_closed_from; eauto.
    + eapply ty_wf_ty_closed_from; eauto.
    + apply IH. exact Hctx.
  - intros Γ m b A T_B T_R HwfA HwfTB HwfTR HnoLocal Hsub Hb IHb c Hctx. simpl.
    repeat split.
    + eapply ty_wf_ty_closed_from; eauto.
    + eapply ty_wf_ty_closed_from; eauto.
    + apply IHb. apply ctx_ty_closed_from_bind_tm. exact Hctx.
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
  - intros Γ t B U S Ht IH HwfS Hsub HnlArg c Hctx. simpl.
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
      apply ctx_lt_closed_from_push_lt_vars. exact Hctx.
    + apply IHno. exact Hctx.
  - intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff Hlen HwfTs HwfTR Hsig Hret Hop IHop c Hctx.
    simpl. repeat split.
    + eapply types_wf_lt_closed_from; eauto.
    + eapply ty_wf_lt_closed_from; eauto.
    + apply IHop. repeat apply ctx_lt_closed_from_bind_tm.
      apply ctx_lt_closed_from_push_ty_vars. exact Hctx.
  - intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hsig Hret Hop IHop Hbody IHbody c Hctx.
    simpl. repeat split.
    + eapply types_wf_lt_closed_from; eauto.
    + eapply ty_wf_lt_closed_from; eauto.
    + eapply ty_wf_lt_closed_from; eauto.
    + apply IHop. repeat apply ctx_lt_closed_from_bind_tm.
      apply ctx_lt_closed_from_push_ty_vars. exact Hctx.
    + apply IHbody. apply ctx_lt_closed_from_bind_tm. exact Hctx.
  - intros Γ recv arg E_tag Delta Ts Ss n_α n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg c Hctx.
    simpl. repeat split.
    + apply IHrecv. exact Hctx.
    + eapply types_wf_lt_closed_from; eauto.
    + apply IHarg. exact Hctx.
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH c Hctx. simpl.
    repeat split.
    + eapply ty_wf_lt_closed_from; eauto.
    + eapply ty_wf_lt_closed_from; eauto.
    + apply IH. exact Hctx.
  - intros Γ m b A T_B T_R HwfA HwfTB HwfTR HnoLocal Hsub Hb IHb c Hctx. simpl.
    repeat split.
    + eapply ty_wf_lt_closed_from; eauto.
    + eapply ty_wf_lt_closed_from; eauto.
    + apply IHb. apply ctx_lt_closed_from_bind_tm. exact Hctx.
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

Lemma typing_eval_ctx_tm_ty_stable : forall Γ t T,
  eval_ctx Γ -> Γ ⊢ₜ t : T -> tm_ty_stable t.
Proof.
  intros Γ t T Hec Hty. apply tm_ty_closed_stable.
  eapply typing_eval_ctx_tm_ty_closed; eauto.
Qed.

Lemma typing_eval_ctx_tm_lt_stable : forall Γ t T,
  eval_ctx Γ -> Γ ⊢ₜ t : T -> tm_lt_stable t.
Proof.
  intros Γ t T Hec Hty. apply tm_lt_closed_stable.
  eapply typing_eval_ctx_tm_lt_closed; eauto.
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
  - intros Γ t B U S Ht IH HwfS Hsub HnlArg.
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
  - intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff Hlen HwfTs HwfTR Hsig Hret Hop IHop.
    constructor; [constructor|exact HwfTs].
  - intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hsig Hret Hop IHop Hbody IHbody.
    exact HwfTR.
  - intros Γ recv arg E_tag Δ Ts Ss n_α n_β sig ret sig_inst ret_inst
      Hrecv IHrecv Heff Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg.
    exact HwfRet.
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH. exact HwfTR.
  - intros Γ m b A T_B T_R HwfA HwfTB HwfTR HnoLocal Hsub Hb IHb.
    constructor; [exact HwfA|constructor|exact HwfTR].
Qed.

Lemma typing_InsLt_closed_from : forall Γ t T,
  Γ ⊢ₜ t : T ->
  forall c Γ',
    InsLt c Γ Γ' ->
    ctx_lt_closed_from c Γ ->
    ctx_schemas_lt_closed_from c Γ ->
    Γ' ⊢ₜ t : T.
Proof.
  apply (typing_ind_forall2
    (fun Γ t T => forall c Γ',
      InsLt c Γ Γ' ->
      ctx_lt_closed_from c Γ ->
      ctx_schemas_lt_closed_from c Γ ->
      Γ' ⊢ₜ t : T)).
  - intros Γ x T Hlk HwfT c Γ' HIns Hlt Hschemas.
    apply T_Var.
    + rewrite (InsLt_lookup_tm c Γ Γ' HIns x), Hlk. simpl.
      rewrite shift_lt_in_type_closed.
      * reflexivity.
      * eapply ty_wf_lt_closed_from; eauto.
    + eapply ty_wf_InsLt_closed; eauto.
      eapply ty_wf_lt_closed_from; eauto.
  - intros Γ t T U Ht IHt Hsub c Γ' HIns Hlt Hschemas.
    eapply T_Sub.
    + apply (IHt c Γ'); assumption.
    + destruct (sub_wf _ _ _ Hsub) as [HwfT HwfU].
      eapply sub_InsLt_closed; eauto;
        eapply ty_wf_lt_closed_from; eauto.
  - intros Γ body A l B HwfA HwfB Hbody IHbody Hcap c Γ' HIns Hlt Hschemas.
    assert (HAclosed : ty_lt_closed c A) by (eapply ty_wf_lt_closed_from; eauto).
    assert (HBclosed : ty_lt_closed c B) by (eapply ty_wf_lt_closed_from; eauto).
    apply T_Lam.
    + exact (ty_wf_InsLt_closed Γ A HwfA c Γ' HIns HAclosed).
    + exact (ty_wf_InsLt_closed Γ B HwfB c Γ' HIns HBclosed).
    + apply (IHbody c (bind_tm A :: Γ')).
      * exact (InsLt_bind_tm_closed A c Γ Γ' HIns HAclosed).
      * apply ctx_lt_closed_from_bind_tm. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_tm. exact Hschemas.
    + replace (capture_lt Γ' body) with (capture_lt Γ body).
      * destruct (lt_sub_wf _ _ _ Hcap) as [Hwfcap Hwfl].
        eapply lt_sub_InsLt_closed; eauto;
          eapply lt_wf_closed_from; eauto.
      * pose proof (capture_lt_InsLt c Γ Γ' HIns body) as HcapEq.
        rewrite shift_lt_in_tm_closed in HcapEq.
        -- rewrite HcapEq. symmetry. apply shift_lt_closed_lifetime.
           destruct (lt_sub_wf _ _ _ Hcap) as [Hwfcap _].
           eapply lt_wf_closed_from; eauto.
        -- eapply typing_tm_lt_closed_from; [exact Hbody|].
           apply ctx_lt_closed_from_bind_tm. exact Hlt.
  - intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 c Γ' HIns Hlt Hschemas.
    eapply T_App; [apply (IH1 c Γ')|apply (IH2 c Γ')]; assumption.
  - intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody c Γ' HIns Hlt Hschemas.
    assert (HboundClosed : ty_lt_closed c bound) by (eapply ty_wf_lt_closed_from; eauto).
    assert (HTClosed : ty_lt_closed c T).
    { eapply ty_wf_lt_closed_from; [exact HwfT|].
      apply ctx_lt_closed_from_bind_ty. exact Hlt. }
    apply T_TyLam.
    + exact (ty_wf_InsLt_closed Γ bound HwfBound c Γ' HIns HboundClosed).
    + exact (ty_wf_InsLt_closed (bind_ty bound :: Γ) T HwfT c (bind_ty bound :: Γ')
        (InsLt_bind_ty_closed bound c Γ Γ' HIns HboundClosed) HTClosed).
    + exact HisAbs.
    + apply (IHbody c (bind_ty bound :: Γ')).
      * exact (InsLt_bind_ty_closed bound c Γ Γ' HIns HboundClosed).
      * apply ctx_lt_closed_from_bind_ty. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_ty. exact Hschemas.
  - intros Γ t B U S Ht IH HwfS Hsub HnlArg c Γ' HIns Hlt Hschemas.
    eapply T_TyApp.
    + apply (IH c Γ'); assumption.
    + eapply ty_wf_InsLt_closed; eauto.
      eapply ty_wf_lt_closed_from; eauto.
    + destruct (sub_wf _ _ _ Hsub) as [HwfS' HwfB].
      eapply sub_InsLt_closed; eauto;
        eapply ty_wf_lt_closed_from; eauto.
    + destruct (sub_wf _ _ _ Hsub) as [HwfS' HwfB].
      eapply ty_app_arg_no_local_InsLt_closed; eauto;
        eapply ty_wf_lt_closed_from; eauto.
  - intros Γ body T HwfT HisAbs Hbody IHbody c Γ' HIns Hlt Hschemas.
    assert (HTClosed : ty_lt_closed (S c) T).
    { eapply ty_wf_lt_closed_from; [exact HwfT|].
      apply ctx_lt_closed_from_bind_lt. exact Hlt. }
    apply T_LtLam.
    + exact (ty_wf_InsLt_closed (bind_lt lt_local :: Γ) T HwfT (S c) (bind_lt lt_local :: Γ')
        (InsLt_bind_lt_closed lt_local c Γ Γ' HIns I) HTClosed).
    + exact HisAbs.
    + apply (IHbody (S c) (bind_lt lt_local :: Γ')).
      * exact (InsLt_bind_lt_closed lt_local c Γ Γ' HIns I).
      * apply ctx_lt_closed_from_bind_lt. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_lt. exact Hschemas.
  - intros Γ t T l Ht IH Hwfl c Γ' HIns Hlt Hschemas.
    eapply T_LtApp.
    + apply (IH c Γ'); assumption.
    + exact (lt_wf_InsLt_closed Γ l Hwfl c Γ' HIns (lt_wf_closed_from Γ l Hwfl c Hlt)).
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
           Hctor Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs Hresult Hshape Hresult_eff Hwfl HltSub Hbounded Hlen_vs Hargs IHargs
           c Γ' HIns Hlt Hschemas.
        assert (HTsClosed : tys_lt_closed c Ts) by (eapply types_wf_lt_closed_from; eauto).
    eapply T_Ctor with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := sigma_fields) (result_ty_schema := result_ty_schema)
      (lts := lts) (rho_fields := rho_fields) (result_tag := result_tag).
    + exact (InsLt_lookup_ctor_schemas_closed Γ Γ' c K n_lt n_ty sigma_fields result_ty_schema Hschemas HIns Hctor).
    + rewrite (InsLt_lookup_eff c Γ Γ' HIns K). rewrite Heff. reflexivity.
    + exact Hlen_lts.
    + eapply lifetimes_wf_InsLt_closed; eauto.
      eapply lifetimes_wf_lt_closed_from; eauto.
    + exact Hrho.
    + exact Hlen_Ts.
    + exact (types_wf_InsLt_closed Γ Ts HwfTs c Γ' HIns HTsClosed).
    + exact Hresult.
    + exact Hshape.
    + rewrite (InsLt_lookup_eff c Γ Γ' HIns result_tag). rewrite Hresult_eff. reflexivity.
    + eapply lt_wf_InsLt_closed; eauto.
      eapply lt_wf_closed_from; eauto.
    + destruct (lt_sub_wf _ _ _ HltSub) as [HwfRhos HwflResult].
      eapply lt_sub_InsLt_closed; eauto;
        eapply lt_wf_closed_from; eauto.
    + eapply Forall_impl; [|exact Hbounded]. intros l0 Hsub0.
      destruct (lt_sub_wf _ _ _ Hsub0) as [Hwfl0 Hwfl'].
      eapply lt_sub_InsLt_closed; eauto;
        eapply lt_wf_closed_from; eauto.
    + exact Hlen_vs.
    + eapply Forall2_typing_InsLt_closed_from; eauto.
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γyes yes_body eta elim_result no_body
           HKne Hctor Heff Hlts Hrho Hlen_Ts HwfTs Hscrut_result Hscrut_shape Hresult_eff Hresult_ne
           HwfDelta Hresult_l Hscrut IHscrut Harity HΓyes Hyes IHyes Helim Hno IHno
           c Γ' HIns Hlt Hschemas.
    subst Γyes.
    assert (HDeltaClosed : lt_lt_closed c Delta) by (eapply lt_wf_closed_from; eauto).
    assert (HTsClosed : tys_lt_closed c Ts) by (eapply types_wf_lt_closed_from; eauto).
    assert (HrhosClosed : tys_lt_closed (c + n_lt) rho_fields).
    { subst lts rho_fields. replace (c + n_lt) with (n_lt + c) by lia.
      eapply inst_ctor_type_list_lt_var_list_lt_closed; eauto.
      destruct Hschemas as [HctorSchemas _].
      destruct (HctorSchemas K n_lt n_ty sigma_fields result_ty_schema Hctor) as [Hfields _].
      exact Hfields. }
    eapply T_Match with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := sigma_fields) (result_ty_schema := result_ty_schema)
      (lts := lts) (rho_fields := rho_fields)
      (scrut_result_ty := scrut_result_ty)
      (result_tag := result_tag) (result_l := result_l)
      (Γ' := push_lt_vars n_lt Delta Γ') (eta := eta).
    + exact HKne.
    + eapply InsLt_lookup_ctor_schemas_closed; eauto.
    + rewrite (InsLt_lookup_eff c Γ Γ' HIns K). rewrite Heff. reflexivity.
    + exact Hlts.
    + exact Hrho.
    + exact Hlen_Ts.
    + eapply types_wf_InsLt_closed; eauto.
    + exact Hscrut_result.
    + exact Hscrut_shape.
    + rewrite (InsLt_lookup_eff c Γ Γ' HIns result_tag). rewrite Hresult_eff. reflexivity.
    + exact Hresult_ne.
    + exact (lt_wf_InsLt_closed Γ Delta HwfDelta c Γ' HIns HDeltaClosed).
    + destruct (lt_sub_wf _ _ _ Hresult_l) as [HwfResultL HwfDeltaSub].
      exact (lt_sub_InsLt_closed Γ result_l Delta Hresult_l c Γ' HIns
        (lt_wf_closed_from Γ result_l HwfResultL c Hlt) HDeltaClosed).
    + apply (IHscrut c Γ'); assumption.
    + exact Harity.
    + reflexivity.
    + apply (IHyes (c + n_lt)
        (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) (push_lt_vars n_lt Delta Γ') rho_fields)).
      * exact (InsLt_fold_bind_tm_closed rho_fields (c + n_lt)
          (push_lt_vars n_lt Delta Γ) (push_lt_vars n_lt Delta Γ')
          (InsLt_push_lt_vars_closed n_lt Delta c Γ Γ' HIns HDeltaClosed)
          HrhosClosed).
      * apply ctx_lt_closed_from_fold_bind_tm.
        apply ctx_lt_closed_from_push_lt_vars. exact Hlt.
      * apply ctx_schemas_lt_closed_from_fold_bind_tm.
        apply ctx_schemas_lt_closed_from_push_lt_vars. exact Hschemas.
    + exact Helim.
    + apply (IHno c Γ'); assumption.
  - intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff Hlen HwfTs HwfTR Hsig Hret Hop IHop c Γ' HIns Hlt Hschemas.
            pose proof Hschemas as HschemasAll.
    assert (HTsClosed : tys_lt_closed c Ts) by (eapply types_wf_lt_closed_from; eauto).
    assert (HTRClosed : ty_lt_closed c T_R) by (eapply ty_wf_lt_closed_from; eauto).
    destruct Hschemas as [_ HeffSchemas].
    destruct (HeffSchemas E_tag n_α n_β sig ret Heff) as [HsigSchema HretSchema].
    assert (HsigBetaClosed : ty_lt_closed c sig_β).
    { rewrite Hsig. eapply inst_op_alpha_lt_closed; eauto. }
    assert (HretBetaClosed : ty_lt_closed c ret_β).
    { rewrite Hret. eapply inst_op_alpha_lt_closed; eauto. }
    assert (HfunClosed : ty_lt_closed c (type_fun ret_β lt_local (shift_ty n_β 0 T_R))).
    { simpl. repeat split; try exact I; try exact HretBetaClosed.
      apply ty_lt_closed_shift_ty. exact HTRClosed. }
    eapply T_Cap with
      (n_α := n_α) (n_β := n_β) (sig := sig) (ret := ret)
      (sig_β := sig_β) (ret_β := ret_β).
    + rewrite (InsLt_lookup_eff c Γ Γ' HIns E_tag). rewrite Heff. cbn [option_map].
      rewrite (shift_lt_eff_sig_closed_from n_α n_β sig ret c HsigSchema HretSchema).
      reflexivity.
    + exact Hlen.
    + exact (types_wf_InsLt_closed Γ Ts HwfTs c Γ' HIns HTsClosed).
    + exact (ty_wf_InsLt_closed Γ T_R HwfTR c Γ' HIns HTRClosed).
    + exact Hsig.
    + exact Hret.
    + apply (IHop c (bind_tm sig_β :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R)) ::
        push_ty_vars n_β any_at_free Γ')).
      * exact (InsLt_bind_tm_closed sig_β c
          (bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R)) :: push_ty_vars n_β any_at_free Γ)
          (bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R)) :: push_ty_vars n_β any_at_free Γ')
          (InsLt_bind_tm_closed (type_fun ret_β lt_local (shift_ty n_β 0 T_R)) c
            (push_ty_vars n_β any_at_free Γ) (push_ty_vars n_β any_at_free Γ')
            (InsLt_push_ty_vars_any_at_free n_β c Γ Γ' HIns) HfunClosed)
          HsigBetaClosed).
      * apply ctx_lt_closed_from_bind_tm. apply ctx_lt_closed_from_bind_tm.
        apply ctx_lt_closed_from_push_ty_vars. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_tm. apply ctx_schemas_lt_closed_from_bind_tm.
        apply ctx_schemas_lt_closed_from_push_ty_vars. exact HschemasAll.
  - intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hsig Hret Hop IHop Hbody IHbody c Γ' HIns Hlt Hschemas.
    pose proof Hschemas as HschemasAll.
    assert (HTsClosed : tys_lt_closed c Ts) by (eapply types_wf_lt_closed_from; eauto).
    assert (HTBClosed : ty_lt_closed c T_B) by (eapply ty_wf_lt_closed_from; eauto).
    assert (HTRClosed : ty_lt_closed c T_R) by (eapply ty_wf_lt_closed_from; eauto).
    assert (HhandledClosed : ty_lt_closed c (type_ctor E_tag lt_local Ts))
      by (simpl; split; [exact I|exact HTsClosed]).
    destruct Hschemas as [_ HeffSchemas].
    destruct (HeffSchemas E_tag n_α n_β sig ret Heff) as [HsigSchema HretSchema].
    assert (HsigBetaClosed : ty_lt_closed c sig_β).
    { rewrite Hsig. eapply inst_op_alpha_lt_closed; eauto. }
    assert (HretBetaClosed : ty_lt_closed c ret_β).
    { rewrite Hret. eapply inst_op_alpha_lt_closed; eauto. }
    assert (HfunClosed : ty_lt_closed c (type_fun ret_β lt_local (shift_ty n_β 0 T_R))).
    { simpl. repeat split; try exact I; try exact HretBetaClosed.
      apply ty_lt_closed_shift_ty. exact HTRClosed. }
    eapply T_Handle with
      (n_α := n_α) (n_β := n_β) (sig := sig) (ret := ret)
      (T_B := T_B) (sig_β := sig_β) (ret_β := ret_β).
    + rewrite (InsLt_lookup_eff c Γ Γ' HIns E_tag). rewrite Heff. cbn [option_map].
      rewrite (shift_lt_eff_sig_closed_from n_α n_β sig ret c HsigSchema HretSchema).
      reflexivity.
    + exact Hlen.
    + exact (types_wf_InsLt_closed Γ Ts HwfTs c Γ' HIns HTsClosed).
    + exact (ty_wf_InsLt_closed Γ T_B HwfTB c Γ' HIns HTBClosed).
    + exact (ty_wf_InsLt_closed Γ T_R HwfTR c Γ' HIns HTRClosed).
    + exact (no_local_ty_G_InsLt_closed Γ T_B c Γ' HIns HTBClosed HnoLocal).
    + exact (sub_InsLt_closed Γ T_B T_R Hsub c Γ' HIns HTBClosed HTRClosed).
    + exact Hsig.
    + exact Hret.
    + apply (IHop c (bind_tm sig_β :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R)) ::
        push_ty_vars n_β any_at_free Γ')).
      * exact (InsLt_bind_tm_closed sig_β c
          (bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R)) :: push_ty_vars n_β any_at_free Γ)
          (bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R)) :: push_ty_vars n_β any_at_free Γ')
          (InsLt_bind_tm_closed (type_fun ret_β lt_local (shift_ty n_β 0 T_R)) c
            (push_ty_vars n_β any_at_free Γ) (push_ty_vars n_β any_at_free Γ')
            (InsLt_push_ty_vars_any_at_free n_β c Γ Γ' HIns) HfunClosed)
          HsigBetaClosed).
      * apply ctx_lt_closed_from_bind_tm. apply ctx_lt_closed_from_bind_tm.
        apply ctx_lt_closed_from_push_ty_vars. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_tm. apply ctx_schemas_lt_closed_from_bind_tm.
        apply ctx_schemas_lt_closed_from_push_ty_vars. exact HschemasAll.
    + apply (IHbody c (bind_tm (type_ctor E_tag lt_local Ts) :: Γ')).
      * exact (InsLt_bind_tm_closed (type_ctor E_tag lt_local Ts) c Γ Γ' HIns HhandledClosed).
      * apply ctx_lt_closed_from_bind_tm. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_tm. exact HschemasAll.
  - intros Γ recv arg E_tag Delta Ts Ss n_α n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg c Γ' HIns Hlt Hschemas.
    pose proof Hschemas as HschemasAll.
    assert (HSsClosed : tys_lt_closed c Ss) by (eapply types_wf_lt_closed_from; eauto).
    assert (HrecvWf : ty_wf Γ (type_ctor E_tag Delta Ts)) by (eapply typing_implies_wf; eauto).
    assert (HwfTs : types_wf Γ Ts).
    { inversion HrecvWf; subst. exact H4. }
    assert (HTsClosed : tys_lt_closed c Ts) by (eapply types_wf_lt_closed_from; eauto).
    destruct Hschemas as [_ HeffSchemas].
    destruct (HeffSchemas E_tag n_α n_β sig ret Heff) as [HsigSchema HretSchema].
    assert (HsigInstClosed : ty_lt_closed c sig_inst).
    { rewrite Hsig. eapply inst_op_arg_lt_closed; eauto. }
    assert (HretInstClosed : ty_lt_closed c ret_inst).
    { rewrite Hret. eapply inst_op_arg_lt_closed; eauto. }
    eapply T_Perform with
      (n_α := n_α) (n_β := n_β) (sig := sig) (ret := ret)
      (sig_inst := sig_inst) (ret_inst := ret_inst).
    + exact (IHrecv c Γ' HIns Hlt HschemasAll).
    + rewrite (InsLt_lookup_eff c Γ Γ' HIns E_tag). rewrite Heff. cbn [option_map].
      rewrite (shift_lt_eff_sig_closed_from n_α n_β sig ret c HsigSchema HretSchema).
      reflexivity.
    + exact Hlen_Ts.
    + exact Hlen_Ss.
    + exact (types_wf_InsLt_closed Γ Ss HwfSs c Γ' HIns HSsClosed).
    + exact (forallb_no_local_ty_G_InsLt_closed Γ Ss c Γ' HIns HSsClosed HnoSs).
    + exact Hsig.
    + exact (no_local_ty_G_InsLt_closed Γ sig_inst c Γ' HIns HsigInstClosed HnoSig).
    + exact Hret.
    + exact (ty_wf_InsLt_closed Γ ret_inst HwfRet c Γ' HIns HretInstClosed).
    + exact (IHarg c Γ' HIns Hlt HschemasAll).
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH c Γ' HIns Hlt Hschemas.
    assert (HTBClosed : ty_lt_closed c T_B) by (eapply ty_wf_lt_closed_from; eauto).
    assert (HTRClosed : ty_lt_closed c T_R) by (eapply ty_wf_lt_closed_from; eauto).
    apply T_HandlerM.
    + exact (ty_wf_InsLt_closed Γ T_B HwfTB c Γ' HIns HTBClosed).
    + exact (ty_wf_InsLt_closed Γ T_R HwfTR c Γ' HIns HTRClosed).
    + exact (no_local_ty_G_InsLt_closed Γ T_B c Γ' HIns HTBClosed HnoLocal).
    + exact (sub_InsLt_closed Γ T_B T_R Hsub c Γ' HIns HTBClosed HTRClosed).
    + exact (IH c Γ' HIns Hlt Hschemas).
  - intros Γ m b A T_B T_R HwfA HwfTB HwfTR HnoLocal Hsub Hb IHb c Γ' HIns Hlt Hschemas.
    assert (HAClosed : ty_lt_closed c A) by (eapply ty_wf_lt_closed_from; eauto).
    assert (HTBClosed : ty_lt_closed c T_B) by (eapply ty_wf_lt_closed_from; eauto).
    assert (HTRClosed : ty_lt_closed c T_R) by (eapply ty_wf_lt_closed_from; eauto).
    apply T_Resume.
    + exact (ty_wf_InsLt_closed Γ A HwfA c Γ' HIns HAClosed).
    + exact (ty_wf_InsLt_closed Γ T_B HwfTB c Γ' HIns HTBClosed).
    + exact (ty_wf_InsLt_closed Γ T_R HwfTR c Γ' HIns HTRClosed).
    + exact (no_local_ty_G_InsLt_closed Γ T_B c Γ' HIns HTBClosed HnoLocal).
    + exact (sub_InsLt_closed Γ T_B T_R Hsub c Γ' HIns HTBClosed HTRClosed).
    + apply (IHb c (bind_tm A :: Γ')).
      * exact (InsLt_bind_tm_closed A c Γ Γ' HIns HAClosed).
      * apply ctx_lt_closed_from_bind_tm. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_tm. exact Hschemas.
Qed.

Lemma typing_push_lt_vars_closed_from0 : forall Γ t T,
  Γ ⊢ₜ t : T ->
  forall k Delta,
    ctx_lt_closed_from 0 Γ ->
    ctx_schemas_lt_closed_from 0 Γ ->
    lt_lt_closed 0 Delta ->
    push_lt_vars k Delta Γ ⊢ₜ t : T.
Proof.
  intros Γ t T Hty k. induction k as [|k IH]; intros Delta Hlt Hschemas HDelta; simpl.
  - exact Hty.
  - pose proof (IH Delta Hlt Hschemas HDelta) as Htyped.
    eapply (typing_InsLt_closed_from (push_lt_vars k Delta Γ) t T Htyped k
      (push_lt_vars k Delta (bind_lt Delta :: Γ))).
    + replace k with (0 + k) by lia.
      exact (InsLt_push_lt_vars_closed k Delta 0 Γ (bind_lt Delta :: Γ)
        (InsLt_here Delta Γ) HDelta).
    + replace k with (0 + k) by lia.
      apply ctx_lt_closed_from_push_lt_vars. exact Hlt.
    + replace k with (0 + k) by lia.
      apply ctx_schemas_lt_closed_from_push_lt_vars. exact Hschemas.
Qed.

Lemma typing_push_lt_vars_eval_ctx_closed : forall Γ t T,
  eval_ctx Γ ->
  Γ ⊢ₜ t : T ->
  forall k Delta,
    lt_lt_closed 0 Delta ->
    push_lt_vars k Delta Γ ⊢ₜ t : T.
Proof.
  intros Γ t T Hec Hty k Delta HDelta.
  eapply typing_push_lt_vars_closed_from0; eauto.
  - apply eval_ctx_lt_closed_from. exact Hec.
  - apply eval_ctx_schemas_lt_closed_from. exact Hec.
Qed.

Lemma typing_weaken_lt_shift_eval_ctx_closed : forall Γ Delta t T,
  eval_ctx Γ ->
  Γ ⊢ₜ t : T ->
  lt_lt_closed 0 Delta ->
  tm_lt_closed 0 t ->
  ty_lt_closed 0 T ->
  (bind_lt Delta :: Γ) ⊢ₜ shift_lt_in_tm 1 0 t : shift_lt_in_ty 1 0 T.
Proof.
  intros Γ Delta t T Hec Hty HDelta Htm HT.
  rewrite shift_lt_in_tm_closed by exact Htm.
  rewrite shift_lt_in_type_closed by exact HT.
  change (bind_lt Delta :: Γ) with (push_lt_vars 1 Delta Γ).
  apply typing_push_lt_vars_eval_ctx_closed; assumption.
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

Lemma typing_weaken_lt_shift_closed_from0 : forall Γ Delta t T,
  Γ ⊢ₜ t : T ->
  ctx_lt_closed_from 0 Γ ->
  ctx_schemas_lt_closed_from 0 Γ ->
  tm_lt_closed 0 t ->
  ty_lt_closed 0 T ->
  (bind_lt Delta :: Γ) ⊢ₜ shift_lt_in_tm 1 0 t : shift_lt_in_ty 1 0 T.
Proof.
  intros Γ Delta t T Hty Hlt Hschemas Htm HT.
  rewrite shift_lt_in_tm_closed by exact Htm.
  rewrite shift_lt_in_type_closed by exact HT.
  eapply (typing_InsLt_closed_from Γ t T Hty 0 (bind_lt Delta :: Γ)).
  - apply InsLt_here.
  - exact Hlt.
  - exact Hschemas.
Qed.

Lemma typing_push_ty_vars_any_at_free_closed_from0 : forall Γ t T,
  Γ ⊢ₜ t : T ->
  forall k,
    tm_ty_closed 0 t ->
    ty_ty_closed 0 T ->
    push_ty_vars k any_at_free Γ ⊢ₜ t : T.
Proof.
  intros Γ t T Hty k. induction k as [|k IH]; intros Htm HT; simpl.
  - exact Hty.
  - pose proof (IH Htm HT) as Htyped.
    assert (HIns : InsTy k (push_ty_vars k any_at_free Γ)
      (push_ty_vars k any_at_free (bind_ty any_at_free :: Γ))).
    { pose proof (InsTy_push_ty_vars_any_at_free k 0 Γ (bind_ty any_at_free :: Γ)
        (InsTy_here any_at_free Γ)) as HIns0.
      replace (k + 0) with k in HIns0 by lia. exact HIns0. }
    pose proof (typing_InsTy (push_ty_vars k any_at_free Γ) t T Htyped k
      (push_ty_vars k any_at_free (bind_ty any_at_free :: Γ)) HIns) as Hshifted.
    assert (Htmk : tm_ty_closed k t) by (apply (tm_ty_closed_mono t 0 k); [lia|exact Htm]).
    assert (HTk : ty_ty_closed k T) by (apply (ty_ty_closed_mono T 0 k); [lia|exact HT]).
    rewrite shift_ty_in_tm_closed in Hshifted by exact Htmk.
    rewrite shift_ty_in_ty_closed in Hshifted by exact HTk.
    exact Hshifted.
Qed.

Definition SubstTm_replacement_typed (v : term) (n : nat) (G G' : ctx) : Prop :=
  forall T, ctx_lookup_tm G n = Some T -> G' ⊢ₜ v : T.

Definition SubstTm_target_ty_closed0 (n : nat) (G : ctx) : Prop :=
  forall T, ctx_lookup_tm G n = Some T -> ty_ty_closed 0 T.

Definition SubstTm_target_lt_closed0 (n : nat) (G : ctx) : Prop :=
  forall T, ctx_lookup_tm G n = Some T -> ty_lt_closed 0 T.

Lemma SubstTm_replacement_typed_eval_ctx_push_lt_vars_here : forall Γ v T k Delta,
  eval_ctx Γ ->
  Γ ⊢ₜ v : T ->
  tm_lt_closed 0 v ->
  ty_lt_closed 0 T ->
  lt_lt_closed 0 Delta ->
  SubstTm_replacement_typed (shift_lt_in_tm k 0 v) 0
    (push_lt_vars k Delta (bind_tm T :: Γ))
    (push_lt_vars k Delta Γ).
Proof.
  intros Γ v T k Delta Hec Hty Htm HT HDelta U Hlk.
  rewrite ctx_lookup_tm_push_lt_vars in Hlk. simpl in Hlk.
  inversion Hlk; subst U; clear Hlk.
  rewrite shift_lt_in_tm_closed by exact Htm.
  rewrite shift_lt_in_type_closed by exact HT.
  apply typing_push_lt_vars_eval_ctx_closed; assumption.
Qed.

Lemma SubstTm_replacement_typed_eval_ctx_push_ty_vars_here : forall Γ v T k B,
  Γ ⊢ₜ v : T ->
  SubstTm_replacement_typed (shift_ty_in_tm k 0 v) 0
    (push_ty_vars k B (bind_tm T :: Γ))
    (push_ty_vars k B Γ).
Proof.
  intros Γ v T k B Hty U Hlk.
  rewrite ctx_lookup_tm_push_ty_vars in Hlk. simpl in Hlk.
  inversion Hlk; subst U; clear Hlk.
  apply typing_push_ty_vars_shift. exact Hty.
Qed.

Lemma SubstTm_replacement_typed_eval_ctx_fold_bind_tm_here : forall Γ v T rhos,
  Γ ⊢ₜ v : T ->
  SubstTm_replacement_typed (shift_tm (List.length rhos) 0 v) (List.length rhos)
    (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) (bind_tm T :: Γ) rhos)
    (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos).
Proof.
  intros Γ v T rhos Hty U Hlk.
  replace (List.length rhos) with (0 + List.length rhos) in Hlk by lia.
  rewrite lookup_tm_skip_bind_tm_many in Hlk. simpl in Hlk.
  inversion Hlk; subst U; clear Hlk.
  apply typing_weaken_tm_shift_many. exact Hty.
Qed.

Lemma SubstTm_replacement_typed_eval_ctx_push_lt_fold_bind_tm_here :
  forall Γ v T k Delta rhos,
    eval_ctx Γ ->
    Γ ⊢ₜ v : T ->
    tm_lt_closed 0 v ->
    ty_lt_closed 0 T ->
    lt_lt_closed 0 Delta ->
    SubstTm_replacement_typed
      (shift_tm (List.length rhos) 0 (shift_lt_in_tm k 0 v))
      (List.length rhos)
      (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
        (push_lt_vars k Delta (bind_tm T :: Γ)) rhos)
      (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
        (push_lt_vars k Delta Γ) rhos).
Proof.
  intros Γ v T k Delta rhos Hec Hty Htm HT HDelta U Hlk.
  replace (List.length rhos) with (0 + List.length rhos) in Hlk by lia.
  rewrite lookup_tm_skip_bind_tm_many in Hlk.
  rewrite ctx_lookup_tm_push_lt_vars in Hlk. simpl in Hlk.
  inversion Hlk; subst U; clear Hlk.
  rewrite shift_lt_in_tm_closed by exact Htm.
  rewrite shift_lt_in_type_closed by exact HT.
  apply typing_weaken_tm_shift_many.
  apply typing_push_lt_vars_eval_ctx_closed; assumption.
Qed.

Lemma SubstTm_replacement_typed_eval_ctx_push_ty_fold_bind_tm_here :
  forall Γ v T k B rhos,
    Γ ⊢ₜ v : T ->
    SubstTm_replacement_typed
      (shift_tm (List.length rhos) 0 (shift_ty_in_tm k 0 v))
      (List.length rhos)
      (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
        (push_ty_vars k B (bind_tm T :: Γ)) rhos)
      (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
        (push_ty_vars k B Γ) rhos).
Proof.
  intros Γ v T k B rhos Hty U Hlk.
  replace (List.length rhos) with (0 + List.length rhos) in Hlk by lia.
  rewrite lookup_tm_skip_bind_tm_many in Hlk.
  rewrite ctx_lookup_tm_push_ty_vars in Hlk. simpl in Hlk.
  inversion Hlk; subst U; clear Hlk.
  apply typing_weaken_tm_shift_many.
  apply typing_push_ty_vars_shift. exact Hty.
Qed.

Inductive SubstTm_eval_ctx_provider_shape (Γ : ctx) (v : term) (T : type) :
  term -> nat -> ctx -> ctx -> Prop :=
  | SEPS_here :
      SubstTm_eval_ctx_provider_shape Γ v T
        v 0 (bind_tm T :: Γ) Γ
  | SEPS_fold_bind_tm : forall rhos,
      SubstTm_eval_ctx_provider_shape Γ v T
        (shift_tm (List.length rhos) 0 v) (List.length rhos)
        (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
          (bind_tm T :: Γ) rhos)
        (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos)
  | SEPS_push_lt_vars : forall k Delta,
      lt_lt_closed 0 Delta ->
      SubstTm_eval_ctx_provider_shape Γ v T
        (shift_lt_in_tm k 0 v) 0
        (push_lt_vars k Delta (bind_tm T :: Γ))
        (push_lt_vars k Delta Γ)
  | SEPS_push_ty_vars : forall k B,
      SubstTm_eval_ctx_provider_shape Γ v T
        (shift_ty_in_tm k 0 v) 0
        (push_ty_vars k B (bind_tm T :: Γ))
        (push_ty_vars k B Γ)
  | SEPS_push_lt_fold_bind_tm : forall k Delta rhos,
      lt_lt_closed 0 Delta ->
      SubstTm_eval_ctx_provider_shape Γ v T
        (shift_tm (List.length rhos) 0 (shift_lt_in_tm k 0 v))
        (List.length rhos)
        (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
          (push_lt_vars k Delta (bind_tm T :: Γ)) rhos)
        (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
          (push_lt_vars k Delta Γ) rhos)
  | SEPS_push_ty_fold_bind_tm : forall k B rhos,
      SubstTm_eval_ctx_provider_shape Γ v T
        (shift_tm (List.length rhos) 0 (shift_ty_in_tm k 0 v))
        (List.length rhos)
        (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
          (push_ty_vars k B (bind_tm T :: Γ)) rhos)
        (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
          (push_ty_vars k B Γ) rhos).

Lemma SubstTm_eval_ctx_provider_shape_SubstTm :
  forall Γ v T repl n G G',
    value v ->
    Γ ⊢ₜ v : T ->
    SubstTm_eval_ctx_provider_shape Γ v T repl n G G' ->
    SubstTm repl n G G'.
Proof.
  intros Γ v T repl n G G' Hv Hty Hshape.
  inversion Hshape; subst; clear Hshape.
  - apply SubstTm_here; assumption.
  - replace (List.length rhos) with (0 + List.length rhos) by lia.
    apply SubstTm_fold_bind_tm. apply SubstTm_here; assumption.
  - apply SubstTm_push_lt_vars. apply SubstTm_here; assumption.
  - apply SubstTm_push_ty_vars. apply SubstTm_here; assumption.
  - replace (List.length rhos) with (0 + List.length rhos) by lia.
    apply SubstTm_fold_bind_tm. apply SubstTm_push_lt_vars. apply SubstTm_here; assumption.
  - replace (List.length rhos) with (0 + List.length rhos) by lia.
    apply SubstTm_fold_bind_tm. apply SubstTm_push_ty_vars. apply SubstTm_here; assumption.
Qed.

Lemma SubstTm_replacement_typed_eval_ctx_provider_shape :
  forall Γ v T repl n G G',
    eval_ctx Γ ->
    Γ ⊢ₜ v : T ->
    tm_lt_closed 0 v ->
    ty_lt_closed 0 T ->
    SubstTm_eval_ctx_provider_shape Γ v T repl n G G' ->
    SubstTm_replacement_typed repl n G G'.
Proof.
  intros Γ v T repl n G G' Hec Hty Htm HT Hshape.
  inversion Hshape; subst; clear Hshape.
  - intros U Hlk. simpl in Hlk. inversion Hlk; subst U; clear Hlk. exact Hty.
  - apply SubstTm_replacement_typed_eval_ctx_fold_bind_tm_here. exact Hty.
  - eapply SubstTm_replacement_typed_eval_ctx_push_lt_vars_here; eauto.
  - apply SubstTm_replacement_typed_eval_ctx_push_ty_vars_here. exact Hty.
  - eapply SubstTm_replacement_typed_eval_ctx_push_lt_fold_bind_tm_here; eauto.
  - apply SubstTm_replacement_typed_eval_ctx_push_ty_fold_bind_tm_here. exact Hty.
Qed.

Lemma SubstTm_replacement_typed_fold_bind_tm : forall rhos v n G G',
  SubstTm_replacement_typed v n G G' ->
  SubstTm_replacement_typed (shift_tm (List.length rhos) 0 v) (n + List.length rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G' rhos).
Proof.
  intros rhos v n G G' Hrep T Hlk.
  rewrite lookup_tm_skip_bind_tm_many in Hlk.
  apply typing_weaken_tm_shift_many. apply Hrep. exact Hlk.
Qed.

Lemma SubstTm_replacement_typed_push_ty_vars : forall k B v n G G',
  SubstTm_replacement_typed v n G G' ->
  SubstTm_replacement_typed (shift_ty_in_tm k 0 v) n
    (push_ty_vars k B G) (push_ty_vars k B G').
Proof.
  intros k B v n G G' Hrep T Hlk.
  rewrite ctx_lookup_tm_push_ty_vars in Hlk.
  destruct (ctx_lookup_tm G n) as [T0|] eqn:Hbase; [|discriminate].
  simpl in Hlk. inversion Hlk; subst T; clear Hlk.
  apply typing_push_ty_vars_shift. apply Hrep. exact Hbase.
Qed.

Lemma SubstTm_replacement_typed_push_lt_vars_closed_from0 : forall k Delta v n G G',
  tm_lt_closed 0 v ->
  SubstTm_target_lt_closed0 n G ->
  SubstTm_replacement_typed v n G G' ->
  ctx_lt_closed_from 0 G' ->
  ctx_schemas_lt_closed_from 0 G' ->
  lt_lt_closed 0 Delta ->
  SubstTm_replacement_typed (shift_lt_in_tm k 0 v) n
    (push_lt_vars k Delta G) (push_lt_vars k Delta G').
Proof.
  intros k Delta v n G G' Htm HtargetLt Hrep Hlt Hschemas HDelta T Hlk.
  rewrite ctx_lookup_tm_push_lt_vars in Hlk.
  destruct (ctx_lookup_tm G n) as [T0|] eqn:Hbase; [|discriminate].
  simpl in Hlk. inversion Hlk; subst T; clear Hlk.
  rewrite shift_lt_in_tm_closed by exact Htm.
  rewrite shift_lt_in_type_closed by (apply HtargetLt; exact Hbase).
  eapply typing_push_lt_vars_closed_from0; eauto.
Qed.

Lemma SubstTm_replacement_typed_eval_ctx_fold_push_lt_fold_bind_tm_here :
  forall Γ v T lower k Delta upper,
    eval_ctx Γ ->
    Γ ⊢ₜ v : T ->
    tm_lt_closed 0 v ->
    ty_lt_closed 0 T ->
    lt_lt_closed 0 Delta ->
    SubstTm_replacement_typed
      (shift_tm (List.length upper) 0
        (shift_lt_in_tm k 0 (shift_tm (List.length lower) 0 v)))
      (List.length lower + List.length upper)
      (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
        (push_lt_vars k Delta
          (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
            (bind_tm T :: Γ) lower)) upper)
      (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
        (push_lt_vars k Delta
          (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ lower)) upper).
Proof.
  intros Γ v T lower k Delta upper Hec Hty Htm HT HDelta.
  assert (HtargetBase : SubstTm_target_lt_closed0 0 (bind_tm T :: Γ)).
  { intros U Hlk. simpl in Hlk. inversion Hlk; subst U; clear Hlk. exact HT. }
  assert (HtargetLower : SubstTm_target_lt_closed0 (List.length lower)
    (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) (bind_tm T :: Γ) lower)).
  { intros U Hlk.
    replace (List.length lower) with (0 + List.length lower) in Hlk by lia.
    rewrite lookup_tm_skip_bind_tm_many in Hlk. apply HtargetBase. exact Hlk. }
  pose proof (SubstTm_replacement_typed_eval_ctx_fold_bind_tm_here Γ v T lower Hty)
    as HrepLower.
  pose proof (SubstTm_replacement_typed_push_lt_vars_closed_from0 k Delta
    (shift_tm (List.length lower) 0 v) (List.length lower)
    (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) (bind_tm T :: Γ) lower)
    (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ lower)
    (tm_lt_closed_shift_tm v 0 (List.length lower) 0 Htm)
    HtargetLower HrepLower
    (ctx_lt_closed_from_fold_bind_tm lower 0 Γ (eval_ctx_lt_closed_from Γ Hec))
    (ctx_schemas_lt_closed_from_fold_bind_tm lower 0 Γ (eval_ctx_schemas_lt_closed_from Γ Hec))
    HDelta) as HrepPush.
  exact (SubstTm_replacement_typed_fold_bind_tm upper
    (shift_lt_in_tm k 0 (shift_tm (List.length lower) 0 v))
    (List.length lower)
    (push_lt_vars k Delta
      (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) (bind_tm T :: Γ) lower))
    (push_lt_vars k Delta
      (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ lower))
    HrepPush).
Qed.

Lemma SubstTm_replacement_typed_eval_ctx_fold_push_ty_fold_bind_tm_here :
  forall Γ v T lower k B upper,
    Γ ⊢ₜ v : T ->
    SubstTm_replacement_typed
      (shift_tm (List.length upper) 0
        (shift_ty_in_tm k 0 (shift_tm (List.length lower) 0 v)))
      (List.length lower + List.length upper)
      (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
        (push_ty_vars k B
          (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
            (bind_tm T :: Γ) lower)) upper)
      (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
        (push_ty_vars k B
          (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ lower)) upper).
Proof.
  intros Γ v T lower k B upper Hty.
  pose proof (SubstTm_replacement_typed_eval_ctx_fold_bind_tm_here Γ v T lower Hty)
    as HrepLower.
  pose proof (SubstTm_replacement_typed_push_ty_vars k B
    (shift_tm (List.length lower) 0 v) (List.length lower)
    (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) (bind_tm T :: Γ) lower)
    (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ lower)
    HrepLower) as HrepPush.
  exact (SubstTm_replacement_typed_fold_bind_tm upper
    (shift_ty_in_tm k 0 (shift_tm (List.length lower) 0 v))
    (List.length lower)
    (push_ty_vars k B
      (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) (bind_tm T :: Γ) lower))
    (push_ty_vars k B
      (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ lower))
    HrepPush).
Qed.

Lemma SubstTm_replacement_typed_tm : forall v n G G' A,
  SubstTm_replacement_typed v n G G' ->
  SubstTm_replacement_typed (shift_tm 1 0 v) (S n) (bind_tm A :: G) (bind_tm A :: G').
Proof.
  intros v n G G' A Hrep T Hlk. simpl in Hlk.
  eapply typing_InsTmAt.
  - apply Hrep. exact Hlk.
  - apply InsTmAt_here.
Qed.

Lemma SubstTm_replacement_typed_ty : forall v n G G' B,
  SubstTm_replacement_typed v n G G' ->
  SubstTm_replacement_typed (shift_ty_in_tm 1 0 v) n (bind_ty B :: G) (bind_ty B :: G').
Proof.
  intros v n G G' B Hrep T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm G n) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst; clear Hlk.
  apply typing_weaken_ty_shift. apply Hrep. exact Hbase.
Qed.

Lemma SubstTm_replacement_typed_lt_closed_from0 : forall v n G G' D,
  free_tm_vars 0 v = [] ->
  tm_lt_closed 0 v ->
  SubstTm_target_lt_closed0 n G ->
  SubstTm_replacement_typed v n G G' ->
  ctx_lt_closed_from 0 G' ->
  ctx_schemas_lt_closed_from 0 G' ->
  SubstTm_replacement_typed (shift_lt_in_tm 1 0 v) n (bind_lt D :: G) (bind_lt D :: G').
Proof.
  intros v n G G' D Hfree HtmLt HtargetLt Hrep Hlt Hschemas T Hlk.
  simpl in Hlk. destruct (ctx_lookup_tm G n) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst; clear Hlk.
  rewrite shift_lt_in_tm_closed by exact HtmLt.
  rewrite shift_lt_in_type_closed by (apply HtargetLt; exact Hbase).
  eapply typing_InsLt_closed_from.
  - apply Hrep. exact Hbase.
  - apply InsLt_here.
  - exact Hlt.
  - exact Hschemas.
Qed.

Inductive SubstTm_eval_ctx_prefix (Γ : ctx) (v : term) (T : type) :
  term -> nat -> ctx -> ctx -> Prop :=
  | SETP_here :
      SubstTm_eval_ctx_prefix Γ v T v 0 (bind_tm T :: Γ) Γ
  | SETP_tm : forall repl n G G' A,
      SubstTm_eval_ctx_prefix Γ v T repl n G G' ->
      SubstTm_eval_ctx_prefix Γ v T
        (shift_tm 1 0 repl) (S n) (bind_tm A :: G) (bind_tm A :: G')
  | SETP_ty : forall repl n G G' B,
      SubstTm_eval_ctx_prefix Γ v T repl n G G' ->
      SubstTm_eval_ctx_prefix Γ v T
        (shift_ty_in_tm 1 0 repl) n (bind_ty B :: G) (bind_ty B :: G')
  | SETP_fold_bind_tm : forall rhos repl n G G',
      SubstTm_eval_ctx_prefix Γ v T repl n G G' ->
      SubstTm_eval_ctx_prefix Γ v T
        (shift_tm (List.length rhos) 0 repl) (n + List.length rhos)
        (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
        (List.fold_right (fun rho G0 => bind_tm rho :: G0) G' rhos)
  | SETP_push_ty_vars : forall k B repl n G G',
      SubstTm_eval_ctx_prefix Γ v T repl n G G' ->
      SubstTm_eval_ctx_prefix Γ v T
        (shift_ty_in_tm k 0 repl) n
        (push_ty_vars k B G) (push_ty_vars k B G')
  | SETP_push_lt_vars_closed0 : forall k Delta repl n G G',
      SubstTm_eval_ctx_prefix Γ v T repl n G G' ->
      tm_lt_closed 0 repl ->
      SubstTm_target_lt_closed0 n G ->
      ctx_lt_closed_from 0 G' ->
      ctx_schemas_lt_closed_from 0 G' ->
      lt_lt_closed 0 Delta ->
      SubstTm_eval_ctx_prefix Γ v T
        (shift_lt_in_tm k 0 repl) n
        (push_lt_vars k Delta G) (push_lt_vars k Delta G').

Lemma SubstTm_eval_ctx_prefix_SubstTm :
  forall Γ v T repl n G G',
    value v ->
    Γ ⊢ₜ v : T ->
    SubstTm_eval_ctx_prefix Γ v T repl n G G' ->
    SubstTm repl n G G'.
Proof.
  intros Γ v T repl n G G' Hv Hty Hprefix.
  induction Hprefix.
  - apply SubstTm_here; assumption.
  - apply SubstTm_tm. exact IHHprefix.
  - apply SubstTm_ty. exact IHHprefix.
  - apply SubstTm_fold_bind_tm. exact IHHprefix.
  - apply SubstTm_push_ty_vars. exact IHHprefix.
  - apply SubstTm_push_lt_vars. exact IHHprefix.
Qed.

Lemma SubstTm_eval_ctx_prefix_replacement_typed :
  forall Γ v T repl n G G',
    Γ ⊢ₜ v : T ->
    SubstTm_eval_ctx_prefix Γ v T repl n G G' ->
    SubstTm_replacement_typed repl n G G'.
Proof.
  intros Γ v T repl n G G' Hty Hprefix.
  induction Hprefix.
  - intros U Hlk. simpl in Hlk. inversion Hlk; subst U; clear Hlk. exact Hty.
  - apply SubstTm_replacement_typed_tm. exact IHHprefix.
  - apply SubstTm_replacement_typed_ty. exact IHHprefix.
  - apply SubstTm_replacement_typed_fold_bind_tm. exact IHHprefix.
  - apply SubstTm_replacement_typed_push_ty_vars. exact IHHprefix.
  - eapply SubstTm_replacement_typed_push_lt_vars_closed_from0; eauto.
Qed.

Lemma SubstTm_target_ty_closed0_tm : forall n G A,
  SubstTm_target_ty_closed0 n G ->
  SubstTm_target_ty_closed0 (S n) (bind_tm A :: G).
Proof.
  intros n G A Htarget T Hlk. simpl in Hlk. apply Htarget. exact Hlk.
Qed.

Lemma SubstTm_target_ty_closed0_ty : forall n G B,
  SubstTm_target_ty_closed0 n G ->
  SubstTm_target_ty_closed0 n (bind_ty B :: G).
Proof.
  intros n G B Htarget T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm G n) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst; clear Hlk.
  rewrite shift_ty_in_ty_closed by (apply Htarget; exact Hbase).
  apply Htarget. exact Hbase.
Qed.

Lemma SubstTm_target_ty_closed0_lt : forall n G D,
  SubstTm_target_ty_closed0 n G ->
  SubstTm_target_ty_closed0 n (bind_lt D :: G).
Proof.
  intros n G D Htarget T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm G n) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst; clear Hlk.
  apply ty_ty_closed_shift_lt. apply Htarget. exact Hbase.
Qed.

Lemma SubstTm_target_lt_closed0_tm : forall n G A,
  SubstTm_target_lt_closed0 n G ->
  SubstTm_target_lt_closed0 (S n) (bind_tm A :: G).
Proof.
  intros n G A Htarget T Hlk. simpl in Hlk. apply Htarget. exact Hlk.
Qed.

Lemma SubstTm_target_lt_closed0_ty : forall n G B,
  SubstTm_target_lt_closed0 n G ->
  SubstTm_target_lt_closed0 n (bind_ty B :: G).
Proof.
  intros n G B Htarget T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm G n) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst; clear Hlk.
  apply ty_lt_closed_shift_ty. apply Htarget. exact Hbase.
Qed.

Lemma SubstTm_target_lt_closed0_lt : forall n G D,
  SubstTm_target_lt_closed0 n G ->
  SubstTm_target_lt_closed0 n (bind_lt D :: G).
Proof.
  intros n G D Htarget T Hlk. simpl in Hlk.
  destruct (ctx_lookup_tm G n) as [T0|] eqn:Hbase; [|discriminate].
  inversion Hlk; subst; clear Hlk.
  rewrite shift_lt_in_type_closed by (apply Htarget; exact Hbase).
  apply Htarget. exact Hbase.
Qed.

Lemma SubstTm_target_ty_closed0_ctor : forall n G K n_lt n_ty fields result,
  SubstTm_target_ty_closed0 n G ->
  SubstTm_target_ty_closed0 n (bind_ctor K n_lt n_ty fields result :: G).
Proof.
  intros n G K n_lt n_ty fields result Htarget T Hlk.
  simpl in Hlk. apply Htarget. exact Hlk.
Qed.

Lemma SubstTm_target_ty_closed0_eff : forall n G E n_a n_b sig ret,
  SubstTm_target_ty_closed0 n G ->
  SubstTm_target_ty_closed0 n (bind_eff E n_a n_b sig ret :: G).
Proof.
  intros n G E n_a n_b sig ret Htarget T Hlk.
  simpl in Hlk. apply Htarget. exact Hlk.
Qed.

Lemma SubstTm_target_lt_closed0_ctor : forall n G K n_lt n_ty fields result,
  SubstTm_target_lt_closed0 n G ->
  SubstTm_target_lt_closed0 n (bind_ctor K n_lt n_ty fields result :: G).
Proof.
  intros n G K n_lt n_ty fields result Htarget T Hlk.
  simpl in Hlk. apply Htarget. exact Hlk.
Qed.

Lemma SubstTm_target_lt_closed0_eff : forall n G E n_a n_b sig ret,
  SubstTm_target_lt_closed0 n G ->
  SubstTm_target_lt_closed0 n (bind_eff E n_a n_b sig ret :: G).
Proof.
  intros n G E n_a n_b sig ret Htarget T Hlk.
  simpl in Hlk. apply Htarget. exact Hlk.
Qed.

Lemma SubstTm_target_ty_closed0_push_lt_vars : forall k Delta n G,
  SubstTm_target_ty_closed0 n G ->
  SubstTm_target_ty_closed0 n (push_lt_vars k Delta G).
Proof.
  induction k as [|k IH]; intros Delta n G Htarget; simpl.
  - exact Htarget.
  - apply IH. apply SubstTm_target_ty_closed0_lt. exact Htarget.
Qed.

Lemma SubstTm_target_lt_closed0_push_lt_vars : forall k Delta n G,
  SubstTm_target_lt_closed0 n G ->
  SubstTm_target_lt_closed0 n (push_lt_vars k Delta G).
Proof.
  induction k as [|k IH]; intros Delta n G Htarget; simpl.
  - exact Htarget.
  - apply IH. apply SubstTm_target_lt_closed0_lt. exact Htarget.
Qed.

Lemma SubstTm_target_ty_closed0_push_ty_vars : forall k B n G,
  SubstTm_target_ty_closed0 n G ->
  SubstTm_target_ty_closed0 n (push_ty_vars k B G).
Proof.
  induction k as [|k IH]; intros B n G Htarget; simpl.
  - exact Htarget.
  - apply IH. apply SubstTm_target_ty_closed0_ty. exact Htarget.
Qed.

Lemma SubstTm_target_lt_closed0_push_ty_vars : forall k B n G,
  SubstTm_target_lt_closed0 n G ->
  SubstTm_target_lt_closed0 n (push_ty_vars k B G).
Proof.
  induction k as [|k IH]; intros B n G Htarget; simpl.
  - exact Htarget.
  - apply IH. apply SubstTm_target_lt_closed0_ty. exact Htarget.
Qed.

Lemma SubstTm_target_ty_closed0_fold_bind_tm : forall rhos n G,
  SubstTm_target_ty_closed0 n G ->
  SubstTm_target_ty_closed0 (n + List.length rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos).
Proof.
  intros rhos n G Htarget T Hlk.
  rewrite lookup_tm_skip_bind_tm_many in Hlk.
  apply Htarget. exact Hlk.
Qed.

Lemma SubstTm_target_lt_closed0_fold_bind_tm : forall rhos n G,
  SubstTm_target_lt_closed0 n G ->
  SubstTm_target_lt_closed0 (n + List.length rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos).
Proof.
  intros rhos n G Htarget T Hlk.
  rewrite lookup_tm_skip_bind_tm_many in Hlk.
  apply Htarget. exact Hlk.
Qed.

Lemma SubstTm_eval_ctx_prefix_free_tm_vars_closed :
  forall Γ v T repl n G G',
    free_tm_vars 0 v = [] ->
    SubstTm_eval_ctx_prefix Γ v T repl n G G' ->
    free_tm_vars 0 repl = [].
Proof.
  intros Γ v T repl n G G' Hfree Hprefix.
  induction Hprefix.
  - exact Hfree.
  - apply free_tm_vars_closed_shift_tm_any. exact IHHprefix.
  - rewrite free_tm_vars_shift_ty_in_tm_any. exact IHHprefix.
  - apply free_tm_vars_closed_shift_tm_any. exact IHHprefix.
  - rewrite free_tm_vars_shift_ty_in_tm_any. exact IHHprefix.
  - rewrite free_tm_vars_shift_lt_in_tm_any. exact IHHprefix.
Qed.

Lemma SubstTm_eval_ctx_prefix_tm_ty_closed0 :
  forall Γ v T repl n G G',
    tm_ty_closed 0 v ->
    SubstTm_eval_ctx_prefix Γ v T repl n G G' ->
    tm_ty_closed 0 repl.
Proof.
  intros Γ v T repl n G G' Hclosed Hprefix.
  induction Hprefix.
  - exact Hclosed.
  - apply tm_ty_closed_shift_tm. exact IHHprefix.
  - apply tm_ty_closed_shift_ty_closed0. exact IHHprefix.
  - apply tm_ty_closed_shift_tm. exact IHHprefix.
  - apply tm_ty_closed_shift_ty_closed0. exact IHHprefix.
  - apply tm_ty_closed_shift_lt. exact IHHprefix.
Qed.

Lemma SubstTm_eval_ctx_prefix_tm_lt_closed0 :
  forall Γ v T repl n G G',
    tm_lt_closed 0 v ->
    SubstTm_eval_ctx_prefix Γ v T repl n G G' ->
    tm_lt_closed 0 repl.
Proof.
  intros Γ v T repl n G G' Hclosed Hprefix.
  induction Hprefix.
  - exact Hclosed.
  - apply tm_lt_closed_shift_tm. exact IHHprefix.
  - apply tm_lt_closed_shift_ty. exact IHHprefix.
  - apply tm_lt_closed_shift_tm. exact IHHprefix.
  - apply tm_lt_closed_shift_ty. exact IHHprefix.
  - apply tm_lt_closed_shift_lt_closed0. exact IHHprefix.
Qed.

Lemma SubstTm_eval_ctx_prefix_target_ty_closed0 :
  forall Γ v T repl n G G',
    ty_ty_closed 0 T ->
    SubstTm_eval_ctx_prefix Γ v T repl n G G' ->
    SubstTm_target_ty_closed0 n G.
Proof.
  intros Γ v T repl n G G' HT Hprefix.
  induction Hprefix.
  - intros U Hlk. simpl in Hlk. inversion Hlk; subst U; clear Hlk. exact HT.
  - apply SubstTm_target_ty_closed0_tm. exact IHHprefix.
  - apply SubstTm_target_ty_closed0_ty. exact IHHprefix.
  - apply SubstTm_target_ty_closed0_fold_bind_tm. exact IHHprefix.
  - apply SubstTm_target_ty_closed0_push_ty_vars. exact IHHprefix.
  - apply SubstTm_target_ty_closed0_push_lt_vars. exact IHHprefix.
Qed.

Lemma SubstTm_eval_ctx_prefix_target_lt_closed0 :
  forall Γ v T repl n G G',
    ty_lt_closed 0 T ->
    SubstTm_eval_ctx_prefix Γ v T repl n G G' ->
    SubstTm_target_lt_closed0 n G.
Proof.
  intros Γ v T repl n G G' HT Hprefix.
  induction Hprefix.
  - intros U Hlk. simpl in Hlk. inversion Hlk; subst U; clear Hlk. exact HT.
  - apply SubstTm_target_lt_closed0_tm. exact IHHprefix.
  - apply SubstTm_target_lt_closed0_ty. exact IHHprefix.
  - apply SubstTm_target_lt_closed0_fold_bind_tm. exact IHHprefix.
  - apply SubstTm_target_lt_closed0_push_ty_vars. exact IHHprefix.
  - apply SubstTm_target_lt_closed0_push_lt_vars. exact IHHprefix.
Qed.

Lemma SubstTm_eval_ctx_prefix_side_conditions :
  forall Γ v T repl n G G',
    eval_ctx Γ ->
    value v ->
    Γ ⊢ₜ v : T ->
    free_tm_vars 0 v = [] ->
    SubstTm_eval_ctx_prefix Γ v T repl n G G' ->
    SubstTm repl n G G' /\
    value repl /\
    free_tm_vars 0 repl = [] /\
    tm_ty_closed 0 repl /\
    tm_lt_closed 0 repl /\
    SubstTm_target_ty_closed0 n G /\
    SubstTm_target_lt_closed0 n G /\
    SubstTm_replacement_typed repl n G G'.
Proof.
  intros Γ v T repl n G G' Hec Hv Hty Hfree Hprefix.
  pose proof (SubstTm_eval_ctx_prefix_SubstTm Γ v T repl n G G' Hv Hty Hprefix) as HSub.
  pose proof (typing_eval_ctx_tm_ty_closed Γ v T Hec Hty) as HtmTy.
  pose proof (typing_eval_ctx_tm_lt_closed Γ v T Hec Hty) as HtmLt.
  pose proof (typing_implies_wf Γ v T Hty) as HwfT.
  pose proof (ty_wf_eval_ctx_ty_closed Γ T Hec HwfT) as HTy.
  pose proof (ty_wf_eval_ctx_lt_closed Γ T Hec HwfT) as HTl.
  repeat split.
  - exact HSub.
  - exact (SubstTm_value repl n G G' HSub).
  - exact (SubstTm_eval_ctx_prefix_free_tm_vars_closed Γ v T repl n G G' Hfree Hprefix).
  - exact (SubstTm_eval_ctx_prefix_tm_ty_closed0 Γ v T repl n G G' HtmTy Hprefix).
  - exact (SubstTm_eval_ctx_prefix_tm_lt_closed0 Γ v T repl n G G' HtmLt Hprefix).
  - exact (SubstTm_eval_ctx_prefix_target_ty_closed0 Γ v T repl n G G' HTy Hprefix).
  - exact (SubstTm_eval_ctx_prefix_target_lt_closed0 Γ v T repl n G G' HTl Hprefix).
  - exact (SubstTm_eval_ctx_prefix_replacement_typed Γ v T repl n G G' Hty Hprefix).
Qed.

Lemma SubstTm_eval_ctx_prefix_ctx_schemas_lt_closed_from0_left :
  forall Γ v T repl n G G',
    eval_ctx Γ ->
    SubstTm_eval_ctx_prefix Γ v T repl n G G' ->
    ctx_schemas_lt_closed_from 0 G.
Proof.
  intros Γ v T repl n G G' Hec Hprefix.
  induction Hprefix.
  - apply ctx_schemas_lt_closed_from_bind_tm.
    apply eval_ctx_schemas_lt_closed_from. exact Hec.
  - apply ctx_schemas_lt_closed_from_bind_tm. exact IHHprefix.
  - apply ctx_schemas_lt_closed_from_bind_ty. exact IHHprefix.
  - apply ctx_schemas_lt_closed_from_fold_bind_tm. exact IHHprefix.
  - apply ctx_schemas_lt_closed_from_push_ty_vars. exact IHHprefix.
  - apply ctx_schemas_lt_closed_from0_push_lt_vars. exact IHHprefix.
Qed.

Lemma SubstTm_eval_ctx_prefix_ctx_schemas_lt_closed_from0_right :
  forall Γ v T repl n G G',
    eval_ctx Γ ->
    SubstTm_eval_ctx_prefix Γ v T repl n G G' ->
    ctx_schemas_lt_closed_from 0 G'.
Proof.
  intros Γ v T repl n G G' Hec Hprefix.
  induction Hprefix.
  - apply eval_ctx_schemas_lt_closed_from. exact Hec.
  - apply ctx_schemas_lt_closed_from_bind_tm. exact IHHprefix.
  - apply ctx_schemas_lt_closed_from_bind_ty. exact IHHprefix.
  - apply ctx_schemas_lt_closed_from_fold_bind_tm. exact IHHprefix.
  - apply ctx_schemas_lt_closed_from_push_ty_vars. exact IHHprefix.
  - apply ctx_schemas_lt_closed_from0_push_lt_vars. exact IHHprefix.
Qed.

Lemma Forall2_typing_SubstTm_closed : forall Γ vs rhos,
  Forall2 (fun v rho => forall repl n G',
    SubstTm repl n Γ G' ->
    free_tm_vars 0 repl = [] ->
    tm_ty_closed 0 repl ->
    tm_lt_closed 0 repl ->
    SubstTm_target_ty_closed0 n Γ ->
    SubstTm_target_lt_closed0 n Γ ->
    SubstTm_replacement_typed repl n Γ G' ->
    forall c,
    ctx_lt_closed_from c G' ->
    ctx_schemas_lt_closed_from c G' ->
    G' ⊢ₗ capture_lt G' repl <: capture_var_lifetime Γ n ->
    G' ⊢ₜ subst_tm n repl v : rho) vs rhos ->
  forall repl n G',
    SubstTm repl n Γ G' ->
    free_tm_vars 0 repl = [] ->
    tm_ty_closed 0 repl ->
    tm_lt_closed 0 repl ->
    SubstTm_target_ty_closed0 n Γ ->
    SubstTm_target_lt_closed0 n Γ ->
    SubstTm_replacement_typed repl n Γ G' ->
    forall c,
    ctx_lt_closed_from c G' ->
    ctx_schemas_lt_closed_from c G' ->
    G' ⊢ₗ capture_lt G' repl <: capture_var_lifetime Γ n ->
    Forall2 (fun v rho => G' ⊢ₜ v : rho)
             (List.map (subst_tm n repl) vs) rhos.
Proof.
  intros Γ vs rhos H. induction H; intros repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt Hrep c Hlt Hschemas Hcap; simpl.
  - constructor.
  - constructor.
    + apply (H repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt Hrep c Hlt Hschemas Hcap).
    + apply (IHForall2 repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt Hrep c Hlt Hschemas Hcap).
Qed.

Lemma Forall2_typing_SubstTm_global : forall Γ vs rhos,
  Forall2 (fun v rho => forall repl n G',
    SubstTm repl n Γ G' ->
    free_tm_vars 0 repl = [] ->
    tm_ty_closed 0 repl ->
    tm_lt_closed 0 repl ->
    SubstTm_target_ty_closed0 n Γ ->
    SubstTm_target_lt_closed0 n Γ ->
    (forall repl0 n0 G0 G0',
      SubstTm repl0 n0 G0 G0' ->
      SubstTm_replacement_typed repl0 n0 G0 G0') ->
    forall c,
    ctx_lt_closed_from c G' ->
    ctx_schemas_lt_closed_from c G' ->
    G' ⊢ₗ capture_lt G' repl <: capture_var_lifetime Γ n ->
    G' ⊢ₜ subst_tm n repl v : rho) vs rhos ->
  forall repl n G',
    SubstTm repl n Γ G' ->
    free_tm_vars 0 repl = [] ->
    tm_ty_closed 0 repl ->
    tm_lt_closed 0 repl ->
    SubstTm_target_ty_closed0 n Γ ->
    SubstTm_target_lt_closed0 n Γ ->
    (forall repl0 n0 G0 G0',
      SubstTm repl0 n0 G0 G0' ->
      SubstTm_replacement_typed repl0 n0 G0 G0') ->
    forall c,
    ctx_lt_closed_from c G' ->
    ctx_schemas_lt_closed_from c G' ->
    G' ⊢ₗ capture_lt G' repl <: capture_var_lifetime Γ n ->
    Forall2 (fun v rho => G' ⊢ₜ v : rho)
             (List.map (subst_tm n repl) vs) rhos.
Proof.
  intros Γ vs rhos H. induction H; intros repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap; simpl.
  - constructor.
  - constructor.
    + apply (H repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    + apply (IHForall2 repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
Qed.

Lemma typing_SubstTm : forall Γ t T,
  Γ ⊢ₜ t : T ->
  forall repl n G',
    SubstTm repl n Γ G' ->
    free_tm_vars 0 repl = [] ->
    tm_ty_closed 0 repl ->
    tm_lt_closed 0 repl ->
    SubstTm_target_ty_closed0 n Γ ->
    SubstTm_target_lt_closed0 n Γ ->
    (forall repl0 n0 G0 G0',
      SubstTm repl0 n0 G0 G0' ->
      SubstTm_replacement_typed repl0 n0 G0 G0') ->
    forall c,
    ctx_lt_closed_from c G' ->
    ctx_schemas_lt_closed_from c G' ->
    G' ⊢ₗ capture_lt G' repl <: capture_var_lifetime Γ n ->
    G' ⊢ₜ subst_tm n repl t : T.
Proof.
  apply (typing_ind_forall2
    (fun Γ t T => forall repl n G',
      SubstTm repl n Γ G' ->
      free_tm_vars 0 repl = [] ->
      tm_ty_closed 0 repl ->
      tm_lt_closed 0 repl ->
      SubstTm_target_ty_closed0 n Γ ->
      SubstTm_target_lt_closed0 n Γ ->
      (forall repl0 n0 G0 G0',
        SubstTm repl0 n0 G0 G0' ->
        SubstTm_replacement_typed repl0 n0 G0 G0') ->
      forall c,
      ctx_lt_closed_from c G' ->
      ctx_schemas_lt_closed_from c G' ->
      G' ⊢ₗ capture_lt G' repl <: capture_var_lifetime Γ n ->
      G' ⊢ₜ subst_tm n repl t : T)).
  - intros Γ x T Hlk HwfT repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. destruct (Nat.eqb x n) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst x.
      exact (HrepAll repl n Γ G' HSub T Hlk).
    + apply Nat.eqb_neq in Heq.
      destruct (Nat.ltb n x) eqn:Hltx.
      * apply T_Var.
        -- assert (Hidx : slv n x = pred x) by (unfold slv; rewrite Hltx; reflexivity).
          rewrite <- Hidx.
          rewrite (SubstTm_lookup_tm repl n Γ G' HSub x Heq). exact Hlk.
        -- eapply ty_wf_SubstTm; eauto.
      * apply T_Var.
        -- assert (Hidx : slv n x = x) by (unfold slv; rewrite Hltx; reflexivity).
          rewrite <- Hidx.
          rewrite (SubstTm_lookup_tm repl n Γ G' HSub x Heq). exact Hlk.
        -- eapply ty_wf_SubstTm; eauto.
  - intros Γ t T U Ht IH Hsub repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    eapply T_Sub.
    + apply (IH repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    + eapply sub_SubstTm; eauto.
  - intros Γ body A l B HwfA HwfB Hbody IHbody HcapLam repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas HcapRepl.
    simpl. apply T_Lam.
    + eapply ty_wf_SubstTm; eauto.
    + eapply ty_wf_SubstTm; eauto.
    + apply (IHbody (shift_tm 1 0 repl) (S n) (bind_tm A :: G')
      (SubstTm_tm repl n Γ G' A HSub)
      (free_tm_vars_closed_shift_tm_any 1 repl Hfree)
      (tm_ty_closed_shift_tm repl 0 1 0 HtmTy)
      (tm_lt_closed_shift_tm repl 0 1 0 HtmLt)
      (SubstTm_target_ty_closed0_tm n Γ A HtargetTy)
      (SubstTm_target_lt_closed0_tm n Γ A HtargetLt)
      HrepAll c).
      * apply ctx_lt_closed_from_bind_tm. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_tm. exact Hschemas.
      * apply replacement_capture_bound_tm; assumption.
    + destruct (lt_sub_wf _ _ _ HcapLam) as [HwfCap _].
      eapply LS_Trans.
      * eapply capture_lt_SubstTm_le_closed; eauto.
      * eapply lt_sub_SubstTm; eauto.
  - intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. eapply T_App.
    + apply (IH1 repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    + apply (IH2 repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
  - intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. apply T_TyLam.
    + eapply ty_wf_SubstTm; eauto.
    + eapply ty_wf_SubstTm; [exact HwfT|]. apply SubstTm_ty. exact HSub.
    + apply is_abs_subst_tm_true. exact HisAbs.
    + apply (IHbody (shift_ty_in_tm 1 0 repl) n (bind_ty bound :: G')
      (SubstTm_ty repl n Γ G' bound HSub)
      ltac:(rewrite free_tm_vars_shift_ty_in_tm; exact Hfree)
      (tm_ty_closed_shift_ty_closed0 repl 1 HtmTy)
      (tm_lt_closed_shift_ty repl 0 1 0 HtmLt)
      (SubstTm_target_ty_closed0_ty n Γ bound HtargetTy)
      (SubstTm_target_lt_closed0_ty n Γ bound HtargetLt)
      HrepAll c).
      * apply ctx_lt_closed_from_bind_ty. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_ty. exact Hschemas.
      * apply replacement_capture_bound_ty; assumption.
  - intros Γ t B U S Ht IH HwfS Hsub HnlArg repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. eapply T_TyApp.
    + apply (IH repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    + eapply ty_wf_SubstTm; eauto.
    + eapply sub_SubstTm; eauto.
    + eapply ty_app_arg_no_local_SubstTm; eauto.
  - intros Γ body T HwfT HisAbs Hbody IHbody repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. apply T_LtLam.
    + eapply ty_wf_SubstTm; [exact HwfT|]. apply SubstTm_lt. exact HSub.
    + apply is_abs_subst_tm_true. exact HisAbs.
    + apply (IHbody (shift_lt_in_tm 1 0 repl) n (bind_lt lt_local :: G')
      (SubstTm_lt repl n Γ G' lt_local HSub)
      ltac:(rewrite free_tm_vars_shift_lt_in_tm; exact Hfree)
      (tm_ty_closed_shift_lt repl 0 1 0 HtmTy)
      (tm_lt_closed_shift_lt_closed0 repl 1 HtmLt)
      (SubstTm_target_ty_closed0_lt n Γ lt_local HtargetTy)
      (SubstTm_target_lt_closed0_lt n Γ lt_local HtargetLt)
      HrepAll (S c)).
      * apply ctx_lt_closed_from_bind_lt. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_lt. exact Hschemas.
      * apply replacement_capture_bound_lt; assumption.
  - intros Γ t T l Ht IH Hwfl repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. eapply T_LtApp.
    + apply (IH repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    + eapply lt_wf_SubstTm; eauto.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
      result_ty result_tag l vs Hctor Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs Hresult Hshape
      Hresult_eff Hwfl HltSub Hbounded Hlen_vs Hargs IHargs repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. rewrite subst_tm_go_eq_map.
    eapply T_Ctor with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := sigma_fields) (result_ty_schema := result_ty_schema)
      (lts := lts) (rho_fields := rho_fields) (result_tag := result_tag).
    + rewrite (SubstTm_lookup_ctor repl n Γ G' HSub K). exact Hctor.
    + rewrite (SubstTm_lookup_eff repl n Γ G' HSub K). exact Heff.
    + exact Hlen_lts.
    + eapply lifetimes_wf_SubstTm; eauto.
    + exact Hrho.
    + exact Hlen_Ts.
    + eapply types_wf_SubstTm; eauto.
    + exact Hresult.
    + exact Hshape.
    + rewrite (SubstTm_lookup_eff repl n Γ G' HSub result_tag). exact Hresult_eff.
    + eapply lt_wf_SubstTm; eauto.
    + eapply lt_sub_SubstTm; eauto.
    + eapply Forall_impl.
      * intros l0 Hl0. exact (lt_sub_SubstTm Γ l0 l Hl0 repl n G' HSub).
      * exact Hbounded.
    + rewrite length_map. exact Hlen_vs.
    + exact (Forall2_typing_SubstTm_global Γ vs rho_fields IHargs
      repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    all: try solve [eauto].
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
      rho_fields scrut_result_ty result_tag result_l Γyes yes_body eta elim_result no_body
      HKne Hctor Heff Hlts Hrho Hlen_Ts HwfTs Hscrut_result Hscrut_shape Hresult_eff Hresult_ne
      HwfDelta Hresult_l Hscrut IHscrut Harity HΓyes Hyes IHyes Helim Hno IHno repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    subst Γyes. simpl.
    eapply T_Match with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := sigma_fields) (result_ty_schema := result_ty_schema)
      (lts := lts) (rho_fields := rho_fields)
      (scrut_result_ty := scrut_result_ty)
      (result_tag := result_tag) (result_l := result_l)
      (Γ' := push_lt_vars n_lt Delta G') (eta := eta).
    + exact HKne.
    + rewrite (SubstTm_lookup_ctor repl n Γ G' HSub K). exact Hctor.
    + rewrite (SubstTm_lookup_eff repl n Γ G' HSub K). exact Heff.
    + exact Hlts.
    + exact Hrho.
    + exact Hlen_Ts.
    + eapply types_wf_SubstTm; eauto.
    + exact Hscrut_result.
    + exact Hscrut_shape.
    + rewrite (SubstTm_lookup_eff repl n Γ G' HSub result_tag). exact Hresult_eff.
    + exact Hresult_ne.
    + eapply lt_wf_SubstTm; eauto.
    + eapply lt_sub_SubstTm; eauto.
    + apply (IHscrut repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    + exact Harity.
    + reflexivity.
    + replace (subst_tm (n + arity) (shift_tm arity 0 (shift_lt_in_tm n_lt 0 repl)) yes_body)
        with (subst_tm (n + List.length rho_fields)
          (shift_tm (List.length rho_fields) 0 (shift_lt_in_tm n_lt 0 repl)) yes_body)
        by (rewrite Harity; reflexivity).
      refine (IHyes (shift_tm (List.length rho_fields) 0 (shift_lt_in_tm n_lt 0 repl))
        (n + List.length rho_fields)
        (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) (push_lt_vars n_lt Delta G') rho_fields)
        _ _ _ _ _ _ HrepAll (c + n_lt) _ _ _).
      * apply SubstTm_fold_bind_tm. apply SubstTm_push_lt_vars. exact HSub.
      * apply free_tm_vars_closed_shift_tm_any. rewrite free_tm_vars_shift_lt_in_tm_any. exact Hfree.
      * apply tm_ty_closed_shift_tm. apply tm_ty_closed_shift_lt. exact HtmTy.
      * apply tm_lt_closed_shift_tm. apply tm_lt_closed_shift_lt_closed0. exact HtmLt.
      * apply SubstTm_target_ty_closed0_fold_bind_tm. apply SubstTm_target_ty_closed0_push_lt_vars. exact HtargetTy.
      * apply SubstTm_target_lt_closed0_fold_bind_tm. apply SubstTm_target_lt_closed0_push_lt_vars. exact HtargetLt.
      * apply ctx_lt_closed_from_fold_bind_tm. apply ctx_lt_closed_from_push_lt_vars. exact Hlt.
      * apply ctx_schemas_lt_closed_from_fold_bind_tm. apply ctx_schemas_lt_closed_from_push_lt_vars. exact Hschemas.
      * apply replacement_capture_bound_fold_bind_tm.
        -- rewrite free_tm_vars_shift_lt_in_tm_any. exact Hfree.
        -- apply replacement_capture_bound_push_lt_vars; assumption.
    + exact Helim.
    + apply (IHno repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
  - intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
      Heff Hlen HwfTs HwfTR Hsig Hret Hop IHop repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl.
    set (rho_k := type_fun ret_β lt_local (shift_ty n_β 0 T_R)).
    replace (subst_tm (n + 2) (shift_tm 2 0 repl) op_body)
      with (subst_tm (n + List.length [sig_β; rho_k])
        (shift_tm (List.length [sig_β; rho_k]) 0 (shift_ty_in_tm n_β 0 repl)) op_body).
    2:{ simpl. rewrite shift_ty_in_tm_closed by exact HtmTy. reflexivity. }
    eapply T_Cap with
      (n_α := n_α) (n_β := n_β) (sig := sig) (ret := ret)
      (sig_β := sig_β) (ret_β := ret_β).
    + rewrite (SubstTm_lookup_eff repl n Γ G' HSub E_tag). exact Heff.
    + exact Hlen.
    + eapply types_wf_SubstTm; eauto.
    + eapply ty_wf_SubstTm; eauto.
    + exact Hsig.
    + exact Hret.
      + unfold rho_k.
        refine (IHop (shift_tm (List.length [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)]) 0
          (shift_ty_in_tm n_β 0 repl)) (n + List.length [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)])
          (fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
            (push_ty_vars n_β any_at_free G') [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)])
          _ _ _ _ _ _ HrepAll c _ _ _).
      * exact (SubstTm_fold_bind_tm
        [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)]
        (shift_ty_in_tm n_β 0 repl) n
        (push_ty_vars n_β any_at_free Γ)
        (push_ty_vars n_β any_at_free G')
        (SubstTm_push_ty_vars_any_at_free n_β repl n Γ G' HSub)).
      * apply free_tm_vars_closed_shift_tm_any. rewrite free_tm_vars_shift_ty_in_tm_any. exact Hfree.
      * apply tm_ty_closed_shift_tm. apply tm_ty_closed_shift_ty_closed0. exact HtmTy.
      * apply tm_lt_closed_shift_tm. apply tm_lt_closed_shift_ty. exact HtmLt.
      * exact (SubstTm_target_ty_closed0_fold_bind_tm
        [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)] n
        (push_ty_vars n_β any_at_free Γ)
        (SubstTm_target_ty_closed0_push_ty_vars n_β any_at_free n Γ HtargetTy)).
      * exact (SubstTm_target_lt_closed0_fold_bind_tm
        [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)] n
        (push_ty_vars n_β any_at_free Γ)
        (SubstTm_target_lt_closed0_push_ty_vars n_β any_at_free n Γ HtargetLt)).
      * apply ctx_lt_closed_from_fold_bind_tm. apply ctx_lt_closed_from_push_ty_vars. exact Hlt.
      * apply ctx_schemas_lt_closed_from_fold_bind_tm. apply ctx_schemas_lt_closed_from_push_ty_vars. exact Hschemas.
        * exact (replacement_capture_bound_fold_bind_tm
            [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)]
            (push_ty_vars n_β any_at_free Γ)
            (push_ty_vars n_β any_at_free G')
            (shift_ty_in_tm n_β 0 repl) n
            ltac:(rewrite free_tm_vars_shift_ty_in_tm_any; exact Hfree)
            (replacement_capture_bound_push_ty_vars_any_at_free
              n_β Γ G' repl n Hfree Hcap)).
  - intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
      Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hsig Hret Hop IHop Hbody IHbody repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl.
    set (rho_k := type_fun ret_β lt_local (shift_ty n_β 0 T_R)).
    replace (subst_tm (n + 2) (shift_tm 2 0 repl) op_body)
      with (subst_tm (n + List.length [sig_β; rho_k])
        (shift_tm (List.length [sig_β; rho_k]) 0 (shift_ty_in_tm n_β 0 repl)) op_body).
    2:{ simpl. rewrite shift_ty_in_tm_closed by exact HtmTy. reflexivity. }
    eapply T_Handle with
      (n_α := n_α) (n_β := n_β) (sig := sig) (ret := ret)
      (T_B := T_B) (sig_β := sig_β) (ret_β := ret_β).
    + rewrite (SubstTm_lookup_eff repl n Γ G' HSub E_tag). exact Heff.
    + exact Hlen.
    + eapply types_wf_SubstTm; eauto.
    + eapply ty_wf_SubstTm; eauto.
    + eapply ty_wf_SubstTm; eauto.
    + eapply no_local_ty_G_SubstTm; eauto.
    + eapply sub_SubstTm; eauto.
    + exact Hsig.
    + exact Hret.
    + unfold rho_k.
      refine (IHop (shift_tm (List.length [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)]) 0
          (shift_ty_in_tm n_β 0 repl)) (n + List.length [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)])
          (fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
            (push_ty_vars n_β any_at_free G') [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)])
          _ _ _ _ _ _ HrepAll c _ _ _).
        * exact (SubstTm_fold_bind_tm
          [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)]
          (shift_ty_in_tm n_β 0 repl) n
          (push_ty_vars n_β any_at_free Γ)
          (push_ty_vars n_β any_at_free G')
          (SubstTm_push_ty_vars_any_at_free n_β repl n Γ G' HSub)).
      * apply free_tm_vars_closed_shift_tm_any. rewrite free_tm_vars_shift_ty_in_tm_any. exact Hfree.
      * apply tm_ty_closed_shift_tm. apply tm_ty_closed_shift_ty_closed0. exact HtmTy.
      * apply tm_lt_closed_shift_tm. apply tm_lt_closed_shift_ty. exact HtmLt.
        * exact (SubstTm_target_ty_closed0_fold_bind_tm
          [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)] n
          (push_ty_vars n_β any_at_free Γ)
          (SubstTm_target_ty_closed0_push_ty_vars n_β any_at_free n Γ HtargetTy)).
        * exact (SubstTm_target_lt_closed0_fold_bind_tm
          [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)] n
          (push_ty_vars n_β any_at_free Γ)
          (SubstTm_target_lt_closed0_push_ty_vars n_β any_at_free n Γ HtargetLt)).
      * apply ctx_lt_closed_from_fold_bind_tm. apply ctx_lt_closed_from_push_ty_vars. exact Hlt.
      * apply ctx_schemas_lt_closed_from_fold_bind_tm. apply ctx_schemas_lt_closed_from_push_ty_vars. exact Hschemas.
      * exact (replacement_capture_bound_fold_bind_tm
          [sig_β; type_fun ret_β lt_local (shift_ty n_β 0 T_R)]
          (push_ty_vars n_β any_at_free Γ)
          (push_ty_vars n_β any_at_free G')
          (shift_ty_in_tm n_β 0 repl) n
          ltac:(rewrite free_tm_vars_shift_ty_in_tm_any; exact Hfree)
          (replacement_capture_bound_push_ty_vars_any_at_free
            n_β Γ G' repl n Hfree Hcap)).
    + refine (IHbody (shift_tm 1 0 repl) (S n) (bind_tm (type_ctor E_tag lt_local Ts) :: G')
      _ _ _ _ _ _ HrepAll c _ _ _).
      * apply SubstTm_tm. exact HSub.
      * apply free_tm_vars_closed_shift_tm_any. exact Hfree.
      * apply tm_ty_closed_shift_tm. exact HtmTy.
      * apply tm_lt_closed_shift_tm. exact HtmLt.
      * apply SubstTm_target_ty_closed0_tm. exact HtargetTy.
      * apply SubstTm_target_lt_closed0_tm. exact HtargetLt.
      * apply ctx_lt_closed_from_bind_tm. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_tm. exact Hschemas.
      * apply replacement_capture_bound_tm; assumption.
  - intros Γ recv arg E_tag Delta Ts Ss n_α n_β sig ret sig_inst ret_inst
      Hrecv IHrecv Heff Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. eapply T_Perform with
      (n_α := n_α) (n_β := n_β) (sig := sig) (ret := ret)
      (sig_inst := sig_inst) (ret_inst := ret_inst).
    + apply (IHrecv repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
    + rewrite (SubstTm_lookup_eff repl n Γ G' HSub E_tag). exact Heff.
    + exact Hlen_Ts.
    + exact Hlen_Ss.
    + eapply types_wf_SubstTm; eauto.
    + eapply forallb_no_local_ty_G_SubstTm; eauto.
    + exact Hsig.
    + eapply no_local_ty_G_SubstTm; eauto.
    + exact Hret.
    + eapply ty_wf_SubstTm; eauto.
    + apply (IHarg repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. apply T_HandlerM.
    + eapply ty_wf_SubstTm; eauto.
    + eapply ty_wf_SubstTm; eauto.
    + eapply no_local_ty_G_SubstTm; eauto.
    + eapply sub_SubstTm; eauto.
    + apply (IH repl n G' HSub Hfree HtmTy HtmLt HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap).
  - intros Γ m b A T_B T_R HwfA HwfTB HwfTR HnoLocal Hsub Hb IHb repl n G' HSub Hfree HtmTy HtmLt
      HtargetTy HtargetLt HrepAll c Hlt Hschemas Hcap.
    simpl. apply T_Resume.
    + eapply ty_wf_SubstTm; eauto.
    + eapply ty_wf_SubstTm; eauto.
    + eapply ty_wf_SubstTm; eauto.
    + eapply no_local_ty_G_SubstTm; eauto.
    + eapply sub_SubstTm; eauto.
    + refine (IHb (shift_tm 1 0 repl) (S n) (bind_tm A :: G')
      _ _ _ _ _ _ HrepAll c _ _ _).
      * apply SubstTm_tm. exact HSub.
      * apply free_tm_vars_closed_shift_tm_any. exact Hfree.
      * apply tm_ty_closed_shift_tm. exact HtmTy.
      * apply tm_lt_closed_shift_tm. exact HtmLt.
      * apply SubstTm_target_ty_closed0_tm. exact HtargetTy.
      * apply SubstTm_target_lt_closed0_tm. exact HtargetLt.
      * apply ctx_lt_closed_from_bind_tm. exact Hlt.
      * apply ctx_schemas_lt_closed_from_bind_tm. exact Hschemas.
      * apply replacement_capture_bound_tm; assumption.
Qed.

Fixpoint has_rt_cap_list (ts : list term) : bool :=
  match ts with
  | [] => false
  | t :: rest => orb (has_rt_cap t) (has_rt_cap_list rest)
  end.

Lemma Forall2_typing_lt_of_ty_list_wf : forall Γ vs rhos,
  eval_ctx Γ ->
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rhos ->
  lt_wf Γ (lt_of_ty_list rhos).
Proof.
  intros Γ vs rhos Hec Hty. induction Hty; simpl.
  - constructor.
  - constructor.
    + pose proof (typing_implies_wf Γ x y H) as Hwf.
      pose proof (ty_wf_eval_ctx_ty_closed Γ y Hec Hwf) as Hclosed.
      rewrite <- (lt_of_ty_G_ty_closed_eq Γ y Hclosed).
      apply lt_of_ty_G_wf. exact Hwf.
    + exact IHHty.
Qed.

Lemma Forall2_value_capture_has_rt_cap_list : forall Γ vs rhos,
  eval_ctx Γ ->
  Forall2 (fun v rho =>
    eval_ctx Γ -> value v -> free_tm_vars 0 v = [] ->
    Γ ⊢ₗ capture_lt Γ v <: lt_of_ty_G Γ rho) vs rhos ->
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rhos ->
  Forall value vs ->
  List.concat (List.map (free_tm_vars 0) vs) = [] ->
  has_rt_cap_list vs = true ->
  Γ ⊢ₗ lt_local <: lt_of_ty_list rhos.
Proof.
  intros Γ vs rhos Hec HcapF HtyF HvalF Hfree HcapList.
  induction HcapF as [|v rho vs rhos Hcap IHcapF IHHcapF].
  - simpl in HcapList. discriminate.
  - inversion HtyF as [|v' rho' vs' rhos' Hty HtyTail Heq1 Heq2]; subst.
    inversion HvalF as [|v0 vs0 Hv Hvals Heq]; subst.
    simpl in Hfree. apply List.app_eq_nil in Hfree as [HfreeV HfreeVs].
    simpl in HcapList. apply Bool.orb_true_iff in HcapList as [HcapV | HcapVs].
    + apply LS_MinR1.
      * specialize (Hcap Hec Hv HfreeV).
        rewrite (capture_lt_closed Γ v HfreeV) in Hcap. rewrite HcapV in Hcap. simpl in Hcap.
        pose proof (typing_implies_wf Γ v rho Hty) as Hwf.
        pose proof (ty_wf_eval_ctx_ty_closed Γ rho Hec Hwf) as Hclosed.
        rewrite <- (lt_of_ty_G_ty_closed_eq Γ rho Hclosed). exact Hcap.
      * eapply Forall2_typing_lt_of_ty_list_wf; eauto.
    + apply LS_MinR2.
      * apply IHHcapF; assumption.
      * pose proof (typing_implies_wf Γ v rho Hty) as Hwf.
        pose proof (ty_wf_eval_ctx_ty_closed Γ rho Hec Hwf) as Hclosed.
        rewrite <- (lt_of_ty_G_ty_closed_eq Γ rho Hclosed).
        apply lt_of_ty_G_wf. exact Hwf.
Qed.

Lemma typing_value_capture_lt_le_type : forall Γ v T,
  Γ ⊢ₜ v : T ->
  eval_ctx Γ ->
  value v ->
  free_tm_vars 0 v = [] ->
  Γ ⊢ₗ capture_lt Γ v <: lt_of_ty_G Γ T.
Proof.
  apply (typing_ind_forall2
    (fun Γ v T => eval_ctx Γ -> value v -> free_tm_vars 0 v = [] ->
      Γ ⊢ₗ capture_lt Γ v <: lt_of_ty_G Γ T)).
  - intros Γ x T Hlk HwfT Hec Hval Hfree. inversion Hval.
  - intros Γ t T U Ht IH Hsub Hec Hval Hfree.
    eapply LS_Trans.
    + apply IH; assumption.
    + apply lt_of_ty_G_mono_sub. exact Hsub.
  - intros Γ body A l B HwfA HwfB Hbody IHbody Hcap Hec Hval Hfree.
    inversion Hval; subst. simpl in Hfree.
    rewrite (capture_lt_closed Γ (term_lam body A) Hfree). simpl.
    unfold lt_of_ty_G. rewrite lt_of_ty_ctx_fun.
    destruct (has_rt_cap body) eqn:HcapBody.
    + unfold capture_lt in Hcap. rewrite HcapBody in Hcap. exact Hcap.
    + apply LS_Free. destruct (lt_sub_wf _ _ _ Hcap) as [_ Hwfl]. exact Hwfl.
  - intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 Hec Hval Hfree. inversion Hval.
  - intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody Hec Hval Hfree.
    inversion Hval; subst.
    rewrite (capture_lt_closed Γ (term_ty_lam bound body) Hfree). simpl.
    unfold lt_of_ty_G. rewrite lt_of_ty_ctx_tyall.
    destruct (has_rt_cap body) eqn:HcapBody.
    + apply LS_Refl. constructor.
    + apply LS_Free. constructor.
  - intros Γ t B U S Ht IH HwfS Hsub HnlArg Hec Hval Hfree. inversion Hval.
  - intros Γ body T HwfT HisAbs Hbody IHbody Hec Hval Hfree.
    inversion Hval; subst.
    rewrite (capture_lt_closed Γ (term_lt_lam body) Hfree). simpl.
    unfold lt_of_ty_G. rewrite lt_of_ty_ctx_ltall.
    destruct (has_rt_cap body) eqn:HcapBody.
    + apply LS_Refl. constructor.
    + apply LS_Free. constructor.
  - intros Γ t T l Ht IH Hwfl Hec Hval Hfree. inversion Hval.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
           Hlk Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs Hresult Hshape
           Hresult_eff Hwfl Hlt Hforall Hlen_vs Hfields IHfields Hec Hval Hfree.
    inversion Hval as [| | |K0 l0 lts0 Ts0 vs0 Hvals Heq| |]; subst.
    rewrite (capture_lt_closed Γ (term_ctor K l lts Ts vs) Hfree). simpl.
    change ((fix go (ts : list term) : bool :=
      match ts with
      | [] => false
      | u :: rest => orb (has_rt_cap u) (go rest)
      end) vs) with (has_rt_cap_list vs).
    destruct (has_rt_cap_list vs) eqn:HcapVs.
    + rewrite Hshape. unfold lt_of_ty_G. rewrite lt_of_ty_ctx_ctor.
      match type of Hfields with
      | Forall2 _ vs ?rhos =>
          assert (HlocalFields : Γ ⊢ₗ lt_local <: lt_of_ty_list rhos)
            by (eapply Forall2_value_capture_has_rt_cap_list;
                [exact Hec|exact IHfields|exact Hfields|exact Hvals|
                 simpl in Hfree; rewrite free_tm_vars_go_eq_concat in Hfree; exact Hfree|
                 exact HcapVs])
      end.
      rewrite Hshape in Hlt. rewrite lt_of_ty_ctor_eq in Hlt.
      eapply LS_Trans; [exact HlocalFields|].
      eapply LS_Trans; [exact Hlt|].
      apply lt_min_mono; [apply LS_Refl; exact Hwfl|].
      eapply lt_of_ty_list_le_lt_of_ty_ctx_list. exact HwfTs.
    + apply LS_Free. apply lt_of_ty_G_wf. rewrite Hshape. constructor; assumption.
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γ' yes_body eta
           elim_result no_body HKne Hlk Heff Hlts Hrho Hlen_Ts HwfTs
           Hscrut_result Hscrut_shape Hresult_eff Hresult_ne HwfDelta Hresult_l Hscrut IHscrut
           Harity HGamma' Hyes IHyes Helim Hno IHno Hec Hval Hfree. inversion Hval.
  - intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff Hlen HwfTs HwfTR Hsig Hret Hop IHop Hec Hval Hfree.
    inversion Hval; subst.
    rewrite (capture_lt_closed Γ (term_cap E_tag m n_β Ts T_R op_body) Hfree). simpl.
    unfold lt_of_ty_G. rewrite lt_of_ty_ctx_ctor.
    apply LS_MinR1.
    + apply LS_Refl. constructor.
    + eapply lt_of_ty_G_list_wf; eauto.
  - intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hsig Hret Hop IHop Hbody IHbody Hec Hval Hfree.
    inversion Hval.
  - intros Γ recv arg E_tag Delta Ts Ss n_α n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg Hec Hval Hfree.
    inversion Hval.
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH Hec Hval Hfree.
    inversion Hval.
  - intros Γ m b A T_B T_R HwfA HwfTB HwfTR HnoLocal Hsub Hb IHb Hec Hval Hfree.
    inversion Hval; subst.
    rewrite (capture_lt_closed Γ (term_resume m T_B T_R b) Hfree). simpl.
    unfold lt_of_ty_G. rewrite lt_of_ty_ctx_fun. apply LS_Refl. constructor.
Qed.

(* ================================================================ *)
(* AXIOM 3: HrepAll-free term-substitution preservation under an     *)
(* evaluation context.  This is the SubstTm_eval_ctx_prefix          *)
(* restructure: the SETP constructors use 0-indexed closedness while *)
(* typing_SubstTm threads a varying binder depth c, so discharging   *)
(* the HrepAll closure structurally is a ~300-line rebuild (deferred).*)
(* NOTE (investigated): the gap is exactly the [HrepAll] premise of   *)
(* typing_SubstTm — its SubstTm_lt case needs an UNCONDITIONAL        *)
(* lt-weakening (typing_InsLt), which is itself blocked at the        *)
(* T_Match case (schema-origin closedness the bare statement lacks).  *)
(* So this routes back through the same match-substitution kernel as  *)
(* ltbeta / typing_SubstTy_match_case.                                *)
(* ================================================================ *)
Axiom typing_SubstTm_eval_ctx : forall Γ A t B v,
  eval_ctx Γ ->
  (bind_tm A :: Γ) ⊢ₜ t : B ->
  value v ->
  Γ ⊢ₜ v : A ->
  Γ ⊢ₜ subst_tm 0 v t : B.

(* ================================================================ *)
(* AXIOM 4: the list version of Axiom 3 (used by match / perform).   *)
(* ================================================================ *)
Axiom typing_subst_list_tm_eval_ctx : forall Γ vs rhos t T,
  eval_ctx Γ ->
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rhos ->
  Forall value vs ->
  List.concat (List.map (free_tm_vars 0) vs) = [] ->
  (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos) ⊢ₜ t : T ->
  Γ ⊢ₜ subst_list_tm vs t : T.

Lemma typing_SubstTm_eval_ctx_global : forall Γ A t B v,
  eval_ctx Γ ->
  (bind_tm A :: Γ) ⊢ₜ t : B ->
  value v ->
  Γ ⊢ₜ v : A ->
  (forall repl0 n0 G0 G0',
    SubstTm repl0 n0 G0 G0' ->
    SubstTm_replacement_typed repl0 n0 G0 G0') ->
  Γ ⊢ₜ subst_tm 0 v t : B.
Proof.
  intros Γ A t B v Hec Ht Hval Hv HrepAll.
  pose proof (typing_closed Γ v A Hec Hv) as Hfree.
  pose proof (typing_eval_ctx_tm_ty_closed Γ v A Hec Hv) as HtmTy.
  pose proof (typing_eval_ctx_tm_lt_closed Γ v A Hec Hv) as HtmLt.
  pose proof (typing_implies_wf Γ v A Hv) as HwfA.
  pose proof (ty_wf_eval_ctx_ty_closed Γ A Hec HwfA) as HAty.
  pose proof (ty_wf_eval_ctx_lt_closed Γ A Hec HwfA) as HAlt.
  eapply (typing_SubstTm (bind_tm A :: Γ) t B Ht v 0 Γ).
  - apply SubstTm_here; assumption.
  - exact Hfree.
  - exact HtmTy.
  - exact HtmLt.
  - intros T Hlk. simpl in Hlk. inversion Hlk; subst. exact HAty.
  - intros T Hlk. simpl in Hlk. inversion Hlk; subst. exact HAlt.
  - exact HrepAll.
  - apply eval_ctx_lt_closed_from. exact Hec.
  - apply eval_ctx_schemas_lt_closed_from. exact Hec.
  - unfold capture_var_lifetime. simpl.
    rewrite lt_of_ty_G_weaken_tm.
    eapply typing_value_capture_lt_le_type; eauto.
Qed.

Lemma typing_subst_list_tm_eval_ctx_global : forall Γ vs rhos t T,
  eval_ctx Γ ->
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rhos ->
  Forall value vs ->
  List.concat (List.map (free_tm_vars 0) vs) = [] ->
  (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos) ⊢ₜ t : T ->
  (forall repl0 n0 G0 G0',
    SubstTm repl0 n0 G0 G0' ->
    SubstTm_replacement_typed repl0 n0 G0 G0') ->
  Γ ⊢ₜ subst_list_tm vs t : T.
Proof.
  intros Γ vs rhos t T Hec Hargs.
  revert t T.
  induction Hargs as [|v rho vs rhos Hv Hargs IHHargs]; intros t T Hvals Hfree Ht HrepAll; simpl in *.
  - exact Ht.
  - inversion Hvals as [|v0 vs0 HvVal HvalsTail Heq]; subst.
    apply List.app_eq_nil in Hfree as [HfreeV HfreeTail].
    pose proof (typing_implies_wf Γ v rho Hv) as HwfRho.
    pose proof (ty_wf_eval_ctx_ty_closed Γ rho Hec HwfRho) as HrhoTy.
    pose proof (ty_wf_eval_ctx_lt_closed Γ rho Hec HwfRho) as HrhoLt.
    pose proof (typing_eval_ctx_tm_ty_closed Γ v rho Hec Hv) as HvTy.
    pose proof (typing_eval_ctx_tm_lt_closed Γ v rho Hec Hv) as HvLt.
    set (Grest := List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos).
    assert (HfreeShift : free_tm_vars 0 (shift_tm (List.length rhos) 0 v) = []).
    { apply free_tm_vars_closed_shift_tm_any. exact HfreeV. }
    assert (Hcap : Grest ⊢ₗ
      capture_lt Grest (shift_tm (List.length rhos) 0 v) <:
      capture_var_lifetime (bind_tm rho :: Grest) 0).
    { pose proof (typing_value_capture_lt_le_type Γ v rho Hv Hec HvVal HfreeV) as HcapBase.
      subst Grest. unfold capture_var_lifetime. simpl.
      rewrite lt_of_ty_G_weaken_tm.
      rewrite (lt_of_ty_G_ty_closed_eq (List.fold_right (fun rho0 Γ0 => bind_tm rho0 :: Γ0) Γ rhos) rho HrhoTy).
      rewrite <- (lt_of_ty_G_ty_closed_eq Γ rho HrhoTy).
      rewrite (capture_lt_closed (List.fold_right (fun rho0 Γ0 => bind_tm rho0 :: Γ0) Γ rhos)
        (shift_tm (List.length rhos) 0 v) HfreeShift).
      rewrite has_rt_cap_shift_tm.
      rewrite <- (capture_lt_closed Γ v HfreeV).
      apply lt_sub_fold_bind_tm. exact HcapBase. }
    assert (Ht' : Grest ⊢ₜ subst_tm 0 (shift_tm (List.length rhos) 0 v) t : T).
    { subst Grest.
      eapply (typing_SubstTm (bind_tm rho :: List.fold_right (fun rho0 Γ0 => bind_tm rho0 :: Γ0) Γ rhos)
        t T Ht (shift_tm (List.length rhos) 0 v) 0
        (List.fold_right (fun rho0 Γ0 => bind_tm rho0 :: Γ0) Γ rhos)).
      - apply SubstTm_here.
        + apply value_shift_tm. exact HvVal.
        + apply typing_weaken_tm_shift_many. exact Hv.
      - exact HfreeShift.
      - apply tm_ty_closed_shift_tm. exact HvTy.
      - apply tm_lt_closed_shift_tm. exact HvLt.
      - intros U Hlk. simpl in Hlk. inversion Hlk; subst U; clear Hlk. exact HrhoTy.
      - intros U Hlk. simpl in Hlk. inversion Hlk; subst U; clear Hlk. exact HrhoLt.
      - exact HrepAll.
      - apply ctx_lt_closed_from_fold_bind_tm. apply eval_ctx_lt_closed_from. exact Hec.
      - apply ctx_schemas_lt_closed_from_fold_bind_tm. apply eval_ctx_schemas_lt_closed_from. exact Hec.
      - exact Hcap. }
    rewrite (Forall2_length Hargs).
    apply (IHHargs (subst_tm 0 (shift_tm (List.length rhos) 0 v) t) T
      HvalsTail HfreeTail Ht' HrepAll).
Qed.

