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
(* The context-closedness bookkeeping derived from [eval_ctx] (the    *)
(* `*_closed_from` predicate families and the typing-level closedness *)
(* corollaries) lives in CtxClosed.v.                                 *)
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
