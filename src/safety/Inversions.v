Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import Markers.
Require Import Progress.
Require Import Narrowing.
Require Import Variance.
Require Import TypingInv.


(* ------------------------------------------------------------------ *)
(* Well-scopedness: a well-typed term's free term variables are all   *)
(* bound by its typing context.  Specialized to an `eval_ctx` (which  *)
(* has no `bind_tm` entries) this gives term-closedness, discharging  *)
(* the closedness side-condition of `subst_tm_lemma`.                 *)
(* ------------------------------------------------------------------ *)

(* Shifting the cutoff of `free_tm_vars` by one shifts membership.     *)
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
  - (* var *)
    intros x c y. simpl.
    destruct (Nat.ltb x (S c)) eqn:E1.
    + intros [].
    + apply Nat.ltb_ge in E1.
      assert (E2 : Nat.ltb x c = false) by (apply Nat.ltb_ge; lia).
      rewrite E2. simpl. intros [Hy | []]. subst y. left. lia.
  - (* app *)
    intros t1 t2 IH1 IH2 c y. simpl. rewrite !List.in_app_iff.
    intros [H|H]; [left; apply IH1; exact H | right; apply IH2; exact H].
  - (* lam *)
    intros body T IH c y. simpl. apply IH.
  - (* ty_app *)
    intros t T IH c y. simpl. apply IH.
  - (* ty_lam *)
    intros bound body IH c y. simpl. apply IH.
  - (* lt_app *)
    intros t l IH c y. simpl. apply IH.
  - (* lt_lam *)
    intros body IH c y. simpl. apply IH.
  - (* ctor *)
    intros K l lts Ts ts IH c y. simpl.
    rewrite !free_tm_vars_go_eq_concat. apply IH.
  - (* match *)
    intros scrut tag n_lt arity yes_body no_body IHs IHy IHn c y. simpl.
    rewrite !List.in_app_iff. intros [H|[H|H]].
    + left. apply IHs; exact H.
    + right; left. apply IHy; exact H.
    + right; right. apply IHn; exact H.
  - (* handle *)
    intros E Ts T_B T_R op_bodies body IHops IHb c y. simpl.
    rewrite !free_tm_vars_go_ops_eq_concat.
    rewrite !List.in_app_iff. intros [H|H].
    + left. apply IHops; exact H.
    + right. apply IHb; exact H.
  - (* perform *)
    intros t op Ss A_ret arg IHt IHa c y. simpl.
    rewrite !List.in_app_iff. intros [H|H]; [left; apply IHt; exact H | right; apply IHa; exact H].
  - (* cap *)
    intros E m Ts T_R op_bodies IHops c y. simpl.
    rewrite !free_tm_vars_go_ops_eq_concat. apply IHops.
  - (* handler_m *)
    intros m T_B T_R t IH c y. simpl. apply IH.
  - (* nil *)
    intros c y. simpl. intros [].
  - (* cons *)
    intros t ts IHt IHts c y. simpl.
    rewrite !List.in_app_iff. intros [H|H]; [left; apply IHt; exact H | right; apply IHts; exact H].
  - (* ops nil *)
    intros c y. simpl. intros [].
  - (* ops cons *)
    intros nb ob obs IHob IHobs c y. simpl.
    rewrite !List.in_app_iff. intros [H|H]; [left; apply IHob; exact H | right; apply IHobs; exact H].
Qed.

(* Iterated version of `fv_succ`. *)
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

(* Looking up a term variable past `n` pushed lifetime binders.        *)
Lemma lookup_tm_push_lt_None : forall n bound Γ x,
  ctx_lookup_tm Γ x = None ->
  ctx_lookup_tm (push_lt_vars n bound Γ) x = None.
Proof.
  induction n as [|n IH]; intros bound Γ x H; simpl.
  - exact H.
  - apply IH. simpl. rewrite H. reflexivity.
Qed.

(* Looking up a term variable past `n` pushed type binders.            *)
Lemma lookup_tm_push_ty_None : forall n bound Γ x,
  ctx_lookup_tm Γ x = None ->
  ctx_lookup_tm (push_ty_vars n bound Γ) x = None.
Proof.
  induction n as [|n IH]; intros bound Γ x H; simpl.
  - exact H.
  - apply IH. simpl. rewrite H. reflexivity.
Qed.

(* Looking up a term variable past a block of `bind_tm` binders.       *)
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

(* Every free term variable of a well-typed term is bound in Γ.        *)
Lemma typing_fv_bound : forall Γ t T,
  Γ ⊢ₜ t : T ->
  forall x, In x (free_tm_vars 0 t) -> ctx_lookup_tm Γ x <> None.
Proof.
  apply (typing_ind2
    (fun Γ t T => forall x, In x (free_tm_vars 0 t) -> ctx_lookup_tm Γ x <> None)).
  - (* T_Var *)
    intros Γ x T Hlk HwfT y Hin. simpl in Hin. rewrite Nat.sub_0_r in Hin.
    destruct Hin as [Hy | []].
    subst y. rewrite Hlk. discriminate.
  - (* T_Sub *)
    intros Γ t T U Ht IH Hsub x Hin. apply IH; exact Hin.
  - (* T_Lam *)
    intros Γ body A l B HwfA HwfB Hbody IH Hcap x Hin.
    simpl in Hin. apply fv_succ in Hin. specialize (IH (S x) Hin).
    simpl in IH. exact IH.
  - (* T_App *)
    intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 x Hin.
    simpl in Hin. rewrite List.in_app_iff in Hin.
    destruct Hin as [H|H]; [apply IH1 | apply IH2]; exact H.
  - (* T_TyLam *)
    intros Γ bound body T HwfBound HwfT Hbody IH x Hin.
    simpl in Hin. specialize (IH x Hin).
    intros Hnone. apply IH. simpl. rewrite Hnone. reflexivity.
  - (* T_TyApp *)
    intros Γ t B U S Ht IH HwfS Hsub x Hin. apply IH; exact Hin.
  - (* T_LtLam *)
    intros Γ body T HwfT Hbody IH x Hin.
    simpl in Hin. specialize (IH x Hin).
    intros Hnone. apply IH. simpl. rewrite Hnone. reflexivity.
  - (* T_LtApp *)
    intros Γ t T l Ht IH Hwfl x Hin. apply IH; exact Hin.
  - (* T_Ctor *)
    intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
          Hlk Heff Hlts HwfLts Hrho HTs HwfTs Hres Hshape Hresult_eff Hwfl Hltsub Hvslen
          Hf2ty Hf2P Hf2IH x Hin.
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
  - (* T_Match *)
    intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γ' yes_body eta
           elim_result no_body
           HKne Hlk Heff Hlts Hrho HTs HwfTs Hsrt Hshape Hresult_eff Hrtne HwfDelta Hrl Hscrut IHscrut
           Harity HΓ' Hyes IHyes Helim Hno IHno x Hin.
    simpl in Hin. rewrite !List.in_app_iff in Hin.
    destruct Hin as [Hs | [Hy | Hn]].
    + apply IHscrut; exact Hs.
    + apply (fv_add arity yes_body 0 x) in Hy.
      specialize (IHyes (x + arity) Hy). subst Γ'.
      rewrite Harity in IHyes.
      rewrite lookup_tm_skip_bind_tm_many in IHyes.
      intros Hnone. apply IHyes. apply lookup_tm_push_match_bound_None. exact Hnone.
    + apply IHno; exact Hn.
  - (* T_Cap *)
    intros Γ E_tag m Ts op_bodies n_α ops T_R
           Heff Hlen HwfTs HwfTR Hfst Hops IHops x Hin.
    simpl in Hin.
    rewrite free_tm_vars_go_ops_eq_concat in Hin.
    clear - IHops Hin.
    revert Hin. induction IHops as [|ob osig obs' ops' Hp Hrest IH]; intros Hin.
    + simpl in Hin. contradiction.
    + simpl in Hin. rewrite List.in_app_iff in Hin.
      destruct Hin as [H|H]; [| apply IH; exact H].
      apply (fv_add 2 (snd ob) 0 x) in H.
      specialize (Hp (x + 2) H).
      replace (x + 2) with (S (S x)) in Hp by lia. simpl in Hp.
      intros Hnone. apply Hp. apply lookup_tm_push_ty_None. exact Hnone.
  - (* T_Handle *)
    intros Γ E_tag Ts op_bodies body n_α ops T_B T_R
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hfst Hops IHops Hbody IHbody x Hin.
    simpl in Hin.
    rewrite free_tm_vars_go_ops_eq_concat in Hin.
    rewrite List.in_app_iff in Hin. destruct Hin as [HopsFree | Hb].
    + clear - IHops HopsFree.
      revert HopsFree. induction IHops as [|ob osig obs' ops' Hp Hrest IH]; intros Hin.
      * simpl in Hin. contradiction.
      * simpl in Hin. rewrite List.in_app_iff in Hin.
        destruct Hin as [H|H]; [| apply IH; exact H].
        apply (fv_add 2 (snd ob) 0 x) in H.
        specialize (Hp (x + 2) H).
        replace (x + 2) with (S (S x)) in Hp by lia. simpl in Hp.
        intros Hnone. apply Hp. apply lookup_tm_push_ty_None. exact Hnone.
    + apply fv_succ in Hb. specialize (IHbody (S x) Hb).
      simpl in IHbody. exact IHbody.
  - (* T_Perform *)
        intros Γ recv op arg E_tag Δ Ts Ss n_α ops n_β sig ret sig_inst ret_inst
          H1 IHrecv H3 Hnth H4 H5 H6 HnoSs H7 HnoSig H8 HwfRet H9 IHarg x Hin.
    simpl in Hin. rewrite List.in_app_iff in Hin.
    destruct Hin as [H|H]; [apply IHrecv | apply IHarg]; exact H.
  - (* T_HandlerM *)
    intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH x Hin. apply IH; exact Hin.
Qed.

(* A well-typed term under an `eval_ctx` is term-closed.               *)
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


Lemma ctx_lookup_ty_fold_bind_tm : forall rhos G a,
  ctx_lookup_ty (fold_right (fun rho G0 => bind_tm rho :: G0) G rhos) a = ctx_lookup_ty G a.
Proof.
  induction rhos as [|rho rhos IH]; intros G a; simpl; [reflexivity|apply IH].
Qed.

Lemma ctx_lookup_lt_fold_bind_tm : forall rhos G x,
  ctx_lookup_lt (fold_right (fun rho G0 => bind_tm rho :: G0) G rhos) x = ctx_lookup_lt G x.
Proof.
  induction rhos as [|rho rhos IH]; intros G x; simpl; [reflexivity|apply IH].
Qed.

(* [ty_wf]/[lt_wf] depend only on the ty/lt-variable lookups, so they    *)
(* are invariant under any context change preserving those lookups —      *)
(* in particular under dropping bind_tm binders (which they ignore).      *)
Lemma lt_wf_conv : forall G1 l, lt_wf G1 l ->
  forall G2, (forall x, ctx_lookup_lt G1 x = ctx_lookup_lt G2 x) -> lt_wf G2 l.
Proof.
  intros G1 l H. induction H; intros G2 Hlt.
  - apply LWF_Var with (Δ := Δ). rewrite <- (Hlt x). exact H.
  - apply LWF_Free.
  - apply LWF_Local.
  - apply LWF_Min; [apply IHlt_wf1 | apply IHlt_wf2]; exact Hlt.
Qed.

Scheme ty_wf_mut := Induction for ty_wf Sort Prop
  with types_wf_mut := Induction for types_wf Sort Prop.

Lemma ty_wf_conv : forall G1 T, ty_wf G1 T ->
  forall G2, (forall a, ctx_lookup_ty G1 a = ctx_lookup_ty G2 a) ->
             (forall x, ctx_lookup_lt G1 x = ctx_lookup_lt G2 x) -> ty_wf G2 T.
Proof.
  apply (ty_wf_mut
    (fun G1 T (_ : ty_wf G1 T) =>
       forall G2, (forall a, ctx_lookup_ty G1 a = ctx_lookup_ty G2 a) ->
                  (forall x, ctx_lookup_lt G1 x = ctx_lookup_lt G2 x) -> ty_wf G2 T)
    (fun G1 Ts (_ : types_wf G1 Ts) =>
       forall G2, (forall a, ctx_lookup_ty G1 a = ctx_lookup_ty G2 a) ->
                  (forall x, ctx_lookup_lt G1 x = ctx_lookup_lt G2 x) -> types_wf G2 Ts)).
  - (* TWF_Var *) intros Γ α B Hlk Hsub IHB G2 Hty Hlt.
    apply TWF_Var with (B := B). rewrite <- (Hty α). exact Hlk. apply IHB; assumption.
  - (* TWF_Fun *) intros Γ A l B HA IHA Hl HB IHB G2 Hty Hlt.
    apply TWF_Fun; [apply IHA | eapply lt_wf_conv; [exact Hl|exact Hlt] | apply IHB]; assumption.
  - (* TWF_Ctor *) intros Γ K l Ts Hl HTs IHTs G2 Hty Hlt.
    apply TWF_Ctor; [eapply lt_wf_conv; [exact Hl|exact Hlt] | apply IHTs; assumption].
  - (* TWF_LtAll *) intros Γ A HA IHA G2 Hty Hlt.
    apply TWF_LtAll. apply IHA.
    + intros a. simpl. rewrite Hty. reflexivity.
    + intros x. destruct x as [|x']; simpl; [reflexivity| rewrite Hlt; reflexivity].
  - (* TWF_TyAll *) intros Γ B A HB IHB HA IHA G2 Hty Hlt.
    apply TWF_TyAll.
    + apply IHB; assumption.
    + apply IHA.
      * intros a. destruct a as [|a']; simpl; [reflexivity| rewrite Hty; reflexivity].
      * intros x. simpl. rewrite Hlt. reflexivity.
  - (* TWFs_nil *) intros Γ G2 Hty Hlt. apply TWFs_nil.
  - (* TWFs_cons *) intros Γ T Ts HT IHT HTs IHTs G2 Hty Hlt.
    apply TWFs_cons; [apply IHT | apply IHTs]; assumption.
Qed.

Lemma ty_wf_fold_bind_tm_inv : forall rhos G T,
  ty_wf (fold_right (fun rho G0 => bind_tm rho :: G0) G rhos) T -> ty_wf G T.
Proof.
  intros rhos G T H.
  eapply ty_wf_conv; [exact H| |].
  - intros a. apply ctx_lookup_ty_fold_bind_tm.
  - intros x. apply ctx_lookup_lt_fold_bind_tm.
Qed.


(* ------------------------------------------------------------------ *)
(* Type Safety corollary                                              *)
(* ------------------------------------------------------------------ *)

