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

Lemma elim_ty_n_sound_pos : forall n Delta lts eta elim_result Γ,
  elim_ty_n n (shift_lt n 0 Delta) var_pos eta = Some elim_result ->
  List.length lts = n ->
  lt_wf Γ Delta ->
  ty_wf (push_corr n Delta Γ) eta ->
  Forall (fun l => Γ ⊢ₗ l <: Delta) lts ->
  Γ ⊢ subst_list_lt_in_ty lts eta <:: elim_result.
Proof.
  intros n Delta lts eta elim_result Γ Helim Hlen HwfDelta HwfEta Hfor.
  subst n.
  pose proof (elim_in_ctx_sound (List.length lts) Delta eta elim_result Γ Helim
                HwfDelta HwfEta) as Hctx.
  pose proof (sub_peel_push_corr lts Delta eta
                (shift_lt_in_ty (List.length lts) 0 elim_result) Γ Hfor Hctx) as Hpeel.
  rewrite subst_list_lt_in_ty_shift_cancel in Hpeel.
  exact Hpeel.
Qed.

(* ------------------------------------------------------------------ *)
(* Inversion lemmas for T_Match and T_Ctor                            *)
(* ------------------------------------------------------------------ *)

Lemma match_typing_inv : forall Γ scrut K n_lt0 arity yes_body no_body T,
  Γ ⊢ₜ term_match scrut K n_lt0 arity yes_body no_body : T ->
  exists n_lt n_ty sigma_fields result_ty_schema Ts Delta scrut_result_ty
         result_tag result_l eta elim_result,
    K <> any_tag /\
    ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) /\
    ctx_lookup_eff Γ K = None /\
    n_lt0 = n_lt /\
    List.length Ts = n_ty /\
    scrut_result_ty = inst_ctor_type n_lt n_ty (List.repeat Delta n_lt) Ts result_ty_schema /\
    scrut_result_ty = type_ctor result_tag result_l Ts /\
    result_tag <> any_tag /\
    lt_wf Γ Delta /\
    Γ ⊢ₗ result_l <: Delta /\
    Γ ⊢ₜ scrut : type_ctor result_tag Delta Ts /\
    arity = List.length (List.map (inst_ctor_type_open n_lt n_ty Ts) sigma_fields) /\
    (fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
                (push_corr n_lt Delta Γ)
                (List.map (inst_ctor_type_open n_lt n_ty Ts) sigma_fields))
       ⊢ₜ yes_body : eta /\
    elim_ty_n n_lt (shift_lt n_lt 0 Delta) var_pos eta = Some elim_result /\
    Γ ⊢ₜ no_body : elim_result /\
    (elim_result = T \/ Γ ⊢ elim_result <:: T).
Proof.
  intros Γ scrut K n_lt0 arity yes_body no_body T Hty.
  remember (term_match scrut K n_lt0 arity yes_body no_body) as t eqn:Ht.
  induction Hty; try discriminate.
  - (* T_Sub *) subst.
    destruct (IHHty eq_refl) as
      [n_lt [n_ty [sig [res [Ts0 [Delta0 [scrut_result_ty0
       [result_tag0 [result_l0 [eta0 [elim_r Hinv]]]]]]]]]]].
    destruct Hinv as
      (HK & Hlk & Heff & Hnlt_eq & HTs & Hscrut_result & Hscrut_shape &
       Hresult_ne & HwfDelta & Hresult_l & Hscrut & Har & Hbody & Helim &
       Hno & HsubOr).
    exists n_lt, n_ty, sig, res, Ts0, Delta0, scrut_result_ty0,
      result_tag0, result_l0, eta0, elim_r.
    repeat split; auto.
    destruct HsubOr as [Heq|Hsub0].
    + subst. right. match goal with H : _ ⊢ _ <:: _ |- _ => exact H end.
    + right. eapply SA_Trans; [exact Hsub0|].
      match goal with H : _ ⊢ _ <:: _ |- _ => exact H end.
  - (* T_Match *)
    injection Ht; intros; subst.
    repeat eexists; repeat split; eauto.
    all: try match goal with
    | Hrho : ?rho = List.map _ ?sigma,
      Harity : ?arity0 = List.length ?rho
      |- ?arity0 = List.length (List.map _ ?sigma) =>
        rewrite Harity, Hrho; reflexivity
    end.
Qed.

Lemma ctor_typing_inv : forall Γ K l lts Ts vs T,
  Γ ⊢ₜ term_ctor K l lts Ts vs : T ->
  exists n_lt n_ty sigma_fields result_ty_schema result_tag,
    ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) /\
    List.length lts = n_lt /\
    List.length Ts = n_ty /\
    inst_ctor_type n_lt n_ty lts Ts result_ty_schema = type_ctor result_tag l Ts /\
    Forall (fun l0 => Γ ⊢ₗ l0 <: l) lts /\
    List.length vs = List.length sigma_fields /\
    Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs
            (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields) /\
    Γ ⊢ type_ctor result_tag l Ts <:: T.
Proof.
  intros Γ K l lts Ts vs T Hty.
  remember (term_ctor K l lts Ts vs) as t eqn:Ht.
  induction Hty; try discriminate.
  - (* T_Sub *) subst.
    destruct (IHHty eq_refl) as
      (n_lt & n_ty & sig & res & result_tag &
       Hlk & Hltlen & HTslen & Hresult & Hlts_bound & Hvslen & Hf2 & Hsub).
    exists n_lt, n_ty, sig, res, result_tag.
    repeat split; auto. eapply SA_Trans; eauto.
  - (* T_Ctor *)
    inversion Ht; subst.
    exists (List.length lts), (List.length Ts), sigma_fields, result_ty_schema, result_tag.
    repeat split; eauto; try reflexivity.
    + match goal with
      | Hlen : List.length vs = List.length (List.map _ sigma_fields) |- _ =>
          rewrite Hlen, List.length_map; reflexivity
      end.
    + match goal with
      | Hshape : inst_ctor_type (List.length lts) (List.length Ts) lts Ts result_ty_schema =
                 type_ctor result_tag l Ts |- _ =>
          rewrite Hshape; apply SA_Refl; constructor; assumption
      end.
Qed.

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
       In (S y) (List.concat (List.map (free_tm_vars c) ts)))).
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
    intros E n_beta Ts T_B T_R op_body body IHop IHb c y. simpl.
    rewrite !List.in_app_iff. intros [H|H].
    + left. apply IHop; exact H.
    + right. apply IHb; exact H.
  - (* perform *)
    intros t Ss arg IHt IHa c y. simpl.
    rewrite !List.in_app_iff. intros [H|H]; [left; apply IHt; exact H | right; apply IHa; exact H].
  - (* cap *)
    intros E m n_beta Ts T_R op_body IHop c y. simpl. apply IHop.
  - (* handler_m *)
    intros m T_B T_R t IH c y. simpl. apply IH.
  - (* resume *)
    intros m T_B T_R b IH c y. simpl. apply IH.
  - (* nil *)
    intros c y. simpl. intros [].
  - (* cons *)
    intros t ts IHt IHts c y. simpl.
    rewrite !List.in_app_iff. intros [H|H]; [left; apply IHt; exact H | right; apply IHts; exact H].
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
      intros Hnone. apply IHyes. apply lookup_tm_push_corr_None. exact Hnone.
    + apply IHno; exact Hn.
  - (* T_Cap *)
    intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           H1 H2 H3 H4 H5 H6 H7 IHop x Hin.
    simpl in Hin. apply (fv_add 2 op_body 0 x) in Hin.
    specialize (IHop (x + 2) Hin).
    replace (x + 2) with (S (S x)) in IHop by lia. simpl in IHop.
    intros Hnone. apply IHop. apply lookup_tm_push_ty_None. exact Hnone.
  - (* T_Handle *)
    intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
           H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 IHop H11 IHbody x Hin.
    simpl in Hin. rewrite List.in_app_iff in Hin. destruct Hin as [Hop | Hb].
    + apply (fv_add 2 op_body 0 x) in Hop. specialize (IHop (x + 2) Hop).
      replace (x + 2) with (S (S x)) in IHop by lia. simpl in IHop.
      intros Hnone. apply IHop. apply lookup_tm_push_ty_None. exact Hnone.
    + apply fv_succ in Hb. specialize (IHbody (S x) Hb).
      simpl in IHbody. exact IHbody.
  - (* T_Perform *)
        intros Γ recv arg E_tag Δ Ts Ss n_α n_β sig ret sig_inst ret_inst
          H1 IHrecv H3 H4 H5 H6 HnoSs H7 HnoSig H8 HwfRet H9 IHarg x Hin.
    simpl in Hin. rewrite List.in_app_iff in Hin.
    destruct Hin as [H|H]; [apply IHrecv | apply IHarg]; exact H.
  - (* T_HandlerM *)
    intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH x Hin. apply IH; exact Hin.
  - (* T_Resume *)
    intros Γ m b A T_B T_R HwfA HwfTB HwfTR HnoLocal Hsub Hb IH x Hin.
    simpl in Hin. apply fv_succ in Hin. specialize (IH (S x) Hin).
    simpl in IH. exact IH.
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

Lemma lt_wf_lookup_dom : forall G l,
  lt_wf G l -> forall G',
    (forall x, ctx_lookup_lt G x <> None -> ctx_lookup_lt G' x <> None) ->
    lt_wf G' l.
Proof.
  intros G l Hwf. induction Hwf; intros G' Hdom.
  - assert (Hsome : ctx_lookup_lt G' x <> None).
    { apply Hdom. rewrite H. discriminate. }
    destruct (ctx_lookup_lt G' x) as [D|] eqn:Hlk; [econstructor; exact Hlk|contradiction].
  - constructor.
  - constructor.
  - constructor; eauto.
Qed.

Lemma ty_wf_lookup_ty_eq_lt_dom_all :
  (forall G T, ty_wf G T -> forall G',
      (forall x, ctx_lookup_lt G x <> None -> ctx_lookup_lt G' x <> None) ->
      (forall a, ctx_lookup_ty G a = ctx_lookup_ty G' a) ->
      ty_wf G' T) /\
  (forall G Ts, types_wf G Ts -> forall G',
      (forall x, ctx_lookup_lt G x <> None -> ctx_lookup_lt G' x <> None) ->
      (forall a, ctx_lookup_ty G a = ctx_lookup_ty G' a) ->
      types_wf G' Ts).
Proof.
  apply (ty_wf_types_wf_mutind
    (fun G T _ => forall G',
      (forall x, ctx_lookup_lt G x <> None -> ctx_lookup_lt G' x <> None) ->
      (forall a, ctx_lookup_ty G a = ctx_lookup_ty G' a) ->
      ty_wf G' T)
    (fun G Ts _ => forall G',
      (forall x, ctx_lookup_lt G x <> None -> ctx_lookup_lt G' x <> None) ->
      (forall a, ctx_lookup_ty G a = ctx_lookup_ty G' a) ->
      types_wf G' Ts)).
  - intros Γ α B Hlk HwfB IHBound G' Hdom Htyeq.
    econstructor.
    + rewrite <- Htyeq. exact Hlk.
    + apply (IHBound G' Hdom Htyeq).
  - intros Γ A l B HwfA IHA Hwfl HwfB IHB G' Hdom Htyeq.
    constructor.
    + apply (IHA G' Hdom Htyeq).
    + eapply lt_wf_lookup_dom; eauto.
    + apply (IHB G' Hdom Htyeq).
  - intros Γ K l Ts Hwfl HwfTs IHTs G' Hdom Htyeq.
    constructor.
    + eapply lt_wf_lookup_dom; eauto.
    + apply (IHTs G' Hdom Htyeq).
  - intros Γ A HwfA IHA G' Hdom Htyeq.
    constructor. apply (IHA (bind_lt lt_local :: G')).
    + intros [|x] Hsome; simpl in *.
      * discriminate.
      * destruct (ctx_lookup_lt Γ x) as [D|] eqn:Hlk; [|contradiction].
        assert (ctx_lookup_lt G' x <> None) as Hsome'.
        { apply Hdom. rewrite Hlk. discriminate. }
        destruct (ctx_lookup_lt G' x); [discriminate|contradiction].
    + intro a. simpl. rewrite Htyeq. reflexivity.
  - intros Γ B A HwfB IHB HwfA IHA G' Hdom Htyeq.
    constructor.
    + apply (IHB G' Hdom Htyeq).
    + apply (IHA (bind_ty B :: G')).
      * intros x Hsome. simpl in *. apply Hdom. exact Hsome.
      * intros [|a]; simpl; [reflexivity|]. rewrite Htyeq. reflexivity.
  - intros Γ G' Hdom Htyeq. constructor.
  - intros Γ T Ts HwfT IHT HwfTs IHTs G' Hdom Htyeq.
    constructor.
    + apply (IHT G' Hdom Htyeq).
    + apply (IHTs G' Hdom Htyeq).
Qed.

Lemma ty_wf_lookup_ty_eq_lt_dom : forall G G' T,
  ty_wf G T ->
  (forall x, ctx_lookup_lt G x <> None -> ctx_lookup_lt G' x <> None) ->
  (forall a, ctx_lookup_ty G a = ctx_lookup_ty G' a) ->
  ty_wf G' T.
Proof.
  intros G G' T Hwf Hdom Htyeq.
  exact (proj1 ty_wf_lookup_ty_eq_lt_dom_all G T Hwf G' Hdom Htyeq).
Qed.

Lemma push_lt_vars_cons : forall n Delta G,
  push_lt_vars n Delta (bind_lt Delta :: G) = bind_lt Delta :: push_lt_vars n Delta G.
Proof.
  induction n as [|n IH]; intros Delta G.
  - reflexivity.
  - simpl. rewrite (IH Delta (bind_lt Delta :: G)). reflexivity.
Qed.

Lemma push_lt_vars_unfold_front : forall n Delta G,
  push_lt_vars (S n) Delta G = bind_lt Delta :: push_lt_vars n Delta G.
Proof.
  intros n Delta G. simpl. apply push_lt_vars_cons.
Qed.

Lemma ctx_lookup_ty_push_lt_vars_push_corr : forall n Delta G a,
  ctx_lookup_ty (push_lt_vars n Delta G) a = ctx_lookup_ty (push_corr n Delta G) a.
Proof.
  induction n as [|n IH]; intros Delta G a.
  - reflexivity.
  - rewrite push_lt_vars_unfold_front. simpl. rewrite IH. reflexivity.
Qed.

Lemma ctx_lookup_lt_push_lt_vars_push_corr_dom : forall n Delta G x,
  ctx_lookup_lt (push_lt_vars n Delta G) x <> None ->
  ctx_lookup_lt (push_corr n Delta G) x <> None.
Proof.
  induction n as [|n IH]; intros Delta G x Hsome.
  - exact Hsome.
  - rewrite push_lt_vars_unfold_front in Hsome. simpl in *.
    destruct x as [|x']; [discriminate|].
    destruct (ctx_lookup_lt (push_lt_vars n Delta G) x') as [D|] eqn:Hlk; [|contradiction].
    assert (ctx_lookup_lt (push_corr n Delta G) x' <> None) as Hsome'.
    { apply IH. rewrite Hlk. discriminate. }
    destruct (ctx_lookup_lt (push_corr n Delta G) x'); [discriminate|contradiction].
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

Lemma ctx_lookup_eff_fold_bind_tm : forall rhos G E,
  ctx_lookup_eff (fold_right (fun rho G0 => bind_tm rho :: G0) G rhos) E = ctx_lookup_eff G E.
Proof.
  induction rhos as [|rho rhos IH]; intros G E; simpl; [reflexivity|apply IH].
Qed.

Lemma ctx_lookup_eff_push_lt_vars_none : forall n Delta G E,
  ctx_lookup_eff G E = None ->
  ctx_lookup_eff (push_lt_vars n Delta G) E = None.
Proof.
  induction n as [|n IH]; intros Delta G E Hnone.
  - exact Hnone.
  - rewrite push_lt_vars_unfold_front. simpl. rewrite (IH Delta G E Hnone). reflexivity.
Qed.

Lemma typing_regular_no_eff : forall Γ t T,
  (forall E, ctx_lookup_eff Γ E = None) ->
  Γ ⊢ₜ t : T -> ty_wf Γ T.
Proof.
  intros Γ t T Hnoeff Hty. induction Hty.
  - match goal with Hwf : ty_wf Γ T |- _ => exact Hwf end.
  - match goal with Hsub : Γ ⊢ _ <:: _ |- _ =>
      destruct (sub_wf _ _ _ Hsub) as [_ HwfU]; exact HwfU
    end.
  - constructor.
    + match goal with Hwf : ty_wf Γ A |- _ => exact Hwf end.
    + match goal with Hsub : Γ ⊢ₗ capture_lt Γ body <: l |- _ =>
        destruct (lt_sub_wf _ _ _ Hsub) as [_ Hwfl]; exact Hwfl
      end.
    + match goal with Hwf : ty_wf Γ B |- _ => exact Hwf end.
  - specialize (IHHty1 Hnoeff). inversion IHHty1; subst. assumption.
  - constructor; assumption.
  - pose proof (IHHty Hnoeff) as HwfTyAll. inversion HwfTyAll; subst.
    eapply ty_wf_SubstTy; [eassumption|]. apply SubstTy_here.
    match goal with Hsub : Γ ⊢ _ <:: _ |- _ => exact Hsub end.
  - constructor. match goal with Hwf : ty_wf (bind_lt lt_local :: Γ) T |- _ => exact Hwf end.
  - pose proof (IHHty Hnoeff) as HwfLtAll. inversion HwfLtAll; subst.
    eapply ty_wf_SubstLt; [eassumption|]. apply SubstLt_here. apply LS_Local.
    match goal with Hwf : lt_wf Γ l |- _ => exact Hwf end.
  - match goal with
    | Hshape : ?R = type_ctor _ _ _ |- ty_wf _ ?R =>
        rewrite Hshape; constructor; assumption
    end.
  - apply IHHty3. exact Hnoeff.
  - specialize (Hnoeff E_tag).
    match goal with Hlk : ctx_lookup_eff Γ E_tag = Some _ |- _ => rewrite Hlk in Hnoeff end.
    discriminate.
  - specialize (Hnoeff E_tag).
    match goal with Hlk : ctx_lookup_eff Γ E_tag = Some _ |- _ => rewrite Hlk in Hnoeff end.
    discriminate.
  - specialize (Hnoeff E_tag).
    match goal with Hlk : ctx_lookup_eff Γ E_tag = Some _ |- _ => rewrite Hlk in Hnoeff end.
    discriminate.
  - match goal with Hwf : ty_wf Γ T_R |- _ => exact Hwf end.
  - constructor.
    + match goal with Hwf : ty_wf Γ A |- _ => exact Hwf end.
    + constructor.
    + match goal with Hwf : ty_wf Γ T_R |- _ => exact Hwf end.
Qed.

Lemma lt_wf_eval_ctx_shift_lt : forall Γ l amount,
  eval_ctx Γ ->
  lt_wf Γ l ->
  shift_lt amount 0 l = l.
Proof.
  intros Γ l amount Hec Hwf.
  induction Hwf; simpl.
  - rewrite (eval_ctx_no_lt Γ x Hec) in H. discriminate.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto.
Qed.

Lemma lt_wf_eval_ctx_subst_lt : forall Γ l var repl,
  eval_ctx Γ ->
  lt_wf Γ l ->
  subst_lt var repl l = l.
Proof.
  intros Γ l var repl Hec Hwf.
  induction Hwf; simpl.
  - rewrite (eval_ctx_no_lt Γ x Hec) in H. discriminate.
  - reflexivity.
  - reflexivity.
  - f_equal; eauto.
Qed.

Lemma chain_bounded_from_eval_ctx_forall : forall Γ lts n Delta,
  eval_ctx Γ ->
  lt_wf Γ Delta ->
  List.length lts = n ->
  Forall (fun l => Γ ⊢ₗ l <: Delta) lts ->
  chain_bounded Γ lts (shift_lt n 0 Delta).
Proof.
  induction lts as [|l rest IH]; intros n Delta Hec HwfDelta Hlen Hfor.
  - constructor.
  - simpl in Hlen. subst n. inversion Hfor as [|l0 rest0 Hl Hrest Heq]; subst.
    simpl. split.
    + rewrite (lt_wf_eval_ctx_shift_lt Γ Delta (S (List.length rest)) Hec HwfDelta).
      rewrite (lt_wf_eval_ctx_subst_lt Γ Delta 0 lt_free Hec HwfDelta).
      exact Hl.
    + rewrite (lt_wf_eval_ctx_shift_lt Γ Delta (S (List.length rest)) Hec HwfDelta).
      rewrite (lt_wf_eval_ctx_subst_lt Γ Delta 0 lt_free Hec HwfDelta).
      pose proof (IH (List.length rest) Delta Hec HwfDelta eq_refl Hrest) as Hcb.
      rewrite (lt_wf_eval_ctx_shift_lt Γ Delta (List.length rest) Hec HwfDelta) in Hcb.
      exact Hcb.
Qed.

(* ------------------------------------------------------------------ *)
(* Type Safety corollary                                              *)
(* ------------------------------------------------------------------ *)

Inductive multi_step : term -> term -> Prop :=
  | MS_Refl : forall t, multi_step t t
  | MS_Step : forall t1 t2 t3,
      t1 ==> t2 -> multi_step t2 t3 -> multi_step t1 t3.

Lemma multi_step_value_inv : forall v t,
  value v ->
  multi_step v t ->
  t = v.
Proof.
  intros v t Hv Hmulti.
  inversion Hmulti; subst.
  - reflexivity.
  - exfalso. eapply no_step_value; eauto.
Qed.
