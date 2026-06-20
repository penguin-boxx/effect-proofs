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

Definition perform_escape (ms : list marker) (t : term) : Prop :=
  exists E_tag m n_beta Ts T_R op_body Ss v P,
    In m ms /\ pure_ectx_m m P /\ value v /\
    t = plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v).

Definition progress_result (ms : list marker) (t : term) : Prop :=
  value t \/ (exists t', t ==> t') \/ perform_escape ms t.

(* Schema regularity for effect receivers: a value inhabiting an   *)
(* effect capability type is a runtime capability.                 *)

(* This is the dual of `canonical_ctor_data`: there the `T_Cap` case was        *)
(* impossible because the data tag has `ctx_lookup_eff = None`; here the        *)
(* `T_Ctor` case is impossible because the effect tag has                       *)
(* `ctx_lookup_eff = Some _`, and the data/effect tag-disjointness premise on   *)
(* `T_Ctor` (`ctx_lookup_eff Γ result_tag = None`) contradicts it.  The         *)
(* `E_tag <> any_tag` side-condition required by `sub_ctor_inv` is derived from *)
(* `eval_ctx_no_eff_any`: under an `eval_ctx`, no effect is registered at the   *)
(* reserved Any tag.                                                            *)
Lemma canonical_cap : forall Γ v E_tag Δ Ts n_α n_β sig ret,
    eval_ctx Γ ->
    ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
    Γ ⊢ₜ v : type_ctor E_tag Δ Ts ->
    value v ->
    exists m T_R op_body, v = term_cap E_tag m n_β Ts T_R op_body.
Proof.
  intros Γ v E_tag Δ Ts n_α n_β sig ret Hec Heff Hty.
  assert (HEne : E_tag <> any_tag).
  { intros Heq; subst E_tag.
    rewrite (eval_ctx_no_eff_any _ Hec) in Heff. discriminate. }
  remember (type_ctor E_tag Δ Ts) as T0 eqn:HT.
  revert Δ HT.
  induction Hty; intros Δ0 HT Hval; subst;
    try (inversion Hval; fail);
    try discriminate HT.
  - (* T_Sub *)
    destruct (sub_ctor_inv _ _ _ _ _ Hec H HEne) as [l' [HeqT _]].
    subst T.
    eapply IHHty; eauto.
  - (* T_Ctor: a data constructor cannot inhabit an effect type, since
       `T_Ctor` requires `ctx_lookup_eff Γ result_tag = None` while the goal's
       tag `E_tag` satisfies `ctx_lookup_eff Γ E_tag = Some _`. *)
    exfalso. congruence.
  - (* T_Cap: the value is a runtime capability with the matching β-arity. *)
    injection HT as HEeq Hleq HTseq; subst.
    match goal with
    | |- exists _ _ _, term_cap _ _ ?nb _ _ _ = _ =>
        replace n_β with nb by congruence
    end.
    do 3 eexists; reflexivity.
Qed.

Lemma canonical_lt_all : forall Γ v T,
  eval_ctx Γ ->
  Γ ⊢ₜ v : type_lt_all T ->
  value v ->
  exists body, v = term_lt_lam body.
Proof.
  intros Γ v T Hec Hty Hval.
  remember (type_lt_all T) as T0 eqn:HT.
  revert T HT.
  induction Hty; intros T0 HT; subst;
    try (inversion Hval; fail);
    try discriminate HT.
  - (* T_Sub *)
    destruct (sub_lt_all_inv _ _ _ Hec H) as [T' HeqT]; subst.
    eapply IHHty; eauto.
  - (* T_LtLam *) eauto.
  - (* T_Ctor *)
    match goal with
    | H1 : ?R = type_ctor _ _ _, H2 : ?R = type_lt_all _ |- _ => rewrite H1 in H2; discriminate H2
    | H1 : ?R = type_ctor _ _ _, H2 : type_lt_all _ = ?R |- _ => rewrite H1 in H2; discriminate H2
    | H1 : type_ctor _ _ _ = ?R, H2 : ?R = type_lt_all _ |- _ => rewrite <- H1 in H2; discriminate H2
    | H1 : type_ctor _ _ _ = ?R, H2 : type_lt_all _ = ?R |- _ => rewrite <- H1 in H2; discriminate H2
    | H : type_lt_all _ = type_ctor _ _ _ |- _ => discriminate H
    | H : type_ctor _ _ _ = type_lt_all _ |- _ => discriminate H
    end.
Qed.

Lemma canonical_ty_all : forall Γ v B T,
  eval_ctx Γ ->
  Γ ⊢ₜ v : type_ty_all B T ->
  value v ->
  exists bound body, v = term_ty_lam bound body.
Proof.
  intros Γ v B T Hec Hty Hval.
  remember (type_ty_all B T) as T0 eqn:HT.
  revert B T HT.
  induction Hty; intros B0 T0 HT; subst;
    try (inversion Hval; fail);
    try discriminate HT.
  - (* T_Sub *)
    destruct (sub_ty_all_inv _ _ _ _ Hec H) as [B' [T' HeqT]]; subst.
    eapply IHHty; eauto.
  - (* T_TyLam *) eauto.
  - (* T_Ctor *)
    match goal with
    | H1 : ?R = type_ctor _ _ _, H2 : ?R = type_ty_all _ _ |- _ => rewrite H1 in H2; discriminate H2
    | H1 : ?R = type_ctor _ _ _, H2 : type_ty_all _ _ = ?R |- _ => rewrite H1 in H2; discriminate H2
    | H1 : type_ctor _ _ _ = ?R, H2 : ?R = type_ty_all _ _ |- _ => rewrite <- H1 in H2; discriminate H2
    | H1 : type_ctor _ _ _ = ?R, H2 : type_ty_all _ _ = ?R |- _ => rewrite <- H1 in H2; discriminate H2
    | H : type_ty_all _ _ = type_ctor _ _ _ |- _ => discriminate H
    | H : type_ctor _ _ _ = type_ty_all _ _ |- _ => discriminate H
    end.
Qed.

Lemma canonical_ctor_data : forall Γ v K l Ts,
  eval_ctx Γ ->
  ctx_lookup_eff Γ K = None ->
  Γ ⊢ₜ v : type_ctor K l Ts ->
  value v ->
  K <> any_tag ->
  exists K' l' lts' Ts' vs,
    v = term_ctor K' l' lts' Ts' vs /\ Forall value vs.
Proof.
  intros Γ v K l Ts Hec Hnoeff Hty.
  remember (type_ctor K l Ts) as T0 eqn:HT.
  revert K l Ts HT Hnoeff.
  induction Hty; intros K0 l0 Ts0 HT Hnoeff Hval HK; subst;
    try (inversion Hval; fail);
    try discriminate HT.
  - (* T_Sub *)
    destruct (sub_ctor_inv _ _ _ _ _ Hec H HK) as [l' [HeqT _]].
    subst T.
    eapply IHHty; eauto.
  - (* T_Ctor *)
    inversion Hval; subst.
    exists K, l, lts, Ts, vs. split; [reflexivity|eassumption].
  - (* T_Cap *)
    injection HT as HK0 Hl0 HTs0. subst K0 l0 Ts0.
    rewrite H in Hnoeff. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* PROGRESS                                                           *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------- *)
(* Forall2 plumbing + a Forall2-aware induction principle for `typing` *)
(*                                                                     *)
(* Coq's auto-generated `typing_ind` does NOT thread per-element       *)
(* induction hypotheses through the `Forall2` premise of T_Ctor.       *)
(* `typing_ind2` below augments the T_Ctor case with exactly that      *)
(* `Forall2 (fun v rho => P Γ v rho)` hypothesis, which is what lets   *)
(* `progress` and `preservation` discharge the constructor case        *)
(* without any axioms.                                                 *)
(* ------------------------------------------------------------------- *)

Lemma f2_uncons_l : forall {A B} (R : A -> B -> Prop) x l ys,
  Forall2 R (x :: l) ys ->
  exists y l', ys = y :: l' /\ R x y /\ Forall2 R l l'.
Proof. intros A B R x l ys H. inversion H; subst. eauto. Qed.

Lemma Forall2_Forall_left : forall {A B} (R : A -> Prop) (S : A -> B -> Prop) xs ys,
  Forall2 S xs ys ->
  (forall x y, S x y -> R x) ->
  Forall R xs.
Proof.
  intros A B R S xs ys H Himp; induction H; constructor.
  - eapply Himp; eauto.
  - apply IHForall2; auto.
Qed.

Lemma typing_ind2 :
  forall (P : ctx -> term -> type -> Prop),
  (forall Γ x T, ctx_lookup_tm Γ x = Some T -> ty_wf Γ T -> P Γ (term_var x) T) ->
  (forall Γ t T U, Γ ⊢ₜ t : T -> P Γ t T -> Γ ⊢ T <:: U -> P Γ t U) ->
  (forall Γ body A l B,
    ty_wf Γ A ->
    ty_wf Γ B ->
     (bind_tm A :: Γ) ⊢ₜ body : B -> P (bind_tm A :: Γ) body B ->
    Γ ⊢ₗ capture_lt Γ body <: l ->
     P Γ (term_lam body A) (type_fun A l B)) ->
  (forall Γ t1 t2 A l B,
     Γ ⊢ₜ t1 : type_fun A l B -> P Γ t1 (type_fun A l B) ->
     Γ ⊢ₜ t2 : A -> P Γ t2 A ->
     P Γ (term_app t1 t2) B) ->
  (forall Γ bound body T,
    ty_wf Γ bound ->
    ty_wf (bind_ty bound :: Γ) T ->
     (bind_ty bound :: Γ) ⊢ₜ body : T -> P (bind_ty bound :: Γ) body T ->
     P Γ (term_ty_lam bound body) (type_ty_all bound T)) ->
  (forall Γ t B U S,
     Γ ⊢ₜ t : type_ty_all B U -> P Γ t (type_ty_all B U) ->
    ty_wf Γ S ->
     Γ ⊢ S <:: B ->
     P Γ (term_ty_app t S) (subst_ty 0 S U)) ->
  (forall Γ body T,
    ty_wf (bind_lt lt_local :: Γ) T ->
     (bind_lt lt_local :: Γ) ⊢ₜ body : T -> P (bind_lt lt_local :: Γ) body T ->
     P Γ (term_lt_lam body) (type_lt_all T)) ->
  (forall Γ t T l,
     Γ ⊢ₜ t : type_lt_all T -> P Γ t (type_lt_all T) ->
    lt_wf Γ l ->
     P Γ (term_lt_app t l) (subst_lt_in_ty 0 l T)) ->
        (forall Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
          result_ty result_tag l vs,
     ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) ->
     ctx_lookup_eff Γ K = None ->
     List.length lts = n_lt ->
    lifetimes_wf Γ lts ->
     rho_fields = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields ->
     List.length Ts = n_ty ->
    types_wf Γ Ts ->
      result_ty = inst_ctor_type n_lt n_ty lts Ts result_ty_schema ->
      result_ty = type_ctor result_tag l Ts ->
      ctx_lookup_eff Γ result_tag = None ->
     lt_wf Γ l ->
      Γ ⊢ₗ lt_of_ty_list rho_fields <: lt_of_ty result_ty ->
      Forall (fun l0 => Γ ⊢ₗ l0 <: l) lts ->
     List.length vs = List.length rho_fields ->
     Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rho_fields ->
     Forall2 (fun v rho => P Γ v rho) vs rho_fields ->
      P Γ (term_ctor K l lts Ts vs) result_ty) ->
        (forall Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
          rho_fields scrut_result_ty result_tag result_l
         Γ' yes_body eta elim_result no_body,
     K <> any_tag ->
     ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) ->
     ctx_lookup_eff Γ K = None ->
     lts = lt_var_list n_lt ->
     rho_fields = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields ->
      List.length Ts = n_ty ->
      types_wf Γ Ts ->
      scrut_result_ty = inst_ctor_type n_lt n_ty (List.repeat Delta n_lt) Ts result_ty_schema ->
      scrut_result_ty = type_ctor result_tag result_l Ts ->
      ctx_lookup_eff Γ result_tag = None ->
      result_tag <> any_tag ->
      lt_wf Γ Delta ->
      Γ ⊢ₗ result_l <: Delta ->
      Γ ⊢ₜ scrut : type_ctor result_tag Delta Ts ->
      P Γ scrut (type_ctor result_tag Delta Ts) ->
     arity = List.length rho_fields ->
     Γ' = push_lt_vars n_lt Delta Γ ->
     (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ' rho_fields) ⊢ₜ yes_body : eta ->
     P (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ' rho_fields) yes_body eta ->
     elim_ty_n n_lt (shift_lt n_lt 0 Delta) var_pos eta = Some elim_result ->
     Γ ⊢ₜ no_body : elim_result -> P Γ no_body elim_result ->
    P Γ (term_match scrut K n_lt arity yes_body no_body) elim_result) ->
  (forall Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β,
     ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
     List.length Ts = n_α ->
    types_wf Γ Ts ->
    ty_wf Γ T_R ->
      sig_β = inst_op_alpha n_α Ts n_β sig ->
      ret_β = inst_op_alpha n_α Ts n_β ret ->
     (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) ⊢ₜ op_body : shift_ty n_β 0 T_R ->
     P (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) op_body (shift_ty n_β 0 T_R) ->
    P Γ (term_cap E_tag m n_β Ts T_R op_body) (type_ctor E_tag lt_local Ts)) ->
  (forall Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β,
     ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
     List.length Ts = n_α ->
    types_wf Γ Ts ->
    ty_wf Γ T_B ->
    ty_wf Γ T_R ->
    Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free ->
    Γ ⊢ T_B <:: T_R ->
      sig_β = inst_op_alpha n_α Ts n_β sig ->
      ret_β = inst_op_alpha n_α Ts n_β ret ->
     (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) ⊢ₜ op_body : shift_ty n_β 0 T_R ->
     P (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) op_body (shift_ty n_β 0 T_R) ->
      (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) ⊢ₜ body : T_B ->
      P (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) body T_B ->
     P Γ (term_handle E_tag n_β Ts T_B T_R op_body body) T_R) ->
  (forall Γ recv arg E_tag Δ Ts Ss n_α n_β sig ret sig_inst ret_inst,
     Γ ⊢ₜ recv : type_ctor E_tag Δ Ts -> P Γ recv (type_ctor E_tag Δ Ts) ->
     ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
     List.length Ts = n_α ->
     List.length Ss = n_β ->
    types_wf Γ Ss ->
    Forall (fun S => Γ ⊢ₗ lt_of_ty_G Γ S <: lt_free) Ss ->
     sig_inst = inst_op_arg n_α Ts n_β Ss sig ->
      Γ ⊢ₗ lt_of_ty_G Γ sig_inst <: lt_free ->
     ret_inst = inst_op_arg n_α Ts n_β Ss ret ->
    ty_wf Γ ret_inst ->
     Γ ⊢ₜ arg : sig_inst -> P Γ arg sig_inst ->
     P Γ (term_perform recv Ss arg) ret_inst) ->
  (forall Γ m T_B T_R t,
    ty_wf Γ T_B ->
    ty_wf Γ T_R ->
    Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free ->
    Γ ⊢ T_B <:: T_R ->
    Γ ⊢ₜ t : T_B -> P Γ t T_B ->
    P Γ (term_handler_m m T_B T_R t) T_R) ->
  (forall Γ m b A T_B T_R,
    ty_wf Γ A ->
    ty_wf Γ T_B ->
    ty_wf Γ T_R ->
    Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free ->
    Γ ⊢ T_B <:: T_R ->
     (bind_tm A :: Γ) ⊢ₜ b : T_B -> P (bind_tm A :: Γ) b T_B ->
    P Γ (term_resume m T_B T_R b) (type_fun A lt_local T_R)) ->
  forall Γ t T, Γ ⊢ₜ t : T -> P Γ t T.
Proof.
  intros P HVar HSub HLam HApp HTyLam HTyApp HLtLam HLtApp HCtor HMatch
         HCap HHandle HPerform HHandlerM HResume.
  fix IH 4.
  intros Γ t T H. destruct H.
  - eapply HVar; (eassumption || (apply IH; eassumption)).
  - eapply HSub; (eassumption || (apply IH; eassumption)).
  - eapply HLam; (eassumption || (apply IH; eassumption)).
  - eapply HApp; (eassumption || (apply IH; eassumption)).
  - eapply HTyLam; (eassumption || (apply IH; eassumption)).
  - eapply HTyApp; (eassumption || (apply IH; eassumption)).
  - eapply HLtLam; (eassumption || (apply IH; eassumption)).
  - eapply HLtApp; (eassumption || (apply IH; eassumption)).
  - (* T_Ctor: build the Forall2 of IHs inline so the recursive calls    *)
    (* stay on structural subterms of the derivation (guardedness).      *)
    eapply HCtor; try (eassumption || (apply IH; eassumption)).
    match goal with
    | HF : Forall2 (fun v rho => _ ⊢ₜ v : rho) ?vs ?rf |- Forall2 _ ?vs ?rf =>
        clear -IH HF; induction HF
    end.
    + constructor.
    + constructor; [ apply IH; assumption | assumption ].
  - eapply HMatch; (eassumption || (apply IH; eassumption)).
  - eapply HCap; (eassumption || (apply IH; eassumption)).
  - eapply HHandle; (eassumption || (apply IH; eassumption)).
  - eapply HPerform; (eassumption || (apply IH; eassumption)).
  - eapply HHandlerM; (eassumption || (apply IH; eassumption)).
  - eapply HResume; (eassumption || (apply IH; eassumption)).
Qed.

(* A well-typed ctor value has |vs| matching its runtime tag's arity. *)
Lemma ctor_value_arity : forall Γ K l lts Ts vs T,
  Γ ⊢ₜ term_ctor K l lts Ts vs : T ->
  exists n_lt n_ty sigma result,
    ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma, result) /\
    List.length vs = List.length sigma.
Proof.
  intros Γ K l lts Ts vs T Hty.
  remember (term_ctor K l lts Ts vs) as t eqn:Ht.
  revert K l lts Ts vs Ht.
  induction Hty; intros K0 l0 lts0 Ts0 vs0 Ht; try discriminate Ht.
  - (* T_Sub *) eapply IHHty; eauto.
  - (* T_Ctor *)
    injection Ht; intros Hvs HTs0 Hlts0 Hl0 HK0.
    subst K0 l0 lts0 Ts0 vs0.
    exists n_lt, n_ty, sigma_fields, result_ty_schema. split; auto.
    match goal with
    | Hlen : List.length ?vs = List.length ?rho,
      Hrho : ?rho = List.map _ ?sigma |- List.length ?vs = List.length ?sigma =>
        rewrite Hlen, Hrho, List.length_map; reflexivity
    end.
Qed.

(* Helper: from Forall (value-or-step) deduce all-values or a step-in-list. *)
Lemma split_values_or_step : forall vs,
  Forall (fun v => value v \/ exists v', v ==> v') vs ->
  Forall value vs \/
  exists vsl t t' vsr,
    Forall value vsl /\ vs = vsl ++ t :: vsr /\ t ==> t'.
Proof.
  induction vs as [| v vs' IH]; intros H.
  { left; constructor. }
  inversion H as [| x xs Hhead Hrest]; subst.
  destruct Hhead as [Hv | [v' Hs]].
  - destruct (IH Hrest) as [Hall | [vsl [t [t' [vsr [Hallvl [Heq Hst]]]]]]].
    + left. constructor; auto.
    + right. exists (v :: vsl), t, t', vsr.
      repeat split; auto. simpl. f_equal; auto.
  - right. exists (@nil term), v, v', vs'. repeat split; auto.
Qed.

Lemma split_values_or_step_or_escape : forall ms vs,
  Forall (progress_result ms) vs ->
  Forall value vs \/
  (exists vsl t t' vsr,
    Forall value vsl /\ vs = vsl ++ t :: vsr /\ t ==> t') \/
  (exists vsl t vsr,
    Forall value vsl /\ vs = vsl ++ t :: vsr /\ perform_escape ms t).
Proof.
  intros ms vs. induction vs as [|v vs IH]; intros H.
  - left. constructor.
  - inversion H as [|x xs Hhead Hrest]; subst.
    destruct Hhead as [Hv | [[v' Hs] | Hesc]].
    + destruct (IH Hrest) as [Hall | Hnon].
      * left. constructor; auto.
      * destruct Hnon as
          [[vsl [t [t' [vsr [Hallvl [Heq Hst]]]]]]
          | [vsl [t [vsr [Hallvl [Heq Hesc']]]]]].
        -- right. left. exists (v :: vsl), t, t', vsr.
           repeat split; auto. simpl. f_equal; auto.
        -- right. right. exists (v :: vsl), t, vsr.
           repeat split; auto. simpl. f_equal; auto.
    + right. left. exists (@nil term), v, v', vs. repeat split; auto.
    + right. right. exists (@nil term), v, vs. repeat split; auto.
Qed.

Theorem progress_open_safe : forall Γ ms t T,
  eval_ctx Γ ->
  marker_ok ms t ->
  marker_types_safe t ->
  Γ ⊢ₜ t : T ->
  progress_result ms t.
Proof.
  intros Γ0 ms0 t0 T0 Hec0 Hmok0 Hsafe0 Hty0. revert ms0 Hmok0 Hsafe0 Hec0.
  revert Hty0; revert T0; revert t0; revert Γ0.
  apply (typing_ind2 (fun Γ t T => forall ms,
    marker_ok ms t -> marker_types_safe t -> eval_ctx Γ -> progress_result ms t)).
  - (* T_Var *)
    intros Γ x T Hlk Hwf ms Hmok Hsafe Hec.
    rewrite eval_ctx_no_tm in Hlk; auto; discriminate.
  - (* T_Sub *)
    intros Γ t T U Hty IH Hsub ms Hmok Hsafe Hec. apply IH; assumption.
  - (* T_Lam *)
    intros Γ body A l B HwfA HwfB Hbody IHbody Hcap ms Hmok Hsafe Hec. left; constructor.
  - (* T_App *)
    intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 ms Hmok Hsafe Hec.
    simpl in Hmok. destruct Hmok as [Hmok1 Hmok2].
    specialize (IH1 ms Hmok1 (marker_types_safe_app_l _ _ Hsafe) Hec).
    specialize (IH2 ms Hmok2 (marker_types_safe_app_r _ _ Hsafe) Hec).
    destruct IH1 as [Hv1 | [[t1' Hs1] | Hesc1]].
    + destruct IH2 as [Hv2 | [[t2' Hs2] | Hesc2]].
        * destruct (canonical_fun _ _ _ _ _ Hec Ht1 Hv1) as
          [[body [T0 Heq]] | [m [T_B [T_R [b Heq]]]]]; subst.
        -- right. left. eexists. apply S_Beta; auto.
        -- right. left. eexists. apply S_Resume; auto.
      * destruct (S_App2 t1 t2 Hv1 (ex_intro _ t2' Hs2)) as [u Hu].
        right. left. exists u. exact Hu.
      * destruct Hesc2 as (Et & m & nb & Ts0 & T_R & ob & Ss & v & P & Hin & Hp & Hv & Heq); subst.
        right. right. exists Et, m, nb, Ts0, T_R, ob, Ss, v, (EC_app2 t1 P).
        repeat split; auto.
    + destruct (S_App1 t1 t2 (ex_intro _ t1' Hs1)) as [u Hu].
      right. left. exists u. exact Hu.
    + destruct Hesc1 as (Et & m & nb & Ts0 & T_R & ob & Ss & v & P & Hin & Hp & Hv & Heq); subst.
      right. right. exists Et, m, nb, Ts0, T_R, ob, Ss, v, (EC_app1 P t2).
      repeat split; auto.
  - (* T_TyLam *)
    intros Γ bound body T HwfBound HwfT Hbody IHbody ms Hmok Hsafe Hec. left; constructor.
  - (* T_TyApp *)
    intros Γ t B U S Ht IH HwfS Hsub ms Hmok Hsafe Hec.
    simpl in Hmok. specialize (IH ms Hmok Hsafe Hec).
    destruct IH as [Hv | [[t' Hs] | Hesc]].
    + destruct (canonical_ty_all _ _ _ _ Hec Ht Hv) as [bnd [body Heq]]; subst.
      right. left. eexists. apply S_TyBeta.
    + destruct (S_TyApp t S (ex_intro _ t' Hs)) as [u Hu].
      right. left. exists u. exact Hu.
    + destruct Hesc as (Et & m & nb & Ts0 & T_R & ob & Ss & v & P & Hin & Hp & Hv & Heq); subst.
      right. right. exists Et, m, nb, Ts0, T_R, ob, Ss, v, (EC_ty_app P S).
      repeat split; auto.
  - (* T_LtLam *)
    intros Γ body T HwfT Hbody IHbody ms Hmok Hsafe Hec. left; constructor.
  - (* T_LtApp *)
    intros Γ t T l Ht IH Hwfl ms Hmok Hsafe Hec.
    simpl in Hmok. specialize (IH ms Hmok Hsafe Hec).
    destruct IH as [Hv | [[t' Hs] | Hesc]].
    + destruct (canonical_lt_all _ _ _ Hec Ht Hv) as [body Heq]; subst.
      right. left. eexists. apply S_LtBeta.
    + destruct (S_LtApp t l (ex_intro _ t' Hs)) as [u Hu].
      right. left. exists u. exact Hu.
    + destruct Hesc as (Et & m & nb & Ts0 & T_R & ob & Ss & v & P & Hin & Hp & Hv & Heq); subst.
      right. right. exists Et, m, nb, Ts0, T_R, ob, Ss, v, (EC_lt_app P l).
      repeat split; auto.
  - (* T_Ctor *)
    intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
      result_ty result_tag l vs
      Hlk Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs Hresult Hshape Hresult_eff Hwfl Hlt Hlen_vs
      HF HFP HargsIH ms Hmok Hsafe Hec.
    assert (Hmok_vs : Forall (marker_ok ms) vs).
    { clear - Hmok. induction vs as [|v vs IH]; simpl in Hmok; constructor; [tauto|apply IH; tauto]. }
    assert (Hsafe_vs : Forall marker_types_safe vs).
    { apply marker_types_safe_ctor_args with (K := K) (l := l) (lts := lts) (Ts := Ts). exact Hsafe. }
    assert (Hforall : Forall (progress_result ms) vs).
    { clear - HargsIH Hmok_vs Hsafe_vs Hec.
      induction HargsIH; inversion Hmok_vs; inversion Hsafe_vs; subst; constructor.
      - apply H; assumption.
      - apply IHHargsIH; assumption. }
    destruct (split_values_or_step_or_escape _ _ Hforall) as
      [Hall | [[vsl [tm [tm' [vsr [Hallvl [Heq Hst]]]]]]
              | [vsl [tm [vsr [Hallvl [Heq Hesc]]]]]]].
    + left. constructor; auto.
    + subst. destruct (S_Ctor K l lts Ts vsl tm vsr Hallvl (ex_intro _ tm' Hst)) as [u Hu].
      right. left. exists u. exact Hu.
    + destruct Hesc as (Et & m & nb & Ts0 & T_R & ob & Ss & v & P & Hin & Hp & Hv & Heqesc).
      subst vs tm.
      right. right. exists Et, m, nb, Ts0, T_R, ob, Ss, v, (EC_ctor K l lts Ts vsl P vsr).
      repeat split; auto.
  - (* T_Match *)
    intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
      rho_fields scrut_result_ty result_tag result_l Γ' yes_body eta elim_result no_body
      HKne Hlk Heff Hlts Hrho HTs HwfTs Hscrut_result Hscrut_shape
      Hresult_eff Hresult_ne HwfDelta Hresult_l Hscrut IHscrut Harity HGamma' Hyes IHyes Helim Hno IHno
      ms Hmok Hsafe Hec.
    simpl in Hmok. destruct Hmok as [Hmok_scrut [Hmok_yes Hmok_no]].
    specialize (IHscrut ms Hmok_scrut
      (marker_types_safe_match_scrut _ _ _ _ _ _ Hsafe) Hec).
    destruct IHscrut as [Hv | [[scrut' Hs] | Hesc]].
    + destruct (canonical_ctor_data _ _ result_tag Delta Ts Hec Hresult_eff Hscrut Hv Hresult_ne)
        as [K' [l' [lts' [Ts' [vs [Heq Hvvs]]]]]]; subst.
      right. left.
      destruct (Nat.eq_dec K' K) as [HKeq | HKdiff].
      * subst K'.
        destruct (ctor_value_arity _ _ _ _ _ _ _ Hscrut)
          as [n_lt' [n_ty' [sig' [res' [Hlook Hlen]]]]].
        rewrite Hlk in Hlook.
        injection Hlook as Heq1 Heq2 Heq3 Heq4.
        subst n_lt' n_ty' sig' res'.
        eexists.
        match goal with
        | |- term_match _ _ _ ?a _ _ ==> _ => replace a with (@length term vs)
        end.
        2:{ rewrite List.length_map. exact Hlen. }
        apply S_MatchYes. auto.
      * eexists. eapply S_MatchNo; eauto.
    + destruct (S_Match scrut K n_lt arity yes_body no_body (ex_intro _ scrut' Hs)) as [u Hu].
      right. left. exists u. exact Hu.
    + destruct Hesc as (Et & m & nb & Ts0 & T_R & ob & Ss & v & P & Hin & Hp & Hv & Heq).
      subst scrut.
      right. right. exists Et, m, nb, Ts0, T_R, ob, Ss, v, (EC_match P K n_lt arity yes_body no_body).
      repeat split; auto.
  - (* T_Cap *)
    intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
      Heff Hlen HwfTs HwfTR Hsb Hrb Hop IHop ms Hmok Hsafe Hec. left; constructor.
  - (* T_Handle *)
    intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
      Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hsb Hrb Hop IHop Hbody IHbody ms Hmok Hsafe Hec.
    set (m := marker_bound (term_handle E_tag n_β Ts T_B T_R op_body body)).
    right. left.
    exists (term_handler_m m T_B T_R (subst_tm 0 (term_cap E_tag m n_β Ts T_R op_body) body)).
    unfold m. apply S_Handle. apply marker_bound_fresh.
  - (* T_Perform *)
    intros Γ recv arg E_tag Δ Ts Ss n_α n_β sig ret sig_inst ret_inst
      Hrecv IHrecv Heff Hlen_Ts Hlen_Ss HwfSs HnoSs Hsi HnoSig Hri HwfRet Harg IHarg ms Hmok Hsafe Hec.
    simpl in Hmok. destruct Hmok as [Hmok_recv Hmok_arg].
    specialize (IHrecv ms Hmok_recv (marker_types_safe_perform_recv _ _ _ Hsafe) Hec).
    destruct IHrecv as [Hvrecv | [[recv' Hsrecv] | Hescrecv]].
    + specialize (IHarg ms Hmok_arg (marker_types_safe_perform_arg _ _ _ Hsafe) Hec).
      destruct IHarg as [Hvarg | [[arg' Hsarg] | Hescarg]].
      * destruct (canonical_cap Γ recv E_tag Δ Ts n_α n_β sig ret Hec Heff Hrecv Hvrecv)
          as [m [T_R [op_body Heqcap]]].
        subst recv. simpl in Hmok_recv. destruct Hmok_recv as [Hin Hop_ok].
        right. right. exists E_tag, m, n_β, Ts, T_R, op_body, Ss, arg, EC_hole.
        repeat split; auto.
      * destruct (S_PerformArg recv Ss arg Hvrecv (ex_intro _ arg' Hsarg)) as [u Hu].
        right. left. exists u. exact Hu.
      * destruct Hescarg as (Et & m & nb & Ts0 & T_R & ob & Ss0 & v & P & Hin & Hp & Hv & Heq); subst.
        right. right. exists Et, m, nb, Ts0, T_R, ob, Ss0, v, (EC_perform_a recv Ss P).
        repeat split; auto.
    + destruct (S_PerformRecv recv Ss arg (ex_intro _ recv' Hsrecv)) as [u Hu].
      right. left. exists u. exact Hu.
    + destruct Hescrecv as (Et & m & nb & Ts0 & T_R & ob & Ss0 & v & P & Hin & Hp & Hv & Heq); subst.
      right. right. exists Et, m, nb, Ts0, T_R, ob, Ss0, v, (EC_perform_r P Ss arg).
      repeat split; auto.
  - (* T_HandlerM *)
    intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH ms Hmok Hsafe Hec.
    simpl in Hmok.
    specialize (IH (m :: ms) Hmok (marker_types_safe_handler_body _ _ _ _ Hsafe) Hec).
    destruct IH as [Hv | [[t' Hs] | Hesc]].
    + right. left. exists t. apply S_Return; auto.
    + destruct (S_HandlerM m T_B T_R t (ex_intro _ t' Hs)) as [u Hu].
      right. left. exists u. exact Hu.
    + destruct Hesc as (Et & m0 & nb & Ts & T_R0 & op_body & Ss & v & P & Hin & Hp & Hv & Heq); subst.
      destruct (Nat.eq_dec m0 m) as [Heqm | Hneq].
      * subst m0. right. left. eexists.
        pose proof (marker_types_ok_handler_perform_annotation_match
                      m T_B T_R Et nb Ts T_R0 op_body Ss v P Hsafe) as HTR.
        subst T_R0.
        apply (S_step EC_hole); [constructor|]. apply H_Perform; auto.
      * destruct Hin as [Hin_head | Hin_tail].
        { subst. contradiction. }
        right. right. exists Et, m0, nb, Ts, T_R0, op_body, Ss, v, (EC_handler_m m T_B T_R P).
        repeat split; auto.
  - (* T_Resume *)
    intros Γ m T_B T_R b A HwfA HwfTB HwfTR HnoLocal Hsub Hb IHb ms Hmok Hsafe Hec. left; constructor.
Qed.

Theorem progress_safe : forall Γ t T,
  eval_ctx Γ ->
  marker_ok [] t ->
  marker_types_safe t ->
  Γ ⊢ₜ t : T ->
  value t \/ exists t', t ==> t'.
Proof.
  intros Γ t T Hec Hmok Hsafe Hty.
  destruct (progress_open_safe _ _ _ _ Hec Hmok Hsafe Hty) as [Hv | [[t' Hs] | Hesc]].
  - left. exact Hv.
  - right. exists t'. exact Hs.
  - destruct Hesc as (Et & m & nb & Ts & T_R & op_body & Ss & v & P & Hin & Hp & Hv & Heq).
    inversion Hin.
Qed.

Theorem progress : forall Γ t T,
  eval_ctx Γ ->
  marker_ok [] t ->
  marker_types_safe t ->
  Γ ⊢ₜ t : T ->
  value t \/ exists t', t ==> t'.
Proof.
  intros Γ t T Hec Hmok Hsafe Hty.
  eapply progress_safe; eauto.
Qed.
