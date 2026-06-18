Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import SubstitutionTheory.
Require Import SafetyMarkers.

Definition perform_escape (ms : list marker) (t : term) : Prop :=
  exists E_tag m n_beta Ts T_R op_body Ss v P,
    In m ms /\ pure_ectx_m m P /\ value v /\
    t = plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v).

Definition progress_result (ms : list marker) (t : term) : Prop :=
  value t \/ (exists t', t ==> t') \/ perform_escape ms t.

(* Schema regularity for effect receivers: a value inhabiting an   *)
(** effect capability type is a runtime capability.                *)

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
      ty_app_arg_no_local Γ B S = true ->
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
    no_local_ty_G Γ T_B = true ->
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
    forallb (no_local_ty_G Γ) Ss = true ->
     sig_inst = inst_op_arg n_α Ts n_β Ss sig ->
      no_local_ty_G Γ sig_inst = true ->
     ret_inst = inst_op_arg n_α Ts n_β Ss ret ->
    ty_wf Γ ret_inst ->
     Γ ⊢ₜ arg : sig_inst -> P Γ arg sig_inst ->
     P Γ (term_perform recv Ss arg) ret_inst) ->
  (forall Γ m T_B T_R t,
    ty_wf Γ T_B ->
    ty_wf Γ T_R ->
    no_local_ty_G Γ T_B = true ->
    Γ ⊢ T_B <:: T_R ->
    Γ ⊢ₜ t : T_B -> P Γ t T_B ->
    P Γ (term_handler_m m T_B T_R t) T_R) ->
  (forall Γ m b A T_B T_R,
    ty_wf Γ A ->
    ty_wf Γ T_B ->
    ty_wf Γ T_R ->
    no_local_ty_G Γ T_B = true ->
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
    intros Γ t B U S Ht IH HwfS Hsub HnlArg ms Hmok Hsafe Hec.
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

(* ------------------------------------------------------------------ *)
(* Typing inversion lemmas                                            *)
(* ------------------------------------------------------------------ *)

Lemma lam_typing_inv : forall Γ body A T,
  Γ ⊢ₜ term_lam body A : T ->
  exists l B,
    (bind_tm A :: Γ) ⊢ₜ body : B /\
    Γ ⊢ type_fun A l B <:: T.
Proof.
  intros Γ body A T Hty.
  remember (term_lam body A) as t eqn:Ht.
  induction Hty; try discriminate.
  - subst. destruct (IHHty eq_refl) as [l0 [B0 [Hbody Hsub]]].
    exists l0, B0; split; auto. eapply SA_Trans; eauto.
  - injection Ht; intros; subst. exists l, B; split; [assumption|].
    apply SA_Refl. constructor.
    + match goal with HwfA : ty_wf Γ A |- _ => exact HwfA end.
    + match goal with Hcap : Γ ⊢ₗ capture_lt Γ body <: l |- _ =>
        destruct (lt_sub_wf _ _ _ Hcap) as [_ Hwfl]; exact Hwfl
      end.
    + match goal with HwfB : ty_wf Γ B |- _ => exact HwfB end.
Qed.

Lemma ty_lam_typing_inv : forall Γ bound body T,
  Γ ⊢ₜ term_ty_lam bound body : T ->
  exists U,
    (bind_ty bound :: Γ) ⊢ₜ body : U /\
    Γ ⊢ type_ty_all bound U <:: T.
Proof.
  intros Γ bound body T Hty.
  remember (term_ty_lam bound body) as t eqn:Ht.
  induction Hty; try discriminate.
  - subst. destruct (IHHty eq_refl) as [U0 [Hbody Hsub]].
    exists U0; split; auto. eapply SA_Trans; eauto.
  - injection Ht; intros; subst. exists T; split; [assumption|].
    apply SA_Refl. constructor.
    + match goal with HwfBound : ty_wf Γ bound |- _ => exact HwfBound end.
    + match goal with HwfT : ty_wf (bind_ty bound :: Γ) T |- _ => exact HwfT end.
Qed.

Lemma lt_lam_typing_inv : forall Γ body T,
  Γ ⊢ₜ term_lt_lam body : T ->
  exists U,
    (bind_lt lt_local :: Γ) ⊢ₜ body : U /\
    Γ ⊢ type_lt_all U <:: T.
Proof.
  intros Γ body T Hty.
  remember (term_lt_lam body) as t eqn:Ht.
  induction Hty; try discriminate.
  - subst. destruct (IHHty eq_refl) as [U0 [Hbody Hsub]].
    exists U0; split; auto. eapply SA_Trans; eauto.
  - injection Ht; intros; subst. exists T; split; [assumption|].
    apply SA_Refl. constructor.
    match goal with HwfT : ty_wf (bind_lt lt_local :: Γ) T |- _ => exact HwfT end.
Qed.

Lemma resume_typing_inv : forall Γ m T_B T_R b T,
  Γ ⊢ₜ term_resume m T_B T_R b : T ->
  exists A,
    (bind_tm A :: Γ) ⊢ₜ b : T_B /\
    Γ ⊢ type_fun A lt_local T_R <:: T.
Proof.
  intros Γ m T_B T_R b T Hty.
  remember (term_resume m T_B T_R b) as t eqn:Ht.
  induction Hty; try discriminate.
  - subst. destruct (IHHty eq_refl) as [A0 [Hbody Hsub]].
    exists A0; split; auto. eapply SA_Trans; eauto.
  - injection Ht; intros; subst. exists A; split; [assumption|].
    apply SA_Refl. constructor.
    + match goal with HwfA : ty_wf Γ A |- _ => exact HwfA end.
    + constructor.
    + match goal with HwfTR : ty_wf Γ T_R |- _ => exact HwfTR end.
Qed.

(* ------------------------------------------------------------------ *)
(* PRESERVATION                                                       *)
(*                                                                    *)
(* Top-level structure is standard; the β-reduction cases rely on     *)
(* shape inversion and the substitution axioms above.  The App case   *)
(* is fully proven; Ty/Lt β-cases need a narrowing-style lemma that   *)
(* recovers the body-subtyping witness — axiomatized as sub_*_body.   *)
(* ------------------------------------------------------------------ *)

(* Narrowing/body-subtyping witnesses extracted from sub_*_inv.       *)
(* Under eval_ctx these follow structurally from the full inversion   *)
(* (including the body-subtype witness); we axiomatize the            *)
(* body-witness part since we stated sub_lt_all_inv / sub_ty_all_inv  *)
(* without it for brevity.                                            *)
Lemma sub_lt_all_inv_full : forall Γ S T,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_lt_all T ->
  exists T', S = type_lt_all T' /\ (bind_lt lt_local :: Γ) ⊢ T' <:: T.
Proof.
  intros Γ S T Hec Hsub.
  remember (type_lt_all T) as U eqn:HU.
  revert T HU.
  induction Hsub; intros T0 HU.
  - (* Refl *) inversion HU; subst. inversion H; subst.
    exists T0. split; [reflexivity|apply SA_Refl; assumption].
  - (* Trans *) subst T.
    destruct (IHHsub2 Hec _ eq_refl) as [U0 [HeqU HsubU]]; subst.
    destruct (IHHsub1 Hec _ eq_refl) as [S0 [HeqS HsubS]]; subst.
    exists S0; split; auto. eapply SA_Trans; eauto.
  - (* VarCtx *) subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - (* Data *) discriminate HU.
  - (* Any *) discriminate HU.
  - (* Fun *) discriminate HU.
  - (* LtAll *) injection HU; intros; subst. exists A; split; auto.
  - (* TyAll *) discriminate HU.
Qed.

(* ------------------------------------------------------------------ *)
(* Kernel-F<: narrowing for subtyping.                                *)
(*                                                                    *)
(* Replacing the bound of a type-variable binder by a *subtype*       *)
(* preserves any subtyping derivation under it.  We prove this by     *)
(* induction on the derivation, generalised over an arbitrary context *)
(* prefix `Δ` so the binder cases (`SA_LtAll`/`SA_TyAll`) go through. *)
(*                                                                    *)
(* Three context-level facts are needed:                              *)
(*   (a) lifetime subtyping is invariant under narrowing a `bind_ty`  *)
(*       (proved: `ctx_lookup_lt` skips `bind_ty` entries),           *)
(*   (b) general (no-shift) weakening of `<::` — for the `SA_VarCtx`  *)
(*       case when the looked-up variable *is* the narrowed one,      *)
(*   (c) `lt_of_ty_G` is monotone under narrowing — narrowing a bound *)
(*       to a subtype can only shrink the computed `lt_∅`.            *)
(* (b) and (c) are standard de Bruijn / lattice facts kept axiomatic, *)
(* in the same spirit as `sub_weaken_ty`; everything else is proved.  *)
(* ------------------------------------------------------------------ *)

(* (a.0) `ctx_lookup_lt` ignores the narrowed `bind_ty` slot. *)
Lemma ctx_lookup_lt_narrow : forall Δ Γ Bsup Bsub x,
  ctx_lookup_lt (Δ ++ bind_ty Bsub :: Γ) x
  = ctx_lookup_lt (Δ ++ bind_ty Bsup :: Γ) x.
Proof.
  induction Δ as [|b Δ' IH]; intros Γ Bsup Bsub x; simpl.
  - reflexivity.
  - destruct b; simpl.
    all: try apply IH.
    (* bind_lt remains *)
    destruct x; [reflexivity | rewrite (IH Γ Bsup Bsub x); reflexivity].
Qed.

(* (a.1) Lifetime subtyping only depends on the lt-lookup function. *)
Lemma lt_wf_lookup_eq : forall G1 l,
  lt_wf G1 l ->
  forall G2, (forall x, ctx_lookup_lt G1 x = ctx_lookup_lt G2 x) -> lt_wf G2 l.
Proof.
  intros G1 l Hwf. induction Hwf; intros G2 Heq.
  - econstructor. rewrite <- (Heq x). exact H.
  - constructor.
  - constructor.
  - constructor; eauto.
Qed.

Lemma lt_sub_lookup_eq : forall G1 l1 l2,
  G1 ⊢ₗ l1 <: l2 ->
  forall G2, (forall x, ctx_lookup_lt G1 x = ctx_lookup_lt G2 x) ->
  G2 ⊢ₗ l1 <: l2.
Proof.
  intros G1 l1 l2 H.
  induction H as [Γ l Hwf|Γ l Hwf|Γ x Δ Hlk HwfD|Γ l Hwf
                 |Γ l1 l2 l3 H1 IH1 H2 IH2|Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H1 IH1 Hwf2|Γ l l1 l2 H1 IH1 Hwf1]; intros G2 Heq.
  - apply LS_Free. eapply lt_wf_lookup_eq; eauto.
  - apply LS_Local. eapply lt_wf_lookup_eq; eauto.
  - apply LS_Var.
    + rewrite <- (Heq x). exact Hlk.
    + eapply lt_wf_lookup_eq; eauto.
  - apply LS_Refl. eapply lt_wf_lookup_eq; eauto.
  - eapply LS_Trans; eauto.
  - apply LS_MinL; eauto.
  - apply LS_MinR1; eauto. eapply lt_wf_lookup_eq; eauto.
  - apply LS_MinR2; eauto. eapply lt_wf_lookup_eq; eauto.
Qed.

(* (a) Lifetime subtyping is invariant under narrowing a `bind_ty`. *)
Lemma lt_sub_narrow : forall Δ Γ Bsup Bsub l1 l2,
  (Δ ++ bind_ty Bsup :: Γ) ⊢ₗ l1 <: l2 ->
  (Δ ++ bind_ty Bsub :: Γ) ⊢ₗ l1 <: l2.
Proof.
  intros Δ Γ Bsup Bsub l1 l2 H.
  eapply lt_sub_lookup_eq; [exact H |].
  intros x. symmetry. apply ctx_lookup_lt_narrow.
Qed.

(* `ctx_lookup_ty` either is unchanged by narrowing or hits the slot.   *)
(* When it hits the slot, both lookups return the *same* shift `s` of   *)
(* the respective bound (the path to the binder is identical in both    *)
(* contexts, so the accumulated shift is identical).                    *)
Lemma ctx_lookup_ty_narrow : forall Δ Γ Bsup Bsub α,
  (ctx_lookup_ty (Δ ++ bind_ty Bsub :: Γ) α
     = ctx_lookup_ty (Δ ++ bind_ty Bsup :: Γ) α)
  \/ (exists s, ctx_lookup_ty (Δ ++ bind_ty Bsup :: Γ) α = Some (s Bsup)
             /\ ctx_lookup_ty (Δ ++ bind_ty Bsub :: Γ) α = Some (s Bsub)).
Proof.
  induction Δ as [|b Δ' IH]; intros Γ Bsup Bsub α; simpl.
  - destruct α.
    + right. exists (shift_ty 1 0). split; reflexivity.
    + left. reflexivity.
  - destruct b; simpl; try apply IH.
    + (* bind_ty *)
      destruct α; [left; reflexivity | ].
      destruct (IH Γ Bsup Bsub α) as [Heq | [s [H1 H2]]].
      * left. rewrite Heq. reflexivity.
      * right. exists (fun T => shift_ty 1 0 (s T)).
        rewrite H1, H2. split; reflexivity.
    + (* bind_lt *)
      destruct (IH Γ Bsup Bsub α) as [Heq | [s [H1 H2]]].
      * left. rewrite Heq. reflexivity.
      * right. exists (fun T => shift_lt_in_ty 1 0 (s T)).
        rewrite H1, H2. split; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Lattice helper: `lt_min` is monotone in both arguments.            *)
(* ------------------------------------------------------------------ *)
Lemma lt_min_mono : forall G a a' b b',
  G ⊢ₗ a <: a' -> G ⊢ₗ b <: b' -> G ⊢ₗ lt_min a b <: lt_min a' b'.
Proof.
  intros G a a' b b' Ha Hb.
  destruct (lt_sub_wf _ _ _ Ha) as [_ Hwfa'].
  destruct (lt_sub_wf _ _ _ Hb) as [_ Hwfb'].
  apply LS_MinL.
  - eapply LS_Trans; [exact Ha |].
    apply LS_MinR1.
    + apply LS_Refl. exact Hwfa'.
    + exact Hwfb'.
  - eapply LS_Trans; [exact Hb |].
    apply LS_MinR2.
    + apply LS_Refl. exact Hwfb'.
    + exact Hwfa'.
Qed.

(* ------------------------------------------------------------------ *)
(* `lt_of_ty_ctx` is monotone in its fuel argument: with more fuel,   *)
(* type-variable chains are resolved further, which can only *raise*  *)
(* the computed lifetime (chains that run out of fuel bottom out at   *)
(* `lt_free`, the lattice bottom).                                    *)
(* ------------------------------------------------------------------ *)
Lemma lt_of_ty_ctx_wf : forall f G T,
  ty_wf G T -> f <= List.length G -> lt_wf G (lt_of_ty_ctx f G T)
with lt_of_ty_ctx_list_wf : forall f G Ts,
  types_wf G Ts -> f <= List.length G -> lt_wf G (lt_of_ty_ctx_list f G Ts).
Proof.
  - intros f G T Hwf. revert f.
    induction Hwf as [Γ α B Hlk HwfB IHB
                     |Γ A l B HwfA IHA Hwfl HwfB IHB
                     |Γ K l Ts Hwfl HwfTs IHTs
                     |Γ A HwfA IHA
                     |Γ B A HwfB IHB HwfA IHA]; intros f Hf.
    + rewrite (lt_of_ty_ctx_var f Γ α). destruct f as [|f']; [constructor|].
      rewrite Hlk. apply IHB. lia.
    + rewrite lt_of_ty_ctx_fun. exact Hwfl.
    + rewrite lt_of_ty_ctx_ctor. constructor; eauto.
    + rewrite lt_of_ty_ctx_ltall. constructor.
    + rewrite lt_of_ty_ctx_tyall. constructor.
  - intros f G Ts Hwf. induction Hwf; intros Hf.
    + rewrite lt_of_ty_ctx_list_nil. constructor.
    + rewrite lt_of_ty_ctx_list_cons. constructor.
      * eapply lt_of_ty_ctx_wf; eauto.
      * apply IHHwf. exact Hf.
Qed.

Lemma lt_of_ty_ctx_fuel_mono_S : forall f G T,
  ty_wf G T -> S f <= List.length G ->
  G ⊢ₗ lt_of_ty_ctx f G T <: lt_of_ty_ctx (S f) G T
with lt_of_ty_ctx_list_fuel_mono_S : forall f G Ts,
  types_wf G Ts -> S f <= List.length G ->
  G ⊢ₗ lt_of_ty_ctx_list f G Ts <: lt_of_ty_ctx_list (S f) G Ts.
Proof.
  - intros f G T Hwf. revert f.
    induction Hwf as [Γ α B Hlk HwfB IHB
                     |Γ A l B HwfA IHA Hwfl HwfB IHB
                     |Γ K l Ts Hwfl HwfTs IHTs
                     |Γ A HwfA IHA
                     |Γ B A HwfB IHB HwfA IHA]; intros f Hf.
    + rewrite (lt_of_ty_ctx_var f Γ α), (lt_of_ty_ctx_var (S f) Γ α).
      destruct f as [|f'].
      * rewrite Hlk. apply LS_Free. eapply lt_of_ty_ctx_wf; eauto. lia.
      * rewrite Hlk. apply IHB. lia.
    + rewrite !lt_of_ty_ctx_fun. apply LS_Refl. exact Hwfl.
    + rewrite !lt_of_ty_ctx_ctor. apply lt_min_mono.
      * apply LS_Refl. exact Hwfl.
      * eapply lt_of_ty_ctx_list_fuel_mono_S; eauto.
    + rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
  - intros f G Ts Hwf. induction Hwf; intros Hf.
    + rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + rewrite !lt_of_ty_ctx_list_cons. apply lt_min_mono.
      * eapply lt_of_ty_ctx_fuel_mono_S; eauto.
      * apply IHHwf. exact Hf.
Qed.

Lemma lt_of_ty_ctx_fuel_mono : forall f1 f2 G T,
  ty_wf G T -> f2 <= List.length G -> f1 <= f2 ->
  G ⊢ₗ lt_of_ty_ctx f1 G T <: lt_of_ty_ctx f2 G T.
Proof.
  intros f1 f2 G T Hwf Hf2. revert f1.
  induction f2 as [|f2 IH]; intros f1 Hle.
  - assert (f1 = 0) by lia. subst.
    apply LS_Refl. eapply lt_of_ty_ctx_wf; eauto.
  - destruct (Nat.eq_dec f1 (S f2)) as [Heq|Hneq].
    + subst. apply LS_Refl. eapply lt_of_ty_ctx_wf; eauto.
    + assert (Hle' : f1 <= f2) by lia.
      eapply LS_Trans.
      * apply IH; [lia|exact Hle'].
      * apply lt_of_ty_ctx_fuel_mono_S; assumption.
Qed.

(* ------------------------------------------------------------------- *)
(* `lt_of_ty_ctx` is monotone under subtyping (fixed context), as long *)
(* as the fuel does not exceed the context length (so the `SA_Any`     *)
(* premise, stated at fuel `|G|`, can be transported down via fuel     *)
(* monotonicity).                                                      *)
(* ------------------------------------------------------------------- *)
Lemma lt_of_ty_ctx_mono_sub : forall f G S T,
  G ⊢ S <:: T ->
  f <= List.length G ->
  G ⊢ₗ lt_of_ty_ctx f G S <: lt_of_ty_ctx f G T.
Proof.
  intros f G S T Hsub. revert f.
  induction Hsub as [Γ T Hwf|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                    |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                    |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                    |Γ A A' H1 IH1|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2]; intros f Hf.
  - (* SA_Refl *) apply LS_Refl. eapply lt_of_ty_ctx_wf; eauto.
  - (* SA_Trans *) eapply LS_Trans; [apply IH1 | apply IH2]; exact Hf.
  - (* SA_VarCtx *)
    rewrite (lt_of_ty_ctx_var f). destruct f as [|f'].
    + apply LS_Free. apply (lt_of_ty_ctx_wf 0 Γ B HwfB). lia.
    + rewrite Hlk. apply lt_of_ty_ctx_fuel_mono_S; [exact HwfB|lia].
  - (* SA_Data *)
    rewrite !lt_of_ty_ctx_ctor. apply lt_min_mono; [exact Hls|].
    apply LS_Refl. eapply lt_of_ty_ctx_list_wf; eauto.
  - (* SA_Any *)
    (* lt_of_ty_ctx f Γ T <: Δ <: lt_of_ty_ctx f Γ (any Δ []).          *)
    unfold lt_of_ty_G in Hls.
    eapply LS_Trans.
    + eapply LS_Trans; [ apply lt_of_ty_ctx_fuel_mono; [exact HwfT|apply Nat.le_refl|exact Hf] | exact Hls ].
    + rewrite lt_of_ty_ctx_ctor. apply LS_MinR1.
      * apply LS_Refl. exact HwfD.
      * constructor.
  - (* SA_Fun *) destruct f as [|f']; simpl; assumption.
  - (* SA_LtAll *) destruct f as [|f']; simpl; apply LS_Refl; constructor.
  - (* SA_TyAll *) destruct f as [|f']; simpl; apply LS_Refl; constructor.
Qed.

(* `G` is the wider (sup) context, `G'` the narrowed (sub) context. *)
Inductive NarrowTy : type -> type -> ctx -> ctx -> Prop :=
| NT_here : forall Bsub Bsup Γ,
    Γ ⊢ Bsub <:: Bsup ->
    NarrowTy Bsub Bsup (bind_ty Bsup :: Γ) (bind_ty Bsub :: Γ)
| NT_ty : forall Bsub Bsup G G' A,
    NarrowTy Bsub Bsup G G' ->
  ty_wf G A ->
  ty_wf G' A ->
    NarrowTy Bsub Bsup (bind_ty A :: G) (bind_ty A :: G')
| NT_lt : forall Bsub Bsup G G' D,
    NarrowTy Bsub Bsup G G' ->
  lt_wf G D ->
  lt_wf G' D ->
    NarrowTy Bsub Bsup (bind_lt D :: G) (bind_lt D :: G').

Lemma NT_length : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' -> length G = length G'.
Proof. intros Bsub Bsup G G' H. induction H; simpl; lia. Qed.

(* lt-lookups are unchanged by narrowing a `bind_ty` slot *)
Lemma NT_lookup_lt : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall x, ctx_lookup_lt G x = ctx_lookup_lt G' x.
Proof.
  intros Bsub Bsup G G' H. induction H; intro x.
  - simpl. reflexivity.
  - simpl. apply IHNarrowTy.
  - destruct x as [|x']; simpl.
    + reflexivity.
    + rewrite (IHNarrowTy x'). reflexivity.
Qed.

Lemma ty_wf_unshift_ty : forall Γ B S T,
  Γ ⊢ S <:: B ->
  ty_wf (bind_ty B :: Γ) (shift_ty 1 0 T) ->
  ty_wf Γ T.
Proof.
  intros Γ B S T Hsub Hwf.
  pose proof (ty_wf_SubstTy (bind_ty B :: Γ) (shift_ty 1 0 T) Hwf
               S 0 Γ (SubstTy_here Γ B S Hsub)) as HwfSub.
  rewrite subst_ty_shift_cancel in HwfSub. exact HwfSub.
Qed.

Lemma ty_wf_unshift_lt : forall Γ D R T,
  Γ ⊢ₗ R <: D ->
  ty_wf (bind_lt D :: Γ) (shift_lt_in_ty 1 0 T) ->
  ty_wf Γ T.
Proof.
  intros Γ D R T Hsub Hwf.
  pose proof (ty_wf_SubstLt (bind_lt D :: Γ) (shift_lt_in_ty 1 0 T) Hwf
               R 0 Γ (SubstLt_here Γ D R Hsub)) as HwfSub.
  rewrite subst_lt_in_ty_shift_cancel in HwfSub. exact HwfSub.
Qed.

Lemma lt_wf_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall l, lt_wf G l -> lt_wf G' l.
Proof.
  intros Bsub Bsup G G' HN l Hwf.
  eapply lt_wf_lookup_eq; [exact Hwf|].
  intros x. apply (NT_lookup_lt Bsub Bsup G G' HN x).
Qed.

Lemma lt_sub_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall l1 l2, G ⊢ₗ l1 <: l2 -> G' ⊢ₗ l1 <: l2.
Proof.
  intros Bsub Bsup G G' HN l1 l2 H.
  eapply lt_sub_lookup_eq; [exact H |].
  intros x. apply (NT_lookup_lt Bsub Bsup G G' HN x).
Qed.

(* ty-lookup narrowing: the narrowed bound is a subtype, in both ctxs *)
Lemma NT_lookup_sub : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall α U, ctx_lookup_ty G α = Some U -> ty_wf G U ->
    exists U', ctx_lookup_ty G' α = Some U'
            /\ G ⊢ U' <:: U
            /\ G' ⊢ U' <:: U.
Proof.
  intros Bsub Bsup G G' HN.
  induction HN as [Bsub Bsup Γ Hsub
                  |Bsub Bsup G G' A HN IH HwfA HwfA'
                  |Bsub Bsup G G' D HN IH HwfD HwfD']; intros α U Hlk HwfU.
  - (* NT_here *) destruct α as [|n].
    + simpl in Hlk. injection Hlk; intros; subst U.
      exists (shift_ty 1 0 Bsub). split; [reflexivity|]. split.
      * apply (sub_weaken_ty_shift Γ Bsup Bsub Bsup Hsub).
      * apply (sub_weaken_ty_shift Γ Bsub Bsub Bsup Hsub).
    + simpl in Hlk.
      destruct (ctx_lookup_ty Γ n) as [W|] eqn:E; simpl in Hlk; [|discriminate].
      injection Hlk; intros; subst U.
      assert (HwfW : ty_wf Γ W).
      { eapply ty_wf_unshift_ty; [exact Hsub|exact HwfU]. }
      assert (HwfTarget : ty_wf (bind_ty Bsub :: Γ) (shift_ty 1 0 W)).
      { eapply ty_wf_InsTy; [exact HwfW|apply InsTy_here]. }
      exists (shift_ty 1 0 W). split; [simpl; rewrite E; reflexivity|].
      split; apply SA_Refl; assumption.
  - (* NT_ty *) destruct α as [|n].
    + simpl in Hlk. injection Hlk; intros; subst U.
      assert (HwfTarget : ty_wf (bind_ty A :: G') (shift_ty 1 0 A)).
      { eapply ty_wf_InsTy; [exact HwfA'|apply InsTy_here]. }
      exists (shift_ty 1 0 A). simpl. split; [reflexivity|]. split; apply SA_Refl; assumption.
    + simpl in Hlk. destruct (ctx_lookup_ty G n) as [W|] eqn:E; simpl in Hlk;
        [|discriminate].
      injection Hlk; intros; subst U.
      assert (HwfW : ty_wf G W).
      { eapply ty_wf_unshift_ty; [apply SA_Refl; exact HwfA|exact HwfU]. }
      destruct (IH n W E HwfW) as [W' [HW' [HsubG HsubG']]].
      exists (shift_ty 1 0 W'). simpl. rewrite HW'. simpl.
      split; [reflexivity|]. split.
      * apply (sub_weaken_ty_shift G A W' W HsubG).
      * apply (sub_weaken_ty_shift G' A W' W HsubG').
  - (* NT_lt *) simpl in Hlk.
    destruct (ctx_lookup_ty G α) as [W|] eqn:E; simpl in Hlk; [|discriminate].
    injection Hlk; intros; subst U.
    assert (HwfW : ty_wf G W).
    { eapply ty_wf_unshift_lt; [apply LS_Refl; exact HwfD|exact HwfU]. }
    destruct (IH α W E HwfW) as [W' [HW' [HsubG HsubG']]].
    exists (shift_lt_in_ty 1 0 W'). simpl. rewrite HW'. simpl.
    split; [reflexivity|]. split.
    + apply (sub_weaken_lt_shift G D W' W HsubG).
    + apply (sub_weaken_lt_shift G' D W' W HsubG').
Qed.

Lemma NT_lookup_None : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall α, ctx_lookup_ty G α = None -> ctx_lookup_ty G' α = None.
Proof.
  intros Bsub Bsup G G' H. induction H; intros α Hlk.
  - destruct α as [|n]; simpl in *.
    + discriminate.
    + destruct (ctx_lookup_ty Γ n) as [W|] eqn:E; simpl in Hlk; [discriminate|].
      reflexivity.
  - destruct α as [|n]; simpl in *.
    + discriminate.
    + destruct (ctx_lookup_ty G n) as [W|] eqn:E; simpl in Hlk; [discriminate|].
      rewrite (IHNarrowTy n E). reflexivity.
  - simpl in *.
    destruct (ctx_lookup_ty G α) as [W|] eqn:E; simpl in Hlk; [discriminate|].
    rewrite (IHNarrowTy α E). reflexivity.
Qed.

Scheme ty_wf_mutind := Induction for ty_wf Sort Prop
with types_wf_mutind := Induction for types_wf Sort Prop.
Combined Scheme ty_wf_types_wf_mutind from ty_wf_mutind, types_wf_mutind.

(* lt_of_ty_ctx is monotone under narrowing (computed lt_∅ can only shrink) *)
Lemma lt_of_ty_ctx_NT_all : forall f,
  (forall G T, ty_wf G T -> forall Bsub Bsup G',
      NarrowTy Bsub Bsup G G' -> f <= List.length G ->
      G' ⊢ₗ lt_of_ty_ctx f G' T <: lt_of_ty_ctx f G T) /\
  (forall G Ts, types_wf G Ts -> forall Bsub Bsup G',
      NarrowTy Bsub Bsup G G' -> f <= List.length G ->
      G' ⊢ₗ lt_of_ty_ctx_list f G' Ts <: lt_of_ty_ctx_list f G Ts).
Proof.
  induction f as [|f' IHf].
  - apply (ty_wf_types_wf_mutind
      (fun G T _ => forall Bsub Bsup G', NarrowTy Bsub Bsup G G' ->
        0 <= List.length G -> G' ⊢ₗ lt_of_ty_ctx 0 G' T <: lt_of_ty_ctx 0 G T)
      (fun G Ts _ => forall Bsub Bsup G', NarrowTy Bsub Bsup G G' ->
        0 <= List.length G -> G' ⊢ₗ lt_of_ty_ctx_list 0 G' Ts <: lt_of_ty_ctx_list 0 G Ts)).
    + intros Γ α B Hlk HwfB IHBound Bsub Bsup G' HN Hf.
      rewrite !(lt_of_ty_ctx_var 0). apply LS_Refl. constructor.
    + intros Γ A l B HwfA IHA Hwfl HwfB IHB Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_fun. apply LS_Refl. eapply lt_wf_NT; eauto.
    + intros Γ K l Ts Hwfl HwfTs IHTs Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_ctor. apply lt_min_mono.
      * apply LS_Refl. eapply lt_wf_NT; eauto.
      * apply (IHTs Bsub Bsup G' HN Hf).
    + intros Γ A HwfA IHA Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + intros Γ B A HwfB IHB HwfA IHA Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + intros Γ Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + intros Γ T Ts HwfT IHT HwfTs IHTs Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_list_cons. apply lt_min_mono.
      * apply (IHT Bsub Bsup G' HN Hf).
      * apply (IHTs Bsub Bsup G' HN Hf).
  - destruct IHf as [IHf_ty IHf_tys].
    apply (ty_wf_types_wf_mutind
      (fun G T _ => forall Bsub Bsup G', NarrowTy Bsub Bsup G G' ->
        S f' <= List.length G -> G' ⊢ₗ lt_of_ty_ctx (S f') G' T <: lt_of_ty_ctx (S f') G T)
      (fun G Ts _ => forall Bsub Bsup G', NarrowTy Bsub Bsup G G' ->
        S f' <= List.length G -> G' ⊢ₗ lt_of_ty_ctx_list (S f') G' Ts <: lt_of_ty_ctx_list (S f') G Ts)).
    + intros Γ α B Hlk HwfB IHBound Bsub Bsup G' HN Hf.
      rewrite (lt_of_ty_ctx_var (S f') G' α), (lt_of_ty_ctx_var (S f') Γ α).
      destruct (NT_lookup_sub Bsub Bsup Γ G' HN α B Hlk HwfB)
        as [B' [HB' [HsubG HsubG']]].
      rewrite Hlk, HB'.
      destruct (sub_wf _ _ _ HsubG) as [HwfB' _].
      assert (Hf' : f' <= List.length Γ) by lia.
      eapply LS_Trans.
      * apply (IHf_ty Γ B' HwfB' Bsub Bsup G' HN Hf').
      * apply (lt_sub_NT Bsub Bsup Γ G' HN).
        apply (lt_of_ty_ctx_mono_sub f' Γ B' B HsubG Hf').
    + intros Γ A l B HwfA IHA Hwfl HwfB IHB Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_fun. apply LS_Refl. eapply lt_wf_NT; eauto.
    + intros Γ K l Ts Hwfl HwfTs IHTs Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_ctor. apply lt_min_mono.
      * apply LS_Refl. eapply lt_wf_NT; eauto.
      * apply (IHTs Bsub Bsup G' HN Hf).
    + intros Γ A HwfA IHA Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + intros Γ B A HwfB IHB HwfA IHA Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + intros Γ Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + intros Γ T Ts HwfT IHT HwfTs IHTs Bsub Bsup G' HN Hf.
      rewrite !lt_of_ty_ctx_list_cons. apply lt_min_mono.
      * apply (IHT Bsub Bsup G' HN Hf).
      * apply (IHTs Bsub Bsup G' HN Hf).
Qed.

Lemma lt_of_ty_ctx_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall f T, ty_wf G T -> f <= List.length G ->
    G' ⊢ₗ lt_of_ty_ctx f G' T <: lt_of_ty_ctx f G T.
Proof.
  intros Bsub Bsup G G' HN f T Hwf Hf.
  exact (proj1 (lt_of_ty_ctx_NT_all f) G T Hwf Bsub Bsup G' HN Hf).
Qed.

Lemma lt_of_ty_ctx_list_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall f Ts, types_wf G Ts -> f <= List.length G ->
    G' ⊢ₗ lt_of_ty_ctx_list f G' Ts <: lt_of_ty_ctx_list f G Ts.
Proof.
  intros Bsub Bsup G G' HN f Ts Hwf Hf.
  exact (proj2 (lt_of_ty_ctx_NT_all f) G Ts Hwf Bsub Bsup G' HN Hf).
Qed.

Lemma lt_of_ty_G_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' ->
  forall T, ty_wf G T -> G' ⊢ₗ lt_of_ty_G G' T <: lt_of_ty_G G T.
Proof.
  intros Bsub Bsup G G' HN T HwfT. unfold lt_of_ty_G.
  rewrite <- (NT_length Bsub Bsup G G' HN).
  apply (lt_of_ty_ctx_NT Bsub Bsup G G' HN (List.length G) T HwfT (Nat.le_refl _)).
Qed.

Lemma ty_wf_NT_all :
  (forall G T, ty_wf G T -> forall Bsub Bsup G',
      NarrowTy Bsub Bsup G G' -> ty_wf G' T) /\
  (forall G Ts, types_wf G Ts -> forall Bsub Bsup G',
      NarrowTy Bsub Bsup G G' -> types_wf G' Ts).
Proof.
  apply (ty_wf_types_wf_mutind
    (fun G T _ => forall Bsub Bsup G', NarrowTy Bsub Bsup G G' -> ty_wf G' T)
    (fun G Ts _ => forall Bsub Bsup G', NarrowTy Bsub Bsup G G' -> types_wf G' Ts)).
  - intros Γ α B Hlk HwfB IHBound Bsub Bsup G' HN.
    destruct (NT_lookup_sub Bsub Bsup Γ G' HN α B Hlk HwfB)
      as [B' [HB' [_ HsubG']]].
    destruct (sub_wf _ _ _ HsubG') as [HwfB' _].
    econstructor; eauto.
  - intros Γ A l B HwfA IHA Hwfl HwfB IHB Bsub Bsup G' HN.
    constructor.
    + apply (IHA Bsub Bsup G' HN).
    + eapply lt_wf_NT; eauto.
    + apply (IHB Bsub Bsup G' HN).
  - intros Γ K l Ts Hwfl HwfTs IHTs Bsub Bsup G' HN.
    constructor.
    + eapply lt_wf_NT; eauto.
    + apply (IHTs Bsub Bsup G' HN).
  - intros Γ A HwfA IHA Bsub Bsup G' HN.
    constructor.
    apply (IHA Bsub Bsup (bind_lt lt_local :: G')).
    apply NT_lt; [exact HN|constructor|constructor].
  - intros Γ B A HwfB IHB HwfA IHA Bsub Bsup G' HN.
    constructor.
    + apply (IHB Bsub Bsup G' HN).
    + apply (IHA Bsub Bsup (bind_ty B :: G')).
      apply NT_ty.
      * exact HN.
      * exact HwfB.
      * apply (IHB Bsub Bsup G' HN).
  - intros Γ Bsub Bsup G' HN. constructor.
  - intros Γ T Ts HwfT IHT HwfTs IHTs Bsub Bsup G' HN.
    constructor.
    + apply (IHT Bsub Bsup G' HN).
    + apply (IHTs Bsub Bsup G' HN).
Qed.

Lemma ty_wf_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' -> forall T, ty_wf G T -> ty_wf G' T.
Proof.
  intros Bsub Bsup G G' HN T Hwf.
  exact (proj1 ty_wf_NT_all G T Hwf Bsub Bsup G' HN).
Qed.

Lemma types_wf_NT : forall Bsub Bsup G G',
  NarrowTy Bsub Bsup G G' -> forall Ts, types_wf G Ts -> types_wf G' Ts.
Proof.
  intros Bsub Bsup G G' HN Ts Hwf.
  exact (proj2 ty_wf_NT_all G Ts Hwf Bsub Bsup G' HN).
Qed.

(* Well-formedness of types does not depend on the subtyping strength of a *)
(* type-variable bound, only on the replacement bound being well-formed.   *)
Inductive ReplaceTy : ctx -> ctx -> Prop :=
  | RT_here : forall Γ B B',
      ty_wf Γ B ->
      ty_wf Γ B' ->
      ReplaceTy (bind_ty B :: Γ) (bind_ty B' :: Γ)
  | RT_ty : forall G G' B,
      ReplaceTy G G' ->
      ty_wf G B ->
      ty_wf G' B ->
      ReplaceTy (bind_ty B :: G) (bind_ty B :: G')
  | RT_lt : forall G G' Δ,
      ReplaceTy G G' ->
      lt_wf G Δ ->
      lt_wf G' Δ ->
      ReplaceTy (bind_lt Δ :: G) (bind_lt Δ :: G').

Lemma RT_lookup_lt : forall G G',
  ReplaceTy G G' -> forall x, ctx_lookup_lt G x = ctx_lookup_lt G' x.
Proof.
  intros G G' H. induction H; intro x; simpl.
  - reflexivity.
  - apply IHReplaceTy.
  - destruct x as [|x']; [reflexivity|]. rewrite (IHReplaceTy x'). reflexivity.
Qed.

Lemma RT_lookup_ty : forall G G',
  ReplaceTy G G' ->
  forall α B, ctx_lookup_ty G α = Some B -> ty_wf G B ->
    exists B', ctx_lookup_ty G' α = Some B' /\ ty_wf G' B'.
Proof.
  intros G G' H. induction H as [Γ B B' HwfB HwfB'
                                |G G' B HRT IH HwfB HwfB'
                                |G G' Δ HRT IH HwfΔ HwfΔ'];
    intros α U Hlk HwfU.
  - destruct α as [|α']; simpl in Hlk.
    + injection Hlk; intros; subst U.
      exists (shift_ty 1 0 B'). split; [reflexivity|].
      eapply ty_wf_InsTy; [exact HwfB'|apply InsTy_here].
    + destruct (ctx_lookup_ty Γ α') as [W|] eqn:E; simpl in Hlk; [|discriminate].
      injection Hlk; intros; subst U.
      assert (HwfW : ty_wf Γ W).
      { eapply ty_wf_unshift_ty; [apply SA_Refl; exact HwfB|exact HwfU]. }
      exists (shift_ty 1 0 W). split.
      * simpl. rewrite E. reflexivity.
      * eapply ty_wf_InsTy; [exact HwfW|apply InsTy_here].
  - destruct α as [|α']; simpl in Hlk.
    + injection Hlk; intros; subst U.
      exists (shift_ty 1 0 B). split; [reflexivity|].
      eapply ty_wf_InsTy; [exact HwfB'|apply InsTy_here].
    + destruct (ctx_lookup_ty G α') as [W|] eqn:E; simpl in Hlk; [|discriminate].
      injection Hlk; intros; subst U.
      assert (HwfW : ty_wf G W).
      { eapply ty_wf_unshift_ty; [apply SA_Refl; exact HwfB|exact HwfU]. }
      destruct (IH α' W E HwfW) as [W' [HW' HwfW']].
      exists (shift_ty 1 0 W'). split.
      * simpl. rewrite HW'. reflexivity.
      * eapply ty_wf_InsTy; [exact HwfW'|apply InsTy_here].
  - simpl in Hlk.
    destruct (ctx_lookup_ty G α) as [W|] eqn:E; simpl in Hlk; [|discriminate].
    injection Hlk; intros; subst U.
    assert (HwfW : ty_wf G W).
    { eapply ty_wf_unshift_lt; [apply LS_Refl; exact HwfΔ|exact HwfU]. }
    destruct (IH α W E HwfW) as [W' [HW' HwfW']].
    exists (shift_lt_in_ty 1 0 W'). split.
    + simpl. rewrite HW'. reflexivity.
    + eapply ty_wf_InsLt; [exact HwfW'|apply InsLt_here].
Qed.

Lemma lt_wf_RT : forall G G',
  ReplaceTy G G' -> forall l, lt_wf G l -> lt_wf G' l.
Proof.
  intros G G' HRT l Hwf.
  eapply lt_wf_lookup_eq; [exact Hwf|].
  intros x. apply (RT_lookup_lt G G' HRT x).
Qed.

Lemma ty_wf_RT_all :
  (forall G T, ty_wf G T -> forall G', ReplaceTy G G' -> ty_wf G' T) /\
  (forall G Ts, types_wf G Ts -> forall G', ReplaceTy G G' -> types_wf G' Ts).
Proof.
  apply (ty_wf_types_wf_mutind
    (fun G T _ => forall G', ReplaceTy G G' -> ty_wf G' T)
    (fun G Ts _ => forall G', ReplaceTy G G' -> types_wf G' Ts)).
  - intros Γ α B Hlk HwfB _ G' HRT.
    destruct (RT_lookup_ty Γ G' HRT α B Hlk HwfB) as [B' [HB' HwfB']].
    econstructor; eauto.
  - intros Γ A l B HwfA IHA Hwfl HwfB IHB G' HRT.
    constructor.
    + apply (IHA G' HRT).
    + eapply lt_wf_RT; eauto.
    + apply (IHB G' HRT).
  - intros Γ K l Ts Hwfl HwfTs IHTs G' HRT.
    constructor.
    + eapply lt_wf_RT; eauto.
    + apply (IHTs G' HRT).
  - intros Γ A HwfA IHA G' HRT.
    constructor.
    apply (IHA (bind_lt lt_local :: G')).
    apply RT_lt; [exact HRT|constructor|constructor].
  - intros Γ B A HwfB IHB HwfA IHA G' HRT.
    constructor.
    + apply (IHB G' HRT).
    + apply (IHA (bind_ty B :: G')).
      apply RT_ty.
      * exact HRT.
      * exact HwfB.
      * apply (IHB G' HRT).
  - intros Γ G' HRT. constructor.
  - intros Γ T Ts HwfT IHT HwfTs IHTs G' HRT.
    constructor.
    + apply (IHT G' HRT).
    + apply (IHTs G' HRT).
Qed.

Lemma ty_wf_RT : forall G G',
  ReplaceTy G G' -> forall T, ty_wf G T -> ty_wf G' T.
Proof.
  intros G G' HRT T Hwf.
  exact (proj1 ty_wf_RT_all G T Hwf G' HRT).
Qed.

Lemma types_wf_RT : forall G G',
  ReplaceTy G G' -> forall Ts, types_wf G Ts -> types_wf G' Ts.
Proof.
  intros G G' HRT Ts Hwf.
  exact (proj2 ty_wf_RT_all G Ts Hwf G' HRT).
Qed.

Lemma sub_NT : forall G S T, G ⊢ S <:: T ->
  forall Bsub Bsup G', NarrowTy Bsub Bsup G G' -> G' ⊢ S <:: T.
Proof.
  intros G S T H.
  induction H as [Γ T Hwf|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                 |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                 |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2];
    intros Bsub Bsup G' HN.
  - apply SA_Refl. eapply ty_wf_NT; eauto.
  - eapply SA_Trans; [apply (IH1 _ _ _ HN) | apply (IH2 _ _ _ HN)].
  - destruct (NT_lookup_sub Bsub Bsup Γ G' HN α B Hlk HwfB) as [B' [HB' [_ HsubG']]].
    destruct (sub_wf _ _ _ HsubG') as [HwfB' _].
    eapply SA_Trans; [apply SA_VarCtx; [exact HB'|exact HwfB'] | exact HsubG'].
  - apply SA_Data.
    + apply (lt_sub_NT Bsub Bsup Γ G' HN _ _ Hls).
    + eapply types_wf_NT; eauto.
  - apply SA_Any.
    + eapply ty_wf_NT; eauto.
    + eapply lt_wf_NT; eauto.
    + eapply LS_Trans.
      * apply (lt_of_ty_G_NT Bsub Bsup Γ G' HN T HwfT).
      * apply (lt_sub_NT Bsub Bsup Γ G' HN _ _ Hls).
  - apply SA_Fun.
    + apply (IH1 _ _ _ HN).
    + apply (lt_sub_NT Bsub Bsup Γ G' HN _ _ Hl).
    + apply (IH2 _ _ _ HN).
  - apply SA_LtAll.
    apply (IH1 Bsub Bsup (bind_lt lt_local :: G')).
    apply NT_lt; [exact HN|constructor|constructor].
  - destruct (sub_wf _ _ _ H1) as [HwfB' HwfB].
    pose proof (IH1 Bsub Bsup G' HN) as H1'.
    destruct (sub_wf _ _ _ H1') as [HwfB'_NT HwfB_NT].
    eapply SA_TyAll.
    + eapply ty_wf_NT; [|exact HwfA].
      apply NT_ty; [exact HN|exact HwfB|exact HwfB_NT].
    + eapply ty_wf_NT; [|exact HwfA'].
      apply NT_ty; [exact HN|exact HwfB'|exact HwfB'_NT].
    + exact H1'.
    + apply (IH2 Bsub Bsup (bind_ty B' :: G')).
      apply NT_ty; [exact HN|exact HwfB'|exact HwfB'_NT].
Qed.

Lemma sub_narrow_ty : forall Γ Bsub Bsup T1 T2,
  Γ ⊢ Bsub <:: Bsup ->
  (bind_ty Bsup :: Γ) ⊢ T1 <:: T2 ->
  (bind_ty Bsub :: Γ) ⊢ T1 <:: T2.
Proof.
  intros Γ Bsub Bsup T1 T2 Hb Hsub.
  apply (sub_NT (bind_ty Bsup :: Γ) T1 T2 Hsub Bsub Bsup (bind_ty Bsub :: Γ)).
  apply NT_here. exact Hb.
Qed.

(* Full inversion for `type_ty_all` supertypes, now a theorem: it       *)
(* recovers both the bound-subtyping witness (contravariant) and the    *)
(* body-subtyping witness (covariant, under the tighter bound).  The    *)
(* transitivity case composes the two body witnesses by narrowing the   *)
(* left one down to the common bound `B`.                               *)
Lemma sub_ty_all_inv_full : forall Γ S B T,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_ty_all B T ->
  exists B' T',
    S = type_ty_all B' T' /\
    Γ ⊢ B <:: B' /\
    (bind_ty B :: Γ) ⊢ T' <:: T.
Proof.
  intros Γ S B T Hec Hsub.
  remember (type_ty_all B T) as U eqn:HU.
  revert B T HU.
  induction Hsub; intros B0 T0 HU.
  - (* Refl *) inversion HU; subst. inversion H; subst.
    exists B0, T0. split; [reflexivity|]. split.
    + apply SA_Refl; assumption.
    + apply SA_Refl; assumption.
  - (* Trans: S <:: U0 <:: type_ty_all B0 T0 *)
    subst T.
    destruct (IHHsub2 Hec _ _ eq_refl) as [Bm [Tm [HeqU [HBm HTm]]]]; subst.
    destruct (IHHsub1 Hec _ _ eq_refl) as [B' [T' [HeqS [HB' HT']]]]; subst.
    exists B', T'. repeat split; auto.
    + eapply SA_Trans; eauto.
    + eapply SA_Trans;
        [ eapply sub_narrow_ty; [ exact HBm | exact HT' ] | exact HTm ].
  - (* VarCtx *) subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - (* Data *) discriminate HU.
  - (* Any *) discriminate HU.
  - (* Fun *) discriminate HU.
  - (* LtAll *) discriminate HU.
  - (* TyAll *) injection HU; intros; subst.
    eexists; eexists; repeat split; eauto.
Qed.

(* Replacing one stepping argument inside a well-typed constructor     *)
(* argument list preserves the per-element typing.  The per-element    *)
(* preservation comes from the `typing_ind2` IH packaged as the second *)
(* `Forall2` hypothesis below; this lemma is consumed in the T_Ctor    *)
(* case of `preservation`.                                             *)
Lemma ctor_args_preserve :
  forall Γ vsl t0 t0' tsr rho_fields,
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) (vsl ++ t0 :: tsr) rho_fields ->
  Forall2 (fun v rho => eval_ctx Γ -> forall v', v ==> v' -> Γ ⊢ₜ v' : rho)
          (vsl ++ t0 :: tsr) rho_fields ->
  eval_ctx Γ ->
  t0 ==> t0' ->
  Forall2 (fun v rho => Γ ⊢ₜ v : rho) (vsl ++ t0' :: tsr) rho_fields.
Proof.
  intros Γ vsl. induction vsl as [| a vsl' IHvsl];
    intros t0 t0' tsr rho_fields HF HFP Hec Hstep; simpl in *.
  - apply f2_uncons_l in HF.
    destruct HF as [rho0 [rest [Erf [Hhd Htl]]]]. subst rho_fields.
    apply f2_uncons_l in HFP.
    destruct HFP as [rho0' [rest' [Erf' [HPhd HPtl]]]].
    injection Erf'; intros; subst rho0' rest'.
    constructor.
    + apply HPhd; assumption.
    + exact Htl.
  - apply f2_uncons_l in HF.
    destruct HF as [rho0 [rest [Erf [Hhd Htl]]]]. subst rho_fields.
    apply f2_uncons_l in HFP.
    destruct HFP as [rho0' [rest' [Erf' [HPhd HPtl]]]].
    injection Erf'; intros; subst rho0' rest'.
    constructor.
    + exact Hhd.
    + eapply IHvsl with (t0 := t0); eassumption.
Qed.

