Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import TypingInv.
Require Import Markers.

(* The third disjunct of the open-scope progress result: [t] is a      *)
(* perform of a live capability whose matching delimiter lies OUTSIDE  *)
(* [t] (its marker is only promised to be in the ambient scope [ms]).  *)
(* This is what makes the induction go through under a delimiter: the  *)
(* T_HandlerM case either catches the escape (same marker — then       *)
(* H_Perform fires, using [marker_types_safe] to reconcile the         *)
(* delimiter's and the capability's answer-type annotations) or        *)
(* forwards it one scope out.  At the closed top level ([ms] = []),    *)
(* the escape disjunct is vacuous, giving the classical progress.      *)
Definition perform_escape (ms : list marker) (t : term) : Prop :=
  exists E_tag m n_beta Ts T_R op_body Ss A v P,
    In m ms /\ pure_ectx_m m P /\ value v /\
    t = plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss A v).

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
  well_scoped ms t ->
  marker_types_safe t ->
  Γ ⊢ₜ t : T ->
  progress_result ms t.
Proof.
  intros Γ0 ms0 t0 T0 Hec0 Hmok0 Hsafe0 Hty0. revert ms0 Hmok0 Hsafe0 Hec0.
  revert Hty0; revert T0; revert t0; revert Γ0.
  apply (typing_ind2 (fun Γ t T => forall ms,
    well_scoped ms t -> marker_types_safe t -> eval_ctx Γ -> progress_result ms t)).
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
        * destruct (canonical_fun _ _ _ _ _ Hec Ht1 Hv1) as [body [T0 Heq]]; subst.
          right. left. eexists. apply S_Beta; auto.
      * destruct (S_App2 t1 t2 Hv1 (ex_intro _ t2' Hs2)) as [u Hu].
        right. left. exists u. exact Hu.
      * destruct Hesc2 as (Et & m & nb & Ts0 & T_R & ob & Ss & A0 & v & P & Hin & Hp & Hv & Heq); subst.
        right. right. exists Et, m, nb, Ts0, T_R, ob, Ss, A0, v, (EC_app2 t1 P).
        repeat split; auto.
    + destruct (S_App1 t1 t2 (ex_intro _ t1' Hs1)) as [u Hu].
      right. left. exists u. exact Hu.
    + destruct Hesc1 as (Et & m & nb & Ts0 & T_R & ob & Ss & A0 & v & P & Hin & Hp & Hv & Heq); subst.
      right. right. exists Et, m, nb, Ts0, T_R, ob, Ss, A0, v, (EC_app1 P t2).
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
    + destruct Hesc as (Et & m & nb & Ts0 & T_R & ob & Ss & A0 & v & P & Hin & Hp & Hv & Heq); subst.
      right. right. exists Et, m, nb, Ts0, T_R, ob, Ss, A0, v, (EC_ty_app P S).
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
    + destruct Hesc as (Et & m & nb & Ts0 & T_R & ob & Ss & A0 & v & P & Hin & Hp & Hv & Heq); subst.
      right. right. exists Et, m, nb, Ts0, T_R, ob, Ss, A0, v, (EC_lt_app P l).
      repeat split; auto.
  - (* T_Ctor *)
    intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
      result_ty result_tag l vs
      Hlk Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs Hresult Hshape Hresult_eff Hwfl Hlt Hlen_vs
      HF HFP HargsIH ms Hmok Hsafe Hec.
    assert (Hmok_vs : Forall (well_scoped ms) vs).
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
    + destruct Hesc as (Et & m & nb & Ts0 & T_R & ob & Ss & A0 & v & P & Hin & Hp & Hv & Heqesc).
      subst vs tm.
      right. right. exists Et, m, nb, Ts0, T_R, ob, Ss, A0, v, (EC_ctor K l lts Ts vsl P vsr).
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
    + destruct Hesc as (Et & m & nb & Ts0 & T_R & ob & Ss & A0 & v & P & Hin & Hp & Hv & Heq).
      subst scrut.
      right. right. exists Et, m, nb, Ts0, T_R, ob, Ss, A0, v, (EC_match P K n_lt arity yes_body no_body).
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
    specialize (IHrecv ms Hmok_recv (marker_types_safe_perform_recv _ _ _ _ Hsafe) Hec).
    destruct IHrecv as [Hvrecv | [[recv' Hsrecv] | Hescrecv]].
    + specialize (IHarg ms Hmok_arg (marker_types_safe_perform_arg _ _ _ _ Hsafe) Hec).
      destruct IHarg as [Hvarg | [[arg' Hsarg] | Hescarg]].
      * destruct (canonical_cap Γ recv E_tag Δ Ts n_α n_β sig ret Hec Heff Hrecv Hvrecv)
          as [m [T_R [op_body Heqcap]]].
        subst recv. simpl in Hmok_recv. destruct Hmok_recv as [Hin Hop_ok].
        right. right. exists E_tag, m, n_β, Ts, T_R, op_body, Ss, ret_inst, arg, EC_hole.
        repeat split; auto.
      * destruct (S_PerformArg recv Ss ret_inst arg Hvrecv (ex_intro _ arg' Hsarg)) as [u Hu].
        right. left. exists u. exact Hu.
      * destruct Hescarg as (Et & m & nb & Ts0 & T_R & ob & Ss0 & A0 & v & P & Hin & Hp & Hv & Heq); subst arg.
        right. right. exists Et, m, nb, Ts0, T_R, ob, Ss0, A0, v, (EC_perform_a recv Ss ret_inst P).
        repeat split; auto.
    + destruct (S_PerformRecv recv Ss ret_inst arg (ex_intro _ recv' Hsrecv)) as [u Hu].
      right. left. exists u. exact Hu.
    + destruct Hescrecv as (Et & m & nb & Ts0 & T_R & ob & Ss0 & A0 & v & P & Hin & Hp & Hv & Heq); subst recv.
      right. right. exists Et, m, nb, Ts0, T_R, ob, Ss0, A0, v, (EC_perform_r P Ss ret_inst arg).
      repeat split; auto.
  - (* T_HandlerM *)
    intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH ms Hmok Hsafe Hec.
    simpl in Hmok.
    specialize (IH (m :: ms) Hmok (marker_types_safe_handler_body _ _ _ _ Hsafe) Hec).
    destruct IH as [Hv | [[t' Hs] | Hesc]].
    + right. left. exists t. apply S_Return; auto.
    + destruct (S_HandlerM m T_B T_R t (ex_intro _ t' Hs)) as [u Hu].
      right. left. exists u. exact Hu.
    + destruct Hesc as (Et & m0 & nb & Ts & T_R0 & op_body & Ss & A0 & v & P & Hin & Hp & Hv & Heq); subst.
      destruct (Nat.eq_dec m0 m) as [Heqm | Hneq].
      * subst m0. right. left. eexists.
        pose proof (marker_types_ok_handler_perform_annotation_match
                      m T_B T_R Et nb Ts T_R0 op_body Ss A0 v P Hsafe) as HTR.
        subst T_R0.
        apply (S_step EC_hole); [constructor|]. apply H_Perform; auto.
      * destruct Hin as [Hin_head | Hin_tail].
        { subst. contradiction. }
        right. right. exists Et, m0, nb, Ts, T_R0, op_body, Ss, A0, v, (EC_handler_m m T_B T_R P).
        repeat split; auto.
Qed.

Theorem progress_safe : forall Γ t T,
  eval_ctx Γ ->
  well_scoped [] t ->
  marker_types_safe t ->
  Γ ⊢ₜ t : T ->
  value t \/ exists t', t ==> t'.
Proof.
  intros Γ t T Hec Hmok Hsafe Hty.
  destruct (progress_open_safe _ _ _ _ Hec Hmok Hsafe Hty) as [Hv | [[t' Hs] | Hesc]].
  - left. exact Hv.
  - right. exists t'. exact Hs.
  - destruct Hesc as (Et & m & nb & Ts & T_R & op_body & Ss & A0 & v & P & Hin & Hp & Hv & Heq).
    inversion Hin.
Qed.

Theorem progress : forall Γ t T,
  eval_ctx Γ ->
  well_scoped [] t ->
  marker_types_safe t ->
  Γ ⊢ₜ t : T ->
  value t \/ exists t', t ==> t'.
Proof.
  intros Γ t T Hec Hmok Hsafe Hty.
  eapply progress_safe; eauto.
Qed.
