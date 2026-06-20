Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.

Require Import Typing.
Require Import Subst.

(* ------------------------------------------------------------------ *)
(* Effect-handler invariant                                           *)
(*                                                                    *)
(* Under an `eval_ctx` (no `bind_eff` entries), `T_Cap` cannot fire,  *)
(* so a well-typed term cannot be a perform of a typed capability.    *)
(* We prove this structurally:                                        *)
(*                                                                    *)
(*   1. A well-typed `term_cap E …` forces `ctx_lookup_eff Γ E` to be *)
(*      `Some …` (recorded by `T_Cap`; `T_Sub` is term-preserving).   *)
(*   2. Every evaluation-context constructor (`ectx`) types its hole  *)
(*      sub-term in the *same* context `Γ` — none introduce binders — *)
(*      so `Γ ⊢ₜ plug P u : T` yields a typing of `u` under `Γ`.      *)
(*   3. Inverting the `term_perform`/`term_cap` typing then collides  *)
(*      with `eval_ctx_no_eff`, giving the contradiction.             *)
(* ------------------------------------------------------------------ *)

(* From a `Forall2` typing premise, recover per-element typability. *)
Lemma Forall2_Forall_exists :
  forall (A B : Type) (R : A -> B -> Prop) xs ys,
    Forall2 R xs ys ->
    Forall (fun x => exists y, R x y) xs.
Proof.
  induction 1; constructor; eauto.
Qed.

(* A well-typed capability value forces its effect tag to be in Γ.    *)
Lemma cap_typed_eff_some : forall Γ E_tag m n_beta Ts T_R op_body T,
  Γ ⊢ₜ term_cap E_tag m n_beta Ts T_R op_body : T ->
  exists n_α n_β sig0 ret, ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig0, ret).
Proof.
  intros Γ E_tag m n_beta Ts T_R op_body T H.
  remember (term_cap E_tag m n_beta Ts T_R op_body) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - (* T_Sub *) apply IHtyping; exact Hs.
  - (* T_Cap *) injection Hs; intros; subst. eauto.
Qed.

(* Subsumption-stripping inversions: each gives a typing of the      *)
(* hole-bearing sub-term in the same context Γ.                      *)

Lemma typed_app_inv : forall Γ f x T,
  Γ ⊢ₜ term_app f x : T ->
  exists A l B, Γ ⊢ₜ f : type_fun A l B /\ Γ ⊢ₜ x : A.
Proof.
  intros Γ f x T H.
  remember (term_app f x) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - apply IHtyping; exact Hs.
  - injection Hs; intros; subst. exists A, l, B; split; assumption.
Qed.

Lemma typed_ty_app_inv : forall Γ t S T,
  Γ ⊢ₜ term_ty_app t S : T -> exists T0, Γ ⊢ₜ t : T0.
Proof.
  intros Γ t S T H.
  remember (term_ty_app t S) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - apply IHtyping; exact Hs.
  - injection Hs; intros; subst. eexists; eassumption.
Qed.

Lemma typed_lt_app_inv : forall Γ t l T,
  Γ ⊢ₜ term_lt_app t l : T -> exists T0, Γ ⊢ₜ t : T0.
Proof.
  intros Γ t l T H.
  remember (term_lt_app t l) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - apply IHtyping; exact Hs.
  - injection Hs; intros; subst. eexists; eassumption.
Qed.

Lemma typed_match_inv : forall Γ scrut K n_lt arity yes no T,
  Γ ⊢ₜ term_match scrut K n_lt arity yes no : T -> exists T0, Γ ⊢ₜ scrut : T0.
Proof.
  intros Γ scrut K n_lt arity yes no T H.
  remember (term_match scrut K n_lt arity yes no) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - apply IHtyping; exact Hs.
  - injection Hs; intros; subst. eexists; eassumption.
Qed.

Lemma typed_handler_m_inv : forall Γ m T_B T_R t T,
  Γ ⊢ₜ term_handler_m m T_B T_R t : T -> exists T0, Γ ⊢ₜ t : T0.
Proof.
  intros Γ m T_B T_R t T H.
  remember (term_handler_m m T_B T_R t) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - apply IHtyping; exact Hs.
  - injection Hs; intros; subst. eexists; eassumption.
Qed.

Lemma typed_perform_inv : forall Γ recv Ss arg T,
  Γ ⊢ₜ term_perform recv Ss arg : T ->
  exists Tr Ta, Γ ⊢ₜ recv : Tr /\ Γ ⊢ₜ arg : Ta.
Proof.
  intros Γ recv Ss arg T H.
  remember (term_perform recv Ss arg) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - apply IHtyping; exact Hs.
  - injection Hs; intros; subst. eexists; eexists; split; eassumption.
Qed.

Lemma typed_ctor_inv : forall Γ K l lts Ts args T,
  Γ ⊢ₜ term_ctor K l lts Ts args : T ->
  Forall (fun a => exists rho, Γ ⊢ₜ a : rho) args.
Proof.
  intros Γ K l lts Ts args T H.
  remember (term_ctor K l lts Ts args) as s eqn:Hs.
  revert Hs. induction H; intros Hs; try discriminate Hs.
  - (* T_Sub *) apply IHtyping; exact Hs.
  - (* T_Ctor *) injection Hs; intros; subst.
    match goal with
    | Hf : Forall2 _ _ _ |- _ =>
        exact (Forall2_Forall_exists _ _ _ _ _ Hf)
    end.
Qed.

Lemma handle_typing_inv_for_markers : forall Γ E_tag n_beta Ts T_B T_R op_body body T,
  Γ ⊢ₜ term_handle E_tag n_beta Ts T_B T_R op_body body : T ->
  exists n_α sig ret sig_β ret_β,
    ctx_lookup_eff Γ E_tag = Some (n_α, n_beta, sig, ret) /\
    List.length Ts = n_α /\ types_wf Γ Ts /\
    ty_wf Γ T_B /\ ty_wf Γ T_R /\ Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free /\ Γ ⊢ T_B <:: T_R /\
    sig_β = inst_op_alpha n_α Ts n_beta sig /\
    ret_β = inst_op_alpha n_α Ts n_beta ret /\
    (bind_tm sig_β
      :: bind_tm (type_fun ret_β lt_local (shift_ty n_beta 0 T_R))
      :: push_ty_vars n_beta any_at_free Γ)
      ⊢ₜ op_body : shift_ty n_beta 0 T_R /\
    (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) ⊢ₜ body : T_B /\
    Γ ⊢ T_R <:: T.
Proof.
  intros Γ E_tag n_beta Ts T_B T_R op_body body T H.
  remember (term_handle E_tag n_beta Ts T_B T_R op_body body) as s eqn:Hs.
  induction H; try discriminate Hs.
  - destruct (IHtyping Hs) as
      (n_α & sig & ret & sig_β & ret_β & Heff & HlenTs & HwfTs & HwfTB & HwfTR
       & Hnl & Hbr & Hsigβ & Hretβ & Hop & Hbody & Hsub).
    exists n_α, sig, ret, sig_β, ret_β.
    repeat (split; [assumption|]). eapply SA_Trans; eassumption.
  - injection Hs; intros; subst.
    do 5 eexists.
    repeat split; try eassumption; try reflexivity.
    apply SA_Refl. assumption.
Qed.

(* Typing of `plug P u` yields a typing of the plugged sub-term `u`   *)
(* under the same context: evaluation contexts add no binders.        *)
Lemma plug_typing_inv : forall P Γ u T,
  Γ ⊢ₜ plug P u : T -> exists T', Γ ⊢ₜ u : T'.
Proof.
  induction P; intros Γ u T H; simpl in H.
  - (* EC_hole *) exists T; exact H.
  - (* EC_app1 *)
    apply typed_app_inv in H. destruct H as [A [l [B [Hf _]]]].
    eapply IHP; exact Hf.
  - (* EC_app2 *)
    apply typed_app_inv in H. destruct H as [A [l [B [_ Hx]]]].
    eapply IHP; exact Hx.
  - (* EC_ty_app *)
    apply typed_ty_app_inv in H. destruct H as [T0 Ht].
    eapply IHP; exact Ht.
  - (* EC_lt_app *)
    apply typed_lt_app_inv in H. destruct H as [T0 Ht].
    eapply IHP; exact Ht.
  - (* EC_ctor *)
    apply typed_ctor_inv in H.
    rewrite Forall_app in H. destruct H as [_ H].
    apply Forall_inv in H. destruct H as [rho Hrho].
    eapply IHP; exact Hrho.
  - (* EC_match *)
    apply typed_match_inv in H. destruct H as [T0 Ht].
    eapply IHP; exact Ht.
  - (* EC_handler_m *)
    apply typed_handler_m_inv in H. destruct H as [T0 Ht].
    eapply IHP; exact Ht.
  - (* EC_perform_r *)
    apply typed_perform_inv in H. destruct H as [Tr [Ta [Hr _]]].
    eapply IHP; exact Hr.
  - (* EC_perform_a *)
    apply typed_perform_inv in H. destruct H as [Tr [Ta [_ Ha]]].
    eapply IHP; exact Ha.
Qed.

Lemma handle_result_closed_from_plug_typing_for_markers :
  forall Γ E E_tag n_beta Ts T_B T_R op_body body T,
    eval_ctx Γ ->
    Γ ⊢ₜ plug E (term_handle E_tag n_beta Ts T_B T_R op_body body) : T ->
    ty_ty_closed 0 T_R /\ ty_lt_closed 0 T_R.
Proof.
  intros Γ E E_tag n_beta Ts T_B T_R op_body body T Hec Hty.
  destruct (plug_typing_inv E Γ (term_handle E_tag n_beta Ts T_B T_R op_body body) T Hty)
    as [Th Hhandle].
  apply handle_typing_inv_for_markers in Hhandle.
  destruct Hhandle as
    (n_α & sig & ret & sig_β & ret_β & Heff & HlenTs & HwfTs & HwfTB & HwfTR
     & Hnl & Hbr & Hsigβ & Hretβ & Hop & Hbody & Hsub).
  split.
  - eapply ty_wf_eval_ctx_ty_closed; eauto.
  - eapply ty_wf_eval_ctx_lt_closed; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Subtyping shape inversion under eval_ctx.                          *)
(* ------------------------------------------------------------------ *)

Lemma sub_fun_inv : forall Γ S A l B,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_fun A l B ->
  exists A' l' B',
    S = type_fun A' l' B' /\
    Γ ⊢ A <:: A' /\
    Γ ⊢ₗ l' <: l /\
    Γ ⊢ B' <:: B.
Proof.
  intros Γ S A l B Hec Hsub.
  remember (type_fun A l B) as T eqn:HT.
  revert A l B HT.
  induction Hsub; intros A0 l0 B0 HT.
  - (* Refl *) inversion HT; subst. inversion H; subst.
    exists A0, l0, B0. repeat split;
      try (apply SA_Refl; assumption);
      try (apply LS_Refl; assumption).
  - (* Trans *) subst T.
    destruct (IHHsub2 Hec _ _ _ eq_refl) as [A1 [l1 [B1 [HeqU [HAa [Hla HBa]]]]]]; subst.
    destruct (IHHsub1 Hec _ _ _ eq_refl) as [A2 [l2 [B2 [HeqS [HAb [Hlb HBb]]]]]]; subst.
    exists A2, l2, B2. repeat split; eauto.
  - (* VarCtx *) subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - (* Data *) discriminate HT.
  - (* Any *) discriminate HT.
  - (* Fun *) injection HT; intros HB0 Hl0 HA0; subst.
    exists A', l, B; repeat split; auto.
  - (* LtAll *) discriminate HT.
  - (* TyAll *) discriminate HT.
Qed.

Lemma sub_ctor_inv : forall Γ S K l Ts,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_ctor K l Ts ->
  K <> any_tag ->
  exists l', S = type_ctor K l' Ts /\ Γ ⊢ₗ l' <: l.
Proof.
  intros Γ S K l Ts Hec Hsub HK.
  remember (type_ctor K l Ts) as T eqn:HT.
  revert K l Ts HT HK.
  induction Hsub; intros K0 l0 Ts0 HT HK.
  - (* Refl *) inversion HT; subst. inversion H; subst.
    exists l0; split; [reflexivity|apply LS_Refl; assumption].
  - (* Trans *) subst T.
    destruct (IHHsub2 Hec _ _ _ eq_refl HK) as [l'' [HeqU Hl2]]; subst.
    destruct (IHHsub1 Hec _ _ _ eq_refl HK) as [l''' [HeqS Hl1]]; subst.
    exists l'''; split; eauto.
  - (* VarCtx *) subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - (* Data *) injection HT; intros; subst. exists l; split; auto.
  - (* Any *) injection HT; intros; subst. contradiction.
  - (* Fun *) discriminate HT.
  - (* LtAll *) discriminate HT.
  - (* TyAll *) discriminate HT.
Qed.

Lemma sub_lt_all_inv : forall Γ S T,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_lt_all T ->
  exists T', S = type_lt_all T'.
Proof.
  intros Γ S T Hec Hsub.
  remember (type_lt_all T) as U eqn:HU.
  revert T HU.
  induction Hsub; intros T0 HU.
  - (* Refl *) inversion HU; subst. eauto.
  - (* Trans *) subst T.
    destruct (IHHsub2 Hec _ eq_refl) as [T' HeqU]; subst.
    destruct (IHHsub1 Hec _ eq_refl) as [T'' HeqS]; subst. eauto.
  - (* VarCtx *) subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - (* Data *) discriminate HU.
  - (* Any *) discriminate HU.
  - (* Fun *) discriminate HU.
  - (* LtAll *) injection HU; intros; subst. eauto.
  - (* TyAll *) discriminate HU.
Qed.

Lemma sub_ty_all_inv : forall Γ S B T,
  eval_ctx Γ ->
  Γ ⊢ S <:: type_ty_all B T ->
  exists B' T', S = type_ty_all B' T'.
Proof.
  intros Γ S B T Hec Hsub.
  remember (type_ty_all B T) as U eqn:HU.
  revert B T HU.
  induction Hsub; intros B0 T0 HU.
  - (* Refl *) inversion HU; subst. eauto.
  - (* Trans *) subst T.
    destruct (IHHsub2 Hec _ _ eq_refl) as [B' [T' HeqU]]; subst.
    destruct (IHHsub1 Hec _ _ eq_refl) as [B'' [T'' HeqS]]; subst. eauto.
  - (* VarCtx *) subst. rewrite eval_ctx_no_ty in H; auto; discriminate.
  - (* Data *) discriminate HU.
  - (* Any *) discriminate HU.
  - (* Fun *) discriminate HU.
  - (* LtAll *) discriminate HU.
  - (* TyAll *) injection HU; intros; subst. eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Canonical forms                                                    *)
(* ------------------------------------------------------------------ *)

Lemma canonical_fun : forall Γ v A l B,
  eval_ctx Γ ->
  Γ ⊢ₜ v : type_fun A l B ->
  value v ->
  (exists body T, v = term_lam body T)
  \/ (exists m T_B T_R b, v = term_resume m T_B T_R b).
Proof.
  intros Γ v A l B Hec Hty Hval.
  remember (type_fun A l B) as T0 eqn:HT.
  revert A l B HT.
  induction Hty; intros A0 l0 B0 HT; subst;
    try (inversion Hval; fail);
    try discriminate HT.
  - (* T_Sub *)
    destruct (sub_fun_inv _ _ _ _ _ Hec H) as [A' [l' [B' [HeqT _]]]]; subst.
    eapply IHHty; eauto.
  - (* T_Lam *) left; eauto.
  - (* T_Ctor *)
    match goal with
    | H1 : ?R = type_ctor _ _ _, H2 : ?R = type_fun _ _ _ |- _ => rewrite H1 in H2; discriminate H2
    | H1 : ?R = type_ctor _ _ _, H2 : type_fun _ _ _ = ?R |- _ => rewrite H1 in H2; discriminate H2
    | H1 : type_ctor _ _ _ = ?R, H2 : ?R = type_fun _ _ _ |- _ => rewrite <- H1 in H2; discriminate H2
    | H1 : type_ctor _ _ _ = ?R, H2 : type_fun _ _ _ = ?R |- _ => rewrite <- H1 in H2; discriminate H2
    | H : type_fun _ _ _ = type_ctor _ _ _ |- _ => discriminate H
    | H : type_ctor _ _ _ = type_fun _ _ _ |- _ => discriminate H
    end.
  - (* T_Resume *) right; eauto.
Qed.

Fixpoint marker_ok (ms : list marker) (t : term) : Prop :=
  let fix marker_ok_list (ts : list term) : Prop :=
    match ts with
    | [] => True
    | u :: rest => marker_ok ms u /\ marker_ok_list rest
    end
  in
  match t with
  | term_var _ => True
  | term_app t1 t2 => marker_ok ms t1 /\ marker_ok ms t2
  | term_lam body _ => marker_ok ms body
  | term_ty_app t1 _ => marker_ok ms t1
  | term_ty_lam _ body => marker_ok ms body
  | term_lt_app t1 _ => marker_ok ms t1
  | term_lt_lam body => marker_ok ms body
  | term_ctor _ _ _ _ ts => marker_ok_list ts
  | term_match scrut _ _ _ yes_body no_body =>
      marker_ok ms scrut /\ marker_ok ms yes_body /\ marker_ok ms no_body
  | term_handle _ _ _ _ _ op_body body => marker_ok ms op_body /\ marker_ok ms body
  | term_perform recv _ arg => marker_ok ms recv /\ marker_ok ms arg
  | term_cap _ m _ _ _ op_body => In m ms /\ marker_ok (m :: ms) op_body
  | term_handler_m m _ _ body => marker_ok (m :: ms) body
  | term_resume m _ _ body => marker_ok (m :: ms) body
  end.

Fixpoint marker_annots (t : term) : list (marker * type) :=
  match t with
  | term_var _ => []
  | term_app t1 t2 => marker_annots t1 ++ marker_annots t2
  | term_lam body _ => marker_annots body
  | term_ty_app t1 _ => marker_annots t1
  | term_ty_lam _ body => marker_annots body
  | term_lt_app t1 _ => marker_annots t1
  | term_lt_lam body => marker_annots body
  | term_ctor _ _ _ _ ts => List.concat (List.map marker_annots ts)
  | term_match scrut _ _ _ yes_body no_body =>
      marker_annots scrut ++ marker_annots yes_body ++ marker_annots no_body
  | term_handle _ _ _ _ _ op_body body =>
      marker_annots op_body ++ marker_annots body
  | term_perform recv _ arg => marker_annots recv ++ marker_annots arg
  | term_cap _ m _ _ T_R op_body => (m, T_R) :: marker_annots op_body
  | term_handler_m m _ T_R body => (m, T_R) :: marker_annots body
  | term_resume m _ T_R body => (m, T_R) :: marker_annots body
  end.

Definition marker_types_ok (t : term) : Prop :=
  forall m T U,
    In (m, T) (marker_annots t) ->
    In (m, U) (marker_annots t) ->
    T = U.

Definition marker_annots_no_local (t : term) : Prop :=
  Forall (fun mt => no_local_ty (snd mt) = true) (marker_annots t).

Definition marker_annots_list_no_local (ts : list term) : Prop :=
  Forall (fun mt => no_local_ty (snd mt) = true)
         (List.concat (List.map marker_annots ts)).

Definition marker_annots_closed (t : term) : Prop :=
  Forall (fun mt => ty_ty_closed 0 (snd mt) /\ ty_lt_closed 0 (snd mt))
         (marker_annots t).

Definition marker_annots_list_closed (ts : list term) : Prop :=
  Forall (fun mt => ty_ty_closed 0 (snd mt) /\ ty_lt_closed 0 (snd mt))
         (List.concat (List.map marker_annots ts)).

Definition marker_types_safe (t : term) : Prop :=
  marker_types_ok t.

Lemma marker_types_safe_ok : forall t,
  marker_types_safe t -> marker_types_ok t.
Proof.
  intros t H. exact H.
Qed.

Lemma marker_types_safe_empty : forall t,
  marker_annots t = [] -> marker_types_safe t.
Proof.
  intros t Hann m T U Hin. rewrite Hann in Hin. inversion Hin.
Qed.

Lemma marker_annots_no_rt_cap : forall t,
  has_rt_cap t = false -> marker_annots t = [].
Proof.
  apply (term_list_ind
    (fun t => has_rt_cap t = false -> marker_annots t = [])
    (fun ts =>
       (fix go (ts : list term) : bool :=
          match ts with
          | [] => false
          | u :: rest => orb (has_rt_cap u) (go rest)
          end) ts = false ->
       List.concat (List.map marker_annots ts) = [])).
  - intros n H. reflexivity.
  - intros t1 t2 IH1 IH2 H. simpl in *.
    apply Bool.orb_false_iff in H as [H1 H2].
    rewrite (IH1 H1), (IH2 H2). reflexivity.
  - intros body T IH H. simpl in *. apply IH. exact H.
  - intros t T IH H. simpl in *. apply IH. exact H.
  - intros bound body IH H. simpl in *. apply IH. exact H.
  - intros t l IH H. simpl in *. apply IH. exact H.
  - intros body IH H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH H. simpl in *. apply IH. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn H. simpl in *.
    apply Bool.orb_false_iff in H as [Hs Hyn].
    apply Bool.orb_false_iff in Hyn as [Hy Hn].
    rewrite (IHs Hs), (IHy Hy), (IHn Hn). reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody H. simpl in *.
    apply Bool.orb_false_iff in H as [Hop Hbody].
    rewrite (IHop Hop), (IHbody Hbody). reflexivity.
  - intros recv Ss arg IHrecv IHarg H. simpl in *.
    apply Bool.orb_false_iff in H as [Hr Ha].
    rewrite (IHrecv Hr), (IHarg Ha). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop H. simpl in H. discriminate.
  - intros m T_B T_R body IH H. simpl in H. discriminate.
  - intros m T_B T_R body IH H. simpl in H. discriminate.
  - intros H. reflexivity.
  - intros t ts IHt IHts H. simpl in *.
    apply Bool.orb_false_iff in H as [Ht Hts].
    rewrite (IHt Ht), (IHts Hts). reflexivity.
Qed.

Lemma marker_annots_closed_no_rt_cap : forall t,
  has_rt_cap t = false -> marker_annots_closed t.
Proof.
  intros t Hcap. unfold marker_annots_closed.
  rewrite (marker_annots_no_rt_cap t Hcap). constructor.
Qed.

Lemma marker_types_safe_no_rt_cap : forall t,
  has_rt_cap t = false -> marker_types_safe t.
Proof.
  intros t Hcap. apply marker_types_safe_empty.
  apply marker_annots_no_rt_cap. exact Hcap.
Qed.

Lemma marker_ok_no_rt_cap : forall t ms,
  has_rt_cap t = false -> marker_ok ms t.
Proof.
  apply (term_list_ind
    (fun t => forall ms, has_rt_cap t = false -> marker_ok ms t)
    (fun ts => forall ms,
       (fix go (ts : list term) : bool :=
          match ts with
          | [] => false
          | u :: rest => orb (has_rt_cap u) (go rest)
          end) ts = false ->
       (fix marker_ok_list (ts : list term) : Prop :=
          match ts with
          | [] => True
          | u :: rest => marker_ok ms u /\ marker_ok_list rest
          end) ts)).
  - intros n ms H. exact I.
  - intros t1 t2 IH1 IH2 ms H. simpl in *.
    apply Bool.orb_false_iff in H as [H1 H2]. split; [apply IH1 | apply IH2]; assumption.
  - intros body T IH ms H. simpl in *. apply IH. exact H.
  - intros t T IH ms H. simpl in *. apply IH. exact H.
  - intros bound body IH ms H. simpl in *. apply IH. exact H.
  - intros t l IH ms H. simpl in *. apply IH. exact H.
  - intros body IH ms H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH ms H. simpl in *. apply IH. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn ms H. simpl in *.
    apply Bool.orb_false_iff in H as [Hs Hyn].
    apply Bool.orb_false_iff in Hyn as [Hy Hn].
    repeat split; [apply IHs | apply IHy | apply IHn]; assumption.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody ms H. simpl in *.
    apply Bool.orb_false_iff in H as [Hop Hbody]. split; [apply IHop | apply IHbody]; assumption.
  - intros recv Ss arg IHrecv IHarg ms H. simpl in *.
    apply Bool.orb_false_iff in H as [Hr Ha]. split; [apply IHrecv | apply IHarg]; assumption.
  - intros E m n_beta Ts T_R op_body IHop ms H. simpl in H. discriminate.
  - intros m T_B T_R body IH ms H. simpl in H. discriminate.
  - intros m T_B T_R body IH ms H. simpl in H. discriminate.
  - intros ms H. exact I.
  - intros t ts IHt IHts ms H. simpl in *.
    apply Bool.orb_false_iff in H as [Ht Hts]. split; [apply IHt | apply IHts]; assumption.
Qed.

Lemma marker_types_safe_incl : forall sub whole,
  incl (marker_annots sub) (marker_annots whole) ->
  marker_types_safe whole ->
  marker_types_safe sub.
Proof.
  intros sub whole Hincl Hok m T U HT HU.
  eapply Hok; [apply Hincl | apply Hincl]; eauto.
Qed.

Lemma marker_types_safe_app_l : forall t1 t2,
  marker_types_safe (term_app t1 t2) -> marker_types_safe t1.
Proof.
  intros t1 t2 Hsafe. eapply marker_types_safe_incl; [|exact Hsafe].
  intros p Hp. simpl. apply List.in_or_app. left. exact Hp.
Qed.

Lemma marker_types_safe_app_r : forall t1 t2,
  marker_types_safe (term_app t1 t2) -> marker_types_safe t2.
Proof.
  intros t1 t2 Hsafe. eapply marker_types_safe_incl; [|exact Hsafe].
  intros p Hp. simpl. apply List.in_or_app. right. exact Hp.
Qed.

Lemma marker_types_safe_match_scrut : forall scrut K n_lt arity yes no,
  marker_types_safe (term_match scrut K n_lt arity yes no) -> marker_types_safe scrut.
Proof.
  intros scrut K n_lt arity yes no Hsafe. eapply marker_types_safe_incl; [|exact Hsafe].
  intros p Hp. simpl. apply List.in_or_app. left. exact Hp.
Qed.

Lemma marker_types_safe_match_yes : forall scrut K n_lt arity yes no,
  marker_types_safe (term_match scrut K n_lt arity yes no) -> marker_types_safe yes.
Proof.
  intros scrut K n_lt arity yes no Hsafe. eapply marker_types_safe_incl; [|exact Hsafe].
  intros p Hp. simpl. apply List.in_or_app. right. apply List.in_or_app. left. exact Hp.
Qed.

Lemma marker_types_safe_match_no : forall scrut K n_lt arity yes no,
  marker_types_safe (term_match scrut K n_lt arity yes no) -> marker_types_safe no.
Proof.
  intros scrut K n_lt arity yes no Hsafe. eapply marker_types_safe_incl; [|exact Hsafe].
  intros p Hp. simpl. apply List.in_or_app. right. apply List.in_or_app. right. exact Hp.
Qed.

Lemma marker_types_safe_perform_recv : forall recv Ss arg,
  marker_types_safe (term_perform recv Ss arg) -> marker_types_safe recv.
Proof.
  intros recv Ss arg Hsafe. eapply marker_types_safe_incl; [|exact Hsafe].
  intros p Hp. simpl. apply List.in_or_app. left. exact Hp.
Qed.

Lemma marker_types_safe_perform_arg : forall recv Ss arg,
  marker_types_safe (term_perform recv Ss arg) -> marker_types_safe arg.
Proof.
  intros recv Ss arg Hsafe. eapply marker_types_safe_incl; [|exact Hsafe].
  intros p Hp. simpl. apply List.in_or_app. right. exact Hp.
Qed.

Lemma marker_types_safe_handler_body : forall m T_B T_R body,
  marker_types_safe (term_handler_m m T_B T_R body) -> marker_types_safe body.
Proof.
  intros m T_B T_R body Hsafe. eapply marker_types_safe_incl; [|exact Hsafe].
  intros p Hp. simpl. right. exact Hp.
Qed.

Lemma marker_types_safe_ctor_args : forall K l lts Ts vs,
  marker_types_safe (term_ctor K l lts Ts vs) ->
  Forall marker_types_safe vs.
Proof.
  intros K l lts Ts vs. induction vs as [|v rest IH]; intros Hsafe; constructor.
  - eapply marker_types_safe_incl; [|exact Hsafe].
    intros p Hp. simpl. apply List.in_or_app. left. exact Hp.
  - apply IH. eapply marker_types_safe_incl; [|exact Hsafe].
    intros p Hp. simpl. apply List.in_or_app. right. exact Hp.
Qed.

Lemma marker_annots_list_no_local_cons : forall t ts,
  marker_annots_no_local t ->
  marker_annots_list_no_local ts ->
  marker_annots_list_no_local (t :: ts).
Proof.
  intros t ts Ht Hts.
  unfold marker_annots_no_local, marker_annots_list_no_local in *.
  simpl. apply Forall_app. split; assumption.
Qed.

Lemma no_local_ty_shift_ty_any : forall amount T c,
  no_local_ty (shift_ty amount c T) = no_local_ty T.
Proof.
  intros amount.
  apply (type_list_ind
    (fun T => forall c, no_local_ty (shift_ty amount c T) = no_local_ty T)
    (fun Ts => forall c,
       fold_right (fun A acc => andb (no_local_ty A) acc) true
         (List.map (shift_ty amount c) Ts) =
       fold_right (fun A acc => andb (no_local_ty A) acc) true Ts)).
  - intros n c. simpl. destruct (Nat.leb c n); reflexivity.
  - intros A l B IHA IHB c. simpl. rewrite IHA, IHB. reflexivity.
  - intros K l Ts IHTs c. simpl. rewrite shift_ty_go_eq_map. simpl.
    rewrite !no_local_ty_go_eq_fold. rewrite IHTs. reflexivity.
  - intros A IHA c. simpl. apply IHA.
  - intros B A IHB IHA c. simpl. rewrite IHB, IHA. reflexivity.
  - intro c. reflexivity.
  - intros A Ts IHA IHTs c. simpl. rewrite IHA, IHTs. reflexivity.
Qed.

Lemma no_local_lt_shift_any : forall amount l c,
  no_local_lt (shift_lt amount c l) = no_local_lt l.
Proof.
  intros amount l. induction l; intro c; simpl.
  - destruct (Nat.leb c n); reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHl1, IHl2. reflexivity.
Qed.

Lemma no_local_ty_shift_lt_any : forall amount T c,
  no_local_ty (shift_lt_in_ty amount c T) = no_local_ty T.
Proof.
  intros amount.
  apply (type_list_ind
    (fun T => forall c, no_local_ty (shift_lt_in_ty amount c T) = no_local_ty T)
    (fun Ts => forall c,
       fold_right (fun A acc => andb (no_local_ty A) acc) true
         (List.map (shift_lt_in_ty amount c) Ts) =
       fold_right (fun A acc => andb (no_local_ty A) acc) true Ts)).
  - intros n c. reflexivity.
  - intros A l B IHA IHB c. simpl. rewrite IHA, IHB, no_local_lt_shift_any. reflexivity.
  - intros K l Ts IHTs c. simpl. rewrite shift_lt_in_ty_go_eq_map. simpl.
    rewrite !no_local_ty_go_eq_fold. rewrite IHTs, no_local_lt_shift_any. reflexivity.
  - intros A IHA c. simpl. apply IHA.
  - intros B A IHB IHA c. simpl. rewrite IHB, IHA. reflexivity.
  - intro c. reflexivity.
  - intros A Ts IHA IHTs c. simpl. rewrite IHA, IHTs. reflexivity.
Qed.

Lemma no_local_lt_closed : forall l c,
  no_local_lt l = true -> lt_lt_closed c l.
Proof.
  induction l as [x| | |l1 IH1 l2 IH2]; intros c H; simpl in *.
  - discriminate.
  - exact I.
  - discriminate.
  - apply Bool.andb_true_iff in H as [H1 H2]. split; [apply IH1 | apply IH2]; assumption.
Qed.

Lemma no_local_ty_ty_closed : forall T c,
  no_local_ty T = true -> ty_ty_closed c T.
Proof.
  apply (type_list_ind
    (fun T => forall c, no_local_ty T = true -> ty_ty_closed c T)
    (fun Ts => forall c,
      fold_right (fun A acc => andb (no_local_ty A) acc) true Ts = true ->
      tys_ty_closed c Ts)).
  - intros n c H. simpl in H. discriminate.
  - intros A l B IHA IHB c H. simpl in *.
    apply Bool.andb_true_iff in H as [HA Hrest].
    apply Bool.andb_true_iff in Hrest as [_ HB].
    split; [apply IHA | apply IHB]; assumption.
  - intros K l Ts IHTs c H. simpl in *.
    apply Bool.andb_true_iff in H as [_ HTs].
    apply IHTs. exact HTs.
  - intros A IHA c H. simpl in *. apply IHA. exact H.
  - intros B A IHB IHA c H. simpl in *.
    apply Bool.andb_true_iff in H as [HB HA].
    split; [apply IHB | apply IHA]; assumption.
  - intros c H. exact I.
  - intros A Ts IHA IHTs c H. simpl in *.
    apply Bool.andb_true_iff in H as [HA HTs].
    split; [apply IHA | apply IHTs]; assumption.
Qed.

Lemma no_local_tys_ty_closed : forall Ts c,
  fold_right (fun A acc => andb (no_local_ty A) acc) true Ts = true ->
  tys_ty_closed c Ts.
Proof.
  induction Ts as [|T Ts IH]; intros c H; simpl in *.
  - exact I.
  - apply Bool.andb_true_iff in H as [HT HTs].
    split; [apply no_local_ty_ty_closed | apply IH]; assumption.
Qed.

Lemma no_local_ty_lt_closed : forall T c,
  no_local_ty T = true -> ty_lt_closed c T.
Proof.
  apply (type_list_ind
    (fun T => forall c, no_local_ty T = true -> ty_lt_closed c T)
    (fun Ts => forall c,
      fold_right (fun A acc => andb (no_local_ty A) acc) true Ts = true ->
      tys_lt_closed c Ts)).
  - intros n c H. simpl in H. discriminate.
  - intros A l B IHA IHB c H. simpl in *.
    apply Bool.andb_true_iff in H as [HA Hrest].
    apply Bool.andb_true_iff in Hrest as [Hl HB].
    repeat split.
    + apply IHA. exact HA.
    + apply no_local_lt_closed. exact Hl.
    + apply IHB. exact HB.
  - intros K l Ts IHTs c H. simpl in *.
    apply Bool.andb_true_iff in H as [Hl HTs].
    split; [apply no_local_lt_closed | apply IHTs]; assumption.
  - intros A IHA c H. simpl in *. apply IHA. exact H.
  - intros B A IHB IHA c H. simpl in *.
    apply Bool.andb_true_iff in H as [HB HA].
    split; [apply IHB | apply IHA]; assumption.
  - intros c H. exact I.
  - intros A Ts IHA IHTs c H. simpl in *.
    apply Bool.andb_true_iff in H as [HA HTs].
    split; [apply IHA | apply IHTs]; assumption.
Qed.

Lemma no_local_tys_lt_closed : forall Ts c,
  fold_right (fun A acc => andb (no_local_ty A) acc) true Ts = true ->
  tys_lt_closed c Ts.
Proof.
  induction Ts as [|T Ts IH]; intros c H; simpl in *.
  - exact I.
  - apply Bool.andb_true_iff in H as [HT HTs].
    split; [apply no_local_ty_lt_closed | apply IH]; assumption.
Qed.

Lemma shift_ty_no_local_id : forall T amount cutoff,
  no_local_ty T = true -> shift_ty amount cutoff T = T.
Proof.
  intros T amount cutoff Hnl.
  apply shift_ty_in_ty_closed. apply no_local_ty_ty_closed. exact Hnl.
Qed.

Lemma shift_lt_in_ty_no_local_id : forall T amount cutoff,
  no_local_ty T = true -> shift_lt_in_ty amount cutoff T = T.
Proof.
  intros T amount cutoff Hnl.
  apply shift_lt_in_type_closed. apply no_local_ty_lt_closed. exact Hnl.
Qed.

Lemma subst_ty_no_local_id : forall T var R,
  no_local_ty T = true -> subst_ty var R T = T.
Proof.
  intros T var R Hnl.
  apply subst_ty_ty_closed_id with (c := 0); [apply no_local_ty_ty_closed; exact Hnl | lia].
Qed.

Lemma subst_lt_in_ty_no_local_id : forall T var R,
  no_local_ty T = true -> subst_lt_in_ty var R T = T.
Proof.
  intros T var R Hnl.
  apply subst_lt_in_type_closed with (c := var).
  apply no_local_ty_lt_closed. exact Hnl.
Qed.

Lemma shift_ty_closed0_id : forall T amount cutoff,
  ty_ty_closed 0 T -> shift_ty amount cutoff T = T.
Proof.
  intros T amount cutoff Hclosed.
  apply shift_ty_in_ty_closed with (c := cutoff).
  eapply ty_ty_closed_mono; [apply Nat.le_0_l | exact Hclosed].
Qed.

Lemma shift_lt_in_ty_closed0_id : forall T amount cutoff,
  ty_lt_closed 0 T -> shift_lt_in_ty amount cutoff T = T.
Proof.
  intros T amount cutoff Hclosed.
  apply shift_lt_in_type_closed with (c := cutoff).
  eapply ty_lt_closed_mono; [apply Nat.le_0_l | exact Hclosed].
Qed.

Lemma subst_ty_closed0_id : forall T var R,
  ty_ty_closed 0 T -> subst_ty var R T = T.
Proof.
  intros T var R Hclosed.
  apply subst_ty_ty_closed_id with (c := 0); [exact Hclosed | lia].
Qed.

Lemma subst_lt_in_ty_closed0_id : forall T var R,
  ty_lt_closed 0 T -> subst_lt_in_ty var R T = T.
Proof.
  intros T var R Hclosed.
  apply subst_lt_in_type_closed with (c := var).
  eapply ty_lt_closed_mono; [apply Nat.le_0_l | exact Hclosed].
Qed.

Lemma marker_annots_no_local_closed : forall t,
  marker_annots_no_local t -> marker_annots_closed t.
Proof.
  intros t Hnl.
  unfold marker_annots_no_local, marker_annots_closed in *.
  eapply Forall_impl; [|exact Hnl].
  intros [m T] HT. simpl in *. split.
  - apply no_local_ty_ty_closed. exact HT.
  - apply no_local_ty_lt_closed. exact HT.
Qed.

Lemma marker_annots_list_no_local_closed : forall ts,
  marker_annots_list_no_local ts -> marker_annots_list_closed ts.
Proof.
  intros ts Hnl.
  unfold marker_annots_list_no_local, marker_annots_list_closed in *.
  eapply Forall_impl; [|exact Hnl].
  intros [m T] HT. simpl in *. split.
  - apply no_local_ty_ty_closed. exact HT.
  - apply no_local_ty_lt_closed. exact HT.
Qed.

Lemma marker_annots_no_local_shift_tm : forall t amount cutoff,
  marker_annots_no_local t ->
  marker_annots_no_local (shift_tm amount cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
       marker_annots_no_local t -> marker_annots_no_local (shift_tm amount cutoff t))
    (fun ts => forall amount cutoff,
       marker_annots_list_no_local ts ->
       marker_annots_list_no_local (List.map (shift_tm amount cutoff) ts))).
  - intros n amount cutoff H. exact H.
  - intros t1 t2 IH1 IH2 amount cutoff H. unfold marker_annots_no_local in *.
    simpl in *. apply Forall_app in H. destruct H as [H1 H2].
    apply Forall_app. split; [apply IH1 | apply IH2]; assumption.
  - intros body T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros bound body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t l IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH amount cutoff H. simpl in *.
    unfold marker_annots_no_local in H. fold marker_annots_list_no_local in H.
    exact (IH amount cutoff H).
  - intros scrut tag n_lt arity yes no IHs IHy IHn amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    repeat rewrite Forall_app. repeat split; [apply IHs | apply IHy | apply IHn]; assumption.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Hop Hbody].
    apply Forall_app. split; [apply IHop | apply IHbody]; assumption.
  - intros recv Ss arg IHrecv IHarg amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Hr Ha].
    apply Forall_app. split; [apply IHrecv | apply IHarg]; assumption.
  - intros E m n_beta Ts T_R op_body IHop amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + exact Hhead.
    + apply IHop. exact Htail.
  - intros m T_B T_R t IH amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + exact Hhead.
    + apply IH. exact Htail.
  - intros m T_B T_R b IH amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + exact Hhead.
    + apply IH. exact Htail.
  - intros amount cutoff H. exact H.
  - intros t ts IHt IHts amount cutoff H.
    unfold marker_annots_list_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Ht Hts].
    apply Forall_app. split.
    + apply IHt. exact Ht.
    + apply IHts. exact Hts.
Qed.

Lemma marker_annots_no_local_shift_ty_in_tm : forall t amount cutoff,
  marker_annots_no_local t ->
  marker_annots_no_local (shift_ty_in_tm amount cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
       marker_annots_no_local t -> marker_annots_no_local (shift_ty_in_tm amount cutoff t))
    (fun ts => forall amount cutoff,
       marker_annots_list_no_local ts ->
       marker_annots_list_no_local (List.map (shift_ty_in_tm amount cutoff) ts))).
  - intros n amount cutoff H. exact H.
  - intros t1 t2 IH1 IH2 amount cutoff H. unfold marker_annots_no_local in *.
    simpl in *. apply Forall_app in H. destruct H as [H1 H2].
    apply Forall_app. split; [apply IH1 | apply IH2]; assumption.
  - intros body T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros bound body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t l IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH amount cutoff H. simpl in *.
    unfold marker_annots_no_local in H. fold marker_annots_list_no_local in H.
    exact (IH amount cutoff H).
  - intros scrut tag n_lt arity yes no IHs IHy IHn amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    repeat rewrite Forall_app. repeat split; [apply IHs | apply IHy | apply IHn]; assumption.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Hop Hbody].
    apply Forall_app. split; [apply IHop | apply IHbody]; assumption.
  - intros recv Ss arg IHrecv IHarg amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Hr Ha].
    apply Forall_app. split; [apply IHrecv | apply IHarg]; assumption.
  - intros E m n_beta Ts T_R op_body IHop amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + simpl. rewrite no_local_ty_shift_ty_any. exact Hhead.
    + apply IHop. exact Htail.
  - intros m T_B T_R t IH amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + simpl. rewrite no_local_ty_shift_ty_any. exact Hhead.
    + apply IH. exact Htail.
  - intros m T_B T_R b IH amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + simpl. rewrite no_local_ty_shift_ty_any. exact Hhead.
    + apply IH. exact Htail.
  - intros amount cutoff H. exact H.
  - intros t ts IHt IHts amount cutoff H.
    unfold marker_annots_list_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Ht Hts].
    apply Forall_app. split.
    + apply IHt. exact Ht.
    + apply IHts. exact Hts.
Qed.

Lemma marker_annots_no_local_shift_lt_in_tm : forall t amount cutoff,
  marker_annots_no_local t ->
  marker_annots_no_local (shift_lt_in_tm amount cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
       marker_annots_no_local t -> marker_annots_no_local (shift_lt_in_tm amount cutoff t))
    (fun ts => forall amount cutoff,
       marker_annots_list_no_local ts ->
       marker_annots_list_no_local (List.map (shift_lt_in_tm amount cutoff) ts))).
  - intros n amount cutoff H. exact H.
  - intros t1 t2 IH1 IH2 amount cutoff H. unfold marker_annots_no_local in *.
    simpl in *. apply Forall_app in H. destruct H as [H1 H2].
    apply Forall_app. split; [apply IH1 | apply IH2]; assumption.
  - intros body T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros bound body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t l IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH amount cutoff H. simpl in *.
    unfold marker_annots_no_local in H. fold marker_annots_list_no_local in H.
    exact (IH amount cutoff H).
  - intros scrut tag n_lt arity yes no IHs IHy IHn amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    repeat rewrite Forall_app. repeat split; [apply IHs | apply IHy | apply IHn]; assumption.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Hop Hbody].
    apply Forall_app. split; [apply IHop | apply IHbody]; assumption.
  - intros recv Ss arg IHrecv IHarg amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Hr Ha].
    apply Forall_app. split; [apply IHrecv | apply IHarg]; assumption.
  - intros E m n_beta Ts T_R op_body IHop amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + simpl. rewrite no_local_ty_shift_lt_any. exact Hhead.
    + apply IHop. exact Htail.
  - intros m T_B T_R t IH amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + simpl. rewrite no_local_ty_shift_lt_any. exact Hhead.
    + apply IH. exact Htail.
  - intros m T_B T_R b IH amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + simpl. rewrite no_local_ty_shift_lt_any. exact Hhead.
    + apply IH. exact Htail.
  - intros amount cutoff H. exact H.
  - intros t ts IHt IHts amount cutoff H.
    unfold marker_annots_list_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Ht Hts].
    apply Forall_app. split.
    + apply IHt. exact Ht.
    + apply IHts. exact Hts.
Qed.

Lemma marker_annots_no_local_subst_tm : forall t var repl,
  marker_annots_no_local repl ->
  marker_annots_no_local t ->
  marker_annots_no_local (subst_tm var repl t).
Proof.
  apply (term_list_ind
    (fun t => forall var repl,
       marker_annots_no_local repl ->
       marker_annots_no_local t ->
       marker_annots_no_local (subst_tm var repl t))
    (fun ts => forall var repl,
       marker_annots_no_local repl ->
       marker_annots_list_no_local ts ->
       marker_annots_list_no_local (List.map (subst_tm var repl) ts))).
  - intros n var repl Hrepl H. simpl.
    destruct (Nat.eqb n var); [exact Hrepl|].
    destruct (Nat.ltb var n); constructor.
  - intros t1 t2 IH1 IH2 var repl Hrepl H. unfold marker_annots_no_local in *.
    simpl in *. apply Forall_app in H. destruct H as [H1 H2].
    apply Forall_app. split; [apply IH1 | apply IH2]; assumption.
  - intros body T IH var repl Hrepl H. simpl in *.
    apply IH; [apply marker_annots_no_local_shift_tm |]; assumption.
  - intros t T IH var repl Hrepl H. simpl in *.
    apply IH; assumption.
  - intros bound body IH var repl Hrepl H. simpl in *.
    apply IH; [apply marker_annots_no_local_shift_ty_in_tm |]; assumption.
  - intros t l IH var repl Hrepl H. simpl in *.
    apply IH; assumption.
  - intros body IH var repl Hrepl H. simpl in *.
    apply IH; [apply marker_annots_no_local_shift_lt_in_tm |]; assumption.
  - intros K l lts Ts ts IH var repl Hrepl H. simpl in *.
    unfold marker_annots_no_local in H. fold marker_annots_list_no_local in H.
    apply IH; assumption.
  - intros scrut tag n_lt arity yes no IHs IHy IHn var repl Hrepl H.
    unfold marker_annots_no_local in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    repeat rewrite Forall_app. repeat split.
    + apply IHs; assumption.
    + apply IHy; [apply marker_annots_no_local_shift_tm; apply marker_annots_no_local_shift_lt_in_tm |]; assumption.
    + apply IHn; assumption.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody var repl Hrepl H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Hop Hbody].
    apply Forall_app. split.
    + apply IHop; [apply marker_annots_no_local_shift_tm |]; assumption.
    + apply IHbody; [apply marker_annots_no_local_shift_tm |]; assumption.
  - intros recv Ss arg IHrecv IHarg var repl Hrepl H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Hr Ha].
    apply Forall_app. split; [apply IHrecv | apply IHarg]; assumption.
  - intros E m n_beta Ts T_R op_body IHop var repl Hrepl H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + exact Hhead.
    + apply IHop; [apply marker_annots_no_local_shift_tm |]; assumption.
  - intros m T_B T_R t IH var repl Hrepl H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + exact Hhead.
    + apply IH; assumption.
  - intros m T_B T_R b IH var repl Hrepl H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + exact Hhead.
    + apply IH; [apply marker_annots_no_local_shift_tm |]; assumption.
  - intros var repl Hrepl H. exact H.
  - intros t ts IHt IHts var repl Hrepl H.
    unfold marker_annots_list_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Ht Hts].
    apply Forall_app. split.
    + apply IHt; assumption.
    + apply IHts; assumption.
Qed.

Lemma marker_annots_no_local_subst_ty_in_tm : forall t n S,
  marker_annots_no_local t ->
  marker_annots_no_local (subst_ty_in_tm n S t).
Proof.
  apply (term_list_ind
    (fun t => forall n S,
       marker_annots_no_local t ->
       marker_annots_no_local (subst_ty_in_tm n S t))
    (fun ts => forall n S,
       marker_annots_list_no_local ts ->
       marker_annots_list_no_local (List.map (subst_ty_in_tm n S) ts))).
  - intros n0 n S H. exact H.
  - intros t1 t2 IH1 IH2 n S H. unfold marker_annots_no_local in *.
    simpl in *. apply Forall_app in H. destruct H as [H1 H2].
    apply Forall_app. split; [apply IH1 | apply IH2]; assumption.
  - intros body T IH n S H. simpl in *. apply IH. exact H.
  - intros t T IH n S H. simpl in *. apply IH. exact H.
  - intros bound body IH n S H. simpl in *. apply IH. exact H.
  - intros t l IH n S H. simpl in *. apply IH. exact H.
  - intros body IH n S H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH n S H. simpl in *.
    unfold marker_annots_no_local in H. fold marker_annots_list_no_local in H.
    exact (IH n S H).
  - intros scrut tag n_lt arity yes no IHs IHy IHn n S H.
    unfold marker_annots_no_local in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    repeat rewrite Forall_app. repeat split; [apply IHs | apply IHy | apply IHn]; assumption.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody n S H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Hop Hbody].
    apply Forall_app. split; [apply IHop | apply IHbody]; assumption.
  - intros recv Ss arg IHrecv IHarg n S H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Hr Ha].
    apply Forall_app. split; [apply IHrecv | apply IHarg]; assumption.
  - intros E m n_beta Ts T_R op_body IHop n S H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + simpl. eapply no_local_ty_subst_ty. exact Hhead.
    + apply IHop. exact Htail.
  - intros m T_B T_R t IH n S H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + simpl. eapply no_local_ty_subst_ty. exact Hhead.
    + apply IH. exact Htail.
  - intros m T_B T_R b IH n S H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + simpl. eapply no_local_ty_subst_ty. exact Hhead.
    + apply IH. exact Htail.
  - intros n S H. exact H.
  - intros t ts IHt IHts n S H.
    unfold marker_annots_list_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Ht Hts].
    apply Forall_app. split.
    + apply IHt. exact Ht.
    + apply IHts. exact Hts.
Qed.

Lemma marker_annots_no_local_subst_lt_in_tm : forall t n l,
  marker_annots_no_local t ->
  marker_annots_no_local (subst_lt_in_tm n l t).
Proof.
  apply (term_list_ind
    (fun t => forall n l,
       marker_annots_no_local t ->
       marker_annots_no_local (subst_lt_in_tm n l t))
    (fun ts => forall n l,
       marker_annots_list_no_local ts ->
       marker_annots_list_no_local (List.map (subst_lt_in_tm n l) ts))).
  - intros n0 n l H. exact H.
  - intros t1 t2 IH1 IH2 n l H. unfold marker_annots_no_local in *.
    simpl in *. apply Forall_app in H. destruct H as [H1 H2].
    apply Forall_app. split; [apply IH1 | apply IH2]; assumption.
  - intros body T IH n l H. simpl in *. apply IH. exact H.
  - intros t T IH n l H. simpl in *. apply IH. exact H.
  - intros bound body IH n l H. simpl in *. apply IH. exact H.
  - intros t l0 IH n l H. simpl in *. apply IH. exact H.
  - intros body IH n l H. simpl in *. apply IH. exact H.
  - intros K l0 lts Ts ts IH n l H. simpl in *.
    unfold marker_annots_no_local in H. fold marker_annots_list_no_local in H.
    exact (IH n l H).
  - intros scrut tag n_lt arity yes no IHs IHy IHn n l H.
    unfold marker_annots_no_local in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    repeat rewrite Forall_app. repeat split; [apply IHs | apply IHy | apply IHn]; assumption.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody n l H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Hop Hbody].
    apply Forall_app. split; [apply IHop | apply IHbody]; assumption.
  - intros recv Ss arg IHrecv IHarg n l H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Hr Ha].
    apply Forall_app. split; [apply IHrecv | apply IHarg]; assumption.
  - intros E m n_beta Ts T_R op_body IHop n l H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + simpl. eapply no_local_ty_subst_lt. exact Hhead.
    + apply IHop. exact Htail.
  - intros m T_B T_R t IH n l H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + simpl. eapply no_local_ty_subst_lt. exact Hhead.
    + apply IH. exact Htail.
  - intros m T_B T_R b IH n l H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst. constructor.
    + simpl. eapply no_local_ty_subst_lt. exact Hhead.
    + apply IH. exact Htail.
  - intros n l H. exact H.
  - intros t ts IHt IHts n l H.
    unfold marker_annots_list_no_local in *. simpl in *.
    apply Forall_app in H. destruct H as [Ht Hts].
    apply Forall_app. split.
    + apply IHt. exact Ht.
    + apply IHts. exact Hts.
Qed.

Lemma marker_annots_no_local_subst_list_tm : forall vs t,
  Forall marker_annots_no_local vs ->
  marker_annots_no_local t ->
  marker_annots_no_local (subst_list_tm vs t).
Proof.
  induction vs as [|v rest IH]; intros t Hvs Ht; simpl.
  - exact Ht.
  - inversion Hvs as [|v0 rest0 Hv Hrest Heq]; subst.
    apply IH; [exact Hrest|].
    apply marker_annots_no_local_subst_tm.
    + apply marker_annots_no_local_shift_tm. exact Hv.
    + exact Ht.
Qed.

Lemma marker_annots_no_local_subst_list_lt_in_tm : forall lts t,
  marker_annots_no_local t ->
  marker_annots_no_local (subst_list_lt_in_tm lts t).
Proof.
  induction lts as [|l rest IH]; intros t Ht; simpl.
  - exact Ht.
  - apply IH. apply marker_annots_no_local_subst_lt_in_tm. exact Ht.
Qed.

Lemma marker_annots_no_local_subst_list_ty_in_tm : forall Ss t,
  marker_annots_no_local t ->
  marker_annots_no_local (subst_list_ty_in_tm Ss t).
Proof.
  induction Ss as [|S rest IH]; intros t Ht; simpl.
  - exact Ht.
  - apply IH. apply marker_annots_no_local_subst_ty_in_tm. exact Ht.
Qed.

(* go_eq_map for subst_ty_in_tm (the other go_eq_map lemmas live upstream). *)
Lemma subst_ty_in_tm_go_eq_map : forall var R ts,
  (fix go ts := match ts with [] => [] | u :: rest => subst_ty_in_tm var R u :: go rest end) ts =
  List.map (subst_ty_in_tm var R) ts.
Proof. intros; induction ts; simpl; congruence. Qed.

Lemma marker_annots_shift_tm : forall t amount cutoff,
  marker_annots (shift_tm amount cutoff t) = marker_annots t.
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
       marker_annots (shift_tm amount cutoff t) = marker_annots t)
    (fun ts => forall amount cutoff,
       List.concat (List.map marker_annots (List.map (shift_tm amount cutoff) ts)) =
       List.concat (List.map marker_annots ts))).
  - intros n amount cutoff. reflexivity.
  - intros t1 t2 IH1 IH2 amount cutoff. simpl.
    rewrite IH1, IH2. reflexivity.
  - intros body T IH amount cutoff. simpl. apply IH.
  - intros t T IH amount cutoff. simpl. apply IH.
  - intros bound body IH amount cutoff. simpl. apply IH.
  - intros t l IH amount cutoff. simpl. apply IH.
  - intros body IH amount cutoff. simpl. apply IH.
  - intros K l lts Ts ts IH amount cutoff. simpl.
    rewrite shift_tm_go_eq_map. apply IH.
  - intros scrut tag n_lt arity yes no IHs IHy IHn amount cutoff. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody amount cutoff. simpl.
    rewrite IHop, IHbody. reflexivity.
  - intros recv Ss arg IHrecv IHarg amount cutoff. simpl.
    rewrite IHrecv, IHarg. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop amount cutoff. simpl.
    rewrite IHop. reflexivity.
  - intros m T_B T_R t IH amount cutoff. simpl.
    rewrite IH. reflexivity.
  - intros m T_B T_R b IH amount cutoff. simpl.
    rewrite IH. reflexivity.
  - intros amount cutoff. reflexivity.
  - intros t ts IHt IHts amount cutoff. simpl.
    rewrite IHt, IHts. reflexivity.
Qed.

Lemma marker_annots_list_shift_tm : forall ts amount cutoff,
  List.concat (List.map marker_annots (List.map (shift_tm amount cutoff) ts)) =
  List.concat (List.map marker_annots ts).
Proof.
  induction ts as [|t ts IH]; intros amount cutoff; simpl.
  - reflexivity.
  - rewrite marker_annots_shift_tm, IH. reflexivity.
Qed.

Lemma marker_annots_shift_ectx_tm : forall E hole amount cutoff,
  marker_annots (plug (shift_ectx_tm amount cutoff E) hole) = marker_annots (plug E hole).
Proof.
  induction E; intros hole amount cutoff; simpl.
  - reflexivity.
  - rewrite IHE, marker_annots_shift_tm. reflexivity.
  - rewrite marker_annots_shift_tm, IHE. reflexivity.
  - apply IHE.
  - apply IHE.
  - repeat rewrite List.map_app. repeat rewrite List.concat_app. simpl.
    rewrite marker_annots_list_shift_tm, IHE, marker_annots_list_shift_tm. reflexivity.
  - rewrite IHE, !marker_annots_shift_tm. reflexivity.
  - rewrite IHE. reflexivity.
  - rewrite IHE, marker_annots_shift_tm. reflexivity.
  - rewrite marker_annots_shift_tm, IHE. reflexivity.
Qed.

Lemma marker_annots_shift_ty_in_tm_no_local : forall t amount cutoff,
  marker_annots_no_local t ->
  marker_annots (shift_ty_in_tm amount cutoff t) = marker_annots t.
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
       marker_annots_no_local t ->
       marker_annots (shift_ty_in_tm amount cutoff t) = marker_annots t)
    (fun ts => forall amount cutoff,
       marker_annots_list_no_local ts ->
       List.concat (List.map marker_annots (List.map (shift_ty_in_tm amount cutoff) ts)) =
       List.concat (List.map marker_annots ts))).
  - intros n amount cutoff H. reflexivity.
  - intros t1 t2 IH1 IH2 amount cutoff H. unfold marker_annots_no_local in *.
    simpl in *. apply Forall_app in H as [H1 H2].
    rewrite (IH1 amount cutoff H1), (IH2 amount cutoff H2). reflexivity.
  - intros body T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros bound body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t l IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH amount cutoff H. simpl in *.
    rewrite shift_ty_in_tm_go_eq_map.
    unfold marker_annots_no_local in H. fold marker_annots_list_no_local in H.
    apply IH. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    rewrite (IHs amount cutoff Hs), (IHy amount cutoff Hy), (IHn amount cutoff Hn).
    reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H as [Hop Hbody].
    rewrite (IHop amount (cutoff + n_beta) Hop), (IHbody amount cutoff Hbody).
    reflexivity.
  - intros recv Ss arg IHrecv IHarg amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H as [Hr Ha].
    rewrite (IHrecv amount cutoff Hr), (IHarg amount cutoff Ha). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    rewrite (shift_ty_no_local_id T_R amount cutoff Hhead).
    rewrite (IHop amount (cutoff + n_beta) Htail). reflexivity.
  - intros m T_B T_R t IH amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    rewrite (shift_ty_no_local_id T_R amount cutoff Hhead).
    rewrite (IH amount cutoff Htail). reflexivity.
  - intros m T_B T_R b IH amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    rewrite (shift_ty_no_local_id T_R amount cutoff Hhead).
    rewrite (IH amount cutoff Htail). reflexivity.
  - intros amount cutoff H. reflexivity.
  - intros t ts IHt IHts amount cutoff H.
    unfold marker_annots_list_no_local in *. simpl in *.
    apply Forall_app in H as [Ht Hts].
    rewrite (IHt amount cutoff Ht), (IHts amount cutoff Hts). reflexivity.
Qed.

Lemma marker_annots_shift_lt_in_tm_no_local : forall t amount cutoff,
  marker_annots_no_local t ->
  marker_annots (shift_lt_in_tm amount cutoff t) = marker_annots t.
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
       marker_annots_no_local t ->
       marker_annots (shift_lt_in_tm amount cutoff t) = marker_annots t)
    (fun ts => forall amount cutoff,
       marker_annots_list_no_local ts ->
       List.concat (List.map marker_annots (List.map (shift_lt_in_tm amount cutoff) ts)) =
       List.concat (List.map marker_annots ts))).
  - intros n amount cutoff H. reflexivity.
  - intros t1 t2 IH1 IH2 amount cutoff H. unfold marker_annots_no_local in *.
    simpl in *. apply Forall_app in H as [H1 H2].
    rewrite (IH1 amount cutoff H1), (IH2 amount cutoff H2). reflexivity.
  - intros body T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros bound body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t l IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH amount cutoff H. simpl in *.
    rewrite shift_lt_in_tm_go_eq_map.
    unfold marker_annots_no_local in H. fold marker_annots_list_no_local in H.
    apply IH. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    rewrite (IHs amount cutoff Hs), (IHy amount (cutoff + n_lt) Hy), (IHn amount cutoff Hn).
    reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H as [Hop Hbody].
    rewrite (IHop amount cutoff Hop), (IHbody amount cutoff Hbody). reflexivity.
  - intros recv Ss arg IHrecv IHarg amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H as [Hr Ha].
    rewrite (IHrecv amount cutoff Hr), (IHarg amount cutoff Ha). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    rewrite (shift_lt_in_ty_no_local_id T_R amount cutoff Hhead).
    rewrite (IHop amount cutoff Htail). reflexivity.
  - intros m T_B T_R t IH amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    rewrite (shift_lt_in_ty_no_local_id T_R amount cutoff Hhead).
    rewrite (IH amount cutoff Htail). reflexivity.
  - intros m T_B T_R b IH amount cutoff H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    rewrite (shift_lt_in_ty_no_local_id T_R amount cutoff Hhead).
    rewrite (IH amount cutoff Htail). reflexivity.
  - intros amount cutoff H. reflexivity.
  - intros t ts IHt IHts amount cutoff H.
    unfold marker_annots_list_no_local in *. simpl in *.
    apply Forall_app in H as [Ht Hts].
    rewrite (IHt amount cutoff Ht), (IHts amount cutoff Hts). reflexivity.
Qed.

Lemma marker_annots_shift_ty_in_tm_closed : forall t amount cutoff,
  marker_annots_closed t ->
  marker_annots (shift_ty_in_tm amount cutoff t) = marker_annots t.
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
       marker_annots_closed t ->
       marker_annots (shift_ty_in_tm amount cutoff t) = marker_annots t)
    (fun ts => forall amount cutoff,
       marker_annots_list_closed ts ->
       List.concat (List.map marker_annots (List.map (shift_ty_in_tm amount cutoff) ts)) =
       List.concat (List.map marker_annots ts))).
  - intros n amount cutoff H. reflexivity.
  - intros t1 t2 IH1 IH2 amount cutoff H. unfold marker_annots_closed in *.
    simpl in *. apply Forall_app in H as [H1 H2].
    rewrite (IH1 amount cutoff H1), (IH2 amount cutoff H2). reflexivity.
  - intros body T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros bound body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t l IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH amount cutoff H. simpl in *.
    rewrite shift_ty_in_tm_go_eq_map.
    unfold marker_annots_closed in H. fold marker_annots_list_closed in H.
    apply IH. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    rewrite (IHs amount cutoff Hs), (IHy amount cutoff Hy), (IHn amount cutoff Hn).
    reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hop Hbody].
    rewrite (IHop amount (cutoff + n_beta) Hop), (IHbody amount cutoff Hbody).
    reflexivity.
  - intros recv Ss arg IHrecv IHarg amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hr Ha].
    rewrite (IHrecv amount cutoff Hr), (IHarg amount cutoff Ha). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [HTy _].
    rewrite (shift_ty_closed0_id T_R amount cutoff HTy).
    rewrite (IHop amount (cutoff + n_beta) Htail). reflexivity.
  - intros m T_B T_R t IH amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [HTy _].
    rewrite (shift_ty_closed0_id T_R amount cutoff HTy).
    rewrite (IH amount cutoff Htail). reflexivity.
  - intros m T_B T_R b IH amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [HTy _].
    rewrite (shift_ty_closed0_id T_R amount cutoff HTy).
    rewrite (IH amount cutoff Htail). reflexivity.
  - intros amount cutoff H. reflexivity.
  - intros t ts IHt IHts amount cutoff H.
    unfold marker_annots_list_closed in *. simpl in *.
    apply Forall_app in H as [Ht Hts].
    rewrite (IHt amount cutoff Ht), (IHts amount cutoff Hts). reflexivity.
Qed.

Lemma marker_annots_shift_lt_in_tm_closed : forall t amount cutoff,
  marker_annots_closed t ->
  marker_annots (shift_lt_in_tm amount cutoff t) = marker_annots t.
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
       marker_annots_closed t ->
       marker_annots (shift_lt_in_tm amount cutoff t) = marker_annots t)
    (fun ts => forall amount cutoff,
       marker_annots_list_closed ts ->
       List.concat (List.map marker_annots (List.map (shift_lt_in_tm amount cutoff) ts)) =
       List.concat (List.map marker_annots ts))).
  - intros n amount cutoff H. reflexivity.
  - intros t1 t2 IH1 IH2 amount cutoff H. unfold marker_annots_closed in *.
    simpl in *. apply Forall_app in H as [H1 H2].
    rewrite (IH1 amount cutoff H1), (IH2 amount cutoff H2). reflexivity.
  - intros body T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros bound body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t l IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH amount cutoff H. simpl in *.
    rewrite shift_lt_in_tm_go_eq_map.
    unfold marker_annots_closed in H. fold marker_annots_list_closed in H.
    apply IH. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    rewrite (IHs amount cutoff Hs), (IHy amount (cutoff + n_lt) Hy), (IHn amount cutoff Hn).
    reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hop Hbody].
    rewrite (IHop amount cutoff Hop), (IHbody amount cutoff Hbody). reflexivity.
  - intros recv Ss arg IHrecv IHarg amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hr Ha].
    rewrite (IHrecv amount cutoff Hr), (IHarg amount cutoff Ha). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [_ HLt].
    rewrite (shift_lt_in_ty_closed0_id T_R amount cutoff HLt).
    rewrite (IHop amount cutoff Htail). reflexivity.
  - intros m T_B T_R t IH amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [_ HLt].
    rewrite (shift_lt_in_ty_closed0_id T_R amount cutoff HLt).
    rewrite (IH amount cutoff Htail). reflexivity.
  - intros m T_B T_R b IH amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [_ HLt].
    rewrite (shift_lt_in_ty_closed0_id T_R amount cutoff HLt).
    rewrite (IH amount cutoff Htail). reflexivity.
  - intros amount cutoff H. reflexivity.
  - intros t ts IHt IHts amount cutoff H.
    unfold marker_annots_list_closed in *. simpl in *.
    apply Forall_app in H as [Ht Hts].
    rewrite (IHt amount cutoff Ht), (IHts amount cutoff Hts). reflexivity.
Qed.

Lemma marker_annots_closed_shift_tm : forall t amount cutoff,
  marker_annots_closed t -> marker_annots_closed (shift_tm amount cutoff t).
Proof.
  intros t amount cutoff H.
  unfold marker_annots_closed in *. rewrite marker_annots_shift_tm. exact H.
Qed.

Lemma marker_annots_closed_shift_ty_in_tm : forall t amount cutoff,
  marker_annots_closed t -> marker_annots_closed (shift_ty_in_tm amount cutoff t).
Proof.
  intros t amount cutoff H.
  unfold marker_annots_closed in *. rewrite marker_annots_shift_ty_in_tm_closed by exact H. exact H.
Qed.

Lemma marker_annots_closed_shift_lt_in_tm : forall t amount cutoff,
  marker_annots_closed t -> marker_annots_closed (shift_lt_in_tm amount cutoff t).
Proof.
  intros t amount cutoff H.
  unfold marker_annots_closed in *. rewrite marker_annots_shift_lt_in_tm_closed by exact H. exact H.
Qed.

Lemma marker_annots_subst_ty_in_tm_no_local : forall t var replacement,
  marker_annots_no_local t ->
  marker_annots (subst_ty_in_tm var replacement t) = marker_annots t.
Proof.
  apply (term_list_ind
    (fun t => forall var replacement,
       marker_annots_no_local t ->
       marker_annots (subst_ty_in_tm var replacement t) = marker_annots t)
    (fun ts => forall var replacement,
       marker_annots_list_no_local ts ->
       List.concat (List.map marker_annots (List.map (subst_ty_in_tm var replacement) ts)) =
       List.concat (List.map marker_annots ts))).
  - intros n var replacement H. reflexivity.
  - intros t1 t2 IH1 IH2 var replacement H. unfold marker_annots_no_local in *.
    simpl in *. apply Forall_app in H as [H1 H2].
    rewrite (IH1 var replacement H1), (IH2 var replacement H2). reflexivity.
  - intros body T IH var replacement H. simpl in *. apply IH. exact H.
  - intros t T IH var replacement H. simpl in *. apply IH. exact H.
  - intros bound body IH var replacement H. simpl in *. apply IH. exact H.
  - intros t l IH var replacement H. simpl in *. apply IH. exact H.
  - intros body IH var replacement H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH var replacement H. simpl in *.
    rewrite subst_ty_in_tm_go_eq_map.
    unfold marker_annots_no_local in H. fold marker_annots_list_no_local in H.
    apply IH. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn var replacement H.
    unfold marker_annots_no_local in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    rewrite (IHs var replacement Hs).
    rewrite (IHy var (shift_lt_in_ty n_lt 0 replacement) Hy).
    rewrite (IHn var replacement Hn). reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody var replacement H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H as [Hop Hbody].
    rewrite (IHop (var + n_beta) (shift_ty n_beta 0 replacement) Hop).
    rewrite (IHbody var replacement Hbody). reflexivity.
  - intros recv Ss arg IHrecv IHarg var replacement H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H as [Hr Ha].
    rewrite (IHrecv var replacement Hr), (IHarg var replacement Ha). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop var replacement H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    rewrite (subst_ty_no_local_id T_R var replacement Hhead).
    rewrite (IHop (var + n_beta) (shift_ty n_beta 0 replacement) Htail). reflexivity.
  - intros m T_B T_R t IH var replacement H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    rewrite (subst_ty_no_local_id T_R var replacement Hhead).
    rewrite (IH var replacement Htail). reflexivity.
  - intros m T_B T_R b IH var replacement H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    rewrite (subst_ty_no_local_id T_R var replacement Hhead).
    rewrite (IH var replacement Htail). reflexivity.
  - intros var replacement H. reflexivity.
  - intros t ts IHt IHts var replacement H.
    unfold marker_annots_list_no_local in *. simpl in *.
    apply Forall_app in H as [Ht Hts].
    rewrite (IHt var replacement Ht), (IHts var replacement Hts). reflexivity.
Qed.

Lemma marker_annots_subst_lt_in_tm_no_local : forall t var replacement,
  marker_annots_no_local t ->
  marker_annots (subst_lt_in_tm var replacement t) = marker_annots t.
Proof.
  apply (term_list_ind
    (fun t => forall var replacement,
       marker_annots_no_local t ->
       marker_annots (subst_lt_in_tm var replacement t) = marker_annots t)
    (fun ts => forall var replacement,
       marker_annots_list_no_local ts ->
       List.concat (List.map marker_annots (List.map (subst_lt_in_tm var replacement) ts)) =
       List.concat (List.map marker_annots ts))).
  - intros n var replacement H. reflexivity.
  - intros t1 t2 IH1 IH2 var replacement H. unfold marker_annots_no_local in *.
    simpl in *. apply Forall_app in H as [H1 H2].
    rewrite (IH1 var replacement H1), (IH2 var replacement H2). reflexivity.
  - intros body T IH var replacement H. simpl in *. apply IH. exact H.
  - intros t T IH var replacement H. simpl in *. apply IH. exact H.
  - intros bound body IH var replacement H. simpl in *. apply IH. exact H.
  - intros t l IH var replacement H. simpl in *. apply IH. exact H.
  - intros body IH var replacement H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH var replacement H. simpl in *.
    rewrite subst_lt_in_tm_go_eq_map.
    unfold marker_annots_no_local in H. fold marker_annots_list_no_local in H.
    apply IH. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn var replacement H.
    unfold marker_annots_no_local in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    rewrite (IHs var replacement Hs).
    rewrite (IHy (n_lt + var) (shift_lt n_lt 0 replacement) Hy).
    rewrite (IHn var replacement Hn). reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody var replacement H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H as [Hop Hbody].
    rewrite (IHop var replacement Hop), (IHbody var replacement Hbody). reflexivity.
  - intros recv Ss arg IHrecv IHarg var replacement H.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H as [Hr Ha].
    rewrite (IHrecv var replacement Hr), (IHarg var replacement Ha). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop var replacement H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    rewrite (subst_lt_in_ty_no_local_id T_R var replacement Hhead).
    rewrite (IHop var replacement Htail). reflexivity.
  - intros m T_B T_R t IH var replacement H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    rewrite (subst_lt_in_ty_no_local_id T_R var replacement Hhead).
    rewrite (IH var replacement Htail). reflexivity.
  - intros m T_B T_R b IH var replacement H.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    rewrite (subst_lt_in_ty_no_local_id T_R var replacement Hhead).
    rewrite (IH var replacement Htail). reflexivity.
  - intros var replacement H. reflexivity.
  - intros t ts IHt IHts var replacement H.
    unfold marker_annots_list_no_local in *. simpl in *.
    apply Forall_app in H as [Ht Hts].
    rewrite (IHt var replacement Ht), (IHts var replacement Hts). reflexivity.
Qed.

Lemma marker_annots_subst_ty_in_tm_closed : forall t var replacement,
  marker_annots_closed t ->
  marker_annots (subst_ty_in_tm var replacement t) = marker_annots t.
Proof.
  apply (term_list_ind
    (fun t => forall var replacement,
       marker_annots_closed t ->
       marker_annots (subst_ty_in_tm var replacement t) = marker_annots t)
    (fun ts => forall var replacement,
       marker_annots_list_closed ts ->
       List.concat (List.map marker_annots (List.map (subst_ty_in_tm var replacement) ts)) =
       List.concat (List.map marker_annots ts))).
  - intros n var replacement H. reflexivity.
  - intros t1 t2 IH1 IH2 var replacement H. unfold marker_annots_closed in *.
    simpl in *. apply Forall_app in H as [H1 H2].
    rewrite (IH1 var replacement H1), (IH2 var replacement H2). reflexivity.
  - intros body T IH var replacement H. simpl in *. apply IH. exact H.
  - intros t T IH var replacement H. simpl in *. apply IH. exact H.
  - intros bound body IH var replacement H. simpl in *. apply IH. exact H.
  - intros t l IH var replacement H. simpl in *. apply IH. exact H.
  - intros body IH var replacement H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH var replacement H. simpl in *.
    rewrite subst_ty_in_tm_go_eq_map.
    unfold marker_annots_closed in H. fold marker_annots_list_closed in H.
    apply IH. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    rewrite (IHs var replacement Hs).
    rewrite (IHy var (shift_lt_in_ty n_lt 0 replacement) Hy).
    rewrite (IHn var replacement Hn). reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hop Hbody].
    rewrite (IHop (var + n_beta) (shift_ty n_beta 0 replacement) Hop).
    rewrite (IHbody var replacement Hbody). reflexivity.
  - intros recv Ss arg IHrecv IHarg var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hr Ha].
    rewrite (IHrecv var replacement Hr), (IHarg var replacement Ha). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [HTy _].
    rewrite (subst_ty_closed0_id T_R var replacement HTy).
    rewrite (IHop (var + n_beta) (shift_ty n_beta 0 replacement) Htail). reflexivity.
  - intros m T_B T_R t IH var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [HTy _].
    rewrite (subst_ty_closed0_id T_R var replacement HTy).
    rewrite (IH var replacement Htail). reflexivity.
  - intros m T_B T_R b IH var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [HTy _].
    rewrite (subst_ty_closed0_id T_R var replacement HTy).
    rewrite (IH var replacement Htail). reflexivity.
  - intros var replacement H. reflexivity.
  - intros t ts IHt IHts var replacement H.
    unfold marker_annots_list_closed in *. simpl in *.
    apply Forall_app in H as [Ht Hts].
    rewrite (IHt var replacement Ht), (IHts var replacement Hts). reflexivity.
Qed.

Lemma marker_annots_subst_lt_in_tm_closed : forall t var replacement,
  marker_annots_closed t ->
  marker_annots (subst_lt_in_tm var replacement t) = marker_annots t.
Proof.
  apply (term_list_ind
    (fun t => forall var replacement,
       marker_annots_closed t ->
       marker_annots (subst_lt_in_tm var replacement t) = marker_annots t)
    (fun ts => forall var replacement,
       marker_annots_list_closed ts ->
       List.concat (List.map marker_annots (List.map (subst_lt_in_tm var replacement) ts)) =
       List.concat (List.map marker_annots ts))).
  - intros n var replacement H. reflexivity.
  - intros t1 t2 IH1 IH2 var replacement H. unfold marker_annots_closed in *.
    simpl in *. apply Forall_app in H as [H1 H2].
    rewrite (IH1 var replacement H1), (IH2 var replacement H2). reflexivity.
  - intros body T IH var replacement H. simpl in *. apply IH. exact H.
  - intros t T IH var replacement H. simpl in *. apply IH. exact H.
  - intros bound body IH var replacement H. simpl in *. apply IH. exact H.
  - intros t l IH var replacement H. simpl in *. apply IH. exact H.
  - intros body IH var replacement H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH var replacement H. simpl in *.
    rewrite subst_lt_in_tm_go_eq_map.
    unfold marker_annots_closed in H. fold marker_annots_list_closed in H.
    apply IH. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    rewrite (IHs var replacement Hs).
    rewrite (IHy (n_lt + var) (shift_lt n_lt 0 replacement) Hy).
    rewrite (IHn var replacement Hn). reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hop Hbody].
    rewrite (IHop var replacement Hop), (IHbody var replacement Hbody). reflexivity.
  - intros recv Ss arg IHrecv IHarg var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hr Ha].
    rewrite (IHrecv var replacement Hr), (IHarg var replacement Ha). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [_ HLt].
    rewrite (subst_lt_in_ty_closed0_id T_R var replacement HLt).
    rewrite (IHop var replacement Htail). reflexivity.
  - intros m T_B T_R t IH var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [_ HLt].
    rewrite (subst_lt_in_ty_closed0_id T_R var replacement HLt).
    rewrite (IH var replacement Htail). reflexivity.
  - intros m T_B T_R b IH var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [_ HLt].
    rewrite (subst_lt_in_ty_closed0_id T_R var replacement HLt).
    rewrite (IH var replacement Htail). reflexivity.
  - intros var replacement H. reflexivity.
  - intros t ts IHt IHts var replacement H.
    unfold marker_annots_list_closed in *. simpl in *.
    apply Forall_app in H as [Ht Hts].
    rewrite (IHt var replacement Ht), (IHts var replacement Hts). reflexivity.
Qed.

Lemma marker_annots_subst_list_ty_in_tm_no_local : forall Ss t,
  marker_annots_no_local t ->
  marker_annots (subst_list_ty_in_tm Ss t) = marker_annots t.
Proof.
  induction Ss as [|S rest IH]; intros t Ht; simpl.
  - reflexivity.
  - rewrite (IH _ (marker_annots_no_local_subst_ty_in_tm _ _ _ Ht)).
    apply marker_annots_subst_ty_in_tm_no_local. exact Ht.
Qed.

Lemma marker_annots_subst_list_lt_in_tm_no_local : forall lts t,
  marker_annots_no_local t ->
  marker_annots (subst_list_lt_in_tm lts t) = marker_annots t.
Proof.
  induction lts as [|l rest IH]; intros t Ht; simpl.
  - reflexivity.
  - rewrite (IH _ (marker_annots_no_local_subst_lt_in_tm _ _ _ Ht)).
    apply marker_annots_subst_lt_in_tm_no_local. exact Ht.
Qed.

Lemma marker_annots_subst_list_ty_in_tm_closed : forall Ss t,
  marker_annots_closed t ->
  marker_annots (subst_list_ty_in_tm Ss t) = marker_annots t.
Proof.
  induction Ss as [|S rest IH]; intros t Ht; simpl.
  - reflexivity.
  - assert (Hsubst : marker_annots_closed (subst_ty_in_tm 0 (shift_ty (List.length rest) 0 S) t)).
    { unfold marker_annots_closed in *.
      rewrite marker_annots_subst_ty_in_tm_closed by exact Ht.
      exact Ht. }
    rewrite (IH _ Hsubst).
    apply marker_annots_subst_ty_in_tm_closed. exact Ht.
Qed.

Lemma marker_annots_subst_list_lt_in_tm_closed : forall lts t,
  marker_annots_closed t ->
  marker_annots (subst_list_lt_in_tm lts t) = marker_annots t.
Proof.
  induction lts as [|l rest IH]; intros t Ht; simpl.
  - reflexivity.
  - assert (Hsubst : marker_annots_closed (subst_lt_in_tm 0 (shift_lt (List.length rest) 0 l) t)).
    { unfold marker_annots_closed in *.
      rewrite marker_annots_subst_lt_in_tm_closed by exact Ht.
      exact Ht. }
    rewrite (IH _ Hsubst).
    apply marker_annots_subst_lt_in_tm_closed. exact Ht.
Qed.

Lemma marker_types_safe_marker_annots_eq : forall t u,
  marker_annots u = marker_annots t ->
  marker_types_safe t -> marker_types_safe u.
Proof.
  intros t u Hann Hsafe m T U HT HU.
  unfold marker_types_safe, marker_types_ok in Hsafe.
  rewrite Hann in HT, HU. eauto.
Qed.

Lemma marker_types_safe_shift_tm : forall t amount cutoff,
  marker_types_safe t -> marker_types_safe (shift_tm amount cutoff t).
Proof.
  intros t amount cutoff Hsafe.
  eapply marker_types_safe_marker_annots_eq; [apply marker_annots_shift_tm | exact Hsafe].
Qed.

Lemma marker_types_safe_subst_list_ty_in_tm_no_local : forall Ss t,
  marker_annots_no_local t ->
  marker_types_safe t -> marker_types_safe (subst_list_ty_in_tm Ss t).
Proof.
  intros Ss t Hnl Hsafe.
  eapply marker_types_safe_marker_annots_eq; [apply marker_annots_subst_list_ty_in_tm_no_local |]; eauto.
Qed.

Lemma marker_types_safe_subst_list_lt_in_tm_no_local : forall lts t,
  marker_annots_no_local t ->
  marker_types_safe t -> marker_types_safe (subst_list_lt_in_tm lts t).
Proof.
  intros lts t Hnl Hsafe.
  eapply marker_types_safe_marker_annots_eq; [apply marker_annots_subst_list_lt_in_tm_no_local |]; eauto.
Qed.

Lemma marker_annots_subst_tm_no_local_incl : forall t var repl,
  marker_annots_no_local repl ->
  marker_annots_no_local t ->
  incl (marker_annots (subst_tm var repl t))
       (marker_annots repl ++ marker_annots t).
Proof.
  apply (term_list_ind
    (fun t => forall var repl,
       marker_annots_no_local repl ->
       marker_annots_no_local t ->
       incl (marker_annots (subst_tm var repl t))
            (marker_annots repl ++ marker_annots t))
    (fun ts => forall var repl,
       marker_annots_no_local repl ->
       marker_annots_list_no_local ts ->
       incl (List.concat (List.map marker_annots (List.map (subst_tm var repl) ts)))
            (marker_annots repl ++ List.concat (List.map marker_annots ts)))).
  - intros n var repl Hrepl H p Hp. simpl in *.
    destruct (Nat.eqb n var); [apply List.in_or_app; left; exact Hp|].
    destruct (Nat.ltb var n); inversion Hp.
  - intros t1 t2 IH1 IH2 var repl Hrepl H p Hp.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H as [H1 H2].
    apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IH1 var repl Hrepl H1 p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IH2 var repl Hrepl H2 p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
  - intros body T IH var repl Hrepl H p Hp. simpl in *.
    specialize (IH (S var) (shift_tm 1 0 repl)
      (marker_annots_no_local_shift_tm _ _ _ Hrepl) H p Hp).
    rewrite marker_annots_shift_tm in IH. exact IH.
  - intros t T IH var repl Hrepl H p Hp. simpl in *.
    exact (IH var repl Hrepl H p Hp).
  - intros bound body IH var repl Hrepl H p Hp. simpl in *.
    specialize (IH var (shift_ty_in_tm 1 0 repl)
      (marker_annots_no_local_shift_ty_in_tm _ _ _ Hrepl) H p Hp).
    rewrite (marker_annots_shift_ty_in_tm_no_local repl 1 0 Hrepl) in IH. exact IH.
  - intros t l IH var repl Hrepl H p Hp. simpl in *.
    exact (IH var repl Hrepl H p Hp).
  - intros body IH var repl Hrepl H p Hp. simpl in *.
    specialize (IH var (shift_lt_in_tm 1 0 repl)
      (marker_annots_no_local_shift_lt_in_tm _ _ _ Hrepl) H p Hp).
    rewrite (marker_annots_shift_lt_in_tm_no_local repl 1 0 Hrepl) in IH. exact IH.
  - intros K l lts Ts ts IH var repl Hrepl H p Hp. simpl in *.
    rewrite subst_tm_go_eq_map in Hp.
    unfold marker_annots_no_local in H. fold marker_annots_list_no_local in H.
    exact (IH var repl Hrepl H p Hp).
  - intros scrut tag n_lt arity yes no IHs IHy IHn var repl Hrepl H p Hp.
    unfold marker_annots_no_local in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    repeat rewrite List.in_app_iff in Hp. destruct Hp as [Hp | [Hp | Hp]].
    + specialize (IHs var repl Hrepl Hs p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IHy (var + arity) (shift_tm arity 0 (shift_lt_in_tm n_lt 0 repl))
        (marker_annots_no_local_shift_tm _ _ _
          (marker_annots_no_local_shift_lt_in_tm _ _ _ Hrepl)) Hy p Hp).
      rewrite marker_annots_shift_tm in IHy.
      rewrite (marker_annots_shift_lt_in_tm_no_local repl n_lt 0 Hrepl) in IHy.
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IHn var repl Hrepl Hn p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody var repl Hrepl H p Hp.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H as [Hop Hbody].
    apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IHop (var + 2) (shift_tm 2 0 repl)
        (marker_annots_no_local_shift_tm _ _ _ Hrepl) Hop p Hp).
      rewrite marker_annots_shift_tm in IHop.
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IHbody (S var) (shift_tm 1 0 repl)
        (marker_annots_no_local_shift_tm _ _ _ Hrepl) Hbody p Hp).
      rewrite marker_annots_shift_tm in IHbody.
      repeat rewrite List.in_app_iff in *. tauto.
  - intros recv Ss arg IHrecv IHarg var repl Hrepl H p Hp.
    unfold marker_annots_no_local in *. simpl in *.
    apply Forall_app in H as [Hr Ha].
    apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IHrecv var repl Hrepl Hr p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IHarg var repl Hrepl Ha p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
  - intros E m n_beta Ts T_R op_body IHop var repl Hrepl H p Hp.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hp as [Hp | Hp].
    + apply List.in_or_app. right. simpl. left. exact Hp.
    + specialize (IHop (var + 2) (shift_tm 2 0 repl)
        (marker_annots_no_local_shift_tm _ _ _ Hrepl) Htail p Hp).
      rewrite marker_annots_shift_tm in IHop.
      apply List.in_app_or in IHop as [IHop | IHop].
      * apply List.in_or_app. left. exact IHop.
      * apply List.in_or_app. right. simpl. right. exact IHop.
  - intros m T_B T_R t IH var repl Hrepl H p Hp.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hp as [Hp | Hp].
    + apply List.in_or_app. right. simpl. left. exact Hp.
    + specialize (IH var repl Hrepl Htail p Hp).
      apply List.in_app_or in IH as [IH | IH].
      * apply List.in_or_app. left. exact IH.
      * apply List.in_or_app. right. simpl. right. exact IH.
  - intros m T_B T_R b IH var repl Hrepl H p Hp.
    unfold marker_annots_no_local in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hp as [Hp | Hp].
    + apply List.in_or_app. right. simpl. left. exact Hp.
    + specialize (IH (S var) (shift_tm 1 0 repl)
        (marker_annots_no_local_shift_tm _ _ _ Hrepl) Htail p Hp).
      rewrite marker_annots_shift_tm in IH.
      apply List.in_app_or in IH as [IH | IH].
      * apply List.in_or_app. left. exact IH.
      * apply List.in_or_app. right. simpl. right. exact IH.
  - intros var repl Hrepl H p Hp. inversion Hp.
  - intros t ts IHt IHts var repl Hrepl H p Hp.
    unfold marker_annots_list_no_local in *. simpl in *.
    apply Forall_app in H as [Ht Hts].
    apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IHt var repl Hrepl Ht p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IHts var repl Hrepl Hts p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
Qed.

Lemma marker_annots_subst_tm_closed_repl_incl : forall t var repl,
  marker_annots_closed repl ->
  incl (marker_annots (subst_tm var repl t))
       (marker_annots repl ++ marker_annots t).
Proof.
  apply (term_list_ind
    (fun t => forall var repl,
       marker_annots_closed repl ->
       incl (marker_annots (subst_tm var repl t))
            (marker_annots repl ++ marker_annots t))
    (fun ts => forall var repl,
       marker_annots_closed repl ->
       incl (List.concat (List.map marker_annots (List.map (subst_tm var repl) ts)))
            (marker_annots repl ++ List.concat (List.map marker_annots ts)))).
  - intros n var repl Hrepl p Hp. simpl in *.
    destruct (Nat.eqb n var); [apply List.in_or_app; left; exact Hp|].
    destruct (Nat.ltb var n); inversion Hp.
  - intros t1 t2 IH1 IH2 var repl Hrepl p Hp. simpl in *.
    apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IH1 var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IH2 var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
  - intros body T IH var repl Hrepl p Hp. simpl in *.
    specialize (IH (S var) (shift_tm 1 0 repl)
      (marker_annots_closed_shift_tm _ _ _ Hrepl) p Hp).
    rewrite marker_annots_shift_tm in IH. exact IH.
  - intros t T IH var repl Hrepl p Hp. simpl in *.
    exact (IH var repl Hrepl p Hp).
  - intros bound body IH var repl Hrepl p Hp. simpl in *.
    specialize (IH var (shift_ty_in_tm 1 0 repl)
      (marker_annots_closed_shift_ty_in_tm _ _ _ Hrepl) p Hp).
    rewrite (marker_annots_shift_ty_in_tm_closed repl 1 0 Hrepl) in IH. exact IH.
  - intros t l IH var repl Hrepl p Hp. simpl in *.
    exact (IH var repl Hrepl p Hp).
  - intros body IH var repl Hrepl p Hp. simpl in *.
    specialize (IH var (shift_lt_in_tm 1 0 repl)
      (marker_annots_closed_shift_lt_in_tm _ _ _ Hrepl) p Hp).
    rewrite (marker_annots_shift_lt_in_tm_closed repl 1 0 Hrepl) in IH. exact IH.
  - intros K l lts Ts ts IH var repl Hrepl p Hp. simpl in *.
    rewrite subst_tm_go_eq_map in Hp.
    exact (IH var repl Hrepl p Hp).
  - intros scrut tag n_lt arity yes no IHs IHy IHn var repl Hrepl p Hp. simpl in *.
    repeat rewrite List.in_app_iff in Hp. destruct Hp as [Hp | [Hp | Hp]].
    + specialize (IHs var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IHy (var + arity) (shift_tm arity 0 (shift_lt_in_tm n_lt 0 repl))
        (marker_annots_closed_shift_tm _ _ _
          (marker_annots_closed_shift_lt_in_tm _ _ _ Hrepl)) p Hp).
      rewrite marker_annots_shift_tm in IHy.
      rewrite (marker_annots_shift_lt_in_tm_closed repl n_lt 0 Hrepl) in IHy.
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IHn var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody var repl Hrepl p Hp. simpl in *.
    apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IHop (var + 2) (shift_tm 2 0 repl)
        (marker_annots_closed_shift_tm _ _ _ Hrepl) p Hp).
      rewrite marker_annots_shift_tm in IHop.
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IHbody (S var) (shift_tm 1 0 repl)
        (marker_annots_closed_shift_tm _ _ _ Hrepl) p Hp).
      rewrite marker_annots_shift_tm in IHbody.
      repeat rewrite List.in_app_iff in *. tauto.
  - intros recv Ss arg IHrecv IHarg var repl Hrepl p Hp. simpl in *.
    apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IHrecv var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IHarg var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
  - intros E m n_beta Ts T_R op_body IHop var repl Hrepl p Hp. simpl in *.
    destruct Hp as [Hp | Hp].
    + apply List.in_or_app. right. simpl. left. exact Hp.
    + specialize (IHop (var + 2) (shift_tm 2 0 repl)
        (marker_annots_closed_shift_tm _ _ _ Hrepl) p Hp).
      rewrite marker_annots_shift_tm in IHop.
      apply List.in_app_or in IHop as [IHop | IHop].
      * apply List.in_or_app. left. exact IHop.
      * apply List.in_or_app. right. simpl. right. exact IHop.
  - intros m T_B T_R t IH var repl Hrepl p Hp. simpl in *.
    destruct Hp as [Hp | Hp].
    + apply List.in_or_app. right. simpl. left. exact Hp.
    + specialize (IH var repl Hrepl p Hp).
      apply List.in_app_or in IH as [IH | IH].
      * apply List.in_or_app. left. exact IH.
      * apply List.in_or_app. right. simpl. right. exact IH.
  - intros m T_B T_R b IH var repl Hrepl p Hp. simpl in *.
    destruct Hp as [Hp | Hp].
    + apply List.in_or_app. right. simpl. left. exact Hp.
    + specialize (IH (S var) (shift_tm 1 0 repl)
        (marker_annots_closed_shift_tm _ _ _ Hrepl) p Hp).
      rewrite marker_annots_shift_tm in IH.
      apply List.in_app_or in IH as [IH | IH].
      * apply List.in_or_app. left. exact IH.
      * apply List.in_or_app. right. simpl. right. exact IH.
  - intros var repl Hrepl p Hp. inversion Hp.
  - intros t ts IHt IHts var repl Hrepl p Hp. simpl in *.
    apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IHt var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IHts var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
Qed.

Lemma marker_annots_subst_list_tm_no_local_incl : forall vs t,
  Forall marker_annots_no_local vs ->
  marker_annots_no_local t ->
  incl (marker_annots (subst_list_tm vs t))
       (List.concat (List.map marker_annots vs) ++ marker_annots t).
Proof.
  induction vs as [|v rest IH]; intros t Hvs Ht p Hp; simpl in *.
  - exact Hp.
  - inversion Hvs as [|v0 rest0 Hv Hrest Heq]; subst.
    specialize (IH (subst_tm 0 (shift_tm (List.length rest) 0 v) t) Hrest
      (marker_annots_no_local_subst_tm _ _ _
        (marker_annots_no_local_shift_tm _ _ _ Hv) Ht) p Hp).
    apply List.in_app_or in IH as [HinRest | HinSubst].
    + repeat rewrite List.in_app_iff in *. tauto.
    + pose proof (marker_annots_subst_tm_no_local_incl t 0
        (shift_tm (List.length rest) 0 v)
        (marker_annots_no_local_shift_tm _ _ _ Hv) Ht p HinSubst) as Hsingle.
      rewrite marker_annots_shift_tm in Hsingle.
      repeat rewrite List.in_app_iff in *. tauto.
Qed.

Lemma marker_annots_subst_list_tm_closed_repl_incl : forall vs t,
  Forall marker_annots_closed vs ->
  incl (marker_annots (subst_list_tm vs t))
       (List.concat (List.map marker_annots vs) ++ marker_annots t).
Proof.
  induction vs as [|v rest IH]; intros t Hvs p Hp; simpl in *.
  - exact Hp.
  - inversion Hvs as [|v0 rest0 Hv Hrest Heq]; subst.
    specialize (IH (subst_tm 0 (shift_tm (List.length rest) 0 v) t) Hrest p Hp).
    apply List.in_app_or in IH as [HinRest | HinSubst].
    + repeat rewrite List.in_app_iff in *. tauto.
    + pose proof (marker_annots_subst_tm_closed_repl_incl t 0
        (shift_tm (List.length rest) 0 v)
        (marker_annots_closed_shift_tm _ _ _ Hv) p HinSubst) as Hsingle.
      rewrite marker_annots_shift_tm in Hsingle.
      repeat rewrite List.in_app_iff in *. tauto.
Qed.

Lemma marker_annots_no_local_incl : forall sub whole,
  incl (marker_annots sub) (marker_annots whole) ->
  marker_annots_no_local whole -> marker_annots_no_local sub.
Proof.
  intros sub whole Hincl Hwhole.
  unfold marker_annots_no_local in *.
  apply Forall_forall. intros mt Hmt.
  apply Forall_forall with (x := mt) in Hwhole; [exact Hwhole | apply Hincl; exact Hmt].
Qed.

Lemma marker_annots_closed_incl : forall sub whole,
  incl (marker_annots sub) (marker_annots whole) ->
  marker_annots_closed whole -> marker_annots_closed sub.
Proof.
  intros sub whole Hincl Hwhole.
  unfold marker_annots_closed in *.
  apply Forall_forall. intros mt Hmt.
  apply Forall_forall with (x := mt) in Hwhole; [exact Hwhole | apply Hincl; exact Hmt].
Qed.

Lemma marker_annots_closed_cons_incl : forall t m T source,
  ty_ty_closed 0 T ->
  ty_lt_closed 0 T ->
  marker_annots_closed source ->
  incl (marker_annots t) ((m, T) :: marker_annots source) ->
  marker_annots_closed t.
Proof.
  intros t m T source HTy HLt Hsource Hincl.
  unfold marker_annots_closed in *.
  apply Forall_forall. intros mt Hmt.
  specialize (Hincl mt Hmt) as Hin.
  destruct mt as [m0 T0].
  simpl in Hin |- *. destruct Hin as [Hin | Hin].
  - inversion Hin; subst. simpl. split; assumption.
  - exact (proj1 (Forall_forall _ _) Hsource (m0, T0) Hin).
Qed.

Lemma marker_annots_closed_concat : forall ts,
  Forall marker_annots_closed ts ->
  Forall (fun mt => ty_ty_closed 0 (snd mt) /\ ty_lt_closed 0 (snd mt))
    (List.concat (List.map marker_annots ts)).
Proof.
  induction ts as [|t ts IH]; intros Hts; simpl.
  - constructor.
  - inversion Hts as [|t0 ts0 Ht Hrest Heq]; subst.
    apply Forall_app. split.
    + exact Ht.
    + apply IH. exact Hrest.
Qed.

Lemma marker_annots_closed_subst_tm : forall t var repl,
  marker_annots_closed repl ->
  marker_annots_closed t ->
  marker_annots_closed (subst_tm var repl t).
Proof.
  intros t var repl Hrepl Ht.
  unfold marker_annots_closed in *.
  apply Forall_forall. intros mt Hmt.
  pose proof (marker_annots_subst_tm_closed_repl_incl t var repl Hrepl mt Hmt) as Hin.
  apply List.in_app_or in Hin as [Hin | Hin].
  - exact (proj1 (Forall_forall _ _) Hrepl mt Hin).
  - exact (proj1 (Forall_forall _ _) Ht mt Hin).
Qed.

Lemma marker_annots_closed_subst_list_tm : forall vs t,
  Forall marker_annots_closed vs ->
  marker_annots_closed t ->
  marker_annots_closed (subst_list_tm vs t).
Proof.
  intros vs t Hvs Ht.
  unfold marker_annots_closed in *.
  apply Forall_forall. intros mt Hmt.
  pose proof (marker_annots_subst_list_tm_closed_repl_incl vs t Hvs mt Hmt) as Hin.
  apply List.in_app_or in Hin as [Hin | Hin].
  - exact (proj1 (Forall_forall _ _) (marker_annots_closed_concat _ Hvs) mt Hin).
  - exact (proj1 (Forall_forall _ _) Ht mt Hin).
Qed.

Lemma marker_annots_closed_subst_list_ty_in_tm : forall Ss t,
  marker_annots_closed t ->
  marker_annots_closed (subst_list_ty_in_tm Ss t).
Proof.
  intros Ss t Ht. unfold marker_annots_closed in *.
  rewrite marker_annots_subst_list_ty_in_tm_closed by exact Ht. exact Ht.
Qed.

Lemma marker_annots_closed_subst_list_lt_in_tm : forall lts t,
  marker_annots_closed t ->
  marker_annots_closed (subst_list_lt_in_tm lts t).
Proof.
  intros lts t Ht. unfold marker_annots_closed in *.
  rewrite marker_annots_subst_list_lt_in_tm_closed by exact Ht. exact Ht.
Qed.

Lemma marker_annots_list_no_local_Forall : forall ts,
  marker_annots_list_no_local ts -> Forall marker_annots_no_local ts.
Proof.
  induction ts as [|t ts IH]; intros H; constructor.
  - unfold marker_annots_list_no_local, marker_annots_no_local in *.
    simpl in H. apply Forall_app in H as [Ht _]. exact Ht.
  - apply IH. unfold marker_annots_list_no_local in *.
    simpl in H. apply Forall_app in H as [_ Hts]. exact Hts.
Qed.

Lemma marker_annots_list_closed_Forall : forall ts,
  marker_annots_list_closed ts -> Forall marker_annots_closed ts.
Proof.
  induction ts as [|t ts IH]; intros H; constructor.
  - unfold marker_annots_list_closed, marker_annots_closed in *.
    simpl in H. apply Forall_app in H as [Ht _]. exact Ht.
  - apply IH. unfold marker_annots_list_closed in *.
    simpl in H. apply Forall_app in H as [_ Hts]. exact Hts.
Qed.

Lemma marker_annots_beta_incl_no_local : forall body T v,
  marker_annots_no_local body ->
  marker_annots_no_local v ->
  incl (marker_annots (subst_tm 0 v body))
       (marker_annots (term_app (term_lam body T) v)).
Proof.
  intros body T v Hbody Hv p Hp.
  pose proof (marker_annots_subst_tm_no_local_incl body 0 v Hv Hbody p Hp) as Hincl.
  simpl. repeat rewrite List.in_app_iff in *. tauto.
Qed.

Lemma marker_annots_tybeta_incl_no_local : forall bound body T,
  marker_annots_no_local body ->
  incl (marker_annots (subst_ty_in_tm 0 T body))
       (marker_annots (term_ty_app (term_ty_lam bound body) T)).
Proof.
  intros bound body T Hbody p Hp. simpl.
  rewrite marker_annots_subst_ty_in_tm_no_local in Hp; [exact Hp | exact Hbody].
Qed.

Lemma marker_annots_ltbeta_incl_no_local : forall body l,
  marker_annots_no_local body ->
  incl (marker_annots (subst_lt_in_tm 0 l body))
       (marker_annots (term_lt_app (term_lt_lam body) l)).
Proof.
  intros body l Hbody p Hp. simpl.
  rewrite marker_annots_subst_lt_in_tm_no_local in Hp; [exact Hp | exact Hbody].
Qed.

Lemma marker_annots_match_yes_incl_no_local : forall K l lts Ts vs n_lt yes_body no_body,
  marker_annots_list_no_local vs ->
  marker_annots_no_local yes_body ->
  incl (marker_annots (subst_list_tm vs (subst_list_lt_in_tm lts yes_body)))
       (marker_annots (term_match (term_ctor K l lts Ts vs) K n_lt (List.length vs) yes_body no_body)).
Proof.
  intros K l lts Ts vs n_lt yes_body no_body Hvs Hyes p Hp.
  pose proof (marker_annots_subst_list_tm_no_local_incl vs
    (subst_list_lt_in_tm lts yes_body)
    (marker_annots_list_no_local_Forall _ Hvs)
    (marker_annots_no_local_subst_list_lt_in_tm _ _ Hyes) p Hp) as Hincl.
  rewrite marker_annots_subst_list_lt_in_tm_no_local in Hincl; [|exact Hyes].
  simpl. repeat rewrite List.in_app_iff in *. tauto.
Qed.

Lemma marker_annots_match_no_incl : forall K K' l lts Ts vs n_lt arity yes_body no_body,
  incl (marker_annots no_body)
       (marker_annots (term_match (term_ctor K' l lts Ts vs) K n_lt arity yes_body no_body)).
Proof.
  intros K K' l lts Ts vs n_lt arity yes_body no_body p Hp.
  simpl. repeat rewrite List.in_app_iff. tauto.
Qed.

Lemma marker_annots_return_incl : forall m T_B T_R v,
  incl (marker_annots v) (marker_annots (term_handler_m m T_B T_R v)).
Proof.
  intros m T_B T_R v p Hp. simpl. right. exact Hp.
Qed.

Lemma marker_annots_resume_incl_no_local : forall m T_B T_R b v,
  marker_annots_no_local b ->
  marker_annots_no_local v ->
  incl (marker_annots (term_handler_m m T_B T_R (subst_tm 0 v b)))
       (marker_annots (term_app (term_resume m T_B T_R b) v)).
Proof.
  intros m T_B T_R b v Hb Hv p Hp. simpl in Hp |- *.
  destruct Hp as [Hp | Hp].
  - left. exact Hp.
  - pose proof (marker_annots_subst_tm_no_local_incl b 0 v Hv Hb p Hp) as Hincl.
    repeat rewrite List.in_app_iff in *. simpl in *. tauto.
Qed.

Lemma marker_annots_beta_incl_closed : forall body T v,
  marker_annots_closed v ->
  incl (marker_annots (subst_tm 0 v body))
       (marker_annots (term_app (term_lam body T) v)).
Proof.
  intros body T v Hv p Hp.
  pose proof (marker_annots_subst_tm_closed_repl_incl body 0 v Hv p Hp) as Hincl.
  simpl. repeat rewrite List.in_app_iff in *. tauto.
Qed.

Lemma marker_annots_tybeta_incl_closed : forall bound body T,
  marker_annots_closed body ->
  incl (marker_annots (subst_ty_in_tm 0 T body))
       (marker_annots (term_ty_app (term_ty_lam bound body) T)).
Proof.
  intros bound body T Hbody p Hp. simpl.
  rewrite marker_annots_subst_ty_in_tm_closed in Hp; [exact Hp | exact Hbody].
Qed.

Lemma marker_annots_ltbeta_incl_closed : forall body l,
  marker_annots_closed body ->
  incl (marker_annots (subst_lt_in_tm 0 l body))
       (marker_annots (term_lt_app (term_lt_lam body) l)).
Proof.
  intros body l Hbody p Hp. simpl.
  rewrite marker_annots_subst_lt_in_tm_closed in Hp; [exact Hp | exact Hbody].
Qed.

Lemma marker_annots_match_yes_incl_closed : forall K l lts Ts vs n_lt yes_body no_body,
  marker_annots_list_closed vs ->
  marker_annots_closed yes_body ->
  incl (marker_annots (subst_list_tm vs (subst_list_lt_in_tm lts yes_body)))
       (marker_annots (term_match (term_ctor K l lts Ts vs) K n_lt (List.length vs) yes_body no_body)).
Proof.
  intros K l lts Ts vs n_lt yes_body no_body Hvs Hyes p Hp.
  pose proof (marker_annots_subst_list_tm_closed_repl_incl vs
    (subst_list_lt_in_tm lts yes_body)
    (marker_annots_list_closed_Forall _ Hvs) p Hp) as Hincl.
  rewrite marker_annots_subst_list_lt_in_tm_closed in Hincl; [|exact Hyes].
  simpl. repeat rewrite List.in_app_iff in *. tauto.
Qed.

Lemma marker_annots_resume_incl_closed : forall m T_B T_R b v,
  marker_annots_closed v ->
  incl (marker_annots (term_handler_m m T_B T_R (subst_tm 0 v b)))
       (marker_annots (term_app (term_resume m T_B T_R b) v)).
Proof.
  intros m T_B T_R b v Hv p Hp. simpl in Hp |- *.
  destruct Hp as [Hp | Hp].
  - left. exact Hp.
  - pose proof (marker_annots_subst_tm_closed_repl_incl b 0 v Hv p Hp) as Hincl.
    repeat rewrite List.in_app_iff in *. simpl in *. tauto.
Qed.

Lemma head_step_marker_annots_incl_no_local_with_perform :
  forall r r',
    r -->h r' ->
    marker_annots_no_local r ->
    (forall E_tag m n_beta Ts T_B T_R op_body Ss v P,
      value v -> pure_ectx_m m P ->
      marker_annots_no_local
        (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))) ->
      incl
        (marker_annots
          (subst_list_tm [v; term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))]
            (subst_list_ty_in_tm Ss op_body)))
        (marker_annots
          (term_handler_m m T_B T_R
            (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))))) ->
    incl (marker_annots r') (marker_annots r).
Proof.
  intros r r' Hstep Hnl Hperform.
  inversion Hstep; subst.
  - (* H_Beta *)
    simpl in Hnl. apply Forall_app in Hnl as [Hbody Hv].
    apply marker_annots_beta_incl_no_local; assumption.
  - (* H_TyBeta *)
    apply marker_annots_tybeta_incl_no_local. exact Hnl.
  - (* H_LtBeta *)
    apply marker_annots_ltbeta_incl_no_local. exact Hnl.
  - (* H_MatchYes *)
    simpl in Hnl. apply Forall_app in Hnl as [Hvs Hyn].
    apply Forall_app in Hyn as [Hyes _].
    apply marker_annots_match_yes_incl_no_local; assumption.
  - (* H_MatchNo *)
    apply marker_annots_match_no_incl.
  - (* H_Return *)
    apply marker_annots_return_incl.
  - (* H_Perform *)
    eapply Hperform; eauto.
  - (* H_Resume *)
    simpl in Hnl. apply Forall_app in Hnl as [Hresume Hv].
    inversion Hresume as [|mt rest Hhead Hb]; subst.
    apply marker_annots_resume_incl_no_local; assumption.
Qed.

Lemma head_step_preserves_marker_types_safe_no_local_with_perform :
  forall r r',
    r -->h r' ->
    marker_annots_no_local r ->
    marker_types_safe r ->
    (forall E_tag m n_beta Ts T_B T_R op_body Ss v P,
      value v -> pure_ectx_m m P ->
      marker_annots_no_local
        (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))) ->
      marker_types_safe
        (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))) ->
      marker_types_safe
        (subst_list_tm [v; term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))]
          (subst_list_ty_in_tm Ss op_body))) ->
    marker_types_safe r'.
Proof.
  intros r r' Hstep Hnl Hsafe Hperform.
  inversion Hstep; subst.
  - (* H_Beta *)
    simpl in Hnl. apply Forall_app in Hnl as [Hbody Hv].
    eapply marker_types_safe_incl; [apply marker_annots_beta_incl_no_local; eauto | exact Hsafe].
  - (* H_TyBeta *)
    eapply marker_types_safe_incl; [apply marker_annots_tybeta_incl_no_local; exact Hnl | exact Hsafe].
  - (* H_LtBeta *)
    eapply marker_types_safe_incl; [apply marker_annots_ltbeta_incl_no_local; exact Hnl | exact Hsafe].
  - (* H_MatchYes *)
    simpl in Hnl. apply Forall_app in Hnl as [Hvs Hyn].
    apply Forall_app in Hyn as [Hyes _].
    eapply marker_types_safe_incl; [apply marker_annots_match_yes_incl_no_local; eauto | exact Hsafe].
  - (* H_MatchNo *)
    eapply marker_types_safe_incl; [apply marker_annots_match_no_incl | exact Hsafe].
  - (* H_Return *)
    eapply marker_types_safe_incl; [apply marker_annots_return_incl | exact Hsafe].
  - (* H_Perform *)
    eapply Hperform; eauto.
  - (* H_Resume *)
    simpl in Hnl. apply Forall_app in Hnl as [Hresume Hv].
    inversion Hresume as [|mt rest Hhead Hb]; subst.
    eapply marker_types_safe_incl; [apply marker_annots_resume_incl_no_local; eauto | exact Hsafe].
Qed.

Lemma incl_app_compat_local : forall (A : Type) (xs xs' ys ys' : list A),
  incl xs xs' -> incl ys ys' -> incl (xs ++ ys) (xs' ++ ys').
Proof.
  intros A xs xs' ys ys' Hxs Hys p Hp.
  apply List.in_app_or in Hp as [Hp | Hp].
  - apply List.in_or_app. left. apply Hxs. exact Hp.
  - apply List.in_or_app. right. apply Hys. exact Hp.
Qed.

Lemma incl_cons_same_local : forall (A : Type) (x : A) xs ys,
  incl xs ys -> incl (x :: xs) (x :: ys).
Proof.
  intros A x xs ys H p Hp. simpl in Hp |- *.
  destruct Hp as [Hp | Hp]; [left; exact Hp | right; apply H; exact Hp].
Qed.

Lemma marker_annots_ctor_replace_incl : forall vs t t' ts,
  incl (marker_annots t') (marker_annots t) ->
  incl (List.concat (List.map marker_annots (vs ++ t' :: ts)))
       (List.concat (List.map marker_annots (vs ++ t :: ts))).
Proof.
  induction vs as [|v vs IH]; intros t t' ts Hincl.
  - simpl. apply incl_app_compat_local; [exact Hincl | apply incl_refl].
  - simpl. apply incl_app_compat_local; [apply incl_refl | apply IH; exact Hincl].
Qed.

Lemma marker_annots_ctor_replace_incl_cons : forall vs t t' ts new,
  incl (marker_annots t') (new :: marker_annots t) ->
  incl (List.concat (List.map marker_annots (vs ++ t' :: ts)))
       (new :: List.concat (List.map marker_annots (vs ++ t :: ts))).
Proof.
  induction vs as [|v vs IH]; intros t t' ts new Hincl p Hp; simpl in *.
  - apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (Hincl p Hp). simpl in Hincl. destruct Hincl as [Hnew | Hold].
      * left. exact Hnew.
      * right. apply List.in_or_app. left. exact Hold.
    + right. apply List.in_or_app. right. exact Hp.
  - apply List.in_app_or in Hp as [Hp | Hp].
    + right. apply List.in_or_app. left. exact Hp.
    + specialize (IH t t' ts new Hincl p Hp). simpl in IH. destruct IH as [Hnew | Hold].
      * left. exact Hnew.
      * right. apply List.in_or_app. right. exact Hold.
Qed.

Lemma marker_annots_plug_replace_incl : forall E r r',
  incl (marker_annots r') (marker_annots r) ->
  incl (marker_annots (plug E r')) (marker_annots (plug E r)).
Proof.
  induction E; intros r r' Hincl; simpl.
  - exact Hincl.
  - apply incl_app_compat_local; [apply IHE; exact Hincl | apply incl_refl].
  - apply incl_app_compat_local; [apply incl_refl | apply IHE; exact Hincl].
  - apply IHE. exact Hincl.
  - apply IHE. exact Hincl.
  - apply marker_annots_ctor_replace_incl. apply IHE. exact Hincl.
  - apply incl_app_compat_local; [apply IHE; exact Hincl | apply incl_refl].
  - apply incl_cons_same_local. apply IHE. exact Hincl.
  - apply incl_app_compat_local; [apply IHE; exact Hincl | apply incl_refl].
  - apply incl_app_compat_local; [apply incl_refl | apply IHE; exact Hincl].
Qed.

Lemma marker_annots_plug_replace_incl_cons : forall E r r' new,
  incl (marker_annots r') (new :: marker_annots r) ->
  incl (marker_annots (plug E r')) (new :: marker_annots (plug E r)).
Proof.
  induction E; intros r r' new Hincl p Hp; simpl in *.
  - apply Hincl. exact Hp.
  - apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IHE r r' new Hincl p Hp). simpl in IHE. destruct IHE as [Hnew | Hold].
      * left. exact Hnew.
      * right. apply List.in_or_app. left. exact Hold.
    + right. apply List.in_or_app. right. exact Hp.
  - apply List.in_app_or in Hp as [Hp | Hp].
    + right. apply List.in_or_app. left. exact Hp.
    + specialize (IHE r r' new Hincl p Hp). simpl in IHE. destruct IHE as [Hnew | Hold].
      * left. exact Hnew.
      * right. apply List.in_or_app. right. exact Hold.
  - exact (IHE r r' new Hincl p Hp).
  - exact (IHE r r' new Hincl p Hp).
  - exact (marker_annots_ctor_replace_incl_cons _ _ _ _ _
      (IHE r r' new Hincl) p Hp).
  - apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IHE r r' new Hincl p Hp). simpl in IHE. destruct IHE as [Hnew | Hold].
      * left. exact Hnew.
      * right. apply List.in_or_app. left. exact Hold.
    + right. apply List.in_or_app. right. exact Hp.
  - destruct Hp as [Hp | Hp].
    + right. left. exact Hp.
    + specialize (IHE r r' new Hincl p Hp). simpl in IHE. destruct IHE as [Hnew | Hold].
      * left. exact Hnew.
      * right. right. exact Hold.
  - apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IHE r r' new Hincl p Hp). simpl in IHE. destruct IHE as [Hnew | Hold].
      * left. exact Hnew.
      * right. apply List.in_or_app. left. exact Hold.
    + right. apply List.in_or_app. right. exact Hp.
  - apply List.in_app_or in Hp as [Hp | Hp].
    + right. apply List.in_or_app. left. exact Hp.
    + specialize (IHE r r' new Hincl p Hp). simpl in IHE. destruct IHE as [Hnew | Hold].
      * left. exact Hnew.
      * right. apply List.in_or_app. right. exact Hold.
Qed.

Lemma marker_annots_plug_var_incl : forall E r n,
  incl (marker_annots (plug E (term_var n))) (marker_annots (plug E r)).
Proof.
  intros E r n. apply marker_annots_plug_replace_incl.
  intros p Hp. inversion Hp.
Qed.

Lemma marker_annots_shift_ectx_tm_plug_var_incl : forall E r amount cutoff n,
  incl (marker_annots (plug (shift_ectx_tm amount cutoff E) (term_var n)))
       (marker_annots (plug E r)).
Proof.
  intros E r amount cutoff n p Hp.
  rewrite marker_annots_shift_ectx_tm in Hp.
  eapply marker_annots_plug_var_incl. exact Hp.
Qed.

Lemma marker_types_safe_plug_replace_incl : forall E r r',
  incl (marker_annots r') (marker_annots r) ->
  marker_types_safe (plug E r) ->
  marker_types_safe (plug E r').
Proof.
  intros E r r' Hincl Hsafe.
  eapply marker_types_safe_incl; [apply marker_annots_plug_replace_incl; exact Hincl | exact Hsafe].
Qed.

Lemma markers_in_ctor_eq : forall K l lts Ts ts,
  markers_in (term_ctor K l lts Ts ts) = markers_in_list ts.
Proof.
  intros K l lts Ts ts. simpl.
  induction ts as [|u rest IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma marker_annots_marker_in : forall t m T,
  In (m, T) (marker_annots t) -> In m (markers_in t).
Proof.
  apply (term_list_ind
    (fun t => forall m T, In (m, T) (marker_annots t) -> In m (markers_in t))
    (fun ts => forall m T,
       In (m, T) (List.concat (List.map marker_annots ts)) ->
       In m (markers_in_list ts))).
  - intros n m T H. inversion H.
  - intros t1 t2 IH1 IH2 m T H. simpl in *.
    apply List.in_app_or in H as [H | H].
    + apply List.in_or_app. left. apply IH1 with (T := T). exact H.
    + apply List.in_or_app. right. apply IH2 with (T := T). exact H.
  - intros body T0 IH m T H. simpl in *. apply IH with (T := T). exact H.
  - intros t T0 IH m T H. simpl in *. apply IH with (T := T). exact H.
  - intros bound body IH m T H. simpl in *. apply IH with (T := T). exact H.
  - intros t l IH m T H. simpl in *. apply IH with (T := T). exact H.
  - intros body IH m T H. simpl in *. apply IH with (T := T). exact H.
  - intros K l lts Ts ts IH m T H. rewrite markers_in_ctor_eq. apply IH with (T := T). exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn m T H. simpl in *.
    repeat rewrite List.in_app_iff in H. destruct H as [H | [H | H]].
    + apply List.in_or_app. left. apply IHs with (T := T). exact H.
    + apply List.in_or_app. right. apply List.in_or_app. left. apply IHy with (T := T). exact H.
    + apply List.in_or_app. right. apply List.in_or_app. right. apply IHn with (T := T). exact H.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody m T H. simpl in *.
    apply List.in_app_or in H as [H | H].
    + apply List.in_or_app. left. apply IHop with (T := T). exact H.
    + apply List.in_or_app. right. apply IHbody with (T := T). exact H.
  - intros recv Ss arg IHrecv IHarg m T H. simpl in *.
    apply List.in_app_or in H as [H | H].
    + apply List.in_or_app. left. apply IHrecv with (T := T). exact H.
    + apply List.in_or_app. right. apply IHarg with (T := T). exact H.
  - intros E m0 n_beta Ts T_R op_body IHop m T H. simpl in *.
    destruct H as [H | H].
    + injection H; intros; subst. left. reflexivity.
    + right. apply IHop with (T := T). exact H.
  - intros m0 T_B T_R body IH m T H. simpl in *.
    destruct H as [H | H].
    + injection H; intros; subst. left. reflexivity.
    + right. apply IH with (T := T). exact H.
  - intros m0 T_B T_R body IH m T H. simpl in *.
    destruct H as [H | H].
    + injection H; intros; subst. left. reflexivity.
    + right. apply IH with (T := T). exact H.
  - intros m T H. inversion H.
  - intros t ts IHt IHts m T H. simpl in *.
    apply List.in_app_or in H as [H | H].
    + apply List.in_or_app. left. apply IHt with (T := T). exact H.
    + apply List.in_or_app. right. apply IHts with (T := T). exact H.
Qed.

Lemma marker_types_safe_fresh_cons_incl : forall source t m T,
  ~ In m (markers_in source) ->
  marker_types_safe source ->
  incl (marker_annots t) ((m, T) :: marker_annots source) ->
  marker_types_safe t.
Proof.
  intros source t m T Hfresh Hsafe Hincl m0 U V HU HV.
  specialize (Hincl _ HU) as HU'.
  specialize (Hincl _ HV) as HV'.
  simpl in HU', HV'.
  destruct HU' as [HU' | HU']; destruct HV' as [HV' | HV'].
  - injection HU'; injection HV'; intros; subst. reflexivity.
  - injection HU'; intros; subst. exfalso. apply Hfresh.
    eapply marker_annots_marker_in. exact HV'.
  - injection HV'; intros; subst. exfalso. apply Hfresh.
    eapply marker_annots_marker_in. exact HU'.
  - eapply Hsafe; eauto.
Qed.

Lemma marker_annots_closed_cap : forall E m n_beta Ts T_R op_body,
  ty_ty_closed 0 T_R ->
  ty_lt_closed 0 T_R ->
  marker_annots_closed op_body ->
  marker_annots_closed (term_cap E m n_beta Ts T_R op_body).
Proof.
  intros E m n_beta Ts T_R op_body HTy HLt Hop.
  unfold marker_annots_closed in *. simpl. constructor.
  - simpl. split; assumption.
  - exact Hop.
Qed.

Lemma marker_annots_handle_alloc_redex_incl_closed :
  forall E_tag n_beta Ts T_B T_R op_body body m,
    ty_ty_closed 0 T_R ->
    ty_lt_closed 0 T_R ->
    marker_annots_closed op_body ->
    incl
      (marker_annots
        (term_handler_m m T_B T_R
          (subst_tm 0 (term_cap E_tag m n_beta Ts T_R op_body) body)))
      ((m, T_R) :: marker_annots (term_handle E_tag n_beta Ts T_B T_R op_body body)).
Proof.
  intros E_tag n_beta Ts T_B T_R op_body body m HTy HLt Hop p Hp.
  simpl in Hp |- *.
  destruct Hp as [Hp | Hp].
  - left. exact Hp.
  - pose proof (marker_annots_closed_cap E_tag m n_beta Ts T_R op_body HTy HLt Hop) as Hcap.
    pose proof (marker_annots_subst_tm_closed_repl_incl body 0
      (term_cap E_tag m n_beta Ts T_R op_body) Hcap p Hp) as Hincl.
    simpl in Hincl. repeat rewrite List.in_app_iff in *. tauto.
Qed.

Lemma marker_types_safe_handle_alloc_closed :
  forall E E_tag n_beta Ts T_B T_R op_body body m,
    ~ In m (markers_in (plug E (term_handle E_tag n_beta Ts T_B T_R op_body body))) ->
    ty_ty_closed 0 T_R ->
    ty_lt_closed 0 T_R ->
    marker_annots_closed op_body ->
    marker_types_safe (plug E (term_handle E_tag n_beta Ts T_B T_R op_body body)) ->
    marker_types_safe
      (plug E
        (term_handler_m m T_B T_R
          (subst_tm 0 (term_cap E_tag m n_beta Ts T_R op_body) body))).
Proof.
  intros E E_tag n_beta Ts T_B T_R op_body body m Hfresh HTy HLt Hop Hsafe.
  eapply marker_types_safe_fresh_cons_incl with
    (source := plug E (term_handle E_tag n_beta Ts T_B T_R op_body body))
    (m := m) (T := T_R); eauto.
  apply marker_annots_plug_replace_incl_cons.
  apply marker_annots_handle_alloc_redex_incl_closed; assumption.
Qed.

Lemma marker_types_safe_cap_fresh : forall E m n_beta Ts T_R op_body,
  ~ In m (markers_in op_body) ->
  marker_types_safe op_body ->
  marker_types_safe (term_cap E m n_beta Ts T_R op_body).
Proof.
  intros E m n_beta Ts T_R op_body Hfresh Hsafe m0 T U HT HU.
  simpl in HT, HU.
  destruct HT as [HT | HT]; destruct HU as [HU | HU].
  - injection HT; injection HU; intros; subst. reflexivity.
  - injection HT; intros; subst. exfalso. apply Hfresh.
    eapply marker_annots_marker_in. exact HU.
  - injection HU; intros; subst. exfalso. apply Hfresh.
    eapply marker_annots_marker_in. exact HT.
  - eapply Hsafe; eauto.
Qed.

Lemma marker_types_safe_handler_m_fresh : forall m T_B T_R body,
  ~ In m (markers_in body) ->
  marker_types_safe body ->
  marker_types_safe (term_handler_m m T_B T_R body).
Proof.
  intros m T_B T_R body Hfresh Hsafe m0 T U HT HU.
  simpl in HT, HU.
  destruct HT as [HT | HT]; destruct HU as [HU | HU].
  - injection HT; injection HU; intros; subst. reflexivity.
  - injection HT; intros; subst. exfalso. apply Hfresh.
    eapply marker_annots_marker_in. exact HU.
  - injection HU; intros; subst. exfalso. apply Hfresh.
    eapply marker_annots_marker_in. exact HT.
  - eapply Hsafe; eauto.
Qed.

Lemma marker_types_safe_resume_fresh : forall m T_B T_R body,
  ~ In m (markers_in body) ->
  marker_types_safe body ->
  marker_types_safe (term_resume m T_B T_R body).
Proof.
  intros m T_B T_R body Hfresh Hsafe m0 T U HT HU.
  simpl in HT, HU.
  destruct HT as [HT | HT]; destruct HU as [HU | HU].
  - injection HT; injection HU; intros; subst. reflexivity.
  - injection HT; intros; subst. exfalso. apply Hfresh.
    eapply marker_annots_marker_in. exact HU.
  - injection HU; intros; subst. exfalso. apply Hfresh.
    eapply marker_annots_marker_in. exact HT.
  - eapply Hsafe; eauto.
Qed.

Lemma marker_annots_ctor_focus_in : forall p vs t ts,
  In p (marker_annots t) ->
  In p (List.concat (List.map marker_annots (vs ++ t :: ts))).
Proof.
  intros p vs. induction vs as [|v vs IH]; intros t ts Hin; simpl.
  - apply List.in_or_app. left. exact Hin.
  - apply List.in_or_app. right. apply IH. exact Hin.
Qed.

Lemma marker_annots_plug_in : forall E hole p,
  In p (marker_annots hole) ->
  In p (marker_annots (plug E hole)).
Proof.
  induction E; intros hole p Hin; simpl.
  - exact Hin.
  - apply List.in_or_app. left. apply IHE. exact Hin.
  - apply List.in_or_app. right. apply IHE. exact Hin.
  - apply IHE. exact Hin.
  - apply IHE. exact Hin.
  - apply marker_annots_ctor_focus_in. apply IHE. exact Hin.
  - apply List.in_or_app. left. apply IHE. exact Hin.
  - simpl. right. apply IHE. exact Hin.
  - apply List.in_or_app. left. apply IHE. exact Hin.
  - apply List.in_or_app. right. apply IHE. exact Hin.
Qed.

Lemma marker_types_safe_handle_alloc_closed_from_no_local :
  forall E E_tag n_beta Ts T_B T_R op_body body m,
    ~ In m (markers_in (plug E (term_handle E_tag n_beta Ts T_B T_R op_body body))) ->
    ty_ty_closed 0 T_R ->
    ty_lt_closed 0 T_R ->
    marker_annots_no_local (plug E (term_handle E_tag n_beta Ts T_B T_R op_body body)) ->
    marker_types_safe (plug E (term_handle E_tag n_beta Ts T_B T_R op_body body)) ->
    marker_types_safe
      (plug E
        (term_handler_m m T_B T_R
          (subst_tm 0 (term_cap E_tag m n_beta Ts T_R op_body) body))).
Proof.
  intros E E_tag n_beta Ts T_B T_R op_body body m Hfresh HTy HLt Hnl Hsafe.
  eapply marker_types_safe_handle_alloc_closed; try eassumption.
  apply marker_annots_no_local_closed.
  eapply marker_annots_no_local_incl; [|exact Hnl].
  intros p Hp. apply marker_annots_plug_in. simpl. apply List.in_or_app. left. exact Hp.
Qed.

Lemma step_preserves_marker_types_safe_no_local_with_hard_cases :
  forall t t',
    t ==> t' ->
    marker_annots_no_local t ->
    marker_types_safe t ->
    (forall E_tag m n_beta Ts T_B T_R op_body Ss v P,
      value v -> pure_ectx_m m P ->
      marker_annots_no_local
        (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))) ->
      incl
        (marker_annots
          (subst_list_tm [v; term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))]
            (subst_list_ty_in_tm Ss op_body)))
        (marker_annots
          (term_handler_m m T_B T_R
            (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))))) ->
    (forall E E_tag n_beta Ts T_B T_R op_body body m,
      ectx_wf E ->
      ~ In m (markers_in (plug E (term_handle E_tag n_beta Ts T_B T_R op_body body))) ->
      marker_annots_no_local (plug E (term_handle E_tag n_beta Ts T_B T_R op_body body)) ->
      marker_types_safe (plug E (term_handle E_tag n_beta Ts T_B T_R op_body body)) ->
      marker_types_safe
        (plug E
          (term_handler_m m T_B T_R
            (subst_tm 0 (term_cap E_tag m n_beta Ts T_R op_body) body)))) ->
    marker_types_safe t'.
Proof.
  intros t t' Hstep Hnl Hsafe Hperform Hhandle.
  inversion Hstep as
    [E r r' Hwf Hhead Heq1 Heq2
    | E E_tag n_beta Ts T_B T_R op_body body m Hwf Hfresh Heq1 Heq2]; subst.
  - assert (Hnl_r : marker_annots_no_local r).
    { eapply marker_annots_no_local_incl.
      - intros p Hp. apply marker_annots_plug_in. exact Hp.
      - exact Hnl. }
    pose proof (head_step_marker_annots_incl_no_local_with_perform
      r r' Hhead Hnl_r Hperform) as Hincl.
    eapply marker_types_safe_plug_replace_incl; [exact Hincl | exact Hsafe].
  - eapply Hhandle; eauto.
Qed.

Lemma step_preserves_marker_types_safe_no_local_with_perform_and_handle_closed :
  forall t t',
    t ==> t' ->
    marker_annots_no_local t ->
    marker_types_safe t ->
    (forall E_tag m n_beta Ts T_B T_R op_body Ss v P,
      value v -> pure_ectx_m m P ->
      marker_annots_no_local
        (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))) ->
      incl
        (marker_annots
          (subst_list_tm [v; term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))]
            (subst_list_ty_in_tm Ss op_body)))
        (marker_annots
          (term_handler_m m T_B T_R
            (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))))) ->
    (forall E E_tag n_beta Ts T_B T_R op_body body (m : marker),
      t = plug E (term_handle E_tag n_beta Ts T_B T_R op_body body) ->
      ty_ty_closed 0 T_R /\ ty_lt_closed 0 T_R) ->
    marker_types_safe t'.
Proof.
  intros t t' Hstep Hnl Hsafe Hperform Hhandle_closed.
  inversion Hstep as
    [E r r' Hwf Hhead Heq1 Heq2
    | E E_tag n_beta Ts T_B T_R op_body body m Hwf Hfresh Heq1 Heq2]; subst.
  - assert (Hnl_r : marker_annots_no_local r).
    { eapply marker_annots_no_local_incl.
      - intros p Hp. apply marker_annots_plug_in. exact Hp.
      - exact Hnl. }
    pose proof (head_step_marker_annots_incl_no_local_with_perform
      r r' Hhead Hnl_r Hperform) as Hincl.
    eapply marker_types_safe_plug_replace_incl; [exact Hincl | exact Hsafe].
  - destruct (Hhandle_closed E E_tag n_beta Ts T_B T_R op_body body m eq_refl) as [HTy HLt].
    eapply marker_types_safe_handle_alloc_closed_from_no_local; eauto.
Qed.

Lemma step_preserves_marker_types_safe_no_local_typed_with_perform :
  forall Γ t t' T,
    eval_ctx Γ ->
    Γ ⊢ₜ t : T ->
    t ==> t' ->
    marker_annots_no_local t ->
    marker_types_safe t ->
    (forall E_tag m n_beta Ts T_B T_R op_body Ss v P,
      value v -> pure_ectx_m m P ->
      marker_annots_no_local
        (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))) ->
      incl
        (marker_annots
          (subst_list_tm [v; term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))]
            (subst_list_ty_in_tm Ss op_body)))
        (marker_annots
          (term_handler_m m T_B T_R
            (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))))) ->
    marker_types_safe t'.
Proof.
  intros Γ t t' T Hec Hty Hstep Hnl Hsafe Hperform.
  eapply step_preserves_marker_types_safe_no_local_with_perform_and_handle_closed; eauto.
  intros E E_tag n_beta Ts T_B T_R op_body body m Heq. subst.
  eapply handle_result_closed_from_plug_typing_for_markers; eauto.
Qed.

Lemma marker_types_ok_handler_perform_annotation_match :
  forall m T_B T_H E_tag n_beta Ts T_R op_body Ss v P,
    marker_types_safe
      (term_handler_m m T_B T_H
        (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))) ->
    T_R = T_H.
Proof.
  intros m T_B T_H E_tag n_beta Ts T_R op_body Ss v P Hok.
  symmetry.
  eapply (marker_types_safe_ok _ Hok m T_H T_R).
  - simpl. left. reflexivity.
  - simpl. right. apply marker_annots_plug_in.
    simpl. left. reflexivity.
Qed.

Lemma marker_annots_perform_reduct_incl_no_local :
  forall E_tag m n_beta Ts T_B T_R op_body Ss v P,
    marker_annots_no_local
      (term_handler_m m T_B T_R
        (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))) ->
    incl
      (marker_annots
        (subst_list_tm [v; term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))]
          (subst_list_ty_in_tm Ss op_body)))
      (marker_annots
        (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v)))).
Proof.
  intros E_tag m n_beta Ts T_B T_R op_body Ss v P Hnl.
  set (perform_redex := term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v).
  set (source := term_handler_m m T_B T_R (plug P perform_redex)).
  set (resume := term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))).
  assert (HTRnl : no_local_ty T_R = true).
  { unfold marker_annots_no_local in Hnl. subst source perform_redex resume. simpl in Hnl.
    inversion Hnl as [|mt rest Hhead Htail]; subst. exact Hhead. }
  assert (Hop_nl : marker_annots_no_local op_body).
  { subst source perform_redex resume.
    eapply marker_annots_no_local_incl; [|exact Hnl].
    intros p Hp. simpl. right. apply marker_annots_plug_in.
    simpl. right. apply List.in_or_app. left. exact Hp. }
  assert (Hv_nl : marker_annots_no_local v).
  { subst source perform_redex resume.
    eapply marker_annots_no_local_incl; [|exact Hnl].
    intros p Hp. simpl. right. apply marker_annots_plug_in.
    simpl. right. apply List.in_or_app. right. exact Hp. }
  assert (Hresume_nl : marker_annots_no_local resume).
  { subst source perform_redex resume. unfold marker_annots_no_local. simpl. constructor.
    - exact HTRnl.
    - eapply marker_annots_no_local_incl; [|exact Hnl].
      intros p Hp. simpl. right.
      eapply marker_annots_shift_ectx_tm_plug_var_incl with (r := term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v).
      exact Hp. }
  assert (Hvincl : incl (marker_annots v) (marker_annots source)).
  { subst source perform_redex resume. intros p Hp. simpl. right. apply marker_annots_plug_in.
    simpl. right. apply List.in_or_app. right. exact Hp. }
  assert (Hopincl : incl (marker_annots op_body) (marker_annots source)).
  { subst source perform_redex resume. intros p Hp. simpl. right. apply marker_annots_plug_in.
    simpl. right. apply List.in_or_app. left. exact Hp. }
  assert (Hresincl : incl (marker_annots resume) (marker_annots source)).
  { subst source perform_redex resume. intros p Hp. simpl in Hp. destruct Hp as [Hp | Hp].
    - simpl. left. exact Hp.
    - simpl. right.
      eapply marker_annots_shift_ectx_tm_plug_var_incl with (r := term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v).
      exact Hp. }
  intros p Hp.
  pose proof (marker_annots_subst_list_tm_no_local_incl
    [v; resume] (subst_list_ty_in_tm Ss op_body)
    (Forall_cons _ Hv_nl (Forall_cons _ Hresume_nl (Forall_nil _)))
    (marker_annots_no_local_subst_list_ty_in_tm Ss op_body Hop_nl)
    p Hp) as Hincl.
  subst resume source perform_redex.
  rewrite marker_annots_subst_list_ty_in_tm_no_local in Hincl by exact Hop_nl.
  simpl in Hincl. repeat rewrite List.app_nil_r in Hincl.
  repeat rewrite List.in_app_iff in Hincl.
  destruct Hincl as [[HvIn | HresIn] | HopIn].
  - apply Hvincl. exact HvIn.
  - apply Hresincl. exact HresIn.
  - apply Hopincl. exact HopIn.
Qed.

Lemma step_preserves_marker_types_safe_no_local_typed : forall Γ t t' T,
  eval_ctx Γ -> marker_annots_no_local t -> marker_types_safe t -> Γ ⊢ₜ t : T ->
  t ==> t' -> marker_types_safe t'.
Proof.
  intros Γ t t' T Hec Hnl Hsafe Hty Hstep.
  eapply step_preserves_marker_types_safe_no_local_typed_with_perform; eauto.
  intros E_tag m n_beta Ts T_B T_R op_body Ss v P Hval Hpure Hnl_redex.
  apply marker_annots_perform_reduct_incl_no_local. exact Hnl_redex.
Qed.

Lemma head_step_marker_annots_incl_closed_with_perform :
  forall r r',
    r -->h r' ->
    marker_annots_closed r ->
    (forall E_tag m n_beta Ts T_B T_R op_body Ss v P,
      value v -> pure_ectx_m m P ->
      marker_annots_closed
        (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))) ->
      incl
        (marker_annots
          (subst_list_tm [v; term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))]
            (subst_list_ty_in_tm Ss op_body)))
        (marker_annots
          (term_handler_m m T_B T_R
            (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))))) ->
    incl (marker_annots r') (marker_annots r).
Proof.
  intros r r' Hstep Hclosed Hperform.
  inversion Hstep; subst.
  - (* H_Beta *)
    simpl in Hclosed. apply Forall_app in Hclosed as [_ Hv].
    apply marker_annots_beta_incl_closed. exact Hv.
  - (* H_TyBeta *)
    apply marker_annots_tybeta_incl_closed. exact Hclosed.
  - (* H_LtBeta *)
    apply marker_annots_ltbeta_incl_closed. exact Hclosed.
  - (* H_MatchYes *)
    simpl in Hclosed. apply Forall_app in Hclosed as [Hvs Hyn].
    apply Forall_app in Hyn as [Hyes _].
    apply marker_annots_match_yes_incl_closed; assumption.
  - (* H_MatchNo *)
    apply marker_annots_match_no_incl.
  - (* H_Return *)
    apply marker_annots_return_incl.
  - (* H_Perform *)
    eapply Hperform; eauto.
  - (* H_Resume *)
    simpl in Hclosed. apply Forall_app in Hclosed as [_ Hv].
    apply marker_annots_resume_incl_closed. exact Hv.
Qed.

Lemma step_preserves_marker_types_safe_closed_with_perform_and_handle_closed :
  forall t t',
    t ==> t' ->
    marker_annots_closed t ->
    marker_types_safe t ->
    (forall E_tag m n_beta Ts T_B T_R op_body Ss v P,
      value v -> pure_ectx_m m P ->
      marker_annots_closed
        (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))) ->
      incl
        (marker_annots
          (subst_list_tm [v; term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))]
            (subst_list_ty_in_tm Ss op_body)))
        (marker_annots
          (term_handler_m m T_B T_R
            (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))))) ->
    (forall E E_tag n_beta Ts T_B T_R op_body body (m : marker),
      t = plug E (term_handle E_tag n_beta Ts T_B T_R op_body body) ->
      ty_ty_closed 0 T_R /\ ty_lt_closed 0 T_R) ->
    marker_types_safe t'.
Proof.
  intros t t' Hstep Hclosed Hsafe Hperform Hhandle_closed.
  inversion Hstep as
    [E r r' Hwf Hhead Heq1 Heq2
    | E E_tag n_beta Ts T_B T_R op_body body m Hwf Hfresh Heq1 Heq2]; subst.
  - assert (Hclosed_r : marker_annots_closed r).
    { eapply marker_annots_closed_incl.
      - intros p Hp. apply marker_annots_plug_in. exact Hp.
      - exact Hclosed. }
    pose proof (head_step_marker_annots_incl_closed_with_perform
      r r' Hhead Hclosed_r Hperform) as Hincl.
    eapply marker_types_safe_plug_replace_incl; [exact Hincl | exact Hsafe].
  - destruct (Hhandle_closed E E_tag n_beta Ts T_B T_R op_body body m eq_refl) as [HTy HLt].
    eapply marker_types_safe_handle_alloc_closed; eauto.
    eapply marker_annots_closed_incl; [|exact Hclosed].
    intros p Hp. apply marker_annots_plug_in. simpl. apply List.in_or_app. left. exact Hp.
Qed.

Lemma step_preserves_marker_types_safe_closed_typed_with_perform :
  forall Γ t t' T,
    eval_ctx Γ ->
    Γ ⊢ₜ t : T ->
    t ==> t' ->
    marker_annots_closed t ->
    marker_types_safe t ->
    (forall E_tag m n_beta Ts T_B T_R op_body Ss v P,
      value v -> pure_ectx_m m P ->
      marker_annots_closed
        (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))) ->
      incl
        (marker_annots
          (subst_list_tm [v; term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))]
            (subst_list_ty_in_tm Ss op_body)))
        (marker_annots
          (term_handler_m m T_B T_R
            (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))))) ->
    marker_types_safe t'.
Proof.
  intros Γ t t' T Hec Hty Hstep Hclosed Hsafe Hperform.
  eapply step_preserves_marker_types_safe_closed_with_perform_and_handle_closed; eauto.
  intros E E_tag n_beta Ts T_B T_R op_body body m Heq. subst.
  eapply handle_result_closed_from_plug_typing_for_markers; eauto.
Qed.

Lemma marker_annots_perform_reduct_incl_closed :
  forall E_tag m n_beta Ts T_B T_R op_body Ss v P,
    marker_annots_closed
      (term_handler_m m T_B T_R
        (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v))) ->
    incl
      (marker_annots
        (subst_list_tm [v; term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))]
          (subst_list_ty_in_tm Ss op_body)))
      (marker_annots
        (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v)))).
Proof.
  intros E_tag m n_beta Ts T_B T_R op_body Ss v P Hclosed.
  set (perform_redex := term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v).
  set (source := term_handler_m m T_B T_R (plug P perform_redex)).
  set (resume := term_resume m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))).
  assert (HTRclosed : ty_ty_closed 0 T_R /\ ty_lt_closed 0 T_R).
  { unfold marker_annots_closed in Hclosed. subst source perform_redex resume. simpl in Hclosed.
    inversion Hclosed as [|mt rest Hhead Htail]; subst. exact Hhead. }
  assert (Hop_closed : marker_annots_closed op_body).
  { subst source perform_redex resume.
    eapply marker_annots_closed_incl; [|exact Hclosed].
    intros p Hp. simpl. right. apply marker_annots_plug_in.
    simpl. right. apply List.in_or_app. left. exact Hp. }
  assert (Hv_closed : marker_annots_closed v).
  { subst source perform_redex resume.
    eapply marker_annots_closed_incl; [|exact Hclosed].
    intros p Hp. simpl. right. apply marker_annots_plug_in.
    simpl. right. apply List.in_or_app. right. exact Hp. }
  assert (Hresume_closed : marker_annots_closed resume).
  { subst source perform_redex resume. unfold marker_annots_closed. simpl. constructor.
    - exact HTRclosed.
    - eapply marker_annots_closed_incl; [|exact Hclosed].
      intros p Hp. simpl. right.
      eapply marker_annots_shift_ectx_tm_plug_var_incl with (r := term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v).
      exact Hp. }
  assert (Hvincl : incl (marker_annots v) (marker_annots source)).
  { subst source perform_redex resume. intros p Hp. simpl. right. apply marker_annots_plug_in.
    simpl. right. apply List.in_or_app. right. exact Hp. }
  assert (Hopincl : incl (marker_annots op_body) (marker_annots source)).
  { subst source perform_redex resume. intros p Hp. simpl. right. apply marker_annots_plug_in.
    simpl. right. apply List.in_or_app. left. exact Hp. }
  assert (Hresincl : incl (marker_annots resume) (marker_annots source)).
  { subst source perform_redex resume. intros p Hp. simpl in Hp. destruct Hp as [Hp | Hp].
    - simpl. left. exact Hp.
    - simpl. right.
      eapply marker_annots_shift_ectx_tm_plug_var_incl with (r := term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss v).
      exact Hp. }
  intros p Hp.
  pose proof (marker_annots_subst_list_tm_closed_repl_incl
    [v; resume] (subst_list_ty_in_tm Ss op_body)
    (Forall_cons _ Hv_closed (Forall_cons _ Hresume_closed (Forall_nil _)))
    p Hp) as Hincl.
  subst resume source perform_redex.
  rewrite marker_annots_subst_list_ty_in_tm_closed in Hincl by exact Hop_closed.
  simpl in Hincl. repeat rewrite List.app_nil_r in Hincl.
  repeat rewrite List.in_app_iff in Hincl.
  destruct Hincl as [[HvIn | HresIn] | HopIn].
  - apply Hvincl. exact HvIn.
  - apply Hresincl. exact HresIn.
  - apply Hopincl. exact HopIn.
Qed.

Lemma step_preserves_marker_types_safe_closed_typed : forall Γ t t' T,
  eval_ctx Γ -> marker_annots_closed t -> marker_types_safe t -> Γ ⊢ₜ t : T ->
  t ==> t' -> marker_types_safe t'.
Proof.
  intros Γ t t' T Hec Hclosed Hsafe Hty Hstep.
  eapply step_preserves_marker_types_safe_closed_typed_with_perform; eauto.
  intros E_tag m n_beta Ts T_B T_R op_body Ss v P Hval Hpure Hclosed_redex.
  apply marker_annots_perform_reduct_incl_closed. exact Hclosed_redex.
Qed.

Lemma step_preserves_marker_annots_closed_typed : forall Γ t t' T,
  eval_ctx Γ -> marker_annots_closed t -> Γ ⊢ₜ t : T ->
  t ==> t' -> marker_annots_closed t'.
Proof.
  intros Γ t t' T Hec Hclosed Hty Hstep.
  inversion Hstep as
    [E r r' Hwf Hhead Heq1 Heq2
    | E E_tag n_beta Ts T_B T_R op_body body m Hwf Hfresh Heq1 Heq2]; subst.
  - assert (Hclosed_r : marker_annots_closed r).
    { eapply marker_annots_closed_incl.
      - intros p Hp. apply marker_annots_plug_in. exact Hp.
      - exact Hclosed. }
    pose proof (head_step_marker_annots_incl_closed_with_perform r r' Hhead Hclosed_r) as Hincl.
    assert (Hred_incl : incl (marker_annots r') (marker_annots r)).
    { apply Hincl. intros E_tag m n_beta Ts T_B T_R op_body Ss v P Hval Hpure Hclosed_redex.
      apply marker_annots_perform_reduct_incl_closed. exact Hclosed_redex. }
    eapply marker_annots_closed_incl.
    + apply marker_annots_plug_replace_incl. exact Hred_incl.
    + exact Hclosed.
  - destruct (handle_result_closed_from_plug_typing_for_markers
      Γ E E_tag n_beta Ts T_B T_R op_body body T Hec Hty) as [HTy HLt].
    assert (Hop_closed : marker_annots_closed op_body).
    { eapply marker_annots_closed_incl; [|exact Hclosed].
      intros p Hp. apply marker_annots_plug_in. simpl. apply List.in_or_app. left. exact Hp. }
    eapply marker_annots_closed_cons_incl with
      (m := m) (T := T_R)
      (source := plug E (term_handle E_tag n_beta Ts T_B T_R op_body body)); eauto.
    apply marker_annots_plug_replace_incl_cons.
    apply marker_annots_handle_alloc_redex_incl_closed; assumption.
Qed.

Lemma marker_ok_ctor_focus_inv : forall ms K l lts Ts vs t ts,
  marker_ok ms (term_ctor K l lts Ts (vs ++ t :: ts)) ->
  marker_ok ms t.
Proof.
  intros ms K l lts Ts vs t ts H.
  induction vs as [|v vs IH]; simpl in H; [tauto|].
  apply IH. tauto.
Qed.

(* ================================================================== *)
(* marker_ok metatheory: monotonicity and substitution invariance     *)
(*                                                                    *)
(* These are the genuinely-true, reusable structural facts about the  *)
(* runtime marker invariant.  They are needed by any sound proof of   *)
(* marker preservation (subject reduction for marker_ok).             *)
(* ================================================================== *)

(* Top-level mirror of the nested marker_ok_list fixpoint, so that the  *)
(* constructor-argument list can be reasoned about with term_list_ind.  *)
Fixpoint marker_ok_list (ms : list marker) (ts : list term) : Prop :=
  match ts with
  | [] => True
  | u :: rest => marker_ok ms u /\ marker_ok_list ms rest
  end.

Lemma marker_ok_ctor_eq : forall ms K l lts Ts ts,
  marker_ok ms (term_ctor K l lts Ts ts) = marker_ok_list ms ts.
Proof.
  intros ms K l lts Ts ts. induction ts as [|u rest IH].
  - reflexivity.
  - change (marker_ok ms (term_ctor K l lts Ts (u :: rest)))
      with (marker_ok ms u /\ marker_ok ms (term_ctor K l lts Ts rest)).
    rewrite IH. reflexivity.
Qed.

(* Extract per-argument marker_ok from a constructor's marker_ok. *)
Lemma marker_ok_ctor_args_forall : forall ms K l lts Ts vs,
  marker_ok ms (term_ctor K l lts Ts vs) -> Forall (marker_ok ms) vs.
Proof.
  intros ms K l lts Ts vs H. rewrite marker_ok_ctor_eq in H.
  induction vs as [|v vs IH]; constructor.
  - destruct H as [Hv _]. exact Hv.
  - apply IH. destruct H as [_ Hrest]. exact Hrest.
Qed.

(* Recompose marker_ok through an evaluation context: replacing the hole
   contents by anything that is marker_ok in every marker scope preserves
   marker_ok of the whole plug.  The handler frame extends the scope by m,
   which the uniform (forall ms') replacement condition absorbs.  Use
   [cbn [plug]]/[destruct], NOT [simpl], to avoid unfolding marker_ok's
   nested constructor fixpoint (which would defeat marker_ok_ctor_eq). *)
Lemma marker_ok_plug_replace : forall E r r' ms,
  marker_ok ms (plug E r) ->
  (forall ms', marker_ok ms' r -> marker_ok ms' r') ->
  marker_ok ms (plug E r').
Proof.
  induction E as
    [ | E1 IHE ta | ta E1 IHE | E1 IHE Ty | E1 IHE lt
    | tag dl lts Tys vs E1 IHE ts | E1 IHE K nlt ar yes no
    | mk TB TR E1 IHE | E1 IHE Ss ar2 | rcv Ss E1 IHE ];
    intros r r' ms Hok Hrep; cbn [plug] in Hok |- *.
  - apply Hrep. exact Hok.
  - destruct Hok as [H1 H2]. split; [eapply IHE; eauto | exact H2].
  - destruct Hok as [H1 H2]. split; [exact H1 | eapply IHE; eauto].
  - eapply IHE; eauto.
  - eapply IHE; eauto.
  - rewrite marker_ok_ctor_eq in Hok |- *.
    induction vs as [|a vs' IHvs]; cbn [List.app] in Hok |- *.
    + destruct Hok as [Hfoc Hrest]. split; [eapply IHE; eauto | exact Hrest].
    + destruct Hok as [Ha Hrest]. split; [exact Ha | apply IHvs; exact Hrest].
  - destruct Hok as [Hs [Hy Hn]]. repeat split; [eapply IHE; eauto | exact Hy | exact Hn].
  - eapply IHE; eauto.
  - destruct Hok as [H1 H2]. split; [eapply IHE; eauto | exact H2].
  - destruct Hok as [H1 H2]. split; [exact H1 | eapply IHE; eauto].
Qed.

(* incl is preserved by prepending a common head. *)
Lemma incl_same_cons : forall (m : marker) ms ms',
  incl ms ms' -> incl (m :: ms) (m :: ms').
Proof.
  intros m ms ms' H x Hx. simpl in Hx |- *. destruct Hx as [Heq | Hin].
  - left; exact Heq.
  - right; exact (H x Hin).
Qed.

(* marker_ok is monotone in the marker context (upward-closed in ms). *)
Lemma marker_ok_mono : forall t ms ms',
  incl ms ms' -> marker_ok ms t -> marker_ok ms' t.
Proof.
  apply (term_list_ind
    (fun t => forall ms ms', incl ms ms' -> marker_ok ms t -> marker_ok ms' t)
    (fun ts => forall ms ms', incl ms ms' -> marker_ok_list ms ts -> marker_ok_list ms' ts)).
  - (* var *) intros n ms ms' Hi Hm. exact I.
  - (* app *) intros t1 t2 H1 H2 ms ms' Hi Hm. simpl in *.
    destruct Hm as [Ha Hb]. split; [eapply H1 | eapply H2]; eauto.
  - (* lam *) intros body T H ms ms' Hi Hm. simpl in *. eapply H; eauto.
  - (* ty_app *) intros t T H ms ms' Hi Hm. simpl in *. eapply H; eauto.
  - (* ty_lam *) intros bound body H ms ms' Hi Hm. simpl in *. eapply H; eauto.
  - (* lt_app *) intros t l H ms ms' Hi Hm. simpl in *. eapply H; eauto.
  - (* lt_lam *) intros body H ms ms' Hi Hm. simpl in *. eapply H; eauto.
  - (* ctor *) intros K l lts Ts ts HQ ms ms' Hi Hm.
    rewrite marker_ok_ctor_eq in Hm |- *. apply (HQ ms ms' Hi Hm).
  - (* match *) intros scrut tag n_lt arity yes no Hs Hy Hn ms ms' Hi Hm. simpl in *.
    destruct Hm as [H1 [H2 H3]]. repeat split; [eapply Hs | eapply Hy | eapply Hn]; eauto.
  - (* handle *) intros E n_beta Ts T_B T_R op body Hop Hb ms ms' Hi Hm. simpl in *.
    destruct Hm as [H1 H2]. split; [eapply Hop | eapply Hb]; eauto.
  - (* perform *) intros t Ss arg Ht Ha ms ms' Hi Hm. simpl in *.
    destruct Hm as [H1 H2]. split; [eapply Ht | eapply Ha]; eauto.
  - (* cap *) intros E m n_beta Ts T_R op Hop ms ms' Hi Hm. simpl in *.
    destruct Hm as [Hin Hrec]. split.
    + exact (Hi m Hin).
    + apply (Hop (m :: ms) (m :: ms')); [apply incl_same_cons; exact Hi | exact Hrec].
  - (* handler_m *) intros m T_B T_R t H ms ms' Hi Hm. simpl in *.
    apply (H (m :: ms) (m :: ms')); [apply incl_same_cons; exact Hi | exact Hm].
  - (* resume *) intros m T_B T_R b H ms ms' Hi Hm. simpl in *.
    apply (H (m :: ms) (m :: ms')); [apply incl_same_cons; exact Hi | exact Hm].
  - (* nil *) intros ms ms' Hi Hm. exact I.
  - (* cons *) intros u ts Hu Hts ms ms' Hi Hm. simpl in *.
    destruct Hm as [Ha Hb]. split; [eapply Hu | eapply Hts]; eauto.
Qed.

(* Closes every term_list_ind case EXCEPT the constructor case, for the      *)
(* marker-invariance lemmas: shift/type-subst/lt-subst never touch markers.   *)
Ltac mok_inv_noctor :=
  try (solve [ intros; simpl in *;
       repeat match goal with [ H : _ /\ _ |- _ ] => destruct H end;
       repeat split; eauto ]).

(* Shifting term variables does not affect marker_ok. *)
Lemma marker_ok_shift_tm : forall t ms k c,
  marker_ok ms t -> marker_ok ms (shift_tm k c t).
Proof.
  apply (term_list_ind
    (fun t => forall ms k c, marker_ok ms t -> marker_ok ms (shift_tm k c t))
    (fun ts => forall ms k c, marker_ok_list ms ts ->
       marker_ok_list ms (List.map (shift_tm k c) ts)));
    mok_inv_noctor.
  intros K l lts Ts ts HQ ms k c Hm.
  cbn [shift_tm]. rewrite shift_tm_go_eq_map.
  rewrite marker_ok_ctor_eq in Hm. rewrite marker_ok_ctor_eq.
  apply HQ; exact Hm.
Qed.

(* Shifting type variables inside a term does not affect marker_ok. *)
Lemma marker_ok_shift_ty_in_tm : forall t ms k c,
  marker_ok ms t -> marker_ok ms (shift_ty_in_tm k c t).
Proof.
  apply (term_list_ind
    (fun t => forall ms k c, marker_ok ms t -> marker_ok ms (shift_ty_in_tm k c t))
    (fun ts => forall ms k c, marker_ok_list ms ts ->
       marker_ok_list ms (List.map (shift_ty_in_tm k c) ts)));
    mok_inv_noctor.
  intros K l lts Ts ts HQ ms k c Hm.
  cbn [shift_ty_in_tm]. rewrite shift_ty_in_tm_go_eq_map.
  rewrite marker_ok_ctor_eq in Hm. rewrite marker_ok_ctor_eq.
  apply HQ; exact Hm.
Qed.

(* Shifting lifetime variables inside a term does not affect marker_ok. *)
Lemma marker_ok_shift_lt_in_tm : forall t ms k c,
  marker_ok ms t -> marker_ok ms (shift_lt_in_tm k c t).
Proof.
  apply (term_list_ind
    (fun t => forall ms k c, marker_ok ms t -> marker_ok ms (shift_lt_in_tm k c t))
    (fun ts => forall ms k c, marker_ok_list ms ts ->
       marker_ok_list ms (List.map (shift_lt_in_tm k c) ts)));
    mok_inv_noctor.
  intros K l lts Ts ts HQ ms k c Hm.
  cbn [shift_lt_in_tm]. rewrite shift_lt_in_tm_go_eq_map.
  rewrite marker_ok_ctor_eq in Hm. rewrite marker_ok_ctor_eq.
  apply HQ; exact Hm.
Qed.

(* Type substitution inside a term does not affect marker_ok. *)
Lemma marker_ok_subst_ty_in_tm : forall t ms var R,
  marker_ok ms t -> marker_ok ms (subst_ty_in_tm var R t).
Proof.
  apply (term_list_ind
    (fun t => forall ms var R, marker_ok ms t -> marker_ok ms (subst_ty_in_tm var R t))
    (fun ts => forall ms var R, marker_ok_list ms ts ->
       marker_ok_list ms (List.map (subst_ty_in_tm var R) ts)));
    mok_inv_noctor.
  intros K l lts Ts ts HQ ms var R Hm.
  cbn [subst_ty_in_tm]. rewrite subst_ty_in_tm_go_eq_map.
  rewrite marker_ok_ctor_eq in Hm. rewrite marker_ok_ctor_eq.
  apply HQ; exact Hm.
Qed.

(* Lifetime substitution inside a term does not affect marker_ok. *)
Lemma marker_ok_subst_lt_in_tm : forall t ms var R,
  marker_ok ms t -> marker_ok ms (subst_lt_in_tm var R t).
Proof.
  apply (term_list_ind
    (fun t => forall ms var R, marker_ok ms t -> marker_ok ms (subst_lt_in_tm var R t))
    (fun ts => forall ms var R, marker_ok_list ms ts ->
       marker_ok_list ms (List.map (subst_lt_in_tm var R) ts)));
    mok_inv_noctor.
  intros K l lts Ts ts HQ ms var R Hm.
  cbn [subst_lt_in_tm]. rewrite subst_lt_in_tm_go_eq_map.
  rewrite marker_ok_ctor_eq in Hm. rewrite marker_ok_ctor_eq.
  apply HQ; exact Hm.
Qed.

(* Substituting a marker_ok term into a marker_ok term yields marker_ok. *)
Lemma marker_ok_subst_tm : forall t ms var repl,
  marker_ok ms repl -> marker_ok ms t -> marker_ok ms (subst_tm var repl t).
Proof.
  apply (term_list_ind
    (fun t => forall ms var repl,
       marker_ok ms repl -> marker_ok ms t -> marker_ok ms (subst_tm var repl t))
    (fun ts => forall ms var repl,
       marker_ok ms repl -> marker_ok_list ms ts ->
       marker_ok_list ms (List.map (subst_tm var repl) ts))).
  - (* var *) intros n ms var repl Hrepl Hm. simpl.
    destruct (Nat.eqb n var); [exact Hrepl|].
    destruct (Nat.ltb var n); exact I.
  - (* app *) intros t1 t2 H1 H2 ms var repl Hrepl Hm. simpl in *.
    destruct Hm as [Ha Hb]. split; [eapply H1 | eapply H2]; eauto.
  - (* lam *) intros body T H ms var repl Hrepl Hm. simpl in *.
    eapply H; [ apply marker_ok_shift_tm; exact Hrepl | exact Hm ].
  - (* ty_app *) intros t T H ms var repl Hrepl Hm. simpl in *.
    eapply H; eauto.
  - (* ty_lam *) intros bound body H ms var repl Hrepl Hm. simpl in *.
    eapply H; [ apply marker_ok_shift_ty_in_tm; exact Hrepl | exact Hm ].
  - (* lt_app *) intros t l H ms var repl Hrepl Hm. simpl in *.
    eapply H; eauto.
  - (* lt_lam *) intros body H ms var repl Hrepl Hm. simpl in *.
    eapply H; [ apply marker_ok_shift_lt_in_tm; exact Hrepl | exact Hm ].
  - (* ctor *) intros K l lts Ts ts HQ ms var repl Hrepl Hm.
    cbn [subst_tm]. rewrite subst_tm_go_eq_map.
    rewrite marker_ok_ctor_eq in Hm. rewrite marker_ok_ctor_eq.
    apply HQ; [exact Hrepl | exact Hm].
  - (* match *) intros scrut tag n_lt arity yes no Hs Hy Hn ms var repl Hrepl Hm.
    simpl in *. destruct Hm as [Hsc [Hye Hno]]. repeat split.
    + eapply Hs; eauto.
    + eapply Hy; [ apply marker_ok_shift_tm; apply marker_ok_shift_lt_in_tm; exact Hrepl
                 | exact Hye ].
    + eapply Hn; eauto.
  - (* handle *) intros E n_beta Ts T_B T_R op body Hop Hb ms var repl Hrepl Hm. simpl in *.
    destruct Hm as [Ho Hbo]. split.
    + eapply Hop; [ apply marker_ok_shift_tm; exact Hrepl | exact Ho ].
    + eapply Hb;  [ apply marker_ok_shift_tm; exact Hrepl | exact Hbo ].
  - (* perform *) intros t Ss arg Ht Ha ms var repl Hrepl Hm. simpl in *.
    destruct Hm as [Ht1 Ha1]. split; [eapply Ht | eapply Ha]; eauto.
  - (* cap *) intros E m n_beta Ts T_R op Hop ms var repl Hrepl Hm. simpl in *.
    destruct Hm as [Hin Hrec]. split.
    + exact Hin.
    + apply (Hop (m :: ms) (var + 2) (shift_tm 2 0 repl)).
      * eapply marker_ok_mono; [ apply incl_tl; apply incl_refl
                               | apply marker_ok_shift_tm; exact Hrepl ].
      * exact Hrec.
  - (* handler_m *) intros m T_B T_R t H ms var repl Hrepl Hm. simpl in *.
    apply (H (m :: ms) var repl).
    + eapply marker_ok_mono; [ apply incl_tl; apply incl_refl | exact Hrepl ].
    + exact Hm.
  - (* resume *) intros m T_B T_R b H ms var repl Hrepl Hm. simpl in *.
    apply (H (m :: ms) (S var) (shift_tm 1 0 repl)).
    + eapply marker_ok_mono; [ apply incl_tl; apply incl_refl
                             | apply marker_ok_shift_tm; exact Hrepl ].
    + exact Hm.
  - (* nil *) intros ms var repl Hrepl Hm. exact I.
  - (* cons *) intros u ts Hu Hts ms var repl Hrepl Hm. simpl in *.
    destruct Hm as [Hu_m Hts_m]. split; [eapply Hu | eapply Hts]; eauto.
Qed.

(* Simultaneous term substitution preserves marker_ok. *)
Lemma marker_ok_subst_list_tm : forall vs t ms,
  Forall (marker_ok ms) vs -> marker_ok ms t -> marker_ok ms (subst_list_tm vs t).
Proof.
  induction vs as [|v rest IH]; intros t ms HF Hm; simpl.
  - exact Hm.
  - assert (Hv := Forall_inv HF).
    assert (HFrest := Forall_inv_tail HF).
    apply IH; [exact HFrest|].
    apply marker_ok_subst_tm; [ apply marker_ok_shift_tm; exact Hv | exact Hm ].
Qed.

(* Simultaneous lifetime substitution preserves marker_ok. *)
Lemma marker_ok_subst_list_lt_in_tm : forall lts t ms,
  marker_ok ms t -> marker_ok ms (subst_list_lt_in_tm lts t).
Proof.
  induction lts as [|l rest IH]; intros t ms Hm; simpl.
  - exact Hm.
  - apply IH. apply marker_ok_subst_lt_in_tm. exact Hm.
Qed.

(* Simultaneous type substitution preserves marker_ok. *)
Lemma marker_ok_subst_list_ty_in_tm : forall Ss t ms,
  marker_ok ms t -> marker_ok ms (subst_list_ty_in_tm Ss t).
Proof.
  induction Ss as [|S0 rest IH]; intros t ms Hm; simpl.
  - exact Hm.
  - apply IH. apply marker_ok_subst_ty_in_tm. exact Hm.
Qed.

(* has_rt_cap on a constructor reduces to has_rt_cap_list on its       *)
(* argument list (the in-body fixpoint equals the named list version).  *)
Lemma has_rt_cap_ctor_eq : forall K l lts Ts ts,
  has_rt_cap (term_ctor K l lts Ts ts) = has_rt_cap_list ts.
Proof.
  intros K l lts Ts ts. simpl.
  induction ts as [|u rest IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(* CONFINEMENT BUILDING BLOCK 1 (structural).  When a term carries no    *)
(* runtime capability, marker_ok is insensitive to the marker scope: an  *)
(* extra delimiter m at the front can be dropped.  The only constructs   *)
(* that read the scope (cap / handler_m / resume) all set has_rt_cap to  *)
(* true, so the hypothesis makes their cases vacuous; everything else     *)
(* recurses.  This is the half of handler-elimination that does NOT need *)
(* typing — it reduces the goal to "the returned value has no cap".       *)
Lemma marker_ok_strengthen_no_cap : forall t ms m,
  has_rt_cap t = false -> marker_ok (m :: ms) t -> marker_ok ms t.
Proof.
  apply (term_list_ind
    (fun t => forall ms m, has_rt_cap t = false ->
       marker_ok (m :: ms) t -> marker_ok ms t)
    (fun ts => forall ms m, has_rt_cap_list ts = false ->
       marker_ok_list (m :: ms) ts -> marker_ok_list ms ts)).
  - (* var *) intros n ms m Hcap Hm. exact I.
  - (* app *) intros t1 t2 H1 H2 ms m Hcap Hm. simpl in *.
    apply Bool.orb_false_iff in Hcap as [Hc1 Hc2].
    destruct Hm as [Ha Hb]. split; [eapply H1 | eapply H2]; eauto.
  - (* lam *) intros body T H ms m Hcap Hm. simpl in *. eapply H; eauto.
  - (* ty_app *) intros t T H ms m Hcap Hm. simpl in *. eapply H; eauto.
  - (* ty_lam *) intros bound body H ms m Hcap Hm. simpl in *. eapply H; eauto.
  - (* lt_app *) intros t l H ms m Hcap Hm. simpl in *. eapply H; eauto.
  - (* lt_lam *) intros body H ms m Hcap Hm. simpl in *. eapply H; eauto.
  - (* ctor *) intros K l lts Ts ts HQ ms m Hcap Hm.
    rewrite has_rt_cap_ctor_eq in Hcap.
    rewrite marker_ok_ctor_eq in Hm |- *. eapply HQ; eauto.
  - (* match *) intros scrut tag n_lt arity yes no Hs Hy Hn ms m Hcap Hm. simpl in *.
    apply Bool.orb_false_iff in Hcap as [Hc1 Hc23].
    apply Bool.orb_false_iff in Hc23 as [Hc2 Hc3].
    destruct Hm as [H1 [H2 H3]]. repeat split; [eapply Hs | eapply Hy | eapply Hn]; eauto.
  - (* handle *) intros E n_beta Ts T_B T_R op body Hop Hb ms m Hcap Hm. simpl in *.
    apply Bool.orb_false_iff in Hcap as [Hc1 Hc2].
    destruct Hm as [H1 H2]. split; [eapply Hop | eapply Hb]; eauto.
  - (* perform *) intros t Ss arg Ht Ha ms m Hcap Hm. simpl in *.
    apply Bool.orb_false_iff in Hcap as [Hc1 Hc2].
    destruct Hm as [H1 H2]. split; [eapply Ht | eapply Ha]; eauto.
  - (* cap *) intros E m0 n_beta Ts T_R op Hop ms m Hcap Hm. simpl in Hcap. discriminate.
  - (* handler_m *) intros m0 T_B T_R t H ms m Hcap Hm. simpl in Hcap. discriminate.
  - (* resume *) intros m0 T_B T_R b H ms m Hcap Hm. simpl in Hcap. discriminate.
  - (* nil *) intros ms m Hcap Hm. exact I.
  - (* cons *) intros u ts Hu Hts ms m Hcap Hm. simpl in *.
    apply Bool.orb_false_iff in Hcap as [Hc1 Hc2].
    destruct Hm as [Ha Hb]. split; [eapply Hu | eapply Hts]; eauto.
Qed.

Lemma marker_ok_handler_return_no_cap : forall m T_B T_R v ms,
  has_rt_cap v = false ->
  marker_ok ms (term_handler_m m T_B T_R v) ->
  marker_ok ms v.
Proof.
  intros m T_B T_R v ms Hcap Hok.
  simpl in Hok. eapply marker_ok_strengthen_no_cap; eauto.
Qed.

(* ================================================================== *)
(* AXIOM 5: marker_ok preservation for the handler-elimination head   *)
(* steps (H_Return / H_Perform), whose redex is `term_handler_m m`.   *)
(* These delete the delimiter m, so re-establishing marker_ok at the  *)
(* smaller scope requires capability confinement (the returned/       *)
(* resumed term contains no dangling m), which follows from typing —  *)
(* NOT from a structural argument.  Stated with the typing +          *)
(* marker_types_safe premises so it is sound (true, just hard).       *)
(*                                                                    *)
(* REDUCTION OF THE PROOF (investigated; sound, not a gap):           *)
(*  - H_Return is `handler_m m T_B T_R v -->h v` with `value v` and    *)
(*    `marker_ok ms (handler_m ... v) = marker_ok (m::ms) v`; so the   *)
(*    goal is exactly `marker_ok (m::ms) v -> marker_ok ms v`.  By     *)
(*    [marker_ok_strengthen_no_cap] (above, PROVEN) this collapses to  *)
(*    the CONFINEMENT obligation `has_rt_cap v = false`.               *)
(*  - H_Perform reduces to the same confinement on the perform-arg `w` *)
(*    (typed at the no-local operation parameter) plus marker_ok-under- *)
(*    substitution for the operation body with the re-introduced       *)
(*    `term_resume m` (which re-binds m for its own body).             *)
(*                                                                    *)
(*  CONFINEMENT (the remaining gap): a CLOSED value typed at a         *)
(*  no_local type carries no runtime capability                        *)
(*    `eval_ctx Γ -> Γ ⊢ₜ v : T -> value v -> free_tm_vars 0 v = [] -> *)
(*     no_local_ty_G Γ T = true -> has_rt_cap v = false`.              *)
(*  It is TRUE (capture-lifetime discipline: a cap is local, T_Lam     *)
(*  bounds the closure lifetime by the captured-var lifetimes, and the *)
(*  prenex-Λ restriction forces every value to bottom out at a λ whose *)
(*  annotation `no_local_ty_G` checks).  But `lt_of_ty_G` is too       *)
(*  COARSE to express it directly: it joins to `lt_local` at every     *)
(*  ∀-type and at every cap-carrying ctor field, so the existing       *)
(*  [typing_value_capture_lt_le_type] (`capture_lt v <: lt_of_ty_G T`) *)
(*  is VACUOUS on ∀-typed values.  A real proof must peel the prenex   *)
(*  Λ-chain to reach each innermost λ-annotation — which pushes the    *)
(*  induction into contexts that are `eval_ctx` EXTENDED by Λ-binders  *)
(*  (bind_ty bound / bind_lt lt_local), where both                     *)
(*  [typing_value_capture_lt_le_type] and [lt_sub_no_local_mono]       *)
(*  currently require plain `eval_ctx`.  Discharging it thus means     *)
(*  generalizing that capture-lifetime layer from `eval_ctx` to        *)
(*  `eval_ctx + prenex Λ-binders` (a foundational, match-kernel-sized  *)
(*  effort), plus a schema lemma propagating `no_local` from a ctor's  *)
(*  result type to its instantiated field types.                       *)
(* ================================================================== *)
Axiom marker_ok_step_handler_elim : forall Γ m T_B T_R body r' Tr,
  Γ ⊢ₜ term_handler_m m T_B T_R body : Tr ->
  marker_types_safe (term_handler_m m T_B T_R body) ->
  term_handler_m m T_B T_R body -->h r' ->
  forall ms, marker_ok ms (term_handler_m m T_B T_R body) -> marker_ok ms r'.

(* A head step preserves marker_ok uniformly in the scope.  The six   *)
(* non-handler-elimination cases are structural; the two              *)
(* handler-elimination cases (whose redex head is term_handler_m)     *)
(* are discharged by Axiom 5 using the redex typing. *)
Lemma head_step_preserves_marker_ok : forall Γ r r' Tr,
  Γ ⊢ₜ r : Tr -> marker_types_safe r -> r -->h r' ->
  forall ms, marker_ok ms r -> marker_ok ms r'.
Proof.
  intros Γ r r' Tr Hr Hsafe Hstep ms Hok. inversion Hstep; subst.
  - (* H_Beta *)
    destruct Hok as [Hbody Hv].
    apply marker_ok_subst_tm; [exact Hv | exact Hbody].
  - (* H_TyBeta *)
    apply marker_ok_subst_ty_in_tm. exact Hok.
  - (* H_LtBeta *)
    apply marker_ok_subst_lt_in_tm. exact Hok.
  - (* H_MatchYes *)
    destruct Hok as [Hctor [Hyes Hno]].
    apply marker_ok_subst_list_tm.
    + apply (marker_ok_ctor_args_forall ms K l lts Ts vs Hctor).
    + apply marker_ok_subst_list_lt_in_tm. exact Hyes.
  - (* H_MatchNo *)
    destruct Hok as [Hctor [Hyes Hno]]. exact Hno.
  - (* H_Return: handler-elim, via Axiom 5 *)
    eapply marker_ok_step_handler_elim; [ exact Hr | exact Hsafe | exact Hstep | exact Hok ].
  - (* H_Perform: handler-elim, via Axiom 5 *)
    eapply marker_ok_step_handler_elim; [ exact Hr | exact Hsafe | exact Hstep | exact Hok ].
  - (* H_Resume *)
    destruct Hok as [Hres Hv].
    apply marker_ok_subst_tm.
    + eapply marker_ok_mono; [apply incl_tl; apply incl_refl | exact Hv].
    + exact Hres.
Qed.

(* One reduction step preserves marker_ok [].  S_step lifts the head  *)
(* lemma through the evaluation context via marker_ok_plug_replace;   *)
(* S_HandleCtx installs the fresh delimiter (purely structural).      *)
Lemma step_preserves_marker_ok : forall Γ t t' T,
  eval_ctx Γ -> marker_ok [] t -> marker_types_safe t -> Γ ⊢ₜ t : T ->
  t ==> t' -> marker_ok [] t'.
Proof.
  intros Γ t t' T Hec Hmok Hsafe Hty Hstep.
  inversion Hstep as
    [E r r' Hwf Hhead Heq1 Heq2
    | E E_tag n_beta Ts T_B T_R op_body body m Hwf Hfresh Heq1 Heq2]; subst.
  - (* S_step *)
    destruct (plug_typing_inv E Γ r T Hty) as [Tr Hr].
    assert (Hsafe_r : marker_types_safe r).
    { eapply marker_types_safe_incl;
        [ intros p Hp; apply (marker_annots_plug_in E r p Hp) | exact Hsafe ]. }
    eapply marker_ok_plug_replace; [ exact Hmok | ].
    intros ms' Hm.
    eapply head_step_preserves_marker_ok;
      [ exact Hr | exact Hsafe_r | exact Hhead | exact Hm ].
  - (* S_HandleCtx *)
    eapply marker_ok_plug_replace; [ exact Hmok | ].
    intros ms' Hm. destruct Hm as [Hop Hbody]. simpl.
    apply marker_ok_subst_tm.
    + simpl. split.
      * left. reflexivity.
      * eapply marker_ok_mono; [ apply incl_tl; apply incl_tl; apply incl_refl | exact Hop ].
    + eapply marker_ok_mono; [ apply incl_tl; apply incl_refl | exact Hbody ].
Qed.

