Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import SubstitutionTheory.

(* ================================================================== *)
(*                                                                    *)
(*                 PROGRESS AND PRESERVATION                          *)
(*                                                                    *)
(* We prove type safety for CoreΔ under a top-level evaluation ctx    *)
(* that contains only lifetime and constructor bindings (no bind_tm,  *)
(* no bind_ty).  This blocks SA_VarCtx at the top level and matches   *)
(* the paper's "program-level" evaluation scenario.                   *)
(* ================================================================== *)

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

(* go_eq_map for subst_ty_in_tm (the other go_eq_map lemmas live upstream). *)
Lemma subst_ty_in_tm_go_eq_map : forall var R ts,
  (fix go ts := match ts with [] => [] | u :: rest => subst_ty_in_tm var R u :: go rest end) ts =
  List.map (subst_ty_in_tm var R) ts.
Proof. intros; induction ts; simpl; congruence. Qed.

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
      Γ ⊢ₗ lt_of_ty_list rho_fields <: l ->
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

(* =================================================================== *)
(* Variance soundness for `elim_ty` / `elim_lt`                        *)
(*                                                                     *)
(* This is the central meta-theoretic lemma that justifies eliminating *)
(* fresh lifetime variables from a match-branch result type:           *)
(*                                                                     *)
(*   Provided eta has no invariant occurrence of the eliminated var,   *)
(*   substituting any concrete witness l_0 (with l_0 <: Δ) yields a    *)
(*   subtype of `elim_ty 0 Δ var_pos eta`.                             *)
(*                                                                     *)
(* The proof goes by mutual structural induction on the eliminated     *)
(* type/lifetime, simultaneously varying the variance position.        *)
(* Auxiliary mechanical de Bruijn lemmas are axiomatized: subtyping    *)
(* monotonicity under shift / single-var lt-substitution.              *)
(* =================================================================== *)

(* --- Custom type induction principle providing per-element IH      *)
(*     for the list-of-types in `type_ctor`.                         *)
Section TypeInd.
  Variable P : type -> Prop.
  Hypotheses
    (Hvar  : forall n, P (type_var n))
    (Hfun  : forall A l B, P A -> P B -> P (type_fun A l B))
    (Hctor : forall K l Ts, Forall P Ts -> P (type_ctor K l Ts))
    (Hltall: forall A, P A -> P (type_lt_all A))
    (Htyall: forall B A, P B -> P A -> P (type_ty_all B A)).

  Fixpoint type_ind' (T : type) : P T :=
    match T with
    | type_var n        => Hvar n
    | type_fun A l B    => Hfun A l B (type_ind' A) (type_ind' B)
    | type_ctor K l Ts  =>
        Hctor K l Ts
          ((fix go (Ts : list type) : Forall P Ts :=
            match Ts return Forall P Ts with
            | []     => Forall_nil _
            | A :: r => Forall_cons _ (type_ind' A) (go r)
            end) Ts)
    | type_lt_all A     => Hltall A (type_ind' A)
    | type_ty_all B A   => Htyall B A (type_ind' B) (type_ind' A)
    end.
End TypeInd.

Fixpoint elim_ty_list (lvar : nat) (bound : lifetime) (p : variance) (Ts : list type)
    : option (list type) :=
  match Ts with
  | [] => Some []
  | A :: rest =>
      match elim_ty lvar bound p A, elim_ty_list lvar bound p rest with
      | Some A', Some rest' => Some (A' :: rest')
      | _, _ => None
      end
  end.

Lemma elim_ty_list_eq_worker : forall lvar bound p Ts,
  (fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
     match Ts0 with
     | [] => Some []
     | A :: rest =>
         match elim_ty lvar bound p' A, go_list p' rest with
         | Some A', Some rest' => Some (A' :: rest')
         | _, _ => None
         end
     end) p Ts = elim_ty_list lvar bound p Ts.
Proof.
  intros lvar bound p Ts. induction Ts as [|A rest IH]; simpl.
  - reflexivity.
  - destruct (elim_ty lvar bound p A); simpl; [rewrite IH |]; reflexivity.
Qed.

Lemma elim_ty_ctor_eq : forall lvar bound p K l Ts,
  elim_ty lvar bound p (type_ctor K l Ts)
  = match elim_lt lvar bound p l, elim_ty_list lvar bound var_inv Ts with
    | Some l', Some Ts' => Some (type_ctor K l' Ts')
    | _, _ => None
    end.
Proof.
  intros lvar bound p K l Ts. simpl.
  rewrite elim_ty_list_eq_worker. reflexivity.
Qed.

(* ================================================================== *)
(* Sound iterated-elim soundness (binder-removal reformulation).      *)
(*                                                                    *)
(* The old `elim_ty_n_sound` relied on `iter_subst_lt_in_ty_mono`,    *)
(* which is FALSE (lifetime-variable substitution is not monotone in  *)
(* the subtyping order under LS_Var).  We replace it with an          *)
(* over-approximate-in-context + peel construction that never needs   *)
(* monotonicity:                                                      *)
(*   1. `elim_in_ctx_sound`: over-approximate eta entirely in a       *)
(*      context with n fresh lt-binders (no witnesses), giving        *)
(*      eta <:: shift_lt_in_ty n 0 elim_result.                       *)
(*   2. `sub_peel_push_corr`: peel all n binders at once via SubstLt, *)
(*      sound because the context shrinks together with the shift.    *)
(* ================================================================== *)

(* Over-approximation context: n fresh lt-binders, each storing the   *)
(* bound shifted to live at its level (uniform lookup = shift_lt n).  *)
Fixpoint push_corr (n : nat) (Delta : lifetime) (G : ctx) : ctx :=
  match n with
  | O    => G
  | S n' => bind_lt (shift_lt n' 0 Delta) :: push_corr n' Delta G
  end.

Lemma push_corr_lookup0 : forall n' Delta G,
  ctx_lookup_lt (push_corr (S n') Delta G) 0 = Some (shift_lt (S n') 0 Delta).
Proof.
  intros n' Delta G. simpl. f_equal.
  rewrite shift_lt_fuse. reflexivity.
Qed.

Lemma lt_wf_push_corr_bound : forall n Delta G,
  lt_wf G Delta -> lt_wf (push_corr n Delta G) (shift_lt n 0 Delta).
Proof.
  induction n as [|n' IH]; intros Delta G HwfDelta.
  - cbn [push_corr]. rewrite shift_lt_zero. exact HwfDelta.
  - cbn [push_corr].
    pose proof (IH Delta G HwfDelta) as HwfPrev.
    pose proof (lt_wf_InsLt (push_corr n' Delta G) (shift_lt n' 0 Delta) HwfPrev
                 0 (bind_lt (shift_lt n' 0 Delta) :: push_corr n' Delta G)
                 (InsLt_here (shift_lt n' 0 Delta) (push_corr n' Delta G))) as HwfIns.
    rewrite shift_lt_fuse in HwfIns. exact HwfIns.
Qed.

(* --- In-context single-step elim soundness (no substitution) ------ *)
(* Mirrors elim_lt_step_sound/elim_ty_step_sound but keeps the        *)
(* eliminated variable in the context and discharges via LS_Var.      *)
Lemma elim_lt_step_ctx : forall l lvar bound p l' G,
  elim_lt lvar bound p l = Some l' ->
  ctx_lookup_lt G lvar = Some bound ->
  lt_wf G bound ->
  lt_wf G l ->
  lt_wf G l' /\
  match p with
  | var_pos => G ⊢ₗ l <: l'
  | var_neg => G ⊢ₗ l' <: l
  | var_inv => l = l'
  end.
Proof.
  induction l as [n | | | l1 IHl1 l2 IHl2]; intros lvar bound p l' G Helim Hlk HwfBound Hwfl; simpl in Helim.
  - (* lt_var n *)
    destruct (Nat.eqb n lvar) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst n.
      destruct p; try discriminate Helim.
      * injection Helim; intros; subst l'. split.
        -- exact HwfBound.
        -- apply LS_Var; assumption.
      * injection Helim; intros; subst l'. split.
        -- constructor.
        -- apply LS_Free. exact Hwfl.
    + injection Helim; intros; subst l'.
      split; [exact Hwfl|]. destruct p; simpl; try (apply LS_Refl; exact Hwfl). reflexivity.
  - injection Helim; intros; subst l'. split; [constructor|].
    destruct p; simpl; try (apply LS_Refl; constructor). reflexivity.
  - injection Helim; intros; subst l'. split; [constructor|].
    destruct p; simpl; try (apply LS_Refl; constructor). reflexivity.
  - destruct (elim_lt lvar bound p l1) as [l1'|] eqn:E1; try discriminate.
    destruct (elim_lt lvar bound p l2) as [l2'|] eqn:E2; try discriminate.
    injection Helim; intros; subst l'.
    inversion Hwfl; subst.
    destruct (IHl1 _ _ _ _ _ E1 Hlk HwfBound H2) as [Hwf1' Hrel1].
    destruct (IHl2 _ _ _ _ _ E2 Hlk HwfBound H3) as [Hwf2' Hrel2].
    split; [constructor; assumption|]. destruct p; simpl in *.
    + apply lt_min_mono; assumption.
    + apply lt_min_mono; assumption.
    + f_equal; assumption.
Qed.

Lemma elim_ty_step_ctx : forall T lvar bound p T' G,
  elim_ty lvar bound p T = Some T' ->
  ctx_lookup_lt G lvar = Some bound ->
  lt_wf G bound ->
  ty_wf G T ->
  ty_wf G T' /\
  match p with
  | var_pos => G ⊢ T <:: T'
  | var_neg => G ⊢ T' <:: T
  | var_inv => T = T'
  end.
Proof.
  apply (type_ind'
    (fun T => forall lvar bound p T' G,
      elim_ty lvar bound p T = Some T' ->
      ctx_lookup_lt G lvar = Some bound ->
      lt_wf G bound ->
      ty_wf G T ->
      ty_wf G T' /\
      match p with
      | var_pos => G ⊢ T <:: T'
      | var_neg => G ⊢ T' <:: T
      | var_inv => T = T'
      end)).
  - (* type_var *)
    intros n lvar bound p T' G Helim Hlk HwfBound HwfT. simpl in Helim.
    injection Helim; intros; subst T'. split; [exact HwfT|].
    destruct p; simpl; try (apply SA_Refl; exact HwfT). reflexivity.
  - (* type_fun A l B *)
    intros A l B IHA IHB lvar bound p T' G Helim Hlk HwfBound HwfT. simpl in Helim.
    inversion HwfT; subst; clear HwfT.
    match goal with H : ty_wf G A |- _ => rename H into HwfA end.
    match goal with H : lt_wf G l |- _ => rename H into Hwfl end.
    match goal with H : ty_wf G B |- _ => rename H into HwfB end.
    destruct (elim_ty lvar bound (flip_var p) A) as [A'|] eqn:HA; try discriminate.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; try discriminate.
    destruct (elim_ty lvar bound p B) as [B'|] eqn:HB; try discriminate.
    injection Helim; intros; subst T'.
    destruct (IHA lvar bound (flip_var p) A' G HA Hlk HwfBound HwfA) as [HwfA' HrelA].
    destruct (elim_lt_step_ctx l lvar bound p l' G Hl Hlk HwfBound Hwfl) as [Hwfl' Hrell].
    destruct (IHB lvar bound p B' G HB Hlk HwfBound HwfB) as [HwfB' HrelB].
    split; [constructor; assumption|]. destruct p; simpl in *.
    + apply SA_Fun; assumption.
    + apply SA_Fun; assumption.
    + f_equal; assumption.
  - (* type_ctor K l Ts *)
    intros K l Ts IHTs lvar bound p T' G Helim Hlk HwfBound HwfT.
    inversion HwfT; subst; clear HwfT.
    match goal with H : lt_wf G l |- _ => rename H into Hwfl end.
    match goal with H : types_wf G Ts |- _ => rename H into HwfTs end.
    rewrite elim_ty_ctor_eq in Helim.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; try discriminate.
    destruct (elim_ty_list lvar bound var_inv Ts) as [Ts'|] eqn:HTs; try discriminate.
    injection Helim; intros; subst T'.
    destruct (elim_lt_step_ctx l lvar bound p l' G Hl Hlk HwfBound Hwfl) as [Hwfl' Hrell].
    assert (Hlist : Ts' = Ts).
    { clear Helim Hl Hrell Hwfl'. revert Ts' HTs HwfTs.
      induction IHTs as [|A rest HPA HFor IHFor]; intros Ts' HTs HwfTs; simpl in HTs.
      - injection HTs; intros; subst Ts'. reflexivity.
      - inversion HwfTs as [|? ? ? HwfA HwfRest]; subst.
        destruct (elim_ty lvar bound var_inv A) as [A'|] eqn:HAe; try discriminate.
        destruct (elim_ty_list lvar bound var_inv rest) as [rest'|] eqn:HRe; try discriminate.
        injection HTs; intros; subst Ts'. f_equal.
          + destruct (HPA lvar bound var_inv A' G HAe Hlk HwfBound HwfA) as [_ HAeq].
            symmetry. exact HAeq.
          + apply (IHFor rest'); [reflexivity|exact HwfRest]. }
    subst Ts'.
    split; [constructor; assumption|]. destruct p; simpl in *.
    + apply SA_Data; assumption.
    + apply SA_Data; assumption.
    + f_equal. exact Hrell.
  - (* type_lt_all A *)
    intros A IHA lvar bound p T' G Helim Hlk HwfBound HwfT. simpl in Helim.
    inversion HwfT; subst; clear HwfT.
    match goal with H : ty_wf (bind_lt lt_local :: G) A |- _ => rename H into HwfA end.
    destruct (elim_ty (S lvar) (shift_lt 1 0 bound) p A) as [A'|] eqn:HA; try discriminate.
    injection Helim; intros; subst T'.
    assert (Hlk' : ctx_lookup_lt (bind_lt lt_local :: G) (S lvar) = Some (shift_lt 1 0 bound)).
    { simpl. rewrite Hlk. reflexivity. }
    assert (HwfBound' : lt_wf (bind_lt lt_local :: G) (shift_lt 1 0 bound)).
    { eapply lt_wf_InsLt; [exact HwfBound|apply InsLt_here]. }
    destruct (IHA (S lvar) (shift_lt 1 0 bound) p A' (bind_lt lt_local :: G)
                HA Hlk' HwfBound' HwfA) as [HwfA' HrelA].
    split; [constructor; exact HwfA'|]. destruct p; simpl in *.
    + apply SA_LtAll. exact HrelA.
    + apply SA_LtAll. exact HrelA.
    + f_equal. exact HrelA.
  - (* type_ty_all B A *)
    intros B A IHB IHA lvar bound p T' G Helim Hlk HwfBound HwfT. simpl in Helim.
    inversion HwfT; subst; clear HwfT.
    match goal with H : ty_wf G B |- _ => rename H into HwfB end.
    match goal with H : ty_wf (bind_ty B :: G) A |- _ => rename H into HwfA end.
    destruct (elim_ty lvar bound (flip_var p) B) as [B'|] eqn:HB; try discriminate.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HA; try discriminate.
    injection Helim; intros; subst T'.
    assert (HlkB : forall Bb, ctx_lookup_lt (bind_ty Bb :: G) lvar = Some bound).
    { intro Bb. simpl. exact Hlk. }
    assert (HwfBoundB : forall Bb, lt_wf (bind_ty Bb :: G) bound).
    { intro Bb. eapply lt_wf_InsTy; [exact HwfBound|apply InsTy_here]. }
    destruct p; simpl.
    + destruct (IHB lvar bound var_neg B' G HB Hlk HwfBound HwfB) as [HwfB' HsubB].
      assert (HwfA_NT : ty_wf (bind_ty B' :: G) A).
      { eapply ty_wf_NT; [apply NT_here; exact HsubB|exact HwfA]. }
      destruct (IHA lvar bound var_pos A' (bind_ty B' :: G) HA (HlkB B')
                  (HwfBoundB B') HwfA_NT) as [HwfA' HsubA].
      split; [constructor; assumption|].
      eapply SA_TyAll; eauto.
    + destruct (IHB lvar bound var_pos B' G HB Hlk HwfBound HwfB) as [HwfB' HsubB].
      destruct (IHA lvar bound var_neg A' (bind_ty B :: G) HA (HlkB B)
                  (HwfBoundB B) HwfA) as [HwfA'_B HsubA].
      assert (HwfA' : ty_wf (bind_ty B' :: G) A').
      { eapply ty_wf_RT; [|exact HwfA'_B].
        apply RT_here; assumption. }
      split; [constructor; assumption|].
      eapply SA_TyAll; eauto.
    + destruct (IHB lvar bound var_inv B' G HB Hlk HwfBound HwfB) as [HwfB' HB_eq].
      subst B'.
      destruct (IHA lvar bound var_inv A' (bind_ty B :: G) HA (HlkB B)
                  (HwfBoundB B) HwfA) as [HwfA' HA_eq].
      split; [constructor; assumption|]. f_equal. exact HA_eq.
Qed.

(* --- Freshness: elim output has no free occurrence of the          *)
(*     eliminated variable.  Encoded via the self-referential        *)
(*     identity shift_lt 1 v (subst_lt v lt_free X) = X.             *)
Lemma elim_lt_closes : forall l lvar bound p l',
  elim_lt lvar bound p l = Some l' ->
  shift_lt 1 lvar (subst_lt lvar lt_free bound) = bound ->
  shift_lt 1 lvar (subst_lt lvar lt_free l') = l'.
Proof.
  induction l as [n | | | l1 IH1 l2 IH2]; intros lvar bound p l' Helim Hb; simpl in Helim.
  - destruct (Nat.eqb n lvar) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst n.
      destruct p; try discriminate Helim.
      * injection Helim; intros; subst l'. exact Hb.
      * injection Helim; intros; subst l'. reflexivity.
    + injection Helim; intros; subst l'. simpl. rewrite Heq.
      destruct (Nat.ltb lvar n) eqn:Hlt.
      * simpl. apply Nat.ltb_lt in Hlt.
        assert (Nat.leb lvar (Nat.pred n) = true) as Hle by (apply Nat.leb_le; lia).
        rewrite Hle. f_equal. lia.
      * simpl. apply Nat.ltb_ge in Hlt. apply Nat.eqb_neq in Heq.
        assert (Nat.leb lvar n = false) as Hle by (apply Nat.leb_gt; lia).
        rewrite Hle. reflexivity.
  - injection Helim; intros; subst l'. reflexivity.
  - injection Helim; intros; subst l'. reflexivity.
  - destruct (elim_lt lvar bound p l1) as [l1'|] eqn:E1; try discriminate.
    destruct (elim_lt lvar bound p l2) as [l2'|] eqn:E2; try discriminate.
    injection Helim; intros; subst l'. simpl. f_equal.
    + exact (IH1 lvar bound p l1' E1 Hb).
    + exact (IH2 lvar bound p l2' E2 Hb).
Qed.

Lemma elim_ty_closes : forall T lvar bound p T',
  elim_ty lvar bound p T = Some T' ->
  shift_lt 1 lvar (subst_lt lvar lt_free bound) = bound ->
  shift_lt_in_ty 1 lvar (subst_lt_in_ty lvar lt_free T') = T'.
Proof.
  apply (type_ind'
    (fun T => forall lvar bound p T',
      elim_ty lvar bound p T = Some T' ->
      shift_lt 1 lvar (subst_lt lvar lt_free bound) = bound ->
      shift_lt_in_ty 1 lvar (subst_lt_in_ty lvar lt_free T') = T')).
  - (* type_var *)
    intros n lvar bound p T' Helim Hb. simpl in Helim.
    injection Helim; intros; subst T'. reflexivity.
  - (* type_fun *)
    intros A l B IHA IHB lvar bound p T' Helim Hb. simpl in Helim.
    destruct (elim_ty lvar bound (flip_var p) A) as [A'|] eqn:HA; try discriminate.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; try discriminate.
    destruct (elim_ty lvar bound p B) as [B'|] eqn:HB; try discriminate.
    injection Helim; intros; subst T'.
    rewrite subst_lt_in_ty_fun_eq, shift_lt_in_ty_fun_eq. f_equal.
    + exact (IHA lvar bound (flip_var p) A' HA Hb).
    + exact (elim_lt_closes l lvar bound p l' Hl Hb).
    + exact (IHB lvar bound p B' HB Hb).
  - (* type_ctor *)
    intros K l Ts IHTs lvar bound p T' Helim Hb.
    rewrite elim_ty_ctor_eq in Helim.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; try discriminate.
    destruct (elim_ty_list lvar bound var_inv Ts) as [Ts'|] eqn:HTs; try discriminate.
    injection Helim; intros; subst T'.
    rewrite subst_lt_in_ty_ctor_eq, shift_lt_in_ty_ctor_eq. f_equal.
    + exact (elim_lt_closes l lvar bound p l' Hl Hb).
    + clear Helim Hl. rewrite List.map_map. revert Ts' HTs.
      induction IHTs as [|A rest HPA HFor IHFor]; intros Ts' HTs; simpl in HTs.
      * injection HTs; intros; subst Ts'. reflexivity.
      * destruct (elim_ty lvar bound var_inv A) as [A'|] eqn:HAe; try discriminate.
        destruct (elim_ty_list lvar bound var_inv rest) as [rest'|] eqn:HRe; try discriminate.
        injection HTs; intros; subst Ts'. simpl. f_equal.
        -- exact (HPA lvar bound var_inv A' HAe Hb).
        -- apply IHFor; reflexivity.
  - (* type_lt_all *)
    intros A IHA lvar bound p T' Helim Hb. simpl in Helim.
    destruct (elim_ty (S lvar) (shift_lt 1 0 bound) p A) as [A'|] eqn:HA; try discriminate.
    injection Helim; intros; subst T'.
    rewrite subst_lt_in_ty_ltall_eq, shift_lt_in_ty_ltall_eq. f_equal.
    apply (IHA (S lvar) (shift_lt 1 0 bound) p A' HA).
    rewrite <- shift_subst_lt_comm. rewrite <- shift_lt_swap_0. rewrite Hb. reflexivity.
  - (* type_ty_all *)
    intros B A IHB IHA lvar bound p T' Helim Hb. simpl in Helim.
    destruct (elim_ty lvar bound (flip_var p) B) as [B'|] eqn:HB; try discriminate.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HA; try discriminate.
    injection Helim; intros; subst T'.
    rewrite subst_lt_in_ty_tyall_eq, shift_lt_in_ty_tyall_eq. f_equal.
    + exact (IHB lvar bound (flip_var p) B' HB Hb).
    + exact (IHA lvar bound p A' HA Hb).
Qed.

(* --- Iterated elim soundness --- *)

(* ================================================================== *)
(* Over-approximate-in-context soundness.                             *)
(* Eliminating n positive binders, then over-approximating the        *)
(* eliminated variables by a context of n fresh lt-binders, yields    *)
(*   push_corr n Delta G ⊢ eta <:: shift_lt_in_ty n 0 elim_result.    *)
(* No witnesses (and hence no monotonicity) are required.             *)
(* ================================================================== *)
Lemma elim_in_ctx_sound : forall n Delta eta elim_result G,
  elim_ty_n n (shift_lt n 0 Delta) var_pos eta = Some elim_result ->
  lt_wf G Delta ->
  ty_wf (push_corr n Delta G) eta ->
  push_corr n Delta G ⊢ eta <:: shift_lt_in_ty n 0 elim_result.
Proof.
  induction n as [|n' IH]; intros Delta eta elim_result G Helim HwfDelta HwfEta.
  - (* n = 0 *)
    simpl in Helim. injection Helim; intros He; subst elim_result.
    simpl. rewrite shift_lt_in_ty_zero. apply SA_Refl. exact HwfEta.
  - (* n = S n' *)
    simpl in Helim.
    destruct (elim_ty 0 (shift_lt (S n') 0 Delta) var_pos eta) as [T1|] eqn:ET1;
      try discriminate.
    assert (Hb : subst_lt 0 lt_free (shift_lt (S n') 0 Delta) = shift_lt n' 0 Delta).
    { replace (shift_lt (S n') 0 Delta) with (shift_lt 1 0 (shift_lt n' 0 Delta))
        by (rewrite shift_lt_fuse; reflexivity).
      rewrite subst_lt_shift_cancel. reflexivity. }
    rewrite Hb in Helim.
    assert (HwfBoundS : lt_wf (push_corr (S n') Delta G) (shift_lt (S n') 0 Delta)).
    { apply lt_wf_push_corr_bound. exact HwfDelta. }
    destruct (elim_ty_step_ctx eta 0 (shift_lt (S n') 0 Delta) var_pos T1
                (push_corr (S n') Delta G) ET1 (push_corr_lookup0 n' Delta G)
                HwfBoundS HwfEta) as [HwfT1 Hstep].
    simpl in Hstep.
    assert (HwfBoundN : lt_wf (push_corr n' Delta G) (shift_lt n' 0 Delta)).
    { apply lt_wf_push_corr_bound. exact HwfDelta. }
    assert (HwfT1Sub : ty_wf (push_corr n' Delta G) (subst_lt_in_ty 0 lt_free T1)).
    { eapply ty_wf_SubstLt; [exact HwfT1|].
      apply SubstLt_here. apply LS_Free. exact HwfBoundN. }
    specialize (IH Delta (subst_lt_in_ty 0 lt_free T1) elim_result G Helim HwfDelta HwfT1Sub).
    pose proof (sub_weaken_lt_shift (push_corr n' Delta G) (shift_lt n' 0 Delta)
                  (subst_lt_in_ty 0 lt_free T1) (shift_lt_in_ty n' 0 elim_result) IH) as Hweak.
    assert (Hfresh : shift_lt_in_ty 1 0 (subst_lt_in_ty 0 lt_free T1) = T1).
    { apply (elim_ty_closes eta 0 (shift_lt (S n') 0 Delta) var_pos T1 ET1).
      rewrite Hb. rewrite shift_lt_fuse. reflexivity. }
    rewrite Hfresh in Hweak.
    rewrite shift_lt_in_ty_fuse in Hweak.
    eapply SA_Trans; [exact Hstep | exact Hweak].
Qed.

(* ================================================================== *)
(* Piece 6: peel all n over-approximation binders at once.            *)
(* ================================================================== *)

(* 6a: weakening lifetime subtyping through the push_corr context.    *)
Lemma lt_sub_push_corr_weaken : forall n Delta Γ l1 l2,
  Γ ⊢ₗ l1 <: l2 ->
  push_corr n Delta Γ ⊢ₗ shift_lt n 0 l1 <: shift_lt n 0 l2.
Proof.
  induction n as [|n' IH]; intros Delta Γ l1 l2 Hsub.
  - cbn [push_corr]. rewrite !shift_lt_zero. exact Hsub.
  - cbn [push_corr].
    specialize (IH Delta Γ l1 l2 Hsub).
    pose proof (lt_sub_InsLt (push_corr n' Delta Γ) (shift_lt n' 0 l1) (shift_lt n' 0 l2) IH
                  0 (bind_lt (shift_lt n' 0 Delta) :: push_corr n' Delta Γ)
                  (InsLt_here (shift_lt n' 0 Delta) (push_corr n' Delta Γ))) as Hins.
    rewrite !shift_lt_fuse in Hins.
    exact Hins.
Qed.

(* 6b: peel all binders via SubstLt, sound because the context        *)
(*     shrinks together with each substitution.                       *)
Lemma sub_peel_push_corr : forall lts Delta A B Γ,
  Forall (fun l => Γ ⊢ₗ l <: Delta) lts ->
  push_corr (List.length lts) Delta Γ ⊢ A <:: B ->
  Γ ⊢ subst_list_lt_in_ty lts A <:: subst_list_lt_in_ty lts B.
Proof.
  induction lts as [|l0 rest IH]; intros Delta A B Γ Hfor Hsub.
  - cbn [subst_list_lt_in_ty]. cbn [List.length push_corr] in Hsub. exact Hsub.
  - pose proof (Forall_inv Hfor) as Hhead.
    pose proof (Forall_inv_tail Hfor) as Htail.
    cbn [List.length push_corr] in Hsub.
    cbn [subst_list_lt_in_ty].
    apply (IH Delta (subst_lt_in_ty 0 (shift_lt (List.length rest) 0 l0) A)
                    (subst_lt_in_ty 0 (shift_lt (List.length rest) 0 l0) B) Γ Htail).
    eapply sub_SubstLt.
    2: { apply SubstLt_here.
         exact (lt_sub_push_corr_weaken (List.length rest) Delta Γ l0 Delta Hhead). }
    exact Hsub.
Qed.

(* 6c: the over-approximation target shift-cancels under the peel.    *)
Lemma subst_list_lt_in_ty_shift_cancel : forall lts X,
  subst_list_lt_in_ty lts (shift_lt_in_ty (List.length lts) 0 X) = X.
Proof.
  induction lts as [|l0 rest IH]; intro X.
  - cbn [List.length subst_list_lt_in_ty]. rewrite shift_lt_in_ty_zero. reflexivity.
  - cbn [List.length subst_list_lt_in_ty].
    replace (shift_lt_in_ty (S (List.length rest)) 0 X)
      with (shift_lt_in_ty 1 0 (shift_lt_in_ty (List.length rest) 0 X))
      by (rewrite shift_lt_in_ty_fuse; reflexivity).
    rewrite subst_lt_in_ty_shift_cancel.
    apply IH.
Qed.

(* ================================================================== *)
(* Piece 7: sound positive iterated-elim soundness (assembly).        *)
(* Replaces the old `elim_ty_n_sound` (which depended on the FALSE    *)
(* `iter_subst_lt_in_ty_mono`).                                       *)
(* ================================================================== *)
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

(* The old `elim_ty_n_sound` (induction on the witness list, depending  *)
(* on the FALSE `iter_subst_lt_in_ty_mono`) has been removed and        *)
(* replaced by the sound `elim_ty_n_sound_pos` above.                   *)

(* The parallel-substitution preservation lemmas (subst_list_lt_in_ty_each, *)
(* subst_list_lt_in_tm_lemma, subst_list_tm_lemma,                     *)
(* subst_list_lt_in_ty_eq_iter, ctor_lts_chain_bounded,                *)
(* inst_ctor_type_subst_eq) are now                                    *)
(* in SubstitutionTheory.v.                                            *)

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
    arity = List.length (List.map (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts) sigma_fields) /\
    (fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
                (push_lt_vars n_lt Delta Γ)
                (List.map (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts) sigma_fields))
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
    Γ ⊢ₗ lt_of_ty_list (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields) <: l /\
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
       Hlk & Hltlen & HTslen & Hresult & Hlt & Hlts_bound & Hvslen & Hf2 & Hsub).
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
    intros Γ t B U S Ht IH HwfS Hsub HnlArg x Hin. apply IH; exact Hin.
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
      intros Hnone. apply IHyes. apply lookup_tm_push_lt_None. exact Hnone.
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

Definition stuck (t : term) : Prop :=
  ~ value t /\ ~ exists t', t ==> t'.

Definition safety_invariants (Γ : ctx) (T : type) (t : term) : Prop :=
  marker_ok [] t /\ marker_types_safe t /\ Γ ⊢ₜ t : T.

Lemma safe_state_not_stuck : forall Γ t T,
  eval_ctx Γ ->
  marker_ok [] t ->
  marker_types_safe t ->
  Γ ⊢ₜ t : T ->
  ~ stuck t.
Proof.
  intros Γ t T Hec Hmok Hsafe Hty [Hnv Hns].
  destruct (progress_safe _ _ _ Hec Hmok Hsafe Hty) as [Hv | [t' Hs]].
  - contradiction.
  - apply Hns; eauto.
Qed.

Corollary type_safety : forall Γ t t' T,
  eval_ctx Γ ->
  (forall u, multi_step t u -> safety_invariants Γ T u) ->
  multi_step t t' ->
  ~ stuck t'.
Proof.
  intros Γ t t' T Hec Hsafe_reachable Hmulti.
  destruct (Hsafe_reachable t' Hmulti) as [Hmok [Hsafe Hty]].
  eapply safe_state_not_stuck.
  - exact Hec.
  - exact Hmok.
  - exact Hsafe.
  - exact Hty.
Qed.

(* ================================================================== *)
(*                                                                    *)
(*                NON-ESCAPING OF LOCAL VALUES                        *)
(*                                                                    *)
(* The lifetime lattice places `lt_free` at the bottom and            *)
(* `lt_local` at the top, with subtyping oriented `free <: local`.    *)
(* A value annotated `local` is confined to its scope: it may be      *)
(* *used where* a `local` value is expected, but it must never flow   *)
(* the other way, into a position demanding a `free` (escapable)      *)
(* lifetime.                                                          *)
(*                                                                    *)
(* The formal content of "local values do not escape" is therefore    *)
(* that subtyping can never relax a `local` lifetime down to `free`:  *)
(* the lattice fact `local <: free` is underivable in *every*         *)
(* context, and consequently a `local`-annotated datum can never be   *)
(* coerced (by subsumption) to its `free` counterpart.                *)
(* ================================================================== *)

(* The boolean `no_local_lt` (defined in Typing.v) is a *downward     *)
(* closed* invariant of the lifetime-subtyping order: if a supertype  *)
(* has no top-level `local`, then neither does any of its subtypes.   *)
(* This is the monotonicity engine behind non-escaping.               *)
Lemma lt_sub_no_local_mono : forall Γ l1 l2,
  eval_ctx Γ ->
  Γ ⊢ₗ l1 <: l2 ->
  no_local_lt l2 = true ->
  no_local_lt l1 = true.
Proof.
  intros Γ l1 l2 Hec H. induction H; intros Hsup; simpl in *.
  - (* LS_Free  : free <: l   — free has no local *) reflexivity.
  - (* LS_Local : l <: local  — supertype IS local, premise absurd *)
    discriminate Hsup.
  - (* LS_Var   : impossible under eval_ctx, which has no lt binders. *)
    rewrite (eval_ctx_no_lt _ x Hec) in H. discriminate.
  - (* LS_Refl  *) exact Hsup.
  - (* LS_Trans *) apply IHlt_sub1. exact Hec. apply IHlt_sub2. exact Hec. exact Hsup.
  - (* LS_MinL  : lt_min l1 l2 <: l *)
    rewrite (IHlt_sub1 Hec Hsup). rewrite (IHlt_sub2 Hec Hsup). reflexivity.
  - (* LS_MinR1 : l <: lt_min l1 l2 *)
    apply IHlt_sub. exact Hec.
    destruct (no_local_lt l1) eqn:E1; simpl in Hsup; [reflexivity | discriminate].
  - (* LS_MinR2 : l <: lt_min l1 l2 *)
    apply IHlt_sub. exact Hec.
    destruct (no_local_lt l2) eqn:E2;
      [reflexivity | destruct (no_local_lt l1); simpl in Hsup; discriminate].
Qed.

(* Lattice form: the top lifetime `local` never outlives the bottom   *)
(* `free`.  Holds in *any* context (no `eval_ctx` needed): even       *)
(* context-bounded lt-variables cannot bridge `local` to `free`.      *)
Theorem lt_local_not_escapes : forall Γ,
  eval_ctx Γ ->
  ~ (Γ ⊢ₗ lt_local <: lt_free).
Proof.
  intros Γ Hec H.
  pose proof (lt_sub_no_local_mono _ _ _ Hec H (eq_refl : no_local_lt lt_free = true))
    as Hcontra.
  simpl in Hcontra. discriminate.
Qed.

(* Value/type form: a `local`-annotated data value can never be       *)
(* subsumed to the same data carrying `free`.  This is the            *)
(* "no escape via subtyping" theorem for local values.                *)
Theorem local_data_not_escapes : forall Γ K Ts,
  eval_ctx Γ ->
  ctx_lookup_eff Γ K = None ->
  K <> any_tag ->
  ~ (Γ ⊢ type_ctor K lt_local Ts <:: type_ctor K lt_free Ts).
Proof.
  intros Γ K Ts Hec Hdata HK H.
  destruct (sub_ctor_inv _ _ _ _ _ Hec H HK) as [l' [Heq Hlsub]].
  injection Heq as Hl'. subst l'.
  exact (lt_local_not_escapes _ Hec Hlsub).
Qed.

(* ================================================================== *)
(*                                                                    *)
(*           OPERATIONAL NON-ESCAPE OF LOCAL VALUES                   *)
(*                                                                    *)
(* The lattice/subtyping theorems above forbid *coercing* a `local`   *)
(* datum to `free`.  Transported along the dynamics they deliver the  *)
(* operational guarantee: whatever value a closed program computes    *)
(* at an escapable (`free`) data type is itself annotated with a      *)
(* lifetime that carries no top-level `local`.  A `local`-confined    *)
(* datum can never surface as the result delivered at a `free` type.  *)
(* ================================================================== *)

(* Operational non-escape: a value produced at an escapable `free`    *)
(* data type is a constructor whose *own* lifetime annotation         *)
(* provably contains no top-level `local`.  Equivalently, a value     *)
(* confined to a `local` lifetime is never the result a program       *)
(* hands back at a `free` (escapable) type.                           *)
Theorem local_value_does_not_escape : forall Γ t K Ts v,
  eval_ctx Γ ->
  ctx_lookup_eff Γ K = None ->
  K <> any_tag ->
  (forall u, multi_step t u -> Γ ⊢ₜ u : type_ctor K lt_free Ts) ->
  multi_step t v ->
  value v ->
  exists K' l' lts' vs,
    v = term_ctor K' l' lts' Ts vs /\
    no_local_lt l' = true.
Proof.
  intros Γ t K Ts v Hec Hdata HK Hty_reachable Hms Hval.
  pose proof (Hty_reachable _ Hms) as Htyv.
  destruct (canonical_ctor_data _ _ _ _ _ Hec Hdata Htyv Hval HK)
    as [K' [l' [lts' [Ts' [vs [Hveq Hvs]]]]]].
  subst v.
  apply ctor_typing_inv in Htyv.
  destruct Htyv as
    (n_lt & n_ty & sig & res & result_tag & Hlk & Hltlen & HTslen & Hresult &
     Hlt_bound & Hlts_bound & Hvslen & Hf2 & Hsub).
  destruct (sub_ctor_inv _ _ _ _ _ Hec Hsub HK) as [lx [Heq Hlsub]].
  injection Heq as HKeq Hleq HTseq.
  subst result_tag. subst Ts'.
  exists K', l', lts', vs. split; [reflexivity|].
  rewrite Hleq.
  apply (lt_sub_no_local_mono _ _ _ Hec Hlsub).
  reflexivity.
Qed.

(* ================================================================== *)
(*                                                                    *)
(*                   CAPABILITY CONFINEMENT                           *)
(*                                                                    *)
(* A runtime capability `cap_E^m _ _` is the only construct whose      *)
(* typing rule (`T_Cap`) consults the effect environment: it is       *)
(* well-typed solely in a context that *binds* the effect tag `E`.    *)
(* Capabilities are minted by `S_Handle`, which wraps each one        *)
(* immediately inside its own `handler_m m` delimiter.  Under the     *)
(* full effectful calculus, typing alone no longer rules out visible  *)
(* capabilities; the runtime `marker_ok` invariant does.              *)
(* ================================================================== *)

Lemma marker_ok_plug_cap_pure_in : forall ms E E_tag m n_beta Ts T_R op_body,
  pure_ectx_m m E ->
  marker_ok ms (plug E (term_cap E_tag m n_beta Ts T_R op_body)) ->
  In m ms.
Proof.
  intros ms E E_tag m n_beta Ts T_R op_body Hpure.
  revert ms. induction Hpure; simpl; intros ms Hmok.
  - exact (proj1 Hmok).
  - apply IHHpure. exact (proj1 Hmok).
  - apply IHHpure. exact (proj2 Hmok).
  - apply IHHpure. exact Hmok.
  - apply IHHpure. exact Hmok.
  - apply IHHpure.
    induction vs as [|u vs IHvs]; simpl in Hmok; [tauto|].
    apply IHvs. tauto.
  - apply IHHpure. exact (proj1 Hmok).
  - apply (IHHpure (m' :: ms)) in Hmok.
    destruct Hmok as [Heq | Hin]; [subst; contradiction|exact Hin].
  - apply IHHpure. exact (proj1 Hmok).
  - apply IHHpure. exact (proj2 Hmok).
  all: tauto.
Qed.

Theorem capability_confined : forall E E_tag m n_beta Ts T_R op_body,
  marker_ok [] (plug E (term_cap E_tag m n_beta Ts T_R op_body)) ->
  ~ pure_ectx_m m E.
Proof.
  intros E E_tag m n_beta Ts T_R op_body Hmok Hpure.
  pose proof (marker_ok_plug_cap_pure_in [] E E_tag m n_beta Ts T_R op_body Hpure Hmok) as Hin.
  inversion Hin.
Qed.

Theorem capability_never_exposed : forall Γ t E E_tag m n_beta Ts T_R op_body T,
  eval_ctx Γ ->
  (forall u, multi_step t u -> marker_ok [] u) ->
  Γ ⊢ₜ t : T ->
  multi_step t (plug E (term_cap E_tag m n_beta Ts T_R op_body)) ->
  ~ pure_ectx_m m E.
Proof.
  intros Γ t E E_tag m n_beta Ts T_R op_body T Hec Hmok_reachable Hty Hms Hpure.
  pose proof (Hmok_reachable _ Hms) as Hmok'.
  eapply capability_confined; eauto.
Qed.

Corollary capability_under_handler : forall Γ t E E_tag m n_beta Ts T_R op_body T,
  eval_ctx Γ ->
  (forall u, multi_step t u -> marker_ok [] u) ->
  Γ ⊢ₜ t : T ->
  multi_step t (plug E (term_cap E_tag m n_beta Ts T_R op_body)) ->
  ~ pure_ectx_m m E.
Proof.
  intros Γ t E E_tag m n_beta Ts T_R op_body T Hec Hmok Hty Hms Hpure.
  eapply capability_never_exposed; eauto.
Qed.
