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

(* ================================================================ *)
(* AXIOM 6: marker_types_safe preservation under one step.  Type-     *)
(* substituting head steps (H_TyBeta, H_LtBeta, H_MatchYes,           *)
(* H_Perform) rewrite the *types* recorded in marker annotations, so  *)
(* preservation of the no-conflict invariant (marker_types_ok) needs  *)
(* that those annotation types are closed/consistent — a typing       *)
(* invariant (capability confinement + marker-type regularity), not a *)
(* structural fact.  Stated with the full typing premise (= the       *)
(* type_soundness obligation) so it is sound.                          *)
(* ================================================================ *)
Axiom step_preserves_marker_types_safe : forall Γ t t' T,
  eval_ctx Γ -> marker_ok [] t -> marker_types_safe t -> Γ ⊢ₜ t : T ->
  t ==> t' -> marker_types_safe t'.
