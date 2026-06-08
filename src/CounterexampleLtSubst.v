(* ================================================================== *)
(* Mechanized refutation of the axiom `subst_lt_in_tm_lemma`.          *)
(*                                                                    *)
(* The axiom claims:                                                  *)
(*   (bind_lt D :: G) |- t : T  ->  G |-l D' <: D  ->                 *)
(*       G |- subst_lt_in_tm 0 D' t : subst_lt_in_ty 0 D' T           *)
(*                                                                    *)
(* It is invoked (Safety.v, T_LtApp preservation) with D = lt_local   *)
(* and D' = the lt-application argument, discharged by `LS_Local`     *)
(* (l <: lt_local for ALL l).  So D' is arbitrary and may be          *)
(* lt_local itself.  Substituting lt_local into a `no_local` return   *)
(* type breaks the T_Lam side-condition `no_local_ty B = true`, and   *)
(* the result is untypeable.                                          *)
(* ================================================================== *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import SubstitutionTheory.
Require Import Safety.

(* ------------------------------------------------------------------ *)
(* Concrete witnesses                                                 *)
(* ------------------------------------------------------------------ *)
Definition A2 : type := type_var 0.
Definition Ain : type := type_fun A2 (lt_var 0) A2.   (* mentions the lt-binder *)
Definition inner : term := term_lam (term_var 0) Ain. (* body of the lt-lambda *)
Definition N : term := term_lt_lam inner.
Definition Tinner : type := type_fun Ain lt_free Ain.

(* The lt-lambda body is well typed under bind_lt lt_local. *)
Lemma inner_typed : (bind_lt lt_local :: nil) ⊢ₜ inner : Tinner.
Proof.
  apply T_Lam.
  - apply T_Var. reflexivity.
  - cbn. apply LS_Free.
  - reflexivity.
Qed.

(* So `term_lt_app N lt_local` is well typed (T_LtApp puts no          *)
(* constraint on the lifetime argument).                              *)
Lemma source_typed :
  nil ⊢ₜ term_lt_app N lt_local : subst_lt_in_ty 0 lt_local Tinner.
Proof.
  eapply T_LtApp. apply T_LtLam. apply inner_typed.
Qed.

(* ------------------------------------------------------------------ *)
(* Small inversion helpers (through the T_Sub tower)                  *)
(* ------------------------------------------------------------------ *)
Lemma var_typing_inv : forall Γ x T,
  Γ ⊢ₜ term_var x : T ->
  exists T0, ctx_lookup_tm Γ x = Some T0 /\ Γ ⊢ T0 <:: T.
Proof.
  intros Γ x T H. remember (term_var x) as t eqn:E. revert x E.
  induction H; intros x0 E; try discriminate E.
  - injection E; intros; subst. exists T. split; [assumption | apply SA_Refl].
  - destruct (IHtyping x0 E) as [T0 [Hl Hs]].
    exists T0. split; [assumption | eapply SA_Trans; eauto].
Qed.

Lemma lam_typing_inv : forall Γ b A T,
  Γ ⊢ₜ term_lam b A : T ->
  exists l B,
    (bind_tm A :: Γ) ⊢ₜ b : B /\ no_local_ty B = true /\
    Γ ⊢ type_fun A l B <:: T.
Proof.
  intros Γ b A T H. remember (term_lam b A) as t eqn:E. revert b A E.
  induction H; intros b0 A0 E; try discriminate E.
  - destruct (IHtyping b0 A0 E) as [l [B [Hb [Hnl Hs]]]].
    exists l, B. split; [exact Hb|]. split; [exact Hnl|]. eapply SA_Trans; eauto.
  - injection E; intros; subst. exists l, B.
    split; [assumption|]. split; [assumption| apply SA_Refl].
Qed.

(* the contexts we use have no bind_ty entries *)
Lemma no_ty_nil : forall a, ctx_lookup_ty nil a = None.
Proof. reflexivity. Qed.
Lemma no_ty_tm : forall A a, ctx_lookup_ty (bind_tm A :: nil) a = None.
Proof. reflexivity. Qed.

(* sub_fun_inv (from Safety) but valid in any context without bind_ty *)
Lemma sub_fun_inv_noty : forall Γ S A l B,
  (forall a, ctx_lookup_ty Γ a = None) ->
  Γ ⊢ S <:: type_fun A l B ->
  exists A' l' B',
    S = type_fun A' l' B' /\
    Γ ⊢ A <:: A' /\ Γ ⊢ₗ l' <: l /\ Γ ⊢ B' <:: B.
Proof.
  intros Γ S A l B Hno Hsub.
  remember (type_fun A l B) as TT eqn:HT. revert A l B HT.
  induction Hsub; intros A0 l0 B0 HT.
  - exists A0, l0, B0. inversion HT; subst. repeat split; auto.
  - subst T.
    destruct (IHHsub2 Hno _ _ _ eq_refl) as [A1 [l1 [B1 [HeqU [HAa [Hla HBa]]]]]]; subst.
    destruct (IHHsub1 Hno _ _ _ eq_refl) as [A3 [l3 [B3 [HeqS [HAb [Hlb HBb]]]]]]; subst.
    exists A3, l3, B3. repeat split; eauto.
  - match goal with H : ctx_lookup_ty _ _ = Some _ |- _ =>
      rewrite Hno in H; discriminate H end.
  - discriminate HT.
  - discriminate HT.
  - injection HT; intros; subst. exists A', l, B. repeat split; auto.
  - discriminate HT.
  - discriminate HT.
Qed.

(* ------------------------------------------------------------------ *)
(* The reduct (what the axiom would produce / what S_LtBeta computes)  *)
(* is NOT typeable at the required type.                              *)
(* ------------------------------------------------------------------ *)
Lemma reduct_not_typed :
  ~ (nil ⊢ₜ subst_lt_in_tm 0 lt_local inner
          : subst_lt_in_ty 0 lt_local Tinner).
Proof.
  cbn [subst_lt_in_tm subst_lt_in_ty subst_lt Nat.eqb inner Ain A2 Tinner].
  intros Hty.
  apply lam_typing_inv in Hty.
  destruct Hty as [l [B [Hbody [Hnl Hsub]]]].
  (* outer: B <:: type_fun (type_var 0) lt_local (type_var 0) *)
  destruct (sub_fun_inv_noty _ _ _ _ _ no_ty_nil Hsub)
    as [A' [l' [B' [Heq [_ [_ HBcod]]]]]].
  assert (B' = B) by congruence. subst B'.
  (* HBcod : nil |- B <:: type_fun (type_var 0) lt_local (type_var 0) *)
  (* var: type_fun (type_var 0) lt_local (type_var 0) <:: B *)
  apply var_typing_inv in Hbody.
  destruct Hbody as [T0 [Hlk HBpB]].
  cbn in Hlk. injection Hlk; intros; subst T0.
  (* HBpB : [bind_tm Bp] |- Bp <:: B *)
  (* B is a function type, with head lifetime l'' >= lt_local *)
  destruct (sub_fun_inv_noty _ _ _ _ _ no_ty_nil HBcod)
    as [A'' [l'' [B'' [HeqB [_ [_ _]]]]]].
  rewrite HeqB in Hnl, HBpB.
  destruct (sub_fun_inv_noty _ _ _ _ _ (no_ty_tm _) HBpB)
    as [A3 [l3 [B3 [Heq3 [_ [Hl3 _]]]]]].
  assert (l3 = lt_local) by congruence. subst l3.
  (* Hl3 : [bind_tm Bp] |-l lt_local <: l'' *)
  (* but no_local_ty B = true forces no_local_lt l'' = true *)
  cbn in Hnl.
  apply andb_prop in Hnl. destruct Hnl as [_ Hnl].
  apply andb_prop in Hnl. destruct Hnl as [Hnl _].
  pose proof (lt_sub_no_local_mono _ _ _ Hl3 Hnl) as Hbad.
  cbn in Hbad. discriminate Hbad.
Qed.

(* ------------------------------------------------------------------ *)
(* Therefore the axiom statement is contradictory.                    *)
(* ------------------------------------------------------------------ *)
Theorem subst_lt_in_tm_lemma_is_false :
  ~ (forall Γ Δ t T Δ',
        (bind_lt Δ :: Γ) ⊢ₜ t : T ->
        Γ ⊢ₗ Δ' <: Δ ->
        Γ ⊢ₜ subst_lt_in_tm 0 Δ' t : subst_lt_in_ty 0 Δ' T).
Proof.
  intros Hax.
  apply reduct_not_typed.
  apply (Hax nil lt_local inner Tinner lt_local).
  - apply inner_typed.
  - apply LS_Local.
Qed.
