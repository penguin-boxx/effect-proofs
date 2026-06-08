(* ================================================================== *)
(* Mechanized refutation of the axiom `subst_ty_in_tm_lemma`.          *)
(*                                                                    *)
(* The axiom claims:                                                  *)
(*   (bind_ty B :: G) |- t : T  ->  G |- S <:: B  ->                  *)
(*       G |- subst_ty_in_tm 0 S t : subst_ty 0 S T                   *)
(*                                                                    *)
(* It is the type-beta preservation step.  The only constraint on the *)
(* type argument S is `S <:: B`, and a type variable's bound B may be *)
(* `Any@local` (the top type), so S is essentially arbitrary -- it may *)
(* be a FUNCTION TYPE whose closure lifetime is `lt_local`.           *)
(*                                                                    *)
(* `no_local_ty (type_var _) = true`, so a lambda whose return type is *)
(* a bare type variable passes the T_Lam side-condition.  Substituting *)
(* a `local` type for that variable un-hides the local in the         *)
(* codomain, breaking `no_local_ty B = true`, and the result is        *)
(* untypeable -- exactly the same leak family as subst_lt_in_tm_lemma. *)
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
Definition K0 : ctor_tag := 1.                       (* a non-`any` tag *)
Definition Tf : type := type_ctor K0 lt_free [].     (* a no-local leaf  *)
Definition Sloc : type := type_fun Tf lt_local Tf.   (* local closure!   *)
Definition Bnd : type := type_ctor any_tag lt_local []. (* Any@local = top *)

(* t = lambda whose annotation AND return type are the abstract var a. *)
Definition tbody : term := term_var 0.
Definition tlam  : term := term_lam tbody (type_var 0).
Definition Tlam  : type := type_fun (type_var 0) lt_free (type_var 0).

(* The lambda is well typed under the bound binder (the bound is never  *)
(* used: typing the lambda only needs `no_local_ty (type_var 0)=true`). *)
Lemma t_typed : (bind_ty Bnd :: nil) ⊢ₜ tlam : Tlam.
Proof.
  unfold tlam, tbody, Tlam.
  apply T_Lam.
  - apply T_Var. reflexivity.
  - cbn. apply LS_Free.
  - reflexivity.
Qed.

(* S <:: B : even the most permissive bound (Any@local) admits the     *)
(* local function type Sloc.                                           *)
Lemma s_sub_b : nil ⊢ Sloc <:: Bnd.
Proof.
  unfold Sloc, Bnd. apply SA_Any. cbn. apply LS_Refl.
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
(* The reduct (what the axiom would produce / what S_TyBeta computes)  *)
(* is NOT typeable at the required type.                              *)
(* ------------------------------------------------------------------ *)
Lemma reduct_not_typed :
  ~ (nil ⊢ₜ subst_ty_in_tm 0 Sloc tlam : subst_ty 0 Sloc Tlam).
Proof.
  unfold tlam, tbody, Tlam.
  cbn [subst_ty_in_tm subst_ty Nat.eqb].
  intros Hty.
  apply lam_typing_inv in Hty.
  destruct Hty as [l [B [Hbody [Hnl Hsub]]]].
  (* Hsub : nil |- type_fun Sloc l B <:: type_fun Sloc lt_free Sloc *)
  destruct (sub_fun_inv_noty _ _ _ _ _ no_ty_nil Hsub)
    as [A' [l' [B' [Heq [_ [_ HBcod]]]]]].
  assert (B' = B) by congruence. subst B'.
  (* HBcod : nil |- B <:: Sloc *)
  apply var_typing_inv in Hbody.
  destruct Hbody as [T0 [Hlk HBpB]].
  cbn in Hlk. injection Hlk; intros; subst T0.
  (* HBpB : [bind_tm Sloc] |- Sloc <:: B *)
  (* expose Sloc as a function type and learn B is one too *)
  unfold Sloc in HBcod.
  destruct (sub_fun_inv_noty _ _ _ _ _ no_ty_nil HBcod)
    as [A'' [l'' [B'' [HeqB [_ [_ _]]]]]].
  rewrite HeqB in Hnl, HBpB.
  unfold Sloc in HBpB.
  destruct (sub_fun_inv_noty _ _ _ _ _ (no_ty_tm _) HBpB)
    as [A3 [l3 [B3 [Heq3 [_ [Hl3 _]]]]]].
  assert (l3 = lt_local) by congruence. subst l3.
  (* Hl3 : [bind_tm Sloc] |-l lt_local <: l'' *)
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
Theorem subst_ty_in_tm_lemma_is_false :
  ~ (forall Γ B t T S,
        (bind_ty B :: Γ) ⊢ₜ t : T ->
        Γ ⊢ S <:: B ->
        Γ ⊢ₜ subst_ty_in_tm 0 S t : subst_ty 0 S T).
Proof.
  intros Hax.
  apply reduct_not_typed.
  apply (Hax nil Bnd tlam Tlam Sloc).
  - apply t_typed.
  - apply s_sub_b.
Qed.
