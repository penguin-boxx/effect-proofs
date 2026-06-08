(* ================================================================== *)
(* Mechanized refutation of the axiom `subst_tm_lemma` AS STATED.      *)
(*                                                                    *)
(* The axiom claims (for an ARBITRARY context Γ):                     *)
(*   (bind_tm T1 :: Γ) |- t : T2  ->  value v  ->  Γ |- v : T1  ->    *)
(*       Γ |- subst_tm 0 v t : T2                                     *)
(*                                                                    *)
(* It is FALSE.  Root cause (same capture-hiding family as            *)
(* `subst_lt_in_tm_lemma`): `lt_of_ty_G (type_ty_all _ _) = lt_free`  *)
(* UNDER-approximates a `local` capability captured INSIDE a          *)
(* `term_ty_lam` value (T_TyLam carries NO capture constraint).       *)
(* Substituting such a value inlines it, un-hiding the captured       *)
(* local, which `capture_lt` then picks up with its true `lt_local`   *)
(* lifetime — breaking a `capture_lt <: l` constraint that was        *)
(* satisfiable before (the type-var's contribution read as bottom).   *)
(*                                                                    *)
(* NOTE: the witness context Γ = [bind_tm Cap] is NOT an `eval_ctx`.  *)
(* All call sites of the axiom in Safety.v DO have `eval_ctx Γ` (so   *)
(* every well-typed `v` there is term-closed and the leak cannot      *)
(* arise).  Hence the *fix* is to add the premise `eval_ctx Γ`, which *)
(* is available at every use site — no core typing rule changes.      *)
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
Definition Cap : type := type_ctor K0 lt_local [].   (* a `local` capability type *)
Definition Tf  : type := type_ctor K0 lt_free  [].   (* a closed, no_local type *)
Definition T1  : type := type_ty_all Tf Cap.         (* lt_of_ty_G = lt_free; HIDES Cap *)
Definition A0  : type := type_fun T1 lt_free Tf.      (* the inner lambda's parameter ("launderer") *)
Definition T2  : type := type_fun A0 lt_free Tf.

Definition Gamma : ctx := bind_tm Cap :: nil.        (* cap at index 0 — NOT an eval_ctx *)

Definition vval  : term := term_ty_lam Tf (term_var 0).            (* value; captures cap *)
Definition tbody : term := term_app (term_var 0) (term_var 1).     (* apply param to z *)
Definition tlam  : term := term_lam tbody A0.

(* ------------------------------------------------------------------ *)
(* The three premises of the axiom all hold.                          *)
(* ------------------------------------------------------------------ *)

(* (1)  (bind_tm T1 :: Γ) |- tlam : T2                                 *)
Lemma t_typed : (bind_tm T1 :: Gamma) ⊢ₜ tlam : T2.
Proof.
  unfold tlam, tbody, T2.
  apply T_Lam.
  - (* body : Tf  — apply the parameter (var 0 : A0) to z (var 1 : T1) *)
    eapply T_App.
    + apply T_Var. reflexivity.
    + apply T_Var. reflexivity.
  - (* capture_lt (only z is free; z : T1 contributes the HIDDEN lt_free) <: lt_free *)
    cbn. apply LS_MinL; apply LS_Free.
  - (* no_local_ty Tf = true *)
    reflexivity.
Qed.

(* (2)  value vval                                                    *)
Lemma v_is_value : value vval.
Proof. apply value_ty_lam. Qed.

(* (3)  Γ |- vval : T1   (the type-lambda captures the local `cap`)   *)
Lemma v_typed : Gamma ⊢ₜ vval : T1.
Proof.
  unfold vval, T1.
  apply T_TyLam.
  apply T_Var. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Inversion helpers (through the T_Sub tower).                       *)
(* `lam_typing_inv_cap` KEEPS the capture constraint that the         *)
(* plain `lam_typing_inv` in CounterexampleLtSubst.v drops.           *)
(* ------------------------------------------------------------------ *)
Lemma lam_typing_inv_cap : forall Γ b A T,
  Γ ⊢ₜ term_lam b A : T ->
  exists l B,
    (bind_tm A :: Γ) ⊢ₜ b : B /\
    Γ ⊢ₗ capture_lt Γ b <: l /\
    no_local_ty B = true /\
    Γ ⊢ type_fun A l B <:: T.
Proof.
  intros Γ b A T H. remember (term_lam b A) as t eqn:E. revert b A E.
  induction H; intros b0 A0' E; try discriminate E.
  - (* T_Sub *)
    destruct (IHtyping b0 A0' E) as [l [B [Hb [Hcap [Hnl Hs]]]]].
    exists l, B. split; [exact Hb|]. split; [exact Hcap|]. split; [exact Hnl|].
    eapply SA_Trans; eauto.
  - (* T_Lam *)
    injection E; intros; subst. exists l, B.
    split; [assumption|]. split; [assumption|]. split; [assumption| apply SA_Refl].
Qed.

(* the witness context has no bind_ty entries *)
Lemma no_ty_gamma : forall a, ctx_lookup_ty Gamma a = None.
Proof. reflexivity. Qed.

(* function-type subtyping inversion, valid when Γ has no bind_ty *)
Lemma sub_fun_inv_noty : forall Γ S A l B,
  (forall a, ctx_lookup_ty Γ a = None) ->
  Γ ⊢ S <:: type_fun A l B ->
  exists A' l' B',
    S = type_fun A' l' B' /\
    Γ ⊢ A <:: A' /\ Γ ⊢ₗ l' <: l /\ Γ ⊢ B' <:: B.
Proof.
  intros Γ S A l B Hno Hsub.
  remember (type_fun A l B) as TT eqn:HT. revert A l B HT.
  induction Hsub; intros A0' l0 B0 HT.
  - exists A0', l0, B0. inversion HT; subst. repeat split; auto.
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
(* The reduct the axiom would produce is NOT typeable at T2.          *)
(* ------------------------------------------------------------------ *)

(* Compute the substitution result explicitly: substituting the       *)
(* type-lambda value inlines it INTO the body, so `cap` (a local)      *)
(* now appears as a genuine free term variable of the lambda body.    *)
Lemma subst_compute :
  subst_tm 0 vval tlam
  = term_lam (term_app (term_var 0) (term_ty_lam Tf (term_var 1))) A0.
Proof. reflexivity. Qed.

Lemma reduct_not_typed : ~ (Gamma ⊢ₜ subst_tm 0 vval tlam : T2).
Proof.
  rewrite subst_compute. intros Hty.
  apply lam_typing_inv_cap in Hty.
  destruct Hty as [lc [Bc [Hbody [Hcap [Hnl Hsub]]]]].
  unfold T2 in Hsub.
  destruct (sub_fun_inv_noty _ _ _ _ _ no_ty_gamma Hsub)
    as [A' [l' [B' [Heq [HA [Hl HB]]]]]].
  assert (l' = lc) by congruence. subst l'.
  (* Hcap : Gamma |-l capture_lt Gamma body' <: lc                     *)
  (* Hl   : Gamma |-l lc <: lt_free   (SA_Fun covariant in closure lt) *)
  pose proof (LS_Trans _ _ _ _ Hcap Hl) as Htr.
  pose proof (lt_sub_no_local_mono _ _ _ Htr
                (eq_refl : no_local_lt lt_free = true)) as Hbad.
  (* but the capture contains lt_local (the un-hidden `cap`)           *)
  vm_compute in Hbad. discriminate Hbad.
Qed.

(* ------------------------------------------------------------------ *)
(* Therefore the axiom statement (for arbitrary Γ) is contradictory.  *)
(* ------------------------------------------------------------------ *)
Theorem subst_tm_lemma_is_false :
  ~ (forall Γ T1 t T2 v,
        (bind_tm T1 :: Γ) ⊢ₜ t : T2 ->
        value v ->
        Γ ⊢ₜ v : T1 ->
        Γ ⊢ₜ subst_tm 0 v t : T2).
Proof.
  intros Hax.
  apply reduct_not_typed.
  apply (Hax Gamma T1 tlam T2 vval).
  - exact t_typed.
  - exact v_is_value.
  - exact v_typed.
Qed.
