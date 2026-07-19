Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import TypingInv.
Require Import Decide.
Require Import Examples.
Require Import ExamplesProofs.

Import CoreNotation.

(* ================================================================== *)
(*                                                                    *)
(*        GENUINE REJECTION OF COMPLETE OFFENDING TERMS               *)
(*                                                                    *)
(* The witnesses in Examples.v certify that individual PREMISES of    *)
(* the typing rules are underivable.  This file states rejection at   *)
(* the level the paper claims it: complete offending TERMS have no    *)
(* typing derivation at their intended escapable interface.           *)
(*                                                                    *)
(* Each negative theorem comes with a positive companion showing the  *)
(* same construction is accepted at its confined interface — the      *)
(* system rejects the ESCAPE, not the construction.                   *)
(*                                                                    *)
(* Proof method: the T_Sub-closed inversion lemmas (TypingInv.v)      *)
(* expose the offending premise of ANY derivation; the reflected      *)
(* decider (Decide.v) then refutes it by computation.                 *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Context plumbing: the example contexts (and their term-binder      *)
(* extensions) have no type and no lifetime binders, so the noty-     *)
(* conditioned subtyping inversions and the lattice decider apply.    *)
(* ------------------------------------------------------------------ *)

Lemma data_ctx_no_ty : forall α, ctx_lookup_ty data_ctx α = None.
Proof. intro α; reflexivity. Qed.

Lemma full_ctx_no_ty : forall α, ctx_lookup_ty full_ctx α = None.
Proof. intro α; reflexivity. Qed.

Lemma full_ctx_tm_no_ty : forall T α,
  ctx_lookup_ty (bind_tm T :: full_ctx) α = None.
Proof. intros T α; reflexivity. Qed.

Lemma full_ctx_lt_ctx_wf : lt_ctx_wf full_ctx.
Proof. intros x Δ H; vm_compute in H; discriminate. Qed.

Lemma full_ctx_tm_lt_ctx_wf : forall T, lt_ctx_wf (bind_tm T :: full_ctx).
Proof. intros T x Δ H; vm_compute in H; discriminate. Qed.

(* Typing inversion for variables, closed under subsumption.          *)
Lemma var_typing_inv : forall Γ x T,
  Γ ⊢ₜ term_var x : T ->
  exists S, ctx_lookup_tm Γ x = Some S /\ Γ ⊢ S <:: T.
Proof.
  intros Γ x T H.
  remember (term_var x) as t eqn:Ht.
  induction H; try discriminate Ht.
  - (* T_Var *)
    injection Ht as ->.
    eexists; split; [eassumption | apply SA_Refl; assumption].
  - (* T_Sub *)
    destruct (IHtyping Ht) as [S [Hlk Hsub]].
    exists S; split; [exact Hlk | eapply SA_Trans; eauto].
Qed.

(* ================================================================== *)
(* 1. leak_reader: returning the capability out of its handler        *)
(*                                                                    *)
(*   handle cap : Reader<Unit> { op ask(x) ... } in Some(cap)         *)
(*                                                                    *)
(* The handler body computes Some(cap) and the handle is annotated    *)
(* to deliver it at the escapable interface                           *)
(*   leak_ty = Option'free (Reader'local Unit).                       *)
(* T_Handle demands `lt_of_ty_G Γ T_B <: lt_free` for the body type,  *)
(* and leak_ty's Reader field is local, so NO typing derivation       *)
(* exists — at leak_ty or at any other type.                          *)
(* ================================================================== *)

Definition leak_ty : type := T_Option `Lf (T_Reader `Ll T_Unit).

Definition leak_reader : term :=
  term_handle Reader_tag 0 [T_Unit] leak_ty leak_ty
    ($$ 0)
    (some_v (T_Reader `Ll T_Unit) ($$ 0)).

Theorem leak_reader_rejected : forall T,
  ~ (full_ctx ⊢ₜ leak_reader : T).
Proof.
  intros T H.
  apply handle_typing_inv in H.
  destruct H as (n_α & sig & ret & sigβ & retβ &
                 _ & _ & _ & _ & _ & Hnl & _).
  revert Hnl.
  apply nolocb_false_rejects.
  - exact full_ctx_lt_ctx_wf.
  - solve_wf.
  - vm_compute; reflexivity.
Qed.

(* The reviewer-facing instance: rejection at the intended free       *)
(* interface itself.                                                  *)
Corollary leak_reader_rejected_at_free :
  ~ (full_ctx ⊢ₜ leak_reader : leak_ty).
Proof. apply leak_reader_rejected. Qed.

(* Positive companion: the very value the body computes — the         *)
(* capability wrapped in Some — is well-typed INSIDE the handler      *)
(* (in the body's context, at the very same type).  Only the          *)
(* boundary crossing is rejected, not the construction.               *)
Theorem some_capability_typable_inside :
  (bind_tm (T_Reader `Ll T_Unit) :: full_ctx)
    ⊢ₜ some_v (T_Reader `Ll T_Unit) ($$ 0) : leak_ty.
Proof.
  unfold some_v, leak_ty. solve_ctor.
Qed.

(* ================================================================== *)
(* 2. get on a state of local readers                                 *)
(*                                                                    *)
(* The testWithState scenario: a State handler instantiated at        *)
(*   S = Option'free (Reader'local Unit)                              *)
(* is itself typable (T_Handle constrains only T_B), but EVERY get /  *)
(* put operation on its capability is rejected: T_Perform's noloc     *)
(* premise on the instantiated signature Cmd'free S fails because S   *)
(* buries a local Reader.  The handler is accepted; the operations    *)
(* that would move local state across the boundary are not.           *)
(* ================================================================== *)

Definition leak_state_cap_ty : type := T_State `Ll leak_ty.

Definition get_local_reader : term :=
  term_perform ($$ 0) [] leak_ty (term_ctor get_tag `Lf [] [leak_ty] []).

Theorem get_local_reader_rejected : forall T,
  ~ ((bind_tm leak_state_cap_ty :: full_ctx) ⊢ₜ get_local_reader : T).
Proof.
  intros T H.
  apply perform_typing_inv in H.
  destruct H as (E & Δ & Ts & n_α & n_β & sig & ret & sig_inst &
                 Hrecv & Heff & _ & _ & _ & _ & Hsi & Hnlsi & _).
  (* pin the receiver's effect type: the capability variable's bound  *)
  (* is a State constructor, and constructor subtyping preserves tag  *)
  (* and (invariant) type arguments.                                  *)
  apply var_typing_inv in Hrecv.
  destruct Hrecv as [S [Hlk Hsub]].
  cbn in Hlk. injection Hlk as HeqS. subst S.
  assert (HE : E <> any_tag).
  { intros ->. vm_compute in Heff. discriminate. }
  destruct (sub_ctor_inv_noty _ _ _ _ _ (full_ctx_tm_no_ty _) Hsub HE)
    as [l' [Heq _]].
  unfold leak_state_cap_ty, T_State in Heq.
  injection Heq as HeqE Heql HeqTs. subst E l' Ts.
  vm_compute in Heff. injection Heff as Hnα Hnβ Hsig Hret.
  subst n_α n_β sig ret. subst sig_inst.
  revert Hnlsi.
  apply nolocb_false_rejects.
  - apply full_ctx_tm_lt_ctx_wf.
  - cbn. solve_wf.
  - vm_compute; reflexivity.
Qed.

(* Positive companion: the identical perform shape at an escapable    *)
(* state type is accepted — [typed_withState_example]                 *)
(* (ExamplesProofs.v) types a program performing get and put on a     *)
(* State<Nat'free> capability.                                        *)

(* ================================================================== *)
(* 3. crashBox: the local payload cannot be coerced free              *)
(*                                                                    *)
(* Box's field at a local instantiation, Option'local (Nat'local),    *)
(* can never be subsumed to its free counterpart: constructor         *)
(* subtyping is covariant only in the top-level lifetime and          *)
(* INVARIANT in the type arguments, and Nat'local ≠ Nat'free.  This   *)
(* is the subtyping face of [rejected_crashBox] (whose witness        *)
(* refutes the noloc premise by certified decision).                  *)
(* ================================================================== *)

Theorem local_box_payload_not_coercible :
  ~ (data_ctx ⊢ T_Option `Ll (T_Nat `Ll) <:: T_Option `Lf (T_Nat `Lf)).
Proof.
  intros H.
  assert (HK : option_tag <> any_tag).
  { intro Hk; vm_compute in Hk; discriminate. }
  destruct (sub_ctor_inv_noty _ _ _ _ _ data_ctx_no_ty H HK)
    as [l' [Heq _]].
  unfold T_Option, T_Nat in Heq.
  discriminate Heq.
Qed.

(* ================================================================== *)
(* 4. Capability captured by a closure                                *)
(*                                                                    *)
(* A lambda whose body performs on a captured capability is typable — *)
(* but only at closure lifetime `local`.  T_Lam's capture premise     *)
(* `Γ ⊢ₗ capture_lt Γ body <: l` folds the capability variable's      *)
(* (local) type lifetime into the closure lifetime, so annotating     *)
(* the closure escapable is rejected.  Precision pair on the SAME     *)
(* term: accepted at `-{local}->`, rejected at `-{free}->`.           *)
(* ================================================================== *)

(* Typing inversion for lambdas RETAINING the capture premise         *)
(* (Narrowing.v's [lam_typing_inv] drops it).                         *)
Lemma lam_typing_inv_capture : forall Γ body A T,
  Γ ⊢ₜ term_lam body A : T ->
  exists l B,
    (bind_tm A :: Γ) ⊢ₜ body : B /\
    Γ ⊢ₗ capture_lt Γ body <: l /\
    Γ ⊢ type_fun A l B <:: T.
Proof.
  intros Γ body A T Hty.
  remember (term_lam body A) as t eqn:Ht.
  induction Hty; try discriminate Ht.
  - (* T_Sub *)
    subst. destruct (IHHty eq_refl) as [l0 [B0 [Hbody [Hcap Hsub]]]].
    exists l0, B0; repeat split; auto. eapply SA_Trans; eauto.
  - (* T_Lam *)
    injection Ht as -> ->.
    exists l, B; repeat split; auto.
    apply SA_Refl. constructor; auto.
    eapply proj2, lt_sub_wf; eassumption.
Qed.

(* Function-subtyping inversion under a no-type-variable context      *)
(* (the eval_ctx-conditioned [sub_fun_inv] generalised the same way   *)
(* [sub_ctor_inv_noty] generalises [sub_ctor_inv]).                   *)
Lemma sub_fun_inv_noty : forall Γ S A l B,
  (forall α, ctx_lookup_ty Γ α = None) ->
  Γ ⊢ S <:: type_fun A l B ->
  exists A' l' B',
    S = type_fun A' l' B' /\
    Γ ⊢ A <:: A' /\
    Γ ⊢ₗ l' <: l /\
    Γ ⊢ B' <:: B.
Proof.
  intros Γ S A l B Hnoty Hsub.
  remember (type_fun A l B) as T eqn:HT.
  revert A l B HT.
  induction Hsub; intros A0 l0 B0 HT.
  - (* Refl *) inversion HT; subst. inversion H; subst.
    exists A0, l0, B0. repeat split;
      try (apply SA_Refl; assumption);
      try (apply LS_Refl; assumption).
  - (* Trans *) subst T.
    destruct (IHHsub2 Hnoty _ _ _ eq_refl) as [A1 [l1 [B1 [HeqU [HAa [Hla HBa]]]]]]; subst.
    destruct (IHHsub1 Hnoty _ _ _ eq_refl) as [A2 [l2 [B2 [HeqS [HAb [Hlb HBb]]]]]]; subst.
    exists A2, l2, B2. repeat split; eauto.
  - (* VarCtx *) subst. rewrite Hnoty in H. discriminate.
  - (* Data *) discriminate HT.
  - (* Any *) discriminate HT.
  - (* Fun *) injection HT; intros HB0 Hl0 HA0; subst.
    exists A', l, B; repeat split; auto.
  - (* LtAll *) discriminate HT.
  - (* TyAll *) discriminate HT.
Qed.

Definition capture_ctx : ctx := bind_tm (T_Reader `Ll T_Unit) :: full_ctx.

Definition ask_closure : term :=
  λ: T_Unit \\ term_perform ($$ 1) [] T_Unit ($$ 0).

Theorem ask_closure_rejected_at_free : forall B,
  ~ (capture_ctx ⊢ₜ ask_closure : (T_Unit -{ `Lf }-> B)).
Proof.
  intros B H.
  apply lam_typing_inv_capture in H.
  destruct H as [l [B0 [_ [Hcap Hsub]]]].
  destruct (sub_fun_inv_noty _ _ _ _ _ (full_ctx_tm_no_ty _) Hsub)
    as [A' [l' [B' [Heq [_ [Hl _]]]]]].
  injection Heq as HA Hll HB. subst A' l' B'.
  assert (Hfree : capture_ctx ⊢ₗ
            capture_lt capture_ctx (term_perform ($$ 1) [] T_Unit ($$ 0))
            <: lt_free)
    by (eapply LS_Trans; eauto).
  apply lt_subb_complete in Hfree.
  vm_compute in Hfree. discriminate.
Qed.

Theorem ask_closure_typable_local :
  capture_ctx ⊢ₜ ask_closure : (T_Unit -{ `Ll }-> T_Unit).
Proof.
  apply T_Lam.
  - solve_wf.
  - solve_wf.
  - eapply T_Perform with (Ts := [T_Unit]) (Ss := []).
    + solve_var.
    + cbn; reflexivity.
    + reflexivity.
    + reflexivity.
    + constructor.
    + constructor.
    + reflexivity.
    + cbn. solve_lt.
    + cbn; reflexivity.
    + solve_wf.
    + cbn. solve_var.
  - apply LS_Local. solve_wf.
Qed.

(* ================================================================== *)
(* 5. Capability nested through two data constructors                 *)
(*                                                                    *)
(* Depth does not launder locality: Some(Some(cap)) is typable        *)
(* inside the handler, and the doubly-nested delivery type is         *)
(* rejected at the boundary exactly as the singly-nested one.         *)
(* ================================================================== *)

Definition leak2_ty : type :=
  T_Option `Lf (T_Option `Lf (T_Reader `Ll T_Unit)).

Definition leak_reader2 : term :=
  term_handle Reader_tag 0 [T_Unit] leak2_ty leak2_ty
    ($$ 0)
    (some_v (T_Option `Lf (T_Reader `Ll T_Unit))
            (some_v (T_Reader `Ll T_Unit) ($$ 0))).

Theorem leak_reader2_rejected : forall T,
  ~ (full_ctx ⊢ₜ leak_reader2 : T).
Proof.
  intros T H.
  apply handle_typing_inv in H.
  destruct H as (n_α & sig & ret & sigβ & retβ &
                 _ & _ & _ & _ & _ & Hnl & _).
  revert Hnl.
  apply nolocb_false_rejects.
  - exact full_ctx_lt_ctx_wf.
  - solve_wf.
  - vm_compute; reflexivity.
Qed.

Theorem some_some_capability_typable_inside :
  (bind_tm (T_Reader `Ll T_Unit) :: full_ctx)
    ⊢ₜ some_v (T_Option `Lf (T_Reader `Ll T_Unit))
              (some_v (T_Reader `Ll T_Unit) ($$ 0)) : leak2_ty.
Proof.
  unfold some_v, leak2_ty.
  repeat first
    [ solve_var | solve_lt | progress solve_wf | progress cbn
    | apply Forall2_nil | apply Forall_nil
    | apply Forall2_cons | apply Forall_cons
    | eapply T_Ctor; cbn; try reflexivity ].
Qed.

(* ================================================================== *)
(* 6. The ∀-conservatism false positive, measured                     *)
(*                                                                    *)
(* [lt_of_ty] sends every quantified type to [lt_local]               *)
(* (Typing.v), so a CLOSED, capability-free polymorphic value is      *)
(* conservatively classified local and can never cross a handler      *)
(* boundary — a genuine precision limitation of the analysis, not a   *)
(* soundness issue.  We mechanize the pair: the polymorphic identity  *)
(* is well-typed, yet its type fails the noloc check.                 *)
(* ================================================================== *)

Lemma data_ctx_lt_ctx_wf : lt_ctx_wf data_ctx.
Proof. intros x Δ H; vm_compute in H; discriminate. Qed.

Definition poly_id_ty : type :=
  type_ty_all (T_Any `Lf) ((`T 0) -{ `Lf }-> (`T 0)).

Definition poly_id : term :=
  Λt: T_Any `Lf \\ (λ: `T 0 \\ $$ 0).

Theorem typed_poly_id : data_ctx ⊢ₜ poly_id : poly_id_ty.
Proof.
  apply T_TyLam.
  - solve_wf.
  - solve_wf.
  - reflexivity.
  - apply T_Lam.
    + solve_wf.
    + solve_wf.
    + solve_var.
    + cbn. solve_lt.
Qed.

(* The false positive: a closed, harmless value whose type the        *)
(* lifetime analysis nevertheless classifies as local.                *)
Theorem poly_id_conservatively_local :
  ~ (data_ctx ⊢ₗ lt_of_ty_G data_ctx poly_id_ty <: lt_free).
Proof.
  apply nolocb_false_rejects.
  - exact data_ctx_lt_ctx_wf.
  - solve_wf.
  - vm_compute; reflexivity.
Qed.
