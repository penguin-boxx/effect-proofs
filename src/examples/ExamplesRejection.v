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
