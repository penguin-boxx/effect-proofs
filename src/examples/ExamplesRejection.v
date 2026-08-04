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
Require Import ExamplesTactics.

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

Lemma state_ctx_tm_no_ty : forall T α,
  ctx_lookup_ty (bind_tm T :: state_ctx) α = None.
Proof. intros T α; reflexivity. Qed.

Lemma state_ctx_tm_lt_ctx_wf : forall T, lt_ctx_wf (bind_tm T :: state_ctx).
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
  term_handle Reader_tag [T_Unit] leak_ty leak_ty
    [(0, ($$ 1) @· ($$ 0))]
    (some_v (T_Reader `Ll T_Unit) ($$ 0)).

Theorem leak_reader_rejected : forall T,
  ~ (full_ctx ⊢ₜ leak_reader : T).
Proof.
  intros T H.
  apply handle_typing_inv in H.
  destruct H as (n_α & ops & _ & _ & _ & _ & _ & Hnl & _).
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
(* 2. put on a state of local readers                                 *)
(*                                                                    *)
(* The testWithState scenario: a State handler instantiated at        *)
(*   S = Option'free (Reader'local Unit)                              *)
(* is itself typable (T_Handle constrains only T_B), but the put      *)
(* operation on its capability — the one that would move the local    *)
(* state OUT across the boundary — is rejected: T_Perform's noloc     *)
(* premise on the instantiated signature (= S itself) fails because   *)
(* S buries a local Reader.  (get's argument is Unit and its result   *)
(* flows INWARD, into the delimited program, so there is nothing for  *)
(* T_Perform to reject on get.)                                       *)
(* ================================================================== *)

Definition leak_state_cap_ty : type := T_State `Ll leak_ty.

Definition put_local_reader : term :=
  term_perform ($$ 0) 1 [] T_Unit (none_v (T_Reader `Ll T_Unit)).

Theorem put_local_reader_rejected : forall T,
  ~ ((bind_tm leak_state_cap_ty :: state_ctx) ⊢ₜ put_local_reader : T).
Proof.
  intros T H.
  apply perform_typing_inv in H.
  destruct H as (E & Δ & Ts & n_α & ops & n_β & sig & ret & sig_inst &
                 Hrecv & Heff & Hnth & _ & _ & _ & _ & Hsi & Hnlsi & _).
  (* pin the receiver's effect type: the capability variable's bound  *)
  (* is a State constructor, and constructor subtyping preserves tag  *)
  (* and (invariant) type arguments.                                  *)
  apply var_typing_inv in Hrecv.
  destruct Hrecv as [S [Hlk Hsub]].
  cbn in Hlk. injection Hlk as HeqS. subst S.
  assert (HE : E <> any_tag).
  { intros ->. vm_compute in Heff. discriminate. }
  destruct (sub_ctor_inv_noty _ _ _ _ _ (state_ctx_tm_no_ty _) Hsub HE)
    as [l' [Heq _]].
  unfold leak_state_cap_ty, T_State in Heq.
  injection Heq as HeqE Heql HeqTs. subst E l' Ts.
  vm_compute in Heff. injection Heff as Hnα Hops.
  subst n_α ops.
  vm_compute in Hnth. injection Hnth as Hnβ Hsig Hret.
  subst n_β sig ret. subst sig_inst.
  revert Hnlsi.
  apply nolocb_false_rejects.
  - apply state_ctx_tm_lt_ctx_wf.
  - cbn. solve_wf.
  - vm_compute; reflexivity.
Qed.

(* Positive companion: the identical perform shape at an escapable    *)
(* state type is accepted — [typed_state_example]                     *)
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
(* (TypingInv.v's [lam_typing_inv] drops it).                         *)
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
  λ: T_Unit \\ term_perform ($$ 1) 0 [] T_Unit ($$ 0).

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
            capture_lt capture_ctx (term_perform ($$ 1) 0 [] T_Unit ($$ 0))
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
  term_handle Reader_tag [T_Unit] leak2_ty leak2_ty
    [(0, ($$ 1) @· ($$ 0))]
    (some_v (T_Option `Lf (T_Reader `Ll T_Unit))
            (some_v (T_Reader `Ll T_Unit) ($$ 0))).

Theorem leak_reader2_rejected : forall T,
  ~ (full_ctx ⊢ₜ leak_reader2 : T).
Proof.
  intros T H.
  apply handle_typing_inv in H.
  destruct H as (n_α & ops & _ & _ & _ & _ & _ & Hnl & _).
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
    | apply Forall2_nil | apply Forall_nil | apply TS_Nil
    | apply Forall2_cons | apply Forall_cons | apply TS_Cons
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

(* ================================================================== *)
(* 7. crashEndo / crashBox as complete match terms                    *)
(*                                                                    *)
(* The match that binds a Trash/Box existential lifetime and returns  *)
(* the field is REJECTED at every data-constructor interface: T_Match *)
(* demands `elim_ty_n ... eta = Some _` for the yes-branch type eta,  *)
(* and the bound existential occurs in an INVARIANT position (a       *)
(* constructor argument) of the field type, where elimination fails.  *)
(*                                                                    *)
(* The rejection is deliberately NOT `forall T`: subsumption into     *)
(* `Any` is available (eta := Any@local always passes elimination),   *)
(* so the match may still type at Any-supertypes — the local-Any      *)
(* escape hatch, through which data remains confined.  Rejection at   *)
(* every proper constructor interface is the exact boundary of what   *)
(* is derivable.                                                      *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Supertype characterizations (left inversion).  Unlike the right    *)
(* inversions these need NO context hypothesis: the variable rule     *)
(* has a type variable on the LEFT, which a constructor shape kills.  *)
(* ------------------------------------------------------------------ *)

(* Supertypes of Any@Δ are Any@Δ'.                                    *)
Lemma sub_any_sup : forall Γ S U,
  Γ ⊢ S <:: U ->
  forall Δ, S = type_ctor any_tag Δ [] ->
  exists Δ', U = type_ctor any_tag Δ' [].
Proof.
  intros Γ S U H; induction H; intros Δ0 Heq.
  - (* Refl *) subst. eauto.
  - (* Trans *)
    destruct (IHsub1 _ Heq) as [Δ1 HeqU].
    destruct (IHsub2 _ HeqU) as [Δ2 HeqT]. eauto.
  - (* VarCtx *) discriminate.
  - (* Data *) injection Heq as -> -> ->. eauto.
  - (* Any *) eauto.
  - (* Fun *) discriminate.
  - (* LtAll *) discriminate.
  - (* TyAll *) discriminate.
Qed.

(* Supertypes of a non-Any constructor type: the same constructor     *)
(* with the same (invariant) arguments at a larger lifetime, or an    *)
(* Any type.                                                          *)
Lemma sub_ctor_sup : forall Γ S U,
  Γ ⊢ S <:: U ->
  forall K l Ts, S = type_ctor K l Ts -> K <> any_tag ->
  (exists l', U = type_ctor K l' Ts /\ Γ ⊢ₗ l <: l') \/
  (exists Δ, U = type_ctor any_tag Δ []).
Proof.
  intros Γ S U H; induction H; intros K0 l0 Ts0 Heq HK.
  - (* Refl *) subst. left. exists l0. split; [reflexivity|].
    apply LS_Refl. inversion H; assumption.
  - (* Trans *)
    destruct (IHsub1 _ _ _ Heq HK) as [[l1 [HeqU Hl1]] | [Δ1 HeqU]].
    + destruct (IHsub2 _ _ _ HeqU HK) as [[l2 [HeqT Hl2]] | [Δ2 HeqT]].
      * left. exists l2. split; [exact HeqT | eapply LS_Trans; eauto].
      * right. eauto.
    + subst U.
      destruct (sub_any_sup _ _ _ H0 _ eq_refl) as [Δ2 HeqT].
      right. eauto.
  - (* VarCtx *) discriminate.
  - (* Data *) injection Heq as HKe Hle HTse. subst. left.
    exists l'. split; [reflexivity | assumption].
  - (* Any *) right. eauto.
  - (* Fun *) discriminate.
  - (* LtAll *) discriminate.
  - (* TyAll *) discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Elimination facts: the shared field shape [K l' [Nat@`L0]] has the *)
(* bound variable in an invariant constructor-argument position, so   *)
(* elimination fails for ANY lifetime l' and ANY bound; on Any@Δ it   *)
(* succeeds and preserves the Any head.                               *)
(* ------------------------------------------------------------------ *)

Lemma elim_ty_nat_arg_None : forall bound l' K,
  elim_ty 0 bound var_pos (type_ctor K l' [T_Nat (`L 0)]) = None.
Proof.
  intros bound l' K. cbn.
  destruct (elim_lt 0 bound var_pos l'); reflexivity.
Qed.

Lemma elim_ty_n_nat_arg_None : forall bound l' K,
  elim_ty_n 1 bound var_pos (type_ctor K l' [T_Nat (`L 0)]) = None.
Proof.
  intros bound l' K. cbn [elim_ty_n].
  rewrite elim_ty_nat_arg_None. reflexivity.
Qed.

Lemma elim_ty_n_any_shape : forall bound Δa r,
  elim_ty_n 1 bound var_pos (type_ctor any_tag Δa []) = Some r ->
  exists Δr, r = type_ctor any_tag Δr [].
Proof.
  intros bound Δa r H. simpl in H.
  destruct (elim_lt 0 bound var_pos Δa) as [Δ1|]; simpl in H;
    [| discriminate].
  injection H as <-. eexists. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The complete offending terms, with well-typed scrutinees           *)
(* ------------------------------------------------------------------ *)

(* Endo<Nat'local> value: the identity on local naturals.             *)
Definition endo_id_local_v : term :=
  term_ctor endo_tag `Lf [] [T_Nat `Ll] [λ: T_Nat `Ll \\ $$ 0].

(* Endo<Nat'free> value: the fallback branch of crashEndo_match.  It  *)
(* is typable at the advertised free Endo interface (proved below),   *)
(* so the match is rejected solely for the escape the YES branch      *)
(* attempts — not for an independently ill-typed fallback.            *)
Definition endo_id_free_v : term :=
  term_ctor endo_tag `Lf [] [T_Nat `Lf] [λ: T_Nat `Lf \\ $$ 0].

(* Trash[local](Endo<Nat'local>) — a legitimate local datum.          *)
Definition trash_val : term :=
  term_ctor trash_tag `Ll [`Ll] [] [endo_id_local_v].

(* match trash_val as Trash[l](e) => e — tries to move the field out. *)
Definition crashEndo_match : term :=
  term_match trash_val trash_tag 1 1 ($$ 0) endo_id_free_v.

Theorem crashEndo_match_rejected_at_data : forall K l Ts,
  K <> any_tag ->
  ~ (data_ctx ⊢ₜ crashEndo_match : type_ctor K l Ts).
Proof.
  intros K l Ts HK H.
  apply match_typing_inv in H.
  destruct H as
    (n_lt & n_ty & sigma & schema & Ts0 & Delta & sres & rtag & rl & eta & er &
     _ & Hlk & _ & _ & HTs0 & _ & _ & _ & _ & _ & _ & _ & Hbody & Helim & _ &
     HsubOr).
  vm_compute in Hlk. injection Hlk as H1 H2 H3 H4. subst n_lt n_ty sigma schema.
  destruct Ts0 as [|? ?]; [|discriminate HTs0].
  cbn in Hbody.
  apply var_typing_inv in Hbody.
  destruct Hbody as [S [Hlk0 Hsub]].
  cbn in Hlk0. injection Hlk0 as HS. subst S.
  assert (Hne : endo_tag <> any_tag) by (intro Hx; discriminate Hx).
  destruct (sub_ctor_sup _ _ _ Hsub _ _ _ eq_refl Hne)
    as [[l1 [Heta _]] | [Δa Heta]]; subst eta.
  - (* eta is the Endo constructor: elimination fails *)
    rewrite elim_ty_n_nat_arg_None in Helim. discriminate.
  - (* eta is Any@Δa: the eliminated result keeps the Any head, which *)
    (* can never reach a non-Any constructor interface.               *)
    destruct (elim_ty_n_any_shape _ _ _ Helim) as [Δr Her]. subst er.
    destruct HsubOr as [HeqT | HsubT].
    + injection HeqT as HKa _ _. congruence.
    + destruct (sub_ctor_inv_noty _ _ _ _ _ data_ctx_no_ty HsubT HK)
        as [l'' [Heq'' _]].
      injection Heq'' as HKa _ _. congruence.
Qed.

(* The reviewer-facing instance: the field cannot come out at the     *)
(* free Endo interface (nor, per the theorem above, at ANY            *)
(* constructor interface, free or local — the variance failure is     *)
(* about the existential, not the lattice).                           *)
Corollary crashEndo_match_rejected_at_free :
  ~ (data_ctx ⊢ₜ crashEndo_match : T_Endo `Lf (T_Nat `Lf)).
Proof.
  apply crashEndo_match_rejected_at_data.
  intro Hx; discriminate Hx.
Qed.

(* Box[local](Option<Nat'local>) and its match.                       *)
Definition box_val : term :=
  term_ctor box_tag `Ll [`Ll] [] [some_v (T_Nat `Ll) zero_v].

Definition crashBox_match : term :=
  term_match box_val box_tag 1 1 ($$ 0) (none_v (T_Nat `Lf)).

Theorem crashBox_match_rejected_at_data : forall K l Ts,
  K <> any_tag ->
  ~ (data_ctx ⊢ₜ crashBox_match : type_ctor K l Ts).
Proof.
  intros K l Ts HK H.
  apply match_typing_inv in H.
  destruct H as
    (n_lt & n_ty & sigma & schema & Ts0 & Delta & sres & rtag & rl & eta & er &
     _ & Hlk & _ & _ & HTs0 & _ & _ & _ & _ & _ & _ & _ & Hbody & Helim & _ &
     HsubOr).
  vm_compute in Hlk. injection Hlk as H1 H2 H3 H4. subst n_lt n_ty sigma schema.
  destruct Ts0 as [|? ?]; [|discriminate HTs0].
  cbn in Hbody.
  apply var_typing_inv in Hbody.
  destruct Hbody as [S [Hlk0 Hsub]].
  cbn in Hlk0. injection Hlk0 as HS. subst S.
  assert (Hne : option_tag <> any_tag) by (intro Hx; discriminate Hx).
  destruct (sub_ctor_sup _ _ _ Hsub _ _ _ eq_refl Hne)
    as [[l1 [Heta _]] | [Δa Heta]]; subst eta.
  - rewrite elim_ty_n_nat_arg_None in Helim. discriminate.
  - destruct (elim_ty_n_any_shape _ _ _ Helim) as [Δr Her]. subst er.
    destruct HsubOr as [HeqT | HsubT].
    + injection HeqT as HKa _ _. congruence.
    + destruct (sub_ctor_inv_noty _ _ _ _ _ data_ctx_no_ty HsubT HK)
        as [l'' [Heq'' _]].
      injection Heq'' as HKa _ _. congruence.
Qed.

Corollary crashBox_match_rejected_at_free :
  ~ (data_ctx ⊢ₜ crashBox_match : T_Option `Lf (T_Nat `Lf)).
Proof.
  apply crashBox_match_rejected_at_data.
  intro Hx; discriminate Hx.
Qed.

(* ------------------------------------------------------------------ *)
(* The scrutinees are genuine well-typed local values — the matches   *)
(* above are rejected for the escape they attempt, not because their  *)
(* scrutinees were ill-formed.                                        *)
(* ------------------------------------------------------------------ *)

Lemma typed_endo_id_local :
  data_ctx ⊢ₜ endo_id_local_v : T_Endo `Ll (T_Nat `Ll).
Proof.
  unfold endo_id_local_v.
  eapply T_Sub.
  - eapply T_Ctor with
      (lts := []) (Ts := [T_Nat `Ll])
      (rho_fields := [T_Nat `Ll -{ `Lf }-> T_Nat `Ll])
      (result_tag := endo_tag) (l := `Lf);
      cbn; try reflexivity;
      try solve [ repeat constructor | solve_wf | solve_lt ].
  - apply SA_Data; [ solve_lt | solve_wf ].
Qed.

Theorem typed_trash_val : data_ctx ⊢ₜ trash_val : T_Trash `Ll.
Proof.
  unfold trash_val.
  eapply T_Ctor with
    (lts := [`Ll]) (Ts := [])
    (rho_fields := [T_Endo `Ll (T_Nat `Ll)])
    (result_tag := trash_tag) (l := `Ll);
    cbn; try reflexivity;
    try solve [ repeat constructor | solve_wf | solve_lt
              | repeat (constructor; try (apply LS_Refl; solve_wf)) ].
  apply TS_Cons; [ exact typed_endo_id_local | apply TS_Nil ].
Qed.

Lemma typed_some_nat_local :
  data_ctx ⊢ₜ some_v (T_Nat `Ll) zero_v : T_Option `Ll (T_Nat `Ll).
Proof.
  assert (Hz : data_ctx ⊢ₜ zero_v : T_Nat `Lf)
    by (unfold zero_v; solve_nullary_ctor).
  unfold some_v.
  eapply T_Sub.
  - eapply T_Ctor with
      (lts := []) (Ts := [T_Nat `Ll])
      (rho_fields := [T_Nat `Ll])
      (result_tag := option_tag) (l := `Lf);
      cbn; try reflexivity;
      try solve [ repeat constructor | solve_wf | solve_lt ].
    apply TS_Cons; [| apply TS_Nil].
    eapply T_Sub; [ exact Hz | apply SA_Data; [ solve_lt | solve_wf ] ].
  - apply SA_Data; [ solve_lt | solve_wf ].
Qed.

Theorem typed_box_val : data_ctx ⊢ₜ box_val : T_Box `Ll.
Proof.
  unfold box_val.
  eapply T_Ctor with
    (lts := [`Ll]) (Ts := [])
    (rho_fields := [T_Option `Ll (T_Nat `Ll)])
    (result_tag := box_tag) (l := `Ll);
    cbn; try reflexivity;
    try solve [ repeat constructor | solve_wf | solve_lt
              | repeat (constructor; try (apply LS_Refl; solve_wf)) ].
  apply TS_Cons; [ exact typed_some_nat_local | apply TS_Nil ].
Qed.

(* ------------------------------------------------------------------ *)
(* No independent typing error obscures the rejections: the fallback  *)
(* branches are typable at the advertised free interfaces, and the    *)
(* leak_reader operation clauses are typable at exactly the T_Handle  *)
(* premise instance.                                                  *)
(* ------------------------------------------------------------------ *)

Lemma typed_endo_id_free :
  data_ctx ⊢ₜ endo_id_free_v : T_Endo `Lf (T_Nat `Lf).
Proof.
  unfold endo_id_free_v.
  eapply T_Ctor with
    (lts := []) (Ts := [T_Nat `Lf])
    (rho_fields := [T_Nat `Lf -{ `Lf }-> T_Nat `Lf])
    (result_tag := endo_tag) (l := `Lf);
    cbn; try reflexivity;
    try solve [ repeat constructor | solve_wf | solve_lt ].
Qed.

Lemma typed_none_free :
  data_ctx ⊢ₜ none_v (T_Nat `Lf) : T_Option `Lf (T_Nat `Lf).
Proof.
  unfold none_v.
  eapply T_Ctor with
    (lts := []) (Ts := [T_Nat `Lf]) (rho_fields := [])
    (result_tag := option_tag) (l := `Lf);
    cbn; try reflexivity;
    try solve [ repeat constructor | solve_wf | solve_lt ].
Qed.

(* The Reader operation clause `resume(x)` is well-typed at exactly   *)
(* the instantiated T_Handle premise, so leak_reader's rejection      *)
(* rests SOLELY on the body-type noloc check.                         *)
Lemma leak_reader_op_body_typed :
  (op_body_ctx full_ctx 0
     (inst_op_ty_args 1 [T_Unit] 0 T_Unit)
     (inst_op_ty_args 1 [T_Unit] 0 (`T 0)) leak_ty)
    ⊢ₜ ($$ 1) @· ($$ 0) : shift_ty 0 0 leak_ty.
Proof.
  cbn. eapply T_App; solve_var.
Qed.

Lemma leak_reader2_op_body_typed :
  (op_body_ctx full_ctx 0
     (inst_op_ty_args 1 [T_Unit] 0 T_Unit)
     (inst_op_ty_args 1 [T_Unit] 0 (`T 0)) leak2_ty)
    ⊢ₜ ($$ 1) @· ($$ 0) : shift_ty 0 0 leak2_ty.
Proof.
  cbn. eapply T_App; solve_var.
Qed.

(* ------------------------------------------------------------------ *)
(* The Any@local escape hatch, PROVED: the very matches rejected at   *)
(* every constructor interface are typable at Any@local — the sole    *)
(* remaining interface, through which the data stays local and        *)
(* confined.  Together with the rejections this delimits exactly      *)
(* what is derivable.                                                 *)
(* ------------------------------------------------------------------ *)

Theorem crashEndo_match_typable_at_local_any :
  data_ctx ⊢ₜ crashEndo_match : T_Any `Ll.
Proof.
  unfold crashEndo_match.
  eapply T_Match with
    (Delta := `Ll) (Ts := []) (eta := T_Any `Ll)
    (result_tag := trash_tag) (result_l := `Ll)
    (sigma_fields := [trash_field]) (result_ty_schema := T_Trash (`L 0))
    (rho_fields := List.map (inst_ctor_type_open 1 0 []) [trash_field])
    (lts := lt_var_list 1)
    (Γ' := push_match_bound 1 `Ll data_ctx);
    cbn; try reflexivity;
    try solve [ intro Hx; discriminate Hx
              | repeat constructor
              | solve_wf
              | apply LS_Refl; solve_wf
              | exact typed_trash_val ].
  (* remaining: the yes-branch and fallback typings at Any@local *)
  all: try (eapply T_Sub;
        [ solve_var
        | apply SA_Any;
          [ solve_wf | solve_wf | apply LS_Local; cbn; solve_wf ] ]).
  all: eapply T_Sub;
        [ exact typed_endo_id_free
        | apply SA_Any;
          [ solve_wf | solve_wf | apply LS_Local; cbn; solve_wf ] ].
Qed.

Theorem crashBox_match_typable_at_local_any :
  data_ctx ⊢ₜ crashBox_match : T_Any `Ll.
Proof.
  unfold crashBox_match.
  eapply T_Match with
    (Delta := `Ll) (Ts := []) (eta := T_Any `Ll)
    (result_tag := box_tag) (result_l := `Ll)
    (sigma_fields := [box_field]) (result_ty_schema := T_Box (`L 0))
    (rho_fields := List.map (inst_ctor_type_open 1 0 []) [box_field])
    (lts := lt_var_list 1)
    (Γ' := push_match_bound 1 `Ll data_ctx);
    cbn; try reflexivity;
    try solve [ intro Hx; discriminate Hx
              | repeat constructor
              | solve_wf
              | apply LS_Refl; solve_wf
              | exact typed_box_val ].
  all: try (eapply T_Sub;
        [ solve_var
        | apply SA_Any;
          [ solve_wf | solve_wf | apply LS_Local; cbn; solve_wf ] ]).
  all: eapply T_Sub;
        [ exact typed_none_free
        | apply SA_Any;
          [ solve_wf | solve_wf | apply LS_Local; cbn; solve_wf ] ].
Qed.
