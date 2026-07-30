Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Decide.
Require Import Examples.

Import CoreNotation.

(* ================================================================== *)
(* The examples-tier tactic library.                                  *)
(*                                                                    *)
(* Multi-step plumbing, evaluation-context congruence for ==>>,       *)
(* closed-value lemmas, and the solve_* tactics that discharge the    *)
(* recurring typing-derivation shapes (well-formedness, variables,    *)
(* lifetime subtyping, constructors, numerals, State-effect goals).   *)
(* Shared by ExamplesProofs.v, ExamplesRejection.v and                *)
(* ExamplesSafety.v — none of the example proofs live here.           *)
(* ================================================================== *)

(* ================================================================== *)
(* Multi-step plumbing                                                *)
(* ================================================================== *)

Lemma ms_one : forall t t', t ==> t' -> t ==>> t'.
Proof. intros t t' H. eapply MS_Step; [exact H | apply MS_Refl]. Qed.

Lemma ms_trans : forall t1 t2 t3, t1 ==>> t2 -> t2 ==>> t3 -> t1 ==>> t3.
Proof.
  intros t1 t2 t3 H12. revert t3.
  induction H12 as [|? ? ? Hs ? IH]; intros u H23; auto.
  eapply MS_Step; eauto.
Qed.

(* ================================================================== *)
(* Evaluation-context congruence for multi-step reduction.            *)
(*                                                                    *)
(* Reduction lifts through an application/ty-/lt-application frame.   *)
(* For [ty_app]/[lt_app] the frame carries no marker, so the lift is  *)
(* unconditional.  For [app] the sibling operand's markers join the   *)
(* term, so a [S_HandleCtx] (handler allocation) step would need a    *)
(* marker fresh in the sibling too — we require the sibling to be     *)
(* marker-free, which holds for every closed value/argument here.     *)
(* ================================================================== *)

Lemma step_ty_app : forall t t' S, t ==> t' -> term_ty_app t S ==> term_ty_app t' S.
Proof.
  intros t t' S H. inversion H; subst.
  - apply (S_step (EC_ty_app E S)); [ apply EWF_TyApp; assumption | assumption ].
  - apply (S_HandleCtx (EC_ty_app E S)); [ apply EWF_TyApp; assumption | cbn; assumption ].
Qed.

Lemma step_lt_app : forall t t' l, t ==> t' -> term_lt_app t l ==> term_lt_app t' l.
Proof.
  intros t t' l H. inversion H; subst.
  - apply (S_step (EC_lt_app E l)); [ apply EWF_LtApp; assumption | assumption ].
  - apply (S_HandleCtx (EC_lt_app E l)); [ apply EWF_LtApp; assumption | cbn; assumption ].
Qed.

Lemma step_app1 : forall t t' u, markers_in u = [] -> t ==> t' -> term_app t u ==> term_app t' u.
Proof.
  intros t t' u Hu H. inversion H; subst.
  - apply (S_step (EC_app1 E u)); [ apply EWF_App1; assumption | assumption ].
  - apply (S_HandleCtx (EC_app1 E u)); [ apply EWF_App1; assumption | ].
    cbn. rewrite Hu. rewrite app_nil_r. assumption.
Qed.

Lemma step_app2 : forall v t t', value v -> markers_in v = [] -> t ==> t' ->
  term_app v t ==> term_app v t'.
Proof.
  intros v t t' Hv Hm H. inversion H; subst.
  - apply (S_step (EC_app2 v E)); [ apply EWF_App2; assumption | assumption ].
  - apply (S_HandleCtx (EC_app2 v E)); [ apply EWF_App2; assumption | ].
    cbn. rewrite Hm. cbn. assumption.
Qed.

Lemma ms_ty_app : forall t t' S, t ==>> t' -> term_ty_app t S ==>> term_ty_app t' S.
Proof.
  intros t t' S H. induction H; [ apply MS_Refl |].
  eapply MS_Step; [ apply step_ty_app; eassumption | assumption ].
Qed.

Lemma ms_lt_app : forall t t' l, t ==>> t' -> term_lt_app t l ==>> term_lt_app t' l.
Proof.
  intros t t' l H. induction H; [ apply MS_Refl |].
  eapply MS_Step; [ apply step_lt_app; eassumption | assumption ].
Qed.

Lemma ms_app1 : forall t t' u, markers_in u = [] -> t ==>> t' -> term_app t u ==>> term_app t' u.
Proof.
  intros t t' u Hu H. induction H; [ apply MS_Refl |].
  eapply MS_Step; [ apply step_app1; eassumption | assumption ].
Qed.

Lemma ms_app2 : forall v t t', value v -> markers_in v = [] -> t ==>> t' ->
  term_app v t ==>> term_app v t'.
Proof.
  intros v t t' Hv Hm H. induction H; [ apply MS_Refl |].
  eapply MS_Step; [ apply step_app2; eassumption | assumption ].
Qed.

(* [solve_value] proves [value v] for a CONCRETE closed term by
   reflection: [valueb_value] (Decide.v) plus [vm_compute].  Faster and
   more robust than [repeat constructor] on deeply nested constructor
   values, and independent of the term's shape. *)
Ltac solve_value := apply valueb_value; vm_compute; reflexivity.

Lemma unit_v_value : value unit_v.
Proof. solve_value. Qed.

Lemma file_v_value : value file_v.
Proof. solve_value. Qed.

Lemma two_v_value : value two_v.
Proof. solve_value. Qed.

Lemma three_v_value : value three_v.
Proof. solve_value. Qed.

Lemma some_three_value : value (some_v (T_Nat `Lf) three_v).
Proof. solve_value. Qed.

Hint Resolve unit_v_value file_v_value two_v_value three_v_value some_three_value : core.

(* [solve_wf] discharges well-formedness side conditions ([ty_wf],
   [types_wf], [lt_wf], [lifetimes_wf]) and the context-lookup equations
   they spawn.  For a [type_var] it picks TWF_Var, resolves the lookup by
   computation, and recurses into the bound's well-formedness (the [cbn]
   on the second branch forces a stuck [shift_ty .. any_at_free] back to a
   concrete [type_ctor] so the generic [constructor] arm can fire). *)
Ltac solve_wf :=
  repeat match goal with
  | |- ty_wf _ (type_var _) => econstructor; [cbn; reflexivity | cbn]
  | |- lt_wf _ (lt_var _) => econstructor; [cbn; reflexivity]
  | |- ty_wf _ _ => constructor
  | |- types_wf _ _ => constructor
  | |- lifetimes_wf _ _ => constructor
  | |- lt_wf _ _ => constructor
  | |- ctx_lookup_ty _ _ = Some _ => cbn; reflexivity
  | |- ctx_lookup_lt _ _ = Some _ => cbn; reflexivity
  end.

(* [solve_var] types a de Bruijn variable: it applies T_Var, resolves the
   term-context lookup by computation, and proves the bound is well-formed.
   [cbn] is required before [reflexivity] because [full_ctx] is built with
   list append ([++]). *)
Ltac solve_var :=
  apply T_Var; [cbn; reflexivity | solve_wf].

Ltac solve_free_sub :=
  apply LS_Free; solve_wf.

Ltac solve_lt_sub :=
  match goal with
  | |- _ ⊢ₗ lt_join _ _ <: _ => apply LS_JoinL; solve_lt_sub
  | |- _ ⊢ₗ lt_free <: _ => apply LS_Free; solve_wf
  | |- _ ⊢ₗ ?l <: ?l => apply LS_Refl; solve_wf
  | |- _ ⊢ₗ _ <: lt_local => apply LS_Local; solve_wf
  end.

(* [solve_lt] proves a lifetime-subtyping goal whose endpoints are built
   from [lt_free], [lt_local], [lt_var] and [lt_join] (joins).  It tries the
   reflexive/bottom/join introduction rules and recurses through [lt_join]
   on either side. *)
Ltac solve_lt :=
  solve [ apply LS_Refl; solve_wf
        | apply LS_Free; solve_wf
        | apply LS_JoinR1; [solve_lt | solve_wf]
        | apply LS_JoinR2; [solve_lt | solve_wf]
        | apply LS_JoinL; [solve_lt | solve_lt] ].

Ltac solve_nullary_ctor :=
  eapply T_Ctor with (lts := []) (Ts := []) (rho_fields := []);
  cbn; try reflexivity;
  try solve [ repeat constructor
            | apply LS_Free; repeat constructor
            | apply LS_Refl; repeat constructor ].

(* [solve_ctor] discharges a general constructor-application typing goal
   ([T_Ctor]).  [eapply] leaves the field/lifetime/type arguments as
   evars; the equational premises are closed by [reflexivity] (which
   instantiates those evars), and the loop then proves the remaining
   well-formedness, lifetime-subtyping and [Forall]/[Forall2] obligations.
   The [progress cbn] alternative re-normalises field types of the form
   [inst_ctor_type ..] that only become reducible once the argument evars
   have been resolved. *)
Ltac solve_ctor :=
  eapply T_Ctor; cbn; try reflexivity;
  repeat first
    [ solve_var | solve_lt | progress solve_wf | progress cbn
    | apply Forall2_nil | apply Forall_nil
    | apply Forall2_cons | apply Forall_cons ].

(* [solve_nat] types a Peano numeral [Suc (Suc ... Zero)] at [T_Nat `Lf] in
   any context whose constructor table is computable by [cbn].  It is
   [solve_ctor] with the constructor rule itself added as a fallback, so the
   nested [Suc]-fields (themselves constructor applications) are typed
   recursively rather than left for [solve_var]. *)
Ltac solve_nat :=
  unfold two_v, three_v, suc_v, zero_v;
  repeat first
    [ solve_var | solve_lt | progress solve_wf | progress cbn
    | apply Forall2_nil | apply Forall_nil
    | apply Forall2_cons | apply Forall_cons
    | eapply T_Ctor; cbn; try reflexivity ].

Lemma four_v_value : value four_v.
Proof. solve_value. Qed.

Lemma endoi_v_value : value endoi_v.
Proof. solve_value. Qed.

#[export] Hint Resolve four_v_value endoi_v_value : core.

(* [solve_cmd] types a State command [get]/[put n] : Cmd<Nat> (the [put] field
   is a Nat numeral, typed by [solve_nat]). *)
Ltac solve_cmd :=
  eapply T_Ctor; cbn; try reflexivity;
  repeat first
    [ progress solve_wf | solve_lt
    | apply Forall_nil | apply Forall2_nil
    | apply Forall2_cons; [ solve_nat | ] ].

(* [solve_state_perform] discharges a [perform st.<cmd>() : Nat] goal (the 11
   premises of T_Perform for the single State operation [Cmd<Nat> -> Nat]). *)
Ltac solve_state_perform :=
  eapply T_Perform with (Ss := (@nil type));
  [ solve_var | cbn; reflexivity | cbn; reflexivity | reflexivity | reflexivity
  | solve_wf | constructor | cbn; reflexivity | cbn; solve_lt_sub | cbn; reflexivity
  | solve_wf | solve_cmd ].

Ltac solve_state_k_app :=
  eapply T_App with (A := `T 1) (l := `Ll) (B := `T 0);
  [ eapply T_App with (A := `T 1) (l := `Ll) (B := `T 1 -{ `Ll }-> `T 0);
    [ solve_var | solve_var ]
  | solve_var ].


(* [solve_lt_var] extends [solve_lt] with one more move: descend through
   a lifetime variable's declared bound (LS_Trans + LS_Var).  Needed for
   match-fresh lifetime variables, whose bound is the (shifted) scrutinee
   lifetime. *)
Ltac solve_lt_var :=
  solve [ apply LS_Refl; solve_wf
        | apply LS_Free; solve_wf
        | eapply LS_Trans;
          [ eapply LS_Var; [ cbn; reflexivity | solve_wf ] | solve_lt_var ]
        | apply LS_JoinR1; [ solve_lt_var | solve_wf ]
        | apply LS_JoinR2; [ solve_lt_var | solve_wf ]
        | apply LS_JoinL; [ solve_lt_var | solve_lt_var ] ].

