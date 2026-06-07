(* ================================================================== *)
(*  Soundness-backed guarantees about the example programs.            *)
(*                                                                    *)
(*  These examples instantiate the headline meta-theorems of          *)
(*  Safety.v on the concrete programs defined in Examples.v.  They     *)
(*  live in their own file because they depend on the full safety      *)
(*  development; keeping them separate lets Examples.v /               *)
(*  ExamplesProofs.v stay green independently of Safety.v.             *)
(* ================================================================== *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Examples.
Require Import ExamplesProofs.
Require Import Safety.

Import CoreNotation.

(* Bridge the example-level reflexive-transitive closure (`==>>`,      *)
(* Examples.multi_step) to the one used by Safety's meta-theory.       *)
Lemma ms_examples_to_safety : forall t t',
  Examples.multi_step t t' -> Safety.multi_step t t'.
Proof.
  intros t t' H; induction H.
  - apply MS_Refl.
  - eapply MS_Step; eassumption.
Qed.

(* ------------------------------------------------------------------ *)
(* 1. Lattice refutation: `local` never widens to `free`.             *)
(* ------------------------------------------------------------------ *)
(* beautified:    NOT ( local <: free )                               *)
Example ex_local_lt_never_free :
  forall Γ, ~ (Γ ⊢ₗ `Ll <: `Lf).
Proof. exact lt_local_not_escapes. Qed.

(* ------------------------------------------------------------------ *)
(* 2. Subtyping refutation: a local File can never be coerced to a    *)
(*    free File — the "no escape via subsumption" theorem.            *)
(* ------------------------------------------------------------------ *)
(* beautified:    eval_ctx Γ  =>  NOT ( File@local <: File@free )     *)
Example ex_local_file_never_escapes_sub :
  forall Γ, eval_ctx Γ ->
    ~ (Γ ⊢ T_FileT `Ll <:: T_FileT `Lf).
Proof.
  intros Γ Hec.
  apply local_data_not_escapes; [exact Hec | discriminate].
Qed.

(* ------------------------------------------------------------------ *)
(* 3. Capability confinement: a bare runtime capability is NOT        *)
(*    typeable in any evaluation context — it can never leave the     *)
(*    dynamic extent of its handler.                                  *)
(* ------------------------------------------------------------------ *)
(* beautified:    eval_ctx Γ  =>  ( Γ ⊢ cap_E[m]<Ts>{op} : T )  absurd *)
Example ex_capability_confined :
  forall Γ E_tag m Ts op_body T,
    eval_ctx Γ ->
    Γ ⊢ₜ term_cap E_tag m Ts op_body : T ->
    False.
Proof.
  intros Γ E_tag m Ts op_body T Hec Hty.
  exact (capability_confined Γ EC_hole E_tag m Ts op_body T Hec Hty).
Qed.

(* ------------------------------------------------------------------ *)
(* 4. Operational non-escape (headline corollary of preservation +    *)
(*    the lattice): whatever a closed program returns at a *free*     *)
(*    File type is a constructor whose own annotation carries no       *)
(*    top-level `local`.  A `local`-confined datum is never the value  *)
(*    handed back at a `free` (escapable) type.                       *)
(* ------------------------------------------------------------------ *)
Example ex_free_result_is_local_free :
  forall t v,
    data_ctx ⊢ₜ t : T_FileT `Lf ->
    Examples.multi_step t v ->
    value v ->
    exists K' l' lts' vs,
      v = term_ctor K' l' lts' [] vs /\ no_local_lt l' = true.
Proof.
  intros t v Hty Hms Hval.
  eapply (local_value_does_not_escape data_ctx t file_tag [] v).
  - unfold data_ctx; repeat apply ec_ctor; apply ec_nil.
  - discriminate.
  - exact Hty.
  - apply ms_examples_to_safety; exact Hms.
  - exact Hval.
Qed.

(* ------------------------------------------------------------------ *)
(* 5. End-to-end type safety on a closed program.                     *)
(*    beautified:    (λ (x : Unit). x) unit   ==>>   unit             *)
(* ------------------------------------------------------------------ *)
Example ex_idunit_typed :
  data_ctx ⊢ₜ (λ: T_UnitT \\ $$ 0) @· unit_v : T_UnitT.
Proof.
  eapply T_App with (A := T_UnitT) (l := `Lf) (B := T_UnitT).
  - apply T_Lam.
    + apply T_Var. reflexivity.
    + cbn. apply LS_Free.
    + reflexivity.
  - eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
    + apply LS_Refl.
    + constructor.
Qed.

(* The reduct never gets stuck — neither a value nor any reachable    *)
(* state is a "stuck" configuration (progress holds along the run).   *)
Example ex_idunit_type_safe :
  forall t', Examples.multi_step ((λ: T_UnitT \\ $$ 0) @· unit_v) t' ->
    ~ Safety.stuck t'.
Proof.
  intros t' Hms.
  eapply (type_safety data_ctx _ t' T_UnitT).
  - unfold data_ctx; repeat apply ec_ctor; apply ec_nil.
  - exact ex_idunit_typed.
  - apply ms_examples_to_safety; exact Hms.
Qed.
