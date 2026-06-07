Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Examples.

Import CoreNotation.

(* ================================================================== *)
(* CoreΔ — example PROOFS                                              *)
(*                                                                    *)
(* All proofs about the definitions in `Examples.v` live here.        *)
(* Sections mirror the structure of `Examples.v`.                     *)
(* ================================================================== *)

(* ================================================================== *)
(* 0. Multi-step plumbing                                             *)
(* ================================================================== *)

Lemma ms_one : forall t t', t ==> t' -> t ==>> t'.
Proof. intros t t' H. eapply ms_step; [exact H | apply ms_refl]. Qed.

Lemma ms_trans : forall t1 t2 t3, t1 ==>> t2 -> t2 ==>> t3 -> t1 ==>> t3.
Proof.
  intros t1 t2 t3 H12. revert t3.
  induction H12 as [|? ? ? Hs ? IH]; intros u H23; auto.
  eapply ms_step; eauto.
Qed.

(* Value lemmas + hints (used throughout the reduction proofs).        *)
Lemma unit_v_value : value unit_v.
Proof. apply value_ctor. constructor. Qed.
Hint Resolve unit_v_value : core.

Lemma zero_v_value : value zero_v.
Proof. apply value_ctor. constructor. Qed.
Lemma one_v_value  : value one_v.
Proof. apply value_ctor. repeat constructor. Qed.
Hint Resolve zero_v_value one_v_value : core.

Lemma get_v_value : value get_v.
Proof. apply value_ctor. constructor. Qed.
Lemma put_v_one_value : value (put_v one_v).
Proof. apply value_ctor. repeat constructor. Qed.
Hint Resolve get_v_value put_v_one_value : core.

(* ================================================================== *)
(* 1. Existing examples — basic typing                                *)
(* ================================================================== *)

(* Example 1: Identity λ(x:A). x  :  A -free-> A                      *)
Example ex_identity :
  forall A : type,
    no_local_ty A = true ->
    [] ⊢ₜ (λ: A \\ $$ 0) : (A -{ `Lf }-> A).
Proof.
  intros A HA.
  apply T_Lam.
  - apply T_Var. reflexivity.
  - cbn. apply LS_Free.
  - exact HA.
Qed.

(* Example 2: Free closure ≤ local closure (subsumption)              *)
Example ex_upcast_closure_lt :
  forall A : type,
    no_local_ty A = true ->
    [] ⊢ₜ (λ: A \\ $$ 0) : (A -{ `Ll }-> A).
Proof.
  intros A HA.
  eapply T_Sub.
  - apply T_Lam.
    + apply T_Var. reflexivity.
    + cbn. apply LS_Free.
    + exact HA.
  - apply SA_Fun; [apply SA_Refl | apply LS_Free | apply SA_Refl].
Qed.

(* Example 3: Higher-order application                                *)
Example ex_app :
  forall (A B : type) (l : lifetime),
    [bind_tm A; bind_tm (A -{ l }-> B)] ⊢ₜ ($$ 1 @· $$ 0) : B.
Proof.
  intros A B ll. eapply T_App; apply T_Var; reflexivity.
Qed.

(* Example 4: Lifetime polymorphism (Λl. λ(x:A). x)                  *)
Example ex_lt_poly :
  forall A : type,
    no_local_ty (shift_lt_in_ty 1 0 A) = true ->
    [] ⊢ₜ (Λl \\ λ: shift_lt_in_ty 1 0 A \\ $$ 0)
        : ∀'l. (shift_lt_in_ty 1 0 A -{ `L 0 }-> shift_lt_in_ty 1 0 A).
Proof.
  intros A HA.
  apply T_LtLam.
  eapply T_Sub.
  - apply T_Lam.
    + apply T_Var. reflexivity.
    + cbn. apply LS_Free.
    + exact HA.
  - apply SA_Fun; [apply SA_Refl | apply LS_Free | apply SA_Refl].
Qed.

(* Example 5: Type polymorphism — identity                             *)
Example ex_ty_poly_id :
  [] ⊢ₜ (Λt: any_local \\ λ: `T 0 \\ $$ 0)
      : ∀' <: any_local , (`T 0 -{ `Lf }-> `T 0).
Proof.
  apply T_TyLam. apply T_Lam.
  - apply T_Var. reflexivity.
  - cbn. apply LS_Free.
  - reflexivity.
Qed.

(* Example 6: Constructor — Pair with two free fields                 *)
Example ex_ctor_pair_free :
  let Γ := [ bind_ctor 1 0 0 [ty_A; ty_B] (type_ctor 1 pair_lt_free [])
            ; bind_tm ty_B
            ; bind_tm ty_A ] in
  Γ ⊢ₜ term_ctor 1 pair_lt_free [] [] [$$ 1; $$ 0]
    : type_ctor 1 pair_lt_free [].
Proof.
  eapply T_Ctor with
    (n_lt := 0) (n_ty := 0) (lts := [])
    (sigma_fields := [ty_A; ty_B])
    (rho_fields := [ty_A; ty_B])
    (result_ty := type_ctor 1 pair_lt_free [])
    (result_tag := 1).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold pair_lt_free. reflexivity.
  - reflexivity.
  - apply LS_Refl.
  - reflexivity.
  - repeat constructor; apply T_Var; reflexivity.
Qed.

(* Example 7: Constructor — tracked field gives local result          *)
Example ex_ctor_pair_local :
  let Γ := [ bind_ctor 1 0 0 [ty_A_local; ty_B] (type_ctor 1 pair_lt_local [])
            ; bind_tm ty_B
            ; bind_tm ty_A_local ] in
  Γ ⊢ₜ term_ctor 1 pair_lt_local [] [] [$$ 1; $$ 0]
    : type_ctor 1 pair_lt_local [].
Proof.
  eapply T_Ctor with
    (n_lt := 0) (n_ty := 0) (lts := [])
    (sigma_fields := [ty_A_local; ty_B])
    (rho_fields := [ty_A_local; ty_B])
    (result_ty := type_ctor 1 pair_lt_local [])
    (result_tag := 1).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold pair_lt_local. reflexivity.
  - reflexivity.
  - apply LS_Refl.
  - reflexivity.
  - repeat constructor; apply T_Var; reflexivity.
Qed.

(* Example 8: Match — extract a free field from a free Pair           *)
Example ex_match_pair :
  let Γ := [ bind_ctor 1 0 0 [ty_A; ty_B] (type_ctor 1 pair_lt_free [])
            ; bind_tm ty_A
            ; bind_tm (type_ctor 1 pair_lt_free []) ] in
  Γ ⊢ₜ term_match ($$ 1) 1 2 ($$ 0) ($$ 0) : ty_A.
Proof.
  eapply T_Match with
    (n_lt := 0) (n_ty := 0) (lts := []) (Ts := [])
    (sigma_fields := [ty_A; ty_B])
    (rho_fields := [ty_A; ty_B])
    (Delta := pair_lt_free) (arity := 2)
    (scrut_result_ty := type_ctor 1 pair_lt_free [])
    (result_tag := 1) (result_l := pair_lt_free)
    (Γ' := [ bind_ctor 1 0 0 [ty_A; ty_B] (type_ctor 1 pair_lt_free [])
           ; bind_tm ty_A
           ; bind_tm (type_ctor 1 pair_lt_free []) ])
    (eta := ty_A) (elim_result := ty_A).
  - discriminate.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - discriminate.
  - apply LS_Refl.
  - apply T_Var. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply T_Var. reflexivity.
  - reflexivity.
  - apply T_Var. reflexivity.
Qed.

Lemma repo_fields_lt_sub : forall Γ,
  Γ ⊢ₗ lt_of_ty_list [T_FileT (`L 1); T_ConnT (`L 0)] <: (`L 1 ⊓ `L 0).
Proof.
  intros Γ. cbn.
  apply LS_MinL.
  - apply LS_MinL.
    + apply LS_MinR1. apply LS_Refl.
    + apply LS_Free.
  - apply LS_MinL.
    + apply LS_MinL.
      * apply LS_MinR2. apply LS_Refl.
      * apply LS_Free.
    + apply LS_Free.
Qed.

(* Example 9: Repository — existential lifetime constructor           *)
Example ex_repository :
  let AnyAtLocal := type_ctor any_tag `Ll [] in
  [ bind_tm AnyAtLocal
  ; bind_ctor 7 1 0
      [type_ctor any_tag (`L 0) []]
      (type_ctor 7 (`L 0) []) ] ⊢ₜ
    term_ctor 7 `Ll [`Ll] [] [$$ 0]
    : type_ctor 7 `Ll [].
Proof.
  intros AnyAtLocal.
  eapply T_Ctor with (lts := [`Ll]) (Ts := []); try reflexivity.
  - apply LS_Local.
  - repeat constructor.
Qed.

(* Example 10: Distinct constructor tags with shared data result tags. *)
Lemma nat_field_lt_free : forall Γ,
  Γ ⊢ₗ lt_of_ty_list [T_NatT] <: `Lf.
Proof.
  intros Γ. cbn.
  apply LS_MinL.
  - apply LS_MinL; apply LS_Free.
  - apply LS_Free.
Qed.

Example ex_zero_nat :
  nat_ctx ⊢ₜ zero_v : T_NatT.
Proof.
  unfold zero_v.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
  - apply LS_Refl.
  - constructor.
Qed.

Example ex_one_nat :
  nat_ctx ⊢ₜ one_v : T_NatT.
Proof.
  unfold one_v, suc_v.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
  - apply nat_field_lt_free.
  - apply Forall2_cons; [apply ex_zero_nat | apply Forall2_nil].
Qed.

Example ex_get_cmd :
  cmd_ctx ⊢ₜ get_v : T_CmdT.
Proof.
  unfold get_v.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
  - apply LS_Refl.
  - constructor.
Qed.

Example ex_one_nat_in_cmd_nat_ctx :
  (cmd_ctx ++ nat_ctx) ⊢ₜ one_v : T_NatT.
Proof.
  unfold one_v, suc_v, zero_v.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
  - apply nat_field_lt_free.
  - apply Forall2_cons; [| apply Forall2_nil].
    eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
    + apply LS_Refl.
    + constructor.
Qed.

Example ex_put_cmd :
  (cmd_ctx ++ nat_ctx) ⊢ₜ put_v one_v : T_CmdT.
Proof.
  unfold put_v.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
  - apply nat_field_lt_free.
  - apply Forall2_cons; [apply ex_one_nat_in_cmd_nat_ctx | apply Forall2_nil].
Qed.

Example ex_match_zero_nat :
  nat_ctx ⊢ₜ term_match zero_v zero_tag 0 zero_v zero_v : T_NatT.
Proof.
  eapply T_Match with
    (n_lt := 0) (n_ty := 0) (lts := []) (Ts := [])
    (sigma_fields := []) (rho_fields := [])
    (Delta := `Lf) (arity := 0)
    (scrut_result_ty := T_NatT)
    (result_tag := nat_tag) (result_l := `Lf)
    (Γ' := nat_ctx)
    (eta := T_NatT) (elim_result := T_NatT).
  - discriminate.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - discriminate.
  - apply LS_Refl.
  - apply ex_zero_nat.
  - reflexivity.
  - reflexivity.
  - apply ex_zero_nat.
  - reflexivity.
  - apply ex_zero_nat.
Qed.

(* ================================================================== *)
(* 2. Examples mirroring the paper repository                         *)
(* ================================================================== *)

Example ex_paper_unit :
  data_ctx ⊢ₜ term_ctor unit_tag `Lf [] [] [] : T_UnitT.
Proof.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
  - apply LS_Refl.
  - constructor.
Qed.

Example ex_paper_file :
  data_ctx ⊢ₜ term_ctor file_tag `Lf [] [] [] : T_FileT `Lf.
Proof.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
  - apply LS_Refl.
  - constructor.
Qed.

Example ex_paper_connection :
  data_ctx ⊢ₜ term_ctor connection_tag `Lf [] [] [] : T_ConnT `Lf.
Proof.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
  - apply LS_Refl.
  - constructor.
Qed.

Example ex_paper_repo_intro :
  let lts := [`L 0; `L 1] in
  let rho := List.map (inst_ctor_type 2 0 lts [])
              [ T_FileT (`L 1) ; T_ConnT (`L 0) ] in
  let lr  := `L 1 ⊓ `L 0 in
  ( bind_tm (T_ConnT (`L 0))
   :: bind_tm (T_FileT (`L 1))
   :: bind_lt `Ll
   :: bind_lt `Ll
   :: data_ctx ) ⊢ₜ
    term_ctor repo_tag lr lts [] [$$ 1; $$ 0]
    : T_RepoT lr.
Proof.
  intros lts rho lr.
  eapply T_Ctor with (lts := lts) (Ts := []); try reflexivity.
  - apply repo_fields_lt_sub.
  - cbn.
    apply Forall2_cons; [| apply Forall2_cons; [| apply Forall2_nil]];
      apply T_Var; reflexivity.
Qed.

Example ex_paper_makeRepository :
  let inner_lt := `L 1 in
  let result_lt := `L 1 ⊓ `L 0 in
  data_ctx ⊢ₜ makeRepository
    : ∀'l. ∀'l. ((T_FileT (`L 1)) -{ `Lf }->
                  (T_ConnT (`L 0)) -{ inner_lt }-> T_RepoT result_lt).
Proof.
  intros inner_lt result_lt.
  apply T_LtLam. apply T_LtLam.
  apply T_Lam.
  - apply T_Lam.
    + eapply T_Ctor with (lts := [`L 0; `L 1]) (Ts := []);
        try reflexivity.
      * apply repo_fields_lt_sub.
      * apply Forall2_cons; [| apply Forall2_cons; [| apply Forall2_nil]];
          apply T_Var; reflexivity.
    + cbn. apply LS_MinL; [apply LS_MinL; [apply LS_Refl | apply LS_Free] | apply LS_Free].
    + reflexivity.
  - cbn. apply LS_Free.
  - reflexivity.
Qed.

Example ex_paper_print :
  data_ctx ⊢ₜ print_fn
    : ((T_FileT `Ll) -{ `Lf }-> (T_UnitT -{ `Lf }-> T_UnitT)).
Proof.
  apply T_Lam.
  - apply T_Lam.
    + eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
      * apply LS_Refl.
      * constructor.
    + cbn. apply LS_Free.
    + reflexivity.
  - cbn. apply LS_Free.
  - reflexivity.
Qed.

Example ex_paper_compose :
  let lf := `L 1 in let lg := `L 0 in
  let lcap := lf ⊓ (lg ⊓ `Lf) in
  data_ctx ⊢ₜ compose_fn
    : ∀'l. ∀'l. ((CB -{ lf }-> CC) -{ `Lf }->
                  (CA -{ lg }-> CB) -{ lf }->
                  CA -{ lcap }-> CC).
Proof.
  intros lf lg lcap.
  apply T_LtLam. apply T_LtLam.
  apply T_Lam; [| cbn; apply LS_Free | reflexivity].
  apply T_Lam.
  - apply T_Lam.
    + eapply T_App.
      * apply T_Var. reflexivity.
      * eapply T_App; apply T_Var; reflexivity.
    + cbn. apply LS_Refl.
    + reflexivity.
  - cbn. apply LS_MinL; [apply LS_Refl | apply LS_Free].
  - reflexivity.
Qed.

(* ================================================================== *)
(* 3. Reduction examples for plain (effect-free) programs             *)
(* ================================================================== *)

(* 3.1  Identity application:  (λ:T. #0) v   ==>>   v                 *)
Lemma red_identity :
  forall T v, value v ->
    ((λ: T \\ $$ 0) @· v) ==>> v.
Proof.
  intros T v Hv.
  eapply ms_step; [apply S_Beta; exact Hv |].
  cbn. apply ms_refl.
Qed.

(* Concrete instance:  (λ:Unit. #0) Unit  ==>>  Unit                  *)
Example red_identity_unit :
  ((λ: T_UnitT \\ $$ 0) @· unit_v) ==>> unit_v.
Proof. apply red_identity, unit_v_value. Qed.

(* 3.2  Lifetime instantiation:  (Λl. body) {l0}  ==>>  body[0:=l0]   *)
Lemma red_lt_beta : forall body l,
  ((Λl \\ body) @lt[ l ]) ==>> subst_lt_in_tm 0 l body.
Proof. intros. apply ms_one. apply S_LtBeta. Qed.

(* 3.3  Type instantiation:  (Λt:B. body) [T]   ==>>  body[0:=T]     *)
Lemma red_ty_beta : forall B body T,
  ((Λt: B \\ body) @ty[ T ]) ==>> subst_ty_in_tm 0 T body.
Proof. intros. apply ms_one. apply S_TyBeta. Qed.

(* 3.4  Match success on a free pair                                  *)
Example red_match_pair :
  let p := term_ctor 1 `Lf [] [] [unit_v; unit_v] in
  term_match p 1 2 ($$ 1) ($$ 0) ==>> unit_v.
Proof.
  cbn.
  eapply ms_step.
  - apply S_MatchYes with (vs := [unit_v; unit_v]); repeat constructor.
  - cbn. apply ms_refl.
Qed.

(* 3.5  Typing proofs for Section-3 programs                           *)

(* The identity function is well-typed at any type T without local refs. *)
Example typed_identity :
  forall Γ T, no_local_ty T = true ->
    Γ ⊢ₜ (λ: T \\ $$ 0) : (T -{ `Lf }-> T).
Proof.
  intros Γ T Hnl.
  apply T_Lam.
  - apply T_Var. reflexivity.
  - apply LS_Refl.
  - exact Hnl.
Qed.

(* The concrete match-pair program from 3.4 is well-typed in a context  *)
(* that declares constructor 1 as a binary pair constructor.            *)
(* (The T_Match inference is deferred; see ex_match_pair in Section 1.) *)
Example typed_match_pair :
  [ bind_ctor 1 0 0 [T_UnitT; T_UnitT] (type_ctor 1 lt_free []) ] ⊢ₜ
    term_match (term_ctor 1 lt_free [] [] [unit_v; unit_v]) 1 2 ($$ 1) ($$ 0)
    : T_UnitT.
Proof.
  (* Deferred: T_Match with concrete types requires careful argument passing. *)
  (* See the analogous ex_match_pair in Section 1 for the proof pattern.    *)
  admit.
Admitted.

(* ================================================================== *)
(* 4. Effect programs — reductions and typings                        *)
(* ================================================================== *)

(* 4.1  Reader<Unit>  ==>>  Unit *)
Example red_reader : reader_program ==>> unit_v.
Proof.
  unfold reader_program, reader_op_body.
  (* Step 1: H_Handle picks a fresh marker (we pick m=0). *)
  eapply ms_step.
  { apply (S_step EC_hole).
    - constructor.
    - apply (H_Handle Reader_tag [T_UnitT] (($$ 1) @· unit_v)
                       (term_perform ($$ 0) [] unit_v) 0). }
  cbn.
  (* Step 2: H_Perform with the empty pure context. *)
  eapply ms_step.
  { apply (S_step EC_hole).
    - constructor.
    - apply (H_Perform Reader_tag 0 [T_UnitT]
              (($$ 1) @· unit_v) [] unit_v EC_hole);
        [ apply unit_v_value | constructor ]. }
  cbn.
  (* Step 3: H_Resume — apply resumption to Unit. *)
  eapply ms_step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Resume, unit_v_value. }
  cbn.
  (* Step 4: H_Return collapses the handler. *)
  eapply ms_step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Return, unit_v_value. }
  apply ms_refl.
Qed.

(* 4.2  Exception<Unit>  ==>>  Unit *)
Example red_exception : exception_program ==>> unit_v.
Proof.
  unfold exception_program, exception_op_body.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_Handle Exception_tag [T_UnitT] unit_v
                     (term_perform ($$ 0) [] unit_v) 0). }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_Perform Exception_tag 0 [T_UnitT] unit_v [] unit_v EC_hole);
      [ apply unit_v_value | constructor ]. }
  cbn.
  apply ms_refl.
Qed.

(* 4.3  Choice (per-op β)  ==>>  Unit *)
Example red_choice : choice_program ==>> unit_v.
Proof.
  unfold choice_program, choice_op_body.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_Handle Choice_tag [] (($$ 1) @· unit_v)
                     (term_perform ($$ 0) [T_UnitT] unit_v) 0). }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_Perform Choice_tag 0 [] (($$ 1) @· unit_v)
                     [T_UnitT] unit_v EC_hole);
      [ apply unit_v_value | constructor ]. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Resume, unit_v_value. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor. apply H_Return, unit_v_value. }
  apply ms_refl.
Qed.

(* 4.4  Typing proofs for Section-4 programs *)

(* Reader<Unit>: the program has type Unit in data_ctx ++ effect_ctx.  *)
Example typed_reader :
  (data_ctx ++ effect_ctx) ⊢ₜ reader_program : T_UnitT.
Proof.
  unfold reader_program, reader_op_body, data_ctx, repo_sig, effect_ctx, reader_sig.
  eapply (T_Handle _ Reader_tag [T_UnitT] _ _ 1 0 T_UnitT (`T 0) T_UnitT T_UnitT T_UnitT).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - eapply T_App.
    + apply T_Var. reflexivity.
    + eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
      * apply LS_Refl.
      * constructor.
  - eapply T_Perform with (n_α := 1) (n_β := 0) (sig := T_UnitT) (ret := `T 0)
                          (Ts := [T_UnitT]) (Ss := []) (Δ := `Ll).
    + apply T_Var. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
      * apply LS_Refl.
      * constructor.
Qed.

(* Exception<Unit>: the program has type Unit in effect_ctx.           *)
Example typed_exception :
  (data_ctx ++ effect_ctx) ⊢ₜ exception_program : T_UnitT.
Proof.
  unfold exception_program, exception_op_body, data_ctx, repo_sig, effect_ctx, exception_sig.
  eapply (T_Handle _ Exception_tag [T_UnitT] _ _ 1 0 (`T 0) T_UnitT T_UnitT T_UnitT T_UnitT).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
    + apply LS_Refl.
    + constructor.
  - eapply T_Perform with (n_α := 1) (n_β := 0) (sig := `T 0) (ret := T_UnitT)
                          (Ts := [T_UnitT]) (Ss := []) (Δ := `Ll).
    + apply T_Var. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
      * apply LS_Refl.
      * constructor.
Qed.

(* Choice (per-op β): the program has type Unit in effect_ctx.         *)
Example typed_choice :
  (data_ctx ++ effect_ctx) ⊢ₜ choice_program : T_UnitT.
Proof.
  (* choice_op_body = ($$ 1) @· unit_v requires β = T_UnitT; non-polymorphic instance *)
  admit.
Admitted.

(* ================================================================== *)
(* 5. Capability cannot escape its handle scope (negative result)      *)
(* ================================================================== *)

Lemma cap_escape_blocked :
  forall (E : eff_tag) (Ts : list type),
    no_local_ty (type_ctor E `Ll Ts) = false.
Proof. intros; cbn; reflexivity. Qed.

(* ================================================================== *)
(* 6. State<a> reductions                                             *)
(* ================================================================== *)

(* 6.1  Get on initial state zero  ==>>  Zero                          *)
Example red_state_get : state_get_program ==>> zero_v.
Proof.
  unfold state_get_program, state_op_body.
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply (H_Handle State_tag [T_NatT] _ _ 0). }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply (H_Perform State_tag 0 [T_NatT] _ [] get_v
              (EC_app2 (λ: T_NatT \\ λ: T_NatT \\ ($$ 1)) EC_hole));
        [ apply get_v_value | repeat constructor ]. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta, zero_v_value. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_MatchYes get_tag `Lf [] [] [] _ _).
    constructor. }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply H_Resume, zero_v_value. }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 (EC_handler_m 0 EC_hole) zero_v)).
    - repeat constructor.
    - apply H_Beta, zero_v_value. }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply H_Return, value_lam. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta, zero_v_value. }
  cbn. apply ms_refl.
Qed.

(* 6.2  Put one on initial state zero  ==>>  one                       *)
Example red_state_put : state_put_program ==>> one_v.
Proof.
  unfold state_put_program, state_op_body.
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply (H_Handle State_tag [T_NatT] _ _ 0). }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply (H_Perform State_tag 0 [T_NatT] _ [] (put_v one_v)
              (EC_app2 (λ: T_NatT \\ λ: T_NatT \\ ($$ 1)) EC_hole));
        [ apply put_v_one_value | repeat constructor ]. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta, zero_v_value. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_MatchNo get_tag put_tag `Lf [] [] [one_v] 0 _ _).
    - repeat constructor.
    - discriminate. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_MatchYes put_tag `Lf [] [] [one_v] _ _).
    repeat constructor. }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole one_v)).
    - repeat constructor.
    - apply H_Resume, one_v_value. }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 (EC_handler_m 0 EC_hole) one_v)).
    - repeat constructor.
    - apply H_Beta, one_v_value. }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole one_v)).
    - repeat constructor.
    - apply H_Return, value_lam. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta, one_v_value. }
  cbn. apply ms_refl.
Qed.

(* 6.3  Sequential Put-then-Get on initial state zero  ==>>  one       *)
Example red_state_putget : state_putget_program ==>> one_v.
Proof.
  unfold state_putget_program, state_op_body.
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply (H_Handle State_tag [T_NatT] _ _ 0). }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply (H_Perform State_tag 0 [T_NatT] _ [] (put_v one_v)
              (EC_app2 _ EC_hole));
        [ apply put_v_one_value | repeat constructor ]. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta, zero_v_value. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_MatchNo get_tag put_tag `Lf [] [] [one_v] 0 _ _).
    - repeat constructor.
    - discriminate. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_MatchYes put_tag `Lf [] [] [one_v] _ _).
    repeat constructor. }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole one_v)).
    - repeat constructor.
    - apply H_Resume, one_v_value. }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 (EC_handler_m 0 EC_hole) one_v)).
    - repeat constructor.
    - apply H_Beta, one_v_value. }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole one_v)).
    - repeat constructor.
    - apply (H_Perform State_tag 0 [T_NatT] _ [] get_v
              (EC_app2 _ EC_hole));
        [ apply get_v_value | repeat constructor ]. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta, one_v_value. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_MatchYes get_tag `Lf [] [] [] _ _).
    constructor. }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole one_v)).
    - repeat constructor.
    - apply H_Resume, one_v_value. }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 (EC_handler_m 0 EC_hole) one_v)).
    - repeat constructor.
    - apply H_Beta, one_v_value. }
  cbn.
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole one_v)).
    - repeat constructor.
    - apply H_Return, value_lam. }
  cbn.
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta, one_v_value. }
  cbn. apply ms_refl.
Qed.

(* ================================================================== *)
(* 7. Lifetime-discipline examples (self-contained typing facts)       *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* 7.1  Computed witnesses: local taint is detected syntactically.     *)
(*                                                                    *)
(*   These are the very checks the type system runs to keep local      *)
(*   (scope-bound) data from escaping through a function's result.     *)
(* ------------------------------------------------------------------ *)

(* A local-tracked value fails the "no_local" check that T_Lam imposes *)
(* on return types: a File@local can never appear in a closure result. *)
Example local_value_not_in_return :
  no_local_ty (T_FileT `Ll) = false.
Proof. reflexivity. Qed.

(* A *free* constructor carrying a single *local* field is itself      *)
(* local-tainted — lt_of_ty_list propagates the field's local stamp.   *)
Example local_field_taints_ctor :
  no_local_lt (lt_of_ty_list [T_FileT `Ll]) = false.
Proof. reflexivity. Qed.

(* By contrast an all-free value passes the check and may escape.       *)
Example free_value_may_escape :
  no_local_ty (T_FileT `Lf) = true.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* 7.2  SA_Any: a tracked local value upcasts into Any@local.          *)
(* ------------------------------------------------------------------ *)
(* beautified:    File@local  <:  Any@local                            *)
(*   Forgetting a value's identity is allowed only when the target     *)
(*   Any-lifetime is at least as restrictive as the source's.          *)
Example ex_any_pack_local :
  data_ctx ⊢ T_FileT `Ll <:: type_ctor any_tag `Ll [].
Proof. apply SA_Any. apply LS_Local. Qed.

(* ------------------------------------------------------------------ *)
(* 7.3  capture_lt: capturing a local var forces a local closure.      *)
(* ------------------------------------------------------------------ *)
(* beautified:
     λ (_ : Unit). (λ (_ : File@local). unit) file        (* file captured *)
   The inner closure discards the captured local `file`, yet because    *)
(*   the OUTER body mentions it, capture_lt pins the outer closure to   *)
(*   `local` — so it can be given type Unit -{local}-> Unit.            *)
Example ex_capture_forces_local :
  ( bind_tm (T_FileT `Ll) :: data_ctx ) ⊢ₜ
    (λ: T_UnitT \\ ((λ: (T_FileT `Ll) \\ unit_v) @· ($$ 1)))
    : (T_UnitT -{ `Ll }-> T_UnitT).
Proof.
  apply T_Lam.
  - eapply T_App with (A := T_FileT `Ll) (l := `Lf) (B := T_UnitT).
    + apply T_Lam.
      * eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
        -- apply LS_Refl.
        -- constructor.
      * cbn. apply LS_Free.
      * reflexivity.
    + apply T_Var. reflexivity.
  - apply LS_Local.       (* capture_lt <: local : forced by the captured file *)
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* 7.4  Existential-lifetime elimination in T_Match.                   *)
(* ------------------------------------------------------------------ *)
(* beautified:
     match r with
     | Repo7[ℓ](x : Any@ℓ)  ->  x          (* x : Any@ℓ, ℓ unpacked here *)
     | _                     ->  fallback   (* fallback : Any@local        *)
   The yes-branch result mentions the freshly-unpacked existential       *)
(*   lifetime ℓ in POSITIVE position, so elim_ty_n must widen Any@ℓ up   *)
(*   to Any@local before it can leave the match.                         *)
Example ex_match_existential_lt :
  let G := [ bind_tm (type_ctor 7 `Ll [])               (* r        : Repo7@local *)
           ; bind_tm (type_ctor any_tag `Ll [])         (* fallback : Any@local   *)
           ; bind_ctor 7 1 0 [type_ctor any_tag (`L 0) []]
                             (type_ctor 7 (`L 0) []) ] in
  G ⊢ₜ term_match ($$ 0) 7 1 ($$ 0) ($$ 1)
    : type_ctor any_tag `Ll [].
Proof.
  intro G.
  eapply T_Match with
    (n_lt := 1) (n_ty := 0) (lts := [`L 0]) (Ts := [])
    (sigma_fields := [type_ctor any_tag (`L 0) []])
    (rho_fields := [type_ctor any_tag (`L 0) []])
    (Delta := `Ll) (arity := 1)
    (scrut_result_ty := type_ctor 7 `Ll [])
    (result_tag := 7) (result_l := `Ll)
    (Γ' := bind_lt `Ll :: G)
    (eta := type_ctor any_tag (`L 0) [])
    (elim_result := type_ctor any_tag `Ll []).
  - discriminate.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - discriminate.
  - apply LS_Refl.
  - apply T_Var. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply T_Var. reflexivity.
  - reflexivity.
  - apply T_Var. reflexivity.
Qed.
