Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.

(* ================================================================== *)
(* Examples                                                            *)
(*                                                                     *)
(* Positive examples: well-typed terms.                               *)
(* Negative examples: `Fail` blocks confirm ill-typedness.            *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Example 1: Identity function                                        *)
(*   λ(x : T). x  :  T -free-> T                                     *)
(*                                                                     *)
(* term_lam (term_var 0) A  under empty context.                      *)
(* The single binder puts x at index 0.                               *)
(* ------------------------------------------------------------------ *)

Example ex_identity :
  forall A : type,
    no_local_ty A = true ->
    [] ⊢ₜ term_lam (term_var 0) A : type_fun A lt_free A.
Proof.
  intros A HA.
  apply T_Lam.
  - apply T_Var. reflexivity.
  - (* capture_lt [] (term_var 0) = lt_free *)
    cbn. apply LS_Free.
  - exact HA.
Qed.

(* ------------------------------------------------------------------ *)
(* Example 2: Free lambda can be upcasted to local closure            *)
(*   By subsumption (T_Sub + SA_Fun + LS_Trans/Refl):                *)
(*   λ(x:A).x : A -free-> A  <::  A -local-> A                       *)
(*                                                                     *)
(* (free <: local, so free-closure <:: local-closure covariantl)     *)
(* ------------------------------------------------------------------ *)

Example ex_upcast_closure_lt :
  forall A : type,
    no_local_ty A = true ->
    [] ⊢ₜ term_lam (term_var 0) A : type_fun A lt_local A.
Proof.
  intros A HA.
  eapply T_Sub.
  - apply T_Lam.
    + apply T_Var. reflexivity.
    + cbn. apply LS_Free.
    + exact HA.
  - apply SA_Fun.
    + apply SA_Refl.
    + apply LS_Free.
    + apply SA_Refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Example 3: Higher-order function — apply an argument                *)
(*   Γ = [x:(A -l-> B), f:A]                                         *)
(*   term_app (term_var 1) (term_var 0) : B                           *)
(* ------------------------------------------------------------------ *)

Example ex_app :
  forall (A B : type) (l : lifetime),
    [bind_tm A; bind_tm (type_fun A l B)] ⊢ₜ
      term_app (term_var 1) (term_var 0) : B.
Proof.
  intros A B l.
  eapply T_App.
  - apply T_Var. reflexivity.
  - apply T_Var. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Example 4: Lifetime polymorphism                                   *)
(*   Λl. (λ(x:A). x) : ∀l. A -l-> A                                 *)
(*   (The function does not capture, so its lifetime is the bound l)  *)
(* ------------------------------------------------------------------ *)

Example ex_lt_poly :
  forall A : type,
    no_local_ty (shift_lt_in_ty 1 0 A) = true ->
    [] ⊢ₜ
      term_lt_lam (term_lam (term_var 0) (shift_lt_in_ty 1 0 A))
      : type_lt_all (type_fun (shift_lt_in_ty 1 0 A) (lt_var 0)
                               (shift_lt_in_ty 1 0 A)).
Proof.
  intros A HA.
  apply T_LtLam.
  eapply T_Sub.
  - apply T_Lam.
    + apply T_Var. reflexivity.
    + cbn. apply LS_Free.
    + exact HA.
  - apply SA_Fun.
    + apply SA_Refl.
    + apply LS_Free.   (* lt_free <: lt_var 0 *)
    + apply SA_Refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Example 5: Type polymorphism (identity for any bounded type)       *)
(*   Λ(α <: Any_local). λ(x:α). x : ∀(α<:Any_local). α -free-> α   *)
(*                                                                     *)
(* We use type_ctor 0 lt_local [] as a stand-in for "Any@local".     *)
(* ------------------------------------------------------------------ *)

Definition any_local : type := type_ctor 0 lt_local [].

Example ex_ty_poly_id :
  [] ⊢ₜ
    term_ty_lam any_local (term_lam (term_var 0) (type_var 0))
    : type_ty_all any_local (type_fun (type_var 0) lt_free (type_var 0)).
Proof.
  apply T_TyLam.
  apply T_Lam.
  - apply T_Var. reflexivity.
  - cbn. apply LS_Free.
  - reflexivity.   (* no_local_ty (type_var 0) = true *)
Qed.

(* ------------------------------------------------------------------ *)
(* Example 6: Constructor — Pair with two free fields                 *)
(*                                                                     *)
(* Context contains:                                                   *)
(*   bind_ctor 1 0 0 [ty_A; ty_B] ...  (* Pair : A × B *)            *)
(*   bind_tm ty_B   (* y : B *)                                        *)
(*   bind_tm ty_A   (* x : A *)                                        *)
(*                                                                     *)
(* Result lifetime = lt_of_ty_list [ty_A; ty_B]  (nested lt_min)     *)
(* ------------------------------------------------------------------ *)

Definition ty_A : type := type_ctor 42 lt_free [].
Definition ty_B : type := type_ctor 43 lt_free [].
Definition pair_lt_free : lifetime := lt_of_ty_list [ty_A; ty_B].

Example ex_ctor_pair_free :
  let Γ := [ bind_ctor 1 0 0 [ty_A; ty_B] (type_ctor 1 pair_lt_free [])
            ; bind_tm ty_B
            ; bind_tm ty_A ] in
  Γ ⊢ₜ
    term_ctor 1 pair_lt_free [] [term_var 1; term_var 0]
    : type_ctor 1 pair_lt_free [].
Proof.
  eapply T_Ctor with
    (n_lt := 0) (n_ty := 0) (lts := [])
    (sigma_fields := [ty_A; ty_B])
    (rho_fields := [ty_A; ty_B]).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold pair_lt_free. reflexivity.
  - reflexivity.
  - repeat constructor; apply T_Var; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Example 7: Constructor — tracked field gives local result          *)
(*                                                                     *)
(* Pair(x, y) where x : A@local; result lifetime contains lt_local.  *)
(* n_lt = 0, n_ty = 0                                                 *)
(* ------------------------------------------------------------------ *)

Definition ty_A_local : type := type_ctor 42 lt_local [].
Definition pair_lt_local : lifetime := lt_of_ty_list [ty_A_local; ty_B].

Example ex_ctor_pair_local :
  let Γ := [ bind_ctor 1 0 0 [ty_A_local; ty_B] (type_ctor 1 pair_lt_local [])
            ; bind_tm ty_B
            ; bind_tm ty_A_local ] in
  Γ ⊢ₜ
    term_ctor 1 pair_lt_local [] [term_var 1; term_var 0]
    : type_ctor 1 pair_lt_local [].
Proof.
  eapply T_Ctor with
    (n_lt := 0) (n_ty := 0) (lts := [])
    (sigma_fields := [ty_A_local; ty_B])
    (rho_fields := [ty_A_local; ty_B]).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - unfold pair_lt_local. reflexivity.
  - reflexivity.
  - repeat constructor; apply T_Var; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Example 8: Match — extract a free field from a free Pair           *)
(*                                                                     *)
(* Γ = [bind_ctor 1 0 0 [ty_A; ty_B] ...; bind_tm (type_ctor 1 lt_free [])] *)
(* match x { Pair(a,b) => a | _ => default }                         *)
(*                                                                     *)
(* n_lt = 0, so no fresh lt-vars; Γ' = Γ.                            *)
(* yes_body = term_var 1 (= a, outermost field, index 1 under 2 tm binders) *)
(* eta = ty_A  (type of yes_body)                                     *)
(* elim_ty_n 0 ... = Some ty_A                                       *)
(* no_body : ty_A                                                     *)
(* ------------------------------------------------------------------ *)

Example ex_match_pair :
  let Γ := [ bind_ctor 1 0 0 [ty_A; ty_B] (type_ctor 1 pair_lt_free [])
            ; bind_tm ty_A           (* default value for else branch *)
            ; bind_tm (type_ctor 1 pair_lt_free []) ] in
  Γ ⊢ₜ
    term_match (term_var 1) 1 2 (term_var 0) (term_var 0)
    : ty_A.
Proof.
  eapply T_Match with
    (n_lt := 0) (n_ty := 0) (lts := []) (Ts := [])
    (sigma_fields := [ty_A; ty_B])
    (rho_fields := [ty_A; ty_B])
    (Delta := pair_lt_free) (arity := 2)
    (Γ' := [ bind_ctor 1 0 0 [ty_A; ty_B] (type_ctor 1 pair_lt_free [])
           ; bind_tm ty_A
           ; bind_tm (type_ctor 1 pair_lt_free []) ])
    (eta := ty_A) (elim_result := ty_A).
  - apply T_Var. reflexivity.   (* scrut : type_ctor 1 pair_lt_free [] *)
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply T_Var. reflexivity.   (* yes_body: term_var 0 = ty_A under [bind_tm ty_A; bind_tm ty_B; Γ'] *)
  - reflexivity.
  - apply T_Var. reflexivity.   (* no_body: term_var 0 = ty_A *)
Qed.

(* ------------------------------------------------------------------ *)
(* Negative Example 1: Variable not in context                        *)
(*   [] ⊢ₜ term_var 0 : T  is unprovable                              *)
(* ------------------------------------------------------------------ *)

Example ex_neg_unbound_var :
  forall T : type, ~ ([] ⊢ₜ term_var 0 : T).
Proof.
  intros T H.
  remember (term_var 0) as t eqn:Ht.
  remember ([] : ctx) as Γ eqn:HΓ.
  induction H; subst; try discriminate.
  - apply IHtyping; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Negative Example 2: Wrong constructor lifetime                     *)
(*   term_ctor with lt_local when fields are all free → can't be typed *)
(*   as type_ctor K lt_local [] if the declared result is lt_free.   *)
(*                                                                     *)
(* We check that term_ctor 1 lt_local [] [] : type_ctor 1 lt_local [] *)
(* is unprovable when the ctor has 0 fields (so lt_of_ty_list [] =   *)
(* lt_free ≠ lt_local).                                               *)
(* ------------------------------------------------------------------ *)

Example ex_neg_wrong_lt :
  let Γ := [bind_ctor 1 0 0 [] (type_ctor 1 lt_free [])] in
  ~ (Γ ⊢ₜ term_ctor 1 lt_local [] [] : type_ctor 1 lt_local []).
Proof.
  intros Γ H.
  remember (term_ctor 1 lt_local [] []) as t eqn:Ht.
  induction H; try discriminate.
  - (* T_Sub: IHtyping : t = term_ctor 1 lt_local [] [] -> False *)
    apply IHtyping; exact Ht.
  - (* T_Ctor: K=1, l=lt_local, Ts=[], vs=[] (unified by induction) *)
    (* premises: lt_local = lt_of_ty_list rho_fields, rho_fields = map ... [] *)
    cbn in *.
Admitted. (* TODO: show lt_local ≠ lt_free after reducing rho_fields *)

Example ex_neg_app_mismatch :
  ~ ([] ⊢ₜ term_app (term_lam (term_var 0) ty_A)
                     (term_ctor 43 lt_free [] [])
           : ty_A).
Proof.
  intros H. admit.
Admitted. (* TODO *)

