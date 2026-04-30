Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.

(* ================================================================== *)
(* 0. Notation embedding (CoreΔ surface notations)                    *)
(*                                                                    *)
(* All notations are gathered in `Module CoreNotation`.  Open with    *)
(*   Import CoreNotation.                                             *)
(* They are pure display sugar — every notation reduces by [cbn] to   *)
(* the underlying inductive form, so existing proofs need no change   *)
(* beyond the syntactic surface.                                      *)
(*                                                                    *)
(* Lifetimes:                                                         *)
(*   `Lf       — lt_free                                              *)
(*   `Ll       — lt_local                                             *)
(*   `L n      — lt_var n                                             *)
(*   l1 ⊓ l2   — lt_min  (the lattice meet, written `+` in the paper) *)
(*                                                                    *)
(* Types:                                                             *)
(*   `T n      — type_var n                                           *)
(*   A '-{ l }->' B   — type_fun A l B                                *)
(*   ∀'l. T   — type_lt_all T                                         *)
(*   ∀'<: B , T  — type_ty_all B T                                    *)
(*                                                                    *)
(* Terms:                                                             *)
(*   $$ n      — term_var n                                           *)
(*   t @· u    — term_app t u                                         *)
(*   λ: T \\ body         — term_lam body T                           *)
(*   Λl \\ body           — term_lt_lam body                          *)
(*   Λt: B \\ body        — term_ty_lam B body                        *)
(*   t @ty[ T ]           — term_ty_app t T                           *)
(*   t @lt[ l ]           — term_lt_app t l                           *)
(* ================================================================== *)

Module CoreNotation.

  (* --- lifetimes --- *)
  Notation "'`Lf'"     := lt_free.
  Notation "'`Ll'"     := lt_local.
  Notation "'`L' n"    := (lt_var n) (at level 5, format "'`L'  n").
  Notation "l1 '⊓' l2" := (lt_min l1 l2) (at level 50, left associativity).

  (* --- types --- *)
  Notation "'`T' n" := (type_var n) (at level 5, format "'`T'  n").
  Notation "A '-{' l '}->' B" :=
    (type_fun A l B) (at level 70, right associativity, l at level 0).
  Notation "∀' 'l.' T"          := (type_lt_all T) (at level 80, T at level 80).
  Notation "∀' '<:' B ',' T"    := (type_ty_all B T) (at level 80, B at level 0, T at level 80).

  (* --- terms --- *)
  Notation "'$$' n"          := (term_var n) (at level 5, format "'$$' n").
  Notation "t '@·' u"        := (term_app t u) (at level 31, left associativity).
  Notation "'λ:' T '\\' body" :=
    (term_lam body T)
    (at level 80, T at level 0, body at level 80, right associativity).
  Notation "'Λl' '\\' body"  :=
    (term_lt_lam body) (at level 80, body at level 80, right associativity).
  Notation "'Λt:' B '\\' body" :=
    (term_ty_lam B body)
    (at level 80, B at level 0, body at level 80, right associativity).
  Notation "t '@ty[' T ']'"  := (term_ty_app t T) (at level 31, left associativity).
  Notation "t '@lt[' l ']'"  := (term_lt_app t l) (at level 31, left associativity).
  (* Let-binding: `let: T <- e in body` desugars to `(λ: T \ body) @· e`.  *)  
  (* In de Bruijn style `$$ 0` in `body` refers to the bound value.          *)
  Notation "'let:' T '<-' e 'in' body" :=
    (term_app (term_lam body T) e)
    (at level 80, T at level 0, e at level 80, body at level 80,
     right associativity).

End CoreNotation.

Import CoreNotation.

(* ================================================================== *)
(* 0a. Multi-step reduction relation                                  *)
(*                                                                    *)
(* `t ==>> t'` is the reflexive-transitive closure of the small-step  *)
(* relation `==>` from Semantics.v.                                   *)
(* ================================================================== *)

Inductive multi_step : term -> term -> Prop :=
  | ms_refl : forall t, multi_step t t
  | ms_step : forall t1 t2 t3,
      t1 ==> t2 -> multi_step t2 t3 -> multi_step t1 t3.

Notation "t '==>>' t'" := (multi_step t t') (at level 40).

Lemma ms_one : forall t t', t ==> t' -> t ==>> t'.
Proof. intros t t' H. eapply ms_step; [exact H | apply ms_refl]. Qed.

Lemma ms_trans : forall t1 t2 t3, t1 ==>> t2 -> t2 ==>> t3 -> t1 ==>> t3.
Proof.
  intros t1 t2 t3 H12. revert t3.
  induction H12 as [|? ? ? Hs ? IH]; intros u H23; auto.
  eapply ms_step; eauto.
Qed.

(* ================================================================== *)
(* 1. Existing examples — rewritten with the surface notation         *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Example 1: Identity λ(x:A). x  :  A -free-> A                      *)
(* ------------------------------------------------------------------ *)

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

(* ------------------------------------------------------------------ *)
(* Example 2: Free closure ≤ local closure (subsumption)              *)
(* ------------------------------------------------------------------ *)

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

(* ------------------------------------------------------------------ *)
(* Example 3: Higher-order application                                *)
(* ------------------------------------------------------------------ *)

Example ex_app :
  forall (A B : type) (l : lifetime),
    [bind_tm A; bind_tm (A -{ l }-> B)] ⊢ₜ ($$ 1 @· $$ 0) : B.
Proof.
  intros A B ll. eapply T_App; apply T_Var; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Example 4: Lifetime polymorphism (Λl. λ(x:A). x)                  *)
(* ------------------------------------------------------------------ *)

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

(* ------------------------------------------------------------------ *)
(* Example 5: Type polymorphism — identity                             *)
(* ------------------------------------------------------------------ *)

Definition any_local : type := type_ctor 0 `Ll [].

Example ex_ty_poly_id :
  [] ⊢ₜ (Λt: any_local \\ λ: `T 0 \\ $$ 0)
      : ∀' <: any_local , (`T 0 -{ `Lf }-> `T 0).
Proof.
  apply T_TyLam. apply T_Lam.
  - apply T_Var. reflexivity.
  - cbn. apply LS_Free.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Example 6: Constructor — Pair with two free fields                 *)
(* ------------------------------------------------------------------ *)

Definition ty_A : type := type_ctor 42 `Lf [].
Definition ty_B : type := type_ctor 43 `Lf [].
Definition pair_lt_free : lifetime := lt_of_ty_list [ty_A; ty_B].

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
    (rho_fields := [ty_A; ty_B]).
  - reflexivity.
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
(* ------------------------------------------------------------------ *)

Definition ty_A_local : type := type_ctor 42 `Ll [].
Definition pair_lt_local : lifetime := lt_of_ty_list [ty_A_local; ty_B].

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
    (rho_fields := [ty_A_local; ty_B]).
  - reflexivity.
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
(* ------------------------------------------------------------------ *)

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
    (Γ' := [ bind_ctor 1 0 0 [ty_A; ty_B] (type_ctor 1 pair_lt_free [])
           ; bind_tm ty_A
           ; bind_tm (type_ctor 1 pair_lt_free []) ])
    (eta := ty_A) (elim_result := ty_A).
  - discriminate.
  - apply T_Var. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply T_Var. reflexivity.
  - reflexivity.
  - apply T_Var. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Example 9: Repository — existential lifetime constructor           *)
(* ------------------------------------------------------------------ *)

Example ex_repository :
  let AnyAtLocal := type_ctor any_tag `Ll [] in
  [ bind_tm AnyAtLocal
  ; bind_ctor 7 1 0
      [type_ctor any_tag (`L 0) []]
      (type_ctor 7 (`L 0) []) ] ⊢ₜ
    term_ctor 7 (lt_of_ty_list [AnyAtLocal]) [`Ll] [] [$$ 0]
    : type_ctor 7 `Ll [].
Proof.
  intros AnyAtLocal.
  eapply T_Sub.
  - eapply T_Ctor with (lts := [`Ll]) (Ts := []); try reflexivity.
    repeat constructor.
  - apply SA_Data. cbn. apply LS_MinL; apply LS_Local.
Qed.

(* ================================================================== *)
(* 2. Examples mirroring the paper repository                         *)
(* ================================================================== *)

Definition unit_tag       : ctor_tag := 10.
Definition file_tag       : ctor_tag := 11.
Definition connection_tag : ctor_tag := 12.
Definition repo_tag       : ctor_tag := 13.

Definition T_UnitT    : type := type_ctor unit_tag       `Lf [].
Definition T_FileT (l : lifetime) : type := type_ctor file_tag       l [].
Definition T_ConnT (l : lifetime) : type := type_ctor connection_tag l [].
Definition T_RepoT (l : lifetime) : type := type_ctor repo_tag       l [].

(* "Unit value" — the canonical inhabitant of T_UnitT.                *)
Definition unit_v : term := term_ctor unit_tag `Lf [] [] [].

Lemma unit_v_value : value unit_v.
Proof. apply value_ctor. constructor. Qed.
Hint Resolve unit_v_value : core.

(* Repository[lf, lc](File@lf, Connection@lc) : Repository@(lf+lc)    *)
Definition repo_sig : binding :=
  bind_ctor repo_tag 2 0
    [ T_FileT (`L 1) ; T_ConnT (`L 0) ]
    (T_RepoT (`L 1 ⊓ `L 0)).

Definition data_ctx : ctx :=
  [ repo_sig
  ; bind_ctor connection_tag 0 0 [] (T_ConnT `Lf)
  ; bind_ctor file_tag       0 0 [] (T_FileT `Lf)
  ; bind_ctor unit_tag       0 0 [] T_UnitT ].

Example ex_paper_unit :
  data_ctx ⊢ₜ term_ctor unit_tag `Lf [] [] [] : T_UnitT.
Proof.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity. constructor.
Qed.

Example ex_paper_file :
  data_ctx ⊢ₜ term_ctor file_tag `Lf [] [] [] : T_FileT `Lf.
Proof.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity. constructor.
Qed.

Example ex_paper_connection :
  data_ctx ⊢ₜ term_ctor connection_tag `Lf [] [] [] : T_ConnT `Lf.
Proof.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity. constructor.
Qed.

Example ex_paper_repo_intro :
  let lts := [`L 0; `L 1] in
  let rho := List.map (inst_ctor_type 2 0 lts [])
              [ T_FileT (`L 1) ; T_ConnT (`L 0) ] in
  let lr  := lt_of_ty_list rho in
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
  cbn.
  apply Forall2_cons; [| apply Forall2_cons; [| apply Forall2_nil]];
    apply T_Var; reflexivity.
Qed.

Definition makeRepository : term :=
  Λl \\ Λl \\
    λ: (T_FileT (`L 1)) \\
    λ: (T_ConnT (`L 0)) \\
      term_ctor repo_tag
        (lt_of_ty_list (List.map (inst_ctor_type 2 0 [`L 0; `L 1] [])
                          [ T_FileT (`L 1) ; T_ConnT (`L 0) ]))
        [`L 0; `L 1] []
        [$$ 1; $$ 0].

Example ex_paper_makeRepository :
  let inner_lt := `L 1 in
  let result_lt := lt_of_ty_list (List.map (inst_ctor_type 2 0 [`L 0; `L 1] [])
                                    [ T_FileT (`L 1) ; T_ConnT (`L 0) ]) in
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
      apply Forall2_cons; [| apply Forall2_cons; [| apply Forall2_nil]];
        apply T_Var; reflexivity.
    + cbn. apply LS_MinL; [apply LS_MinL; [apply LS_Refl | apply LS_Free] | apply LS_Free].
    + reflexivity.
  - cbn. apply LS_Free.
  - reflexivity.
Qed.

Definition print_fn : term :=
  λ: (T_FileT `Ll) \\
  λ: T_UnitT \\
    term_ctor unit_tag `Lf [] [] [].

Example ex_paper_print :
  data_ctx ⊢ₜ print_fn
    : ((T_FileT `Ll) -{ `Lf }-> (T_UnitT -{ `Lf }-> T_UnitT)).
Proof.
  apply T_Lam.
  - apply T_Lam.
    + eapply T_Ctor with (lts := []) (Ts := []); try reflexivity. constructor.
    + cbn. apply LS_Free.
    + reflexivity.
  - cbn. apply LS_Free.
  - reflexivity.
Qed.

Definition CA : type := type_ctor 100 `Lf [].
Definition CB : type := type_ctor 101 `Lf [].
Definition CC : type := type_ctor 102 `Lf [].

Definition compose_fn : term :=
  Λl \\ Λl \\
    λ: (CB -{ `L 1 }-> CC) \\
    λ: (CA -{ `L 0 }-> CB) \\
    λ: CA \\
      ($$ 2) @· (($$ 1) @· ($$ 0)).

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
(*                                                                    *)
(* For each program we state a result and prove that the program      *)
(* reduces to it via `==>>`.                                          *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* 3.1  Identity application:  (λ:T. #0) v   ==>>   v                 *)
(* ------------------------------------------------------------------ *)

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

(* ------------------------------------------------------------------ *)
(* 3.2  Lifetime instantiation:  (Λl. body) {l0}  ==>>  body[0:=l0]   *)
(* ------------------------------------------------------------------ *)

Lemma red_lt_beta : forall body l,
  ((Λl \\ body) @lt[ l ]) ==>> subst_lt_in_tm 0 l body.
Proof. intros. apply ms_one. apply S_LtBeta. Qed.

(* ------------------------------------------------------------------ *)
(* 3.3  Type instantiation:  (Λt:B. body) [T]   ==>>  body[0:=T]     *)
(* ------------------------------------------------------------------ *)

Lemma red_ty_beta : forall B body T,
  ((Λt: B \\ body) @ty[ T ]) ==>> subst_ty_in_tm 0 T body.
Proof. intros. apply ms_one. apply S_TyBeta. Qed.

(* ------------------------------------------------------------------ *)
(* 3.4  Match success on a free pair                                  *)
(*    match Pair(v1,v2) with Pair(a,b) -> #1 ; _ -> noBody            *)
(*       ==>>  v1                                                     *)
(* ------------------------------------------------------------------ *)

Example red_match_pair :
  let p := term_ctor 1 `Lf [] [] [unit_v; unit_v] in
  term_match p 1 2 ($$ 1) ($$ 0) ==>> unit_v.
Proof.
  cbn.
  eapply ms_step.
  - apply S_MatchYes with (vs := [unit_v; unit_v]); repeat constructor.
  - cbn. apply ms_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* 3.5  Typing proofs for Section-3 programs                           *)
(* ------------------------------------------------------------------ *)

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
(* 4. Effect declarations and usages                                   *)
(*                                                                    *)
(* For each of the three "basic" effects (Reader, Exception, Choice)  *)
(* we give:                                                            *)
(*    (a) the signature binding (`*_sig` / `*_ctx`)                   *)
(*    (b) a concrete program that uses it                              *)
(*    (c) a closed-form result and a proof `program ==>> result`.     *)
(*                                                                    *)
(* The op-body conventions (see Typing.v T_Cap):                       *)
(*   · op-body lives under n_β type-binders, then 2 term-binders.     *)
(*   · #0 = the operation argument (single)                           *)
(*   · #1 = the resumption k : ret -local-> T_R                       *)
(* ================================================================== *)

Definition Reader_tag    : eff_tag := 100.
Definition Exception_tag : eff_tag := 101.
Definition Choice_tag    : eff_tag := 102.

(* Effect signatures:                                                  *)
(*   Reader   : ask : Unit  -> a    (per-effect type param a)         *)
(*   Exception: raise : a   -> Unit                                   *)
(*   Choice   : pick : Unit -> β    (per-op   type param β)           *)
Definition reader_sig    : binding := bind_eff Reader_tag    1 0 T_UnitT (`T 0).
Definition exception_sig : binding := bind_eff Exception_tag 1 0 (`T 0)  T_UnitT.
Definition choice_sig    : binding := bind_eff Choice_tag    0 1 T_UnitT (`T 0).

Definition effect_ctx : ctx := [ reader_sig ; exception_sig ; choice_sig ].

(* ------------------------------------------------------------------ *)
(* 4.1  Reader<Unit>                                                  *)
(*                                                                    *)
(* op-body for ask (in scope: $$ 0 = op-arg : Unit, $$ 1 = resumption k):  *)
(*    k Unit                                                          *)
(* i.e. the "ask" operation immediately resumes with the constant     *)
(* `Unit`.                                                            *)
(*                                                                    *)
(* Program:                                                            *)
(*   handle Reader<Unit> { ask = k Unit } in                           *)
(*     perform cap () ;; this cap = $$ 0 (the bound capability)        *)
(*                                                                    *)
(* Result: Unit.                                                       *)
(* ------------------------------------------------------------------ *)

Definition reader_op_body : term := ($$ 1) @· unit_v.

Definition reader_program : term :=
  term_handle Reader_tag [T_UnitT] reader_op_body
    (term_perform ($$ 0) [] unit_v).

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
  (* State now: handler_m 0 (perform (cap Reader 0 [Unit] op) [] Unit) *)
  (* Step 2: H_Perform with the empty pure context. *)
  eapply ms_step.
  { apply (S_step EC_hole).
    - constructor.
    - apply (H_Perform Reader_tag 0 [T_UnitT]
              (($$ 1) @· unit_v) [] unit_v EC_hole);
        [ apply unit_v_value | constructor ]. }
  cbn.
  (* State now: (term_resume 0 (handler_m 0 #0)) @· unit_v               *)
  (* The outer delimiter has been consumed by H_Perform.                *)
  (* Step 3: H_Resume — apply resumption to Unit; this re-installs a    *)
  (* fresh handler_m 0 around the resumption body.                      *)
  eapply ms_step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Resume, unit_v_value. }
  cbn.
  (* State now: handler_m 0 unit_v.  H_Return collapses it.            *)
  eapply ms_step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Return, unit_v_value. }
  apply ms_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* 4.2  Exception<Unit>                                                *)
(*                                                                    *)
(* op-body for raise (#0=k:Unit-loc->T_R, #1=arg:Unit):                *)
(*    Unit         (* discard the resumption — exceptional return *)  *)
(*                                                                    *)
(* Program:                                                            *)
(*   handle Exception<Unit> { raise = Unit } in                        *)
(*     perform cap () ()                                                *)
(*                                                                    *)
(* Result: Unit.  The handler's body is replaced by Unit because       *)
(* `raise` never invokes its resumption.                                *)
(* ------------------------------------------------------------------ *)

Definition exception_op_body : term := unit_v.

Definition exception_program : term :=
  term_handle Exception_tag [T_UnitT] exception_op_body
    (term_perform ($$ 0) [] unit_v).

Example red_exception : exception_program ==>> unit_v.
Proof.
  unfold exception_program, exception_op_body.
  (* H_Handle (m := 0) *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_Handle Exception_tag [T_UnitT] unit_v
                     (term_perform ($$ 0) [] unit_v) 0). }
  cbn.
  (* H_Perform: the op-body is just `unit_v`, so resumption is dropped. *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_Perform Exception_tag 0 [T_UnitT] unit_v [] unit_v EC_hole);
      [ apply unit_v_value | constructor ]. }
  cbn.
  (* After H_Perform the handler_m is consumed and op_body = unit_v    *)
  (* with the substitution producing exactly unit_v. Done.             *)
  apply ms_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* 4.3  Choice (per-op β)                                              *)
(*                                                                    *)
(* op-body for pick (under 1 type-binder β; $$ 0 = arg, $$ 1 = k):     *)
(*    k Unit         (* always pick "Unit"; only legal at β := Unit *) *)
(*                                                                    *)
(* Program:                                                            *)
(*   handle Choice { pick = k Unit } in                                *)
(*     perform cap [Unit] ()                                            *)
(*                                                                    *)
(* Result: Unit.                                                       *)
(* ------------------------------------------------------------------ *)

Definition choice_op_body : term := ($$ 1) @· unit_v.

Definition choice_program : term :=
  term_handle Choice_tag [] choice_op_body
    (term_perform ($$ 0) [T_UnitT] unit_v).

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
  (* H_Resume — outer delimiter has been consumed.                     *)
  eapply ms_step.
  { apply (S_step EC_hole).
    - constructor.
    - apply H_Resume, unit_v_value. }
  cbn.
  (* H_Return collapses fresh handler_m around unit_v.                 *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor. apply H_Return, unit_v_value. }
  apply ms_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* 4.4  Typing proofs for Section-4 programs                           *)
(* ------------------------------------------------------------------ *)

(* Reader<Unit>: the program has type Unit in data_ctx ++ effect_ctx.  *)
(*                                                                    *)
(* T_Handle: T_R = T_UnitT                                             *)
(*   op_body ctx: [bind_tm T_UnitT (* arg *);                          *)
(*                 bind_tm (T_UnitT -local-> T_UnitT) (* k *)]         *)
(*                ++ data_ctx ++ effect_ctx                             *)
(*   op_body: ($$ 1) @· unit_v  (k applied to unit_v)                 *)
(*   body ctx: [bind_tm (type_ctor Reader_tag lt_local [T_UnitT])]     *)
(*             ++ data_ctx ++ effect_ctx                               *)
(*   body: perform ($$ 0) [] unit_v                                    *)
Example typed_reader :
  (data_ctx ++ effect_ctx) ⊢ₜ reader_program : T_UnitT.
Proof.
  unfold reader_program, reader_op_body, data_ctx, repo_sig, effect_ctx, reader_sig.
  eapply (T_Handle _ Reader_tag [T_UnitT] _ _ 1 0 T_UnitT (`T 0) T_UnitT T_UnitT T_UnitT).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* op_body: ($$ 1) @· unit_v  in  [bind_tm T_UnitT; bind_tm (T_UnitT -local-> T_UnitT); reader_sig; ...] *)
    eapply T_App.
    + apply T_Var. reflexivity.
    + eapply T_Ctor with (lts := []) (Ts := []); try reflexivity; constructor.
  - (* body: perform ($$ 0) [] unit_v in [bind_tm (type_ctor Reader_tag lt_local [T_UnitT]); reader_sig; ...] *)
    eapply T_Perform with (n_α := 1) (n_β := 0) (sig := T_UnitT) (ret := `T 0)
                          (Ts := [T_UnitT]) (Ss := []) (Δ := `Ll).
    + apply T_Var. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply T_Ctor with (lts := []) (Ts := []); try reflexivity; constructor.
Qed.

(* Exception<Unit>: the program has type Unit in effect_ctx.           *)
(*                                                                    *)
(* T_Handle: T_R = T_UnitT                                             *)
(*   op_body: unit_v (discards both arg and k)                         *)
(*   body: perform ($$ 0) [] unit_v                                    *)
Example typed_exception :
  (data_ctx ++ effect_ctx) ⊢ₜ exception_program : T_UnitT.
Proof.
  unfold exception_program, exception_op_body, data_ctx, repo_sig, effect_ctx, exception_sig.
  eapply (T_Handle _ Exception_tag [T_UnitT] _ _ 1 0 (`T 0) T_UnitT T_UnitT T_UnitT T_UnitT).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* op_body: unit_v in [bind_tm T_UnitT; bind_tm (T_UnitT -local-> T_UnitT); ...] *)
    eapply T_Ctor with (lts := []) (Ts := []); try reflexivity; constructor.
  - (* body: perform ($$ 0) [] unit_v *)
    eapply T_Perform with (n_α := 1) (n_β := 0) (sig := `T 0) (ret := T_UnitT)
                          (Ts := [T_UnitT]) (Ss := []) (Δ := `Ll).
    + apply T_Var. reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + eapply T_Ctor with (lts := []) (Ts := []); try reflexivity; constructor.
Qed.

(* Choice (per-op β): the program has type Unit in effect_ctx.         *)
(*                                                                    *)
(* T_Handle: T_R = T_UnitT, n_β=1 (one op-level type var β)           *)
(*   op_body under 1 type-binder:                                      *)
(*     ctx: [bind_tm (`T 0) (* arg *);                                 *)
(*           bind_tm (`T 0 -local-> T_UnitT) (* k *)                   *)
(*           bind_ty any_at_free] ++ effect_ctx                        *)
(*   op_body: ($$ 1) @· unit_v   (k applied to unit_v : `T 0)         *)
(*   body: perform ($$ 0) [T_UnitT] unit_v                             *)
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
(* 6. State<a> — algebraic mutable state, polymorphic over state type *)
(*                                                                    *)
(* The single op of State<a> takes a `Cmd<a>` request:                *)
(*    Cmd<a> ::= Get  |  Put(a)                                        *)
(* and returns `a` (the state type).  The effect has one per-effect   *)
(* type parameter `a`; concrete programs instantiate it to `Nat`.     *)
(*                                                                    *)
(* The handler threads state via the state-passing transform:          *)
(*   handled computation : a → a                                       *)
(*   each `perform Cmd` : a → a (awaiting the current state)          *)
(* The whole program is applied to the initial state `zero_v`.         *)
(* ================================================================== *)

Definition State_tag : eff_tag  := 103.
Definition cmd_tag   : ctor_tag := 60.
Definition get_tag   : ctor_tag := 50.
Definition put_tag   : ctor_tag := 51.
Definition nat_tag   : ctor_tag := 70.
Definition zero_tag  : ctor_tag := 71.
Definition suc_tag   : ctor_tag := 72.

(* Nat type and its constructors:                                     *)
(*   data Nat = Zero | Suc Nat                                         *)
Definition T_NatT : type := type_ctor nat_tag `Lf [].

Definition nat_ctx : ctx :=
  [ bind_ctor zero_tag 0 0 []        T_NatT
  ; bind_ctor suc_tag  0 0 [T_NatT]  T_NatT ].

Definition zero_v : term := term_ctor zero_tag `Lf [] [] [].
Definition suc_v  : term -> term :=
  fun n => term_ctor suc_tag `Lf [] [] [n].
Definition one_v  : term := suc_v zero_v.

Lemma zero_v_value : value zero_v.
Proof. apply value_ctor. constructor. Qed.
Lemma one_v_value  : value one_v.
Proof. apply value_ctor. repeat constructor. Qed.
Hint Resolve zero_v_value one_v_value : core.

(* Cmd type.  Single-tag wrapper; both Get / Put have ctor type Cmd. *)
Definition T_CmdT : type := type_ctor cmd_tag `Lf [].

(* ctor signatures in Γ:                                              *)
(*   Get : Cmd                  (arity 0)                              *)
(*   Put : Nat -> Cmd           (arity 1)                              *)
Definition cmd_ctx : ctx :=
  [ bind_ctor get_tag 0 0 []        T_CmdT
  ; bind_ctor put_tag 0 0 [T_NatT]  T_CmdT ].

Definition get_v : term := term_ctor get_tag `Lf [] [] [].
Definition put_v : term -> term :=
  fun u => term_ctor put_tag `Lf [] [] [u].

Lemma get_v_value : value get_v.
Proof. apply value_ctor. constructor. Qed.
Lemma put_v_one_value : value (put_v one_v).
Proof. apply value_ctor. repeat constructor. Qed.
Hint Resolve get_v_value put_v_one_value : core.

(* State effect signature: req : Cmd<a> -> a, one per-effect type    *)
(* parameter `a = T 0` (the state cell type).  Concrete programs      *)
(* instantiate a := Nat by passing [T_NatT] to term_handle.           *)
Definition state_sig : binding := bind_eff State_tag 1 0 T_CmdT (`T 0).
Definition state_ctx : ctx := state_sig :: cmd_ctx ++ nat_ctx.

(* ------------------------------------------------------------------ *)
(* State-passing op-body — the handler honestly threads a Nat cell.    *)
(*                                                                    *)
(* Idea: the handle's result type is `Nat -free-> Nat` — a function    *)
(* awaiting the *initial* state.  Each operation likewise produces    *)
(* a `Nat -> Nat` whose argument is the *current* state.  Concretely  *)
(* the resumption has type `k : Nat -local-> (Nat -> Nat)`:            *)
(*     · Get   resumes with `s`, then threads `s` forward                *)
(*     · Put n resumes with `n`, then threads `n` forward (state set!) *)
(*                                                                    *)
(* The op-body lives under 2 term-binders                              *)
(*    $$ 0 = arg : Cmd, $$ 1 = resumption k                            *)
(* and we then introduce `λs:Nat.` to receive the threaded state.     *)
(* Index legend after each binder is added:                           *)
(*    inside `λs:Nat.` body                                             *)
(*      $$ 0 = s, $$ 1 = arg, $$ 2 = k                                  *)
(*    inside Get-yes branch (arity 0, no new binders)                  *)
(*      Get-yes = (k @ s) @ s   = ($$ 2) @· ($$ 0) @· ($$ 0)            *)
(*    inside Put-yes branch (arity 1; payload n)                       *)
(*      $$ 0 = n, $$ 1 = s, $$ 2 = arg, $$ 3 = k                        *)
(*      Put-yes = (k @ n) @ n   = ($$ 3) @· ($$ 0) @· ($$ 0)            *)
(* ------------------------------------------------------------------ *)
Definition state_op_body : term :=
  λ: T_NatT \\
    term_match ($$ 1) get_tag 0
      (($$ 2) @· ($$ 0) @· ($$ 0))
      (term_match ($$ 1) put_tag 1
         (($$ 3) @· ($$ 0) @· ($$ 0))
         ($$ 0)).

(* ------------------------------------------------------------------ *)
(* Each program has the shape                                          *)
(*    (handle State { op_body } in body) @· zero_v                     *)
(* where `body : Nat -free-> Nat` and `zero_v` is the initial state.   *)
(*                                                                    *)
(* The body uses the Haskell-let idiom                                 *)
(*    let n = perform cap req in λ_:Nat. <expr in n>                   *)
(*  ≡ (λn:Nat. λ_:Nat. <expr in n>) @· (perform cap req)               *)
(* so that each perform's continuation closes over the rest of body   *)
(* and ends in a `λ_:Nat. _` value awaiting the (current) state.       *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* 6.1  Get on initial state zero  ==>>  Zero                          *)
(* ------------------------------------------------------------------ *)

Definition state_get_program : term :=
  (term_handle State_tag [T_NatT] state_op_body
     (let: T_NatT <- term_perform ($$ 0) [] get_v in
      λ: T_NatT \\ ($$ 1)))
  @· zero_v.

Example red_state_get : state_get_program ==>> zero_v.
Proof.
  unfold state_get_program, state_op_body.
  (* 1. H_Handle (m := 0). *)
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply (H_Handle State_tag [T_NatT] _ _ 0). }
  cbn.
  (* 2. H_Perform on Get: P = EC_app2 (λn.λs.n) EC_hole. *)
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply (H_Perform State_tag 0 [T_NatT] _ [] get_v
              (EC_app2 (λ: T_NatT \\ λ: T_NatT \\ ($$ 1)) EC_hole));
        [ apply get_v_value | repeat constructor ]. }
  cbn.
  (* 3. S_Beta on the outer @·zero_v: substitute s := zero. *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta, zero_v_value. }
  cbn.
  (* 4. Outer match on Get succeeds (arity 0). *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_MatchYes get_tag `Lf [] [] [] _ _).
    constructor. }
  cbn.
  (* 5. H_Resume on inner (resume 0 ((λn.λs.n) @· $$0)) @· zero_v. *)
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply H_Resume, zero_v_value. }
  cbn.
  (* 6. H_Beta inside handler_m: (λn.λs.n) @· zero_v ==> λs. zero_v. *)
  eapply ms_step.
  { apply (S_step (EC_app1 (EC_handler_m 0 EC_hole) zero_v)).
    - repeat constructor.
    - apply H_Beta, zero_v_value. }
  cbn.
  (* 7. H_Return: handler_m 0 (λs. zero_v) ==> λs. zero_v. *)
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply H_Return, value_lam. }
  cbn.
  (* 8. H_Beta on outer: (λs. zero_v) @· zero_v ==> zero_v. *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta, zero_v_value. }
  cbn. apply ms_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* 6.2  Put one on initial state zero  ==>>  one                       *)
(*                                                                    *)
(* Put returns the new state; here that is `one_v`.                   *)
(* ------------------------------------------------------------------ *)

Definition state_put_program : term :=
  (term_handle State_tag [T_NatT] state_op_body
     (let: T_NatT <- term_perform ($$ 0) [] (put_v one_v) in
      λ: T_NatT \\ ($$ 1)))
  @· zero_v.

Example red_state_put : state_put_program ==>> one_v.
Proof.
  unfold state_put_program, state_op_body.
  (* 1. H_Handle. *)
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply (H_Handle State_tag [T_NatT] _ _ 0). }
  cbn.
  (* 2. H_Perform on Put. *)
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply (H_Perform State_tag 0 [T_NatT] _ [] (put_v one_v)
              (EC_app2 (λ: T_NatT \\ λ: T_NatT \\ ($$ 1)) EC_hole));
        [ apply put_v_one_value | repeat constructor ]. }
  cbn.
  (* 3. S_Beta on outer @·zero_v: substitute s := zero. *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta, zero_v_value. }
  cbn.
  (* 4. Outer match on Get FAILS. *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_MatchNo get_tag put_tag `Lf [] [] [one_v] 0 _ _).
    - repeat constructor.
    - discriminate. }
  cbn.
  (* 5. Inner match on Put SUCCEEDS (arity 1, payload one_v). *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_MatchYes put_tag `Lf [] [] [one_v] _ _).
    repeat constructor. }
  cbn.
  (* 6. H_Resume on (resume 0 ((λn.λs.n) @· $$0)) @· one_v. *)
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole one_v)).
    - repeat constructor.
    - apply H_Resume, one_v_value. }
  cbn.
  (* 7. H_Beta inside handler_m: (λn.λs.n) @· one_v ==> λs. one_v. *)
  eapply ms_step.
  { apply (S_step (EC_app1 (EC_handler_m 0 EC_hole) one_v)).
    - repeat constructor.
    - apply H_Beta, one_v_value. }
  cbn.
  (* 8. H_Return. *)
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole one_v)).
    - repeat constructor.
    - apply H_Return, value_lam. }
  cbn.
  (* 9. H_Beta on outer: (λs. one_v) @· one_v ==> one_v. *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta, one_v_value. }
  cbn. apply ms_refl.
Qed.

(* ------------------------------------------------------------------ *)
(* 6.3  Sequential Put-then-Get on initial state zero  ==>>  one       *)
(*                                                                    *)
(* Pseudocode:                                                         *)
(*    let _  = put one in                                              *)
(*    let n  = get      in                                             *)
(*    n                                                                *)
(*                                                                    *)
(* Encoded with Haskell-let idiom inside the handle, paired with an    *)
(* outer @· zero_v that supplies the initial state to the resulting    *)
(* `Nat -> Nat`.  This honestly observes the state mutation: although  *)
(* the cell starts at zero, after `put one` the subsequent `get`       *)
(* observes `one`, and the program reduces to `one_v`.                 *)
(* ------------------------------------------------------------------ *)

Definition state_putget_program : term :=
  (term_handle State_tag [T_NatT] state_op_body
     (let: T_NatT <- term_perform ($$ 0) [] (put_v one_v) in
      let: T_NatT <- term_perform ($$ 1) [] get_v in
      λ: T_NatT \\ ($$ 1)))
  @· zero_v.

Example red_state_putget : state_putget_program ==>> one_v.
Proof.
  unfold state_putget_program, state_op_body.
  (* 1. H_Handle. *)
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply (H_Handle State_tag [T_NatT] _ _ 0). }
  cbn.
  (* 2. H_Perform on the inner Put. *)
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole zero_v)).
    - repeat constructor.
    - apply (H_Perform State_tag 0 [T_NatT] _ [] (put_v one_v)
              (EC_app2 _ EC_hole));
        [ apply put_v_one_value | repeat constructor ]. }
  cbn.
  (* 3. S_Beta on outer @·zero_v: substitute s := zero. *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta, zero_v_value. }
  cbn.
  (* 4. Outer match on Get FAILS. *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_MatchNo get_tag put_tag `Lf [] [] [one_v] 0 _ _).
    - repeat constructor.
    - discriminate. }
  cbn.
  (* 5. Inner match on Put SUCCEEDS (k resumes with new state n=one). *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_MatchYes put_tag `Lf [] [] [one_v] _ _).
    repeat constructor. }
  cbn.
  (* 6. H_Resume — re-enter body with Put's response = one_v.          *)
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole one_v)).
    - repeat constructor.
    - apply H_Resume, one_v_value. }
  cbn.
  (* 7. H_Beta inside handler_m: outer let-binder consumes one_v.      *)
  eapply ms_step.
  { apply (S_step (EC_app1 (EC_handler_m 0 EC_hole) one_v)).
    - repeat constructor.
    - apply H_Beta, one_v_value. }
  cbn.
  (* 8. H_Perform on Get (state is now `one`, threaded via resume).    *)
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole one_v)).
    - repeat constructor.
    - apply (H_Perform State_tag 0 [T_NatT] _ [] get_v
              (EC_app2 _ EC_hole));
        [ apply get_v_value | repeat constructor ]. }
  cbn.
  (* 9. S_Beta on outer @·one_v: substitute s := one. *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta, one_v_value. }
  cbn.
  (* 10. Outer match on Get SUCCEEDS — resumes with current state. *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply (H_MatchYes get_tag `Lf [] [] [] _ _).
    constructor. }
  cbn.
  (* 11. H_Resume — re-enter body with Get's response = one_v. *)
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole one_v)).
    - repeat constructor.
    - apply H_Resume, one_v_value. }
  cbn.
  (* 12. H_Beta inside handler_m: inner let-binder consumes one_v. *)
  eapply ms_step.
  { apply (S_step (EC_app1 (EC_handler_m 0 EC_hole) one_v)).
    - repeat constructor.
    - apply H_Beta, one_v_value. }
  cbn.
  (* 13. H_Return: body finishes as λs. one_v. *)
  eapply ms_step.
  { apply (S_step (EC_app1 EC_hole one_v)).
    - repeat constructor.
    - apply H_Return, value_lam. }
  cbn.
  (* 14. H_Beta on outer: (λs. one_v) @· one_v ==> one_v. *)
  eapply ms_step.
  { apply (S_step EC_hole). constructor.
    apply H_Beta, one_v_value. }
  cbn. apply ms_refl.
Qed.
