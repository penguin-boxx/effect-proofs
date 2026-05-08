(* ================================================================== *)
(* Examples.v — small sanity-check terms exercising the LN encoding.  *)
(*                                                                    *)
(* Goal: check that the AST and reductions can be instantiated on a  *)
(* handful of representative shapes (identity λ, polymorphic id, an  *)
(* empty constructor value, β-reduction, etc.).                       *)
(*                                                                    *)
(* Typing-derivation sanity checks are stated and `Admitted` — they  *)
(* exercise capture_lt, no_local_ty, and atom-fresh side-conditions  *)
(* that are tedious to discharge by hand.  The structural / value /  *)
(* head-step examples are proved.                                     *)
(* ================================================================== *)

From Stdlib Require Import List.
Import ListNotations.
From Metalib Require Export Metatheory.

Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import CEK.

(* ================================================================== *)
(* 0. Surface notations for term/type readability.                    *)
(*                                                                    *)
(* All notations are display sugar — they reduce by `cbn`/`unfold` to *)
(* the underlying inductive forms, so existing proofs need no change *)
(* beyond the syntactic surface.                                      *)
(*                                                                    *)
(* Open with `Import CoreNotation`.                                   *)
(*                                                                    *)
(* Lifetimes:                                                          *)
(*   `Lf       — lt_free                                              *)
(*   `Ll       — lt_local                                             *)
(*   l1 ⊓ l2   — lt_min                                                *)
(*                                                                    *)
(* Types:                                                              *)
(*   A '-{' l '}->' B  — type_fun A l B                                *)
(*                                                                    *)
(* Terms:                                                              *)
(*   $$ n               — term_bvar n                                  *)
(*   t @· u             — term_app t u                                 *)
(*   λ: T \\ body       — term_lam body T                              *)
(*   Λl \\ body         — term_lt_lam body                             *)
(*   Λt: B \\ body      — term_ty_lam B body                           *)
(*   t @ty[ T ]         — term_ty_app t T                              *)
(*   t @lt[ l ]         — term_lt_app t l                              *)
(*   let: T '<-' e 'in' body            — (λ:T. body) @· e             *)
(* ================================================================== *)

Module CoreNotation.

  (* --- lifetimes --- *)
  Notation "'`Lf'"     := lt_free.
  Notation "'`Ll'"     := lt_local.
  Notation "l1 '⊓' l2" := (lt_min l1 l2)
    (at level 50, left associativity).

  (* --- types --- *)
  Notation "A '-{' l '}->' B" := (type_fun A l B)
    (at level 70, right associativity, l at level 0).

  (* --- terms --- *)
  Notation "'$$' n" := (term_bvar n)
    (at level 5, format "'$$' n").
  Notation "t '@·' u" := (term_app t u)
    (at level 31, left associativity).
  Notation "'λ:' T '\\' body" := (term_lam body T)
    (at level 80, T at level 0, body at level 80, right associativity).
  Notation "'Λl' '\\' body" := (term_lt_lam body)
    (at level 80, body at level 80, right associativity).
  Notation "'Λt:' B '\\' body" := (term_ty_lam B body)
    (at level 80, B at level 0, body at level 80, right associativity).
  Notation "t '@ty[' T ']'" := (term_ty_app t T)
    (at level 31, left associativity).
  Notation "t '@lt[' l ']'" := (term_lt_app t l)
    (at level 31, left associativity).

  (* let: T <- e in body  ≡  (λ:T. body) @· e   (the bound value is $$0
     in body). *)
  Notation "'let:' T '<-' e 'in' body" :=
    (term_app (term_lam body T) e)
    (at level 80, T at level 0, e at level 80, body at level 80,
     right associativity).

End CoreNotation.

(* ------------------------------------------------------------------ *)
(* 1. Identity at type any@free :  λ x : any@free. x                  *)
(* ------------------------------------------------------------------ *)

Definition id_any : term :=
  term_lam (term_bvar 0) any_at_free.

Example id_any_value : value id_any.
Proof. unfold id_any; constructor. Qed.

(* Typing: ⊢ id_any : any@free →ₗ_free any@free *)
Example id_any_typing :
  [] |-t id_any : type_fun any_at_free lt_free any_at_free.
Proof.
  unfold id_any.
  apply (T_Lam empty).
  - intros x _. simpl.
    apply T_Var. simpl.
    destruct (x == x); [reflexivity | contradiction].
  - cbn. apply LS_Free.
Qed.

(* ------------------------------------------------------------------ *)
(* 2. The empty data value :  ctor any_tag@free [] [] []              *)
(* ------------------------------------------------------------------ *)

Definition empty_any : term :=
  term_ctor any_tag lt_free [] [] [].

Example empty_any_value : value empty_any.
Proof. unfold empty_any; constructor; constructor. Qed.

(* ------------------------------------------------------------------ *)
(* 3. β-reduction example :  (λ x:any@free. x) empty_any  ~~>h  empty_any *)
(* ------------------------------------------------------------------ *)

(* (Small-step beta examples moved to                              *)
(*  experiments/legacy_smallstep/Examples_smallstep.v.)              *)

(* ------------------------------------------------------------------ *)
(* 4. Polymorphic identity at type ∀α≤any. α →_free α                 *)
(*                                                                    *)
(*    Λ α ≤ any@free. λ x : α. x                                      *)
(*                                                                    *)
(* In LN, the inner λ uses bvar 0 (in the term-binder), the outer Λ  *)
(* uses bvar 0 (in the type-binder under a fresh ty-binder).         *)
(* ------------------------------------------------------------------ *)

Definition poly_id : term :=
  term_ty_lam any_at_free
    (term_lam (term_bvar 0) (type_bvar 0)).

Example poly_id_value : value poly_id.
Proof. unfold poly_id; constructor. Qed.

(* ------------------------------------------------------------------ *)
(* 5. Lifetime-polymorphic identity :  Λ ℓ. λ x : any@ℓ. x            *)
(* ------------------------------------------------------------------ *)

Definition lt_id : term :=
  term_lt_lam
    (term_lam (term_bvar 0) (type_ctor any_tag (lt_bvar 0) [])).

Example lt_id_value : value lt_id.
Proof. unfold lt_id; constructor. Qed.

(* ------------------------------------------------------------------ *)
(* 6. Multi-step : same as the step example, but in the closure.       *)
(* ------------------------------------------------------------------ *)

(* (Small-step multi-step example moved to                         *)
(*  experiments/legacy_smallstep/Examples_smallstep.v.)              *)

(* ================================================================== *)
(* PORTED FROM LEGACY DE BRUIJN ENCODING                              *)
(*                                                                    *)
(* Below we re-derive the examples from the legacy `Examples.v`       *)
(* under the locally-nameless encoding.  Free variables are atoms,    *)
(* binders are introduced by cofinite quantification:                 *)
(*   T_Lam picks a fresh `x ∉ L` and types the body opened with       *)
(*   `term_fvar x`.                                                   *)
(* For closed values we typically take `L := empty`.                  *)
(* ================================================================== *)

(* ================================================================== *)
(* 7. Generic identity at any free type T                             *)
(*                                                                    *)
(*   ⊢ (λ x:T. x) : T -{lt_free}-> T                                  *)
(* ================================================================== *)

Example id_typing :
  forall (T : type),
    no_local_ty T = true ->
    [] |-t term_lam (term_bvar 0) T : type_fun T lt_free T.
Proof.
  intros T HT.
  apply (T_Lam empty).
  - intros x _. simpl.
    apply T_Var. simpl. destruct (x == x); [reflexivity | contradiction].
  - cbn. apply LS_Free.
Qed.

(* ================================================================== *)
(* 8. Upcast a free function to a local one (T_Sub on the closure)   *)
(* ================================================================== *)

Example upcast_closure_lt :
  forall (T : type),
    no_local_ty T = true ->
    [] |-t term_lam (term_bvar 0) T : type_fun T lt_local T.
Proof.
  intros T HT.
  eapply T_Sub.
  - apply id_typing; exact HT.
  - apply SA_Fun; [apply SA_Refl | apply LS_Free | apply SA_Refl].
Qed.

(* ================================================================== *)
(* 9. Higher-order application                                        *)
(*                                                                    *)
(*    Γ = [bind_tm y A; bind_tm f (A -{l}-> B)]                       *)
(*    Γ ⊢ f y : B                                                    *)
(* ================================================================== *)

Example app_typing :
  forall (A B : type) (l : lifetime) (f y : atom),
    f <> y ->
    [bind_tm y A; bind_tm f (type_fun A l B)] |-t
        term_app (term_fvar f) (term_fvar y) : B.
Proof.
  intros A B l f y Hfy.
  eapply T_App.
  - apply T_Var. simpl.
    destruct (f == y); [contradiction|].
    destruct (f == f); [reflexivity | contradiction].
  - apply T_Var. simpl.
    destruct (y == y); [reflexivity | contradiction].
Qed.

(* ================================================================== *)
(* 10. Lifetime-polymorphic identity                                  *)
(*                                                                    *)
(*   ⊢ (Λℓ. λ x : any@ℓ. x) : ∀ℓ. any@ℓ -{ℓ}-> any@ℓ                *)
(* ================================================================== *)

Definition any_at_local : type := type_ctor any_tag lt_local [].

Definition lt_poly_id : term :=
  term_lt_lam
    (term_lam (term_bvar 0) (type_ctor any_tag (lt_bvar 0) [])).

Example lt_poly_id_value : value lt_poly_id.
Proof. unfold lt_poly_id; constructor. Qed.

Example lt_poly_id_typing :
  [] |-t lt_poly_id :
    type_lt_all
      (type_fun (type_ctor any_tag (lt_bvar 0) [])
                (lt_bvar 0)
                (type_ctor any_tag (lt_bvar 0) [])).
Proof.
  unfold lt_poly_id.
  apply (T_LtLam empty). intros a _. simpl.
  apply (T_Lam (singleton a)).
  - intros x Hx. simpl.
    apply T_Var. simpl. destruct (x == x); [reflexivity | contradiction].
  - cbn. apply LS_Free.
Qed.

(* ================================================================== *)
(* 11. Type-polymorphic identity (bounded)                            *)
(*                                                                    *)
(*   ⊢ (Λα <: any@local. λ x : α. x)                                  *)
(*       : ∀α <: any@local. α -{lt_free}-> α                          *)
(* ================================================================== *)

Definition ty_poly_id : term :=
  term_ty_lam any_at_local
    (term_lam (term_bvar 0) (type_bvar 0)).

Example ty_poly_id_value : value ty_poly_id.
Proof. unfold ty_poly_id; constructor. Qed.

Example ty_poly_id_typing :
  [] |-t ty_poly_id :
    type_ty_all any_at_local
      (type_fun (type_bvar 0) lt_free (type_bvar 0)).
Proof.
  unfold ty_poly_id.
  apply (T_TyLam empty). intros a _. simpl.
  apply (T_Lam (singleton a)).
  - intros x _. simpl.
    apply T_Var. simpl. destruct (x == x); [reflexivity | contradiction].
  - cbn. apply LS_Free.
Qed.

(* ================================================================== *)
(* 12. Paper repository data                                          *)
(* ================================================================== *)

Definition unit_tag       : ctor_tag := 10.
Definition file_tag       : ctor_tag := 11.
Definition connection_tag : ctor_tag := 12.
Definition repo_tag       : ctor_tag := 13.

Definition T_UnitT : type := type_ctor unit_tag       lt_free [].
Definition T_FileT (l : lifetime) : type := type_ctor file_tag       l [].
Definition T_ConnT (l : lifetime) : type := type_ctor connection_tag l [].
Definition T_RepoT (l : lifetime) : type := type_ctor repo_tag       l [].

Definition unit_v : term := term_ctor unit_tag lt_free [] [] [].

Lemma unit_v_value : value unit_v.
Proof. apply value_ctor. constructor. Qed.

#[export] Hint Resolve unit_v_value : core.

(* Repository[lf, lc](File@lf, Connection@lc) : Repository@(lf+lc).   *)
Definition repo_sig : binding :=
  bind_ctor repo_tag 2 0
    [ T_FileT (lt_bvar 1) ; T_ConnT (lt_bvar 0) ]
    (T_RepoT (lt_min (lt_bvar 1) (lt_bvar 0))).

Definition data_ctx : ctx :=
  [ repo_sig
  ; bind_ctor connection_tag 0 0 [] (T_ConnT lt_free)
  ; bind_ctor file_tag       0 0 [] (T_FileT lt_free)
  ; bind_ctor unit_tag       0 0 [] T_UnitT ].

Example paper_unit :
  data_ctx |-t term_ctor unit_tag lt_free [] [] [] : T_UnitT.
Proof.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
  constructor.
Qed.

Example paper_file :
  data_ctx |-t term_ctor file_tag lt_free [] [] [] : T_FileT lt_free.
Proof.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
  constructor.
Qed.

Example paper_connection :
  data_ctx |-t term_ctor connection_tag lt_free [] [] []
              : T_ConnT lt_free.
Proof.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
  constructor.
Qed.

(* ================================================================== *)
(* 13. Constructor instantiation: building a Repository with fresh     *)
(*     lifetime atoms for the two lt-binders.                          *)
(* ================================================================== *)

Example paper_repo_intro :
  forall (a b : atom) (xf xc : atom),
    a <> b -> xf <> xc ->
    let lts := [lt_fvar a; lt_fvar b] in
    let rho := List.map (inst_ctor_type lts [])
                [ T_FileT (lt_bvar 1) ; T_ConnT (lt_bvar 0) ] in
    let lr  := lt_of_ty_list rho in
    ( bind_tm xc (T_ConnT (lt_fvar b))
   :: bind_tm xf (T_FileT (lt_fvar a))
   :: bind_lt b lt_local
   :: bind_lt a lt_local
   :: data_ctx ) |-t
      term_ctor repo_tag lr lts [] [term_fvar xf; term_fvar xc]
      : T_RepoT (lt_min (lt_fvar a) (lt_fvar b)).
Proof.
  intros a b xf xc Hab Hxfc lts rho lr.
  eapply T_Ctor with (lts := lts) (Ts := []); try reflexivity.
  apply Forall2_cons; [| apply Forall2_cons; [| constructor]];
    apply T_Var; simpl;
    repeat match goal with
    | [ |- context [?x == ?y] ] => destruct (x == y); try (subst; congruence)
    end; try reflexivity.
Qed.

(* ================================================================== *)
(* 14. Cap-escape blocked (negative result, paper section)            *)
(* ================================================================== *)

Lemma cap_escape_blocked :
  forall (E : eff_tag) (Ts : list type),
    no_local_ty (type_ctor E lt_local Ts) = false.
Proof. intros; cbn; reflexivity. Qed.

(* ================================================================== *)
(* 15. Simple reduction examples — small-step variants moved to       *)
(*     experiments/legacy_smallstep/Examples_smallstep.v.             *)
(*     Equivalent CEK-machine reductions appear in section 21 below.  *)
(* ================================================================== *)

(* ================================================================== *)
(* 16. print_fn  : (File@local -free-> Unit -free-> Unit)              *)
(* ================================================================== *)

Definition print_fn : term :=
  term_lam
    (term_lam unit_v T_UnitT)
    (T_FileT lt_local).

Example print_fn_value : value print_fn.
Proof. unfold print_fn. constructor. Qed.

Example typed_print :
  data_ctx |-t print_fn
    : type_fun (T_FileT lt_local) lt_free
        (type_fun T_UnitT lt_free T_UnitT).
Proof.
  unfold print_fn.
  apply (T_Lam empty).
  - intros xf _. simpl.
    apply (T_Lam (singleton xf)).
    + intros xu _. simpl.
      eapply T_Ctor with (lts := []) (Ts := []); try reflexivity.
      constructor.
    + cbn. apply LS_Free.
  - cbn. apply LS_Free.
Qed.

(* ================================================================== *)
(* 17. compose_fn: Λl1.Λl2. λg λf λx. g (f x)                         *)
(* ================================================================== *)

Definition CA : type := type_ctor 100 lt_free [].
Definition CB : type := type_ctor 101 lt_free [].
Definition CC : type := type_ctor 102 lt_free [].

Definition compose_fn : term :=
  term_lt_lam (term_lt_lam
    (term_lam
      (term_lam
        (term_lam
          (term_app (term_bvar 2) (term_app (term_bvar 1) (term_bvar 0)))
          CA)
        (type_fun CA (lt_bvar 0) CB))
      (type_fun CB (lt_bvar 1) CC))).

Example compose_fn_value : value compose_fn.
Proof. unfold compose_fn. repeat constructor. Qed.

(* ================================================================== *)
(* 21. CEK machine reduction examples                                  *)
(*                                                                     *)
(* These mirror the small-step examples in section 15 but target the  *)
(* CEK abstract machine introduced in CEK.v.                           *)
(* ================================================================== *)

(* (λ:Unit. b0) Unit  ~~>c*  C_done (clos_ctor unit_tag ...)           *)
Example cek_red_identity_unit :
  C_ev (term_app (term_lam (term_bvar 0) T_UnitT) unit_v) [] [] 0
    ~~>c* C_done (clos_ctor unit_tag lt_free [] [] []).
Proof.
  unfold unit_v.
  (* push App                                                          *)
  eapply CM_step; [apply CS_App|].
  (* push Lam                                                          *)
  eapply CM_step; [apply CS_Lam|].
  (* pop KApp1 -> evaluate arg                                         *)
  eapply CM_step; [apply CS_KApp1|].
  (* push CtorNil for unit_v                                           *)
  eapply CM_step; [apply CS_CtorNil|].
  (* pop KApp2 of clos_lam: env-extend, step into body (term_bvar 0)   *)
  eapply CM_step; [apply CS_BetaLam|].
  (* lookup bvar 0 in env                                              *)
  eapply CM_step; [apply CS_BVar; reflexivity|].
  (* empty kont with a value: halt                                    *)
  eapply CM_step; [apply CS_Done|].
  apply CM_refl.
Qed.

(* (Λl. body) [l]  ~~>c*  C_ev (open_tm_wrt_lt l body) [] [] 0          *)
Example cek_red_lt_beta : forall body l,
  C_ev (term_lt_app (term_lt_lam body) l) [] [] 0
    ~~>c* C_ev (open_tm_wrt_lt l body) [] [] 0.
Proof.
  intros body l.
  eapply CM_step; [apply CS_LtApp|].
  eapply CM_step; [apply CS_LtLam|].
  eapply CM_step; [apply CS_BetaLt|].
  apply CM_refl.
Qed.

(* (Λα<:B. body) [T]  ~~>c*  C_ev (open_tm_wrt_ty T body) [] [] 0      *)
Example cek_red_ty_beta : forall B body T,
  C_ev (term_ty_app (term_ty_lam B body) T) [] [] 0
    ~~>c* C_ev (open_tm_wrt_ty T body) [] [] 0.
Proof.
  intros B body T.
  eapply CM_step; [apply CS_TyApp|].
  eapply CM_step; [apply CS_TyLam|].
  eapply CM_step; [apply CS_BetaTy|].
  apply CM_refl.
Qed.

(* match Unit with Unit() => yes_body | _ => no_body                    *)
(*   ~~>c*  C_ev yes_body [] [] 0                                       *)
(* (arity 0, lts 0 — yes_body has no binders to open).                 *)
Example cek_red_match_unit :
  forall yes_body no_body,
    C_ev (term_match unit_v unit_tag 0 yes_body no_body) [] [] 0
      ~~>c* C_ev yes_body [] [] 0.
Proof.
  intros yes_body no_body.
  unfold unit_v.
  eapply CM_step; [apply CS_Match|].
  eapply CM_step; [apply CS_CtorNil|].
  eapply CM_step.
  { apply CS_KMatchYes. reflexivity. }
  cbn. apply CM_refl.
Qed.

(* identity-application as a single CEK trace from initial_config.     *)
Example cek_initial_identity :
  cmulti
    (initial_config (term_app (term_lam (term_bvar 0) T_UnitT) unit_v))
    (C_done (clos_ctor unit_tag lt_free [] [] [])).
Proof. apply cek_red_identity_unit. Qed.

(* ================================================================== *)
(* 22. State<Nat> effect — handler example with put-then-get          *)
(*                                                                    *)
(* The standard "state-passing" handler implementation:               *)
(*   · the handle's result type is `Nat -free-> Nat` (awaits initial *)
(*     state)                                                         *)
(*   · each operation produces a `Nat -> Nat` whose argument is the   *)
(*     current state                                                  *)
(*   · `Get`     resumes with `s`, then forwards `s`                  *)
(*   · `Put n`   resumes with `n`, then forwards `n`                  *)
(*                                                                    *)
(* The whole program is `(handle State<Nat> {...} body) @ zero_v`.    *)
(*                                                                    *)
(* The bvar discipline matches the CEK runtime ordering:              *)
(*   inside op_body (before the λs):  $$0 = arg, $$1 = k              *)
(*   inside the λs:                    $$0 = s, $$1 = arg, $$2 = k    *)
(*   inside Put-yes (arity 1, payload n):                             *)
(*     $$0 = n, $$1 = s, $$2 = arg, $$3 = k                            *)
(* ================================================================== *)

Import CoreNotation.

Section State_Example.

(* ------------------------------------------------------------------ *)
(* Tags, types, values                                                 *)
(* ------------------------------------------------------------------ *)

Definition State_tag : eff_tag  := 103.
Definition cmd_tag   : ctor_tag := 60.
Definition get_tag   : ctor_tag := 50.
Definition put_tag   : ctor_tag := 51.
Definition nat_tag   : ctor_tag := 70.
Definition zero_tag  : ctor_tag := 71.
Definition suc_tag   : ctor_tag := 72.

Definition T_NatT : type := type_ctor nat_tag `Lf [].
Definition T_CmdT : type := type_ctor cmd_tag `Lf [].

Definition zero_v : term := term_ctor zero_tag `Lf [] [] [].
Definition one_v  : term := term_ctor suc_tag  (lt_of_ty_list [T_NatT]) [] [] [zero_v].
Definition get_v  : term := term_ctor get_tag  `Lf [] [] [].
Definition put_v (n : term) : term :=
  term_ctor put_tag (lt_of_ty_list [T_NatT]) [] [] [n].

Lemma zero_v_value : value zero_v.
Proof. apply value_ctor. constructor. Qed.

Lemma one_v_value : value one_v.
Proof. apply value_ctor. repeat constructor. Qed.

Lemma get_v_value : value get_v.
Proof. apply value_ctor. constructor. Qed.

Lemma put_one_v_value : value (put_v one_v).
Proof. apply value_ctor. repeat constructor. Qed.

#[local] Hint Resolve zero_v_value one_v_value
                       get_v_value put_one_v_value : core.

(* CEK runtime values (closures) of the same constants. *)
Definition zero_clos    : rvalue := clos_ctor zero_tag `Lf [] [] [].
Definition one_clos     : rvalue :=
  clos_ctor suc_tag  (lt_of_ty_list [T_NatT]) [] [] [zero_clos].
Definition get_clos     : rvalue := clos_ctor get_tag  `Lf [] [] [].
Definition put_one_clos : rvalue :=
  clos_ctor put_tag  (lt_of_ty_list [T_NatT]) [] [] [one_clos].

(* ------------------------------------------------------------------ *)
(* State signature                                                     *)
(*                                                                    *)
(*   State : (a : type)                                               *)
(*     op  : Cmd  ->  a                                               *)
(*                                                                    *)
(* n_α = 1 (the state cell type a), n_β = 0 (op has no return-type    *)
(* parameter).                                                        *)
(* ------------------------------------------------------------------ *)

Definition state_sig : binding :=
  bind_eff State_tag 1 0 T_CmdT (type_bvar 0).

Definition cmd_ctx : ctx :=
  [ bind_ctor put_tag 0 0 [T_NatT] T_CmdT
  ; bind_ctor get_tag 0 0 []        T_CmdT ].

Definition nat_ctx : ctx :=
  [ bind_ctor suc_tag  0 0 [T_NatT] T_NatT
  ; bind_ctor zero_tag 0 0 []        T_NatT ].

Definition state_ctx : ctx := state_sig :: cmd_ctx ++ nat_ctx.

(* ------------------------------------------------------------------ *)
(* The state-passing op-body                                           *)
(*                                                                    *)
(*   λ s : Nat .                                                      *)
(*     match arg with                                                 *)
(*     | Get     => k @ s @ s                                         *)
(*     | _       =>                                                   *)
(*       match arg with                                               *)
(*       | Put(n) => k @ n @ n                                        *)
(*       | _      => s          (* unreachable on well-typed inputs *)*)
(* ------------------------------------------------------------------ *)

Definition state_op_body : term :=
  λ: T_NatT \\
    term_match ($$ 1) get_tag 0
      (* yes_get (arity 0): k @ s @ s *)
      ($$ 2 @· $$ 0 @· $$ 0)
      (term_match ($$ 1) put_tag 1
         (* yes_put (arity 1, n at $$0): k @ n @ n *)
         ($$ 3 @· $$ 0 @· $$ 0)
         ($$ 0)).

(* ------------------------------------------------------------------ *)
(* The "put one then get" program                                     *)
(*                                                                    *)
(*    handle State<Nat> { state_op_body } in                          *)
(*      let _  = perform cap (put one)    in                          *)
(*      let n  = perform cap get          in                          *)
(*      λ s : Nat . n                                                 *)
(*    @ zero_v                                                        *)
(* ------------------------------------------------------------------ *)

Definition state_putget_program : term :=
  (term_handle State_tag [T_NatT] state_op_body
     (* cap = $$0 *)
     (let: T_NatT <- term_perform ($$ 0) [] (put_v one_v) in
      (* now $$0 = n1 (put result), $$1 = cap *)
      let: T_NatT <- term_perform ($$ 1) [] get_v in
      (* now $$0 = n2 (get result), $$1 = n1, $$2 = cap *)
      λ: T_NatT \\ ($$ 1)))
  @· zero_v.

(* ------------------------------------------------------------------ *)
(* TYPING                                                              *)
(*                                                                    *)
(* With the new `T_Ctor` / `T_Match` rules (see Typing.v), the        *)
(* schema's *result* type is what `T_Ctor` produces — so several      *)
(* value-ctors (a sum) can share a declared type.  The State<Nat>    *)
(* example exploits this: `Get` and `Put _` both have type `Cmd`.    *)
(*                                                                    *)
(* `state_putget_program` is typed as `T_NatT` under `state_ctx`.    *)
(* The handle's result type (`T_R`) is `T_NatT -{lt_local}-> T_NatT`, *)
(* and the @· zero_v reduces it to `T_NatT`.                          *)
(* ------------------------------------------------------------------ *)

(* Result type produced by the handle: a function awaiting initial state. *)
Local Definition T_R_st : type := type_fun T_NatT lt_local T_NatT.

(* Type of the `cap : State<Nat>` capability variable. *)
Local Definition cap_ty : type := type_ctor State_tag lt_local [T_NatT].

(* Type of the resumption `k : Nat -lt_local-> T_R`. *)
Local Definition k_ty : type := type_fun T_NatT lt_local T_R_st.

Local Ltac solve_var :=
  apply T_Var; cbn;
  repeat (first
    [ reflexivity
    | match goal with
      | [ |- context [?x == ?y] ] =>
          destruct (x == y); subst; try congruence
      end ]).

(* yes-branch for `Get`: `k @· s @· s` produces `T_NatT`. *)
Local Lemma typed_yes_get : forall Γ k_x s_x,
  k_x <> s_x ->
  ctx_lookup_tm Γ k_x = Some k_ty ->
  ctx_lookup_tm Γ s_x = Some T_NatT ->
  Γ |-t (term_fvar k_x @· term_fvar s_x @· term_fvar s_x) : T_NatT.
Proof.
  intros Γ k_x s_x Hne Hk Hs.
  eapply T_App with (A := T_NatT) (l := lt_local).
  - eapply T_App with (A := T_NatT) (l := lt_local).
    + apply T_Var; assumption.
    + apply T_Var; assumption.
  - apply T_Var; assumption.
Qed.

(* yes-branch for `Put(n)` (with payload `n` bound at $$0):           *)
(*   `k @· n @· n` produces `T_NatT`.                                  *)
Local Lemma typed_yes_put : forall Γ k_x n_x,
  k_x <> n_x ->
  ctx_lookup_tm Γ k_x = Some k_ty ->
  ctx_lookup_tm Γ n_x = Some T_NatT ->
  Γ |-t (term_fvar k_x @· term_fvar n_x @· term_fvar n_x) : T_NatT.
Proof.
  intros Γ k_x n_x Hne Hk Hn.
  eapply T_App with (A := T_NatT) (l := lt_local).
  - eapply T_App with (A := T_NatT) (l := lt_local).
    + apply T_Var; assumption.
    + apply T_Var; assumption.
  - apply T_Var; assumption.
Qed.

(* `zero_v : T_NatT` in any context whose ctor lookup yields the     *)
(* `zero_tag` schema.  Used as the argument to the handle.           *)
Local Lemma typed_zero_v : forall Γ,
  ctx_lookup_ctor Γ zero_tag = Some (0, 0, [], T_NatT) ->
  ctx_lookup_eff  Γ zero_tag = None ->
  Γ |-t zero_v : T_NatT.
Proof.
  intros Γ Hc He. unfold zero_v.
  eapply T_Ctor with (lts := []) (Ts := []) (rho_fields := []) (l := lt_free)
                     (K_res := nat_tag) (lr_schema := lt_free) (Ts_res_schema := []).
  - cbn. exact Hc.
  - exact He.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - constructor.
  - reflexivity.
Qed.

(* `one_v : T_NatT`. *)
Local Lemma typed_one_v : forall Γ,
  ctx_lookup_ctor Γ suc_tag  = Some (0, 0, [T_NatT], T_NatT) ->
  ctx_lookup_eff  Γ suc_tag  = None ->
  ctx_lookup_ctor Γ zero_tag = Some (0, 0, [], T_NatT) ->
  ctx_lookup_eff  Γ zero_tag = None ->
  Γ |-t one_v : T_NatT.
Proof.
  intros Γ Hcs Hes Hcz Hez. unfold one_v.
  eapply T_Ctor with (lts := []) (Ts := []) (rho_fields := [T_NatT])
                     (K_res := nat_tag) (lr_schema := lt_free) (Ts_res_schema := []).
  - exact Hcs.
  - exact Hes.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - constructor; [| constructor]. apply typed_zero_v; assumption.
  - reflexivity.
Qed.

(* `put_v one_v : T_CmdT` (sum constructor: shares declared head Cmd). *)
Local Lemma typed_put_one_v : forall Γ,
  ctx_lookup_ctor Γ put_tag  = Some (0, 0, [T_NatT], T_CmdT) ->
  ctx_lookup_eff  Γ put_tag  = None ->
  ctx_lookup_ctor Γ suc_tag  = Some (0, 0, [T_NatT], T_NatT) ->
  ctx_lookup_eff  Γ suc_tag  = None ->
  ctx_lookup_ctor Γ zero_tag = Some (0, 0, [], T_NatT) ->
  ctx_lookup_eff  Γ zero_tag = None ->
  Γ |-t put_v one_v : T_CmdT.
Proof.
  intros Γ Hcp Hep Hcs Hes Hcz Hez. unfold put_v.
  eapply T_Ctor with (lts := []) (Ts := []) (rho_fields := [T_NatT])
                     (K_res := cmd_tag) (lr_schema := lt_free) (Ts_res_schema := []).
  - exact Hcp.
  - exact Hep.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - constructor; [| constructor]. apply typed_one_v; assumption.
  - reflexivity.
Qed.

(* `get_v : T_CmdT`. *)
Local Lemma typed_get_v : forall Γ,
  ctx_lookup_ctor Γ get_tag  = Some (0, 0, [], T_CmdT) ->
  ctx_lookup_eff  Γ get_tag  = None ->
  Γ |-t get_v : T_CmdT.
Proof.
  intros Γ Hcg Heg. unfold get_v.
  eapply T_Ctor with (lts := []) (Ts := []) (rho_fields := []) (l := lt_free)
                     (K_res := cmd_tag) (lr_schema := lt_free) (Ts_res_schema := []).
  - exact Hcg.
  - exact Heg.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - constructor.
  - reflexivity.
Qed.

(* The op_body, after T_Handle has opened its outer 2 binders with    *)
(* fresh atoms `arg_x` (innermost = bvar 0) and `k_x` (= bvar 1).     *)
(* This is the body that needs to be typed at `T_R_st`.               *)
Local Definition op_body_open (arg_x k_x : atom) : term :=
  λ: T_NatT \\
    term_match (term_fvar arg_x) get_tag 0
      (term_fvar k_x @· $$ 0 @· $$ 0)
      (term_match (term_fvar arg_x) put_tag 1
         (term_fvar k_x @· $$ 0 @· $$ 0)
         ($$ 0)).

Lemma op_body_open_eq : forall arg_x k_x,
  open_tm_wrt_tm (term_fvar k_x)
    (open_tm_wrt_tm (term_fvar arg_x) state_op_body)
  = op_body_open arg_x k_x.
Proof. intros. cbv. reflexivity. Qed.

(* The op_body inhabits T_R = T_NatT -{lt_local}-> T_NatT under the   *)
(* extended environment from T_Handle.                                *)
Local Lemma typed_op_body : forall arg_x k_x,
  arg_x <> k_x ->
  (bind_tm arg_x T_CmdT
    :: bind_tm k_x   k_ty
    :: state_ctx)
  |-t op_body_open arg_x k_x : T_R_st.
Proof.
  intros arg_x k_x Hne. unfold op_body_open, T_R_st, k_ty.
  pose (Γ0 := bind_tm arg_x T_CmdT
              :: bind_tm k_x (type_fun T_NatT lt_local T_R_st)
              :: state_ctx).
  (* T_Lam introduces s_x : T_NatT. *)
  apply (T_Lam (singleton arg_x `union` singleton k_x)).
  - intros s_x Hs_fr.
    assert (s_neq_arg : s_x <> arg_x) by fsetdec.
    assert (s_neq_k   : s_x <> k_x)   by fsetdec.
    cbn [open_tm_wrt_tm open_tm_wrt_tm_rec].
    (* Outer T_Match on Get. *)
    eapply (T_Match (singleton arg_x `union` singleton k_x `union` singleton s_x))
      with (n_lt := 0) (n_ty := 0)
           (sigma_fields := [])
           (K_res := cmd_tag) (lr_schema := lt_free) (Ts_res_schema := [])
           (Ts := []) (Delta := lt_free) (Ts_res_inst := [])
           (eta := T_NatT) (elim_result := T_NatT).
    + discriminate.
    + cbn. reflexivity.
    + cbn. reflexivity.
    + reflexivity.
    + (* scrut: arg_x : type_ctor cmd_tag lt_free [] = T_CmdT *)
      solve_var.
    + reflexivity.
    + (* yes-Get branch (arity 0, n_lt 0) *)
      intros lt_xs tm_xs Hlts Htms _ _ _ _.
      apply length_zero_iff_nil in Hlts. apply length_zero_iff_nil in Htms.
      subst lt_xs tm_xs. cbn.
      split; [| reflexivity].
      apply typed_yes_get; auto; cbn;
        repeat match goal with
        | [ |- context [?x == ?y] ] =>
            destruct (x == y); subst; try congruence
        end; try reflexivity.
    + (* no-branch: inner match on Put *)
      eapply (T_Match (singleton arg_x `union` singleton k_x `union` singleton s_x))
        with (n_lt := 0) (n_ty := 0)
             (sigma_fields := [T_NatT])
             (K_res := cmd_tag) (lr_schema := lt_free) (Ts_res_schema := [])
             (Ts := []) (Delta := lt_free) (Ts_res_inst := [])
             (eta := T_NatT) (elim_result := T_NatT).
      * discriminate.
      * cbn. reflexivity.
      * cbn. reflexivity.
      * reflexivity.
      * solve_var.
      * reflexivity.
      * (* yes-Put branch (arity 1, payload n_x : T_NatT) *)
        intros lt_xs tm_xs Hlts Htms Hnod1 Hnod2 HfL HtL.
        apply length_zero_iff_nil in Hlts. subst lt_xs.
        destruct tm_xs as [| n_x [| ? ?]]; try discriminate Htms.
        cbn.
        assert (Hn_fr : n_x `notin`
                  (singleton arg_x `union` singleton k_x
                                  `union` singleton s_x))
          by (apply HtL; simpl; auto).
        assert (n_neq_arg : n_x <> arg_x) by fsetdec.
        assert (n_neq_k   : n_x <> k_x)   by fsetdec.
        assert (n_neq_s   : n_x <> s_x)   by fsetdec.
        cbn [open_tm_wrt_tms open_tm_wrt_tm open_tm_wrt_tm_rec
             open_tm_wrt_lt_list].
        split; [| reflexivity].
        apply typed_yes_put; auto; cbn;
          repeat match goal with
          | [ |- context [?x == ?y] ] =>
              destruct (x == y); subst; try congruence
          end; try reflexivity.
      * (* no-Put branch: $$ 0 = s_x : T_NatT *)
        solve_var.
  - (* capture_lt of the body <: lt_local *)
    apply LS_Local.
Qed.

(* The handle body opened with cap_x has type T_R_st. *)
Local Definition body_open (cap_x : atom) : term :=
  (λ: T_NatT \\
     (λ: T_NatT \\ λ: T_NatT \\ ($$ 1)) @· term_perform (term_fvar cap_x) [] get_v)
   @· term_perform (term_fvar cap_x) [] (put_v one_v).

Lemma body_open_eq : forall cap_x,
  open_tm_wrt_tm (term_fvar cap_x)
    (let: T_NatT <- term_perform ($$ 0) [] (put_v one_v) in
     let: T_NatT <- term_perform ($$ 1) [] get_v in
     λ: T_NatT \\ ($$ 1))
  = body_open cap_x.
Proof. intros. cbv. reflexivity. Qed.

Local Lemma typed_body : forall cap_x,
  (bind_tm cap_x cap_ty :: state_ctx) |-t body_open cap_x : T_R_st.
Proof.
  intros cap_x. unfold body_open, T_R_st, cap_ty.
  (* Type: ((λ:T_NatT. (λ:T_NatT. λ:T_NatT. $$1) @· perform cap [] get_v)
              @· perform cap [] (put_v one_v))                            *)
  eapply T_App with (A := T_NatT) (l := lt_local).
  - (* The outer λ: takes the put-result, returns T_R_st. *)
    apply (T_Lam (singleton cap_x)).
    + intros put_x Hput_fr.
      assert (Hpc : put_x <> cap_x) by fsetdec.
      cbn [open_tm_wrt_tm open_tm_wrt_tm_rec].
      eapply T_App with (A := T_NatT) (l := lt_local).
      * (* λ:T_NatT. λ:T_NatT. $$1 — applied to get_result, returns
           λ: T_NatT \\ get_x. *)
        apply (T_Lam (singleton cap_x `union` singleton put_x)).
        -- intros get_x Hget_fr.
           assert (Hgc : get_x <> cap_x) by fsetdec.
           assert (Hgp : get_x <> put_x) by fsetdec.
           cbn [open_tm_wrt_tm open_tm_wrt_tm_rec].
           (* Goal: ... |-t λ: T_NatT \\ get_x : T_NatT -{lt_local}-> T_NatT. *)
           apply (T_Lam (singleton cap_x `union` singleton put_x
                                       `union` singleton get_x)).
           ++ intros s_x Hs_fr.
              assert (Hsg : s_x <> get_x) by fsetdec.
              assert (Hsp : s_x <> put_x) by fsetdec.
              assert (Hsc : s_x <> cap_x) by fsetdec.
              cbn [open_tm_wrt_tm open_tm_wrt_tm_rec].
              solve_var.
           ++ (* capture <: lt_local: trivially via LS_Local. *)
              apply LS_Local.
        -- (* capture of middle λ: trivial via LS_Local. *)
           apply LS_Local.
      * (* perform cap [] get_v : T_NatT *)
        eapply T_Perform with (E_tag := State_tag) (Δ := lt_local)
                              (Ts := [T_NatT]) (Ss := [])
                              (n_α := 1) (n_β := 0)
                              (sig := T_CmdT) (ret := type_bvar 0).
        -- solve_var.
        -- cbn. reflexivity.
        -- reflexivity.
        -- reflexivity.
        -- cbn. reflexivity.
        -- cbn. reflexivity.
        -- (* get_v : T_CmdT *)
           apply typed_get_v; cbn; reflexivity.
    + (* capture of put_x's lam <: lt_local: trivial via LS_Local. *)
      apply LS_Local.
  - (* perform cap [] (put_v one_v) : T_NatT *)
    eapply T_Perform with (E_tag := State_tag) (Δ := lt_local)
                          (Ts := [T_NatT]) (Ss := [])
                          (n_α := 1) (n_β := 0)
                          (sig := T_CmdT) (ret := type_bvar 0).
    + solve_var.
    + cbn. reflexivity.
    + reflexivity.
    + reflexivity.
    + cbn. reflexivity.
    + cbn. reflexivity.
    + apply typed_put_one_v; cbn; reflexivity.
Qed.

Theorem typed_state_putget :
  state_ctx |-t state_putget_program : T_NatT.
Proof.
  unfold state_putget_program.
  eapply T_App with (A := T_NatT) (l := lt_local).
  - eapply (T_Handle empty)
      with (n_α := 1) (n_β := 0)
           (sig := T_CmdT) (ret := type_bvar 0)
           (T_R := T_R_st).
    + cbn. reflexivity.
    + reflexivity.
    + cbn. reflexivity.
    + cbn. reflexivity.
    + intros β_xs arg_x k_x Hl HND Hne HβL HaL HkL.
      apply length_zero_iff_nil in Hl. subst β_xs.
      cbn [List.map open_ty_wrt_ty_list open_tm_wrt_ty_list].
      rewrite op_body_open_eq.
      apply typed_op_body. exact Hne.
    + intros cap_x _.
      rewrite body_open_eq.
      apply typed_body.
  - apply typed_zero_v; cbn; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* EVALUATION                                                          *)
(*                                                                    *)
(* The trace is mechanical but long (~60 steps) because every nested *)
(* let, perform, ctor and resume produces its own kont frame.         *)
(* ------------------------------------------------------------------ *)

(* Local abbreviations for readability of intermediate machine states. *)

Definition cap_clos : rvalue :=
  clos_cap State_tag 0 [T_NatT] state_op_body [].

Definition lam1_clos : rvalue :=
  clos_lam
    (term_app
       (term_lam (term_lam ($$ 1) T_NatT) T_NatT)
       (term_perform ($$ 1) [] get_v))
    [cap_clos]
    T_NatT.

Definition lam2_clos : rvalue :=
  clos_lam (term_lam ($$ 1) T_NatT) [one_clos; cap_clos] T_NatT.

Definition Kr1 : kont :=
  [KApp2 lam1_clos;
   KHandle 0 State_tag [T_NatT] state_op_body []].

Definition resume1 : rvalue := clos_resume Kr1.

Definition Kr2 : kont :=
  [KApp2 lam2_clos;
   KHandle 0 State_tag [T_NatT] state_op_body []].

Definition resume2 : rvalue := clos_resume Kr2.

Definition lam3_clos : rvalue :=
  clos_lam ($$ 1) [one_clos; one_clos; cap_clos] T_NatT.

(* Tactics for the CEK trace. *)
Local Ltac cek_step rule := eapply CM_step; [apply rule|].
Local Ltac cek_bvar :=
  eapply CM_step; [eapply CS_BVar; cbn; reflexivity|].

Theorem cek_red_state_putget :
  C_ev state_putget_program [] [] 0 ~~>c* C_done one_clos.
Proof.
  unfold state_putget_program.
  (*  1. App       *) cek_step CS_App.
  (*  2. Handle    *) cek_step CS_Handle.
  (*  3. App       *) cek_step CS_App.
  (*  4. Lam       *) cek_step CS_Lam.
  (*  5. KApp1     *) cek_step CS_KApp1.
  (*  6. Perform   *) cek_step CS_Perform.
  (*  7. BVar 0    *) cek_bvar.
  (*  8. KPerformR *) cek_step CS_KPerformR.
  (*  9. CtorCons  *) cek_step CS_CtorCons.
  (* 10. CtorCons  *) cek_step CS_CtorCons.
  (* 11. CtorNil   *) cek_step CS_CtorNil.
  (* 12. KCtorDone *) cek_step CS_KCtorDone.
  (* 13. KCtorDone *) cek_step CS_KCtorDone.
  (* 14. KPerformFire (m=0): split_at_handler picks KHandle 0. *)
  eapply CM_step.
  { eapply (CS_KPerformFire State_tag 0 [T_NatT] state_op_body []
                            [] put_one_clos
                            _ 1
                            [KApp2 lam1_clos] State_tag [T_NatT]
                            state_op_body []
                            [KApp1 zero_v []]).
    cbn. reflexivity. }
  cbn.
  (* 15. Lam       *) cek_step CS_Lam.
  (* 16. KApp1     *) cek_step CS_KApp1.
  (* 17. CtorNil   *) cek_step CS_CtorNil.
  (* 18. BetaLam   *) cek_step CS_BetaLam.
  (* 19. Match     *) cek_step CS_Match.
  (* 20. BVar 1    *) cek_bvar.
  (* 21. KMatchNo  *) eapply CM_step. { eapply CS_KMatchNo. discriminate. }
  (* 22. Match     *) cek_step CS_Match.
  (* 23. BVar 1    *) cek_bvar.
  (* 24. KMatchYes *) eapply CM_step. { apply CS_KMatchYes. cbn. reflexivity. }
  cbn.
  (* 25. App       *) cek_step CS_App.
  (* 26. App       *) cek_step CS_App.
  (* 27. BVar 3    *) cek_bvar.
  (* 28. KApp1     *) cek_step CS_KApp1.
  (* 29. BVar 0    *) cek_bvar.
  (* 30. BetaResume*) cek_step CS_BetaResume.
  (* 31. BetaLam   *) cek_step CS_BetaLam.
  (* 32. App       *) cek_step CS_App.
  (* 33. Lam       *) cek_step CS_Lam.
  (* 34. KApp1     *) cek_step CS_KApp1.
  (* 35. Perform   *) cek_step CS_Perform.
  (* 36. BVar 1    *) cek_bvar.
  (* 37. KPerformR *) cek_step CS_KPerformR.
  (* 38. CtorNil   *) cek_step CS_CtorNil.
  (* 39. KPerformFire (m=0, second time). *)
  eapply CM_step.
  { eapply (CS_KPerformFire State_tag 0 [T_NatT] state_op_body []
                            [] get_clos
                            _ 1
                            [KApp2 lam2_clos] State_tag [T_NatT]
                            state_op_body []
                            [KApp1 ($$ 0)
                               [one_clos; zero_clos; put_one_clos; resume1]]).
    cbn. reflexivity. }
  cbn.
  (* 40. Lam       *) cek_step CS_Lam.
  (* 41. KApp1     *) cek_step CS_KApp1.
  (* 42. BVar 0    *) cek_bvar.
  (* 43. BetaLam   *) cek_step CS_BetaLam.
  (* 44. Match     *) cek_step CS_Match.
  (* 45. BVar 1    *) cek_bvar.
  (* 46. KMatchYes *) eapply CM_step. { apply CS_KMatchYes. cbn. reflexivity. }
  cbn.
  (* 47. App       *) cek_step CS_App.
  (* 48. App       *) cek_step CS_App.
  (* 49. BVar 2    *) cek_bvar.
  (* 50. KApp1     *) cek_step CS_KApp1.
  (* 51. BVar 0    *) cek_bvar.
  (* 52. BetaResume*) cek_step CS_BetaResume.
  (* 53. BetaLam   *) cek_step CS_BetaLam.
  (* 54. Lam       *) cek_step CS_Lam.
  (* 55. KHandleReturn *) cek_step CS_KHandleReturn.
  (* 56. KApp1     *) cek_step CS_KApp1.
  (* 57. BVar 0    *) cek_bvar.
  (* 58. BetaLam   *) cek_step CS_BetaLam.
  (* 59. BVar 1    *) cek_bvar.
  (* 60. Done      *) cek_step CS_Done.
  apply CM_refl.
Qed.

Theorem cek_initial_state_putget :
  cmulti (initial_config state_putget_program) (C_done one_clos).
Proof. apply cek_red_state_putget. Qed.

End State_Example.
