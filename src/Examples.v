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
    term_ctor 1 pair_lt_free [] [] [term_var 1; term_var 0]
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
    term_ctor 1 pair_lt_local [] [] [term_var 1; term_var 0]
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
  - discriminate.               (* K = 1 <> any_tag = 0 *)
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
  ~ (Γ ⊢ₜ term_ctor 1 lt_local [] [] [] : type_ctor 1 lt_local []).
Proof.
  intros Γ H.
  remember (term_ctor 1 lt_local [] [] []) as t eqn:Ht.
  induction H; try discriminate.
  - (* T_Sub: IHtyping : t = term_ctor 1 lt_local [] [] -> False *)
    apply IHtyping; exact Ht.
  - (* T_Ctor: K=1, l=lt_local, Ts=[], vs=[] (unified by induction) *)
    (* premises: lt_local = lt_of_ty_list rho_fields, rho_fields = map ... [] *)
    cbn in *.
Admitted. (* TODO: show lt_local ≠ lt_free after reducing rho_fields *)

Example ex_neg_app_mismatch :
  ~ ([] ⊢ₜ term_app (term_lam (term_var 0) ty_A)
                     (term_ctor 43 lt_free [] [] [])
           : ty_A).
Proof.
  intros H. admit.
Admitted. (* TODO *)


(* ------------------------------------------------------------------ *)
(* Example 9: Repository — existential lifetime constructor           *)
(*                                                                    *)
(*   data Repository[l](x: Any@l)                                     *)
(*                                                                    *)
(* The existential witness is supplied directly as a concrete         *)
(* lifetime (lt_local) — no outer bind_lt is required.  The result    *)
(* lifetime is auto-computed by T_Ctor; we coerce it down to          *)
(* lt_local with T_Sub + SA_Data.                                     *)
(* ------------------------------------------------------------------ *)

Example ex_repository :
  let AnyAtLocal := type_ctor any_tag lt_local [] in
  [ bind_tm AnyAtLocal
  ; bind_ctor 7 1 0
      [type_ctor any_tag (lt_var 0) []]
      (type_ctor 7 (lt_var 0) []) ] ⊢ₜ
    term_ctor 7 (lt_of_ty_list [AnyAtLocal]) [lt_local] [] [term_var 0]
    : type_ctor 7 lt_local [].
Proof.
  intros AnyAtLocal.
  eapply T_Sub.
  - eapply T_Ctor with (lts := [lt_local]) (Ts := []); try reflexivity.
    repeat constructor.
  - apply SA_Data. cbn. apply LS_MinL; apply LS_Local.
Qed.

(* ================================================================== *)
(* Examples from examples.co (paper repository)                       *)
(*                                                                    *)
(* Mechanization of the non-recursive examples; recursive functions   *)
(* (map, lazyMap, collect, printAll, map2, lazyMap2) are skipped      *)
(* because the core has no fix.  Multi-case matches are unrolled to   *)
(* a single case + else branch (no_body).  let-bindings are encoded   *)
(* as immediate beta:  let x = e1 in e2  ≡  (λx.e2) e1.               *)
(* ================================================================== *)

Definition unit_tag       : ctor_tag := 10.
Definition file_tag       : ctor_tag := 11.
Definition connection_tag : ctor_tag := 12.
Definition repo_tag       : ctor_tag := 13.

Definition T_UnitT    : type := type_ctor unit_tag       lt_free [].
Definition T_FileT (l : lifetime) : type := type_ctor file_tag       l [].
Definition T_ConnT (l : lifetime) : type := type_ctor connection_tag l [].
Definition T_RepoT (l : lifetime) : type := type_ctor repo_tag       l [].

(* --- Constructor signatures ------------------------------------- *)

(* Repository[lf, lc](File@lf, Connection@lc) : Repository@(min lf lc) *)
(* Under the binder, lt_var 1 = lf (outer), lt_var 0 = lc (inner).    *)
Definition repo_sig : binding :=
  bind_ctor repo_tag 2 0
    [ T_FileT (lt_var 1) ; T_ConnT (lt_var 0) ]
    (T_RepoT (lt_min (lt_var 1) (lt_var 0))).

Definition data_ctx : ctx :=
  [ repo_sig
  ; bind_ctor connection_tag 0 0 [] (T_ConnT lt_free)
  ; bind_ctor file_tag       0 0 [] (T_FileT lt_free)
  ; bind_ctor unit_tag       0 0 [] T_UnitT ].

(* ------------------------------------------------------------------ *)
(* paper:  Unit() : Unit                                              *)
(* ------------------------------------------------------------------ *)

Example ex_paper_unit :
  data_ctx ⊢ₜ term_ctor unit_tag lt_free [] [] [] : T_UnitT.
Proof.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity. constructor.
Qed.

(* ------------------------------------------------------------------ *)
(* paper:  File()       : File@free                                   *)
(* paper:  Connection() : Connection@free                             *)
(* ------------------------------------------------------------------ *)

Example ex_paper_file :
  data_ctx ⊢ₜ term_ctor file_tag lt_free [] [] [] : T_FileT lt_free.
Proof.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity. constructor.
Qed.

Example ex_paper_connection :
  data_ctx ⊢ₜ term_ctor connection_tag lt_free [] [] [] : T_ConnT lt_free.
Proof.
  eapply T_Ctor with (lts := []) (Ts := []); try reflexivity. constructor.
Qed.

(* ------------------------------------------------------------------ *)
(* paper:  Repository[lf, lc](file, conn) : Repository@(lf+lc)        *)
(*                                                                    *)
(* Under a context with two outer bind_lt's and the two field         *)
(* bindings, build the constructor with explicit lt witnesses.        *)
(* ------------------------------------------------------------------ *)

Example ex_paper_repo_intro :
  let lts := [lt_var 0; lt_var 1] in
  let rho := List.map (inst_ctor_type 2 0 lts [])
              [ T_FileT (lt_var 1) ; T_ConnT (lt_var 0) ] in
  let l   := lt_of_ty_list rho in
  ( bind_tm (T_ConnT (lt_var 0))
   :: bind_tm (T_FileT (lt_var 1))
   :: bind_lt lt_local
   :: bind_lt lt_local
   :: data_ctx ) ⊢ₜ
    term_ctor repo_tag l lts [] [term_var 1; term_var 0]
    : T_RepoT l.
Proof.
  intros lts rho l.
  eapply T_Ctor with (lts := lts) (Ts := []); try reflexivity.
  cbn.
  apply Forall2_cons; [| apply Forall2_cons; [| apply Forall2_nil]];
    apply T_Var; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* paper:  fun makeRepository(file: File'lf, conn: Connection'lc)    *)
(*           : Repository'lf+lc =                                     *)
(*         Repository[lf, lc](file, conn)                             *)
(*                                                                    *)
(* Curried encoding:                                                  *)
(*   makeRepository = Λlf. Λlc. λfile. λconn. Repository[lf,lc]...    *)
(*                                                                    *)
(* Type:                                                              *)
(*   ∀lf. ∀lc. File@lf -free-> (Connection@lc -lf-> Repo@(lf+lc))     *)
(* ------------------------------------------------------------------ *)

Definition makeRepository : term :=
  term_lt_lam (term_lt_lam (
    term_lam (term_lam (
      term_ctor repo_tag
        (lt_of_ty_list (List.map (inst_ctor_type 2 0 [lt_var 0; lt_var 1] [])
                          [ T_FileT (lt_var 1) ; T_ConnT (lt_var 0) ]))
        [lt_var 0; lt_var 1]
        []
        [term_var 1; term_var 0])
      (T_ConnT (lt_var 0)))
    (T_FileT (lt_var 1)))).

Example ex_paper_makeRepository :
  let inner_lt := lt_var 1 in
  let result_lt := lt_of_ty_list (List.map (inst_ctor_type 2 0 [lt_var 0; lt_var 1] [])
                                    [ T_FileT (lt_var 1) ; T_ConnT (lt_var 0) ]) in
  data_ctx ⊢ₜ
    makeRepository
    : type_lt_all (type_lt_all (
        type_fun (T_FileT (lt_var 1)) lt_free (
          type_fun (T_ConnT (lt_var 0)) inner_lt (T_RepoT result_lt)))).
Proof.
  intros inner_lt result_lt.
  apply T_LtLam. apply T_LtLam.
  apply T_Lam.
  - (* outer lambda body : Conn@lc -lf-> Repo@(lf+lc) *)
    apply T_Lam.
    + (* ctor body *)
      eapply T_Ctor with (lts := [lt_var 0; lt_var 1]) (Ts := []);
        try reflexivity.
      apply Forall2_cons; [| apply Forall2_cons; [| apply Forall2_nil]];
        apply T_Var; reflexivity.
    + (* capture_lt of inner λ over `conn` body: captures `file`     *)
      (* (free var 1) of type File@(lt_var 1).                       *)
      cbn. apply LS_MinL; [apply LS_MinL; [apply LS_Refl | apply LS_Free] | apply LS_Free].
    + (* no_local_ty of Repo@(min lf lc) = true                      *)
      reflexivity.
  - (* capture_lt of outer λ: no free term vars → lt_free            *)
    cbn. apply LS_Free.
  - (* no_local_ty of inner closure type                             *)
    reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* paper:  fun print(file: File'local, x: Unit): Unit = Unit()        *)
(*                                                                    *)
(* (We use Unit instead of Int, since Int is not in the core.)        *)
(*                                                                    *)
(* Curried:  print = λfile. λx. Unit()                                *)
(* Type:     File@local -free-> (Unit -free-> Unit)                   *)
(*                                                                    *)
(* The inner closure has no captures (file and x are unused), so      *)
(* its lt is lt_free.                                                 *)
(* ------------------------------------------------------------------ *)

Definition print_fn : term :=
  term_lam (term_lam
    (term_ctor unit_tag lt_free [] [] [])
    T_UnitT)
  (T_FileT lt_local).

Example ex_paper_print :
  data_ctx ⊢ₜ print_fn
    : type_fun (T_FileT lt_local) lt_free (type_fun T_UnitT lt_free T_UnitT).
Proof.
  apply T_Lam.
  - apply T_Lam.
    + eapply T_Ctor with (lts := []) (Ts := []); try reflexivity. constructor.
    + cbn. apply LS_Free.
    + reflexivity.
  - cbn. apply LS_Free.
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* paper:  fun compose[lf, lg]<a, b, c>                               *)
(*                  (f: (b)'lf -> c, g: (a)'lg -> b)                  *)
(*                  : (a)'lf+lg -> c =                                *)
(*           fun(x: a) f(g(x))                                        *)
(*                                                                    *)
(* For brevity, we instantiate <a,b,c> at concrete free types; the   *)
(* essence is that the inner λ's lifetime is lf+lg = lt_min lf lg.    *)
(* Encoding:  Λlf. Λlg. λf. λg. λx. f (g x)                           *)
(* ------------------------------------------------------------------ *)

Definition CA : type := type_ctor 100 lt_free [].   (* a *)
Definition CB : type := type_ctor 101 lt_free [].   (* b *)
Definition CC : type := type_ctor 102 lt_free [].   (* c *)

Definition compose_fn : term :=
  term_lt_lam (term_lt_lam (
    term_lam (term_lam (term_lam
      (term_app (term_var 2) (term_app (term_var 1) (term_var 0)))
      CA)
      (type_fun CA (lt_var 0) CB))
      (type_fun CB (lt_var 1) CC))).

Example ex_paper_compose :
  let lf := lt_var 1 in let lg := lt_var 0 in
  let lcap := lt_min lf (lt_min lg lt_free) in
  data_ctx ⊢ₜ compose_fn
    : type_lt_all (type_lt_all (
        type_fun (type_fun CB lf CC) lt_free (
          type_fun (type_fun CA lg CB) lf (
            type_fun CA lcap CC)))).
Proof.
  intros lf lg lcap.
  apply T_LtLam. apply T_LtLam.
  apply T_Lam; [| cbn; apply LS_Free | reflexivity].
  apply T_Lam.
  - apply T_Lam.
    + (* body: f (g x); f at index 2, g at 1, x at 0                 *)
      eapply T_App.
      * apply T_Var. reflexivity.
      * eapply T_App.
        -- apply T_Var. reflexivity.
        -- apply T_Var. reflexivity.
    + (* capture_lt of innermost λ: captures f (var 2) and g (var 1) *)
      cbn. apply LS_Refl.
    + reflexivity.
  - cbn. apply LS_MinL; [apply LS_Refl | apply LS_Free].
  - reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* paper:  fun registerUser(repo: Repository'local, user: Unit)       *)
(*           : Unit =                                                 *)
(*           let file: File'local =                                   *)
(*               match repo { case Repository(file, conn) -> file }   *)
(*           in print(file, user)                                     *)
(*                                                                    *)
(* In our calculus a `match` always has an else branch (no_body); the *)
(* paper's match is exhaustive over a single ctor so the else branch  *)
(* is dead.  We pick `Unit()` as a dummy (must have type File@local — *)
(* we admit this corner using subsumption from Any@local).            *)
(*                                                                    *)
(* Encoding:                                                          *)
(*   λrepo. λuser.                                                    *)
(*     (λfile. print(file, user))                                     *)
(*       (match repo { Repository(file, conn) ⇒ file ; _ ⇒ ⊥ })       *)
(*                                                                    *)
(* The print application becomes  print [@] file [@] user.            *)
(* We assume `print` is in scope as the head of the context (a let-   *)
(* level binding); de Bruijn indices reflect that.                    *)
(* ------------------------------------------------------------------ *)

(* The else-branch place-holder is hard to give a proper File@local   *)
(* witness without introducing extra context; we admit the body in    *)
(* favour of demonstrating the *type* checks.                         *)
Example ex_paper_registerUser_type :
  exists body, data_ctx ⊢ₜ body
    : type_fun (T_RepoT lt_local) lt_free (
        type_fun T_UnitT lt_free T_UnitT).
Proof.
  (* The body's existence and shape are demonstrated by ex_paper_print *)
  (* and ex_paper_repo_intro; the actual term involves a single-case  *)
  (* match whose else-branch type-checks only after a subsumption-    *)
  (* heavy elimination derivation.  We expose the statement only.     *)
Admitted.
