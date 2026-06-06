Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.

(* ================================================================== *)
(* CoreΔ — example DEFINITIONS                                         *)
(*                                                                    *)
(* This file collects the surface notations, the programs, the types  *)
(* and the typing/reduction contexts used by the example suite.       *)
(* Every *proof* (Lemma/Example/Theorem) lives in `ExamplesProofs.v`. *)
(*                                                                    *)
(* For each program (term-level `Definition`) we also give a          *)
(* "beautified" rendering of the same definition in surface syntax,   *)
(* in a comment immediately above it.                                 *)
(* ================================================================== *)

(* ================================================================== *)
(* 0. Notation embedding (CoreΔ surface notations)                    *)
(*                                                                    *)
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

(* ================================================================== *)
(* 1. Core types/contexts for the basic examples                      *)
(* ================================================================== *)

Definition any_local : type := type_ctor 0 `Ll [].

Definition ty_A : type := type_ctor 42 `Lf [].
Definition ty_B : type := type_ctor 43 `Lf [].
Definition pair_lt_free : lifetime := lt_of_ty_list [ty_A; ty_B].

Definition ty_A_local : type := type_ctor 42 `Ll [].
Definition pair_lt_local : lifetime := lt_of_ty_list [ty_A_local; ty_B].

(* ================================================================== *)
(* 2. Types/contexts/programs mirroring the paper repository          *)
(* ================================================================== *)

Definition unit_tag       : ctor_tag := 10.
Definition file_tag       : ctor_tag := 11.
Definition connection_tag : ctor_tag := 12.
Definition repo_tag       : ctor_tag := 13.

Definition T_UnitT    : type := type_ctor unit_tag       `Lf [].
Definition T_FileT (l : lifetime) : type := type_ctor file_tag       l [].
Definition T_ConnT (l : lifetime) : type := type_ctor connection_tag l [].
Definition T_RepoT (l : lifetime) : type := type_ctor repo_tag       l [].

(* beautified:  unit_v  ≅  Unit()                                      *)
(* "Unit value" — the canonical inhabitant of T_UnitT.                *)
Definition unit_v : term := term_ctor unit_tag `Lf [] [] [].

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

(* beautified:
     makeRepository  ≅
       Λ lf. Λ lc.
         λ (f : File@lf).
         λ (c : Conn@lc).
           Repository[lc, lf]() (f, c)
   (the result lifetime is the meet of the two field lifetimes)        *)
Definition makeRepository : term :=
  Λl \\ Λl \\
    λ: (T_FileT (`L 1)) \\
    λ: (T_ConnT (`L 0)) \\
      term_ctor repo_tag
        (lt_of_ty_list (List.map (inst_ctor_type 2 0 [`L 0; `L 1] [])
                          [ T_FileT (`L 1) ; T_ConnT (`L 0) ]))
        [`L 0; `L 1] []
        [$$ 1; $$ 0].

(* beautified:
     print_fn  ≅
       λ (f : File@local).
       λ (u : Unit).
         Unit()
   (takes a *local* File but returns a *free* Unit)                    *)
Definition print_fn : term :=
  λ: (T_FileT `Ll) \\
  λ: T_UnitT \\
    term_ctor unit_tag `Lf [] [] [].

Definition CA : type := type_ctor 100 `Lf [].
Definition CB : type := type_ctor 101 `Lf [].
Definition CC : type := type_ctor 102 `Lf [].

(* beautified:
     compose_fn  ≅
       Λ lf. Λ lg.
         λ (g : B -{lf}-> C).
         λ (f : A -{lg}-> B).
         λ (x : A).
           g (f x)
   (the composite's closure lifetime is lf ⊓ lg ⊓ free)               *)
Definition compose_fn : term :=
  Λl \\ Λl \\
    λ: (CB -{ `L 1 }-> CC) \\
    λ: (CA -{ `L 0 }-> CB) \\
    λ: CA \\
      ($$ 2) @· (($$ 1) @· ($$ 0)).

(* ================================================================== *)
(* 3. Effect declarations (Reader / Exception / Choice)               *)
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

(* beautified:  reader_op_body  ≅  k Unit       (k = #1, resume now)   *)
Definition reader_op_body : term := ($$ 1) @· unit_v.

(* beautified:
     reader_program  ≅
       handle Reader<Unit> { ask = λarg. λk. k Unit } in
         perform cap () : Unit                                         *)
Definition reader_program : term :=
  term_handle Reader_tag [T_UnitT] reader_op_body
    (term_perform ($$ 0) [] unit_v).

(* beautified:  exception_op_body  ≅  Unit       (drop the resumption) *)
Definition exception_op_body : term := unit_v.

(* beautified:
     exception_program  ≅
       handle Exception<Unit> { raise = λarg. λk. Unit } in
         perform cap () : Unit                                         *)
Definition exception_program : term :=
  term_handle Exception_tag [T_UnitT] exception_op_body
    (term_perform ($$ 0) [] unit_v).

(* beautified:  choice_op_body  ≅  k Unit        (k = #1, resume now)  *)
Definition choice_op_body : term := ($$ 1) @· unit_v.

(* beautified:
     choice_program  ≅
       handle Choice { pick = Λβ. λarg. λk. k Unit } in
         perform cap [Unit] () : Unit                                  *)
Definition choice_program : term :=
  term_handle Choice_tag [] choice_op_body
    (term_perform ($$ 0) [T_UnitT] unit_v).

(* ================================================================== *)
(* 4. State<a> — algebraic mutable state, polymorphic over state type *)
(*                                                                    *)
(* The single op of State<a> takes a `Cmd<a>` request:                *)
(*    Cmd<a> ::= Get  |  Put(a)                                        *)
(* and returns `a` (the state type).  The effect has one per-effect   *)
(* type parameter `a`; concrete programs instantiate it to `Nat`.     *)
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

(* beautified:  zero_v  ≅  Zero()                                      *)
Definition zero_v : term := term_ctor zero_tag `Lf [] [] [].
(* beautified:  suc_v n  ≅  Suc(n)                                     *)
Definition suc_v  : term -> term :=
  fun n => term_ctor suc_tag `Lf [] [] [n].
(* beautified:  one_v  ≅  Suc(Zero())                                  *)
Definition one_v  : term := suc_v zero_v.

(* Cmd type.  Single-tag wrapper; both Get / Put have ctor type Cmd. *)
Definition T_CmdT : type := type_ctor cmd_tag `Lf [].

(* ctor signatures in Γ:                                              *)
(*   Get : Cmd                  (arity 0)                              *)
(*   Put : Nat -> Cmd           (arity 1)                              *)
Definition cmd_ctx : ctx :=
  [ bind_ctor get_tag 0 0 []        T_CmdT
  ; bind_ctor put_tag 0 0 [T_NatT]  T_CmdT ].

(* beautified:  get_v  ≅  Get()                                        *)
Definition get_v : term := term_ctor get_tag `Lf [] [] [].
(* beautified:  put_v u  ≅  Put(u)                                     *)
Definition put_v : term -> term :=
  fun u => term_ctor put_tag `Lf [] [] [u].

(* State effect signature: req : Cmd<a> -> a, one per-effect type    *)
(* parameter `a = T 0` (the state cell type).                         *)
Definition state_sig : binding := bind_eff State_tag 1 0 T_CmdT (`T 0).
Definition state_ctx : ctx := state_sig :: cmd_ctx ++ nat_ctx.

(* ------------------------------------------------------------------ *)
(* State-passing op-body — the handler honestly threads a Nat cell.    *)
(*                                                                    *)
(* The op-body lives under 2 term-binders                              *)
(*    $$ 0 = arg : Cmd, $$ 1 = resumption k                            *)
(* and we then introduce `λs:Nat.` to receive the threaded state.     *)
(* ------------------------------------------------------------------ *)
(* beautified:
     state_op_body  ≅
       λ (s : Nat).                                  (* current state *)
         match arg with
         | Get      -> (k s) s                        (* read:  resume s, thread s  *)
         | Put(n)   -> (k n) n                        (* write: resume n, thread n  *)
         | _        -> s
   where arg = #1 and k = #2 under the λs binder.                      *)
Definition state_op_body : term :=
  λ: T_NatT \\
    term_match ($$ 1) get_tag 0
      (($$ 2) @· ($$ 0) @· ($$ 0))
      (term_match ($$ 1) put_tag 1
         (($$ 3) @· ($$ 0) @· ($$ 0))
         ($$ 0)).

(* beautified:
     state_get_program  ≅
       ( handle State<Nat> { req = state_op_body } in
           let n = perform cap Get in λ_. n ) Zero
     i.e. read the state, starting from Zero.                          *)
Definition state_get_program : term :=
  (term_handle State_tag [T_NatT] state_op_body
     (let: T_NatT <- term_perform ($$ 0) [] get_v in
      λ: T_NatT \\ ($$ 1)))
  @· zero_v.

(* beautified:
     state_put_program  ≅
       ( handle State<Nat> { req = state_op_body } in
           let n = perform cap (Put one) in λ_. n ) Zero
     i.e. write `one` (Put returns the new state).                     *)
Definition state_put_program : term :=
  (term_handle State_tag [T_NatT] state_op_body
     (let: T_NatT <- term_perform ($$ 0) [] (put_v one_v) in
      λ: T_NatT \\ ($$ 1)))
  @· zero_v.

(* beautified:
     state_putget_program  ≅
       ( handle State<Nat> { req = state_op_body } in
           let _ = perform cap (Put one) in
           let n = perform cap Get       in
           λ_. n ) Zero
     i.e. put one; then get observes one.                              *)
Definition state_putget_program : term :=
  (term_handle State_tag [T_NatT] state_op_body
     (let: T_NatT <- term_perform ($$ 0) [] (put_v one_v) in
      let: T_NatT <- term_perform ($$ 1) [] get_v in
      λ: T_NatT \\ ($$ 1)))
  @· zero_v.
