(* =================================================================== *)
(* CEK.v — closed CEK abstract machine for the effect calculus         *)
(*                                                                     *)
(* The state of the machine is                                         *)
(*                                                                     *)
(*    config := ⟨ ctrl : term ; env : env ; kont : kont ; nm : nat ⟩   *)
(*                                                                     *)
(* Bound term-variables are resolved by environment lookup (closures); *)
(* bound type / lifetime variables continue to use LN opening from     *)
(* `Substitution.v`.  Handlers are first-class kont frames.            *)
(* =================================================================== *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Metalib Require Export Metatheory.

Require Import Syntax.
Require Import Substitution.

(* ================================================================== *)
(* Runtime values                                                     *)
(*                                                                    *)
(* These are CLOSED runtime entities and are distinct from the        *)
(* syntactic `Syntax.value : term -> Prop` predicate.  Each closure   *)
(* form pairs a piece of source `term` with the environment captured  *)
(* at definition time.                                                *)
(* ================================================================== *)

Inductive rvalue : Type :=
  | clos_lam     : term -> list rvalue -> type -> rvalue
      (* body, captured env, parameter type *)
  | clos_ty_lam  : type -> term -> list rvalue -> rvalue
      (* bound, body, captured env *)
  | clos_lt_lam  : term -> list rvalue -> rvalue
      (* body, captured env *)
  | clos_ctor    : ctor_tag -> lifetime -> list lifetime -> list type ->
                   list rvalue -> rvalue
      (* K, l, lts, Ts, value-fields                                   *)
  | clos_cap     : eff_tag -> marker -> list type -> term ->
                   list rvalue -> rvalue
      (* E, m, Ts, op_body (still a syntactic term — its tm-binders    *)
      (*   are filled by env at perform-time), captured env            *)
  | clos_resume  : list kframe -> rvalue
      (* reified resumption.  The stored kont K_r equals               *)
      (*   K_inner ++ [KHandle m E Ts op_body ρ_h]                     *)
      (* where K_inner is the pure prefix above the matching delimiter *)
      (* at capture time.  Applying this resumption to a value v       *)
      (* simply prepends K_r to the current kont and returns v.        *)

with kframe : Type :=
  | KApp1       : term -> list rvalue -> kframe
      (* unevaluated arg t2 with its env: we are currently evaluating  *)
      (* t1; once t1 ↓ v1 we move to evaluating t2 under this env.     *)
  | KApp2       : rvalue -> kframe
      (* fully-evaluated function value awaiting its arg's value       *)
  | KTyApp      : type -> kframe
  | KLtApp      : lifetime -> kframe
  | KCtor       : ctor_tag -> lifetime -> list lifetime -> list type ->
                  list rvalue ->         (* values already evaluated   *)
                  list term  ->          (* terms still to evaluate    *)
                  list rvalue ->         (* env for those terms        *)
                  kframe
  | KMatch      : ctor_tag -> nat -> term -> term -> list rvalue -> kframe
      (* K_tag, arity, yes_body, no_body, env                          *)
  | KHandle     : marker -> eff_tag -> list type -> term -> list rvalue -> kframe
      (* m, E, Ts, op_body, captured env                               *)
  | KPerformR   : list type -> term -> list rvalue -> kframe
      (* evaluating receiver: (Ss, arg, env)                           *)
  | KPerformA   : rvalue -> list type -> kframe
      (* evaluating arg: receiver-value, Ss                            *)
  .

Definition env : Type := list rvalue.
Definition kont : Type := list kframe.

(* ================================================================== *)
(* Configurations                                                     *)
(*                                                                    *)
(* Two shapes: an "evaluating" config has a control term to reduce;   *)
(* a "returning" config has a runtime value to feed to the top frame. *)
(* ================================================================== *)

Inductive config : Type :=
  | C_ev  : term   -> env  -> kont -> nat -> config
      (* "evaluate t under ρ with kont K and next-marker counter n"   *)
  | C_ret : rvalue -> kont -> nat -> config
      (* "return value v to kont K"                                   *)
  | C_done : rvalue -> config
      (* terminal halt state                                          *)
  .

(* ================================================================== *)
(* Environment lookup                                                 *)
(*                                                                    *)
(* Bound term-variables `term_bvar n` resolve to the n-th element of  *)
(* the env (zero-indexed, INNERMOST first).  `nth_error` returns the  *)
(* runtime value, or `None` if the index is out of scope (impossible  *)
(* in well-typed terms).                                              *)
(* ================================================================== *)

Definition env_lookup (rho : env) (n : nat) : option rvalue :=
  nth_error rho n.

(* ================================================================== *)
(* Initial / final configurations                                     *)
(* ================================================================== *)

Definition initial_config (t : term) : config :=
  C_ev t [] [] 0.

Definition is_done (c : config) : Prop :=
  match c with
  | C_done _ => True
  | _        => False
  end.

(* ================================================================== *)
(* Helper: split a kont at the first KHandle frame matching marker m. *)
(*                                                                    *)
(*   split_at_handler m K = Some (K_inner, m, E, Ts, ob, ρ, K_outer)  *)
(*                                                                    *)
(* iff K = K_inner ++ KHandle m E Ts ob ρ :: K_outer  and             *)
(* no frame in K_inner is a KHandle for m.                            *)
(*                                                                    *)
(* (Markers are unique by construction at runtime, so the predicate   *)
(* is functional: we just take the first matching KHandle.)           *)
(* ================================================================== *)

Fixpoint split_at_handler (m : marker) (K : kont)
  : option (kont * eff_tag * list type * term * env * kont) :=
  match K with
  | []                                  => None
  | KHandle m' E Ts ob ρ :: rest =>
      if Nat.eqb m m'
      then Some ([], E, Ts, ob, ρ, rest)
      else match split_at_handler m rest with
           | None => None
           | Some (K_inner, E', Ts', ob', ρ', K_outer) =>
               Some (KHandle m' E Ts ob ρ :: K_inner, E', Ts', ob', ρ', K_outer)
           end
  | f :: rest =>
      match split_at_handler m rest with
      | None => None
      | Some (K_inner, E', Ts', ob', ρ', K_outer) =>
          Some (f :: K_inner, E', Ts', ob', ρ', K_outer)
      end
  end.

(* ================================================================== *)
(* Step relation                                                      *)
(* ================================================================== *)

Reserved Notation "c1 '~~>c' c2" (at level 55).

Inductive cstep : config -> config -> Prop :=

  (* ---------------- PUSH transitions: control is a non-value -------- *)

  | CS_BVar : forall n ρ K nm v,
      env_lookup ρ n = Some v ->
      C_ev (term_bvar n) ρ K nm ~~>c C_ret v K nm

  | CS_App : forall t1 t2 ρ K nm,
      C_ev (term_app t1 t2) ρ K nm
        ~~>c C_ev t1 ρ (KApp1 t2 ρ :: K) nm

  | CS_Lam : forall body T ρ K nm,
      C_ev (term_lam body T) ρ K nm
        ~~>c C_ret (clos_lam body ρ T) K nm

  | CS_TyLam : forall bound body ρ K nm,
      C_ev (term_ty_lam bound body) ρ K nm
        ~~>c C_ret (clos_ty_lam bound body ρ) K nm

  | CS_LtLam : forall body ρ K nm,
      C_ev (term_lt_lam body) ρ K nm
        ~~>c C_ret (clos_lt_lam body ρ) K nm

  | CS_TyApp : forall t T ρ K nm,
      C_ev (term_ty_app t T) ρ K nm
        ~~>c C_ev t ρ (KTyApp T :: K) nm

  | CS_LtApp : forall t l ρ K nm,
      C_ev (term_lt_app t l) ρ K nm
        ~~>c C_ev t ρ (KLtApp l :: K) nm

  (* ctor with no fields: emit value immediately. *)
  | CS_CtorNil : forall Kt l lts Ts ρ K nm,
      C_ev (term_ctor Kt l lts Ts []) ρ K nm
        ~~>c C_ret (clos_ctor Kt l lts Ts []) K nm

  (* ctor with at least one field: start evaluating the leftmost. *)
  | CS_CtorCons : forall Kt l lts Ts t ts ρ K nm,
      C_ev (term_ctor Kt l lts Ts (t :: ts)) ρ K nm
        ~~>c C_ev t ρ (KCtor Kt l lts Ts [] ts ρ :: K) nm

  | CS_Match : forall scrut Kt ar y n ρ K nm,
      C_ev (term_match scrut Kt ar y n) ρ K nm
        ~~>c C_ev scrut ρ (KMatch Kt ar y n ρ :: K) nm

  (* (handle): allocate a fresh marker = nm, push KHandle delimiter,    *)
  (*  extend env with the cap, step into body.                          *)
  | CS_Handle : forall E Ts ob body ρ K nm,
      C_ev (term_handle E Ts ob body) ρ K nm
        ~~>c C_ev body
              (clos_cap E nm Ts ob ρ :: ρ)
              (KHandle nm E Ts ob ρ :: K)
              (S nm)

  | CS_Cap : forall E m Ts ob ρ K nm,
      C_ev (term_cap E m Ts ob) ρ K nm
        ~~>c C_ret (clos_cap E m Ts ob ρ) K nm

  | CS_Perform : forall recv Ss arg ρ K nm,
      C_ev (term_perform recv Ss arg) ρ K nm
        ~~>c C_ev recv ρ (KPerformR Ss arg ρ :: K) nm

  (* ---------------- POP transitions: control is a value ------------ *)

  (* App: evaluate the arg next. *)
  | CS_KApp1 : forall v t2 ρ K nm,
      C_ret v (KApp1 t2 ρ :: K) nm
        ~~>c C_ev t2 ρ (KApp2 v :: K) nm

  (* App-beta on a lambda: extend env, step into body — NO opening. *)
  | CS_BetaLam : forall body ρ' T v K nm,
      C_ret v (KApp2 (clos_lam body ρ' T) :: K) nm
        ~~>c C_ev body (v :: ρ') K nm

  (* App on a reified resumption: prepend its kont to current K, then  *)
  (* return the value.  The trailing KHandle in Kr restores the        *)
  (* delimiter automatically.                                          *)
  | CS_BetaResume : forall Kr v K nm,
      C_ret v (KApp2 (clos_resume Kr) :: K) nm
        ~~>c C_ret v (Kr ++ K) nm

  (* TyApp on a ty-lambda: open the type binder.  (Types still use LN.) *)
  | CS_BetaTy : forall bound body ρ' T K nm,
      C_ret (clos_ty_lam bound body ρ') (KTyApp T :: K) nm
        ~~>c C_ev (open_tm_wrt_ty T body) ρ' K nm

  (* LtApp on a lt-lambda: open the lifetime binder. *)
  | CS_BetaLt : forall body ρ' l K nm,
      C_ret (clos_lt_lam body ρ') (KLtApp l :: K) nm
        ~~>c C_ev (open_tm_wrt_lt l body) ρ' K nm

  (* Ctor: a field finished evaluating; advance to next field or emit. *)
  | CS_KCtorMore : forall v Kt l lts Ts vs t ts ρ' K nm,
      C_ret v (KCtor Kt l lts Ts vs (t :: ts) ρ' :: K) nm
        ~~>c C_ev t ρ' (KCtor Kt l lts Ts (vs ++ [v]) ts ρ' :: K) nm

  | CS_KCtorDone : forall v Kt l lts Ts vs ρ' K nm,
      C_ret v (KCtor Kt l lts Ts vs [] ρ' :: K) nm
        ~~>c C_ret (clos_ctor Kt l lts Ts (vs ++ [v])) K nm

  (* Match success: env-extend by lts (lifetime binders, opened first  *)
  (* in legacy) plus the constructor fields, then step into yes.       *)
  (* Lifetime binders are still opened via open_tm_wrt_lt_list since   *)
  (* lifetimes are not closures.                                       *)
  | CS_KMatchYes : forall Kt l lts Ts vs ar y n ρ' K nm,
      List.length vs = ar ->
      C_ret (clos_ctor Kt l lts Ts vs) (KMatch Kt ar y n ρ' :: K) nm
        ~~>c C_ev (open_tm_wrt_lt_list lts y)
                  (List.rev vs ++ ρ')
                  K nm

  (* Match failure: tag mismatch — step into no-branch (binds nothing). *)
  | CS_KMatchNo : forall Kt' l lts Ts vs Kt ar y n ρ' K nm,
      Kt <> Kt' ->
      C_ret (clos_ctor Kt' l lts Ts vs) (KMatch Kt ar y n ρ' :: K) nm
        ~~>c C_ev n ρ' K nm

  (* Handler delimiter pops if the body returned a value. *)
  | CS_KHandleReturn : forall v m E Ts ob ρ' K nm,
      C_ret v (KHandle m E Ts ob ρ' :: K) nm
        ~~>c C_ret v K nm

  (* PerformR finished: receiver evaluated to a cap.  Step to evaluate
     the argument. *)
  | CS_KPerformR : forall v Ss arg ρ' K nm,
      C_ret v (KPerformR Ss arg ρ' :: K) nm
        ~~>c C_ev arg ρ' (KPerformA v Ss :: K) nm

  (* PerformA finished: argument evaluated.  Now fire the operation:   *)
  (*   walk K to find the matching KHandle for the cap's marker;       *)
  (*   the prefix above it (plus the KHandle itself) becomes the       *)
  (*   reified resumption; the rest of K becomes the new outer kont.   *)
  | CS_KPerformFire : forall E m Ts ob ρ_cap Ss v K nm
                            K_inner E' Ts' ob' ρ_h K_outer,
      split_at_handler m K
        = Some (K_inner, E', Ts', ob', ρ_h, K_outer) ->
      let Kr := K_inner ++ [KHandle m E' Ts' ob' ρ_h] in
      C_ret v (KPerformA (clos_cap E m Ts ob ρ_cap) Ss :: K) nm
        ~~>c C_ev (open_tm_wrt_ty_list Ss ob)
                  (v :: clos_resume Kr :: ρ_cap)
                  K_outer nm

  (* Empty kont with a value: machine halts. *)
  | CS_Done : forall v nm,
      C_ret v [] nm ~~>c C_done v

where "c1 '~~>c' c2" := (cstep c1 c2).

#[export] Hint Constructors cstep : core.

(* ================================================================== *)
(* Reflexive-transitive closure                                       *)
(* ================================================================== *)

Reserved Notation "c1 '~~>c*' c2" (at level 55).

Inductive cmulti : config -> config -> Prop :=
  | CM_refl : forall c, c ~~>c* c
  | CM_step : forall c1 c2 c3,
      c1 ~~>c c2 -> c2 ~~>c* c3 -> c1 ~~>c* c3
where "c1 '~~>c*' c2" := (cmulti c1 c2).

#[export] Hint Constructors cmulti : core.
