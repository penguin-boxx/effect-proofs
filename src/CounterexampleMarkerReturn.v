(* ================================================================== *)
(* Mechanized refutation of the axiom `marker_ok_preservation`.        *)
(*                                                                    *)
(* The axiom (Safety.v) claims subject reduction for the runtime       *)
(* marker invariant, with NO typing premise:                          *)
(*                                                                    *)
(*   forall ms t t', marker_ok ms t -> t ==> t' -> marker_ok ms t'    *)
(*                                                                    *)
(* It is FALSE, and — crucially — it stays false even when t is        *)
(* well typed AND the offending handler body has a `no_local` type.    *)
(* Hence NEITHER of the two "obvious" repairs rescues it:              *)
(*                                                                    *)
(*   (A) adding `no_local_ty T = true` to the runtime rule T_HandlerM; *)
(*   (B) a separate runtime invariant recording `no_local` at every    *)
(*       handler_m frame.                                              *)
(*                                                                    *)
(* Root cause.  `marker_ok` recurses into EVERY subterm, including     *)
(* frozen / dead positions under binders.  A capability can be buried  *)
(* as the DISCARDED argument of a function:                           *)
(*                                                                    *)
(*       lam _ : A.  (lam x : Unit. unit)  (cap E m Ts op)            *)
(*                                                                    *)
(* This value has type `A -lt_free-> Unit`, which is `no_local`,       *)
(* because the buried `cap` is not a free *variable* of the closure    *)
(* (it is a literal, discarded argument), so `capture_lt` never sees   *)
(* it and the closure lifetime stays `lt_free`.  Yet `marker_ok`       *)
(* still demands the cap's marker be in scope.                        *)
(*                                                                    *)
(* When the enclosing `handler_m m` delimiter is removed by H_Return,  *)
(* the marker `m` leaves scope while the (dead) buried cap remains,     *)
(* so `marker_ok []` is destroyed.  The escape is harmless to actual   *)
(* type safety (the cap is dead — it is never `perform`ed), which is    *)
(* exactly why `marker_ok` is too strong to be preserved: it          *)
(* constrains dead positions that the operational semantics never      *)
(* evaluates.                                                          *)
(* ================================================================== *)

Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import Semantics.
Require Import Safety.

(* ------------------------------------------------------------------ *)
(* Concrete witnesses                                                 *)
(* ------------------------------------------------------------------ *)

(* A capability with marker 7 (effect tag 1, no type args). *)
Definition cap7 : term := term_cap 1 7 0 [] (term_var 0).

(* Two simple closed `no_local` types. *)
Definition TyUnit : type := type_ctor 2 lt_free [].
Definition TyA    : type := type_ctor 3 lt_free [].

(* A closed unit value (nullary constructor). *)
Definition unitVal : term := term_ctor 2 lt_free [] [] [].

(* The handler body, AFTER the capability has been substituted in:
     lam _:A.  (lam x:Unit. unitVal)  cap7
   The inner lambda DISCARDS its argument, so the whole value has the
   `no_local` type `A -lt_free-> Unit`; the cap is a buried dead arg. *)
Definition body_value : term :=
  term_lam (term_app (term_lam unitVal TyUnit) cap7) TyA.

(* The runtime delimiter around it. *)
Definition pre : term := term_handler_m 7 body_value.

(* ------------------------------------------------------------------ *)
(* The reduction and the marker facts                                 *)
(* ------------------------------------------------------------------ *)

(* `body_value` is a value (any lambda is). *)
Lemma body_value_is_value : value body_value.
Proof. apply value_lam. Qed.

(* H_Return fires under the empty context: handler_m 7 body_value ==> body_value. *)
Lemma steps : pre ==> body_value.
Proof.
  apply (S_step EC_hole).
  - apply wf_hole.
  - apply H_Return. apply body_value_is_value.
Qed.

(* `pre` IS marker_ok [] : the cap sits under its handler_m 7. *)
Lemma pre_ok : marker_ok [] pre.
Proof. simpl. tauto. Qed.

(* `body_value` is NOT marker_ok [] : the cap escaped its handler. *)
Lemma post_not_ok : ~ marker_ok [] body_value.
Proof. simpl. tauto. Qed.

(* ------------------------------------------------------------------ *)
(* The `no_local` shape: why repairs (A)/(B) do not help              *)
(* ------------------------------------------------------------------ *)

(* The intended handle answer type `T_R = A -lt_free-> Unit` is no_local. *)
Lemma TR_no_local : no_local_ty (type_fun TyA lt_free TyUnit) = true.
Proof. reflexivity. Qed.

(* The SOURCE handle body (capability still the de Bruijn binder, var 1
   inside the closure) has NO free term variables at cutoff 1, hence
   `capture_lt _ source_body = lt_free` and the closure is `no_local`. *)
Definition source_body : term :=
  term_lam (term_app (term_lam unitVal TyUnit) (term_var 1)) TyA.

Lemma source_body_no_free : free_tm_vars 1 source_body = [].
Proof. reflexivity. Qed.

(* The S_HandleCtx substitution turns the source body into `body_value`,
   i.e. the escaped-cap shape is reachable by substituting the
   capability for the handle binder. *)
Lemma subst_makes_buried_cap :
  subst_tm 0 cap7 source_body = body_value.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Conclusion                                                         *)
(* ------------------------------------------------------------------ *)

(* `marker_ok_preservation` (no typing premise) is false. *)
Theorem marker_ok_preservation_is_false :
  ~ (forall ms t t', marker_ok ms t -> t ==> t' -> marker_ok ms t').
Proof.
  intro H. apply post_not_ok.
  eapply H. apply pre_ok. apply steps.
Qed.

(* And it remains false on a term whose handler body has a `no_local`
   type and is reachable from a source `term_handle` (TR_no_local,
   source_body_no_free, subst_makes_buried_cap above), so adding a
   `no_local` premise to T_HandlerM (A) or tracking `no_local` at
   handler_m frames (B) does NOT make the principle provable. *)
