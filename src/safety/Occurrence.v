Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import MarkerAnnots.
Require Import WellScoped.
Require Import WsRtLaws.
Require Import Soundness.
Require Import Escape.

(* ================================================================== *)
(*                                                                    *)
(*        OCCURRENCE-LEVEL CAPABILITY CONFINEMENT (paths)             *)
(*                                                                    *)
(* Escape.v's [capability_confined] speaks only about a capability    *)
(* sitting in an evaluation-context hole — an *active* position.      *)
(* The invariant it consumes, [well_scoped] (WellScoped.v), is        *)
(* structurally stronger: it traverses lambda bodies, constructor     *)
(* arguments, match branches, handler op-bodies, and even the         *)
(* op-bodies stored inside capabilities themselves.  This file        *)
(* exposes that strength as a path theorem: EVERY syntactic           *)
(* occurrence of a capability, at any depth — under binders, inside   *)
(* stored op-bodies — has its marker in the marker scope computed     *)
(* along the path to that occurrence.                                 *)
(*                                                                    *)
(* The scope discipline of the path semantics mirrors [well_scoped]   *)
(* exactly:                                                           *)
(*  - descending into [term_handler_m m _ _ body] pushes m;           *)
(*  - descending into a cap's stored op-body re-scopes with           *)
(*    [scope_below m ms] — the scope OUTSIDE the cap's own            *)
(*    delimiter, where the H_Perform reduct would land;               *)
(*  - every other child position passes the scope through unchanged   *)
(*    (including under term/type/lifetime binders).                   *)
(*                                                                    *)
(* [capability_confined] is recovered below as the empty-scope,       *)
(* eval-ctx-path instance ([capability_confined_from_occurrence]).    *)
(* ================================================================== *)


(* ================================================================== *)
(* Paths: one step per descendable child position of a term.          *)
(* ================================================================== *)

Inductive pstep : Type :=
  | P_app1           : pstep          (* term_app, function position   *)
  | P_app2           : pstep          (* term_app, argument position   *)
  | P_lam_body       : pstep
  | P_ty_app         : pstep
  | P_ty_lam_body    : pstep
  | P_lt_app         : pstep
  | P_lt_lam_body    : pstep
  | P_ctor_arg       : nat -> pstep   (* i-th constructor argument     *)
  | P_match_scrut    : pstep
  | P_match_yes      : pstep
  | P_match_no       : pstep
  | P_handle_op      : nat -> pstep   (* i-th operation clause         *)
  | P_handle_body    : pstep
  | P_perform_recv   : pstep
  | P_perform_arg    : pstep
  | P_cap_op_body    : nat -> pstep   (* i-th op-body STORED in a cap  *)
  | P_handler_m_body : pstep.

Definition path : Type := list pstep.

(* The immediate subterm of [t] selected by one path step, if any.    *)
Definition child_at (t : term) (s : pstep) : option term :=
  match t, s with
  | term_app t1 _,                 P_app1           => Some t1
  | term_app _ t2,                 P_app2           => Some t2
  | term_lam body _,               P_lam_body       => Some body
  | term_ty_app t1 _,              P_ty_app         => Some t1
  | term_ty_lam _ body,            P_ty_lam_body    => Some body
  | term_lt_app t1 _,              P_lt_app         => Some t1
  | term_lt_lam body,              P_lt_lam_body    => Some body
  | term_ctor _ _ _ _ ts,          P_ctor_arg i     => nth_error ts i
  | term_match scrut _ _ _ _ _,    P_match_scrut    => Some scrut
  | term_match _ _ _ _ yes _,      P_match_yes      => Some yes
  | term_match _ _ _ _ _ no,       P_match_no       => Some no
  | term_handle _ _ _ _ ops _,     P_handle_op i    => option_map snd (nth_error ops i)
  | term_handle _ _ _ _ _ body,    P_handle_body    => Some body
  | term_perform recv _ _ _ _,     P_perform_recv   => Some recv
  | term_perform _ _ _ _ arg,      P_perform_arg    => Some arg
  | term_cap _ _ _ _ ops,          P_cap_op_body i  => option_map snd (nth_error ops i)
  | term_handler_m _ _ _ body,     P_handler_m_body => Some body
  | _, _ => None
  end.

(* The subterm of [t] at path [p]; None iff [p] is not a valid path.  *)
Fixpoint subterm_at (t : term) (p : path) : option term :=
  match p with
  | [] => Some t
  | s :: rest =>
      match child_at t s with
      | Some u => subterm_at u rest
      | None   => None
      end
  end.


(* ================================================================== *)
(* Scope transport along a path.                                      *)
(*                                                                    *)
(* [scope_step] is the one-step scope transformer, mirroring the two  *)
(* scope-changing clauses of [well_scoped]: handler_m pushes its      *)
(* marker; a cap's stored op-body is re-scoped at [scope_below m ms]. *)
(* All other positions — including all binder-crossing ones — pass    *)
(* the ambient scope through unchanged.                               *)
(* ================================================================== *)

Definition scope_step (ms : list marker) (t : term) (s : pstep) : list marker :=
  match t, s with
  | term_handler_m m _ _ _, P_handler_m_body => m :: ms
  | term_cap _ m _ _ _,     P_cap_op_body _  => scope_below m ms
  | _, _ => ms
  end.

(* The marker scope in force at the subterm reached by [p], starting  *)
(* from ambient scope [ms]; None iff [p] is not a valid path in [t].  *)
Fixpoint scope_at (ms : list marker) (t : term) (p : path) : option (list marker) :=
  match p with
  | [] => Some ms
  | s :: rest =>
      match child_at t s with
      | Some u => scope_at (scope_step ms t s) u rest
      | None   => None
      end
  end.

(* [scope_at] is defined exactly where [subterm_at] is: both recurse  *)
(* through the same [child_at] spine.                                 *)
(* Sanity check for the path semantics (documentation; no consumers). *)
Lemma scope_at_defined_iff_subterm_at : forall p t ms,
  (exists ms', scope_at ms t p = Some ms') <-> (exists u, subterm_at t p = Some u).
Proof.
  induction p as [|s p IH]; intros t ms; simpl.
  - split; intros _; eexists; reflexivity.
  - destruct (child_at t s) as [u|].
    + apply IH.
    + split; intros [x Hx]; discriminate.
Qed.


(* ================================================================== *)
(* well_scoped is exactly path-compatible: descending one child       *)
(* position transports the invariant along [scope_step].              *)
(* ================================================================== *)

Lemma well_scoped_list_nth_error : forall ms ts i u,
  well_scoped_list ms ts ->
  nth_error ts i = Some u ->
  well_scoped ms u.
Proof.
  intros ms ts. induction ts as [|t ts IH]; intros i u Hws Hnth.
  - destruct i; discriminate.
  - destruct i as [|i]; simpl in Hnth.
    + injection Hnth as <-. exact (proj1 Hws).
    + exact (IH i u (proj2 Hws) Hnth).
Qed.

(* Ops-clause variant, through the [option_map snd] child selector. *)
Lemma ops_well_scoped_child : forall ms (obs : list (nat * term)) i u,
  ops_well_scoped ms obs ->
  option_map snd (nth_error obs i) = Some u ->
  well_scoped ms u.
Proof.
  intros ms obs i u Hws Hnth.
  destruct (nth_error obs i) as [[nb ob]|] eqn:Hn; simpl in Hnth; [|discriminate].
  injection Hnth as <-.
  eapply ops_well_scoped_nth; eauto.
Qed.

(* The single-step kernel of the occurrence theorem.  Each case reads *)
(* off the corresponding conjunct of the matching [well_scoped]       *)
(* clause; the cap and handler_m cases are the two where the scope    *)
(* actually moves, and [scope_step] moves it identically.             *)
Lemma well_scoped_child : forall ms t s u,
  well_scoped ms t ->
  child_at t s = Some u ->
  well_scoped (scope_step ms t s) u.
Proof.
  intros ms t s u Hws Hchild.
  destruct t; destruct s; simpl in Hchild; try discriminate; simpl.
  - (* app / P_app1 *)          injection Hchild as <-. exact (proj1 Hws).
  - (* app / P_app2 *)          injection Hchild as <-. exact (proj2 Hws).
  - (* lam / P_lam_body *)      injection Hchild as <-. exact Hws.
  - (* ty_app / P_ty_app *)     injection Hchild as <-. exact Hws.
  - (* ty_lam / P_ty_lam_body *) injection Hchild as <-. exact Hws.
  - (* lt_app / P_lt_app *)     injection Hchild as <-. exact Hws.
  - (* lt_lam / P_lt_lam_body *) injection Hchild as <-. exact Hws.
  - (* ctor / P_ctor_arg *)
    rewrite well_scoped_ctor_eq in Hws.
    eapply well_scoped_list_nth_error; eauto.
  - (* match / P_match_scrut *) injection Hchild as <-. exact (proj1 Hws).
  - (* match / P_match_yes *)   injection Hchild as <-. exact (proj1 (proj2 Hws)).
  - (* match / P_match_no *)    injection Hchild as <-. exact (proj2 (proj2 Hws)).
  - (* handle / P_handle_op i *)
    eapply ops_well_scoped_child; [exact (proj1 Hws) | exact Hchild].
  - (* handle / P_handle_body *) injection Hchild as <-. exact (proj2 Hws).
  - (* perform / P_perform_recv *) injection Hchild as <-. exact (proj1 Hws).
  - (* perform / P_perform_arg *)  injection Hchild as <-. exact (proj2 Hws).
  - (* cap / P_cap_op_body i: scope_below re-scope, per well_scoped *)
    eapply ops_well_scoped_child; [exact (proj2 Hws) | exact Hchild].
  - (* handler_m / P_handler_m_body: marker push, per well_scoped *)
    injection Hchild as <-. exact Hws.
Qed.


(* ================================================================== *)
(*                                                                    *)
(*                THE OCCURRENCE THEOREM                              *)
(*                                                                    *)
(* Every syntactic capability occurrence — at ANY depth, including    *)
(* under binders and inside the op-bodies stored in other caps — has  *)
(* its marker in the scope computed along its path.  In particular,   *)
(* at ambient scope [] a capability can only occur strictly inside a  *)
(* handler_m delimiter carrying its marker (or below a cap whose      *)
(* path already crossed one).                                         *)
(* ================================================================== *)

Theorem well_scoped_occurrence_delimited :
  forall p ms t E_tag m Ts T_R op_bodies,
  well_scoped ms t ->
  subterm_at t p = Some (term_cap E_tag m Ts T_R op_bodies) ->
  exists ms', scope_at ms t p = Some ms' /\ In m ms'.
Proof.
  induction p as [|s p IH]; intros ms t E_tag m Ts T_R op_bodies Hws Hsub;
    simpl in Hsub |- *.
  - (* Empty path: t IS the cap; its well_scoped clause has In m ms. *)
    injection Hsub as ->. simpl in Hws.
    exists ms. split; [reflexivity | exact (proj1 Hws)].
  - destruct (child_at t s) as [u|] eqn:Hchild; [|discriminate].
    eapply IH; [|exact Hsub].
    eapply well_scoped_child; eauto.
Qed.

(* Source-facing form: for a program with no runtime marker            *)
(* constructs, [well_scoped [] u] along the trace is discharged by     *)
(* the step-preserved runtime invariants (the ws_rt conjunct of        *)
(* [safety_invariants], exactly as in                                  *)
(* [source_capability_never_exposed], Escape.v), so the guarantee      *)
(* needs only the initial typing.                                      *)
Corollary source_capability_occurrence_delimited :
  forall Γ t T u p E_tag m Ts T_R op_bodies,
  eval_ctx Γ ->
  has_rt_marker t = false ->
  Γ ⊢ₜ t : T ->
  multi_step t u ->
  subterm_at u p = Some (term_cap E_tag m Ts T_R op_bodies) ->
  exists ms', scope_at [] u p = Some ms' /\ In m ms'.
Proof.
  intros Γ t T u p E_tag m Ts T_R op_bodies Hec Hsrc Hty Hms Hsub.
  destruct (multi_step_preserves_safety_invariants _ _ _ _ Hec
              (source_safety_invariants _ _ _ Hsrc Hty) Hms)
    as [_ [[Hws _] _]].
  eapply well_scoped_occurrence_delimited; eauto.
Qed.


(* ================================================================== *)
(*                                                                    *)
(*        BRIDGE TO EVAL-CTX CONFINEMENT (Escape.v)                   *)
(*                                                                    *)
(* An evaluation context is a path: [path_of_ectx] reads off the      *)
(* spine, and [subterm_at_plug] identifies the plug hole with the     *)
(* subterm at that path.  A [pure_ectx_m m E] context is precisely a  *)
(* path crossing no handler_m frame with marker m, so the scope it    *)
(* transports can only contain m if the ambient scope already did     *)
(* ([scope_at_plug_pure]).  At ambient scope [] that is impossible —  *)
(* Escape.v's [capability_confined] is the empty-scope instance of    *)
(* the occurrence theorem.                                            *)
(* ================================================================== *)

Fixpoint path_of_ectx (E : ectx) : path :=
  match E with
  | EC_hole                  => []
  | EC_app1 E1 _             => P_app1 :: path_of_ectx E1
  | EC_app2 _ E2             => P_app2 :: path_of_ectx E2
  | EC_ty_app E1 _           => P_ty_app :: path_of_ectx E1
  | EC_lt_app E1 _           => P_lt_app :: path_of_ectx E1
  | EC_ctor _ _ _ _ vs E1 _  => P_ctor_arg (List.length vs) :: path_of_ectx E1
  | EC_match E1 _ _ _ _ _    => P_match_scrut :: path_of_ectx E1
  | EC_handler_m _ _ _ E1    => P_handler_m_body :: path_of_ectx E1
  | EC_perform_r E1 _ _ _ _  => P_perform_recv :: path_of_ectx E1
  | EC_perform_a _ _ _ _ E1  => P_perform_arg :: path_of_ectx E1
  end.

(* The hole of EC_ctor sits at index (length vs) of vs ++ hole :: ts. *)
Lemma nth_error_app_mid : forall (A : Type) (vs ts : list A) (x : A),
  nth_error (vs ++ x :: ts) (List.length vs) = Some x.
Proof.
  intros A vs ts x. induction vs as [|v vs IH]; simpl; [reflexivity | exact IH].
Qed.

Lemma subterm_at_plug : forall E r,
  subterm_at (plug E r) (path_of_ectx E) = Some r.
Proof.
  induction E; intros r; simpl.
  - reflexivity.
  - apply IHE.
  - apply IHE.
  - apply IHE.
  - apply IHE.
  - rewrite nth_error_app_mid. apply IHE.
  - apply IHE.
  - apply IHE.
  - apply IHE.
  - apply IHE.
Qed.

(* A marker-pure context never pushes m: the scope at its hole        *)
(* contains m only if the ambient scope already did.  (Handlers with  *)
(* a different marker m' <> m are transparent, exactly as in          *)
(* [pure_ectx_m]; no ectx frame descends into a stored op-body, so    *)
(* [scope_below] never fires along an eval-ctx path.)                 *)
Lemma scope_at_plug_pure : forall m E r ms,
  pure_ectx_m m E ->
  exists ms', scope_at ms (plug E r) (path_of_ectx E) = Some ms' /\
              (In m ms' -> In m ms).
Proof.
  intros m E r ms Hpure. revert ms.
  induction Hpure; intros ms; simpl.
  - exists ms. split; [reflexivity | tauto].
  - apply IHHpure.
  - apply IHHpure.
  - apply IHHpure.
  - apply IHHpure.
  - rewrite nth_error_app_mid. apply IHHpure.
  - apply IHHpure.
  - (* handler_m with m' <> m: the push cannot introduce m. *)
    destruct (IHHpure (m' :: ms)) as [ms'' [Heq Himp]].
    exists ms''. split; [exact Heq|].
    intros Hin. destruct (Himp Hin) as [Heqm | Hin'];
      [exfalso; apply H; symmetry; exact Heqm | exact Hin'].
  - apply IHHpure.
  - apply IHHpure.
Qed.

(* The formal bridge: Escape.v's [capability_confined], re-derived as *)
(* the empty-scope, eval-ctx-path instance of                         *)
(* [well_scoped_occurrence_delimited].                                *)
(* PUBLIC API — terminal deliverable: no internal consumers; do not
   mistake for dead code.  Gated by scripts/check_assumptions.py. *)
Theorem capability_confined_from_occurrence :
  forall E E_tag m Ts T_R op_bodies,
  well_scoped [] (plug E (term_cap E_tag m Ts T_R op_bodies)) ->
  ~ pure_ectx_m m E.
Proof.
  intros E E_tag m Ts T_R op_bodies Hws Hpure.
  destruct (well_scoped_occurrence_delimited (path_of_ectx E) [] _ _ _ _ _ _
              Hws (subterm_at_plug E _)) as [ms' [Hscope Hin]].
  destruct (scope_at_plug_pure m E (term_cap E_tag m Ts T_R op_bodies) [] Hpure)
    as [ms'' [Hscope' Himp]].
  rewrite Hscope in Hscope'. injection Hscope' as Heq. subst ms''.
  destruct (Himp Hin).
Qed.
