(* ================================================================== *)
(* Examples_smallstep.v — legacy small-step reduction examples.       *)
(*                                                                    *)
(* These were originally part of src/Examples.v, alongside the CEK   *)
(* reduction examples in section 21.  They now live here as a        *)
(* historical/reference archive.  The CEK examples in src/Examples.v *)
(* (section 21: cek_red_*) are the canonical reduction demonstrations*)
(* for the calculus.                                                  *)
(*                                                                    *)
(* This file is NOT built as part of the main project (it is not in  *)
(* src/_CoqProject).  To compile it standalone:                       *)
(*   coqc -Q ../../src "" -Q ../../vendor/Metalib Metalib            *)
(*        Semantics.v Safety.v Examples_smallstep.v                   *)
(* ================================================================== *)

From Stdlib Require Import List.
Import ListNotations.
From Metalib Require Export Metatheory.

Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import Semantics.

(* ------------------------------------------------------------------ *)
(* Beta-reduction of an identity function on a free constructor.      *)
(* ------------------------------------------------------------------ *)

Definition id_any : term :=
  term_lam (term_bvar 0) (type_ctor any_tag lt_free []).

Definition empty_any : term :=
  term_ctor any_tag lt_free [] [] [].

Example beta_id_empty :
  term_app id_any empty_any ~~>h empty_any.
Proof.
  unfold id_any, empty_any.
  replace (term_ctor any_tag lt_free [] [] [])
     with (open_tm_wrt_tm
              (term_ctor any_tag lt_free [] [] [])
              (term_bvar 0))
       by reflexivity.
  apply H_Beta. constructor. constructor.
Qed.

Example beta_id_empty_step :
  term_app id_any empty_any ~~> empty_any.
Proof.
  apply (S_step EC_hole _ _).
  - constructor.
  - simpl. apply beta_id_empty.
Qed.

Example beta_id_empty_multi :
  term_app id_any empty_any ~~>* empty_any.
Proof.
  eapply MS_step; [ apply beta_id_empty_step | apply MS_refl ].
Qed.

(* ------------------------------------------------------------------ *)
(* Generic small-step reductions.                                     *)
(* ------------------------------------------------------------------ *)

Lemma red_identity :
  forall T v,
    value v ->
    term_app (term_lam (term_bvar 0) T) v ~~>* v.
Proof.
  intros T v Hv.
  eapply MS_step.
  - apply S_step with (E := EC_hole).
    + constructor.
    + apply H_Beta. exact Hv.
  - simpl. apply MS_refl.
Qed.

Lemma red_lt_beta : forall body l,
  term_lt_app (term_lt_lam body) l ~~>* open_tm_wrt_lt l body.
Proof.
  intros body l.
  eapply MS_step; [| apply MS_refl].
  apply S_step with (E := EC_hole); [constructor|].
  apply H_LtBeta.
Qed.

Lemma red_ty_beta : forall B body T,
  term_ty_app (term_ty_lam B body) T ~~>* open_tm_wrt_ty T body.
Proof.
  intros B body T.
  eapply MS_step; [| apply MS_refl].
  apply S_step with (E := EC_hole); [constructor|].
  apply H_TyBeta.
Qed.

Example red_match_arity0 :
  forall K l Ts yes_body no_body,
    term_match (term_ctor K l [] Ts []) K 0 yes_body no_body
      ~~>* yes_body.
Proof.
  intros K l Ts yes_body no_body.
  eapply MS_step; [| apply MS_refl].
  apply S_step with (E := EC_hole); [constructor|].
  change yes_body with (open_tm_wrt_tm_list [] (open_tm_wrt_lt_list [] yes_body))
    at 2.
  apply (H_MatchYes K l [] Ts []).
  constructor.
Qed.
