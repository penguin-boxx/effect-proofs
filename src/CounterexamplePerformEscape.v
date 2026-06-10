(* ================================================================== *)
(* Regression for the operation-argument escape that motivated the    *)
(* no-local premise on T_Perform.                                     *)
(*                                                                    *)
(* The old rule allowed an operation whose argument type was the       *)
(* handler's own local capability type.  Then an op body could force  *)
(* evaluation of `perform cap [] cap` after H_Perform had removed the *)
(* delimiter, yielding an unhandled, stuck perform.                   *)
(*                                                                    *)
(* The current rule rejects exactly this shape because the             *)
(* instantiated argument signature is not `no_local_ty`.              *)
(* ================================================================== *)

Require Import Stdlib.Lists.List.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.

Definition bad_E : eff_tag := 17.
Definition bad_unit_K : ctor_tag := 18.
Definition bad_m : marker := 19.

Definition bad_cap_ty : type := type_ctor bad_E lt_local [].
Definition bad_unit_ty : type := type_ctor bad_unit_K lt_free [].
Definition bad_unit_v : term := term_ctor bad_unit_K lt_free [] [] [].

(* Under the op-body binders, variable 0 is the operation argument. *)
Definition bad_op_body : term :=
  term_app
    (term_lam bad_unit_v bad_unit_ty)
    (term_perform (term_var 0) [] (term_var 0)).

(* Under the handle body binder, variable 0 is the freshly allocated cap. *)
Definition bad_handle_body : term :=
  term_perform (term_var 0) [] (term_var 0).

Definition bad_cap (m : marker) : term :=
  term_cap bad_E m 0 [] bad_unit_ty bad_op_body.

Definition bad_source : term :=
  term_handle bad_E 0 [] bad_unit_ty bad_op_body bad_handle_body.

Definition bad_after_handle (m : marker) : term :=
  term_handler_m m bad_unit_ty
    (term_perform (bad_cap m) [] (bad_cap m)).

Definition bad_escaped_perform (m : marker) : term :=
  term_perform (bad_cap m) [] (bad_cap m).

Definition bad_after_perform (m : marker) : term :=
  term_app (term_lam bad_unit_v bad_unit_ty) (bad_escaped_perform m).

Lemma bad_cap_value : forall m,
  value (bad_cap m).
Proof.
  intros m. unfold bad_cap. constructor.
Qed.

Lemma bad_source_allocates_marker :
  bad_source ==> bad_after_handle bad_m.
Proof.
  unfold bad_source, bad_after_handle, bad_handle_body, bad_cap.
  apply S_Handle. simpl. tauto.
Qed.

Lemma bad_handle_performs_and_exposes_escape :
  bad_after_handle bad_m ==> bad_after_perform bad_m.
Proof.
  unfold bad_after_handle, bad_after_perform, bad_escaped_perform, bad_cap.
  apply (S_step EC_hole).
  - constructor.
  - change (term_handler_m bad_m bad_unit_ty
        (term_perform (term_cap bad_E bad_m 0 [] bad_unit_ty bad_op_body) []
           (term_cap bad_E bad_m 0 [] bad_unit_ty bad_op_body)) -->h
      subst_list_tm
        [term_cap bad_E bad_m 0 [] bad_unit_ty bad_op_body;
         term_resume bad_m bad_unit_ty (term_var 0)]
        (subst_list_ty_in_tm [] bad_op_body)).
    apply (H_Perform bad_E bad_m 0 [] bad_unit_ty bad_op_body []
         (term_cap bad_E bad_m 0 [] bad_unit_ty bad_op_body) EC_hole).
    + constructor.
    + constructor.
Qed.

Lemma bad_escaped_perform_no_step : forall t,
  bad_escaped_perform bad_m ==> t -> False.
Proof.
  intros t Hstep.
  unfold bad_escaped_perform in Hstep.
  apply step_perform_inv in Hstep.
  destruct Hstep as [(t1' & Hcap_step & _) | (arg' & _ & Harg_step & _)].
  - eapply no_step_value; [apply bad_cap_value | exact Hcap_step].
  - eapply no_step_value; [apply bad_cap_value | exact Harg_step].
Qed.

Lemma bad_argument_signature_is_local :
  inst_op_arg 0 [] 0 [] bad_cap_ty = bad_cap_ty /\
  no_local_ty (inst_op_arg 0 [] 0 [] bad_cap_ty) = false.
Proof.
  split; reflexivity.
Qed.

Lemma bad_argument_signature_rejected_by_T_Perform :
  no_local_ty (inst_op_arg 0 [] 0 [] bad_cap_ty) = true -> False.
Proof.
  intro H. discriminate H.
Qed.
