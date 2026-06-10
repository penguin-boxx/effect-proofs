(* ================================================================== *)
(* Mechanized refutation of the axiom `ctor_lts_chain_bounded`.        *)
(*                                                                    *)
(* The axiom concludes (4th conjunct):                                *)
(*     Forall (fun l => Γ |-l l <: Delta') lts                        *)
(* i.e. EVERY lifetime argument of a constructor is bounded by Delta'.*)
(* Its only hypotheses are: the fields type-check, |lts|=n_lt,         *)
(*   Delta = lt_of_ty_list (instantiated field types), Delta <: Delta'.*)
(*                                                                    *)
(* But `lt_of_ty (type_fun _ l _) = l` IGNORES the domain/codomain.   *)
(* So a schema lt-variable that appears ONLY in a function-DOMAIN      *)
(* position is invisible to `Delta = lt_of_ty_list ...`, yet it may    *)
(* be instantiated with `lt_local`.  Then Delta = lt_free, Delta' may  *)
(* be lt_free, and the 4th conjunct demands `lt_local <: lt_free`,     *)
(* which is FALSE.  (Same root issue as the other capture/no-local     *)
(* leaks: a syntactic lifetime aggregate under-approximates locals     *)
(* hidden in a contravariant position.)                               *)
(* ================================================================== *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import SubstitutionTheory.
Require Import Safety.

(* ------------------------------------------------------------------ *)
(* Concrete witnesses                                                 *)
(* ------------------------------------------------------------------ *)
Definition Kc : ctor_tag := 1.                       (* a non-`any` tag *)
Definition Cap : type := type_ctor Kc lt_local [].   (* local capability *)
Definition Res : type := type_ctor Kc lt_free [].    (* no-local result  *)

(* A one-field schema whose single lt-binder (lt_var 0) appears ONLY   *)
(* in the DOMAIN of a function field -- invisible to lt_of_ty.         *)
Definition field : type :=
  type_fun (type_ctor Kc (lt_var 0) []) lt_free Res.

(* Outer context provides a Res-typed variable to inhabit the codomain.*)
Definition Gz : ctx := [bind_tm Res].

(* v = lambda whose parameter is `Cap` (the instantiated domain) and   *)
(* whose body returns the outer Res variable (index 1 under the lam).  *)
Definition vlam : term := term_lam (term_var 1) Cap.

Lemma vlam_typed :
  Gz ⊢ₜ vlam : inst_ctor_type 1 0 [lt_local] [] field.
Proof.
  unfold vlam, Gz, field, Cap, Res.
  cbn [inst_ctor_type inst_lt_vars inst_ty_vars multi_subst_lt_in_ty
       multi_subst_lt Nat.ltb Nat.leb Nat.sub List.length List.nth shift_lt].
  apply T_Lam.
  - unfold Cap. repeat constructor.
  - unfold Res. repeat constructor.
  - apply T_Var.
    + reflexivity.
    + unfold Res. repeat constructor.
  - cbn. repeat (apply LS_MinL || apply LS_Free || constructor).
Qed.

Lemma Gz_no_lt : forall x, ctx_lookup_lt Gz x = None.
Proof.
  intros x. reflexivity.
Qed.

Lemma lt_sub_no_local_mono_no_lt : forall Γ l1 l2,
  (forall x, ctx_lookup_lt Γ x = None) ->
  Γ ⊢ₗ l1 <: l2 ->
  no_local_lt l2 = true ->
  no_local_lt l1 = true.
Proof.
  intros Γ l1 l2 Hnone H. induction H; intros Hsup; simpl in *.
  - reflexivity.
  - discriminate Hsup.
  - rewrite Hnone in H. discriminate.
  - exact Hsup.
  - apply IHlt_sub1; [exact Hnone|].
    apply IHlt_sub2; [exact Hnone|exact Hsup].
  - rewrite (IHlt_sub1 Hnone Hsup). rewrite (IHlt_sub2 Hnone Hsup). reflexivity.
  - apply IHlt_sub; [exact Hnone|].
    destruct (no_local_lt l1) eqn:E1; simpl in Hsup; [reflexivity | discriminate].
  - apply IHlt_sub; [exact Hnone|].
    destruct (no_local_lt l2) eqn:E2;
      [reflexivity | destruct (no_local_lt l1); simpl in Hsup; discriminate].
Qed.

(* ------------------------------------------------------------------ *)
(* The 4th conjunct fails: lt_local is not bounded by Delta' = lt_free. *)
(* ------------------------------------------------------------------ *)
Theorem ctor_lts_chain_bounded_is_false :
  ~ (forall Γ lts n_lt n_ty Ts sigma vs Delta Delta',
        Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs
                (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma) ->
        List.length lts = n_lt ->
        Delta = lt_of_ty_list (List.map (inst_ctor_type n_lt n_ty lts Ts) sigma) ->
        Γ ⊢ₗ Delta <: Delta' ->
        chain_bounded Γ lts (shift_lt n_lt 0 Delta') /\
        chain_bounded Γ (shift_each_lt lts) (shift_lt n_lt 0 Delta') /\
        Forall (ctor_field_bounded_ty n_lt)
               (List.map (inst_ty_vars n_ty Ts) sigma) /\
        Forall (fun l => Γ ⊢ₗ l <: Delta') lts).
Proof.
  intros Hax.
  assert (Hforall2 : Forall2 (fun v rho => Gz ⊢ₜ v : rho) [vlam]
                       (List.map (inst_ctor_type 1 0 [lt_local] []) [field])).
  { cbn [List.map]. apply Forall2_cons; [ exact vlam_typed | apply Forall2_nil ]. }
  assert (Hsub : Gz ⊢ₗ lt_min lt_free lt_free <: lt_free).
  { apply LS_MinL; apply LS_Free; constructor. }
  pose proof (Hax Gz [lt_local] 1 0 [] [field] [vlam]
                  (lt_min lt_free lt_free) lt_free
                  Hforall2 eq_refl eq_refl Hsub) as Hconj.
  destruct Hconj as [_ [_ [_ H4]]].
  inversion H4 as [| ? ? Hlocal _]; subst.
  pose proof (lt_sub_no_local_mono_no_lt _ _ _ Gz_no_lt Hlocal eq_refl) as Hbad.
  cbn in Hbad. discriminate Hbad.
Qed.
