Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Context.
Require Import Wf.
Require Import LtSub.
Require Import LtAnalysis.

(* ================================================================== *)
(* Type subtyping                                                     *)
(*                                                                    *)
(* Γ ⊢ S <: T                                                         *)
(*                                                                    *)
(*   SA_Refl    : reflexivity                                         *)
(*   SA_Trans   : transitivity                                        *)
(*   SA_VarCtx  : (α <: B) ∈ Γ → Γ ⊢ α <: B                           *)
(*   SA_Data    : Γ ⊢ₗ l <: l' → Γ ⊢ T l τ̄ <: T l' τ̄                  *)
(*                covariant in lifetime, invariant in type args       *)
(*   SA_Fun     : Γ ⊢ A <: A' (contra) ∧ Γ ⊢ₗ l <: l' (co) ∧          *)
(*                Γ ⊢ B <: B' (co) → Γ ⊢ A' l → B <: A l' → B'        *)
(*                (SubFun — contra domain, co lifetime, co codomain)  *)
(*   SA_LtAll   : (∀l is covariant) body under a fresh bound-local lt *)
(*   SA_TyAll   : F₋<: rule — contra in bound, co in body             *)
(*                Γ ⊢ B' <: B → (α<:B')::Γ ⊢ A <: A' →                *)
(*                  Γ ⊢ ∀(α<:B).A <: ∀(α<:B').A'                      *)
(* ================================================================== *)

Reserved Notation "G '⊢' S '<::' T" (at level 40, S at next level).

Inductive sub : ctx -> type -> type -> Prop :=

  | SA_Refl   : forall Γ T,
      ty_wf Γ T ->
      Γ ⊢ T <:: T

  | SA_Trans  : forall Γ S U T,
      Γ ⊢ S <:: U ->
      Γ ⊢ U <:: T ->
      Γ ⊢ S <:: T

  (* SubCtx: use the bound stored in the context for a type variable *)
  | SA_VarCtx : forall Γ α B,
      ctx_lookup_ty Γ α = Some B ->
      ty_wf Γ B ->
      Γ ⊢ type_var α <:: B

  (* SubData: covariant in the lifetime annotation, invariant in Ts *)
  | SA_Data   : forall Γ K l l' Ts,
      Γ ⊢ₗ l <: l' ->
      types_wf Γ Ts ->
      Γ ⊢ type_ctor K l Ts <:: type_ctor K l' Ts

  (* SubAny: τ <: Any@Δ when all lifetime                              *)
  (* restrictions in τ outlive Δ.                                      *)
  | SA_Any    : forall Γ T Δ,
      ty_wf Γ T ->
      lt_wf Γ Δ ->
      Γ ⊢ₗ lt_of_ty_G Γ T <: Δ ->
      Γ ⊢ T <:: type_ctor any_tag Δ []

  (* SubFun: contravariant in domain type, covariant in closure        *)
  (* lifetime and codomain.  (Paper figure 4, SubFun.)                 *)
  (* Subtype: A' -l-> B   Supertype: A -l'-> B'                        *)
  (* Requires: A <: A' (contra),  l <: l' (co),  B <: B' (co)          *)
  | SA_Fun    : forall Γ A A' l l' B B',
      Γ ⊢ A <:: A' ->
      Γ ⊢ₗ l <: l' ->
      Γ ⊢ B <:: B' ->
      Γ ⊢ type_fun A' l B <:: type_fun A l' B'

  (* type_lt_all is covariant: extend ctx with a fresh lt var          *)
  (* bounded by lt_local (no restriction — any lifetime is allowed)    *)
  | SA_LtAll  : forall Γ A A',
      (bind_lt lt_local :: Γ) ⊢ A <:: A' ->
      Γ ⊢ type_lt_all A <:: type_lt_all A'

  (* Full F<: for bounded type abstraction: distinct, contravariant   *)
  (* bounds — NOT the kernel rule (equal bounds).  With SA_Trans this  *)
  (* makes the subtype relation full F<:, which is undecidable         *)
  (* (Pierce 1992); no complete terminating checker is claimed.        *)
  (* ∀(α<:B).A <: ∀(α<:B').A' when B'<:B (contra) and                  *)
  (* A <: A' under the tighter bound B'.                               *)
  | SA_TyAll  : forall Γ B B' A A',
      ty_wf (bind_ty B :: Γ) A ->
      ty_wf (bind_ty B' :: Γ) A' ->
      Γ ⊢ B' <:: B ->
      (bind_ty B' :: Γ) ⊢ A <:: A' ->
      Γ ⊢ type_ty_all B A <:: type_ty_all B' A'

where "G '⊢' S '<::' T" := (sub G S T).

Hint Constructors sub : core.

(* Regularity: both sides of a subtyping judgment are well-formed.    *)
Lemma sub_wf : forall Γ T1 T2,
  Γ ⊢ T1 <:: T2 -> ty_wf Γ T1 /\ ty_wf Γ T2.
Proof.
  intros Γ T1 T2 H.
  induction H as [Γ T Hwf
                 |Γ S U T HSU IHSU HUT IHUT
                 |Γ α B Hlk HwfB
                 |Γ K l l' Ts Hlt HwfTs
                 |Γ T Δ HwfT HwfD Hlt
                 |Γ A A' l l' B B' HA IHA Hl HB IHB
                 |Γ A A' HAA IHAA
                 |Γ B B' A A' HwfA HwfA' HB IHB HA IHA].
  - split; exact Hwf.
  - destruct IHSU as [HwfS _]. destruct IHUT as [_ HwfT]. split; assumption.
  - split.
    + econstructor; eauto.
    + exact HwfB.
  - destruct (lt_sub_wf _ _ _ Hlt) as [Hwfl Hwfl'].
    split; constructor; assumption.
  - split.
    + exact HwfT.
    + constructor; [exact HwfD|constructor].
  - destruct IHA as [HwfA HwfA'].
    destruct IHB as [HwfB HwfB'].
    destruct (lt_sub_wf _ _ _ Hl) as [Hwfl Hwfl'].
    split; constructor; assumption.
  - destruct IHAA as [HwfA HwfA'].
    split; constructor; assumption.
  - destruct IHB as [HwfB' HwfB].
    split; constructor; assumption.
Qed.
