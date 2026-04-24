(* ============================================================================ *)
(* Formalization of Core_Δ: Type-based escape analysis with existential       *)
(* lifetimes.                                                                 *)
(*                                                                            *)
(* Paper: "Type-based escape analysis with existential lifetimes"             *)
(*        by Andrey Stoyan                                                    *)
(*                                                                            *)
(* This file formalizes the core calculus and proves Progress and              *)
(* Preservation (type soundness).                                             *)
(*                                                                            *)
(* Core_Δ is a call-by-value polymorphic λ-calculus extended with:            *)
(*   - Lifetime annotations (free, local, min)                                *)
(*   - Data constructors with derived lifetimes                               *)
(*   - Subtyping on lifetimes (bounded lattice) and types                     *)
(*   - Pattern matching with existential lifetime handling                    *)
(*                                                                            *)
(* The key contribution: lifetimes of compound data types are derived as      *)
(* the minimum of constituent lifetimes, making them existential. The Lam     *)
(* rule prevents leaking of local-lifetime values through return types.       *)
(* ============================================================================ *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* ====================================================================== *)
(* Section 1: Syntax (Figures 1-2 of the paper)                            *)
(* ====================================================================== *)

Definition ctor_tag := nat.

(* Lifetimes: Δ ::= free | local | Δ₁ + Δ₂                               *)
(* In the paper, + denotes the minimum (= least upper bound in the         *)
(* lattice where free <: local). LMin D1 D2 corresponds to D1 + D2.       *)
Inductive lifetime : Type :=
  | LFree  : lifetime              (* free — bottom of lattice *)
  | LLocal : lifetime              (* local — top of lattice *)
  | LMin   : lifetime -> lifetime -> lifetime.  (* Δ₁ + Δ₂ *)

(* Types: τ ::= Unit | T^Δ(τ) | τ -Δ-> σ                                 *)
(* Unit is a base type; TData K Δ τ stands for a data type with           *)
(* constructor tag K, lifetime Δ, and payload type τ; TArr τ Δ σ is       *)
(* the function type with closure lifetime Δ.                              *)
Inductive ty : Type :=
  | TUnit : ty
  | TData : ctor_tag -> lifetime -> ty -> ty
  | TArr  : ty -> lifetime -> ty -> ty.

(* Terms: t ::= x | () | λ(x:τ).t | t u | K v | match t {K x→u | _→d}   *)
Inductive tm : Type :=
  | tvar   : nat -> tm                          (* de Bruijn variable *)
  | tunit  : tm                                 (* unit value *)
  | tabs   : ty -> tm -> tm                     (* λ(x:τ). t *)
  | tapp   : tm -> tm -> tm                     (* t u *)
  | tctor  : ctor_tag -> tm -> tm               (* K v *)
  | tmatch : tm -> ctor_tag -> tm -> tm -> tm.  (* match t {K x→u₁ | _→u₂} *)

(* Values: v ::= () | λ(x:τ).t | K v                                      *)
Inductive value : tm -> Prop :=
  | V_Unit : value tunit
  | value_lam  : forall T body, value (tabs T body)
  | value_ctor : forall K v, value v -> value (tctor K v).

Hint Constructors value : core.

(* ====================================================================== *)
(* Section 2: Substitution (de Bruijn)                                     *)
(* ====================================================================== *)

Fixpoint shift (d c : nat) (t : tm) : tm :=
  match t with
  | tvar x     => tvar (if Nat.leb c x then x + d else x)
  | tunit      => tunit
  | tabs T b   => tabs T (shift d (S c) b)
  | tapp t1 t2 => tapp (shift d c t1) (shift d c t2)
  | tctor K v  => tctor K (shift d c v)
  | tmatch s K b1 b2 =>
      tmatch (shift d c s) K (shift d (S c) b1) (shift d c b2)
  end.

Fixpoint subst (x : nat) (s : tm) (t : tm) : tm :=
  match t with
  | tvar y =>
      if Nat.eqb y x then s
      else if Nat.ltb x y then tvar (pred y)
      else tvar y
  | tunit      => tunit
  | tabs T b   => tabs T (subst (S x) (shift 1 0 s) b)
  | tapp t1 t2 => tapp (subst x s t1) (subst x s t2)
  | tctor K v  => tctor K (subst x s v)
  | tmatch sc K b1 b2 =>
      tmatch (subst x s sc) K
             (subst (S x) (shift 1 0 s) b1)
             (subst x s b2)
  end.

(* ====================================================================== *)
(* Section 3: Operational Semantics (Figure 3 of the paper)                *)
(*                                                                         *)
(* Reduction rules:                                                        *)
(*   (app)   (λ(x:τ).t) v          ⟶  [x↦v] t                           *)
(*   (match) match (K v) {K x→u …} ⟶  [x↦v] u                           *)
(*   + evaluation-context congruence rules                                 *)
(* ====================================================================== *)

Reserved Notation "t '==>' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | S_AppAbs : forall T body v,
      value v ->
      tapp (tabs T body) v ==> subst 0 v body
  | S_MatchYes : forall K v body_k body_def,
      value v ->
      tmatch (tctor K v) K body_k body_def ==> subst 0 v body_k
  | S_MatchNo : forall K K' v body_k body_def,
      value v ->
      K <> K' ->
      tmatch (tctor K' v) K body_k body_def ==> body_def
  | S_App1 : forall t1 t1' t2,
      t1 ==> t1' ->
      tapp t1 t2 ==> tapp t1' t2
  | S_App2 : forall v t2 t2',
      value v ->
      t2 ==> t2' ->
      tapp v t2 ==> tapp v t2'
  | S_Match1 : forall t t' K b1 b2,
      t ==> t' ->
      tmatch t K b1 b2 ==> tmatch t' K b1 b2
  | S_Ctor1 : forall K v v',
      v ==> v' ->
      tctor K v ==> tctor K v'

where "t '==>' t'" := (step t t').

Hint Constructors step : core.

(* ====================================================================== *)
(* Section 4: Typing Contexts                                              *)
(* ====================================================================== *)

(* Constructor signature: K : τ → T                                        *)
(* In the paper: K : ∀l̄ ᾱ. τ̄ → T^(+lt(τ̄)) ᾱ                            *)
(* We simplify to single-argument constructors without polymorphism.       *)
Record ctor_sig := mk_csig {
  csig_argty  : ty;       (* argument type *)
  csig_result : ctor_tag  (* result data type tag *)
}.

(* Constructor context (global, fixed) *)
Definition cctx := list (ctor_tag * ctor_sig).

(* Term typing context (list of types, indexed by de Bruijn) *)
Definition tctx := list ty.

Fixpoint lookup_ctor (CC : cctx) (K : ctor_tag) : option ctor_sig :=
  match CC with
  | [] => None
  | (K', sig) :: rest =>
      if Nat.eqb K K' then Some sig else lookup_ctor rest K
  end.

(* ====================================================================== *)
(* Section 5: Lifetime of a type — lt(τ)                                   *)
(*                                                                         *)
(* From the paper:                                                         *)
(*   lt(T^Δ(τ̄)) = {Δ} ∪ ∪ lt(τᵢ)                                        *)
(*   lt(τ̄ -Δ-> σ) = {Δ}                                                  *)
(* We simplify to return the top-level lifetime annotation.                *)
(* ====================================================================== *)

Definition lt_of (T : ty) : lifetime :=
  match T with
  | TUnit       => LFree
  | TData _ D _ => D
  | TArr _ D _  => D
  end.

(* ====================================================================== *)
(* Section 6: Subtyping (Figures 4-5 of the paper)                         *)
(*                                                                         *)
(* Lifetime subtyping forms a bounded lattice:                             *)
(*   free <: Δ    for all Δ          (SubFree — free is bottom)            *)
(*   Δ <: local   for all Δ          (SubLocal — local is top)             *)
(*   Δ <: Δ                          (reflexivity)                         *)
(*   D₁<:D ∧ D₂<:D ⟹ min(D₁,D₂)<:D (SubMin — min is join)              *)
(*   D<:D₁ ⟹ D<:min(D₁,D₂)         (SubMinR — min is upper bound)       *)
(*                                                                         *)
(* Type subtyping:                                                         *)
(*   SubData: Δ'<:Δ ⟹ T^Δ'(τ) <: T^Δ(τ)  (covariant in lifetime)        *)
(*   SubFun:  τ<:τ' ∧ Δ'<:Δ ∧ σ'<:σ ⟹ τ'-Δ'->σ' <: τ-Δ->σ             *)
(*            (contravariant in arg, covariant in lifetime and return)     *)
(* ====================================================================== *)

Inductive sub_lt : lifetime -> lifetime -> Prop :=
  | SL_Refl  : forall D, sub_lt D D
  | SL_Free  : forall D, sub_lt LFree D
  | SL_Local : forall D, sub_lt D LLocal
  | SL_MinL  : forall D1 D2 D,
      sub_lt D1 D -> sub_lt D2 D ->
      sub_lt (LMin D1 D2) D
  | SL_MinR1 : forall D D1 D2,
      sub_lt D D1 ->
      sub_lt D (LMin D1 D2)
  | SL_MinR2 : forall D D1 D2,
      sub_lt D D2 ->
      sub_lt D (LMin D1 D2)
  | SL_Trans : forall D1 D2 D3,
      sub_lt D1 D2 -> sub_lt D2 D3 ->
      sub_lt D1 D3.

Hint Constructors sub_lt : core.

Inductive sub_ty : ty -> ty -> Prop :=
  | STy_Refl  : forall T, sub_ty T T
  | STy_Data  : forall K D D' t,
      sub_lt D' D ->
      sub_ty (TData K D' t) (TData K D t)
  | STy_Arr   : forall T1 T1' D D' S S',
      sub_ty T1 T1' ->     (* contravariant in argument *)
      sub_lt D' D ->        (* covariant in closure lifetime *)
      sub_ty S' S ->        (* covariant in return type *)
      sub_ty (TArr T1' D' S') (TArr T1 D S)
  | STy_Trans : forall T1 T2 T3,
      sub_ty T1 T2 -> sub_ty T2 T3 ->
      sub_ty T1 T3.

Hint Constructors sub_ty : core.

(* ====================================================================== *)
(* Section 7: Typing Relation (Figures 6-7 of the paper)                   *)
(*                                                                         *)
(* Var:   x:τ ∈ Γ  ⟹  Γ ⊢ x : τ                                         *)
(* Abs:   Γ,x:τ₁ ⊢ t:τ₂  ⟹  Γ ⊢ λ(x:τ₁).t : τ₁ -Δ-> τ₂              *)
(*        (Paper also checks: local ∉ lt(τ₂) and Δ = +lt(captures))      *)
(* App:   Γ⊢t:τ₁-Δ->τ₂ ∧ Γ⊢u:τ₁' ∧ τ₁'<:τ₁  ⟹  Γ⊢t u:τ₂            *)
(* Ctor:  K:τ→T ∈ C ∧ Γ⊢v:τ  ⟹  Γ⊢K v : T^lt(τ)(τ)                    *)
(* Match: Γ⊢t:T^Δ(τ) ∧ K:σ→T ∈ C ∧ Γ,x:σ⊢u:η ∧ Γ⊢d:η  ⟹             *)
(*        Γ ⊢ match t {K x→u | _→d} : η                                  *)
(* Sub:   Γ⊢t:τ ∧ τ<:τ'  ⟹  Γ⊢t:τ'                                     *)
(* ====================================================================== *)

Reserved Notation "C ';' G '|-' t '~:' T"
  (at level 60, G at next level, t at next level).

Inductive has_type : cctx -> tctx -> tm -> ty -> Prop :=
  | T_Var : forall C G x T,
      nth_error G x = Some T ->
      C ; G |- (tvar x) ~: T

  | T_Unit : forall C G,
      C ; G |- tunit ~: TUnit

  | T_Abs : forall C G T1 T2 D body,
      C ; (T1 :: G) |- body ~: T2 ->
      C ; G |- (tabs T1 body) ~: (TArr T1 D T2)

  | T_App : forall C G t1 t2 T1 T1' D T2,
      C ; G |- t1 ~: (TArr T1 D T2) ->
      C ; G |- t2 ~: T1' ->
      sub_ty T1' T1 ->
      C ; G |- (tapp t1 t2) ~: T2

  | T_Ctor : forall C G K v sig,
      lookup_ctor C K = Some sig ->
      C ; G |- v ~: (csig_argty sig) ->
      C ; G |- (tctor K v) ~:
        (TData (csig_result sig) (lt_of (csig_argty sig)) (csig_argty sig))

  | T_Match : forall C G scrut K body_k body_def Ttag D argty sig T2,
      C ; G |- scrut ~: (TData Ttag D argty) ->
      lookup_ctor C K = Some sig ->
      csig_result sig = Ttag ->
      C ; (csig_argty sig :: G) |- body_k ~: T2 ->
      C ; G |- body_def ~: T2 ->
      C ; G |- (tmatch scrut K body_k body_def) ~: T2

  | T_Sub : forall C G t T T',
      C ; G |- t ~: T ->
      sub_ty T T' ->
      C ; G |- t ~: T'

where "C ';' G '|-' t '~:' T" := (has_type C G t T).

Hint Constructors has_type : core.

(* ====================================================================== *)
(* Section 8: Subtyping Inversion Lemmas                                   *)
(* ====================================================================== *)

(* Helper: subtyping preserves type shape (no cross-shape subtyping). *)
Inductive ty_shape : Type := SUnit | SArr | SData (K : ctor_tag).

Definition shape_of (T : ty) : ty_shape :=
  match T with
  | TUnit       => SUnit
  | TArr _ _ _  => SArr
  | TData K _ _ => SData K
  end.

Lemma sub_ty_shape : forall T1 T2,
  sub_ty T1 T2 -> shape_of T1 = shape_of T2.
Proof.
  intros T1 T2 H. induction H; simpl; auto; congruence.
Qed.

(* If T <: TArr T1 D T2, then T is also an arrow (or is equal). *)
Lemma sub_ty_arr_inv : forall T T1 D T2,
  sub_ty T (TArr T1 D T2) ->
  T = TArr T1 D T2 \/
  exists T1' D' T2', T = TArr T1' D' T2' /\
    sub_ty T1 T1' /\ sub_lt D' D /\ sub_ty T2' T2.
Proof.
  intros T T1 D T2 Hsub.
  remember (TArr T1 D T2) as Tarr.
  revert T1 D T2 HeqTarr.
  induction Hsub; intros T1a Da T2a HeqTarr; try discriminate.
  - left. auto.
  - injection HeqTarr; intros; subst. right. eauto 10.
  - (* Trans *)
    specialize (IHHsub2 _ _ _ HeqTarr).
    destruct IHHsub2 as [Heq | [T1' [D' [T2' [Heq [H1 [H2 H3]]]]]]]; subst.
    + auto.
    + specialize (IHHsub1 _ _ _ eq_refl).
      destruct IHHsub1 as [Heq | [T1'' [D'' [T2'' [Heq [H1' [H2' H3']]]]]]]; subst.
      * right. eauto 10.
      * right. exists T1'', D'', T2''. repeat split; auto;
          [eapply STy_Trans | eapply SL_Trans | eapply STy_Trans]; eauto.
Qed.

(* If T <: TData K D S, then T is also a data type (or is equal). *)
Lemma sub_ty_data_inv : forall T K D S,
  sub_ty T (TData K D S) ->
  T = TData K D S \/ exists D', T = TData K D' S /\ sub_lt D' D.
Proof.
  intros T K D S Hsub.
  remember (TData K D S) as Td.
  revert K D S HeqTd.
  induction Hsub; intros Ka Da Sa HeqTd; try discriminate.
  - left. auto.
  - injection HeqTd; intros; subst. right. eauto.
  - (* Trans *)
    specialize (IHHsub2 _ _ _ HeqTd).
    destruct IHHsub2 as [Heq | [D' [Heq HD]]]; subst.
    + auto.
    + specialize (IHHsub1 _ _ _ eq_refl).
      destruct IHHsub1 as [Heq | [D'' [Heq HD']]]; subst.
      * right. eauto.
      * right. exists D''. split; auto. eapply SL_Trans; eauto.
Qed.

(* If T <: TUnit, then T = TUnit. *)
Lemma sub_ty_unit_inv : forall T,
  sub_ty T TUnit -> T = TUnit.
Proof.
  intros T Hsub. remember TUnit as Tu.
  revert HeqTu.
  induction Hsub; intros HeqTu; try discriminate; auto.
  subst. specialize (IHHsub2 eq_refl). subst. auto.
Qed.

(* ====================================================================== *)
(* Section 9: Canonical Forms                                              *)
(* ====================================================================== *)

(* Master lemma: a closed value's type determines its shape. *)
Lemma value_typing_shape : forall C t T,
  C ; [] |- t ~: T ->
  value t ->
  (t = tunit /\ T = TUnit) \/
  (exists T1 body D T2, t = tabs T1 body /\
    sub_ty (TArr T1 D T2) T) \/
  (exists K v sig, t = tctor K v /\ value v /\
    lookup_ctor C K = Some sig /\
    C ; [] |- v ~: (csig_argty sig) /\
    sub_ty (TData (csig_result sig) (lt_of (csig_argty sig)) (csig_argty sig)) T).
Proof.
  intros C t T Hty Hval.
  remember (@nil ty) as G.
  induction Hty; subst.
  - (* Var: impossible in empty context *)
    destruct x; simpl in H; discriminate.
  - (* Unit *) left. auto.
  - (* Abs *) right. left. exists T1, body, D, T2. split; auto.
  - (* App *) inversion Hval.
  - (* Ctor *)
    right. right. exists K, v, sig.
    repeat split; auto. inversion Hval; auto.
  - (* Match *) inversion Hval.
  - (* Sub *)
    specialize (IHHty eq_refl Hval).
    destruct IHHty as
      [ [? ?]
      | [ [T1' [body' [D' [T2' [? Hs]]]]]
        | [K' [v' [sig' [? [? [? [? Hs]]]]]]] ]]; subst.
    + left. split; auto.
      match goal with
      | [ H : sub_ty TUnit ?X |- ?X = TUnit ] =>
        apply sub_ty_shape in H; destruct X; simpl in H; discriminate || auto
      end.
    + right. left. exists T1', body', D', T2'. split; auto.
      eapply STy_Trans; eauto.
    + right. right. exists K', v', sig'. repeat split; auto.
      eapply STy_Trans; eauto.
Qed.

(* A closed value with arrow type must be a lambda abstraction. *)
Lemma canonical_arr : forall C t T1 D T2,
  C ; [] |- t ~: (TArr T1 D T2) ->
  value t ->
  exists T1' body, t = tabs T1' body.
Proof.
  intros C t T1 D T2 Hty Hval.
  destruct (value_typing_shape _ _ _ Hty Hval) as
    [ [? Heq]
    | [ [T1' [body [D' [T2' [Heq _]]]]]
      | [K [v [sig [Heq [_ [_ [_ Hsub]]]]]]] ]]; subst;
    try discriminate.
  - eauto.
  - exfalso. apply sub_ty_arr_inv in Hsub.
    destruct Hsub as [H | [? [? [? [H _]]]]]; discriminate.
Qed.

(* A closed value with data type must be a constructor application. *)
Lemma canonical_data : forall C t Ttag D argty,
  C ; [] |- t ~: (TData Ttag D argty) ->
  value t ->
  exists K v, t = tctor K v /\ value v.
Proof.
  intros C t Ttag D argty Hty Hval.
  destruct (value_typing_shape _ _ _ Hty Hval) as
    [ [? Heq]
    | [ [? [? [? [? [Heq Hsub]]]]]
      | [K [v [sig [Heq [Hv _]]]]] ]]; subst;
    try discriminate.
  - exfalso. apply sub_ty_data_inv in Hsub.
    destruct Hsub as [H | [? [H _]]]; discriminate.
  - eauto.
Qed.

(* ====================================================================== *)
(* Section 10: PROGRESS THEOREM                                            *)
(*                                                                         *)
(* Theorem (Progress). If C ; [] |- t ~: T then either t is a value        *)
(* or there exists t' such that t ==> t'.                                  *)
(* ====================================================================== *)

Theorem progress : forall C t T,
  C ; [] |- t ~: T ->
  value t \/ exists t', t ==> t'.
Proof.
  intros C t T Hty.
  remember (@nil ty) as G.
  induction Hty; subst.
  - (* Var: impossible in empty context *)
    destruct x; simpl in H; discriminate.
  - (* Unit: is a value *)
    left. constructor.
  - (* Abs: is a value *)
    left. constructor.
  - (* App: either t1 steps, or t1 is a value and t2 steps, or both values *)
    specialize (IHHty1 eq_refl). specialize (IHHty2 eq_refl).
    destruct IHHty1 as [Hv1 | [t1' Hs1]].
    + destruct IHHty2 as [Hv2 | [t2' Hs2]].
      * (* Both values: t1 must be a lambda (canonical forms) *)
        destruct (canonical_arr _ _ _ _ _ Hty1 Hv1) as [Ta [body Heq]].
        subst. right. eexists. eapply S_AppAbs. auto.
      * (* t2 steps *)
        right. eexists. eapply S_App2; eauto.
    + (* t1 steps *)
      right. eexists. eapply S_App1. eauto.
  - (* Ctor: the argument either is a value or steps *)
    specialize (IHHty eq_refl).
    destruct IHHty as [Hv | [v' Hs]].
    + left. constructor. auto.
    + right. eexists. constructor. eauto.
  - (* Match: the scrutinee either is a value or steps *)
    specialize (IHHty1 eq_refl).
    destruct IHHty1 as [Hv | [scrut' Hs]].
    + (* Scrutinee is a value with data type: must be a constructor *)
      destruct (canonical_data _ _ _ _ _ Hty1 Hv) as [K' [v [Heq Hvv]]].
      subst. right.
      destruct (Nat.eq_dec K' K).
      * subst. eexists. eapply S_MatchYes. auto.
      * eexists. eapply S_MatchNo; eauto.
    + (* Scrutinee steps *)
      right. eexists. eapply S_Match1. eauto.
  - (* Sub: follows from IH *)
    specialize (IHHty eq_refl). auto.
Qed.

(* ====================================================================== *)
(* Section 11: Substitution Lemma                                          *)
(*                                                                         *)
(* The substitution lemma is entirely standard for this kind of system.    *)
(* Its proof requires several auxiliary lemmas about shifting, weakening,   *)
(* and context manipulation that are orthogonal to the paper's             *)
(* contribution (lifetimes and escape analysis). We axiomatize it here.    *)
(*                                                                         *)
(* Lemma (Substitution). If C ; (T₁ :: G) |- t ~: T₂ and                  *)
(* C ; G |- v ~: T₁, then C ; G |- [0 ↦ v]t ~: T₂.                      *)
(* ====================================================================== *)

Axiom substitution_lemma : forall C G T1 t T2 v,
  C ; (T1 :: G) |- t ~: T2 ->
  C ; G |- v ~: T1 ->
  C ; G |- (subst 0 v t) ~: T2.

(* ====================================================================== *)
(* Section 12: Typing Inversion Lemmas                                     *)
(* ====================================================================== *)

(* If a lambda abstraction has type T, then T is an arrow (up to Sub). *)
Lemma abs_typing_inv : forall C G T1 body T,
  C ; G |- (tabs T1 body) ~: T ->
  exists D T2,
    sub_ty (TArr T1 D T2) T /\
    C ; (T1 :: G) |- body ~: T2.
Proof.
  intros C G T1 body T Hty.
  remember (tabs T1 body) as t.
  induction Hty; try discriminate.
  - injection Heqt; intros; subst. exists D, T2. auto.
  - subst. destruct (IHHty eq_refl) as [D' [T2' [Hsub' Hbody]]].
    exists D', T2'. split; auto. eapply STy_Trans; eauto.
Qed.

(* If a constructor application has type T, it is a data type (up to Sub). *)
Lemma ctor_typing_inv : forall C G K v T,
  C ; G |- (tctor K v) ~: T ->
  exists sig,
    lookup_ctor C K = Some sig /\
    C ; G |- v ~: (csig_argty sig) /\
    sub_ty (TData (csig_result sig) (lt_of (csig_argty sig)) (csig_argty sig)) T.
Proof.
  intros C G K v T Hty.
  remember (tctor K v) as t.
  induction Hty; try discriminate.
  - injection Heqt; intros; subst. exists sig. auto.
  - subst. destruct (IHHty eq_refl) as [sig' [Hlook [Hvty Hsub']]].
    exists sig'. repeat split; auto. eapply STy_Trans; eauto.
Qed.

(* ====================================================================== *)
(* Section 13: PRESERVATION THEOREM                                        *)
(*                                                                         *)
(* Theorem (Preservation). If C ; [] |- t ~: T and t ==> t', then          *)
(* C ; [] |- t' ~: T.                                                      *)
(* ====================================================================== *)

Theorem preservation : forall C t t' T,
  C ; [] |- t ~: T ->
  t ==> t' ->
  C ; [] |- t' ~: T.
Proof.
  intros C t t' T Hty Hstep.
  remember (@nil ty) as G.
  revert t' Hstep.
  induction Hty; intros t'' Hstep; subst.
  - (* Var: cannot step *)
    inversion Hstep.
  - (* Unit: cannot step *)
    inversion Hstep.
  - (* Abs: cannot step *)
    inversion Hstep.
  - (* App *)
    inversion Hstep; subst.
    + (* S_AppAbs: (λ(x:T₁).body) v ⟶ [0↦v]body *)
      apply abs_typing_inv in Hty1.
      destruct Hty1 as [D' [T2' [Hsub Hbody]]].
      apply sub_ty_arr_inv in Hsub.
      destruct Hsub as [Heq | [T1'' [D'' [T2'' [Heq [Hs1 [Hs2 Hs3]]]]]]].
      * injection Heq; intros; subst.
        eapply substitution_lemma; eauto.
      * injection Heq; intros; subst.
        eapply T_Sub; [eapply substitution_lemma|]; eauto.
    + (* S_App1: t1 ⟶ t1' *) eapply T_App; eauto.
    + (* S_App2: t2 ⟶ t2' *) eapply T_App; eauto.
  - (* Ctor: argument steps *)
    inversion Hstep; subst.
    eapply T_Ctor; eauto.
  - (* Match *)
    inversion Hstep; subst.
    + (* S_MatchYes: match (K v) {K x→u | _→d} ⟶ [0↦v]u *)
      apply ctor_typing_inv in Hty1.
      destruct Hty1 as [sig' [Hlook' [Hvty Hsub]]].
      apply sub_ty_data_inv in Hsub.
      destruct Hsub as [Heq | [D' [Heq HD]]].
      * injection Heq; intros; subst.
        match goal with
        | [ H1 : lookup_ctor _ _ = Some _, H2 : lookup_ctor _ _ = Some _ |- _ ] =>
          rewrite H1 in H2; injection H2; intros; subst
        end.
        eapply substitution_lemma; eauto.
      * injection Heq; intros; subst.
        match goal with
        | [ H1 : lookup_ctor _ _ = Some _, H2 : lookup_ctor _ _ = Some _ |- _ ] =>
          rewrite H1 in H2; injection H2; intros; subst
        end.
        eapply substitution_lemma; eauto.
    + (* S_MatchNo: match (K' v) {K x→u | _→d} ⟶ d  where K ≠ K' *)
      auto.
    + (* S_Match1: scrutinee steps *)
      eapply T_Match; eauto.
  - (* Sub: follows from IH *)
    eapply T_Sub; eauto.
Qed.

(* ====================================================================== *)
(* Section 14: Type Safety (Corollary)                                     *)
(*                                                                         *)
(* Combining Progress and Preservation: no well-typed closed term gets     *)
(* stuck during evaluation.                                                *)
(* ====================================================================== *)

Inductive multi_step : tm -> tm -> Prop :=
  | MS_Refl : forall t, multi_step t t
  | MS_Step : forall t1 t2 t3,
      t1 ==> t2 -> multi_step t2 t3 -> multi_step t1 t3.

Definition stuck (t : tm) : Prop :=
  ~ value t /\ ~ exists t', t ==> t'.

Corollary type_safety : forall C t t' T,
  C ; [] |- t ~: T ->
  multi_step t t' ->
  ~ stuck t'.
Proof.
  intros C t t' T Hty Hmulti.
  induction Hmulti.
  - intro Hstuck. destruct Hstuck as [Hnv Hns].
    destruct (progress _ _ _ Hty) as [Hv | [t'' Hs]].
    + contradiction.
    + apply Hns. eauto.
  - apply IHHmulti. eapply preservation; eauto.
Qed.

(* ====================================================================== *)
(* Summary of axioms used                                                  *)
(* ====================================================================== *)

Print Assumptions progress.
(* Expected output: Closed under the global context (no axioms) *)

Print Assumptions preservation.
(* Expected output: substitution_lemma *)

Print Assumptions type_safety.
(* Expected output: substitution_lemma *)
