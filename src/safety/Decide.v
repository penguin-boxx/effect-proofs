Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import Subst.
Require Import Narrowing.
Require Import Eqb.

(* ================================================================== *)
(*                                                                    *)
(*        REFLECTED DECISION PROCEDURES FOR THE STATIC CHECKS         *)
(*                                                                    *)
(* The typing rules' escape checks are lattice judgments              *)
(* `Γ ⊢ₗ lt_of_ty_G Γ T <: lt_free`, not boolean computations.  This  *)
(* file provides certified deciders for the judgments the paper       *)
(* advertises as decidable:                                           *)
(*                                                                    *)
(*   lt_subb  Γ l r   decides   Γ ⊢ₗ l <: r        (lt_subb_spec)     *)
(*   nolocb   Γ T     decides   Γ ⊢ₗ lt_of_ty_G Γ T <: lt_free        *)
(*                                                   (nolocb_spec)    *)
(*   valueb   t       decides   value t            (valueb_spec)      *)
(*   sourceb  t       decides   has_rt_marker t = false                  *)
(*                                                   (sourceb_spec)   *)
(*                                                                    *)
(* The lattice decider works in three layers:                         *)
(*  1. [lt_le], a CUT-FREE inductive characterization of lifetime     *)
(*     subtyping: the left side is decomposed into its atoms          *)
(*     (lt_join is the lattice join), and an atom lies below [r] iff   *)
(*     it is [lt_free], occurs among [r]'s atoms, [lt_local] occurs   *)
(*     among [r]'s atoms, or (for a variable) its context bound lies  *)
(*     below [r].  Admissibility of transitivity ([lt_le_trans]) is   *)
(*     the little cut-elimination theorem making [lt_le] equivalent   *)
(*     to [lt_sub] ([lt_le_iff]).                                     *)
(*  2. [atom_leb]/[lt_leb], a fuel-indexed boolean implementation of  *)
(*     [lt_le].  Fuel is consumed ONLY when chasing a variable's      *)
(*     bound.  Because [ctx_lookup_lt] shifts every bound it returns  *)
(*     past the binders it traverses, the variables of a looked-up    *)
(*     bound are STRICTLY ABOVE the variable being looked up          *)
(*     ([ctx_lookup_lt_occurs_above]), so bound-chains have length    *)
(*     at most [ctx_lt_count Γ] and that fixed fuel is complete for   *)
(*     EVERY context — no well-formedness of Γ needed.                *)
(*  3. [lt_subb := lt_leb (ctx_lt_count Γ)], with soundness           *)
(*     conditional only on [lt_ctx_wf] (looked-up bounds are wf —     *)
(*     vacuous under [eval_ctx], which has no lifetime binders).      *)
(* ================================================================== *)

(* Decidable equality of lifetimes ([lt_eqb]/[lt_eqb_spec]) lives in  *)
(* Eqb.v.                                                             *)

(* ------------------------------------------------------------------ *)
(* Atoms: flattening the joins                                        *)
(* ------------------------------------------------------------------ *)

Fixpoint lt_atoms (l : lifetime) : list lifetime :=
  match l with
  | lt_join l1 l2 => lt_atoms l1 ++ lt_atoms l2
  | a => [a]
  end.

(* Elements of an atom list are themselves atomic.                    *)
Lemma lt_atoms_atom : forall r a,
  In a (lt_atoms r) -> lt_atoms a = [a].
Proof.
  induction r; simpl; intros a Hin;
    try (destruct Hin as [<-|[]]; reflexivity).
  apply in_app_or in Hin; destruct Hin; auto.
Qed.

Lemma lt_atoms_no_min : forall l a1 a2,
  ~ In (lt_join a1 a2) (lt_atoms l).
Proof.
  induction l; simpl; intros a1 a2 Hin;
    try (destruct Hin as [Heq|[]]; discriminate).
  apply in_app_or in Hin; destruct Hin; [eapply IHl1 | eapply IHl2]; eauto.
Qed.

Definition lt_memb (a r : lifetime) : bool :=
  existsb (lt_eqb a) (lt_atoms r).

Lemma lt_memb_true_in : forall a r,
  lt_memb a r = true -> In a (lt_atoms r).
Proof.
  intros a r H. unfold lt_memb in H.
  apply existsb_exists in H. destruct H as [b [Hb Heq]].
  destruct (lt_eqb_spec a b); [subst; exact Hb | discriminate].
Qed.

Lemma lt_memb_in_true : forall a r,
  In a (lt_atoms r) -> lt_memb a r = true.
Proof.
  intros a r Hin. unfold lt_memb.
  apply existsb_exists. exists a. split; [exact Hin|].
  destruct (lt_eqb_spec a a); [reflexivity | congruence].
Qed.

(* ------------------------------------------------------------------ *)
(* The cut-free characterization                                      *)
(* ------------------------------------------------------------------ *)

Inductive lt_le (Γ : ctx) : lifetime -> lifetime -> Prop :=
  | LL_Free  : forall r,
      lt_le Γ lt_free r
  | LL_Join   : forall l1 l2 r,
      lt_le Γ l1 r ->
      lt_le Γ l2 r ->
      lt_le Γ (lt_join l1 l2) r
  (* reflexivity at the atoms: an atom below any join containing it *)
  | LL_Mem   : forall a r,
      In a (lt_atoms r) ->
      lt_le Γ a r
  (* local is the top: anything is below a join containing local *)
  | LL_Top   : forall l r,
      In lt_local (lt_atoms r) ->
      lt_le Γ l r
  (* chase a variable's declared bound *)
  | LL_Bound : forall x Δ r,
      ctx_lookup_lt Γ x = Some Δ ->
      lt_wf Γ Δ ->
      lt_le Γ Δ r ->
      lt_le Γ (lt_var x) r.

(* Local: [lt_le] is an internal artefact of the decider; its         *)
(* constructors must not leak into the global hint database of every  *)
(* downstream file.                                                   *)
#[local] Hint Constructors lt_le : core.

(* Right-monotonicity: growing the right-hand atom set preserves      *)
(* everything (this is what LS_JoinR1/LS_JoinR2 become, cut-free).      *)
Lemma lt_le_r_mono : forall Γ l r r',
  lt_le Γ l r ->
  incl (lt_atoms r) (lt_atoms r') ->
  lt_le Γ l r'.
Proof.
  intros Γ l r r' H Hincl; induction H; eauto using lt_le.
Qed.

Lemma lt_le_refl : forall Γ l, lt_le Γ l l.
Proof.
  intros Γ l; induction l;
    try (apply LL_Mem; simpl; auto; fail).
  apply LL_Join.
  - eapply lt_le_r_mono; [exact IHl1|].
    intros a Ha; simpl; apply in_or_app; auto.
  - eapply lt_le_r_mono; [exact IHl2|].
    intros a Ha; simpl; apply in_or_app; auto.
Qed.

(* A derivation for [u] yields a derivation for each of [u]'s atoms.  *)
Lemma lt_le_atoms : forall Γ u r,
  lt_le Γ u r ->
  forall a, In a (lt_atoms u) -> lt_le Γ a r.
Proof.
  intros Γ u r H; induction H; simpl; intros b Hb.
  - destruct Hb as [<-|[]]; apply LL_Free.
  - apply in_app_or in Hb; destruct Hb; auto.
  - rewrite (lt_atoms_atom _ _ H) in Hb.
    destruct Hb as [<-|[]]; apply LL_Mem; exact H.
  - apply LL_Top; exact H.
  - destruct Hb as [<-|[]]; eapply LL_Bound; eauto.
Qed.

(* Only membership of local can put local below r.                    *)
Lemma lt_le_local_inv : forall Γ r,
  lt_le Γ lt_local r -> In lt_local (lt_atoms r).
Proof.
  intros Γ r H; inversion H; subst; assumption.
Qed.

(* Cut elimination: transitivity is admissible.  Induction on the     *)
(* LEFT derivation; the right side of any [lt_le] derivation is       *)
(* invariant, so [lt_le_atoms] discharges the membership cases.       *)
Lemma lt_le_trans : forall Γ l u r,
  lt_le Γ l u -> lt_le Γ u r -> lt_le Γ l r.
Proof.
  intros Γ l u r H; revert r; induction H; intros r' Hur;
    eauto using lt_le.
  - (* LL_Mem: l is an atom of u *)
    eapply lt_le_atoms; eauto.
  - (* LL_Top: local is an atom of u, hence local ≤ r', hence top *)
    apply LL_Top. eapply lt_le_local_inv.
    eapply lt_le_atoms; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Equivalence with the declarative judgment                          *)
(* ------------------------------------------------------------------ *)

(* An atom of a wf lifetime is declaratively below it (via MinR).     *)
Lemma lt_atoms_in_sub : forall Γ r a,
  lt_wf Γ r ->
  In a (lt_atoms r) ->
  Γ ⊢ₗ a <: r.
Proof.
  induction r; simpl; intros a Hwf Hin;
    try (destruct Hin as [<-|[]]; apply LS_Refl; assumption).
  inversion Hwf; subst.
  apply in_app_or in Hin; destruct Hin.
  - apply LS_JoinR1; auto.
  - apply LS_JoinR2; auto.
Qed.

Lemma lt_le_sound : forall Γ l r,
  lt_le Γ l r ->
  lt_wf Γ l ->
  lt_wf Γ r ->
  Γ ⊢ₗ l <: r.
Proof.
  intros Γ l r H; induction H; intros Hwfl Hwfr.
  - apply LS_Free; exact Hwfr.
  - inversion Hwfl; subst. apply LS_JoinL; auto.
  - apply lt_atoms_in_sub; assumption.
  - eapply LS_Trans; [apply LS_Local; exact Hwfl|].
    apply lt_atoms_in_sub; assumption.
  - eapply LS_Trans; [eapply LS_Var; eauto|]. auto.
Qed.

Lemma lt_sub_lt_le : forall Γ l r,
  Γ ⊢ₗ l <: r -> lt_le Γ l r.
Proof.
  intros Γ l r H; induction H.
  - apply LL_Free.
  - apply LL_Top; simpl; auto.
  - eapply LL_Bound; eauto using lt_le_refl.
  - apply lt_le_refl.
  - eapply lt_le_trans; eauto.
  - apply LL_Join; auto.
  - eapply lt_le_r_mono; [exact IHlt_sub|].
    intros a Ha; simpl; apply in_or_app; auto.
  - eapply lt_le_r_mono; [exact IHlt_sub|].
    intros a Ha; simpl; apply in_or_app; auto.
Qed.

(* PUBLIC API — terminal deliverable: no internal consumers; do not
   mistake for dead code.  Gated by scripts/check_assumptions.py. *)
Theorem lt_le_iff : forall Γ l r,
  lt_wf Γ l ->
  lt_wf Γ r ->
  (lt_le Γ l r <-> Γ ⊢ₗ l <: r).
Proof.
  intros; split;
    [intro; apply lt_le_sound | intro; apply lt_sub_lt_le]; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* The boolean implementation                                         *)
(* ------------------------------------------------------------------ *)

(* Fuel is consumed only when chasing a variable's bound; all other   *)
(* work is structural.  [lt_join] is never reached: [lt_leb] feeds     *)
(* only atoms.                                                        *)
Fixpoint atom_leb (fuel : nat) (Γ : ctx) (a r : lifetime) {struct fuel} : bool :=
  match a with
  | lt_free      => true
  | lt_local     => lt_memb lt_local r
  | lt_var x     =>
      lt_memb lt_local r || lt_memb (lt_var x) r ||
      match fuel, ctx_lookup_lt Γ x with
      | S fuel', Some Δ =>
          forallb (fun a' => atom_leb fuel' Γ a' r) (lt_atoms Δ)
      | _, _ => false
      end
  | lt_join _ _   => false
  end.

Definition lt_leb (fuel : nat) (Γ : ctx) (l r : lifetime) : bool :=
  forallb (fun a => atom_leb fuel Γ a r) (lt_atoms l).

(* [atom_leb] is a fixpoint on fuel, so it does not reduce while fuel *)
(* is abstract; these unfolding equations restore the view by shape.  *)
Lemma atom_leb_free : forall fuel Γ r, atom_leb fuel Γ lt_free r = true.
Proof. destruct fuel; reflexivity. Qed.

Lemma atom_leb_local : forall fuel Γ r,
  atom_leb fuel Γ lt_local r = lt_memb lt_local r.
Proof. destruct fuel; reflexivity. Qed.

Lemma atom_leb_var : forall fuel Γ x r,
  atom_leb fuel Γ (lt_var x) r
  = (lt_memb lt_local r || lt_memb (lt_var x) r ||
     match fuel, ctx_lookup_lt Γ x with
     | S fuel', Some Δ =>
         forallb (fun a' => atom_leb fuel' Γ a' r) (lt_atoms Δ)
     | _, _ => false
     end).
Proof. destruct fuel; reflexivity. Qed.

(* Rebuild a full derivation from per-atom derivations.               *)
Lemma lt_le_from_atoms : forall Γ l r,
  (forall a, In a (lt_atoms l) -> lt_le Γ a r) ->
  lt_le Γ l r.
Proof.
  induction l; simpl; intros r H;
    try (apply H; simpl; auto; fail).
  apply LL_Join; [apply IHl1 | apply IHl2];
    intros a Ha; apply H; apply in_or_app; auto.
Qed.

(* Contexts whose stored lifetime bounds are themselves wf.  Vacuous  *)
(* under [eval_ctx] (no lifetime binders at all); holds for any       *)
(* context built by the typing rules.                                 *)
Definition lt_ctx_wf (Γ : ctx) : Prop :=
  forall x Δ, ctx_lookup_lt Γ x = Some Δ -> lt_wf Γ Δ.

Lemma eval_ctx_lt_ctx_wf : forall Γ, eval_ctx Γ -> lt_ctx_wf Γ.
Proof.
  intros Γ Hec x Δ Hlk.
  rewrite (eval_ctx_no_lt _ x Hec) in Hlk. discriminate.
Qed.

Lemma atom_leb_sound : forall fuel Γ a r,
  lt_ctx_wf Γ ->
  atom_leb fuel Γ a r = true ->
  lt_le Γ a r.
Proof.
  induction fuel as [|fuel IH]; intros Γ a r Hctx H; destruct a; simpl in H;
    try discriminate;
    try apply LL_Free;
    try (apply LL_Top; apply lt_memb_true_in; exact H).
  - (* fuel = 0, lt_var: the bound branch is dead *)
    apply orb_true_iff in H; destruct H as [H|H].
    + apply orb_true_iff in H; destruct H as [H|H].
      * apply LL_Top; apply lt_memb_true_in; exact H.
      * apply LL_Mem; apply lt_memb_true_in; exact H.
    + destruct (ctx_lookup_lt Γ n); discriminate.
  - (* fuel = S fuel', lt_var *)
    apply orb_true_iff in H; destruct H as [H|H].
    + apply orb_true_iff in H; destruct H as [H|H].
      * apply LL_Top; apply lt_memb_true_in; exact H.
      * apply LL_Mem; apply lt_memb_true_in; exact H.
    + destruct (ctx_lookup_lt Γ n) as [Δ|] eqn:Hlk; [|discriminate].
      eapply LL_Bound; [exact Hlk | exact (Hctx _ _ Hlk) |].
      apply lt_le_from_atoms. intros a' Ha'.
      apply IH; [exact Hctx|].
      rewrite forallb_forall in H. auto.
Qed.

Lemma lt_leb_sound : forall fuel Γ l r,
  lt_ctx_wf Γ ->
  lt_leb fuel Γ l r = true ->
  lt_le Γ l r.
Proof.
  intros fuel Γ l r Hctx H.
  apply lt_le_from_atoms. intros a Ha.
  unfold lt_leb in H. rewrite forallb_forall in H.
  eapply atom_leb_sound; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Completeness at fixed fuel                                         *)
(*                                                                    *)
(* [ctx_lookup_lt] shifts every bound past the binders it traverses,  *)
(* so a looked-up bound's variables are strictly above the variable   *)
(* looked up.  Bound-chains therefore strictly increase and fuel      *)
(* [ctx_lt_count Γ] suffices — for EVERY context, well-formed or not. *)
(* ------------------------------------------------------------------ *)

Fixpoint ctx_lt_count (Γ : ctx) : nat :=
  match Γ with
  | []                 => 0
  | bind_lt _ :: rest  => S (ctx_lt_count rest)
  | _ :: rest          => ctx_lt_count rest
  end.

Fixpoint lt_occursb (y : nat) (l : lifetime) : bool :=
  match l with
  | lt_var x     => Nat.eqb x y
  | lt_join l1 l2 => lt_occursb y l1 || lt_occursb y l2
  | _            => false
  end.

Lemma lt_occursb_shift : forall Δ y,
  lt_occursb y (shift_lt 1 0 Δ) = true ->
  exists y', y = S y' /\ lt_occursb y' Δ = true.
Proof.
  induction Δ; simpl; intros y H; try discriminate.
  - destruct (Nat.eqb_spec (n + 1) y); [|discriminate].
    exists n. split; [lia|]. apply Nat.eqb_refl.
  - apply orb_true_iff in H; destruct H as [H|H];
      [destruct (IHΔ1 _ H) as [y' [-> Hy]]
      |destruct (IHΔ2 _ H) as [y' [-> Hy]]];
      exists y'; split; auto; simpl; rewrite Hy;
      [reflexivity | apply orb_true_r].
Qed.

Lemma ctx_lookup_lt_count : forall Γ x Δ,
  ctx_lookup_lt Γ x = Some Δ -> x < ctx_lt_count Γ.
Proof.
  induction Γ as [|b Γ IH]; simpl; intros x Δ H; [discriminate|].
  destruct b; eauto.
  destruct x as [|n]; [lia|].
  destruct (ctx_lookup_lt Γ n) as [Δ'|] eqn:E; simpl in H; [|discriminate].
  specialize (IH _ _ E). lia.
Qed.

Lemma ctx_lookup_lt_occurs_above : forall Γ x Δ y,
  ctx_lookup_lt Γ x = Some Δ ->
  lt_occursb y Δ = true ->
  x < y.
Proof.
  induction Γ as [|b Γ IH]; simpl; intros x Δ y Hlk Hocc; [discriminate|].
  destruct b; eauto.
  destruct x as [|n].
  - injection Hlk as <-.
    destruct (lt_occursb_shift _ _ Hocc) as [y' [-> _]]. lia.
  - destruct (ctx_lookup_lt Γ n) as [Δ'|] eqn:E; simpl in Hlk; [|discriminate].
    injection Hlk as <-.
    destruct (lt_occursb_shift _ _ Hocc) as [y' [-> Hy]].
    specialize (IH _ _ _ E Hy). lia.
Qed.

Lemma lt_occursb_atoms : forall l a y,
  In a (lt_atoms l) -> lt_occursb y a = true -> lt_occursb y l = true.
Proof.
  induction l; simpl; intros a y Hin Hocc;
    try (destruct Hin as [<-|[]]; assumption).
  apply in_app_or in Hin; apply orb_true_iff.
  destruct Hin; eauto.
Qed.

(* The invariant ties available fuel to how deep the atom sits in the *)
(* variable order: [ctx_lt_count Γ - y <= fuel] for every variable    *)
(* [y] of the atom.  Bound-chasing strictly increases [y], recovering *)
(* the fuel decrement.                                                *)
Lemma lt_le_atom_leb : forall Γ l r,
  lt_le Γ l r ->
  forall b fuel,
    In b (lt_atoms l) ->
    (forall y, lt_occursb y b = true -> ctx_lt_count Γ - y <= fuel) ->
    atom_leb fuel Γ b r = true.
Proof.
  intros Γ l r H; induction H; simpl; intros b fuel Hin Hfuel.
  - (* LL_Free *)
    destruct Hin as [<-|[]]. apply atom_leb_free.
  - (* LL_Join *)
    apply in_app_or in Hin; destruct Hin; eauto.
  - (* LL_Mem: the atom a is an atom of r *)
    rewrite (lt_atoms_atom _ _ H) in Hin.
    destruct Hin as [<-|[]].
    destruct a as [x| | |a1 a2].
    + rewrite atom_leb_var.
      rewrite (lt_memb_in_true _ _ H).
      rewrite orb_true_r. reflexivity.
    + apply atom_leb_free.
    + rewrite atom_leb_local. apply lt_memb_in_true; exact H.
    + exfalso. eapply lt_atoms_no_min; eauto.
  - (* LL_Top: local among r's atoms covers every atom b *)
    destruct b as [x| | |b1 b2].
    + rewrite atom_leb_var.
      rewrite (lt_memb_in_true _ _ H). reflexivity.
    + apply atom_leb_free.
    + rewrite atom_leb_local. apply lt_memb_in_true; exact H.
    + exfalso. eapply lt_atoms_no_min; eauto.
  - (* LL_Bound *)
    destruct Hin as [<-|[]].
    pose proof (ctx_lookup_lt_count _ _ _ H) as Hx.
    assert (Hge : ctx_lt_count Γ - x <= fuel).
    { apply Hfuel. simpl. apply Nat.eqb_refl. }
    destruct fuel as [|fuel']; [lia|].
    simpl. rewrite H.
    apply orb_true_iff; right.
    apply forallb_forall. intros a' Ha'.
    apply IHlt_le; [exact Ha'|].
    intros y Hy.
    assert (Hocc : lt_occursb y Δ = true)
      by (eapply lt_occursb_atoms; eauto).
    pose proof (ctx_lookup_lt_occurs_above _ _ _ _ H Hocc). lia.
Qed.

Lemma lt_le_lt_leb : forall Γ l r,
  lt_le Γ l r ->
  lt_leb (ctx_lt_count Γ) Γ l r = true.
Proof.
  intros Γ l r H.
  unfold lt_leb. apply forallb_forall. intros a Ha.
  eapply lt_le_atom_leb; eauto.
  intros y _. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The decider and its reflection theorems                            *)
(* ------------------------------------------------------------------ *)

Definition lt_subb (Γ : ctx) (l r : lifetime) : bool :=
  lt_leb (ctx_lt_count Γ) Γ l r.

Theorem lt_subb_complete : forall Γ l r,
  Γ ⊢ₗ l <: r -> lt_subb Γ l r = true.
Proof.
  intros. apply lt_le_lt_leb, lt_sub_lt_le. assumption.
Qed.

Theorem lt_subb_sound : forall Γ l r,
  lt_ctx_wf Γ ->
  lt_wf Γ l ->
  lt_wf Γ r ->
  lt_subb Γ l r = true ->
  Γ ⊢ₗ l <: r.
Proof.
  intros Γ l r Hctx Hl Hr H.
  apply lt_le_sound; auto.
  eapply lt_leb_sound; eauto.
Qed.

Theorem lt_subb_spec : forall Γ l r,
  lt_ctx_wf Γ ->
  lt_wf Γ l ->
  lt_wf Γ r ->
  reflect (Γ ⊢ₗ l <: r) (lt_subb Γ l r).
Proof.
  intros Γ l r Hctx Hl Hr.
  destruct (lt_subb Γ l r) eqn:E.
  - apply ReflectT. apply lt_subb_sound; assumption.
  - apply ReflectF. intros H.
    rewrite (lt_subb_complete _ _ _ H) in E. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* nolocb: the REAL noloc premise, decided                            *)
(*                                                                    *)
(* [nolocb] decides exactly the escape side condition the typing      *)
(* rules impose (`Γ ⊢ₗ lt_of_ty_G Γ T <: lt_free`); no syntactic      *)
(* approximation is involved.                                         *)
(* ------------------------------------------------------------------ *)

Definition nolocb (Γ : ctx) (T : type) : bool :=
  lt_subb Γ (lt_of_ty_G Γ T) lt_free.

Theorem nolocb_spec : forall Γ T,
  lt_ctx_wf Γ ->
  ty_wf Γ T ->
  reflect (Γ ⊢ₗ lt_of_ty_G Γ T <: lt_free) (nolocb Γ T).
Proof.
  intros Γ T Hctx Hwf.
  apply lt_subb_spec; [exact Hctx | | apply LWF_Free].
  unfold lt_of_ty_G.
  apply lt_of_ty_ctx_wf; [exact Hwf | apply Nat.le_refl].
Qed.

(* PUBLIC API — terminal deliverable: no internal consumers; do not
   mistake for dead code.  Gated by scripts/check_assumptions.py. *)
Corollary nolocb_spec_eval_ctx : forall Γ T,
  eval_ctx Γ ->
  ty_wf Γ T ->
  reflect (Γ ⊢ₗ lt_of_ty_G Γ T <: lt_free) (nolocb Γ T).
Proof.
  intros Γ T Hec Hwf.
  apply nolocb_spec; [apply eval_ctx_lt_ctx_wf; exact Hec | exact Hwf].
Qed.

(* Rejection form used by the negative example witnesses: a computed  *)
(* [false] certifies underivability of the real premise.              *)
Corollary nolocb_false_rejects : forall Γ T,
  lt_ctx_wf Γ ->
  ty_wf Γ T ->
  nolocb Γ T = false ->
  ~ (Γ ⊢ₗ lt_of_ty_G Γ T <: lt_free).
Proof.
  intros Γ T Hctx Hwf Hb H.
  destruct (nolocb_spec Γ T Hctx Hwf); [congruence | contradiction].
Qed.

(* Acceptance form used by the positive example witnesses: a computed *)
(* [true] certifies the real premise.                                 *)
Corollary nolocb_true_accepts : forall Γ T,
  lt_ctx_wf Γ ->
  ty_wf Γ T ->
  nolocb Γ T = true ->
  Γ ⊢ₗ lt_of_ty_G Γ T <: lt_free.
Proof.
  intros Γ T Hctx Hwf Hb.
  destruct (nolocb_spec Γ T Hctx Hwf); [assumption | congruence].
Qed.

(* ------------------------------------------------------------------ *)
(* valueb / sourceb                                                   *)
(* ------------------------------------------------------------------ *)

Fixpoint valueb (t : term) : bool :=
  match t with
  | term_lam _ _         => true
  | term_ty_lam _ _      => true
  | term_lt_lam _        => true
  | term_ctor _ _ _ _ vs =>
      (fix go (ts : list term) : bool :=
         match ts with
         | []        => true
         | u :: rest => andb (valueb u) (go rest)
         end) vs
  | term_cap _ _ _ _ _ => true
  | _                    => false
  end.

Lemma valueb_value : forall t, valueb t = true -> value t.
Proof.
  fix IH 1.
  intros t; destruct t as
    [ x | t1 t2 | body T | t' T | B body | t' lft | body
    | K clt lts Ts vs | scrut K nlt ar yb nb
    | Etag Ts TB TR opb bod | recv op Ss A arg
    | Ecap m Ts TR opb | m TB TR inner ];
    simpl; intro H; try discriminate; try (constructor; fail).
  (* ctor *)
  constructor.
  revert H; revert vs.
  fix IHvs 1. intros vs H; destruct vs as [|u vs']; constructor.
  - apply IH. simpl in H; apply andb_true_iff in H; tauto.
  - apply IHvs. simpl in H; apply andb_true_iff in H; tauto.
Qed.

Lemma value_valueb : forall t, value t -> valueb t = true.
Proof.
  fix IH 1.
  intros t Hv; destruct t as
    [ x | t1 t2 | body T | t' T | B body | t' lft | body
    | K clt lts Ts vs | scrut K nlt ar yb nb
    | Etag Ts TB TR opb bod | recv op Ss A arg
    | Ecap m Ts TR opb | m TB TR inner ];
    simpl; try reflexivity; try (inversion Hv; fail).
  (* ctor *)
  assert (HF : Forall value vs) by (inversion Hv; assumption).
  clear Hv.
  revert HF; revert vs.
  fix IHvs 1. intros vs HF; destruct vs as [|u vs']; simpl.
  - reflexivity.
  - apply andb_true_iff; split.
    + apply IH. inversion HF; assumption.
    + apply IHvs. inversion HF; assumption.
Qed.

(* [valueb] backs the reflective [solve_value] tactic                 *)
(* (examples/ExamplesTactics.v); [valueb_spec] is the artifact-facing *)
(* statement.  Gated by scripts/check_assumptions.py.                 *)
Theorem valueb_spec : forall t, reflect (value t) (valueb t).
Proof.
  intros t. destruct (valueb t) eqn:E.
  - apply ReflectT. apply valueb_value; exact E.
  - apply ReflectF. intros Hv.
    rewrite (value_valueb _ Hv) in E. discriminate.
Qed.

(* A term is a SOURCE term iff no runtime marker construct occurs in  *)
(* it; [has_rt_marker] is already executable, so the decider is its      *)
(* negation.                                                          *)
Definition sourceb (t : term) : bool := negb (has_rt_marker t).

Theorem sourceb_spec : forall t,
  sourceb t = true <-> has_rt_marker t = false.
Proof.
  intros t. unfold sourceb. apply negb_true_iff.
Qed.
