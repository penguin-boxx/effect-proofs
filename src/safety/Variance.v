Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import Markers.
Require Import Progress.
Require Import Narrowing.

(* =================================================================== *)
(* Variance soundness for `elim_ty` / `elim_lt`                        *)
(*                                                                     *)
(* This is the central meta-theoretic lemma that justifies eliminating *)
(* fresh lifetime variables from a match-branch result type:           *)
(*                                                                     *)
(*   Provided eta has no invariant occurrence of the eliminated var,   *)
(*   substituting any concrete witness l_0 (with l_0 <: Δ) yields a    *)
(*   subtype of `elim_ty 0 Δ var_pos eta`.                             *)
(*                                                                     *)
(* The proof goes by mutual structural induction on the eliminated     *)
(* type/lifetime, simultaneously varying the variance position.        *)
(* Auxiliary mechanical de Bruijn lemmas are axiomatized: subtyping    *)
(* monotonicity under shift / single-var lt-substitution.              *)
(* =================================================================== *)

(* --- Custom type induction principle providing per-element IH      *)
(*     for the list-of-types in `type_ctor`.                         *)
Section TypeInd.
  Variable P : type -> Prop.
  Hypotheses
    (Hvar  : forall n, P (type_var n))
    (Hfun  : forall A l B, P A -> P B -> P (type_fun A l B))
    (Hctor : forall K l Ts, Forall P Ts -> P (type_ctor K l Ts))
    (Hltall: forall A, P A -> P (type_lt_all A))
    (Htyall: forall B A, P B -> P A -> P (type_ty_all B A)).

  Fixpoint type_ind' (T : type) : P T :=
    match T with
    | type_var n        => Hvar n
    | type_fun A l B    => Hfun A l B (type_ind' A) (type_ind' B)
    | type_ctor K l Ts  =>
        Hctor K l Ts
          ((fix go (Ts : list type) : Forall P Ts :=
            match Ts return Forall P Ts with
            | []     => Forall_nil _
            | A :: r => Forall_cons _ (type_ind' A) (go r)
            end) Ts)
    | type_lt_all A     => Hltall A (type_ind' A)
    | type_ty_all B A   => Htyall B A (type_ind' B) (type_ind' A)
    end.
End TypeInd.

Fixpoint elim_ty_list (lvar : nat) (bound : lifetime) (p : variance) (Ts : list type)
    : option (list type) :=
  match Ts with
  | [] => Some []
  | A :: rest =>
      match elim_ty lvar bound p A, elim_ty_list lvar bound p rest with
      | Some A', Some rest' => Some (A' :: rest')
      | _, _ => None
      end
  end.

Lemma elim_ty_list_eq_worker : forall lvar bound p Ts,
  (fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
     match Ts0 with
     | [] => Some []
     | A :: rest =>
         match elim_ty lvar bound p' A, go_list p' rest with
         | Some A', Some rest' => Some (A' :: rest')
         | _, _ => None
         end
     end) p Ts = elim_ty_list lvar bound p Ts.
Proof.
  intros lvar bound p Ts. induction Ts as [|A rest IH]; simpl.
  - reflexivity.
  - destruct (elim_ty lvar bound p A); simpl; [rewrite IH |]; reflexivity.
Qed.

Lemma elim_ty_ctor_eq : forall lvar bound p K l Ts,
  elim_ty lvar bound p (type_ctor K l Ts)
  = match elim_lt lvar bound p l, elim_ty_list lvar bound var_inv Ts with
    | Some l', Some Ts' => Some (type_ctor K l' Ts')
    | _, _ => None
    end.
Proof.
  intros lvar bound p K l Ts. simpl.
  rewrite elim_ty_list_eq_worker. reflexivity.
Qed.

(* ================================================================== *)
(* Sound iterated-elim soundness (binder-removal reformulation).      *)
(*                                                                    *)
(* The old `elim_ty_n_sound` relied on `iter_subst_lt_in_ty_mono`,    *)
(* which is FALSE (lifetime-variable substitution is not monotone in  *)
(* the subtyping order under LS_Var).  We replace it with an          *)
(* over-approximate-in-context + peel construction that never needs   *)
(* monotonicity:                                                      *)
(*   1. `elim_in_ctx_sound`: over-approximate eta entirely in a       *)
(*      context with n fresh lt-binders (no witnesses), giving        *)
(*      eta <:: shift_lt_in_ty n 0 elim_result.                       *)
(*   2. `sub_peel_push_corr`: peel all n binders at once via SubstLt, *)
(*      sound because the context shrinks together with the shift.    *)
(* ================================================================== *)

(* Over-approximation context: n fresh lt-binders, each storing the   *)
(* bound shifted to live at its level (uniform lookup = shift_lt n).  *)
Fixpoint push_corr (n : nat) (Delta : lifetime) (G : ctx) : ctx :=
  match n with
  | O    => G
  | S n' => bind_lt (shift_lt n' 0 Delta) :: push_corr n' Delta G
  end.

Lemma push_corr_lookup0 : forall n' Delta G,
  ctx_lookup_lt (push_corr (S n') Delta G) 0 = Some (shift_lt (S n') 0 Delta).
Proof.
  intros n' Delta G. simpl. f_equal.
  rewrite shift_lt_fuse. reflexivity.
Qed.

Lemma lt_wf_push_corr_bound : forall n Delta G,
  lt_wf G Delta -> lt_wf (push_corr n Delta G) (shift_lt n 0 Delta).
Proof.
  induction n as [|n' IH]; intros Delta G HwfDelta.
  - cbn [push_corr]. rewrite shift_lt_zero. exact HwfDelta.
  - cbn [push_corr].
    pose proof (IH Delta G HwfDelta) as HwfPrev.
    pose proof (lt_wf_InsLt (push_corr n' Delta G) (shift_lt n' 0 Delta) HwfPrev
                 0 (bind_lt (shift_lt n' 0 Delta) :: push_corr n' Delta G)
                 (InsLt_here (shift_lt n' 0 Delta) (push_corr n' Delta G))) as HwfIns.
    rewrite shift_lt_fuse in HwfIns. exact HwfIns.
Qed.

(* --- In-context single-step elim soundness (no substitution) ------ *)
(* Mirrors elim_lt_step_sound/elim_ty_step_sound but keeps the        *)
(* eliminated variable in the context and discharges via LS_Var.      *)
Lemma elim_lt_step_ctx : forall l lvar bound p l' G,
  elim_lt lvar bound p l = Some l' ->
  ctx_lookup_lt G lvar = Some bound ->
  lt_wf G bound ->
  lt_wf G l ->
  lt_wf G l' /\
  match p with
  | var_pos => G ⊢ₗ l <: l'
  | var_neg => G ⊢ₗ l' <: l
  | var_inv => l = l'
  end.
Proof.
  induction l as [n | | | l1 IHl1 l2 IHl2]; intros lvar bound p l' G Helim Hlk HwfBound Hwfl; simpl in Helim.
  - (* lt_var n *)
    destruct (Nat.eqb n lvar) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst n.
      destruct p; try discriminate Helim.
      * injection Helim; intros; subst l'. split.
        -- exact HwfBound.
        -- apply LS_Var; assumption.
      * injection Helim; intros; subst l'. split.
        -- constructor.
        -- apply LS_Free. exact Hwfl.
    + injection Helim; intros; subst l'.
      split; [exact Hwfl|]. destruct p; simpl; try (apply LS_Refl; exact Hwfl). reflexivity.
  - injection Helim; intros; subst l'. split; [constructor|].
    destruct p; simpl; try (apply LS_Refl; constructor). reflexivity.
  - injection Helim; intros; subst l'. split; [constructor|].
    destruct p; simpl; try (apply LS_Refl; constructor). reflexivity.
  - destruct (elim_lt lvar bound p l1) as [l1'|] eqn:E1; try discriminate.
    destruct (elim_lt lvar bound p l2) as [l2'|] eqn:E2; try discriminate.
    injection Helim; intros; subst l'.
    inversion Hwfl; subst.
    destruct (IHl1 _ _ _ _ _ E1 Hlk HwfBound H2) as [Hwf1' Hrel1].
    destruct (IHl2 _ _ _ _ _ E2 Hlk HwfBound H3) as [Hwf2' Hrel2].
    split; [constructor; assumption|]. destruct p; simpl in *.
    + apply lt_min_mono; assumption.
    + apply lt_min_mono; assumption.
    + f_equal; assumption.
Qed.

Lemma elim_ty_step_ctx : forall T lvar bound p T' G,
  elim_ty lvar bound p T = Some T' ->
  ctx_lookup_lt G lvar = Some bound ->
  lt_wf G bound ->
  ty_wf G T ->
  ty_wf G T' /\
  match p with
  | var_pos => G ⊢ T <:: T'
  | var_neg => G ⊢ T' <:: T
  | var_inv => T = T'
  end.
Proof.
  apply (type_ind'
    (fun T => forall lvar bound p T' G,
      elim_ty lvar bound p T = Some T' ->
      ctx_lookup_lt G lvar = Some bound ->
      lt_wf G bound ->
      ty_wf G T ->
      ty_wf G T' /\
      match p with
      | var_pos => G ⊢ T <:: T'
      | var_neg => G ⊢ T' <:: T
      | var_inv => T = T'
      end)).
  - (* type_var *)
    intros n lvar bound p T' G Helim Hlk HwfBound HwfT. simpl in Helim.
    injection Helim; intros; subst T'. split; [exact HwfT|].
    destruct p; simpl; try (apply SA_Refl; exact HwfT). reflexivity.
  - (* type_fun A l B *)
    intros A l B IHA IHB lvar bound p T' G Helim Hlk HwfBound HwfT. simpl in Helim.
    inversion HwfT; subst; clear HwfT.
    match goal with H : ty_wf G A |- _ => rename H into HwfA end.
    match goal with H : lt_wf G l |- _ => rename H into Hwfl end.
    match goal with H : ty_wf G B |- _ => rename H into HwfB end.
    destruct (elim_ty lvar bound (flip_var p) A) as [A'|] eqn:HA; try discriminate.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; try discriminate.
    destruct (elim_ty lvar bound p B) as [B'|] eqn:HB; try discriminate.
    injection Helim; intros; subst T'.
    destruct (IHA lvar bound (flip_var p) A' G HA Hlk HwfBound HwfA) as [HwfA' HrelA].
    destruct (elim_lt_step_ctx l lvar bound p l' G Hl Hlk HwfBound Hwfl) as [Hwfl' Hrell].
    destruct (IHB lvar bound p B' G HB Hlk HwfBound HwfB) as [HwfB' HrelB].
    split; [constructor; assumption|]. destruct p; simpl in *.
    + apply SA_Fun; assumption.
    + apply SA_Fun; assumption.
    + f_equal; assumption.
  - (* type_ctor K l Ts *)
    intros K l Ts IHTs lvar bound p T' G Helim Hlk HwfBound HwfT.
    inversion HwfT; subst; clear HwfT.
    match goal with H : lt_wf G l |- _ => rename H into Hwfl end.
    match goal with H : types_wf G Ts |- _ => rename H into HwfTs end.
    rewrite elim_ty_ctor_eq in Helim.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; try discriminate.
    destruct (elim_ty_list lvar bound var_inv Ts) as [Ts'|] eqn:HTs; try discriminate.
    injection Helim; intros; subst T'.
    destruct (elim_lt_step_ctx l lvar bound p l' G Hl Hlk HwfBound Hwfl) as [Hwfl' Hrell].
    assert (Hlist : Ts' = Ts).
    { clear Helim Hl Hrell Hwfl'. revert Ts' HTs HwfTs.
      induction IHTs as [|A rest HPA HFor IHFor]; intros Ts' HTs HwfTs; simpl in HTs.
      - injection HTs; intros; subst Ts'. reflexivity.
      - inversion HwfTs as [|? ? ? HwfA HwfRest]; subst.
        destruct (elim_ty lvar bound var_inv A) as [A'|] eqn:HAe; try discriminate.
        destruct (elim_ty_list lvar bound var_inv rest) as [rest'|] eqn:HRe; try discriminate.
        injection HTs; intros; subst Ts'. f_equal.
          + destruct (HPA lvar bound var_inv A' G HAe Hlk HwfBound HwfA) as [_ HAeq].
            symmetry. exact HAeq.
          + apply (IHFor rest'); [reflexivity|exact HwfRest]. }
    subst Ts'.
    split; [constructor; assumption|]. destruct p; simpl in *.
    + apply SA_Data; assumption.
    + apply SA_Data; assumption.
    + f_equal. exact Hrell.
  - (* type_lt_all A *)
    intros A IHA lvar bound p T' G Helim Hlk HwfBound HwfT. simpl in Helim.
    inversion HwfT; subst; clear HwfT.
    match goal with H : ty_wf (bind_lt lt_local :: G) A |- _ => rename H into HwfA end.
    destruct (elim_ty (S lvar) (shift_lt 1 0 bound) p A) as [A'|] eqn:HA; try discriminate.
    injection Helim; intros; subst T'.
    assert (Hlk' : ctx_lookup_lt (bind_lt lt_local :: G) (S lvar) = Some (shift_lt 1 0 bound)).
    { simpl. rewrite Hlk. reflexivity. }
    assert (HwfBound' : lt_wf (bind_lt lt_local :: G) (shift_lt 1 0 bound)).
    { eapply lt_wf_InsLt; [exact HwfBound|apply InsLt_here]. }
    destruct (IHA (S lvar) (shift_lt 1 0 bound) p A' (bind_lt lt_local :: G)
                HA Hlk' HwfBound' HwfA) as [HwfA' HrelA].
    split; [constructor; exact HwfA'|]. destruct p; simpl in *.
    + apply SA_LtAll. exact HrelA.
    + apply SA_LtAll. exact HrelA.
    + f_equal. exact HrelA.
  - (* type_ty_all B A *)
    intros B A IHB IHA lvar bound p T' G Helim Hlk HwfBound HwfT. simpl in Helim.
    inversion HwfT; subst; clear HwfT.
    match goal with H : ty_wf G B |- _ => rename H into HwfB end.
    match goal with H : ty_wf (bind_ty B :: G) A |- _ => rename H into HwfA end.
    destruct (elim_ty lvar bound (flip_var p) B) as [B'|] eqn:HB; try discriminate.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HA; try discriminate.
    injection Helim; intros; subst T'.
    assert (HlkB : forall Bb, ctx_lookup_lt (bind_ty Bb :: G) lvar = Some bound).
    { intro Bb. simpl. exact Hlk. }
    assert (HwfBoundB : forall Bb, lt_wf (bind_ty Bb :: G) bound).
    { intro Bb. eapply lt_wf_InsTy; [exact HwfBound|apply InsTy_here]. }
    destruct p; simpl.
    + destruct (IHB lvar bound var_neg B' G HB Hlk HwfBound HwfB) as [HwfB' HsubB].
      assert (HwfA_NT : ty_wf (bind_ty B' :: G) A).
      { eapply ty_wf_NT; [apply NT_here; exact HsubB|exact HwfA]. }
      destruct (IHA lvar bound var_pos A' (bind_ty B' :: G) HA (HlkB B')
                  (HwfBoundB B') HwfA_NT) as [HwfA' HsubA].
      split; [constructor; assumption|].
      eapply SA_TyAll; eauto.
    + destruct (IHB lvar bound var_pos B' G HB Hlk HwfBound HwfB) as [HwfB' HsubB].
      destruct (IHA lvar bound var_neg A' (bind_ty B :: G) HA (HlkB B)
                  (HwfBoundB B) HwfA) as [HwfA'_B HsubA].
      assert (HwfA' : ty_wf (bind_ty B' :: G) A').
      { eapply ty_wf_RT; [|exact HwfA'_B].
        apply RT_here; assumption. }
      split; [constructor; assumption|].
      eapply SA_TyAll; eauto.
    + destruct (IHB lvar bound var_inv B' G HB Hlk HwfBound HwfB) as [HwfB' HB_eq].
      subst B'.
      destruct (IHA lvar bound var_inv A' (bind_ty B :: G) HA (HlkB B)
                  (HwfBoundB B) HwfA) as [HwfA' HA_eq].
      split; [constructor; assumption|]. f_equal. exact HA_eq.
Qed.

(* --- Freshness: elim output has no free occurrence of the          *)
(*     eliminated variable.  Encoded via the self-referential        *)
(*     identity shift_lt 1 v (subst_lt v lt_free X) = X.             *)
Lemma elim_lt_closes : forall l lvar bound p l',
  elim_lt lvar bound p l = Some l' ->
  shift_lt 1 lvar (subst_lt lvar lt_free bound) = bound ->
  shift_lt 1 lvar (subst_lt lvar lt_free l') = l'.
Proof.
  induction l as [n | | | l1 IH1 l2 IH2]; intros lvar bound p l' Helim Hb; simpl in Helim.
  - destruct (Nat.eqb n lvar) eqn:Heq.
    + apply Nat.eqb_eq in Heq; subst n.
      destruct p; try discriminate Helim.
      * injection Helim; intros; subst l'. exact Hb.
      * injection Helim; intros; subst l'. reflexivity.
    + injection Helim; intros; subst l'. simpl. rewrite Heq.
      destruct (Nat.ltb lvar n) eqn:Hlt.
      * simpl. apply Nat.ltb_lt in Hlt.
        assert (Nat.leb lvar (Nat.pred n) = true) as Hle by (apply Nat.leb_le; lia).
        rewrite Hle. f_equal. lia.
      * simpl. apply Nat.ltb_ge in Hlt. apply Nat.eqb_neq in Heq.
        assert (Nat.leb lvar n = false) as Hle by (apply Nat.leb_gt; lia).
        rewrite Hle. reflexivity.
  - injection Helim; intros; subst l'. reflexivity.
  - injection Helim; intros; subst l'. reflexivity.
  - destruct (elim_lt lvar bound p l1) as [l1'|] eqn:E1; try discriminate.
    destruct (elim_lt lvar bound p l2) as [l2'|] eqn:E2; try discriminate.
    injection Helim; intros; subst l'. simpl. f_equal.
    + exact (IH1 lvar bound p l1' E1 Hb).
    + exact (IH2 lvar bound p l2' E2 Hb).
Qed.

Lemma elim_ty_closes : forall T lvar bound p T',
  elim_ty lvar bound p T = Some T' ->
  shift_lt 1 lvar (subst_lt lvar lt_free bound) = bound ->
  shift_lt_in_ty 1 lvar (subst_lt_in_ty lvar lt_free T') = T'.
Proof.
  apply (type_ind'
    (fun T => forall lvar bound p T',
      elim_ty lvar bound p T = Some T' ->
      shift_lt 1 lvar (subst_lt lvar lt_free bound) = bound ->
      shift_lt_in_ty 1 lvar (subst_lt_in_ty lvar lt_free T') = T')).
  - (* type_var *)
    intros n lvar bound p T' Helim Hb. simpl in Helim.
    injection Helim; intros; subst T'. reflexivity.
  - (* type_fun *)
    intros A l B IHA IHB lvar bound p T' Helim Hb. simpl in Helim.
    destruct (elim_ty lvar bound (flip_var p) A) as [A'|] eqn:HA; try discriminate.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; try discriminate.
    destruct (elim_ty lvar bound p B) as [B'|] eqn:HB; try discriminate.
    injection Helim; intros; subst T'.
    rewrite subst_lt_in_ty_fun_eq, shift_lt_in_ty_fun_eq. f_equal.
    + exact (IHA lvar bound (flip_var p) A' HA Hb).
    + exact (elim_lt_closes l lvar bound p l' Hl Hb).
    + exact (IHB lvar bound p B' HB Hb).
  - (* type_ctor *)
    intros K l Ts IHTs lvar bound p T' Helim Hb.
    rewrite elim_ty_ctor_eq in Helim.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hl; try discriminate.
    destruct (elim_ty_list lvar bound var_inv Ts) as [Ts'|] eqn:HTs; try discriminate.
    injection Helim; intros; subst T'.
    rewrite subst_lt_in_ty_ctor_eq, shift_lt_in_ty_ctor_eq. f_equal.
    + exact (elim_lt_closes l lvar bound p l' Hl Hb).
    + clear Helim Hl. rewrite List.map_map. revert Ts' HTs.
      induction IHTs as [|A rest HPA HFor IHFor]; intros Ts' HTs; simpl in HTs.
      * injection HTs; intros; subst Ts'. reflexivity.
      * destruct (elim_ty lvar bound var_inv A) as [A'|] eqn:HAe; try discriminate.
        destruct (elim_ty_list lvar bound var_inv rest) as [rest'|] eqn:HRe; try discriminate.
        injection HTs; intros; subst Ts'. simpl. f_equal.
        -- exact (HPA lvar bound var_inv A' HAe Hb).
        -- apply IHFor; reflexivity.
  - (* type_lt_all *)
    intros A IHA lvar bound p T' Helim Hb. simpl in Helim.
    destruct (elim_ty (S lvar) (shift_lt 1 0 bound) p A) as [A'|] eqn:HA; try discriminate.
    injection Helim; intros; subst T'.
    rewrite subst_lt_in_ty_ltall_eq, shift_lt_in_ty_ltall_eq. f_equal.
    apply (IHA (S lvar) (shift_lt 1 0 bound) p A' HA).
    rewrite <- shift_subst_lt_comm. rewrite <- shift_lt_swap_0. rewrite Hb. reflexivity.
  - (* type_ty_all *)
    intros B A IHB IHA lvar bound p T' Helim Hb. simpl in Helim.
    destruct (elim_ty lvar bound (flip_var p) B) as [B'|] eqn:HB; try discriminate.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HA; try discriminate.
    injection Helim; intros; subst T'.
    rewrite subst_lt_in_ty_tyall_eq, shift_lt_in_ty_tyall_eq. f_equal.
    + exact (IHB lvar bound (flip_var p) B' HB Hb).
    + exact (IHA lvar bound p A' HA Hb).
Qed.

(* --- Iterated elim soundness --- *)

(* ================================================================== *)
(* Over-approximate-in-context soundness.                             *)
(* Eliminating n positive binders, then over-approximating the        *)
(* eliminated variables by a context of n fresh lt-binders, yields    *)
(*   push_corr n Delta G ⊢ eta <:: shift_lt_in_ty n 0 elim_result.    *)
(* No witnesses (and hence no monotonicity) are required.             *)
(* ================================================================== *)
Lemma elim_in_ctx_sound : forall n Delta eta elim_result G,
  elim_ty_n n (shift_lt n 0 Delta) var_pos eta = Some elim_result ->
  lt_wf G Delta ->
  ty_wf (push_corr n Delta G) eta ->
  push_corr n Delta G ⊢ eta <:: shift_lt_in_ty n 0 elim_result.
Proof.
  induction n as [|n' IH]; intros Delta eta elim_result G Helim HwfDelta HwfEta.
  - (* n = 0 *)
    simpl in Helim. injection Helim; intros He; subst elim_result.
    simpl. rewrite shift_lt_in_ty_zero. apply SA_Refl. exact HwfEta.
  - (* n = S n' *)
    simpl in Helim.
    destruct (elim_ty 0 (shift_lt (S n') 0 Delta) var_pos eta) as [T1|] eqn:ET1;
      try discriminate.
    assert (Hb : subst_lt 0 lt_free (shift_lt (S n') 0 Delta) = shift_lt n' 0 Delta).
    { replace (shift_lt (S n') 0 Delta) with (shift_lt 1 0 (shift_lt n' 0 Delta))
        by (rewrite shift_lt_fuse; reflexivity).
      rewrite subst_lt_shift_cancel. reflexivity. }
    rewrite Hb in Helim.
    assert (HwfBoundS : lt_wf (push_corr (S n') Delta G) (shift_lt (S n') 0 Delta)).
    { apply lt_wf_push_corr_bound. exact HwfDelta. }
    destruct (elim_ty_step_ctx eta 0 (shift_lt (S n') 0 Delta) var_pos T1
                (push_corr (S n') Delta G) ET1 (push_corr_lookup0 n' Delta G)
                HwfBoundS HwfEta) as [HwfT1 Hstep].
    simpl in Hstep.
    assert (HwfBoundN : lt_wf (push_corr n' Delta G) (shift_lt n' 0 Delta)).
    { apply lt_wf_push_corr_bound. exact HwfDelta. }
    assert (HwfT1Sub : ty_wf (push_corr n' Delta G) (subst_lt_in_ty 0 lt_free T1)).
    { eapply ty_wf_SubstLt; [exact HwfT1|].
      apply SubstLt_here. apply LS_Free. exact HwfBoundN. }
    specialize (IH Delta (subst_lt_in_ty 0 lt_free T1) elim_result G Helim HwfDelta HwfT1Sub).
    pose proof (sub_weaken_lt_shift (push_corr n' Delta G) (shift_lt n' 0 Delta)
                  (subst_lt_in_ty 0 lt_free T1) (shift_lt_in_ty n' 0 elim_result) IH) as Hweak.
    assert (Hfresh : shift_lt_in_ty 1 0 (subst_lt_in_ty 0 lt_free T1) = T1).
    { apply (elim_ty_closes eta 0 (shift_lt (S n') 0 Delta) var_pos T1 ET1).
      rewrite Hb. rewrite shift_lt_fuse. reflexivity. }
    rewrite Hfresh in Hweak.
    rewrite shift_lt_in_ty_fuse in Hweak.
    eapply SA_Trans; [exact Hstep | exact Hweak].
Qed.

(* ================================================================== *)
(* Piece 6: peel all n over-approximation binders at once.            *)
(* ================================================================== *)

(* 6a: weakening lifetime subtyping through the push_corr context.    *)
Lemma lt_sub_push_corr_weaken : forall n Delta Γ l1 l2,
  Γ ⊢ₗ l1 <: l2 ->
  push_corr n Delta Γ ⊢ₗ shift_lt n 0 l1 <: shift_lt n 0 l2.
Proof.
  induction n as [|n' IH]; intros Delta Γ l1 l2 Hsub.
  - cbn [push_corr]. rewrite !shift_lt_zero. exact Hsub.
  - cbn [push_corr].
    specialize (IH Delta Γ l1 l2 Hsub).
    pose proof (lt_sub_InsLt (push_corr n' Delta Γ) (shift_lt n' 0 l1) (shift_lt n' 0 l2) IH
                  0 (bind_lt (shift_lt n' 0 Delta) :: push_corr n' Delta Γ)
                  (InsLt_here (shift_lt n' 0 Delta) (push_corr n' Delta Γ))) as Hins.
    rewrite !shift_lt_fuse in Hins.
    exact Hins.
Qed.

(* 6b: peel all binders via SubstLt, sound because the context        *)
(*     shrinks together with each substitution.                       *)
Lemma sub_peel_push_corr : forall lts Delta A B Γ,
  Forall (fun l => Γ ⊢ₗ l <: Delta) lts ->
  push_corr (List.length lts) Delta Γ ⊢ A <:: B ->
  Γ ⊢ subst_list_lt_in_ty lts A <:: subst_list_lt_in_ty lts B.
Proof.
  induction lts as [|l0 rest IH]; intros Delta A B Γ Hfor Hsub.
  - cbn [subst_list_lt_in_ty]. cbn [List.length push_corr] in Hsub. exact Hsub.
  - pose proof (Forall_inv Hfor) as Hhead.
    pose proof (Forall_inv_tail Hfor) as Htail.
    cbn [List.length push_corr] in Hsub.
    cbn [subst_list_lt_in_ty].
    apply (IH Delta (subst_lt_in_ty 0 (shift_lt (List.length rest) 0 l0) A)
                    (subst_lt_in_ty 0 (shift_lt (List.length rest) 0 l0) B) Γ Htail).
    eapply sub_SubstLt.
    2: { apply SubstLt_here.
         exact (lt_sub_push_corr_weaken (List.length rest) Delta Γ l0 Delta Hhead). }
    exact Hsub.
Qed.

(* 6c: the over-approximation target shift-cancels under the peel.    *)
Lemma subst_list_lt_in_ty_shift_cancel : forall lts X,
  subst_list_lt_in_ty lts (shift_lt_in_ty (List.length lts) 0 X) = X.
Proof.
  induction lts as [|l0 rest IH]; intro X.
  - cbn [List.length subst_list_lt_in_ty]. rewrite shift_lt_in_ty_zero. reflexivity.
  - cbn [List.length subst_list_lt_in_ty].
    replace (shift_lt_in_ty (S (List.length rest)) 0 X)
      with (shift_lt_in_ty 1 0 (shift_lt_in_ty (List.length rest) 0 X))
      by (rewrite shift_lt_in_ty_fuse; reflexivity).
    rewrite subst_lt_in_ty_shift_cancel.
    apply IH.
Qed.

