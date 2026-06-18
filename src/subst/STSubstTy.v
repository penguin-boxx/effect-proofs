Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import STShiftLaws.
Require Import STInsertions.
Require Import STSubstLt.

(* ================================================================== *)
(* SubstTy : substitute a type for a ty-binder at depth n             *)
(* ================================================================== *)

Lemma lt_min_mono : forall G a1 a2 b1 b2,
  G ⊢ₗ a1 <: a2 -> G ⊢ₗ b1 <: b2 -> G ⊢ₗ lt_min a1 b1 <: lt_min a2 b2.
Proof.
  intros G a1 a2 b1 b2 Ha Hb.
  destruct (lt_sub_wf _ _ _ Ha) as [_ Hwfa2].
  destruct (lt_sub_wf _ _ _ Hb) as [_ Hwfb2].
  apply LS_MinL.
  - eapply LS_Trans; [exact Ha |].
    apply LS_MinR1.
    + apply LS_Refl. exact Hwfa2.
    + exact Hwfb2.
  - eapply LS_Trans; [exact Hb |].
    apply LS_MinR2.
    + apply LS_Refl. exact Hwfb2.
    + exact Hwfa2.
Qed.

Lemma subst_ty_var_neq : forall n Sb x,
  x <> n -> subst_ty n Sb (type_var x) = type_var (slv n x).
Proof.
  intros n Sb x H. rewrite subst_ty_var_eq.
  destruct (Nat.eqb_spec x n); [contradiction|]. unfold slv.
  destruct (Nat.ltb n x); reflexivity.
Qed.

Inductive SubstTy : type -> nat -> ctx -> ctx -> Prop :=
| SubstTy_here : forall Gamma B Sb,
    Gamma ⊢ Sb <:: B ->
    SubstTy Sb 0 (bind_ty B :: Gamma) Gamma
| SubstTy_ty : forall Sb n G G' B,
    SubstTy Sb n G G' ->
    SubstTy (shift_ty 1 0 Sb) (S n)
            (bind_ty B :: G)
            (bind_ty (subst_ty n Sb B) :: G')
| SubstTy_lt : forall Sb n G G' D,
    SubstTy Sb n G G' ->
    SubstTy (shift_lt_in_ty 1 0 Sb) n
            (bind_lt D :: G)
      (bind_lt D :: G')
| SubstTy_tm : forall Sb n G G' A,
  SubstTy Sb n G G' ->
  SubstTy Sb n
      (bind_tm A :: G)
      (bind_tm (subst_ty n Sb A) :: G').

Lemma SubstTy_length : forall Sb n G G', SubstTy Sb n G G' -> length G = S (length G').
Proof. intros Sb n G G' H. induction H; simpl; lia. Qed.

Lemma SubstTy_n_lt : forall Sb n G G', SubstTy Sb n G G' -> n < length G.
Proof. intros Sb n G G' H. induction H; simpl; lia. Qed.

Lemma SubstTy_S_VB : forall Sb n G G', SubstTy Sb n G G' -> VB n Sb.
Proof.
  intros Sb n G G' H. induction H.
  - apply VB_0.
  - apply shift_ty_VB. exact IHSubstTy.
  - apply shift_lt_in_ty_VB. exact IHSubstTy.
  - exact IHSubstTy.
Qed.

Lemma SubstTy_lookup_ty : forall Sb n G G', SubstTy Sb n G G' ->
  forall a, a <> n ->
  ctx_lookup_ty G' (slv n a) = option_map (subst_ty n Sb) (ctx_lookup_ty G a).
Proof.
  intros Sb n G G' H. induction H; intros a Hne.
  - destruct a as [|a']; [contradiction|].
    unfold slv. simpl Nat.ltb. simpl pred. simpl ctx_lookup_ty.
    destruct (ctx_lookup_ty Gamma a') as [X|]; simpl;
      [rewrite subst_ty_shift_cancel; reflexivity | reflexivity].
  - destruct a as [|a'].
    + unfold slv. simpl Nat.ltb. simpl ctx_lookup_ty.
      rewrite shift_ty_subst_ty_comm0. reflexivity.
    + assert (a' <> n) by lia.
      rewrite slv_S. simpl ctx_lookup_ty. rewrite (IHSubstTy a' H0).
      destruct (ctx_lookup_ty G a') as [X|]; simpl;
        [rewrite shift_ty_subst_ty_comm0; reflexivity | reflexivity].
  - specialize (IHSubstTy a Hne). simpl ctx_lookup_ty. rewrite IHSubstTy.
    destruct (ctx_lookup_ty G a) as [X|]; simpl;
      [rewrite shift_lt_in_ty_subst_ty_comm0; reflexivity | reflexivity].
  - apply IHSubstTy. exact Hne.
Qed.

Lemma SubstTy_lookup_lt : forall Sb n G G', SubstTy Sb n G G' ->
  forall x, ctx_lookup_lt G' x = ctx_lookup_lt G x.
Proof.
  intros Sb n G G' H. induction H; intro x.
  - simpl ctx_lookup_lt. reflexivity.
  - simpl ctx_lookup_lt. apply IHSubstTy.
  - destruct x as [|x']; simpl ctx_lookup_lt.
    + reflexivity.
    + rewrite (IHSubstTy x'). reflexivity.
  - apply IHSubstTy.
Qed.

Lemma lt_wf_SubstTy_ctx : forall G l,
  lt_wf G l -> forall Sb n G', SubstTy Sb n G G' -> lt_wf G' l.
Proof.
  intros G l Hwf. induction Hwf; intros Sb n G' HS.
  - econstructor. rewrite (SubstTy_lookup_lt Sb n Γ G' HS x). exact H.
  - constructor.
  - constructor.
  - constructor.
    + apply (IHHwf1 Sb n G' HS).
    + apply (IHHwf2 Sb n G' HS).
Qed.

Lemma lt_sub_SubstTy_ctx : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall Sb n G', SubstTy Sb n G G' -> G' ⊢ₗ l1 <: l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l Hwf|Γ l Hwf|Γ x Δ Hlk HwfD|Γ l Hwf
                 |Γ l1 l2 l3 H1 IH1 H2 IH2|Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H1 IH1 Hwf2|Γ l l1 l2 H1 IH1 Hwf1];
    intros Sb n G' HS.
  - apply LS_Free. eapply lt_wf_SubstTy_ctx; eauto.
  - apply LS_Local. eapply lt_wf_SubstTy_ctx; eauto.
  - apply LS_Var.
    + rewrite (SubstTy_lookup_lt Sb n Γ G' HS x). exact Hlk.
    + eapply lt_wf_SubstTy_ctx; eauto.
  - apply LS_Refl. eapply lt_wf_SubstTy_ctx; eauto.
  - eapply LS_Trans; [apply (IH1 Sb n G' HS) | apply (IH2 Sb n G' HS)].
  - apply LS_MinL; [apply (IH1 Sb n G' HS) | apply (IH2 Sb n G' HS)].
  - apply LS_MinR1.
    + apply (IH1 Sb n G' HS).
    + eapply lt_wf_SubstTy_ctx; eauto.
  - apply LS_MinR2.
    + apply (IH1 Sb n G' HS).
    + eapply lt_wf_SubstTy_ctx; eauto.
Qed.

Lemma lt_of_ty_G_wf : forall G T,
  ty_wf G T -> lt_wf G (lt_of_ty_G G T)
with lt_of_ty_G_list_wf : forall G Ts,
  types_wf G Ts -> lt_wf G (lt_of_ty_ctx_list (List.length G) G Ts).
Proof.
  - intros G T Hwf.
    induction Hwf as [Γ α B Hlk HwfB IHBound
                     |Γ A l B HwfA IHA Hwfl HwfB IHB
                     |Γ K l Ts Hwfl HwfTs IHTs
                     |Γ A HwfA IHA
                     |Γ B A HwfB IHB HwfA IHA].
    + unfold lt_of_ty_G.
      assert (Hlt: α < length Γ).
      { destruct (Nat.le_gt_cases (length Γ) α) as [Hle|Hgt]; [|exact Hgt].
        rewrite ctx_lookup_ty_None in Hlk by exact Hle. discriminate. }
      rewrite (lt_of_ty_ctx_var (length Γ) Γ α).
      destruct (length Γ) as [|m] eqn:HL; [lia|].
      rewrite Hlk.
      rewrite (lt_of_ty_ctx_fuel_irrel m (S m) B Γ (S α)
                 (ctx_inv_all Γ α B Hlk) ltac:(lia) ltac:(lia)).
      unfold lt_of_ty_G in IHBound. rewrite HL in IHBound. exact IHBound.
    + unfold lt_of_ty_G. rewrite lt_of_ty_ctx_fun. exact Hwfl.
    + unfold lt_of_ty_G. rewrite lt_of_ty_ctx_ctor. constructor.
      * exact Hwfl.
      * eapply lt_of_ty_G_list_wf; eauto.
    + unfold lt_of_ty_G. rewrite lt_of_ty_ctx_ltall. constructor.
    + unfold lt_of_ty_G. rewrite lt_of_ty_ctx_tyall. constructor.
  - intros G Ts Hwf.
    induction Hwf.
    + rewrite lt_of_ty_ctx_list_nil. constructor.
    + rewrite lt_of_ty_ctx_list_cons. constructor.
      * change (lt_wf Γ (lt_of_ty_G Γ T)). eapply lt_of_ty_G_wf; eauto.
      * assumption.
Qed.

(* Context-free [lt_of_ty] of a constructor unfolds to [lt_min l ...].  *)
Lemma lt_of_ty_ctor_eq : forall K l Ts,
  lt_of_ty (type_ctor K l Ts) = lt_min l (lt_of_ty_list Ts).
Proof.
  intros K l Ts. simpl. f_equal.
Qed.

(* Context-free escape lifetime is below the context-aware one          *)
(* (a type variable contributes [free] context-free, its bound          *)
(* context-aware).  Used to thread the (weaker) T_Ctor escape premise   *)
(* `lt_of_ty_list rho <: lt_of_ty result_ty` into context-aware goals.  *)
Lemma lt_of_ty_le_lt_of_ty_ctx : forall G T,
  ty_wf G T -> G ⊢ₗ lt_of_ty T <: lt_of_ty_ctx (List.length G) G T
with lt_of_ty_list_le_lt_of_ty_ctx_list : forall G Ts,
  types_wf G Ts -> G ⊢ₗ lt_of_ty_list Ts <: lt_of_ty_ctx_list (List.length G) G Ts.
Proof.
  - intros G T Hwf.
    induction Hwf as [Γ α B Hlk HwfB IHBound
                     |Γ A l B HwfA IHA Hwfl HwfB IHB
                     |Γ K l Ts Hwfl HwfTs IHTs
                     |Γ A HwfA IHA
                     |Γ B A HwfB IHB HwfA IHA].
    + apply LS_Free. change (lt_wf Γ (lt_of_ty_G Γ (type_var α))).
      apply lt_of_ty_G_wf. exact (TWF_Var Γ α B Hlk HwfB).
    + rewrite lt_of_ty_ctx_fun. apply LS_Refl. exact Hwfl.
    + rewrite lt_of_ty_ctor_eq, lt_of_ty_ctx_ctor.
      apply lt_min_mono; [apply LS_Refl; exact Hwfl|].
      eapply lt_of_ty_list_le_lt_of_ty_ctx_list; eauto.
    + rewrite lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + rewrite lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
  - intros G Ts Hwf.
    induction Hwf as [Γ | Γ T Ts HwfT IHT HwfTs IHTs].
    + rewrite lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + change (lt_of_ty_list (T :: Ts)) with (lt_min (lt_of_ty T) (lt_of_ty_list Ts)).
      rewrite lt_of_ty_ctx_list_cons.
      apply lt_min_mono.
      * eapply lt_of_ty_le_lt_of_ty_ctx; eauto.
      * eapply lt_of_ty_list_le_lt_of_ty_ctx_list; eauto.
Qed.

Lemma lt_of_ty_list_nil : lt_of_ty_list [] = lt_free.
Proof. reflexivity. Qed.

Lemma lt_of_ty_list_cons : forall A Ts,
  lt_of_ty_list (A :: Ts) = lt_min (lt_of_ty A) (lt_of_ty_list Ts).
Proof. reflexivity. Qed.

(* ================================================================== *)
(* Bounds on the context-free escape lifetime under type substitution.*)
(* These are the substitution-stability facts that make the T_Ctor    *)
(* effective-lifetime escape premise survive `subst_ty`:              *)
(*   LOWER : lt_of_ty T <: lt_of_ty (subst T)   (subst only raises it) *)
(*   UPPER : lt_of_ty (subst T) <: lt_min (lt_of_ty T) (lt_of_ty Sb)   *)
(* ================================================================== *)
Lemma lt_of_ty_subst_ty_ge : forall T n Sb G,
  lt_wf G (lt_of_ty Sb) -> ty_wf G (subst_ty n Sb T) ->
  G ⊢ₗ lt_of_ty T <: lt_of_ty (subst_ty n Sb T).
Proof.
  apply (type_list_ind
    (fun T => forall n Sb G, lt_wf G (lt_of_ty Sb) -> ty_wf G (subst_ty n Sb T) ->
       G ⊢ₗ lt_of_ty T <: lt_of_ty (subst_ty n Sb T))
    (fun Ts => forall n Sb G, lt_wf G (lt_of_ty Sb) ->
       types_wf G (List.map (subst_ty n Sb) Ts) ->
       G ⊢ₗ lt_of_ty_list Ts <: lt_of_ty_list (List.map (subst_ty n Sb) Ts))).
  - (* type_var *) intros x n Sb G HSb Hwf.
    rewrite subst_ty_var_eq. destruct (Nat.eqb_spec x n).
    + apply LS_Free. exact HSb.
    + destruct (Nat.ltb n x); apply LS_Free; apply LWF_Free.
  - (* type_fun *) intros A l B IHA IHB n Sb G HSb Hwf.
    rewrite subst_ty_fun_eq in Hwf. inversion Hwf; subst.
    cbn [lt_of_ty]. apply LS_Refl. assumption.
  - (* type_ctor *) intros K l Ts IHTs n Sb G HSb Hwf.
    rewrite subst_ty_ctor_eq in Hwf. inversion Hwf; subst.
    rewrite subst_ty_ctor_eq, !lt_of_ty_ctor_eq.
    apply lt_min_mono.
    + apply LS_Refl. assumption.
    + apply IHTs; assumption.
  - (* type_lt_all *) intros A IHA n Sb G HSb Hwf.
    rewrite subst_ty_ltall_eq. cbn [lt_of_ty]. apply LS_Refl. apply LWF_Local.
  - (* type_ty_all *) intros B A IHB IHA n Sb G HSb Hwf.
    rewrite subst_ty_tyall_eq. cbn [lt_of_ty]. apply LS_Refl. apply LWF_Local.
  - (* nil *) intros n Sb G HSb Hwf.
    rewrite lt_of_ty_list_nil. apply LS_Free. apply LWF_Free.
  - (* cons *) intros A Ts IHA IHTs n Sb G HSb Hwf.
    cbn [List.map] in Hwf |- *. inversion Hwf; subst.
    rewrite !lt_of_ty_list_cons. apply lt_min_mono.
    + apply IHA; assumption.
    + apply IHTs; assumption.
Qed.

(* Context-free escape lifetime of a well-formed type is well-formed.  *)
Lemma lt_of_ty_wf : forall G T, ty_wf G T -> lt_wf G (lt_of_ty T)
with lt_of_ty_list_wf : forall G Ts, types_wf G Ts -> lt_wf G (lt_of_ty_list Ts).
Proof.
  - intros G T Hwf. destruct Hwf as [Γ α B Hlk HwfB|Γ A l B HwfA Hwfl HwfB
                                    |Γ K l Ts Hwfl HwfTs|Γ A HwfA|Γ B A HwfB HwfA].
    + apply LWF_Free.
    + cbn [lt_of_ty]. exact Hwfl.
    + rewrite lt_of_ty_ctor_eq. apply LWF_Min; [exact Hwfl | apply lt_of_ty_list_wf; exact HwfTs].
    + cbn [lt_of_ty]. apply LWF_Local.
    + cbn [lt_of_ty]. apply LWF_Local.
  - intros G Ts Hwf. destruct Hwf as [Γ|Γ T Ts HwfT HwfTs].
    + rewrite lt_of_ty_list_nil. apply LWF_Free.
    + rewrite lt_of_ty_list_cons. apply LWF_Min; [apply lt_of_ty_wf; exact HwfT | apply lt_of_ty_list_wf; exact HwfTs].
Qed.

(* UPPER bound: substitution raises the escape lifetime by at most the   *)
(* escape lifetime of the replacement.                                   *)
Lemma lt_of_ty_subst_ty_le : forall T n Sb G,
  lt_wf G (lt_of_ty T) -> lt_wf G (lt_of_ty Sb) ->
  G ⊢ₗ lt_of_ty (subst_ty n Sb T) <: lt_min (lt_of_ty T) (lt_of_ty Sb).
Proof.
  apply (type_list_ind
    (fun T => forall n Sb G, lt_wf G (lt_of_ty T) -> lt_wf G (lt_of_ty Sb) ->
       G ⊢ₗ lt_of_ty (subst_ty n Sb T) <: lt_min (lt_of_ty T) (lt_of_ty Sb))
    (fun Ts => forall n Sb G, lt_wf G (lt_of_ty_list Ts) -> lt_wf G (lt_of_ty Sb) ->
       G ⊢ₗ lt_of_ty_list (List.map (subst_ty n Sb) Ts)
            <: lt_min (lt_of_ty_list Ts) (lt_of_ty Sb))).
  - (* type_var *) intros x n Sb G HT HSb.
    rewrite subst_ty_var_eq. destruct (Nat.eqb_spec x n).
    + apply LS_MinR2; [apply LS_Refl; exact HSb | apply LWF_Free].
    + destruct (Nat.ltb n x); apply LS_MinR1; solve [apply LS_Free; apply LWF_Free | exact HSb].
  - (* type_fun *) intros A l B IHA IHB n Sb G HT HSb.
    cbn [lt_of_ty] in HT |- *. apply LS_MinR1; [apply LS_Refl; exact HT | exact HSb].
  - (* type_ctor *) intros K l Ts IHTs n Sb G HT HSb.
    rewrite lt_of_ty_ctor_eq in HT. inversion HT as [| | |G0 a b Hwfl HwfTs]; subst.
    rewrite subst_ty_ctor_eq, !lt_of_ty_ctor_eq.
    apply LS_MinL.
    + apply LS_MinR1; [apply LS_MinR1; [apply LS_Refl; exact Hwfl | exact HwfTs] | exact HSb].
    + eapply LS_Trans; [apply IHTs; [exact HwfTs | exact HSb] |].
      apply lt_min_mono; [apply LS_MinR2; [apply LS_Refl; exact HwfTs | exact Hwfl] | apply LS_Refl; exact HSb].
  - (* type_lt_all *) intros A IHA n Sb G HT HSb.
    rewrite subst_ty_ltall_eq. cbn [lt_of_ty]. apply LS_MinR1; [apply LS_Refl; apply LWF_Local | exact HSb].
  - (* type_ty_all *) intros B A IHB IHA n Sb G HT HSb.
    rewrite subst_ty_tyall_eq. cbn [lt_of_ty]. apply LS_MinR1; [apply LS_Refl; apply LWF_Local | exact HSb].
  - (* nil *) intros n Sb G HT HSb.
    cbn [List.map]. rewrite lt_of_ty_list_nil. apply LS_MinR1; [apply LS_Free; apply LWF_Free | exact HSb].
  - (* cons *) intros A Ts IHA IHTs n Sb G HT HSb.
    rewrite lt_of_ty_list_cons in HT. inversion HT as [| | |G0 a b HwfA HwfTs]; subst.
    cbn [List.map]. rewrite !lt_of_ty_list_cons.
    apply LS_MinL.
    + eapply LS_Trans; [apply IHA; [exact HwfA | exact HSb] |].
      apply lt_min_mono; [apply LS_MinR1; [apply LS_Refl; exact HwfA | exact HwfTs] | apply LS_Refl; exact HSb].
    + eapply LS_Trans; [apply IHTs; [exact HwfTs | exact HSb] |].
      apply lt_min_mono; [apply LS_MinR2; [apply LS_Refl; exact HwfTs | exact HwfA] | apply LS_Refl; exact HSb].
Qed.

(* lt_of_ty is invariant under (any-amount) type-variable shifting.     *)
Lemma lt_of_ty_shift_ty_amt : forall T k c, lt_of_ty (shift_ty k c T) = lt_of_ty T.
Proof.
  apply (type_list_ind
    (fun T => forall k c, lt_of_ty (shift_ty k c T) = lt_of_ty T)
    (fun Ts => forall k c, lt_of_ty_list (List.map (shift_ty k c) Ts) = lt_of_ty_list Ts)).
  - intros x k c. reflexivity.
  - intros A l B HA HB k c. reflexivity.
  - intros K l Ts HTs k c. rewrite shift_ty_ctor_eq. cbn [lt_of_ty]. f_equal.
    change ((fix go_list (Ts0 : list type) : lifetime :=
       match Ts0 with [] => lt_free | A :: rest => lt_min (lt_of_ty A) (go_list rest) end)
       (List.map (shift_ty k c) Ts)) with (lt_of_ty_list (List.map (shift_ty k c) Ts)).
    change ((fix go_list (Ts0 : list type) : lifetime :=
       match Ts0 with [] => lt_free | A :: rest => lt_min (lt_of_ty A) (go_list rest) end) Ts)
       with (lt_of_ty_list Ts).
    apply HTs.
  - intros A HA k c. reflexivity.
  - intros B A HB HA k c. reflexivity.
  - intros k c. reflexivity.
  - intros A Ts HA HTs k c. cbn [List.map]. rewrite !lt_of_ty_list_cons. rewrite HA, HTs. reflexivity.
Qed.

(* UPPER bound through type-variable instantiation (inst_ty_vars is      *)
(* iterated subst_ty): instantiating raises lt_of_ty by at most the      *)
(* join of the arguments' escape lifetimes.                              *)
Lemma lt_of_ty_inst_ty_vars_le : forall Ts T G,
  lt_wf G (lt_of_ty T) -> lt_wf G (lt_of_ty_list Ts) ->
  G ⊢ₗ lt_of_ty (inst_ty_vars (List.length Ts) Ts T) <: lt_min (lt_of_ty T) (lt_of_ty_list Ts).
Proof.
  induction Ts as [|U rest IH]; intros T G HT HTs.
  - simpl. apply LS_MinR1; [apply LS_Refl; exact HT | apply LWF_Free].
  - rewrite lt_of_ty_list_cons in HTs. inversion HTs as [| | |G0 a b HwfU HwfRest]; subst.
    cbn [inst_ty_vars List.length].
    set (T1 := subst_ty 0 (shift_ty (List.length rest) 0 U) T).
    assert (Hub : G ⊢ₗ lt_of_ty T1 <: lt_min (lt_of_ty T) (lt_of_ty U)).
    { unfold T1.
      eapply LS_Trans; [apply lt_of_ty_subst_ty_le; [exact HT | rewrite lt_of_ty_shift_ty_amt; exact HwfU] |].
      rewrite lt_of_ty_shift_ty_amt. apply LS_Refl. apply LWF_Min; assumption. }
    assert (HwfT1 : lt_wf G (lt_of_ty T1)) by (destruct (lt_sub_wf _ _ _ Hub) as [H _]; exact H).
    eapply LS_Trans; [apply IH; [exact HwfT1 | exact HwfRest] |].
    rewrite lt_of_ty_list_cons.
    (* lt_min (lt_of_ty T1) (lt_of_ty_list rest) <: lt_min (lt_of_ty T) (lt_min (lt_of_ty U) (lt_of_ty_list rest)) *)
    apply LS_MinL.
    + eapply LS_Trans; [exact Hub |].
      apply LS_MinL.
      * apply LS_MinR1; [apply LS_Refl; exact HT | apply LWF_Min; assumption].
      * apply LS_MinR2; [apply LS_MinR1; [apply LS_Refl; exact HwfU | exact HwfRest] | exact HT].
    + apply LS_MinR2; [apply LS_MinR2; [apply LS_Refl; exact HwfRest | exact HwfU] | exact HT].
Qed.

(* lt_of_ty commutes with parallel lifetime substitution (inst_lt_vars).*)
Lemma lt_of_ty_multi_subst_lt_in_ty : forall T c lts,
  lt_of_ty (multi_subst_lt_in_ty c lts T) = multi_subst_lt c lts (lt_of_ty T).
Proof.
  apply (type_list_ind
    (fun T => forall c lts,
      lt_of_ty (multi_subst_lt_in_ty c lts T) = multi_subst_lt c lts (lt_of_ty T))
    (fun Ts => forall c lts,
      lt_of_ty_list (List.map (multi_subst_lt_in_ty c lts) Ts)
      = multi_subst_lt c lts (lt_of_ty_list Ts))).
  - intros x c lts. reflexivity.
  - intros A l B HA HB c lts. reflexivity.
  - intros K l Ts IHTs c lts. cbn [multi_subst_lt_in_ty]. rewrite !lt_of_ty_ctor_eq.
    cbn [multi_subst_lt]. f_equal.
    change ((fix go (Ts0 : list type) : list type :=
       match Ts0 with [] => [] | A :: rest => multi_subst_lt_in_ty c lts A :: go rest end) Ts)
       with (List.map (multi_subst_lt_in_ty c lts) Ts).
    apply IHTs.
  - intros A HA c lts. reflexivity.
  - intros B A HB HA c lts. reflexivity.
  - intros c lts. reflexivity.
  - intros A Ts HA HTs c lts. cbn [List.map]. rewrite !lt_of_ty_list_cons.
    cbn [multi_subst_lt]. rewrite HA, HTs. reflexivity.
Qed.

Lemma lt_of_ty_inst_lt_vars : forall n lts T,
  lt_of_ty (inst_lt_vars n lts T) = multi_subst_lt 0 lts (lt_of_ty T).
Proof. intros n lts T. unfold inst_lt_vars. apply lt_of_ty_multi_subst_lt_in_ty. Qed.

Lemma lt_of_ty_G_mono_sub : forall G T1 T2, G ⊢ T1 <:: T2 ->
  G ⊢ₗ lt_of_ty_G G T1 <: lt_of_ty_G G T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T Hwf|Γ S0 U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                 |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                 |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2].
  - apply LS_Refl. apply lt_of_ty_G_wf. exact Hwf.
  - eapply LS_Trans; [exact IH1 | exact IH2].
  - unfold lt_of_ty_G.
    assert (Hlt: α < length Γ).
    { destruct (Nat.le_gt_cases (length Γ) α) as [Hle|Hgt]; [|exact Hgt].
      rewrite ctx_lookup_ty_None in Hlk by exact Hle; discriminate. }
    rewrite (lt_of_ty_ctx_var (length Γ) Γ α).
    destruct (length Γ) as [|m] eqn:HL; [lia|].
    rewrite Hlk.
    rewrite (lt_of_ty_ctx_fuel_irrel m (S m) B Γ (S α)
               (ctx_inv_all Γ α B Hlk) ltac:(lia) ltac:(lia)).
    apply LS_Refl. rewrite <- HL. apply lt_of_ty_G_wf. exact HwfB.
  - unfold lt_of_ty_G. rewrite !lt_of_ty_ctx_ctor.
    apply lt_min_mono; [exact Hls |].
    apply LS_Refl. eapply lt_of_ty_G_list_wf; eauto.
  - replace (lt_of_ty_G Γ (type_ctor any_tag Δ [])) with (lt_min Δ lt_free).
    + eapply LS_Trans; [exact Hls |].
      apply LS_MinR1.
      * apply LS_Refl. exact HwfD.
      * constructor.
    + unfold lt_of_ty_G. rewrite lt_of_ty_ctx_ctor, lt_of_ty_ctx_list_nil. reflexivity.
  - unfold lt_of_ty_G. rewrite !lt_of_ty_ctx_fun. exact Hl.
  - unfold lt_of_ty_G. rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
  - unfold lt_of_ty_G. rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
Qed.

Lemma SubstTy_target : forall Sb n G G', SubstTy Sb n G G' ->
  exists B, ctx_lookup_ty G n = Some B /\
    G' ⊢ₗ lt_of_ty_G G' Sb <: lt_of_ty_G G B.
Proof.
  intros Sb n G G' H. induction H.
  - exists (shift_ty 1 0 B). split.
    + reflexivity.
    + rewrite lt_of_ty_G_weaken_ty. apply lt_of_ty_G_mono_sub. exact H.
  - destruct IHSubstTy as [B0 [Hlk Hsub]].
    exists (shift_ty 1 0 B0). split.
    + simpl ctx_lookup_ty. rewrite Hlk. reflexivity.
    + rewrite lt_of_ty_G_weaken_ty. rewrite lt_of_ty_G_weaken_ty.
      apply (lt_sub_InsTy G' (lt_of_ty_G G' Sb) (lt_of_ty_G G B0) Hsub
               0 (bind_ty (subst_ty n Sb B) :: G') (InsTy_here _ _)).
  - destruct IHSubstTy as [B0 [Hlk Hsub]].
    exists (shift_lt_in_ty 1 0 B0). split.
    + simpl ctx_lookup_ty. rewrite Hlk. reflexivity.
    + rewrite lt_of_ty_G_weaken_lt. rewrite lt_of_ty_G_weaken_lt.
      apply (lt_sub_InsLt G' (lt_of_ty_G G' Sb) (lt_of_ty_G G B0) Hsub
               0 (bind_lt D :: G') (InsLt_here _ _)).
  - destruct IHSubstTy as [B0 [Hlk Hsub]].
    exists B0. split.
    + simpl ctx_lookup_ty. exact Hlk.
    + rewrite lt_of_ty_G_weaken_tm. rewrite lt_of_ty_G_weaken_tm.
      apply (lt_sub_InsTm G' (lt_of_ty_G G' Sb) (lt_of_ty_G G B0) Hsub
               (bind_tm (subst_ty n Sb A) :: G') (InsTm_here _ _)).
Qed.

Lemma SubstTy_sub_target : forall Sb n G G', SubstTy Sb n G G' ->
  forall B, ctx_lookup_ty G n = Some B ->
  G' ⊢ Sb <:: subst_ty n Sb B.
Proof.
  intros Sb n G G' H. induction H; intros B0 HB.
  - simpl in HB. injection HB as HB; subst B0.
    rewrite subst_ty_shift_cancel. exact H.
  - simpl in HB. destruct (ctx_lookup_ty G n) as [B'|] eqn:E; simpl in HB; [|discriminate].
    injection HB as HB; subst B0.
    rewrite <- shift_ty_subst_ty_comm0. apply sub_weaken_ty_shift. apply (IHSubstTy B' eq_refl).
  - simpl in HB. destruct (ctx_lookup_ty G n) as [B'|] eqn:E; simpl in HB; [|discriminate].
    injection HB as HB; subst B0.
    rewrite <- shift_lt_in_ty_subst_ty_comm0. apply sub_weaken_lt_shift. apply (IHSubstTy B' eq_refl).
  - simpl in HB. apply IHSubstTy in HB.
    apply (sub_InsTm G' Sb (subst_ty n Sb B0) HB
             (bind_tm (subst_ty n Sb A) :: G') (InsTm_here _ _)).
Qed.

Lemma SubstTy_replacement_wf : forall Sb n G G',
  SubstTy Sb n G G' -> ty_wf G' Sb.
Proof.
  intros Sb n G G' H. induction H.
  - destruct (sub_wf _ _ _ H) as [HwfSb _]. exact HwfSb.
  - eapply ty_wf_InsTy; [exact IHSubstTy|]. apply InsTy_here.
  - eapply ty_wf_InsLt; [exact IHSubstTy|]. apply InsLt_here.
  - eapply ty_wf_InsTm; [exact IHSubstTy|]. apply InsTm_here.
Qed.

Lemma ty_wf_SubstTy : forall G T,
  ty_wf G T -> forall Sb n G', SubstTy Sb n G G' -> ty_wf G' (subst_ty n Sb T)
with types_wf_SubstTy : forall G Ts,
  types_wf G Ts -> forall Sb n G', SubstTy Sb n G G' ->
    types_wf G' (List.map (subst_ty n Sb) Ts).
Proof.
  - intros G T Hwf. induction Hwf; intros Sb n G' HS.
    + destruct (Nat.eq_dec α n) as [Hα|Hα].
      * subst α. rewrite subst_ty_var_eq, Nat.eqb_refl.
        eapply SubstTy_replacement_wf; eauto.
      * rewrite (subst_ty_var_neq n Sb α Hα). econstructor.
        -- rewrite (SubstTy_lookup_ty Sb n Γ G' HS α Hα). rewrite H. reflexivity.
        -- apply (IHHwf Sb n G' HS).
    + rewrite subst_ty_fun_eq. constructor.
      * apply IHHwf1. exact HS.
      * eapply lt_wf_SubstTy_ctx; eauto.
      * apply IHHwf2. exact HS.
    + rewrite subst_ty_ctor_eq. constructor.
      * eapply lt_wf_SubstTy_ctx; eauto.
      * eapply types_wf_SubstTy; eauto.
    + rewrite subst_ty_ltall_eq. constructor.
      apply IHHwf. apply SubstTy_lt. exact HS.
    + rewrite subst_ty_tyall_eq. constructor.
      * apply IHHwf1. exact HS.
      * apply IHHwf2. apply SubstTy_ty. exact HS.
  - intros G Ts Hwf. induction Hwf; intros Sb n G' HS; cbn [List.map].
    + constructor.
    + constructor.
      * eapply ty_wf_SubstTy; eauto.
      * apply (IHHwf Sb n G' HS).
Qed.

Lemma lt_of_ty_ctx_SubstTy_le : forall Sb n G G', SubstTy Sb n G G' ->
  forall f T k, ty_wf G T -> VB k T -> length G <= k + f ->
  G' ⊢ₗ lt_of_ty_ctx f G' (subst_ty n Sb T) <: lt_of_ty_ctx f G T.
Proof.
  intros Sb n G G' HS.
  pose proof (SubstTy_n_lt Sb n G G' HS) as Hn.
  pose proof (SubstTy_S_VB Sb n G G' HS) as HSVB.
  pose proof (SubstTy_length Sb n G G' HS) as HLen.
  destruct (SubstTy_target Sb n G G' HS) as [Btgt [Htgt Hsubtgt]].
  induction f as [|f' IHf]; intros T k HwfT HVB Hlen.
  - rewrite Nat.add_0_r in Hlen. revert k HwfT HVB Hlen.
    induction T using type_list_ind with
      (Q := fun Ts => forall k, types_wf G Ts -> VBL k Ts -> length G <= k ->
              G' ⊢ₗ lt_of_ty_ctx_list 0 G' (List.map (subst_ty n Sb) Ts)
                  <: lt_of_ty_ctx_list 0 G Ts);
      intros k HwfT HVB Hlen.
    + simpl in HVB.
      assert (Hane : n0 <> n) by lia.
      rewrite (subst_ty_var_neq n Sb n0 Hane).
      rewrite !(lt_of_ty_ctx_var 0). apply LS_Refl. constructor.
    + inversion HwfT; subst.
      rewrite subst_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. apply LS_Refl.
      eapply lt_wf_SubstTy_ctx; eauto.
    + rewrite subst_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor.
      inversion HwfT; subst. rewrite VB_ctor in HVB.
      apply lt_min_mono.
      * apply LS_Refl. eapply lt_wf_SubstTy_ctx; eauto.
      * eapply IHT; eauto.
    + rewrite subst_ty_ltall_eq. rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + rewrite subst_ty_tyall_eq. rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + rewrite VBL_cons in HVB. destruct HVB as [Ha Hr].
      inversion HwfT; subst.
      cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons.
      apply lt_min_mono; [eapply IHT; eauto | eapply IHT0; eauto].
  - revert k HwfT HVB Hlen.
    induction T using type_list_ind with
      (Q := fun Ts => forall k, types_wf G Ts -> VBL k Ts -> length G <= k + S f' ->
              G' ⊢ₗ lt_of_ty_ctx_list (S f') G' (List.map (subst_ty n Sb) Ts)
                  <: lt_of_ty_ctx_list (S f') G Ts);
      intros k HwfT HVB Hlen.
    + simpl in HVB.
      destruct (Nat.eq_dec n0 n) as [Hae|Hane].
      * subst n0. rewrite subst_ty_var_eq, Nat.eqb_refl.
        rewrite (lt_of_ty_ctx_fuel_irrel (S f') (length G') Sb G' n HSVB ltac:(lia) ltac:(lia)).
        replace (lt_of_ty_ctx (S f') G (type_var n)) with (lt_of_ty_ctx (length G) G Btgt).
        -- unfold lt_of_ty_G in Hsubtgt. exact Hsubtgt.
        -- rewrite (lt_of_ty_ctx_var (S f') G n), Htgt.
           apply (lt_of_ty_ctx_fuel_irrel (length G) f' Btgt G (S n)
                    (ctx_inv_all G n Btgt Htgt) ltac:(lia) ltac:(lia)).
      * rewrite (subst_ty_var_neq n Sb n0 Hane).
        rewrite (lt_of_ty_ctx_var (S f') G' (slv n n0)).
        rewrite (lt_of_ty_ctx_var (S f') G n0).
        rewrite (SubstTy_lookup_ty Sb n G G' HS n0 Hane).
        destruct (ctx_lookup_ty G n0) as [B0|] eqn:E; simpl.
        -- assert (HwfB0 : ty_wf G B0).
           { inversion HwfT; subst.
             match goal with
             | Hlookup : ctx_lookup_ty G n0 = Some ?B,
               Hbound : ty_wf G ?B |- _ =>
                 rewrite E in Hlookup; inversion Hlookup; subst; exact Hbound
             end. }
           apply (IHf B0 (S n0) HwfB0 (ctx_inv_all G n0 B0 E)). lia.
        -- apply LS_Refl. constructor.
    + inversion HwfT; subst.
      rewrite subst_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. apply LS_Refl.
      eapply lt_wf_SubstTy_ctx; eauto.
    + rewrite subst_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor.
      inversion HwfT; subst. rewrite VB_ctor in HVB.
      apply lt_min_mono.
      * apply LS_Refl. eapply lt_wf_SubstTy_ctx; eauto.
      * eapply IHT; eauto.
    + rewrite subst_ty_ltall_eq. rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + rewrite subst_ty_tyall_eq. rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + rewrite VBL_cons in HVB. destruct HVB as [Ha Hr].
      inversion HwfT; subst.
      cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons.
      apply lt_min_mono; [eapply IHT; eauto | eapply IHT0; eauto].
Qed.

Lemma lt_of_ty_G_SubstTy_le : forall Sb n G G', SubstTy Sb n G G' ->
  forall T, ty_wf G T -> G' ⊢ₗ lt_of_ty_G G' (subst_ty n Sb T) <: lt_of_ty_G G T.
Proof.
  intros Sb n G G' HS T HwfT. unfold lt_of_ty_G.
  pose proof (SubstTy_length Sb n G G' HS) as HL.
  rewrite (lt_of_ty_ctx_fuel_irrel (length G') (length G)
             (subst_ty n Sb T) G' 0 (VB_0 _) ltac:(lia) ltac:(lia)).
  apply (lt_of_ty_ctx_SubstTy_le Sb n G G' HS (length G) T 0 HwfT (VB_0 T) ltac:(lia)).
Qed.

Lemma sub_SubstTy : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall Sb n G', SubstTy Sb n G G' ->
  G' ⊢ subst_ty n Sb T1 <:: subst_ty n Sb T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T Hwf|Γ S0 U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                 |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                 |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2];
    intros Sb n G' HS.
  - apply SA_Refl. eapply ty_wf_SubstTy; eauto.
  - eapply SA_Trans; [apply (IH1 Sb n G' HS) | apply (IH2 Sb n G' HS)].
  - destruct (Nat.eq_dec α n) as [Hae|Hane].
    + subst α. rewrite subst_ty_var_eq, Nat.eqb_refl.
      apply (SubstTy_sub_target Sb n Γ G' HS B Hlk).
    + rewrite (subst_ty_var_neq n Sb α Hane). apply SA_VarCtx.
      * rewrite (SubstTy_lookup_ty Sb n Γ G' HS α Hane). rewrite Hlk. reflexivity.
      * eapply ty_wf_SubstTy; eauto.
  - rewrite !subst_ty_ctor_eq. apply SA_Data.
    + apply (lt_sub_SubstTy_ctx Γ l l' Hls Sb n G' HS).
    + eapply types_wf_SubstTy; eauto.
  - rewrite subst_ty_ctor_eq. cbn [List.map]. apply SA_Any.
    + eapply ty_wf_SubstTy; eauto.
    + eapply lt_wf_SubstTy_ctx; eauto.
    + eapply LS_Trans.
      * apply (lt_of_ty_G_SubstTy_le Sb n Γ G' HS T HwfT).
      * apply (lt_sub_SubstTy_ctx Γ (lt_of_ty_G Γ T) Δ Hls Sb n G' HS).
  - rewrite !subst_ty_fun_eq. apply SA_Fun.
    + apply (IH1 Sb n G' HS).
    + apply (lt_sub_SubstTy_ctx Γ l l' Hl Sb n G' HS).
    + apply (IH2 Sb n G' HS).
  - rewrite !subst_ty_ltall_eq. apply SA_LtAll.
    apply (IH1 (shift_lt_in_ty 1 0 Sb) n (bind_lt lt_local :: G')
             (SubstTy_lt Sb n Γ G' lt_local HS)).
  - rewrite !subst_ty_tyall_eq. apply SA_TyAll.
    + eapply ty_wf_SubstTy; [exact HwfA|]. apply SubstTy_ty. exact HS.
    + eapply ty_wf_SubstTy; [exact HwfA'|]. apply SubstTy_ty. exact HS.
    + apply (IH1 Sb n G' HS).
    + apply (IH2 (shift_ty 1 0 Sb) (S n) (bind_ty (subst_ty n Sb B') :: G')
               (SubstTy_ty Sb n Γ G' B' HS)).
Qed.

(* Subtyping is preserved by type-substitution at the head binder.    *)
Lemma sub_subst_ty : forall Γ B U0 U S,
  (bind_ty B :: Γ) ⊢ U0 <:: U ->
  Γ ⊢ S <:: B ->
  Γ ⊢ subst_ty 0 S U0 <:: subst_ty 0 S U.
Proof.
  intros Γ B U0 U S Hsub HSsub.
  apply (sub_SubstTy (bind_ty B :: Γ) U0 U Hsub S 0 Γ
           (SubstTy_here Γ B S HSsub)).
Qed.

Lemma sub_subst_lt : forall Γ Δ U0 U Δ',
  (bind_lt Δ :: Γ) ⊢ U0 <:: U ->
  Γ ⊢ₗ Δ' <: Δ ->
  Γ ⊢ subst_lt_in_ty 0 Δ' U0 <:: subst_lt_in_ty 0 Δ' U.
Proof.
  intros Γ Δ U0 U Δ' Hsub HltΔ.
  apply (sub_SubstLt (bind_lt Δ :: Γ) U0 U Hsub Δ' 0 Γ).
  apply SubstLt_here. exact HltΔ.
Qed.

(* Narrowing a type-variable bound preserves type well-formedness.     *)
(* This is the small F<: narrowing fragment needed by the unrestricted *)
(* lifetime-substitution T_TyApp case: after substituting lifetimes,   *)
(* we may view [forall α <: B. U] at the tighter bound [S] when        *)
(* [S <: B], and then apply T_TyApp with the self-bound [S].           *)

Inductive NarrowTyWf : type -> type -> ctx -> ctx -> Prop :=
  | NTW_here : forall Bsub Bsup Γ,
      Γ ⊢ Bsub <:: Bsup ->
      NarrowTyWf Bsub Bsup (bind_ty Bsup :: Γ) (bind_ty Bsub :: Γ)
  | NTW_ty : forall Bsub Bsup G G' A,
      NarrowTyWf Bsub Bsup G G' ->
      ty_wf G A ->
      ty_wf G' A ->
      NarrowTyWf Bsub Bsup (bind_ty A :: G) (bind_ty A :: G')
  | NTW_lt : forall Bsub Bsup G G' D,
      NarrowTyWf Bsub Bsup G G' ->
      lt_wf G D ->
      lt_wf G' D ->
      NarrowTyWf Bsub Bsup (bind_lt D :: G) (bind_lt D :: G').

Lemma NarrowTyWf_lookup_lt : forall Bsub Bsup G G',
  NarrowTyWf Bsub Bsup G G' ->
  forall x, ctx_lookup_lt G x = ctx_lookup_lt G' x.
Proof.
  intros Bsub Bsup G G' H. induction H; intro x.
  - simpl. reflexivity.
  - simpl. apply IHNarrowTyWf.
  - destruct x as [|x']; simpl.
    + reflexivity.
    + rewrite (IHNarrowTyWf x'). reflexivity.
Qed.

Lemma ty_wf_unshift_ty : forall Γ B S T,
  Γ ⊢ S <:: B ->
  ty_wf (bind_ty B :: Γ) (shift_ty 1 0 T) ->
  ty_wf Γ T.
Proof.
  intros Γ B S T Hsub Hwf.
  pose proof (ty_wf_SubstTy (bind_ty B :: Γ) (shift_ty 1 0 T) Hwf
               S 0 Γ (SubstTy_here Γ B S Hsub)) as HwfSub.
  rewrite subst_ty_shift_cancel in HwfSub. exact HwfSub.
Qed.

Lemma ty_wf_unshift_lt : forall Γ D R T,
  Γ ⊢ₗ R <: D ->
  ty_wf (bind_lt D :: Γ) (shift_lt_in_ty 1 0 T) ->
  ty_wf Γ T.
Proof.
  intros Γ D R T Hsub Hwf.
  pose proof (ty_wf_SubstLt (bind_lt D :: Γ) (shift_lt_in_ty 1 0 T) Hwf
               R 0 Γ (SubstLt_here Γ D R Hsub)) as HwfSub.
  rewrite subst_lt_in_ty_shift_cancel in HwfSub. exact HwfSub.
Qed.

Lemma lt_wf_NarrowTyWf : forall Bsub Bsup G G',
  NarrowTyWf Bsub Bsup G G' ->
  forall l, lt_wf G l -> lt_wf G' l.
Proof.
  intros Bsub Bsup G G' HN l Hwf.
  revert G' HN.
  induction Hwf.
  all: intros G' HN.
  - apply LWF_Var with (Δ := Δ).
    rewrite <- (NarrowTyWf_lookup_lt Bsub Bsup Γ G' HN x). exact H.
  - apply LWF_Free.
  - apply LWF_Local.
  - apply LWF_Min; [apply (IHHwf1 G' HN) | apply (IHHwf2 G' HN)].
Qed.

Lemma lt_sub_NarrowTyWf : forall Bsub Bsup G G',
  NarrowTyWf Bsub Bsup G G' ->
  forall l1 l2, G ⊢ₗ l1 <: l2 -> G' ⊢ₗ l1 <: l2.
Proof.
  intros Bsub Bsup G G' HN l1 l2 H.
  revert G' HN.
  induction H.
  all: intros G' HN.
  - apply LS_Free. eapply lt_wf_NarrowTyWf; eauto.
  - apply LS_Local. eapply lt_wf_NarrowTyWf; eauto.
  - apply LS_Var with (Δ := Δ);
      [rewrite <- (NarrowTyWf_lookup_lt Bsub Bsup Γ G' HN x); exact H |
       eapply lt_wf_NarrowTyWf; eauto].
  - apply LS_Refl. eapply lt_wf_NarrowTyWf; eauto.
  - eapply LS_Trans; eauto.
  - apply LS_MinL; eauto.
  - apply LS_MinR1; eauto. eapply lt_wf_NarrowTyWf; eauto.
  - apply LS_MinR2; eauto. eapply lt_wf_NarrowTyWf; eauto.
Qed.

Lemma NarrowTyWf_lookup_sub : forall Bsub Bsup G G',
  NarrowTyWf Bsub Bsup G G' ->
  forall α U, ctx_lookup_ty G α = Some U -> ty_wf G U ->
    exists U', ctx_lookup_ty G' α = Some U'
            /\ G ⊢ U' <:: U
            /\ G' ⊢ U' <:: U.
Proof.
  intros Bsub Bsup G G' HN.
  induction HN as [Bsub Bsup Γ Hsub
                  |Bsub Bsup G G' A HN IH HwfA HwfA'
                  |Bsub Bsup G G' D HN IH HwfD HwfD']; intros α U Hlk HwfU.
  - destruct α as [|n].
    + simpl in Hlk. injection Hlk; intros; subst U.
      exists (shift_ty 1 0 Bsub). split; [reflexivity|]. split.
      * apply (sub_weaken_ty_shift Γ Bsup Bsub Bsup Hsub).
      * apply (sub_weaken_ty_shift Γ Bsub Bsub Bsup Hsub).
    + simpl in Hlk.
      destruct (ctx_lookup_ty Γ n) as [W|] eqn:E; simpl in Hlk; [|discriminate].
      injection Hlk; intros; subst U.
      assert (HwfW : ty_wf Γ W).
      { eapply ty_wf_unshift_ty; [exact Hsub|exact HwfU]. }
      assert (HwfTarget : ty_wf (bind_ty Bsub :: Γ) (shift_ty 1 0 W)).
      { eapply ty_wf_InsTy; [exact HwfW|apply InsTy_here]. }
      exists (shift_ty 1 0 W). split; [simpl; rewrite E; reflexivity|].
      split; apply SA_Refl; assumption.
  - destruct α as [|n].
    + simpl in Hlk. injection Hlk; intros; subst U.
      assert (HwfTarget : ty_wf (bind_ty A :: G') (shift_ty 1 0 A)).
      { eapply ty_wf_InsTy; [exact HwfA'|apply InsTy_here]. }
      exists (shift_ty 1 0 A). simpl. split; [reflexivity|]. split; apply SA_Refl; assumption.
    + simpl in Hlk. destruct (ctx_lookup_ty G n) as [W|] eqn:E; simpl in Hlk;
        [|discriminate].
      injection Hlk; intros; subst U.
      assert (HwfW : ty_wf G W).
      { eapply ty_wf_unshift_ty; [apply SA_Refl; exact HwfA|exact HwfU]. }
      destruct (IH n W E HwfW) as [W' [HW' [HsubG HsubG']]].
      exists (shift_ty 1 0 W'). simpl. rewrite HW'. simpl.
      split; [reflexivity|]. split.
      * apply (sub_weaken_ty_shift G A W' W HsubG).
      * apply (sub_weaken_ty_shift G' A W' W HsubG').
  - simpl in Hlk.
    destruct (ctx_lookup_ty G α) as [W|] eqn:E; simpl in Hlk; [|discriminate].
    injection Hlk; intros; subst U.
    assert (HwfW : ty_wf G W).
    { eapply ty_wf_unshift_lt; [apply LS_Refl; exact HwfD|exact HwfU]. }
    destruct (IH α W E HwfW) as [W' [HW' [HsubG HsubG']]].
    exists (shift_lt_in_ty 1 0 W'). simpl. rewrite HW'. simpl.
    split; [reflexivity|]. split.
    + apply (sub_weaken_lt_shift G D W' W HsubG).
    + apply (sub_weaken_lt_shift G' D W' W HsubG').
Qed.

Scheme ty_wf_st_mutind := Induction for ty_wf Sort Prop
with types_wf_st_mutind := Induction for types_wf Sort Prop.
Combined Scheme ty_wf_types_wf_st_mutind from ty_wf_st_mutind, types_wf_st_mutind.

Lemma ty_wf_NarrowTyWf_all :
  (forall G T, ty_wf G T -> forall Bsub Bsup G',
      NarrowTyWf Bsub Bsup G G' -> ty_wf G' T) /\
  (forall G Ts, types_wf G Ts -> forall Bsub Bsup G',
      NarrowTyWf Bsub Bsup G G' -> types_wf G' Ts).
Proof.
  apply (ty_wf_types_wf_st_mutind
    (fun G T _ => forall Bsub Bsup G', NarrowTyWf Bsub Bsup G G' -> ty_wf G' T)
    (fun G Ts _ => forall Bsub Bsup G', NarrowTyWf Bsub Bsup G G' -> types_wf G' Ts)).
  - intros Γ α B Hlk HwfB IHBound Bsub Bsup G' HN.
    destruct (NarrowTyWf_lookup_sub Bsub Bsup Γ G' HN α B Hlk HwfB)
      as [B' [HB' [_ HsubG']]].
    destruct (sub_wf _ _ _ HsubG') as [HwfB' _].
    econstructor; eauto.
  - intros Γ A l B HwfA IHA Hwfl HwfB IHB Bsub Bsup G' HN.
    constructor.
    + apply (IHA Bsub Bsup G' HN).
    + eapply lt_wf_NarrowTyWf; eauto.
    + apply (IHB Bsub Bsup G' HN).
  - intros Γ K l Ts Hwfl HwfTs IHTs Bsub Bsup G' HN.
    constructor.
    + eapply lt_wf_NarrowTyWf; eauto.
    + apply (IHTs Bsub Bsup G' HN).
  - intros Γ A HwfA IHA Bsub Bsup G' HN.
    constructor. apply (IHA Bsub Bsup (bind_lt lt_local :: G')).
    apply NTW_lt; [exact HN|constructor|constructor].
  - intros Γ B A HwfB IHB HwfA IHA Bsub Bsup G' HN.
    constructor.
    + apply (IHB Bsub Bsup G' HN).
    + apply (IHA Bsub Bsup (bind_ty B :: G')).
      apply NTW_ty.
      * exact HN.
      * exact HwfB.
      * apply (IHB Bsub Bsup G' HN).
  - intros Γ Bsub Bsup G' HN. constructor.
  - intros Γ T Ts HwfT IHT HwfTs IHTs Bsub Bsup G' HN.
    constructor.
    + apply (IHT Bsub Bsup G' HN).
    + apply (IHTs Bsub Bsup G' HN).
Qed.

Lemma ty_wf_NarrowTyWf : forall Bsub Bsup G G',
  NarrowTyWf Bsub Bsup G G' -> forall T, ty_wf G T -> ty_wf G' T.
Proof.
  intros Bsub Bsup G G' HN T Hwf.
  exact (proj1 ty_wf_NarrowTyWf_all G T Hwf Bsub Bsup G' HN).
Qed.

Lemma type_ty_all_narrow_bound : forall Γ Bsub Bsup U,
  Γ ⊢ Bsub <:: Bsup ->
  ty_wf (bind_ty Bsup :: Γ) U ->
  Γ ⊢ type_ty_all Bsup U <:: type_ty_all Bsub U.
Proof.
  intros Γ Bsub Bsup U Hsub HwfU.
  eapply SA_TyAll.
  - exact HwfU.
  - eapply ty_wf_NarrowTyWf; [apply NTW_here; exact Hsub|exact HwfU].
  - exact Hsub.
  - apply SA_Refl. eapply ty_wf_NarrowTyWf; [apply NTW_here; exact Hsub|exact HwfU].
Qed.

