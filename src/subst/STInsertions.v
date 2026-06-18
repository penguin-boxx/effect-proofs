Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import STShiftLaws.

(* ================================================================== *)
(* Depth-general bind_ty weakening for subtyping.                     *)
(*                                                                    *)
(* InsTy c G G' : G' is G with one bind_ty inserted after c ty-binders*)
(* (counted from the head).  Subtyping is closed under InsTy, with    *)
(* types shifted by `shift_ty 1 c`.  `sub_weaken_ty_shift` is the     *)
(* front (c = 0) instance.                                            *)
(* ================================================================== *)

(* Shift swap law (different cutoffs); needed for the head bind_ty case. *)
Lemma shift_ty_swap : forall T c1 c2, c1 <= c2 ->
  shift_ty 1 c1 (shift_ty 1 c2 T) = shift_ty 1 (S c2) (shift_ty 1 c1 T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall c1 c2, c1 <= c2 ->
      shift_ty 1 c1 (shift_ty 1 c2 T) = shift_ty 1 (S c2) (shift_ty 1 c1 T))
    (fun Ts => forall c1 c2, c1 <= c2 ->
      List.map (shift_ty 1 c1) (List.map (shift_ty 1 c2) Ts)
      = List.map (shift_ty 1 (S c2)) (List.map (shift_ty 1 c1) Ts))).
  - intros n c1 c2 Hle.
    rewrite !shift_ty_var_eq. f_equal.
    destruct (Nat.leb c2 n) eqn:E2.
    + apply Nat.leb_le in E2.
      rewrite (proj2 (Nat.leb_le c1 n)) by lia.
      rewrite (proj2 (Nat.leb_le c1 (n+1))) by lia.
      rewrite (proj2 (Nat.leb_le (S c2) (n+1))) by lia.
      reflexivity.
    + apply Nat.leb_gt in E2.
      destruct (Nat.leb c1 n) eqn:E1.
      * apply Nat.leb_le in E1.
        rewrite (proj2 (Nat.leb_gt (S c2) (n+1))) by lia. reflexivity.
      * apply Nat.leb_gt in E1.
        rewrite (proj2 (Nat.leb_gt (S c2) n)) by lia. reflexivity.
  - intros A l B HA HB c1 c2 Hle.
    simpl. rewrite HA by lia. rewrite HB by lia. reflexivity.
  - intros K l Ts HTs c1 c2 Hle.
    rewrite !shift_ty_ctor_eq. f_equal. apply HTs. lia.
  - intros A HA c1 c2 Hle.
    simpl. rewrite HA by lia. reflexivity.
  - intros B A HB HA c1 c2 Hle.
    simpl. rewrite HB by lia. rewrite HA by lia. reflexivity.
  - intros c1 c2 Hle. reflexivity.
  - intros A Ts HA HTs c1 c2 Hle.
    simpl. rewrite HA by lia. f_equal. apply HTs. lia.
Qed.

Lemma shift_ty_swap_0 : forall T c,
  shift_ty 1 0 (shift_ty 1 c T) = shift_ty 1 (S c) (shift_ty 1 0 T).
Proof. intros T c. apply shift_ty_swap. lia. Qed.

Lemma shift_ty_lift_shift : forall a c T,
  shift_ty a 0 (shift_ty 1 c T) = shift_ty 1 (a + c) (shift_ty a 0 T).
Proof.
  induction a as [|a IH]; intros c T.
  - rewrite !shift_ty_zero. reflexivity.
  - replace (shift_ty (S a) 0 (shift_ty 1 c T))
      with (shift_ty 1 0 (shift_ty a 0 (shift_ty 1 c T))).
    2:{ rewrite shift_ty_fuse. replace (1 + a) with (S a) by lia. reflexivity. }
    rewrite IH.
    rewrite shift_ty_swap_0.
    replace (S (a + c)) with (S a + c) by lia.
    rewrite shift_ty_fuse. replace (1 + a) with (S a) by lia. reflexivity.
Qed.

Lemma shift_ty_ctor_sig_swap_0 : forall sig c,
  shift_ty_ctor_sig 1 0 (shift_ty_ctor_sig 1 c sig) =
  shift_ty_ctor_sig 1 (S c) (shift_ty_ctor_sig 1 0 sig).
Proof.
  intros [[[n_lt n_ty] fields] result] c. unfold shift_ty_ctor_sig. simpl.
  f_equal.
  - f_equal. rewrite !List.map_map. apply List.map_ext. intro T.
    replace (n_ty + 0) with n_ty by lia.
    replace (n_ty + S c) with (S (n_ty + c)) by lia.
    apply shift_ty_swap. lia.
  - replace (n_ty + 0) with n_ty by lia.
    replace (n_ty + S c) with (S (n_ty + c)) by lia.
    apply shift_ty_swap. lia.
Qed.

Lemma shift_ty_eff_sig_swap_0 : forall sig c,
  shift_ty_eff_sig 1 0 (shift_ty_eff_sig 1 c sig) =
  shift_ty_eff_sig 1 (S c) (shift_ty_eff_sig 1 0 sig).
Proof.
  intros [[[n_α n_β] sig_ty] ret_ty] c. unfold shift_ty_eff_sig. simpl.
  f_equal.
  - f_equal. replace (n_α + n_β + 0) with (n_α + n_β) by lia.
    replace (n_α + n_β + S c) with (S (n_α + n_β + c)) by lia.
    apply shift_ty_swap. lia.
  - replace (n_α + n_β + 0) with (n_α + n_β) by lia.
    replace (n_α + n_β + S c) with (S (n_α + n_β + c)) by lia.
    apply shift_ty_swap. lia.
Qed.

Lemma shift_ty_ctor_sig_shift_lt_comm : forall sig c,
  shift_lt_ctor_sig 1 0 (shift_ty_ctor_sig 1 c sig) =
  shift_ty_ctor_sig 1 c (shift_lt_ctor_sig 1 0 sig).
Proof.
  intros [[[n_lt n_ty] fields] result] c. unfold shift_lt_ctor_sig, shift_ty_ctor_sig. simpl.
  f_equal.
  - f_equal. rewrite !List.map_map. apply List.map_ext. intro T.
    symmetry. apply shift_ty_shift_lt_in_ty_commute.
  - symmetry. apply shift_ty_shift_lt_in_ty_commute.
Qed.

Lemma shift_ty_eff_sig_shift_lt_comm : forall sig c,
  shift_lt_eff_sig 1 0 (shift_ty_eff_sig 1 c sig) =
  shift_ty_eff_sig 1 c (shift_lt_eff_sig 1 0 sig).
Proof.
  intros [[[n_α n_β] sig_ty] ret_ty] c. unfold shift_lt_eff_sig, shift_ty_eff_sig. simpl.
  f_equal; [f_equal|]; symmetry; apply shift_ty_shift_lt_in_ty_commute.
Qed.

Inductive InsTy : nat -> ctx -> ctx -> Prop :=
  | InsTy_here : forall B G, InsTy 0 G (bind_ty B :: G)
  | InsTy_ty : forall c G G' A,
      InsTy c G G' -> InsTy (S c) (bind_ty A :: G) (bind_ty (shift_ty 1 c A) :: G')
  | InsTy_lt : forall c G G' D,
      InsTy c G G' -> InsTy c (bind_lt D :: G) (bind_lt D :: G')
  | InsTy_tm : forall c G G' T,
      InsTy c G G' -> InsTy c (bind_tm T :: G) (bind_tm (shift_ty 1 c T) :: G')
  | InsTy_ctor : forall c G G' tg n1 n2 Ts Tr,
      InsTy c G G' ->
      InsTy c (bind_ctor tg n1 n2 Ts Tr :: G)
        (bind_ctor tg n1 n2 (List.map (shift_ty 1 (n2 + c)) Ts)
                  (shift_ty 1 (n2 + c) Tr) :: G')
  | InsTy_eff : forall c G G' eg m1 m2 Ts Tr,
      InsTy c G G' ->
      InsTy c (bind_eff eg m1 m2 Ts Tr :: G)
        (bind_eff eg m1 m2 (shift_ty 1 (m1 + m2 + c) Ts)
                  (shift_ty 1 (m1 + m2 + c) Tr) :: G').

Definition shv (c a : nat) : nat := if Nat.leb c a then S a else a.

Lemma InsTy_lookup_ty : forall c G G', InsTy c G G' ->
  forall a, ctx_lookup_ty G' (shv c a)
            = option_map (shift_ty 1 c) (ctx_lookup_ty G a).
Proof.
  intros c G G' H. induction H; intro a.
  - unfold shv; simpl Nat.leb.
    destruct a as [|a']; reflexivity.
  - destruct a as [|a'].
    + unfold shv; simpl Nat.leb. simpl ctx_lookup_ty.
      rewrite shift_ty_swap_0. reflexivity.
    + specialize (IHInsTy a').
      destruct (Nat.leb c a') eqn:E.
      * assert (E2 : shv (S c) (S a') = S (S a')).
        { unfold shv. apply Nat.leb_le in E. rewrite (proj2 (Nat.leb_le (S c)(S a'))) by lia. reflexivity. }
        rewrite E2. unfold shv in IHInsTy. rewrite E in IHInsTy.
        simpl ctx_lookup_ty.
        rewrite IHInsTy.
        destruct (ctx_lookup_ty G a') as [X|]; simpl; [rewrite shift_ty_swap_0; reflexivity | reflexivity].
      * apply Nat.leb_gt in E.
        assert (E2 : shv (S c) (S a') = S a').
        { unfold shv. rewrite (proj2 (Nat.leb_gt (S c)(S a'))) by lia. reflexivity. }
        rewrite E2. unfold shv in IHInsTy. rewrite (proj2 (Nat.leb_gt c a')) in IHInsTy by lia.
        simpl ctx_lookup_ty.
        rewrite IHInsTy.
        destruct (ctx_lookup_ty G a') as [X|]; simpl; [rewrite shift_ty_swap_0; reflexivity | reflexivity].
  - specialize (IHInsTy a). simpl ctx_lookup_ty. rewrite IHInsTy.
    destruct (ctx_lookup_ty G a) as [X|]; simpl;
      [rewrite shift_ty_shift_lt_in_ty_commute; reflexivity | reflexivity].
  - specialize (IHInsTy a). simpl ctx_lookup_ty. apply IHInsTy.
  - specialize (IHInsTy a). simpl ctx_lookup_ty. apply IHInsTy.
  - specialize (IHInsTy a). simpl ctx_lookup_ty. apply IHInsTy.
Qed.

Lemma InsTy_lookup_lt : forall c G G', InsTy c G G' ->
  forall x, ctx_lookup_lt G' x = ctx_lookup_lt G x.
Proof.
  intros c G G' H. induction H; intro x; simpl; try (apply IHInsTy).
  - reflexivity.
  - destruct x as [|x']; simpl.
    + reflexivity.
    + rewrite IHInsTy. reflexivity.
Qed.

Lemma InsTy_lookup_tm : forall c G G', InsTy c G G' ->
  forall x, ctx_lookup_tm G' x = option_map (shift_ty 1 c) (ctx_lookup_tm G x).
Proof.
  intros c G G' H. induction H; intro x.
  - simpl ctx_lookup_tm. reflexivity.
  - simpl ctx_lookup_tm. rewrite IHInsTy.
    destruct (ctx_lookup_tm G x) as [T|]; simpl;
      [rewrite shift_ty_swap_0|]; reflexivity.
  - simpl ctx_lookup_tm. rewrite IHInsTy.
    destruct (ctx_lookup_tm G x) as [T|]; simpl;
      [rewrite shift_ty_shift_lt_in_ty_commute|]; reflexivity.
  - destruct x as [|x']; simpl ctx_lookup_tm.
    + reflexivity.
    + apply IHInsTy.
  - simpl ctx_lookup_tm. apply IHInsTy.
  - simpl ctx_lookup_tm. apply IHInsTy.
Qed.

Lemma InsTy_lookup_ctor : forall c G G', InsTy c G G' ->
  forall K, ctx_lookup_ctor G' K = option_map (shift_ty_ctor_sig 1 c) (ctx_lookup_ctor G K).
Proof.
  intros c G G' H. induction H; intro K.
  - simpl. reflexivity.
  - simpl. rewrite IHInsTy. destruct (ctx_lookup_ctor G K) as [sig|] eqn:E; cbn [option_map].
    + rewrite shift_ty_ctor_sig_swap_0. reflexivity.
    + reflexivity.
  - simpl. rewrite IHInsTy. destruct (ctx_lookup_ctor G K) as [sig|] eqn:E; cbn [option_map].
    + rewrite shift_ty_ctor_sig_shift_lt_comm. reflexivity.
    + reflexivity.
  - simpl. apply IHInsTy.
  - simpl. destruct (Nat.eqb K tg); [reflexivity|apply IHInsTy].
  - simpl. apply IHInsTy.
Qed.

Lemma InsTy_lookup_eff : forall c G G', InsTy c G G' ->
  forall E, ctx_lookup_eff G' E = option_map (shift_ty_eff_sig 1 c) (ctx_lookup_eff G E).
Proof.
  intros c G G' H. induction H; intro E.
  - simpl. reflexivity.
  - simpl. rewrite IHInsTy. destruct (ctx_lookup_eff G E) as [sig|] eqn:Ef; cbn [option_map].
    + rewrite shift_ty_eff_sig_swap_0. reflexivity.
    + reflexivity.
  - simpl. rewrite IHInsTy. destruct (ctx_lookup_eff G E) as [sig|] eqn:Ef; cbn [option_map].
    + rewrite shift_ty_eff_sig_shift_lt_comm. reflexivity.
    + reflexivity.
  - simpl. apply IHInsTy.
  - simpl. apply IHInsTy.
  - simpl. destruct (Nat.eqb E eg); [reflexivity|apply IHInsTy].
Qed.

Lemma shift_ty_fun_eq : forall a c A l B,
  shift_ty a c (type_fun A l B) = type_fun (shift_ty a c A) l (shift_ty a c B).
Proof. reflexivity. Qed.
Lemma shift_ty_ltall_eq : forall a c A,
  shift_ty a c (type_lt_all A) = type_lt_all (shift_ty a c A).
Proof. reflexivity. Qed.
Lemma shift_ty_tyall_eq : forall a c B A,
  shift_ty a c (type_ty_all B A) = type_ty_all (shift_ty a c B) (shift_ty a (S c) A).
Proof. reflexivity. Qed.

Lemma shv_shift : forall c n, shift_ty 1 c (type_var n) = type_var (shv c n).
Proof.
  intros c n. rewrite shift_ty_var_eq. unfold shv.
  destruct (Nat.leb c n); [rewrite Nat.add_1_r|]; reflexivity.
Qed.

Lemma InsTy_length : forall c G G', InsTy c G G' -> length G' = S (length G).
Proof. intros c G G' H. induction H; simpl; lia. Qed.

Lemma lt_of_ty_ctx_InsTy : forall c G G', InsTy c G G' ->
  forall f T, lt_of_ty_ctx f G' (shift_ty 1 c T) = lt_of_ty_ctx f G T.
Proof.
  intros c G G' HIns f. induction f as [|f' IHf]; intro T.
  - induction T using type_list_ind with
      (Q := fun Ts => lt_of_ty_ctx_list 0 G' (List.map (shift_ty 1 c) Ts)
                      = lt_of_ty_ctx_list 0 G Ts).
    + rewrite shv_shift. rewrite !(lt_of_ty_ctx_var 0). reflexivity.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_fun. reflexivity.
    + rewrite shift_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor. f_equal. exact IHT.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite IHT, IHT0. reflexivity.
  - induction T using type_list_ind with
      (Q := fun Ts => lt_of_ty_ctx_list (S f') G' (List.map (shift_ty 1 c) Ts)
                      = lt_of_ty_ctx_list (S f') G Ts).
    + rewrite shv_shift.
      rewrite (lt_of_ty_ctx_var (S f') G' (shv c n)), (lt_of_ty_ctx_var (S f') G n).
      rewrite (InsTy_lookup_ty c G G' HIns n).
      destruct (ctx_lookup_ty G n) as [B|] eqn:E; simpl.
      * apply IHf.
      * reflexivity.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_fun. reflexivity.
    + rewrite shift_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor. f_equal. exact IHT.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + simpl shift_ty. rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite IHT, IHT0. reflexivity.
Qed.

Lemma lt_of_ty_G_InsTy : forall c G G', InsTy c G G' ->
  forall T, lt_of_ty_G G' (shift_ty 1 c T) = lt_of_ty_G G T.
Proof.
  intros c G G' HIns T. unfold lt_of_ty_G.
  rewrite (InsTy_length c G G' HIns).
  rewrite (lt_of_ty_ctx_InsTy c G G' HIns (S (length G)) T).
  apply (lt_of_ty_ctx_fuel_irrel (S (length G)) (length G) T G 0).
  - apply VB_0.
  - simpl; lia.
  - simpl; lia.
Qed.

Lemma lt_wf_InsTy : forall G l,
  lt_wf G l -> forall c G', InsTy c G G' -> lt_wf G' l.
Proof.
  intros G l Hwf. induction Hwf; intros c G' HIns.
  - econstructor. rewrite (InsTy_lookup_lt c Γ G' HIns x). exact H.
  - constructor.
  - constructor.
  - constructor.
    + apply (IHHwf1 c G' HIns).
    + apply (IHHwf2 c G' HIns).
Qed.

Lemma lifetimes_wf_InsTy : forall G lts,
  lifetimes_wf G lts -> forall c G', InsTy c G G' -> lifetimes_wf G' lts.
Proof.
  intros G lts Hwf. induction Hwf; intros c G' HIns.
  - constructor.
  - constructor.
    + eapply lt_wf_InsTy; eauto.
    + apply (IHHwf c G' HIns).
Qed.

Lemma ty_wf_InsTy : forall G T,
  ty_wf G T -> forall c G', InsTy c G G' -> ty_wf G' (shift_ty 1 c T)
with types_wf_InsTy : forall G Ts,
  types_wf G Ts -> forall c G', InsTy c G G' -> types_wf G' (List.map (shift_ty 1 c) Ts).
Proof.
  - intros G T Hwf. induction Hwf; intros c G' HIns.
    + rewrite shv_shift. econstructor.
      * rewrite (InsTy_lookup_ty c Γ G' HIns α). rewrite H. reflexivity.
      * apply IHHwf. exact HIns.
    + rewrite shift_ty_fun_eq. constructor.
      * apply IHHwf1. exact HIns.
      * eapply lt_wf_InsTy; eauto.
      * apply IHHwf2. exact HIns.
    + rewrite shift_ty_ctor_eq. constructor.
      * eapply lt_wf_InsTy; eauto.
      * eapply types_wf_InsTy; eauto.
    + rewrite shift_ty_ltall_eq. constructor.
      apply IHHwf. apply InsTy_lt. exact HIns.
    + rewrite shift_ty_tyall_eq. constructor.
      * apply IHHwf1. exact HIns.
      * apply IHHwf2. apply InsTy_ty. exact HIns.
  - intros G Ts Hwf. induction Hwf; intros c G' HIns; cbn [List.map].
    + constructor.
    + constructor.
      * eapply ty_wf_InsTy; eauto.
      * auto.
Qed.

Lemma lt_sub_InsTy : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall c G', InsTy c G G' -> G' ⊢ₗ l1 <: l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l Hwf|Γ l Hwf|Γ x Δ Hlk Hwf|Γ l Hwf
                 |Γ l1 l2 l3 H1 IH1 H2 IH2|Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H1 IH1 Hwf2|Γ l l1 l2 H1 IH1 Hwf1];
    intros c G' HIns.
  - apply LS_Free. eapply lt_wf_InsTy; eauto.
  - apply LS_Local. eapply lt_wf_InsTy; eauto.
  - apply LS_Var.
    + rewrite (InsTy_lookup_lt c Γ G' HIns x). exact Hlk.
    + eapply lt_wf_InsTy; eauto.
  - apply LS_Refl. eapply lt_wf_InsTy; eauto.
  - eapply LS_Trans; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - apply LS_MinL; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - apply LS_MinR1.
    + apply (IH1 c G' HIns).
    + eapply lt_wf_InsTy; eauto.
  - apply LS_MinR2.
    + apply (IH1 c G' HIns).
    + eapply lt_wf_InsTy; eauto.
Qed.

Lemma sub_InsTy : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall c G', InsTy c G G' -> G' ⊢ shift_ty 1 c T1 <:: shift_ty 1 c T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T Hwf|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                 |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                 |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2];
    intros c G' HIns.
  - apply SA_Refl. eapply ty_wf_InsTy; eauto.
  - eapply SA_Trans; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - rewrite shv_shift. apply SA_VarCtx.
    + rewrite (InsTy_lookup_ty c Γ G' HIns α). rewrite Hlk. reflexivity.
    + eapply ty_wf_InsTy; eauto.
  - rewrite !shift_ty_ctor_eq. apply SA_Data.
    + apply (lt_sub_InsTy Γ l l' Hls c G' HIns).
    + eapply types_wf_InsTy; eauto.
  - rewrite shift_ty_ctor_eq. cbn [List.map]. apply SA_Any.
    + eapply ty_wf_InsTy; eauto.
    + eapply lt_wf_InsTy; eauto.
    + rewrite (lt_of_ty_G_InsTy c Γ G' HIns T).
      apply (lt_sub_InsTy Γ (lt_of_ty_G Γ T) Δ Hls c G' HIns).
  - rewrite !shift_ty_fun_eq. apply SA_Fun.
    + apply (IH1 c G' HIns).
    + apply (lt_sub_InsTy Γ l l' Hl c G' HIns).
    + apply (IH2 c G' HIns).
  - rewrite !shift_ty_ltall_eq. apply SA_LtAll.
    apply (IH1 c (bind_lt lt_local :: G') (InsTy_lt c Γ G' lt_local HIns)).
  - rewrite !shift_ty_tyall_eq. eapply SA_TyAll.
    + eapply ty_wf_InsTy; [exact HwfA|]. apply InsTy_ty. exact HIns.
    + eapply ty_wf_InsTy; [exact HwfA'|]. apply InsTy_ty. exact HIns.
    + apply (IH1 c G' HIns).
    + apply (IH2 (S c) (bind_ty (shift_ty 1 c B') :: G') (InsTy_ty c Γ G' B' HIns)).
Qed.

(* ---- Subtyping weakening (correctly shifted) -------------------- *)

(* Correct context weakening for subtyping.  Inserting a `bind_ty`      *)
(* binding at the front shifts the type-variable namespace by one, so   *)
(* the related types must be shifted by `shift_ty 1 0`.  (The earlier   *)
(* no-shift `sub_weaken_cons` omitted this shift and was unsound:       *)
(* prepending a binding silently re-captured the de Bruijn indices.)    *)
(* Standard weakening metatheory; now derived from `sub_InsTy`.         *)
Lemma sub_weaken_ty_shift : forall Γ B T1 T2,
  Γ ⊢ T1 <:: T2 ->
  (bind_ty B :: Γ) ⊢ shift_ty 1 0 T1 <:: shift_ty 1 0 T2.
Proof.
  intros Γ B T1 T2 H. apply (sub_InsTy Γ T1 T2 H 0 (bind_ty B :: Γ)). apply InsTy_here.
Qed.

(* Likewise, inserting a `bind_lt` binding shifts the lifetime         *)
(* namespace inside types by one.  Derived from `sub_InsLt`.           *)

(* ===== InsLt: depth-general bind_lt weakening ===== *)

Lemma shift_lt_var_eq : forall a c n,
  shift_lt a c (lt_var n) = lt_var (if Nat.leb c n then n + a else n).
Proof. reflexivity. Qed.

(* swap law for shift_lt (lifetimes) *)
Lemma shift_lt_swap : forall l c1 c2, c1 <= c2 ->
  shift_lt 1 c1 (shift_lt 1 c2 l) = shift_lt 1 (S c2) (shift_lt 1 c1 l).
Proof.
  induction l as [n| | |l1 IH1 l2 IH2]; intros c1 c2 Hle.
  - rewrite !shift_lt_var_eq. f_equal.
    destruct (Nat.leb c2 n) eqn:E2.
    + apply Nat.leb_le in E2.
      rewrite (proj2 (Nat.leb_le c1 n)) by lia.
      rewrite (proj2 (Nat.leb_le c1 (n+1))) by lia.
      rewrite (proj2 (Nat.leb_le (S c2) (n+1))) by lia.
      reflexivity.
    + apply Nat.leb_gt in E2.
      destruct (Nat.leb c1 n) eqn:E1.
      * apply Nat.leb_le in E1.
        rewrite (proj2 (Nat.leb_gt (S c2) (n+1))) by lia. reflexivity.
      * apply Nat.leb_gt in E1.
        rewrite (proj2 (Nat.leb_gt (S c2) n)) by lia. reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IH1 by lia. rewrite IH2 by lia. reflexivity.
Qed.

Lemma shift_lt_swap_0 : forall l c,
  shift_lt 1 0 (shift_lt 1 c l) = shift_lt 1 (S c) (shift_lt 1 0 l).
Proof. intros l c. apply shift_lt_swap. lia. Qed.

(* swap law for shift_lt_in_ty (types) *)
Lemma shift_lt_in_ty_swap : forall T c1 c2, c1 <= c2 ->
  shift_lt_in_ty 1 c1 (shift_lt_in_ty 1 c2 T)
  = shift_lt_in_ty 1 (S c2) (shift_lt_in_ty 1 c1 T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall c1 c2, c1 <= c2 ->
      shift_lt_in_ty 1 c1 (shift_lt_in_ty 1 c2 T)
      = shift_lt_in_ty 1 (S c2) (shift_lt_in_ty 1 c1 T))
    (fun Ts => forall c1 c2, c1 <= c2 ->
      List.map (shift_lt_in_ty 1 c1) (List.map (shift_lt_in_ty 1 c2) Ts)
      = List.map (shift_lt_in_ty 1 (S c2)) (List.map (shift_lt_in_ty 1 c1) Ts))).
  - intros n c1 c2 Hle. reflexivity.
  - intros A l B HA HB c1 c2 Hle.
    simpl. rewrite HA by lia. rewrite HB by lia. rewrite shift_lt_swap by lia. reflexivity.
  - intros K l Ts HTs c1 c2 Hle.
    rewrite !shift_lt_in_ty_ctor_eq. rewrite shift_lt_swap by lia. f_equal. apply HTs. lia.
  - intros A HA c1 c2 Hle.
    simpl. rewrite HA by lia. reflexivity.
  - intros B A HB HA c1 c2 Hle.
    simpl. rewrite HB by lia. rewrite HA by lia. reflexivity.
  - intros c1 c2 Hle. reflexivity.
  - intros A Ts HA HTs c1 c2 Hle.
    simpl. rewrite HA by lia. f_equal. apply HTs. lia.
Qed.

Lemma shift_lt_in_ty_swap_0 : forall T c,
  shift_lt_in_ty 1 0 (shift_lt_in_ty 1 c T)
  = shift_lt_in_ty 1 (S c) (shift_lt_in_ty 1 0 T).
Proof. intros T c. apply shift_lt_in_ty_swap. lia. Qed.

Lemma shift_lt_ctor_sig_swap_0 : forall sig c,
  shift_lt_ctor_sig 1 0 (shift_lt_ctor_sig 1 c sig) =
  shift_lt_ctor_sig 1 (S c) (shift_lt_ctor_sig 1 0 sig).
Proof.
  intros [[[n_lt n_ty] fields] result] c. unfold shift_lt_ctor_sig. simpl.
  f_equal.
  - f_equal. rewrite !List.map_map. apply List.map_ext. intro T.
    replace (n_lt + 0) with n_lt by lia.
    replace (n_lt + S c) with (S (n_lt + c)) by lia.
    apply shift_lt_in_ty_swap. lia.
  - replace (n_lt + 0) with n_lt by lia.
    replace (n_lt + S c) with (S (n_lt + c)) by lia.
    apply shift_lt_in_ty_swap. lia.
Qed.

Lemma shift_lt_eff_sig_swap_0 : forall sig c,
  shift_lt_eff_sig 1 0 (shift_lt_eff_sig 1 c sig) =
  shift_lt_eff_sig 1 (S c) (shift_lt_eff_sig 1 0 sig).
Proof.
  intros [[[n_α n_β] sig_ty] ret_ty] c. unfold shift_lt_eff_sig. simpl.
  f_equal; [f_equal|]; apply shift_lt_in_ty_swap_0.
Qed.

Lemma shift_lt_ctor_sig_shift_ty_comm : forall sig c,
  shift_ty_ctor_sig 1 0 (shift_lt_ctor_sig 1 c sig) =
  shift_lt_ctor_sig 1 c (shift_ty_ctor_sig 1 0 sig).
Proof.
  intros [[[n_lt n_ty] fields] result] c. unfold shift_lt_ctor_sig, shift_ty_ctor_sig. simpl.
  f_equal.
  - f_equal. rewrite !List.map_map. apply List.map_ext. intro T.
    apply shift_ty_shift_lt_in_ty_commute.
  - apply shift_ty_shift_lt_in_ty_commute.
Qed.

Lemma shift_lt_eff_sig_shift_ty_comm : forall sig c,
  shift_ty_eff_sig 1 0 (shift_lt_eff_sig 1 c sig) =
  shift_lt_eff_sig 1 c (shift_ty_eff_sig 1 0 sig).
Proof.
  intros [[[n_α n_β] sig_ty] ret_ty] c. unfold shift_lt_eff_sig, shift_ty_eff_sig. simpl.
  f_equal; [f_equal|]; apply shift_ty_shift_lt_in_ty_commute.
Qed.

Inductive InsLt : nat -> ctx -> ctx -> Prop :=
  | InsLt_here : forall D G, InsLt 0 G (bind_lt D :: G)
  | InsLt_lt : forall c G G' D,
      InsLt c G G' -> InsLt (S c) (bind_lt D :: G) (bind_lt (shift_lt 1 c D) :: G')
  | InsLt_ty : forall c G G' A,
      InsLt c G G' -> InsLt c (bind_ty A :: G) (bind_ty (shift_lt_in_ty 1 c A) :: G')
  | InsLt_tm : forall c G G' T,
      InsLt c G G' -> InsLt c (bind_tm T :: G) (bind_tm (shift_lt_in_ty 1 c T) :: G')
  | InsLt_ctor : forall c G G' tg n1 n2 Ts Tr,
      InsLt c G G' ->
      InsLt c (bind_ctor tg n1 n2 Ts Tr :: G)
        (bind_ctor tg n1 n2 (List.map (shift_lt_in_ty 1 (n1 + c)) Ts)
                  (shift_lt_in_ty 1 (n1 + c) Tr) :: G')
  | InsLt_eff : forall c G G' eg m1 m2 Ts Tr,
      InsLt c G G' ->
      InsLt c (bind_eff eg m1 m2 Ts Tr :: G)
              (bind_eff eg m1 m2 (shift_lt_in_ty 1 c Ts) (shift_lt_in_ty 1 c Tr) :: G').

Lemma InsLt_length : forall c G G', InsLt c G G' -> length G' = S (length G).
Proof. intros c G G' H. induction H; simpl; lia. Qed.

(* lt-lookups shift by shift_lt 1 c at the renamed index shv c x *)
Lemma InsLt_lookup_lt : forall c G G', InsLt c G G' ->
  forall x, ctx_lookup_lt G' (shv c x)
            = option_map (shift_lt 1 c) (ctx_lookup_lt G x).
Proof.
  intros c G G' H. induction H; intro x.
  - unfold shv; simpl Nat.leb. destruct x as [|x']; reflexivity.
  - destruct x as [|x'].
    + unfold shv; simpl Nat.leb. simpl ctx_lookup_lt.
      rewrite shift_lt_swap_0. reflexivity.
    + specialize (IHInsLt x').
      destruct (Nat.leb c x') eqn:E.
      * assert (E2 : shv (S c) (S x') = S (S x')).
        { unfold shv. apply Nat.leb_le in E. rewrite (proj2 (Nat.leb_le (S c)(S x'))) by lia. reflexivity. }
        rewrite E2. unfold shv in IHInsLt. rewrite E in IHInsLt.
        simpl ctx_lookup_lt. rewrite IHInsLt.
        destruct (ctx_lookup_lt G x') as [X|]; simpl; [rewrite shift_lt_swap_0; reflexivity | reflexivity].
      * apply Nat.leb_gt in E.
        assert (E2 : shv (S c) (S x') = S x').
        { unfold shv. rewrite (proj2 (Nat.leb_gt (S c)(S x'))) by lia. reflexivity. }
        rewrite E2. unfold shv in IHInsLt. rewrite (proj2 (Nat.leb_gt c x')) in IHInsLt by lia.
        simpl ctx_lookup_lt. rewrite IHInsLt.
        destruct (ctx_lookup_lt G x') as [X|]; simpl; [rewrite shift_lt_swap_0; reflexivity | reflexivity].
  - specialize (IHInsLt x). simpl ctx_lookup_lt. apply IHInsLt.
  - specialize (IHInsLt x). simpl ctx_lookup_lt. apply IHInsLt.
  - specialize (IHInsLt x). simpl ctx_lookup_lt. apply IHInsLt.
  - specialize (IHInsLt x). simpl ctx_lookup_lt. apply IHInsLt.
Qed.

(* ty-lookups shift by shift_lt_in_ty 1 c (index unchanged) *)
Lemma InsLt_lookup_ty : forall c G G', InsLt c G G' ->
  forall a, ctx_lookup_ty G' a
            = option_map (shift_lt_in_ty 1 c) (ctx_lookup_ty G a).
Proof.
  intros c G G' H. induction H; intro a.
  - (* InsLt_here *) simpl ctx_lookup_ty.
    destruct (ctx_lookup_ty G a) as [X|]; simpl; reflexivity.
  - (* InsLt_lt *) specialize (IHInsLt a). simpl ctx_lookup_ty. rewrite IHInsLt.
    destruct (ctx_lookup_ty G a) as [X|]; simpl;
      [rewrite shift_lt_in_ty_swap_0; reflexivity | reflexivity].
  - (* InsLt_ty *) destruct a as [|a'].
    + simpl ctx_lookup_ty. rewrite shift_ty_shift_lt_in_ty_commute. reflexivity.
    + specialize (IHInsLt a'). simpl ctx_lookup_ty. rewrite IHInsLt.
      destruct (ctx_lookup_ty G a') as [X|]; simpl;
        [rewrite shift_ty_shift_lt_in_ty_commute; reflexivity | reflexivity].
  - specialize (IHInsLt a). simpl ctx_lookup_ty. apply IHInsLt.
  - specialize (IHInsLt a). simpl ctx_lookup_ty. apply IHInsLt.
  - specialize (IHInsLt a). simpl ctx_lookup_ty. apply IHInsLt.
Qed.

Lemma InsLt_lookup_tm : forall c G G', InsLt c G G' ->
  forall x, ctx_lookup_tm G' x = option_map (shift_lt_in_ty 1 c) (ctx_lookup_tm G x).
Proof.
  intros c G G' H. induction H; intro x.
  - simpl ctx_lookup_tm. reflexivity.
  - simpl ctx_lookup_tm. rewrite IHInsLt.
    destruct (ctx_lookup_tm G x) as [T|]; simpl;
      [rewrite shift_lt_in_ty_swap_0|]; reflexivity.
  - simpl ctx_lookup_tm. rewrite IHInsLt.
    destruct (ctx_lookup_tm G x) as [T|]; simpl;
      [rewrite shift_ty_shift_lt_in_ty_commute|]; reflexivity.
  - destruct x as [|x']; simpl ctx_lookup_tm.
    + reflexivity.
    + apply IHInsLt.
  - simpl ctx_lookup_tm. apply IHInsLt.
  - simpl ctx_lookup_tm. apply IHInsLt.
Qed.

Lemma InsLt_lookup_ctor : forall c G G', InsLt c G G' ->
  forall K, ctx_lookup_ctor G' K = option_map (shift_lt_ctor_sig 1 c) (ctx_lookup_ctor G K).
Proof.
  intros c G G' H. induction H; intro K.
  - simpl. reflexivity.
  - simpl. rewrite IHInsLt. destruct (ctx_lookup_ctor G K) as [sig|] eqn:E; cbn [option_map].
    + rewrite shift_lt_ctor_sig_swap_0. reflexivity.
    + reflexivity.
  - simpl. rewrite IHInsLt. destruct (ctx_lookup_ctor G K) as [sig|] eqn:E; cbn [option_map].
    + rewrite shift_lt_ctor_sig_shift_ty_comm. reflexivity.
    + reflexivity.
  - simpl. apply IHInsLt.
  - simpl. destruct (Nat.eqb K tg); [reflexivity|apply IHInsLt].
  - simpl. apply IHInsLt.
Qed.

Lemma InsLt_lookup_eff : forall c G G', InsLt c G G' ->
  forall E, ctx_lookup_eff G' E = option_map (shift_lt_eff_sig 1 c) (ctx_lookup_eff G E).
Proof.
  intros c G G' H. induction H; intro E.
  - simpl. reflexivity.
  - simpl. rewrite IHInsLt. destruct (ctx_lookup_eff G E) as [sig|] eqn:Ef; cbn [option_map].
    + rewrite shift_lt_eff_sig_swap_0. reflexivity.
    + reflexivity.
  - simpl. rewrite IHInsLt. destruct (ctx_lookup_eff G E) as [sig|] eqn:Ef; cbn [option_map].
    + rewrite shift_lt_eff_sig_shift_ty_comm. reflexivity.
    + reflexivity.
  - simpl. apply IHInsLt.
  - simpl. apply IHInsLt.
  - simpl. destruct (Nat.eqb E eg); [reflexivity|apply IHInsLt].
Qed.

Lemma shv_shift_lt : forall c n, shift_lt 1 c (lt_var n) = lt_var (shv c n).
Proof.
  intros c n. simpl. unfold shv.
  destruct (Nat.leb c n); [rewrite Nat.add_1_r|]; reflexivity.
Qed.

(* lt_of_ty_ctx commutes with shift_lt_in_ty under InsLt *)
Lemma lt_of_ty_ctx_InsLt : forall c G G', InsLt c G G' ->
  forall f T, lt_of_ty_ctx f G' (shift_lt_in_ty 1 c T) = shift_lt 1 c (lt_of_ty_ctx f G T).
Proof.
  intros c G G' HIns f. induction f as [|f' IHf]; intro T.
  - induction T using type_list_ind with
      (Q := fun Ts => lt_of_ty_ctx_list 0 G' (List.map (shift_lt_in_ty 1 c) Ts)
                      = shift_lt 1 c (lt_of_ty_ctx_list 0 G Ts)).
    + rewrite shift_lt_in_ty_var_eq. rewrite !(lt_of_ty_ctx_var 0). reflexivity.
    + rewrite shift_lt_in_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. reflexivity.
    + rewrite shift_lt_in_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor. rewrite shift_lt_min_eq.
      f_equal. exact IHT.
    + rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite shift_lt_min_eq. rewrite IHT, IHT0. reflexivity.
  - induction T using type_list_ind with
      (Q := fun Ts => lt_of_ty_ctx_list (S f') G' (List.map (shift_lt_in_ty 1 c) Ts)
                      = shift_lt 1 c (lt_of_ty_ctx_list (S f') G Ts)).
    + rewrite shift_lt_in_ty_var_eq.
      rewrite (lt_of_ty_ctx_var (S f') G' n), (lt_of_ty_ctx_var (S f') G n).
      rewrite (InsLt_lookup_ty c G G' HIns n).
      destruct (ctx_lookup_ty G n) as [B|] eqn:E; simpl.
      * apply IHf.
      * reflexivity.
    + rewrite shift_lt_in_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. reflexivity.
    + rewrite shift_lt_in_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor. rewrite shift_lt_min_eq.
      f_equal. exact IHT.
    + rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite shift_lt_min_eq. rewrite IHT, IHT0. reflexivity.
Qed.

Lemma lt_of_ty_G_InsLt : forall c G G', InsLt c G G' ->
  forall T, lt_of_ty_G G' (shift_lt_in_ty 1 c T) = shift_lt 1 c (lt_of_ty_G G T).
Proof.
  intros c G G' HIns T. unfold lt_of_ty_G.
  rewrite (InsLt_length c G G' HIns).
  rewrite (lt_of_ty_ctx_InsLt c G G' HIns (S (length G)) T).
  f_equal.
  apply (lt_of_ty_ctx_fuel_irrel (S (length G)) (length G) T G 0).
  - apply VB_0.
  - simpl; lia.
  - simpl; lia.
Qed.

Lemma shift_lt_in_ty_ltall_eq : forall a c A,
  shift_lt_in_ty a c (type_lt_all A) = type_lt_all (shift_lt_in_ty a (S c) A).
Proof. reflexivity. Qed.
Lemma shift_lt_in_ty_tyall_eq : forall a c B A,
  shift_lt_in_ty a c (type_ty_all B A)
  = type_ty_all (shift_lt_in_ty a c B) (shift_lt_in_ty a c A).
Proof. reflexivity. Qed.

Lemma lt_wf_InsLt : forall G l,
  lt_wf G l -> forall c G', InsLt c G G' -> lt_wf G' (shift_lt 1 c l).
Proof.
  intros G l Hwf. induction Hwf; intros c G' HIns; simpl.
  - replace (if Nat.leb c x then x + 1 else x) with (shv c x)
      by (unfold shv; destruct (Nat.leb c x); [rewrite Nat.add_1_r|]; reflexivity).
    econstructor. rewrite (InsLt_lookup_lt c Γ G' HIns x). rewrite H. reflexivity.
  - constructor.
  - constructor.
  - constructor.
    + apply (IHHwf1 c G' HIns).
    + apply (IHHwf2 c G' HIns).
Qed.

Lemma lifetimes_wf_InsLt : forall G lts,
  lifetimes_wf G lts -> forall c G', InsLt c G G' ->
    lifetimes_wf G' (List.map (shift_lt 1 c) lts).
Proof.
  intros G lts Hwf. induction Hwf; intros c G' HIns; cbn [List.map].
  - constructor.
  - constructor.
    + eapply lt_wf_InsLt; eauto.
    + apply (IHHwf c G' HIns).
Qed.

Lemma ty_wf_InsLt : forall G T,
  ty_wf G T -> forall c G', InsLt c G G' -> ty_wf G' (shift_lt_in_ty 1 c T)
with types_wf_InsLt : forall G Ts,
  types_wf G Ts -> forall c G', InsLt c G G' -> types_wf G' (List.map (shift_lt_in_ty 1 c) Ts).
Proof.
  - intros G T Hwf. induction Hwf; intros c G' HIns.
    + simpl. econstructor.
      * rewrite (InsLt_lookup_ty c Γ G' HIns α). rewrite H. reflexivity.
      * apply IHHwf. exact HIns.
    + rewrite shift_lt_in_ty_fun_eq. constructor.
      * apply IHHwf1. exact HIns.
      * eapply lt_wf_InsLt; eauto.
      * apply IHHwf2. exact HIns.
    + rewrite shift_lt_in_ty_ctor_eq. constructor.
      * eapply lt_wf_InsLt; eauto.
      * eapply types_wf_InsLt; eauto.
    + rewrite shift_lt_in_ty_ltall_eq. constructor.
      apply IHHwf. apply InsLt_lt. exact HIns.
    + rewrite shift_lt_in_ty_tyall_eq. constructor.
      * apply IHHwf1. exact HIns.
      * apply IHHwf2. apply InsLt_ty. exact HIns.
  - intros G Ts Hwf. induction Hwf; intros c G' HIns; cbn [List.map].
    + constructor.
    + constructor.
      * eapply ty_wf_InsLt; eauto.
      * apply (IHHwf c G' HIns).
Qed.

Lemma lt_sub_InsLt : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall c G', InsLt c G G' -> G' ⊢ₗ shift_lt 1 c l1 <: shift_lt 1 c l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l Hwf|Γ l Hwf|Γ x Δ Hlk Hwf|Γ l Hwf
                 |Γ l1 l2 l3 H1 IH1 H2 IH2|Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H1 IH1 Hwf2|Γ l l1 l2 H1 IH1 Hwf1];
    intros c G' HIns; simpl.
  - apply LS_Free. eapply lt_wf_InsLt; eauto.
  - apply LS_Local. eapply lt_wf_InsLt; eauto.
  - replace (if Nat.leb c x then x + 1 else x) with (shv c x)
      by (unfold shv; destruct (Nat.leb c x); [rewrite Nat.add_1_r|]; reflexivity).
    apply LS_Var.
    + rewrite (InsLt_lookup_lt c Γ G' HIns x). rewrite Hlk. reflexivity.
    + eapply lt_wf_InsLt; eauto.
  - apply LS_Refl. eapply lt_wf_InsLt; eauto.
  - eapply LS_Trans; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - apply LS_MinL; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - apply LS_MinR1.
    + apply (IH1 c G' HIns).
    + eapply lt_wf_InsLt; eauto.
  - apply LS_MinR2.
    + apply (IH1 c G' HIns).
    + eapply lt_wf_InsLt; eauto.
Qed.

Lemma sub_InsLt : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall c G', InsLt c G G' -> G' ⊢ shift_lt_in_ty 1 c T1 <:: shift_lt_in_ty 1 c T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T Hwf|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                 |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                 |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H1 IH1|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2];
    intros c G' HIns.
  - apply SA_Refl. eapply ty_wf_InsLt; eauto.
  - eapply SA_Trans; [apply (IH1 c G' HIns) | apply (IH2 c G' HIns)].
  - simpl. apply SA_VarCtx.
    + rewrite (InsLt_lookup_ty c Γ G' HIns α). rewrite Hlk. reflexivity.
    + eapply ty_wf_InsLt; eauto.
  - rewrite !shift_lt_in_ty_ctor_eq. apply SA_Data.
    + apply (lt_sub_InsLt Γ l l' Hls c G' HIns).
    + eapply types_wf_InsLt; eauto.
  - rewrite shift_lt_in_ty_ctor_eq. cbn [List.map]. apply SA_Any.
    + eapply ty_wf_InsLt; eauto.
    + eapply lt_wf_InsLt; eauto.
    + rewrite (lt_of_ty_G_InsLt c Γ G' HIns T).
      apply (lt_sub_InsLt Γ (lt_of_ty_G Γ T) Δ Hls c G' HIns).
  - rewrite !shift_lt_in_ty_fun_eq. apply SA_Fun.
    + apply (IH1 c G' HIns).
    + apply (lt_sub_InsLt Γ l l' Hl c G' HIns).
    + apply (IH2 c G' HIns).
  - rewrite !shift_lt_in_ty_ltall_eq. apply SA_LtAll.
    apply (IH1 (S c) (bind_lt (shift_lt 1 c lt_local) :: G') (InsLt_lt c Γ G' lt_local HIns)).
  - rewrite !shift_lt_in_ty_tyall_eq. eapply SA_TyAll.
    + eapply ty_wf_InsLt; [exact HwfA|]. apply InsLt_ty. exact HIns.
    + eapply ty_wf_InsLt; [exact HwfA'|]. apply InsLt_ty. exact HIns.
    + apply (IH1 c G' HIns).
    + apply (IH2 c (bind_ty (shift_lt_in_ty 1 c B') :: G') (InsLt_ty c Γ G' B' HIns)).
Qed.

Lemma lt_wf_InsLt_closed : forall G l,
  lt_wf G l -> forall c G', InsLt c G G' -> lt_lt_closed c l -> lt_wf G' l.
Proof.
  intros G l Hwf c G' HIns Hclosed.
  pose proof (lt_wf_InsLt G l Hwf c G' HIns) as Hwf'.
  rewrite shift_lt_closed_lifetime in Hwf' by exact Hclosed. exact Hwf'.
Qed.

Lemma lifetimes_wf_InsLt_closed : forall G lts,
  lifetimes_wf G lts -> forall c G', InsLt c G G' -> lts_lt_closed c lts -> lifetimes_wf G' lts.
Proof.
  intros G lts Hwf. induction Hwf; intros c G' HIns Hclosed; simpl in *.
  - constructor.
  - destruct Hclosed as [Hl Hlts]. constructor.
    + eapply lt_wf_InsLt_closed; eauto.
    + apply (IHHwf c G' HIns Hlts).
Qed.

Lemma ty_wf_InsLt_closed : forall G T,
  ty_wf G T -> forall c G', InsLt c G G' -> ty_lt_closed c T -> ty_wf G' T.
Proof.
  intros G T Hwf c G' HIns Hclosed.
  pose proof (ty_wf_InsLt G T Hwf c G' HIns) as Hwf'.
  rewrite shift_lt_in_type_closed in Hwf' by exact Hclosed. exact Hwf'.
Qed.

Lemma types_wf_InsLt_closed : forall G Ts,
  types_wf G Ts -> forall c G', InsLt c G G' -> tys_lt_closed c Ts -> types_wf G' Ts.
Proof.
  intros G Ts Hwf. induction Hwf; intros c G' HIns Hclosed; simpl in *.
  - constructor.
  - destruct Hclosed as [HT HTs]. constructor.
    + eapply ty_wf_InsLt_closed; eauto.
    + apply (IHHwf c G' HIns HTs).
Qed.

Lemma lt_sub_InsLt_closed : forall G l1 l2,
  G ⊢ₗ l1 <: l2 -> forall c G', InsLt c G G' ->
  lt_lt_closed c l1 -> lt_lt_closed c l2 -> G' ⊢ₗ l1 <: l2.
Proof.
  intros G l1 l2 Hsub c G' HIns Hc1 Hc2.
  pose proof (lt_sub_InsLt G l1 l2 Hsub c G' HIns) as Hsub'.
  rewrite shift_lt_closed_lifetime in Hsub' by exact Hc1.
  rewrite shift_lt_closed_lifetime in Hsub' by exact Hc2.
  exact Hsub'.
Qed.

Lemma sub_InsLt_closed : forall G T1 T2,
  G ⊢ T1 <:: T2 -> forall c G', InsLt c G G' ->
  ty_lt_closed c T1 -> ty_lt_closed c T2 -> G' ⊢ T1 <:: T2.
Proof.
  intros G T1 T2 Hsub c G' HIns Hc1 Hc2.
  pose proof (sub_InsLt G T1 T2 Hsub c G' HIns) as Hsub'.
  rewrite shift_lt_in_type_closed in Hsub' by exact Hc1.
  rewrite shift_lt_in_type_closed in Hsub' by exact Hc2.
  exact Hsub'.
Qed.

Lemma sub_weaken_lt_shift : forall Γ D T1 T2,
  Γ ⊢ T1 <:: T2 ->
  (bind_lt D :: Γ) ⊢ shift_lt_in_ty 1 0 T1 <:: shift_lt_in_ty 1 0 T2.
Proof.
  intros Γ D T1 T2 H. apply (sub_InsLt Γ T1 T2 H 0 (bind_lt D :: Γ)). apply InsLt_here.
Qed.

(* ===== InsTm: depth-general bind_tm weakening =================== *)

Inductive InsTm : ctx -> ctx -> Prop :=
| InsTm_here : forall A G, InsTm G (bind_tm A :: G)
| InsTm_tm : forall A G G',
    InsTm G G' -> InsTm (bind_tm A :: G) (bind_tm A :: G')
| InsTm_ty : forall B G G',
    InsTm G G' -> InsTm (bind_ty B :: G) (bind_ty B :: G')
| InsTm_lt : forall D G G',
    InsTm G G' -> InsTm (bind_lt D :: G) (bind_lt D :: G')
| InsTm_ctor : forall K n_lt n_ty f r G G',
    InsTm G G' -> InsTm (bind_ctor K n_lt n_ty f r :: G) (bind_ctor K n_lt n_ty f r :: G')
| InsTm_eff : forall E n_a n_b sig ret G G',
    InsTm G G' -> InsTm (bind_eff E n_a n_b sig ret :: G) (bind_eff E n_a n_b sig ret :: G').

Lemma InsTm_length : forall G G', InsTm G G' -> List.length G' = S (List.length G).
Proof. induction 1; simpl; lia. Qed.

Lemma InsTm_lookup_ty : forall G G', InsTm G G' ->
  forall a, ctx_lookup_ty G' a = ctx_lookup_ty G a.
Proof.
  intros G G' H. induction H; intro a; simpl; try apply IHInsTm.
  - reflexivity.
  - destruct a as [|a']; simpl.
    + reflexivity.
    + rewrite IHInsTm. reflexivity.
  - rewrite IHInsTm. reflexivity.
Qed.

Lemma InsTm_lookup_lt : forall G G', InsTm G G' ->
  forall x, ctx_lookup_lt G' x = ctx_lookup_lt G x.
Proof.
  intros G G' H. induction H; intro x; simpl; try apply IHInsTm.
  - reflexivity.
  - destruct x as [|x']; simpl.
    + reflexivity.
    + rewrite IHInsTm. reflexivity.
Qed.

Lemma InsTm_lookup_ctor : forall G G', InsTm G G' ->
  forall K, ctx_lookup_ctor G' K = ctx_lookup_ctor G K.
Proof.
  intros G G' H.
  induction H as [A G|A G G' H IH|B G G' H IH|D G G' H IH
                 |K0 n_lt n_ty f r G G' H IH|E n_a n_b sig ret G G' H IH];
    intro K; simpl.
  - reflexivity.
  - apply IH.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - destruct (Nat.eqb K K0); [reflexivity|apply IH].
  - apply IH.
Qed.

Lemma InsTm_lookup_eff : forall G G', InsTm G G' ->
  forall E, ctx_lookup_eff G' E = ctx_lookup_eff G E.
Proof.
  intros G G' H.
  induction H as [A G|A G G' H IH|B G G' H IH|D G G' H IH
                 |K n_lt n_ty f r G G' H IH|E0 n_a n_b sig ret G G' H IH];
    intro E; simpl.
  - reflexivity.
  - apply IH.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - apply IH.
  - destruct (Nat.eqb E E0); [reflexivity|apply IH].
Qed.

Lemma lt_of_ty_ctx_InsTm : forall G G', InsTm G G' ->
  forall f T, lt_of_ty_ctx f G' T = lt_of_ty_ctx f G T.
Proof.
  intros G G' HIns f. revert G G' HIns.
  induction f as [|f IH]; intros G G' HIns T.
  - destruct T; reflexivity.
  - revert G G' HIns. induction T using type_list_ind with
      (Q := fun Ts => forall G G', InsTm G G' ->
        lt_of_ty_ctx_list (S f) G' Ts = lt_of_ty_ctx_list (S f) G Ts);
      intros G G' HIns.
    + simpl. rewrite (InsTm_lookup_ty G G' HIns n).
      destruct (ctx_lookup_ty G n) as [B|] eqn:HB; [apply (IH G G' HIns B)|reflexivity].
    + reflexivity.
    + rewrite !lt_of_ty_ctx_ctor. f_equal. apply IHT. exact HIns.
    + reflexivity.
    + reflexivity.
    + rewrite !lt_of_ty_ctx_list_nil. reflexivity.
    + rewrite !lt_of_ty_ctx_list_cons.
      rewrite (IHT G G' HIns), (IHT0 G G' HIns). reflexivity.
Qed.

Lemma lt_of_ty_G_InsTm : forall G G', InsTm G G' ->
  forall T, lt_of_ty_G G' T = lt_of_ty_G G T.
Proof.
  intros G G' HIns T. unfold lt_of_ty_G.
  rewrite (lt_of_ty_ctx_InsTm G G' HIns (List.length G') T).
  rewrite (lt_of_ty_ctx_fuel_irrel (List.length G') (List.length G) T G 0 (VB_0 T));
    [reflexivity| |].
  - pose proof (InsTm_length G G' HIns). lia.
  - lia.
Qed.

Lemma lt_wf_InsTm : forall G l,
  lt_wf G l -> forall G', InsTm G G' -> lt_wf G' l.
Proof.
  intros G l Hwf. induction Hwf; intros G' HIns.
  - econstructor. rewrite (InsTm_lookup_lt Γ G' HIns x). exact H.
  - constructor.
  - constructor.
  - constructor.
    + apply (IHHwf1 G' HIns).
    + apply (IHHwf2 G' HIns).
Qed.

Lemma lifetimes_wf_InsTm : forall G lts,
  lifetimes_wf G lts -> forall G', InsTm G G' -> lifetimes_wf G' lts.
Proof.
  intros G lts Hwf. induction Hwf; intros G' HIns.
  - constructor.
  - constructor.
    + eapply lt_wf_InsTm; eauto.
    + apply (IHHwf G' HIns).
Qed.

Lemma ty_wf_InsTm : forall G T,
  ty_wf G T -> forall G', InsTm G G' -> ty_wf G' T
with types_wf_InsTm : forall G Ts,
  types_wf G Ts -> forall G', InsTm G G' -> types_wf G' Ts.
Proof.
  - intros G T Hwf. induction Hwf; intros G' HIns.
    + econstructor.
      * rewrite (InsTm_lookup_ty Γ G' HIns α). exact H.
      * apply IHHwf. exact HIns.
    + constructor.
      * apply IHHwf1. exact HIns.
      * eapply lt_wf_InsTm; eauto.
      * apply IHHwf2. exact HIns.
    + constructor.
      * eapply lt_wf_InsTm; eauto.
      * eapply types_wf_InsTm; eauto.
    + constructor. apply IHHwf. apply InsTm_lt. exact HIns.
    + constructor.
      * apply IHHwf1. exact HIns.
      * apply IHHwf2. apply InsTm_ty. exact HIns.
  - intros G Ts Hwf. induction Hwf; intros G' HIns.
    + constructor.
    + constructor.
      * eapply ty_wf_InsTm; eauto.
      * apply (IHHwf G' HIns).
Qed.

Lemma lt_sub_InsTm : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall G', InsTm G G' -> G' ⊢ₗ l1 <: l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l Hwf|Γ l Hwf|Γ x Δ Hlk Hwf|Γ l Hwf
                 |Γ l1 l2 l3 H12 IH12 H23 IH23
                 |Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H IH Hwf2|Γ l l1 l2 H IH Hwf1]; intros G' HIns.
  - apply LS_Free. eapply lt_wf_InsTm; eauto.
  - apply LS_Local. eapply lt_wf_InsTm; eauto.
  - apply LS_Var.
    + rewrite (InsTm_lookup_lt Γ G' HIns x). exact Hlk.
    + eapply lt_wf_InsTm; eauto.
  - apply LS_Refl. eapply lt_wf_InsTm; eauto.
  - eapply LS_Trans; [apply IH12 | apply IH23]; exact HIns.
  - apply LS_MinL; [apply IH1|apply IH2]; exact HIns.
  - apply LS_MinR1.
    + apply IH. exact HIns.
    + eapply lt_wf_InsTm; eauto.
  - apply LS_MinR2.
    + apply IH. exact HIns.
    + eapply lt_wf_InsTm; eauto.
Qed.

Lemma sub_InsTm : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall G', InsTm G G' -> G' ⊢ T1 <:: T2.
Proof.
  intros G T1 T2 H.
  induction H as [Γ T Hwf|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                 |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                 |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                 |Γ A A' H IH|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2]; intros G' HIns.
  - apply SA_Refl. eapply ty_wf_InsTm; eauto.
  - eapply SA_Trans; [apply IH1|apply IH2]; exact HIns.
  - apply SA_VarCtx.
    + rewrite (InsTm_lookup_ty Γ G' HIns α). exact Hlk.
    + eapply ty_wf_InsTm; eauto.
  - apply SA_Data.
    + eapply lt_sub_InsTm; eauto.
    + eapply types_wf_InsTm; eauto.
  - apply SA_Any.
    + eapply ty_wf_InsTm; eauto.
    + eapply lt_wf_InsTm; eauto.
    + rewrite lt_of_ty_G_InsTm with (G := Γ) (G' := G') by exact HIns.
      eapply lt_sub_InsTm; eauto.
  - apply SA_Fun; [apply IH1|eapply lt_sub_InsTm|apply IH2]; eauto.
  - apply SA_LtAll. apply IH. apply InsTm_lt. exact HIns.
  - eapply SA_TyAll.
    + eapply ty_wf_InsTm; [exact HwfA|]. apply InsTm_ty. exact HIns.
    + eapply ty_wf_InsTm; [exact HwfA'|]. apply InsTm_ty. exact HIns.
    + apply IH1. exact HIns.
    + apply IH2. apply InsTm_ty. exact HIns.
Qed.

Lemma lt_sub_wf : forall Γ l1 l2,
  Γ ⊢ₗ l1 <: l2 -> lt_wf Γ l1 /\ lt_wf Γ l2.
Proof.
  intros Γ l1 l2 H. induction H.
  - split; [constructor|exact H].
  - split; [exact H|constructor].
  - split; [econstructor; exact H|exact H0].
  - split; exact H.
  - destruct IHlt_sub1 as [Hwf1 _]. destruct IHlt_sub2 as [_ Hwf3].
    split; assumption.
  - destruct IHlt_sub1 as [Hwf1 Hwfl]. destruct IHlt_sub2 as [Hwf2 _].
    split; [constructor; assumption|exact Hwfl].
  - destruct IHlt_sub as [Hwfl Hwfl1]. split.
    + exact Hwfl.
    + constructor; assumption.
  - destruct IHlt_sub as [Hwfl Hwfl2]. split.
    + exact Hwfl.
    + constructor; assumption.
Qed.

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

Inductive InsTmAt : nat -> ctx -> ctx -> Prop :=
| InsTmAt_here : forall A G, InsTmAt 0 G (bind_tm A :: G)
| InsTmAt_tm : forall c A G G',
    InsTmAt c G G' -> InsTmAt (S c) (bind_tm A :: G) (bind_tm A :: G')
| InsTmAt_ty : forall c B G G',
    InsTmAt c G G' -> InsTmAt c (bind_ty B :: G) (bind_ty B :: G')
| InsTmAt_lt : forall c D G G',
    InsTmAt c G G' -> InsTmAt c (bind_lt D :: G) (bind_lt D :: G')
| InsTmAt_ctor : forall c K n_lt n_ty f r G G',
    InsTmAt c G G' -> InsTmAt c (bind_ctor K n_lt n_ty f r :: G)
                              (bind_ctor K n_lt n_ty f r :: G')
| InsTmAt_eff : forall c E n_a n_b sig ret G G',
    InsTmAt c G G' -> InsTmAt c (bind_eff E n_a n_b sig ret :: G)
                              (bind_eff E n_a n_b sig ret :: G').

Lemma InsTmAt_to_InsTm : forall c G G', InsTmAt c G G' -> InsTm G G'.
Proof.
  intros c G G' H. induction H; constructor; exact IHInsTmAt.
Qed.

Lemma InsTmAt_lookup_tm : forall c G G', InsTmAt c G G' ->
  forall x, ctx_lookup_tm G' (shv c x) = ctx_lookup_tm G x.
Proof.
  intros c G G' H. induction H; intro x.
  - unfold shv. simpl Nat.leb. destruct x; reflexivity.
  - destruct x as [|x'].
    + unfold shv. simpl Nat.leb. reflexivity.
    + simpl ctx_lookup_tm. rewrite <- (IHInsTmAt x').
      unfold shv.
      destruct (Nat.leb c x') eqn:E.
      * apply Nat.leb_le in E.
        rewrite (proj2 (Nat.leb_le (S c) (S x'))) by lia. reflexivity.
      * apply Nat.leb_gt in E.
        rewrite (proj2 (Nat.leb_gt (S c) (S x'))) by lia. reflexivity.
  - simpl ctx_lookup_tm. rewrite IHInsTmAt. reflexivity.
  - simpl ctx_lookup_tm. rewrite IHInsTmAt. reflexivity.
  - simpl ctx_lookup_tm. apply IHInsTmAt.
  - simpl ctx_lookup_tm. apply IHInsTmAt.
Qed.

Lemma shift_tm_var_eq : forall a c n,
  shift_tm a c (term_var n) = term_var (if Nat.leb c n then n + a else n).
Proof. reflexivity. Qed.

Lemma typing_var_InsTmAt : forall c G G' x T,
  InsTmAt c G G' ->
  ctx_lookup_tm G x = Some T ->
  ty_wf G T ->
  G' ⊢ₜ shift_tm 1 c (term_var x) : T.
Proof.
  intros c G G' x T HIns Hlk Hwf.
  rewrite shift_tm_var_eq. rewrite Nat.add_1_r.
  apply T_Var.
  - change (ctx_lookup_tm G' (shv c x) = Some T).
    rewrite (InsTmAt_lookup_tm c G G' HIns x). exact Hlk.
  - eapply ty_wf_InsTm; [exact Hwf|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
Qed.

Lemma free_tm_vars_go_eq_concat : forall cutoff ts,
  (fix go ts := match ts with [] => [] | u :: rest => free_tm_vars cutoff u ++ go rest end) ts =
  List.concat (List.map (free_tm_vars cutoff) ts).
Proof.
  intros cutoff ts. induction ts as [|t ts IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma free_tm_vars_shift_ty_in_tm : forall t cutoff c,
  free_tm_vars cutoff (shift_ty_in_tm 1 c t) = free_tm_vars cutoff t.
Proof.
  apply (term_list_ind
    (fun t => forall cutoff c, free_tm_vars cutoff (shift_ty_in_tm 1 c t) = free_tm_vars cutoff t)
    (fun ts => forall cutoff c,
      List.concat (List.map (free_tm_vars cutoff) (List.map (shift_ty_in_tm 1 c) ts)) =
      List.concat (List.map (free_tm_vars cutoff) ts))).
  - reflexivity.
  - intros t1 t2 IH1 IH2 cutoff c. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH cutoff c. simpl. apply IH.
  - intros t T IH cutoff c. simpl. apply IH.
  - intros bound body IH cutoff c. simpl. apply IH.
  - intros t l IH cutoff c. simpl. apply IH.
  - intros body IH cutoff c. simpl. apply IH.
  - intros K l lts Ts ts IH cutoff c. simpl. rewrite shift_ty_in_tm_go_eq_map.
    rewrite !free_tm_vars_go_eq_concat. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn cutoff c. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff c. simpl. rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa cutoff c. simpl. rewrite IHt, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff c. simpl. apply IHop.
  - intros m T_B T_R t IH cutoff c. simpl. apply IH.
  - intros m T_B T_R b IH cutoff c. simpl. apply IH.
  - reflexivity.
  - intros t ts IHt IHts cutoff c. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma free_tm_vars_shift_ty_in_tm_any : forall t cutoff amount c,
  free_tm_vars cutoff (shift_ty_in_tm amount c t) = free_tm_vars cutoff t.
Proof.
  intros t cutoff amount c. induction amount as [|amount IH].
  - rewrite shift_ty_in_tm_zero. reflexivity.
  - replace (S amount) with (1 + amount) by lia.
    rewrite <- shift_ty_in_tm_fuse.
    rewrite free_tm_vars_shift_ty_in_tm. exact IH.
Qed.

Lemma free_tm_vars_shift_lt_in_tm : forall t cutoff c,
  free_tm_vars cutoff (shift_lt_in_tm 1 c t) = free_tm_vars cutoff t.
Proof.
  apply (term_list_ind
    (fun t => forall cutoff c, free_tm_vars cutoff (shift_lt_in_tm 1 c t) = free_tm_vars cutoff t)
    (fun ts => forall cutoff c,
      List.concat (List.map (free_tm_vars cutoff) (List.map (shift_lt_in_tm 1 c) ts)) =
      List.concat (List.map (free_tm_vars cutoff) ts))).
  - reflexivity.
  - intros t1 t2 IH1 IH2 cutoff c. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH cutoff c. simpl. apply IH.
  - intros t T IH cutoff c. simpl. apply IH.
  - intros bound body IH cutoff c. simpl. apply IH.
  - intros t l IH cutoff c. simpl. apply IH.
  - intros body IH cutoff c. simpl. apply IH.
  - intros K l lts Ts ts IH cutoff c. simpl. rewrite shift_lt_in_tm_go_eq_map.
    rewrite !free_tm_vars_go_eq_concat. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn cutoff c. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff c. simpl. rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa cutoff c. simpl. rewrite IHt, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff c. simpl. apply IHop.
  - intros m T_B T_R t IH cutoff c. simpl. apply IH.
  - intros m T_B T_R b IH cutoff c. simpl. apply IH.
  - reflexivity.
  - intros t ts IHt IHts cutoff c. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma free_tm_vars_shift_lt_in_tm_any : forall t cutoff amount c,
  free_tm_vars cutoff (shift_lt_in_tm amount c t) = free_tm_vars cutoff t.
Proof.
  intros t cutoff amount c. induction amount as [|amount IH].
  - rewrite shift_lt_in_tm_zero. reflexivity.
  - replace (S amount) with (1 + amount) by lia.
    rewrite <- shift_lt_in_tm_fuse.
    rewrite free_tm_vars_shift_lt_in_tm. exact IH.
Qed.

Lemma subst_lt_in_tm_go_eq_map : forall n R ts,
  (fix go ts := match ts with [] => [] | u :: rest => subst_lt_in_tm n R u :: go rest end) ts =
  List.map (subst_lt_in_tm n R) ts.
Proof.
  intros n R ts. induction ts as [|t ts IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma free_tm_vars_subst_lt_in_tm : forall t cutoff n R,
  free_tm_vars cutoff (subst_lt_in_tm n R t) = free_tm_vars cutoff t.
Proof.
  apply (term_list_ind
    (fun t => forall cutoff n R,
      free_tm_vars cutoff (subst_lt_in_tm n R t) = free_tm_vars cutoff t)
    (fun ts => forall cutoff n R,
      List.concat (List.map (free_tm_vars cutoff) (List.map (subst_lt_in_tm n R) ts)) =
      List.concat (List.map (free_tm_vars cutoff) ts))).
  - reflexivity.
  - intros t1 t2 IH1 IH2 cutoff n R. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH cutoff n R. simpl. apply IH.
  - intros t T IH cutoff n R. simpl. apply IH.
  - intros bound body IH cutoff n R. simpl. apply IH.
  - intros t l IH cutoff n R. simpl. apply IH.
  - intros body IH cutoff n R. simpl. apply IH.
  - intros K l lts Ts ts IH cutoff n R. simpl. rewrite subst_lt_in_tm_go_eq_map.
    rewrite !free_tm_vars_go_eq_concat. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn cutoff n R. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff n R. simpl. rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa cutoff n R. simpl. rewrite IHt, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff n R. simpl. apply IHop.
  - intros m T_B T_R t IH cutoff n R. simpl. apply IH.
  - intros m T_B T_R b IH cutoff n R. simpl. apply IH.
  - reflexivity.
  - intros t ts IHt IHts cutoff n R. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma no_local_lt_shift : forall l c,
  no_local_lt (shift_lt 1 c l) = no_local_lt l.
Proof.
  induction l as [n| | |l1 IH1 l2 IH2]; intro c; simpl; try reflexivity.
  rewrite IH1, IH2. reflexivity.
Qed.

Lemma no_local_ty_go_eq_fold : forall Ts,
  (fix go Ts := match Ts with [] => true | A :: rest => andb (no_local_ty A) (go rest) end) Ts =
  fold_right (fun A acc => andb (no_local_ty A) acc) true Ts.
Proof.
  induction Ts as [|A Ts IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma no_local_ty_shift_ty : forall T c,
  no_local_ty (shift_ty 1 c T) = no_local_ty T.
Proof.
  apply (type_list_ind
    (fun T => forall c, no_local_ty (shift_ty 1 c T) = no_local_ty T)
    (fun Ts => forall c,
      fold_right (fun A acc => andb (no_local_ty A) acc) true (List.map (shift_ty 1 c) Ts) =
      fold_right (fun A acc => andb (no_local_ty A) acc) true Ts)).
  - reflexivity.
  - intros A l B IHA IHB c. simpl. rewrite IHA, IHB. reflexivity.
  - intros K l Ts IHTs c. rewrite shift_ty_ctor_eq. simpl.
    rewrite !no_local_ty_go_eq_fold. rewrite IHTs. reflexivity.
  - intros A IHA c. simpl. apply IHA.
  - intros B A IHB IHA c. simpl. rewrite IHB, IHA. reflexivity.
  - reflexivity.
  - intros A Ts IHA IHTs c. simpl. rewrite IHA, IHTs. reflexivity.
Qed.

Lemma no_local_ty_shift_lt : forall T c,
  no_local_ty (shift_lt_in_ty 1 c T) = no_local_ty T.
Proof.
  apply (type_list_ind
    (fun T => forall c, no_local_ty (shift_lt_in_ty 1 c T) = no_local_ty T)
    (fun Ts => forall c,
      fold_right (fun A acc => andb (no_local_ty A) acc) true (List.map (shift_lt_in_ty 1 c) Ts) =
      fold_right (fun A acc => andb (no_local_ty A) acc) true Ts)).
  - reflexivity.
  - intros A l B IHA IHB c. simpl. rewrite IHA, IHB, no_local_lt_shift. reflexivity.
  - intros K l Ts IHTs c. rewrite shift_lt_in_ty_ctor_eq. simpl.
    rewrite no_local_lt_shift. rewrite !no_local_ty_go_eq_fold. rewrite IHTs. reflexivity.
  - intros A IHA c. simpl. apply IHA.
  - intros B A IHB IHA c. simpl. rewrite IHB, IHA. reflexivity.
  - reflexivity.
  - intros A Ts IHA IHTs c. simpl. rewrite IHA, IHTs. reflexivity.
Qed.

Lemma no_local_lt_subst_lt : forall l n R,
  no_local_lt l = true ->
  no_local_lt (subst_lt n R l) = true.
Proof.
  induction l as [x| | |l1 IH1 l2 IH2]; intros n R Hnl; simpl in *.
  - discriminate Hnl.
  - reflexivity.
  - discriminate Hnl.
  - apply andb_prop in Hnl. destruct Hnl as [H1 H2].
    rewrite (IH1 n R H1), (IH2 n R H2). reflexivity.
Qed.

Lemma no_local_ty_subst_lt : forall T n R,
  no_local_ty T = true ->
  no_local_ty (subst_lt_in_ty n R T) = true.
Proof.
  intros T. apply (type_list_ind
    (fun T => forall n R,
      no_local_ty T = true -> no_local_ty (subst_lt_in_ty n R T) = true)
    (fun Ts => forall n R,
      fold_right (fun A acc => andb (no_local_ty A) acc) true Ts = true ->
      fold_right (fun A acc => andb (no_local_ty A) acc) true
        (List.map (subst_lt_in_ty n R) Ts) = true)).
  - intros x n R Hnl. exact Hnl.
  - intros A l B HA HB n R Hnl. simpl in *.
    repeat rewrite Bool.andb_true_iff in Hnl.
    destruct Hnl as [HnlA [Hnll HnlB]].
    rewrite (HA n R HnlA), (HB n R HnlB), (no_local_lt_subst_lt l n R Hnll).
    reflexivity.
  - intros K l Ts HTs n R Hnl. rewrite subst_lt_in_ty_ctor_eq. simpl in *.
    rewrite !no_local_ty_go_eq_fold in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [Hnll HnlTs].
    rewrite (no_local_lt_subst_lt l n R Hnll), (HTs n R HnlTs). reflexivity.
  - intros A HA n R Hnl. simpl in *. apply HA. exact Hnl.
  - intros B A HB HA n R Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlB HnlA].
    rewrite (HB n R HnlB), (HA n R HnlA). reflexivity.
  - intros n R Hnl. reflexivity.
  - intros A Ts HA HTs n R Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlA HnlTs].
    rewrite (HA n R HnlA), (HTs n R HnlTs). reflexivity.
Qed.

Lemma free_tm_vars_shift_tm_1 : forall t cutoff c,
  free_tm_vars cutoff (shift_tm 1 (cutoff + c) t) =
  List.map (shv c) (free_tm_vars cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall cutoff c,
      free_tm_vars cutoff (shift_tm 1 (cutoff + c) t) =
      List.map (shv c) (free_tm_vars cutoff t))
    (fun ts => forall cutoff c,
      List.concat (List.map (free_tm_vars cutoff) (List.map (shift_tm 1 (cutoff + c)) ts)) =
      List.map (shv c) (List.concat (List.map (free_tm_vars cutoff) ts)))).
  - intros x cutoff c. simpl.
    destruct (Nat.ltb x cutoff) eqn:Ex0.
    + assert (Hlt : x < cutoff) by (apply Nat.ltb_lt; exact Ex0).
      rewrite (proj2 (Nat.leb_gt (cutoff + c) x)) by lia.
      rewrite Ex0. reflexivity.
    + assert (Hge0 : cutoff <= x) by (apply Nat.ltb_ge; exact Ex0).
      destruct (Nat.leb (cutoff + c) x) eqn:Ex.
      * apply Nat.leb_le in Ex. rewrite Nat.add_1_r.
        rewrite (proj2 (Nat.ltb_ge (S x) cutoff)) by lia.
        unfold shv. cbn [List.map]. destruct (Nat.leb c (x - cutoff)) eqn:Ec.
        -- f_equal. rewrite Nat.sub_succ_l by lia. reflexivity.
        -- apply Nat.leb_gt in Ec. lia.
      * apply Nat.leb_gt in Ex.
        unfold shv. cbn [List.map]. destruct (Nat.leb c (x - cutoff)) eqn:Ec.
        -- apply Nat.leb_le in Ec. lia.
        -- rewrite Ex0. reflexivity.
  - intros t1 t2 IH1 IH2 cutoff c. simpl. rewrite IH1, IH2. rewrite List.map_app. reflexivity.
  - intros body T IH cutoff c. simpl. replace (S (cutoff + c)) with (S cutoff + c) by lia. apply IH.
  - intros t T IH cutoff c. simpl. apply IH.
  - intros bound body IH cutoff c. simpl. apply IH.
  - intros t l IH cutoff c. simpl. apply IH.
  - intros body IH cutoff c. simpl. apply IH.
  - intros K l lts Ts ts IH cutoff c. simpl. rewrite shift_tm_go_eq_map.
    rewrite !free_tm_vars_go_eq_concat. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn cutoff c. simpl.
    rewrite IHs, IHn.
    replace (cutoff + c + arity) with (cutoff + arity + c) by lia.
    rewrite IHy. rewrite !List.map_app. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff c. simpl.
    replace (cutoff + c + 2) with (cutoff + 2 + c) by lia.
    rewrite IHop.
    replace (S (cutoff + c)) with (S cutoff + c) by lia.
    rewrite IHb. rewrite List.map_app. reflexivity.
  - intros t Ss arg IHt IHa cutoff c. simpl. rewrite IHt, IHa. rewrite List.map_app. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff c. simpl.
    replace (cutoff + c + 2) with (cutoff + 2 + c) by lia. apply IHop.
  - intros m T_B T_R t IH cutoff c. simpl. apply IH.
  - intros m T_B T_R b IH cutoff c. simpl. replace (S (cutoff + c)) with (S cutoff + c) by lia. apply IH.
  - intros cutoff c. reflexivity.
  - intros t ts IHt IHts cutoff c. simpl. rewrite IHt, IHts. rewrite List.map_app. reflexivity.
Qed.

Lemma free_tm_vars_cutoff_mono_empty : forall t c d,
  c <= d -> free_tm_vars c t = [] -> free_tm_vars d t = [].
Proof.
  apply (term_list_ind
    (fun t => forall c d,
      c <= d -> free_tm_vars c t = [] -> free_tm_vars d t = [])
    (fun ts => forall c d,
      c <= d ->
      List.concat (List.map (free_tm_vars c) ts) = [] ->
      List.concat (List.map (free_tm_vars d) ts) = [])).
  - intros x c d Hle Hfree. simpl in *.
    destruct (Nat.ltb x c) eqn:Hxc; [|discriminate].
    apply Nat.ltb_lt in Hxc. rewrite (proj2 (Nat.ltb_lt x d)) by lia. reflexivity.
  - intros t1 t2 IH1 IH2 c d Hle Hfree. simpl in *.
    apply List.app_eq_nil in Hfree as [H1 H2].
    rewrite (IH1 c d Hle H1), (IH2 c d Hle H2). reflexivity.
  - intros body T IH c d Hle Hfree. simpl in *.
    apply IH with (c := S c); [lia|exact Hfree].
  - intros t T IH c d Hle Hfree. simpl in *. apply IH with (c := c); [exact Hle|exact Hfree].
  - intros bound body IH c d Hle Hfree. simpl in *. apply IH with (c := c); [exact Hle|exact Hfree].
  - intros t l IH c d Hle Hfree. simpl in *. apply IH with (c := c); [exact Hle|exact Hfree].
  - intros body IH c d Hle Hfree. simpl in *. apply IH with (c := c); [exact Hle|exact Hfree].
  - intros K l lts Ts ts IH c d Hle Hfree. simpl in *.
    rewrite free_tm_vars_go_eq_concat in Hfree.
    rewrite free_tm_vars_go_eq_concat. apply IH with (c := c); [exact Hle|exact Hfree].
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn c d Hle Hfree. simpl in *.
    apply List.app_eq_nil in Hfree as [Hs Hrest].
    apply List.app_eq_nil in Hrest as [Hy Hn].
    rewrite (IHs c d Hle Hs).
    rewrite (IHy (c + arity) (d + arity) ltac:(lia) Hy).
    rewrite (IHn c d Hle Hn). reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb c d Hle Hfree. simpl in *.
    apply List.app_eq_nil in Hfree as [Hop Hbody].
    rewrite (IHop (c + 2) (d + 2) ltac:(lia) Hop).
    rewrite (IHb (S c) (S d) ltac:(lia) Hbody). reflexivity.
  - intros t Ss arg IHt IHa c d Hle Hfree. simpl in *.
    apply List.app_eq_nil in Hfree as [Ht Harg].
    rewrite (IHt c d Hle Ht), (IHa c d Hle Harg). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop c d Hle Hfree. simpl in *.
    apply IHop with (c := c + 2); [lia|exact Hfree].
  - intros m T_B T_R t IH c d Hle Hfree. simpl in *. apply IH with (c := c); [exact Hle|exact Hfree].
  - intros m T_B T_R b IH c d Hle Hfree. simpl in *.
    apply IH with (c := S c); [lia|exact Hfree].
  - intros c d Hle Hfree. reflexivity.
  - intros t ts IHt IHts c d Hle Hfree. simpl in *.
    apply List.app_eq_nil in Hfree as [Ht Hts].
    rewrite (IHt c d Hle Ht), (IHts c d Hle Hts). reflexivity.
Qed.

Lemma free_tm_vars_closed_cutoff : forall t c,
  free_tm_vars 0 t = [] -> free_tm_vars c t = [].
Proof.
  intros t c Hfree. apply (free_tm_vars_cutoff_mono_empty t 0 c); [lia|exact Hfree].
Qed.

Lemma capture_lt_closed : forall Γ t,
  free_tm_vars 0 t = [] ->
  capture_lt Γ t = if has_rt_cap t then lt_local else lt_free.
Proof.
  intros Γ t Hfree. unfold capture_lt.
  destruct (has_rt_cap t); [reflexivity|].
  rewrite (free_tm_vars_closed_cutoff t 1 Hfree). reflexivity.
Qed.

Lemma lt_of_ty_G_ty_closed_eq : forall Γ T,
  ty_ty_closed 0 T -> lt_of_ty_G Γ T = lt_of_ty T.
Proof.
  enough (H : forall T, forall Γ,
    ty_ty_closed 0 T -> lt_of_ty_G Γ T = lt_of_ty T).
  { intros Γ T Hclosed. apply H. exact Hclosed. }
  apply (type_list_ind
    (fun T => forall Γ, ty_ty_closed 0 T -> lt_of_ty_G Γ T = lt_of_ty T)
    (fun Ts => forall Γ, tys_ty_closed 0 Ts ->
      lt_of_ty_ctx_list (List.length Γ) Γ Ts = lt_of_ty_list Ts)); simpl; intros; try reflexivity.
  - lia.
  - unfold lt_of_ty_G. rewrite lt_of_ty_ctx_fun. reflexivity.
  - unfold lt_of_ty_G. rewrite lt_of_ty_ctx_ctor. f_equal. apply H. exact H0.
  - unfold lt_of_ty_G. rewrite lt_of_ty_ctx_ltall. reflexivity.
  - unfold lt_of_ty_G. rewrite lt_of_ty_ctx_tyall. reflexivity.
  - destruct H1 as [HT HTs].
    change (lt_of_ty_ctx (List.length Γ) Γ A) with (lt_of_ty_G Γ A).
    change (fold_right (fun A0 acc => lt_min (lt_of_ty_ctx (List.length Γ) Γ A0) acc) lt_free Ts)
      with (lt_of_ty_ctx_list (List.length Γ) Γ Ts).
    change (fold_right (fun T0 acc => lt_min (lt_of_ty T0) acc) lt_free Ts)
      with (lt_of_ty_list Ts).
    rewrite H by exact HT. rewrite H0 by exact HTs. reflexivity.
Qed.

Lemma lt_of_ty_G_tys_closed_eq : forall Γ Ts,
  tys_ty_closed 0 Ts -> lt_of_ty_ctx_list (List.length Γ) Γ Ts = lt_of_ty_list Ts.
Proof.
  intros Γ Ts. induction Ts as [|T Ts IH]; intros Hclosed; simpl in *.
  - reflexivity.
  - destruct Hclosed as [HT HTs].
    change (lt_of_ty_ctx (List.length Γ) Γ T) with (lt_of_ty_G Γ T).
    change (fold_right (fun A acc => lt_min (lt_of_ty_ctx (List.length Γ) Γ A) acc) lt_free Ts)
      with (lt_of_ty_ctx_list (List.length Γ) Γ Ts).
    change (fold_right (fun T0 acc => lt_min (lt_of_ty T0) acc) lt_free Ts)
      with (lt_of_ty_list Ts).
    rewrite lt_of_ty_G_ty_closed_eq by exact HT. rewrite IH by exact HTs. reflexivity.
Qed.

Lemma has_rt_cap_shift_tm : forall t amount cutoff,
  has_rt_cap (shift_tm amount cutoff t) = has_rt_cap t.
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
      has_rt_cap (shift_tm amount cutoff t) = has_rt_cap t)
    (fun ts => forall amount cutoff,
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end)
        (List.map (shift_tm amount cutoff) ts) =
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts)).
  - reflexivity.
  - intros t1 t2 IH1 IH2 amount cutoff. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH amount cutoff. simpl. apply IH.
  - intros t T IH amount cutoff. simpl. apply IH.
  - intros bound body IH amount cutoff. simpl. apply IH.
  - intros t l IH amount cutoff. simpl. apply IH.
  - intros body IH amount cutoff. simpl. apply IH.
  - intros K l lts Ts ts IH amount cutoff. simpl. rewrite shift_tm_go_eq_map. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn amount cutoff. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb amount cutoff. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa amount cutoff. simpl. rewrite IHt, IHa. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros t ts IHt IHts amount cutoff. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma has_rt_cap_shift_ty_in_tm : forall t amount cutoff,
  has_rt_cap (shift_ty_in_tm amount cutoff t) = has_rt_cap t.
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
      has_rt_cap (shift_ty_in_tm amount cutoff t) = has_rt_cap t)
    (fun ts => forall amount cutoff,
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end)
        (List.map (shift_ty_in_tm amount cutoff) ts) =
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts)).
  - reflexivity.
  - intros t1 t2 IH1 IH2 amount cutoff. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH amount cutoff. simpl. apply IH.
  - intros t T IH amount cutoff. simpl. apply IH.
  - intros bound body IH amount cutoff. simpl. apply IH.
  - intros t l IH amount cutoff. simpl. apply IH.
  - intros body IH amount cutoff. simpl. apply IH.
  - intros K l lts Ts ts IH amount cutoff. simpl. rewrite shift_ty_in_tm_go_eq_map. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn amount cutoff. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb amount cutoff. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa amount cutoff. simpl. rewrite IHt, IHa. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros t ts IHt IHts amount cutoff. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma has_rt_cap_shift_lt_in_tm : forall t amount cutoff,
  has_rt_cap (shift_lt_in_tm amount cutoff t) = has_rt_cap t.
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
      has_rt_cap (shift_lt_in_tm amount cutoff t) = has_rt_cap t)
    (fun ts => forall amount cutoff,
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end)
        (List.map (shift_lt_in_tm amount cutoff) ts) =
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts)).
  - reflexivity.
  - intros t1 t2 IH1 IH2 amount cutoff. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH amount cutoff. simpl. apply IH.
  - intros t T IH amount cutoff. simpl. apply IH.
  - intros bound body IH amount cutoff. simpl. apply IH.
  - intros t l IH amount cutoff. simpl. apply IH.
  - intros body IH amount cutoff. simpl. apply IH.
  - intros K l lts Ts ts IH amount cutoff. simpl. rewrite shift_lt_in_tm_go_eq_map. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn amount cutoff. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb amount cutoff. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa amount cutoff. simpl. rewrite IHt, IHa. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros t ts IHt IHts amount cutoff. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma is_abs_shift_tm : forall t amount cutoff,
  is_abs (shift_tm amount cutoff t) = is_abs t.
Proof. destruct t; reflexivity. Qed.

Lemma is_abs_shift_ty_in_tm : forall t amount cutoff,
  is_abs (shift_ty_in_tm amount cutoff t) = is_abs t.
Proof. destruct t; reflexivity. Qed.

Lemma is_abs_shift_lt_in_tm : forall t amount cutoff,
  is_abs (shift_lt_in_tm amount cutoff t) = is_abs t.
Proof. destruct t; reflexivity. Qed.

Lemma is_abs_subst_ty_in_tm : forall t var replacement,
  is_abs (subst_ty_in_tm var replacement t) = is_abs t.
Proof. destruct t; reflexivity. Qed.

Lemma is_abs_subst_lt_in_tm : forall t var replacement,
  is_abs (subst_lt_in_tm var replacement t) = is_abs t.
Proof. destruct t; reflexivity. Qed.

Lemma is_abs_subst_tm_true : forall t var replacement,
  is_abs t = true -> is_abs (subst_tm var replacement t) = true.
Proof.
  destruct t; simpl; congruence.
Qed.

Lemma has_rt_cap_subst_lt_in_tm : forall t var replacement,
  has_rt_cap (subst_lt_in_tm var replacement t) = has_rt_cap t.
Proof.
  apply (term_list_ind
    (fun t => forall var replacement,
      has_rt_cap (subst_lt_in_tm var replacement t) = has_rt_cap t)
    (fun ts => forall var replacement,
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end)
        (List.map (subst_lt_in_tm var replacement) ts) =
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts)).
  - reflexivity.
  - intros t1 t2 IH1 IH2 var replacement. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH var replacement. simpl. apply IH.
  - intros t T IH var replacement. simpl. apply IH.
  - intros bound body IH var replacement. simpl. apply IH.
  - intros t l IH var replacement. simpl. apply IH.
  - intros body IH var replacement. simpl. apply IH.
  - intros K l lts Ts ts IH var replacement. simpl. rewrite subst_lt_in_tm_go_eq_map. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn var replacement. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb var replacement. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa var replacement. simpl. rewrite IHt, IHa. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros t ts IHt IHts var replacement. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma capture_lt_InsTmAt : forall c G G', InsTmAt c G G' ->
  forall body, capture_lt G' (shift_tm 1 (S c) body) = capture_lt G body.
Proof.
  intros c G G' HIns body. unfold capture_lt.
  replace (S c) with (1 + c) by lia.
  rewrite has_rt_cap_shift_tm.
  destruct (has_rt_cap body) eqn:Hcap; [reflexivity|].
  rewrite free_tm_vars_shift_tm_1.
  induction (free_tm_vars 1 body) as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite (InsTmAt_lookup_tm c G G' HIns x).
    destruct (ctx_lookup_tm G x) as [T|] eqn:Hlk;
      [rewrite (lt_of_ty_G_InsTm G G' (InsTmAt_to_InsTm c G G' HIns) T)|];
      rewrite IH; reflexivity.
Qed.

Lemma capture_lt_InsTy : forall c G G', InsTy c G G' ->
  forall body, capture_lt G' (shift_ty_in_tm 1 c body) = capture_lt G body.
Proof.
  intros c G G' HIns body. unfold capture_lt.
  rewrite has_rt_cap_shift_ty_in_tm.
  destruct (has_rt_cap body) eqn:Hcap; [reflexivity|].
  rewrite free_tm_vars_shift_ty_in_tm.
  induction (free_tm_vars 1 body) as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite (InsTy_lookup_tm c G G' HIns x).
    destruct (ctx_lookup_tm G x) as [T|] eqn:Hlk; simpl.
    + rewrite (lt_of_ty_G_InsTy c G G' HIns T). rewrite IH. reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma capture_lt_InsLt : forall c G G', InsLt c G G' ->
  forall body, capture_lt G' (shift_lt_in_tm 1 c body) = shift_lt 1 c (capture_lt G body).
Proof.
  intros c G G' HIns body. unfold capture_lt.
  rewrite has_rt_cap_shift_lt_in_tm.
  destruct (has_rt_cap body) eqn:Hcap; [reflexivity|].
  rewrite free_tm_vars_shift_lt_in_tm.
  induction (free_tm_vars 1 body) as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite (InsLt_lookup_tm c G G' HIns x).
    destruct (ctx_lookup_tm G x) as [T|] eqn:Hlk; simpl.
    + rewrite (lt_of_ty_G_InsLt c G G' HIns T). rewrite IH. reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma typing_ind_forall2 :
  forall (P : ctx -> term -> type -> Prop),
  (forall Γ x T, ctx_lookup_tm Γ x = Some T -> ty_wf Γ T -> P Γ (term_var x) T) ->
  (forall Γ t T U, Γ ⊢ₜ t : T -> P Γ t T -> Γ ⊢ T <:: U -> P Γ t U) ->
  (forall Γ body A l B,
      ty_wf Γ A ->
      ty_wf Γ B ->
     (bind_tm A :: Γ) ⊢ₜ body : B -> P (bind_tm A :: Γ) body B ->
      Γ ⊢ₗ capture_lt Γ body <: l ->
     P Γ (term_lam body A) (type_fun A l B)) ->
  (forall Γ t1 t2 A l B,
     Γ ⊢ₜ t1 : type_fun A l B -> P Γ t1 (type_fun A l B) ->
     Γ ⊢ₜ t2 : A -> P Γ t2 A ->
     P Γ (term_app t1 t2) B) ->
  (forall Γ bound body T,
      ty_wf Γ bound ->
      ty_wf (bind_ty bound :: Γ) T ->
      is_abs body = true ->
     (bind_ty bound :: Γ) ⊢ₜ body : T -> P (bind_ty bound :: Γ) body T ->
     P Γ (term_ty_lam bound body) (type_ty_all bound T)) ->
  (forall Γ t B U S,
     Γ ⊢ₜ t : type_ty_all B U -> P Γ t (type_ty_all B U) ->
      ty_wf Γ S ->
     Γ ⊢ S <:: B ->
      ty_app_arg_no_local Γ B S = true ->
     P Γ (term_ty_app t S) (subst_ty 0 S U)) ->
  (forall Γ body T,
      ty_wf (bind_lt lt_local :: Γ) T ->
      is_abs body = true ->
     (bind_lt lt_local :: Γ) ⊢ₜ body : T -> P (bind_lt lt_local :: Γ) body T ->
     P Γ (term_lt_lam body) (type_lt_all T)) ->
  (forall Γ t T l,
     Γ ⊢ₜ t : type_lt_all T -> P Γ t (type_lt_all T) ->
      lt_wf Γ l ->
     P Γ (term_lt_app t l) (subst_lt_in_ty 0 l T)) ->
        (forall Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
          result_ty result_tag l vs,
     ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) ->
     ctx_lookup_eff Γ K = None ->
     List.length lts = n_lt ->
    lifetimes_wf Γ lts ->
     rho_fields = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields ->
     List.length Ts = n_ty ->
    types_wf Γ Ts ->
      result_ty = inst_ctor_type n_lt n_ty lts Ts result_ty_schema ->
      result_ty = type_ctor result_tag l Ts ->
      ctx_lookup_eff Γ result_tag = None ->
     lt_wf Γ l ->
      Γ ⊢ₗ lt_of_ty_list rho_fields <: lt_of_ty result_ty ->
      Forall (fun l0 => Γ ⊢ₗ l0 <: l) lts ->
     List.length vs = List.length rho_fields ->
     Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rho_fields ->
     Forall2 (fun v rho => P Γ v rho) vs rho_fields ->
      P Γ (term_ctor K l lts Ts vs) result_ty) ->
      (forall Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
        rho_fields scrut_result_ty result_tag result_l
         Γ' yes_body eta elim_result no_body,
     K <> any_tag ->
     ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) ->
     ctx_lookup_eff Γ K = None ->
     lts = lt_var_list n_lt ->
     rho_fields = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields ->
      List.length Ts = n_ty ->
      types_wf Γ Ts ->
         scrut_result_ty = inst_ctor_type n_lt n_ty (List.repeat Delta n_lt) Ts result_ty_schema ->
        scrut_result_ty = type_ctor result_tag result_l Ts ->
      ctx_lookup_eff Γ result_tag = None ->
      result_tag <> any_tag ->
        lt_wf Γ Delta ->
         Γ ⊢ₗ result_l <: Delta ->
        Γ ⊢ₜ scrut : type_ctor result_tag Delta Ts ->
        P Γ scrut (type_ctor result_tag Delta Ts) ->
     arity = List.length rho_fields ->
     Γ' = push_lt_vars n_lt Delta Γ ->
     (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ' rho_fields) ⊢ₜ yes_body : eta ->
     P (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ' rho_fields) yes_body eta ->
     elim_ty_n n_lt (shift_lt n_lt 0 Delta) var_pos eta = Some elim_result ->
     Γ ⊢ₜ no_body : elim_result -> P Γ no_body elim_result ->
    P Γ (term_match scrut K n_lt arity yes_body no_body) elim_result) ->
  (forall Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β,
     ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
     List.length Ts = n_α ->
    types_wf Γ Ts ->
    ty_wf Γ T_R ->
      sig_β = inst_op_alpha n_α Ts n_β sig ->
      ret_β = inst_op_alpha n_α Ts n_β ret ->
     (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) ⊢ₜ op_body : shift_ty n_β 0 T_R ->
     P (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) op_body (shift_ty n_β 0 T_R) ->
    P Γ (term_cap E_tag m n_β Ts T_R op_body) (type_ctor E_tag lt_local Ts)) ->
  (forall Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β,
     ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
     List.length Ts = n_α ->
    types_wf Γ Ts ->
    ty_wf Γ T_B ->
    ty_wf Γ T_R ->
    no_local_ty_G Γ T_B = true ->
    Γ ⊢ T_B <:: T_R ->
      sig_β = inst_op_alpha n_α Ts n_β sig ->
      ret_β = inst_op_alpha n_α Ts n_β ret ->
     (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) ⊢ₜ op_body : shift_ty n_β 0 T_R ->
     P (bind_tm sig_β
        :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
        :: push_ty_vars n_β any_at_free Γ) op_body (shift_ty n_β 0 T_R) ->
      (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) ⊢ₜ body : T_B ->
      P (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) body T_B ->
     P Γ (term_handle E_tag n_β Ts T_B T_R op_body body) T_R) ->
  (forall Γ recv arg E_tag Delta Ts Ss n_α n_β sig ret sig_inst ret_inst,
     Γ ⊢ₜ recv : type_ctor E_tag Delta Ts -> P Γ recv (type_ctor E_tag Delta Ts) ->
     ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
     List.length Ts = n_α ->
     List.length Ss = n_β ->
    types_wf Γ Ss ->
    forallb (no_local_ty_G Γ) Ss = true ->
     sig_inst = inst_op_arg n_α Ts n_β Ss sig ->
      no_local_ty_G Γ sig_inst = true ->
     ret_inst = inst_op_arg n_α Ts n_β Ss ret ->
    ty_wf Γ ret_inst ->
     Γ ⊢ₜ arg : sig_inst -> P Γ arg sig_inst ->
     P Γ (term_perform recv Ss arg) ret_inst) ->
  (forall Γ m T_B T_R t,
      ty_wf Γ T_B ->
      ty_wf Γ T_R ->
      no_local_ty_G Γ T_B = true ->
      Γ ⊢ T_B <:: T_R ->
      Γ ⊢ₜ t : T_B -> P Γ t T_B ->
      P Γ (term_handler_m m T_B T_R t) T_R) ->
  (forall Γ m b A T_B T_R,
      ty_wf Γ A ->
      ty_wf Γ T_B ->
      ty_wf Γ T_R ->
      no_local_ty_G Γ T_B = true ->
      Γ ⊢ T_B <:: T_R ->
     (bind_tm A :: Γ) ⊢ₜ b : T_B -> P (bind_tm A :: Γ) b T_B ->
    P Γ (term_resume m T_B T_R b) (type_fun A lt_local T_R)) ->
  forall Γ t T, Γ ⊢ₜ t : T -> P Γ t T.
Proof.
  intros P HVar HSub HLam HApp HTyLam HTyApp HLtLam HLtApp HCtor HMatch
         HCap HHandle HPerform HHandlerM HResume.
  fix IH 4.
  intros Γ t T H. destruct H.
  - eapply HVar; (eassumption || (apply IH; eassumption)).
  - eapply HSub; (eassumption || (apply IH; eassumption)).
  - eapply HLam; (eassumption || (apply IH; eassumption)).
  - eapply HApp; (eassumption || (apply IH; eassumption)).
  - eapply HTyLam; (eassumption || (apply IH; eassumption)).
  - eapply HTyApp; (eassumption || (apply IH; eassumption)).
  - eapply HLtLam; (eassumption || (apply IH; eassumption)).
  - eapply HLtApp; (eassumption || (apply IH; eassumption)).
  - eapply HCtor; try (eassumption || (apply IH; eassumption)).
    match goal with
    | HF : Forall2 (fun v rho => _ ⊢ₜ v : rho) ?vs ?rf |- Forall2 _ ?vs ?rf =>
        clear -IH HF; induction HF
    end.
    + constructor.
    + constructor; [apply IH; assumption | assumption].
  - eapply HMatch; (eassumption || (apply IH; eassumption)).
  - eapply HCap; (eassumption || (apply IH; eassumption)).
  - eapply HHandle; (eassumption || (apply IH; eassumption)).
  - eapply HPerform; (eassumption || (apply IH; eassumption)).
  - eapply HHandlerM; (eassumption || (apply IH; eassumption)).
  - eapply HResume; (eassumption || (apply IH; eassumption)).
Qed.

Lemma InsTmAt_push_lt_vars : forall n Delta c G G',
  InsTmAt c G G' -> InsTmAt c (push_lt_vars n Delta G) (push_lt_vars n Delta G').
Proof.
  induction n as [|n IH]; intros Delta c G G' H; simpl.
  - exact H.
  - apply IH. apply InsTmAt_lt. exact H.
Qed.

Lemma InsTmAt_push_ty_vars : forall n B c G G',
  InsTmAt c G G' -> InsTmAt c (push_ty_vars n B G) (push_ty_vars n B G').
Proof.
  induction n as [|n IH]; intros B c G G' H; simpl.
  - exact H.
  - apply IH. apply InsTmAt_ty. exact H.
Qed.

Lemma InsTy_push_lt_vars : forall n Delta c G G',
  InsTy c G G' -> InsTy c (push_lt_vars n Delta G) (push_lt_vars n Delta G').
Proof.
  induction n as [|n IH]; intros Delta c G G' H; simpl.
  - exact H.
  - apply IH. apply InsTy_lt. exact H.
Qed.

(* ================================================================== *)
(* Stability of the context-sensitive no-local checks under weakening *)
(*                                                                    *)
(* The new typing premises ([no_local_ty_G], [ty_app_arg_no_local],   *)
(* [forallb no_local_ty_G ...]) read the bound of each type variable  *)
(* from the context, so weakening lemmas must show they are preserved *)
(* when a binder is inserted ([InsTm]/[InsTy]/[InsLt]).  The two      *)
(* [is_any_at_free_bound_shift_*] lemmas establish that shifting an   *)
(* inserted bound does not change whether it is [Any]'free, and       *)
(* [no_local_ty_G_go_eq_fold] re-exposes the inner [go] fixpoint as a *)
(* [fold_right] so it can be reasoned about by [Forall]/induction.    *)
(* ================================================================== *)

Lemma shift_ty_any_at_free : forall c, shift_ty 1 c any_at_free = any_at_free.
Proof. intros c. reflexivity. Qed.

Lemma shift_lt_any_at_free : forall c, shift_lt_in_ty 1 c any_at_free = any_at_free.
Proof. intros c. reflexivity. Qed.

Lemma is_any_at_free_bound_shift_ty : forall T c,
  is_any_at_free_bound (shift_ty 1 c T) = is_any_at_free_bound T.
Proof.
  destruct T as [n|A l B|K l Ts|A|B A]; intros c; simpl; try reflexivity.
  destruct l; destruct Ts; reflexivity.
Qed.

Lemma is_any_at_free_bound_shift_lt : forall T c,
  is_any_at_free_bound (shift_lt_in_ty 1 c T) = is_any_at_free_bound T.
Proof.
  destruct T as [n|A l B|K l Ts|A|B A]; intros c; simpl; try reflexivity.
  destruct l; destruct Ts; reflexivity.
Qed.

Lemma no_local_ty_G_go_eq_fold : forall Γ Ts,
  (fix go (Γ0 : ctx) (Ts0 : list type) {struct Ts0} : bool :=
     match Ts0 with
     | [] => true
     | A :: rest => andb (no_local_ty_G Γ0 A) (go Γ0 rest)
     end) Γ Ts =
  fold_right (fun A acc => andb (no_local_ty_G Γ A) acc) true Ts.
Proof.
  intros Gamma Ts. induction Ts as [|A Ts IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma no_local_ty_G_InsTm : forall Γ T G',
  InsTm Γ G' ->
  no_local_ty_G Γ T = true ->
  no_local_ty_G G' T = true.
Proof.
  intros Γ T. revert Γ.
  apply (type_list_ind
    (fun T => forall Γ G', InsTm Γ G' ->
      no_local_ty_G Γ T = true -> no_local_ty_G G' T = true)
    (fun Ts => forall Γ G', InsTm Γ G' ->
      fold_right (fun A acc => andb (no_local_ty_G Γ A) acc) true Ts = true ->
      fold_right (fun A acc => andb (no_local_ty_G G' A) acc) true Ts = true)).
  - intros x Γ G' HIns Hnl. simpl in *. rewrite (InsTm_lookup_ty Γ G' HIns x). exact Hnl.
  - intros A l B IHA IHB Γ G' HIns Hnl. simpl in *.
    repeat rewrite Bool.andb_true_iff in Hnl.
    destruct Hnl as [HnlA [Hnll HnlB]].
    rewrite (IHA Γ G' HIns HnlA), (IHB Γ G' HIns HnlB), Hnll. reflexivity.
  - intros K l Ts IHTs Γ G' HIns Hnl. simpl in *.
    rewrite !no_local_ty_G_go_eq_fold in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [Hnll HnlTs].
    rewrite Hnll, (IHTs Γ G' HIns HnlTs). reflexivity.
  - intros A IHA Γ G' HIns Hnl. simpl in *.
    apply IHA with (Γ := bind_lt lt_local :: Γ).
    + apply InsTm_lt. exact HIns.
    + exact Hnl.
  - intros B A IHB IHA Γ G' HIns Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlB HnlA].
    rewrite (IHB Γ G' HIns HnlB).
    rewrite (IHA (bind_ty B :: Γ) (bind_ty B :: G') (InsTm_ty B Γ G' HIns) HnlA).
    reflexivity.
  - intros Γ G' HIns Hnl. reflexivity.
  - intros A Ts IHA IHTs Γ G' HIns Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlA HnlTs].
    rewrite (IHA Γ G' HIns HnlA), (IHTs Γ G' HIns HnlTs). reflexivity.
Qed.

Lemma no_local_ty_G_InsTy : forall Γ T c G',
  InsTy c Γ G' ->
  no_local_ty_G Γ T = true ->
  no_local_ty_G G' (shift_ty 1 c T) = true.
Proof.
  intros Γ T. revert Γ.
  apply (type_list_ind
    (fun T => forall Γ c G', InsTy c Γ G' ->
      no_local_ty_G Γ T = true -> no_local_ty_G G' (shift_ty 1 c T) = true)
    (fun Ts => forall Γ c G', InsTy c Γ G' ->
      fold_right (fun A acc => andb (no_local_ty_G Γ A) acc) true Ts = true ->
      fold_right (fun A acc => andb (no_local_ty_G G' A) acc) true (List.map (shift_ty 1 c) Ts) = true)).
  - intros x Γ c G' HIns Hnl. simpl in *.
    replace (if c <=? x then x + 1 else x) with (shv c x) by (unfold shv; destruct (c <=? x); lia).
    rewrite (InsTy_lookup_ty c Γ G' HIns x).
    destruct (ctx_lookup_ty Γ x) as [B|] eqn:HB; simpl in *; [|discriminate].
    rewrite is_any_at_free_bound_shift_ty. exact Hnl.
  - intros A l B IHA IHB Γ c G' HIns Hnl. simpl in *.
    repeat rewrite Bool.andb_true_iff in Hnl.
    destruct Hnl as [HnlA [Hnll HnlB]].
    rewrite (IHA Γ c G' HIns HnlA), (IHB Γ c G' HIns HnlB), Hnll. reflexivity.
  - intros K l Ts IHTs Γ c G' HIns Hnl. rewrite shift_ty_ctor_eq. simpl in *.
    rewrite !no_local_ty_G_go_eq_fold in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [Hnll HnlTs].
    rewrite Hnll, (IHTs Γ c G' HIns HnlTs). reflexivity.
  - intros A IHA Γ c G' HIns Hnl. simpl in *.
    apply IHA with (Γ := bind_lt lt_local :: Γ).
    + apply InsTy_lt. exact HIns.
    + exact Hnl.
  - intros B A IHB IHA Γ c G' HIns Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlB HnlA].
    rewrite (IHB Γ c G' HIns HnlB).
    rewrite (IHA (bind_ty B :: Γ) (S c) (bind_ty (shift_ty 1 c B) :: G')
              (InsTy_ty c Γ G' B HIns) HnlA).
    reflexivity.
  - intros Γ c G' HIns Hnl. reflexivity.
  - intros A Ts IHA IHTs Γ c G' HIns Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlA HnlTs].
    rewrite (IHA Γ c G' HIns HnlA), (IHTs Γ c G' HIns HnlTs). reflexivity.
Qed.

Lemma no_local_ty_G_InsLt : forall Γ T c G',
  InsLt c Γ G' ->
  no_local_ty_G Γ T = true ->
  no_local_ty_G G' (shift_lt_in_ty 1 c T) = true.
Proof.
  intros Γ T. revert Γ.
  apply (type_list_ind
    (fun T => forall Γ c G', InsLt c Γ G' ->
      no_local_ty_G Γ T = true -> no_local_ty_G G' (shift_lt_in_ty 1 c T) = true)
    (fun Ts => forall Γ c G', InsLt c Γ G' ->
      fold_right (fun A acc => andb (no_local_ty_G Γ A) acc) true Ts = true ->
      fold_right (fun A acc => andb (no_local_ty_G G' A) acc) true (List.map (shift_lt_in_ty 1 c) Ts) = true)).
  - intros x Γ c G' HIns Hnl. simpl in *.
    rewrite (InsLt_lookup_ty c Γ G' HIns x).
    destruct (ctx_lookup_ty Γ x) as [B|] eqn:HB; simpl in *; [|discriminate].
    rewrite is_any_at_free_bound_shift_lt. exact Hnl.
  - intros A l B IHA IHB Γ c G' HIns Hnl. simpl in *.
    repeat rewrite Bool.andb_true_iff in Hnl.
    destruct Hnl as [HnlA [Hnll HnlB]].
    rewrite (IHA Γ c G' HIns HnlA), (IHB Γ c G' HIns HnlB).
    rewrite no_local_lt_shift, Hnll. reflexivity.
  - intros K l Ts IHTs Γ c G' HIns Hnl. rewrite shift_lt_in_ty_ctor_eq. simpl in *.
    rewrite !no_local_ty_G_go_eq_fold in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [Hnll HnlTs].
    rewrite no_local_lt_shift, Hnll, (IHTs Γ c G' HIns HnlTs). reflexivity.
  - intros A IHA Γ c G' HIns Hnl. simpl in *.
    apply IHA with (Γ := bind_lt lt_local :: Γ).
    + apply InsLt_lt. exact HIns.
    + exact Hnl.
  - intros B A IHB IHA Γ c G' HIns Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlB HnlA].
    rewrite (IHB Γ c G' HIns HnlB).
    rewrite (IHA (bind_ty B :: Γ) c (bind_ty (shift_lt_in_ty 1 c B) :: G')
              (InsLt_ty c Γ G' B HIns) HnlA).
    reflexivity.
  - intros Γ c G' HIns Hnl. reflexivity.
  - intros A Ts IHA IHTs Γ c G' HIns Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlA HnlTs].
    rewrite (IHA Γ c G' HIns HnlA), (IHTs Γ c G' HIns HnlTs). reflexivity.
Qed.

Lemma ty_app_arg_no_local_InsTm : forall Γ B S G',
  InsTm Γ G' ->
  ty_app_arg_no_local Γ B S = true ->
  ty_app_arg_no_local G' B S = true.
Proof.
  intros Γ B S G' HIns Hnl. unfold ty_app_arg_no_local in *.
  destruct (is_any_at_free_bound B) eqn:HB; [|exact Hnl].
  eapply no_local_ty_G_InsTm; eauto.
Qed.

Lemma ty_app_arg_no_local_InsTy : forall Γ B S c G',
  InsTy c Γ G' ->
  ty_app_arg_no_local Γ B S = true ->
  ty_app_arg_no_local G' (shift_ty 1 c B) (shift_ty 1 c S) = true.
Proof.
  intros Γ B S c G' HIns Hnl. unfold ty_app_arg_no_local in *.
  rewrite is_any_at_free_bound_shift_ty.
  destruct (is_any_at_free_bound B) eqn:HB; [|exact Hnl].
  eapply no_local_ty_G_InsTy; eauto.
Qed.

Lemma ty_app_arg_no_local_InsLt : forall Γ B S c G',
  InsLt c Γ G' ->
  ty_app_arg_no_local Γ B S = true ->
  ty_app_arg_no_local G' (shift_lt_in_ty 1 c B) (shift_lt_in_ty 1 c S) = true.
Proof.
  intros Γ B S c G' HIns Hnl. unfold ty_app_arg_no_local in *.
  rewrite is_any_at_free_bound_shift_lt.
  destruct (is_any_at_free_bound B) eqn:HB; [|exact Hnl].
  eapply no_local_ty_G_InsLt; eauto.
Qed.

Lemma forallb_no_local_ty_G_InsTm : forall Γ Ss G',
  InsTm Γ G' ->
  forallb (no_local_ty_G Γ) Ss = true ->
  forallb (no_local_ty_G G') Ss = true.
Proof.
  intros Gamma Ss. induction Ss as [|S Ss IH]; intros G' HIns Hnl; simpl in *; [reflexivity|].
  apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlS HnlSs].
  rewrite (no_local_ty_G_InsTm Gamma S G' HIns HnlS), (IH G' HIns HnlSs). reflexivity.
Qed.

Lemma forallb_no_local_ty_G_InsTy : forall Γ Ss c G',
  InsTy c Γ G' ->
  forallb (no_local_ty_G Γ) Ss = true ->
  forallb (no_local_ty_G G') (List.map (shift_ty 1 c) Ss) = true.
Proof.
  intros Gamma Ss. induction Ss as [|S Ss IH]; intros c G' HIns Hnl; simpl in *; [reflexivity|].
  apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlS HnlSs].
  rewrite (no_local_ty_G_InsTy Gamma S c G' HIns HnlS), (IH c G' HIns HnlSs). reflexivity.
Qed.

Lemma forallb_no_local_ty_G_InsLt : forall Γ Ss c G',
  InsLt c Γ G' ->
  forallb (no_local_ty_G Γ) Ss = true ->
  forallb (no_local_ty_G G') (List.map (shift_lt_in_ty 1 c) Ss) = true.
Proof.
  intros Gamma Ss. induction Ss as [|S Ss IH]; intros c G' HIns Hnl; simpl in *; [reflexivity|].
  apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlS HnlSs].
  rewrite (no_local_ty_G_InsLt Gamma S c G' HIns HnlS), (IH c G' HIns HnlSs). reflexivity.
Qed.

Lemma no_local_ty_G_InsLt_closed : forall G T c G',
  InsLt c G G' ->
  ty_lt_closed c T ->
  no_local_ty_G G T = true ->
  no_local_ty_G G' T = true.
Proof.
  intros G T c G' HIns Hclosed Hnl.
  pose proof (no_local_ty_G_InsLt G T c G' HIns Hnl) as Hnl'.
  rewrite shift_lt_in_type_closed in Hnl' by exact Hclosed. exact Hnl'.
Qed.

Lemma ty_app_arg_no_local_InsLt_closed : forall G B S c G',
  InsLt c G G' ->
  ty_lt_closed c B ->
  ty_lt_closed c S ->
  ty_app_arg_no_local G B S = true ->
  ty_app_arg_no_local G' B S = true.
Proof.
  intros G B S c G' HIns HB HS Hnl.
  pose proof (ty_app_arg_no_local_InsLt G B S c G' HIns Hnl) as Hnl'.
  rewrite shift_lt_in_type_closed in Hnl' by exact HB.
  rewrite shift_lt_in_type_closed in Hnl' by exact HS.
  exact Hnl'.
Qed.

Lemma forallb_no_local_ty_G_InsLt_closed : forall G Ts c G',
  InsLt c G G' ->
  tys_lt_closed c Ts ->
  forallb (no_local_ty_G G) Ts = true ->
  forallb (no_local_ty_G G') Ts = true.
Proof.
  intros G Ts c G' HIns Hclosed Hnl.
  pose proof (forallb_no_local_ty_G_InsLt G Ts c G' HIns Hnl) as Hnl'.
  change (List.map (shift_lt_in_ty 1 c) Ts) with (shift_lt_in_ty_list 1 c Ts) in Hnl'.
  rewrite shift_lt_in_ty_list_closed in Hnl' by exact Hclosed. exact Hnl'.
Qed.

Lemma InsTy_push_ty_vars_any_at_free : forall n c G G',
  InsTy c G G' ->
  InsTy (n + c) (push_ty_vars n any_at_free G) (push_ty_vars n any_at_free G').
Proof.
  induction n as [|n IH]; intros c G G' H; simpl.
  - replace (0 + c) with c by lia. exact H.
  - replace (S (n + c)) with (n + S c) by lia.
    apply IH. rewrite <- (shift_ty_any_at_free c).
    apply InsTy_ty. exact H.
Qed.

Lemma InsLt_push_ty_vars_any_at_free : forall n c G G',
  InsLt c G G' ->
  InsLt c (push_ty_vars n any_at_free G) (push_ty_vars n any_at_free G').
Proof.
  induction n as [|n IH]; intros c G G' H; simpl.
  - exact H.
  - apply IH. rewrite <- (shift_lt_any_at_free c).
    apply InsLt_ty. exact H.
Qed.

Lemma InsTmAt_fold_bind_tm : forall rhos c G G',
  InsTmAt c G G' ->
  InsTmAt (c + List.length rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G' rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros c G G' H; simpl.
  - replace (c + 0) with c by lia. exact H.
  - replace (c + S (List.length rhos)) with (S (c + List.length rhos)) by lia.
    apply InsTmAt_tm. apply IH. exact H.
Qed.

Lemma InsTy_fold_bind_tm : forall rhos c G G',
  InsTy c G G' ->
  InsTy c
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm (shift_ty 1 c rho) :: G0) G' rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros c G G' H; simpl.
  - exact H.
  - apply InsTy_tm. apply IH. exact H.
Qed.

Lemma InsLt_fold_bind_tm : forall rhos c G G',
  InsLt c G G' ->
  InsLt c
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm (shift_lt_in_ty 1 c rho) :: G0) G' rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros c G G' H; simpl.
  - exact H.
  - apply InsLt_tm. apply IH. exact H.
Qed.

Lemma InsLt_push_lt_vars_closed : forall k Delta c G G',
  InsLt c G G' ->
  lt_lt_closed c Delta ->
  InsLt (c + k) (push_lt_vars k Delta G) (push_lt_vars k Delta G').
Proof.
  induction k as [|k IH]; intros Delta c G G' HIns Hclosed; simpl.
  - replace (c + 0) with c by lia. exact HIns.
  - replace (c + S k) with (S c + k) by lia.
    apply IH.
    + assert (Hctx : bind_lt (shift_lt 1 c Delta) :: G' = bind_lt Delta :: G').
      { rewrite shift_lt_closed_lifetime by exact Hclosed. reflexivity. }
      rewrite <- Hctx. apply InsLt_lt. exact HIns.
    + eapply lt_lt_closed_mono; [|exact Hclosed]. lia.
Qed.

Lemma InsLt_fold_bind_tm_closed : forall rhos c G G',
  InsLt c G G' ->
  tys_lt_closed c rhos ->
  InsLt c
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G' rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros c G G' HIns Hclosed; simpl in *.
  - exact HIns.
  - destruct Hclosed as [Hrho Hrhos].
    assert (Hctx :
      bind_tm (shift_lt_in_ty 1 c rho) ::
        List.fold_right (fun rho0 G0 => bind_tm rho0 :: G0) G' rhos =
      bind_tm rho :: List.fold_right (fun rho0 G0 => bind_tm rho0 :: G0) G' rhos).
    { rewrite shift_lt_in_type_closed by exact Hrho. reflexivity. }
    rewrite <- Hctx. apply InsLt_tm. apply IH; assumption.
Qed.

Lemma InsLt_bind_tm_closed : forall A c G G',
  InsLt c G G' -> ty_lt_closed c A ->
  InsLt c (bind_tm A :: G) (bind_tm A :: G').
Proof.
  intros A c G G' HIns Hclosed.
  assert (Hctx : bind_tm (shift_lt_in_ty 1 c A) :: G' = bind_tm A :: G').
  { rewrite shift_lt_in_type_closed by exact Hclosed. reflexivity. }
  rewrite <- Hctx. apply InsLt_tm. exact HIns.
Qed.

Lemma InsLt_bind_ty_closed : forall B c G G',
  InsLt c G G' -> ty_lt_closed c B ->
  InsLt c (bind_ty B :: G) (bind_ty B :: G').
Proof.
  intros B c G G' HIns Hclosed.
  assert (Hctx : bind_ty (shift_lt_in_ty 1 c B) :: G' = bind_ty B :: G').
  { rewrite shift_lt_in_type_closed by exact Hclosed. reflexivity. }
  rewrite <- Hctx. apply InsLt_ty. exact HIns.
Qed.

Lemma InsLt_bind_lt_closed : forall D c G G',
  InsLt c G G' -> lt_lt_closed c D ->
  InsLt (S c) (bind_lt D :: G) (bind_lt D :: G').
Proof.
  intros D c G G' HIns Hclosed.
  assert (Hctx : bind_lt (shift_lt 1 c D) :: G' = bind_lt D :: G').
  { rewrite shift_lt_closed_lifetime by exact Hclosed. reflexivity. }
  rewrite <- Hctx. apply InsLt_lt. exact HIns.
Qed.

Lemma Forall2_typing_InsTmAt : forall Γ vs rhos,
  Forall2 (fun v rho => forall c G', InsTmAt c Γ G' -> G' ⊢ₜ shift_tm 1 c v : rho) vs rhos ->
  forall c G', InsTmAt c Γ G' ->
  Forall2 (fun v rho => G' ⊢ₜ v : rho) (List.map (shift_tm 1 c) vs) rhos.
Proof.
  intros Γ vs rhos H. induction H; intros c G' HIns; simpl.
  - constructor.
  - constructor.
    + apply H. exact HIns.
    + apply IHForall2. exact HIns.
Qed.

Lemma Forall2_typing_InsTy : forall Γ vs rhos,
  Forall2 (fun v rho => forall c G', InsTy c Γ G' -> G' ⊢ₜ shift_ty_in_tm 1 c v : shift_ty 1 c rho) vs rhos ->
  forall c G', InsTy c Γ G' ->
  Forall2 (fun v rho => G' ⊢ₜ v : rho)
           (List.map (shift_ty_in_tm 1 c) vs) (List.map (shift_ty 1 c) rhos).
Proof.
  intros Γ vs rhos H. induction H; intros c G' HIns; simpl.
  - constructor.
  - constructor.
    + apply H. exact HIns.
    + apply IHForall2. exact HIns.
Qed.

Lemma Forall2_typing_InsLt : forall Γ vs rhos,
  Forall2 (fun v rho => forall c G', InsLt c Γ G' -> G' ⊢ₜ shift_lt_in_tm 1 c v : shift_lt_in_ty 1 c rho) vs rhos ->
  forall c G', InsLt c Γ G' ->
  Forall2 (fun v rho => G' ⊢ₜ v : rho)
           (List.map (shift_lt_in_tm 1 c) vs) (List.map (shift_lt_in_ty 1 c) rhos).
Proof.
  intros Γ vs rhos H. induction H; intros c G' HIns; simpl.
  - constructor.
  - constructor.
    + apply H. exact HIns.
    + apply IHForall2. exact HIns.
Qed.

Lemma typing_InsTmAt : forall G t T, G ⊢ₜ t : T ->
  forall c G', InsTmAt c G G' -> G' ⊢ₜ shift_tm 1 c t : T.
Proof.
  apply (typing_ind_forall2 (fun G t T => forall c G', InsTmAt c G G' -> G' ⊢ₜ shift_tm 1 c t : T)).
  - intros Γ x T Hlk Hwf c G' HIns. simpl. eapply typing_var_InsTmAt; eauto.
  - intros Γ t T U Ht IHt Hsub c G' HIns. simpl.
    eapply T_Sub.
    + apply IHt. exact HIns.
    + apply (sub_InsTm Γ T U Hsub G' (InsTmAt_to_InsTm c Γ G' HIns)).
  - intros Γ body A l B HwfA HwfB Hbody IHbody Hcap c G' HIns. simpl.
    apply T_Lam.
    + eapply ty_wf_InsTm; [exact HwfA|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfB|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + apply IHbody. apply InsTmAt_tm. exact HIns.
    + rewrite (capture_lt_InsTmAt c Γ G' HIns body).
      apply (lt_sub_InsTm Γ (capture_lt Γ body) l Hcap G' (InsTmAt_to_InsTm c Γ G' HIns)).
  - intros Γ t1 t2 A l B Ht1 IHt1 Ht2 IHt2 c G' HIns. simpl.
    eapply T_App; [apply IHt1|apply IHt2]; exact HIns.
  - intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody c G' HIns. simpl.
    apply T_TyLam.
    + eapply ty_wf_InsTm; [exact HwfBound|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfT|]. apply InsTm_ty. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + rewrite is_abs_shift_tm. exact HisAbs.
    + apply IHbody. apply InsTmAt_ty. exact HIns.
  - intros Γ t B U S Ht IHt HwfS Hsub HnlArg c G' HIns. simpl.
    eapply T_TyApp.
    + apply IHt. exact HIns.
    + eapply ty_wf_InsTm; [exact HwfS|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + apply (sub_InsTm Γ S B Hsub G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + eapply ty_app_arg_no_local_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact HnlArg].
  - intros Γ body T HwfT HisAbs Hbody IHbody c G' HIns. simpl.
    apply T_LtLam.
    + eapply ty_wf_InsTm; [exact HwfT|]. apply InsTm_lt. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + rewrite is_abs_shift_tm. exact HisAbs.
    + apply IHbody. apply InsTmAt_lt. exact HIns.
  - intros Γ t T l Ht IHt Hwfl c G' HIns. simpl.
    eapply T_LtApp.
    + apply IHt. exact HIns.
    + eapply lt_wf_InsTm; [exact Hwfl|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
            Hctor Heff Hlts Hwflts Hrho HTs HwfTs Hresult Hshape Hresult_eff Hwfl Hlt Hbounded Hlen Hargs IHargs c G' HIns.
    simpl. rewrite shift_tm_go_eq_map.
    eapply T_Ctor with
      (rho_fields := rho_fields) (result_ty_schema := result_ty_schema)
      (result_tag := result_tag); eauto.
    + rewrite (InsTm_lookup_ctor Γ G' (InsTmAt_to_InsTm c Γ G' HIns) K). exact Hctor.
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) K). exact Heff.
            + eapply lifetimes_wf_InsTm; [exact Hwflts|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
            + eapply types_wf_InsTm; [exact HwfTs|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) result_tag). exact Hresult_eff.
            + eapply lt_wf_InsTm; [exact Hwfl|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + apply (lt_sub_InsTm Γ (lt_of_ty_list rho_fields) (lt_of_ty result_ty) Hlt
           G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + eapply Forall_impl; [|exact Hbounded].
      intros l0 Hsub.
      apply (lt_sub_InsTm Γ l0 l Hsub G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + rewrite !List.length_map. exact Hlen.
    + apply (Forall2_typing_InsTmAt Γ vs rho_fields IHargs c G' HIns).
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l
           Γyes yes_body eta elim_result no_body
           Hneq Hctor Heff Hlts Hrho HTs HwfTs Hscrut_result Hscrut_shape
           Hresult_eff Hresult_ne HwfDelta Hresult_l Hscrut IHscrut Harity HΓyes Hyes IHyes Helim Hno IHno c G' HIns.
    simpl. subst Γyes.
    eapply T_Match with
      (n_lt := n_lt) (n_ty := n_ty) (sigma_fields := sigma_fields)
      (result_ty_schema := result_ty_schema) (lts := lts) (rho_fields := rho_fields)
      (scrut_result_ty := scrut_result_ty)
      (result_tag := result_tag) (result_l := result_l)
      (Γ' := push_lt_vars n_lt Delta G') (eta := eta).
    + exact Hneq.
    + rewrite (InsTm_lookup_ctor Γ G' (InsTmAt_to_InsTm c Γ G' HIns) K). exact Hctor.
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) K). exact Heff.
    + exact Hlts.
    + exact Hrho.
    + exact HTs.
    + eapply types_wf_InsTm; [exact HwfTs|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + exact Hscrut_result.
    + exact Hscrut_shape.
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) result_tag). exact Hresult_eff.
    + exact Hresult_ne.
    + eapply lt_wf_InsTm; [exact HwfDelta|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + apply (lt_sub_InsTm Γ result_l Delta Hresult_l
           G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + apply IHscrut. exact HIns.
    + exact Harity.
    + reflexivity.
    + apply IHyes.
      rewrite Harity.
      apply InsTmAt_fold_bind_tm.
      apply InsTmAt_push_lt_vars. exact HIns.
    + exact Helim.
    + apply IHno. exact HIns.
  - intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff HTs HwfTs HwfTR Hsig Hret Hop IHop c G' HIns.
    simpl.
    eapply T_Cap with (n_α := n_α) (n_β := n_β) (sig := sig) (ret := ret)
      (sig_β := sig_β) (ret_β := ret_β).
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) E_tag). exact Heff.
    + exact HTs.
    + eapply types_wf_InsTm; [exact HwfTs|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTR|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + exact Hsig.
    + exact Hret.
    + apply IHop.
      replace (c + 2) with (S (S c)) by lia.
      apply InsTmAt_tm. apply InsTmAt_tm. apply InsTmAt_push_ty_vars. exact HIns.
  - intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
           Heff HTs HwfTs HwfTB HwfTR Hnolocal Hsub Hsig Hret Hop IHop Hbody IHbody c G' HIns.
    simpl.
    eapply T_Handle with (n_α := n_α) (n_β := n_β) (sig := sig) (ret := ret)
      (T_B := T_B) (sig_β := sig_β) (ret_β := ret_β).
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) E_tag). exact Heff.
    + exact HTs.
    + eapply types_wf_InsTm; [exact HwfTs|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTB|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTR|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply no_local_ty_G_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact Hnolocal].
    + apply (sub_InsTm Γ T_B T_R Hsub G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + exact Hsig.
    + exact Hret.
    + apply IHop.
      replace (c + 2) with (S (S c)) by lia.
      apply InsTmAt_tm. apply InsTmAt_tm. apply InsTmAt_push_ty_vars. exact HIns.
    + apply IHbody. apply InsTmAt_tm. exact HIns.
  - intros Γ recv arg E_tag Delta Ts Ss n_α n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff HTs HSs HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg c G' HIns.
    simpl.
    eapply T_Perform with (n_α := n_α) (n_β := n_β) (sig := sig) (ret := ret)
      (sig_inst := sig_inst) (ret_inst := ret_inst).
    + apply IHrecv. exact HIns.
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) E_tag). exact Heff.
    + exact HTs.
    + exact HSs.
    + eapply types_wf_InsTm; [exact HwfSs|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply forallb_no_local_ty_G_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact HnoSs].
    + exact Hsig.
    + eapply no_local_ty_G_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact HnoSig].
    + exact Hret.
    + eapply ty_wf_InsTm; [exact HwfRet|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + apply IHarg. exact HIns.
  - intros Γ m T_B T_R t HwfTB HwfTR Hnolocal Hsub Ht IHt c G' HIns. simpl.
    apply T_HandlerM.
    + eapply ty_wf_InsTm; [exact HwfTB|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTR|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply no_local_ty_G_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact Hnolocal].
    + apply (sub_InsTm Γ T_B T_R Hsub G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + apply IHt. exact HIns.
  - intros Γ m b A T_B T_R HwfA HwfTB HwfTR Hnolocal Hsub Hb IHb c G' HIns. simpl.
    apply T_Resume.
    + eapply ty_wf_InsTm; [exact HwfA|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTB|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTR|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply no_local_ty_G_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact Hnolocal].
    + apply (sub_InsTm Γ T_B T_R Hsub G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + apply IHb. apply InsTmAt_tm. exact HIns.
Qed.

Lemma typing_weaken_tm_shift : forall Γ A t T,
  Γ ⊢ₜ t : T -> (bind_tm A :: Γ) ⊢ₜ shift_tm 1 0 t : T.
Proof.
  intros Γ A t T H. eapply typing_InsTmAt; [exact H|apply InsTmAt_here].
Qed.

Lemma typing_weaken_tm_shift_many : forall Γ rhos t T,
  Γ ⊢ₜ t : T ->
  (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ rhos)
    ⊢ₜ shift_tm (List.length rhos) 0 t : T.
Proof.
  intros Γ rhos. induction rhos as [|rho rhos IH]; intros t T Hty; simpl.
  - rewrite shift_tm_zero. exact Hty.
  - replace (shift_tm (S (List.length rhos)) 0 t)
      with (shift_tm 1 0 (shift_tm (List.length rhos) 0 t)).
    + apply typing_weaken_tm_shift. apply IH. exact Hty.
    + rewrite shift_tm_fuse.
      replace (1 + List.length rhos) with (S (List.length rhos)) by lia.
      reflexivity.
Qed.

Lemma value_shift_tm : forall v,
  value v -> forall amount cutoff, value (shift_tm amount cutoff v).
Proof.
  fix IH 2.
  intros v Hv amount cutoff. destruct Hv; simpl.
  - constructor.
  - constructor.
  - constructor.
  - rewrite shift_tm_go_eq_map. constructor.
    induction H as [|v vs Hv Hvs IHvs]; simpl.
    + constructor.
    + constructor; [apply (IH v Hv amount cutoff)|exact IHvs].
  - constructor.
  - constructor.
Qed.

Lemma value_shift_ty_in_tm : forall v,
  value v -> forall amount cutoff, value (shift_ty_in_tm amount cutoff v).
Proof.
  fix IH 2.
  intros v Hv amount cutoff. destruct Hv; simpl.
  - constructor.
  - constructor.
  - constructor.
  - rewrite shift_ty_in_tm_go_eq_map. constructor.
    induction H as [|v vs Hv Hvs IHvs]; simpl.
    + constructor.
    + constructor; [apply (IH v Hv amount cutoff)|exact IHvs].
  - constructor.
  - constructor.
Qed.

Lemma value_shift_lt_in_tm : forall v,
  value v -> forall amount cutoff, value (shift_lt_in_tm amount cutoff v).
Proof.
  fix IH 2.
  intros v Hv amount cutoff. destruct Hv; simpl.
  - constructor.
  - constructor.
  - constructor.
  - rewrite shift_lt_in_tm_go_eq_map. constructor.
    induction H as [|v vs Hv Hvs IHvs]; simpl.
    + constructor.
    + constructor; [apply (IH v Hv amount cutoff)|exact IHvs].
  - constructor.
  - constructor.
Qed.

Lemma subst_tm_go_eq_map : forall var replacement ts,
  (fix go ts := match ts with [] => [] | u :: rest => subst_tm var replacement u :: go rest end) ts =
  List.map (subst_tm var replacement) ts.
Proof.
  intros var replacement ts. induction ts as [|t ts IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma has_rt_cap_subst_tm_false : forall t var replacement,
  has_rt_cap t = false ->
  has_rt_cap replacement = false ->
  has_rt_cap (subst_tm var replacement t) = false.
Proof.
  apply (term_list_ind
    (fun t => forall var replacement,
      has_rt_cap t = false ->
      has_rt_cap replacement = false ->
      has_rt_cap (subst_tm var replacement t) = false)
    (fun ts => forall var replacement,
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts = false ->
      has_rt_cap replacement = false ->
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end)
        (List.map (subst_tm var replacement) ts) = false)).
  - intros x var replacement Hcap Hrepl. simpl.
    destruct (Nat.eqb x var); [exact Hrepl|]. destruct (Nat.ltb var x); reflexivity.
  - intros t1 t2 IH1 IH2 var replacement Hcap Hrepl. simpl in *.
    apply Bool.orb_false_iff in Hcap as [H1 H2].
    rewrite (IH1 var replacement H1 Hrepl), (IH2 var replacement H2 Hrepl). reflexivity.
  - intros body T IH var replacement Hcap Hrepl. simpl in *.
    apply IH; [exact Hcap|]. rewrite has_rt_cap_shift_tm. exact Hrepl.
  - intros t T IH var replacement Hcap Hrepl. simpl in *. apply IH; assumption.
  - intros bound body IH var replacement Hcap Hrepl. simpl in *.
    apply IH; [exact Hcap|]. rewrite has_rt_cap_shift_ty_in_tm. exact Hrepl.
  - intros t l IH var replacement Hcap Hrepl. simpl in *. apply IH; assumption.
  - intros body IH var replacement Hcap Hrepl. simpl in *.
    apply IH; [exact Hcap|]. rewrite has_rt_cap_shift_lt_in_tm. exact Hrepl.
  - intros K l lts Ts ts IH var replacement Hcap Hrepl. simpl in *.
    rewrite subst_tm_go_eq_map. apply IH; assumption.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn var replacement Hcap Hrepl. simpl in *.
    apply Bool.orb_false_iff in Hcap as [Hs Hrest].
    apply Bool.orb_false_iff in Hrest as [Hy Hn].
    rewrite (IHs var replacement Hs Hrepl).
    rewrite (IHy (var + arity) (shift_tm arity 0 (shift_lt_in_tm n_lt 0 replacement)) Hy).
    2:{ rewrite has_rt_cap_shift_tm, has_rt_cap_shift_lt_in_tm. exact Hrepl. }
    rewrite (IHn var replacement Hn Hrepl). reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb var replacement Hcap Hrepl. simpl in *.
    apply Bool.orb_false_iff in Hcap as [Hop Hbody].
    rewrite (IHop (var + 2) (shift_tm 2 0 replacement) Hop).
    2:{ rewrite has_rt_cap_shift_tm. exact Hrepl. }
    rewrite (IHb (S var) (shift_tm 1 0 replacement) Hbody).
    2:{ rewrite has_rt_cap_shift_tm. exact Hrepl. }
    reflexivity.
  - intros t Ss arg IHt IHa var replacement Hcap Hrepl. simpl in *.
    apply Bool.orb_false_iff in Hcap as [Ht Ha].
    rewrite (IHt var replacement Ht Hrepl), (IHa var replacement Ha Hrepl). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop var replacement Hcap Hrepl. discriminate.
  - intros m T_B T_R t IH var replacement Hcap Hrepl. discriminate.
  - intros m T_B T_R b IH var replacement Hcap Hrepl. discriminate.
  - intros var replacement Hcap Hrepl. reflexivity.
  - intros t ts IHt IHts var replacement Hcap Hrepl. simpl in *.
    apply Bool.orb_false_iff in Hcap as [Ht Hts].
    rewrite (IHt var replacement Ht Hrepl), (IHts var replacement Hts Hrepl). reflexivity.
Qed.

Lemma has_rt_cap_subst_tm_source_true : forall t var replacement,
  has_rt_cap t = true -> has_rt_cap (subst_tm var replacement t) = true.
Proof.
  apply (term_list_ind
    (fun t => forall var replacement,
      has_rt_cap t = true -> has_rt_cap (subst_tm var replacement t) = true)
    (fun ts => forall var replacement,
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts = true ->
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end)
        (List.map (subst_tm var replacement) ts) = true)).
  - intros x var replacement Hcap. discriminate.
  - intros t1 t2 IH1 IH2 var replacement Hcap. simpl in *.
    apply Bool.orb_true_iff in Hcap as [Hcap|Hcap].
    + rewrite (IH1 var replacement Hcap). reflexivity.
    + rewrite (IH2 var replacement Hcap). destruct (has_rt_cap (subst_tm var replacement t1)); reflexivity.
  - intros body T IH var replacement Hcap. simpl in *. apply IH. exact Hcap.
  - intros t T IH var replacement Hcap. simpl in *. apply IH. exact Hcap.
  - intros bound body IH var replacement Hcap. simpl in *. apply IH. exact Hcap.
  - intros t l IH var replacement Hcap. simpl in *. apply IH. exact Hcap.
  - intros body IH var replacement Hcap. simpl in *. apply IH. exact Hcap.
  - intros K l lts Ts ts IH var replacement Hcap. simpl in *.
    rewrite subst_tm_go_eq_map. apply IH. exact Hcap.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn var replacement Hcap. simpl in *.
    apply Bool.orb_true_iff in Hcap as [Hs|Hrest].
    + rewrite (IHs var replacement Hs). reflexivity.
    + apply Bool.orb_true_iff in Hrest as [Hy|Hn].
      * rewrite (IHy (var + arity) (shift_tm arity 0 (shift_lt_in_tm n_lt 0 replacement)) Hy).
        destruct (has_rt_cap (subst_tm var replacement scrut)); reflexivity.
      * rewrite (IHn var replacement Hn).
        destruct (has_rt_cap (subst_tm var replacement scrut));
          destruct (has_rt_cap (subst_tm (var + arity)
            (shift_tm arity 0 (shift_lt_in_tm n_lt 0 replacement)) yes_body)); reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb var replacement Hcap. simpl in *.
    apply Bool.orb_true_iff in Hcap as [Hop|Hbody].
    + rewrite (IHop (var + 2) (shift_tm 2 0 replacement) Hop). reflexivity.
    + rewrite (IHb (S var) (shift_tm 1 0 replacement) Hbody).
      destruct (has_rt_cap (subst_tm (var + 2) (shift_tm 2 0 replacement) op_body)); reflexivity.
  - intros t Ss arg IHt IHa var replacement Hcap. simpl in *.
    apply Bool.orb_true_iff in Hcap as [Ht|Ha].
    + rewrite (IHt var replacement Ht). reflexivity.
    + rewrite (IHa var replacement Ha). destruct (has_rt_cap (subst_tm var replacement t)); reflexivity.
  - intros E m n_beta Ts T_R op_body IHop var replacement Hcap. reflexivity.
  - intros m T_B T_R t IH var replacement Hcap. reflexivity.
  - intros m T_B T_R b IH var replacement Hcap. reflexivity.
  - intros var replacement Hcap. discriminate.
  - intros t ts IHt IHts var replacement Hcap. simpl in *.
    apply Bool.orb_true_iff in Hcap as [Ht|Hts].
    + rewrite (IHt var replacement Ht). reflexivity.
    + rewrite (IHts var replacement Hts). destruct (has_rt_cap (subst_tm var replacement t)); reflexivity.
Qed.

Lemma has_rt_cap_subst_tm_intro : forall t cutoff n v,
  has_rt_cap t = false ->
  has_rt_cap (subst_tm (cutoff + n) (shift_tm cutoff 0 v) t) = true ->
  has_rt_cap v = true /\ In n (free_tm_vars cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall cutoff n v,
      has_rt_cap t = false ->
      has_rt_cap (subst_tm (cutoff + n) (shift_tm cutoff 0 v) t) = true ->
      has_rt_cap v = true /\ In n (free_tm_vars cutoff t))
    (fun ts => forall cutoff n v,
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts = false ->
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end)
        (List.map (subst_tm (cutoff + n) (shift_tm cutoff 0 v)) ts) = true ->
      has_rt_cap v = true /\ In n (List.concat (List.map (free_tm_vars cutoff) ts)))).
  - intros x cutoff n v _ Hsubst. simpl in *.
    destruct (Nat.eqb x (cutoff + n)) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst x. rewrite has_rt_cap_shift_tm in Hsubst.
      split; [exact Hsubst|].
      destruct (Nat.ltb (cutoff + n) cutoff) eqn:Hlt.
      * apply Nat.ltb_lt in Hlt. lia.
      * simpl. left. lia.
    + destruct (Nat.ltb (cutoff + n) x); discriminate Hsubst.
  - intros t1 t2 IH1 IH2 cutoff n v Hcap Hsubst. simpl in *.
    apply Bool.orb_false_iff in Hcap as [Hcap1 Hcap2].
    apply Bool.orb_true_iff in Hsubst as [Hsubst1|Hsubst2].
    + destruct (IH1 cutoff n v Hcap1 Hsubst1) as [Hv Hin]. split; [exact Hv|].
      apply in_or_app. left. exact Hin.
    + destruct (IH2 cutoff n v Hcap2 Hsubst2) as [Hv Hin]. split; [exact Hv|].
      apply in_or_app. right. exact Hin.
  - intros body T IH cutoff n v Hcap Hsubst. simpl in *.
    replace (S (cutoff + n)) with (S cutoff + n) in Hsubst by lia.
    replace (shift_tm 1 0 (shift_tm cutoff 0 v)) with (shift_tm (S cutoff) 0 v) in Hsubst.
    2:{ rewrite shift_tm_fuse. replace (1 + cutoff) with (S cutoff) by lia. reflexivity. }
    apply IH; assumption.
  - intros t T IH cutoff n v Hcap Hsubst. simpl in *. apply IH; assumption.
  - intros bound body IH cutoff n v Hcap Hsubst. simpl in *.
    replace (shift_ty_in_tm 1 0 (shift_tm cutoff 0 v))
      with (shift_tm cutoff 0 (shift_ty_in_tm 1 0 v)) in Hsubst.
    2:{ rewrite shift_tm_shift_ty_in_tm_commute. reflexivity. }
    destruct (IH cutoff n (shift_ty_in_tm 1 0 v) Hcap Hsubst) as [Hv Hin].
    split; [rewrite has_rt_cap_shift_ty_in_tm in Hv; exact Hv|exact Hin].
  - intros t l IH cutoff n v Hcap Hsubst. simpl in *. apply IH; assumption.
  - intros body IH cutoff n v Hcap Hsubst. simpl in *.
    replace (shift_lt_in_tm 1 0 (shift_tm cutoff 0 v))
      with (shift_tm cutoff 0 (shift_lt_in_tm 1 0 v)) in Hsubst.
    2:{ rewrite shift_tm_shift_lt_in_tm_commute. reflexivity. }
    destruct (IH cutoff n (shift_lt_in_tm 1 0 v) Hcap Hsubst) as [Hv Hin].
    split; [rewrite has_rt_cap_shift_lt_in_tm in Hv; exact Hv|exact Hin].
  - intros K l lts Ts ts IH cutoff n v Hcap Hsubst. simpl in *.
    rewrite subst_tm_go_eq_map in Hsubst. rewrite free_tm_vars_go_eq_concat.
    apply IH; assumption.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn cutoff n v Hcap Hsubst. simpl in *.
    apply Bool.orb_false_iff in Hcap as [HcapS HcapYN].
    apply Bool.orb_false_iff in HcapYN as [HcapY HcapN].
    apply Bool.orb_true_iff in Hsubst as [HsubstS|HsubstYN].
    + destruct (IHs cutoff n v HcapS HsubstS) as [Hv Hin]. split; [exact Hv|].
      repeat rewrite in_app_iff. left. exact Hin.
    + apply Bool.orb_true_iff in HsubstYN as [HsubstY|HsubstN].
      * replace (cutoff + n + arity) with (cutoff + arity + n) in HsubstY by lia.
        replace (shift_tm arity 0 (shift_lt_in_tm n_lt 0 (shift_tm cutoff 0 v)))
          with (shift_tm (cutoff + arity) 0 (shift_lt_in_tm n_lt 0 v)) in HsubstY.
        2:{ rewrite <- shift_tm_shift_lt_in_tm_commute.
            rewrite shift_tm_fuse. replace (arity + cutoff) with (cutoff + arity) by lia. reflexivity. }
        destruct (IHy (cutoff + arity) n (shift_lt_in_tm n_lt 0 v) HcapY HsubstY) as [Hv Hin].
        split; [rewrite has_rt_cap_shift_lt_in_tm in Hv; exact Hv|].
        repeat rewrite in_app_iff. right. left. exact Hin.
      * destruct (IHn cutoff n v HcapN HsubstN) as [Hv Hin]. split; [exact Hv|].
        repeat rewrite in_app_iff. right. right. exact Hin.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff n v Hcap Hsubst. simpl in *.
    apply Bool.orb_false_iff in Hcap as [HcapOp HcapBody].
    apply Bool.orb_true_iff in Hsubst as [HsubstOp|HsubstBody].
    + replace (cutoff + n + 2) with (cutoff + 2 + n) in HsubstOp by lia.
      replace (shift_tm 2 0 (shift_tm cutoff 0 v)) with (shift_tm (cutoff + 2) 0 v) in HsubstOp.
      2:{ rewrite shift_tm_fuse. replace (2 + cutoff) with (cutoff + 2) by lia. reflexivity. }
      destruct (IHop (cutoff + 2) n v HcapOp HsubstOp) as [Hv Hin]. split; [exact Hv|].
      apply in_or_app. left. exact Hin.
    + replace (S (cutoff + n)) with (S cutoff + n) in HsubstBody by lia.
      replace (shift_tm 1 0 (shift_tm cutoff 0 v)) with (shift_tm (S cutoff) 0 v) in HsubstBody.
      2:{ rewrite shift_tm_fuse. replace (1 + cutoff) with (S cutoff) by lia. reflexivity. }
      destruct (IHb (S cutoff) n v HcapBody HsubstBody) as [Hv Hin]. split; [exact Hv|].
      apply in_or_app. right. exact Hin.
  - intros t Ss arg IHt IHa cutoff n v Hcap Hsubst. simpl in *.
    apply Bool.orb_false_iff in Hcap as [HcapT HcapA].
    apply Bool.orb_true_iff in Hsubst as [HsubstT|HsubstA].
    + destruct (IHt cutoff n v HcapT HsubstT) as [Hv Hin]. split; [exact Hv|].
      apply in_or_app. left. exact Hin.
    + destruct (IHa cutoff n v HcapA HsubstA) as [Hv Hin]. split; [exact Hv|].
      apply in_or_app. right. exact Hin.
  - intros E m n_beta Ts T_R op_body IHop cutoff n v Hcap. simpl in Hcap. discriminate Hcap.
  - intros m T_B T_R t IH cutoff n v Hcap. simpl in Hcap. discriminate Hcap.
  - intros m T_B T_R b IH cutoff n v Hcap. simpl in Hcap. discriminate Hcap.
  - intros cutoff n v _ Hsubst. simpl in Hsubst. discriminate Hsubst.
  - intros t ts IHt IHts cutoff n v Hcap Hsubst. simpl in *.
    apply Bool.orb_false_iff in Hcap as [HcapT HcapTs].
    apply Bool.orb_true_iff in Hsubst as [HsubstT|HsubstTs].
    + destruct (IHt cutoff n v HcapT HsubstT) as [Hv Hin]. split; [exact Hv|].
      rewrite in_app_iff. left. exact Hin.
    + destruct (IHts cutoff n v HcapTs HsubstTs) as [Hv Hin]. split; [exact Hv|].
      rewrite in_app_iff. right. exact Hin.
Qed.

Fixpoint subst_tm_fv (n : nat) (xs : list nat) : list nat :=
  match xs with
  | [] => []
  | x :: rest =>
      if Nat.eqb x n then subst_tm_fv n rest
      else (if Nat.ltb n x then pred x else x) :: subst_tm_fv n rest
  end.

Lemma subst_tm_fv_app : forall n xs ys,
  subst_tm_fv n (xs ++ ys) = subst_tm_fv n xs ++ subst_tm_fv n ys.
Proof.
  induction xs as [|x xs IH]; intros ys; simpl; [reflexivity|].
  destruct (Nat.eqb x n); simpl; rewrite IH; reflexivity.
Qed.

Lemma free_tm_vars_closed_shift_tm_any : forall a v,
  free_tm_vars 0 v = [] -> free_tm_vars 0 (shift_tm a 0 v) = [].
Proof.
  induction a as [|a IH]; intros v Hfree.
  - rewrite shift_tm_zero. exact Hfree.
  - replace (S a) with (1 + a) by lia.
    rewrite <- shift_tm_fuse.
    pose proof (free_tm_vars_shift_tm_1 (shift_tm a 0 v) 0 0) as Hshift.
    cbn [Nat.add] in Hshift. rewrite (IH v Hfree) in Hshift. exact Hshift.
Qed.

Lemma free_tm_vars_shift_tm_closed_at : forall v cutoff,
  free_tm_vars 0 v = [] -> free_tm_vars cutoff (shift_tm cutoff 0 v) = [].
Proof.
  intros v cutoff Hfree.
  apply free_tm_vars_closed_cutoff.
  apply free_tm_vars_closed_shift_tm_any. exact Hfree.
Qed.

Lemma free_tm_vars_subst_tm_closed : forall t cutoff n v,
  free_tm_vars 0 v = [] ->
  free_tm_vars cutoff (subst_tm (cutoff + n) (shift_tm cutoff 0 v) t) =
  subst_tm_fv n (free_tm_vars cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall cutoff n v,
      free_tm_vars 0 v = [] ->
      free_tm_vars cutoff (subst_tm (cutoff + n) (shift_tm cutoff 0 v) t) =
      subst_tm_fv n (free_tm_vars cutoff t))
    (fun ts => forall cutoff n v,
      free_tm_vars 0 v = [] ->
      List.concat (List.map (free_tm_vars cutoff)
        (List.map (subst_tm (cutoff + n) (shift_tm cutoff 0 v)) ts)) =
      subst_tm_fv n (List.concat (List.map (free_tm_vars cutoff) ts)))).
  - intros x cutoff n v Hfree. simpl.
    destruct (Nat.ltb x cutoff) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      destruct (Nat.eqb x (cutoff + n)) eqn:Heq; [apply Nat.eqb_eq in Heq; lia|].
      destruct (Nat.ltb (cutoff + n) x) eqn:Hlt2; [apply Nat.ltb_lt in Hlt2; lia|].
      cbn [free_tm_vars subst_tm_fv]. rewrite (proj2 (Nat.ltb_lt x cutoff)) by lia. reflexivity.
    + apply Nat.ltb_ge in Hlt.
      destruct (Nat.eqb x (cutoff + n)) eqn:Heq.
      * apply Nat.eqb_eq in Heq. subst x.
        cbn [free_tm_vars subst_tm_fv]. replace (cutoff + n - cutoff) with n by lia.
        rewrite Nat.eqb_refl.
        apply free_tm_vars_shift_tm_closed_at. exact Hfree.
      * apply Nat.eqb_neq in Heq.
        destruct (Nat.ltb (cutoff + n) x) eqn:Hgt.
        -- apply Nat.ltb_lt in Hgt.
           assert (HltPred : Nat.ltb (pred x) cutoff = false) by (apply Nat.ltb_ge; lia).
            cbn [free_tm_vars subst_tm_fv]. rewrite HltPred. simpl.
           assert (Hneq : x - cutoff <> n) by lia.
           rewrite (proj2 (Nat.eqb_neq (x - cutoff) n)) by exact Hneq.
           rewrite (proj2 (Nat.ltb_lt n (x - cutoff))) by lia.
           f_equal. lia.
        -- apply Nat.ltb_ge in Hgt.
            cbn [free_tm_vars subst_tm_fv]. rewrite (proj2 (Nat.ltb_ge x cutoff)) by lia. simpl.
           assert (Hneq : x - cutoff <> n) by lia.
           rewrite (proj2 (Nat.eqb_neq (x - cutoff) n)) by exact Hneq.
           rewrite (proj2 (Nat.ltb_ge n (x - cutoff))) by lia.
           reflexivity.
  - intros t1 t2 IH1 IH2 cutoff n v Hfree. simpl.
    rewrite IH1 by exact Hfree. rewrite IH2 by exact Hfree.
    rewrite subst_tm_fv_app. reflexivity.
  - intros body T IH cutoff n v Hfree. simpl.
    replace (S (cutoff + n)) with (S cutoff + n) by lia.
    replace (shift_tm 1 0 (shift_tm cutoff 0 v)) with (shift_tm (S cutoff) 0 v).
    2:{ rewrite shift_tm_fuse. replace (1 + cutoff) with (S cutoff) by lia. reflexivity. }
    apply IH. exact Hfree.
  - intros t T IH cutoff n v Hfree. simpl. apply IH. exact Hfree.
  - intros bound body IH cutoff n v Hfree. simpl.
    replace (shift_ty_in_tm 1 0 (shift_tm cutoff 0 v))
      with (shift_tm cutoff 0 (shift_ty_in_tm 1 0 v)).
    2:{ rewrite shift_tm_shift_ty_in_tm_commute. reflexivity. }
    apply IH. rewrite free_tm_vars_shift_ty_in_tm. exact Hfree.
  - intros t l IH cutoff n v Hfree. simpl. apply IH. exact Hfree.
  - intros body IH cutoff n v Hfree. simpl.
    replace (shift_lt_in_tm 1 0 (shift_tm cutoff 0 v))
      with (shift_tm cutoff 0 (shift_lt_in_tm 1 0 v)).
    2:{ rewrite shift_tm_shift_lt_in_tm_commute. reflexivity. }
    apply IH. rewrite free_tm_vars_shift_lt_in_tm. exact Hfree.
  - intros K l lts Ts ts IH cutoff n v Hfree. simpl.
    rewrite subst_tm_go_eq_map. rewrite !free_tm_vars_go_eq_concat.
    apply IH. exact Hfree.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn cutoff n v Hfree. simpl.
    rewrite IHs by exact Hfree.
    replace (cutoff + n + arity) with (cutoff + arity + n) by lia.
    replace (shift_tm arity 0 (shift_lt_in_tm n_lt 0 (shift_tm cutoff 0 v)))
      with (shift_tm (cutoff + arity) 0 (shift_lt_in_tm n_lt 0 v)).
    2:{ rewrite <- shift_tm_shift_lt_in_tm_commute.
        rewrite shift_tm_fuse. replace (arity + cutoff) with (cutoff + arity) by lia. reflexivity. }
    rewrite IHy.
    2:{ rewrite (free_tm_vars_shift_lt_in_tm_any v 0 n_lt 0). exact Hfree. }
    rewrite IHn by exact Hfree.
    rewrite !subst_tm_fv_app. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff n v Hfree. simpl.
    replace (cutoff + n + 2) with (cutoff + 2 + n) by lia.
    replace (shift_tm 2 0 (shift_tm cutoff 0 v)) with (shift_tm (cutoff + 2) 0 v).
    2:{ rewrite shift_tm_fuse. replace (2 + cutoff) with (cutoff + 2) by lia. reflexivity. }
    rewrite IHop.
    2:{ exact Hfree. }
    replace (S (cutoff + n)) with (S cutoff + n) by lia.
    replace (shift_tm 1 0 (shift_tm cutoff 0 v)) with (shift_tm (S cutoff) 0 v).
    2:{ rewrite shift_tm_fuse. replace (1 + cutoff) with (S cutoff) by lia. reflexivity. }
    rewrite IHb by exact Hfree.
    rewrite subst_tm_fv_app. reflexivity.
  - intros t Ss arg IHt IHa cutoff n v Hfree. simpl.
    rewrite IHt by exact Hfree. rewrite IHa by exact Hfree.
    rewrite subst_tm_fv_app. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff n v Hfree. simpl.
    replace (cutoff + n + 2) with (cutoff + 2 + n) by lia.
    replace (shift_tm 2 0 (shift_tm cutoff 0 v)) with (shift_tm (cutoff + 2) 0 v).
    2:{ rewrite shift_tm_fuse. replace (2 + cutoff) with (cutoff + 2) by lia. reflexivity. }
    apply IHop. exact Hfree.
  - intros m T_B T_R t IH cutoff n v Hfree. simpl. apply IH. exact Hfree.
  - intros m T_B T_R b IH cutoff n v Hfree. simpl.
    replace (S (cutoff + n)) with (S cutoff + n) by lia.
    replace (shift_tm 1 0 (shift_tm cutoff 0 v)) with (shift_tm (S cutoff) 0 v).
    2:{ rewrite shift_tm_fuse. replace (1 + cutoff) with (S cutoff) by lia. reflexivity. }
    apply IH. exact Hfree.
  - intros cutoff n v Hfree. reflexivity.
  - intros t ts IHt IHts cutoff n v Hfree. simpl.
    rewrite IHt by exact Hfree. rewrite IHts by exact Hfree.
    rewrite subst_tm_fv_app. reflexivity.
Qed.

Lemma subst_tm_var_eq : forall var replacement y,
  subst_tm var replacement (term_var y) =
    if Nat.eqb y var then replacement else if Nat.ltb var y then term_var (pred y) else term_var y.
Proof. reflexivity. Qed.

Lemma subst_tm_shift_cancel : forall t c replacement,
  subst_tm c replacement (shift_tm 1 c t) = t.
Proof.
  enough (H : forall t, forall c replacement,
    subst_tm c replacement (shift_tm 1 c t) = t).
  { intros; apply H. }
  apply (term_list_ind
    (fun t => forall c replacement, subst_tm c replacement (shift_tm 1 c t) = t)
    (fun ts => forall c replacement,
      List.map (subst_tm c replacement) (List.map (shift_tm 1 c) ts) = ts)).
  - intros n c replacement. rewrite shift_tm_var_eq, subst_tm_var_eq.
    destruct (Nat.leb c n) eqn:E.
    + apply Nat.leb_le in E.
      destruct (Nat.eqb_spec (n + 1) c); [lia|].
      destruct (Nat.ltb_spec c (n + 1)); [f_equal; lia|lia].
    + apply Nat.leb_gt in E.
      destruct (Nat.eqb_spec n c); [lia|].
      destruct (Nat.ltb_spec c n); [lia|reflexivity].
  - intros t1 t2 IH1 IH2 c replacement. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH c replacement. simpl. rewrite IH. reflexivity.
  - intros t T IH c replacement. simpl. rewrite IH. reflexivity.
  - intros bound body IH c replacement. simpl. rewrite IH. reflexivity.
  - intros t l IH c replacement. simpl. rewrite IH. reflexivity.
  - intros body IH c replacement. simpl. rewrite IH. reflexivity.
  - intros K l lts Ts ts IH c replacement. simpl.
    rewrite shift_tm_go_eq_map, subst_tm_go_eq_map. rewrite IH. reflexivity.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn c replacement. simpl.
    rewrite IHs.
    replace (c + arity) with (c + arity) by reflexivity.
    rewrite IHy.
    rewrite IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb c replacement. simpl.
    rewrite IHop. rewrite IHb. reflexivity.
  - intros t Ss arg IHt IHa c replacement. simpl. rewrite IHt, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop c replacement. simpl. rewrite IHop. reflexivity.
  - intros m T_B T_R t IH c replacement. simpl. rewrite IH. reflexivity.
  - intros m T_B T_R b IH c replacement. simpl. rewrite IH. reflexivity.
  - intros c replacement. reflexivity.
  - intros t ts IHt IHts c replacement. simpl. rewrite IHt, IHts. reflexivity.
Qed.

(* ============================================================ *)
(* subst_lt_in_ty head-constructor rewrite equations            *)
(* ============================================================ *)
Lemma subst_lt_in_ty_var_eq : forall v R n,
  subst_lt_in_ty v R (type_var n) = type_var n.
Proof. reflexivity. Qed.
Lemma subst_lt_in_ty_fun_eq : forall v R A l B,
  subst_lt_in_ty v R (type_fun A l B)
  = type_fun (subst_lt_in_ty v R A) (subst_lt v R l) (subst_lt_in_ty v R B).
Proof. reflexivity. Qed.
Lemma subst_lt_in_ty_ltall_eq : forall v R A,
  subst_lt_in_ty v R (type_lt_all A)
  = type_lt_all (subst_lt_in_ty (S v) (shift_lt 1 0 R) A).
Proof. reflexivity. Qed.
Lemma subst_lt_in_ty_tyall_eq : forall v R B A,
  subst_lt_in_ty v R (type_ty_all B A)
  = type_ty_all (subst_lt_in_ty v R B) (subst_lt_in_ty v R A).
Proof. reflexivity. Qed.

Lemma subst_lt_var_eq : forall v R y,
  subst_lt v R (lt_var y) =
    if Nat.eqb y v then R else if Nat.ltb v y then lt_var (pred y) else lt_var y.
Proof. reflexivity. Qed.

Lemma subst_lt_var_same : forall v R,
  subst_lt v R (lt_var v) = R.
Proof.
  intros v R. rewrite subst_lt_var_eq, Nat.eqb_refl. reflexivity.
Qed.

(* ============================================================ *)
(* subst_lt / shift_lt : cancel and commute                     *)
(* ============================================================ *)

Lemma subst_lt_shift_cancel : forall l c R,
  subst_lt c R (shift_lt 1 c l) = l.
Proof.
  induction l as [y| | |l1 IH1 l2 IH2]; intros c R.
  - rewrite shift_lt_var_eq. destruct (Nat.leb c y) eqn:E.
    + apply Nat.leb_le in E. simpl subst_lt.
      destruct (Nat.eqb_spec (y+1) c); [lia|].
      destruct (Nat.ltb_spec c (y+1)); [|lia]. f_equal. lia.
    + apply Nat.leb_gt in E. simpl subst_lt.
      destruct (Nat.eqb_spec y c); [lia|].
      destruct (Nat.ltb_spec c y); [lia|]. reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IH1, IH2. reflexivity.
Qed.

Lemma subst_lt_in_ty_shift_cancel : forall T c R,
  subst_lt_in_ty c R (shift_lt_in_ty 1 c T) = T.
Proof.
  intros T. apply (type_list_ind
    (fun T => forall c R, subst_lt_in_ty c R (shift_lt_in_ty 1 c T) = T)
    (fun Ts => forall c R,
       List.map (subst_lt_in_ty c R) (List.map (shift_lt_in_ty 1 c) Ts) = Ts)).
  - intros n c R. reflexivity.
  - intros A l B HA HB c R.
    rewrite shift_lt_in_ty_fun_eq. simpl subst_lt_in_ty.
    rewrite HA, HB, subst_lt_shift_cancel. reflexivity.
  - intros K l Ts HTs c R.
    rewrite shift_lt_in_ty_ctor_eq, subst_lt_in_ty_ctor_eq.
    rewrite subst_lt_shift_cancel. f_equal. apply HTs.
  - intros A HA c R.
    rewrite shift_lt_in_ty_ltall_eq. simpl subst_lt_in_ty. rewrite HA. reflexivity.
  - intros B A HB HA c R.
    rewrite shift_lt_in_ty_tyall_eq. simpl subst_lt_in_ty. rewrite HB, HA. reflexivity.
  - intros c R. reflexivity.
  - intros A Ts HA HTs c R. cbn [List.map]. rewrite HA. f_equal. apply HTs.
Qed.

(* general-cutoff commute: shift below the subst point *)
Lemma shift_lt_subst_lt_comm : forall l n c R,
  c <= n ->
  shift_lt 1 c (subst_lt n R l) = subst_lt (S n) (shift_lt 1 c R) (shift_lt 1 c l).
Proof.
  induction l as [y| | |l1 IH1 l2 IH2]; intros n c R Hcn.
  - rewrite subst_lt_var_eq. rewrite (shift_lt_var_eq 1 c y).
    rewrite subst_lt_var_eq.
    destruct (Nat.eqb_spec y n) as [Hy|Hy].
    + subst y. destruct (Nat.leb c n) eqn:Ecn.
      * destruct (Nat.eqb_spec (n+1) (S n)); [reflexivity|lia].
      * apply Nat.leb_gt in Ecn. lia.
    + destruct (Nat.ltb_spec n y) as [Hlt|Hge].
      * rewrite (shift_lt_var_eq 1 c (pred y)).
        destruct (Nat.leb c y) eqn:E2; destruct (Nat.leb c (pred y)) eqn:E1.
        -- destruct (Nat.eqb_spec (y+1) (S n)); [lia|].
           destruct (Nat.ltb_spec (S n) (y+1)); [|lia]. f_equal. lia.
        -- apply Nat.leb_le in E2. apply Nat.leb_gt in E1. lia.
        -- apply Nat.leb_gt in E2. lia.
        -- apply Nat.leb_gt in E2. lia.
      * rewrite (shift_lt_var_eq 1 c y).
        destruct (Nat.leb c y) eqn:E2.
        -- destruct (Nat.eqb_spec (y+1) (S n)); [lia|].
           destruct (Nat.ltb_spec (S n) (y+1)); [lia|]. reflexivity.
        -- destruct (Nat.eqb_spec y (S n)); [lia|].
           destruct (Nat.ltb_spec (S n) y); [lia|]. reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IH1 by lia. rewrite IH2 by lia. reflexivity.
Qed.

Lemma shift_lt_subst_lt_comm0 : forall l n R,
  shift_lt 1 0 (subst_lt n R l) = subst_lt (S n) (shift_lt 1 0 R) (shift_lt 1 0 l).
Proof. intros l n R. apply shift_lt_subst_lt_comm. lia. Qed.

Lemma shift_lt_in_ty_subst_lt_in_ty_comm : forall T n c R,
  c <= n ->
  shift_lt_in_ty 1 c (subst_lt_in_ty n R T)
  = subst_lt_in_ty (S n) (shift_lt 1 c R) (shift_lt_in_ty 1 c T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall n c R, c <= n ->
       shift_lt_in_ty 1 c (subst_lt_in_ty n R T)
       = subst_lt_in_ty (S n) (shift_lt 1 c R) (shift_lt_in_ty 1 c T))
    (fun Ts => forall n c R, c <= n ->
       List.map (shift_lt_in_ty 1 c) (List.map (subst_lt_in_ty n R) Ts)
       = List.map (subst_lt_in_ty (S n) (shift_lt 1 c R)) (List.map (shift_lt_in_ty 1 c) Ts))).
  - intros m n c R Hcn. reflexivity.
  - intros A l B HA HB n c R Hcn.
    simpl subst_lt_in_ty. rewrite !shift_lt_in_ty_fun_eq. simpl subst_lt_in_ty.
    rewrite HA by lia. rewrite HB by lia. rewrite shift_lt_subst_lt_comm by lia. reflexivity.
  - intros K l Ts HTs n c R Hcn.
    rewrite subst_lt_in_ty_ctor_eq, !shift_lt_in_ty_ctor_eq, subst_lt_in_ty_ctor_eq.
    rewrite shift_lt_subst_lt_comm by lia. f_equal. apply HTs. lia.
  - intros A HA n c R Hcn.
    rewrite subst_lt_in_ty_ltall_eq, !shift_lt_in_ty_ltall_eq, subst_lt_in_ty_ltall_eq.
    f_equal.
    rewrite (HA (S n) (S c) (shift_lt 1 0 R) ltac:(lia)).
    f_equal. symmetry. apply shift_lt_swap. lia.
  - intros B A HB HA n c R Hcn.
    rewrite subst_lt_in_ty_tyall_eq, !shift_lt_in_ty_tyall_eq, subst_lt_in_ty_tyall_eq.
    rewrite HB by lia. rewrite HA by lia. reflexivity.
  - intros n c R Hcn. reflexivity.
  - intros A Ts HA HTs n c R Hcn.
    cbn [List.map]. rewrite HA by lia. f_equal. apply HTs. lia.
Qed.

Lemma shift_lt_in_ty_subst_lt_in_ty_comm0 : forall T n R,
  shift_lt_in_ty 1 0 (subst_lt_in_ty n R T)
  = subst_lt_in_ty (S n) (shift_lt 1 0 R) (shift_lt_in_ty 1 0 T).
Proof. intros T n R. apply shift_lt_in_ty_subst_lt_in_ty_comm. lia. Qed.

Lemma shift_lt_subst_lt_above_comm : forall l n c R,
  shift_lt 1 (n + c) (subst_lt n R l) =
  subst_lt n (shift_lt 1 (n + c) R) (shift_lt 1 (S (n + c)) l).
Proof.
  induction l as [x| | |l1 IH1 l2 IH2]; intros n c R.
  - rewrite subst_lt_var_eq, !shift_lt_var_eq, subst_lt_var_eq.
    destruct (Nat.eqb_spec x n) as [Heq|Hneq].
    + subst x. rewrite (proj2 (Nat.leb_gt (S (n + c)) n)) by lia.
      rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.ltb_spec n x) as [Hgt|Hle].
      * rewrite (shift_lt_var_eq 1 (n + c) (pred x)).
        destruct (Nat.leb (S (n + c)) x) eqn:Hshift.
        -- apply Nat.leb_le in Hshift.
           rewrite (proj2 (Nat.leb_le (n + c) (pred x))) by lia.
           destruct (Nat.eqb_spec (x + 1) n); [lia|].
           destruct (Nat.ltb_spec n (x + 1)); [f_equal; lia|lia].
        -- apply Nat.leb_gt in Hshift.
           rewrite (proj2 (Nat.leb_gt (n + c) (pred x))) by lia.
           destruct (Nat.eqb_spec x n); [lia|].
           destruct (Nat.ltb_spec n x); [reflexivity|lia].
      * destruct (Nat.eqb_spec x n); [lia|].
        destruct (Nat.ltb_spec n x); [lia|].
        destruct x as [|x'].
        -- destruct n as [|n']; [lia|]. reflexivity.
        -- simpl.
           assert (Hcut_pred : (n + c <=? x') = false) by (apply Nat.leb_gt; lia).
           assert (Hcut_x : (n + c <=? S x') = false) by (apply Nat.leb_gt; lia).
           rewrite Hcut_pred, Hcut_x.
           destruct (Nat.eqb_spec (S x') n); [lia|].
           destruct (Nat.ltb_spec n (S x')); [lia|reflexivity].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IH1, IH2. reflexivity.
Qed.

Lemma shift_lt_in_ty_subst_lt_in_ty_above_comm : forall T n c R,
  shift_lt_in_ty 1 (n + c) (subst_lt_in_ty n R T) =
  subst_lt_in_ty n (shift_lt 1 (n + c) R) (shift_lt_in_ty 1 (S (n + c)) T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall n c R,
      shift_lt_in_ty 1 (n + c) (subst_lt_in_ty n R T) =
      subst_lt_in_ty n (shift_lt 1 (n + c) R) (shift_lt_in_ty 1 (S (n + c)) T))
    (fun Ts => forall n c R,
      List.map (shift_lt_in_ty 1 (n + c)) (List.map (subst_lt_in_ty n R) Ts) =
      List.map (subst_lt_in_ty n (shift_lt 1 (n + c) R))
        (List.map (shift_lt_in_ty 1 (S (n + c))) Ts))).
  - reflexivity.
  - intros A l B HA HB n c R. simpl.
    rewrite HA, HB, shift_lt_subst_lt_above_comm. reflexivity.
  - intros K l Ts HTs n c R. rewrite subst_lt_in_ty_ctor_eq, !shift_lt_in_ty_ctor_eq, subst_lt_in_ty_ctor_eq.
    rewrite shift_lt_subst_lt_above_comm. f_equal. apply HTs.
  - intros A HA n c R. rewrite subst_lt_in_ty_ltall_eq, !shift_lt_in_ty_ltall_eq, subst_lt_in_ty_ltall_eq.
    replace (S (n + c)) with (S n + c) by lia.
    rewrite HA.
    replace (S (S n + c)) with (S (S (n + c))) by lia.
    f_equal. rewrite shift_lt_swap_0. reflexivity.
  - intros B A HB HA n c R. rewrite subst_lt_in_ty_tyall_eq, !shift_lt_in_ty_tyall_eq, subst_lt_in_ty_tyall_eq.
    rewrite HB, HA. reflexivity.
  - reflexivity.
  - intros A Ts HA HTs n c R. cbn [List.map]. rewrite HA. f_equal. apply HTs.
Qed.

Lemma shift_lt_in_ty_subst_lt_in_ty_bound0_comm : forall T c R,
  shift_lt_in_ty 1 c (subst_lt_in_ty 0 R T) =
  subst_lt_in_ty 0 (shift_lt 1 c R) (shift_lt_in_ty 1 (S c) T).
Proof.
  intros T c R.
  replace c with (0 + c) by lia.
  apply shift_lt_in_ty_subst_lt_in_ty_above_comm.
Qed.

Lemma subst_lt_shift_many_cancel : forall cutoff Q R,
  subst_lt cutoff Q (shift_lt (S cutoff) 0 R) = shift_lt cutoff 0 R.
Proof.
  intros cutoff Q R. revert cutoff Q.
  induction R as [x| | |l1 IH1 l2 IH2]; intros cutoff Q; simpl.
  - destruct (Nat.leb cutoff (x + S cutoff)) eqn:Hle.
    + destruct (Nat.eqb_spec (x + S cutoff) cutoff); [lia|].
      destruct (Nat.ltb_spec cutoff (x + S cutoff)); [f_equal; lia|lia].
    + apply Nat.leb_gt in Hle. lia.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma subst_lt_subst_lt_comm0_var : forall x cutoff n R Q,
  subst_lt cutoff
    (subst_lt (cutoff + n) (shift_lt cutoff 0 R) (shift_lt cutoff 0 Q))
    (subst_lt (S (cutoff + n)) (shift_lt (S cutoff) 0 R) (lt_var x)) =
  subst_lt (cutoff + n) (shift_lt cutoff 0 R)
    (subst_lt cutoff (shift_lt cutoff 0 Q) (lt_var x)).
Proof.
  intros x cutoff n R Q; simpl.
  repeat match goal with
    | |- context[Nat.eqb ?a ?b] => destruct (Nat.eqb_spec a b); subst; simpl
    | |- context[Nat.ltb ?a ?b] => destruct (Nat.ltb_spec a b); subst; simpl
    end; try lia; try rewrite subst_lt_shift_cancel;
      try rewrite subst_lt_shift_many_cancel; try reflexivity; try (f_equal; lia);
      try (rewrite subst_lt_shift_many_cancel;
           destruct cutoff as [|cutoff']; simpl;
           [rewrite Nat.eqb_refl; reflexivity|
            destruct (Nat.eqb_spec (S cutoff' + n) cutoff'); [lia|];
            rewrite Nat.eqb_refl; reflexivity]);
      try (destruct cutoff as [|cutoff']; simpl;
           [rewrite Nat.eqb_refl; reflexivity|
            destruct (Nat.eqb_spec (S cutoff' + n) cutoff'); [lia|];
            rewrite Nat.eqb_refl; reflexivity]).
  destruct cutoff as [|cutoff'].
  - change (shift_lt 0 0 R =
      subst_lt (0 + n) (shift_lt 0 0 R) (lt_var (0 + n))).
    rewrite subst_lt_var_same. reflexivity.
  - change (shift_lt (S cutoff') 0 R =
      subst_lt (S cutoff' + n) (shift_lt (S cutoff') 0 R)
        (if S cutoff' + n =? cutoff'
         then shift_lt (S cutoff') 0 Q
         else lt_var (S cutoff' + n))).
    destruct (Nat.eqb_spec (S cutoff' + n) cutoff'); [lia|].
    rewrite subst_lt_var_same. reflexivity.
Qed.

Lemma subst_lt_subst_lt_comm0 : forall l cutoff n R Q,
  subst_lt cutoff
    (subst_lt (cutoff + n) (shift_lt cutoff 0 R) (shift_lt cutoff 0 Q))
    (subst_lt (S (cutoff + n)) (shift_lt (S cutoff) 0 R) l) =
  subst_lt (cutoff + n) (shift_lt cutoff 0 R)
    (subst_lt cutoff (shift_lt cutoff 0 Q) l).
Proof.
  induction l as [x| | |l1 IH1 l2 IH2]; intros cutoff n R Q; simpl.
  - apply subst_lt_subst_lt_comm0_var.
  - reflexivity.
  - reflexivity.
  - simpl. rewrite IH1, IH2. reflexivity.
Qed.

Lemma subst_lt_in_ty_subst_lt_in_ty_comm0 : forall T cutoff n R Q,
  subst_lt_in_ty cutoff
    (subst_lt (cutoff + n) (shift_lt cutoff 0 R) (shift_lt cutoff 0 Q))
    (subst_lt_in_ty (S (cutoff + n)) (shift_lt (S cutoff) 0 R) T) =
  subst_lt_in_ty (cutoff + n) (shift_lt cutoff 0 R)
    (subst_lt_in_ty cutoff (shift_lt cutoff 0 Q) T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall cutoff n R Q,
      subst_lt_in_ty cutoff
        (subst_lt (cutoff + n) (shift_lt cutoff 0 R) (shift_lt cutoff 0 Q))
        (subst_lt_in_ty (S (cutoff + n)) (shift_lt (S cutoff) 0 R) T) =
      subst_lt_in_ty (cutoff + n) (shift_lt cutoff 0 R)
        (subst_lt_in_ty cutoff (shift_lt cutoff 0 Q) T))
    (fun Ts => forall cutoff n R Q,
      List.map (subst_lt_in_ty cutoff
        (subst_lt (cutoff + n) (shift_lt cutoff 0 R) (shift_lt cutoff 0 Q)))
        (List.map (subst_lt_in_ty (S (cutoff + n)) (shift_lt (S cutoff) 0 R)) Ts) =
      List.map (subst_lt_in_ty (cutoff + n) (shift_lt cutoff 0 R))
        (List.map (subst_lt_in_ty cutoff (shift_lt cutoff 0 Q)) Ts))).
  - reflexivity.
  - intros A l B HA HB cutoff n R Q. simpl.
    rewrite HA, HB, subst_lt_subst_lt_comm0. reflexivity.
  - intros K l Ts HTs cutoff n R Q. rewrite subst_lt_in_ty_ctor_eq. simpl.
    rewrite subst_lt_subst_lt_comm0. f_equal. apply HTs.
  - intros A HA cutoff n R Q. simpl.
    rewrite shift_lt_subst_lt_comm0.
    rewrite !shift_lt_fuse.
    replace (1 + S cutoff) with (S (S cutoff)) by lia.
    replace (1 + cutoff) with (S cutoff) by lia.
    replace (S (cutoff + n)) with (S cutoff + n) by lia.
    replace (S (S (cutoff + n))) with (S (S cutoff + n)) by lia.
    rewrite HA.
    reflexivity.
  - intros B A HB HA cutoff n R Q. simpl. rewrite HB, HA. reflexivity.
  - intros cutoff n R Q. reflexivity.
  - intros A Ts HA HTs cutoff n R Q. cbn [List.map]. rewrite HA. f_equal. apply HTs.
Qed.

Lemma subst_lt_in_ty_subst_lt_in_ty_comm_head : forall T n R Q,
  subst_lt_in_ty 0 (subst_lt n R Q)
    (subst_lt_in_ty (S n) (shift_lt 1 0 R) T) =
  subst_lt_in_ty n R (subst_lt_in_ty 0 Q T).
Proof.
  intros T n R Q.
  pose proof (subst_lt_in_ty_subst_lt_in_ty_comm0 T 0 n R Q) as H.
  simpl in H. rewrite !shift_lt_zero in H. exact H.
Qed.

Lemma shift_lt_subst_lt_comm_many0 : forall k l n R,
  shift_lt k 0 (subst_lt n R l) =
  subst_lt (k + n) (shift_lt k 0 R) (shift_lt k 0 l).
Proof.
  induction k as [|k IH]; intros l n R.
  - rewrite !shift_lt_zero. replace (0 + n) with n by lia. reflexivity.
  - replace (S k) with (1 + k) by lia.
    rewrite <- !shift_lt_fuse.
    rewrite IH.
    rewrite shift_lt_subst_lt_comm0.
    replace (S (k + n)) with (S k + n) by lia.
    rewrite !shift_lt_fuse.
    replace (1 + k) with (S k) by lia.
    reflexivity.
Qed.

Lemma shift_lt_in_ty_subst_lt_in_ty_comm_many0 : forall k T n R,
  shift_lt_in_ty k 0 (subst_lt_in_ty n R T) =
  subst_lt_in_ty (k + n) (shift_lt k 0 R) (shift_lt_in_ty k 0 T).
Proof.
  induction k as [|k IH]; intros T n R.
  - rewrite !shift_lt_in_ty_zero, shift_lt_zero. replace (0 + n) with n by lia. reflexivity.
  - replace (S k) with (1 + k) by lia.
    rewrite <- !shift_lt_in_ty_fuse.
    rewrite IH.
    rewrite shift_lt_in_ty_subst_lt_in_ty_comm0.
    replace (S (k + n)) with (S k + n) by lia.
    rewrite shift_lt_fuse.
    rewrite !shift_lt_in_ty_fuse.
    replace (1 + k) with (S k) by lia.
    reflexivity.
Qed.

Lemma map_shift_lt_in_ty_subst_lt_in_ty_comm_many0 : forall k Ts n R,
  List.map (shift_lt_in_ty k 0) (List.map (subst_lt_in_ty n R) Ts) =
  List.map (subst_lt_in_ty (k + n) (shift_lt k 0 R))
           (List.map (shift_lt_in_ty k 0) Ts).
Proof.
  induction Ts as [|T Ts IH]; intros n R; simpl.
  - reflexivity.
  - rewrite shift_lt_in_ty_subst_lt_in_ty_comm_many0. f_equal. apply IH.
Qed.

Lemma map_shift_lt_subst_lt_comm : forall lts n c R,
  c <= n ->
  List.map (shift_lt 1 c) (List.map (subst_lt n R) lts) =
  List.map (subst_lt (S n) (shift_lt 1 c R)) (List.map (shift_lt 1 c) lts).
Proof.
  induction lts as [|l lts IH]; intros n c R Hcn; simpl.
  - reflexivity.
  - rewrite shift_lt_subst_lt_comm by lia. f_equal. apply IH. lia.
Qed.

Lemma map_shift_lt_in_ty_subst_lt_in_ty_comm : forall Ts n c R,
  c <= n ->
  List.map (shift_lt_in_ty 1 c) (List.map (subst_lt_in_ty n R) Ts) =
  List.map (subst_lt_in_ty (S n) (shift_lt 1 c R))
           (List.map (shift_lt_in_ty 1 c) Ts).
Proof.
  induction Ts as [|T Ts IH]; intros n c R Hcn; simpl.
  - reflexivity.
  - rewrite shift_lt_in_ty_subst_lt_in_ty_comm by lia. f_equal. apply IH. lia.
Qed.

Lemma shift_lt_lift_many_swap : forall k c R,
  shift_lt 1 (c + k) (shift_lt k 0 R) =
  shift_lt k 0 (shift_lt 1 c R).
Proof.
  induction k as [|k IH]; intros c R.
  - rewrite !shift_lt_zero. replace (c + 0) with c by lia. reflexivity.
  - replace (c + S k) with (S (c + k)) by lia.
    replace (shift_lt (S k) 0 R) with (shift_lt 1 0 (shift_lt k 0 R)).
    2:{ rewrite shift_lt_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    rewrite <- (shift_lt_swap (shift_lt k 0 R) 0 (c + k)) by lia.
    rewrite IH.
    rewrite shift_lt_fuse.
    replace (1 + k) with (S k) by lia.
    reflexivity.
Qed.

Lemma shift_lt_in_ty_lift_many_swap : forall k c T,
  shift_lt_in_ty 1 (c + k) (shift_lt_in_ty k 0 T) =
  shift_lt_in_ty k 0 (shift_lt_in_ty 1 c T).
Proof.
  induction k as [|k IH]; intros c T.
  - rewrite !shift_lt_in_ty_zero. replace (c + 0) with c by lia. reflexivity.
  - replace (c + S k) with (S (c + k)) by lia.
    replace (shift_lt_in_ty (S k) 0 T) with (shift_lt_in_ty 1 0 (shift_lt_in_ty k 0 T)).
    2:{ rewrite shift_lt_in_ty_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    rewrite <- (shift_lt_in_ty_swap (shift_lt_in_ty k 0 T) 0 (c + k)) by lia.
    rewrite IH.
    rewrite shift_lt_in_ty_fuse.
    replace (1 + k) with (S k) by lia.
    reflexivity.
Qed.

Lemma map_shift_lt_in_ty_lift_many_swap : forall k c Ts,
  List.map (shift_lt_in_ty 1 (c + k)) (List.map (shift_lt_in_ty k 0) Ts) =
  List.map (shift_lt_in_ty k 0) (List.map (shift_lt_in_ty 1 c) Ts).
Proof.
  intros k c Ts. induction Ts as [|T Ts IH]; simpl.
  - reflexivity.
  - rewrite shift_lt_in_ty_lift_many_swap. f_equal. apply IH.
Qed.

Lemma shift_lt_in_tm_subst_lt_in_tm_comm : forall t n c R,
  c <= n ->
  shift_lt_in_tm 1 c (subst_lt_in_tm n R t) =
  subst_lt_in_tm (S n) (shift_lt 1 c R) (shift_lt_in_tm 1 c t).
Proof.
  intros t. apply (term_list_ind
    (fun t => forall n c R, c <= n ->
       shift_lt_in_tm 1 c (subst_lt_in_tm n R t) =
       subst_lt_in_tm (S n) (shift_lt 1 c R) (shift_lt_in_tm 1 c t))
    (fun ts => forall n c R, c <= n ->
       List.map (shift_lt_in_tm 1 c) (List.map (subst_lt_in_tm n R) ts) =
       List.map (subst_lt_in_tm (S n) (shift_lt 1 c R))
                (List.map (shift_lt_in_tm 1 c) ts))).
  - intros x n c R Hcn. reflexivity.
  - intros t1 t2 IH1 IH2 n c R Hcn. simpl. rewrite IH1 by lia. rewrite IH2 by lia. reflexivity.
  - intros body T IH n c R Hcn. simpl.
    rewrite IH by lia. rewrite shift_lt_in_ty_subst_lt_in_ty_comm by lia. reflexivity.
  - intros tm T IH n c R Hcn. simpl.
    rewrite IH by lia. rewrite shift_lt_in_ty_subst_lt_in_ty_comm by lia. reflexivity.
  - intros bound body IH n c R Hcn. simpl.
    rewrite shift_lt_in_ty_subst_lt_in_ty_comm by lia. rewrite IH by lia. reflexivity.
  - intros tm l IH n c R Hcn. simpl.
    rewrite IH by lia. rewrite shift_lt_subst_lt_comm by lia. reflexivity.
  - intros body IH n c R Hcn. simpl.
    rewrite (IH (S n) (S c) (shift_lt 1 0 R)) by lia.
    rewrite (shift_lt_swap R 0 c) by lia. reflexivity.
  - intros K l lts Ts ts IH n c R Hcn. simpl.
    f_equal.
    + apply shift_lt_subst_lt_comm. lia.
    + change (List.map (shift_lt 1 c) (List.map (subst_lt n R) lts) =
              List.map (subst_lt (S n) (shift_lt 1 c R)) (List.map (shift_lt 1 c) lts)).
      apply map_shift_lt_subst_lt_comm. lia.
    + change (List.map (shift_lt_in_ty 1 c) (List.map (subst_lt_in_ty n R) Ts) =
              List.map (subst_lt_in_ty (S n) (shift_lt 1 c R))
                       (List.map (shift_lt_in_ty 1 c) Ts)).
      apply map_shift_lt_in_ty_subst_lt_in_ty_comm. lia.
    + apply IH. lia.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn n c R Hcn. simpl.
    rewrite IHs by lia.
    rewrite (IHy (n_lt + n) (c + n_lt) (shift_lt n_lt 0 R)) by lia.
    replace (S (n_lt + n)) with (n_lt + S n) by lia.
    rewrite shift_lt_lift_many_swap.
    rewrite IHn by lia.
    reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody n c R Hcn. simpl.
    f_equal.
    + change (List.map (shift_lt_in_ty 1 c) (List.map (subst_lt_in_ty n R) Ts) =
              List.map (subst_lt_in_ty (S n) (shift_lt 1 c R))
                       (List.map (shift_lt_in_ty 1 c) Ts)).
      apply map_shift_lt_in_ty_subst_lt_in_ty_comm. lia.
    + apply shift_lt_in_ty_subst_lt_in_ty_comm. lia.
    + apply shift_lt_in_ty_subst_lt_in_ty_comm. lia.
    + apply IHop. lia.
    + apply IHbody. lia.
  - intros tm Ss arg IHt IHa n c R Hcn. simpl.
    f_equal.
    + apply IHt. lia.
    + change (List.map (shift_lt_in_ty 1 c) (List.map (subst_lt_in_ty n R) Ss) =
              List.map (subst_lt_in_ty (S n) (shift_lt 1 c R))
                       (List.map (shift_lt_in_ty 1 c) Ss)).
      apply map_shift_lt_in_ty_subst_lt_in_ty_comm. lia.
    + apply IHa. lia.
  - intros E m n_beta Ts T_R op_body IHop n c R Hcn. simpl.
    f_equal.
    + change (List.map (shift_lt_in_ty 1 c) (List.map (subst_lt_in_ty n R) Ts) =
              List.map (subst_lt_in_ty (S n) (shift_lt 1 c R))
                       (List.map (shift_lt_in_ty 1 c) Ts)).
      apply map_shift_lt_in_ty_subst_lt_in_ty_comm. lia.
    + apply shift_lt_in_ty_subst_lt_in_ty_comm. lia.
    + apply IHop. lia.
  - intros m T_B T_R tm IH n c R Hcn. simpl.
    rewrite !shift_lt_in_ty_subst_lt_in_ty_comm by lia. rewrite IH by lia. reflexivity.
  - intros m T_B T_R b IH n c R Hcn. simpl.
    rewrite !shift_lt_in_ty_subst_lt_in_ty_comm by lia. rewrite IH by lia. reflexivity.
  - intros n c R Hcn. reflexivity.
  - intros tm ts IHt IHts n c R Hcn. simpl. rewrite IHt by lia. f_equal. apply IHts. lia.
Qed.

Lemma shift_lt_in_tm_subst_lt_in_tm_comm0 : forall t n R,
  shift_lt_in_tm 1 0 (subst_lt_in_tm n R t) =
  subst_lt_in_tm (S n) (shift_lt 1 0 R) (shift_lt_in_tm 1 0 t).
Proof. intros t n R. apply shift_lt_in_tm_subst_lt_in_tm_comm. lia. Qed.

Lemma shift_ty_subst_lt_in_ty_commute : forall T a1 c1 n R,
  shift_ty a1 c1 (subst_lt_in_ty n R T)
  = subst_lt_in_ty n R (shift_ty a1 c1 T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall a1 c1 n R,
       shift_ty a1 c1 (subst_lt_in_ty n R T) = subst_lt_in_ty n R (shift_ty a1 c1 T))
    (fun Ts => forall a1 c1 n R,
       List.map (shift_ty a1 c1) (List.map (subst_lt_in_ty n R) Ts)
       = List.map (subst_lt_in_ty n R) (List.map (shift_ty a1 c1) Ts))).
  - intros m a1 c1 n R. reflexivity.
  - intros A l B HA HB a1 c1 n R.
    simpl subst_lt_in_ty. simpl shift_ty. simpl subst_lt_in_ty.
    rewrite HA, HB. reflexivity.
  - intros K l Ts HTs a1 c1 n R.
    rewrite subst_lt_in_ty_ctor_eq, shift_ty_ctor_eq, shift_ty_ctor_eq, subst_lt_in_ty_ctor_eq.
    f_equal. apply HTs.
  - intros A HA a1 c1 n R.
    simpl subst_lt_in_ty. simpl shift_ty. simpl subst_lt_in_ty. rewrite HA. reflexivity.
  - intros B A HB HA a1 c1 n R.
    simpl subst_lt_in_ty. simpl shift_ty. simpl subst_lt_in_ty. rewrite HB, HA. reflexivity.
  - intros a1 c1 n R. reflexivity.
  - intros A Ts HA HTs a1 c1 n R. cbn [List.map]. rewrite HA. f_equal. apply HTs.
Qed.

