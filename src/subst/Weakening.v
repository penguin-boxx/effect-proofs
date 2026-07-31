Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import ShiftLaws.
Require Import CtxMap.
Require Import SubstTactics.

(* =================================================================== *)
(* Weakening: context-insertion relations and the weakening payload.   *)
(*                                                                     *)
(* One insertion relation per binding sort — [InsTy c G G'], [InsLt],  *)
(* [InsTm] / [InsTmAt] (G' is G with one binder inserted at depth c) — *)
(* each with its lookup/wf transport lemmas, culminating in the three  *)
(* typing-weakening theorems [typing_InsTy] / [typing_InsLt] (in       *)
(* SubstLt.v — their T_Match cases need SubstLt's elim/multi_subst     *)
(* theory, so the dependency order forces them there) and              *)
(* [typing_InsTmAt] with                                               *)
(* its front instance [typing_weaken_tm_shift].  ([typing_ind_forall2],*)
(* the Forall2-aware induction principle every payload theorem in this *)
(* tier applies, lives in core/Typing.v with the mutual scheme.)       *)
(* =================================================================== *)

(* =================================================================== *)
(* Depth-general bind_ty weakening for subtyping.                      *)
(*                                                                     *)
(* InsTy c G G' : G' is G with one bind_ty inserted after c ty-binders *)
(* (counted from the head).  Subtyping is closed under InsTy, with     *)
(* types shifted by `shift_ty 1 c`.  `sub_weaken_ty_shift` is the      *)
(* front (c = 0) instance.                                             *)
(* =================================================================== *)

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
Proof. sig_congr shift_ty_swap. Qed.

Lemma shift_ty_eff_sig_swap_0 : forall sig c,
  shift_ty_eff_sig 1 0 (shift_ty_eff_sig 1 c sig) =
  shift_ty_eff_sig 1 (S c) (shift_ty_eff_sig 1 0 sig).
Proof. sig_congr shift_ty_swap. Qed.

Lemma shift_ty_ctor_sig_shift_lt_comm : forall sig c,
  shift_lt_ctor_sig 1 0 (shift_ty_ctor_sig 1 c sig) =
  shift_ty_ctor_sig 1 c (shift_lt_ctor_sig 1 0 sig).
Proof. sig_congr shift_ty_shift_lt_in_ty_commute. Qed.

Lemma shift_ty_eff_sig_shift_lt_comm : forall sig c,
  shift_lt_eff_sig 1 0 (shift_ty_eff_sig 1 c sig) =
  shift_ty_eff_sig 1 c (shift_lt_eff_sig 1 0 sig).
Proof. sig_congr shift_ty_shift_lt_in_ty_commute. Qed.

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
  | InsTy_eff : forall c G G' eg m1 ops,
      InsTy c G G' ->
      InsTy c (bind_eff eg m1 ops :: G)
        (bind_eff eg m1
           (List.map (fun '(n_b, sig_ty, ret_ty) =>
               (n_b, shift_ty 1 (m1 + n_b + c) sig_ty,
                shift_ty 1 (m1 + n_b + c) ret_ty)) ops) :: G').

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

(* InsTy as a context map: types shift by [shift_ty 1 c] (cutoff bumped *)
(* under a ty binder), lifetimes are untouched.                         *)
Lemma CtxMapSpec_InsTy :
  CtxMapSpec nat (fun c => shift_ty 1 c) (fun _ l => l)
    (fun c => c) S (fun c G G' => InsTy c G G').
Proof.
  constructor.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; apply shift_ty_ctor_eq.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros c G G' D HIns. apply InsTy_lt. exact HIns.
  - intros c G G' B HIns. apply InsTy_ty. exact HIns.
  - intros c G G' x Δ HIns Hlk. econstructor.
    rewrite (InsTy_lookup_lt c G G' HIns x). exact Hlk.
  - intros c G G' x Δ HIns Hlk Hwf. apply LS_Var.
    + rewrite (InsTy_lookup_lt c G G' HIns x). exact Hlk.
    + exact Hwf.
  - intros c G G' α B HIns Hlk _ HwfB'. rewrite shv_shift. econstructor.
    + rewrite (InsTy_lookup_ty c G G' HIns α). rewrite Hlk. reflexivity.
    + exact HwfB'.
  - intros c G G' α B HIns Hlk _ HwfB'. rewrite shv_shift. apply SA_VarCtx.
    + rewrite (InsTy_lookup_ty c G G' HIns α). rewrite Hlk. reflexivity.
    + exact HwfB'.
Qed.

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
  intros G l Hwf c G' HIns.
  exact (lt_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_InsTy G l Hwf c G' HIns).
Qed.
#[export] Hint Resolve lt_wf_InsTy : ctxmap.

Lemma lifetimes_wf_InsTy : forall G lts,
  lifetimes_wf G lts -> forall c G', InsTy c G G' -> lifetimes_wf G' lts.
Proof.
  intros G lts Hwf c G' HIns.
  pose proof (lifetimes_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_InsTy
                G lts Hwf c G' HIns) as H.
  rewrite List.map_id in H. exact H.
Qed.
#[export] Hint Resolve lifetimes_wf_InsTy : ctxmap.

Lemma ty_wf_InsTy : forall G T,
  ty_wf G T -> forall c G', InsTy c G G' -> ty_wf G' (shift_ty 1 c T).
Proof.
  intros G T Hwf c G' HIns.
  exact (ty_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_InsTy G T Hwf c G' HIns).
Qed.

Lemma types_wf_InsTy : forall G Ts,
  types_wf G Ts -> forall c G', InsTy c G G' -> types_wf G' (List.map (shift_ty 1 c) Ts).
Proof.
  intros G Ts Hwf c G' HIns.
  exact (types_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_InsTy G Ts Hwf c G' HIns).
Qed.
#[export] Hint Resolve types_wf_InsTy : ctxmap.
#[export] Hint Resolve ty_wf_InsTy : ctxmap.

Lemma lt_sub_InsTy : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall c G', InsTy c G G' -> G' ⊢ₗ l1 <: l2.
Proof.
  intros G l1 l2 H c G' HIns.
  exact (lt_sub_ctx_map _ _ _ _ _ _ CtxMapSpec_InsTy G l1 l2 H c G' HIns).
Qed.
#[export] Hint Resolve lt_sub_InsTy : ctxmap.

(* SA_Any side-condition transport for the generic sub payload:      *)
(* [lt_of_ty_G] commutes with [shift_ty 1 c] as an equality.         *)
Lemma sub_any_InsTy : forall (c : nat) G G' T Δ,
  InsTy c G G' -> ty_wf G T ->
  G' ⊢ₗ lt_of_ty_G G T <: Δ ->
  G' ⊢ₗ lt_of_ty_G G' (shift_ty 1 c T) <: Δ.
Proof.
  intros c G G' T Δ HIns _ Hle.
  rewrite (lt_of_ty_G_InsTy c G G' HIns T). exact Hle.
Qed.

Lemma sub_InsTy : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall c G', InsTy c G G' -> G' ⊢ shift_ty 1 c T1 <:: shift_ty 1 c T2.
Proof.
  intros G T1 T2 H c G' HIns.
  exact (sub_ctx_map _ _ _ _ _ _ CtxMapSpec_InsTy sub_any_InsTy
           G T1 T2 H c G' HIns).
Qed.
#[export] Hint Resolve sub_InsTy : ctxmap.

(* ---- Subtyping weakening (correctly shifted) -------------------- *)

(* Context weakening for subtyping.  Inserting a `bind_ty` binding at   *)
(* the front shifts the type-variable namespace by one, so the related  *)
(* types must be shifted by `shift_ty 1 0`.  (A no-shift variant would  *)
(* be unsound: prepending a binding silently re-captures the de Bruijn  *)
(* indices.)  Derived from `sub_InsTy`.                                 *)
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
Proof. sig_congr shift_lt_in_ty_swap. Qed.

Lemma shift_lt_eff_sig_swap_0 : forall sig c,
  shift_lt_eff_sig 1 0 (shift_lt_eff_sig 1 c sig) =
  shift_lt_eff_sig 1 (S c) (shift_lt_eff_sig 1 0 sig).
Proof. sig_congr shift_lt_in_ty_swap_0. Qed.

Lemma shift_lt_ctor_sig_shift_ty_comm : forall sig c,
  shift_ty_ctor_sig 1 0 (shift_lt_ctor_sig 1 c sig) =
  shift_lt_ctor_sig 1 c (shift_ty_ctor_sig 1 0 sig).
Proof. sig_congr shift_ty_shift_lt_in_ty_commute. Qed.

Lemma shift_lt_eff_sig_shift_ty_comm : forall sig c,
  shift_ty_eff_sig 1 0 (shift_lt_eff_sig 1 c sig) =
  shift_lt_eff_sig 1 c (shift_ty_eff_sig 1 0 sig).
Proof. sig_congr shift_ty_shift_lt_in_ty_commute. Qed.

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
  | InsLt_eff : forall c G G' eg m1 ops,
      InsLt c G G' ->
      InsLt c (bind_eff eg m1 ops :: G)
              (bind_eff eg m1
                 (List.map (fun '(n_b, sig_ty, ret_ty) =>
                     (n_b, shift_lt_in_ty 1 c sig_ty,
                      shift_lt_in_ty 1 c ret_ty)) ops) :: G').

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

(* InsLt as a context map: lifetimes shift by [shift_lt 1 c] (cutoff  *)
(* bumped under an lt binder), types by [shift_lt_in_ty 1 c].         *)
Lemma CtxMapSpec_InsLt :
  CtxMapSpec nat (fun c => shift_lt_in_ty 1 c) (fun c => shift_lt 1 c)
    S (fun c => c) (fun c G G' => InsLt c G G').
Proof.
  constructor.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; apply shift_lt_in_ty_ctor_eq.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros c G G' D HIns. apply InsLt_lt. exact HIns.
  - intros c G G' B HIns. apply InsLt_ty. exact HIns.
  - intros c G G' x Δ HIns Hlk. rewrite shift_lt_var_eq.
    replace (if Nat.leb c x then x + 1 else x) with (shv c x)
      by (unfold shv; destruct (Nat.leb c x); [rewrite Nat.add_1_r|]; reflexivity).
    econstructor. rewrite (InsLt_lookup_lt c G G' HIns x).
    rewrite Hlk. reflexivity.
  - intros c G G' x Δ HIns Hlk Hwf. rewrite shift_lt_var_eq.
    replace (if Nat.leb c x then x + 1 else x) with (shv c x)
      by (unfold shv; destruct (Nat.leb c x); [rewrite Nat.add_1_r|]; reflexivity).
    apply LS_Var.
    + rewrite (InsLt_lookup_lt c G G' HIns x). rewrite Hlk. reflexivity.
    + exact Hwf.
  - intros c G G' α B HIns Hlk _ HwfB'. rewrite shift_lt_in_ty_var_eq.
    econstructor.
    + rewrite (InsLt_lookup_ty c G G' HIns α). rewrite Hlk. reflexivity.
    + exact HwfB'.
  - intros c G G' α B HIns Hlk _ HwfB'. rewrite shift_lt_in_ty_var_eq.
    apply SA_VarCtx.
    + rewrite (InsLt_lookup_ty c G G' HIns α). rewrite Hlk. reflexivity.
    + exact HwfB'.
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
    + rewrite shift_lt_in_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor. rewrite shift_lt_join_eq.
      f_equal. exact IHT.
    + rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite shift_lt_join_eq. rewrite IHT, IHT0. reflexivity.
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
    + rewrite shift_lt_in_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor. rewrite shift_lt_join_eq.
      f_equal. exact IHT.
    + rewrite !lt_of_ty_ctx_ltall. reflexivity.
    + rewrite !lt_of_ty_ctx_tyall. reflexivity.
    + reflexivity.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons. rewrite shift_lt_join_eq. rewrite IHT, IHT0. reflexivity.
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
  intros G l Hwf c G' HIns.
  exact (lt_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_InsLt G l Hwf c G' HIns).
Qed.
#[export] Hint Resolve lt_wf_InsLt : ctxmap.

Lemma lifetimes_wf_InsLt : forall G lts,
  lifetimes_wf G lts -> forall c G', InsLt c G G' ->
    lifetimes_wf G' (List.map (shift_lt 1 c) lts).
Proof.
  intros G lts Hwf c G' HIns.
  exact (lifetimes_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_InsLt G lts Hwf c G' HIns).
Qed.
#[export] Hint Resolve lifetimes_wf_InsLt : ctxmap.

Lemma ty_wf_InsLt : forall G T,
  ty_wf G T -> forall c G', InsLt c G G' -> ty_wf G' (shift_lt_in_ty 1 c T).
Proof.
  intros G T Hwf c G' HIns.
  exact (ty_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_InsLt G T Hwf c G' HIns).
Qed.

Lemma types_wf_InsLt : forall G Ts,
  types_wf G Ts -> forall c G', InsLt c G G' -> types_wf G' (List.map (shift_lt_in_ty 1 c) Ts).
Proof.
  intros G Ts Hwf c G' HIns.
  exact (types_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_InsLt G Ts Hwf c G' HIns).
Qed.
#[export] Hint Resolve types_wf_InsLt : ctxmap.
#[export] Hint Resolve ty_wf_InsLt : ctxmap.

Lemma lt_sub_InsLt : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall c G', InsLt c G G' -> G' ⊢ₗ shift_lt 1 c l1 <: shift_lt 1 c l2.
Proof.
  intros G l1 l2 H c G' HIns.
  exact (lt_sub_ctx_map _ _ _ _ _ _ CtxMapSpec_InsLt G l1 l2 H c G' HIns).
Qed.
#[export] Hint Resolve lt_sub_InsLt : ctxmap.

(* SA_Any side-condition transport for the generic sub payload:      *)
(* [lt_of_ty_G] commutes with [shift_lt_in_ty 1 c] as an equality.   *)
Lemma sub_any_InsLt : forall (c : nat) G G' T Δ,
  InsLt c G G' -> ty_wf G T ->
  G' ⊢ₗ shift_lt 1 c (lt_of_ty_G G T) <: shift_lt 1 c Δ ->
  G' ⊢ₗ lt_of_ty_G G' (shift_lt_in_ty 1 c T) <: shift_lt 1 c Δ.
Proof.
  intros c G G' T Δ HIns _ Hle.
  rewrite (lt_of_ty_G_InsLt c G G' HIns T). exact Hle.
Qed.

Lemma sub_InsLt : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall c G', InsLt c G G' -> G' ⊢ shift_lt_in_ty 1 c T1 <:: shift_lt_in_ty 1 c T2.
Proof.
  intros G T1 T2 H c G' HIns.
  exact (sub_ctx_map _ _ _ _ _ _ CtxMapSpec_InsLt sub_any_InsLt
           G T1 T2 H c G' HIns).
Qed.
#[export] Hint Resolve sub_InsLt : ctxmap.


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
| InsTm_eff : forall E n_a ops G G',
    InsTm G G' -> InsTm (bind_eff E n_a ops :: G) (bind_eff E n_a ops :: G').

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
                 |K0 n_lt n_ty f r G G' H IH|E n_a ops G G' H IH];
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
                 |K n_lt n_ty f r G G' H IH|E0 n_a ops G G' H IH];
    intro E; simpl.
  - reflexivity.
  - apply IH.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - apply IH.
  - destruct (Nat.eqb E E0); [reflexivity|apply IH].
Qed.

(* InsTm as a context map: term binders are invisible to types and    *)
(* lifetimes, so both transformations are the identity (parameter     *)
(* [unit]).                                                           *)
Lemma CtxMapSpec_InsTm :
  CtxMapSpec unit (fun _ T => T) (fun _ l => l)
    (fun p => p) (fun p => p) (fun _ G G' => InsTm G G').
Proof.
  constructor.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros p K l Ts. rewrite List.map_id. reflexivity.
  - intros; reflexivity.
  - intros; reflexivity.
  - intros p G G' D HIns. apply InsTm_lt. exact HIns.
  - intros p G G' B HIns. apply InsTm_ty. exact HIns.
  - intros p G G' x Δ HIns Hlk. econstructor.
    rewrite (InsTm_lookup_lt G G' HIns x). exact Hlk.
  - intros p G G' x Δ HIns Hlk Hwf. apply LS_Var.
    + rewrite (InsTm_lookup_lt G G' HIns x). exact Hlk.
    + exact Hwf.
  - intros p G G' α B HIns Hlk _ HwfB'. econstructor.
    + rewrite (InsTm_lookup_ty G G' HIns α). exact Hlk.
    + exact HwfB'.
  - intros p G G' α B HIns Hlk _ HwfB'. apply SA_VarCtx.
    + rewrite (InsTm_lookup_ty G G' HIns α). exact Hlk.
    + exact HwfB'.
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
  intros G l Hwf G' HIns.
  exact (lt_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_InsTm G l Hwf tt G' HIns).
Qed.
#[export] Hint Resolve lt_wf_InsTm : ctxmap.

Lemma lifetimes_wf_InsTm : forall G lts,
  lifetimes_wf G lts -> forall G', InsTm G G' -> lifetimes_wf G' lts.
Proof.
  intros G lts Hwf G' HIns.
  pose proof (lifetimes_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_InsTm
                G lts Hwf tt G' HIns) as H.
  rewrite List.map_id in H. exact H.
Qed.
#[export] Hint Resolve lifetimes_wf_InsTm : ctxmap.

Lemma ty_wf_InsTm : forall G T,
  ty_wf G T -> forall G', InsTm G G' -> ty_wf G' T.
Proof.
  intros G T Hwf G' HIns.
  exact (ty_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_InsTm G T Hwf tt G' HIns).
Qed.

Lemma types_wf_InsTm : forall G Ts,
  types_wf G Ts -> forall G', InsTm G G' -> types_wf G' Ts.
Proof.
  intros G Ts Hwf G' HIns.
  pose proof (types_wf_ctx_map _ _ _ _ _ _ CtxMapSpec_InsTm
                G Ts Hwf tt G' HIns) as H.
  rewrite List.map_id in H. exact H.
Qed.
#[export] Hint Resolve types_wf_InsTm : ctxmap.
#[export] Hint Resolve ty_wf_InsTm : ctxmap.

Lemma lt_sub_InsTm : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall G', InsTm G G' -> G' ⊢ₗ l1 <: l2.
Proof.
  intros G l1 l2 H G' HIns.
  exact (lt_sub_ctx_map _ _ _ _ _ _ CtxMapSpec_InsTm G l1 l2 H tt G' HIns).
Qed.
#[export] Hint Resolve lt_sub_InsTm : ctxmap.

(* ---- escape side-condition transport: [lt_of_ty_G Γ T <: lt_free] ----  *)
(* The handler/perform escape premise (paper: local ∉ lt_Γ(T)) is preserved *)
(* by every context map: [lt_of_ty_G] commutes (= or <:) and [lt_sub_*]     *)
(* transports, with shift/subst of [lt_free] being [lt_free].               *)
Lemma sub_free_InsTm : forall G G' T,
  InsTm G G' -> G ⊢ₗ lt_of_ty_G G T <: lt_free ->
  G' ⊢ₗ lt_of_ty_G G' T <: lt_free.
Proof.
  intros G G' T HIns H. rewrite (lt_of_ty_G_InsTm G G' HIns T).
  wf_transport.
Qed.
#[export] Hint Resolve sub_free_InsTm : ctxmap.

Lemma sub_free_list_InsTm : forall G G' Ss,
  InsTm G G' -> Forall (fun S => G ⊢ₗ lt_of_ty_G G S <: lt_free) Ss ->
  Forall (fun S => G' ⊢ₗ lt_of_ty_G G' S <: lt_free) Ss.
Proof.
  intros G G' Ss HIns H. induction H; constructor;
    [eapply sub_free_InsTm; eauto | auto].
Qed.
#[export] Hint Resolve sub_free_list_InsTm : ctxmap.

Lemma sub_free_InsTy : forall c G G' T,
  InsTy c G G' -> G ⊢ₗ lt_of_ty_G G T <: lt_free ->
  G' ⊢ₗ lt_of_ty_G G' (shift_ty 1 c T) <: lt_free.
Proof.
  intros c G G' T HIns H. rewrite (lt_of_ty_G_InsTy c G G' HIns T).
  wf_transport.
Qed.
#[export] Hint Resolve sub_free_InsTy : ctxmap.

Lemma sub_free_list_InsTy : forall c G G' Ss,
  InsTy c G G' -> Forall (fun S => G ⊢ₗ lt_of_ty_G G S <: lt_free) Ss ->
  Forall (fun S => G' ⊢ₗ lt_of_ty_G G' S <: lt_free) (List.map (shift_ty 1 c) Ss).
Proof.
  intros c G G' Ss HIns H. induction H; simpl; constructor;
    [eapply sub_free_InsTy; eauto | auto].
Qed.
#[export] Hint Resolve sub_free_list_InsTy : ctxmap.

Lemma sub_free_InsLt : forall c G G' T,
  InsLt c G G' -> G ⊢ₗ lt_of_ty_G G T <: lt_free ->
  G' ⊢ₗ lt_of_ty_G G' (shift_lt_in_ty 1 c T) <: lt_free.
Proof.
  intros c G G' T HIns H. rewrite (lt_of_ty_G_InsLt c G G' HIns T).
  change lt_free with (shift_lt 1 c lt_free) at 1.
  wf_transport.
Qed.
#[export] Hint Resolve sub_free_InsLt : ctxmap.

Lemma sub_free_list_InsLt : forall c G G' Ss,
  InsLt c G G' -> Forall (fun S => G ⊢ₗ lt_of_ty_G G S <: lt_free) Ss ->
  Forall (fun S => G' ⊢ₗ lt_of_ty_G G' S <: lt_free) (List.map (shift_lt_in_ty 1 c) Ss).
Proof.
  intros c G G' Ss HIns H. induction H; simpl; constructor;
    [eapply sub_free_InsLt; eauto | auto].
Qed.
#[export] Hint Resolve sub_free_list_InsLt : ctxmap.

(* SA_Any side-condition transport for the generic sub payload:      *)
(* [lt_of_ty_G] is invariant under InsTm.                            *)
Lemma sub_any_InsTm : forall G G' T Δ,
  InsTm G G' -> ty_wf G T ->
  G' ⊢ₗ lt_of_ty_G G T <: Δ ->
  G' ⊢ₗ lt_of_ty_G G' T <: Δ.
Proof.
  intros G G' T Δ HIns _ Hle.
  rewrite (lt_of_ty_G_InsTm G G' HIns T). exact Hle.
Qed.

Lemma sub_InsTm : forall G T1 T2, G ⊢ T1 <:: T2 ->
  forall G', InsTm G G' -> G' ⊢ T1 <:: T2.
Proof.
  intros G T1 T2 H G' HIns.
  exact (sub_ctx_map _ _ _ _ _ _ CtxMapSpec_InsTm (fun _ => sub_any_InsTm)
           G T1 T2 H tt G' HIns).
Qed.
#[export] Hint Resolve sub_InsTm : ctxmap.

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
| InsTmAt_eff : forall c E n_a ops G G',
    InsTmAt c G G' -> InsTmAt c (bind_eff E n_a ops :: G)
                              (bind_eff E n_a ops :: G').

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


(* Bridge: free_tm_vars' inline op-bodies fix as a concat-map.  The   *)
(* inner cutoff is quantified in full generality so the pattern also  *)
(* matches goals where simpl has normalised (S c + 2) to S (c + 2).   *)
Lemma free_tm_vars_ops_eq_concat : forall d (obs : list (nat * term)),
  List.concat (List.map (fun '(_, ob) => free_tm_vars d ob) obs)
  = List.concat (List.map (fun p => free_tm_vars d (snd p)) obs).
Proof. intros; induction obs as [|[nb ob] rest IH]; simpl; congruence. Qed.
#[export] Hint Rewrite free_tm_vars_ops_eq_concat : subst_go.

Lemma free_tm_vars_shift_ty_in_tm : forall t cutoff c,
  free_tm_vars cutoff (shift_ty_in_tm 1 c t) = free_tm_vars cutoff t.
Proof.
  apply (term_list_ind
    (fun t => forall cutoff c, free_tm_vars cutoff (shift_ty_in_tm 1 c t) = free_tm_vars cutoff t)
    (fun ts => forall cutoff c,
      List.concat (List.map (free_tm_vars cutoff) (List.map (shift_ty_in_tm 1 c) ts)) =
      List.concat (List.map (free_tm_vars cutoff) ts))
    (fun obs => forall cutoff c,
      List.concat (List.map (fun p => free_tm_vars cutoff (snd p))
        (List.map (fun p => (fst p, shift_ty_in_tm 1 (c + fst p) (snd p))) obs)) =
      List.concat (List.map (fun p => free_tm_vars cutoff (snd p)) obs))).
  - reflexivity.
  - intros t1 t2 IH1 IH2 cutoff c. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH cutoff c. simpl. apply IH.
  - intros t T IH cutoff c. simpl. apply IH.
  - intros bound body IH cutoff c. simpl. apply IH.
  - intros t l IH cutoff c. simpl. apply IH.
  - intros body IH cutoff c. simpl. apply IH.
  - intros K l lts Ts ts IH cutoff c. simpl.    apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn cutoff c. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb cutoff c. simpl.
    rewrite !free_tm_vars_ops_eq_concat, shift_ty_in_tm_ops_eq_map,
            IHops, IHb. reflexivity.
  - intros t op Ss A_ret arg IHt IHa cutoff c. simpl. rewrite IHt, IHa. reflexivity.
  - intros E m Ts T_R op_bodies IHops cutoff c. simpl.
    rewrite !free_tm_vars_ops_eq_concat, shift_ty_in_tm_ops_eq_map.
    apply IHops.
  - intros m T_B T_R t IH cutoff c. simpl. apply IH.
  - reflexivity.
  - intros t ts IHt IHts cutoff c. simpl. rewrite IHt, IHts. reflexivity.
  - reflexivity.
  - intros nb ob obs IHob IHobs cutoff c. simpl. rewrite IHob, IHobs. reflexivity.
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
      List.concat (List.map (free_tm_vars cutoff) ts))
    (fun obs => forall cutoff c,
      List.concat (List.map (fun p => free_tm_vars cutoff (snd p))
        (List.map (fun p => (fst p, shift_lt_in_tm 1 c (snd p))) obs)) =
      List.concat (List.map (fun p => free_tm_vars cutoff (snd p)) obs)));
    go_traverse.
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


Lemma free_tm_vars_subst_lt_in_tm : forall t cutoff n R,
  free_tm_vars cutoff (subst_lt_in_tm n R t) = free_tm_vars cutoff t.
Proof.
  apply (term_list_ind
    (fun t => forall cutoff n R,
      free_tm_vars cutoff (subst_lt_in_tm n R t) = free_tm_vars cutoff t)
    (fun ts => forall cutoff n R,
      List.concat (List.map (free_tm_vars cutoff) (List.map (subst_lt_in_tm n R) ts)) =
      List.concat (List.map (free_tm_vars cutoff) ts))
    (fun obs => forall cutoff n R,
      List.concat (List.map (fun p => free_tm_vars cutoff (snd p))
        (List.map (fun p => (fst p, subst_lt_in_tm n R (snd p))) obs)) =
      List.concat (List.map (fun p => free_tm_vars cutoff (snd p)) obs)));
    go_traverse.
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
      List.map (shv c) (List.concat (List.map (free_tm_vars cutoff) ts)))
    (fun obs => forall cutoff c,
      List.concat (List.map (fun p => free_tm_vars cutoff (snd p))
        (List.map (fun p => (fst p, shift_tm 1 (cutoff + c) (snd p))) obs)) =
      List.map (shv c)
        (List.concat (List.map (fun p => free_tm_vars cutoff (snd p)) obs)))).
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
  - intros K l lts Ts ts IH cutoff c. simpl.    apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn cutoff c. simpl.
    rewrite IHs, IHn.
    replace (cutoff + c + arity) with (cutoff + arity + c) by lia.
    rewrite IHy. rewrite !List.map_app. reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb cutoff c. simpl.
    rewrite !free_tm_vars_ops_eq_concat, shift_tm_ops_eq_map.
    replace (cutoff + c + 2) with (cutoff + 2 + c) by lia.
    rewrite IHops.
    replace (S (cutoff + c)) with (S cutoff + c) by lia.
    rewrite IHb. rewrite List.map_app. reflexivity.
  - intros t op Ss A_ret arg IHt IHa cutoff c. simpl. rewrite IHt, IHa. rewrite List.map_app. reflexivity.
  - intros E m Ts T_R op_bodies IHops cutoff c. simpl.
    rewrite !free_tm_vars_ops_eq_concat, shift_tm_ops_eq_map.
    replace (cutoff + c + 2) with (cutoff + 2 + c) by lia. apply IHops.
  - intros m T_B T_R t IH cutoff c. simpl. apply IH.
  - intros cutoff c. reflexivity.
  - intros t ts IHt IHts cutoff c. simpl. rewrite IHt, IHts. rewrite List.map_app. reflexivity.
  - intros cutoff c. reflexivity.
  - intros nb ob obs IHob IHobs cutoff c. simpl.
    rewrite IHob, IHobs. rewrite List.map_app. reflexivity.
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
      List.concat (List.map (free_tm_vars d) ts) = [])
    (fun obs => forall c d,
      c <= d ->
      List.concat (List.map (fun p => free_tm_vars c (snd p)) obs) = [] ->
      List.concat (List.map (fun p => free_tm_vars d (snd p)) obs) = [])).
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
    apply IH with (c := c); [exact Hle|exact Hfree].
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn c d Hle Hfree. simpl in *.
    apply List.app_eq_nil in Hfree as [Hs Hrest].
    apply List.app_eq_nil in Hrest as [Hy Hn].
    rewrite (IHs c d Hle Hs).
    rewrite (IHy (c + arity) (d + arity) ltac:(lia) Hy).
    rewrite (IHn c d Hle Hn). reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb c d Hle Hfree. simpl in *.
    rewrite free_tm_vars_ops_eq_concat in Hfree.
    rewrite free_tm_vars_ops_eq_concat.
    apply List.app_eq_nil in Hfree as [Hops Hbody].
    rewrite (IHops (c + 2) (d + 2) ltac:(lia) Hops).
    rewrite (IHb (S c) (S d) ltac:(lia) Hbody). reflexivity.
  - intros t op Ss A_ret arg IHt IHa c d Hle Hfree. simpl in *.
    apply List.app_eq_nil in Hfree as [Ht Harg].
    rewrite (IHt c d Hle Ht), (IHa c d Hle Harg). reflexivity.
  - intros E m Ts T_R op_bodies IHops c d Hle Hfree. simpl in *.
    rewrite free_tm_vars_ops_eq_concat in Hfree.
    rewrite free_tm_vars_ops_eq_concat.
    apply IHops with (c := c + 2); [lia|exact Hfree].
  - intros m T_B T_R t IH c d Hle Hfree. simpl in *. apply IH with (c := c); [exact Hle|exact Hfree].
  - intros c d Hle Hfree. reflexivity.
  - intros t ts IHt IHts c d Hle Hfree. simpl in *.
    apply List.app_eq_nil in Hfree as [Ht Hts].
    rewrite (IHt c d Hle Ht), (IHts c d Hle Hts). reflexivity.
  - intros c d Hle Hfree. reflexivity.
  - intros nb ob obs IHob IHobs c d Hle Hfree. simpl in *.
    apply List.app_eq_nil in Hfree as [Hob Hobs].
    rewrite (IHob c d Hle Hob), (IHobs c d Hle Hobs). reflexivity.
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
    change (fold_right (fun A0 acc => lt_join (lt_of_ty_ctx (List.length Γ) Γ A0) acc) lt_free Ts)
      with (lt_of_ty_ctx_list (List.length Γ) Γ Ts).
    change (fold_right (fun T0 acc => lt_join (lt_of_ty T0) acc) lt_free Ts)
      with (lt_of_ty_list Ts).
    rewrite H by exact HT. rewrite H0 by exact HTs. reflexivity.
Qed.


(* Bridge: has_rt_cap's inline op-bodies fix as an existsb.           *)
Lemma has_rt_cap_ops_eq : forall (obs : list (nat * term)),
  existsb (fun '(_, ob) => has_rt_cap ob) obs
  = existsb (fun p => has_rt_cap (snd p)) obs.
Proof. intros; induction obs as [|[nb ob] rest IH]; simpl; congruence. Qed.
#[export] Hint Rewrite has_rt_cap_ops_eq : subst_go.

Lemma has_rt_cap_shift_tm : forall t amount cutoff,
  has_rt_cap (shift_tm amount cutoff t) = has_rt_cap t.
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
      has_rt_cap (shift_tm amount cutoff t) = has_rt_cap t)
    (fun ts => forall amount cutoff,
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end)
        (List.map (shift_tm amount cutoff) ts) =
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts)
    (fun obs => forall amount cutoff,
      existsb (fun p => has_rt_cap (snd p))
        (List.map (fun p => (fst p, shift_tm amount (cutoff + 2) (snd p))) obs) =
      existsb (fun p => has_rt_cap (snd p)) obs));
    go_traverse.
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
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts)
    (fun obs => forall amount cutoff,
      existsb (fun p => has_rt_cap (snd p))
        (List.map (fun p => (fst p, shift_ty_in_tm amount (cutoff + fst p) (snd p))) obs) =
      existsb (fun p => has_rt_cap (snd p)) obs));
    go_traverse.
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
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts)
    (fun obs => forall amount cutoff,
      existsb (fun p => has_rt_cap (snd p))
        (List.map (fun p => (fst p, shift_lt_in_tm amount cutoff (snd p))) obs) =
      existsb (fun p => has_rt_cap (snd p)) obs));
    go_traverse.
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
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts)
    (fun obs => forall var replacement,
      existsb (fun p => has_rt_cap (snd p))
        (List.map (fun p => (fst p, subst_lt_in_tm var replacement (snd p))) obs) =
      existsb (fun p => has_rt_cap (snd p)) obs));
    go_traverse.
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

(* The Forall2-aware induction principle `typing_ind_forall2` now lives  *)
(* in core/Typing.v, derived from the generated mutual scheme            *)
(* `typing_mut_ind` (see the `typings`/`typing_ops` mutual block there). *)


Lemma InsTmAt_push_match_bound : forall n Delta c G G',
  InsTmAt c G G' -> InsTmAt c (push_match_bound n Delta G) (push_match_bound n Delta G').
Proof.
  induction n as [|n IH]; intros Delta c G G' H; simpl.
  - exact H.
  - apply InsTmAt_lt. apply IH. exact H.
Qed.

Lemma InsTmAt_push_ty_vars : forall n B c G G',
  InsTmAt c G G' -> InsTmAt c (push_ty_vars n B G) (push_ty_vars n B G').
Proof.
  induction n as [|n IH]; intros B c G G' H; simpl.
  - exact H.
  - apply IH. apply InsTmAt_ty. exact H.
Qed.


Lemma InsTy_push_match_bound : forall n Delta c G G',
  InsTy c G G' -> InsTy c (push_match_bound n Delta G) (push_match_bound n Delta G').
Proof.
  induction n as [|n IH]; intros Delta c G G' H; simpl.
  - exact H.
  - apply InsTy_lt. apply IH. exact H.
Qed.

(* ================================================================== *)
(* Stability of the [any_at_free] bound under weakening               *)
(*                                                                    *)
(* The op-body contexts of T_Cap/T_Handle push type binders bounded   *)
(* by [any_at_free], so the weakening lemmas must show that inserting *)
(* a binder ([InsTm]/[InsTy]/[InsLt]) leaves those pushed bounds      *)
(* untouched: shifting [any_at_free] is the identity.                 *)
(* ================================================================== *)

Lemma shift_ty_any_at_free : forall c, shift_ty 1 c any_at_free = any_at_free.
Proof. intros c. reflexivity. Qed.

Lemma shift_lt_any_at_free : forall c, shift_lt_in_ty 1 c any_at_free = any_at_free.
Proof. intros c. reflexivity. Qed.


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


(* Map form: target is [fold_right bind_tm G' (map (shift_lt_in_ty 1 c) *)
(* rhos)], matching the reconstructed yes-branch context of typing_InsLt.*)
Lemma InsLt_fold_bind_tm_map : forall rhos c G G',
  InsLt c G G' ->
  InsLt c
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G'
       (List.map (shift_lt_in_ty 1 c) rhos)).
Proof.
  induction rhos as [|rho rhos IH]; intros c G G' H; simpl.
  - exact H.
  - apply InsLt_tm. apply IH. exact H.
Qed.


Lemma typings_InsTmAt : forall Γ vs rhos,
  Forall2 (fun v rho => forall c G', InsTmAt c Γ G' -> G' ⊢ₜ shift_tm 1 c v : rho) vs rhos ->
  forall c G', InsTmAt c Γ G' ->
  typings G' (List.map (shift_tm 1 c) vs) rhos.
Proof.
  intros Γ vs rhos H. induction H; intros c G' HIns; simpl.
  - constructor.
  - constructor.
    + apply H. exact HIns.
    + apply IHForall2. exact HIns.
Qed.

Lemma typings_InsTy : forall Γ vs rhos,
  Forall2 (fun v rho => forall c G', InsTy c Γ G' -> G' ⊢ₜ shift_ty_in_tm 1 c v : shift_ty 1 c rho) vs rhos ->
  forall c G', InsTy c Γ G' ->
  typings G' (List.map (shift_ty_in_tm 1 c) vs) (List.map (shift_ty 1 c) rhos).
Proof.
  intros Γ vs rhos H. induction H; intros c G' HIns; simpl.
  - constructor.
  - constructor.
    + apply H. exact HIns.
    + apply IHForall2. exact HIns.
Qed.

Lemma typings_InsLt : forall Γ vs rhos,
  Forall2 (fun v rho => forall c G', InsLt c Γ G' -> G' ⊢ₜ shift_lt_in_tm 1 c v : shift_lt_in_ty 1 c rho) vs rhos ->
  forall c G', InsLt c Γ G' ->
  typings G' (List.map (shift_lt_in_tm 1 c) vs) (List.map (shift_lt_in_ty 1 c) rhos).
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
  - intros Γ t B U S Ht IHt HwfS Hsub c G' HIns. simpl.
    eapply T_TyApp.
    + apply IHt. exact HIns.
    + eapply ty_wf_InsTm; [exact HwfS|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + apply (sub_InsTm Γ S B Hsub G' (InsTmAt_to_InsTm c Γ G' HIns)).
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
    simpl.    eapply T_Ctor with
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
    + apply (typings_InsTmAt Γ vs rho_fields IHargs c G' HIns).
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
      (Γ' := push_match_bound n_lt Delta G') (eta := eta).
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
      apply InsTmAt_push_match_bound. exact HIns.
    + exact Helim.
    + apply IHno. exact HIns.
  - intros Γ E_tag m Ts op_bodies n_α ops T_R
           Heff HTs HwfTs HwfTR Hfst Hops IHops c G' HIns.
    simpl. rewrite shift_tm_ops_eq_map.
    eapply T_Cap with (n_α := n_α) (ops := ops).
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) E_tag). exact Heff.
    + exact HTs.
    + eapply types_wf_InsTm; [exact HwfTs|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTR|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + rewrite List.map_map. exact Hfst.
    + clear Hops Heff Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IHrest]; simpl.
      * constructor.
      * constructor; [| exact IHrest ].
        apply Hone.
        replace (c + 2) with (S (S c)) by lia.
        apply InsTmAt_tm. apply InsTmAt_tm. apply InsTmAt_push_ty_vars. exact HIns.
  - intros Γ E_tag Ts op_bodies body n_α ops T_B T_R
           Heff HTs HwfTs HwfTB HwfTR Hnolocal Hsub Hfst Hops IHops Hbody IHbody c G' HIns.
    simpl. rewrite shift_tm_ops_eq_map.
    eapply T_Handle with (n_α := n_α) (ops := ops) (T_B := T_B).
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) E_tag). exact Heff.
    + exact HTs.
    + eapply types_wf_InsTm; [exact HwfTs|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTB|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTR|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply sub_free_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact Hnolocal].
    + apply (sub_InsTm Γ T_B T_R Hsub G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + rewrite List.map_map. exact Hfst.
    + clear Hops Heff Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IHrest]; simpl.
      * constructor.
      * constructor; [| exact IHrest ].
        apply Hone.
        replace (c + 2) with (S (S c)) by lia.
        apply InsTmAt_tm. apply InsTmAt_tm. apply InsTmAt_push_ty_vars. exact HIns.
    + apply IHbody. apply InsTmAt_tm. exact HIns.
  - intros Γ recv op arg E_tag Delta Ts Ss n_α ops n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hnth HTs HSs HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg c G' HIns.
    simpl.
    eapply T_Perform with (n_α := n_α) (ops := ops) (n_β := n_β) (sig := sig)
      (ret := ret) (sig_inst := sig_inst) (ret_inst := ret_inst).
    + apply IHrecv. exact HIns.
    + rewrite (InsTm_lookup_eff Γ G' (InsTmAt_to_InsTm c Γ G' HIns) E_tag). exact Heff.
    + exact Hnth.
    + exact HTs.
    + exact HSs.
    + eapply types_wf_InsTm; [exact HwfSs|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply sub_free_list_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact HnoSs].
    + exact Hsig.
    + eapply sub_free_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact HnoSig].
    + exact Hret.
    + eapply ty_wf_InsTm; [exact HwfRet|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + apply IHarg. exact HIns.
  - intros Γ m T_B T_R t HwfTB HwfTR Hnolocal Hsub Ht IHt c G' HIns. simpl.
    apply T_HandlerM.
    + eapply ty_wf_InsTm; [exact HwfTB|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply ty_wf_InsTm; [exact HwfTR|]. apply InsTmAt_to_InsTm with (c := c). exact HIns.
    + eapply sub_free_InsTm; [apply InsTmAt_to_InsTm with (c := c); exact HIns|exact Hnolocal].
    + apply (sub_InsTm Γ T_B T_R Hsub G' (InsTmAt_to_InsTm c Γ G' HIns)).
    + apply IHt. exact HIns.
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
  - constructor.
    induction H as [|v vs Hv Hvs IHvs]; simpl.
    + constructor.
    + constructor; [apply (IH v Hv amount cutoff)|exact IHvs].
  - constructor.
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
        (List.map (subst_tm var replacement) ts) = true)
    (fun obs => forall var replacement,
      existsb (fun p => has_rt_cap (snd p)) obs = true ->
      existsb (fun p => has_rt_cap (snd p))
        (List.map (fun p => (fst p, subst_tm var replacement (snd p))) obs)
      = true)).
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
    apply IH. exact Hcap.
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
  - intros E Ts T_B T_R op_bodies body IHops IHb var replacement Hcap. simpl in *.
    rewrite has_rt_cap_ops_eq in Hcap.
    rewrite !has_rt_cap_ops_eq, subst_tm_ops_eq_map.
    apply Bool.orb_true_iff in Hcap as [Hops|Hbody].
    + rewrite (IHops (var + 2) (shift_tm 2 0 replacement) Hops). reflexivity.
    + rewrite (IHb (S var) (shift_tm 1 0 replacement) Hbody).
      destruct (existsb (fun p => has_rt_cap (snd p))
        (List.map (fun p => (fst p, subst_tm (var + 2) (shift_tm 2 0 replacement) (snd p))) op_bodies));
        reflexivity.
  - intros t op Ss A_ret arg IHt IHa var replacement Hcap. simpl in *.
    apply Bool.orb_true_iff in Hcap as [Ht|Ha].
    + rewrite (IHt var replacement Ht). reflexivity.
    + rewrite (IHa var replacement Ha). destruct (has_rt_cap (subst_tm var replacement t)); reflexivity.
  - intros E m Ts T_R op_bodies IHops var replacement Hcap. reflexivity.
  - intros m T_B T_R t IH var replacement Hcap. reflexivity.
  - intros var replacement Hcap. discriminate.
  - intros t ts IHt IHts var replacement Hcap. simpl in *.
    apply Bool.orb_true_iff in Hcap as [Ht|Hts].
    + rewrite (IHt var replacement Ht). reflexivity.
    + rewrite (IHts var replacement Hts). destruct (has_rt_cap (subst_tm var replacement t)); reflexivity.
  - intros var replacement Hcap. discriminate.
  - intros nb ob obs IHob IHobs var replacement Hcap. simpl in *.
    apply Bool.orb_true_iff in Hcap as [Hob|Hobs].
    + rewrite (IHob var replacement Hob). reflexivity.
    + rewrite (IHobs var replacement Hobs).
      destruct (has_rt_cap (subst_tm var replacement ob)); reflexivity.
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
      has_rt_cap v = true /\ In n (List.concat (List.map (free_tm_vars cutoff) ts)))
    (fun obs => forall cutoff n v,
      existsb (fun p => has_rt_cap (snd p)) obs = false ->
      existsb (fun p => has_rt_cap (snd p))
        (List.map (fun p => (fst p, subst_tm (cutoff + n) (shift_tm cutoff 0 v) (snd p))) obs)
        = true ->
      has_rt_cap v = true /\
      In n (List.concat (List.map (fun p => free_tm_vars cutoff (snd p)) obs)))).
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
  - intros E Ts T_B T_R op_bodies body IHops IHb cutoff n v Hcap Hsubst. simpl in *.
    rewrite has_rt_cap_ops_eq in Hcap.
    rewrite has_rt_cap_ops_eq, subst_tm_ops_eq_map in Hsubst.
    rewrite free_tm_vars_ops_eq_concat.
    apply Bool.orb_false_iff in Hcap as [HcapOps HcapBody].
    apply Bool.orb_true_iff in Hsubst as [HsubstOps|HsubstBody].
    + replace (cutoff + n + 2) with (cutoff + 2 + n) in HsubstOps by lia.
      replace (shift_tm 2 0 (shift_tm cutoff 0 v)) with (shift_tm (cutoff + 2) 0 v) in HsubstOps.
      2:{ rewrite shift_tm_fuse. replace (2 + cutoff) with (cutoff + 2) by lia. reflexivity. }
      destruct (IHops (cutoff + 2) n v HcapOps HsubstOps) as [Hv Hin]. split; [exact Hv|].
      apply in_or_app. left. exact Hin.
    + replace (S (cutoff + n)) with (S cutoff + n) in HsubstBody by lia.
      replace (shift_tm 1 0 (shift_tm cutoff 0 v)) with (shift_tm (S cutoff) 0 v) in HsubstBody.
      2:{ rewrite shift_tm_fuse. replace (1 + cutoff) with (S cutoff) by lia. reflexivity. }
      destruct (IHb (S cutoff) n v HcapBody HsubstBody) as [Hv Hin]. split; [exact Hv|].
      apply in_or_app. right. exact Hin.
  - intros t op Ss A_ret arg IHt IHa cutoff n v Hcap Hsubst. simpl in *.
    apply Bool.orb_false_iff in Hcap as [HcapT HcapA].
    apply Bool.orb_true_iff in Hsubst as [HsubstT|HsubstA].
    + destruct (IHt cutoff n v HcapT HsubstT) as [Hv Hin]. split; [exact Hv|].
      apply in_or_app. left. exact Hin.
    + destruct (IHa cutoff n v HcapA HsubstA) as [Hv Hin]. split; [exact Hv|].
      apply in_or_app. right. exact Hin.
  - intros E m Ts T_R op_bodies IHops cutoff n v Hcap. simpl in Hcap. discriminate Hcap.
  - intros m T_B T_R t IH cutoff n v Hcap. simpl in Hcap. discriminate Hcap.
  - intros cutoff n v _ Hsubst. simpl in Hsubst. discriminate Hsubst.
  - intros t ts IHt IHts cutoff n v Hcap Hsubst. simpl in *.
    apply Bool.orb_false_iff in Hcap as [HcapT HcapTs].
    apply Bool.orb_true_iff in Hsubst as [HsubstT|HsubstTs].
    + destruct (IHt cutoff n v HcapT HsubstT) as [Hv Hin]. split; [exact Hv|].
      rewrite in_app_iff. left. exact Hin.
    + destruct (IHts cutoff n v HcapTs HsubstTs) as [Hv Hin]. split; [exact Hv|].
      rewrite in_app_iff. right. exact Hin.
  - intros cutoff n v _ Hsubst. simpl in Hsubst. discriminate Hsubst.
  - intros nb ob obs IHob IHobs cutoff n v Hcap Hsubst. simpl in *.
    apply Bool.orb_false_iff in Hcap as [HcapOb HcapObs].
    apply Bool.orb_true_iff in Hsubst as [HsubstOb|HsubstObs].
    + destruct (IHob cutoff n v HcapOb HsubstOb) as [Hv Hin]. split; [exact Hv|].
      rewrite in_app_iff. left. exact Hin.
    + destruct (IHobs cutoff n v HcapObs HsubstObs) as [Hv Hin]. split; [exact Hv|].
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
      subst_tm_fv n (List.concat (List.map (free_tm_vars cutoff) ts)))
    (fun obs => forall cutoff n v,
      free_tm_vars 0 v = [] ->
      List.concat (List.map (fun p => free_tm_vars cutoff (snd p))
        (List.map (fun p => (fst p, subst_tm (cutoff + n) (shift_tm cutoff 0 v) (snd p))) obs)) =
      subst_tm_fv n
        (List.concat (List.map (fun p => free_tm_vars cutoff (snd p)) obs)))).
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
  - intros E Ts T_B T_R op_bodies body IHops IHb cutoff n v Hfree. simpl.
    rewrite subst_tm_ops_eq_map, !free_tm_vars_ops_eq_concat.
    replace (cutoff + n + 2) with (cutoff + 2 + n) by lia.
    replace (shift_tm 2 0 (shift_tm cutoff 0 v)) with (shift_tm (cutoff + 2) 0 v).
    2:{ rewrite shift_tm_fuse. replace (2 + cutoff) with (cutoff + 2) by lia. reflexivity. }
    rewrite IHops.
    2:{ exact Hfree. }
    replace (S (cutoff + n)) with (S cutoff + n) by lia.
    replace (shift_tm 1 0 (shift_tm cutoff 0 v)) with (shift_tm (S cutoff) 0 v).
    2:{ rewrite shift_tm_fuse. replace (1 + cutoff) with (S cutoff) by lia. reflexivity. }
    rewrite IHb by exact Hfree.
    rewrite subst_tm_fv_app. reflexivity.
  - intros t op Ss A_ret arg IHt IHa cutoff n v Hfree. simpl.
    rewrite IHt by exact Hfree. rewrite IHa by exact Hfree.
    rewrite subst_tm_fv_app. reflexivity.
  - intros E m Ts T_R op_bodies IHops cutoff n v Hfree. simpl.
    rewrite subst_tm_ops_eq_map, !free_tm_vars_ops_eq_concat.
    replace (cutoff + n + 2) with (cutoff + 2 + n) by lia.
    replace (shift_tm 2 0 (shift_tm cutoff 0 v)) with (shift_tm (cutoff + 2) 0 v).
    2:{ rewrite shift_tm_fuse. replace (2 + cutoff) with (cutoff + 2) by lia. reflexivity. }
    apply IHops. exact Hfree.
  - intros m T_B T_R t IH cutoff n v Hfree. simpl. apply IH. exact Hfree.
  - intros cutoff n v Hfree. reflexivity.
  - intros t ts IHt IHts cutoff n v Hfree. simpl.
    rewrite IHt by exact Hfree. rewrite IHts by exact Hfree.
    rewrite subst_tm_fv_app. reflexivity.
  - intros cutoff n v Hfree. reflexivity.
  - intros nb ob obs IHob IHobs cutoff n v Hfree. simpl.
    rewrite IHob by exact Hfree. rewrite IHobs by exact Hfree.
    rewrite subst_tm_fv_app. reflexivity.
Qed.


(* ================================================================== *)
(* subst_lt_in_ty head-constructor rewrite equations                  *)
(* ================================================================== *)
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

(* ================================================================== *)
(* subst_lt / shift_lt : cancel and commute                           *)
(* ================================================================== *)

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
#[export] Hint Rewrite subst_lt_shift_cancel : subst_norm.

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

(* [push_match_bound] is STABLE under lt-insertion (UNLIKE [push_lt_vars],    *)
(* whose closed sibling needs lt_lt_closed Delta): the per-level bound  *)
(* [shift_lt j 0 Delta] shifts uniformly because [InsLt_lt]'s bound     *)
(* shift commutes with the level shift ([shift_lt_lift_many_swap]).     *)
(* Inserting at cutoff c turns the bound Delta into [shift_lt 1 c Delta]*)
(* — no closedness assumption.                                          *)
Lemma InsLt_push_match_bound : forall k Delta c G G',
  InsLt c G G' ->
  InsLt (k + c) (push_match_bound k Delta G) (push_match_bound k (shift_lt 1 c Delta) G').
Proof.
  induction k as [|k IH]; intros Delta c G G' H; simpl.
  - exact H.
  - replace (shift_lt k 0 (shift_lt 1 c Delta))
      with (shift_lt 1 (k + c) (shift_lt k 0 Delta)).
    2:{ replace (k + c) with (c + k) by lia. apply shift_lt_lift_many_swap. }
    apply InsLt_lt. apply IH. exact H.
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


Lemma shift_ty_subst_lt_in_ty_commute : forall T a1 c1 n R,
  shift_ty a1 c1 (subst_lt_in_ty n R T)
  = subst_lt_in_ty n R (shift_ty a1 c1 T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall a1 c1 n R,
       shift_ty a1 c1 (subst_lt_in_ty n R T) = subst_lt_in_ty n R (shift_ty a1 c1 T))
    (fun Ts => forall a1 c1 n R,
       List.map (shift_ty a1 c1) (List.map (subst_lt_in_ty n R) Ts)
       = List.map (subst_lt_in_ty n R) (List.map (shift_ty a1 c1) Ts)));
    go_traverse.
Qed.
