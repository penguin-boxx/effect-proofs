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
Require Import STSubstTy.
Require Import STSubstTm.
Require Import STEvalCtx.

(* ================================================================== *)
(* typing_SubstTy : type-substitution preserves typing.               *)
(* Discharges `subst_ty_in_tm_lemma` (it is the depth-0 instance with *)
(* `SubstTy_here`).  Mirrors `typing_InsTy`, swapping shift→subst.    *)
(* ================================================================== *)

(* ---- schema-level type substitution ---- *)
(* A ctor schema's fields/result live under n_lt lifetime binders then  *)
(* n_ty type binders, so the replacement type must be lifted past both. *)
Definition subst_ty_ctor_sig (n : nat) (Sb : type)
    (sig : nat * nat * list type * type) : nat * nat * list type * type :=
  let '(n_lt, n_ty, fields, result) := sig in
  let Sb' := shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb) in
  (n_lt, n_ty,
   List.map (subst_ty (n_ty + n) Sb') fields,
   subst_ty (n_ty + n) Sb' result).

(* An effect schema's sig/ret live under n_α + n_β type binders only.   *)
Definition subst_ty_eff_sig (n : nat) (Sb : type)
    (sig : nat * nat * type * type) : nat * nat * type * type :=
  let '(n_α, n_β, sig_ty, ret_ty) := sig in
  let Sb' := shift_ty (n_α + n_β) 0 Sb in
  (n_α, n_β,
   subst_ty (n_α + n_β + n) Sb' sig_ty,
   subst_ty (n_α + n_β + n) Sb' ret_ty).

Lemma subst_ty_eff_sig_shift_cancel : forall Sb sig,
  subst_ty_eff_sig 0 Sb (shift_ty_eff_sig 1 0 sig) = sig.
Proof.
  intros Sb (((n_α, n_β), sig_ty), ret_ty).
  unfold subst_ty_eff_sig, shift_ty_eff_sig. simpl.
  rewrite !subst_ty_shift_cancel. reflexivity.
Qed.

Lemma subst_ty_ctor_sig_shift_cancel : forall Sb sig,
  subst_ty_ctor_sig 0 Sb (shift_ty_ctor_sig 1 0 sig) = sig.
Proof.
  intros Sb (((n_lt, n_ty), fields), result).
  unfold subst_ty_ctor_sig, shift_ty_ctor_sig. simpl.
  assert (Hfields :
    List.map (subst_ty (n_ty + 0) (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb)))
      (List.map (shift_ty 1 (n_ty + 0)) fields) = fields).
  { induction fields as [|T fields IH]; simpl.
    - reflexivity.
    - rewrite subst_ty_shift_cancel. f_equal. exact IH. }
  rewrite Hfields, subst_ty_shift_cancel. reflexivity.
Qed.

Lemma shift_ty_eff_sig_subst_ty_eff_sig_comm0 : forall n Sb sig,
  shift_ty_eff_sig 1 0 (subst_ty_eff_sig n Sb sig) =
  subst_ty_eff_sig (S n) (shift_ty 1 0 Sb) (shift_ty_eff_sig 1 0 sig).
Proof.
  intros n Sb (((n_α, n_β), sig_ty), ret_ty).
  unfold subst_ty_eff_sig, shift_ty_eff_sig. simpl.
  assert (Hc : forall T,
    shift_ty 1 (n_α + n_β + 0) (subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) T)
    = subst_ty (n_α + n_β + S n) (shift_ty (n_α + n_β) 0 (shift_ty 1 0 Sb))
        (shift_ty 1 (n_α + n_β + 0) T)).
  { intro T. rewrite shift_ty_subst_ty_comm by lia.
    replace (S (n_α + n_β + n)) with (n_α + n_β + S n) by lia.
    f_equal. rewrite <- shift_ty_lift_shift. reflexivity. }
  rewrite !Hc. reflexivity.
Qed.

Lemma shift_ty_ctor_sig_subst_ty_ctor_sig_comm0 : forall n Sb sig,
  shift_ty_ctor_sig 1 0 (subst_ty_ctor_sig n Sb sig) =
  subst_ty_ctor_sig (S n) (shift_ty 1 0 Sb) (shift_ty_ctor_sig 1 0 sig).
Proof.
  intros n Sb (((n_lt, n_ty), fields), result).
  unfold subst_ty_ctor_sig, shift_ty_ctor_sig. simpl.
  assert (Hc : forall T,
    shift_ty 1 (n_ty + 0)
      (subst_ty (n_ty + n) (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb)) T)
    = subst_ty (n_ty + S n)
        (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 (shift_ty 1 0 Sb)))
        (shift_ty 1 (n_ty + 0) T)).
  { intro T. rewrite shift_ty_subst_ty_comm by lia.
    replace (S (n_ty + n)) with (n_ty + S n) by lia.
    f_equal. rewrite shift_ty_shift_lt_in_ty_commute.
    f_equal. rewrite <- shift_ty_lift_shift. reflexivity. }
  rewrite !List.map_map.
  f_equal; [f_equal | exact (Hc result)].
  apply List.map_ext. exact Hc.
Qed.

Lemma shift_lt_eff_sig_subst_ty_eff_sig_comm : forall n Sb sig,
  shift_lt_eff_sig 1 0 (subst_ty_eff_sig n Sb sig) =
  subst_ty_eff_sig n (shift_lt_in_ty 1 0 Sb) (shift_lt_eff_sig 1 0 sig).
Proof.
  intros n Sb (((n_α, n_β), sig_ty), ret_ty).
  unfold subst_ty_eff_sig, shift_lt_eff_sig. simpl.
  assert (Hc : forall T,
    shift_lt_in_ty 1 0 (subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) T)
    = subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 (shift_lt_in_ty 1 0 Sb))
        (shift_lt_in_ty 1 0 T)).
  { intro T. rewrite shift_lt_in_ty_subst_ty_comm. f_equal.
    rewrite shift_ty_shift_lt_in_ty_commute. reflexivity. }
  rewrite !Hc. reflexivity.
Qed.

Lemma shift_lt_ctor_sig_subst_ty_ctor_sig_comm : forall n Sb sig,
  shift_lt_ctor_sig 1 0 (subst_ty_ctor_sig n Sb sig) =
  subst_ty_ctor_sig n (shift_lt_in_ty 1 0 Sb) (shift_lt_ctor_sig 1 0 sig).
Proof.
  intros n Sb (((n_lt, n_ty), fields), result).
  unfold subst_ty_ctor_sig, shift_lt_ctor_sig. simpl.
  assert (Hc : forall T,
    shift_lt_in_ty 1 (n_lt + 0)
      (subst_ty (n_ty + n) (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb)) T)
    = subst_ty (n_ty + n)
        (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 (shift_lt_in_ty 1 0 Sb)))
        (shift_lt_in_ty 1 (n_lt + 0) T)).
  { intro T. rewrite shift_lt_in_ty_subst_ty_comm. f_equal.
    replace (n_lt + 0) with (0 + n_lt) by lia.
    rewrite shift_lt_in_ty_lift_many_swap.
    f_equal. rewrite shift_ty_shift_lt_in_ty_commute. reflexivity. }
  rewrite !List.map_map.
  f_equal; [f_equal | exact (Hc result)].
  apply List.map_ext. exact Hc.
Qed.

(* ---- SubstTy lookups for the remaining context entry kinds ---- *)
Lemma SubstTy_lookup_tm : forall Sb n G G', SubstTy Sb n G G' ->
  forall x, ctx_lookup_tm G' x = option_map (subst_ty n Sb) (ctx_lookup_tm G x).
Proof.
  intros Sb n G G' H. induction H; intro x.
  - simpl ctx_lookup_tm.
    destruct (ctx_lookup_tm Gamma x) as [T|]; simpl;
      [rewrite subst_ty_shift_cancel|]; reflexivity.
  - simpl ctx_lookup_tm. rewrite IHSubstTy.
    destruct (ctx_lookup_tm G x) as [T|]; simpl;
      [rewrite shift_ty_subst_ty_comm0|]; reflexivity.
  - simpl ctx_lookup_tm. rewrite IHSubstTy.
    destruct (ctx_lookup_tm G x) as [T|]; simpl;
      [rewrite shift_lt_in_ty_subst_ty_comm0|]; reflexivity.
  - destruct x as [|x']; simpl ctx_lookup_tm.
    + reflexivity.
    + apply IHSubstTy.
Qed.

Lemma SubstTy_lookup_ctor : forall Sb n G G', SubstTy Sb n G G' ->
  forall K, ctx_lookup_ctor G' K
            = option_map (subst_ty_ctor_sig n Sb) (ctx_lookup_ctor G K).
Proof.
  intros Sb n G G' H. induction H; intro K.
  - simpl ctx_lookup_ctor.
    destruct (ctx_lookup_ctor Gamma K) as [sig|]; simpl;
      [rewrite subst_ty_ctor_sig_shift_cancel|]; reflexivity.
  - simpl ctx_lookup_ctor. rewrite IHSubstTy.
    destruct (ctx_lookup_ctor G K) as [sig|] eqn:E; cbn [option_map].
    + rewrite shift_ty_ctor_sig_subst_ty_ctor_sig_comm0. reflexivity.
    + reflexivity.
  - simpl ctx_lookup_ctor. rewrite IHSubstTy.
    destruct (ctx_lookup_ctor G K) as [sig|] eqn:E; cbn [option_map].
    + rewrite shift_lt_ctor_sig_subst_ty_ctor_sig_comm. reflexivity.
    + reflexivity.
  - simpl ctx_lookup_ctor. apply IHSubstTy.
Qed.

Lemma SubstTy_lookup_eff : forall Sb n G G', SubstTy Sb n G G' ->
  forall E, ctx_lookup_eff G' E
            = option_map (subst_ty_eff_sig n Sb) (ctx_lookup_eff G E).
Proof.
  intros Sb n G G' H. induction H; intro E.
  - simpl ctx_lookup_eff.
    destruct (ctx_lookup_eff Gamma E) as [sig|]; simpl;
      [rewrite subst_ty_eff_sig_shift_cancel|]; reflexivity.
  - simpl ctx_lookup_eff. rewrite IHSubstTy.
    destruct (ctx_lookup_eff G E) as [sig|] eqn:Ef; cbn [option_map].
    + rewrite shift_ty_eff_sig_subst_ty_eff_sig_comm0. reflexivity.
    + reflexivity.
  - simpl ctx_lookup_eff. rewrite IHSubstTy.
    destruct (ctx_lookup_eff G E) as [sig|] eqn:Ef; cbn [option_map].
    + rewrite shift_lt_eff_sig_subst_ty_eff_sig_comm. reflexivity.
    + reflexivity.
  - simpl ctx_lookup_eff. apply IHSubstTy.
Qed.

(* ---- type-substitution algebra used by typing_SubstTy ---- *)
Lemma subst_ty_subst_ty_comm : forall T c n Sb U,
  c <= n ->
  subst_ty c (subst_ty n Sb U) (subst_ty (S n) (shift_ty 1 c Sb) T) =
  subst_ty n Sb (subst_ty c U T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall c n Sb U,
      c <= n ->
      subst_ty c (subst_ty n Sb U) (subst_ty (S n) (shift_ty 1 c Sb) T) =
      subst_ty n Sb (subst_ty c U T))
    (fun Ts => forall c n Sb U,
      c <= n ->
      List.map (subst_ty c (subst_ty n Sb U))
        (List.map (subst_ty (S n) (shift_ty 1 c Sb)) Ts) =
      List.map (subst_ty n Sb) (List.map (subst_ty c U) Ts))).
  - intros m c n Sb U Hle.
    destruct (Nat.eqb_spec m (S n)) as [HeqSn|HneSn].
    + subst m.
      replace (subst_ty (S n) (shift_ty 1 c Sb) (type_var (S n)))
        with (shift_ty 1 c Sb).
      2:{ rewrite subst_ty_var_eq, Nat.eqb_refl. reflexivity. }
      rewrite subst_ty_shift_cancel.
      replace (subst_ty c U (type_var (S n))) with (type_var n).
      2:{ rewrite subst_ty_var_eq.
          destruct (Nat.eqb_spec (S n) c); [lia|].
          destruct (Nat.ltb_spec c (S n)); [f_equal; lia|lia]. }
      rewrite subst_ty_var_eq, Nat.eqb_refl. reflexivity.
    + destruct (Nat.ltb_spec (S n) m) as [Hgt|Hngt].
      * replace (subst_ty (S n) (shift_ty 1 c Sb) (type_var m))
          with (type_var (pred m)).
        2:{ rewrite subst_ty_var_eq.
            destruct (Nat.eqb_spec m (S n)); [lia|].
            destruct (Nat.ltb_spec (S n) m); [reflexivity|lia]. }
        replace (subst_ty c U (type_var m)) with (type_var (pred m)).
        2:{ rewrite subst_ty_var_eq.
            destruct (Nat.eqb_spec m c); [lia|].
            destruct (Nat.ltb_spec c m); [reflexivity|lia]. }
        replace (subst_ty c (subst_ty n Sb U) (type_var (pred m)))
          with (type_var (pred (pred m))).
        2:{ rewrite subst_ty_var_eq.
            destruct (Nat.eqb_spec (pred m) c); [lia|].
            destruct (Nat.ltb_spec c (pred m)); [reflexivity|lia]. }
        replace (subst_ty n Sb (type_var (pred m)))
          with (type_var (pred (pred m))).
        2:{ rewrite subst_ty_var_eq.
            destruct (Nat.eqb_spec (pred m) n); [lia|].
            destruct (Nat.ltb_spec n (pred m)); [reflexivity|lia]. }
        reflexivity.
      * assert (Hmle : m <= n) by lia.
        destruct (Nat.eqb_spec m c) as [Heqc|Hneqc].
        -- subst m.
           replace (subst_ty (S n) (shift_ty 1 c Sb) (type_var c))
             with (type_var c).
           2:{ rewrite subst_ty_var_eq.
               destruct (Nat.eqb_spec c (S n)); [lia|].
               destruct (Nat.ltb_spec (S n) c); [lia|reflexivity]. }
           rewrite subst_ty_var_eq, Nat.eqb_refl.
           rewrite subst_ty_var_eq, Nat.eqb_refl. reflexivity.
        -- destruct (Nat.ltb_spec c m) as [Hclt|Hcge].
           ++ replace (subst_ty (S n) (shift_ty 1 c Sb) (type_var m))
                with (type_var m).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec m (S n)); [lia|].
                  destruct (Nat.ltb_spec (S n) m); [lia|reflexivity]. }
              replace (subst_ty c U (type_var m)) with (type_var (pred m)).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec m c); [lia|].
                  destruct (Nat.ltb_spec c m); [reflexivity|lia]. }
              replace (subst_ty c (subst_ty n Sb U) (type_var m))
                with (type_var (pred m)).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec m c); [lia|].
                  destruct (Nat.ltb_spec c m); [reflexivity|lia]. }
              replace (subst_ty n Sb (type_var (pred m)))
                with (type_var (pred m)).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec (pred m) n); [lia|].
                  destruct (Nat.ltb_spec n (pred m)); [lia|reflexivity]. }
              reflexivity.
           ++ replace (subst_ty (S n) (shift_ty 1 c Sb) (type_var m))
                with (type_var m).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec m (S n)); [lia|].
                  destruct (Nat.ltb_spec (S n) m); [lia|reflexivity]. }
              replace (subst_ty c U (type_var m)) with (type_var m).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec m c); [lia|].
                  destruct (Nat.ltb_spec c m); [lia|reflexivity]. }
              replace (subst_ty c (subst_ty n Sb U) (type_var m))
                with (type_var m).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec m c); [lia|].
                  destruct (Nat.ltb_spec c m); [lia|reflexivity]. }
              replace (subst_ty n Sb (type_var m)) with (type_var m).
              2:{ rewrite subst_ty_var_eq.
                  destruct (Nat.eqb_spec m n); [lia|].
                  destruct (Nat.ltb_spec n m); [lia|reflexivity]. }
              reflexivity.
  - intros A l B HA HB c n Sb U Hle.
    rewrite subst_ty_fun_eq, subst_ty_fun_eq, subst_ty_fun_eq, subst_ty_fun_eq.
    rewrite HA by exact Hle. rewrite HB by exact Hle. reflexivity.
  - intros K l Ts HTs c n Sb U Hle.
    rewrite subst_ty_ctor_eq, subst_ty_ctor_eq, subst_ty_ctor_eq, subst_ty_ctor_eq.
    f_equal. apply HTs. exact Hle.
  - intros A HA c n Sb U Hle.
    rewrite subst_ty_ltall_eq, subst_ty_ltall_eq, subst_ty_ltall_eq, subst_ty_ltall_eq.
    f_equal.
    replace (shift_lt_in_ty 1 0 (subst_ty n Sb U))
      with (subst_ty n (shift_lt_in_ty 1 0 Sb) (shift_lt_in_ty 1 0 U)).
    2:{ symmetry. apply shift_lt_in_ty_subst_ty_comm0. }
    replace (shift_lt_in_ty 1 0 (shift_ty 1 c Sb))
      with (shift_ty 1 c (shift_lt_in_ty 1 0 Sb)).
    2:{ rewrite shift_ty_shift_lt_in_ty_commute. reflexivity. }
    rewrite HA by exact Hle. reflexivity.
  - intros B A HB HA c n Sb U Hle.
    rewrite subst_ty_tyall_eq, subst_ty_tyall_eq, subst_ty_tyall_eq, subst_ty_tyall_eq.
    rewrite HB by exact Hle. f_equal.
    replace (shift_ty 1 0 (subst_ty n Sb U))
      with (subst_ty (S n) (shift_ty 1 0 Sb) (shift_ty 1 0 U)).
    2:{ symmetry. apply shift_ty_subst_ty_comm0. }
    replace (shift_ty 1 0 (shift_ty 1 c Sb))
      with (shift_ty 1 (S c) (shift_ty 1 0 Sb)).
    2:{ symmetry. apply shift_ty_swap_0. }
    rewrite HA by lia. reflexivity.
  - intros c n Sb U Hle. reflexivity.
  - intros A Ts HA HTs c n Sb U Hle.
    cbn [List.map]. rewrite HA by exact Hle. f_equal. apply HTs. exact Hle.
Qed.

Lemma subst_ty_subst_ty_comm0 : forall T n Sb U,
  subst_ty 0 (subst_ty n Sb U) (subst_ty (S n) (shift_ty 1 0 Sb) T) =
  subst_ty n Sb (subst_ty 0 U T).
Proof.
  intros T n Sb U. apply subst_ty_subst_ty_comm. lia.
Qed.

Lemma shift_ty_many_subst_ty_comm0 : forall k n Sb U,
  subst_ty (k + n) (shift_ty k 0 Sb) (shift_ty k 0 U) =
  shift_ty k 0 (subst_ty n Sb U).
Proof.
  induction k as [|k IH]; intros n Sb U.
  - rewrite !shift_ty_zero. simpl. reflexivity.
  - replace (S k + n) with (S (k + n)) by lia.
    replace (shift_ty (S k) 0 Sb) with (shift_ty 1 0 (shift_ty k 0 Sb)).
    2:{ rewrite shift_ty_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    replace (shift_ty (S k) 0 U) with (shift_ty 1 0 (shift_ty k 0 U)).
    2:{ rewrite shift_ty_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    rewrite <- shift_ty_subst_ty_comm0.
    rewrite IH. rewrite shift_ty_fuse.
    replace (1 + k) with (S k) by lia. reflexivity.
Qed.

Lemma inst_ty_vars_subst_ty : forall k Ts T n Sb,
  List.length Ts = k ->
  inst_ty_vars k (List.map (subst_ty n Sb) Ts)
    (subst_ty (k + n) (shift_ty k 0 Sb) T) =
  subst_ty n Sb (inst_ty_vars k Ts T).
Proof.
  induction k as [|k IH]; intros Ts T n Sb Hlen.
  - destruct Ts as [|U rest]; [|simpl in Hlen; discriminate].
    rewrite shift_ty_zero. simpl. replace (0 + n) with n by lia. reflexivity.
  - destruct Ts as [|U rest]; [simpl in Hlen; discriminate|].
    simpl in Hlen. injection Hlen as Hlen.
    simpl.
    rewrite <- shift_ty_many_subst_ty_comm0.
    replace (S k + n) with (S (k + n)) by lia.
    replace (shift_ty (S k) 0 Sb) with (shift_ty 1 0 (shift_ty k 0 Sb)).
    2:{ rewrite shift_ty_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    rewrite subst_ty_subst_ty_comm0.
    rewrite IH by exact Hlen. reflexivity.
Qed.





Lemma inst_op_alpha_subst_ty : forall n_alpha Ts n_beta T n Sb,
  List.length Ts = n_alpha ->
  inst_op_alpha n_alpha (List.map (subst_ty n Sb) Ts) n_beta
    (subst_ty (n_alpha + n_beta + n) (shift_ty (n_alpha + n_beta) 0 Sb) T) =
  subst_ty (n_beta + n) (shift_ty n_beta 0 Sb)
    (inst_op_alpha n_alpha Ts n_beta T).
Proof.
  intros n_alpha Ts n_beta T n Sb Hlen. unfold inst_op_alpha.
  replace (List.map (shift_ty n_beta 0) (List.map (subst_ty n Sb) Ts)) with
    (List.map (subst_ty (n_beta + n) (shift_ty n_beta 0 Sb))
      (List.map (shift_ty n_beta 0) Ts)).
  - replace (n_alpha + n_beta + n) with (n_alpha + (n_beta + n)) by lia.
    replace (shift_ty (n_alpha + n_beta) 0 Sb)
      with (shift_ty n_alpha 0 (shift_ty n_beta 0 Sb)).
    2:{ rewrite shift_ty_fuse. reflexivity. }
    rewrite inst_ty_vars_subst_ty by (rewrite List.length_map; exact Hlen).
    reflexivity.
  - rewrite !List.map_map. apply List.map_ext. intro U.
    rewrite shift_ty_many_subst_ty_comm0. reflexivity.
Qed.

Lemma inst_op_arg_subst_ty : forall n_alpha Ts n_beta Ss T n Sb,
  List.length Ts = n_alpha ->
  List.length Ss = n_beta ->
  inst_op_arg n_alpha (List.map (subst_ty n Sb) Ts)
              n_beta (List.map (subst_ty n Sb) Ss)
              (subst_ty (n_alpha + n_beta + n)
                (shift_ty (n_alpha + n_beta) 0 Sb) T) =
  subst_ty n Sb (inst_op_arg n_alpha Ts n_beta Ss T).
Proof.
  intros n_alpha Ts n_beta Ss T n Sb HlenTs HlenSs.
  unfold inst_op_arg.
  rewrite inst_op_alpha_subst_ty by exact HlenTs.
  rewrite inst_ty_vars_subst_ty by exact HlenSs.
  reflexivity.
Qed.

Lemma shift_lt_in_ty_subst_ty_comm_many : forall T k c n Sb,
  shift_lt_in_ty k c (subst_ty n Sb T) =
  subst_ty n (shift_lt_in_ty k c Sb) (shift_lt_in_ty k c T).
Proof.
  intros T k. revert T.
  induction k as [|k IH]; intros T c n Sb.
  - rewrite !shift_lt_in_ty_zero. reflexivity.
  - replace (shift_lt_in_ty (S k) c (subst_ty n Sb T))
      with (shift_lt_in_ty 1 c (shift_lt_in_ty k c (subst_ty n Sb T))).
    2:{ rewrite shift_lt_in_ty_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    rewrite IH.
    rewrite shift_lt_in_ty_subst_ty_comm.
    rewrite shift_lt_in_ty_fuse.
    rewrite shift_lt_in_ty_fuse.
    replace (1 + k) with (S k) by lia. reflexivity.
Qed.

Lemma shift_lt_lift_lower : forall l off d k,
  d <= k ->
  shift_lt 1 (off + d) (shift_lt k off l) = shift_lt (S k) off l.
Proof.
  intros l. induction l as [x| | |l1 IH1 l2 IH2]; intros off d k Hle; simpl.
  - destruct (Nat.leb off x) eqn:Hx.
    + apply Nat.leb_le in Hx.
      rewrite (proj2 (Nat.leb_le (off + d) (x + k))) by lia.
      f_equal. lia.
    + apply Nat.leb_gt in Hx.
      rewrite (proj2 (Nat.leb_gt (off + d) x)) by lia.
      reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1 by exact Hle. rewrite IH2 by exact Hle. reflexivity.
Qed.

Lemma shift_lt_in_ty_lift_lower : forall T off d k,
  d <= k ->
  shift_lt_in_ty 1 (off + d) (shift_lt_in_ty k off T) =
  shift_lt_in_ty (S k) off T.
Proof.
  intros T. apply (type_list_ind
    (fun T => forall off d k,
      d <= k ->
      shift_lt_in_ty 1 (off + d) (shift_lt_in_ty k off T) =
      shift_lt_in_ty (S k) off T)
    (fun Ts => forall off d k,
      d <= k ->
      List.map (shift_lt_in_ty 1 (off + d))
        (List.map (shift_lt_in_ty k off) Ts) =
      List.map (shift_lt_in_ty (S k) off) Ts)).
  - reflexivity.
  - intros A l B HA HB off d k Hle. simpl.
    rewrite HA by exact Hle. rewrite HB by exact Hle.
    rewrite shift_lt_lift_lower by exact Hle. reflexivity.
  - intros K l Ts HTs off d k Hle. simpl.
    rewrite shift_lt_lift_lower by exact Hle. f_equal. apply HTs. exact Hle.
  - intros A HA off d k Hle. simpl.
    replace (S (off + d)) with (S off + d) by lia.
    rewrite HA by exact Hle. reflexivity.
  - intros B A HB HA off d k Hle. simpl.
    rewrite HB by exact Hle. rewrite HA by exact Hle. reflexivity.
  - reflexivity.
  - intros A Ts HA HTs off d k Hle. cbn [List.map].
    rewrite HA by exact Hle. f_equal. apply HTs. exact Hle.
Qed.

Lemma multi_subst_lt_shift_lt_above : forall l cutoff d lts,
  d <= cutoff ->
  multi_subst_lt (S cutoff) lts (shift_lt 1 d l) =
  shift_lt 1 d (multi_subst_lt cutoff lts l).
Proof.
  intros l. induction l as [x| | |l1 IH1 l2 IH2]; intros cutoff d lts Hle; simpl.
  - destruct (Nat.leb d x) eqn:Hshift.
    + apply Nat.leb_le in Hshift.
      destruct (Nat.ltb_spec x cutoff) as [Hbelow|Hge].
      * assert (Hlt1 : (x + 1 <? S cutoff) = true) by (apply Nat.ltb_lt; lia).
        rewrite Hlt1.
        simpl. assert (Hdb : (d <=? x) = true) by (apply Nat.leb_le; lia).
        rewrite Hdb. reflexivity.
      * assert (Hge1 : (x + 1 <? S cutoff) = false) by (apply Nat.ltb_ge; lia).
        assert (Hge0 : (x <? cutoff) = false) by (apply Nat.ltb_ge; lia).
        rewrite Hge1.
        replace (x + 1 - S cutoff) with (x - cutoff) by lia.
        destruct (Nat.ltb_spec (x - cutoff) (List.length lts)) as [Hin|Hout].
        -- assert (Hinb : (x - cutoff <? List.length lts) = true) by (apply Nat.ltb_lt; lia).
            replace d with (0 + d) by lia.
           rewrite shift_lt_lift_lower by exact Hle. reflexivity.
        -- assert (Houtb : (x - cutoff <? List.length lts) = false) by (apply Nat.ltb_ge; lia).
           simpl. assert (Hdb : (d <=? x - List.length lts) = true) by (apply Nat.leb_le; lia).
           rewrite Hdb.
           f_equal. lia.
    + apply Nat.leb_gt in Hshift.
      assert (Hbelow : x < cutoff) by lia.
      assert (Hlt0 : (x <? cutoff) = true) by (apply Nat.ltb_lt; lia).
      assert (Hlt1 : (x <? S cutoff) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hlt0, Hlt1.
      simpl. assert (Hdb : (d <=? x) = false) by (apply Nat.leb_gt; lia).
      rewrite Hdb. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1 by exact Hle. rewrite IH2 by exact Hle. reflexivity.
Qed.

Lemma multi_subst_lt_in_ty_shift_lt_above : forall T cutoff d lts,
  d <= cutoff ->
  multi_subst_lt_in_ty (S cutoff) lts (shift_lt_in_ty 1 d T) =
  shift_lt_in_ty 1 d (multi_subst_lt_in_ty cutoff lts T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall cutoff d lts,
      d <= cutoff ->
      multi_subst_lt_in_ty (S cutoff) lts (shift_lt_in_ty 1 d T) =
      shift_lt_in_ty 1 d (multi_subst_lt_in_ty cutoff lts T))
    (fun Ts => forall cutoff d lts,
      d <= cutoff ->
      List.map (multi_subst_lt_in_ty (S cutoff) lts)
        (List.map (shift_lt_in_ty 1 d) Ts) =
      List.map (shift_lt_in_ty 1 d)
        (List.map (multi_subst_lt_in_ty cutoff lts) Ts))).
  - reflexivity.
  - intros A l B HA HB cutoff d lts Hle. simpl.
    rewrite HA by exact Hle. rewrite HB by exact Hle.
    rewrite multi_subst_lt_shift_lt_above by exact Hle. reflexivity.
  - intros K l Ts HTs cutoff d lts Hle. simpl.
    rewrite multi_subst_lt_shift_lt_above by exact Hle.
    f_equal. apply HTs. exact Hle.
  - intros A HA cutoff d lts Hle. simpl.
    rewrite HA by lia. reflexivity.
  - intros B A HB HA cutoff d lts Hle. simpl.
    rewrite HB by exact Hle. rewrite HA by exact Hle. reflexivity.
  - reflexivity.
  - intros A Ts HA HTs cutoff d lts Hle. cbn [List.map].
    rewrite HA by exact Hle. f_equal. apply HTs. exact Hle.
Qed.

Lemma multi_subst_lt_in_ty_subst_ty : forall T cutoff lts n Sb,
  multi_subst_lt_in_ty cutoff lts (subst_ty n Sb T) =
  subst_ty n (multi_subst_lt_in_ty cutoff lts Sb)
    (multi_subst_lt_in_ty cutoff lts T).
Proof.
  intros T. apply (type_list_ind
    (fun T => forall cutoff lts n Sb,
      multi_subst_lt_in_ty cutoff lts (subst_ty n Sb T) =
      subst_ty n (multi_subst_lt_in_ty cutoff lts Sb)
        (multi_subst_lt_in_ty cutoff lts T))
    (fun Ts => forall cutoff lts n Sb,
      List.map (multi_subst_lt_in_ty cutoff lts) (List.map (subst_ty n Sb) Ts) =
      List.map (subst_ty n (multi_subst_lt_in_ty cutoff lts Sb))
        (List.map (multi_subst_lt_in_ty cutoff lts) Ts))).
  - intros m cutoff lts n Sb. simpl.
    destruct (Nat.eqb m n); destruct (Nat.ltb n m); reflexivity.
  - intros A l B HA HB cutoff lts n Sb. simpl.
    rewrite HA, HB. reflexivity.
  - intros K l Ts HTs cutoff lts n Sb. simpl. f_equal. apply HTs.
  - intros A HA cutoff lts n Sb. simpl. f_equal.
    rewrite HA. f_equal.
    rewrite multi_subst_lt_in_ty_shift_lt_above by lia. reflexivity.
  - intros B A HB HA cutoff lts n Sb. simpl.
    rewrite HB. f_equal. rewrite HA. f_equal.
    rewrite multi_subst_lt_in_ty_shift_ty. reflexivity.
  - intros cutoff lts n Sb. reflexivity.
  - intros A Ts HA HTs cutoff lts n Sb. cbn [List.map].
    rewrite HA. f_equal. apply HTs.
Qed.

Lemma inst_ctor_type_subst_ty : forall n_lt n_ty lts Ts T n Sb,
  List.length lts = n_lt ->
  List.length Ts = n_ty ->
  inst_ctor_type n_lt n_ty lts (List.map (subst_ty n Sb) Ts)
    (subst_ty (n_ty + n) (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb)) T) =
  subst_ty n Sb (inst_ctor_type n_lt n_ty lts Ts T).
Proof.
  intros n_lt n_ty lts Ts T n Sb HlenL HlenT.
  unfold inst_ctor_type, inst_lt_vars.
  replace (List.map (shift_lt_in_ty n_lt 0) (List.map (subst_ty n Sb) Ts))
    with (List.map (subst_ty n (shift_lt_in_ty n_lt 0 Sb))
      (List.map (shift_lt_in_ty n_lt 0) Ts)).
  2:{ rewrite !List.map_map. apply List.map_ext. intro U.
      rewrite shift_lt_in_ty_subst_ty_comm_many. reflexivity. }
  replace (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb))
    with (shift_ty n_ty 0 (shift_lt_in_ty n_lt 0 Sb)).
  2:{ rewrite shift_ty_shift_lt_in_ty_commute. reflexivity. }
  rewrite inst_ty_vars_subst_ty by (rewrite List.length_map; exact HlenT).
  rewrite multi_subst_lt_in_ty_subst_ty.
  rewrite multi_subst_lt_in_ty_shift_lt_cancel0 by exact HlenL.
  reflexivity.
Qed.

(* Well-formedness of shifted type-argument escape lifetimes in the     *)
(* pushed-binder context (used by the per-field alignment).             *)
Lemma lt_wf_push_shift_lt_of_ty_list : forall X k G,
  lt_wf G (lt_of_ty_list X) ->
  lt_wf (push_lt_vars k lt_local G)
        (lt_of_ty_list (List.map (shift_lt_in_ty k 0) X)).
Proof.
  intros X k G HX. rewrite lt_of_ty_list_shift_lt_amt.
  apply lt_wf_shift_push. exact HX.
Qed.

Lemma Forall_lt_wf_push_shift_lt_of_ty : forall X k G,
  Forall (fun U => lt_wf G (lt_of_ty U)) X ->
  Forall (fun U => lt_wf (push_lt_vars k lt_local G) (lt_of_ty U))
         (List.map (shift_lt_in_ty k 0) X).
Proof.
  intros X k G HX. induction HX as [| U Us HU HUs IHUs]; simpl.
  - constructor.
  - constructor.
    + rewrite lt_of_ty_shift_lt_amt. apply lt_wf_shift_push. exact HU.
    + exact IHUs.
Qed.

(* ================================================================== *)
(* PER-FIELD ESCAPE ALIGNMENT.  For a (ty- and lt-closed) constructor  *)
(* field schema S, substituting a type through the instantiated field  *)
(* raises its escape lifetime by at most the join of the substituted   *)
(* type arguments' escape lifetimes.  This is exactly what keeps the   *)
(* T_Ctor effective-lifetime escape premise stable under subst_ty.     *)
(* ================================================================== *)
Lemma inst_ctor_field_alignment : forall S lts Ts n Sb G,
  ty_lt_closed (List.length lts) S ->
  ty_ty_closed (List.length Ts) S ->
  Forall (lt_wf G) lts ->
  Forall (fun U => lt_wf G (lt_of_ty U)) Ts ->
  lt_wf G (lt_of_ty_list (List.map (subst_ty n Sb) Ts)) ->
  G ⊢ₗ lt_of_ty (subst_ty n Sb (inst_ctor_type (List.length lts) (List.length Ts) lts Ts S))
      <: lt_min (lt_of_ty (inst_ctor_type (List.length lts) (List.length Ts) lts Ts S))
                (lt_of_ty_list (List.map (subst_ty n Sb) Ts)).
Proof.
  intros S lts Ts n Sb G HltC HtyC HFlts HwfTs HwfTs'.
  set (Ts' := List.map (subst_ty n Sb) Ts).
  (* Step 1: subst commutes into the type args; ty-closed schema is fixed. *)
  assert (Hstep1 : subst_ty n Sb (inst_ctor_type (List.length lts) (List.length Ts) lts Ts S)
                   = inst_ctor_type (List.length lts) (List.length Ts) lts Ts' S).
  { rewrite <- (inst_ctor_type_subst_ty (List.length lts) (List.length Ts) lts Ts S n Sb
                  eq_refl eq_refl).
    unfold Ts'. f_equal.
    apply (subst_ty_ty_closed_id S (List.length Ts) (List.length Ts + n)
             (shift_lt_in_ty (List.length lts) 0 (shift_ty (List.length Ts) 0 Sb)));
      [exact HtyC | lia]. }
  rewrite Hstep1.
  set (Gp := push_lt_vars (List.length lts) lt_local G).
  assert (HwfS_p : lt_wf Gp (lt_of_ty S)).
  { unfold Gp. apply lt_lt_closed_lt_wf_push. apply ty_lt_closed_lt_of_ty. exact HltC. }
  unfold inst_ctor_type. rewrite !lt_of_ty_inst_lt_vars.
  eapply LS_Trans.
  { apply (multi_subst_lt_lt_sub
             (lt_of_ty (inst_ty_vars (List.length Ts)
                          (List.map (shift_lt_in_ty (List.length lts) 0) Ts') S))
             (lt_min (lt_of_ty S) (shift_lt (List.length lts) 0 (lt_of_ty_list Ts')))
             lts G HFlts).
    fold Gp.
    rewrite <- (lt_of_ty_list_shift_lt_amt Ts' (List.length lts) 0).
    replace (List.length Ts)
      with (List.length (List.map (shift_lt_in_ty (List.length lts) 0) Ts'))
      by (unfold Ts'; rewrite !List.length_map; reflexivity).
    apply (lt_of_ty_inst_ty_vars_le (List.map (shift_lt_in_ty (List.length lts) 0) Ts') S Gp
             HwfS_p (lt_wf_push_shift_lt_of_ty_list Ts' (List.length lts) G HwfTs')). }
  cbn [multi_subst_lt].
  rewrite (multi_subst_lt_shift_cancel0 (List.length lts) lts (lt_of_ty_list Ts') eq_refl).
  apply lt_min_mono; [| apply LS_Refl; exact HwfTs'].
  apply (multi_subst_lt_lt_sub (lt_of_ty S)
           (lt_of_ty (inst_ty_vars (List.length Ts)
                        (List.map (shift_lt_in_ty (List.length lts) 0) Ts) S)) lts G HFlts).
  fold Gp.
  replace (List.length Ts)
    with (List.length (List.map (shift_lt_in_ty (List.length lts) 0) Ts))
    by (rewrite List.length_map; reflexivity).
  apply (lt_of_ty_inst_ty_vars_ge (List.map (shift_lt_in_ty (List.length lts) 0) Ts) S Gp
           HwfS_p (Forall_lt_wf_push_shift_lt_of_ty Ts (List.length lts) G HwfTs)).
Qed.

(* Lattice redistribution: (P∨c) ∨ (Q∨c) <: (P∨Q) ∨ c.                  *)
Lemma lt_min_redistribute : forall G P Q c,
  lt_wf G P -> lt_wf G Q -> lt_wf G c ->
  G ⊢ₗ lt_min (lt_min P c) (lt_min Q c) <: lt_min (lt_min P Q) c.
Proof.
  intros G P Q c HP HQ Hc. apply LS_MinL.
  - apply LS_MinL.
    + apply LS_MinR1; [apply LS_MinR1; [apply LS_Refl; exact HP | exact HQ] | exact Hc].
    + apply LS_MinR2; [apply LS_Refl; exact Hc | apply LWF_Min; assumption].
  - apply LS_MinL.
    + apply LS_MinR1; [apply LS_MinR2; [apply LS_Refl; exact HQ | exact HP] | exact Hc].
    + apply LS_MinR2; [apply LS_Refl; exact Hc | apply LWF_Min; assumption].
Qed.

(* The escape-premise stability lifted to the full constructor field    *)
(* list: substituting raises the field-list escape lifetime by at most  *)
(* the substituted type arguments' escape lifetime.                     *)
Lemma inst_ctor_fields_alignment : forall sigma_fields lts Ts n Sb G,
  Forall (fun S => ty_lt_closed (List.length lts) S /\ ty_ty_closed (List.length Ts) S) sigma_fields ->
  Forall (lt_wf G) lts ->
  Forall (fun U => lt_wf G (lt_of_ty U)) Ts ->
  lt_wf G (lt_of_ty_list (List.map (subst_ty n Sb) Ts)) ->
  G ⊢ₗ lt_of_ty_list (List.map (subst_ty n Sb)
         (List.map (inst_ctor_type (List.length lts) (List.length Ts) lts Ts) sigma_fields))
      <: lt_min (lt_of_ty_list
           (List.map (inst_ctor_type (List.length lts) (List.length Ts) lts Ts) sigma_fields))
           (lt_of_ty_list (List.map (subst_ty n Sb) Ts)).
Proof.
  intros sigma_fields lts Ts n Sb G HClosed HFlts HwfTs HwfTs'.
  assert (Hwfc : lt_wf G (lt_of_ty_list (List.map (subst_ty n Sb) Ts))) by exact HwfTs'.
  induction sigma_fields as [|S rest IH].
  - cbn [List.map]. rewrite !lt_of_ty_list_nil.
    apply LS_MinR1; [apply LS_Free; apply LWF_Free | exact Hwfc].
  - inversion HClosed as [|S0 rest0 [HltC HtyC] HClosedRest]; subst.
    cbn [List.map]. rewrite !lt_of_ty_list_cons.
    pose proof (inst_ctor_field_alignment S lts Ts n Sb G HltC HtyC HFlts HwfTs HwfTs') as Hpe.
    pose proof (IH HClosedRest) as Hih.
    destruct (lt_sub_wf _ _ _ Hpe) as [_ HwfRpe].
    inversion HwfRpe as [| | |G0 a0 b0 HwfPe Hwfc0]; subst.
    destruct (lt_sub_wf _ _ _ Hih) as [_ HwfRih].
    inversion HwfRih as [| | |G1 a1 b1 HwfIh Hwfc1]; subst.
    eapply LS_Trans.
    + apply lt_min_mono; [exact Hpe | exact Hih].
    + apply lt_min_redistribute; assumption.
Qed.

Lemma subst_ty_in_tm_go_eq_map_local : forall n Sb ts,
  (fix go ts := match ts with [] => [] | u :: rest => subst_ty_in_tm n Sb u :: go rest end) ts =
  List.map (subst_ty_in_tm n Sb) ts.
Proof.
  intros n Sb ts. induction ts as [|t ts IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma free_tm_vars_subst_ty_in_tm : forall t cutoff n Sb,
  free_tm_vars cutoff (subst_ty_in_tm n Sb t) = free_tm_vars cutoff t.
Proof.
  apply (term_list_ind
    (fun t => forall cutoff n Sb,
      free_tm_vars cutoff (subst_ty_in_tm n Sb t) = free_tm_vars cutoff t)
    (fun ts => forall cutoff n Sb,
      List.concat (List.map (free_tm_vars cutoff) (List.map (subst_ty_in_tm n Sb) ts)) =
      List.concat (List.map (free_tm_vars cutoff) ts))).
  - reflexivity.
  - intros t1 t2 IH1 IH2 cutoff n Sb. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH cutoff n Sb. simpl. apply IH.
  - intros t T IH cutoff n Sb. simpl. apply IH.
  - intros bound body IH cutoff n Sb. simpl. apply IH.
  - intros t l IH cutoff n Sb. simpl. apply IH.
  - intros body IH cutoff n Sb. simpl. apply IH.
  - intros K l lts Ts ts IH cutoff n Sb. simpl. rewrite subst_ty_in_tm_go_eq_map_local.
    rewrite !free_tm_vars_go_eq_concat. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn cutoff n Sb. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb cutoff n Sb. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa cutoff n Sb. simpl. rewrite IHt, IHa. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop cutoff n Sb. simpl. apply IHop.
  - intros m T_B T_R t IH cutoff n Sb. simpl. apply IH.
  - intros m T_B T_R b IH cutoff n Sb. simpl. apply IH.
  - reflexivity.
  - intros t ts IHt IHts cutoff n Sb. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma has_rt_cap_subst_ty_in_tm : forall t n Sb,
  has_rt_cap (subst_ty_in_tm n Sb t) = has_rt_cap t.
Proof.
  apply (term_list_ind
    (fun t => forall n Sb,
      has_rt_cap (subst_ty_in_tm n Sb t) = has_rt_cap t)
    (fun ts => forall n Sb,
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end)
        (List.map (subst_ty_in_tm n Sb) ts) =
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts)).
  - reflexivity.
  - intros t1 t2 IH1 IH2 n Sb. simpl. rewrite IH1, IH2. reflexivity.
  - intros body T IH n Sb. simpl. apply IH.
  - intros t T IH n Sb. simpl. apply IH.
  - intros bound body IH n Sb. simpl. apply IH.
  - intros t l IH n Sb. simpl. apply IH.
  - intros body IH n Sb. simpl. apply IH.
  - intros K l lts Ts ts IH n Sb. simpl. rewrite subst_ty_in_tm_go_eq_map_local. apply IH.
  - intros scrut tag n_lt arity yes_body no_body IHs IHy IHn n Sb. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHb n Sb. simpl.
    rewrite IHop, IHb. reflexivity.
  - intros t Ss arg IHt IHa n Sb. simpl. rewrite IHt, IHa. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros t ts IHt IHts n Sb. simpl. rewrite IHt, IHts. reflexivity.
Qed.

Lemma lt_of_ty_ctx_SubstTy_le_wf : forall Sb n G G', SubstTy Sb n G G' ->
  forall f T k, lt_wf G (lt_of_ty_ctx f G T) -> VB k T -> length G <= k + f ->
  G' ⊢ₗ lt_of_ty_ctx f G' (subst_ty n Sb T) <: lt_of_ty_ctx f G T.
Proof.
  intros Sb n G G' HS.
  pose proof (SubstTy_n_lt Sb n G G' HS) as Hn.
  pose proof (SubstTy_S_VB Sb n G G' HS) as HSVB.
  pose proof (SubstTy_length Sb n G G' HS) as HLen.
  destruct (SubstTy_target Sb n G G' HS) as [Btgt [Htgt Hsubtgt]].
  induction f as [|f' IHf]; intros T k HwfLt HVB Hlen.
  - rewrite Nat.add_0_r in Hlen. revert k HwfLt HVB Hlen.
    induction T using type_list_ind with
      (Q := fun Ts => forall k,
              lt_wf G (lt_of_ty_ctx_list 0 G Ts) -> VBL k Ts -> length G <= k ->
              G' ⊢ₗ lt_of_ty_ctx_list 0 G' (List.map (subst_ty n Sb) Ts)
                  <: lt_of_ty_ctx_list 0 G Ts);
      intros k HwfLt HVB Hlen.
    + simpl in HVB.
      assert (Hane : n0 <> n) by lia.
      rewrite (subst_ty_var_neq n Sb n0 Hane).
      rewrite !(lt_of_ty_ctx_var 0). apply LS_Refl. constructor.
    + rewrite subst_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. apply LS_Refl.
      eapply lt_wf_SubstTy_ctx; eauto.
    + rewrite subst_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor.
      rewrite VB_ctor in HVB. inversion HwfLt; subst.
      apply lt_min_mono.
      * apply LS_Refl. eapply lt_wf_SubstTy_ctx; eauto.
      * eapply IHT; eauto.
    + rewrite subst_ty_ltall_eq. rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + rewrite subst_ty_tyall_eq. rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + rewrite VBL_cons in HVB. destruct HVB as [Ha Hr].
      cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons.
      inversion HwfLt; subst.
      apply lt_min_mono; [eapply IHT; eauto | eapply IHT0; eauto].
  - revert k HwfLt HVB Hlen.
    induction T using type_list_ind with
      (Q := fun Ts => forall k,
              lt_wf G (lt_of_ty_ctx_list (S f') G Ts) -> VBL k Ts -> length G <= k + S f' ->
              G' ⊢ₗ lt_of_ty_ctx_list (S f') G' (List.map (subst_ty n Sb) Ts)
                  <: lt_of_ty_ctx_list (S f') G Ts);
      intros k HwfLt HVB Hlen.
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
          -- assert (HwfB0 : lt_wf G (lt_of_ty_ctx f' G B0)).
            { rewrite (lt_of_ty_ctx_var (S f') G n0), E in HwfLt. exact HwfLt. }
            apply (IHf B0 (S n0) HwfB0 (ctx_inv_all G n0 B0 E)). lia.
        -- apply LS_Refl. constructor.
    + rewrite subst_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. apply LS_Refl.
      eapply lt_wf_SubstTy_ctx; eauto.
    + rewrite subst_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor.
      rewrite VB_ctor in HVB. inversion HwfLt; subst.
      apply lt_min_mono.
      * apply LS_Refl. eapply lt_wf_SubstTy_ctx; eauto.
      * eapply IHT; eauto.
    + rewrite subst_ty_ltall_eq. rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + rewrite subst_ty_tyall_eq. rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + rewrite VBL_cons in HVB. destruct HVB as [Ha Hr].
      cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons.
      inversion HwfLt; subst.
      apply lt_min_mono; [eapply IHT; eauto | eapply IHT0; eauto].
Qed.

Lemma lt_of_ty_G_SubstTy_le_wf : forall Sb n G G', SubstTy Sb n G G' ->
  forall T, lt_wf G (lt_of_ty_G G T) ->
  G' ⊢ₗ lt_of_ty_G G' (subst_ty n Sb T) <: lt_of_ty_G G T.
Proof.
  intros Sb n G G' HS T HwfLt. unfold lt_of_ty_G in *.
  pose proof (SubstTy_length Sb n G G' HS) as HL.
  rewrite (lt_of_ty_ctx_fuel_irrel (length G') (length G)
             (subst_ty n Sb T) G' 0 (VB_0 _) ltac:(lia) ltac:(lia)).
  apply (lt_of_ty_ctx_SubstTy_le_wf Sb n G G' HS (length G) T 0 HwfLt (VB_0 T) ltac:(lia)).
Qed.

Lemma capture_lt_SubstTy_le : forall Sb n G G', SubstTy Sb n G G' ->
  forall body, lt_wf G (capture_lt G body) ->
  G' ⊢ₗ capture_lt G' (subst_ty_in_tm n Sb body) <: capture_lt G body.
Proof.
  intros Sb n G G' HS body HwfCap. unfold capture_lt in *.
  rewrite has_rt_cap_subst_ty_in_tm.
  destruct (has_rt_cap body) eqn:Hcap.
  - apply LS_Refl. constructor.
  - rewrite free_tm_vars_subst_ty_in_tm.
    induction (free_tm_vars 1 body) as [|x xs IH]; simpl in *.
    + apply LS_Refl. constructor.
    + inversion HwfCap; subst.
      rewrite (SubstTy_lookup_tm Sb n G G' HS x).
      destruct (ctx_lookup_tm G x) as [T|] eqn:Hlk; simpl.
      * apply lt_min_mono.
        -- match goal with
          | Hh : lt_wf G (lt_of_ty_G G T) |-
            G' ⊢ₗ lt_of_ty_G G' (subst_ty n Sb T) <: lt_of_ty_G G T =>
            apply (lt_of_ty_G_SubstTy_le_wf Sb n G G' HS T Hh)
          end.
        -- match goal with
          | Ht : lt_wf G (fold_right _ _ xs) |- _ => apply IH; exact Ht
          end.
      * apply lt_min_mono.
        -- apply LS_Refl. constructor.
        -- match goal with
          | Ht : lt_wf G (fold_right _ _ xs) |- _ => apply IH; exact Ht
          end.
Qed.

Lemma lifetimes_wf_SubstTy : forall G lts,
  lifetimes_wf G lts -> forall Sb n G', SubstTy Sb n G G' -> lifetimes_wf G' lts.
Proof.
  intros G lts Hwf. induction Hwf; intros Sb n G' HS.
  - constructor.
  - constructor.
    + eapply lt_wf_SubstTy_ctx; eauto.
    + apply (IHHwf Sb n G' HS).
Qed.

Lemma subst_ty_any_at_free : forall n Sb, subst_ty n Sb any_at_free = any_at_free.
Proof. intros n Sb. reflexivity. Qed.

Lemma SubstTy_push_lt_vars : forall k Delta Sb n G G',
  SubstTy Sb n G G' ->
  SubstTy (shift_lt_in_ty k 0 Sb) n
    (push_lt_vars k Delta G) (push_lt_vars k Delta G').
Proof.
  induction k as [|k IH]; intros Delta Sb n G G' HS; simpl.
  - rewrite shift_lt_in_ty_zero. exact HS.
  - replace (shift_lt_in_ty (S k) 0 Sb)
      with (shift_lt_in_ty k 0 (shift_lt_in_ty 1 0 Sb)).
    2:{ rewrite shift_lt_in_ty_fuse. replace (k + 1) with (S k) by lia. reflexivity. }
    apply IH. apply SubstTy_lt. exact HS.
Qed.

Lemma SubstTy_push_ty_vars_any_at_free : forall k Sb n G G',
  SubstTy Sb n G G' ->
  SubstTy (shift_ty k 0 Sb) (k + n)
    (push_ty_vars k any_at_free G) (push_ty_vars k any_at_free G').
Proof.
  induction k as [|k IH]; intros Sb n G G' HS; simpl.
  - rewrite shift_ty_zero. replace (0 + n) with n by lia. exact HS.
  - replace (shift_ty (S k) 0 Sb) with (shift_ty k 0 (shift_ty 1 0 Sb)).
    2:{ rewrite shift_ty_fuse. replace (k + 1) with (S k) by lia. reflexivity. }
    replace (S (k + n)) with (k + S n) by lia.
    apply IH. rewrite <- (subst_ty_any_at_free n Sb).
    apply SubstTy_ty. exact HS.
Qed.

Lemma SubstTy_fold_bind_tm : forall rhos Sb n G G',
  SubstTy Sb n G G' ->
  SubstTy Sb n
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm (subst_ty n Sb rho) :: G0) G' rhos).
Proof.
  induction rhos as [|rho rhos IH]; intros Sb n G G' HS; simpl.
  - exact HS.
  - apply SubstTy_tm. apply IH. exact HS.
Qed.

Lemma Forall2_typing_SubstTy : forall Γ vs rhos,
  Forall2 (fun v rho => forall Sb n G', SubstTy Sb n Γ G' ->
    G' ⊢ₜ subst_ty_in_tm n Sb v : subst_ty n Sb rho) vs rhos ->
  forall Sb n G', SubstTy Sb n Γ G' ->
  Forall2 (fun v rho => G' ⊢ₜ v : rho)
           (List.map (subst_ty_in_tm n Sb) vs) (List.map (subst_ty n Sb) rhos).
Proof.
  intros Γ vs rhos H. induction H; intros Sb n G' HS; simpl.
  - constructor.
  - constructor.
    + apply H. exact HS.
    + apply IHForall2. exact HS.
Qed.

Lemma elim_lt_shift_miss : forall l lvar bound p,
  elim_lt lvar bound p (shift_lt 1 lvar l) = Some (shift_lt 1 lvar l).
Proof.
  induction l as [x| | |l1 IH1 l2 IH2]; intros lvar bound p; simpl.
  - destruct (Nat.leb lvar x) eqn:Hle.
    + apply Nat.leb_le in Hle.
      assert (Hneq : (x + 1 =? lvar) = false) by (apply Nat.eqb_neq; lia).
      rewrite Hneq. reflexivity.
    + apply Nat.leb_gt in Hle.
      assert (Hneq : (x =? lvar) = false) by (apply Nat.eqb_neq; lia).
      rewrite Hneq. reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma elim_ty_shift_miss : forall T lvar bound p,
  elim_ty lvar bound p (shift_lt_in_ty 1 lvar T) = Some (shift_lt_in_ty 1 lvar T).
Proof.
  apply (type_list_ind
    (fun T => forall lvar bound p,
      elim_ty lvar bound p (shift_lt_in_ty 1 lvar T) = Some (shift_lt_in_ty 1 lvar T))
    (fun Ts => forall lvar bound p,
      (fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
         match Ts0 with
         | [] => Some []
         | A :: rest =>
             match elim_ty lvar bound p' A, go_list p' rest with
             | Some A', Some rest' => Some (A' :: rest')
             | _, _ => None
             end
         end) p (List.map (shift_lt_in_ty 1 lvar) Ts) =
      Some (List.map (shift_lt_in_ty 1 lvar) Ts))).
  - reflexivity.
  - intros A l B HA HB lvar bound p. simpl.
    rewrite HA, HB, elim_lt_shift_miss. reflexivity.
  - intros K l Ts HTs lvar bound p. rewrite shift_lt_in_ty_ctor_eq. simpl.
    rewrite elim_lt_shift_miss. rewrite HTs. reflexivity.
  - intros A HA lvar bound p. simpl.
    rewrite HA. reflexivity.
  - intros B A HB HA lvar bound p. simpl.
    rewrite HB, HA. reflexivity.
  - reflexivity.
  - intros A Ts HA HTs lvar bound p. cbn [List.map]. simpl.
    rewrite HA, HTs. reflexivity.
Qed.

Lemma elim_lt_subst_lt_shifted : forall l lvar bound p l' c R,
  lvar < c ->
  elim_lt lvar bound p l = Some l' ->
  elim_lt lvar (subst_lt c (shift_lt 1 lvar R) bound) p
    (subst_lt c (shift_lt 1 lvar R) l) =
  Some (subst_lt c (shift_lt 1 lvar R) l').
Proof.
  induction l as [x| | |l1 IH1 l2 IH2]; intros lvar bound p l' c R Hlt H; simpl in H.
  - destruct (Nat.eqb_spec x lvar) as [Heq|Hne].
    + subst x. destruct p; simpl in H; try discriminate.
      * injection H as H; subst l'. simpl.
        destruct (Nat.eqb_spec lvar c); [lia|].
        destruct (Nat.ltb_spec c lvar); [lia|]. simpl. rewrite Nat.eqb_refl. reflexivity.
      * injection H as H; subst l'. simpl.
        destruct (Nat.eqb_spec lvar c); [lia|].
        destruct (Nat.ltb_spec c lvar); [lia|]. simpl. rewrite Nat.eqb_refl. reflexivity.
    + injection H as H; subst l'. simpl.
      destruct (Nat.eqb_spec x c) as [Hxc|Hxc].
      * subst x. apply elim_lt_shift_miss.
      * destruct (Nat.ltb_spec c x) as [Hcx|Hcx]; simpl.
        -- destruct (Nat.eqb_spec (Init.Nat.pred x) lvar); [lia|reflexivity].
        -- destruct (Nat.eqb_spec x lvar); [contradiction|reflexivity].
  - injection H as H; subst l'. reflexivity.
  - injection H as H; subst l'. reflexivity.
  - destruct (elim_lt lvar bound p l1) as [l1'|] eqn:H1; try discriminate.
    destruct (elim_lt lvar bound p l2) as [l2'|] eqn:H2; try discriminate.
    injection H as H; subst l'. simpl.
    rewrite (IH1 lvar bound p l1' c R Hlt H1).
    rewrite (IH2 lvar bound p l2' c R Hlt H2). reflexivity.
Qed.

Lemma elim_ty_subst_lt_shifted : forall T lvar bound p T' c R,
  lvar < c ->
  elim_ty lvar bound p T = Some T' ->
  elim_ty lvar (subst_lt c (shift_lt 1 lvar R) bound) p
    (subst_lt_in_ty c (shift_lt 1 lvar R) T) =
  Some (subst_lt_in_ty c (shift_lt 1 lvar R) T').
Proof.
  apply (type_list_ind
    (fun T => forall lvar bound p T' c R,
      lvar < c ->
      elim_ty lvar bound p T = Some T' ->
      elim_ty lvar (subst_lt c (shift_lt 1 lvar R) bound) p
        (subst_lt_in_ty c (shift_lt 1 lvar R) T) =
      Some (subst_lt_in_ty c (shift_lt 1 lvar R) T'))
    (fun Ts => forall lvar bound p Ts' c R,
      lvar < c ->
      (fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
         match Ts0 with
         | [] => Some []
         | A :: rest =>
             match elim_ty lvar bound p' A, go_list p' rest with
             | Some A', Some rest' => Some (A' :: rest')
             | _, _ => None
             end
         end) p Ts = Some Ts' ->
      (fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
         match Ts0 with
         | [] => Some []
         | A :: rest =>
             match elim_ty lvar (subst_lt c (shift_lt 1 lvar R) bound) p' A, go_list p' rest with
             | Some A', Some rest' => Some (A' :: rest')
             | _, _ => None
             end
         end) p (List.map (subst_lt_in_ty c (shift_lt 1 lvar R)) Ts) =
      Some (List.map (subst_lt_in_ty c (shift_lt 1 lvar R)) Ts'))).
  - intros m lvar bound p T' c R Hlt H. simpl in H. injection H as H; subst T'. reflexivity.
  - intros A l B HA HB lvar bound p T' c R Hlt H. simpl in H.
    destruct (elim_ty lvar bound (flip_var p) A) as [A'|] eqn:HAe; try discriminate.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hle; try discriminate.
    destruct (elim_ty lvar bound p B) as [B'|] eqn:HBe; try discriminate.
    injection H as H; subst T'. rewrite subst_lt_in_ty_fun_eq. simpl.
    rewrite (HA lvar bound (flip_var p) A' c R Hlt HAe).
    rewrite (elim_lt_subst_lt_shifted l lvar bound p l' c R Hlt Hle).
    rewrite (HB lvar bound p B' c R Hlt HBe). reflexivity.
  - intros K l Ts HTs lvar bound p T' c R Hlt H. simpl in H.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hle; try discriminate.
    destruct ((fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
      match Ts0 with
      | [] => Some []
      | A :: rest =>
          match elim_ty lvar bound p' A, go_list p' rest with
          | Some A', Some rest' => Some (A' :: rest')
          | _, _ => None
          end
      end) var_inv Ts) as [Ts'|] eqn:HTse; try discriminate.
    injection H as H; subst T'. rewrite subst_lt_in_ty_ctor_eq. simpl.
    rewrite (elim_lt_subst_lt_shifted l lvar bound p l' c R Hlt Hle).
    rewrite (HTs lvar bound var_inv Ts' c R Hlt HTse). reflexivity.
  - intros A HA lvar bound p T' c R Hlt H. simpl in H.
    destruct (elim_ty (S lvar) (shift_lt 1 0 bound) p A) as [A'|] eqn:HAe; try discriminate.
    injection H as H; subst T'. rewrite subst_lt_in_ty_ltall_eq. simpl.
    replace (shift_lt 1 0 (subst_lt c (shift_lt 1 lvar R) bound))
      with (subst_lt (S c) (shift_lt 1 (S lvar) (shift_lt 1 0 R)) (shift_lt 1 0 bound)).
    2:{ rewrite <- shift_lt_swap_0. rewrite <- shift_lt_subst_lt_comm0. reflexivity. }
    replace (shift_lt 1 0 (shift_lt 1 lvar R))
      with (shift_lt 1 (S lvar) (shift_lt 1 0 R)).
    2:{ symmetry. apply shift_lt_swap_0. }
    rewrite (HA (S lvar) (shift_lt 1 0 bound) p A' (S c) (shift_lt 1 0 R) ltac:(lia) HAe).
    reflexivity.
  - intros B A HB HA lvar bound p T' c R Hlt H. simpl in H.
    destruct (elim_ty lvar bound (flip_var p) B) as [B'|] eqn:HBe; try discriminate.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HAe; try discriminate.
    injection H as H; subst T'. rewrite subst_lt_in_ty_tyall_eq. simpl.
    rewrite (HB lvar bound (flip_var p) B' c R Hlt HBe).
    rewrite (HA lvar bound p A' c R Hlt HAe). reflexivity.
  - intros lvar bound p Ts' c R Hlt H. simpl in H. injection H as H; subst Ts'. reflexivity.
  - intros A Ts HA HTs lvar bound p Ts' c R Hlt H. simpl in H.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HAe; try discriminate.
    destruct ((fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
      match Ts0 with
      | [] => Some []
      | A0 :: rest =>
          match elim_ty lvar bound p' A0, go_list p' rest with
          | Some A'', Some rest' => Some (A'' :: rest')
          | _, _ => None
          end
      end) p Ts) as [Ts0'|] eqn:HTse; try discriminate.
    injection H as H; subst Ts'. cbn [List.map].
    rewrite (HA lvar bound p A' c R Hlt HAe).
    rewrite (HTs lvar bound p Ts0' c R Hlt HTse). reflexivity.
Qed.

Lemma elim_ty_n_subst_lt_shifted : forall k bound p T T' n R,
  elim_ty_n k bound p T = Some T' ->
  elim_ty_n k (subst_lt (k + n) (shift_lt k 0 R) bound) p
    (subst_lt_in_ty (k + n) (shift_lt k 0 R) T) =
  Some (subst_lt_in_ty n R T').
Proof.
  induction k as [|k IH]; intros bound p T T' n R H.
  - simpl in H. injection H as H; subst T'. simpl. rewrite shift_lt_zero. reflexivity.
  - simpl in H. destruct (elim_ty 0 bound p T) as [T1|] eqn:HE; try discriminate.
    simpl.
    replace (S k + n) with (S (k + n)) by lia.
    replace (shift_lt (S k) 0 R) with (shift_lt 1 0 (shift_lt k 0 R)).
    2:{ rewrite shift_lt_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    rewrite (elim_ty_subst_lt_shifted T 0 bound p T1 (S (k + n)) (shift_lt k 0 R) ltac:(lia) HE).
    replace (subst_lt 0 lt_free (subst_lt (S (k + n)) (shift_lt 1 0 (shift_lt k 0 R)) bound))
      with (subst_lt (k + n) (shift_lt k 0 R) (subst_lt 0 lt_free bound)).
    2:{ pose proof (subst_lt_subst_lt_comm0 bound 0 (k + n) (shift_lt k 0 R) lt_free) as Hcomm.
        simpl in Hcomm. rewrite shift_lt_zero in Hcomm.
        exact (eq_sym Hcomm). }
    replace (subst_lt_in_ty 0 lt_free
      (subst_lt_in_ty (S (k + n)) (shift_lt 1 0 (shift_lt k 0 R)) T1))
      with (subst_lt_in_ty (k + n) (shift_lt k 0 R) (subst_lt_in_ty 0 lt_free T1)).
    2:{ pose proof (subst_lt_in_ty_subst_lt_in_ty_comm0 T1 0 (k + n) (shift_lt k 0 R) lt_free) as Hcomm.
        simpl in Hcomm. rewrite shift_lt_zero in Hcomm.
        exact (eq_sym Hcomm). }
    apply IH. exact H.
Qed.

Lemma Forall2_typing_SubstLt_closed_from : forall Γ vs rhos,
  Forall2 (fun v rho => forall R n G',
    SubstLt R n Γ G' ->
    ctx_lt_closed_from n Γ ->
    ctx_schemas_lt_closed_from n Γ ->
    G' ⊢ₜ subst_lt_in_tm n R v : subst_lt_in_ty n R rho) vs rhos ->
  forall R n G',
    SubstLt R n Γ G' ->
    ctx_lt_closed_from n Γ ->
    ctx_schemas_lt_closed_from n Γ ->
    Forall2 (fun v rho => G' ⊢ₜ v : rho)
      (List.map (subst_lt_in_tm n R) vs)
      (List.map (subst_lt_in_ty n R) rhos).
Proof.
  intros Γ vs rhos H. induction H; intros R n G' HSub Hlt Hschemas; simpl.
  - constructor.
  - constructor.
    + apply H; assumption.
    + apply IHForall2; assumption.
Qed.

Lemma Forall_lt_sub_SubstLt : forall Γ lts l,
  Forall (fun l0 => Γ ⊢ₗ l0 <: l) lts ->
  forall R n G', SubstLt R n Γ G' ->
  Forall (fun l0 => G' ⊢ₗ l0 <: subst_lt n R l) (List.map (subst_lt n R) lts).
Proof.
  intros Γ lts l H. induction H as [|l0 lts0 Hsub Hrest IH]; intros R n G' HSub; simpl.
  - constructor.
  - constructor.
    + apply (lt_sub_SubstLt Γ l0 l Hsub R n G' HSub).
    + apply IH. exact HSub.
Qed.

Lemma inst_ctor_type_list_subst_lt : forall n_lt n_ty lts Ts fields n R,
  List.length lts = n_lt ->
  List.map
    (inst_ctor_type n_lt n_ty (List.map (subst_lt n R) lts)
      (List.map (subst_lt_in_ty n R) Ts))
    (List.map (subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R)) fields) =
  List.map (subst_lt_in_ty n R)
    (List.map (inst_ctor_type n_lt n_ty lts Ts) fields).
Proof.
  intros n_lt n_ty lts Ts fields n R Hlen.
  rewrite !List.map_map. apply List.map_ext. intro T.
  apply inst_ctor_type_subst_lt. exact Hlen.
Qed.

Lemma lt_of_ty_subst_lt : forall T n R,
  lt_of_ty (subst_lt_in_ty n R T) = subst_lt n R (lt_of_ty T).
Proof.
  apply (type_list_ind
    (fun T => forall c R,
      lt_of_ty (subst_lt_in_ty c R T) = subst_lt c R (lt_of_ty T))
    (fun Ts => forall c R,
      lt_of_ty_list (List.map (subst_lt_in_ty c R) Ts) = subst_lt c R (lt_of_ty_list Ts))).
  - intros x c R. reflexivity.
  - intros A l B IHA IHB c R. simpl. reflexivity.
  - intros K l Ts IHTs c R. simpl.
    change ((fix go_list (Ts0 : list type) : lifetime :=
      match Ts0 with
      | [] => lt_free
      | A :: rest => lt_min (lt_of_ty A) (go_list rest)
      end) ((fix go (Ts0 : list type) : list type :=
        match Ts0 with
        | [] => []
        | A :: rest => subst_lt_in_ty c R A :: go rest
        end) Ts))
      with (lt_of_ty_list (List.map (subst_lt_in_ty c R) Ts)).
    change ((fix go_list (Ts0 : list type) : lifetime :=
      match Ts0 with
      | [] => lt_free
      | A :: rest => lt_min (lt_of_ty A) (go_list rest)
      end) Ts) with (lt_of_ty_list Ts).
    rewrite IHTs. reflexivity.
  - intros A IHA c R. simpl. reflexivity.
  - intros B A IHB IHA c R. simpl. reflexivity.
  - intros c R. reflexivity.
  - intros A Ts IHA IHTs c R. simpl. rewrite IHA, IHTs. reflexivity.
Qed.

Lemma lt_of_ty_list_subst_lt : forall Ts n R,
  lt_of_ty_list (List.map (subst_lt_in_ty n R) Ts) = subst_lt n R (lt_of_ty_list Ts).
Proof.
  induction Ts as [|T Ts IH]; intros c R; simpl.
  - reflexivity.
  - rewrite lt_of_ty_subst_lt, IH. reflexivity.
Qed.

Lemma typing_SubstLt_closed_from : forall Γ t T,
  Γ ⊢ₜ t : T ->
  forall R n G',
    SubstLt R n Γ G' ->
    ctx_lt_closed_from n Γ ->
    ctx_schemas_lt_closed_from n Γ ->
    G' ⊢ₜ subst_lt_in_tm n R t : subst_lt_in_ty n R T.
Proof.
  apply (typing_ind_forall2
    (fun Γ t T => forall R n G',
      SubstLt R n Γ G' ->
      ctx_lt_closed_from n Γ ->
      ctx_schemas_lt_closed_from n Γ ->
      G' ⊢ₜ subst_lt_in_tm n R t : subst_lt_in_ty n R T)).
  - intros Γ x T Hlk HwfT R n G' HSub Hlt Hschemas.
    simpl. apply T_Var.
    + rewrite (SubstLt_lookup_tm R n Γ G' HSub x). rewrite Hlk. reflexivity.
    + eapply ty_wf_SubstLt; eauto.
  - intros Γ t T U Ht IH Hsub R n G' HSub Hlt Hschemas.
    eapply T_Sub.
    + apply (IH R n G' HSub Hlt Hschemas).
    + eapply sub_SubstLt; eauto.
  - intros Γ body A l B HwfA HwfB Hbody IHbody Hcap R n G' HSub Hlt Hschemas.
    simpl. apply T_Lam.
    + eapply ty_wf_SubstLt; eauto.
    + eapply ty_wf_SubstLt; eauto.
    + apply (IHbody R n (bind_tm (subst_lt_in_ty n R A) :: G')
        (SubstLt_tm R n Γ G' A HSub)
        (ctx_lt_closed_from_bind_tm n Γ A Hlt)
        (ctx_schemas_lt_closed_from_bind_tm n Γ A Hschemas)).
    + rewrite (capture_lt_SubstLt R n Γ G' HSub body).
      eapply lt_sub_SubstLt; eauto.
  - intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 R n G' HSub Hlt Hschemas.
    simpl. eapply T_App.
    + apply (IH1 R n G' HSub Hlt Hschemas).
    + apply (IH2 R n G' HSub Hlt Hschemas).
  - intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody R n G' HSub Hlt Hschemas.
    simpl. apply T_TyLam.
    + eapply ty_wf_SubstLt; eauto.
    + eapply ty_wf_SubstLt; [exact HwfT|]. apply SubstLt_ty. exact HSub.
    + rewrite is_abs_subst_lt_in_tm. exact HisAbs.
    + apply (IHbody R n (bind_ty (subst_lt_in_ty n R bound) :: G')
        (SubstLt_ty R n Γ G' bound HSub)
        (ctx_lt_closed_from_bind_ty n Γ bound Hlt)
        (ctx_schemas_lt_closed_from_bind_ty n Γ bound Hschemas)).
  - intros Γ t B U S Ht IH HwfS Hsub HnlArg R n G' HSub Hlt Hschemas.
    simpl. rewrite subst_lt_in_ty_subst_ty_comm.
    eapply T_TyApp.
    + eapply T_Sub.
      * apply (IH R n G' HSub Hlt Hschemas).
      * apply type_ty_all_narrow_bound.
        -- eapply sub_SubstLt; eauto.
        -- pose proof (typing_implies_wf Γ t (type_ty_all B U) Ht) as HwfAll.
           inversion HwfAll; subst.
           eapply ty_wf_SubstLt; [eassumption|].
           apply SubstLt_ty. exact HSub.
    + eapply ty_wf_SubstLt; eauto.
    + apply SA_Refl. eapply ty_wf_SubstLt; eauto.
    + apply ty_app_arg_no_local_self.
  - intros Γ body T HwfT HisAbs Hbody IHbody R n G' HSub Hlt Hschemas.
    simpl. apply T_LtLam.
    + eapply ty_wf_SubstLt; [exact HwfT|]. apply SubstLt_lt. exact HSub.
    + rewrite is_abs_subst_lt_in_tm. exact HisAbs.
    + apply (IHbody (shift_lt 1 0 R) (S n) (bind_lt lt_local :: G')
        (SubstLt_bind_lt_closed lt_local R n Γ G' HSub I)
        (ctx_lt_closed_from_bind_lt n Γ lt_local Hlt)
        (ctx_schemas_lt_closed_from_bind_lt n Γ lt_local Hschemas)).
  - intros Γ t T l Ht IH Hwfl R n G' HSub Hlt Hschemas.
    simpl. rewrite <- subst_lt_in_ty_subst_lt_in_ty_comm_head.
    eapply T_LtApp.
    + apply (IH R n G' HSub Hlt Hschemas).
    + eapply lt_wf_SubstLt; eauto.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs Hctor Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs
           Hresult Hshape Hresult_eff Hwfl HltSub Hbounded Hlen_vs Hargs IHargs
           R n G' HSub Hlt Hschemas.
    simpl. rewrite subst_lt_in_tm_go_eq_map.
    eapply T_Ctor with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := List.map (subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R)) sigma_fields)
      (result_ty_schema := subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R) result_ty_schema)
      (lts := List.map (subst_lt n R) lts)
      (rho_fields := List.map (subst_lt_in_ty n R) rho_fields)
      (result_tag := result_tag) (l := subst_lt n R l).
    + rewrite (SubstLt_lookup_ctor R n Γ G' HSub K). rewrite Hctor. reflexivity.
    + rewrite (SubstLt_lookup_eff R n Γ G' HSub K). rewrite Heff. reflexivity.
    + rewrite List.length_map. exact Hlen_lts.
    + eapply lifetimes_wf_SubstLt; eauto.
    + subst rho_fields. symmetry.
      change (subst_lt_in_ty_list n R Ts) with (List.map (subst_lt_in_ty n R) Ts).
      apply inst_ctor_type_list_subst_lt. exact Hlen_lts.
    + change (List.length (List.map (subst_lt_in_ty n R) Ts) = n_ty).
      rewrite List.length_map. exact Hlen_Ts.
    + eapply types_wf_SubstLt; eauto.
    + subst result_ty. symmetry.
      change (subst_lt_in_ty_list n R Ts) with (List.map (subst_lt_in_ty n R) Ts).
      apply inst_ctor_type_subst_lt. exact Hlen_lts.
    + subst result_ty. rewrite Hshape. reflexivity.
    + rewrite (SubstLt_lookup_eff R n Γ G' HSub result_tag). rewrite Hresult_eff. reflexivity.
    + eapply lt_wf_SubstLt; eauto.
    + rewrite lt_of_ty_list_subst_lt. rewrite lt_of_ty_subst_lt. eapply lt_sub_SubstLt; eauto.
    + exact (Forall_lt_sub_SubstLt Γ lts l Hbounded R n G' HSub).
    + rewrite List.length_map. rewrite Hlen_vs. symmetry. apply List.length_map.
    + eapply Forall2_typing_SubstLt_closed_from; eauto.
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γyes yes_body eta elim_result no_body
           HKne Hctor Heff Hlts Hrho Hlen_Ts HwfTs Hscrut_result Hscrut_shape
           Hresult_eff Hresult_ne HwfDelta Hresult_l Hscrut IHscrut Harity HΓyes
           Hyes IHyes Helim Hno IHno R n G' HSub Hlt Hschemas.
    subst Γyes. simpl.
    assert (HTsClosed : tys_lt_closed n Ts) by (eapply types_wf_lt_closed_from; eauto).
    assert (HrhosClosed : tys_lt_closed (n + n_lt) rho_fields).
    { subst rho_fields. rewrite Hlts. replace (n + n_lt) with (n_lt + n) by lia.
      eapply inst_ctor_type_list_lt_var_list_lt_closed; eauto.
      destruct Hschemas as [HctorClosed _].
      destruct (HctorClosed K n_lt n_ty sigma_fields result_ty_schema Hctor) as [HfieldsClosed _].
      exact HfieldsClosed. }
    eapply T_Match with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := List.map (subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R)) sigma_fields)
      (result_ty_schema := subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R) result_ty_schema)
      (Ts := List.map (subst_lt_in_ty n R) Ts)
      (Delta := subst_lt n R Delta)
      (lts := lt_var_list n_lt)
      (rho_fields := rho_fields)
      (scrut_result_ty := subst_lt_in_ty n R scrut_result_ty)
      (result_tag := result_tag) (result_l := subst_lt n R result_l)
      (Γ' := push_lt_vars n_lt Delta G')
      (eta := subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R) eta).
    + exact HKne.
    + rewrite (SubstLt_lookup_ctor R n Γ G' HSub K). rewrite Hctor. reflexivity.
    + rewrite (SubstLt_lookup_eff R n Γ G' HSub K). rewrite Heff. reflexivity.
    + reflexivity.
    + subst rho_fields.
      change (subst_lt_in_ty_list n R Ts) with (List.map (subst_lt_in_ty n R) Ts).
      rewrite (subst_lt_in_type_list_closed Ts n R HTsClosed).
      destruct Hschemas as [HctorClosed _].
      destruct (HctorClosed K n_lt n_ty sigma_fields result_ty_schema Hctor) as [HfieldsClosed _].
      rewrite (subst_lt_in_type_list_closed sigma_fields (n_lt + n) (shift_lt n_lt 0 R) HfieldsClosed).
      rewrite Hlts.
      reflexivity.
    + change (List.length (List.map (subst_lt_in_ty n R) Ts) = n_ty).
      rewrite List.length_map. exact Hlen_Ts.
    + eapply types_wf_SubstLt; eauto.
    + subst scrut_result_ty. rewrite <- inst_ctor_type_subst_lt by (rewrite repeat_length; reflexivity).
      rewrite List.map_repeat. reflexivity.
    + subst scrut_result_ty. rewrite Hscrut_shape. reflexivity.
    + rewrite (SubstLt_lookup_eff R n Γ G' HSub result_tag). rewrite Hresult_eff. reflexivity.
    + exact Hresult_ne.
    + eapply lt_wf_SubstLt; eauto.
    + eapply lt_sub_SubstLt; eauto.
    + apply (IHscrut R n G' HSub Hlt Hschemas).
    + exact Harity.
    + rewrite subst_lt_closed_lifetime by (eapply lt_wf_closed_from; eauto). reflexivity.
    + apply (IHyes (shift_lt n_lt 0 R) (n_lt + n)
        (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
          (push_lt_vars n_lt Delta G') rho_fields)).
      * replace (n_lt + n) with (n + n_lt) by lia.
        apply SubstLt_fold_bind_tm_closed.
        -- apply SubstLt_push_lt_vars_closed.
           ++ exact HSub.
           ++ eapply lt_wf_closed_from; eauto.
          -- exact HrhosClosed.
      * replace (n_lt + n) with (n + n_lt) by lia.
        apply ctx_lt_closed_from_fold_bind_tm.
        apply ctx_lt_closed_from_push_lt_vars. exact Hlt.
      * replace (n_lt + n) with (n + n_lt) by lia.
        apply ctx_schemas_lt_closed_from_fold_bind_tm.
        apply ctx_schemas_lt_closed_from_push_lt_vars. exact Hschemas.
    + rewrite shift_lt_subst_lt_comm_many0.
      apply elim_ty_n_subst_lt_shifted. exact Helim.
    + apply (IHno R n G' HSub Hlt Hschemas).
  - intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff Hlen HwfTs HwfTR Hsig Hret Hop IHop R n G' HSub Hlt Hschemas.
    simpl.
    eapply T_Cap with
      (n_α := n_α) (n_β := n_β)
      (sig := subst_lt_in_ty n R sig) (ret := subst_lt_in_ty n R ret)
      (sig_β := subst_lt_in_ty n R sig_β) (ret_β := subst_lt_in_ty n R ret_β).
    + rewrite (SubstLt_lookup_eff R n Γ G' HSub E_tag). rewrite Heff. reflexivity.
    + change (List.length (List.map (subst_lt_in_ty n R) Ts) = n_α).
      rewrite List.length_map. exact Hlen.
    + eapply types_wf_SubstLt; eauto.
    + eapply ty_wf_SubstLt; eauto.
    + subst sig_β. symmetry.
      change (inst_op_alpha n_α (List.map (subst_lt_in_ty n R) Ts) n_β (subst_lt_in_ty n R sig) =
        subst_lt_in_ty n R (inst_op_alpha n_α Ts n_β sig)).
      apply inst_op_alpha_subst_lt.
    + subst ret_β. symmetry.
      change (inst_op_alpha n_α (List.map (subst_lt_in_ty n R) Ts) n_β (subst_lt_in_ty n R ret) =
        subst_lt_in_ty n R (inst_op_alpha n_α Ts n_β ret)).
      apply inst_op_alpha_subst_lt.
    + replace (shift_ty n_β 0 (subst_lt_in_ty n R T_R))
        with (subst_lt_in_ty n R (shift_ty n_β 0 T_R)).
      2:{ rewrite <- shift_ty_subst_lt_in_ty_commute. reflexivity. }
      apply (IHop R n
        (bind_tm (subst_lt_in_ty n R sig_β) ::
         bind_tm (subst_lt_in_ty n R (type_fun ret_β lt_local (shift_ty n_β 0 T_R))) ::
         push_ty_vars n_β any_at_free G')).
      * apply SubstLt_tm. apply SubstLt_tm. apply SubstLt_push_ty_vars_any_at_free. exact HSub.
      * repeat apply ctx_lt_closed_from_bind_tm.
        apply ctx_lt_closed_from_push_ty_vars. exact Hlt.
      * repeat apply ctx_schemas_lt_closed_from_bind_tm.
        apply ctx_schemas_lt_closed_from_push_ty_vars. exact Hschemas.
  - intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hsig Hret Hop IHop Hbody IHbody
           R n G' HSub Hlt Hschemas.
    simpl.
    eapply T_Handle with
      (n_α := n_α) (n_β := n_β)
      (sig := subst_lt_in_ty n R sig) (ret := subst_lt_in_ty n R ret)
      (T_B := subst_lt_in_ty n R T_B)
      (sig_β := subst_lt_in_ty n R sig_β) (ret_β := subst_lt_in_ty n R ret_β).
    + rewrite (SubstLt_lookup_eff R n Γ G' HSub E_tag). rewrite Heff. reflexivity.
    + change (List.length (List.map (subst_lt_in_ty n R) Ts) = n_α).
      rewrite List.length_map. exact Hlen.
    + eapply types_wf_SubstLt; eauto.
    + eapply ty_wf_SubstLt; eauto.
    + eapply ty_wf_SubstLt; eauto.
    + eapply no_local_ty_G_SubstLt; eauto.
    + eapply sub_SubstLt; eauto.
    + subst sig_β. symmetry.
      change (inst_op_alpha n_α (List.map (subst_lt_in_ty n R) Ts) n_β (subst_lt_in_ty n R sig) =
        subst_lt_in_ty n R (inst_op_alpha n_α Ts n_β sig)).
      apply inst_op_alpha_subst_lt.
    + subst ret_β. symmetry.
      change (inst_op_alpha n_α (List.map (subst_lt_in_ty n R) Ts) n_β (subst_lt_in_ty n R ret) =
        subst_lt_in_ty n R (inst_op_alpha n_α Ts n_β ret)).
      apply inst_op_alpha_subst_lt.
    + replace (shift_ty n_β 0 (subst_lt_in_ty n R T_R))
        with (subst_lt_in_ty n R (shift_ty n_β 0 T_R)).
      2:{ rewrite <- shift_ty_subst_lt_in_ty_commute. reflexivity. }
      apply (IHop R n
        (bind_tm (subst_lt_in_ty n R sig_β) ::
         bind_tm (subst_lt_in_ty n R (type_fun ret_β lt_local (shift_ty n_β 0 T_R))) ::
         push_ty_vars n_β any_at_free G')).
      * apply SubstLt_tm. apply SubstLt_tm. apply SubstLt_push_ty_vars_any_at_free. exact HSub.
      * repeat apply ctx_lt_closed_from_bind_tm.
        apply ctx_lt_closed_from_push_ty_vars. exact Hlt.
      * repeat apply ctx_schemas_lt_closed_from_bind_tm.
        apply ctx_schemas_lt_closed_from_push_ty_vars. exact Hschemas.
    + apply (IHbody R n (bind_tm (subst_lt_in_ty n R (type_ctor E_tag lt_local Ts)) :: G')
      (SubstLt_tm R n Γ G' (type_ctor E_tag lt_local Ts) HSub)
        (ctx_lt_closed_from_bind_tm n Γ (type_ctor E_tag lt_local Ts) Hlt)
        (ctx_schemas_lt_closed_from_bind_tm n Γ (type_ctor E_tag lt_local Ts) Hschemas)).
  - intros Γ recv arg E_tag Delta Ts Ss n_α n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg
         R n G' HSub Hlt Hschemas.
    simpl. eapply T_Perform with
      (n_α := n_α) (n_β := n_β)
      (sig := subst_lt_in_ty n R sig) (ret := subst_lt_in_ty n R ret)
      (sig_inst := subst_lt_in_ty n R sig_inst) (ret_inst := subst_lt_in_ty n R ret_inst).
    + apply (IHrecv R n G' HSub Hlt Hschemas).
    + rewrite (SubstLt_lookup_eff R n Γ G' HSub E_tag). rewrite Heff. reflexivity.
    + change (List.length (List.map (subst_lt_in_ty n R) Ts) = n_α).
      rewrite List.length_map. exact Hlen_Ts.
    + change (List.length (List.map (subst_lt_in_ty n R) Ss) = n_β).
      rewrite List.length_map. exact Hlen_Ss.
    + eapply types_wf_SubstLt; eauto.
    + eapply forallb_no_local_ty_G_SubstLt; eauto.
    + subst sig_inst. symmetry.
      change (inst_op_arg n_α (List.map (subst_lt_in_ty n R) Ts)
        n_β (List.map (subst_lt_in_ty n R) Ss) (subst_lt_in_ty n R sig) =
        subst_lt_in_ty n R (inst_op_arg n_α Ts n_β Ss sig)).
      apply inst_op_arg_subst_lt.
    + eapply no_local_ty_G_SubstLt; eauto.
    + subst ret_inst. symmetry.
      change (inst_op_arg n_α (List.map (subst_lt_in_ty n R) Ts)
        n_β (List.map (subst_lt_in_ty n R) Ss) (subst_lt_in_ty n R ret) =
        subst_lt_in_ty n R (inst_op_arg n_α Ts n_β Ss ret)).
      apply inst_op_arg_subst_lt.
    + eapply ty_wf_SubstLt; eauto.
    + apply (IHarg R n G' HSub Hlt Hschemas).
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH R n G' HSub Hlt Hschemas.
    simpl. apply T_HandlerM.
    + eapply ty_wf_SubstLt; eauto.
    + eapply ty_wf_SubstLt; eauto.
    + eapply no_local_ty_G_SubstLt; eauto.
    + eapply sub_SubstLt; eauto.
    + apply (IH R n G' HSub Hlt Hschemas).
  - intros Γ m b A T_B T_R HwfA HwfTB HwfTR HnoLocal Hsub Hb IHb R n G' HSub Hlt Hschemas.
    simpl. apply T_Resume.
    + eapply ty_wf_SubstLt; eauto.
    + eapply ty_wf_SubstLt; eauto.
    + eapply ty_wf_SubstLt; eauto.
    + eapply no_local_ty_G_SubstLt; eauto.
    + eapply sub_SubstLt; eauto.
    + apply (IHb R n (bind_tm (subst_lt_in_ty n R A) :: G')
      (SubstLt_tm R n Γ G' A HSub)
        (ctx_lt_closed_from_bind_tm n Γ A Hlt)
        (ctx_schemas_lt_closed_from_bind_tm n Γ A Hschemas)).
Qed.

Lemma elim_ty_subst_ty_shifted : forall T lvar bound p T' c Sb,
  elim_ty lvar bound p T = Some T' ->
  elim_ty lvar bound p (subst_ty c (shift_lt_in_ty 1 lvar Sb) T) =
  Some (subst_ty c (shift_lt_in_ty 1 lvar Sb) T').
Proof.
  apply (type_list_ind
    (fun T => forall lvar bound p T' c Sb,
      elim_ty lvar bound p T = Some T' ->
      elim_ty lvar bound p (subst_ty c (shift_lt_in_ty 1 lvar Sb) T) =
      Some (subst_ty c (shift_lt_in_ty 1 lvar Sb) T'))
    (fun Ts => forall lvar bound p Ts' c Sb,
      (fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
         match Ts0 with
         | [] => Some []
         | A :: rest =>
             match elim_ty lvar bound p' A, go_list p' rest with
             | Some A', Some rest' => Some (A' :: rest')
             | _, _ => None
             end
         end) p Ts = Some Ts' ->
      (fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
         match Ts0 with
         | [] => Some []
         | A :: rest =>
             match elim_ty lvar bound p' A, go_list p' rest with
             | Some A', Some rest' => Some (A' :: rest')
             | _, _ => None
             end
         end) p (List.map (subst_ty c (shift_lt_in_ty 1 lvar Sb)) Ts) =
      Some (List.map (subst_ty c (shift_lt_in_ty 1 lvar Sb)) Ts'))).
  - intros m lvar bound p T' c Sb H. simpl in H. injection H as H; subst T'.
    rewrite subst_ty_var_eq.
    destruct (Nat.eqb m c) eqn:Heq.
    + apply elim_ty_shift_miss.
    + simpl. destruct (Nat.ltb c m); reflexivity.
  - intros A l B HA HB lvar bound p T' c Sb H. simpl in H.
    destruct (elim_ty lvar bound (flip_var p) A) as [A'|] eqn:HAe; try discriminate.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hle; try discriminate.
    destruct (elim_ty lvar bound p B) as [B'|] eqn:HBe; try discriminate.
    injection H as H; subst T'. simpl.
    rewrite (HA lvar bound (flip_var p) A' c Sb HAe).
    rewrite Hle.
    rewrite (HB lvar bound p B' c Sb HBe). reflexivity.
  - intros K l Ts HTs lvar bound p T' c Sb H. simpl in H.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hle; try discriminate.
    destruct ((fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
      match Ts0 with
      | [] => Some []
      | A :: rest =>
          match elim_ty lvar bound p' A, go_list p' rest with
          | Some A', Some rest' => Some (A' :: rest')
          | _, _ => None
          end
      end) var_inv Ts) as [Ts'|] eqn:HTse; try discriminate.
    injection H as H; subst T'. simpl. rewrite subst_ty_go_eq_map. rewrite Hle.
    rewrite (HTs lvar bound var_inv Ts' c Sb HTse). reflexivity.
  - intros A HA lvar bound p T' c Sb H. simpl in H.
    destruct (elim_ty (S lvar) (shift_lt 1 0 bound) p A) as [A'|] eqn:HAe; try discriminate.
    injection H as H; subst T'. simpl.
    replace (shift_lt_in_ty 1 0 (shift_lt_in_ty 1 lvar Sb))
      with (shift_lt_in_ty 1 (S lvar) (shift_lt_in_ty 1 0 Sb)).
    2:{ rewrite shift_lt_in_ty_swap_0. reflexivity. }
    rewrite (HA (S lvar) (shift_lt 1 0 bound) p A' c (shift_lt_in_ty 1 0 Sb) HAe).
    reflexivity.
  - intros B A HB HA lvar bound p T' c Sb H. simpl in H.
    destruct (elim_ty lvar bound (flip_var p) B) as [B'|] eqn:HBe; try discriminate.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HAe; try discriminate.
    injection H as H; subst T'. simpl.
    rewrite (HB lvar bound (flip_var p) B' c Sb HBe).
    replace (shift_ty 1 0 (shift_lt_in_ty 1 lvar Sb))
      with (shift_lt_in_ty 1 lvar (shift_ty 1 0 Sb)).
    2:{ rewrite shift_ty_shift_lt_in_ty_commute. reflexivity. }
    rewrite (HA lvar bound p A' (S c) (shift_ty 1 0 Sb) HAe).
    reflexivity.
  - intros lvar bound p Ts' c Sb H. simpl in H. injection H as H; subst Ts'. reflexivity.
  - intros A Ts HA HTs lvar bound p Ts' c Sb H. simpl in H.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HAe; try discriminate.
    destruct ((fix go_list (p' : variance) (Ts0 : list type) {struct Ts0} : option (list type) :=
      match Ts0 with
      | [] => Some []
      | A0 :: rest =>
          match elim_ty lvar bound p' A0, go_list p' rest with
          | Some A'', Some rest' => Some (A'' :: rest')
          | _, _ => None
          end
      end) p Ts) as [Ts0'|] eqn:HTse; try discriminate.
    injection H as H; subst Ts'. simpl.
    rewrite (HA lvar bound p A' c Sb HAe).
    rewrite (HTs lvar bound p Ts0' c Sb HTse). reflexivity.
Qed.

Lemma elim_ty_n_subst_ty_shifted : forall k bound p T T' c Sb,
  elim_ty_n k bound p T = Some T' ->
  elim_ty_n k bound p (subst_ty c (shift_lt_in_ty k 0 Sb) T) =
  Some (subst_ty c Sb T').
Proof.
  induction k as [|k IH]; intros bound p T T' c Sb H.
  - simpl in H. injection H as H; subst T'.
    rewrite shift_lt_in_ty_zero. reflexivity.
  - simpl in H. destruct (elim_ty 0 bound p T) as [T1|] eqn:HE; try discriminate.
    simpl.
    replace (shift_lt_in_ty (S k) 0 Sb)
      with (shift_lt_in_ty 1 0 (shift_lt_in_ty k 0 Sb)).
    2:{ rewrite shift_lt_in_ty_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    rewrite (elim_ty_subst_ty_shifted T 0 bound p T1 c (shift_lt_in_ty k 0 Sb) HE).
    rewrite subst_lt_in_ty_subst_ty_comm.
    replace (subst_lt_in_ty 0 lt_free (shift_lt_in_ty 1 0 (shift_lt_in_ty k 0 Sb)))
      with (shift_lt_in_ty k 0 Sb).
    2:{ rewrite subst_lt_in_ty_shift_cancel. reflexivity. }
    apply IH. exact H.
Qed.

(* Substituting `lts` for bounded schema variables `lt_var_list n_lt`  *)
(* yields direct schema instantiation.                                 *)
Lemma inst_ctor_type_subst_eq : forall n_lt n_ty lts Ts sigma_fields,
  List.length lts = n_lt ->
  Forall (ctor_field_bounded_ty n_lt)
         (List.map (inst_ty_vars n_ty (List.map (shift_lt_in_ty n_lt 0) Ts)) sigma_fields) ->
  subst_list_lt_in_ty_each lts
    (List.map (inst_ctor_type n_lt n_ty (lt_var_list n_lt) Ts) sigma_fields)
  = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields.
Proof.
  intros n_lt n_ty lts Ts sigma_fields Hlen Hbounded.
  unfold subst_list_lt_in_ty_each.
  induction sigma_fields as [|sigma rest IH]; simpl in *.
  - reflexivity.
  - pose proof Hlen as Hlen0.
    inversion Hbounded as [|T Ts' Hhead Htail Heq]; subst.
    simpl. f_equal.
    + unfold inst_ctor_type, inst_lt_vars.
      apply bounded_ctor_inst_type_core; [exact Hlen0 | exact Hhead].
    + apply IH. exact Htail.
Qed.

(* ================================================================== *)
(* typing_SubstTy support: lifetime/no-local helpers under type subst *)
(* (subst_ty never touches lifetime variables, so lt-judgements are   *)
(* preserved verbatim).                                               *)
(* ================================================================== *)

Lemma lt_wf_SubstTy : forall G l,
  lt_wf G l -> forall Sb n G', SubstTy Sb n G G' -> lt_wf G' l.
Proof.
  intros G l Hwf. induction Hwf; intros Sb n G' HS.
  - eapply LWF_Var. rewrite (SubstTy_lookup_lt Sb n Γ G' HS x). exact H.
  - apply LWF_Free.
  - apply LWF_Local.
  - apply LWF_Min; [eapply IHHwf1 | eapply IHHwf2]; eauto.
Qed.

Lemma lt_sub_SubstTy : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
  forall Sb n G', SubstTy Sb n G G' -> G' ⊢ₗ l1 <: l2.
Proof.
  intros G l1 l2 H.
  induction H as [Γ l Hwf|Γ l Hwf|Γ x Δ Hlk Hwf|Γ l Hwf
                 |Γ l1 l2 l3 H1 IH1 H2 IH2|Γ l1 l2 l H1 IH1 H2 IH2
                 |Γ l l1 l2 H1 IH1 Hwf2|Γ l l1 l2 H1 IH1 Hwf1];
    intros Sb n G' HS.
  - apply LS_Free. eapply lt_wf_SubstTy; eauto.
  - apply LS_Local. eapply lt_wf_SubstTy; eauto.
  - apply LS_Var.
    + rewrite (SubstTy_lookup_lt Sb n Γ G' HS x). exact Hlk.
    + eapply lt_wf_SubstTy; eauto.
  - apply LS_Refl. eapply lt_wf_SubstTy; eauto.
  - eapply LS_Trans; [apply (IH1 Sb n G' HS) | apply (IH2 Sb n G' HS)].
  - apply LS_MinL; [apply (IH1 Sb n G' HS) | apply (IH2 Sb n G' HS)].
  - apply LS_MinR1; [apply (IH1 Sb n G' HS) | eapply lt_wf_SubstTy; eauto].
  - apply LS_MinR2; [apply (IH1 Sb n G' HS) | eapply lt_wf_SubstTy; eauto].
Qed.

Lemma is_any_at_free_bound_subst_ty_true : forall B n Sb,
  is_any_at_free_bound B = true -> is_any_at_free_bound (subst_ty n Sb B) = true.
Proof.
  intros B n Sb H. destruct B as [| | K l Ts | |]; simpl in H; try discriminate.
  destruct l; try discriminate. destruct Ts; try discriminate. simpl. exact H.
Qed.

Lemma no_local_ty_G_var_bind_lt : forall D Γ x,
  no_local_ty_G (bind_lt D :: Γ) (type_var x) = no_local_ty_G Γ (type_var x).
Proof.
  intros D Γ x. cbn [no_local_ty_G]. simpl ctx_lookup_ty.
  destruct (ctx_lookup_ty Γ x) as [B|]; simpl;
    [apply is_any_at_free_bound_shift_lt | reflexivity].
Qed.

Lemma no_local_ty_G_var_bind_ty_S : forall B0 Γ x,
  no_local_ty_G (bind_ty B0 :: Γ) (type_var (S x)) = no_local_ty_G Γ (type_var x).
Proof.
  intros B0 Γ x. cbn [no_local_ty_G]. simpl ctx_lookup_ty.
  destruct (ctx_lookup_ty Γ x) as [B|]; simpl;
    [apply is_any_at_free_bound_shift_ty | reflexivity].
Qed.

(* Type substitution preserves no-local-ness, PROVIDED the replacement   *)
(* is no-local whenever the substituted variable is (i.e. has an         *)
(* Any'free bound).  This conditional is exactly `ty_app_arg_no_local`.  *)
Lemma no_local_ty_G_subst_ty : forall T Γ Sb n G',
  SubstTy Sb n Γ G' ->
  (no_local_ty_G Γ (type_var n) = true -> no_local_ty_G G' Sb = true) ->
  no_local_ty_G Γ T = true ->
  no_local_ty_G G' (subst_ty n Sb T) = true.
Proof.
  intro T.
  apply (type_list_ind
    (fun T => forall Γ Sb n G', SubstTy Sb n Γ G' ->
      (no_local_ty_G Γ (type_var n) = true -> no_local_ty_G G' Sb = true) ->
      no_local_ty_G Γ T = true -> no_local_ty_G G' (subst_ty n Sb T) = true)
    (fun Ts => forall Γ Sb n G', SubstTy Sb n Γ G' ->
      (no_local_ty_G Γ (type_var n) = true -> no_local_ty_G G' Sb = true) ->
      fold_right (fun A acc => andb (no_local_ty_G Γ A) acc) true Ts = true ->
      fold_right (fun A acc => andb (no_local_ty_G G' A) acc) true (List.map (subst_ty n Sb) Ts) = true)).
  - (* type_var x *) intros x Γ Sb n G' HS Hcond Hnl.
    destruct (Nat.eq_dec x n) as [Heq|Hne].
    + subst x. replace (subst_ty n Sb (type_var n)) with Sb
        by (simpl; rewrite Nat.eqb_refl; reflexivity).
      apply Hcond. exact Hnl.
    + rewrite (subst_ty_var_neq n Sb x Hne).
      cbn [no_local_ty_G] in Hnl |- *.
      rewrite (SubstTy_lookup_ty Sb n Γ G' HS x Hne).
      destruct (ctx_lookup_ty Γ x) as [B|] eqn:HB; simpl in Hnl |- *; [|discriminate].
      apply is_any_at_free_bound_subst_ty_true. exact Hnl.
  - (* type_fun *) intros A l B IHA IHB Γ Sb n G' HS Hcond Hnl.
    simpl in *. repeat rewrite Bool.andb_true_iff in Hnl.
    destruct Hnl as [HnlA [Hnll HnlB]].
    rewrite (IHA Γ Sb n G' HS Hcond HnlA), (IHB Γ Sb n G' HS Hcond HnlB), Hnll. reflexivity.
  - (* type_ctor *) intros K l Ts IHTs Γ Sb n G' HS Hcond Hnl.
    rewrite subst_ty_ctor_eq. simpl in *.
    rewrite !no_local_ty_G_go_eq_fold in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [Hnll HnlTs].
    rewrite Hnll, (IHTs Γ Sb n G' HS Hcond HnlTs). reflexivity.
  - (* type_lt_all *) intros A IHA Γ Sb n G' HS Hcond Hnl. simpl in Hnl |- *.
    apply (IHA (bind_lt lt_local :: Γ) (shift_lt_in_ty 1 0 Sb) n (bind_lt lt_local :: G')).
    + apply SubstTy_lt. exact HS.
    + intro Hn'.
      apply (no_local_ty_G_InsLt G' Sb 0 (bind_lt lt_local :: G') (InsLt_here lt_local G')).
      apply Hcond. rewrite <- (no_local_ty_G_var_bind_lt lt_local Γ n). exact Hn'.
    + exact Hnl.
  - (* type_ty_all *) intros B A IHB IHA Γ Sb n G' HS Hcond Hnl. simpl in Hnl |- *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlB HnlA].
    rewrite (IHB Γ Sb n G' HS Hcond HnlB).
    rewrite (IHA (bind_ty B :: Γ) (shift_ty 1 0 Sb) (S n)
              (bind_ty (subst_ty n Sb B) :: G')).
    + reflexivity.
    + apply SubstTy_ty. exact HS.
    + intro Hn'.
      apply (no_local_ty_G_InsTy G' Sb 0 (bind_ty (subst_ty n Sb B) :: G')
               (InsTy_here (subst_ty n Sb B) G')).
      apply Hcond. rewrite <- (no_local_ty_G_var_bind_ty_S B Γ n). exact Hn'.
    + exact HnlA.
  - (* nil *) intros Γ Sb n G' HS Hcond Hnl. reflexivity.
  - (* cons *) intros A Ts IHA IHTs Γ Sb n G' HS Hcond Hnl. simpl in *.
    apply Bool.andb_true_iff in Hnl. destruct Hnl as [HnlA HnlTs].
    rewrite (IHA Γ Sb n G' HS Hcond HnlA), (IHTs Γ Sb n G' HS Hcond HnlTs). reflexivity.
Qed.
(* The no-local side condition threaded through typing_SubstTy: when the
   substituted variable n is treated as no-local (its bound is Any@free),
   the replacement Sb must itself be no-local.  This is exactly
   ty_app_arg_no_local, supplied by T_TyApp at the use sites. *)
Definition subst_nl (Sb : type) (n : nat) (Γ G' : ctx) : Prop :=
  no_local_ty_G Γ (type_var n) = true -> no_local_ty_G G' Sb = true.

Lemma subst_nl_bind_ty : forall Sb n Γ G' B,
  subst_nl Sb n Γ G' ->
  subst_nl (shift_ty 1 0 Sb) (S n) (bind_ty B :: Γ) (bind_ty (subst_ty n Sb B) :: G').
Proof.
  intros Sb n Γ G' B H Hnl.
  apply (no_local_ty_G_InsTy G' Sb 0 (bind_ty (subst_ty n Sb B) :: G') (InsTy_here _ _)).
  apply H. rewrite no_local_ty_G_var_bind_ty_S in Hnl. exact Hnl.
Qed.

Lemma subst_nl_bind_lt : forall Sb n Γ G' D,
  subst_nl Sb n Γ G' ->
  subst_nl (shift_lt_in_ty 1 0 Sb) n (bind_lt D :: Γ) (bind_lt D :: G').
Proof.
  intros Sb n Γ G' D H Hnl.
  apply (no_local_ty_G_InsLt G' Sb 0 (bind_lt D :: G') (InsLt_here _ _)).
  apply H. rewrite no_local_ty_G_var_bind_lt in Hnl. exact Hnl.
Qed.

Lemma subst_nl_bind_tm : forall Sb n Γ G' A,
  subst_nl Sb n Γ G' ->
  subst_nl Sb n (bind_tm A :: Γ) (bind_tm (subst_ty n Sb A) :: G').
Proof.
  intros Sb n Γ G' A H Hnl.
  apply (no_local_ty_G_InsTm G' Sb (bind_tm (subst_ty n Sb A) :: G') (InsTm_here _ _)).
  apply H. cbn in Hnl. exact Hnl.
Qed.

Lemma subst_nl_push_ty_vars : forall k Sb n Γ G',
  subst_nl Sb n Γ G' ->
  subst_nl (shift_ty k 0 Sb) (k + n)
    (push_ty_vars k any_at_free Γ) (push_ty_vars k any_at_free G').
Proof.
  induction k as [|k IH]; intros Sb n Γ G' H; simpl.
  - rewrite shift_ty_zero. replace (0 + n) with n by lia. exact H.
  - replace (shift_ty (S k) 0 Sb) with (shift_ty k 0 (shift_ty 1 0 Sb)).
    2:{ rewrite shift_ty_fuse. replace (k + 1) with (S k) by lia. reflexivity. }
    replace (S (k + n)) with (k + S n) by lia.
    apply IH. rewrite <- (subst_ty_any_at_free n Sb).
    apply subst_nl_bind_ty. exact H.
Qed.

Lemma forallb_no_local_ty_G_subst_ty : forall Ss Sb n Γ G',
  SubstTy Sb n Γ G' -> subst_nl Sb n Γ G' ->
  forallb (no_local_ty_G Γ) Ss = true ->
  forallb (no_local_ty_G G') (List.map (subst_ty n Sb) Ss) = true.
Proof.
  induction Ss as [|S Ss IH]; intros Sb n Γ G' HSub Hnl H; simpl in *; [reflexivity|].
  apply Bool.andb_true_iff in H. destruct H as [HS HSs].
  rewrite (no_local_ty_G_subst_ty S Γ Sb n G' HSub Hnl HS).
  rewrite (IH Sb n Γ G' HSub Hnl HSs). reflexivity.
Qed.

(* ================================================================ *)
(* (The T_Ctor case of typing_SubstTy is now PROVEN below via the     *)
(* inst_ctor_fields_alignment escape-stability lemma — no longer an   *)
(* axiom.)  AXIOM: the T_Match case of typing_SubstTy — heavy         *)
(* inst_ctor / elim_ty_n plumbing under type substitution.           *)
(* ================================================================ *)
Axiom typing_SubstTy_match_case : forall Γ scrut K n_lt arity yes_body no_body T,
  Γ ⊢ₜ term_match scrut K n_lt arity yes_body no_body : T ->
  forall Sb n G', SubstTy Sb n Γ G' -> subst_nl Sb n Γ G' ->
  G' ⊢ₜ subst_ty_in_tm n Sb (term_match scrut K n_lt arity yes_body no_body) : subst_ty n Sb T.

Lemma typing_SubstTy : forall Γ t T,
  Γ ⊢ₜ t : T ->
  forall Sb n G', SubstTy Sb n Γ G' -> subst_nl Sb n Γ G' -> ctor_fields_closed Γ ->
  G' ⊢ₜ subst_ty_in_tm n Sb t : subst_ty n Sb T.
Proof.
  apply (typing_ind_forall2
    (fun Γ t T => forall Sb n G', SubstTy Sb n Γ G' -> subst_nl Sb n Γ G' -> ctor_fields_closed Γ ->
       G' ⊢ₜ subst_ty_in_tm n Sb t : subst_ty n Sb T)).
  - (* T_Var *)
    intros Γ x T Hlk HwfT Sb n G' HSub Hnl Hcfc.
    simpl. apply T_Var.
    + rewrite (SubstTy_lookup_tm Sb n Γ G' HSub x). rewrite Hlk. reflexivity.
    + eapply ty_wf_SubstTy; eauto.
  - (* T_Sub *)
    intros Γ t T U Ht IH Hsub Sb n G' HSub Hnl Hcfc.
    eapply T_Sub.
    + apply (IH Sb n G' HSub Hnl Hcfc).
    + eapply sub_SubstTy; eauto.
  - (* T_Lam *)
    intros Γ body A l B HwfA HwfB Hbody IHbody Hcap Sb n G' HSub Hnl Hcfc.
    simpl. apply T_Lam.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + apply (IHbody Sb n (bind_tm (subst_ty n Sb A) :: G')
        (SubstTy_tm Sb n Γ G' A HSub) (subst_nl_bind_tm Sb n Γ G' A Hnl)
        (ctor_fields_closed_bind_tm A Γ Hcfc)).
    + eapply LS_Trans.
      * apply (capture_lt_SubstTy_le Sb n Γ G' HSub body).
        apply (proj1 (lt_sub_wf Γ (capture_lt Γ body) l Hcap)).
      * eapply lt_sub_SubstTy; eauto.
  - (* T_App *)
    intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 Sb n G' HSub Hnl Hcfc.
    simpl. eapply T_App.
    + apply (IH1 Sb n G' HSub Hnl Hcfc).
    + apply (IH2 Sb n G' HSub Hnl Hcfc).
  - (* T_TyLam *)
    intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody Sb n G' HSub Hnl Hcfc.
    simpl. apply T_TyLam.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; [exact HwfT|]. apply SubstTy_ty. exact HSub.
    + rewrite is_abs_subst_ty_in_tm. exact HisAbs.
    + apply (IHbody (shift_ty 1 0 Sb) (S n) (bind_ty (subst_ty n Sb bound) :: G')
        (SubstTy_ty Sb n Γ G' bound HSub) (subst_nl_bind_ty Sb n Γ G' bound Hnl)
        (ctor_fields_closed_bind_ty bound Γ Hcfc)).
  - (* T_TyApp *)
    intros Γ t B U S Ht IH HwfS Hsub HnlArg Sb n G' HSub Hnl Hcfc.
    simpl. rewrite <- subst_ty_subst_ty_comm0.
    eapply T_TyApp.
    + eapply T_Sub.
      * apply (IH Sb n G' HSub Hnl Hcfc).
      * apply type_ty_all_narrow_bound.
        -- eapply sub_SubstTy; eauto.
        -- pose proof (typing_implies_wf Γ t (type_ty_all B U) Ht) as HwfAll.
           inversion HwfAll; subst.
           eapply ty_wf_SubstTy; [eassumption|].
           apply SubstTy_ty. exact HSub.
    + eapply ty_wf_SubstTy; eauto.
    + apply SA_Refl. eapply ty_wf_SubstTy; eauto.
    + apply ty_app_arg_no_local_self.
  - (* T_LtLam *)
    intros Γ body T HwfT HisAbs Hbody IHbody Sb n G' HSub Hnl Hcfc.
    simpl. apply T_LtLam.
    + eapply ty_wf_SubstTy; [exact HwfT|]. apply SubstTy_lt. exact HSub.
    + rewrite is_abs_subst_ty_in_tm. exact HisAbs.
    + apply (IHbody (shift_lt_in_ty 1 0 Sb) n (bind_lt lt_local :: G')
        (SubstTy_lt Sb n Γ G' lt_local HSub) (subst_nl_bind_lt Sb n Γ G' lt_local Hnl)
        (ctor_fields_closed_bind_lt lt_local Γ Hcfc)).
  - (* T_LtApp *)
    intros Γ t T l Ht IH Hwfl Sb n G' HSub Hnl Hcfc.
    simpl.
    replace (subst_ty n Sb (subst_lt_in_ty 0 l T))
      with (subst_lt_in_ty 0 l (subst_ty n (shift_lt_in_ty 1 0 Sb) T)).
    2:{ rewrite subst_lt_in_ty_subst_ty_comm. rewrite subst_lt_in_ty_shift_cancel. reflexivity. }
    eapply T_LtApp.
    + apply (IH Sb n G' HSub Hnl Hcfc).
    + eapply lt_wf_SubstTy; eauto.
  - (* T_Ctor *)
    intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs Hctor Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs
           Hresult Hshape Hresult_eff Hwfl HltSub Hbounded Hlen_vs Hargs IHargs
           Sb n G' HSub Hnl Hcfc.
    cbn [subst_ty_in_tm]. rewrite subst_ty_in_tm_go_eq_map_local. unfold subst_ty_list.
    pose proof (SubstTy_replacement_wf Sb n Γ G' HSub) as HwfSb.
    assert (HwfSbl : lt_wf G' (lt_of_ty Sb)) by (apply lt_of_ty_wf; exact HwfSb).
    assert (HwfMTs : types_wf G' (List.map (subst_ty n Sb) Ts)) by (eapply types_wf_SubstTy; eauto).
    assert (Hwfl' : lt_wf G' l) by (eapply lt_wf_SubstTy; [exact Hwfl | exact HSub]).
    assert (HFlts : Forall (lt_wf G') lts).
    { pose proof (lifetimes_wf_SubstTy Γ lts Hwflts Sb n G' HSub) as Hwf'.
      clear -Hwf'. induction Hwf'; constructor; assumption. }
    assert (HFTs : Forall (fun U => lt_wf G' (lt_of_ty U)) Ts).
    { assert (HF0 : Forall (fun U => lt_wf Γ (lt_of_ty U)) Ts).
      { clear -HwfTs. induction HwfTs; constructor; [apply lt_of_ty_wf; assumption | assumption]. }
      clear -HF0 HSub. induction HF0; constructor;
        [ eapply lt_wf_SubstTy; [eassumption | exact HSub] | assumption ]. }
    eapply T_Ctor with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := List.map
         (subst_ty (n_ty + n) (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb))) sigma_fields)
      (result_ty_schema :=
         subst_ty (n_ty + n) (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb)) result_ty_schema)
      (rho_fields := List.map (subst_ty n Sb) rho_fields)
      (result_tag := result_tag).
    + rewrite (SubstTy_lookup_ctor Sb n Γ G' HSub K). rewrite Hctor. reflexivity.
    + rewrite (SubstTy_lookup_eff Sb n Γ G' HSub K). rewrite Heff. reflexivity.
    + exact Hlen_lts.
    + eapply lifetimes_wf_SubstTy; eauto.
    + subst rho_fields. rewrite !List.map_map. apply List.map_ext_in. intros S _.
      symmetry. apply inst_ctor_type_subst_ty; [exact Hlen_lts | exact Hlen_Ts].
    + rewrite List.length_map. exact Hlen_Ts.
    + exact HwfMTs.
    + subst result_ty. symmetry. apply inst_ctor_type_subst_ty; [exact Hlen_lts | exact Hlen_Ts].
    + rewrite Hshape. rewrite subst_ty_ctor_eq. reflexivity.
    + rewrite (SubstTy_lookup_eff Sb n Γ G' HSub result_tag). rewrite Hresult_eff. reflexivity.
    + exact Hwfl'.
    + (* ESCAPE PREMISE — the substitution-stability payoff *)
      assert (HltSub' : G' ⊢ₗ lt_of_ty_list rho_fields <: lt_min l (lt_of_ty_list Ts)).
      { eapply lt_sub_SubstTy; [| exact HSub].
        rewrite Hshape in HltSub. rewrite lt_of_ty_ctor_eq in HltSub. exact HltSub. }
      rewrite Hshape. rewrite subst_ty_ctor_eq. rewrite lt_of_ty_ctor_eq.
      assert (Halign : G' ⊢ₗ lt_of_ty_list (List.map (subst_ty n Sb) rho_fields)
                  <: lt_min (lt_of_ty_list rho_fields) (lt_of_ty_list (List.map (subst_ty n Sb) Ts))).
      { rewrite Hrho. rewrite <- Hlen_lts, <- Hlen_Ts.
        apply inst_ctor_fields_alignment.
        - destruct (Hcfc K n_lt n_ty sigma_fields result_ty_schema Hctor) as [HltCl HtyCl].
          rewrite Hlen_lts, Hlen_Ts. apply tys_closed_Forall_and; assumption.
        - exact HFlts.
        - exact HFTs.
        - apply lt_of_ty_list_wf. exact HwfMTs. }
      eapply LS_Trans; [exact Halign |].
      apply LS_MinL.
      * eapply LS_Trans; [exact HltSub' |].
        apply lt_min_mono; [apply LS_Refl; exact Hwfl' |].
        apply lt_of_ty_list_subst_ty_ge; [exact HwfSbl | exact HwfMTs].
      * apply LS_MinR2; [apply LS_Refl; apply lt_of_ty_list_wf; exact HwfMTs | exact Hwfl'].
    + eapply Forall_impl; [| exact Hbounded].
      intros l0 Hl0. eapply lt_sub_SubstTy; [exact Hl0 | exact HSub].
    + rewrite !List.length_map. exact Hlen_vs.
    + clear -IHargs HSub Hnl Hcfc.
      induction IHargs as [|v rho vs' rhos' Hv Hrest IH]; simpl; constructor.
      * apply Hv; [exact HSub | exact Hnl | exact Hcfc].
      * exact IH.
  - (* T_Match *)
    intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γyes yes_body eta elim_result no_body
           HKne Hctor Heff Hlts Hrho Hlen_Ts HwfTs Hscrut_result Hscrut_shape
           Hresult_eff Hresult_ne HwfDelta Hresult_l Hscrut IHscrut Harity HΓyes
           Hyes IHyes Helim Hno IHno Sb n G' HSub Hnl Hcfc.
    assert (Hty : Γ ⊢ₜ term_match scrut K n_lt arity yes_body no_body : elim_result)
      by (eapply T_Match; eauto).
    exact (typing_SubstTy_match_case Γ scrut K n_lt arity yes_body no_body elim_result Hty Sb n G' HSub Hnl).
  - (* T_Cap *)
    intros Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β
           Heff Hlen HwfTs HwfTR Hsig Hret Hop IHop Sb n G' HSub Hnl Hcfc.
    simpl.
    eapply T_Cap with
      (n_α := n_α) (n_β := n_β)
      (sig := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) sig)
      (ret := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) ret)
      (sig_β := subst_ty (n_β + n) (shift_ty n_β 0 Sb) sig_β)
      (ret_β := subst_ty (n_β + n) (shift_ty n_β 0 Sb) ret_β).
    + rewrite (SubstTy_lookup_eff Sb n Γ G' HSub E_tag). rewrite Heff. reflexivity.
    + change (List.length (List.map (subst_ty n Sb) Ts) = n_α).
      rewrite List.length_map. exact Hlen.
    + eapply types_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + subst sig_β. symmetry. apply inst_op_alpha_subst_ty. exact Hlen.
    + subst ret_β. symmetry. apply inst_op_alpha_subst_ty. exact Hlen.
    + rewrite <- (shift_ty_many_subst_ty_comm0 n_β n Sb T_R).
      replace (n + n_β) with (n_β + n) by lia.
      eapply IHop.
      * apply SubstTy_tm. apply SubstTy_tm. apply SubstTy_push_ty_vars_any_at_free. exact HSub.
      * apply subst_nl_bind_tm. apply subst_nl_bind_tm. apply subst_nl_push_ty_vars. exact Hnl.
      * apply ctor_fields_closed_bind_tm. apply ctor_fields_closed_bind_tm.
        apply ctor_fields_closed_push_ty_vars. exact Hcfc.
  - (* T_Handle *)
    intros Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hsig Hret Hop IHop Hbody IHbody
           Sb n G' HSub Hnl Hcfc.
    simpl.
    eapply T_Handle with
      (n_α := n_α) (n_β := n_β)
      (sig := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) sig)
      (ret := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) ret)
      (T_B := subst_ty n Sb T_B)
      (sig_β := subst_ty (n_β + n) (shift_ty n_β 0 Sb) sig_β)
      (ret_β := subst_ty (n_β + n) (shift_ty n_β 0 Sb) ret_β).
    + rewrite (SubstTy_lookup_eff Sb n Γ G' HSub E_tag). rewrite Heff. reflexivity.
    + change (List.length (List.map (subst_ty n Sb) Ts) = n_α).
      rewrite List.length_map. exact Hlen.
    + eapply types_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + eapply no_local_ty_G_subst_ty; [eauto| exact Hnl |eauto].
    + eapply sub_SubstTy; eauto.
    + subst sig_β. symmetry. apply inst_op_alpha_subst_ty. exact Hlen.
    + subst ret_β. symmetry. apply inst_op_alpha_subst_ty. exact Hlen.
    + rewrite <- (shift_ty_many_subst_ty_comm0 n_β n Sb T_R).
      replace (n + n_β) with (n_β + n) by lia.
      eapply IHop.
      * apply SubstTy_tm. apply SubstTy_tm. apply SubstTy_push_ty_vars_any_at_free. exact HSub.
      * apply subst_nl_bind_tm. apply subst_nl_bind_tm. apply subst_nl_push_ty_vars. exact Hnl.
      * apply ctor_fields_closed_bind_tm. apply ctor_fields_closed_bind_tm.
        apply ctor_fields_closed_push_ty_vars. exact Hcfc.
    + apply (IHbody Sb n (bind_tm (subst_ty n Sb (type_ctor E_tag lt_local Ts)) :: G')
        (SubstTy_tm Sb n Γ G' (type_ctor E_tag lt_local Ts) HSub)
        (subst_nl_bind_tm Sb n Γ G' (type_ctor E_tag lt_local Ts) Hnl)
        (ctor_fields_closed_bind_tm (type_ctor E_tag lt_local Ts) Γ Hcfc)).
  - (* T_Perform *)
    intros Γ recv arg E_tag Delta Ts Ss n_α n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg
           Sb n G' HSub Hnl Hcfc.
    simpl. eapply T_Perform with
      (n_α := n_α) (n_β := n_β)
      (sig := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) sig)
      (ret := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) ret)
      (sig_inst := subst_ty n Sb sig_inst) (ret_inst := subst_ty n Sb ret_inst).
    + apply (IHrecv Sb n G' HSub Hnl Hcfc).
    + rewrite (SubstTy_lookup_eff Sb n Γ G' HSub E_tag). rewrite Heff. reflexivity.
    + change (List.length (List.map (subst_ty n Sb) Ts) = n_α).
      rewrite List.length_map. exact Hlen_Ts.
    + change (List.length (List.map (subst_ty n Sb) Ss) = n_β).
      rewrite List.length_map. exact Hlen_Ss.
    + eapply types_wf_SubstTy; eauto.
    + eapply forallb_no_local_ty_G_subst_ty; [exact HSub | exact Hnl | exact HnoSs].
    + subst sig_inst. symmetry. apply inst_op_arg_subst_ty; assumption.
    + eapply no_local_ty_G_subst_ty; [eauto| exact Hnl |eauto].
    + subst ret_inst. symmetry. apply inst_op_arg_subst_ty; assumption.
    + eapply ty_wf_SubstTy; eauto.
    + apply (IHarg Sb n G' HSub Hnl Hcfc).
  - (* T_HandlerM *)
    intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH Sb n G' HSub Hnl Hcfc.
    simpl. apply T_HandlerM.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + eapply no_local_ty_G_subst_ty; [eauto| exact Hnl |eauto].
    + eapply sub_SubstTy; eauto.
    + apply (IH Sb n G' HSub Hnl Hcfc).
  - (* T_Resume *)
    intros Γ m b A T_B T_R HwfA HwfTB HwfTR HnoLocal Hsub Hb IHb Sb n G' HSub Hnl Hcfc.
    simpl. apply T_Resume.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + eapply ty_wf_SubstTy; eauto.
    + eapply no_local_ty_G_subst_ty; [eauto| exact Hnl |eauto].
    + eapply sub_SubstTy; eauto.
    + apply (IHb Sb n (bind_tm (subst_ty n Sb A) :: G')
        (SubstTy_tm Sb n Γ G' A HSub) (subst_nl_bind_tm Sb n Γ G' A Hnl)
        (ctor_fields_closed_bind_tm A Γ Hcfc)).
Qed.
