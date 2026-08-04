Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import ShiftLaws.
Require Import CtxMap.
Require Import Weakening.
Require Import SubstLt.
Require Import SubstTy.
Require Import ProgramCtx.
Require Import CtxClosed.
Require Import SubstTm.
Require Import SubstTactics.

(* ================================================================== *)
(* The lt/ty typing payloads: [typing_SubstLt] and [typing_SubstTy].  *)
(*                                                                    *)
(* Both live here — not in SubstLt.v / SubstTy.v — because both       *)
(* T_TyApp cases lean on the F<: narrowing bridge                     *)
(* [type_ty_all_narrow_bound] (SubstTy.v), which itself needs the     *)
(* wf-transport of BOTH substitutions; the dependency order therefore *)
(* forces the payloads below SubstTy.  The depth-0 instances (with    *)
(* SubstLt_here / SubstTy_here) are what Preservation.v's beta        *)
(* lemmas consume.                                                    *)
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

(* An effect op's sig/ret live under n_α + n_β type binders only.       *)
Definition subst_ty_eff_sig (n : nat) (Sb : type)
    (decl : nat * list (nat * type * type)) : nat * list (nat * type * type) :=
  let '(n_α, ops) := decl in
  (n_α,
   List.map (fun '(n_β, sig_ty, ret_ty) =>
       (n_β,
        subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) sig_ty,
        subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) ret_ty)) ops).

Ltac sig_extra_unfold ::= unfold subst_lt_ctor_sig, subst_lt_eff_sig,
  subst_ty_ctor_sig, subst_ty_eff_sig.

Lemma subst_ty_eff_sig_shift_cancel : forall Sb sig,
  subst_ty_eff_sig 0 Sb (shift_ty_eff_sig 1 0 sig) = sig.
Proof.
  intros Sb [n_α ops].
  unfold subst_ty_eff_sig, shift_ty_eff_sig. f_equal.
  induction ops as [|[[n_β sig_ty] ret_ty] ops IH]; simpl; [reflexivity|].
  rewrite !subst_ty_shift_cancel. rewrite IH. reflexivity.
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
  intros n Sb [n_α ops].
  unfold subst_ty_eff_sig, shift_ty_eff_sig. f_equal.
  induction ops as [|[[n_β sig_ty] ret_ty] ops IH]; simpl; [reflexivity|].
  assert (Hc : forall T,
    shift_ty 1 (n_α + n_β + 0) (subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) T)
    = subst_ty (n_α + n_β + S n) (shift_ty (n_α + n_β) 0 (shift_ty 1 0 Sb))
        (shift_ty 1 (n_α + n_β + 0) T)).
  { intro T. rewrite shift_ty_subst_ty_comm by lia.
    replace (S (n_α + n_β + n)) with (n_α + n_β + S n) by lia.
    f_equal. rewrite <- shift_ty_lift_shift. reflexivity. }
  rewrite !Hc. rewrite IH. reflexivity.
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
  intros n Sb [n_α ops].
  unfold subst_ty_eff_sig, shift_lt_eff_sig. f_equal.
  induction ops as [|[[n_β sig_ty] ret_ty] ops IH]; simpl; [reflexivity|].
  assert (Hc : forall T,
    shift_lt_in_ty 1 0 (subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) T)
    = subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 (shift_lt_in_ty 1 0 Sb))
        (shift_lt_in_ty 1 0 T)).
  { intro T. rewrite shift_lt_in_ty_subst_ty_comm. f_equal.
    rewrite shift_ty_shift_lt_in_ty_commute. reflexivity. }
  rewrite !Hc. rewrite IH. reflexivity.
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


Lemma inst_op_ty_args_subst_ty : forall n_alpha Ts n_beta T n Sb,
  List.length Ts = n_alpha ->
  inst_op_ty_args n_alpha (List.map (subst_ty n Sb) Ts) n_beta
    (subst_ty (n_alpha + n_beta + n) (shift_ty (n_alpha + n_beta) 0 Sb) T) =
  subst_ty (n_beta + n) (shift_ty n_beta 0 Sb)
    (inst_op_ty_args n_alpha Ts n_beta T).
Proof.
  intros n_alpha Ts n_beta T n Sb Hlen. unfold inst_op_ty_args.
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

Lemma inst_op_all_args_subst_ty : forall n_alpha Ts n_beta Ss T n Sb,
  List.length Ts = n_alpha ->
  List.length Ss = n_beta ->
  inst_op_all_args n_alpha (List.map (subst_ty n Sb) Ts)
              n_beta (List.map (subst_ty n Sb) Ss)
              (subst_ty (n_alpha + n_beta + n)
                (shift_ty (n_alpha + n_beta) 0 Sb) T) =
  subst_ty n Sb (inst_op_all_args n_alpha Ts n_beta Ss T).
Proof.
  intros n_alpha Ts n_beta Ss T n Sb HlenTs HlenSs.
  unfold inst_op_all_args.
  rewrite inst_op_ty_args_subst_ty by exact HlenTs.
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

(* MATCH-variant type-subst commutation.  Because [inst_ctor_type_open]    *)
(* output lives UNDER the n_lt pushed lt-binders, the substitution that    *)
(* commutes is at the SHIFTED [Sb] ([shift_lt_in_ty n_lt 0 Sb]) — exactly  *)
(* the form the yes-branch IH produces.  This is what makes the T_Match    *)
(* case of [typing_SubstTy] go through (no aliasing). *)
Lemma inst_ctor_type_open_subst_ty : forall n_lt n_ty Ts T n Sb,
  List.length Ts = n_ty ->
  inst_ctor_type_open n_lt n_ty (List.map (subst_ty n Sb) Ts)
    (subst_ty (n_ty + n) (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb)) T) =
  subst_ty n (shift_lt_in_ty n_lt 0 Sb) (inst_ctor_type_open n_lt n_ty Ts T).
Proof.
  intros n_lt n_ty Ts T n Sb HlenT.
  unfold inst_ctor_type_open.
  replace (List.map (shift_lt_in_ty n_lt 0) (List.map (subst_ty n Sb) Ts))
    with (List.map (subst_ty n (shift_lt_in_ty n_lt 0 Sb))
      (List.map (shift_lt_in_ty n_lt 0) Ts)).
  2:{ rewrite !List.map_map. apply List.map_ext. intro U.
      rewrite shift_lt_in_ty_subst_ty_comm_many. reflexivity. }
  replace (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb))
    with (shift_ty n_ty 0 (shift_lt_in_ty n_lt 0 Sb)).
  2:{ rewrite shift_ty_shift_lt_in_ty_commute. reflexivity. }
  rewrite inst_ty_vars_subst_ty by (rewrite List.length_map; exact HlenT).
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
(* PER-FIELD ESCAPE ALIGNMENT.  For a (ty- and lt-closed) constructor *)
(* field schema S, substituting a type through the instantiated field *)
(* raises its escape lifetime by at most the join of the substituted  *)
(* type arguments' escape lifetimes.  This is exactly what keeps the  *)
(* T_Ctor effective-lifetime escape premise stable under subst_ty.    *)
(* ================================================================== *)
Lemma inst_ctor_field_alignment : forall S lts Ts n Sb G,
  ty_lt_closed (List.length lts) S ->
  ty_ty_closed (List.length Ts) S ->
  Forall (lt_wf G) lts ->
  Forall (fun U => lt_wf G (lt_of_ty U)) Ts ->
  lt_wf G (lt_of_ty_list (List.map (subst_ty n Sb) Ts)) ->
  G ⊢ₗ lt_of_ty (subst_ty n Sb (inst_ctor_type (List.length lts) (List.length Ts) lts Ts S))
      <: lt_join (lt_of_ty (inst_ctor_type (List.length lts) (List.length Ts) lts Ts S))
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
             (lt_join (lt_of_ty S) (shift_lt (List.length lts) 0 (lt_of_ty_list Ts')))
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
  apply lt_join_mono; [| apply LS_Refl; exact HwfTs'].
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
Lemma lt_join_redistribute : forall G P Q c,
  lt_wf G P -> lt_wf G Q -> lt_wf G c ->
  G ⊢ₗ lt_join (lt_join P c) (lt_join Q c) <: lt_join (lt_join P Q) c.
Proof.
  intros G P Q c HP HQ Hc. apply LS_JoinL.
  - apply LS_JoinL.
    + apply LS_JoinR1; [apply LS_JoinR1; [apply LS_Refl; exact HP | exact HQ] | exact Hc].
    + apply LS_JoinR2; [apply LS_Refl; exact Hc | apply LWF_Join; assumption].
  - apply LS_JoinL.
    + apply LS_JoinR1; [apply LS_JoinR2; [apply LS_Refl; exact HQ | exact HP] | exact Hc].
    + apply LS_JoinR2; [apply LS_Refl; exact Hc | apply LWF_Join; assumption].
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
      <: lt_join (lt_of_ty_list
           (List.map (inst_ctor_type (List.length lts) (List.length Ts) lts Ts) sigma_fields))
           (lt_of_ty_list (List.map (subst_ty n Sb) Ts)).
Proof.
  intros sigma_fields lts Ts n Sb G HClosed HFlts HwfTs HwfTs'.
  assert (Hwfc : lt_wf G (lt_of_ty_list (List.map (subst_ty n Sb) Ts))) by exact HwfTs'.
  induction sigma_fields as [|S rest IH].
  - cbn [List.map]. rewrite !lt_of_ty_list_nil.
    apply LS_JoinR1; [apply LS_Free; apply LWF_Free | exact Hwfc].
  - inversion HClosed as [|S0 rest0 [HltC HtyC] HClosedRest]; subst.
    cbn [List.map]. rewrite !lt_of_ty_list_cons.
    pose proof (inst_ctor_field_alignment S lts Ts n Sb G HltC HtyC HFlts HwfTs HwfTs') as Hpe.
    pose proof (IH HClosedRest) as Hih.
    destruct (lt_sub_wf _ _ _ Hpe) as [_ HwfRpe].
    inversion HwfRpe as [| | |G0 a0 b0 HwfPe Hwfc0]; subst.
    destruct (lt_sub_wf _ _ _ Hih) as [_ HwfRih].
    inversion HwfRih as [| | |G1 a1 b1 HwfIh Hwfc1]; subst.
    eapply LS_Trans.
    + apply lt_join_mono; [exact Hpe | exact Hih].
    + apply lt_join_redistribute; assumption.
Qed.

Lemma free_tm_vars_subst_ty_in_tm : forall t cutoff n Sb,
  free_tm_vars cutoff (subst_ty_in_tm n Sb t) = free_tm_vars cutoff t.
Proof.
  apply (term_list_ind
    (fun t => forall cutoff n Sb,
      free_tm_vars cutoff (subst_ty_in_tm n Sb t) = free_tm_vars cutoff t)
    (fun ts => forall cutoff n Sb,
      List.concat (List.map (free_tm_vars cutoff) (List.map (subst_ty_in_tm n Sb) ts)) =
      List.concat (List.map (free_tm_vars cutoff) ts))
    (fun obs => forall cutoff n Sb,
      List.concat (List.map (fun p => free_tm_vars cutoff (snd p))
        (List.map (fun p =>
           (fst p, subst_ty_in_tm (n + fst p) (shift_ty (fst p) 0 Sb) (snd p))) obs)) =
      List.concat (List.map (fun p => free_tm_vars cutoff (snd p)) obs)));
    go_traverse.
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
      (fix go ts := match ts with [] => false | u :: rest => orb (has_rt_cap u) (go rest) end) ts)
    (fun obs => forall n Sb,
      existsb (fun p => has_rt_cap (snd p))
        (List.map (fun p =>
           (fst p, subst_ty_in_tm (n + fst p) (shift_ty (fst p) 0 Sb) (snd p))) obs) =
      existsb (fun p => has_rt_cap (snd p)) obs));
    go_traverse.
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
      wf_transport.
    + rewrite subst_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor.
      rewrite VB_ctor in HVB. inversion HwfLt; subst.
      apply lt_join_mono.
      * apply LS_Refl. wf_transport.
      * eapply IHT; eauto.
    + rewrite subst_ty_ltall_eq. rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + rewrite subst_ty_tyall_eq. rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + rewrite VBL_cons in HVB. destruct HVB as [Ha Hr].
      cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons.
      inversion HwfLt; subst.
      apply lt_join_mono; [eapply IHT; eauto | eapply IHT0; eauto].
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
        rewrite (lt_of_ty_ctx_var (S f') G' (subst_lt_var n n0)).
        rewrite (lt_of_ty_ctx_var (S f') G n0).
        rewrite (SubstTy_lookup_ty Sb n G G' HS n0 Hane).
        destruct (ctx_lookup_ty G n0) as [B0|] eqn:E; simpl.
          -- assert (HwfB0 : lt_wf G (lt_of_ty_ctx f' G B0)).
            { rewrite (lt_of_ty_ctx_var (S f') G n0), E in HwfLt. exact HwfLt. }
            apply (IHf B0 (S n0) HwfB0 (ctx_inv_all G n0 B0 E)). lia.
        -- apply LS_Refl. constructor.
    + rewrite subst_ty_fun_eq. rewrite !lt_of_ty_ctx_fun. apply LS_Refl.
      wf_transport.
    + rewrite subst_ty_ctor_eq. rewrite !lt_of_ty_ctx_ctor.
      rewrite VB_ctor in HVB. inversion HwfLt; subst.
      apply lt_join_mono.
      * apply LS_Refl. wf_transport.
      * eapply IHT; eauto.
    + rewrite subst_ty_ltall_eq. rewrite !lt_of_ty_ctx_ltall. apply LS_Refl. constructor.
    + rewrite subst_ty_tyall_eq. rewrite !lt_of_ty_ctx_tyall. apply LS_Refl. constructor.
    + cbn [List.map]. rewrite !lt_of_ty_ctx_list_nil. apply LS_Refl. constructor.
    + rewrite VBL_cons in HVB. destruct HVB as [Ha Hr].
      cbn [List.map]. rewrite !lt_of_ty_ctx_list_cons.
      inversion HwfLt; subst.
      apply lt_join_mono; [eapply IHT; eauto | eapply IHT0; eauto].
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
      * apply lt_join_mono.
        -- match goal with
          | Hh : lt_wf G (lt_of_ty_G G T) |-
            G' ⊢ₗ lt_of_ty_G G' (subst_ty n Sb T) <: lt_of_ty_G G T =>
            apply (lt_of_ty_G_SubstTy_le_wf Sb n G G' HS T Hh)
          end.
        -- match goal with
          | Ht : lt_wf G (fold_right _ _ xs) |- _ => apply IH; exact Ht
          end.
      * apply lt_join_mono.
        -- apply LS_Refl. constructor.
        -- match goal with
          | Ht : lt_wf G (fold_right _ _ xs) |- _ => apply IH; exact Ht
          end.
Qed.

Lemma subst_ty_any_at_free : forall n Sb, subst_ty n Sb any_at_free = any_at_free.
Proof. intros n Sb. reflexivity. Qed.


(* Type substitution crosses [push_match_bound] exactly as [push_lt_vars]:    *)
(* [SubstTy_lt] keeps each bind_lt bound (a lifetime, untouched by      *)
(* type subst), so the per-level shifted bounds are preserved.          *)
Lemma SubstTy_push_match_bound : forall k Delta Sb n G G',
  SubstTy Sb n G G' ->
  SubstTy (shift_lt_in_ty k 0 Sb) n
    (push_match_bound k Delta G) (push_match_bound k Delta G').
Proof.
  induction k as [|k IH]; intros Delta Sb n G G' HS; simpl.
  - rewrite shift_lt_in_ty_zero. exact HS.
  - replace (shift_lt_in_ty (S k) 0 Sb)
      with (shift_lt_in_ty 1 0 (shift_lt_in_ty k 0 Sb)).
    2:{ rewrite shift_lt_in_ty_fuse. replace (1 + k) with (S k) by lia. reflexivity. }
    apply SubstTy_lt. apply IH. exact HS.
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

(* Map form on the target: the bound fields are already substituted into a   *)
(* list (as the T_Match yes-branch provides them).                           *)
Lemma SubstTy_fold_bind_tm_map : forall rhos Sb n G G',
  SubstTy Sb n G G' ->
  SubstTy Sb n
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G rhos)
    (List.fold_right (fun rho G0 => bind_tm rho :: G0) G'
       (List.map (subst_ty n Sb) rhos)).
Proof.
  induction rhos as [|rho rhos IH]; intros Sb n G G' HS; simpl.
  - exact HS.
  - apply SubstTy_tm. apply IH. exact HS.
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
    destruct (elim_ty lvar bound (flip_variance p) A) as [A'|] eqn:HAe; try discriminate.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hle; try discriminate.
    destruct (elim_ty lvar bound p B) as [B'|] eqn:HBe; try discriminate.
    injection H as H; subst T'. rewrite subst_lt_in_ty_fun_eq. simpl.
    rewrite (HA lvar bound (flip_variance p) A' c R Hlt HAe).
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
    destruct (elim_ty lvar bound (flip_variance p) B) as [B'|] eqn:HBe; try discriminate.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HAe; try discriminate.
    injection H as H; subst T'. rewrite subst_lt_in_ty_tyall_eq. simpl.
    rewrite (HB lvar bound (flip_variance p) B' c R Hlt HBe).
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
      lt_of_ty_list (List.map (subst_lt_in_ty c R) Ts) = subst_lt c R (lt_of_ty_list Ts)));
    go_traverse.
Qed.

Lemma lt_of_ty_list_subst_lt : forall Ts n R,
  lt_of_ty_list (List.map (subst_lt_in_ty n R) Ts) = subst_lt n R (lt_of_ty_list Ts).
Proof.
  induction Ts as [|T Ts IH]; intros c R; simpl.
  - reflexivity.
  - rewrite lt_of_ty_subst_lt, IH. reflexivity.
Qed.

(* Escape side-condition transport under lifetime substitution. *)
Lemma sub_free_SubstLt : forall R n G G' T,
  SubstLt R n G G' -> G ⊢ₗ lt_of_ty_G G T <: lt_free ->
  G' ⊢ₗ lt_of_ty_G G' (subst_lt_in_ty n R T) <: lt_free.
Proof.
  intros R n G G' T HS H. rewrite (lt_of_ty_G_SubstLt R n G G' HS T).
  change lt_free with (subst_lt n R lt_free) at 1.
  wf_transport.
Qed.
#[export] Hint Resolve sub_free_SubstLt : ctxmap.

Lemma sub_free_list_SubstLt : forall R n G G' Ss,
  SubstLt R n G G' -> Forall (fun S => G ⊢ₗ lt_of_ty_G G S <: lt_free) Ss ->
  Forall (fun S => G' ⊢ₗ lt_of_ty_G G' S <: lt_free) (List.map (subst_lt_in_ty n R) Ss).
Proof.
  intros R n G G' Ss HS H. induction H; simpl; constructor;
    [eapply sub_free_SubstLt; eauto | auto].
Qed.
#[export] Hint Resolve sub_free_list_SubstLt : ctxmap.

(* GENERAL binder-removing/instantiating lt-substitution: NO closedness *)
(* premise.  Provable because T_Match pushes [push_match_bound], which   *)
(* is stable under SubstLt via [SubstLt_push_match_bound].  The          *)
(* T_Match case substitutes the field types and the scrutinee lifetime   *)
(* Delta (via [inst_ctor_type_open_subst_lt] and [SubstLt_push_match_bound]).   *)
(* This discharges [ltbeta_preserves] and [matchyes_preserves].          *)
Lemma typing_SubstLt : forall Γ t T,
  Γ ⊢ₜ t : T ->
  forall R n G',
    SubstLt R n Γ G' ->
    G' ⊢ₜ subst_lt_in_tm n R t : subst_lt_in_ty n R T.
Proof.
  apply (typing_ind_forall2
    (fun Γ t T => forall R n G',
      SubstLt R n Γ G' ->
      G' ⊢ₜ subst_lt_in_tm n R t : subst_lt_in_ty n R T)).
  - intros Γ x T Hlk HwfT R n G' HSub.
    simpl. apply T_Var.
    + rewrite (SubstLt_lookup_tm R n Γ G' HSub x). rewrite Hlk. reflexivity.
    + wf_transport.
  - intros Γ t T U Ht IH Hsub R n G' HSub.
    eapply T_Sub.
    + apply (IH R n G' HSub).
    + wf_transport.
  - intros Γ body A l B HwfA HwfB Hbody IHbody Hcap R n G' HSub.
    simpl. apply T_Lam.
    + wf_transport.
    + wf_transport.
    + apply (IHbody R n (bind_tm (subst_lt_in_ty n R A) :: G')
        (SubstLt_tm R n Γ G' A HSub)).
    + rewrite (capture_lt_SubstLt R n Γ G' HSub body).
      wf_transport.
  - intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 R n G' HSub.
    simpl. eapply T_App.
    + apply (IH1 R n G' HSub).
    + apply (IH2 R n G' HSub).
  - intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody R n G' HSub.
    simpl. apply T_TyLam.
    + wf_transport.
    + eapply ty_wf_SubstLt; [exact HwfT|]. apply SubstLt_ty. exact HSub.
    + rewrite is_abs_subst_lt_in_tm. exact HisAbs.
    + apply (IHbody R n (bind_ty (subst_lt_in_ty n R bound) :: G')
        (SubstLt_ty R n Γ G' bound HSub)).
  - intros Γ t B U S Ht IH HwfS Hsub R n G' HSub.
    simpl. rewrite subst_lt_in_ty_subst_ty_comm.
    eapply T_TyApp.
    + eapply T_Sub.
      * apply (IH R n G' HSub).
      * apply type_ty_all_narrow_bound.
        -- wf_transport.
        -- pose proof (typing_implies_wf Γ t (type_ty_all B U) Ht) as HwfAll.
           inversion HwfAll; subst.
           eapply ty_wf_SubstLt; [eassumption|].
           apply SubstLt_ty. exact HSub.
    + wf_transport.
    + apply SA_Refl. wf_transport.
  - intros Γ body T HwfT HisAbs Hbody IHbody R n G' HSub.
    simpl. apply T_LtLam.
    + eapply ty_wf_SubstLt; [exact HwfT|]. apply SubstLt_lt. exact HSub.
    + rewrite is_abs_subst_lt_in_tm. exact HisAbs.
    + apply (IHbody (shift_lt 1 0 R) (S n) (bind_lt lt_local :: G')
        (SubstLt_bind_lt_closed lt_local R n Γ G' HSub I)).
  - intros Γ t T l Ht IH Hwfl R n G' HSub.
    simpl. rewrite <- subst_lt_in_ty_subst_lt_in_ty_comm_head.
    eapply T_LtApp.
    + apply (IH R n G' HSub).
    + wf_transport.
  - intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs Hctor Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs
           Hresult Hshape Hresult_eff Hwfl HltSub Hbounded Hlen_vs Hargs IHargs
           R n G' HSub.
    simpl.    eapply T_Ctor with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := List.map (subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R)) sigma_fields)
      (result_ty_schema := subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R) result_ty_schema)
      (lts := List.map (subst_lt n R) lts)
      (rho_fields := List.map (subst_lt_in_ty n R) rho_fields)
      (result_tag := result_tag) (l := subst_lt n R l).
    + rewrite (SubstLt_lookup_ctor R n Γ G' HSub K). rewrite Hctor. reflexivity.
    + rewrite (SubstLt_lookup_eff R n Γ G' HSub K). rewrite Heff. reflexivity.
    + rewrite List.length_map. exact Hlen_lts.
    + wf_transport.
    + subst rho_fields. symmetry.
      change (map_subst_lt_in_ty n R Ts) with (List.map (subst_lt_in_ty n R) Ts).
      apply inst_ctor_type_list_subst_lt. exact Hlen_lts.
    + change (List.length (List.map (subst_lt_in_ty n R) Ts) = n_ty).
      rewrite List.length_map. exact Hlen_Ts.
    + wf_transport.
    + subst result_ty. symmetry.
      change (map_subst_lt_in_ty n R Ts) with (List.map (subst_lt_in_ty n R) Ts).
      apply inst_ctor_type_subst_lt. exact Hlen_lts.
    + subst result_ty. rewrite Hshape. reflexivity.
    + rewrite (SubstLt_lookup_eff R n Γ G' HSub result_tag). rewrite Hresult_eff. reflexivity.
    + wf_transport.
    + rewrite lt_of_ty_list_subst_lt. rewrite lt_of_ty_subst_lt. wf_transport.
    + exact (Forall_lt_sub_SubstLt Γ lts l Hbounded R n G' HSub).
    + rewrite List.length_map. rewrite Hlen_vs. symmetry. apply List.length_map.
    + eapply typings_SubstLt; eauto.
  - intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γyes yes_body eta elim_result no_body
           HKne Hctor Heff Hlts Hrho Hlen_Ts HwfTs Hscrut_result Hscrut_shape
           Hresult_eff Hresult_ne HwfDelta Hresult_l Hscrut IHscrut Harity HΓyes
           Hyes IHyes Helim Hno IHno R n G' HSub.
    subst Γyes. simpl.
    eapply T_Match with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := List.map (subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R)) sigma_fields)
      (result_ty_schema := subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R) result_ty_schema)
      (Ts := List.map (subst_lt_in_ty n R) Ts)
      (Delta := subst_lt n R Delta)
      (lts := lt_var_list n_lt)
      (rho_fields := List.map (subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R)) rho_fields)
      (scrut_result_ty := subst_lt_in_ty n R scrut_result_ty)
      (result_tag := result_tag) (result_l := subst_lt n R result_l)
      (Γ' := push_match_bound n_lt (subst_lt n R Delta) G')
      (eta := subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R) eta).
    + exact HKne.
    + rewrite (SubstLt_lookup_ctor R n Γ G' HSub K). rewrite Hctor. reflexivity.
    + rewrite (SubstLt_lookup_eff R n Γ G' HSub K). rewrite Heff. reflexivity.
    + reflexivity.
    + subst rho_fields. rewrite !List.map_map. apply List.map_ext. intro sigma.
      symmetry. apply inst_ctor_type_open_subst_lt.
    + change (List.length (List.map (subst_lt_in_ty n R) Ts) = n_ty).
      rewrite List.length_map. exact Hlen_Ts.
    + wf_transport.
    + subst scrut_result_ty. rewrite <- inst_ctor_type_subst_lt by (rewrite repeat_length; reflexivity).
      rewrite List.map_repeat. reflexivity.
    + subst scrut_result_ty. rewrite Hscrut_shape. reflexivity.
    + rewrite (SubstLt_lookup_eff R n Γ G' HSub result_tag). rewrite Hresult_eff. reflexivity.
    + exact Hresult_ne.
    + wf_transport.
    + wf_transport.
    + apply (IHscrut R n G' HSub).
    + rewrite List.length_map. exact Harity.
    + reflexivity.
    + apply (IHyes (shift_lt n_lt 0 R) (n_lt + n)
        (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
          (push_match_bound n_lt (subst_lt n R Delta) G')
          (List.map (subst_lt_in_ty (n_lt + n) (shift_lt n_lt 0 R)) rho_fields))).
      apply SubstLt_fold_bind_tm_map.
      apply SubstLt_push_match_bound. exact HSub.
    + rewrite shift_lt_subst_lt_comm_many0.
      apply elim_ty_n_subst_lt_shifted. exact Helim.
    + apply (IHno R n G' HSub).
  - intros Γ E_tag m Ts op_bodies n_α ops T_R
           Heff Hlen HwfTs HwfTR Hfst Hops IHops R n G' HSub.
    simpl. rewrite subst_lt_in_tm_ops_eq_map.
    eapply T_Cap with
      (n_α := n_α)
      (ops := List.map (fun osig =>
                 (op_nb osig,
                  subst_lt_in_ty n R (op_sig_ty osig),
                  subst_lt_in_ty n R (op_ret_ty osig))) ops).
    + rewrite (SubstLt_lookup_eff R n Γ G' HSub E_tag). rewrite Heff. simpl.
      do 2 f_equal. apply List.map_ext. intros [[nβ sg] rt]. reflexivity.
    + change (List.length (List.map (subst_lt_in_ty n R) Ts) = n_α).
      rewrite List.length_map. exact Hlen.
    + wf_transport.
    + wf_transport.
    + rewrite !List.map_map. exact Hfst.
    + clear Hops Heff. revert Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IHrest]; intros Hfst; simpl.
      * constructor.
      * simpl in Hfst. injection Hfst as Hnb Hfstrest.
        constructor; [| apply IHrest; exact Hfstrest ].
        destruct osig as [[nβ sg] rt].
        unfold op_nb, op_sig_ty, op_ret_ty in *. simpl in *.
        unfold op_body_ctx.
        try change (map_subst_lt_in_ty n R Ts) with (List.map (subst_lt_in_ty n R) Ts).
        try change ((fix go (l : list type) : list type :=
                   match l with
                   | [] => []
                   | A :: rest => subst_lt_in_ty n R A :: go rest
                   end) Ts) with (List.map (subst_lt_in_ty n R) Ts).
        replace (inst_op_ty_args n_α (List.map (subst_lt_in_ty n R) Ts) nβ (subst_lt_in_ty n R sg))
          with (subst_lt_in_ty n R (inst_op_ty_args n_α Ts nβ sg))
          by (symmetry; apply inst_op_ty_args_subst_lt).
        replace (inst_op_ty_args n_α (List.map (subst_lt_in_ty n R) Ts) nβ (subst_lt_in_ty n R rt))
          with (subst_lt_in_ty n R (inst_op_ty_args n_α Ts nβ rt))
          by (symmetry; apply inst_op_ty_args_subst_lt).
        replace (shift_ty nβ 0 (subst_lt_in_ty n R T_R))
          with (subst_lt_in_ty n R (shift_ty nβ 0 T_R))
          by (rewrite <- shift_ty_subst_lt_in_ty_commute; reflexivity).
        apply Hone.
        apply SubstLt_tm. apply SubstLt_tm. apply SubstLt_push_ty_vars_any_at_free. exact HSub.
  - intros Γ E_tag Ts op_bodies body n_α ops T_B T_R
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hfst Hops IHops Hbody IHbody
           R n G' HSub.
    simpl. rewrite subst_lt_in_tm_ops_eq_map.
    eapply T_Handle with
      (n_α := n_α)
      (ops := List.map (fun osig =>
                 (op_nb osig,
                  subst_lt_in_ty n R (op_sig_ty osig),
                  subst_lt_in_ty n R (op_ret_ty osig))) ops)
      (T_B := subst_lt_in_ty n R T_B).
    + rewrite (SubstLt_lookup_eff R n Γ G' HSub E_tag). rewrite Heff. simpl.
      do 2 f_equal. apply List.map_ext. intros [[nβ sg] rt]. reflexivity.
    + change (List.length (List.map (subst_lt_in_ty n R) Ts) = n_α).
      rewrite List.length_map. exact Hlen.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + rewrite !List.map_map. exact Hfst.
    + clear Hops Heff. revert Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IHrest]; intros Hfst; simpl.
      * constructor.
      * simpl in Hfst. injection Hfst as Hnb Hfstrest.
        constructor; [| apply IHrest; exact Hfstrest ].
        destruct osig as [[nβ sg] rt].
        unfold op_nb, op_sig_ty, op_ret_ty in *. simpl in *.
        unfold op_body_ctx.
        try change (map_subst_lt_in_ty n R Ts) with (List.map (subst_lt_in_ty n R) Ts).
        try change ((fix go (l : list type) : list type :=
                   match l with
                   | [] => []
                   | A :: rest => subst_lt_in_ty n R A :: go rest
                   end) Ts) with (List.map (subst_lt_in_ty n R) Ts).
        replace (inst_op_ty_args n_α (List.map (subst_lt_in_ty n R) Ts) nβ (subst_lt_in_ty n R sg))
          with (subst_lt_in_ty n R (inst_op_ty_args n_α Ts nβ sg))
          by (symmetry; apply inst_op_ty_args_subst_lt).
        replace (inst_op_ty_args n_α (List.map (subst_lt_in_ty n R) Ts) nβ (subst_lt_in_ty n R rt))
          with (subst_lt_in_ty n R (inst_op_ty_args n_α Ts nβ rt))
          by (symmetry; apply inst_op_ty_args_subst_lt).
        replace (shift_ty nβ 0 (subst_lt_in_ty n R T_R))
          with (subst_lt_in_ty n R (shift_ty nβ 0 T_R))
          by (rewrite <- shift_ty_subst_lt_in_ty_commute; reflexivity).
        apply Hone.
        apply SubstLt_tm. apply SubstLt_tm. apply SubstLt_push_ty_vars_any_at_free. exact HSub.
    + apply (IHbody R n (bind_tm (subst_lt_in_ty n R (type_ctor E_tag lt_local Ts)) :: G')
      (SubstLt_tm R n Γ G' (type_ctor E_tag lt_local Ts) HSub)).
  - intros Γ recv op arg E_tag Delta Ts Ss n_α ops n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hnth Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg
         R n G' HSub.
    simpl. eapply T_Perform with
      (n_α := n_α)
      (ops := List.map (fun osig =>
                 (op_nb osig,
                  subst_lt_in_ty n R (op_sig_ty osig),
                  subst_lt_in_ty n R (op_ret_ty osig))) ops)
      (n_β := n_β)
      (sig := subst_lt_in_ty n R sig) (ret := subst_lt_in_ty n R ret)
      (sig_inst := subst_lt_in_ty n R sig_inst) (ret_inst := subst_lt_in_ty n R ret_inst).
    + apply (IHrecv R n G' HSub).
    + rewrite (SubstLt_lookup_eff R n Γ G' HSub E_tag). rewrite Heff. simpl.
      do 2 f_equal. apply List.map_ext. intros [[nβ sg] rt]. reflexivity.
    + rewrite (map_nth_error _ _ _ Hnth). reflexivity.
    + change (List.length (List.map (subst_lt_in_ty n R) Ts) = n_α).
      rewrite List.length_map. exact Hlen_Ts.
    + change (List.length (List.map (subst_lt_in_ty n R) Ss) = n_β).
      rewrite List.length_map. exact Hlen_Ss.
    + wf_transport.
    + wf_transport.
    + subst sig_inst. symmetry.
      change (inst_op_all_args n_α (List.map (subst_lt_in_ty n R) Ts)
        n_β (List.map (subst_lt_in_ty n R) Ss) (subst_lt_in_ty n R sig) =
        subst_lt_in_ty n R (inst_op_all_args n_α Ts n_β Ss sig)).
      apply inst_op_all_args_subst_lt.
    + wf_transport.
    + subst ret_inst. symmetry.
      change (inst_op_all_args n_α (List.map (subst_lt_in_ty n R) Ts)
        n_β (List.map (subst_lt_in_ty n R) Ss) (subst_lt_in_ty n R ret) =
        subst_lt_in_ty n R (inst_op_all_args n_α Ts n_β Ss ret)).
      apply inst_op_all_args_subst_lt.
    + wf_transport.
    + apply (IHarg R n G' HSub).
  - intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH R n G' HSub.
    simpl. apply T_HandlerM.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + apply (IH R n G' HSub).
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
    destruct (elim_ty lvar bound (flip_variance p) A) as [A'|] eqn:HAe; try discriminate.
    destruct (elim_lt lvar bound p l) as [l'|] eqn:Hle; try discriminate.
    destruct (elim_ty lvar bound p B) as [B'|] eqn:HBe; try discriminate.
    injection H as H; subst T'. simpl.
    rewrite (HA lvar bound (flip_variance p) A' c Sb HAe).
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
    injection H as H; subst T'. simpl. rewrite Hle.
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
    destruct (elim_ty lvar bound (flip_variance p) B) as [B'|] eqn:HBe; try discriminate.
    destruct (elim_ty lvar bound p A) as [A'|] eqn:HAe; try discriminate.
    injection H as H; subst T'. simpl.
    rewrite (HB lvar bound (flip_variance p) B' c Sb HBe).
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


(* [lt_wf_SubstTy]/[lt_sub_SubstTy] (subst_ty never touches lifetime  *)
(* variables, so lt-judgements are preserved verbatim) live in        *)
(* SubstTy.v.                                                         *)

(* Escape side-condition transport under type substitution.  Unlike the      *)
(* lifetime/insertion cases this is a SUBTYPING (not an equality), but it     *)
(* still composes by transitivity through [lt_of_ty_G_SubstTy_le] — and       *)
(* needs NO no-local side condition (that is the whole point of the         *)
(* [<: lt_free] relational formulation: it is monotone under substitution).   *)
Lemma sub_free_SubstTy : forall Sb n G G' T,
  SubstTy Sb n G G' -> ty_wf G T -> G ⊢ₗ lt_of_ty_G G T <: lt_free ->
  G' ⊢ₗ lt_of_ty_G G' (subst_ty n Sb T) <: lt_free.
Proof.
  intros Sb n G G' T HS Hwf H.
  eapply LS_Trans; [ eapply lt_of_ty_G_SubstTy_le; eauto | eapply lt_sub_SubstTy; eauto ].
Qed.
#[export] Hint Resolve sub_free_SubstTy : ctxmap.

Lemma sub_free_list_SubstTy : forall Sb n G G' Ss,
  SubstTy Sb n G G' -> types_wf G Ss ->
  Forall (fun S => G ⊢ₗ lt_of_ty_G G S <: lt_free) Ss ->
  Forall (fun S => G' ⊢ₗ lt_of_ty_G G' S <: lt_free) (List.map (subst_ty n Sb) Ss).
Proof.
  intros Sb n G G' Ss HS Hwf H. revert Hwf H.
  induction Ss as [|x l IH]; intros Hwf H; simpl; [constructor|].
  inversion Hwf as [|G0 T0 Ts0 Hwfx Hwfl]; subst.
  inversion H as [|x0 l0 Hhx Hhl]; subst.
  constructor; [eapply sub_free_SubstTy; eauto | apply IH; assumption].
Qed.
#[export] Hint Resolve sub_free_list_SubstTy : ctxmap.


(* ================================================================== *)
(* The T_Match case of [typing_SubstTy]: [rho_fields] uses the        *)
(* inst_ctor_type_open (inst_ty_vars-only) form, so it lives          *)
(* consistently in the pushed context, and the commutation            *)
(* [inst_ctor_type_open_subst_ty] (at the SHIFTED Sb) closes both     *)
(* premise 5 and the yes-branch.                                      *)
(* ================================================================== *)

Lemma typing_SubstTy : forall Γ t T,
  Γ ⊢ₜ t : T ->
  forall Sb n G', SubstTy Sb n Γ G' -> ctor_fields_closed Γ ->
  G' ⊢ₜ subst_ty_in_tm n Sb t : subst_ty n Sb T.
Proof.
  apply (typing_ind_forall2
    (fun Γ t T => forall Sb n G', SubstTy Sb n Γ G' -> ctor_fields_closed Γ ->
       G' ⊢ₜ subst_ty_in_tm n Sb t : subst_ty n Sb T)).
  - (* T_Var *)
    intros Γ x T Hlk HwfT Sb n G' HSub Hcfc.
    simpl. apply T_Var.
    + rewrite (SubstTy_lookup_tm Sb n Γ G' HSub x). rewrite Hlk. reflexivity.
    + wf_transport.
  - (* T_Sub *)
    intros Γ t T U Ht IH Hsub Sb n G' HSub Hcfc.
    eapply T_Sub.
    + apply (IH Sb n G' HSub Hcfc).
    + wf_transport.
  - (* T_Lam *)
    intros Γ body A l B HwfA HwfB Hbody IHbody Hcap Sb n G' HSub Hcfc.
    simpl. apply T_Lam.
    + wf_transport.
    + wf_transport.
    + apply (IHbody Sb n (bind_tm (subst_ty n Sb A) :: G')
        (SubstTy_tm Sb n Γ G' A HSub)
        (ctor_fields_closed_bind_tm A Γ Hcfc)).
    + eapply LS_Trans.
      * apply (capture_lt_SubstTy_le Sb n Γ G' HSub body).
        apply (proj1 (lt_sub_wf Γ (capture_lt Γ body) l Hcap)).
      * wf_transport.
  - (* T_App *)
    intros Γ t1 t2 A l B Ht1 IH1 Ht2 IH2 Sb n G' HSub Hcfc.
    simpl. eapply T_App.
    + apply (IH1 Sb n G' HSub Hcfc).
    + apply (IH2 Sb n G' HSub Hcfc).
  - (* T_TyLam *)
    intros Γ bound body T HwfBound HwfT HisAbs Hbody IHbody Sb n G' HSub Hcfc.
    simpl. apply T_TyLam.
    + wf_transport.
    + eapply ty_wf_SubstTy; [exact HwfT|]. apply SubstTy_ty. exact HSub.
    + rewrite is_abs_subst_ty_in_tm. exact HisAbs.
    + apply (IHbody (shift_ty 1 0 Sb) (S n) (bind_ty (subst_ty n Sb bound) :: G')
        (SubstTy_ty Sb n Γ G' bound HSub)
        (ctor_fields_closed_bind_ty bound Γ Hcfc)).
  - (* T_TyApp *)
    intros Γ t B U S Ht IH HwfS Hsub Sb n G' HSub Hcfc.
    simpl. rewrite <- subst_ty_subst_ty_comm0.
    eapply T_TyApp.
    + eapply T_Sub.
      * apply (IH Sb n G' HSub Hcfc).
      * apply type_ty_all_narrow_bound.
        -- wf_transport.
        -- pose proof (typing_implies_wf Γ t (type_ty_all B U) Ht) as HwfAll.
           inversion HwfAll; subst.
           eapply ty_wf_SubstTy; [eassumption|].
           apply SubstTy_ty. exact HSub.
    + wf_transport.
    + apply SA_Refl. wf_transport.
  - (* T_LtLam *)
    intros Γ body T HwfT HisAbs Hbody IHbody Sb n G' HSub Hcfc.
    simpl. apply T_LtLam.
    + eapply ty_wf_SubstTy; [exact HwfT|]. apply SubstTy_lt. exact HSub.
    + rewrite is_abs_subst_ty_in_tm. exact HisAbs.
    + apply (IHbody (shift_lt_in_ty 1 0 Sb) n (bind_lt lt_local :: G')
        (SubstTy_lt Sb n Γ G' lt_local HSub)
        (ctor_fields_closed_bind_lt lt_local Γ Hcfc)).
  - (* T_LtApp *)
    intros Γ t T l Ht IH Hwfl Sb n G' HSub Hcfc.
    simpl.
    replace (subst_ty n Sb (subst_lt_in_ty 0 l T))
      with (subst_lt_in_ty 0 l (subst_ty n (shift_lt_in_ty 1 0 Sb) T)).
    2:{ rewrite subst_lt_in_ty_subst_ty_comm. rewrite subst_lt_in_ty_shift_cancel. reflexivity. }
    eapply T_LtApp.
    + apply (IH Sb n G' HSub Hcfc).
    + wf_transport.
  - (* T_Ctor *)
    intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs Hctor Heff Hlen_lts Hwflts Hrho Hlen_Ts HwfTs
           Hresult Hshape Hresult_eff Hwfl HltSub Hbounded Hlen_vs Hargs IHargs
           Sb n G' HSub Hcfc.
    cbn [subst_ty_in_tm]. unfold map_subst_ty.
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
    + wf_transport.
    + subst rho_fields. rewrite !List.map_map. apply List.map_ext_in. intros S _.
      symmetry. apply inst_ctor_type_subst_ty; [exact Hlen_lts | exact Hlen_Ts].
    + rewrite List.length_map. exact Hlen_Ts.
    + exact HwfMTs.
    + subst result_ty. symmetry. apply inst_ctor_type_subst_ty; [exact Hlen_lts | exact Hlen_Ts].
    + rewrite Hshape. rewrite subst_ty_ctor_eq. reflexivity.
    + rewrite (SubstTy_lookup_eff Sb n Γ G' HSub result_tag). rewrite Hresult_eff. reflexivity.
    + exact Hwfl'.
    + (* ESCAPE PREMISE — the substitution-stability payoff *)
      assert (HltSub' : G' ⊢ₗ lt_of_ty_list rho_fields <: lt_join l (lt_of_ty_list Ts)).
      { eapply lt_sub_SubstTy; [| exact HSub].
        rewrite Hshape in HltSub. rewrite lt_of_ty_ctor_eq in HltSub. exact HltSub. }
      rewrite Hshape. rewrite subst_ty_ctor_eq. rewrite lt_of_ty_ctor_eq.
      assert (Halign : G' ⊢ₗ lt_of_ty_list (List.map (subst_ty n Sb) rho_fields)
                  <: lt_join (lt_of_ty_list rho_fields) (lt_of_ty_list (List.map (subst_ty n Sb) Ts))).
      { rewrite Hrho. rewrite <- Hlen_lts, <- Hlen_Ts.
        apply inst_ctor_fields_alignment.
        - destruct (Hcfc K n_lt n_ty sigma_fields result_ty_schema Hctor) as [HltCl HtyCl].
          rewrite Hlen_lts, Hlen_Ts. apply tys_closed_Forall_and; assumption.
        - exact HFlts.
        - exact HFTs.
        - apply lt_of_ty_list_wf. exact HwfMTs. }
      eapply LS_Trans; [exact Halign |].
      apply LS_JoinL.
      * eapply LS_Trans; [exact HltSub' |].
        apply lt_join_mono; [apply LS_Refl; exact Hwfl' |].
        apply lt_of_ty_list_subst_ty_ge; [exact HwfSbl | exact HwfMTs].
      * apply LS_JoinR2; [apply LS_Refl; apply lt_of_ty_list_wf; exact HwfMTs | exact Hwfl'].
    + eapply Forall_impl; [| exact Hbounded].
      intros l0 Hl0. eapply lt_sub_SubstTy; [exact Hl0 | exact HSub].
    + rewrite !List.length_map. exact Hlen_vs.
    + clear -IHargs HSub Hcfc.
      induction IHargs as [|v rho vs' rhos' Hv Hrest IH]; simpl; constructor.
      * apply Hv; [exact HSub | exact Hcfc].
      * exact IH.
  - (* T_Match *)
    intros Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
           rho_fields scrut_result_ty result_tag result_l Γyes yes_body eta elim_result no_body
           HKne Hctor Heff Hlts Hrho Hlen_Ts HwfTs Hscrut_result Hscrut_shape
           Hresult_eff Hresult_ne HwfDelta Hresult_l Hscrut IHscrut Harity HΓyes
           Hyes IHyes Helim Hno IHno Sb n G' HSub Hcfc.
    subst Γyes. cbn [subst_ty_in_tm].
    eapply T_Match with
      (n_lt := n_lt) (n_ty := n_ty)
      (sigma_fields := List.map (subst_ty (n_ty + n) (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb))) sigma_fields)
      (result_ty_schema := subst_ty (n_ty + n) (shift_lt_in_ty n_lt 0 (shift_ty n_ty 0 Sb)) result_ty_schema)
      (Ts := List.map (subst_ty n Sb) Ts)
      (Delta := Delta)
      (lts := lt_var_list n_lt)
      (rho_fields := List.map (subst_ty n (shift_lt_in_ty n_lt 0 Sb)) rho_fields)
      (scrut_result_ty := subst_ty n Sb scrut_result_ty)
      (result_tag := result_tag) (result_l := result_l)
      (Γ' := push_match_bound n_lt Delta G')
      (eta := subst_ty n (shift_lt_in_ty n_lt 0 Sb) eta).
    + exact HKne.
    + rewrite (SubstTy_lookup_ctor Sb n Γ G' HSub K). rewrite Hctor. reflexivity.
    + rewrite (SubstTy_lookup_eff Sb n Γ G' HSub K). rewrite Heff. reflexivity.
    + reflexivity.
    + subst rho_fields. rewrite !List.map_map. apply List.map_ext. intro sigma.
      symmetry. apply inst_ctor_type_open_subst_ty. exact Hlen_Ts.
    + rewrite List.length_map. exact Hlen_Ts.
    + wf_transport.
    + subst scrut_result_ty.
      exact (eq_sym (inst_ctor_type_subst_ty n_lt n_ty (List.repeat Delta n_lt) Ts
                       result_ty_schema n Sb (List.repeat_length Delta n_lt) Hlen_Ts)).
    + subst scrut_result_ty. rewrite Hscrut_shape. reflexivity.
    + rewrite (SubstTy_lookup_eff Sb n Γ G' HSub result_tag). rewrite Hresult_eff. reflexivity.
    + exact Hresult_ne.
    + wf_transport.
    + wf_transport.
    + apply (IHscrut Sb n G' HSub Hcfc).
    + rewrite List.length_map. exact Harity.
    + reflexivity.
    + apply (IHyes (shift_lt_in_ty n_lt 0 Sb) n
        (List.fold_right (fun rho Γ0 => bind_tm rho :: Γ0)
          (push_match_bound n_lt Delta G')
          (List.map (subst_ty n (shift_lt_in_ty n_lt 0 Sb)) rho_fields))).
      * apply SubstTy_fold_bind_tm_map. apply SubstTy_push_match_bound. exact HSub.
      * apply ctor_fields_closed_fold_bind_tm. apply ctor_fields_closed_push_match_bound. exact Hcfc.
    + apply elim_ty_n_subst_ty_shifted. exact Helim.
    + apply (IHno Sb n G' HSub Hcfc).
  - (* T_Cap *)
    intros Γ E_tag m Ts op_bodies n_α ops T_R
           Heff Hlen HwfTs HwfTR Hfst Hops IHops Sb n G' HSub Hcfc.
    simpl. rewrite subst_ty_in_tm_ops_eq_map.
    eapply T_Cap with
      (n_α := n_α)
      (ops := List.map (fun osig =>
                 (op_nb osig,
                  subst_ty (n_α + op_nb osig + n) (shift_ty (n_α + op_nb osig) 0 Sb) (op_sig_ty osig),
                  subst_ty (n_α + op_nb osig + n) (shift_ty (n_α + op_nb osig) 0 Sb) (op_ret_ty osig))) ops).
    + rewrite (SubstTy_lookup_eff Sb n Γ G' HSub E_tag). rewrite Heff. simpl.
      do 2 f_equal. apply List.map_ext. intros [[nβ sg] rt]. reflexivity.
    + change (List.length (List.map (subst_ty n Sb) Ts) = n_α).
      rewrite List.length_map. exact Hlen.
    + wf_transport.
    + wf_transport.
    + rewrite !List.map_map. exact Hfst.
    + clear Hops Heff. revert Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IHrest]; intros Hfst; simpl.
      * constructor.
      * simpl in Hfst. injection Hfst as Hnb Hfstrest.
        constructor; [| apply IHrest; exact Hfstrest ].
        destruct osig as [[nβ sg] rt].
        unfold op_nb, op_sig_ty, op_ret_ty in *. simpl in *.
        rewrite Hnb.
        unfold op_body_ctx.
        try change (map_subst_ty n Sb Ts) with (List.map (subst_ty n Sb) Ts).
        try change ((fix go (l : list type) : list type :=
                   match l with
                   | [] => []
                   | A :: rest => subst_ty n Sb A :: go rest
                   end) Ts) with (List.map (subst_ty n Sb) Ts).
        replace (inst_op_ty_args n_α (List.map (subst_ty n Sb) Ts) nβ
                   (subst_ty (n_α + nβ + n) (shift_ty (n_α + nβ) 0 Sb) sg))
          with (subst_ty (nβ + n) (shift_ty nβ 0 Sb) (inst_op_ty_args n_α Ts nβ sg))
          by (symmetry; apply inst_op_ty_args_subst_ty; exact Hlen).
        replace (inst_op_ty_args n_α (List.map (subst_ty n Sb) Ts) nβ
                   (subst_ty (n_α + nβ + n) (shift_ty (n_α + nβ) 0 Sb) rt))
          with (subst_ty (nβ + n) (shift_ty nβ 0 Sb) (inst_op_ty_args n_α Ts nβ rt))
          by (symmetry; apply inst_op_ty_args_subst_ty; exact Hlen).
        rewrite <- (shift_ty_many_subst_ty_comm0 nβ n Sb T_R).
        replace (n + nβ) with (nβ + n) by lia.
        eapply Hone.
        -- apply SubstTy_tm. apply SubstTy_tm. apply SubstTy_push_ty_vars_any_at_free. exact HSub.
        -- apply ctor_fields_closed_bind_tm. apply ctor_fields_closed_bind_tm.
           apply ctor_fields_closed_push_ty_vars. exact Hcfc.
  - (* T_Handle *)
    intros Γ E_tag Ts op_bodies body n_α ops T_B T_R
           Heff Hlen HwfTs HwfTB HwfTR HnoLocal Hsub Hfst Hops IHops Hbody IHbody
           Sb n G' HSub Hcfc.
    simpl. rewrite subst_ty_in_tm_ops_eq_map.
    eapply T_Handle with
      (n_α := n_α)
      (ops := List.map (fun osig =>
                 (op_nb osig,
                  subst_ty (n_α + op_nb osig + n) (shift_ty (n_α + op_nb osig) 0 Sb) (op_sig_ty osig),
                  subst_ty (n_α + op_nb osig + n) (shift_ty (n_α + op_nb osig) 0 Sb) (op_ret_ty osig))) ops)
      (T_B := subst_ty n Sb T_B).
    + rewrite (SubstTy_lookup_eff Sb n Γ G' HSub E_tag). rewrite Heff. simpl.
      do 2 f_equal. apply List.map_ext. intros [[nβ sg] rt]. reflexivity.
    + change (List.length (List.map (subst_ty n Sb) Ts) = n_α).
      rewrite List.length_map. exact Hlen.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + rewrite !List.map_map. exact Hfst.
    + clear Hops Heff. revert Hfst.
      induction IHops as [|ob osig obs' ops' Hone Hrest IHrest]; intros Hfst; simpl.
      * constructor.
      * simpl in Hfst. injection Hfst as Hnb Hfstrest.
        constructor; [| apply IHrest; exact Hfstrest ].
        destruct osig as [[nβ sg] rt].
        unfold op_nb, op_sig_ty, op_ret_ty in *. simpl in *.
        rewrite Hnb.
        unfold op_body_ctx.
        try change (map_subst_ty n Sb Ts) with (List.map (subst_ty n Sb) Ts).
        try change ((fix go (l : list type) : list type :=
                   match l with
                   | [] => []
                   | A :: rest => subst_ty n Sb A :: go rest
                   end) Ts) with (List.map (subst_ty n Sb) Ts).
        replace (inst_op_ty_args n_α (List.map (subst_ty n Sb) Ts) nβ
                   (subst_ty (n_α + nβ + n) (shift_ty (n_α + nβ) 0 Sb) sg))
          with (subst_ty (nβ + n) (shift_ty nβ 0 Sb) (inst_op_ty_args n_α Ts nβ sg))
          by (symmetry; apply inst_op_ty_args_subst_ty; exact Hlen).
        replace (inst_op_ty_args n_α (List.map (subst_ty n Sb) Ts) nβ
                   (subst_ty (n_α + nβ + n) (shift_ty (n_α + nβ) 0 Sb) rt))
          with (subst_ty (nβ + n) (shift_ty nβ 0 Sb) (inst_op_ty_args n_α Ts nβ rt))
          by (symmetry; apply inst_op_ty_args_subst_ty; exact Hlen).
        rewrite <- (shift_ty_many_subst_ty_comm0 nβ n Sb T_R).
        replace (n + nβ) with (nβ + n) by lia.
        eapply Hone.
        -- apply SubstTy_tm. apply SubstTy_tm. apply SubstTy_push_ty_vars_any_at_free. exact HSub.
        -- apply ctor_fields_closed_bind_tm. apply ctor_fields_closed_bind_tm.
           apply ctor_fields_closed_push_ty_vars. exact Hcfc.
    + apply (IHbody Sb n (bind_tm (subst_ty n Sb (type_ctor E_tag lt_local Ts)) :: G')
        (SubstTy_tm Sb n Γ G' (type_ctor E_tag lt_local Ts) HSub)
        (ctor_fields_closed_bind_tm (type_ctor E_tag lt_local Ts) Γ Hcfc)).
  - (* T_Perform *)
    intros Γ recv op arg E_tag Delta Ts Ss n_α ops n_β sig ret sig_inst ret_inst
           Hrecv IHrecv Heff Hnth Hlen_Ts Hlen_Ss HwfSs HnoSs Hsig HnoSig Hret HwfRet Harg IHarg
           Sb n G' HSub Hcfc.
    simpl. eapply T_Perform with
      (n_α := n_α)
      (ops := List.map (fun osig =>
                 (op_nb osig,
                  subst_ty (n_α + op_nb osig + n) (shift_ty (n_α + op_nb osig) 0 Sb) (op_sig_ty osig),
                  subst_ty (n_α + op_nb osig + n) (shift_ty (n_α + op_nb osig) 0 Sb) (op_ret_ty osig))) ops)
      (n_β := n_β)
      (sig := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) sig)
      (ret := subst_ty (n_α + n_β + n) (shift_ty (n_α + n_β) 0 Sb) ret)
      (sig_inst := subst_ty n Sb sig_inst) (ret_inst := subst_ty n Sb ret_inst).
    + apply (IHrecv Sb n G' HSub Hcfc).
    + rewrite (SubstTy_lookup_eff Sb n Γ G' HSub E_tag). rewrite Heff. simpl.
      do 2 f_equal. apply List.map_ext. intros [[nβ sg] rt]. reflexivity.
    + rewrite (map_nth_error _ _ _ Hnth). reflexivity.
    + change (List.length (List.map (subst_ty n Sb) Ts) = n_α).
      rewrite List.length_map. exact Hlen_Ts.
    + change (List.length (List.map (subst_ty n Sb) Ss) = n_β).
      rewrite List.length_map. exact Hlen_Ss.
    + wf_transport.
    + wf_transport.
    + subst sig_inst. symmetry. apply inst_op_all_args_subst_ty; assumption.
    + eapply sub_free_SubstTy; [exact HSub | eapply typing_implies_wf; exact Harg | exact HnoSig].
    + subst ret_inst. symmetry. apply inst_op_all_args_subst_ty; assumption.
    + wf_transport.
    + apply (IHarg Sb n G' HSub Hcfc).
  - (* T_HandlerM *)
    intros Γ m T_B T_R t HwfTB HwfTR HnoLocal Hsub Ht IH Sb n G' HSub Hcfc.
    simpl. apply T_HandlerM.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + wf_transport.
    + apply (IH Sb n G' HSub Hcfc).
Qed.

(* ==================================================================== *)
(*  push_ty_vars TYPE peel — needed for perform_preserves.              *)
(*                                                                      *)
(*  An operation body is typed under [push_ty_vars n_β any_at_free Γ]   *)
(*  (the n_β operation type parameters, each bounded by [any_at_free]), *)
(*  with two [bind_tm] binders on top (the argument and the resume).    *)
(*  A [perform] instantiates the type parameters with concrete [Ss]     *)
(*  (each no-local, hence [<:: any_at_free] via SA_Any).  This peel     *)
(*  removes the n_β type binders by iterated [typing_SubstTy].          *)
(* ==================================================================== *)

(* Front-unfold for the (tail-recursive) [push_ty_vars]. *)
Lemma push_ty_vars_S_front : forall n b Γ,
  push_ty_vars (S n) b Γ = bind_ty b :: push_ty_vars n b Γ.
Proof.
  induction n; intros b Γ.
  - reflexivity.
  - change (push_ty_vars (S (S n)) b Γ)
      with (push_ty_vars (S n) b (bind_ty b :: Γ)).
    change (push_ty_vars (S n) b Γ)
      with (push_ty_vars n b (bind_ty b :: Γ)).
    apply IHn.
Qed.

(* A no-local type stays [<:: any_at_free] after pushing type binders
   (bounded by [any_at_free]) and shifting by the same amount. *)
Lemma sub_any_at_free_push_ty_vars : forall k Γ S,
  Γ ⊢ S <:: any_at_free ->
  push_ty_vars k any_at_free Γ ⊢ shift_ty k 0 S <:: any_at_free.
Proof.
  induction k; intros Γ S Hsub.
  - cbn [push_ty_vars]. rewrite shift_ty_zero. exact Hsub.
  - rewrite push_ty_vars_S_front.
    pose proof (sub_weaken_ty_shift (push_ty_vars k any_at_free Γ) any_at_free
                  (shift_ty k 0 S) any_at_free (IHk Γ S Hsub)) as Hw.
    rewrite shift_ty_fuse in Hw.
    replace (shift_ty 1 0 any_at_free) with any_at_free in Hw
      by (unfold any_at_free; rewrite shift_ty_ctor_eq; reflexivity).
    exact Hw.
Qed.

(* Fuse a per-binder type map into the [bind_tm] fold. *)
Lemma fold_right_bind_tm_map : forall (f : type -> type) base rhos,
  List.fold_right (fun rho G0 => bind_tm (f rho) :: G0) base rhos
  = List.fold_right (fun rho G0 => bind_tm rho :: G0) base (List.map f rhos).
Proof. intros f base rhos. induction rhos; cbn; [reflexivity| rewrite IHrhos; reflexivity]. Qed.

(* The peel: substitute the list [Ss] (each [<:: any_at_free]) for the
   [push_ty_vars (length Ss) any_at_free Γ] type binders, crossing any
   number of [bind_tm] binders [rhos] (whose types are substituted too). *)
Lemma typing_peel_push_ty_vars_fold : forall Ss rhos t U Γ,
  Forall (fun S => Γ ⊢ S <:: any_at_free) Ss ->
  ctor_fields_closed Γ ->
  List.fold_right (fun rho G => bind_tm rho :: G)
                  (push_ty_vars (List.length Ss) any_at_free Γ) rhos ⊢ₜ t : U ->
  List.fold_right (fun rho G => bind_tm rho :: G) Γ (List.map (subst_list_ty Ss) rhos)
    ⊢ₜ subst_list_ty_in_tm Ss t : subst_list_ty Ss U.
Proof.
  induction Ss as [|S0 rest IH]; intros rhos t U Γ Hall Hcfc Hty.
  - (* Ss = [] *)
    cbn [List.length push_ty_vars] in Hty.
    assert (Hnil : List.map (subst_list_ty []) rhos = rhos).
    { clear. induction rhos as [|r rs IHr];
        cbn [List.map subst_list_ty]; [reflexivity| f_equal; exact IHr]. }
    rewrite Hnil.
    cbn [subst_list_ty_in_tm subst_list_ty].
    exact Hty.
  - (* Ss = S0 :: rest *)
    cbn [List.length] in Hty.
    rewrite push_ty_vars_S_front in Hty.
    set (PG := push_ty_vars (List.length rest) any_at_free Γ) in *.
    pose proof (SubstTy_here PG any_at_free (shift_ty (List.length rest) 0 S0)
                  (sub_any_at_free_push_ty_vars (List.length rest) Γ S0 (Forall_inv Hall)))
      as Hsub0.
    pose proof (SubstTy_fold_bind_tm rhos (shift_ty (List.length rest) 0 S0) 0
                  (bind_ty any_at_free :: PG) PG Hsub0) as HsubF.
    assert (Hcfc' : ctor_fields_closed
              (List.fold_right (fun rho G0 => bind_tm rho :: G0)
                               (bind_ty any_at_free :: PG) rhos)).
    { apply ctor_fields_closed_fold_bind_tm. apply ctor_fields_closed_bind_ty.
      apply ctor_fields_closed_push_ty_vars. exact Hcfc. }
    pose proof (typing_SubstTy _ t U Hty _ _ _ HsubF Hcfc') as Hstep.
    rewrite fold_right_bind_tm_map in Hstep.
    specialize (IH (List.map (subst_ty 0 (shift_ty (List.length rest) 0 S0)) rhos)
                   (subst_ty_in_tm 0 (shift_ty (List.length rest) 0 S0) t)
                   (subst_ty 0 (shift_ty (List.length rest) 0 S0) U) Γ
                   (Forall_inv_tail Hall) Hcfc Hstep).
    rewrite List.map_map in IH.
    (* goal and IH agree by eta/iota: subst_list_ty (S0::rest) x reduces to
       subst_list_ty rest (subst_ty 0 (shift_ty (length rest) 0 S0) x). *)
    exact IH.
Qed.

(* ================================================================== *)
(*  Type-level reconciliations for perform_preserves.                 *)
(* ================================================================== *)

(* [subst_list_ty] of a closed-length list IS [inst_ty_vars]. *)
Lemma subst_list_ty_eq_inst_ty_vars : forall Ss T,
  subst_list_ty Ss T = inst_ty_vars (List.length Ss) Ss T.
Proof.
  induction Ss as [|U rest IH]; intros T; [reflexivity|].
  cbn [List.length subst_list_ty inst_ty_vars]. apply IH.
Qed.

(* Instantiating [length Ss] freshly-shifted type variables cancels. *)
Lemma inst_ty_vars_shift_cancel : forall Ss T,
  inst_ty_vars (List.length Ss) Ss (shift_ty (List.length Ss) 0 T) = T.
Proof.
  induction Ss as [|U rest IH]; intros T.
  - cbn [List.length inst_ty_vars]. apply shift_ty_zero.
  - cbn [List.length inst_ty_vars].
    replace (shift_ty (S (List.length rest)) 0 T)
      with (shift_ty 1 0 (shift_ty (List.length rest) 0 T))
      by (rewrite shift_ty_fuse; reflexivity).
    rewrite subst_ty_shift_cancel. apply IH.
Qed.

Lemma subst_list_ty_shift_cancel : forall Ss T,
  subst_list_ty Ss (shift_ty (List.length Ss) 0 T) = T.
Proof.
  intros Ss T. rewrite subst_list_ty_eq_inst_ty_vars. apply inst_ty_vars_shift_cancel.
Qed.

(* [subst_list_ty] distributes through [type_fun] (lifetime preserved). *)
Lemma subst_list_ty_fun : forall Ss A l B,
  subst_list_ty Ss (type_fun A l B)
  = type_fun (subst_list_ty Ss A) l (subst_list_ty Ss B).
Proof.
  induction Ss as [|U rest IH]; intros A l B; [reflexivity|].
  cbn [subst_list_ty]. cbn [subst_ty]. apply IH.
Qed.

(* The operation-signature reconciliation: substituting the perform's [Ss]
   into the capability's [inst_op_ty_args …] yields the perform's
   [inst_op_all_args … Ss …]. *)
Lemma subst_list_ty_inst_op_ty_args : forall n_α Ts n_β Ss X,
  List.length Ss = n_β ->
  subst_list_ty Ss (inst_op_ty_args n_α Ts n_β X)
  = inst_op_all_args n_α Ts n_β Ss X.
Proof.
  intros n_α Ts n_β Ss X Hlen. unfold inst_op_all_args.
  rewrite subst_list_ty_eq_inst_ty_vars, Hlen. reflexivity.
Qed.
