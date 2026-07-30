Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import WellScoped.

(* ================================================================== *)
(* Runtime marker invariants, part 2: the ws_rt proof engine.         *)
(*                                                                    *)
(* Closed-subterm identity laws, preservation of the FUSED invariant  *)
(* [ws_rt] (= well_scoped /\ rt_closed) under shifts, substitutions   *)
(* and plug, and the H_Perform confinement facts.  Each traversal law *)
(* is proved by ONE structural induction whose motive is the          *)
(* conjunction; the only single-sided laws are the ones that CANNOT   *)
(* fuse: [well_scoped_shift_tm] (rt_closed's cap clause pins          *)
(* op-bodies at term-cutoff 2, which shift_tm below cutoff 2 does not *)
(* respect) and the ws-only confinement/rt-only reified-continuation  *)
(* facts.  Definitions live in WellScoped.v.                          *)
(* ================================================================== *)

(* ==================================================================== *)
(* Closed-subterm identity laws.                                        *)
(*                                                                      *)
(* A term with no free variables at/above [c] is untouched by shifts    *)
(* and substitutions at index >= c.  Runtime marker constructs have     *)
(* closed bodies ([rt_closed]), so these laws make term substitution    *)
(* vacuous exactly at the scope-sensitive positions of well_scoped.    *)
(* ==================================================================== *)

Lemma shift_tm_closed_id : forall t c a cutoff,
  free_tm_vars c t = [] -> c <= cutoff -> shift_tm a cutoff t = t.
Proof.
  apply (term_list_ind
    (fun t => forall c a cutoff,
       free_tm_vars c t = [] -> c <= cutoff -> shift_tm a cutoff t = t)
    (fun ts => forall c a cutoff,
       List.concat (List.map (free_tm_vars c) ts) = [] -> c <= cutoff ->
       List.map (shift_tm a cutoff) ts = ts)
    (fun obs => forall c a cutoff,
       List.concat (List.map (fun p => free_tm_vars c (snd p)) obs) = [] -> c <= cutoff ->
       List.map (fun p => (fst p, shift_tm a cutoff (snd p))) obs = obs)).
  - intros n c a cutoff Hfv Hle. simpl in Hfv |- *.
    destruct (Nat.ltb n c) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      destruct (Nat.leb cutoff n) eqn:Hcn.
      * apply Nat.leb_le in Hcn. lia.
      * reflexivity.
    + discriminate Hfv.
  - intros t1 t2 IH1 IH2 c a cutoff Hfv Hle. simpl in Hfv |- *.
    apply app_eq_nil in Hfv as [H1 H2].
    rewrite (IH1 c a cutoff H1 Hle), (IH2 c a cutoff H2 Hle). reflexivity.
  - intros body T IH c a cutoff Hfv Hle. simpl in Hfv |- *.
    rewrite (IH (S c) a (S cutoff) Hfv); [reflexivity | lia].
  - intros t T IH c a cutoff Hfv Hle. simpl in Hfv |- *.
    rewrite (IH c a cutoff Hfv Hle). reflexivity.
  - intros bound body IH c a cutoff Hfv Hle. simpl in Hfv |- *.
    rewrite (IH c a cutoff Hfv Hle). reflexivity.
  - intros t l IH c a cutoff Hfv Hle. simpl in Hfv |- *.
    rewrite (IH c a cutoff Hfv Hle). reflexivity.
  - intros body IH c a cutoff Hfv Hle. simpl in Hfv |- *.
    rewrite (IH c a cutoff Hfv Hle). reflexivity.
  - intros K l lts Ts ts IH c a cutoff Hfv Hle.
    simpl in Hfv.    cbn [shift_tm].    rewrite (IH c a cutoff Hfv Hle). reflexivity.
  - intros scrut tag nlt ar y n IHs IHy IHn c a cutoff Hfv Hle. simpl in Hfv |- *.
    apply app_eq_nil in Hfv as [Hs Hyn]. apply app_eq_nil in Hyn as [Hy Hn].
    rewrite (IHs c a cutoff Hs Hle).
    rewrite (IHy (c + ar) a (cutoff + ar) Hy); [|lia].
    rewrite (IHn c a cutoff Hn Hle). reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb c a cutoff Hfv Hle. simpl in Hfv |- *.
    rewrite free_tm_vars_ops_eq_concat in Hfv.
    apply app_eq_nil in Hfv as [Hop Hb].
    rewrite shift_tm_ops_eq_map.
    rewrite (IHops (c + 2) a (cutoff + 2) Hop); [|lia].
    rewrite (IHb (S c) a (S cutoff) Hb); [|lia]. reflexivity.
  - intros t op Ss A_ret arg IHt IHa c a cutoff Hfv Hle. simpl in Hfv |- *.
    apply app_eq_nil in Hfv as [Ht Ha].
    rewrite (IHt c a cutoff Ht Hle), (IHa c a cutoff Ha Hle). reflexivity.
  - intros E_tag m Ts T_R op_bodies IHops c a cutoff Hfv Hle. simpl in Hfv |- *.
    rewrite free_tm_vars_ops_eq_concat in Hfv.
    rewrite shift_tm_ops_eq_map.
    rewrite (IHops (c + 2) a (cutoff + 2) Hfv); [reflexivity|lia].
  - intros m T_B T_R body IH c a cutoff Hfv Hle. simpl in Hfv |- *.
    rewrite (IH c a cutoff Hfv Hle). reflexivity.
  - intros c a cutoff _ _. reflexivity.
  - intros u ts IHu IHts c a cutoff Hfv Hle. simpl in Hfv.
    apply app_eq_nil in Hfv as [Hu Hts].
    simpl. rewrite (IHu c a cutoff Hu Hle), (IHts c a cutoff Hts Hle). reflexivity.
  - intros c a cutoff _ _. reflexivity.
  - intros nb ob obs IHob IHobs c a cutoff Hfv Hle. simpl in Hfv.
    apply app_eq_nil in Hfv as [Hob Hobs].
    simpl. rewrite (IHob c a cutoff Hob Hle), (IHobs c a cutoff Hobs Hle). reflexivity.
Qed.

Lemma subst_tm_closed_id : forall t c var r,
  free_tm_vars c t = [] -> c <= var -> subst_tm var r t = t.
Proof.
  apply (term_list_ind
    (fun t => forall c var r,
       free_tm_vars c t = [] -> c <= var -> subst_tm var r t = t)
    (fun ts => forall c var r,
       List.concat (List.map (free_tm_vars c) ts) = [] -> c <= var ->
       List.map (subst_tm var r) ts = ts)
    (fun obs => forall c var r,
       List.concat (List.map (fun p => free_tm_vars c (snd p)) obs) = [] -> c <= var ->
       List.map (fun p => (fst p, subst_tm var r (snd p))) obs = obs)).
  - intros n c var r Hfv Hle. simpl in Hfv |- *.
    destruct (Nat.ltb n c) eqn:Hlt.
    + apply Nat.ltb_lt in Hlt.
      destruct (Nat.eqb n var) eqn:Heq.
      * apply Nat.eqb_eq in Heq. lia.
      * destruct (Nat.ltb var n) eqn:Hvn.
        -- apply Nat.ltb_lt in Hvn. lia.
        -- reflexivity.
    + discriminate Hfv.
  - intros t1 t2 IH1 IH2 c var r Hfv Hle. simpl in Hfv |- *.
    apply app_eq_nil in Hfv as [H1 H2].
    rewrite (IH1 c var _ H1 Hle), (IH2 c var _ H2 Hle). reflexivity.
  - intros body T IH c var r Hfv Hle. simpl in Hfv |- *.
    rewrite (IH (S c) (S var) _ Hfv); [reflexivity | lia].
  - intros t T IH c var r Hfv Hle. simpl in Hfv |- *.
    rewrite (IH c var _ Hfv Hle). reflexivity.
  - intros bound body IH c var r Hfv Hle. simpl in Hfv |- *.
    rewrite (IH c var _ Hfv Hle). reflexivity.
  - intros t l IH c var r Hfv Hle. simpl in Hfv |- *.
    rewrite (IH c var _ Hfv Hle). reflexivity.
  - intros body IH c var r Hfv Hle. simpl in Hfv |- *.
    rewrite (IH c var _ Hfv Hle). reflexivity.
  - intros K l lts Ts ts IH c var r Hfv Hle.
    simpl in Hfv.    cbn [subst_tm].    rewrite (IH c var r Hfv Hle). reflexivity.
  - intros scrut tag nlt ar y n IHs IHy IHn c var r Hfv Hle. simpl in Hfv |- *.
    apply app_eq_nil in Hfv as [Hs Hyn]. apply app_eq_nil in Hyn as [Hy Hn].
    rewrite (IHs c var _ Hs Hle).
    rewrite (IHy (c + ar) (var + ar) _ Hy); [|lia].
    rewrite (IHn c var _ Hn Hle). reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb c var r Hfv Hle. simpl in Hfv |- *.
    rewrite free_tm_vars_ops_eq_concat in Hfv.
    apply app_eq_nil in Hfv as [Hop Hb].
    rewrite subst_tm_ops_eq_map.
    rewrite (IHops (c + 2) (var + 2) _ Hop); [|lia].
    rewrite (IHb (S c) (S var) _ Hb); [|lia]. reflexivity.
  - intros t op Ss A_ret arg IHt IHa c var r Hfv Hle. simpl in Hfv |- *.
    apply app_eq_nil in Hfv as [Ht Ha].
    rewrite (IHt c var _ Ht Hle), (IHa c var _ Ha Hle). reflexivity.
  - intros E_tag m Ts T_R op_bodies IHops c var r Hfv Hle. simpl in Hfv |- *.
    rewrite free_tm_vars_ops_eq_concat in Hfv.
    rewrite subst_tm_ops_eq_map.
    rewrite (IHops (c + 2) (var + 2) _ Hfv); [reflexivity|lia].
  - intros m T_B T_R body IH c var r Hfv Hle. simpl in Hfv |- *.
    rewrite (IH c var _ Hfv Hle). reflexivity.
  - intros c var r _ _. reflexivity.
  - intros u ts IHu IHts c var r Hfv Hle. simpl in Hfv.
    apply app_eq_nil in Hfv as [Hu Hts].
    simpl. rewrite (IHu c var _ Hu Hle), (IHts c var _ Hts Hle). reflexivity.
  - intros c var r _ _. reflexivity.
  - intros nb ob obs IHob IHobs c var r Hfv Hle. simpl in Hfv.
    apply app_eq_nil in Hfv as [Hob Hobs].
    simpl. rewrite (IHob c var _ Hob Hle), (IHobs c var _ Hobs Hle). reflexivity.
Qed.

(* Term/type/lifetime shifts never move markers, so well_scoped is     *)
(* preserved at the SAME scope.                                         *)
Lemma well_scoped_shift_tm : forall t ms a cutoff,
  well_scoped ms t -> well_scoped ms (shift_tm a cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall ms a cutoff,
       well_scoped ms t -> well_scoped ms (shift_tm a cutoff t))
    (fun ts => forall ms a cutoff,
       well_scoped_list ms ts ->
       well_scoped_list ms (List.map (shift_tm a cutoff) ts))
    (fun obs => forall ms a cutoff,
       ops_well_scoped ms obs ->
       ops_well_scoped ms (List.map (fun p => (fst p, shift_tm a (cutoff + 2) (snd p))) obs))).
  - intros n ms a cutoff _. cbn [shift_tm].
    destruct (Nat.leb cutoff n); exact I.
  - intros t1 t2 IH1 IH2 ms a cutoff [H1 H2]. cbn [shift_tm].
    split; [apply IH1|apply IH2]; assumption.
  - intros body T IH ms a cutoff Hws. cbn [shift_tm]. apply IH; exact Hws.
  - intros t T IH ms a cutoff Hws. cbn [shift_tm]. apply IH; exact Hws.
  - intros bound body IH ms a cutoff Hws. cbn [shift_tm]. apply IH; exact Hws.
  - intros t l IH ms a cutoff Hws. cbn [shift_tm]. apply IH; exact Hws.
  - intros body IH ms a cutoff Hws. cbn [shift_tm]. apply IH; exact Hws.
  - intros K l lts Ts ts IH ms a cutoff Hws.
    cbn [shift_tm].    rewrite well_scoped_ctor_eq. apply IH.
    rewrite well_scoped_ctor_eq in Hws. exact Hws.
  - intros scrut tag nlt ar y n IHs IHy IHn ms a cutoff [Hs [Hy Hn]]. cbn [shift_tm].
    split; [apply IHs; exact Hs | split; [apply IHy; exact Hy | apply IHn; exact Hn]].
  - intros E Ts T_B T_R op_bodies body IHops IHb ms a cutoff [Hop Hb]. cbn [shift_tm].
    rewrite shift_tm_ops_eq_map.
    split; [apply IHops; exact Hop | apply IHb; exact Hb].
  - intros t op Ss A_ret arg IHt IHa ms a cutoff [Ht Ha]. cbn [shift_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m Ts T_R op_bodies IHops ms a cutoff [Hin Hws]. cbn [shift_tm].
    rewrite shift_tm_ops_eq_map.
    split; [exact Hin | apply IHops; exact Hws].
  - intros m T_B T_R body IH ms a cutoff Hws. cbn [shift_tm]. apply IH; exact Hws.
  - intros ms a cutoff _. exact I.
  - intros u ts IHu IHts ms a cutoff [Hu Hts].
    split; [apply IHu|apply IHts]; assumption.
  - intros ms a cutoff _. exact I.
  - intros nb ob obs IHob IHobs ms a cutoff [Hob Hobs]. simpl.
    split; [apply IHob; exact Hob | apply IHobs; exact Hobs].
Qed.

(* Fused shift laws: type/lifetime shifts in terms never move markers   *)
(* and never touch term variables, so ws_rt is preserved at the SAME    *)
(* scope — one traversal for both conjuncts.  (Term shift has no        *)
(* rt_closed law: the cap clause pins op-bodies at term-cutoff 2, which *)
(* shift_tm at cutoff < 2 does not respect; well_scoped_shift_tm above  *)
(* is the well_scoped-only exception.)                                  *)
Lemma ws_rt_shift_ty_in_tm : forall t ms a cutoff,
  ws_rt ms t -> ws_rt ms (shift_ty_in_tm a cutoff t).
Proof.
  unfold ws_rt.
  apply (term_list_ind
    (fun t => forall ms a cutoff,
       well_scoped ms t /\ rt_closed t ->
       well_scoped ms (shift_ty_in_tm a cutoff t) /\
       rt_closed (shift_ty_in_tm a cutoff t))
    (fun ts => forall ms a cutoff,
       well_scoped_list ms ts /\ rt_closed_list ts ->
       well_scoped_list ms (List.map (shift_ty_in_tm a cutoff) ts) /\
       rt_closed_list (List.map (shift_ty_in_tm a cutoff) ts))
    (fun obs => forall ms a cutoff,
       ops_well_scoped ms obs /\ ops_rt_closed obs ->
       ops_well_scoped ms
         (List.map (fun p => (fst p, shift_ty_in_tm a (cutoff + fst p) (snd p))) obs) /\
       ops_rt_closed
         (List.map (fun p => (fst p, shift_ty_in_tm a (cutoff + fst p) (snd p))) obs))).
  - intros n ms a cutoff _. split; exact I.
  - intros t1 t2 IH1 IH2 ms a cutoff [[W1 W2] [R1 R2]].
    destruct (IH1 ms a cutoff (conj W1 R1)) as [W1' R1'].
    destruct (IH2 ms a cutoff (conj W2 R2)) as [W2' R2'].
    split; split; assumption.
  - intros body T IH ms a cutoff H. exact (IH ms a cutoff H).
  - intros t T IH ms a cutoff H. exact (IH ms a cutoff H).
  - intros bound body IH ms a cutoff H. exact (IH ms a (S cutoff) H).
  - intros t l IH ms a cutoff H. exact (IH ms a cutoff H).
  - intros body IH ms a cutoff H. exact (IH ms a cutoff H).
  - intros K l lts Ts ts IH ms a cutoff H.
    rewrite well_scoped_ctor_eq, rt_closed_ctor_eq in H.
    cbn [shift_ty_in_tm]. rewrite well_scoped_ctor_eq, rt_closed_ctor_eq.
    exact (IH ms a cutoff H).
  - intros scrut tag nlt ar y n IHs IHy IHn ms a cutoff [[Ws [Wy Wn]] [Rs [Ry Rn]]].
    destruct (IHs ms a cutoff (conj Ws Rs)) as [Ws' Rs'].
    destruct (IHy ms a cutoff (conj Wy Ry)) as [Wy' Ry'].
    destruct (IHn ms a cutoff (conj Wn Rn)) as [Wn' Rn'].
    split; [split; [exact Ws' | split; [exact Wy' | exact Wn']]
           | split; [exact Rs' | split; [exact Ry' | exact Rn']]].
  - intros E Ts T_B T_R op_bodies body IHops IHb ms a cutoff [[Wop Wb] [Rop Rb]].
    cbn [shift_ty_in_tm]. rewrite shift_ty_in_tm_ops_eq_map.
    destruct (IHops ms a cutoff (conj Wop Rop)) as [Wop' Rop'].
    destruct (IHb ms a cutoff (conj Wb Rb)) as [Wb' Rb'].
    split; split; assumption.
  - intros t op Ss A_ret arg IHt IHa ms a cutoff [[Wt Wa] [Rt Ra]].
    destruct (IHt ms a cutoff (conj Wt Rt)) as [Wt' Rt'].
    destruct (IHa ms a cutoff (conj Wa Ra)) as [Wa' Ra'].
    split; split; assumption.
  - intros E_tag m Ts T_R op_bodies IHops ms a cutoff [[Hin Hws] Hcap].
    cbn [shift_ty_in_tm]. rewrite shift_ty_in_tm_ops_eq_map.
    apply ops_cap_closed_split in Hcap as [Hfv Hrt].
    destruct (IHops (scope_below m ms) a cutoff (conj Hws Hrt)) as [Hws' Hrt'].
    split.
    + split; [exact Hin | exact Hws'].
    + apply ops_cap_closed_join; [|exact Hrt'].
      clear - Hfv. induction Hfv as [|[nb ob] obs Hfv1 Hrest IH]; simpl; constructor.
      * simpl in Hfv1 |- *. rewrite free_tm_vars_shift_ty_in_tm_any. exact Hfv1.
      * exact IH.
  - intros m T_B T_R body IH ms a cutoff H. exact (IH (m :: ms) a cutoff H).
  - intros ms a cutoff _. split; exact I.
  - intros u ts IHu IHts ms a cutoff [[Wu Wts] [Ru Rts]].
    destruct (IHu ms a cutoff (conj Wu Ru)) as [Wu' Ru'].
    destruct (IHts ms a cutoff (conj Wts Rts)) as [Wts' Rts'].
    split; split; assumption.
  - intros ms a cutoff _. split; exact I.
  - intros nb ob obs IHob IHobs ms a cutoff [[Wob Wobs] [Rob Robs]].
    destruct (IHob ms a (cutoff + nb) (conj Wob Rob)) as [Wob' Rob'].
    destruct (IHobs ms a cutoff (conj Wobs Robs)) as [Wobs' Robs'].
    split; split; assumption.
Qed.

Lemma ws_rt_shift_lt_in_tm : forall t ms a cutoff,
  ws_rt ms t -> ws_rt ms (shift_lt_in_tm a cutoff t).
Proof.
  unfold ws_rt.
  apply (term_list_ind
    (fun t => forall ms a cutoff,
       well_scoped ms t /\ rt_closed t ->
       well_scoped ms (shift_lt_in_tm a cutoff t) /\
       rt_closed (shift_lt_in_tm a cutoff t))
    (fun ts => forall ms a cutoff,
       well_scoped_list ms ts /\ rt_closed_list ts ->
       well_scoped_list ms (List.map (shift_lt_in_tm a cutoff) ts) /\
       rt_closed_list (List.map (shift_lt_in_tm a cutoff) ts))
    (fun obs => forall ms a cutoff,
       ops_well_scoped ms obs /\ ops_rt_closed obs ->
       ops_well_scoped ms
         (List.map (fun p => (fst p, shift_lt_in_tm a cutoff (snd p))) obs) /\
       ops_rt_closed
         (List.map (fun p => (fst p, shift_lt_in_tm a cutoff (snd p))) obs))).
  - intros n ms a cutoff _. split; exact I.
  - intros t1 t2 IH1 IH2 ms a cutoff [[W1 W2] [R1 R2]].
    destruct (IH1 ms a cutoff (conj W1 R1)) as [W1' R1'].
    destruct (IH2 ms a cutoff (conj W2 R2)) as [W2' R2'].
    split; split; assumption.
  - intros body T IH ms a cutoff H. exact (IH ms a cutoff H).
  - intros t T IH ms a cutoff H. exact (IH ms a cutoff H).
  - intros bound body IH ms a cutoff H. exact (IH ms a cutoff H).
  - intros t l IH ms a cutoff H. exact (IH ms a cutoff H).
  - intros body IH ms a cutoff H. exact (IH ms a (S cutoff) H).
  - intros K l lts Ts ts IH ms a cutoff H.
    rewrite well_scoped_ctor_eq, rt_closed_ctor_eq in H.
    cbn [shift_lt_in_tm]. rewrite well_scoped_ctor_eq, rt_closed_ctor_eq.
    exact (IH ms a cutoff H).
  - intros scrut tag nlt ar y n IHs IHy IHn ms a cutoff [[Ws [Wy Wn]] [Rs [Ry Rn]]].
    destruct (IHs ms a cutoff (conj Ws Rs)) as [Ws' Rs'].
    destruct (IHy ms a (cutoff + nlt) (conj Wy Ry)) as [Wy' Ry'].
    destruct (IHn ms a cutoff (conj Wn Rn)) as [Wn' Rn'].
    split; [split; [exact Ws' | split; [exact Wy' | exact Wn']]
           | split; [exact Rs' | split; [exact Ry' | exact Rn']]].
  - intros E Ts T_B T_R op_bodies body IHops IHb ms a cutoff [[Wop Wb] [Rop Rb]].
    cbn [shift_lt_in_tm]. rewrite shift_lt_in_tm_ops_eq_map.
    destruct (IHops ms a cutoff (conj Wop Rop)) as [Wop' Rop'].
    destruct (IHb ms a cutoff (conj Wb Rb)) as [Wb' Rb'].
    split; split; assumption.
  - intros t op Ss A_ret arg IHt IHa ms a cutoff [[Wt Wa] [Rt Ra]].
    destruct (IHt ms a cutoff (conj Wt Rt)) as [Wt' Rt'].
    destruct (IHa ms a cutoff (conj Wa Ra)) as [Wa' Ra'].
    split; split; assumption.
  - intros E_tag m Ts T_R op_bodies IHops ms a cutoff [[Hin Hws] Hcap].
    cbn [shift_lt_in_tm]. rewrite shift_lt_in_tm_ops_eq_map.
    apply ops_cap_closed_split in Hcap as [Hfv Hrt].
    destruct (IHops (scope_below m ms) a cutoff (conj Hws Hrt)) as [Hws' Hrt'].
    split.
    + split; [exact Hin | exact Hws'].
    + apply ops_cap_closed_join; [|exact Hrt'].
      clear - Hfv. induction Hfv as [|[nb ob] obs Hfv1 Hrest IH]; simpl; constructor.
      * simpl in Hfv1 |- *. rewrite free_tm_vars_shift_lt_in_tm_any. exact Hfv1.
      * exact IH.
  - intros m T_B T_R body IH ms a cutoff H. exact (IH (m :: ms) a cutoff H).
  - intros ms a cutoff _. split; exact I.
  - intros u ts IHu IHts ms a cutoff [[Wu Wts] [Ru Rts]].
    destruct (IHu ms a cutoff (conj Wu Ru)) as [Wu' Ru'].
    destruct (IHts ms a cutoff (conj Wts Rts)) as [Wts' Rts'].
    split; split; assumption.
  - intros ms a cutoff _. split; exact I.
  - intros nb ob obs IHob IHobs ms a cutoff [[Wob Wobs] [Rob Robs]].
    destruct (IHob ms a cutoff (conj Wob Rob)) as [Wob' Rob'].
    destruct (IHobs ms a cutoff (conj Wobs Robs)) as [Wobs' Robs'].
    split; split; assumption.
Qed.

(* The whole clause list of a cap is untouched by term substitution:    *)
(* every body is term-closed above its two binders.                     *)
Lemma subst_tm_ops_closed_id : forall (obs : list (nat * term)) var w,
  Forall (fun p => free_tm_vars 2 (snd p) = []) obs ->
  List.map (fun p => (fst p, subst_tm (var + 2) (shift_tm 2 0 w) (snd p))) obs = obs.
Proof.
  intros obs var w H. induction H as [|[nb ob] obs H1 Hrest IH]; simpl; [reflexivity|].
  simpl in H1.
  rewrite (subst_tm_closed_id ob 2 (var + 2) (shift_tm 2 0 w) H1) by lia.
  rewrite IH. reflexivity.
Qed.

(* The fused crux substitution law: substituting a CLOSED ws_rt value  *)
(* preserves ws_rt at the same scope.  Substitution is the identity     *)
(* inside every scope-sensitive cap body (the rt_closed conjunct), and  *)
(* everywhere else the ambient scope only ever EXTENDS (handler_m),     *)
(* which well_scoped_mono transports the value across.                  *)
Lemma ws_rt_subst_tm : forall t var w ms,
  ws_rt ms t ->
  free_tm_vars 0 w = [] ->
  ws_rt ms w ->
  ws_rt ms (subst_tm var w t).
Proof.
  unfold ws_rt.
  apply (term_list_ind
    (fun t => forall var w ms,
       well_scoped ms t /\ rt_closed t ->
       free_tm_vars 0 w = [] ->
       well_scoped ms w /\ rt_closed w ->
       well_scoped ms (subst_tm var w t) /\ rt_closed (subst_tm var w t))
    (fun ts => forall var w ms,
       well_scoped_list ms ts /\ rt_closed_list ts ->
       free_tm_vars 0 w = [] ->
       well_scoped ms w /\ rt_closed w ->
       well_scoped_list ms (List.map (subst_tm var w) ts) /\
       rt_closed_list (List.map (subst_tm var w) ts))
    (fun obs => forall var w ms,
       ops_well_scoped ms obs /\ ops_rt_closed obs ->
       free_tm_vars 0 w = [] ->
       well_scoped ms w /\ rt_closed w ->
       ops_well_scoped ms
         (List.map (fun p => (fst p, subst_tm (var + 2) (shift_tm 2 0 w) (snd p))) obs) /\
       ops_rt_closed
         (List.map (fun p => (fst p, subst_tm (var + 2) (shift_tm 2 0 w) (snd p))) obs))).
  - intros n var w ms _ Hfw Hw. cbn [subst_tm].
    destruct (Nat.eqb n var); [exact Hw|].
    destruct (Nat.ltb var n); split; exact I.
  - intros t1 t2 IH1 IH2 var w ms [[W1 W2] [R1 R2]] Hfw Hw.
    destruct (IH1 var w ms (conj W1 R1) Hfw Hw) as [W1' R1'].
    destruct (IH2 var w ms (conj W2 R2) Hfw Hw) as [W2' R2'].
    split; split; assumption.
  - intros body T IH var w ms H Hfw Hw. cbn [subst_tm].
    rewrite (shift_tm_closed_id w 0 1 0 Hfw) by lia.
    exact (IH (S var) w ms H Hfw Hw).
  - intros t T IH var w ms H Hfw Hw. exact (IH var w ms H Hfw Hw).
  - intros bound body IH var w ms H Hfw Hw.
    assert (Hfw' : free_tm_vars 0 (shift_ty_in_tm 1 0 w) = []).
    { rewrite free_tm_vars_shift_ty_in_tm_any. exact Hfw. }
    exact (IH var (shift_ty_in_tm 1 0 w) ms H Hfw'
             (ws_rt_shift_ty_in_tm w ms 1 0 Hw)).
  - intros t l IH var w ms H Hfw Hw. exact (IH var w ms H Hfw Hw).
  - intros body IH var w ms H Hfw Hw.
    assert (Hfw' : free_tm_vars 0 (shift_lt_in_tm 1 0 w) = []).
    { rewrite free_tm_vars_shift_lt_in_tm_any. exact Hfw. }
    exact (IH var (shift_lt_in_tm 1 0 w) ms H Hfw'
             (ws_rt_shift_lt_in_tm w ms 1 0 Hw)).
  - intros K l lts Ts ts IH var w ms H Hfw Hw.
    rewrite well_scoped_ctor_eq, rt_closed_ctor_eq in H.
    cbn [subst_tm]. rewrite well_scoped_ctor_eq, rt_closed_ctor_eq.
    exact (IH var w ms H Hfw Hw).
  - intros scrut tag nlt ar y n IHs IHy IHn var w ms [[Ws [Wy Wn]] [Rs [Ry Rn]]] Hfw Hw.
    assert (Hfw' : free_tm_vars 0 (shift_lt_in_tm nlt 0 w) = []).
    { rewrite free_tm_vars_shift_lt_in_tm_any. exact Hfw. }
    cbn [subst_tm].
    rewrite (shift_tm_closed_id (shift_lt_in_tm nlt 0 w) 0 ar 0 Hfw') by lia.
    destruct (IHs var w ms (conj Ws Rs) Hfw Hw) as [Ws' Rs'].
    destruct (IHy (var + ar) (shift_lt_in_tm nlt 0 w) ms (conj Wy Ry) Hfw'
                (ws_rt_shift_lt_in_tm w ms nlt 0 Hw)) as [Wy' Ry'].
    destruct (IHn var w ms (conj Wn Rn) Hfw Hw) as [Wn' Rn'].
    split; [split; [exact Ws' | split; [exact Wy' | exact Wn']]
           | split; [exact Rs' | split; [exact Ry' | exact Rn']]].
  - intros E Ts T_B T_R op_bodies body IHops IHb var w ms [[Wop Wb] [Rop Rb]] Hfw Hw.
    cbn [subst_tm].
    rewrite (shift_tm_closed_id w 0 1 0 Hfw) by lia.
    rewrite subst_tm_ops_eq_map.
    destruct (IHops var w ms (conj Wop Rop) Hfw Hw) as [Wop' Rop'].
    destruct (IHb (S var) w ms (conj Wb Rb) Hfw Hw) as [Wb' Rb'].
    split; split; assumption.
  - intros t op Ss A_ret arg IHt IHa var w ms [[Wt Wa] [Rt Ra]] Hfw Hw.
    destruct (IHt var w ms (conj Wt Rt) Hfw Hw) as [Wt' Rt'].
    destruct (IHa var w ms (conj Wa Ra) Hfw Hw) as [Wa' Ra'].
    split; split; assumption.
  - intros E_tag m Ts T_R op_bodies IHops var w ms [[Hin Hws] Hcap] Hfw Hw.
    cbn [subst_tm]. rewrite subst_tm_ops_eq_map.
    apply ops_cap_closed_split in Hcap as [Hfv2 Hrt].
    rewrite (subst_tm_ops_closed_id op_bodies var w Hfv2).
    split; [split; [exact Hin | exact Hws] | apply ops_cap_closed_join; assumption].
  - intros m T_B T_R body IH var w ms H Hfw Hw. destruct Hw as [Hww Hrw].
    assert (Hww' : well_scoped (m :: ms) w).
    { apply (well_scoped_mono w ms (m :: ms)); [apply se_top; apply se_refl | exact Hww]. }
    exact (IH var w (m :: ms) H Hfw (conj Hww' Hrw)).
  - intros var w ms _ _ _. split; exact I.
  - intros u ts IHu IHts var w ms [[Wu Wts] [Ru Rts]] Hfw Hw.
    destruct (IHu var w ms (conj Wu Ru) Hfw Hw) as [Wu' Ru'].
    destruct (IHts var w ms (conj Wts Rts) Hfw Hw) as [Wts' Rts'].
    split; split; assumption.
  - intros var w ms _ _ _. split; exact I.
  - intros nb ob obs IHob IHobs var w ms [[Wob Wobs] [Rob Robs]] Hfw Hw.
    assert (Hfw2 : free_tm_vars 0 (shift_tm 2 0 w) = []).
    { rewrite (shift_tm_closed_id w 0 2 0 Hfw) by lia. exact Hfw. }
    assert (Hw2 : well_scoped ms (shift_tm 2 0 w) /\ rt_closed (shift_tm 2 0 w)).
    { rewrite (shift_tm_closed_id w 0 2 0 Hfw) by lia. exact Hw. }
    destruct (IHob (var + 2) (shift_tm 2 0 w) ms (conj Wob Rob) Hfw2 Hw2) as [Wob' Rob'].
    destruct (IHobs var w ms (conj Wobs Robs) Hfw Hw) as [Wobs' Robs'].
    split; split; assumption.
Qed.

(* Fused type/lifetime substitution laws: neither touches markers or   *)
(* term variables, so ws_rt is preserved with no side conditions.       *)
Lemma ws_rt_subst_ty_in_tm : forall t var R ms,
  ws_rt ms t -> ws_rt ms (subst_ty_in_tm var R t).
Proof.
  unfold ws_rt.
  apply (term_list_ind
    (fun t => forall var R ms,
       well_scoped ms t /\ rt_closed t ->
       well_scoped ms (subst_ty_in_tm var R t) /\ rt_closed (subst_ty_in_tm var R t))
    (fun ts => forall var R ms,
       well_scoped_list ms ts /\ rt_closed_list ts ->
       well_scoped_list ms (List.map (subst_ty_in_tm var R) ts) /\
       rt_closed_list (List.map (subst_ty_in_tm var R) ts))
    (fun obs => forall var R ms,
       ops_well_scoped ms obs /\ ops_rt_closed obs ->
       ops_well_scoped ms (List.map (fun p =>
         (fst p, subst_ty_in_tm (var + fst p) (shift_ty (fst p) 0 R) (snd p))) obs) /\
       ops_rt_closed (List.map (fun p =>
         (fst p, subst_ty_in_tm (var + fst p) (shift_ty (fst p) 0 R) (snd p))) obs))).
  - intros n var R ms _. split; exact I.
  - intros t1 t2 IH1 IH2 var R ms [[W1 W2] [R1 R2]].
    destruct (IH1 var R ms (conj W1 R1)) as [W1' R1'].
    destruct (IH2 var R ms (conj W2 R2)) as [W2' R2'].
    split; split; assumption.
  - intros body T IH var R ms H. exact (IH var R ms H).
  - intros t T IH var R ms H. exact (IH var R ms H).
  - intros bound body IH var R ms H. exact (IH (S var) (shift_ty 1 0 R) ms H).
  - intros t l IH var R ms H. exact (IH var R ms H).
  - intros body IH var R ms H. exact (IH var (shift_lt_in_ty 1 0 R) ms H).
  - intros K l lts Ts ts IH var R ms H.
    replace (subst_ty_in_tm var R (term_ctor K l lts Ts ts))
      with (term_ctor K l lts (map_subst_ty var R Ts) (List.map (subst_ty_in_tm var R) ts))
      by (cbn [subst_ty_in_tm]; reflexivity).
    rewrite well_scoped_ctor_eq, rt_closed_ctor_eq in H.
    rewrite well_scoped_ctor_eq, rt_closed_ctor_eq.
    exact (IH var R ms H).
  - intros scrut tag nlt ar y n IHs IHy IHn var R ms [[Ws [Wy Wn]] [Rs [Ry Rn]]].
    destruct (IHs var R ms (conj Ws Rs)) as [Ws' Rs'].
    destruct (IHy var (shift_lt_in_ty nlt 0 R) ms (conj Wy Ry)) as [Wy' Ry'].
    destruct (IHn var R ms (conj Wn Rn)) as [Wn' Rn'].
    split; [split; [exact Ws' | split; [exact Wy' | exact Wn']]
           | split; [exact Rs' | split; [exact Ry' | exact Rn']]].
  - intros E Ts T_B T_R op_bodies body IHops IHb var R ms [[Wop Wb] [Rop Rb]].
    cbn [subst_ty_in_tm]. rewrite subst_ty_in_tm_ops_eq_map.
    destruct (IHops var R ms (conj Wop Rop)) as [Wop' Rop'].
    destruct (IHb var R ms (conj Wb Rb)) as [Wb' Rb'].
    split; split; assumption.
  - intros t op Ss A_ret arg IHt IHa var R ms [[Wt Wa] [Rt Ra]].
    destruct (IHt var R ms (conj Wt Rt)) as [Wt' Rt'].
    destruct (IHa var R ms (conj Wa Ra)) as [Wa' Ra'].
    split; split; assumption.
  - intros E_tag m Ts T_R op_bodies IHops var R ms [[Hin Hws] Hcap].
    cbn [subst_ty_in_tm]. rewrite subst_ty_in_tm_ops_eq_map.
    apply ops_cap_closed_split in Hcap as [Hfv Hrt].
    destruct (IHops var R (scope_below m ms) (conj Hws Hrt)) as [Hws' Hrt'].
    split.
    + split; [exact Hin | exact Hws'].
    + apply ops_cap_closed_join; [|exact Hrt'].
      clear - Hfv. induction Hfv as [|[nb ob] obs Hfv1 Hrest IH]; simpl; constructor.
      * simpl in Hfv1 |- *. rewrite free_tm_vars_subst_ty_in_tm. exact Hfv1.
      * exact IH.
  - intros m T_B T_R body IH var R ms H. exact (IH var R (m :: ms) H).
  - intros var R ms _. split; exact I.
  - intros u ts IHu IHts var R ms [[Wu Wts] [Ru Rts]].
    destruct (IHu var R ms (conj Wu Ru)) as [Wu' Ru'].
    destruct (IHts var R ms (conj Wts Rts)) as [Wts' Rts'].
    split; split; assumption.
  - intros var R ms _. split; exact I.
  - intros nb ob obs IHob IHobs var R ms [[Wob Wobs] [Rob Robs]].
    destruct (IHob (var + nb) (shift_ty nb 0 R) ms (conj Wob Rob)) as [Wob' Rob'].
    destruct (IHobs var R ms (conj Wobs Robs)) as [Wobs' Robs'].
    split; split; assumption.
Qed.

Lemma ws_rt_subst_lt_in_tm : forall t var R ms,
  ws_rt ms t -> ws_rt ms (subst_lt_in_tm var R t).
Proof.
  unfold ws_rt.
  apply (term_list_ind
    (fun t => forall var R ms,
       well_scoped ms t /\ rt_closed t ->
       well_scoped ms (subst_lt_in_tm var R t) /\ rt_closed (subst_lt_in_tm var R t))
    (fun ts => forall var R ms,
       well_scoped_list ms ts /\ rt_closed_list ts ->
       well_scoped_list ms (List.map (subst_lt_in_tm var R) ts) /\
       rt_closed_list (List.map (subst_lt_in_tm var R) ts))
    (fun obs => forall var R ms,
       ops_well_scoped ms obs /\ ops_rt_closed obs ->
       ops_well_scoped ms
         (List.map (fun p => (fst p, subst_lt_in_tm var R (snd p))) obs) /\
       ops_rt_closed
         (List.map (fun p => (fst p, subst_lt_in_tm var R (snd p))) obs))).
  - intros n var R ms _. split; exact I.
  - intros t1 t2 IH1 IH2 var R ms [[W1 W2] [R1 R2]].
    destruct (IH1 var R ms (conj W1 R1)) as [W1' R1'].
    destruct (IH2 var R ms (conj W2 R2)) as [W2' R2'].
    split; split; assumption.
  - intros body T IH var R ms H. exact (IH var R ms H).
  - intros t T IH var R ms H. exact (IH var R ms H).
  - intros bound body IH var R ms H. exact (IH var R ms H).
  - intros t l IH var R ms H. exact (IH var R ms H).
  - intros body IH var R ms H. exact (IH (S var) (shift_lt 1 0 R) ms H).
  - intros K l lts Ts ts IH var R ms H.
    rewrite well_scoped_ctor_eq, rt_closed_ctor_eq in H.
    cbn [subst_lt_in_tm]. rewrite well_scoped_ctor_eq, rt_closed_ctor_eq.
    exact (IH var R ms H).
  - intros scrut tag nlt ar y n IHs IHy IHn var R ms [[Ws [Wy Wn]] [Rs [Ry Rn]]].
    destruct (IHs var R ms (conj Ws Rs)) as [Ws' Rs'].
    destruct (IHy (nlt + var) (shift_lt nlt 0 R) ms (conj Wy Ry)) as [Wy' Ry'].
    destruct (IHn var R ms (conj Wn Rn)) as [Wn' Rn'].
    split; [split; [exact Ws' | split; [exact Wy' | exact Wn']]
           | split; [exact Rs' | split; [exact Ry' | exact Rn']]].
  - intros E Ts T_B T_R op_bodies body IHops IHb var R ms [[Wop Wb] [Rop Rb]].
    cbn [subst_lt_in_tm]. rewrite subst_lt_in_tm_ops_eq_map.
    destruct (IHops var R ms (conj Wop Rop)) as [Wop' Rop'].
    destruct (IHb var R ms (conj Wb Rb)) as [Wb' Rb'].
    split; split; assumption.
  - intros t op Ss A_ret arg IHt IHa var R ms [[Wt Wa] [Rt Ra]].
    destruct (IHt var R ms (conj Wt Rt)) as [Wt' Rt'].
    destruct (IHa var R ms (conj Wa Ra)) as [Wa' Ra'].
    split; split; assumption.
  - intros E_tag m Ts T_R op_bodies IHops var R ms [[Hin Hws] Hcap].
    cbn [subst_lt_in_tm]. rewrite subst_lt_in_tm_ops_eq_map.
    apply ops_cap_closed_split in Hcap as [Hfv Hrt].
    destruct (IHops var R (scope_below m ms) (conj Hws Hrt)) as [Hws' Hrt'].
    split.
    + split; [exact Hin | exact Hws'].
    + apply ops_cap_closed_join; [|exact Hrt'].
      clear - Hfv. induction Hfv as [|[nb ob] obs Hfv1 Hrest IH]; simpl; constructor.
      * simpl in Hfv1 |- *. rewrite free_tm_vars_subst_lt_in_tm. exact Hfv1.
      * exact IH.
  - intros m T_B T_R body IH var R ms H. exact (IH var R (m :: ms) H).
  - intros var R ms _. split; exact I.
  - intros u ts IHu IHts var R ms [[Wu Wts] [Ru Rts]].
    destruct (IHu var R ms (conj Wu Ru)) as [Wu' Ru'].
    destruct (IHts var R ms (conj Wts Rts)) as [Wts' Rts'].
    split; split; assumption.
  - intros var R ms _. split; exact I.
  - intros nb ob obs IHob IHobs var R ms [[Wob Wobs] [Rob Robs]].
    destruct (IHob var R ms (conj Wob Rob)) as [Wob' Rob'].
    destruct (IHobs var R ms (conj Wobs Robs)) as [Wobs' Robs'].
    split; split; assumption.
Qed.

(* Iterated substitution of closed ws_rt values. *)
Lemma ws_rt_subst_list_tm : forall vs t ms,
  Forall (fun v => free_tm_vars 0 v = []) vs ->
  Forall (ws_rt ms) vs ->
  ws_rt ms t ->
  ws_rt ms (subst_list_tm vs t).
Proof.
  induction vs as [|v rest IH]; intros t ms Hfv Hwr Ht.
  - exact Ht.
  - inversion Hfv as [|? ? Hfv1 Hfvr]; subst.
    inversion Hwr as [|? ? Hwr1 Hwrr]; subst.
    cbn [subst_list_tm].
    rewrite (shift_tm_closed_id v 0 (List.length rest) 0 Hfv1) by lia.
    apply IH; try assumption.
    apply ws_rt_subst_tm; assumption.
Qed.

(* ==================================================================== *)
(* Plug lemmas: closedness and the runtime invariants through an ectx.  *)
(* No ectx frame crosses a term binder, so all hole positions sit at    *)
(* term-cutoff 0.                                                       *)
(* ==================================================================== *)

Lemma free_tm_vars_plug_nil_inv : forall E r,
  free_tm_vars 0 (plug E r) = [] -> free_tm_vars 0 r = [].
Proof.
  induction E as
    [ | E1 IHE ta | ta E1 IHE | E1 IHE Ty | E1 IHE lt
    | tag dl lts Tys vs E1 IHE ts | E1 IHE K nlt ar yes no
    | mk TB TR E1 IHE | E1 IHE opx Ss An ar2 | rcv opx Ss An E1 IHE ];
    intros r Hfv; cbn [plug] in Hfv; simpl in Hfv.
  - exact Hfv.
  - apply app_eq_nil in Hfv as [H _]. apply IHE; exact H.
  - apply app_eq_nil in Hfv as [_ H]. apply IHE; exact H.
  - apply IHE; exact Hfv.
  - apply IHE; exact Hfv.
  - rewrite map_app in Hfv. rewrite concat_app in Hfv.
    apply app_eq_nil in Hfv as [_ Hfv]. simpl in Hfv.
    apply app_eq_nil in Hfv as [H _]. apply IHE; exact H.
  - apply app_eq_nil in Hfv as [H _]. apply IHE; exact H.
  - apply IHE; exact Hfv.
  - apply app_eq_nil in Hfv as [H _]. apply IHE; exact H.
  - apply app_eq_nil in Hfv as [_ H]. apply IHE; exact H.
Qed.

(* Fused structural plug-replace: frames thread the scope, the          *)
(* EC_handler_m frame prepends its marker, and the replacement          *)
(* callback fires at whatever scope the hole sits at.                   *)
Lemma ws_rt_plug_replace : forall E r r' ms,
  ws_rt ms (plug E r) ->
  (forall ms', ws_rt ms' r -> ws_rt ms' r') ->
  ws_rt ms (plug E r').
Proof.
  induction E as
    [ | E1 IHE ta | ta E1 IHE | E1 IHE Ty | E1 IHE lt
    | tag dl lts Tys vs E1 IHE ts | E1 IHE K nlt ar yes no
    | mk TB TR E1 IHE | E1 IHE opx Ss An ar2 | rcv opx Ss An E1 IHE ];
    intros r r' ms Hwr Hrep; unfold ws_rt in Hwr |- *; cbn [plug] in Hwr |- *.
  - exact (Hrep ms Hwr).
  - destruct Hwr as [[W1 W2] [R1 R2]].
    destruct (IHE r r' ms (conj W1 R1) Hrep) as [W' R'].
    split; split; assumption.
  - destruct Hwr as [[W1 W2] [R1 R2]].
    destruct (IHE r r' ms (conj W2 R2) Hrep) as [W' R'].
    split; split; assumption.
  - exact (IHE r r' ms Hwr Hrep).
  - exact (IHE r r' ms Hwr Hrep).
  - destruct Hwr as [Hws Hrt].
    rewrite well_scoped_ctor_eq in Hws. rewrite rt_closed_ctor_eq in Hrt.
    rewrite well_scoped_ctor_eq, rt_closed_ctor_eq.
    revert Hws Hrt. induction vs as [|a vs' IHvs]; intros Hws Hrt;
      cbn [List.app] in Hws, Hrt |- *.
    + destruct Hws as [Wfoc Wrest]. destruct Hrt as [Rfoc Rrest].
      destruct (IHE r r' ms (conj Wfoc Rfoc) Hrep) as [W' R'].
      split; split; assumption.
    + destruct Hws as [Wa Wrest]. destruct Hrt as [Ra Rrest].
      destruct (IHvs Wrest Rrest) as [W' R'].
      split; split; assumption.
  - destruct Hwr as [[Ws [Wy Wn]] [Rs [Ry Rn]]].
    destruct (IHE r r' ms (conj Ws Rs) Hrep) as [W' R'].
    split; [split; [exact W' | split; [exact Wy | exact Wn]]
           | split; [exact R' | split; [exact Ry | exact Rn]]].
  - exact (IHE r r' (mk :: ms) Hwr Hrep).
  - destruct Hwr as [[W1 W2] [R1 R2]].
    destruct (IHE r r' ms (conj W1 R1) Hrep) as [W' R'].
    split; split; assumption.
  - destruct Hwr as [[W1 W2] [R1 R2]].
    destruct (IHE r r' ms (conj W2 R2) Hrep) as [W' R'].
    split; split; assumption.
Qed.

(* ==================================================================== *)
(* Confinement: the H_Perform facts, returning full well-scopedness     *)
(* of the op-body at the scope OUTSIDE the delimiter.                   *)
(* ==================================================================== *)

Lemma well_scoped_pure_cap_confined :
  forall P m ms E_tag Ts T_R op_bodies op Ss A v,
  pure_ectx_m m P ->
  well_scoped ms (plug P (term_perform (term_cap E_tag m Ts T_R op_bodies) op Ss A v)) ->
  ops_well_scoped (scope_below m ms) op_bodies.
Proof.
  intros P m ms E_tag Ts T_R op_bodies op Ss A v Hpure. revert ms.
  induction Hpure; intros ms Hws; cbn [plug] in Hws.
  - destruct Hws as [Hcap _]. destruct Hcap as [_ Hop]. exact Hop.
  - destruct Hws as [W1 _]. apply IHHpure. exact W1.
  - destruct Hws as [_ W2]. apply IHHpure. exact W2.
  - apply IHHpure. exact Hws.
  - apply IHHpure. exact Hws.
  - rewrite well_scoped_ctor_eq in Hws.
    apply IHHpure.
    induction vs as [|u vs IHvs]; cbn [List.app] in Hws.
    + destruct Hws as [Wfoc _]. exact Wfoc.
    + destruct Hws as [_ Wrest]. apply IHvs. exact Wrest.
  - destruct Hws as [Ws _]. apply IHHpure. exact Ws.
  - specialize (IHHpure (m' :: ms) Hws).
    rewrite scope_below_cons_neq in IHHpure; [exact IHHpure | auto].
  - destruct Hws as [W1 _]. apply IHHpure. exact W1.
  - destruct Hws as [_ W2]. apply IHHpure. exact W2.
Qed.

(* The H_Perform confinement: the op-body of the performing cap is      *)
(* well-scoped at the scope outside the matching delimiter — exactly    *)
(* where the reduct lands.                                              *)
Lemma well_scoped_step_handler_confinement :
  forall ms m T_B T_R E_tag Ts T_R' op_bodies op n_beta op_body Ss A v P,
  well_scoped ms (term_handler_m m T_B T_R
    (plug P (term_perform (term_cap E_tag m Ts T_R' op_bodies) op Ss A v))) ->
  pure_ectx_m m P ->
  nth_error op_bodies op = Some (n_beta, op_body) ->
  well_scoped ms op_body.
Proof.
  intros ms m T_B T_R E_tag Ts T_R' op_bodies op n_beta op_body Ss A v P Hws Hpure Hnth.
  pose proof (well_scoped_pure_cap_confined P m (m :: ms) E_tag Ts T_R' op_bodies op Ss A v
    Hpure Hws) as Hc.
  rewrite scope_below_cons_eq in Hc.
  eapply ops_well_scoped_nth; [exact Hc | exact Hnth].
Qed.

(* ==================================================================== *)
(* Support lemmas: list bridges, closed-substitution fv laws, plug      *)
(* decompositions, and the reified-resume-body facts.                   *)
(* ==================================================================== *)

Lemma Forall_of_concat_map_nil :
  forall (A B : Type) (f : A -> list B) (xs : list A),
  List.concat (List.map f xs) = [] -> Forall (fun x => f x = []) xs.
Proof.
  intros A B f xs H. induction xs as [|x xs IH]; [constructor|].
  simpl in H. apply app_eq_nil in H as [H1 H2].
  constructor; [exact H1 | apply IH; exact H2].
Qed.

(* Fused list-form/Forall bridge. *)
Lemma ws_rt_list_Forall : forall ms ts,
  well_scoped_list ms ts -> rt_closed_list ts -> Forall (ws_rt ms) ts.
Proof.
  intros ms ts Hw Hr. induction ts as [|u ts IH].
  - constructor.
  - destruct Hw as [Hwu Hwts]. destruct Hr as [Hru Hrts].
    constructor; [split; assumption | apply IH; assumption].
Qed.

Lemma ws_rt_subst_list_ty_in_tm : forall Ss t ms,
  ws_rt ms t -> ws_rt ms (subst_list_ty_in_tm Ss t).
Proof.
  induction Ss as [|S0 Ss IH]; intros t ms H; simpl; [exact H|].
  apply IH. apply ws_rt_subst_ty_in_tm. exact H.
Qed.

Lemma ws_rt_subst_list_lt_in_tm : forall lts t ms,
  ws_rt ms t -> ws_rt ms (subst_list_lt_in_tm lts t).
Proof.
  induction lts as [|l lts IH]; intros t ms H; simpl; [exact H|].
  apply IH. apply ws_rt_subst_lt_in_tm. exact H.
Qed.

Lemma map_shift_tm_closed_id : forall vs a cutoff,
  Forall (fun v => free_tm_vars 0 v = []) vs ->
  List.map (shift_tm a cutoff) vs = vs.
Proof.
  intros vs a cutoff H. induction H as [|v vs Hv Hvs IH]; simpl; [reflexivity|].
  rewrite (shift_tm_closed_id v 0 a cutoff Hv) by lia. rewrite IH. reflexivity.
Qed.

Lemma concat_map_fv_closed_cutoff : forall vs c,
  Forall (fun v => free_tm_vars 0 v = []) vs ->
  List.concat (List.map (free_tm_vars c) vs) = [].
Proof.
  intros vs c H. induction H as [|v vs Hv Hvs IH]; simpl; [reflexivity|].
  rewrite (free_tm_vars_closed_cutoff v c Hv). rewrite IH. reflexivity.
Qed.

Lemma rt_closed_plug_inv : forall E r, rt_closed (plug E r) -> rt_closed r.
Proof.
  induction E as
    [ | E1 IHE ta | ta E1 IHE | E1 IHE Ty | E1 IHE lt
    | tag dl lts Tys vs E1 IHE ts | E1 IHE K nlt ar yes no
    | mk TB TR E1 IHE | E1 IHE opx Ss An ar2 | rcv opx Ss An E1 IHE ];
    intros r Hrt; cbn [plug] in Hrt.
  - exact Hrt.
  - destruct Hrt as [H _]. apply IHE; exact H.
  - destruct Hrt as [_ H]. apply IHE; exact H.
  - apply IHE; exact Hrt.
  - apply IHE; exact Hrt.
  - rewrite rt_closed_ctor_eq in Hrt.
    induction vs as [|a vs' IHvs]; cbn [List.app] in Hrt.
    + destruct Hrt as [H _]. apply IHE; exact H.
    + destruct Hrt as [_ H]. apply IHvs; exact H.
  - destruct Hrt as [H _]. apply IHE; exact H.
  - apply IHE; exact Hrt.
  - destruct Hrt as [H _]. apply IHE; exact H.
  - destruct Hrt as [_ H]. apply IHE; exact H.
Qed.

(* The reified resumption body [plug (shift_ectx_tm 1 0 P) (term_var 0)] *)
(* is closed above its one binder, and rt_closed, whenever the captured *)
(* context came from a closed rt_closed spine.                           *)
Lemma reified_continuation_closed_rt : forall P r,
  free_tm_vars 0 (plug P r) = [] ->
  rt_closed (plug P r) ->
  free_tm_vars 1 (plug (shift_ectx_tm 1 0 P) (term_var 0)) = [] /\
  rt_closed (plug (shift_ectx_tm 1 0 P) (term_var 0)).
Proof.
  induction P as
    [ | E1 IHE ta | ta E1 IHE | E1 IHE Ty | E1 IHE lt
    | tag dl lts Tys vs E1 IHE ts | E1 IHE K nlt ar yes no
    | mk TB TR E1 IHE | E1 IHE opx Ss An ar2 | rcv opx Ss An E1 IHE ];
    intros r Hfv Hrt; cbn [plug shift_ectx_tm] in Hfv, Hrt |- *.
  - split; [reflexivity | exact I].
  - simpl in Hfv. apply app_eq_nil in Hfv as [H1 H2].
    destruct Hrt as [R1 R2].
    destruct (IHE r H1 R1) as [IHfv IHrt].
    rewrite (shift_tm_closed_id ta 0 1 0 H2) by lia.
    split.
    + simpl. rewrite IHfv, (free_tm_vars_closed_cutoff ta 1 H2). reflexivity.
    + split; [exact IHrt | exact R2].
  - simpl in Hfv. apply app_eq_nil in Hfv as [H1 H2].
    destruct Hrt as [R1 R2].
    destruct (IHE r H2 R2) as [IHfv IHrt].
    rewrite (shift_tm_closed_id ta 0 1 0 H1) by lia.
    split.
    + simpl. rewrite IHfv, (free_tm_vars_closed_cutoff ta 1 H1). reflexivity.
    + split; [exact R1 | exact IHrt].
  - simpl in Hfv. destruct (IHE r Hfv Hrt) as [IHfv IHrt].
    split; [simpl; exact IHfv | exact IHrt].
  - simpl in Hfv. destruct (IHE r Hfv Hrt) as [IHfv IHrt].
    split; [simpl; exact IHfv | exact IHrt].
  - simpl in Hfv.    rewrite map_app in Hfv. rewrite concat_app in Hfv.
    apply app_eq_nil in Hfv as [Hvs Hfoc_ts]. simpl in Hfoc_ts.
    apply app_eq_nil in Hfoc_ts as [Hfoc Hts].
    apply Forall_of_concat_map_nil in Hvs.
    apply Forall_of_concat_map_nil in Hts.
    rewrite rt_closed_ctor_eq in Hrt.
    (* Extract the focus and get a rebuild continuation, in one pass    *)
    (* over the value prefix (the rt-only half of the old list/Forall   *)
    (* bridges, derived locally).                                       *)
    assert (Hfocus : rt_closed (plug E1 r) /\
      (rt_closed (plug (shift_ectx_tm 1 0 E1) (term_var 0)) ->
       rt_closed_list (vs ++ plug (shift_ectx_tm 1 0 E1) (term_var 0) :: ts))).
    { clear - Hrt. revert Hrt. induction vs as [|u vs' IHvs]; intros Hrt;
        cbn [List.app] in Hrt |- *.
      - destruct Hrt as [Rfoc Rts].
        split; [exact Rfoc | intros R'; split; [exact R' | exact Rts]].
      - destruct Hrt as [Ru Rrest]. destruct (IHvs Rrest) as [Rfoc Hbuild].
        split; [exact Rfoc | intros R'; split; [exact Ru | apply Hbuild; exact R']]. }
    destruct Hfocus as [Rfoc Hbuild].
    destruct (IHE r Hfoc Rfoc) as [IHfv IHrt].
    rewrite (map_shift_tm_closed_id vs 1 0 Hvs).
    rewrite (map_shift_tm_closed_id ts 1 0 Hts).
    split.
    + simpl.      rewrite map_app. rewrite concat_app. simpl.
      rewrite (concat_map_fv_closed_cutoff vs 1 Hvs).
      rewrite IHfv.
      rewrite (concat_map_fv_closed_cutoff ts 1 Hts). reflexivity.
    + rewrite rt_closed_ctor_eq. apply Hbuild. exact IHrt.
  - simpl in Hfv. apply app_eq_nil in Hfv as [Hs Hyn].
    apply app_eq_nil in Hyn as [Hy Hn].
    destruct Hrt as [Rs [Ry Rn]].
    destruct (IHE r Hs Rs) as [IHfv IHrt].
    rewrite (shift_tm_closed_id yes ar 1 (0 + ar) Hy) by lia.
    rewrite (shift_tm_closed_id no 0 1 0 Hn) by lia.
    split.
    + simpl. rewrite IHfv.
      rewrite (free_tm_vars_cutoff_mono_empty yes ar (S ar)) by (lia || exact Hy).
      rewrite (free_tm_vars_closed_cutoff no 1 Hn). reflexivity.
    + split; [exact IHrt | split; [exact Ry | exact Rn]].
  - simpl in Hfv. destruct (IHE r Hfv Hrt) as [IHfv IHrt].
    split; [simpl; exact IHfv | exact IHrt].
  - simpl in Hfv. apply app_eq_nil in Hfv as [H1 H2].
    destruct Hrt as [R1 R2].
    destruct (IHE r H1 R1) as [IHfv IHrt].
    rewrite (shift_tm_closed_id ar2 0 1 0 H2) by lia.
    split.
    + simpl. rewrite IHfv, (free_tm_vars_closed_cutoff ar2 1 H2). reflexivity.
    + split; [exact IHrt | exact R2].
  - simpl in Hfv. apply app_eq_nil in Hfv as [H1 H2].
    destruct Hrt as [R1 R2].
    destruct (IHE r H2 R2) as [IHfv IHrt].
    rewrite (shift_tm_closed_id rcv 0 1 0 H1) by lia.
    split.
    + simpl. rewrite IHfv, (free_tm_vars_closed_cutoff rcv 1 H1). reflexivity.
    + split; [exact R1 | exact IHrt].
Qed.

(* Shifting the captured context's frame terms preserves well_scoped:  *)
(* term shifts never move markers, and the frame skeleton (hence the    *)
(* scope threading) is unchanged.                                       *)
Lemma well_scoped_plug_shift_ectx_tm : forall P t ms a cutoff,
  well_scoped ms (plug P t) ->
  well_scoped ms (plug (shift_ectx_tm a cutoff P) t).
Proof.
  induction P as
    [ | E1 IHE ta | ta E1 IHE | E1 IHE Ty | E1 IHE lt
    | tag dl lts Tys vs E1 IHE ts | E1 IHE K nlt ar yes no
    | mk TB TR E1 IHE | E1 IHE opx Ss An ar2 | rcv opx Ss An E1 IHE ];
    intros t ms a cutoff Hws; cbn [plug shift_ectx_tm] in Hws |- *.
  - exact Hws.
  - destruct Hws as [H1 H2].
    split; [apply IHE; exact H1 | apply well_scoped_shift_tm; exact H2].
  - destruct Hws as [H1 H2].
    split; [apply well_scoped_shift_tm; exact H1 | apply IHE; exact H2].
  - apply IHE; exact Hws.
  - apply IHE; exact Hws.
  - rewrite well_scoped_ctor_eq in Hws |- *.
    (* Direct list induction (the ws-only half of the old list/Forall   *)
    (* bridges, derived locally).                                       *)
    assert (Hmap : forall us, well_scoped_list ms us ->
              well_scoped_list ms (List.map (shift_tm a cutoff) us)).
    { intros us; induction us as [|u us' IHus]; intros Hus; [exact I|].
      destruct Hus as [Hu Hus'].
      split; [apply well_scoped_shift_tm; exact Hu | apply IHus; exact Hus']. }
    revert Hws. induction vs as [|u vs' IHvs]; intros Hws;
      cbn [List.app List.map] in Hws |- *.
    + destruct Hws as [Hfoc Hts].
      split; [apply IHE; exact Hfoc | apply Hmap; exact Hts].
    + destruct Hws as [Hu Hrest].
      split; [apply well_scoped_shift_tm; exact Hu | apply IHvs; exact Hrest].
  - destruct Hws as [Hs [Hy Hn]].
    split; [apply IHE; exact Hs|].
    split; [apply well_scoped_shift_tm; exact Hy
           |apply well_scoped_shift_tm; exact Hn].
  - apply IHE; exact Hws.
  - destruct Hws as [H1 H2].
    split; [apply IHE; exact H1 | apply well_scoped_shift_tm; exact H2].
  - destruct Hws as [H1 H2].
    split; [apply well_scoped_shift_tm; exact H1 | apply IHE; exact H2].
Qed.
