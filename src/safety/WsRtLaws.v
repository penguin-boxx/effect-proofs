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
(* Closed-subterm identity laws, preservation of [well_scoped]/       *)
(* [rt_closed] under shifts and substitutions, plug lemmas, and the   *)
(* H_Perform confinement facts.  Definitions live in WellScoped.v.    *)
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
    simpl in Hfv. rewrite free_tm_vars_go_eq_concat in Hfv.
    cbn [shift_tm]. rewrite shift_tm_go_eq_map.
    rewrite (IH c a cutoff Hfv Hle). reflexivity.
  - intros scrut tag nlt ar y n IHs IHy IHn c a cutoff Hfv Hle. simpl in Hfv |- *.
    apply app_eq_nil in Hfv as [Hs Hyn]. apply app_eq_nil in Hyn as [Hy Hn].
    rewrite (IHs c a cutoff Hs Hle).
    rewrite (IHy (c + ar) a (cutoff + ar) Hy); [|lia].
    rewrite (IHn c a cutoff Hn Hle). reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb c a cutoff Hfv Hle. simpl in Hfv |- *.
    rewrite free_tm_vars_go_ops_eq_concat in Hfv.
    apply app_eq_nil in Hfv as [Hop Hb].
    rewrite shift_tm_go_ops_eq_map.
    rewrite (IHops (c + 2) a (cutoff + 2) Hop); [|lia].
    rewrite (IHb (S c) a (S cutoff) Hb); [|lia]. reflexivity.
  - intros t op Ss A_ret arg IHt IHa c a cutoff Hfv Hle. simpl in Hfv |- *.
    apply app_eq_nil in Hfv as [Ht Ha].
    rewrite (IHt c a cutoff Ht Hle), (IHa c a cutoff Ha Hle). reflexivity.
  - intros E_tag m Ts T_R op_bodies IHops c a cutoff Hfv Hle. simpl in Hfv |- *.
    rewrite free_tm_vars_go_ops_eq_concat in Hfv.
    rewrite shift_tm_go_ops_eq_map.
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
    simpl in Hfv. rewrite free_tm_vars_go_eq_concat in Hfv.
    cbn [subst_tm]. rewrite subst_tm_go_eq_map.
    rewrite (IH c var r Hfv Hle). reflexivity.
  - intros scrut tag nlt ar y n IHs IHy IHn c var r Hfv Hle. simpl in Hfv |- *.
    apply app_eq_nil in Hfv as [Hs Hyn]. apply app_eq_nil in Hyn as [Hy Hn].
    rewrite (IHs c var _ Hs Hle).
    rewrite (IHy (c + ar) (var + ar) _ Hy); [|lia].
    rewrite (IHn c var _ Hn Hle). reflexivity.
  - intros E Ts T_B T_R op_bodies body IHops IHb c var r Hfv Hle. simpl in Hfv |- *.
    rewrite free_tm_vars_go_ops_eq_concat in Hfv.
    apply app_eq_nil in Hfv as [Hop Hb].
    rewrite subst_tm_go_ops_eq_map.
    rewrite (IHops (c + 2) (var + 2) _ Hop); [|lia].
    rewrite (IHb (S c) (S var) _ Hb); [|lia]. reflexivity.
  - intros t op Ss A_ret arg IHt IHa c var r Hfv Hle. simpl in Hfv |- *.
    apply app_eq_nil in Hfv as [Ht Ha].
    rewrite (IHt c var _ Ht Hle), (IHa c var _ Ha Hle). reflexivity.
  - intros E_tag m Ts T_R op_bodies IHops c var r Hfv Hle. simpl in Hfv |- *.
    rewrite free_tm_vars_go_ops_eq_concat in Hfv.
    rewrite subst_tm_go_ops_eq_map.
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
    cbn [shift_tm]. rewrite shift_tm_go_eq_map.
    rewrite well_scoped_ctor_eq. apply IH.
    rewrite well_scoped_ctor_eq in Hws. exact Hws.
  - intros scrut tag nlt ar y n IHs IHy IHn ms a cutoff [Hs [Hy Hn]]. cbn [shift_tm].
    split; [apply IHs; exact Hs | split; [apply IHy; exact Hy | apply IHn; exact Hn]].
  - intros E Ts T_B T_R op_bodies body IHops IHb ms a cutoff [Hop Hb]. cbn [shift_tm].
    rewrite shift_tm_go_ops_eq_map.
    split; [apply IHops; exact Hop | apply IHb; exact Hb].
  - intros t op Ss A_ret arg IHt IHa ms a cutoff [Ht Ha]. cbn [shift_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m Ts T_R op_bodies IHops ms a cutoff [Hin Hws]. cbn [shift_tm].
    rewrite shift_tm_go_ops_eq_map.
    split; [exact Hin | apply IHops; exact Hws].
  - intros m T_B T_R body IH ms a cutoff Hws. cbn [shift_tm]. apply IH; exact Hws.
  - intros ms a cutoff _. exact I.
  - intros u ts IHu IHts ms a cutoff [Hu Hts].
    split; [apply IHu|apply IHts]; assumption.
  - intros ms a cutoff _. exact I.
  - intros nb ob obs IHob IHobs ms a cutoff [Hob Hobs]. simpl.
    split; [apply IHob; exact Hob | apply IHobs; exact Hobs].
Qed.

Lemma well_scoped_shift_ty_in_tm : forall t ms a cutoff,
  well_scoped ms t -> well_scoped ms (shift_ty_in_tm a cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall ms a cutoff,
       well_scoped ms t -> well_scoped ms (shift_ty_in_tm a cutoff t))
    (fun ts => forall ms a cutoff,
       well_scoped_list ms ts ->
       well_scoped_list ms (List.map (shift_ty_in_tm a cutoff) ts))
    (fun obs => forall ms a cutoff,
       ops_well_scoped ms obs ->
       ops_well_scoped ms (List.map (fun p => (fst p, shift_ty_in_tm a (cutoff + fst p) (snd p))) obs))).
  - intros n ms a cutoff _. exact I.
  - intros t1 t2 IH1 IH2 ms a cutoff [H1 H2]. cbn [shift_ty_in_tm].
    split; [apply IH1|apply IH2]; assumption.
  - intros body T IH ms a cutoff Hws. cbn [shift_ty_in_tm]. apply IH; exact Hws.
  - intros t T IH ms a cutoff Hws. cbn [shift_ty_in_tm]. apply IH; exact Hws.
  - intros bound body IH ms a cutoff Hws. cbn [shift_ty_in_tm]. apply IH; exact Hws.
  - intros t l IH ms a cutoff Hws. cbn [shift_ty_in_tm]. apply IH; exact Hws.
  - intros body IH ms a cutoff Hws. cbn [shift_ty_in_tm]. apply IH; exact Hws.
  - intros K l lts Ts ts IH ms a cutoff Hws.
    cbn [shift_ty_in_tm]. rewrite shift_ty_in_tm_go_eq_map.
    rewrite well_scoped_ctor_eq. apply IH.
    rewrite well_scoped_ctor_eq in Hws. exact Hws.
  - intros scrut tag nlt ar y n IHs IHy IHn ms a cutoff [Hs [Hy Hn]]. cbn [shift_ty_in_tm].
    split; [apply IHs; exact Hs | split; [apply IHy; exact Hy | apply IHn; exact Hn]].
  - intros E Ts T_B T_R op_bodies body IHops IHb ms a cutoff [Hop Hb]. cbn [shift_ty_in_tm].
    rewrite shift_ty_in_tm_go_ops_eq_map.
    split; [apply IHops; exact Hop | apply IHb; exact Hb].
  - intros t op Ss A_ret arg IHt IHa ms a cutoff [Ht Ha]. cbn [shift_ty_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m Ts T_R op_bodies IHops ms a cutoff [Hin Hws]. cbn [shift_ty_in_tm].
    rewrite shift_ty_in_tm_go_ops_eq_map.
    split; [exact Hin | apply IHops; exact Hws].
  - intros m T_B T_R body IH ms a cutoff Hws. cbn [shift_ty_in_tm]. apply IH; exact Hws.
  - intros ms a cutoff _. exact I.
  - intros u ts IHu IHts ms a cutoff [Hu Hts].
    split; [apply IHu|apply IHts]; assumption.
  - intros ms a cutoff _. exact I.
  - intros nb ob obs IHob IHobs ms a cutoff [Hob Hobs]. simpl.
    split; [apply IHob; exact Hob | apply IHobs; exact Hobs].
Qed.

Lemma well_scoped_shift_lt_in_tm : forall t ms a cutoff,
  well_scoped ms t -> well_scoped ms (shift_lt_in_tm a cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall ms a cutoff,
       well_scoped ms t -> well_scoped ms (shift_lt_in_tm a cutoff t))
    (fun ts => forall ms a cutoff,
       well_scoped_list ms ts ->
       well_scoped_list ms (List.map (shift_lt_in_tm a cutoff) ts))
    (fun obs => forall ms a cutoff,
       ops_well_scoped ms obs ->
       ops_well_scoped ms (List.map (fun p => (fst p, shift_lt_in_tm a cutoff (snd p))) obs))).
  - intros n ms a cutoff _. exact I.
  - intros t1 t2 IH1 IH2 ms a cutoff [H1 H2]. cbn [shift_lt_in_tm].
    split; [apply IH1|apply IH2]; assumption.
  - intros body T IH ms a cutoff Hws. cbn [shift_lt_in_tm]. apply IH; exact Hws.
  - intros t T IH ms a cutoff Hws. cbn [shift_lt_in_tm]. apply IH; exact Hws.
  - intros bound body IH ms a cutoff Hws. cbn [shift_lt_in_tm]. apply IH; exact Hws.
  - intros t l IH ms a cutoff Hws. cbn [shift_lt_in_tm]. apply IH; exact Hws.
  - intros body IH ms a cutoff Hws. cbn [shift_lt_in_tm]. apply IH; exact Hws.
  - intros K l lts Ts ts IH ms a cutoff Hws.
    cbn [shift_lt_in_tm]. rewrite shift_lt_in_tm_go_eq_map.
    rewrite well_scoped_ctor_eq. apply IH.
    rewrite well_scoped_ctor_eq in Hws. exact Hws.
  - intros scrut tag nlt ar y n IHs IHy IHn ms a cutoff [Hs [Hy Hn]]. cbn [shift_lt_in_tm].
    split; [apply IHs; exact Hs | split; [apply IHy; exact Hy | apply IHn; exact Hn]].
  - intros E Ts T_B T_R op_bodies body IHops IHb ms a cutoff [Hop Hb]. cbn [shift_lt_in_tm].
    rewrite shift_lt_in_tm_go_ops_eq_map.
    split; [apply IHops; exact Hop | apply IHb; exact Hb].
  - intros t op Ss A_ret arg IHt IHa ms a cutoff [Ht Ha]. cbn [shift_lt_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m Ts T_R op_bodies IHops ms a cutoff [Hin Hws]. cbn [shift_lt_in_tm].
    rewrite shift_lt_in_tm_go_ops_eq_map.
    split; [exact Hin | apply IHops; exact Hws].
  - intros m T_B T_R body IH ms a cutoff Hws. cbn [shift_lt_in_tm]. apply IH; exact Hws.
  - intros ms a cutoff _. exact I.
  - intros u ts IHu IHts ms a cutoff [Hu Hts].
    split; [apply IHu|apply IHts]; assumption.
  - intros ms a cutoff _. exact I.
  - intros nb ob obs IHob IHobs ms a cutoff [Hob Hobs]. simpl.
    split; [apply IHob; exact Hob | apply IHobs; exact Hobs].
Qed.


Lemma rt_closed_shift_ty_in_tm : forall t a cutoff,
  rt_closed t -> rt_closed (shift_ty_in_tm a cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall a cutoff, rt_closed t -> rt_closed (shift_ty_in_tm a cutoff t))
    (fun ts => forall a cutoff,
       rt_closed_list ts -> rt_closed_list (List.map (shift_ty_in_tm a cutoff) ts))
    (fun obs => forall a cutoff,
       ops_rt_closed obs ->
       ops_rt_closed (List.map (fun p => (fst p, shift_ty_in_tm a (cutoff + fst p) (snd p))) obs))).
  - intros n a cutoff _. exact I.
  - intros t1 t2 IH1 IH2 a cutoff [H1 H2]. cbn [shift_ty_in_tm].
    split; [apply IH1|apply IH2]; assumption.
  - intros body T IH a cutoff H. cbn [shift_ty_in_tm]. apply IH; exact H.
  - intros t T IH a cutoff H. cbn [shift_ty_in_tm]. apply IH; exact H.
  - intros bound body IH a cutoff H. cbn [shift_ty_in_tm]. apply IH; exact H.
  - intros t l IH a cutoff H. cbn [shift_ty_in_tm]. apply IH; exact H.
  - intros body IH a cutoff H. cbn [shift_ty_in_tm]. apply IH; exact H.
  - intros K l lts Ts ts IH a cutoff H.
    cbn [shift_ty_in_tm]. rewrite shift_ty_in_tm_go_eq_map.
    rewrite rt_closed_ctor_eq. apply IH.
    rewrite rt_closed_ctor_eq in H. exact H.
  - intros scrut tag nlt ar y n IHs IHy IHn a cutoff [Hs [Hy Hn]]. cbn [shift_ty_in_tm].
    split; [apply IHs; exact Hs | split; [apply IHy; exact Hy | apply IHn; exact Hn]].
  - intros E Ts T_B T_R op_bodies body IHops IHb a cutoff [Hop Hb]. cbn [shift_ty_in_tm].
    rewrite shift_ty_in_tm_go_ops_eq_map.
    split; [apply IHops; exact Hop | apply IHb; exact Hb].
  - intros t op Ss A_ret arg IHt IHa a cutoff [Ht Ha]. cbn [shift_ty_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m Ts T_R op_bodies IHops a cutoff Hcap. cbn [shift_ty_in_tm].
    rewrite shift_ty_in_tm_go_ops_eq_map.
    apply ops_cap_closed_split in Hcap as [Hfv Hrt].
    apply ops_cap_closed_join.
    + clear IHops Hrt. induction Hfv as [|[nb ob] obs Hfv1 Hrest IH]; simpl; constructor.
      * simpl in Hfv1 |- *. rewrite free_tm_vars_shift_ty_in_tm_any. exact Hfv1.
      * exact IH.
    + apply IHops. exact Hrt.
  - intros m T_B T_R body IH a cutoff Hrt. cbn [shift_ty_in_tm]. apply IH; exact Hrt.
  - intros a cutoff _. exact I.
  - intros u ts IHu IHts a cutoff [Hu Hts].
    split; [apply IHu|apply IHts]; assumption.
  - intros a cutoff _. exact I.
  - intros nb ob obs IHob IHobs a cutoff [Hob Hobs]. simpl.
    split; [apply IHob; exact Hob | apply IHobs; exact Hobs].
Qed.

Lemma rt_closed_shift_lt_in_tm : forall t a cutoff,
  rt_closed t -> rt_closed (shift_lt_in_tm a cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall a cutoff, rt_closed t -> rt_closed (shift_lt_in_tm a cutoff t))
    (fun ts => forall a cutoff,
       rt_closed_list ts -> rt_closed_list (List.map (shift_lt_in_tm a cutoff) ts))
    (fun obs => forall a cutoff,
       ops_rt_closed obs ->
       ops_rt_closed (List.map (fun p => (fst p, shift_lt_in_tm a cutoff (snd p))) obs))).
  - intros n a cutoff _. exact I.
  - intros t1 t2 IH1 IH2 a cutoff [H1 H2]. cbn [shift_lt_in_tm].
    split; [apply IH1|apply IH2]; assumption.
  - intros body T IH a cutoff H. cbn [shift_lt_in_tm]. apply IH; exact H.
  - intros t T IH a cutoff H. cbn [shift_lt_in_tm]. apply IH; exact H.
  - intros bound body IH a cutoff H. cbn [shift_lt_in_tm]. apply IH; exact H.
  - intros t l IH a cutoff H. cbn [shift_lt_in_tm]. apply IH; exact H.
  - intros body IH a cutoff H. cbn [shift_lt_in_tm]. apply IH; exact H.
  - intros K l lts Ts ts IH a cutoff H.
    cbn [shift_lt_in_tm]. rewrite shift_lt_in_tm_go_eq_map.
    rewrite rt_closed_ctor_eq. apply IH.
    rewrite rt_closed_ctor_eq in H. exact H.
  - intros scrut tag nlt ar y n IHs IHy IHn a cutoff [Hs [Hy Hn]]. cbn [shift_lt_in_tm].
    split; [apply IHs; exact Hs | split; [apply IHy; exact Hy | apply IHn; exact Hn]].
  - intros E Ts T_B T_R op_bodies body IHops IHb a cutoff [Hop Hb]. cbn [shift_lt_in_tm].
    rewrite shift_lt_in_tm_go_ops_eq_map.
    split; [apply IHops; exact Hop | apply IHb; exact Hb].
  - intros t op Ss A_ret arg IHt IHa a cutoff [Ht Ha]. cbn [shift_lt_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m Ts T_R op_bodies IHops a cutoff Hcap. cbn [shift_lt_in_tm].
    rewrite shift_lt_in_tm_go_ops_eq_map.
    apply ops_cap_closed_split in Hcap as [Hfv Hrt].
    apply ops_cap_closed_join.
    + clear IHops Hrt. induction Hfv as [|[nb ob] obs Hfv1 Hrest IH]; simpl; constructor.
      * simpl in Hfv1 |- *. rewrite free_tm_vars_shift_lt_in_tm_any. exact Hfv1.
      * exact IH.
    + apply IHops. exact Hrt.
  - intros m T_B T_R body IH a cutoff Hrt. cbn [shift_lt_in_tm]. apply IH; exact Hrt.
  - intros a cutoff _. exact I.
  - intros u ts IHu IHts a cutoff [Hu Hts].
    split; [apply IHu|apply IHts]; assumption.
  - intros a cutoff _. exact I.
  - intros nb ob obs IHob IHobs a cutoff [Hob Hobs]. simpl.
    split; [apply IHob; exact Hob | apply IHobs; exact Hobs].
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

(* ==================================================================== *)
(* The crux substitution lemma.                                         *)
(*                                                                      *)
(* Substituting a CLOSED value preserves well_scoped at the same       *)
(* scope, with no marker side conditions on the value: substitution     *)
(* is the identity inside every scope-sensitive body (rt_closed), and   *)
(* everywhere else the ambient scope never changes (only handler_m /    *)
(* resume / cap change scope, and those have closed bodies).            *)
(* ==================================================================== *)

Lemma well_scoped_subst_tm : forall t var w ms,
  rt_closed t ->
  free_tm_vars 0 w = [] ->
  well_scoped ms w ->
  well_scoped ms t ->
  well_scoped ms (subst_tm var w t).
Proof.
  apply (term_list_ind
    (fun t => forall var w ms,
       rt_closed t -> free_tm_vars 0 w = [] -> well_scoped ms w ->
       well_scoped ms t -> well_scoped ms (subst_tm var w t))
    (fun ts => forall var w ms,
       rt_closed_list ts -> free_tm_vars 0 w = [] -> well_scoped ms w ->
       well_scoped_list ms ts ->
       well_scoped_list ms (List.map (subst_tm var w) ts))
    (fun obs => forall var w ms,
       ops_rt_closed obs -> free_tm_vars 0 w = [] -> well_scoped ms w ->
       ops_well_scoped ms obs ->
       ops_well_scoped ms (List.map (fun p => (fst p, subst_tm (var + 2) (shift_tm 2 0 w) (snd p))) obs))).
  - intros n var w ms _ Hfw Hww _. cbn [subst_tm].
    destruct (Nat.eqb n var); [exact Hww|].
    destruct (Nat.ltb var n); exact I.
  - intros t1 t2 IH1 IH2 var w ms [Hr1 Hr2] Hfw Hww [H1 H2]. cbn [subst_tm].
    split; [apply IH1|apply IH2]; assumption.
  - intros body T IH var w ms Hrt Hfw Hww Hws. cbn [subst_tm].
    rewrite (shift_tm_closed_id w 0 1 0 Hfw) by lia.
    apply IH; assumption.
  - intros t T IH var w ms Hrt Hfw Hww Hws. cbn [subst_tm].
    apply IH; assumption.
  - intros bound body IH var w ms Hrt Hfw Hww Hws. cbn [subst_tm].
    apply IH; try assumption.
    + rewrite free_tm_vars_shift_ty_in_tm_any. exact Hfw.
    + apply well_scoped_shift_ty_in_tm. exact Hww.
  - intros t l IH var w ms Hrt Hfw Hww Hws. cbn [subst_tm].
    apply IH; assumption.
  - intros body IH var w ms Hrt Hfw Hww Hws. cbn [subst_tm].
    apply IH; try assumption.
    + rewrite free_tm_vars_shift_lt_in_tm_any. exact Hfw.
    + apply well_scoped_shift_lt_in_tm. exact Hww.
  - intros K l lts Ts ts IH var w ms Hrt Hfw Hww Hws.
    cbn [subst_tm]. rewrite subst_tm_go_eq_map.
    rewrite rt_closed_ctor_eq in Hrt. rewrite well_scoped_ctor_eq in Hws.
    rewrite well_scoped_ctor_eq. apply IH; assumption.
  - intros scrut tag nlt ar y n IHs IHy IHn var w ms [Hrs [Hry Hrn]] Hfw Hww [Hs [Hy Hn]].
    cbn [subst_tm].
    assert (Hfw' : free_tm_vars 0 (shift_lt_in_tm nlt 0 w) = []).
    { rewrite free_tm_vars_shift_lt_in_tm_any. exact Hfw. }
    rewrite (shift_tm_closed_id (shift_lt_in_tm nlt 0 w) 0 ar 0 Hfw') by lia.
    split; [apply IHs; assumption|].
    split.
    + apply IHy; try assumption.
      apply well_scoped_shift_lt_in_tm. exact Hww.
    + apply IHn; assumption.
  - intros E Ts T_B T_R op_bodies body IHops IHb var w ms [Hrop Hrb] Hfw Hww [Hop Hb].
    cbn [subst_tm].
    rewrite (shift_tm_closed_id w 0 1 0 Hfw) by lia.
    rewrite subst_tm_go_ops_eq_map.
    split; [apply IHops; assumption | apply IHb; assumption].
  - intros t op Ss A_ret arg IHt IHa var w ms [Hrt Hra] Hfw Hww [Ht Ha]. cbn [subst_tm].
    split; [apply IHt; assumption | apply IHa; assumption].
  - intros E_tag m Ts T_R op_bodies IHops var w ms Hcap Hfw Hww [Hin Hws].
    cbn [subst_tm].
    rewrite subst_tm_go_ops_eq_map.
    apply ops_cap_closed_split in Hcap as [Hfv2 _].
    rewrite (subst_tm_ops_closed_id op_bodies var w Hfv2).
    split; [exact Hin | exact Hws].
  - intros m T_B T_R body IH var w ms Hrt Hfw Hww Hws. cbn [subst_tm].
    apply IH; try assumption.
    apply (well_scoped_mono w ms (m :: ms)); [apply se_top; apply se_refl | exact Hww].
  - intros var w ms _ _ _ _. exact I.
  - intros u ts IHu IHts var w ms [Hru Hrts] Hfw Hww [Hu Hts].
    split; [apply IHu|apply IHts]; assumption.
  - intros var w ms _ _ _ _. exact I.
  - intros nb ob obs IHob IHobs var w ms [Hrob Hrobs] Hfw Hww [Hob Hobs]. simpl.
    split.
    + apply IHob; try assumption.
      * rewrite (shift_tm_closed_id w 0 2 0 Hfw) by lia. exact Hfw.
      * rewrite (shift_tm_closed_id w 0 2 0 Hfw) by lia. exact Hww.
    + apply IHobs; assumption.
Qed.

(* rt_closed is preserved by substitution of a closed rt_closed value.  *)
Lemma rt_closed_subst_tm : forall t var w,
  rt_closed t -> free_tm_vars 0 w = [] -> rt_closed w ->
  rt_closed (subst_tm var w t).
Proof.
  apply (term_list_ind
    (fun t => forall var w,
       rt_closed t -> free_tm_vars 0 w = [] -> rt_closed w ->
       rt_closed (subst_tm var w t))
    (fun ts => forall var w,
       rt_closed_list ts -> free_tm_vars 0 w = [] -> rt_closed w ->
       rt_closed_list (List.map (subst_tm var w) ts))
    (fun obs => forall var w,
       ops_rt_closed obs -> free_tm_vars 0 w = [] -> rt_closed w ->
       ops_rt_closed (List.map (fun p => (fst p, subst_tm (var + 2) (shift_tm 2 0 w) (snd p))) obs))).
  - intros n var w _ Hfw Hrw. cbn [subst_tm].
    destruct (Nat.eqb n var); [exact Hrw|].
    destruct (Nat.ltb var n); exact I.
  - intros t1 t2 IH1 IH2 var w [H1 H2] Hfw Hrw. cbn [subst_tm].
    split; [apply IH1|apply IH2]; assumption.
  - intros body T IH var w Hrt Hfw Hrw. cbn [subst_tm].
    rewrite (shift_tm_closed_id w 0 1 0 Hfw) by lia.
    apply IH; assumption.
  - intros t T IH var w Hrt Hfw Hrw. cbn [subst_tm]. apply IH; assumption.
  - intros bound body IH var w Hrt Hfw Hrw. cbn [subst_tm].
    apply IH; try assumption.
    + rewrite free_tm_vars_shift_ty_in_tm_any. exact Hfw.
    + apply rt_closed_shift_ty_in_tm. exact Hrw.
  - intros t l IH var w Hrt Hfw Hrw. cbn [subst_tm]. apply IH; assumption.
  - intros body IH var w Hrt Hfw Hrw. cbn [subst_tm].
    apply IH; try assumption.
    + rewrite free_tm_vars_shift_lt_in_tm_any. exact Hfw.
    + apply rt_closed_shift_lt_in_tm. exact Hrw.
  - intros K l lts Ts ts IH var w Hrt Hfw Hrw.
    cbn [subst_tm]. rewrite subst_tm_go_eq_map.
    rewrite rt_closed_ctor_eq in Hrt.
    rewrite rt_closed_ctor_eq. apply IH; assumption.
  - intros scrut tag nlt ar y n IHs IHy IHn var w [Hrs [Hry Hrn]] Hfw Hrw.
    cbn [subst_tm].
    assert (Hfw' : free_tm_vars 0 (shift_lt_in_tm nlt 0 w) = []).
    { rewrite free_tm_vars_shift_lt_in_tm_any. exact Hfw. }
    rewrite (shift_tm_closed_id (shift_lt_in_tm nlt 0 w) 0 ar 0 Hfw') by lia.
    split; [apply IHs; assumption|].
    split.
    + apply IHy; try assumption.
      apply rt_closed_shift_lt_in_tm. exact Hrw.
    + apply IHn; assumption.
  - intros E Ts T_B T_R op_bodies body IHops IHb var w [Hrop Hrb] Hfw Hrw.
    cbn [subst_tm].
    rewrite (shift_tm_closed_id w 0 1 0 Hfw) by lia.
    rewrite subst_tm_go_ops_eq_map.
    split; [apply IHops; assumption | apply IHb; assumption].
  - intros t op Ss A_ret arg IHt IHa var w [Hrt Hra] Hfw Hrw. cbn [subst_tm].
    split; [apply IHt; assumption | apply IHa; assumption].
  - intros E_tag m Ts T_R op_bodies IHops var w Hcap Hfw Hrw. cbn [subst_tm].
    rewrite subst_tm_go_ops_eq_map.
    apply ops_cap_closed_split in Hcap as [Hfv2 Hrt].
    rewrite (subst_tm_ops_closed_id op_bodies var w Hfv2).
    apply ops_cap_closed_join; assumption.
  - intros m T_B T_R body IH var w Hrt Hfw Hrw. cbn [subst_tm].
    apply IH; assumption.
  - intros var w _ _ _. exact I.
  - intros u ts IHu IHts var w [Hru Hrts] Hfw Hrw.
    split; [apply IHu|apply IHts]; assumption.
  - intros var w _ _ _. exact I.
  - intros nb ob obs IHob IHobs var w [Hrob Hrobs] Hfw Hrw. simpl.
    split.
    + apply IHob; try assumption.
      * rewrite (shift_tm_closed_id w 0 2 0 Hfw) by lia. exact Hfw.
      * rewrite (shift_tm_closed_id w 0 2 0 Hfw) by lia. exact Hrw.
    + apply IHobs; assumption.
Qed.

(* Type substitution preserves well_scoped (it never touches markers). *)
Lemma well_scoped_subst_ty_in_tm : forall t var R ms,
  well_scoped ms t -> well_scoped ms (subst_ty_in_tm var R t).
Proof.
  apply (term_list_ind
    (fun t => forall var R ms, well_scoped ms t -> well_scoped ms (subst_ty_in_tm var R t))
    (fun ts => forall var R ms, well_scoped_list ms ts ->
       well_scoped_list ms (List.map (subst_ty_in_tm var R) ts))
    (fun obs => forall var R ms, ops_well_scoped ms obs ->
       ops_well_scoped ms (List.map (fun p =>
         (fst p, subst_ty_in_tm (var + fst p) (shift_ty (fst p) 0 R) (snd p))) obs))).
  - intros n var R ms Hws. exact I.
  - intros t1 t2 IH1 IH2 var R ms [H1 H2]. cbn [subst_ty_in_tm].
    split; [apply IH1|apply IH2]; assumption.
  - intros body T IH var R ms Hws. cbn [subst_ty_in_tm]. apply IH; exact Hws.
  - intros t T IH var R ms Hws. cbn [subst_ty_in_tm]. apply IH; exact Hws.
  - intros bound body IH var R ms Hws. cbn [subst_ty_in_tm]. apply IH; exact Hws.
  - intros t l IH var R ms Hws. cbn [subst_ty_in_tm]. apply IH; exact Hws.
  - intros body IH var R ms Hws. cbn [subst_ty_in_tm]. apply IH; exact Hws.
  - intros K l lts Ts ts IH var R ms Hws.
    replace (subst_ty_in_tm var R (term_ctor K l lts Ts ts))
      with (term_ctor K l lts (map_subst_ty var R Ts) (List.map (subst_ty_in_tm var R) ts))
      by (cbn [subst_ty_in_tm]; rewrite subst_ty_in_tm_go_eq_map; reflexivity).
    rewrite well_scoped_ctor_eq. apply IH. rewrite well_scoped_ctor_eq in Hws. exact Hws.
  - intros scrut tag nlt ar y n IHs IHy IHn var R ms [Hs [Hy Hn]]. cbn [subst_ty_in_tm].
    split; [apply IHs; exact Hs | split; [apply IHy; exact Hy | apply IHn; exact Hn]].
  - intros E Ts T_B T_R op_bodies body IHops IHb var R ms [Hop Hb]. cbn [subst_ty_in_tm].
    rewrite subst_ty_in_tm_go_ops_eq_map.
    split; [apply IHops; exact Hop | apply IHb; exact Hb].
  - intros t op Ss A_ret arg IHt IHa var R ms [Ht Ha]. cbn [subst_ty_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m Ts T_R op_bodies IHops var R ms [Hin Hws]. cbn [subst_ty_in_tm].
    rewrite subst_ty_in_tm_go_ops_eq_map.
    split; [exact Hin | apply IHops; exact Hws].
  - intros m T_B T_R body IH var R ms Hws. cbn [subst_ty_in_tm]. apply IH; exact Hws.
  - intros var R ms _. exact I.
  - intros u ts IHu IHts var R ms [Hu Hts]. split; [apply IHu|apply IHts]; assumption.
  - intros var R ms _. exact I.
  - intros nb ob obs IHob IHobs var R ms [Hob Hobs]. simpl.
    split; [apply IHob; exact Hob | apply IHobs; exact Hobs].
Qed.

(* Lifetime substitution preserves well_scoped. *)
Lemma well_scoped_subst_lt_in_tm : forall t var R ms,
  well_scoped ms t -> well_scoped ms (subst_lt_in_tm var R t).
Proof.
  apply (term_list_ind
    (fun t => forall var R ms, well_scoped ms t -> well_scoped ms (subst_lt_in_tm var R t))
    (fun ts => forall var R ms, well_scoped_list ms ts ->
       well_scoped_list ms (List.map (subst_lt_in_tm var R) ts))
    (fun obs => forall var R ms, ops_well_scoped ms obs ->
       ops_well_scoped ms (List.map (fun p => (fst p, subst_lt_in_tm var R (snd p))) obs))).
  - intros n var R ms Hws. exact I.
  - intros t1 t2 IH1 IH2 var R ms [H1 H2]. cbn [subst_lt_in_tm].
    split; [apply IH1|apply IH2]; assumption.
  - intros body T IH var R ms Hws. cbn [subst_lt_in_tm]. apply IH; exact Hws.
  - intros t T IH var R ms Hws. cbn [subst_lt_in_tm]. apply IH; exact Hws.
  - intros bound body IH var R ms Hws. cbn [subst_lt_in_tm]. apply IH; exact Hws.
  - intros t l IH var R ms Hws. cbn [subst_lt_in_tm]. apply IH; exact Hws.
  - intros body IH var R ms Hws. cbn [subst_lt_in_tm]. apply IH; exact Hws.
  - intros K l lts Ts ts IH var R ms Hws.
    cbn [subst_lt_in_tm]. rewrite subst_lt_in_tm_go_eq_map.
    rewrite well_scoped_ctor_eq. apply IH. rewrite well_scoped_ctor_eq in Hws. exact Hws.
  - intros scrut tag nlt ar y n IHs IHy IHn var R ms [Hs [Hy Hn]]. cbn [subst_lt_in_tm].
    split; [apply IHs; exact Hs | split; [apply IHy; exact Hy | apply IHn; exact Hn]].
  - intros E Ts T_B T_R op_bodies body IHops IHb var R ms [Hop Hb]. cbn [subst_lt_in_tm].
    rewrite subst_lt_in_tm_go_ops_eq_map.
    split; [apply IHops; exact Hop | apply IHb; exact Hb].
  - intros t op Ss A_ret arg IHt IHa var R ms [Ht Ha]. cbn [subst_lt_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m Ts T_R op_bodies IHops var R ms [Hin Hws]. cbn [subst_lt_in_tm].
    rewrite subst_lt_in_tm_go_ops_eq_map.
    split; [exact Hin | apply IHops; exact Hws].
  - intros m T_B T_R body IH var R ms Hws. cbn [subst_lt_in_tm]. apply IH; exact Hws.
  - intros var R ms _. exact I.
  - intros u ts IHu IHts var R ms [Hu Hts]. split; [apply IHu|apply IHts]; assumption.
  - intros var R ms _. exact I.
  - intros nb ob obs IHob IHobs var R ms [Hob Hobs]. simpl.
    split; [apply IHob; exact Hob | apply IHobs; exact Hobs].
Qed.

(* rt_closed is preserved by type/lifetime substitution. *)
Lemma rt_closed_subst_ty_in_tm : forall t var R,
  rt_closed t -> rt_closed (subst_ty_in_tm var R t).
Proof.
  apply (term_list_ind
    (fun t => forall var R, rt_closed t -> rt_closed (subst_ty_in_tm var R t))
    (fun ts => forall var R, rt_closed_list ts ->
       rt_closed_list (List.map (subst_ty_in_tm var R) ts))
    (fun obs => forall var R, ops_rt_closed obs ->
       ops_rt_closed (List.map (fun p =>
         (fst p, subst_ty_in_tm (var + fst p) (shift_ty (fst p) 0 R) (snd p))) obs))).
  - intros n var R H. exact I.
  - intros t1 t2 IH1 IH2 var R [H1 H2]. cbn [subst_ty_in_tm].
    split; [apply IH1|apply IH2]; assumption.
  - intros body T IH var R H. cbn [subst_ty_in_tm]. apply IH; exact H.
  - intros t T IH var R H. cbn [subst_ty_in_tm]. apply IH; exact H.
  - intros bound body IH var R H. cbn [subst_ty_in_tm]. apply IH; exact H.
  - intros t l IH var R H. cbn [subst_ty_in_tm]. apply IH; exact H.
  - intros body IH var R H. cbn [subst_ty_in_tm]. apply IH; exact H.
  - intros K l lts Ts ts IH var R H.
    replace (subst_ty_in_tm var R (term_ctor K l lts Ts ts))
      with (term_ctor K l lts (map_subst_ty var R Ts) (List.map (subst_ty_in_tm var R) ts))
      by (cbn [subst_ty_in_tm]; rewrite subst_ty_in_tm_go_eq_map; reflexivity).
    rewrite rt_closed_ctor_eq. apply IH. rewrite rt_closed_ctor_eq in H. exact H.
  - intros scrut tag nlt ar y n IHs IHy IHn var R [Hs [Hy Hn]]. cbn [subst_ty_in_tm].
    split; [apply IHs; exact Hs | split; [apply IHy; exact Hy | apply IHn; exact Hn]].
  - intros E Ts T_B T_R op_bodies body IHops IHb var R [Hop Hb]. cbn [subst_ty_in_tm].
    rewrite subst_ty_in_tm_go_ops_eq_map.
    split; [apply IHops; exact Hop | apply IHb; exact Hb].
  - intros t op Ss A_ret arg IHt IHa var R [Ht Ha]. cbn [subst_ty_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m Ts T_R op_bodies IHops var R Hcap. cbn [subst_ty_in_tm].
    rewrite subst_ty_in_tm_go_ops_eq_map.
    apply ops_cap_closed_split in Hcap as [Hfv Hrt].
    apply ops_cap_closed_join.
    + clear IHops Hrt. induction Hfv as [|[nb ob] obs Hfv1 Hrest IH]; simpl; constructor.
      * simpl in Hfv1 |- *. rewrite free_tm_vars_subst_ty_in_tm. exact Hfv1.
      * exact IH.
    + apply IHops. exact Hrt.
  - intros m T_B T_R body IH var R Hrt. cbn [subst_ty_in_tm]. apply IH; exact Hrt.
  - intros var R _. exact I.
  - intros u ts IHu IHts var R [Hu Hts]. split; [apply IHu|apply IHts]; assumption.
  - intros var R _. exact I.
  - intros nb ob obs IHob IHobs var R [Hob Hobs]. simpl.
    split; [apply IHob; exact Hob | apply IHobs; exact Hobs].
Qed.

Lemma rt_closed_subst_lt_in_tm : forall t var R,
  rt_closed t -> rt_closed (subst_lt_in_tm var R t).
Proof.
  apply (term_list_ind
    (fun t => forall var R, rt_closed t -> rt_closed (subst_lt_in_tm var R t))
    (fun ts => forall var R, rt_closed_list ts ->
       rt_closed_list (List.map (subst_lt_in_tm var R) ts))
    (fun obs => forall var R, ops_rt_closed obs ->
       ops_rt_closed (List.map (fun p => (fst p, subst_lt_in_tm var R (snd p))) obs))).
  - intros n var R H. exact I.
  - intros t1 t2 IH1 IH2 var R [H1 H2]. cbn [subst_lt_in_tm].
    split; [apply IH1|apply IH2]; assumption.
  - intros body T IH var R H. cbn [subst_lt_in_tm]. apply IH; exact H.
  - intros t T IH var R H. cbn [subst_lt_in_tm]. apply IH; exact H.
  - intros bound body IH var R H. cbn [subst_lt_in_tm]. apply IH; exact H.
  - intros t l IH var R H. cbn [subst_lt_in_tm]. apply IH; exact H.
  - intros body IH var R H. cbn [subst_lt_in_tm]. apply IH; exact H.
  - intros K l lts Ts ts IH var R H.
    cbn [subst_lt_in_tm]. rewrite subst_lt_in_tm_go_eq_map.
    rewrite rt_closed_ctor_eq. apply IH. rewrite rt_closed_ctor_eq in H. exact H.
  - intros scrut tag nlt ar y n IHs IHy IHn var R [Hs [Hy Hn]]. cbn [subst_lt_in_tm].
    split; [apply IHs; exact Hs | split; [apply IHy; exact Hy | apply IHn; exact Hn]].
  - intros E Ts T_B T_R op_bodies body IHops IHb var R [Hop Hb]. cbn [subst_lt_in_tm].
    rewrite subst_lt_in_tm_go_ops_eq_map.
    split; [apply IHops; exact Hop | apply IHb; exact Hb].
  - intros t op Ss A_ret arg IHt IHa var R [Ht Ha]. cbn [subst_lt_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m Ts T_R op_bodies IHops var R Hcap. cbn [subst_lt_in_tm].
    rewrite subst_lt_in_tm_go_ops_eq_map.
    apply ops_cap_closed_split in Hcap as [Hfv Hrt].
    apply ops_cap_closed_join.
    + clear IHops Hrt. induction Hfv as [|[nb ob] obs Hfv1 Hrest IH]; simpl; constructor.
      * simpl in Hfv1 |- *. rewrite free_tm_vars_subst_lt_in_tm. exact Hfv1.
      * exact IH.
    + apply IHops. exact Hrt.
  - intros m T_B T_R body IH var R Hrt. cbn [subst_lt_in_tm]. apply IH; exact Hrt.
  - intros var R _. exact I.
  - intros u ts IHu IHts var R [Hu Hts]. split; [apply IHu|apply IHts]; assumption.
  - intros var R _. exact I.
  - intros nb ob obs IHob IHobs var R [Hob Hobs]. simpl.
    split; [apply IHob; exact Hob | apply IHobs; exact Hobs].
Qed.

(* Iterated substitution of closed rt_closed values. *)
Lemma well_scoped_subst_list_tm : forall vs t ms,
  Forall (fun v => free_tm_vars 0 v = []) vs ->
  Forall rt_closed vs ->
  Forall (well_scoped ms) vs ->
  rt_closed t ->
  well_scoped ms t ->
  well_scoped ms (subst_list_tm vs t).
Proof.
  induction vs as [|v rest IH]; intros t ms Hfv Hrc Hws Hrt Hwt.
  - exact Hwt.
  - inversion Hfv as [|? ? Hfv1 Hfvr]; subst.
    inversion Hrc as [|? ? Hrc1 Hrcr]; subst.
    inversion Hws as [|? ? Hws1 Hwsr]; subst.
    cbn [subst_list_tm].
    rewrite (shift_tm_closed_id v 0 (List.length rest) 0 Hfv1) by lia.
    apply IH; try assumption.
    + apply rt_closed_subst_tm; assumption.
    + apply well_scoped_subst_tm; assumption.
Qed.

Lemma rt_closed_subst_list_tm : forall vs t,
  Forall (fun v => free_tm_vars 0 v = []) vs ->
  Forall rt_closed vs ->
  rt_closed t ->
  rt_closed (subst_list_tm vs t).
Proof.
  induction vs as [|v rest IH]; intros t Hfv Hrc Hrt.
  - exact Hrt.
  - inversion Hfv as [|? ? Hfv1 Hfvr]; subst.
    inversion Hrc as [|? ? Hrc1 Hrcr]; subst.
    cbn [subst_list_tm].
    rewrite (shift_tm_closed_id v 0 (List.length rest) 0 Hfv1) by lia.
    apply IH; try assumption.
    apply rt_closed_subst_tm; assumption.
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
  - rewrite free_tm_vars_go_eq_concat in Hfv.
    rewrite map_app in Hfv. rewrite concat_app in Hfv.
    apply app_eq_nil in Hfv as [_ Hfv]. simpl in Hfv.
    apply app_eq_nil in Hfv as [H _]. apply IHE; exact H.
  - apply app_eq_nil in Hfv as [H _]. apply IHE; exact H.
  - apply IHE; exact Hfv.
  - apply app_eq_nil in Hfv as [H _]. apply IHE; exact H.
  - apply app_eq_nil in Hfv as [_ H]. apply IHE; exact H.
Qed.

(* Structural plug-replace for well_scoped: frames thread the scope,   *)
(* the EC_handler_m frame prepends its marker, and the replacement      *)
(* callback fires at whatever scope the hole sits at.                   *)
Lemma well_scoped_plug_replace : forall E r r' ms,
  well_scoped ms (plug E r) ->
  (forall ms', well_scoped ms' r -> well_scoped ms' r') ->
  well_scoped ms (plug E r').
Proof.
  induction E as
    [ | E1 IHE ta | ta E1 IHE | E1 IHE Ty | E1 IHE lt
    | tag dl lts Tys vs E1 IHE ts | E1 IHE K nlt ar yes no
    | mk TB TR E1 IHE | E1 IHE opx Ss An ar2 | rcv opx Ss An E1 IHE ];
    intros r r' ms Hws Hrep; cbn [plug] in Hws |- *.
  - apply Hrep; exact Hws.
  - destruct Hws as [H1 H2]. split; [eapply IHE; eauto | exact H2].
  - destruct Hws as [H1 H2]. split; [exact H1 | eapply IHE; eauto].
  - eapply IHE; eauto.
  - eapply IHE; eauto.
  - rewrite well_scoped_ctor_eq in Hws |- *.
    revert Hws. induction vs as [|a vs' IHvs]; intros Hws; cbn [List.app] in Hws |- *.
    + destruct Hws as [Hfoc Hrest]. split; [eapply IHE; eauto | exact Hrest].
    + destruct Hws as [Ha Hrest]. split; [exact Ha | apply IHvs; exact Hrest].
  - destruct Hws as [Hs [Hy Hn]]. repeat split; [eapply IHE; eauto | exact Hy | exact Hn].
  - eapply IHE; eauto.
  - destruct Hws as [H1 H2]. split; [eapply IHE; eauto | exact H2].
  - destruct Hws as [H1 H2]. split; [exact H1 | eapply IHE; eauto].
Qed.

Lemma rt_closed_plug_replace : forall E r r',
  rt_closed (plug E r) ->
  (rt_closed r -> rt_closed r') ->
  rt_closed (plug E r').
Proof.
  induction E as
    [ | E1 IHE ta | ta E1 IHE | E1 IHE Ty | E1 IHE lt
    | tag dl lts Tys vs E1 IHE ts | E1 IHE K nlt ar yes no
    | mk TB TR E1 IHE | E1 IHE opx Ss An ar2 | rcv opx Ss An E1 IHE ];
    intros r r' Hrt Hrep; cbn [plug] in Hrt |- *.
  - apply Hrep; exact Hrt.
  - destruct Hrt as [H1 H2]. split; [eapply IHE; eauto | exact H2].
  - destruct Hrt as [H1 H2]. split; [exact H1 | eapply IHE; eauto].
  - eapply IHE; eauto.
  - eapply IHE; eauto.
  - rewrite rt_closed_ctor_eq in Hrt |- *.
    revert Hrt. induction vs as [|a vs' IHvs]; intros Hrt; cbn [List.app] in Hrt |- *.
    + destruct Hrt as [Hfoc Hrest]. split; [eapply IHE; eauto | exact Hrest].
    + destruct Hrt as [Ha Hrest]. split; [exact Ha | apply IHvs; exact Hrest].
  - destruct Hrt as [Hs [Hy Hn]]. repeat split; [eapply IHE; eauto | exact Hy | exact Hn].
  - eapply IHE; eauto.
  - destruct Hrt as [H1 H2]. split; [eapply IHE; eauto | exact H2].
  - destruct Hrt as [H1 H2]. split; [exact H1 | eapply IHE; eauto].
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

Lemma well_scoped_list_Forall : forall ms ts,
  well_scoped_list ms ts -> Forall (well_scoped ms) ts.
Proof.
  intros ms ts H. induction ts as [|u ts IH]; [constructor|].
  destruct H as [Hu Hts]. constructor; [exact Hu | apply IH; exact Hts].
Qed.

Lemma Forall_well_scoped_list : forall ms ts,
  Forall (well_scoped ms) ts -> well_scoped_list ms ts.
Proof.
  intros ms ts H. induction H as [|u ts Hu Hts IH]; [exact I|].
  split; [exact Hu | exact IH].
Qed.

Lemma rt_closed_list_Forall : forall ts,
  rt_closed_list ts -> Forall rt_closed ts.
Proof.
  intros ts H. induction ts as [|u ts IH]; [constructor|].
  destruct H as [Hu Hts]. constructor; [exact Hu | apply IH; exact Hts].
Qed.

Lemma Forall_rt_closed_list : forall ts,
  Forall rt_closed ts -> rt_closed_list ts.
Proof.
  intros ts H. induction H as [|u ts Hu Hts IH]; [exact I|].
  split; [exact Hu | exact IH].
Qed.

Lemma well_scoped_subst_list_ty_in_tm : forall Ss t ms,
  well_scoped ms t -> well_scoped ms (subst_list_ty_in_tm Ss t).
Proof.
  induction Ss as [|S0 Ss IH]; intros t ms H; simpl; [exact H|].
  apply IH. apply well_scoped_subst_ty_in_tm. exact H.
Qed.

Lemma well_scoped_subst_list_lt_in_tm : forall lts t ms,
  well_scoped ms t -> well_scoped ms (subst_list_lt_in_tm lts t).
Proof.
  induction lts as [|l lts IH]; intros t ms H; simpl; [exact H|].
  apply IH. apply well_scoped_subst_lt_in_tm. exact H.
Qed.

Lemma rt_closed_subst_list_ty_in_tm : forall Ss t,
  rt_closed t -> rt_closed (subst_list_ty_in_tm Ss t).
Proof.
  induction Ss as [|S0 Ss IH]; intros t H; simpl; [exact H|].
  apply IH. apply rt_closed_subst_ty_in_tm. exact H.
Qed.

Lemma rt_closed_subst_list_lt_in_tm : forall lts t,
  rt_closed t -> rt_closed (subst_list_lt_in_tm lts t).
Proof.
  induction lts as [|l lts IH]; intros t H; simpl; [exact H|].
  apply IH. apply rt_closed_subst_lt_in_tm. exact H.
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
  - simpl in Hfv. rewrite free_tm_vars_go_eq_concat in Hfv.
    rewrite map_app in Hfv. rewrite concat_app in Hfv.
    apply app_eq_nil in Hfv as [Hvs Hfoc_ts]. simpl in Hfoc_ts.
    apply app_eq_nil in Hfoc_ts as [Hfoc Hts].
    apply Forall_of_concat_map_nil in Hvs.
    apply Forall_of_concat_map_nil in Hts.
    rewrite rt_closed_ctor_eq in Hrt.
    apply rt_closed_list_Forall in Hrt.
    apply Forall_app in Hrt as [Rvs Rfoc_ts].
    inversion Rfoc_ts as [|? ? Rfoc Rts]; subst.
    destruct (IHE r Hfoc Rfoc) as [IHfv IHrt].
    rewrite (map_shift_tm_closed_id vs 1 0 Hvs).
    rewrite (map_shift_tm_closed_id ts 1 0 Hts).
    split.
    + simpl. rewrite free_tm_vars_go_eq_concat.
      rewrite map_app. rewrite concat_app. simpl.
      rewrite (concat_map_fv_closed_cutoff vs 1 Hvs).
      rewrite IHfv.
      rewrite (concat_map_fv_closed_cutoff ts 1 Hts). reflexivity.
    + rewrite rt_closed_ctor_eq. apply Forall_rt_closed_list.
      apply Forall_app. split; [exact Rvs|].
      constructor; [exact IHrt | exact Rts].
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
    apply well_scoped_list_Forall in Hws.
    apply Forall_app in Hws as [Wvs Wfoc_ts].
    inversion Wfoc_ts as [|? ? Wfoc Wts]; subst.
    apply Forall_well_scoped_list.
    apply Forall_app. split.
    + apply Forall_map. eapply Forall_impl; [|exact Wvs].
      intros v Hv. apply well_scoped_shift_tm. exact Hv.
    + constructor; [apply IHE; exact Wfoc|].
      apply Forall_map. eapply Forall_impl; [|exact Wts].
      intros v Hv. apply well_scoped_shift_tm. exact Hv.
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
