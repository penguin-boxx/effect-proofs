Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.

(* ================================================================== *)
(* Runtime marker invariants, part 1: marker provenance.              *)
(*                                                                    *)
(*   well_scoped ms t  — each cap's marker is in the ambient scope    *)
(*                       [ms], and its op-body is well-scoped at      *)
(*                       [scope_below m ms] — the scope OUTSIDE its   *)
(*                       own delimiter, exactly where the H_Perform   *)
(*                       reduct lands.  Monotone along [scope_ext]    *)
(*                       (scope insertions).                          *)
(*   rt_closed t       — cap op-bodies are term-closed.               *)
(*   ws_rt             — the two bundled.                             *)
(*                                                                    *)
(* All invariants hold vacuously on source terms                      *)
(* ([has_rt_marker t = false]).  The traversal laws live in WsRtLaws.v   *)
(* and are stated over the fused [ws_rt] (one induction per traversal *)
(* covers both conjuncts); the annotation invariants in               *)
(* MarkerAnnots.v.                                                    *)
(* ================================================================== *)

(* Closed-type identity laws, shared with MarkerAnnots.v.               *)

Lemma shift_ty_closed0_id : forall T amount cutoff,
  ty_ty_closed 0 T -> shift_ty amount cutoff T = T.
Proof.
  intros T amount cutoff Hclosed.
  apply shift_ty_in_ty_closed with (c := cutoff).
  eapply ty_ty_closed_mono; [apply Nat.le_0_l | exact Hclosed].
Qed.

Lemma shift_lt_in_ty_closed0_id : forall T amount cutoff,
  ty_lt_closed 0 T -> shift_lt_in_ty amount cutoff T = T.
Proof.
  intros T amount cutoff Hclosed.
  apply shift_lt_in_type_closed with (c := cutoff).
  eapply ty_lt_closed_mono; [apply Nat.le_0_l | exact Hclosed].
Qed.

Lemma subst_ty_closed0_id : forall T var R,
  ty_ty_closed 0 T -> subst_ty var R T = T.
Proof.
  intros T var R Hclosed.
  apply subst_ty_ty_closed_id with (c := 0); [exact Hclosed | lia].
Qed.

Lemma subst_lt_in_ty_closed0_id : forall T var R,
  ty_lt_closed 0 T -> subst_lt_in_ty var R T = T.
Proof.
  intros T var R Hclosed.
  apply subst_lt_in_type_closed with (c := var).
  eapply ty_lt_closed_mono; [apply Nat.le_0_l | exact Hclosed].
Qed.


(* has_rt_marker on a constructor reduces to has_rt_marker_list on its       *)
(* argument list (the in-body fixpoint equals the named list version).  *)
Lemma has_rt_marker_ctor_eq : forall K l lts Ts ts,
  has_rt_marker (term_ctor K l lts Ts ts) = has_rt_marker_list ts.
Proof.
  intros K l lts Ts ts. simpl.
  induction ts as [|u rest IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.


(* ================================================================== *)
(* CONFINEMENT BUILDING BLOCKS for handler-elimination (H_Perform).   *)
(* ================================================================== *)

(* The scope that was ambient when [m]'s handler was entered: the part  *)
(* of [ms] strictly after the first (innermost) occurrence of [m] —     *)
(* matching [pure_ectx_m]'s innermost-delimiter targeting.  Used by the *)
(* cap clause of [well_scoped] below.                                   *)
Fixpoint scope_below (m : marker) (ms : list marker) : list marker :=
  match ms with
  | []         => []
  | m' :: rest => if Nat.eqb m' m then rest else scope_below m rest
  end.

Lemma scope_below_cons_eq : forall m ms, scope_below m (m :: ms) = ms.
Proof. intros m ms. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma scope_below_cons_neq : forall m m' ms, m' <> m ->
  scope_below m (m' :: ms) = scope_below m ms.
Proof.
  intros m m' ms Hne. simpl.
  destruct (Nat.eqb_spec m' m) as [Heq|]; [contradiction|reflexivity].
Qed.

(* ==================================================================== *)
(* Scope extension.                                                     *)
(*                                                                      *)
(* [scope_ext s ms] relates an ambient marker scope [s] to any scope    *)
(* [ms] obtained from it by inserting extra markers above and/or        *)
(* between the markers of [s], preserving their order.  Well-           *)
(* scopedness is monotone along this relation: a value moved            *)
(* under a newly installed delimiter (applying a reified resumption,    *)
(* now ordinary H_Beta) or under binders                                *)
(* during substitution only ever sees scope_ext-extensions of the       *)
(* scope it was checked at.                                             *)
(* ==================================================================== *)

Inductive scope_ext : list marker -> list marker -> Prop :=
  | se_refl : forall s, scope_ext s s
  | se_top  : forall s ms m, scope_ext s ms -> scope_ext s (m :: ms)
  | se_cons : forall s ms m, scope_ext s ms -> scope_ext (m :: s) (m :: ms).

Lemma scope_ext_incl : forall s ms, scope_ext s ms -> incl s ms.
Proof.
  intros s ms H. induction H as [s' | s' ms' m' H IH | s' ms' m' H IH].
  - apply incl_refl.
  - apply incl_tl. exact IH.
  - intros x [Hx | Hx]; [left; exact Hx | right; apply IH; exact Hx].
Qed.

(* The suffix below any marker is a scope_ext-shrinking of the scope. *)
Lemma scope_below_scope_ext : forall k s, scope_ext (scope_below k s) s.
Proof.
  intros k. induction s as [|m rest IH]; simpl.
  - apply se_refl.
  - destruct (Nat.eqb m k).
    + apply se_top. apply se_refl.
    + apply se_top. exact IH.
Qed.


(* scope_ext absorbs a scope_below on its source. *)
Lemma scope_ext_scope_below_l : forall s ms k,
  scope_ext s ms -> scope_ext (scope_below k s) ms.
Proof.
  intros s ms k H. induction H as [s' | s' ms' m' H IH | s' ms' m' H IH].
  - apply scope_below_scope_ext.
  - apply se_top. exact IH.
  - simpl. destruct (Nat.eqb m' k).
    + apply se_top. exact H.
    + apply se_top. exact IH.
Qed.

(* Scope extension transports through scope_below: inserting markers    *)
(* above/between can only move the cut-point up, never expose a         *)
(* smaller suffix.                                                      *)
Lemma scope_ext_scope_below : forall s ms k,
  scope_ext s ms -> scope_ext (scope_below k s) (scope_below k ms).
Proof.
  intros s ms k H. induction H as [s' | s' ms' m' H IH | s' ms' m' H IH].
  - apply se_refl.
  - simpl. destruct (Nat.eqb m' k).
    + apply scope_ext_scope_below_l. exact H.
    + exact IH.
  - simpl. destruct (Nat.eqb m' k).
    + exact H.
    + exact IH.
Qed.

(* ==================================================================== *)
(* The marker well-scopedness invariant.                                *)
(*                                                                      *)
(* [well_scoped ms t] records marker provenance without freshness:     *)
(*  - at a cap, its marker is in scope AND its op-body is well-scoped   *)
(*    at the scope that was ambient OUTSIDE the cap's own delimiter     *)
(*    (= the suffix of [ms] below the innermost occurrence of the       *)
(*    cap's marker).  This is exactly what the H_Perform reduct needs:  *)
(*    the op-body lands outside the consumed delimiter.                 *)
(*  - at a delimiter/resumption, the bound marker is pushed; NO         *)
(*    freshness is required (marker shadowing is operationally fine:    *)
(*    [pure_ectx_m] and [scope_below] both target the innermost         *)
(*    occurrence).                                                      *)
(* Unlike v1, this predicate is monotone along [scope_ext] and hence    *)
(* preserved by reduction (see step_preserves_ws_rt).                  *)
(* ==================================================================== *)

Fixpoint well_scoped (ms : list marker) (t : term) : Prop :=
  let fix well_scoped_list (ts : list term) : Prop :=
    match ts with
    | [] => True
    | u :: rest => well_scoped ms u /\ well_scoped_list rest
    end
  in
  match t with
  | term_var _ => True
  | term_app t1 t2 => well_scoped ms t1 /\ well_scoped ms t2
  | term_lam body _ => well_scoped ms body
  | term_ty_app t1 _ => well_scoped ms t1
  | term_ty_lam _ body => well_scoped ms body
  | term_lt_app t1 _ => well_scoped ms t1
  | term_lt_lam body => well_scoped ms body
  | term_ctor _ _ _ _ ts => well_scoped_list ts
  | term_match scrut _ _ _ yes_body no_body =>
      well_scoped ms scrut /\ well_scoped ms yes_body /\ well_scoped ms no_body
  | term_handle _ _ _ _ op_bodies body =>
      (fix go_ops (obs : list (nat * term)) : Prop :=
         match obs with
         | [] => True
         | (_, ob) :: rest => well_scoped ms ob /\ go_ops rest
         end) op_bodies /\ well_scoped ms body
  | term_perform recv _ _ _ arg => well_scoped ms recv /\ well_scoped ms arg
  | term_cap _ m _ _ op_bodies =>
      In m ms /\
      (fix go_ops (obs : list (nat * term)) : Prop :=
         match obs with
         | [] => True
         | (_, ob) :: rest => well_scoped (scope_below m ms) ob /\ go_ops rest
         end) op_bodies
  | term_handler_m m _ _ body => well_scoped (m :: ms) body
  end.

(* Wrapper alpha-equal to the inline ops fixes above (convertibility). *)
Definition ops_well_scoped (ms : list marker) (obs : list (nat * term)) : Prop :=
  (fix go_ops (obs : list (nat * term)) : Prop :=
     match obs with
     | [] => True
     | (_, ob) :: rest => well_scoped ms ob /\ go_ops rest
     end) obs.

Fixpoint well_scoped_list (ms : list marker) (ts : list term) : Prop :=
  match ts with
  | [] => True
  | u :: rest => well_scoped ms u /\ well_scoped_list ms rest
  end.

Lemma well_scoped_ctor_eq : forall ms K l lts Ts ts,
  well_scoped ms (term_ctor K l lts Ts ts) = well_scoped_list ms ts.
Proof.
  intros ms K l lts Ts ts. induction ts as [|u rest IH].
  - reflexivity.
  - change (well_scoped ms (term_ctor K l lts Ts (u :: rest)))
      with (well_scoped ms u /\ well_scoped ms (term_ctor K l lts Ts rest)).
    rewrite IH. reflexivity.
Qed.

(* ==================================================================== *)
(* Term-closedness of runtime marker constructs.                        *)
(*                                                                      *)
(* Caps, delimiters, and resumptions are minted at evaluation (spine)   *)
(* positions of a closed program, so their op-bodies never reference    *)
(* enclosing term binders — and substitution into a closed subterm is   *)
(* the identity, so they stay closed.  [rt_closed] records this for     *)
(* CAPS ONLY: the cap clause of well_scoped is the one place the       *)
(* scope SHRINKS (scope_below), which monotonicity cannot transport     *)
(* a substituted value across; closedness makes substitution vacuous    *)
(* there.  handler_m/resume bodies need no such condition — their       *)
(* clauses only EXTEND the scope, and [well_scoped_mono] transports    *)
(* the value.  (Indeed resume bodies are NOT term-closed: the reified   *)
(* continuation body contains the resumption hole [term_var 0], also    *)
(* inside re-captured handler_m frames.)                                *)
(* ==================================================================== *)

Fixpoint rt_closed (t : term) : Prop :=
  let fix rt_closed_list (ts : list term) : Prop :=
    match ts with
    | [] => True
    | u :: rest => rt_closed u /\ rt_closed_list rest
    end
  in
  match t with
  | term_var _ => True
  | term_app t1 t2 => rt_closed t1 /\ rt_closed t2
  | term_lam body _ => rt_closed body
  | term_ty_app t1 _ => rt_closed t1
  | term_ty_lam _ body => rt_closed body
  | term_lt_app t1 _ => rt_closed t1
  | term_lt_lam body => rt_closed body
  | term_ctor _ _ _ _ ts => rt_closed_list ts
  | term_match scrut _ _ _ yes_body no_body =>
      rt_closed scrut /\ rt_closed yes_body /\ rt_closed no_body
  | term_handle _ _ _ _ op_bodies body =>
      (fix go_ops (obs : list (nat * term)) : Prop :=
         match obs with
         | [] => True
         | (_, ob) :: rest => rt_closed ob /\ go_ops rest
         end) op_bodies /\ rt_closed body
  | term_perform recv _ _ _ arg => rt_closed recv /\ rt_closed arg
  | term_cap _ _ _ _ op_bodies =>
      (fix go_ops (obs : list (nat * term)) : Prop :=
         match obs with
         | [] => True
         | (_, ob) :: rest => (free_tm_vars 2 ob = [] /\ rt_closed ob) /\ go_ops rest
         end) op_bodies
  | term_handler_m _ _ _ body => rt_closed body
  end.

Definition ops_rt_closed (obs : list (nat * term)) : Prop :=
  (fix go_ops (obs : list (nat * term)) : Prop :=
     match obs with
     | [] => True
     | (_, ob) :: rest => rt_closed ob /\ go_ops rest
     end) obs.

Definition ops_cap_closed (obs : list (nat * term)) : Prop :=
  (fix go_ops (obs : list (nat * term)) : Prop :=
     match obs with
     | [] => True
     | (_, ob) :: rest => (free_tm_vars 2 ob = [] /\ rt_closed ob) /\ go_ops rest
     end) obs.

Lemma ops_cap_closed_split : forall obs,
  ops_cap_closed obs ->
  Forall (fun p => free_tm_vars 2 (snd p) = []) obs /\ ops_rt_closed obs.
Proof.
  intros obs H. induction obs as [|[nb ob] obs IH]; simpl.
  - split; [constructor | exact I].
  - destruct H as [[Hfv Hrt] Hrest]. destruct (IH Hrest) as [Hf Hr].
    split; [constructor; [exact Hfv | exact Hf] | split; [exact Hrt | exact Hr]].
Qed.

Lemma ops_cap_closed_join : forall obs,
  Forall (fun p => free_tm_vars 2 (snd p) = []) obs ->
  ops_rt_closed obs ->
  ops_cap_closed obs.
Proof.
  intros obs Hf Hr. induction obs as [|[nb ob] obs IH]; simpl; [exact I|].
  inversion Hf as [|? ? Hfv Hfrest]; subst.
  destruct Hr as [Hrt Hrrest].
  split; [split; [exact Hfv | exact Hrt] | apply IH; assumption].
Qed.

Lemma ops_well_scoped_nth : forall ms (obs : list (nat * term)) op nb ob,
  ops_well_scoped ms obs -> nth_error obs op = Some (nb, ob) -> well_scoped ms ob.
Proof.
  intros ms obs; induction obs as [|[nb0 ob0] obs IH]; intros op nb ob Hws Hnth.
  - destruct op; discriminate.
  - destruct Hws as [H1 Hrest]. destruct op as [|op'].
    + injection Hnth; intros; subst. exact H1.
    + eapply IH; eauto.
Qed.

Lemma ops_cap_closed_nth : forall (obs : list (nat * term)) op nb ob,
  ops_cap_closed obs -> nth_error obs op = Some (nb, ob) ->
  free_tm_vars 2 ob = [] /\ rt_closed ob.
Proof.
  intros obs; induction obs as [|[nb0 ob0] obs IH]; intros op nb ob Hcc Hnth.
  - destruct op; discriminate.
  - destruct Hcc as [H1 Hrest]. destruct op as [|op'].
    + injection Hnth; intros; subst. exact H1.
    + eapply IH; eauto.
Qed.

Fixpoint rt_closed_list (ts : list term) : Prop :=
  match ts with
  | [] => True
  | u :: rest => rt_closed u /\ rt_closed_list rest
  end.

Lemma rt_closed_ctor_eq : forall K l lts Ts ts,
  rt_closed (term_ctor K l lts Ts ts) = rt_closed_list ts.
Proof.
  intros K l lts Ts ts. induction ts as [|u rest IH].
  - reflexivity.
  - change (rt_closed (term_ctor K l lts Ts (u :: rest)))
      with (rt_closed u /\ rt_closed (term_ctor K l lts Ts rest)).
    rewrite IH. reflexivity.
Qed.


(* The fused runtime invariant: marker provenance ([well_scoped])      *)
(* and term-closedness of cap op-bodies ([rt_closed]).  The bundle,    *)
(* the step-preservation layer, and the traversal laws (WsRtLaws.v)    *)
(* all work over this fused form: each traversal is proved ONCE, with  *)
(* the conjunction as the induction motive.                            *)
Definition ws_rt (ms : list marker) (t : term) : Prop :=
  well_scoped ms t /\ rt_closed t.

(* ws_rt holds vacuously on terms with no runtime capability, at any   *)
(* ambient scope.                                                      *)
Lemma ws_rt_no_rt_marker : forall t ms, has_rt_marker t = false -> ws_rt ms t.
Proof.
  unfold ws_rt.
  apply (term_list_ind
    (fun t => forall ms, has_rt_marker t = false ->
       well_scoped ms t /\ rt_closed t)
    (fun ts => forall ms, has_rt_marker_list ts = false ->
       well_scoped_list ms ts /\ rt_closed_list ts)
    (fun obs => forall ms,
       existsb (fun p => has_rt_marker (snd p)) obs = false ->
       ops_well_scoped ms obs /\ ops_rt_closed obs)).
  - intros n ms H. split; exact I.
  - intros t1 t2 IH1 IH2 ms H. simpl in H. apply Bool.orb_false_iff in H as [H1 H2].
    destruct (IH1 ms H1) as [W1 R1]. destruct (IH2 ms H2) as [W2 R2].
    split; split; assumption.
  - intros body T IH ms H. simpl in H. exact (IH ms H).
  - intros t T IH ms H. simpl in H. exact (IH ms H).
  - intros bound body IH ms H. simpl in H. exact (IH ms H).
  - intros t l IH ms H. simpl in H. exact (IH ms H).
  - intros body IH ms H. simpl in H. exact (IH ms H).
  - intros K l lts Ts ts IH ms H. rewrite has_rt_marker_ctor_eq in H.
    rewrite well_scoped_ctor_eq, rt_closed_ctor_eq. exact (IH ms H).
  - intros scrut tag nlt ar y n IHs IHy IHn ms H. simpl in H.
    apply Bool.orb_false_iff in H as [Hs Hyn]. apply Bool.orb_false_iff in Hyn as [Hy Hn].
    destruct (IHs ms Hs) as [Ws Rs]. destruct (IHy ms Hy) as [Wy Ry].
    destruct (IHn ms Hn) as [Wn Rn].
    split; [split; [exact Ws | split; [exact Wy | exact Wn]]
           | split; [exact Rs | split; [exact Ry | exact Rn]]].
  - intros E Ts T_B T_R op_bodies body IHops IHb ms H. simpl in H.
    rewrite has_rt_marker_ops_eq in H.
    apply Bool.orb_false_iff in H as [Hop Hb].
    destruct (IHops ms Hop) as [Wop Rop]. destruct (IHb ms Hb) as [Wb Rb].
    split; split; assumption.
  - intros t op Ss A_ret arg IHt IHa ms H. simpl in H.
    apply Bool.orb_false_iff in H as [Ht Ha].
    destruct (IHt ms Ht) as [Wt Rt]. destruct (IHa ms Ha) as [Wa Ra].
    split; split; assumption.
  - intros E_tag m Ts T_R op_bodies IHops ms H. simpl in H. discriminate.
  - intros m T_B T_R body IH ms H. simpl in H. discriminate.
  - intros ms H. split; exact I.
  - intros u ts IHu IHts ms H. simpl in H. apply Bool.orb_false_iff in H as [Hu Hts].
    destruct (IHu ms Hu) as [Wu Ru]. destruct (IHts ms Hts) as [Wts Rts].
    split; split; assumption.
  - intros ms H. split; exact I.
  - intros nb ob obs IHob IHobs ms H. simpl in H.
    apply Bool.orb_false_iff in H as [Hob Hobs].
    destruct (IHob ms Hob) as [Wob Rob]. destruct (IHobs ms Hobs) as [Wobs Robs].
    split; split; assumption.
Qed.

(* Monotonicity of well_scoped along scope extension: the payoff of    *)
(* dropping freshness.  A well-scoped value stays well-scoped when its  *)
(* ambient scope is extended above/between (new delimiters installed    *)
(* around it, or binders crossed during substitution).                  *)
Lemma well_scoped_mono : forall t s ms,
  scope_ext s ms -> well_scoped s t -> well_scoped ms t.
Proof.
  apply (term_list_ind
    (fun t => forall s ms, scope_ext s ms -> well_scoped s t -> well_scoped ms t)
    (fun ts => forall s ms, scope_ext s ms -> well_scoped_list s ts -> well_scoped_list ms ts)
    (fun obs => forall s ms, scope_ext s ms -> ops_well_scoped s obs -> ops_well_scoped ms obs)).
  - intros n s ms Hse H. exact I.
  - intros t1 t2 IH1 IH2 s ms Hse [H1 H2].
    split; [eapply IH1|eapply IH2]; eassumption.
  - intros body T IH s ms Hse H. eapply IH; eassumption.
  - intros t T IH s ms Hse H. eapply IH; eassumption.
  - intros bound body IH s ms Hse H. eapply IH; eassumption.
  - intros t l IH s ms Hse H. eapply IH; eassumption.
  - intros body IH s ms Hse H. eapply IH; eassumption.
  - intros K l lts Ts ts IH s ms Hse H.
    rewrite well_scoped_ctor_eq. rewrite well_scoped_ctor_eq in H.
    eapply IH; eassumption.
  - intros scrut tag nlt ar y n IHs IHy IHn s ms Hse [Hs [Hy Hn]].
    split; [eapply IHs; eassumption
           |split; [eapply IHy; eassumption|eapply IHn; eassumption]].
  - intros E Ts T_B T_R op_bodies body IHops IHb s ms Hse [Hop Hb].
    split; [eapply IHops|eapply IHb]; eassumption.
  - intros t op Ss A_ret arg IHt IHa s ms Hse [Ht Ha].
    split; [eapply IHt|eapply IHa]; eassumption.
  - intros E_tag m Ts T_R op_bodies IHops s ms Hse [Hin Hws]. split.
    + exact (scope_ext_incl _ _ Hse m Hin).
    + eapply IHops; [apply scope_ext_scope_below; exact Hse | exact Hws].
  - intros m T_B T_R body IH s ms Hse Hws.
    eapply IH; [apply se_cons; exact Hse | exact Hws].
  - intros s ms Hse H. exact I.
  - intros u ts IHu IHts s ms Hse [Hu Hts].
    split; [eapply IHu|eapply IHts]; eassumption.
  - intros s ms Hse H. exact I.
  - intros nb ob obs IHob IHobs s ms Hse [Hob Hobs].
    split; [eapply IHob|eapply IHobs]; eassumption.
Qed.
