Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import Typing.
Require Import Subst.
Require Import TypingInv.

(* ================================================================== *)
(* Runtime marker invariants.                                         *)
(*                                                                    *)
(* Typing alone is not enough for the effect layer: runtime terms     *)
(* mention markers, and the H_Perform contraction moves a cap's       *)
(* op-body across its own delimiter.  This file defines the           *)
(* invariants that the multi-step induction carries alongside typing  *)
(* (bundled in Soundness.v as [safety_invariants]) and proves them    *)
(* preserved:                                                         *)
(*                                                                    *)
(*   marker_annots t   — collector: every (marker, answer-type) pair  *)
(*                       on a cap / handler_m in t.                   *)
(*   marker_types_safe — all annotations for the same marker agree    *)
(*                       (Progress's H_Perform case needs the         *)
(*                       delimiter's and the cap's T_R to coincide).  *)
(*   marker_annots_closed — every annotation is a closed type, so     *)
(*                       type/lifetime substitution preserves the     *)
(*                       agreement.                                   *)
(*   marker_annots_ok  — the two bundled.                             *)
(*                                                                    *)
(*   well_scoped ms t  — marker provenance: each cap's marker is in   *)
(*                       the ambient scope [ms] (what Progress's      *)
(*                       delimitedness needs), and its op-body is     *)
(*                       well-scoped at [scope_below m ms] — the      *)
(*                       scope OUTSIDE its own delimiter, exactly     *)
(*                       where the H_Perform reduct lands.  Monotone  *)
(*                       along [scope_ext] (scope insertions).        *)
(*   rt_closed t       — cap op-bodies are term-closed: minted at     *)
(*                       spine positions of a closed program, they    *)
(*                       stay closed, so substituting a value into    *)
(*                       them is the identity                         *)
(*                       ([subst_tm_closed_id]-style vacuity).        *)
(*   ws_rt             — the two bundled.                             *)
(*                                                                    *)
(* All invariants hold vacuously on source terms                      *)
(* ([has_rt_cap t = false]), which is how the source-facing           *)
(* corollaries need only an initial typing.                           *)
(* ================================================================== *)


Fixpoint marker_annots (t : term) : list (marker * type) :=
  match t with
  | term_var _ => []
  | term_app t1 t2 => marker_annots t1 ++ marker_annots t2
  | term_lam body _ => marker_annots body
  | term_ty_app t1 _ => marker_annots t1
  | term_ty_lam _ body => marker_annots body
  | term_lt_app t1 _ => marker_annots t1
  | term_lt_lam body => marker_annots body
  | term_ctor _ _ _ _ ts => List.concat (List.map marker_annots ts)
  | term_match scrut _ _ _ yes_body no_body =>
      marker_annots scrut ++ marker_annots yes_body ++ marker_annots no_body
  | term_handle _ _ _ _ _ op_body body =>
      marker_annots op_body ++ marker_annots body
  | term_perform recv _ _ arg => marker_annots recv ++ marker_annots arg
  | term_cap _ m _ _ T_R op_body => (m, T_R) :: marker_annots op_body
  | term_handler_m m _ T_R body => (m, T_R) :: marker_annots body
  end.

Definition marker_types_safe (t : term) : Prop :=
  forall m T U,
    In (m, T) (marker_annots t) ->
    In (m, U) (marker_annots t) ->
    T = U.

Definition marker_annots_closed (t : term) : Prop :=
  Forall (fun mt => ty_ty_closed 0 (snd mt) /\ ty_lt_closed 0 (snd mt))
         (marker_annots t).

Definition marker_annots_list_closed (ts : list term) : Prop :=
  Forall (fun mt => ty_ty_closed 0 (snd mt) /\ ty_lt_closed 0 (snd mt))
         (List.concat (List.map marker_annots ts)).

Lemma marker_types_safe_empty : forall t,
  marker_annots t = [] -> marker_types_safe t.
Proof.
  intros t Hann m T U Hin. rewrite Hann in Hin. inversion Hin.
Qed.

Lemma marker_annots_no_rt_cap : forall t,
  has_rt_cap t = false -> marker_annots t = [].
Proof.
  apply (term_list_ind
    (fun t => has_rt_cap t = false -> marker_annots t = [])
    (fun ts =>
       (fix go (ts : list term) : bool :=
          match ts with
          | [] => false
          | u :: rest => orb (has_rt_cap u) (go rest)
          end) ts = false ->
       List.concat (List.map marker_annots ts) = [])).
  - intros n H. reflexivity.
  - intros t1 t2 IH1 IH2 H. simpl in *.
    apply Bool.orb_false_iff in H as [H1 H2].
    rewrite (IH1 H1), (IH2 H2). reflexivity.
  - intros body T IH H. simpl in *. apply IH. exact H.
  - intros t T IH H. simpl in *. apply IH. exact H.
  - intros bound body IH H. simpl in *. apply IH. exact H.
  - intros t l IH H. simpl in *. apply IH. exact H.
  - intros body IH H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH H. simpl in *. apply IH. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn H. simpl in *.
    apply Bool.orb_false_iff in H as [Hs Hyn].
    apply Bool.orb_false_iff in Hyn as [Hy Hn].
    rewrite (IHs Hs), (IHy Hy), (IHn Hn). reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody H. simpl in *.
    apply Bool.orb_false_iff in H as [Hop Hbody].
    rewrite (IHop Hop), (IHbody Hbody). reflexivity.
  - intros recv Ss A_ret arg IHrecv IHarg H. simpl in *.
    apply Bool.orb_false_iff in H as [Hr Ha].
    rewrite (IHrecv Hr), (IHarg Ha). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop H. simpl in H. discriminate.
  - intros m T_B T_R body IH H. simpl in H. discriminate.
  - intros H. reflexivity.
  - intros t ts IHt IHts H. simpl in *.
    apply Bool.orb_false_iff in H as [Ht Hts].
    rewrite (IHt Ht), (IHts Hts). reflexivity.
Qed.

(* The two annotation invariants bundled: agreement of all             *)
(* annotations for the same marker, and closedness of every            *)
(* annotation.  This is the annotation conjunct of                     *)
(* [safety_invariants].                                                *)
Definition marker_annots_ok (t : term) : Prop :=
  marker_types_safe t /\ marker_annots_closed t.

Lemma marker_annots_closed_no_rt_cap : forall t,
  has_rt_cap t = false -> marker_annots_closed t.
Proof.
  intros t Hcap. unfold marker_annots_closed.
  rewrite (marker_annots_no_rt_cap t Hcap). constructor.
Qed.

Lemma marker_types_safe_no_rt_cap : forall t,
  has_rt_cap t = false -> marker_types_safe t.
Proof.
  intros t Hcap. apply marker_types_safe_empty.
  apply marker_annots_no_rt_cap. exact Hcap.
Qed.

Lemma marker_annots_ok_no_rt_cap : forall t,
  has_rt_cap t = false -> marker_annots_ok t.
Proof.
  intros t H. split;
    [apply marker_types_safe_no_rt_cap | apply marker_annots_closed_no_rt_cap];
    exact H.
Qed.

Lemma marker_types_safe_incl : forall sub whole,
  incl (marker_annots sub) (marker_annots whole) ->
  marker_types_safe whole ->
  marker_types_safe sub.
Proof.
  intros sub whole Hincl Hok m T U HT HU.
  eapply Hok; [apply Hincl | apply Hincl]; eauto.
Qed.

Lemma marker_types_safe_app_l : forall t1 t2,
  marker_types_safe (term_app t1 t2) -> marker_types_safe t1.
Proof.
  intros t1 t2 Hsafe. eapply marker_types_safe_incl; [|exact Hsafe].
  intros p Hp. simpl. apply List.in_or_app. left. exact Hp.
Qed.

Lemma marker_types_safe_app_r : forall t1 t2,
  marker_types_safe (term_app t1 t2) -> marker_types_safe t2.
Proof.
  intros t1 t2 Hsafe. eapply marker_types_safe_incl; [|exact Hsafe].
  intros p Hp. simpl. apply List.in_or_app. right. exact Hp.
Qed.

Lemma marker_types_safe_match_scrut : forall scrut K n_lt arity yes no,
  marker_types_safe (term_match scrut K n_lt arity yes no) -> marker_types_safe scrut.
Proof.
  intros scrut K n_lt arity yes no Hsafe. eapply marker_types_safe_incl; [|exact Hsafe].
  intros p Hp. simpl. apply List.in_or_app. left. exact Hp.
Qed.

Lemma marker_types_safe_perform_recv : forall recv Ss A arg,
  marker_types_safe (term_perform recv Ss A arg) -> marker_types_safe recv.
Proof.
  intros recv Ss A arg Hsafe. eapply marker_types_safe_incl; [|exact Hsafe].
  intros p Hp. simpl. apply List.in_or_app. left. exact Hp.
Qed.

Lemma marker_types_safe_perform_arg : forall recv Ss A arg,
  marker_types_safe (term_perform recv Ss A arg) -> marker_types_safe arg.
Proof.
  intros recv Ss A arg Hsafe. eapply marker_types_safe_incl; [|exact Hsafe].
  intros p Hp. simpl. apply List.in_or_app. right. exact Hp.
Qed.

Lemma marker_types_safe_handler_body : forall m T_B T_R body,
  marker_types_safe (term_handler_m m T_B T_R body) -> marker_types_safe body.
Proof.
  intros m T_B T_R body Hsafe. eapply marker_types_safe_incl; [|exact Hsafe].
  intros p Hp. simpl. right. exact Hp.
Qed.

Lemma marker_types_safe_ctor_args : forall K l lts Ts vs,
  marker_types_safe (term_ctor K l lts Ts vs) ->
  Forall marker_types_safe vs.
Proof.
  intros K l lts Ts vs. induction vs as [|v rest IH]; intros Hsafe; constructor.
  - eapply marker_types_safe_incl; [|exact Hsafe].
    intros p Hp. simpl. apply List.in_or_app. left. exact Hp.
  - apply IH. eapply marker_types_safe_incl; [|exact Hsafe].
    intros p Hp. simpl. apply List.in_or_app. right. exact Hp.
Qed.


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


(* go_eq_map for subst_ty_in_tm (the other go_eq_map lemmas live upstream). *)
Lemma subst_ty_in_tm_go_eq_map : forall var R ts,
  (fix go ts := match ts with [] => [] | u :: rest => subst_ty_in_tm var R u :: go rest end) ts =
  List.map (subst_ty_in_tm var R) ts.
Proof. intros; induction ts; simpl; congruence. Qed.

Lemma marker_annots_shift_tm : forall t amount cutoff,
  marker_annots (shift_tm amount cutoff t) = marker_annots t.
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
       marker_annots (shift_tm amount cutoff t) = marker_annots t)
    (fun ts => forall amount cutoff,
       List.concat (List.map marker_annots (List.map (shift_tm amount cutoff) ts)) =
       List.concat (List.map marker_annots ts))).
  - intros n amount cutoff. reflexivity.
  - intros t1 t2 IH1 IH2 amount cutoff. simpl.
    rewrite IH1, IH2. reflexivity.
  - intros body T IH amount cutoff. simpl. apply IH.
  - intros t T IH amount cutoff. simpl. apply IH.
  - intros bound body IH amount cutoff. simpl. apply IH.
  - intros t l IH amount cutoff. simpl. apply IH.
  - intros body IH amount cutoff. simpl. apply IH.
  - intros K l lts Ts ts IH amount cutoff. simpl.
    rewrite shift_tm_go_eq_map. apply IH.
  - intros scrut tag n_lt arity yes no IHs IHy IHn amount cutoff. simpl.
    rewrite IHs, IHy, IHn. reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody amount cutoff. simpl.
    rewrite IHop, IHbody. reflexivity.
  - intros recv Ss A_ret arg IHrecv IHarg amount cutoff. simpl.
    rewrite IHrecv, IHarg. reflexivity.
  - intros E m n_beta Ts T_R op_body IHop amount cutoff. simpl.
    rewrite IHop. reflexivity.
  - intros m T_B T_R t IH amount cutoff. simpl.
    rewrite IH. reflexivity.
  - intros amount cutoff. reflexivity.
  - intros t ts IHt IHts amount cutoff. simpl.
    rewrite IHt, IHts. reflexivity.
Qed.

Lemma marker_annots_list_shift_tm : forall ts amount cutoff,
  List.concat (List.map marker_annots (List.map (shift_tm amount cutoff) ts)) =
  List.concat (List.map marker_annots ts).
Proof.
  induction ts as [|t ts IH]; intros amount cutoff; simpl.
  - reflexivity.
  - rewrite marker_annots_shift_tm, IH. reflexivity.
Qed.

Lemma marker_annots_shift_ectx_tm : forall E hole amount cutoff,
  marker_annots (plug (shift_ectx_tm amount cutoff E) hole) = marker_annots (plug E hole).
Proof.
  induction E; intros hole amount cutoff; simpl.
  - reflexivity.
  - rewrite IHE, marker_annots_shift_tm. reflexivity.
  - rewrite marker_annots_shift_tm, IHE. reflexivity.
  - apply IHE.
  - apply IHE.
  - repeat rewrite List.map_app. repeat rewrite List.concat_app. simpl.
    rewrite marker_annots_list_shift_tm, IHE, marker_annots_list_shift_tm. reflexivity.
  - rewrite IHE, !marker_annots_shift_tm. reflexivity.
  - rewrite IHE. reflexivity.
  - rewrite IHE, marker_annots_shift_tm. reflexivity.
  - rewrite marker_annots_shift_tm, IHE. reflexivity.
Qed.


Lemma marker_annots_shift_ty_in_tm_closed : forall t amount cutoff,
  marker_annots_closed t ->
  marker_annots (shift_ty_in_tm amount cutoff t) = marker_annots t.
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
       marker_annots_closed t ->
       marker_annots (shift_ty_in_tm amount cutoff t) = marker_annots t)
    (fun ts => forall amount cutoff,
       marker_annots_list_closed ts ->
       List.concat (List.map marker_annots (List.map (shift_ty_in_tm amount cutoff) ts)) =
       List.concat (List.map marker_annots ts))).
  - intros n amount cutoff H. reflexivity.
  - intros t1 t2 IH1 IH2 amount cutoff H. unfold marker_annots_closed in *.
    simpl in *. apply Forall_app in H as [H1 H2].
    rewrite (IH1 amount cutoff H1), (IH2 amount cutoff H2). reflexivity.
  - intros body T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros bound body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t l IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH amount cutoff H. simpl in *.
    rewrite shift_ty_in_tm_go_eq_map.
    unfold marker_annots_closed in H. fold marker_annots_list_closed in H.
    apply IH. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    rewrite (IHs amount cutoff Hs), (IHy amount cutoff Hy), (IHn amount cutoff Hn).
    reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hop Hbody].
    rewrite (IHop amount (cutoff + n_beta) Hop), (IHbody amount cutoff Hbody).
    reflexivity.
  - intros recv Ss A_ret arg IHrecv IHarg amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hr Ha].
    rewrite (IHrecv amount cutoff Hr), (IHarg amount cutoff Ha). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [HTy _].
    rewrite (shift_ty_closed0_id T_R amount cutoff HTy).
    rewrite (IHop amount (cutoff + n_beta) Htail). reflexivity.
  - intros m T_B T_R t IH amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [HTy _].
    rewrite (shift_ty_closed0_id T_R amount cutoff HTy).
    rewrite (IH amount cutoff Htail). reflexivity.
  - intros amount cutoff H. reflexivity.
  - intros t ts IHt IHts amount cutoff H.
    unfold marker_annots_list_closed in *. simpl in *.
    apply Forall_app in H as [Ht Hts].
    rewrite (IHt amount cutoff Ht), (IHts amount cutoff Hts). reflexivity.
Qed.

Lemma marker_annots_shift_lt_in_tm_closed : forall t amount cutoff,
  marker_annots_closed t ->
  marker_annots (shift_lt_in_tm amount cutoff t) = marker_annots t.
Proof.
  apply (term_list_ind
    (fun t => forall amount cutoff,
       marker_annots_closed t ->
       marker_annots (shift_lt_in_tm amount cutoff t) = marker_annots t)
    (fun ts => forall amount cutoff,
       marker_annots_list_closed ts ->
       List.concat (List.map marker_annots (List.map (shift_lt_in_tm amount cutoff) ts)) =
       List.concat (List.map marker_annots ts))).
  - intros n amount cutoff H. reflexivity.
  - intros t1 t2 IH1 IH2 amount cutoff H. unfold marker_annots_closed in *.
    simpl in *. apply Forall_app in H as [H1 H2].
    rewrite (IH1 amount cutoff H1), (IH2 amount cutoff H2). reflexivity.
  - intros body T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t T IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros bound body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros t l IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros body IH amount cutoff H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH amount cutoff H. simpl in *.
    rewrite shift_lt_in_tm_go_eq_map.
    unfold marker_annots_closed in H. fold marker_annots_list_closed in H.
    apply IH. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    rewrite (IHs amount cutoff Hs), (IHy amount (cutoff + n_lt) Hy), (IHn amount cutoff Hn).
    reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hop Hbody].
    rewrite (IHop amount cutoff Hop), (IHbody amount cutoff Hbody). reflexivity.
  - intros recv Ss A_ret arg IHrecv IHarg amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hr Ha].
    rewrite (IHrecv amount cutoff Hr), (IHarg amount cutoff Ha). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [_ HLt].
    rewrite (shift_lt_in_ty_closed0_id T_R amount cutoff HLt).
    rewrite (IHop amount cutoff Htail). reflexivity.
  - intros m T_B T_R t IH amount cutoff H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [_ HLt].
    rewrite (shift_lt_in_ty_closed0_id T_R amount cutoff HLt).
    rewrite (IH amount cutoff Htail). reflexivity.
  - intros amount cutoff H. reflexivity.
  - intros t ts IHt IHts amount cutoff H.
    unfold marker_annots_list_closed in *. simpl in *.
    apply Forall_app in H as [Ht Hts].
    rewrite (IHt amount cutoff Ht), (IHts amount cutoff Hts). reflexivity.
Qed.

Lemma marker_annots_closed_shift_tm : forall t amount cutoff,
  marker_annots_closed t -> marker_annots_closed (shift_tm amount cutoff t).
Proof.
  intros t amount cutoff H.
  unfold marker_annots_closed in *. rewrite marker_annots_shift_tm. exact H.
Qed.

Lemma marker_annots_closed_shift_ty_in_tm : forall t amount cutoff,
  marker_annots_closed t -> marker_annots_closed (shift_ty_in_tm amount cutoff t).
Proof.
  intros t amount cutoff H.
  unfold marker_annots_closed in *. rewrite marker_annots_shift_ty_in_tm_closed by exact H. exact H.
Qed.

Lemma marker_annots_closed_shift_lt_in_tm : forall t amount cutoff,
  marker_annots_closed t -> marker_annots_closed (shift_lt_in_tm amount cutoff t).
Proof.
  intros t amount cutoff H.
  unfold marker_annots_closed in *. rewrite marker_annots_shift_lt_in_tm_closed by exact H. exact H.
Qed.


Lemma marker_annots_subst_ty_in_tm_closed : forall t var replacement,
  marker_annots_closed t ->
  marker_annots (subst_ty_in_tm var replacement t) = marker_annots t.
Proof.
  apply (term_list_ind
    (fun t => forall var replacement,
       marker_annots_closed t ->
       marker_annots (subst_ty_in_tm var replacement t) = marker_annots t)
    (fun ts => forall var replacement,
       marker_annots_list_closed ts ->
       List.concat (List.map marker_annots (List.map (subst_ty_in_tm var replacement) ts)) =
       List.concat (List.map marker_annots ts))).
  - intros n var replacement H. reflexivity.
  - intros t1 t2 IH1 IH2 var replacement H. unfold marker_annots_closed in *.
    simpl in *. apply Forall_app in H as [H1 H2].
    rewrite (IH1 var replacement H1), (IH2 var replacement H2). reflexivity.
  - intros body T IH var replacement H. simpl in *. apply IH. exact H.
  - intros t T IH var replacement H. simpl in *. apply IH. exact H.
  - intros bound body IH var replacement H. simpl in *. apply IH. exact H.
  - intros t l IH var replacement H. simpl in *. apply IH. exact H.
  - intros body IH var replacement H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH var replacement H. simpl in *.
    rewrite subst_ty_in_tm_go_eq_map.
    unfold marker_annots_closed in H. fold marker_annots_list_closed in H.
    apply IH. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    rewrite (IHs var replacement Hs).
    rewrite (IHy var (shift_lt_in_ty n_lt 0 replacement) Hy).
    rewrite (IHn var replacement Hn). reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hop Hbody].
    rewrite (IHop (var + n_beta) (shift_ty n_beta 0 replacement) Hop).
    rewrite (IHbody var replacement Hbody). reflexivity.
  - intros recv Ss A_ret arg IHrecv IHarg var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hr Ha].
    rewrite (IHrecv var replacement Hr), (IHarg var replacement Ha). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [HTy _].
    rewrite (subst_ty_closed0_id T_R var replacement HTy).
    rewrite (IHop (var + n_beta) (shift_ty n_beta 0 replacement) Htail). reflexivity.
  - intros m T_B T_R t IH var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [HTy _].
    rewrite (subst_ty_closed0_id T_R var replacement HTy).
    rewrite (IH var replacement Htail). reflexivity.
  - intros var replacement H. reflexivity.
  - intros t ts IHt IHts var replacement H.
    unfold marker_annots_list_closed in *. simpl in *.
    apply Forall_app in H as [Ht Hts].
    rewrite (IHt var replacement Ht), (IHts var replacement Hts). reflexivity.
Qed.

Lemma marker_annots_subst_lt_in_tm_closed : forall t var replacement,
  marker_annots_closed t ->
  marker_annots (subst_lt_in_tm var replacement t) = marker_annots t.
Proof.
  apply (term_list_ind
    (fun t => forall var replacement,
       marker_annots_closed t ->
       marker_annots (subst_lt_in_tm var replacement t) = marker_annots t)
    (fun ts => forall var replacement,
       marker_annots_list_closed ts ->
       List.concat (List.map marker_annots (List.map (subst_lt_in_tm var replacement) ts)) =
       List.concat (List.map marker_annots ts))).
  - intros n var replacement H. reflexivity.
  - intros t1 t2 IH1 IH2 var replacement H. unfold marker_annots_closed in *.
    simpl in *. apply Forall_app in H as [H1 H2].
    rewrite (IH1 var replacement H1), (IH2 var replacement H2). reflexivity.
  - intros body T IH var replacement H. simpl in *. apply IH. exact H.
  - intros t T IH var replacement H. simpl in *. apply IH. exact H.
  - intros bound body IH var replacement H. simpl in *. apply IH. exact H.
  - intros t l IH var replacement H. simpl in *. apply IH. exact H.
  - intros body IH var replacement H. simpl in *. apply IH. exact H.
  - intros K l lts Ts ts IH var replacement H. simpl in *.
    rewrite subst_lt_in_tm_go_eq_map.
    unfold marker_annots_closed in H. fold marker_annots_list_closed in H.
    apply IH. exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    repeat rewrite Forall_app in H. destruct H as [Hs [Hy Hn]].
    rewrite (IHs var replacement Hs).
    rewrite (IHy (n_lt + var) (shift_lt n_lt 0 replacement) Hy).
    rewrite (IHn var replacement Hn). reflexivity.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hop Hbody].
    rewrite (IHop var replacement Hop), (IHbody var replacement Hbody). reflexivity.
  - intros recv Ss A_ret arg IHrecv IHarg var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    apply Forall_app in H as [Hr Ha].
    rewrite (IHrecv var replacement Hr), (IHarg var replacement Ha). reflexivity.
  - intros E m n_beta Ts T_R op_body IHop var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [_ HLt].
    rewrite (subst_lt_in_ty_closed0_id T_R var replacement HLt).
    rewrite (IHop var replacement Htail). reflexivity.
  - intros m T_B T_R t IH var replacement H.
    unfold marker_annots_closed in *. simpl in *.
    inversion H as [|mt rest Hhead Htail]; subst.
    destruct Hhead as [_ HLt].
    rewrite (subst_lt_in_ty_closed0_id T_R var replacement HLt).
    rewrite (IH var replacement Htail). reflexivity.
  - intros var replacement H. reflexivity.
  - intros t ts IHt IHts var replacement H.
    unfold marker_annots_list_closed in *. simpl in *.
    apply Forall_app in H as [Ht Hts].
    rewrite (IHt var replacement Ht), (IHts var replacement Hts). reflexivity.
Qed.


Lemma marker_annots_subst_list_ty_in_tm_closed : forall Ss t,
  marker_annots_closed t ->
  marker_annots (subst_list_ty_in_tm Ss t) = marker_annots t.
Proof.
  induction Ss as [|S rest IH]; intros t Ht; simpl.
  - reflexivity.
  - assert (Hsubst : marker_annots_closed (subst_ty_in_tm 0 (shift_ty (List.length rest) 0 S) t)).
    { unfold marker_annots_closed in *.
      rewrite marker_annots_subst_ty_in_tm_closed by exact Ht.
      exact Ht. }
    rewrite (IH _ Hsubst).
    apply marker_annots_subst_ty_in_tm_closed. exact Ht.
Qed.

Lemma marker_annots_subst_list_lt_in_tm_closed : forall lts t,
  marker_annots_closed t ->
  marker_annots (subst_list_lt_in_tm lts t) = marker_annots t.
Proof.
  induction lts as [|l rest IH]; intros t Ht; simpl.
  - reflexivity.
  - assert (Hsubst : marker_annots_closed (subst_lt_in_tm 0 (shift_lt (List.length rest) 0 l) t)).
    { unfold marker_annots_closed in *.
      rewrite marker_annots_subst_lt_in_tm_closed by exact Ht.
      exact Ht. }
    rewrite (IH _ Hsubst).
    apply marker_annots_subst_lt_in_tm_closed. exact Ht.
Qed.


Lemma marker_annots_subst_tm_closed_repl_incl : forall t var repl,
  marker_annots_closed repl ->
  incl (marker_annots (subst_tm var repl t))
       (marker_annots repl ++ marker_annots t).
Proof.
  apply (term_list_ind
    (fun t => forall var repl,
       marker_annots_closed repl ->
       incl (marker_annots (subst_tm var repl t))
            (marker_annots repl ++ marker_annots t))
    (fun ts => forall var repl,
       marker_annots_closed repl ->
       incl (List.concat (List.map marker_annots (List.map (subst_tm var repl) ts)))
            (marker_annots repl ++ List.concat (List.map marker_annots ts)))).
  - intros n var repl Hrepl p Hp. simpl in *.
    destruct (Nat.eqb n var); [apply List.in_or_app; left; exact Hp|].
    destruct (Nat.ltb var n); inversion Hp.
  - intros t1 t2 IH1 IH2 var repl Hrepl p Hp. simpl in *.
    apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IH1 var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IH2 var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
  - intros body T IH var repl Hrepl p Hp. simpl in *.
    specialize (IH (S var) (shift_tm 1 0 repl)
      (marker_annots_closed_shift_tm _ _ _ Hrepl) p Hp).
    rewrite marker_annots_shift_tm in IH. exact IH.
  - intros t T IH var repl Hrepl p Hp. simpl in *.
    exact (IH var repl Hrepl p Hp).
  - intros bound body IH var repl Hrepl p Hp. simpl in *.
    specialize (IH var (shift_ty_in_tm 1 0 repl)
      (marker_annots_closed_shift_ty_in_tm _ _ _ Hrepl) p Hp).
    rewrite (marker_annots_shift_ty_in_tm_closed repl 1 0 Hrepl) in IH. exact IH.
  - intros t l IH var repl Hrepl p Hp. simpl in *.
    exact (IH var repl Hrepl p Hp).
  - intros body IH var repl Hrepl p Hp. simpl in *.
    specialize (IH var (shift_lt_in_tm 1 0 repl)
      (marker_annots_closed_shift_lt_in_tm _ _ _ Hrepl) p Hp).
    rewrite (marker_annots_shift_lt_in_tm_closed repl 1 0 Hrepl) in IH. exact IH.
  - intros K l lts Ts ts IH var repl Hrepl p Hp. simpl in *.
    rewrite subst_tm_go_eq_map in Hp.
    exact (IH var repl Hrepl p Hp).
  - intros scrut tag n_lt arity yes no IHs IHy IHn var repl Hrepl p Hp. simpl in *.
    repeat rewrite List.in_app_iff in Hp. destruct Hp as [Hp | [Hp | Hp]].
    + specialize (IHs var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IHy (var + arity) (shift_tm arity 0 (shift_lt_in_tm n_lt 0 repl))
        (marker_annots_closed_shift_tm _ _ _
          (marker_annots_closed_shift_lt_in_tm _ _ _ Hrepl)) p Hp).
      rewrite marker_annots_shift_tm in IHy.
      rewrite (marker_annots_shift_lt_in_tm_closed repl n_lt 0 Hrepl) in IHy.
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IHn var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody var repl Hrepl p Hp. simpl in *.
    apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IHop (var + 2) (shift_tm 2 0 repl)
        (marker_annots_closed_shift_tm _ _ _ Hrepl) p Hp).
      rewrite marker_annots_shift_tm in IHop.
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IHbody (S var) (shift_tm 1 0 repl)
        (marker_annots_closed_shift_tm _ _ _ Hrepl) p Hp).
      rewrite marker_annots_shift_tm in IHbody.
      repeat rewrite List.in_app_iff in *. tauto.
  - intros recv Ss A_ret arg IHrecv IHarg var repl Hrepl p Hp. simpl in *.
    apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IHrecv var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IHarg var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
  - intros E m n_beta Ts T_R op_body IHop var repl Hrepl p Hp. simpl in *.
    destruct Hp as [Hp | Hp].
    + apply List.in_or_app. right. simpl. left. exact Hp.
    + specialize (IHop (var + 2) (shift_tm 2 0 repl)
        (marker_annots_closed_shift_tm _ _ _ Hrepl) p Hp).
      rewrite marker_annots_shift_tm in IHop.
      apply List.in_app_or in IHop as [IHop | IHop].
      * apply List.in_or_app. left. exact IHop.
      * apply List.in_or_app. right. simpl. right. exact IHop.
  - intros m T_B T_R t IH var repl Hrepl p Hp. simpl in *.
    destruct Hp as [Hp | Hp].
    + apply List.in_or_app. right. simpl. left. exact Hp.
    + specialize (IH var repl Hrepl p Hp).
      apply List.in_app_or in IH as [IH | IH].
      * apply List.in_or_app. left. exact IH.
      * apply List.in_or_app. right. simpl. right. exact IH.
  - intros var repl Hrepl p Hp. inversion Hp.
  - intros t ts IHt IHts var repl Hrepl p Hp. simpl in *.
    apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IHt var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
    + specialize (IHts var repl Hrepl p Hp).
      repeat rewrite List.in_app_iff in *. tauto.
Qed.


Lemma marker_annots_subst_list_tm_closed_repl_incl : forall vs t,
  Forall marker_annots_closed vs ->
  incl (marker_annots (subst_list_tm vs t))
       (List.concat (List.map marker_annots vs) ++ marker_annots t).
Proof.
  induction vs as [|v rest IH]; intros t Hvs p Hp; simpl in *.
  - exact Hp.
  - inversion Hvs as [|v0 rest0 Hv Hrest Heq]; subst.
    specialize (IH (subst_tm 0 (shift_tm (List.length rest) 0 v) t) Hrest p Hp).
    apply List.in_app_or in IH as [HinRest | HinSubst].
    + repeat rewrite List.in_app_iff in *. tauto.
    + pose proof (marker_annots_subst_tm_closed_repl_incl t 0
        (shift_tm (List.length rest) 0 v)
        (marker_annots_closed_shift_tm _ _ _ Hv) p HinSubst) as Hsingle.
      rewrite marker_annots_shift_tm in Hsingle.
      repeat rewrite List.in_app_iff in *. tauto.
Qed.

Lemma marker_annots_closed_incl : forall sub whole,
  incl (marker_annots sub) (marker_annots whole) ->
  marker_annots_closed whole -> marker_annots_closed sub.
Proof.
  intros sub whole Hincl Hwhole.
  unfold marker_annots_closed in *.
  apply Forall_forall. intros mt Hmt.
  apply Forall_forall with (x := mt) in Hwhole; [exact Hwhole | apply Hincl; exact Hmt].
Qed.

Lemma marker_annots_closed_cons_incl : forall t m T source,
  ty_ty_closed 0 T ->
  ty_lt_closed 0 T ->
  marker_annots_closed source ->
  incl (marker_annots t) ((m, T) :: marker_annots source) ->
  marker_annots_closed t.
Proof.
  intros t m T source HTy HLt Hsource Hincl.
  unfold marker_annots_closed in *.
  apply Forall_forall. intros mt Hmt.
  specialize (Hincl mt Hmt) as Hin.
  destruct mt as [m0 T0].
  simpl in Hin |- *. destruct Hin as [Hin | Hin].
  - inversion Hin; subst. simpl. split; assumption.
  - exact (proj1 (Forall_forall _ _) Hsource (m0, T0) Hin).
Qed.


Lemma marker_annots_list_closed_Forall : forall ts,
  marker_annots_list_closed ts -> Forall marker_annots_closed ts.
Proof.
  induction ts as [|t ts IH]; intros H; constructor.
  - unfold marker_annots_list_closed, marker_annots_closed in *.
    simpl in H. apply Forall_app in H as [Ht _]. exact Ht.
  - apply IH. unfold marker_annots_list_closed in *.
    simpl in H. apply Forall_app in H as [_ Hts]. exact Hts.
Qed.


Lemma marker_annots_match_no_incl : forall K K' l lts Ts vs n_lt arity yes_body no_body,
  incl (marker_annots no_body)
       (marker_annots (term_match (term_ctor K' l lts Ts vs) K n_lt arity yes_body no_body)).
Proof.
  intros K K' l lts Ts vs n_lt arity yes_body no_body p Hp.
  simpl. repeat rewrite List.in_app_iff. tauto.
Qed.

Lemma marker_annots_return_incl : forall m T_B T_R v,
  incl (marker_annots v) (marker_annots (term_handler_m m T_B T_R v)).
Proof.
  intros m T_B T_R v p Hp. simpl. right. exact Hp.
Qed.


Lemma marker_annots_beta_incl_closed : forall body T v,
  marker_annots_closed v ->
  incl (marker_annots (subst_tm 0 v body))
       (marker_annots (term_app (term_lam body T) v)).
Proof.
  intros body T v Hv p Hp.
  pose proof (marker_annots_subst_tm_closed_repl_incl body 0 v Hv p Hp) as Hincl.
  simpl. repeat rewrite List.in_app_iff in *. tauto.
Qed.

Lemma marker_annots_tybeta_incl_closed : forall bound body T,
  marker_annots_closed body ->
  incl (marker_annots (subst_ty_in_tm 0 T body))
       (marker_annots (term_ty_app (term_ty_lam bound body) T)).
Proof.
  intros bound body T Hbody p Hp. simpl.
  rewrite marker_annots_subst_ty_in_tm_closed in Hp; [exact Hp | exact Hbody].
Qed.

Lemma marker_annots_ltbeta_incl_closed : forall body l,
  marker_annots_closed body ->
  incl (marker_annots (subst_lt_in_tm 0 l body))
       (marker_annots (term_lt_app (term_lt_lam body) l)).
Proof.
  intros body l Hbody p Hp. simpl.
  rewrite marker_annots_subst_lt_in_tm_closed in Hp; [exact Hp | exact Hbody].
Qed.

Lemma marker_annots_match_yes_incl_closed : forall K l lts Ts vs n_lt yes_body no_body,
  marker_annots_list_closed vs ->
  marker_annots_closed yes_body ->
  incl (marker_annots (subst_list_tm vs (subst_list_lt_in_tm lts yes_body)))
       (marker_annots (term_match (term_ctor K l lts Ts vs) K n_lt (List.length vs) yes_body no_body)).
Proof.
  intros K l lts Ts vs n_lt yes_body no_body Hvs Hyes p Hp.
  pose proof (marker_annots_subst_list_tm_closed_repl_incl vs
    (subst_list_lt_in_tm lts yes_body)
    (marker_annots_list_closed_Forall _ Hvs) p Hp) as Hincl.
  rewrite marker_annots_subst_list_lt_in_tm_closed in Hincl; [|exact Hyes].
  simpl. repeat rewrite List.in_app_iff in *. tauto.
Qed.


Lemma incl_app_compat_local : forall (A : Type) (xs xs' ys ys' : list A),
  incl xs xs' -> incl ys ys' -> incl (xs ++ ys) (xs' ++ ys').
Proof.
  intros A xs xs' ys ys' Hxs Hys p Hp.
  apply List.in_app_or in Hp as [Hp | Hp].
  - apply List.in_or_app. left. apply Hxs. exact Hp.
  - apply List.in_or_app. right. apply Hys. exact Hp.
Qed.

Lemma incl_cons_same_local : forall (A : Type) (x : A) xs ys,
  incl xs ys -> incl (x :: xs) (x :: ys).
Proof.
  intros A x xs ys H p Hp. simpl in Hp |- *.
  destruct Hp as [Hp | Hp]; [left; exact Hp | right; apply H; exact Hp].
Qed.

Lemma marker_annots_ctor_replace_incl : forall vs t t' ts,
  incl (marker_annots t') (marker_annots t) ->
  incl (List.concat (List.map marker_annots (vs ++ t' :: ts)))
       (List.concat (List.map marker_annots (vs ++ t :: ts))).
Proof.
  induction vs as [|v vs IH]; intros t t' ts Hincl.
  - simpl. apply incl_app_compat_local; [exact Hincl | apply incl_refl].
  - simpl. apply incl_app_compat_local; [apply incl_refl | apply IH; exact Hincl].
Qed.

Lemma marker_annots_ctor_replace_incl_cons : forall vs t t' ts new,
  incl (marker_annots t') (new :: marker_annots t) ->
  incl (List.concat (List.map marker_annots (vs ++ t' :: ts)))
       (new :: List.concat (List.map marker_annots (vs ++ t :: ts))).
Proof.
  induction vs as [|v vs IH]; intros t t' ts new Hincl p Hp; simpl in *.
  - apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (Hincl p Hp). simpl in Hincl. destruct Hincl as [Hnew | Hold].
      * left. exact Hnew.
      * right. apply List.in_or_app. left. exact Hold.
    + right. apply List.in_or_app. right. exact Hp.
  - apply List.in_app_or in Hp as [Hp | Hp].
    + right. apply List.in_or_app. left. exact Hp.
    + specialize (IH t t' ts new Hincl p Hp). simpl in IH. destruct IH as [Hnew | Hold].
      * left. exact Hnew.
      * right. apply List.in_or_app. right. exact Hold.
Qed.

Lemma marker_annots_plug_replace_incl : forall E r r',
  incl (marker_annots r') (marker_annots r) ->
  incl (marker_annots (plug E r')) (marker_annots (plug E r)).
Proof.
  induction E; intros r r' Hincl; simpl.
  - exact Hincl.
  - apply incl_app_compat_local; [apply IHE; exact Hincl | apply incl_refl].
  - apply incl_app_compat_local; [apply incl_refl | apply IHE; exact Hincl].
  - apply IHE. exact Hincl.
  - apply IHE. exact Hincl.
  - apply marker_annots_ctor_replace_incl. apply IHE. exact Hincl.
  - apply incl_app_compat_local; [apply IHE; exact Hincl | apply incl_refl].
  - apply incl_cons_same_local. apply IHE. exact Hincl.
  - apply incl_app_compat_local; [apply IHE; exact Hincl | apply incl_refl].
  - apply incl_app_compat_local; [apply incl_refl | apply IHE; exact Hincl].
Qed.

Lemma marker_annots_plug_replace_incl_cons : forall E r r' new,
  incl (marker_annots r') (new :: marker_annots r) ->
  incl (marker_annots (plug E r')) (new :: marker_annots (plug E r)).
Proof.
  induction E; intros r r' new Hincl p Hp; simpl in *.
  - apply Hincl. exact Hp.
  - apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IHE r r' new Hincl p Hp). simpl in IHE. destruct IHE as [Hnew | Hold].
      * left. exact Hnew.
      * right. apply List.in_or_app. left. exact Hold.
    + right. apply List.in_or_app. right. exact Hp.
  - apply List.in_app_or in Hp as [Hp | Hp].
    + right. apply List.in_or_app. left. exact Hp.
    + specialize (IHE r r' new Hincl p Hp). simpl in IHE. destruct IHE as [Hnew | Hold].
      * left. exact Hnew.
      * right. apply List.in_or_app. right. exact Hold.
  - exact (IHE r r' new Hincl p Hp).
  - exact (IHE r r' new Hincl p Hp).
  - exact (marker_annots_ctor_replace_incl_cons _ _ _ _ _
      (IHE r r' new Hincl) p Hp).
  - apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IHE r r' new Hincl p Hp). simpl in IHE. destruct IHE as [Hnew | Hold].
      * left. exact Hnew.
      * right. apply List.in_or_app. left. exact Hold.
    + right. apply List.in_or_app. right. exact Hp.
  - destruct Hp as [Hp | Hp].
    + right. left. exact Hp.
    + specialize (IHE r r' new Hincl p Hp). simpl in IHE. destruct IHE as [Hnew | Hold].
      * left. exact Hnew.
      * right. right. exact Hold.
  - apply List.in_app_or in Hp as [Hp | Hp].
    + specialize (IHE r r' new Hincl p Hp). simpl in IHE. destruct IHE as [Hnew | Hold].
      * left. exact Hnew.
      * right. apply List.in_or_app. left. exact Hold.
    + right. apply List.in_or_app. right. exact Hp.
  - apply List.in_app_or in Hp as [Hp | Hp].
    + right. apply List.in_or_app. left. exact Hp.
    + specialize (IHE r r' new Hincl p Hp). simpl in IHE. destruct IHE as [Hnew | Hold].
      * left. exact Hnew.
      * right. apply List.in_or_app. right. exact Hold.
Qed.

Lemma marker_annots_plug_var_incl : forall E r n,
  incl (marker_annots (plug E (term_var n))) (marker_annots (plug E r)).
Proof.
  intros E r n. apply marker_annots_plug_replace_incl.
  intros p Hp. inversion Hp.
Qed.

Lemma marker_annots_shift_ectx_tm_plug_var_incl : forall E r amount cutoff n,
  incl (marker_annots (plug (shift_ectx_tm amount cutoff E) (term_var n)))
       (marker_annots (plug E r)).
Proof.
  intros E r amount cutoff n p Hp.
  rewrite marker_annots_shift_ectx_tm in Hp.
  eapply marker_annots_plug_var_incl. exact Hp.
Qed.

Lemma marker_types_safe_plug_replace_incl : forall E r r',
  incl (marker_annots r') (marker_annots r) ->
  marker_types_safe (plug E r) ->
  marker_types_safe (plug E r').
Proof.
  intros E r r' Hincl Hsafe.
  eapply marker_types_safe_incl; [apply marker_annots_plug_replace_incl; exact Hincl | exact Hsafe].
Qed.

Lemma markers_in_ctor_eq : forall K l lts Ts ts,
  markers_in (term_ctor K l lts Ts ts) = markers_in_list ts.
Proof.
  intros K l lts Ts ts. simpl.
  induction ts as [|u rest IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma marker_annots_marker_in : forall t m T,
  In (m, T) (marker_annots t) -> In m (markers_in t).
Proof.
  apply (term_list_ind
    (fun t => forall m T, In (m, T) (marker_annots t) -> In m (markers_in t))
    (fun ts => forall m T,
       In (m, T) (List.concat (List.map marker_annots ts)) ->
       In m (markers_in_list ts))).
  - intros n m T H. inversion H.
  - intros t1 t2 IH1 IH2 m T H. simpl in *.
    apply List.in_app_or in H as [H | H].
    + apply List.in_or_app. left. apply IH1 with (T := T). exact H.
    + apply List.in_or_app. right. apply IH2 with (T := T). exact H.
  - intros body T0 IH m T H. simpl in *. apply IH with (T := T). exact H.
  - intros t T0 IH m T H. simpl in *. apply IH with (T := T). exact H.
  - intros bound body IH m T H. simpl in *. apply IH with (T := T). exact H.
  - intros t l IH m T H. simpl in *. apply IH with (T := T). exact H.
  - intros body IH m T H. simpl in *. apply IH with (T := T). exact H.
  - intros K l lts Ts ts IH m T H. rewrite markers_in_ctor_eq. apply IH with (T := T). exact H.
  - intros scrut tag n_lt arity yes no IHs IHy IHn m T H. simpl in *.
    repeat rewrite List.in_app_iff in H. destruct H as [H | [H | H]].
    + apply List.in_or_app. left. apply IHs with (T := T). exact H.
    + apply List.in_or_app. right. apply List.in_or_app. left. apply IHy with (T := T). exact H.
    + apply List.in_or_app. right. apply List.in_or_app. right. apply IHn with (T := T). exact H.
  - intros E n_beta Ts T_B T_R op_body body IHop IHbody m T H. simpl in *.
    apply List.in_app_or in H as [H | H].
    + apply List.in_or_app. left. apply IHop with (T := T). exact H.
    + apply List.in_or_app. right. apply IHbody with (T := T). exact H.
  - intros recv Ss A_ret arg IHrecv IHarg m T H. simpl in *.
    apply List.in_app_or in H as [H | H].
    + apply List.in_or_app. left. apply IHrecv with (T := T). exact H.
    + apply List.in_or_app. right. apply IHarg with (T := T). exact H.
  - intros E m0 n_beta Ts T_R op_body IHop m T H. simpl in *.
    destruct H as [H | H].
    + injection H; intros; subst. left. reflexivity.
    + right. apply IHop with (T := T). exact H.
  - intros m0 T_B T_R body IH m T H. simpl in *.
    destruct H as [H | H].
    + injection H; intros; subst. left. reflexivity.
    + right. apply IH with (T := T). exact H.
  - intros m T H. inversion H.
  - intros t ts IHt IHts m T H. simpl in *.
    apply List.in_app_or in H as [H | H].
    + apply List.in_or_app. left. apply IHt with (T := T). exact H.
    + apply List.in_or_app. right. apply IHts with (T := T). exact H.
Qed.

Lemma marker_types_safe_fresh_cons_incl : forall source t m T,
  ~ In m (markers_in source) ->
  marker_types_safe source ->
  incl (marker_annots t) ((m, T) :: marker_annots source) ->
  marker_types_safe t.
Proof.
  intros source t m T Hfresh Hsafe Hincl m0 U V HU HV.
  specialize (Hincl _ HU) as HU'.
  specialize (Hincl _ HV) as HV'.
  simpl in HU', HV'.
  destruct HU' as [HU' | HU']; destruct HV' as [HV' | HV'].
  - injection HU'; injection HV'; intros; subst. reflexivity.
  - injection HU'; intros; subst. exfalso. apply Hfresh.
    eapply marker_annots_marker_in. exact HV'.
  - injection HV'; intros; subst. exfalso. apply Hfresh.
    eapply marker_annots_marker_in. exact HU'.
  - eapply Hsafe; eauto.
Qed.

Lemma marker_annots_closed_cap : forall E m n_beta Ts T_R op_body,
  ty_ty_closed 0 T_R ->
  ty_lt_closed 0 T_R ->
  marker_annots_closed op_body ->
  marker_annots_closed (term_cap E m n_beta Ts T_R op_body).
Proof.
  intros E m n_beta Ts T_R op_body HTy HLt Hop.
  unfold marker_annots_closed in *. simpl. constructor.
  - simpl. split; assumption.
  - exact Hop.
Qed.

Lemma marker_annots_handle_alloc_redex_incl_closed :
  forall E_tag n_beta Ts T_B T_R op_body body m,
    ty_ty_closed 0 T_R ->
    ty_lt_closed 0 T_R ->
    marker_annots_closed op_body ->
    incl
      (marker_annots
        (term_handler_m m T_B T_R
          (subst_tm 0 (term_cap E_tag m n_beta Ts T_R op_body) body)))
      ((m, T_R) :: marker_annots (term_handle E_tag n_beta Ts T_B T_R op_body body)).
Proof.
  intros E_tag n_beta Ts T_B T_R op_body body m HTy HLt Hop p Hp.
  simpl in Hp |- *.
  destruct Hp as [Hp | Hp].
  - left. exact Hp.
  - pose proof (marker_annots_closed_cap E_tag m n_beta Ts T_R op_body HTy HLt Hop) as Hcap.
    pose proof (marker_annots_subst_tm_closed_repl_incl body 0
      (term_cap E_tag m n_beta Ts T_R op_body) Hcap p Hp) as Hincl.
    simpl in Hincl. repeat rewrite List.in_app_iff in *. tauto.
Qed.

Lemma marker_types_safe_handle_alloc_closed :
  forall E E_tag n_beta Ts T_B T_R op_body body m,
    ~ In m (markers_in (plug E (term_handle E_tag n_beta Ts T_B T_R op_body body))) ->
    ty_ty_closed 0 T_R ->
    ty_lt_closed 0 T_R ->
    marker_annots_closed op_body ->
    marker_types_safe (plug E (term_handle E_tag n_beta Ts T_B T_R op_body body)) ->
    marker_types_safe
      (plug E
        (term_handler_m m T_B T_R
          (subst_tm 0 (term_cap E_tag m n_beta Ts T_R op_body) body))).
Proof.
  intros E E_tag n_beta Ts T_B T_R op_body body m Hfresh HTy HLt Hop Hsafe.
  eapply marker_types_safe_fresh_cons_incl with
    (source := plug E (term_handle E_tag n_beta Ts T_B T_R op_body body))
    (m := m) (T := T_R); eauto.
  apply marker_annots_plug_replace_incl_cons.
  apply marker_annots_handle_alloc_redex_incl_closed; assumption.
Qed.

Lemma marker_annots_ctor_focus_in : forall p vs t ts,
  In p (marker_annots t) ->
  In p (List.concat (List.map marker_annots (vs ++ t :: ts))).
Proof.
  intros p vs. induction vs as [|v vs IH]; intros t ts Hin; simpl.
  - apply List.in_or_app. left. exact Hin.
  - apply List.in_or_app. right. apply IH. exact Hin.
Qed.

Lemma marker_annots_plug_in : forall E hole p,
  In p (marker_annots hole) ->
  In p (marker_annots (plug E hole)).
Proof.
  induction E; intros hole p Hin; simpl.
  - exact Hin.
  - apply List.in_or_app. left. apply IHE. exact Hin.
  - apply List.in_or_app. right. apply IHE. exact Hin.
  - apply IHE. exact Hin.
  - apply IHE. exact Hin.
  - apply marker_annots_ctor_focus_in. apply IHE. exact Hin.
  - apply List.in_or_app. left. apply IHE. exact Hin.
  - simpl. right. apply IHE. exact Hin.
  - apply List.in_or_app. left. apply IHE. exact Hin.
  - apply List.in_or_app. right. apply IHE. exact Hin.
Qed.

Lemma marker_types_ok_handler_perform_annotation_match :
  forall m T_B T_H E_tag n_beta Ts T_R op_body Ss A v P,
    marker_types_safe
      (term_handler_m m T_B T_H
        (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss A v))) ->
    T_R = T_H.
Proof.
  intros m T_B T_H E_tag n_beta Ts T_R op_body Ss A v P Hok.
  symmetry.
  eapply (Hok m T_H T_R).
  - simpl. left. reflexivity.
  - simpl. right. apply marker_annots_plug_in.
    simpl. left. reflexivity.
Qed.

Lemma head_step_marker_annots_incl_closed_with_perform :
  forall r r',
    r -->h r' ->
    marker_annots_closed r ->
    (forall E_tag m n_beta Ts T_B T_R op_body Ss A v P,
      value v -> pure_ectx_m m P ->
      marker_annots_closed
        (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss A v))) ->
      incl
        (marker_annots
          (subst_list_tm [v; term_lam (term_handler_m m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))) A]
            (subst_list_ty_in_tm Ss op_body)))
        (marker_annots
          (term_handler_m m T_B T_R
            (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss A v))))) ->
    incl (marker_annots r') (marker_annots r).
Proof.
  intros r r' Hstep Hclosed Hperform.
  inversion Hstep; subst.
  - (* H_Beta *)
    simpl in Hclosed. apply Forall_app in Hclosed as [_ Hv].
    apply marker_annots_beta_incl_closed. exact Hv.
  - (* H_TyBeta *)
    apply marker_annots_tybeta_incl_closed. exact Hclosed.
  - (* H_LtBeta *)
    apply marker_annots_ltbeta_incl_closed. exact Hclosed.
  - (* H_MatchYes *)
    simpl in Hclosed. apply Forall_app in Hclosed as [Hvs Hyn].
    apply Forall_app in Hyn as [Hyes _].
    apply marker_annots_match_yes_incl_closed; assumption.
  - (* H_MatchNo *)
    apply marker_annots_match_no_incl.
  - (* H_Return *)
    apply marker_annots_return_incl.
  - (* H_Perform *)
    eapply Hperform; eauto.
Qed.

Lemma step_preserves_marker_types_safe_closed_with_perform_and_handle_closed :
  forall t t',
    t ==> t' ->
    marker_annots_closed t ->
    marker_types_safe t ->
    (forall E_tag m n_beta Ts T_B T_R op_body Ss A v P,
      value v -> pure_ectx_m m P ->
      marker_annots_closed
        (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss A v))) ->
      incl
        (marker_annots
          (subst_list_tm [v; term_lam (term_handler_m m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))) A]
            (subst_list_ty_in_tm Ss op_body)))
        (marker_annots
          (term_handler_m m T_B T_R
            (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss A v))))) ->
    (forall E E_tag n_beta Ts T_B T_R op_body body (m : marker),
      t = plug E (term_handle E_tag n_beta Ts T_B T_R op_body body) ->
      ty_ty_closed 0 T_R /\ ty_lt_closed 0 T_R) ->
    marker_types_safe t'.
Proof.
  intros t t' Hstep Hclosed Hsafe Hperform Hhandle_closed.
  inversion Hstep as
    [E r r' Hwf Hhead Heq1 Heq2
    | E E_tag n_beta Ts T_B T_R op_body body m Hwf Hfresh Heq1 Heq2]; subst.
  - assert (Hclosed_r : marker_annots_closed r).
    { eapply marker_annots_closed_incl.
      - intros p Hp. apply marker_annots_plug_in. exact Hp.
      - exact Hclosed. }
    pose proof (head_step_marker_annots_incl_closed_with_perform
      r r' Hhead Hclosed_r Hperform) as Hincl.
    eapply marker_types_safe_plug_replace_incl; [exact Hincl | exact Hsafe].
  - destruct (Hhandle_closed E E_tag n_beta Ts T_B T_R op_body body m eq_refl) as [HTy HLt].
    eapply marker_types_safe_handle_alloc_closed; eauto.
    eapply marker_annots_closed_incl; [|exact Hclosed].
    intros p Hp. apply marker_annots_plug_in. simpl. apply List.in_or_app. left. exact Hp.
Qed.

Lemma step_preserves_marker_types_safe_closed_typed_with_perform :
  forall Γ t t' T,
    eval_ctx Γ ->
    Γ ⊢ₜ t : T ->
    t ==> t' ->
    marker_annots_closed t ->
    marker_types_safe t ->
    (forall E_tag m n_beta Ts T_B T_R op_body Ss A v P,
      value v -> pure_ectx_m m P ->
      marker_annots_closed
        (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss A v))) ->
      incl
        (marker_annots
          (subst_list_tm [v; term_lam (term_handler_m m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))) A]
            (subst_list_ty_in_tm Ss op_body)))
        (marker_annots
          (term_handler_m m T_B T_R
            (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss A v))))) ->
    marker_types_safe t'.
Proof.
  intros Γ t t' T Hec Hty Hstep Hclosed Hsafe Hperform.
  eapply step_preserves_marker_types_safe_closed_with_perform_and_handle_closed; eauto.
  intros E E_tag n_beta Ts T_B T_R op_body body m Heq. subst.
  eapply handle_result_closed_from_plug_typing; eauto.
Qed.

Lemma marker_annots_perform_reduct_incl_closed :
  forall E_tag m n_beta Ts T_B T_R op_body Ss A v P,
    marker_annots_closed
      (term_handler_m m T_B T_R
        (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss A v))) ->
    incl
      (marker_annots
        (subst_list_tm [v; term_lam (term_handler_m m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))) A]
          (subst_list_ty_in_tm Ss op_body)))
      (marker_annots
        (term_handler_m m T_B T_R
          (plug P (term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss A v)))).
Proof.
  intros E_tag m n_beta Ts T_B T_R op_body Ss A v P Hclosed.
  set (perform_redex := term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss A v).
  set (source := term_handler_m m T_B T_R (plug P perform_redex)).
  set (resume := term_lam (term_handler_m m T_B T_R (plug (shift_ectx_tm 1 0 P) (term_var 0))) A).
  assert (HTRclosed : ty_ty_closed 0 T_R /\ ty_lt_closed 0 T_R).
  { unfold marker_annots_closed in Hclosed. subst source perform_redex resume. simpl in Hclosed.
    inversion Hclosed as [|mt rest Hhead Htail]; subst. exact Hhead. }
  assert (Hop_closed : marker_annots_closed op_body).
  { subst source perform_redex resume.
    eapply marker_annots_closed_incl; [|exact Hclosed].
    intros p Hp. simpl. right. apply marker_annots_plug_in.
    simpl. right. apply List.in_or_app. left. exact Hp. }
  assert (Hv_closed : marker_annots_closed v).
  { subst source perform_redex resume.
    eapply marker_annots_closed_incl; [|exact Hclosed].
    intros p Hp. simpl. right. apply marker_annots_plug_in.
    simpl. right. apply List.in_or_app. right. exact Hp. }
  assert (Hresume_closed : marker_annots_closed resume).
  { subst source perform_redex resume. unfold marker_annots_closed. simpl. constructor.
    - exact HTRclosed.
    - eapply marker_annots_closed_incl; [|exact Hclosed].
      intros p Hp. simpl. right.
      eapply marker_annots_shift_ectx_tm_plug_var_incl with (r := term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss A v).
      exact Hp. }
  assert (Hvincl : incl (marker_annots v) (marker_annots source)).
  { subst source perform_redex resume. intros p Hp. simpl. right. apply marker_annots_plug_in.
    simpl. right. apply List.in_or_app. right. exact Hp. }
  assert (Hopincl : incl (marker_annots op_body) (marker_annots source)).
  { subst source perform_redex resume. intros p Hp. simpl. right. apply marker_annots_plug_in.
    simpl. right. apply List.in_or_app. left. exact Hp. }
  assert (Hresincl : incl (marker_annots resume) (marker_annots source)).
  { subst source perform_redex resume. intros p Hp. simpl in Hp. destruct Hp as [Hp | Hp].
    - simpl. left. exact Hp.
    - simpl. right.
      eapply marker_annots_shift_ectx_tm_plug_var_incl with (r := term_perform (term_cap E_tag m n_beta Ts T_R op_body) Ss A v).
      exact Hp. }
  intros p Hp.
  pose proof (marker_annots_subst_list_tm_closed_repl_incl
    [v; resume] (subst_list_ty_in_tm Ss op_body)
    (Forall_cons _ Hv_closed (Forall_cons _ Hresume_closed (Forall_nil _)))
    p Hp) as Hincl.
  subst resume source perform_redex.
  rewrite marker_annots_subst_list_ty_in_tm_closed in Hincl by exact Hop_closed.
  simpl in Hincl. repeat rewrite List.app_nil_r in Hincl.
  repeat rewrite List.in_app_iff in Hincl.
  destruct Hincl as [[HvIn | HresIn] | HopIn].
  - apply Hvincl. exact HvIn.
  - apply Hresincl. exact HresIn.
  - apply Hopincl. exact HopIn.
Qed.

Lemma step_preserves_marker_types_safe_closed_typed : forall Γ t t' T,
  eval_ctx Γ -> marker_annots_closed t -> marker_types_safe t -> Γ ⊢ₜ t : T ->
  t ==> t' -> marker_types_safe t'.
Proof.
  intros Γ t t' T Hec Hclosed Hsafe Hty Hstep.
  eapply step_preserves_marker_types_safe_closed_typed_with_perform; eauto.
  intros E_tag m n_beta Ts T_B T_R op_body Ss A v P Hval Hpure Hclosed_redex.
  apply marker_annots_perform_reduct_incl_closed. exact Hclosed_redex.
Qed.

Lemma step_preserves_marker_annots_closed_typed : forall Γ t t' T,
  eval_ctx Γ -> marker_annots_closed t -> Γ ⊢ₜ t : T ->
  t ==> t' -> marker_annots_closed t'.
Proof.
  intros Γ t t' T Hec Hclosed Hty Hstep.
  inversion Hstep as
    [E r r' Hwf Hhead Heq1 Heq2
    | E E_tag n_beta Ts T_B T_R op_body body m Hwf Hfresh Heq1 Heq2]; subst.
  - assert (Hclosed_r : marker_annots_closed r).
    { eapply marker_annots_closed_incl.
      - intros p Hp. apply marker_annots_plug_in. exact Hp.
      - exact Hclosed. }
    pose proof (head_step_marker_annots_incl_closed_with_perform r r' Hhead Hclosed_r) as Hincl.
    assert (Hred_incl : incl (marker_annots r') (marker_annots r)).
    { apply Hincl. intros E_tag m n_beta Ts T_B T_R op_body Ss A v P Hval Hpure Hclosed_redex.
      apply marker_annots_perform_reduct_incl_closed. exact Hclosed_redex. }
    eapply marker_annots_closed_incl.
    + apply marker_annots_plug_replace_incl. exact Hred_incl.
    + exact Hclosed.
  - destruct (handle_result_closed_from_plug_typing
      Γ E E_tag n_beta Ts T_B T_R op_body body T Hec Hty) as [HTy HLt].
    assert (Hop_closed : marker_annots_closed op_body).
    { eapply marker_annots_closed_incl; [|exact Hclosed].
      intros p Hp. apply marker_annots_plug_in. simpl. apply List.in_or_app. left. exact Hp. }
    eapply marker_annots_closed_cons_incl with
      (m := m) (T := T_R)
      (source := plug E (term_handle E_tag n_beta Ts T_B T_R op_body body)); eauto.
    apply marker_annots_plug_replace_incl_cons.
    apply marker_annots_handle_alloc_redex_incl_closed; assumption.
Qed.

(* The fused annotation invariant is preserved by one step. *)
Lemma step_preserves_marker_annots_ok_typed : forall Γ t t' T,
  eval_ctx Γ -> marker_annots_ok t -> Γ ⊢ₜ t : T ->
  t ==> t' -> marker_annots_ok t'.
Proof.
  intros Γ t t' T Hec [Hsafe Hclosed] Hty Hstep. split.
  - eapply step_preserves_marker_types_safe_closed_typed; eauto.
  - eapply step_preserves_marker_annots_closed_typed; eauto.
Qed.

(* ================================================================== *)
(* marker_ok metatheory: monotonicity and substitution invariance     *)
(*                                                                    *)
(* These are the genuinely-true, reusable structural facts about the  *)
(* runtime marker invariant.  They are needed by any sound proof of   *)
(* marker preservation (subject reduction for marker_ok).             *)
(* ================================================================== *)

(* Top-level mirror of the nested marker_ok_list fixpoint, so that the  *)
(* constructor-argument list can be reasoned about with term_list_ind.  *)



(* has_rt_cap on a constructor reduces to has_rt_cap_list on its       *)
(* argument list (the in-body fixpoint equals the named list version).  *)
Lemma has_rt_cap_ctor_eq : forall K l lts Ts ts,
  has_rt_cap (term_ctor K l lts Ts ts) = has_rt_cap_list ts.
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

(* ================================================================== *)
(* Phase 2 infrastructure: markers_in under shifts and substitutions. *)
(* ================================================================== *)

(* ==================================================================== *)
(* Scope extension.                                                     *)
(*                                                                      *)
(* [scope_ext s ms] relates an ambient marker scope [s] to any scope    *)
(* [ms] obtained from it by inserting extra markers above and/or        *)
(* between the markers of [s], preserving their order.  Well-           *)
(* scopedness (v2) is monotone along this relation: a value moved       *)
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
(* The marker well-scopedness invariant, v2.                            *)
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
(* preserved by reduction (see step_preserves_well_scoped).            *)
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
  | term_handle _ _ _ _ _ op_body body =>
      well_scoped ms op_body /\ well_scoped ms body
  | term_perform recv _ _ arg => well_scoped ms recv /\ well_scoped ms arg
  | term_cap _ m _ _ _ op_body =>
      In m ms /\ well_scoped (scope_below m ms) op_body
  | term_handler_m m _ _ body => well_scoped (m :: ms) body
  end.

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
  | term_handle _ _ _ _ _ op_body body => rt_closed op_body /\ rt_closed body
  | term_perform recv _ _ arg => rt_closed recv /\ rt_closed arg
  | term_cap _ _ _ _ _ op_body => free_tm_vars 2 op_body = [] /\ rt_closed op_body
  | term_handler_m _ _ _ body => rt_closed body
  end.

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


(* well_scoped holds vacuously on terms with no runtime capability. *)
Lemma well_scoped_no_rt_cap : forall t ms, has_rt_cap t = false -> well_scoped ms t.
Proof.
  apply (term_list_ind
    (fun t => forall ms, has_rt_cap t = false -> well_scoped ms t)
    (fun ts => forall ms, has_rt_cap_list ts = false -> well_scoped_list ms ts)).
  - intros n ms H. exact I.
  - intros t1 t2 IH1 IH2 ms H. simpl in H. apply Bool.orb_false_iff in H as [H1 H2].
    split; [apply IH1|apply IH2]; assumption.
  - intros body T IH ms H. simpl in H. apply IH. exact H.
  - intros t T IH ms H. simpl in H. apply IH. exact H.
  - intros bound body IH ms H. simpl in H. apply IH. exact H.
  - intros t l IH ms H. simpl in H. apply IH. exact H.
  - intros body IH ms H. simpl in H. apply IH. exact H.
  - intros K l lts Ts ts IH ms H. rewrite well_scoped_ctor_eq. apply IH.
    rewrite has_rt_cap_ctor_eq in H. exact H.
  - intros scrut tag nlt ar y n IHs IHy IHn ms H. simpl in H.
    apply Bool.orb_false_iff in H as [Hs Hyn]. apply Bool.orb_false_iff in Hyn as [Hy Hn].
    split; [apply IHs|split;[apply IHy|apply IHn]]; assumption.
  - intros E nb Ts T_B T_R op body IHop IHb ms H. simpl in H.
    apply Bool.orb_false_iff in H as [Hop Hb]. split; [apply IHop|apply IHb]; assumption.
  - intros t Ss A_ret arg IHt IHa ms H. simpl in H.
    apply Bool.orb_false_iff in H as [Ht Ha]. split; [apply IHt|apply IHa]; assumption.
  - intros E_tag m nb Ts T_R op IHop ms H. simpl in H. discriminate.
  - intros m T_B T_R body IH ms H. simpl in H. discriminate.
  - intros ms H. exact I.
  - intros u ts IHu IHts ms H. simpl in H. apply Bool.orb_false_iff in H as [Hu Hts].
    split; [apply IHu|apply IHts]; assumption.
Qed.

(* rt_closed holds vacuously on terms with no runtime capability. *)
Lemma rt_closed_no_rt_cap : forall t, has_rt_cap t = false -> rt_closed t.
Proof.
  apply (term_list_ind
    (fun t => has_rt_cap t = false -> rt_closed t)
    (fun ts => has_rt_cap_list ts = false -> rt_closed_list ts)).
  - intros n H. exact I.
  - intros t1 t2 IH1 IH2 H. simpl in H. apply Bool.orb_false_iff in H as [H1 H2].
    split; [apply IH1|apply IH2]; assumption.
  - intros body T IH H. simpl in H. apply IH. exact H.
  - intros t T IH H. simpl in H. apply IH. exact H.
  - intros bound body IH H. simpl in H. apply IH. exact H.
  - intros t l IH H. simpl in H. apply IH. exact H.
  - intros body IH H. simpl in H. apply IH. exact H.
  - intros K l lts Ts ts IH H. rewrite rt_closed_ctor_eq. apply IH.
    rewrite has_rt_cap_ctor_eq in H. exact H.
  - intros scrut tag nlt ar y n IHs IHy IHn H. simpl in H.
    apply Bool.orb_false_iff in H as [Hs Hyn]. apply Bool.orb_false_iff in Hyn as [Hy Hn].
    split; [apply IHs|split;[apply IHy|apply IHn]]; assumption.
  - intros E nb Ts T_B T_R op body IHop IHb H. simpl in H.
    apply Bool.orb_false_iff in H as [Hop Hb]. split; [apply IHop|apply IHb]; assumption.
  - intros t Ss A_ret arg IHt IHa H. simpl in H.
    apply Bool.orb_false_iff in H as [Ht Ha]. split; [apply IHt|apply IHa]; assumption.
  - intros E_tag m nb Ts T_R op IHop H. simpl in H. discriminate.
  - intros m T_B T_R body IH H. simpl in H. discriminate.
  - intros H. exact I.
  - intros u ts IHu IHts H. simpl in H. apply Bool.orb_false_iff in H as [Hu Hts].
    split; [apply IHu|apply IHts]; assumption.
Qed.

(* The fused v2 runtime invariant: marker provenance ([well_scoped])   *)
(* and term-closedness of cap op-bodies ([rt_closed]).  The bundle and *)
(* the step-preservation layer consume this fused form; the component  *)
(* predicates and their traversal lemmas remain the proof engine.      *)
Definition ws_rt (ms : list marker) (t : term) : Prop :=
  well_scoped ms t /\ rt_closed t.

Lemma ws_rt_no_rt_cap : forall t, has_rt_cap t = false -> ws_rt [] t.
Proof.
  intros t H. split;
    [apply well_scoped_no_rt_cap | apply rt_closed_no_rt_cap]; exact H.
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
    (fun ts => forall s ms, scope_ext s ms -> well_scoped_list s ts -> well_scoped_list ms ts)).
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
  - intros E nb Ts T_B T_R op body IHop IHb s ms Hse [Hop Hb].
    split; [eapply IHop|eapply IHb]; eassumption.
  - intros t Ss A_ret arg IHt IHa s ms Hse [Ht Ha].
    split; [eapply IHt|eapply IHa]; eassumption.
  - intros E_tag m nb Ts T_R op IHop s ms Hse [Hin Hws]. split.
    + exact (scope_ext_incl _ _ Hse m Hin).
    + eapply IHop; [apply scope_ext_scope_below; exact Hse | exact Hws].
  - intros m T_B T_R body IH s ms Hse Hws.
    eapply IH; [apply se_cons; exact Hse | exact Hws].
  - intros s ms Hse H. exact I.
  - intros u ts IHu IHts s ms Hse [Hu Hts].
    split; [eapply IHu|eapply IHts]; eassumption.
Qed.

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
       List.map (shift_tm a cutoff) ts = ts)).
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
  - intros E nb Ts T_B T_R op body IHop IHb c a cutoff Hfv Hle. simpl in Hfv |- *.
    apply app_eq_nil in Hfv as [Hop Hb].
    rewrite (IHop (c + 2) a (cutoff + 2) Hop); [|lia].
    rewrite (IHb (S c) a (S cutoff) Hb); [|lia]. reflexivity.
  - intros t Ss A_ret arg IHt IHa c a cutoff Hfv Hle. simpl in Hfv |- *.
    apply app_eq_nil in Hfv as [Ht Ha].
    rewrite (IHt c a cutoff Ht Hle), (IHa c a cutoff Ha Hle). reflexivity.
  - intros E_tag m nb Ts T_R op IHop c a cutoff Hfv Hle. simpl in Hfv |- *.
    rewrite (IHop (c + 2) a (cutoff + 2) Hfv); [reflexivity|lia].
  - intros m T_B T_R body IH c a cutoff Hfv Hle. simpl in Hfv |- *.
    rewrite (IH c a cutoff Hfv Hle). reflexivity.
  - intros c a cutoff _ _. reflexivity.
  - intros u ts IHu IHts c a cutoff Hfv Hle. simpl in Hfv.
    apply app_eq_nil in Hfv as [Hu Hts].
    simpl. rewrite (IHu c a cutoff Hu Hle), (IHts c a cutoff Hts Hle). reflexivity.
Qed.

Lemma subst_tm_closed_id : forall t c var r,
  free_tm_vars c t = [] -> c <= var -> subst_tm var r t = t.
Proof.
  apply (term_list_ind
    (fun t => forall c var r,
       free_tm_vars c t = [] -> c <= var -> subst_tm var r t = t)
    (fun ts => forall c var r,
       List.concat (List.map (free_tm_vars c) ts) = [] -> c <= var ->
       List.map (subst_tm var r) ts = ts)).
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
  - intros E nb Ts T_B T_R op body IHop IHb c var r Hfv Hle. simpl in Hfv |- *.
    apply app_eq_nil in Hfv as [Hop Hb].
    rewrite (IHop (c + 2) (var + 2) _ Hop); [|lia].
    rewrite (IHb (S c) (S var) _ Hb); [|lia]. reflexivity.
  - intros t Ss A_ret arg IHt IHa c var r Hfv Hle. simpl in Hfv |- *.
    apply app_eq_nil in Hfv as [Ht Ha].
    rewrite (IHt c var _ Ht Hle), (IHa c var _ Ha Hle). reflexivity.
  - intros E_tag m nb Ts T_R op IHop c var r Hfv Hle. simpl in Hfv |- *.
    rewrite (IHop (c + 2) (var + 2) _ Hfv); [reflexivity|lia].
  - intros m T_B T_R body IH c var r Hfv Hle. simpl in Hfv |- *.
    rewrite (IH c var _ Hfv Hle). reflexivity.
  - intros c var r _ _. reflexivity.
  - intros u ts IHu IHts c var r Hfv Hle. simpl in Hfv.
    apply app_eq_nil in Hfv as [Hu Hts].
    simpl. rewrite (IHu c var _ Hu Hle), (IHts c var _ Hts Hle). reflexivity.
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
       well_scoped_list ms (List.map (shift_tm a cutoff) ts))).
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
  - intros E nb Ts T_B T_R op body IHop IHb ms a cutoff [Hop Hb]. cbn [shift_tm].
    split; [apply IHop; exact Hop | apply IHb; exact Hb].
  - intros t Ss A_ret arg IHt IHa ms a cutoff [Ht Ha]. cbn [shift_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m nb Ts T_R op IHop ms a cutoff [Hin Hws]. cbn [shift_tm].
    split; [exact Hin | apply IHop; exact Hws].
  - intros m T_B T_R body IH ms a cutoff Hws. cbn [shift_tm]. apply IH; exact Hws.
  - intros ms a cutoff _. exact I.
  - intros u ts IHu IHts ms a cutoff [Hu Hts].
    split; [apply IHu|apply IHts]; assumption.
Qed.

Lemma well_scoped_shift_ty_in_tm : forall t ms a cutoff,
  well_scoped ms t -> well_scoped ms (shift_ty_in_tm a cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall ms a cutoff,
       well_scoped ms t -> well_scoped ms (shift_ty_in_tm a cutoff t))
    (fun ts => forall ms a cutoff,
       well_scoped_list ms ts ->
       well_scoped_list ms (List.map (shift_ty_in_tm a cutoff) ts))).
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
  - intros E nb Ts T_B T_R op body IHop IHb ms a cutoff [Hop Hb]. cbn [shift_ty_in_tm].
    split; [apply IHop; exact Hop | apply IHb; exact Hb].
  - intros t Ss A_ret arg IHt IHa ms a cutoff [Ht Ha]. cbn [shift_ty_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m nb Ts T_R op IHop ms a cutoff [Hin Hws]. cbn [shift_ty_in_tm].
    split; [exact Hin | apply IHop; exact Hws].
  - intros m T_B T_R body IH ms a cutoff Hws. cbn [shift_ty_in_tm]. apply IH; exact Hws.
  - intros ms a cutoff _. exact I.
  - intros u ts IHu IHts ms a cutoff [Hu Hts].
    split; [apply IHu|apply IHts]; assumption.
Qed.

Lemma well_scoped_shift_lt_in_tm : forall t ms a cutoff,
  well_scoped ms t -> well_scoped ms (shift_lt_in_tm a cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall ms a cutoff,
       well_scoped ms t -> well_scoped ms (shift_lt_in_tm a cutoff t))
    (fun ts => forall ms a cutoff,
       well_scoped_list ms ts ->
       well_scoped_list ms (List.map (shift_lt_in_tm a cutoff) ts))).
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
  - intros E nb Ts T_B T_R op body IHop IHb ms a cutoff [Hop Hb]. cbn [shift_lt_in_tm].
    split; [apply IHop; exact Hop | apply IHb; exact Hb].
  - intros t Ss A_ret arg IHt IHa ms a cutoff [Ht Ha]. cbn [shift_lt_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m nb Ts T_R op IHop ms a cutoff [Hin Hws]. cbn [shift_lt_in_tm].
    split; [exact Hin | apply IHop; exact Hws].
  - intros m T_B T_R body IH ms a cutoff Hws. cbn [shift_lt_in_tm]. apply IH; exact Hws.
  - intros ms a cutoff _. exact I.
  - intros u ts IHu IHts ms a cutoff [Hu Hts].
    split; [apply IHu|apply IHts]; assumption.
Qed.


Lemma rt_closed_shift_ty_in_tm : forall t a cutoff,
  rt_closed t -> rt_closed (shift_ty_in_tm a cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall a cutoff, rt_closed t -> rt_closed (shift_ty_in_tm a cutoff t))
    (fun ts => forall a cutoff,
       rt_closed_list ts -> rt_closed_list (List.map (shift_ty_in_tm a cutoff) ts))).
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
  - intros E nb Ts T_B T_R op body IHop IHb a cutoff [Hop Hb]. cbn [shift_ty_in_tm].
    split; [apply IHop; exact Hop | apply IHb; exact Hb].
  - intros t Ss A_ret arg IHt IHa a cutoff [Ht Ha]. cbn [shift_ty_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m nb Ts T_R op IHop a cutoff [Hfv Hrt]. cbn [shift_ty_in_tm].
    split; [rewrite free_tm_vars_shift_ty_in_tm_any; exact Hfv | apply IHop; exact Hrt].
  - intros m T_B T_R body IH a cutoff Hrt. cbn [shift_ty_in_tm]. apply IH; exact Hrt.
  - intros a cutoff _. exact I.
  - intros u ts IHu IHts a cutoff [Hu Hts].
    split; [apply IHu|apply IHts]; assumption.
Qed.

Lemma rt_closed_shift_lt_in_tm : forall t a cutoff,
  rt_closed t -> rt_closed (shift_lt_in_tm a cutoff t).
Proof.
  apply (term_list_ind
    (fun t => forall a cutoff, rt_closed t -> rt_closed (shift_lt_in_tm a cutoff t))
    (fun ts => forall a cutoff,
       rt_closed_list ts -> rt_closed_list (List.map (shift_lt_in_tm a cutoff) ts))).
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
  - intros E nb Ts T_B T_R op body IHop IHb a cutoff [Hop Hb]. cbn [shift_lt_in_tm].
    split; [apply IHop; exact Hop | apply IHb; exact Hb].
  - intros t Ss A_ret arg IHt IHa a cutoff [Ht Ha]. cbn [shift_lt_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m nb Ts T_R op IHop a cutoff [Hfv Hrt]. cbn [shift_lt_in_tm].
    split; [rewrite free_tm_vars_shift_lt_in_tm_any; exact Hfv | apply IHop; exact Hrt].
  - intros m T_B T_R body IH a cutoff Hrt. cbn [shift_lt_in_tm]. apply IH; exact Hrt.
  - intros a cutoff _. exact I.
  - intros u ts IHu IHts a cutoff [Hu Hts].
    split; [apply IHu|apply IHts]; assumption.
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
       well_scoped_list ms (List.map (subst_tm var w) ts))).
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
  - intros E nb Ts T_B T_R op body IHop IHb var w ms [Hrop Hrb] Hfw Hww [Hop Hb].
    cbn [subst_tm].
    rewrite (shift_tm_closed_id w 0 2 0 Hfw) by lia.
    rewrite (shift_tm_closed_id w 0 1 0 Hfw) by lia.
    split; [apply IHop; assumption | apply IHb; assumption].
  - intros t Ss A_ret arg IHt IHa var w ms [Hrt Hra] Hfw Hww [Ht Ha]. cbn [subst_tm].
    split; [apply IHt; assumption | apply IHa; assumption].
  - intros E_tag m nb Ts T_R op IHop var w ms [Hfv2 Hrop] Hfw Hww [Hin Hws].
    cbn [subst_tm].
    rewrite (subst_tm_closed_id op 2 (var + 2) (shift_tm 2 0 w) Hfv2) by lia.
    split; [exact Hin | exact Hws].
  - intros m T_B T_R body IH var w ms Hrt Hfw Hww Hws. cbn [subst_tm].
    apply IH; try assumption.
    apply (well_scoped_mono w ms (m :: ms)); [apply se_top; apply se_refl | exact Hww].
  - intros var w ms _ _ _ _. exact I.
  - intros u ts IHu IHts var w ms [Hru Hrts] Hfw Hww [Hu Hts].
    split; [apply IHu|apply IHts]; assumption.
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
       rt_closed_list (List.map (subst_tm var w) ts))).
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
  - intros E nb Ts T_B T_R op body IHop IHb var w [Hrop Hrb] Hfw Hrw.
    cbn [subst_tm].
    rewrite (shift_tm_closed_id w 0 2 0 Hfw) by lia.
    rewrite (shift_tm_closed_id w 0 1 0 Hfw) by lia.
    split; [apply IHop; assumption | apply IHb; assumption].
  - intros t Ss A_ret arg IHt IHa var w [Hrt Hra] Hfw Hrw. cbn [subst_tm].
    split; [apply IHt; assumption | apply IHa; assumption].
  - intros E_tag m nb Ts T_R op IHop var w [Hfv2 Hrop] Hfw Hrw. cbn [subst_tm].
    rewrite (subst_tm_closed_id op 2 (var + 2) (shift_tm 2 0 w) Hfv2) by lia.
    split; assumption.
  - intros m T_B T_R body IH var w Hrt Hfw Hrw. cbn [subst_tm].
    apply IH; assumption.
  - intros var w _ _ _. exact I.
  - intros u ts IHu IHts var w [Hru Hrts] Hfw Hrw.
    split; [apply IHu|apply IHts]; assumption.
Qed.

(* Type substitution preserves well_scoped (it never touches markers). *)
Lemma well_scoped_subst_ty_in_tm : forall t var R ms,
  well_scoped ms t -> well_scoped ms (subst_ty_in_tm var R t).
Proof.
  apply (term_list_ind
    (fun t => forall var R ms, well_scoped ms t -> well_scoped ms (subst_ty_in_tm var R t))
    (fun ts => forall var R ms, well_scoped_list ms ts ->
       well_scoped_list ms (List.map (subst_ty_in_tm var R) ts))).
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
      with (term_ctor K l lts (subst_ty_list var R Ts) (List.map (subst_ty_in_tm var R) ts))
      by (cbn [subst_ty_in_tm]; rewrite subst_ty_in_tm_go_eq_map; reflexivity).
    rewrite well_scoped_ctor_eq. apply IH. rewrite well_scoped_ctor_eq in Hws. exact Hws.
  - intros scrut tag nlt ar y n IHs IHy IHn var R ms [Hs [Hy Hn]]. cbn [subst_ty_in_tm].
    split; [apply IHs; exact Hs | split; [apply IHy; exact Hy | apply IHn; exact Hn]].
  - intros E nb Ts T_B T_R op body IHop IHb var R ms [Hop Hb]. cbn [subst_ty_in_tm].
    split; [apply IHop; exact Hop | apply IHb; exact Hb].
  - intros t Ss A_ret arg IHt IHa var R ms [Ht Ha]. cbn [subst_ty_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m nb Ts T_R op IHop var R ms [Hin Hws]. cbn [subst_ty_in_tm].
    split; [exact Hin | apply IHop; exact Hws].
  - intros m T_B T_R body IH var R ms Hws. cbn [subst_ty_in_tm]. apply IH; exact Hws.
  - intros var R ms _. exact I.
  - intros u ts IHu IHts var R ms [Hu Hts]. split; [apply IHu|apply IHts]; assumption.
Qed.

(* Lifetime substitution preserves well_scoped. *)
Lemma well_scoped_subst_lt_in_tm : forall t var R ms,
  well_scoped ms t -> well_scoped ms (subst_lt_in_tm var R t).
Proof.
  apply (term_list_ind
    (fun t => forall var R ms, well_scoped ms t -> well_scoped ms (subst_lt_in_tm var R t))
    (fun ts => forall var R ms, well_scoped_list ms ts ->
       well_scoped_list ms (List.map (subst_lt_in_tm var R) ts))).
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
  - intros E nb Ts T_B T_R op body IHop IHb var R ms [Hop Hb]. cbn [subst_lt_in_tm].
    split; [apply IHop; exact Hop | apply IHb; exact Hb].
  - intros t Ss A_ret arg IHt IHa var R ms [Ht Ha]. cbn [subst_lt_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m nb Ts T_R op IHop var R ms [Hin Hws]. cbn [subst_lt_in_tm].
    split; [exact Hin | apply IHop; exact Hws].
  - intros m T_B T_R body IH var R ms Hws. cbn [subst_lt_in_tm]. apply IH; exact Hws.
  - intros var R ms _. exact I.
  - intros u ts IHu IHts var R ms [Hu Hts]. split; [apply IHu|apply IHts]; assumption.
Qed.

(* rt_closed is preserved by type/lifetime substitution. *)
Lemma rt_closed_subst_ty_in_tm : forall t var R,
  rt_closed t -> rt_closed (subst_ty_in_tm var R t).
Proof.
  apply (term_list_ind
    (fun t => forall var R, rt_closed t -> rt_closed (subst_ty_in_tm var R t))
    (fun ts => forall var R, rt_closed_list ts ->
       rt_closed_list (List.map (subst_ty_in_tm var R) ts))).
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
      with (term_ctor K l lts (subst_ty_list var R Ts) (List.map (subst_ty_in_tm var R) ts))
      by (cbn [subst_ty_in_tm]; rewrite subst_ty_in_tm_go_eq_map; reflexivity).
    rewrite rt_closed_ctor_eq. apply IH. rewrite rt_closed_ctor_eq in H. exact H.
  - intros scrut tag nlt ar y n IHs IHy IHn var R [Hs [Hy Hn]]. cbn [subst_ty_in_tm].
    split; [apply IHs; exact Hs | split; [apply IHy; exact Hy | apply IHn; exact Hn]].
  - intros E nb Ts T_B T_R op body IHop IHb var R [Hop Hb]. cbn [subst_ty_in_tm].
    split; [apply IHop; exact Hop | apply IHb; exact Hb].
  - intros t Ss A_ret arg IHt IHa var R [Ht Ha]. cbn [subst_ty_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m nb Ts T_R op IHop var R [Hfv Hrt]. cbn [subst_ty_in_tm].
    split; [rewrite free_tm_vars_subst_ty_in_tm; exact Hfv | apply IHop; exact Hrt].
  - intros m T_B T_R body IH var R Hrt. cbn [subst_ty_in_tm]. apply IH; exact Hrt.
  - intros var R _. exact I.
  - intros u ts IHu IHts var R [Hu Hts]. split; [apply IHu|apply IHts]; assumption.
Qed.

Lemma rt_closed_subst_lt_in_tm : forall t var R,
  rt_closed t -> rt_closed (subst_lt_in_tm var R t).
Proof.
  apply (term_list_ind
    (fun t => forall var R, rt_closed t -> rt_closed (subst_lt_in_tm var R t))
    (fun ts => forall var R, rt_closed_list ts ->
       rt_closed_list (List.map (subst_lt_in_tm var R) ts))).
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
  - intros E nb Ts T_B T_R op body IHop IHb var R [Hop Hb]. cbn [subst_lt_in_tm].
    split; [apply IHop; exact Hop | apply IHb; exact Hb].
  - intros t Ss A_ret arg IHt IHa var R [Ht Ha]. cbn [subst_lt_in_tm].
    split; [apply IHt; exact Ht | apply IHa; exact Ha].
  - intros E_tag m nb Ts T_R op IHop var R [Hfv Hrt]. cbn [subst_lt_in_tm].
    split; [rewrite free_tm_vars_subst_lt_in_tm; exact Hfv | apply IHop; exact Hrt].
  - intros m T_B T_R body IH var R Hrt. cbn [subst_lt_in_tm]. apply IH; exact Hrt.
  - intros var R _. exact I.
  - intros u ts IHu IHts var R [Hu Hts]. split; [apply IHu|apply IHts]; assumption.
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
(* Plug lemmas: closedness and the v2 invariants through an ectx.       *)
(* No ectx frame crosses a term binder, so all hole positions sit at    *)
(* term-cutoff 0.                                                       *)
(* ==================================================================== *)

Lemma free_tm_vars_plug_nil_inv : forall E r,
  free_tm_vars 0 (plug E r) = [] -> free_tm_vars 0 r = [].
Proof.
  induction E as
    [ | E1 IHE ta | ta E1 IHE | E1 IHE Ty | E1 IHE lt
    | tag dl lts Tys vs E1 IHE ts | E1 IHE K nlt ar yes no
    | mk TB TR E1 IHE | E1 IHE Ss An ar2 | rcv Ss An E1 IHE ];
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
    | mk TB TR E1 IHE | E1 IHE Ss An ar2 | rcv Ss An E1 IHE ];
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
    | mk TB TR E1 IHE | E1 IHE Ss An ar2 | rcv Ss An E1 IHE ];
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
(* v2 confinement: the H_Perform facts, now returning full              *)
(* well-scopedness of the op-body at the scope OUTSIDE the delimiter    *)
(* (v1 only delivered marker_ok there).                                 *)
(* ==================================================================== *)

Lemma well_scoped_pure_cap_confined :
  forall P m ms E_tag nb Ts T_R op_body Ss A v,
  pure_ectx_m m P ->
  well_scoped ms (plug P (term_perform (term_cap E_tag m nb Ts T_R op_body) Ss A v)) ->
  well_scoped (scope_below m ms) op_body.
Proof.
  intros P m ms E_tag nb Ts T_R op_body Ss A v Hpure. revert ms.
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
  forall ms m T_B T_R E_tag nb Ts T_R' op_body Ss A v P,
  well_scoped ms (term_handler_m m T_B T_R
    (plug P (term_perform (term_cap E_tag m nb Ts T_R' op_body) Ss A v))) ->
  pure_ectx_m m P ->
  well_scoped ms op_body.
Proof.
  intros ms m T_B T_R E_tag nb Ts T_R' op_body Ss A v P Hws Hpure.
  pose proof (well_scoped_pure_cap_confined P m (m :: ms) E_tag nb Ts T_R' op_body Ss A v
    Hpure Hws) as Hc.
  rewrite scope_below_cons_eq in Hc. exact Hc.
Qed.

(* ==================================================================== *)
(* Stage-5 support: list bridges, closed-substitution fv laws, plug     *)
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
    | mk TB TR E1 IHE | E1 IHE Ss An ar2 | rcv Ss An E1 IHE ];
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
Lemma resume_body_closed_rt : forall P r,
  free_tm_vars 0 (plug P r) = [] ->
  rt_closed (plug P r) ->
  free_tm_vars 1 (plug (shift_ectx_tm 1 0 P) (term_var 0)) = [] /\
  rt_closed (plug (shift_ectx_tm 1 0 P) (term_var 0)).
Proof.
  induction P as
    [ | E1 IHE ta | ta E1 IHE | E1 IHE Ty | E1 IHE lt
    | tag dl lts Tys vs E1 IHE ts | E1 IHE K nlt ar yes no
    | mk TB TR E1 IHE | E1 IHE Ss An ar2 | rcv Ss An E1 IHE ];
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
    | mk TB TR E1 IHE | E1 IHE Ss An ar2 | rcv Ss An E1 IHE ];
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
