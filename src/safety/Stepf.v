Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Semantics.
Require Import ShiftLaws.
Require Import Markers.

(* ================================================================== *)
(* A certified executable evaluator for the step relation.            *)
(*                                                                    *)
(* [step] (Semantics.v) is a relation: S_HandleCtx allocates an       *)
(* ARBITRARY globally fresh marker, and H_Perform quantifies over a   *)
(* captured pure context.  This file gives a computable one-step      *)
(* function [stepf : term -> option term] implementing the canonical  *)
(* left-to-right call-by-value strategy, with the delimiter marker of *)
(* a reducing handle chosen as [marker_bound <whole program>] — the   *)
(* same canonical witness Progress.v uses (progress_open_safe,        *)
(* T_Handle case).                                                    *)
(*                                                                    *)
(* Soundness ([stepf_sound]) says every Some-result is a real step;   *)
(* it needs no typing hypotheses.  The evaluator mirrors the shape of *)
(* the progress proof: the recursive descent returns a four-way       *)
(* verdict (value / stepped / perform-escape / stuck), where the      *)
(* escape verdict carries the components of a                         *)
(* [perform_escape]-style redex (compare Progress.v) so that the      *)
(* enclosing matching delimiter can fire H_Perform.                   *)
(*                                                                    *)
(* H_Perform requires its captured context to be both marker-pure    *)
(* and value-disciplined ([ectx_wf]), so the fresh-marker choice is   *)
(* the only one-step nondeterminism; completeness of [stepf] modulo   *)
(* marker renaming is developed on top of MarkerRename.v.             *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(* Boolean equality on lifetimes and types                            *)
(*                                                                    *)
(* H_Perform only fires when the capability's answer-type annotation  *)
(* coincides syntactically with the delimiter's T_R (on reachable     *)
(* terms marker_types_safe guarantees this; the evaluator must check  *)
(* it on arbitrary terms).  Only the soundness direction              *)
(* (eqb = true -> eq) is needed by stepf_sound.                       *)
(* ------------------------------------------------------------------ *)

Fixpoint lt_eqb (l1 l2 : lifetime) : bool :=
  match l1, l2 with
  | lt_var n1, lt_var n2 => Nat.eqb n1 n2
  | lt_free, lt_free => true
  | lt_local, lt_local => true
  | lt_min a1 b1, lt_min a2 b2 => andb (lt_eqb a1 a2) (lt_eqb b1 b2)
  | _, _ => false
  end.

Lemma lt_eqb_eq : forall l1 l2, lt_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [n| | |a IHa b IHb]; destruct l2; simpl; intros H;
    try discriminate H; try reflexivity.
  - apply Nat.eqb_eq in H. subst. reflexivity.
  - apply Bool.andb_true_iff in H as [H1 H2].
    rewrite (IHa _ H1), (IHb _ H2). reflexivity.
Qed.

Fixpoint ty_eqb (T1 T2 : type) : bool :=
  let fix go (Ts1 Ts2 : list type) : bool :=
    match Ts1, Ts2 with
    | [], [] => true
    | A :: r1, B :: r2 => andb (ty_eqb A B) (go r1 r2)
    | _, _ => false
    end
  in
  match T1, T2 with
  | type_var n1, type_var n2 => Nat.eqb n1 n2
  | type_fun A1 l1 B1, type_fun A2 l2 B2 =>
      andb (ty_eqb A1 A2) (andb (lt_eqb l1 l2) (ty_eqb B1 B2))
  | type_ctor K1 l1 Ts1, type_ctor K2 l2 Ts2 =>
      andb (Nat.eqb K1 K2) (andb (lt_eqb l1 l2) (go Ts1 Ts2))
  | type_lt_all A1, type_lt_all A2 => ty_eqb A1 A2
  | type_ty_all B1 A1, type_ty_all B2 A2 =>
      andb (ty_eqb B1 B2) (ty_eqb A1 A2)
  | _, _ => false
  end.

Fixpoint ty_list_eqb (Ts1 Ts2 : list type) : bool :=
  match Ts1, Ts2 with
  | [], [] => true
  | A :: r1, B :: r2 => andb (ty_eqb A B) (ty_list_eqb r1 r2)
  | _, _ => false
  end.

(* go_eq lemma in the style of shift_tm_go_eq_map (ShiftLaws.v). *)
Lemma ty_eqb_go_eq : forall Ts1 Ts2,
  (fix go (Ts1 Ts2 : list type) : bool :=
     match Ts1, Ts2 with
     | [], [] => true
     | A :: r1, B :: r2 => andb (ty_eqb A B) (go r1 r2)
     | _, _ => false
     end) Ts1 Ts2 = ty_list_eqb Ts1 Ts2.
Proof.
  intros Ts1 Ts2. reflexivity.
Qed.

Lemma ty_eqb_eq : forall T1 T2, ty_eqb T1 T2 = true -> T1 = T2.
Proof.
  apply (type_list_ind
    (fun T1 => forall T2, ty_eqb T1 T2 = true -> T1 = T2)
    (fun Ts1 => forall Ts2, ty_list_eqb Ts1 Ts2 = true -> Ts1 = Ts2)).
  - intros n T2 H; destruct T2; simpl in H; try discriminate.
    apply Nat.eqb_eq in H; subst; reflexivity.
  - intros A l B IHA IHB T2 H; destruct T2; simpl in H; try discriminate.
    apply Bool.andb_true_iff in H as [H1 H23].
    apply Bool.andb_true_iff in H23 as [H2 H3].
    rewrite (IHA _ H1), (lt_eqb_eq _ _ H2), (IHB _ H3). reflexivity.
  - intros K l Ts IHTs T2 H; destruct T2 as [| |K2 l2 Ts2| |]; simpl in H;
      try discriminate.
    rewrite ty_eqb_go_eq in H.
    apply Bool.andb_true_iff in H as [H1 H23].
    apply Bool.andb_true_iff in H23 as [H2 H3].
    apply Nat.eqb_eq in H1.
    rewrite H1, (lt_eqb_eq _ _ H2), (IHTs _ H3). reflexivity.
  - intros A IHA T2 H; destruct T2; simpl in H; try discriminate.
    rewrite (IHA _ H). reflexivity.
  - intros B A IHB IHA T2 H; destruct T2; simpl in H; try discriminate.
    apply Bool.andb_true_iff in H as [H1 H2].
    rewrite (IHB _ H1), (IHA _ H2). reflexivity.
  - intros Ts2 H; destruct Ts2; simpl in H; [reflexivity | discriminate].
  - intros A Ts IHA IHTs Ts2 H; destruct Ts2; simpl in H; try discriminate.
    apply Bool.andb_true_iff in H as [H1 H2].
    rewrite (IHA _ H1), (IHTs _ H2). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Evaluator verdicts                                                 *)
(*                                                                    *)
(* The descent classifies a subterm as a value, a term that stepped   *)
(* (returning the whole stepped subterm), a perform-escape (the       *)
(* third disjunct of Progress.v's progress_result: a redex            *)
(*   plug P (perform (cap E m n_beta Ts T_R op_body) Ss A v)         *)
(* with P pure for m, waiting for the matching delimiter), or stuck.  *)
(* ------------------------------------------------------------------ *)

Record esc_info : Type := mk_esc {
  esc_eff  : eff_tag;
  esc_mk   : marker;
  esc_Ts   : list type;
  esc_TR   : type;
  esc_ops  : list (nat * term);
  esc_opix : nat;
  esc_Ss   : list type;
  esc_A    : type;
  esc_arg  : term
}.

(* The escaping perform-redex an esc_info denotes. *)
Definition esc_redex (e : esc_info) : term :=
  term_perform
    (term_cap (esc_eff e) (esc_mk e) (esc_Ts e) (esc_TR e) (esc_ops e))
    (esc_opix e) (esc_Ss e) (esc_A e) (esc_arg e).

Inductive stepf_res : Type :=
  | SR_val   : stepf_res
  | SR_step  : term -> stepf_res
  | SR_esc   : esc_info -> ectx -> stepf_res
  | SR_stuck : stepf_res.

(* List verdicts, for constructor-argument spines: all values, one    *)
(* stepped (returning the whole new spine), an escape at one element  *)
(* (values before / pure ectx of the escapee / elements after), or    *)
(* stuck.                                                             *)
Inductive lstep_res : Type :=
  | LR_vals  : lstep_res
  | LR_step  : list term -> lstep_res
  | LR_esc   : esc_info -> list term -> ectx -> list term -> lstep_res
  | LR_stuck : lstep_res.

(* ------------------------------------------------------------------ *)
(* The one-step function                                              *)
(*                                                                    *)
(* [fresh] is a marker fresh for the WHOLE program, supplied at the   *)
(* top by [stepf] as [marker_bound t]; a handle in redex position     *)
(* allocates it.  (At most one redex fires per call, so a single      *)
(* fresh marker suffices.)                                            *)
(* ------------------------------------------------------------------ *)

Fixpoint stepf_go (fresh : marker) (t : term) : stepf_res :=
  let fix go_list (ts : list term) : lstep_res :=
    match ts with
    | [] => LR_vals
    | u :: rest =>
        match stepf_go fresh u with
        | SR_val =>
            match go_list rest with
            | LR_vals => LR_vals
            | LR_step rest' => LR_step (u :: rest')
            | LR_esc e vsl P vsr => LR_esc e (u :: vsl) P vsr
            | LR_stuck => LR_stuck
            end
        | SR_step u' => LR_step (u' :: rest)
        | SR_esc e P => LR_esc e [] P rest
        | SR_stuck => LR_stuck
        end
    end
  in
  match t with
  | term_var _ => SR_stuck
  | term_lam _ _ => SR_val
  | term_ty_lam _ _ => SR_val
  | term_lt_lam _ => SR_val
  | term_cap _ _ _ _ _ => SR_val
  | term_app t1 t2 =>
      match stepf_go fresh t1 with
      | SR_val =>
          match stepf_go fresh t2 with
          | SR_val =>
              match t1 with
              | term_lam body T => SR_step (subst_tm 0 t2 body)
              | _ => SR_stuck
              end
          | SR_step t2' => SR_step (term_app t1 t2')
          | SR_esc e P => SR_esc e (EC_app2 t1 P)
          | SR_stuck => SR_stuck
          end
      | SR_step t1' => SR_step (term_app t1' t2)
      | SR_esc e P => SR_esc e (EC_app1 P t2)
      | SR_stuck => SR_stuck
      end
  | term_ty_app t1 T =>
      match stepf_go fresh t1 with
      | SR_val =>
          match t1 with
          | term_ty_lam bound body => SR_step (subst_ty_in_tm 0 T body)
          | _ => SR_stuck
          end
      | SR_step t1' => SR_step (term_ty_app t1' T)
      | SR_esc e P => SR_esc e (EC_ty_app P T)
      | SR_stuck => SR_stuck
      end
  | term_lt_app t1 l =>
      match stepf_go fresh t1 with
      | SR_val =>
          match t1 with
          | term_lt_lam body => SR_step (subst_lt_in_tm 0 l body)
          | _ => SR_stuck
          end
      | SR_step t1' => SR_step (term_lt_app t1' l)
      | SR_esc e P => SR_esc e (EC_lt_app P l)
      | SR_stuck => SR_stuck
      end
  | term_ctor K l lts Ts ts =>
      match go_list ts with
      | LR_vals => SR_val
      | LR_step ts' => SR_step (term_ctor K l lts Ts ts')
      | LR_esc e vsl P vsr => SR_esc e (EC_ctor K l lts Ts vsl P vsr)
      | LR_stuck => SR_stuck
      end
  | term_match scrut K n_lt arity yes_body no_body =>
      match stepf_go fresh scrut with
      | SR_val =>
          match scrut with
          | term_ctor K' l lts Ts vs =>
              if Nat.eqb K' K
              then if Nat.eqb arity (List.length vs)
                   then SR_step (subst_list_tm vs (subst_list_lt_in_tm lts yes_body))
                   else SR_stuck
              else SR_step no_body
          | _ => SR_stuck
          end
      | SR_step s' => SR_step (term_match s' K n_lt arity yes_body no_body)
      | SR_esc e P => SR_esc e (EC_match P K n_lt arity yes_body no_body)
      | SR_stuck => SR_stuck
      end
  | term_handle E_tag Ts T_B T_R op_bodies body =>
      SR_step (term_handler_m fresh T_B T_R
                 (subst_tm 0 (term_cap E_tag fresh Ts T_R op_bodies) body))
  | term_perform recv op Ss A arg =>
      match stepf_go fresh recv with
      | SR_val =>
          match stepf_go fresh arg with
          | SR_val =>
              match recv with
              | term_cap E_tag m Ts T_R op_bodies =>
                  SR_esc (mk_esc E_tag m Ts T_R op_bodies op Ss A arg) EC_hole
              | _ => SR_stuck
              end
          | SR_step a' => SR_step (term_perform recv op Ss A a')
          | SR_esc e P => SR_esc e (EC_perform_a recv op Ss A P)
          | SR_stuck => SR_stuck
          end
      | SR_step r' => SR_step (term_perform r' op Ss A arg)
      | SR_esc e P => SR_esc e (EC_perform_r P op Ss A arg)
      | SR_stuck => SR_stuck
      end
  | term_handler_m m0 T_B T_R body =>
      match stepf_go fresh body with
      | SR_val => SR_step body
      | SR_step b' => SR_step (term_handler_m m0 T_B T_R b')
      | SR_esc e P =>
          if Nat.eqb (esc_mk e) m0
          then if ty_eqb (esc_TR e) T_R
               then match nth_error (esc_ops e) (esc_opix e) with
                    | Some (n_beta, op_body) =>
                        SR_step
                          (subst_list_tm
                             [esc_arg e;
                              term_lam (term_handler_m m0 T_B T_R
                                          (plug (shift_ectx_tm 1 0 P) (term_var 0)))
                                       (esc_A e)]
                             (subst_list_ty_in_tm (esc_Ss e) op_body))
                    | None => SR_stuck
                    end
               else SR_stuck
          else SR_esc e (EC_handler_m m0 T_B T_R P)
      | SR_stuck => SR_stuck
      end
  end.

(* Top-level list variant of the constructor-spine descent, plus the  *)
(* usual go-eq unfolding lemma for the inner fix (same pattern as     *)
(* shift_tm_go_eq_map in ShiftLaws.v).                                *)
Fixpoint stepf_list (fresh : marker) (ts : list term) : lstep_res :=
  match ts with
  | [] => LR_vals
  | u :: rest =>
      match stepf_go fresh u with
      | SR_val =>
          match stepf_list fresh rest with
          | LR_vals => LR_vals
          | LR_step rest' => LR_step (u :: rest')
          | LR_esc e vsl P vsr => LR_esc e (u :: vsl) P vsr
          | LR_stuck => LR_stuck
          end
      | SR_step u' => LR_step (u' :: rest)
      | SR_esc e P => LR_esc e [] P rest
      | SR_stuck => LR_stuck
      end
  end.

Lemma stepf_go_list_eq : forall fresh ts,
  (fix go_list (ts : list term) : lstep_res :=
     match ts with
     | [] => LR_vals
     | u :: rest =>
         match stepf_go fresh u with
         | SR_val =>
             match go_list rest with
             | LR_vals => LR_vals
             | LR_step rest' => LR_step (u :: rest')
             | LR_esc e vsl P vsr => LR_esc e (u :: vsl) P vsr
             | LR_stuck => LR_stuck
             end
         | SR_step u' => LR_step (u' :: rest)
         | SR_esc e P => LR_esc e [] P rest
         | SR_stuck => LR_stuck
         end
     end) ts = stepf_list fresh ts.
Proof.
  intros fresh. induction ts as [|u rest IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma stepf_go_ctor_eq : forall fresh K l lts Ts ts,
  stepf_go fresh (term_ctor K l lts Ts ts) =
  match stepf_list fresh ts with
  | LR_vals => SR_val
  | LR_step ts' => SR_step (term_ctor K l lts Ts ts')
  | LR_esc e vsl P vsr => SR_esc e (EC_ctor K l lts Ts vsl P vsr)
  | LR_stuck => SR_stuck
  end.
Proof.
  intros fresh K l lts Ts ts. simpl.
  rewrite stepf_go_list_eq. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The evaluator: choose the globally fresh marker up front.          *)
(* ------------------------------------------------------------------ *)

Definition stepf (t : term) : option term :=
  match stepf_go (marker_bound t) t with
  | SR_step u => Some u
  | _ => None
  end.

(* ------------------------------------------------------------------ *)
(* Soundness                                                          *)
(*                                                                    *)
(* The invariant of the descent, mirroring progress_result:           *)
(*   SR_val   -> the subterm is a value;                              *)
(*   SR_step  -> the subterm decomposes as plug E r with r either a   *)
(*               head redex or a handle allocating [fresh];           *)
(*   SR_esc   -> the subterm is a perform-escape under a pure,        *)
(*               well-formed context.                                 *)
(* SR_stuck carries no claim.                                         *)
(* ------------------------------------------------------------------ *)

Definition handle_alloc (fresh : marker) (r r' : term) : Prop :=
  exists E_tag Ts T_B T_R op_bodies body,
    r = term_handle E_tag Ts T_B T_R op_bodies body /\
    r' = term_handler_m fresh T_B T_R
           (subst_tm 0 (term_cap E_tag fresh Ts T_R op_bodies) body).

Definition esc_ok (e : esc_info) (P : ectx) : Prop :=
  pure_ectx_m (esc_mk e) P /\ ectx_wf P /\ value (esc_arg e).

Definition go_spec (fresh : marker) (t : term) : Prop :=
  (stepf_go fresh t = SR_val -> value t) /\
  (forall u, stepf_go fresh t = SR_step u ->
     exists E r r', ectx_wf E /\ t = plug E r /\ u = plug E r' /\
       (r -->h r' \/ handle_alloc fresh r r')) /\
  (forall e P, stepf_go fresh t = SR_esc e P ->
     esc_ok e P /\ t = plug P (esc_redex e)).

Definition go_list_spec (fresh : marker) (ts : list term) : Prop :=
  (stepf_list fresh ts = LR_vals -> Forall value ts) /\
  (forall ts', stepf_list fresh ts = LR_step ts' ->
     exists vsl E r r' vsr, Forall value vsl /\ ectx_wf E /\
       ts = vsl ++ plug E r :: vsr /\ ts' = vsl ++ plug E r' :: vsr /\
       (r -->h r' \/ handle_alloc fresh r r')) /\
  (forall e vsl P vsr, stepf_list fresh ts = LR_esc e vsl P vsr ->
     esc_ok e P /\ Forall value vsl /\
     ts = vsl ++ plug P (esc_redex e) :: vsr).

(* Every conjunct of the spec that a stuck (or shape-impossible)      *)
(* verdict makes vacuous.                                             *)
Ltac spec_absurd :=
  split; [let H := fresh in intros H; discriminate H
         | split; [let H := fresh in intros ? H; discriminate H
                  | let H := fresh in intros ? ? H; discriminate H]].

Ltac lspec_absurd :=
  split; [let H := fresh in intros H; discriminate H
         | split; [let H := fresh in intros ? H; discriminate H
                  | let H := fresh in intros ? ? ? ? H; discriminate H]].

Lemma stepf_go_sound : forall fresh t, go_spec fresh t.
Proof.
  intros fresh.
  apply (term_list_ind (go_spec fresh) (go_list_spec fresh) (fun _ => True)).
  - (* term_var *)
    intros n. unfold go_spec. simpl. spec_absurd.
  - (* term_app *)
    intros t1 t2 [IH1v [IH1s IH1e]] [IH2v [IH2s IH2e]].
    unfold go_spec. simpl.
    destruct (stepf_go fresh t1) as [|t1'|e1 P1|] eqn:Hs1.
    + specialize (IH1v eq_refl).
      destruct (stepf_go fresh t2) as [|t2'|e2 P2|] eqn:Hs2.
      * (* both values: beta or stuck *)
        specialize (IH2v eq_refl).
        destruct t1 as [x|ta tb|body T1|ta T1|bound bd|ta la|bd
                       |K' l' lts' Ts' vs|s tg nl ar y n|Et Ts' TB TR ob bd
                       |rc opx Ss' A' ag|Et mm Ts' TR ob|mm TB TR bd];
          try spec_absurd.
        (* t1 = term_lam body T1 *)
        split; [intros H; discriminate H|].
        split; [|intros ? ? H; discriminate H].
        intros u Hu. injection Hu as Hu. subst u.
        exists EC_hole, (term_app (term_lam body T1) t2), (subst_tm 0 t2 body).
        split; [constructor|]. split; [reflexivity|]. split; [reflexivity|].
        left. apply H_Beta. exact IH2v.
      * (* t2 stepped *)
        split; [intros H; discriminate H|].
        split; [|intros ? ? H; discriminate H].
        intros u Hu. injection Hu as Hu. subst u.
        destruct (IH2s _ eq_refl) as (E & r & r' & HE & Ht2 & Ht2' & Hred).
        exists (EC_app2 t1 E), r, r'.
        split; [constructor; assumption|].
        split; [simpl; rewrite <- Ht2; reflexivity|].
        split; [simpl; rewrite <- Ht2'; reflexivity|]. exact Hred.
      * (* t2 escapes *)
        split; [intros H; discriminate H|].
        split; [intros ? H; discriminate H|].
        intros e P He. injection He as He1 He2. subst e P.
        destruct (IH2e _ _ eq_refl) as [[Hpure [Hwf Hv]] Heq].
        split; [split; [constructor; exact Hpure
                       |split; [constructor; assumption|exact Hv]]|].
        simpl. rewrite <- Heq. reflexivity.
      * spec_absurd.
    + (* t1 stepped *)
      split; [intros H; discriminate H|].
      split; [|intros ? ? H; discriminate H].
      intros u Hu. injection Hu as Hu. subst u.
      destruct (IH1s _ eq_refl) as (E & r & r' & HE & Ht1 & Ht1' & Hred).
      exists (EC_app1 E t2), r, r'.
      split; [constructor; assumption|].
      split; [simpl; rewrite <- Ht1; reflexivity|].
      split; [simpl; rewrite <- Ht1'; reflexivity|]. exact Hred.
    + (* t1 escapes *)
      split; [intros H; discriminate H|].
      split; [intros ? H; discriminate H|].
      intros e P He. injection He as He1 He2. subst e P.
      destruct (IH1e _ _ eq_refl) as [[Hpure [Hwf Hv]] Heq].
      split; [split; [constructor; exact Hpure
                     |split; [constructor; assumption|exact Hv]]|].
      simpl. rewrite <- Heq. reflexivity.
    + spec_absurd.
  - (* term_lam *)
    intros body T _. unfold go_spec. simpl.
    split; [intros _; constructor|].
    split; [intros ? H; discriminate H|intros ? ? H; discriminate H].
  - (* term_ty_app *)
    intros t1 T [IH1v [IH1s IH1e]].
    unfold go_spec. simpl.
    destruct (stepf_go fresh t1) as [|t1'|e1 P1|] eqn:Hs1.
    + specialize (IH1v eq_refl).
      destruct t1 as [x|ta tb|body T1|ta T1|bound bd|ta la|bd
                     |K' l' lts' Ts' vs|s tg nl ar y n|Et Ts' TB TR ob bd
                     |rc opx Ss' A' ag|Et mm Ts' TR ob|mm TB TR bd];
        try spec_absurd.
      (* t1 = term_ty_lam bound bd *)
      split; [intros H; discriminate H|].
      split; [|intros ? ? H; discriminate H].
      intros u Hu. injection Hu as Hu. subst u.
      exists EC_hole, (term_ty_app (term_ty_lam bound bd) T),
             (subst_ty_in_tm 0 T bd).
      split; [constructor|]. split; [reflexivity|]. split; [reflexivity|].
      left. apply H_TyBeta.
    + split; [intros H; discriminate H|].
      split; [|intros ? ? H; discriminate H].
      intros u Hu. injection Hu as Hu. subst u.
      destruct (IH1s _ eq_refl) as (E & r & r' & HE & Ht1 & Ht1' & Hred).
      exists (EC_ty_app E T), r, r'.
      split; [constructor; assumption|].
      split; [simpl; rewrite <- Ht1; reflexivity|].
      split; [simpl; rewrite <- Ht1'; reflexivity|]. exact Hred.
    + split; [intros H; discriminate H|].
      split; [intros ? H; discriminate H|].
      intros e P He. injection He as He1 He2. subst e P.
      destruct (IH1e _ _ eq_refl) as [[Hpure [Hwf Hv]] Heq].
      split; [split; [constructor; exact Hpure
                     |split; [constructor; assumption|exact Hv]]|].
      simpl. rewrite <- Heq. reflexivity.
    + spec_absurd.
  - (* term_ty_lam *)
    intros bound body _. unfold go_spec. simpl.
    split; [intros _; constructor|].
    split; [intros ? H; discriminate H|intros ? ? H; discriminate H].
  - (* term_lt_app *)
    intros t1 l [IH1v [IH1s IH1e]].
    unfold go_spec. simpl.
    destruct (stepf_go fresh t1) as [|t1'|e1 P1|] eqn:Hs1.
    + specialize (IH1v eq_refl).
      destruct t1 as [x|ta tb|body T1|ta T1|bound bd|ta la|bd
                     |K' l' lts' Ts' vs|s tg nl ar y n|Et Ts' TB TR ob bd
                     |rc opx Ss' A' ag|Et mm Ts' TR ob|mm TB TR bd];
        try spec_absurd.
      (* t1 = term_lt_lam bd *)
      split; [intros H; discriminate H|].
      split; [|intros ? ? H; discriminate H].
      intros u Hu. injection Hu as Hu. subst u.
      exists EC_hole, (term_lt_app (term_lt_lam bd) l), (subst_lt_in_tm 0 l bd).
      split; [constructor|]. split; [reflexivity|]. split; [reflexivity|].
      left. apply H_LtBeta.
    + split; [intros H; discriminate H|].
      split; [|intros ? ? H; discriminate H].
      intros u Hu. injection Hu as Hu. subst u.
      destruct (IH1s _ eq_refl) as (E & r & r' & HE & Ht1 & Ht1' & Hred).
      exists (EC_lt_app E l), r, r'.
      split; [constructor; assumption|].
      split; [simpl; rewrite <- Ht1; reflexivity|].
      split; [simpl; rewrite <- Ht1'; reflexivity|]. exact Hred.
    + split; [intros H; discriminate H|].
      split; [intros ? H; discriminate H|].
      intros e P He. injection He as He1 He2. subst e P.
      destruct (IH1e _ _ eq_refl) as [[Hpure [Hwf Hv]] Heq].
      split; [split; [constructor; exact Hpure
                     |split; [constructor; assumption|exact Hv]]|].
      simpl. rewrite <- Heq. reflexivity.
    + spec_absurd.
  - (* term_lt_lam *)
    intros body _. unfold go_spec. simpl.
    split; [intros _; constructor|].
    split; [intros ? H; discriminate H|intros ? ? H; discriminate H].
  - (* term_ctor *)
    intros K l lts Ts ts [IHv [IHs IHe]].
    unfold go_spec. rewrite stepf_go_ctor_eq.
    destruct (stepf_list fresh ts) as [|ts'|e vsl P vsr|] eqn:Hl.
    + split; [intros _; constructor; exact (IHv eq_refl)|].
      split; [intros ? H; discriminate H|intros ? ? H; discriminate H].
    + split; [intros H; discriminate H|].
      split; [|intros ? ? H; discriminate H].
      intros u Hu. injection Hu as Hu. subst u.
      destruct (IHs _ eq_refl)
        as (vsl & E & r & r' & vsr & Hvvsl & HE & Hts & Hts' & Hred).
      exists (EC_ctor K l lts Ts vsl E vsr), r, r'.
      split; [constructor; assumption|].
      split; [simpl; rewrite Hts; reflexivity|].
      split; [simpl; rewrite Hts'; reflexivity|]. exact Hred.
    + split; [intros H; discriminate H|].
      split; [intros ? H; discriminate H|].
      intros e' P' He'. injection He' as He1 He2. subst e' P'.
      destruct (IHe _ _ _ _ eq_refl) as [[Hpure [Hwf Hv]] [Hvvsl Hts]].
      split; [split; [constructor; exact Hpure
                     |split; [constructor; assumption|exact Hv]]|].
      simpl. rewrite Hts. reflexivity.
    + spec_absurd.
  - (* term_match *)
    intros scrut K n_lt arity yes_body no_body [IHv [IHs IHe]] _ _.
    unfold go_spec. simpl.
    destruct (stepf_go fresh scrut) as [|s'|e P|] eqn:Hsc.
    + specialize (IHv eq_refl).
      destruct scrut as [x|ta tb|body T1|ta T1|bound bd|ta la|bd
                        |K' l' lts' Ts' vs|s tg nl ar y n|Et Ts' TB TR ob bd
                        |rc opx Ss' A' ag|Et mm Ts' TR ob|mm TB TR bd];
        try spec_absurd.
      (* scrut = term_ctor K' l' lts' Ts' vs *)
      inversion IHv; subst.
      destruct (Nat.eqb K' K) eqn:HK.
      * apply Nat.eqb_eq in HK. subst K'.
        destruct (Nat.eqb arity (List.length vs)) eqn:Har.
        -- apply Nat.eqb_eq in Har. subst arity.
           split; [intros H; discriminate H|].
           split; [|intros ? ? H; discriminate H].
           intros u Hu. injection Hu as Hu. subst u.
           exists EC_hole,
             (term_match (term_ctor K l' lts' Ts' vs) K n_lt (List.length vs)
                yes_body no_body),
             (subst_list_tm vs (subst_list_lt_in_tm lts' yes_body)).
           split; [constructor|]. split; [reflexivity|]. split; [reflexivity|].
           left. apply H_MatchYes. assumption.
        -- spec_absurd.
      * apply Nat.eqb_neq in HK.
        split; [intros H; discriminate H|].
        split; [|intros ? ? H; discriminate H].
        intros u Hu. injection Hu as Hu. subst u.
        exists EC_hole,
          (term_match (term_ctor K' l' lts' Ts' vs) K n_lt arity
             yes_body no_body),
          no_body.
        split; [constructor|]. split; [reflexivity|]. split; [reflexivity|].
        left. apply H_MatchNo; [assumption|].
        intros Heq. apply HK. symmetry. exact Heq.
    + split; [intros H; discriminate H|].
      split; [|intros ? ? H; discriminate H].
      intros u Hu. injection Hu as Hu. subst u.
      destruct (IHs _ eq_refl) as (E & r & r' & HE & Hsce & Hsce' & Hred).
      exists (EC_match E K n_lt arity yes_body no_body), r, r'.
      split; [constructor; assumption|].
      split; [simpl; rewrite <- Hsce; reflexivity|].
      split; [simpl; rewrite <- Hsce'; reflexivity|]. exact Hred.
    + split; [intros H; discriminate H|].
      split; [intros ? H; discriminate H|].
      intros e' P' He'. injection He' as He1 He2. subst e' P'.
      destruct (IHe _ _ eq_refl) as [[Hpure [Hwf Hv]] Heq].
      split; [split; [constructor; exact Hpure
                     |split; [constructor; assumption|exact Hv]]|].
      simpl. rewrite <- Heq. reflexivity.
    + spec_absurd.
  - (* term_handle: allocate the fresh delimiter marker *)
    intros E_tag Ts T_B T_R op_bodies body _ _.
    unfold go_spec. simpl.
    split; [intros H; discriminate H|].
    split; [|intros ? ? H; discriminate H].
    intros u Hu. injection Hu as Hu. subst u.
    exists EC_hole, (term_handle E_tag Ts T_B T_R op_bodies body),
      (term_handler_m fresh T_B T_R
        (subst_tm 0 (term_cap E_tag fresh Ts T_R op_bodies) body)).
    split; [constructor|]. split; [reflexivity|]. split; [reflexivity|].
    right. unfold handle_alloc.
    do 6 eexists. split; reflexivity.
  - (* term_perform *)
    intros recv op Ss A arg [IHrv [IHrs IHre]] [IHav [IHas IHae]].
    unfold go_spec. simpl.
    destruct (stepf_go fresh recv) as [|r'|er Pr|] eqn:Hr.
    + specialize (IHrv eq_refl).
      destruct (stepf_go fresh arg) as [|a'|ea Pa|] eqn:Ha.
      * (* both values: an escape is born (or stuck) *)
        specialize (IHav eq_refl).
        destruct recv as [x|ta tb|body T1|ta T1|bound bd|ta la|bd
                         |K' l' lts' Ts' vs|s tg nl ar y n
                         |Et Ts' TB TR ob bd|rc opx Ss' A' ag
                         |Et mm Ts' TR ob|mm TB TR bd];
          try spec_absurd.
        (* recv = term_cap Et mm nb Ts' TR ob *)
        split; [intros H; discriminate H|].
        split; [intros ? H; discriminate H|].
        intros e P He. injection He as He1 He2. subst e P.
        split; [split; [constructor|split; [constructor|exact IHav]]|].
        reflexivity.
      * split; [intros H; discriminate H|].
        split; [|intros ? ? H; discriminate H].
        intros u Hu. injection Hu as Hu. subst u.
        destruct (IHas _ eq_refl) as (E & r & r'' & HE & Harg & Harg' & Hred).
        exists (EC_perform_a recv op Ss A E), r, r''.
        split; [constructor; assumption|].
        split; [simpl; rewrite <- Harg; reflexivity|].
        split; [simpl; rewrite <- Harg'; reflexivity|]. exact Hred.
      * split; [intros H; discriminate H|].
        split; [intros ? H; discriminate H|].
        intros e' P' He'. injection He' as He1 He2. subst e' P'.
        destruct (IHae _ _ eq_refl) as [[Hpure [Hwf Hv]] Heq].
        split; [split; [constructor; exact Hpure
                       |split; [constructor; assumption|exact Hv]]|].
        simpl. rewrite <- Heq. reflexivity.
      * spec_absurd.
    + split; [intros H; discriminate H|].
      split; [|intros ? ? H; discriminate H].
      intros u Hu. injection Hu as Hu. subst u.
      destruct (IHrs _ eq_refl) as (E & r & r'' & HE & Hrecv & Hrecv' & Hred).
      exists (EC_perform_r E op Ss A arg), r, r''.
      split; [constructor; assumption|].
      split; [simpl; rewrite <- Hrecv; reflexivity|].
      split; [simpl; rewrite <- Hrecv'; reflexivity|]. exact Hred.
    + split; [intros H; discriminate H|].
      split; [intros ? H; discriminate H|].
      intros e' P' He'. injection He' as He1 He2. subst e' P'.
      destruct (IHre _ _ eq_refl) as [[Hpure [Hwf Hv]] Heq].
      split; [split; [constructor; exact Hpure
                     |split; [constructor; assumption|exact Hv]]|].
      simpl. rewrite <- Heq. reflexivity.
    + spec_absurd.
  - (* term_cap *)
    intros E m Ts T_R op_bodies _. unfold go_spec. simpl.
    split; [intros _; constructor|].
    split; [intros ? H; discriminate H|intros ? ? H; discriminate H].
  - (* term_handler_m *)
    intros m0 T_B T_R body [IHv [IHs IHe]].
    unfold go_spec. simpl.
    destruct (stepf_go fresh body) as [|b'|e P|] eqn:Hb.
    + (* value body: H_Return *)
      specialize (IHv eq_refl).
      split; [intros H; discriminate H|].
      split; [|intros ? ? H; discriminate H].
      intros u Hu. injection Hu as Hu. subst u.
      exists EC_hole, (term_handler_m m0 T_B T_R body), body.
      split; [constructor|]. split; [reflexivity|]. split; [reflexivity|].
      left. apply H_Return. exact IHv.
    + (* body stepped *)
      split; [intros H; discriminate H|].
      split; [|intros ? ? H; discriminate H].
      intros u Hu. injection Hu as Hu. subst u.
      destruct (IHs _ eq_refl) as (E & r & r' & HE & Hbody & Hbody' & Hred).
      exists (EC_handler_m m0 T_B T_R E), r, r'.
      split; [constructor; assumption|].
      split; [simpl; rewrite <- Hbody; reflexivity|].
      split; [simpl; rewrite <- Hbody'; reflexivity|]. exact Hred.
    + (* body escapes *)
      destruct (Nat.eqb (esc_mk e) m0) eqn:Hm.
      * apply Nat.eqb_eq in Hm.
        destruct (ty_eqb (esc_TR e) T_R) eqn:HTR.
        -- (* matching delimiter: H_Perform fires on the selected clause *)
           apply ty_eqb_eq in HTR.
           destruct (nth_error (esc_ops e) (esc_opix e)) as [[nb ob]|] eqn:Hnth;
             [|spec_absurd].
           split; [intros H; discriminate H|].
           split; [|intros ? ? H; discriminate H].
           intros u Hu. injection Hu as Hu. subst u.
           destruct (IHe _ _ eq_refl) as [[Hpure [Hwf Hv]] Heq].
           exists EC_hole, (term_handler_m m0 T_B T_R body),
             (subst_list_tm
                [esc_arg e;
                 term_lam (term_handler_m m0 T_B T_R
                             (plug (shift_ectx_tm 1 0 P) (term_var 0)))
                          (esc_A e)]
                (subst_list_ty_in_tm (esc_Ss e) ob)).
           split; [constructor|]. split; [reflexivity|]. split; [reflexivity|].
           left. rewrite Heq.
           destruct e as [Et mm Ts TRc ops opix Ss A v].
           simpl in Hm, HTR, Hpure, Hv, Hnth |- *. subst mm TRc.
           unfold esc_redex. simpl.
           eapply H_Perform; eassumption.
        -- spec_absurd.
      * (* different marker: forward the escape one delimiter out *)
        apply Nat.eqb_neq in Hm.
        split; [intros H; discriminate H|].
        split; [intros ? H; discriminate H|].
        intros e' P' He'. injection He' as He1 He2. subst e' P'.
        destruct (IHe _ _ eq_refl) as [[Hpure [Hwf Hv]] Heq].
        split; [split; [constructor; [exact Hm|exact Hpure]
                       |split; [constructor; assumption|exact Hv]]|].
        simpl. rewrite <- Heq. reflexivity.
    + spec_absurd.
  - (* nil *)
    unfold go_list_spec. simpl.
    split; [intros _; constructor|].
    split; [intros ? H; discriminate H|intros ? ? ? ? H; discriminate H].
  - (* cons *)
    intros u rest [IHuv [IHus IHue]] [IHrv [IHrs IHre]].
    unfold go_list_spec. simpl.
    destruct (stepf_go fresh u) as [|u'|e P|] eqn:Hu.
    + specialize (IHuv eq_refl).
      destruct (stepf_list fresh rest) as [|rest'|e vsl P vsr|] eqn:Hrest.
      * split; [intros _; constructor; [exact IHuv|exact (IHrv eq_refl)]|].
        split; [intros ? H; discriminate H|intros ? ? ? ? H; discriminate H].
      * split; [intros H; discriminate H|].
        split; [|intros ? ? ? ? H; discriminate H].
        intros ts' Hts'. injection Hts' as Hts'. subst ts'.
        destruct (IHrs _ eq_refl)
          as (vsl & E & r & r' & vsr & Hvvsl & HE & Hre & Hre' & Hred).
        exists (u :: vsl), E, r, r', vsr.
        split; [constructor; assumption|]. split; [assumption|].
        split; [simpl; rewrite Hre; reflexivity|].
        split; [simpl; rewrite Hre'; reflexivity|]. exact Hred.
      * split; [intros H; discriminate H|].
        split; [intros ? H; discriminate H|].
        intros e' vsl' P' vsr' He'.
        injection He' as He1 He2 He3 He4. subst e' vsl' P' vsr'.
        destruct (IHre _ _ _ _ eq_refl) as [Hok [Hvvsl Hre]].
        split; [exact Hok|].
        split; [constructor; assumption|].
        simpl. rewrite Hre. reflexivity.
      * lspec_absurd.
    + split; [intros H; discriminate H|].
      split; [|intros ? ? ? ? H; discriminate H].
      intros ts' Hts'. injection Hts' as Hts'. subst ts'.
      destruct (IHus _ eq_refl) as (E & r & r' & HE & Hueq & Hu'eq & Hred).
      exists [], E, r, r', rest.
      split; [constructor|]. split; [assumption|].
      split; [simpl; rewrite <- Hueq; reflexivity|].
      split; [simpl; rewrite <- Hu'eq; reflexivity|]. exact Hred.
    + split; [intros H; discriminate H|].
      split; [intros ? H; discriminate H|].
      intros e' vsl' P' vsr' He'.
      injection He' as He1 He2 He3 He4. subst e' vsl' P' vsr'.
      destruct (IHue _ _ eq_refl) as [Hok Hueq].
      split; [exact Hok|].
      split; [constructor|].
      simpl. rewrite <- Hueq. reflexivity.
    + lspec_absurd.
  - exact I.
  - intros. exact I.
Qed.

Theorem stepf_sound : forall t u, stepf t = Some u -> t ==> u.
Proof.
  intros t u H. unfold stepf in H.
  destruct (stepf_go (marker_bound t) t) as [|u'|e P|] eqn:Hgo;
    try discriminate H.
  injection H as H. subst u'.
  destruct (stepf_go_sound (marker_bound t) t) as [_ [Hs _]].
  destruct (Hs _ Hgo) as (E & r & r' & HE & Ht & Hu & Hred).
  subst u t.
  destruct Hred as [Hhead | Halloc].
  - apply S_step; assumption.
  - destruct Halloc as (E_tag & Ts & T_B & T_R & op_bodies & body
                        & Hr & Hr').
    subst r r'.
    apply S_HandleCtx; [exact HE|].
    apply marker_bound_fresh.
Qed.

(* ------------------------------------------------------------------ *)
(* Values do not step (the cheap half of the value/None dichotomy).   *)
(* ------------------------------------------------------------------ *)

Lemma stepf_go_value : forall fresh t, value t -> stepf_go fresh t = SR_val.
Proof.
  intros fresh.
  apply (term_list_ind
    (fun t => value t -> stepf_go fresh t = SR_val)
    (fun ts => Forall value ts -> stepf_list fresh ts = LR_vals)
    (fun _ => True)).
  - intros n H; inversion H.
  - intros t1 t2 _ _ H; inversion H.
  - intros body T _ _; reflexivity.
  - intros t T _ H; inversion H.
  - intros bound body _ _; reflexivity.
  - intros t l _ H; inversion H.
  - intros body _ _; reflexivity.
  - intros K l lts Ts ts IH H.
    rewrite stepf_go_ctor_eq.
    inversion H; subst.
    rewrite (IH ltac:(assumption)). reflexivity.
  - intros scrut tag n_lt arity yes no _ _ _ H; inversion H.
  - intros E Ts T_B T_R op_bodies body _ _ H; inversion H.
  - intros recv op Ss A arg _ _ H; inversion H.
  - intros E m Ts T_R op_bodies _ _; reflexivity.
  - intros m T_B T_R t _ H; inversion H.
  - intros _; reflexivity.
  - intros t ts IHt IHts H. inversion H; subst. simpl.
    rewrite (IHt ltac:(assumption)), (IHts ltac:(assumption)). reflexivity.
  - exact I.
  - intros; exact I.
Qed.

Theorem stepf_value_none : forall t, value t -> stepf t = None.
Proof.
  intros t Hv. unfold stepf.
  rewrite (stepf_go_value (marker_bound t) t Hv). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* A bounded-fuel driver, certified against multi_step.               *)
(* ------------------------------------------------------------------ *)

Fixpoint stepf_run (n : nat) (t : term) : term :=
  match n with
  | 0 => t
  | S k =>
      match stepf t with
      | Some u => stepf_run k u
      | None => t
      end
  end.

Theorem stepf_run_sound : forall n t, multi_step t (stepf_run n t).
Proof.
  induction n as [|k IH]; intros t; simpl.
  - apply MS_Refl.
  - destruct (stepf t) as [u|] eqn:Hs.
    + eapply MS_Step; [apply stepf_sound; exact Hs | apply IH].
    + apply MS_Refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Smoke tests: stepf actually computes.                              *)
(* ------------------------------------------------------------------ *)

Module StepfSmokeTests.

  (* An arbitrary closed base type and the identity on it. *)
  Definition TU : type := type_ctor 1 lt_free [].
  Definition idt : term := term_lam (term_var 0) TU.

  (* beta: (λx. x) (λx. x)  ⇒  λx. x *)
  Example stepf_beta : stepf (term_app idt idt) = Some idt.
  Proof. vm_compute. reflexivity. Qed.

  (* values do not step *)
  Example stepf_value_id : stepf idt = None.
  Proof. vm_compute. reflexivity. Qed.

  (* a source handle allocates the marker_bound marker (here 1) *)
  Example stepf_handle_allocates :
    stepf (term_handle 5 [] TU TU [(0, term_var 0)] (term_var 0))
      = Some (term_handler_m 1 TU TU (term_cap 5 1 [] TU [(0, term_var 0)])).
  Proof. vm_compute. reflexivity. Qed.

  (* a perform under its matching delimiter fires H_Perform: the       *)
  (* op-body ($1 = the resumption k) returns the reified resumption,   *)
  (* a lambda re-installing the delimiter around the (empty) captured  *)
  (* context.                                                          *)
  Example stepf_perform_fires :
    stepf (term_handler_m 3 TU TU
             (term_perform (term_cap 5 3 [] TU [(0, term_var 1)]) 0 [] TU idt))
      = Some (term_lam (term_handler_m 3 TU TU (term_var 0)) TU).
  Proof. vm_compute. reflexivity. Qed.

  (* the SECOND operation of a two-op capability fires: index 1        *)
  (* selects the second clause (which returns the op argument).        *)
  Example stepf_perform_fires_second_op :
    stepf (term_handler_m 3 TU TU
             (term_perform (term_cap 5 3 [] TU [(0, term_var 1); (0, term_var 0)])
                1 [] TU idt))
      = Some idt.
  Proof. vm_compute. reflexivity. Qed.

  (* an out-of-range operation index is stuck, not misdirected *)
  Example stepf_perform_bad_index_stuck :
    stepf (term_handler_m 3 TU TU
             (term_perform (term_cap 5 3 [] TU [(0, term_var 1)]) 7 [] TU idt))
      = None.
  Proof. vm_compute. reflexivity. Qed.

  (* two beta steps through the driver *)
  Example stepf_run_two :
    stepf_run 2 (term_app (term_app idt idt) idt) = idt.
  Proof. vm_compute. reflexivity. Qed.

End StepfSmokeTests.
