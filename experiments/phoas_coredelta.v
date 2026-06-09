(* ================================================================== *)
(* phoas_coredelta.v  --  PHOAS prototype of CoreDelta                *)
(*                                                                    *)
(* STEP 0: ENCODING SPIKE.                                            *)
(*                                                                    *)
(* Goal: validate the *extrinsic* PHOAS encoding for CoreDelta, where *)
(*   - terms are parametric raw syntax `term' V`,                     *)
(*   - typing and subtyping are separate Prop relations,              *)
(*   - term variables are "self-describing": instantiate V := type so *)
(*     each variable carries its own type (T_Var reads it off).       *)
(*                                                                    *)
(* The central new proof obligation that does NOT appear in the de    *)
(* Bruijn development is *two-instantiation coherence*: substitution  *)
(* (flatten over V := term') must respect typing (over V := type).    *)
(* We discharge it via a Chlipala-style `wf` relation relating two    *)
(* instantiations along a list of variable correspondences.          *)
(*                                                                    *)
(* SIMPLIFICATIONS for the spike (deferred to the full encoding, all  *)
(* lower-risk than term-substitution coherence):                      *)
(*   - Types are closed (NO type variables / SA_VarCtx). Subtyping is *)
(*     exercised via the lifetime lattice on function types, which is *)
(*     enough to make T_Sub non-trivial in the beta case.             *)
(*   - Single-binder lambda only (no ctors/match/effects yet).        *)
(* ================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Vectors.Vector.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* Lifetimes: the minimal CoreDelta lattice  free <: local            *)
(* ------------------------------------------------------------------ *)

Inductive lifetime : Type :=
  | lt_free  : lifetime
  | lt_local : lifetime.

Inductive lt_sub : lifetime -> lifetime -> Prop :=
  | LS_Refl      : forall l, lt_sub l l
  | LS_FreeLocal : lt_sub lt_free lt_local.

Lemma lt_sub_trans : forall a b c, lt_sub a b -> lt_sub b c -> lt_sub a c.
Proof.
  intros a b c H1 H2. inversion H1; subst; try assumption.
  inversion H2; subst; constructor.
Qed.

(* ------------------------------------------------------------------ *)
(* Types (closed) + subtyping                                         *)
(*   function types carry a closure lifetime; subtyping is            *)
(*   contravariant in the domain, covariant in lifetime + codomain.   *)
(* ------------------------------------------------------------------ *)

Inductive type : Type :=
  | type_base : type
  | type_fun  : type -> lifetime -> type -> type.

Inductive sub : type -> type -> Prop :=
  | SA_Refl  : forall T, sub T T
  | SA_Trans : forall S U T, sub S U -> sub U T -> sub S T
  | SA_Fun   : forall A A' l l' B B',
      sub A' A -> lt_sub l l' -> sub B B' ->
      sub (type_fun A l B) (type_fun A' l' B').

(* Function-type subtyping inversion (mirrors Safety.v sub_fun_inv).  *)
Lemma sub_fun_inv : forall S A' l' B',
  sub S (type_fun A' l' B') ->
  exists A l B, S = type_fun A l B /\ sub A' A /\ lt_sub l l' /\ sub B B'.
Proof.
  intros S A' l' B' H. remember (type_fun A' l' B') as T eqn:E.
  revert A' l' B' E. induction H; intros Ar lr Br E.
  - (* SA_Refl *) subst. exists Ar, lr, Br.
    repeat split; [ apply SA_Refl | apply LS_Refl | apply SA_Refl ].
  - (* SA_Trans *) subst T.
    destruct (IHsub2 _ _ _ eq_refl) as (Au & lu & Bu & EU & Hau & Hlu & Hbu).
    subst U.
    destruct (IHsub1 _ _ _ eq_refl) as (As & ls & Bs & ES & Has & Hls & Hbs).
    exists As, ls, Bs. subst S. repeat split.
    + eapply SA_Trans; eauto.
    + eapply lt_sub_trans; eauto.
    + eapply SA_Trans; eauto.
  - (* SA_Fun *) inversion E; subst. exists A, l, B.
    repeat split; assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* PHOAS terms                                                        *)
(* ------------------------------------------------------------------ *)

Inductive term' (V : Type) : Type :=
  | term_var : V -> term' V
  | term_app : term' V -> term' V -> term' V
  | term_abs : type -> (V -> term' V) -> term' V.

Arguments term_var {V} _.
Arguments term_app {V} _ _.
Arguments term_abs {V} _ _.

Definition Term  := forall V, term' V.        (* closed terms       *)
Definition Term1 := forall V, V -> term' V.   (* one free variable  *)

(* Smart constructors over closed terms. *)
Definition tApp (f x : Term) : Term := fun V => term_app (f V) (x V).
Definition tAbs (A : type) (f : Term1) : Term := fun V => term_abs A (f V).

(* ------------------------------------------------------------------ *)
(* Typing, over the instantiation V := type (self-describing vars).   *)
(* ------------------------------------------------------------------ *)

Inductive has_type : term' type -> type -> Prop :=
  | T_Var : forall T, has_type (term_var T) T
  | T_Sub : forall e S T, has_type e S -> sub S T -> has_type e T
  | T_App : forall e1 e2 A l B,
      has_type e1 (type_fun A l B) ->
      has_type e2 A ->
      has_type (term_app e1 e2) B
  | T_Abs : forall A (f : type -> term' type) l B,
      (* body typed with the parameter variable carrying its type A *)
      has_type (f A) B ->
      has_type (term_abs A f) (type_fun A l B).

(* Typing inversion lemmas (each peels the implicit T_Sub chain). *)

Lemma has_type_var_inv : forall X T, has_type (term_var X) T -> sub X T.
Proof.
  intros X T H. remember (term_var X) as e eqn:E.
  induction H; try (inversion E; fail).
  - inversion E; subst. apply SA_Refl.
  - subst e. eapply SA_Trans; [ apply IHhas_type; reflexivity | assumption ].
Qed.

Lemma app_typing_inv : forall a b T,
  has_type (term_app a b) T ->
  exists A l B, has_type a (type_fun A l B) /\ has_type b A /\ sub B T.
Proof.
  intros a b T H. remember (term_app a b) as e eqn:E.
  induction H; try (inversion E; fail).
  - (* T_Sub *) subst e.
    destruct (IHhas_type eq_refl) as (A & l & B & Ha & Hb & Hsub).
    exists A, l, B. repeat split; auto. eapply SA_Trans; eauto.
  - (* T_App *) inversion E; subst. exists A, l, B.
    repeat split; auto. apply SA_Refl.
Qed.

Lemma abs_typing_inv : forall A f T,
  has_type (term_abs A f) T ->
  exists l B, has_type (f A) B /\ sub (type_fun A l B) T.
Proof.
  intros A f T H. remember (term_abs A f) as e eqn:E.
  induction H; try (inversion E; fail).
  - (* T_Sub *) subst e.
    destruct (IHhas_type eq_refl) as (l & B & Hb & Hsub).
    exists l, B. split; auto. eapply SA_Trans; eauto.
  - (* T_Abs *) inversion E; subst. exists l, B.
    split; auto. apply SA_Refl.
Qed.

(* ------------------------------------------------------------------ *)
(* Substitution via flatten (one-level squash).                       *)
(* ------------------------------------------------------------------ *)

Fixpoint flatten {V} (e : term' (term' V)) : term' V :=
  match e with
  | term_var x   => x
  | term_app a b => term_app (flatten a) (flatten b)
  | term_abs A f => term_abs A (fun x => flatten (f (term_var x)))
  end.

Definition Subst (f : Term1) (v : Term) : Term :=
  fun V => flatten (f (term' V) (v V)).

(* ------------------------------------------------------------------ *)
(* Two-instantiation well-formedness (Chlipala-style).                *)
(*                                                                    *)
(* `wf G e1 e2` says raw terms e1 (over V1) and e2 (over V2) have the *)
(* same structure, with corresponding variables paired up in G.       *)
(* ------------------------------------------------------------------ *)

Inductive wf {V1 V2 : Type} : list (V1 * V2) -> term' V1 -> term' V2 -> Prop :=
  | WfVar : forall G v1 v2,
      List.In (v1, v2) G -> wf G (term_var v1) (term_var v2)
  | WfApp : forall G a a' b b',
      wf G a a' -> wf G b b' ->
      wf G (term_app a b) (term_app a' b')
  | WfAbs : forall G A f1 f2,
      (forall v1 v2, wf ((v1, v2) :: G) (f1 v1) (f2 v2)) ->
      wf G (term_abs A f1) (term_abs A f2).

(* Closed well-formedness: a closed term behaves the same under any   *)
(* two instantiations.  Provable for any concrete term by            *)
(* `repeat constructor` (see idTerm_wf below).                        *)
Definition WfT  (E : Term)  : Prop :=
  forall V1 V2, wf (V1:=V1) (V2:=V2) nil (E V1) (E V2).
Definition WfT1 (f : Term1) : Prop :=
  forall V1 V2 (v1 : V1) (v2 : V2), wf [(v1, v2)] (f V1 v1) (f V2 v2).

Lemma WfT_app : forall f x, WfT (tApp f x) -> WfT f /\ WfT x.
Proof.
  intros f x H. split; intros V1 V2; specialize (H V1 V2);
    unfold tApp in H; inversion H; subst; assumption.
Qed.

Lemma WfT_abs : forall A f, WfT (tAbs A f) -> WfT1 f.
Proof.
  intros A f H V1 V2 v1 v2. specialize (H V1 V2). unfold tAbs in H.
  inversion H as [ | | G0 A0 f1 f2 Hbody Hg He1 He2 ]; subst.
  apply Hbody.
Qed.

(* ------------------------------------------------------------------ *)
(* THE COHERENCE LEMMA: substitution respects typing.                 *)
(*                                                                    *)
(* If e1 (over V := type) and e2 (over V := term' type) are wf along  *)
(* G, and every paired substitute is well typed at its variable's     *)
(* type, then typing transports from e1 to (flatten e2).              *)
(* ------------------------------------------------------------------ *)

Lemma subst_has_type :
  forall G (e1 : term' type) (e2 : term' (term' type)),
    wf G e1 e2 ->
    Forall (fun p => has_type (snd p) (fst p)) G ->
    forall T, has_type e1 T -> has_type (flatten e2) T.
Proof.
  intros G e1 e2 Hwf.
  induction Hwf as [ G v1 v2 Hin
                   | G a a' b b' Hwfa IHa Hwfb IHb
                   | G A f1 f2 Hbody IH ];
    intros HG T Hty; simpl.
  - (* WfVar *)
    apply has_type_var_inv in Hty.            (* sub v1 T *)
    rewrite Forall_forall in HG.
    specialize (HG _ Hin). simpl in HG.        (* has_type v2 v1 *)
    eapply T_Sub; [ exact HG | exact Hty ].
  - (* WfApp *)
    apply app_typing_inv in Hty as (A & l & B & Ha & Hb & Hsub).
    eapply T_Sub; [ | exact Hsub ].
    eapply T_App;
      [ apply IHa; [ exact HG | exact Ha ]
      | apply IHb; [ exact HG | exact Hb ] ].
  - (* WfAbs *)
    apply abs_typing_inv in Hty as (l & B & Hb & Hsub).
    eapply T_Sub; [ | exact Hsub ].
    eapply T_Abs.
    (* body, with the new variable mapped to (term_var A), typed at A *)
    apply (IH A (term_var A));
      [ constructor; [ apply T_Var | exact HG ] | exact Hb ].
Qed.

(* ------------------------------------------------------------------ *)
(* Operational semantics (closed terms) + beta preservation.          *)
(* ------------------------------------------------------------------ *)

Inductive value : Term -> Prop :=
  | value_abs : forall A f, value (tAbs A f).

Inductive step : Term -> Term -> Prop :=
  | S_Beta : forall A f v,
      value v -> step (tApp (tAbs A f) v) (Subst f v)
  | S_App1 : forall f f' x,
      step f f' -> step (tApp f x) (tApp f' x)
  | S_App2 : forall f x x',
      value f -> step x x' -> step (tApp f x) (tApp f x').

Lemma beta_preservation : forall A f v T,
  WfT1 f ->
  has_type ((tApp (tAbs A f) v) type) T ->
  has_type (Subst f v type) T.
Proof.
  intros A f v T Hwf Hty.
  unfold tApp, tAbs in Hty. simpl in Hty.
  (* term_app (term_abs A (f type)) (v type) *)
  apply app_typing_inv in Hty as (A0 & l & B0 & Habs & Hv & HsubB).
  apply abs_typing_inv in Habs as (l1 & B1 & Hbody & HsubFun).
  apply sub_fun_inv in HsubFun as (A2 & l2 & B2 & Eeq & HA & Hl & HB).
  inversion Eeq; subst A2 l2 B2.            (* A=A, l1=l, B1=B0 effectively *)
  (* Hbody : has_type (f type A) B1 ; Hv : has_type (v type) A0 ; HA : sub A0 A *)
  unfold Subst.
  eapply T_Sub; [ | eapply SA_Trans; [ exact HB | exact HsubB ] ].
  (* goal: has_type (flatten (f (term' type) (v type))) B1 *)
  eapply subst_has_type.
  - apply (Hwf type (term' type) A (v type)).
  - constructor; [ simpl; eapply T_Sub; [ exact Hv | exact HA ] | constructor ].
  - exact Hbody.
Qed.

Theorem preservation : forall E E',
  step E E' -> forall T, WfT E -> has_type (E type) T -> has_type (E' type) T.
Proof.
  intros E E' Hstep. induction Hstep; intros T Hwf Hty.
  - (* beta *)
    destruct (WfT_app _ _ Hwf) as [Hwfabs Hwfv].
    apply (beta_preservation A f v T); auto. apply (WfT_abs A f Hwfabs).
  - (* S_App1 *)
    destruct (WfT_app _ _ Hwf) as [Hwff Hwfx].
    unfold tApp in Hty |- *. simpl in Hty |- *.
    apply app_typing_inv in Hty as (A & l & B & Hf & Hx & Hsub).
    eapply T_Sub; [ | exact Hsub ]. eapply T_App; [ | exact Hx ].
    apply IHHstep; [ exact Hwff | exact Hf ].
  - (* S_App2 *)
    destruct (WfT_app _ _ Hwf) as [Hwff Hwfx].
    unfold tApp in Hty |- *. simpl in Hty |- *.
    apply app_typing_inv in Hty as (A & l & B & Hf & Hx & Hsub).
    eapply T_Sub; [ | exact Hsub ]. eapply T_App; [ exact Hf | ].
    apply IHHstep; auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Sanity: WfT is dischargeable for concrete terms.                   *)
(* ------------------------------------------------------------------ *)

Definition idTerm : Term := tAbs type_base (fun V x => term_var x).

Example idTerm_wf : WfT idTerm.
Proof.
  intros V1 V2. unfold idTerm, tAbs. constructor. intros v1 v2.
  constructor. left. reflexivity.
Qed.

Example idTerm_typed :
  has_type (idTerm type) (type_fun type_base lt_free type_base).
Proof.
  unfold idTerm, tAbs. simpl. apply T_Abs. apply T_Var.
Qed.

(* ================================================================== *)
(* Capture-lifetime via instantiation (validates Step 7 machinery).   *)
(*                                                                    *)
(* After the V := type instantiation every leaf is `term_var A`, so   *)
(* the free/bound distinction is erased and capture CANNOT be a       *)
(* structural function on `term' type`.  Instead we instantiate at    *)
(* V := lifetime and let each *environment* binder supply the         *)
(* lifetime of the value it binds, while binders *internal* to the    *)
(* lambda contribute the bottom lifetime (they are not captured from  *)
(* the environment).  A lambda's closure lifetime must then dominate  *)
(* the join of the lifetimes that actually occur (= are captured):    *)
(* the full T_Lam would carry the premise `lt_sub (captureLt f lv) l`.*)
(*                                                                    *)
(* NOTE: capture turns out to need only a SINGLE marker instantiation *)
(* (V := lifetime), strictly simpler than the two-instantiation       *)
(* coherence required for substitution.  So Step 7 is lower-risk than *)
(* the (now-discharged) coherence lemma above.                        *)
(* ================================================================== *)

(* lt_free is bottom, lt_local is top of the lattice. *)
Definition lt_join (a b : lifetime) : lifetime :=
  match a with lt_local => lt_local | lt_free => b end.

Fixpoint capturedLt (e : term' lifetime) : lifetime :=
  match e with
  | term_var l   => l
  | term_app a b => lt_join (capturedLt a) (capturedLt b)
  | term_abs _ g => capturedLt (g lt_free)
  end.

Definition captureLt (f : Term1) (lv : lifetime) : lifetime :=
  capturedLt (f lifetime lv).

(* A body that uses its argument captures the argument's lifetime ... *)
Example capture_used :
  captureLt (fun V x => term_var x) lt_local = lt_local.
Proof. reflexivity. Qed.

(* ... while a body that ignores it captures nothing (bottom). *)
Example capture_unused :
  captureLt (fun V (_ : V) => term_abs type_base (fun y => term_var y)) lt_local
    = lt_free.
Proof. reflexivity. Qed.

(* ================================================================== *)
(* FULL PROTOTYPE SKELETON                                            *)
(*                                                                    *)
(* This module starts the real CoreDelta PHOAS prototype while keeping *)
(* the spike above intact.  It mirrors Syntax.v, but replaces each de  *)
(* Bruijn binder by a PHOAS function over the appropriate namespace.  *)
(* ================================================================== *)

Module Full.

Definition ctor_tag := nat.
Definition eff_tag := nat.
Definition marker := nat.
Definition any_tag : ctor_tag := 0.

(* ------------------------------------------------------------------ *)
(* Three namespaces: lifetime vars, type vars, and term vars.         *)
(* ------------------------------------------------------------------ *)

Inductive lifetime' (LV : Type) : Type :=
  | lt_var : LV -> lifetime' LV
  | lt_free : lifetime' LV
  | lt_local : lifetime' LV
  | lt_min : lifetime' LV -> lifetime' LV -> lifetime' LV.

Arguments lt_var {LV} _.
Arguments lt_free {LV}.
Arguments lt_local {LV}.
Arguments lt_min {LV} _ _.

Inductive type' (LV TV : Type) : Type :=
  | type_var : TV -> type' LV TV
  | type_fun : type' LV TV -> lifetime' LV -> type' LV TV -> type' LV TV
  | type_ctor : ctor_tag -> lifetime' LV -> list (type' LV TV) -> type' LV TV
  | type_lt_all : (LV -> type' LV TV) -> type' LV TV
  | type_ty_all : type' LV TV -> (TV -> type' LV TV) -> type' LV TV.

Arguments type_var {LV TV} _.
Arguments type_fun {LV TV} _ _ _.
Arguments type_ctor {LV TV} _ _ _.
Arguments type_lt_all {LV TV} _.
Arguments type_ty_all {LV TV} _ _.

Inductive term' (LV TV V : Type) : Type :=
  | term_var : V -> term' LV TV V
  | term_app : term' LV TV V -> term' LV TV V -> term' LV TV V
  | term_lam : type' LV TV -> (V -> term' LV TV V) -> term' LV TV V
  | term_ty_app : term' LV TV V -> type' LV TV -> term' LV TV V
  | term_ty_lam : type' LV TV -> (TV -> term' LV TV V) -> term' LV TV V
  | term_lt_app : term' LV TV V -> lifetime' LV -> term' LV TV V
  | term_lt_lam : (LV -> term' LV TV V) -> term' LV TV V
  | term_ctor : ctor_tag -> lifetime' LV -> list (lifetime' LV) ->
      list (type' LV TV) -> list (term' LV TV V) -> term' LV TV V
  | term_match : forall n_lt arity,
      term' LV TV V -> ctor_tag ->
      (Vector.t LV n_lt -> Vector.t V arity -> term' LV TV V) ->
      term' LV TV V -> term' LV TV V
  | term_handle : forall n_beta,
      eff_tag -> list (type' LV TV) ->
      (Vector.t TV n_beta -> V -> V -> term' LV TV V) ->
      (V -> term' LV TV V) -> term' LV TV V
  | term_perform : term' LV TV V -> list (type' LV TV) ->
      term' LV TV V -> term' LV TV V
  | term_cap : forall n_beta,
      eff_tag -> marker -> list (type' LV TV) ->
      (Vector.t TV n_beta -> V -> V -> term' LV TV V) -> term' LV TV V
  | term_handler_m : marker -> term' LV TV V -> term' LV TV V
  | term_resume : marker -> (V -> term' LV TV V) -> term' LV TV V.

Arguments term_var {LV TV V} _.
Arguments term_app {LV TV V} _ _.
Arguments term_lam {LV TV V} _ _.
Arguments term_ty_app {LV TV V} _ _.
Arguments term_ty_lam {LV TV V} _ _.
Arguments term_lt_app {LV TV V} _ _.
Arguments term_lt_lam {LV TV V} _.
Arguments term_ctor {LV TV V} _ _ _ _ _.
Arguments term_match {LV TV V} n_lt arity _ _ _ _.
Arguments term_handle {LV TV V} n_beta _ _ _ _.
Arguments term_perform {LV TV V} _ _ _.
Arguments term_cap {LV TV V} n_beta _ _ _ _.
Arguments term_handler_m {LV TV V} _ _.
Arguments term_resume {LV TV V} _ _.

(* ------------------------------------------------------------------ *)
(* Closed wrappers and scope aliases.                                 *)
(* ------------------------------------------------------------------ *)

Definition Lifetime := forall LV, lifetime' LV.
Definition Ty := forall LV TV, type' LV TV.
Definition Term := forall LV TV V, term' LV TV V.

Definition Lifetime1 := forall LV, LV -> lifetime' LV.
Definition TyLt1 := forall LV TV, LV -> type' LV TV.
Definition TyTy1 := forall LV TV, TV -> type' LV TV.
Definition TermTm1 := forall LV TV V, V -> term' LV TV V.
Definition TermTy1 := forall LV TV V, TV -> term' LV TV V.
Definition TermLt1 := forall LV TV V, LV -> term' LV TV V.
Definition TermMatchScope (n_lt arity : nat) :=
  forall LV TV V, Vector.t LV n_lt -> Vector.t V arity -> term' LV TV V.
Definition TermOpScope (n_beta : nat) :=
  forall LV TV V, Vector.t TV n_beta -> V -> V -> term' LV TV V.

(* ------------------------------------------------------------------ *)
(* Smart constructors for closed PHOAS syntax.                        *)
(* ------------------------------------------------------------------ *)

Definition lFree : Lifetime := fun LV => lt_free.
Definition lLocal : Lifetime := fun LV => lt_local.
Definition lMin (l1 l2 : Lifetime) : Lifetime :=
  fun LV => lt_min (l1 LV) (l2 LV).

Definition tyFun (A : Ty) (l : Lifetime) (B : Ty) : Ty :=
  fun LV TV => type_fun (A LV TV) (l LV) (B LV TV).
Definition tyCtor (K : ctor_tag) (l : Lifetime) (Ts : list Ty) : Ty :=
  fun LV TV => type_ctor K (l LV) (List.map (fun T => T LV TV) Ts).
Definition tyLtAll (body : TyLt1) : Ty :=
  fun LV TV => type_lt_all (body LV TV).
Definition tyTyAll (bound : Ty) (body : TyTy1) : Ty :=
  fun LV TV => type_ty_all (bound LV TV) (body LV TV).

Definition tmApp (f x : Term) : Term :=
  fun LV TV V => term_app (f LV TV V) (x LV TV V).
Definition tmLam (A : Ty) (body : TermTm1) : Term :=
  fun LV TV V => term_lam (A LV TV) (body LV TV V).
Definition tmTyApp (e : Term) (T : Ty) : Term :=
  fun LV TV V => term_ty_app (e LV TV V) (T LV TV).
Definition tmTyLam (bound : Ty) (body : TermTy1) : Term :=
  fun LV TV V => term_ty_lam (bound LV TV) (body LV TV V).
Definition tmLtApp (e : Term) (l : Lifetime) : Term :=
  fun LV TV V => term_lt_app (e LV TV V) (l LV).
Definition tmLtLam (body : TermLt1) : Term :=
  fun LV TV V => term_lt_lam (body LV TV V).
Definition tmCtor (K : ctor_tag) (l : Lifetime)
    (lts : list Lifetime) (Ts : list Ty) (args : list Term) : Term :=
  fun LV TV V =>
    term_ctor K (l LV) (List.map (fun lt => lt LV) lts)
      (List.map (fun T => T LV TV) Ts)
      (List.map (fun arg => arg LV TV V) args).
Definition tmMatch (n_lt arity : nat) (scrut : Term) (K : ctor_tag)
    (yes_body : TermMatchScope n_lt arity) (no_body : Term) : Term :=
  fun LV TV V =>
    term_match n_lt arity (scrut LV TV V) K (yes_body LV TV V) (no_body LV TV V).
Definition tmHandle (n_beta : nat) (E : eff_tag) (Ts : list Ty)
    (op_body : TermOpScope n_beta) (body : TermTm1) : Term :=
  fun LV TV V =>
    term_handle n_beta E (List.map (fun T => T LV TV) Ts)
      (op_body LV TV V) (body LV TV V).
Definition tmPerform (recv : Term) (Ss : list Ty) (arg : Term) : Term :=
  fun LV TV V =>
    term_perform (recv LV TV V) (List.map (fun T => T LV TV) Ss) (arg LV TV V).
Definition tmCap (n_beta : nat) (E : eff_tag) (m : marker) (Ts : list Ty)
    (op_body : TermOpScope n_beta) : Term :=
  fun LV TV V =>
    term_cap n_beta E m (List.map (fun T => T LV TV) Ts) (op_body LV TV V).
Definition tmHandlerM (m : marker) (body : Term) : Term :=
  fun LV TV V => term_handler_m m (body LV TV V).
Definition tmResume (m : marker) (body : TermTm1) : Term :=
  fun LV TV V => term_resume m (body LV TV V).

(* ------------------------------------------------------------------ *)
(* Flatten helpers: PHOAS substitution for the three namespaces.      *)
(* ------------------------------------------------------------------ *)

Fixpoint flatten_lt {LV : Type} (l : lifetime' (lifetime' LV)) : lifetime' LV :=
  match l with
  | lt_var x => x
  | lt_free => lt_free
  | lt_local => lt_local
  | lt_min l1 l2 => lt_min (flatten_lt l1) (flatten_lt l2)
  end.

Fixpoint flatten_lt_in_ty {LV TV : Type}
    (T : type' (lifetime' LV) TV) : type' LV TV :=
  match T with
  | type_var X => type_var X
  | type_fun A l B => type_fun (flatten_lt_in_ty A) (flatten_lt l) (flatten_lt_in_ty B)
  | type_ctor K l Ts => type_ctor K (flatten_lt l) (List.map flatten_lt_in_ty Ts)
  | type_lt_all body => type_lt_all (fun x => flatten_lt_in_ty (body (lt_var x)))
  | type_ty_all bound body =>
      type_ty_all (flatten_lt_in_ty bound) (fun X => flatten_lt_in_ty (body X))
  end.

Fixpoint flatten_ty_in_ty {LV TV : Type}
    (T : type' LV (type' LV TV)) : type' LV TV :=
  match T with
  | type_var X => X
  | type_fun A l B => type_fun (flatten_ty_in_ty A) l (flatten_ty_in_ty B)
  | type_ctor K l Ts => type_ctor K l (List.map flatten_ty_in_ty Ts)
  | type_lt_all body => type_lt_all (fun x => flatten_ty_in_ty (body x))
  | type_ty_all bound body =>
      type_ty_all (flatten_ty_in_ty bound) (fun X => flatten_ty_in_ty (body (type_var X)))
  end.

Fixpoint flatten_lt_in_tm {LV TV V : Type}
    (e : term' (lifetime' LV) TV V) : term' LV TV V :=
  match e with
  | term_var x => term_var x
  | term_app f x => term_app (flatten_lt_in_tm f) (flatten_lt_in_tm x)
  | term_lam A body => term_lam (flatten_lt_in_ty A) (fun x => flatten_lt_in_tm (body x))
  | term_ty_app e T => term_ty_app (flatten_lt_in_tm e) (flatten_lt_in_ty T)
  | term_ty_lam bound body =>
      term_ty_lam (flatten_lt_in_ty bound) (fun X => flatten_lt_in_tm (body X))
  | term_lt_app e l => term_lt_app (flatten_lt_in_tm e) (flatten_lt l)
  | term_lt_lam body => term_lt_lam (fun x => flatten_lt_in_tm (body (lt_var x)))
  | term_ctor K l lts Ts args =>
      term_ctor K (flatten_lt l) (List.map flatten_lt lts)
        (List.map flatten_lt_in_ty Ts) (List.map flatten_lt_in_tm args)
  | term_match n_lt arity scrut K yes_body no_body =>
      term_match n_lt arity (flatten_lt_in_tm scrut) K
        (fun lvs vars =>
           flatten_lt_in_tm
             (yes_body (Vector.map lt_var lvs) vars))
        (flatten_lt_in_tm no_body)
  | term_handle n_beta E Ts op_body body =>
      term_handle n_beta E (List.map flatten_lt_in_ty Ts)
        (fun betas arg k => flatten_lt_in_tm (op_body betas arg k))
        (fun cap => flatten_lt_in_tm (body cap))
  | term_perform recv Ss arg =>
      term_perform (flatten_lt_in_tm recv) (List.map flatten_lt_in_ty Ss)
        (flatten_lt_in_tm arg)
  | term_cap n_beta E m Ts op_body =>
      term_cap n_beta E m (List.map flatten_lt_in_ty Ts)
        (fun betas arg k => flatten_lt_in_tm (op_body betas arg k))
  | term_handler_m m body => term_handler_m m (flatten_lt_in_tm body)
  | term_resume m body => term_resume m (fun x => flatten_lt_in_tm (body x))
  end.

Fixpoint flatten_ty_in_tm {LV TV V : Type}
    (e : term' LV (type' LV TV) V) : term' LV TV V :=
  match e with
  | term_var x => term_var x
  | term_app f x => term_app (flatten_ty_in_tm f) (flatten_ty_in_tm x)
  | term_lam A body => term_lam (flatten_ty_in_ty A) (fun x => flatten_ty_in_tm (body x))
  | term_ty_app e T => term_ty_app (flatten_ty_in_tm e) (flatten_ty_in_ty T)
  | term_ty_lam bound body =>
      term_ty_lam (flatten_ty_in_ty bound) (fun X => flatten_ty_in_tm (body (type_var X)))
  | term_lt_app e l => term_lt_app (flatten_ty_in_tm e) l
  | term_lt_lam body => term_lt_lam (fun x => flatten_ty_in_tm (body x))
  | term_ctor K l lts Ts args =>
      term_ctor K l lts (List.map flatten_ty_in_ty Ts) (List.map flatten_ty_in_tm args)
  | term_match n_lt arity scrut K yes_body no_body =>
      term_match n_lt arity (flatten_ty_in_tm scrut) K
        (fun lvs vars => flatten_ty_in_tm (yes_body lvs vars))
        (flatten_ty_in_tm no_body)
  | term_handle n_beta E Ts op_body body =>
      term_handle n_beta E (List.map flatten_ty_in_ty Ts)
        (fun betas arg k =>
           flatten_ty_in_tm (op_body (Vector.map type_var betas) arg k))
        (fun cap => flatten_ty_in_tm (body cap))
  | term_perform recv Ss arg =>
      term_perform (flatten_ty_in_tm recv) (List.map flatten_ty_in_ty Ss)
        (flatten_ty_in_tm arg)
  | term_cap n_beta E m Ts op_body =>
      term_cap n_beta E m (List.map flatten_ty_in_ty Ts)
        (fun betas arg k =>
           flatten_ty_in_tm (op_body (Vector.map type_var betas) arg k))
  | term_handler_m m body => term_handler_m m (flatten_ty_in_tm body)
  | term_resume m body => term_resume m (fun x => flatten_ty_in_tm (body x))
  end.

Fixpoint flatten_tm {LV TV V : Type}
    (e : term' LV TV (term' LV TV V)) : term' LV TV V :=
  match e with
  | term_var x => x
  | term_app f x => term_app (flatten_tm f) (flatten_tm x)
  | term_lam A body => term_lam A (fun x => flatten_tm (body (term_var x)))
  | term_ty_app e T => term_ty_app (flatten_tm e) T
  | term_ty_lam bound body => term_ty_lam bound (fun X => flatten_tm (body X))
  | term_lt_app e l => term_lt_app (flatten_tm e) l
  | term_lt_lam body => term_lt_lam (fun x => flatten_tm (body x))
  | term_ctor K l lts Ts args => term_ctor K l lts Ts (List.map flatten_tm args)
  | term_match n_lt arity scrut K yes_body no_body =>
      term_match n_lt arity (flatten_tm scrut) K
        (fun lvs vars => flatten_tm (yes_body lvs (Vector.map term_var vars)))
        (flatten_tm no_body)
  | term_handle n_beta E Ts op_body body =>
      term_handle n_beta E Ts
        (fun betas arg k => flatten_tm (op_body betas (term_var arg) (term_var k)))
        (fun cap => flatten_tm (body (term_var cap)))
  | term_perform recv Ss arg => term_perform (flatten_tm recv) Ss (flatten_tm arg)
  | term_cap n_beta E m Ts op_body =>
      term_cap n_beta E m Ts
        (fun betas arg k => flatten_tm (op_body betas (term_var arg) (term_var k)))
  | term_handler_m m body => term_handler_m m (flatten_tm body)
  | term_resume m body => term_resume m (fun x => flatten_tm (body (term_var x)))
  end.

Definition substLifetimeInType (body : TyLt1) (l : Lifetime) : Ty :=
  fun LV TV => flatten_lt_in_ty (body (lifetime' LV) TV (l LV)).
Definition substTypeInType (body : TyTy1) (T : Ty) : Ty :=
  fun LV TV => flatten_ty_in_ty (body LV (type' LV TV) (T LV TV)).
Definition substLifetimeInTerm (body : TermLt1) (l : Lifetime) : Term :=
  fun LV TV V => flatten_lt_in_tm (body (lifetime' LV) TV V (l LV)).
Definition substTypeInTerm (body : TermTy1) (T : Ty) : Term :=
  fun LV TV V => flatten_ty_in_tm (body LV (type' LV TV) V (T LV TV)).
Definition substTermInTerm (body : TermTm1) (v : Term) : Term :=
  fun LV TV V => flatten_tm (body LV TV (term' LV TV V) (v LV TV V)).

(* ------------------------------------------------------------------ *)
(* Semantic constructor/effect signatures.                            *)
(*                                                                    *)
(* The de Bruijn development stores schema bodies and later applies   *)
(* `inst_ctor_type` / `inst_op_alpha` / `inst_op_arg`.  Here schemas  *)
(* are PHOAS functions over their lifetime/type argument telescopes,  *)
(* so instantiation is ordinary application after an arity check.     *)
(* ------------------------------------------------------------------ *)

Fixpoint vector_of_list {A : Type} (n : nat) (xs : list A) : option (Vector.t A n) :=
  match n as n0 return option (Vector.t A n0) with
  | O =>
      match xs with
      | [] => Some (Vector.nil A)
      | _ :: _ => None
      end
  | S n' =>
      match xs with
      | [] => None
      | x :: xs' =>
          match vector_of_list n' xs' with
          | Some v => Some (Vector.cons A x n' v)
          | None => None
          end
      end
  end.

Record ctor_sig : Type := {
  ctor_n_lt : nat;
  ctor_n_ty : nat;
  ctor_fields : forall LV TV,
    Vector.t (lifetime' LV) ctor_n_lt ->
    Vector.t (type' LV TV) ctor_n_ty ->
    list (type' LV TV);
  ctor_result : forall LV TV,
    Vector.t (lifetime' LV) ctor_n_lt ->
    Vector.t (type' LV TV) ctor_n_ty ->
    type' LV TV
}.

Definition ctor_fields_at (sig : ctor_sig) {LV TV}
    (lts : list (lifetime' LV)) (Ts : list (type' LV TV))
    : option (list (type' LV TV)) :=
  match vector_of_list (ctor_n_lt sig) lts,
        vector_of_list (ctor_n_ty sig) Ts with
  | Some ltsv, Some Tsv => Some (ctor_fields sig LV TV ltsv Tsv)
  | _, _ => None
  end.

Definition ctor_result_at (sig : ctor_sig) {LV TV}
    (lts : list (lifetime' LV)) (Ts : list (type' LV TV))
    : option (type' LV TV) :=
  match vector_of_list (ctor_n_lt sig) lts,
        vector_of_list (ctor_n_ty sig) Ts with
  | Some ltsv, Some Tsv => Some (ctor_result sig LV TV ltsv Tsv)
  | _, _ => None
  end.

(* Instantiated field types as a length-`arity` vector (so they line up
   with the `Vector.t V arity` term-binders of `term_match`).  The
   lifetime arguments arrive already as a vector of the right width. *)
Definition ctor_fields_vec (sig : ctor_sig) {LV TV} (arity : nat)
    (ltsv : Vector.t (lifetime' LV) (ctor_n_lt sig))
    (Ts : list (type' LV TV))
    : option (Vector.t (type' LV TV) arity) :=
  match vector_of_list (ctor_n_ty sig) Ts with
  | Some Tsv => vector_of_list arity (ctor_fields sig LV TV ltsv Tsv)
  | None => None
  end.

Record eff_sig : Type := {
  eff_n_alpha : nat;
  eff_n_beta : nat;
  eff_param : forall LV TV,
    Vector.t (type' LV TV) eff_n_alpha ->
    Vector.t (type' LV TV) eff_n_beta ->
    type' LV TV;
  eff_ret : forall LV TV,
    Vector.t (type' LV TV) eff_n_alpha ->
    Vector.t (type' LV TV) eff_n_beta ->
    type' LV TV
}.

Definition eff_param_at (sig : eff_sig) {LV TV}
    (alphas betas : list (type' LV TV)) : option (type' LV TV) :=
  match vector_of_list (eff_n_alpha sig) alphas,
        vector_of_list (eff_n_beta sig) betas with
  | Some av, Some bv => Some (eff_param sig LV TV av bv)
  | _, _ => None
  end.

Definition eff_ret_at (sig : eff_sig) {LV TV}
    (alphas betas : list (type' LV TV)) : option (type' LV TV) :=
  match vector_of_list (eff_n_alpha sig) alphas,
        vector_of_list (eff_n_beta sig) betas with
  | Some av, Some bv => Some (eff_ret sig LV TV av bv)
  | _, _ => None
  end.

Definition eff_param_under_betas (sig : eff_sig) {LV TV}
    (alphas : list (type' LV TV))
    : option (Vector.t TV (eff_n_beta sig) -> type' LV TV) :=
  match vector_of_list (eff_n_alpha sig) alphas with
  | Some av => Some (fun betas => eff_param sig LV TV av (Vector.map type_var betas))
  | None => None
  end.

Definition eff_ret_under_betas (sig : eff_sig) {LV TV}
    (alphas : list (type' LV TV))
    : option (Vector.t TV (eff_n_beta sig) -> type' LV TV) :=
  match vector_of_list (eff_n_alpha sig) alphas with
  | Some av => Some (fun betas => eff_ret sig LV TV av (Vector.map type_var betas))
  | None => None
  end.

Record sig_env : Type := {
  lookup_ctor_sig : ctor_tag -> option ctor_sig;
  lookup_eff_sig : eff_tag -> option eff_sig;
  lookup_disjoint : forall tag ctor eff,
    lookup_ctor_sig tag = Some ctor ->
    lookup_eff_sig tag = Some eff -> False
}.

(* ------------------------------------------------------------------ *)
(* Lifetime/type well-formedness and subtyping.                       *)
(*                                                                    *)
(* These judgments are over PHOAS variables directly.  Contexts are   *)
(* predicates assigning bounds to abstract variables; binders extend  *)
(* those predicates with the freshly provided PHOAS variable.         *)
(* ------------------------------------------------------------------ *)

Definition lt_ctx (LV : Type) := LV -> lifetime' LV -> Prop.
Definition ty_ctx (LV TV : Type) := TV -> type' LV TV -> Prop.

Definition empty_lt_ctx {LV : Type} : lt_ctx LV := fun _ _ => False.
Definition empty_ty_ctx {LV TV : Type} : ty_ctx LV TV := fun _ _ => False.

(* Bound-carrier interface for the extrinsic typing pass.  A naive   *)
(* recursive concrete datatype `TV := type' LV TV` is rejected once   *)
(* `type_ty_all` is higher-order, because `TV` appears negatively in  *)
(* binder functions.  So the full prototype keeps the variable types  *)
(* abstract and records their bound accessors as an interface.        *)
Record var_bounds : Type := {
  vb_LV : Type;
  vb_TV : Type;
  vb_lt_bound : vb_LV -> lifetime' vb_LV;
  vb_ty_bound : vb_TV -> type' vb_LV vb_TV
}.

Definition bounds_lt_ctx (B : var_bounds) : lt_ctx (vb_LV B) :=
  fun x bound => vb_lt_bound B x = bound.

Definition bounds_ty_ctx (B : var_bounds) : ty_ctx (vb_LV B) (vb_TV B) :=
  fun X bound => vb_ty_bound B X = bound.

Definition extend_lt {LV : Type} (G : lt_ctx LV) (x : LV) (bound : lifetime' LV)
    : lt_ctx LV :=
  fun y Delta => (y = x /\ Delta = bound) \/ G y Delta.

Definition extend_ty {LV TV : Type} (G : ty_ctx LV TV) (X : TV) (bound : type' LV TV)
    : ty_ctx LV TV :=
  fun Y B => (Y = X /\ B = bound) \/ G Y B.

Inductive lt_wf {LV : Type} (GL : lt_ctx LV) : lifetime' LV -> Prop :=
  | LWF_Var : forall x Delta,
      GL x Delta -> lt_wf GL Delta -> lt_wf GL (lt_var x)
  | LWF_Free : lt_wf GL lt_free
  | LWF_Local : lt_wf GL lt_local
  | LWF_Min : forall l1 l2,
      lt_wf GL l1 -> lt_wf GL l2 -> lt_wf GL (lt_min l1 l2).

Inductive ty_wf {LV TV : Type} (GL : lt_ctx LV) (GT : ty_ctx LV TV)
    : type' LV TV -> Prop :=
  | TWF_Var : forall X B,
      GT X B -> ty_wf GL GT B -> ty_wf GL GT (type_var X)
  | TWF_Fun : forall A l B,
      ty_wf GL GT A -> lt_wf GL l -> ty_wf GL GT B ->
      ty_wf GL GT (type_fun A l B)
  | TWF_Ctor : forall K l Ts,
      lt_wf GL l -> types_wf GL GT Ts ->
      ty_wf GL GT (type_ctor K l Ts)
  | TWF_LtAll : forall body,
      (forall x, ty_wf (extend_lt GL x lt_local) GT (body x)) ->
      ty_wf GL GT (type_lt_all body)
  | TWF_TyAll : forall bound body,
      ty_wf GL GT bound ->
      (forall X, ty_wf GL (extend_ty GT X bound) (body X)) ->
      ty_wf GL GT (type_ty_all bound body)
with types_wf {LV TV : Type} (GL : lt_ctx LV) (GT : ty_ctx LV TV)
    : list (type' LV TV) -> Prop :=
  | TWFs_nil : types_wf GL GT []
  | TWFs_cons : forall T Ts,
      ty_wf GL GT T -> types_wf GL GT Ts -> types_wf GL GT (T :: Ts).

Fixpoint lt_of_ty {LV TV : Type} (T : type' LV TV) : lifetime' LV :=
  let fix go (Ts : list (type' LV TV)) : lifetime' LV :=
    match Ts with
    | [] => lt_free
    | T :: Ts' => lt_min (lt_of_ty T) (go Ts')
    end
  in
  match T with
  | type_var _ => lt_free
  | type_fun _ l _ => l
  | type_ctor _ l Ts => lt_min l (go Ts)
  | type_lt_all _ => lt_free
  | type_ty_all _ _ => lt_free
  end.

Definition lt_of_ty_list {LV TV : Type} (Ts : list (type' LV TV)) : lifetime' LV :=
  List.fold_right (fun T acc => lt_min (lt_of_ty T) acc) lt_free Ts.

Fixpoint no_local_lt {LV : Type} (l : lifetime' LV) : bool :=
  match l with
  | lt_var _ => false
  | lt_free => true
  | lt_local => false
  | lt_min l1 l2 => andb (no_local_lt l1) (no_local_lt l2)
  end.

Fixpoint no_local_ty {LV TV : Type} (T : type' LV TV) : bool :=
  let fix go (Ts : list (type' LV TV)) : bool :=
    match Ts with
    | [] => true
    | T :: Ts' => andb (no_local_ty T) (go Ts')
    end
  in
  match T with
  | type_var _ => false
  | type_fun A l B => andb (no_local_ty A) (andb (no_local_lt l) (no_local_ty B))
  | type_ctor _ l Ts => andb (no_local_lt l) (go Ts)
  | type_lt_all _ => false
  | type_ty_all bound _ => andb (no_local_ty bound) false
  end.

Inductive lt_sub {LV : Type} (GL : lt_ctx LV) : lifetime' LV -> lifetime' LV -> Prop :=
  | LS_Free : forall l,
      lt_wf GL l -> lt_sub GL lt_free l
  | LS_Local : forall l,
      lt_wf GL l -> lt_sub GL l lt_local
  | LS_Var : forall x Delta,
      GL x Delta -> lt_wf GL Delta -> lt_sub GL (lt_var x) Delta
  | LS_Refl : forall l,
      lt_wf GL l -> lt_sub GL l l
  | LS_Trans : forall l1 l2 l3,
      lt_sub GL l1 l2 -> lt_sub GL l2 l3 -> lt_sub GL l1 l3
  | LS_MinL : forall l1 l2 l,
      lt_sub GL l1 l -> lt_sub GL l2 l -> lt_sub GL (lt_min l1 l2) l
  | LS_MinR1 : forall l l1 l2,
      lt_sub GL l l1 -> lt_wf GL l2 -> lt_sub GL l (lt_min l1 l2)
  | LS_MinR2 : forall l l1 l2,
      lt_sub GL l l2 -> lt_wf GL l1 -> lt_sub GL l (lt_min l1 l2).

Inductive sub {LV TV : Type} (GL : lt_ctx LV) (GT : ty_ctx LV TV)
    : type' LV TV -> type' LV TV -> Prop :=
  | SA_Refl : forall T,
      ty_wf GL GT T -> sub GL GT T T
  | SA_Trans : forall S U T,
      sub GL GT S U -> sub GL GT U T -> sub GL GT S T
  | SA_VarCtx : forall X B,
      GT X B -> ty_wf GL GT B -> sub GL GT (type_var X) B
  | SA_Data : forall K l l' Ts,
      lt_sub GL l l' -> types_wf GL GT Ts ->
      sub GL GT (type_ctor K l Ts) (type_ctor K l' Ts)
  | SA_Any : forall T Delta,
      ty_wf GL GT T -> lt_wf GL Delta -> lt_sub GL (lt_of_ty T) Delta ->
      sub GL GT T (type_ctor any_tag Delta [])
  | SA_Fun : forall A A' l l' B B',
      sub GL GT A A' -> lt_sub GL l l' -> sub GL GT B B' ->
      sub GL GT (type_fun A' l B) (type_fun A l' B')
  | SA_LtAll : forall A A',
      (forall x, sub (extend_lt GL x lt_local) GT (A x) (A' x)) ->
      sub GL GT (type_lt_all A) (type_lt_all A')
  | SA_TyAll : forall B B' A A',
      (forall X, ty_wf GL (extend_ty GT X B) (A X)) ->
      (forall X, ty_wf GL (extend_ty GT X B') (A' X)) ->
      sub GL GT B' B ->
      (forall X, sub GL (extend_ty GT X B') (A X) (A' X)) ->
      sub GL GT (type_ty_all B A) (type_ty_all B' A').

Definition bounds_lt_wf (B : var_bounds) : lifetime' (vb_LV B) -> Prop :=
  lt_wf (bounds_lt_ctx B).
Definition bounds_ty_wf (B : var_bounds) : type' (vb_LV B) (vb_TV B) -> Prop :=
  ty_wf (bounds_lt_ctx B) (bounds_ty_ctx B).
Definition bounds_ltsub (B : var_bounds)
    : lifetime' (vb_LV B) -> lifetime' (vb_LV B) -> Prop :=
  lt_sub (bounds_lt_ctx B).
Definition bounds_sub (B : var_bounds)
    : type' (vb_LV B) (vb_TV B) -> type' (vb_LV B) (vb_TV B) -> Prop :=
  sub (bounds_lt_ctx B) (bounds_ty_ctx B).

(* ------------------------------------------------------------------ *)
(* Typing relation (extrinsic).                                       *)
(*                                                                    *)
(* Typing is taken at a fixed instantiation in which TERM variables   *)
(* are self-describing: `V := type' LV TV`, so each term variable     *)
(* carries its own type and `T_Var` reads it off (exactly the spike   *)
(* strategy, now under the full syntax).  Lifetime/type variable      *)
(* bounds are tracked by the predicate contexts GL/GT, which grow at  *)
(* binders via `extend_lt`/`extend_ty`.                               *)
(* ------------------------------------------------------------------ *)

Definition tterm (LV TV : Type) := term' LV TV (type' LV TV).

(* The `Any free` bound used for the β type-variables of an operation
   schema (mirrors de Bruijn `any_at_free`). *)
Definition any_at_free {LV TV : Type} : type' LV TV :=
  type_ctor any_tag lt_free [].

(* Extend a type context with every variable of a vector, all sharing a
   common bound (used for the n_β operation type-binders). *)
Definition extend_ty_vec {LV TV : Type} {n}
    (GT : ty_ctx LV TV) (vs : Vector.t TV n) (bound : type' LV TV)
    : ty_ctx LV TV :=
  Vector.fold_left (fun G x => extend_ty G x bound) GT vs.

(* Extend a lifetime context with every variable of a vector, all bounded
   by a common lifetime (used for the n_lt fresh match lifetime-binders). *)
Definition extend_lt_vec {LV : Type} {n}
    (GL : lt_ctx LV) (vs : Vector.t LV n) (bound : lifetime' LV)
    : lt_ctx LV :=
  Vector.fold_left (fun G x => extend_lt G x bound) GL vs.

(* ------------------------------------------------------------------ *)
(* Type-level substitution as a two-instantiation PHOAS relation.     *)
(*                                                                    *)
(* These relational judgments pin down the RESULT type of the two     *)
(* elimination rules `T_TyApp`/`T_LtApp`, which substitute the         *)
(* supplied argument into an abstraction body `(TV -> type')` /        *)
(* `(LV -> type')`.  At a fixed instantiation a PHOAS binder body      *)
(* cannot be applied to a full classifier, so — exactly as the term-   *)
(* level `wf`/`subst_has_type` spike — we relate the body under a      *)
(* SECOND copy of the bound-variable namespace, threading a graph that *)
(* maps each source variable to its substitute.  Freshness of inner    *)
(* binders is automatic because the inner variable lives in the second *)
(* copy and shadows the graph.                                         *)
(* ------------------------------------------------------------------ *)

(* type-for-type substitution: lifetimes are untouched. *)
Inductive ty_rel {LV : Type} :
    forall {TV1 TV2 : Type},
    (TV1 -> type' LV TV2 -> Prop) ->
    type' LV TV1 -> type' LV TV2 -> Prop :=
  | TR_Var : forall TV1 TV2 (G : TV1 -> type' LV TV2 -> Prop) X T,
      G X T -> ty_rel G (type_var X) T
  | TR_Fun : forall TV1 TV2 (G : TV1 -> type' LV TV2 -> Prop) A A' l B B',
      ty_rel G A A' -> ty_rel G B B' ->
      ty_rel G (type_fun A l B) (type_fun A' l B')
  | TR_Ctor : forall TV1 TV2 (G : TV1 -> type' LV TV2 -> Prop) K l Ts Ts',
      ty_rel_list G Ts Ts' ->
      ty_rel G (type_ctor K l Ts) (type_ctor K l Ts')
  | TR_LtAll : forall TV1 TV2 (G : TV1 -> type' LV TV2 -> Prop) body body',
      (forall x, ty_rel G (body x) (body' x)) ->
      ty_rel G (type_lt_all body) (type_lt_all body')
  | TR_TyAll : forall TV1 TV2 (G : TV1 -> type' LV TV2 -> Prop)
                      bound bound' body body',
      ty_rel G bound bound' ->
      (forall (X : TV1) (Y : TV2),
         ty_rel (fun X0 T => (X0 = X /\ T = type_var Y) \/ G X0 T)
                (body X) (body' Y)) ->
      ty_rel G (type_ty_all bound body) (type_ty_all bound' body')

with ty_rel_list {LV : Type} :
    forall {TV1 TV2 : Type},
    (TV1 -> type' LV TV2 -> Prop) ->
    list (type' LV TV1) -> list (type' LV TV2) -> Prop :=
  | TRL_nil : forall TV1 TV2 (G : TV1 -> type' LV TV2 -> Prop),
      ty_rel_list G [] []
  | TRL_cons : forall TV1 TV2 (G : TV1 -> type' LV TV2 -> Prop) T T' Ts Ts',
      ty_rel G T T' -> ty_rel_list G Ts Ts' ->
      ty_rel_list G (T :: Ts) (T' :: Ts').

(* lifetime substitution inside lifetimes. *)
Inductive lt_rel {LV1 LV2 : Type} (G : LV1 -> lifetime' LV2 -> Prop) :
    lifetime' LV1 -> lifetime' LV2 -> Prop :=
  | LR_Var : forall x l, G x l -> lt_rel G (lt_var x) l
  | LR_Free : lt_rel G lt_free lt_free
  | LR_Local : lt_rel G lt_local lt_local
  | LR_Min : forall a a' b b',
      lt_rel G a a' -> lt_rel G b b' ->
      lt_rel G (lt_min a b) (lt_min a' b').

(* lifetime-for-lifetime substitution inside types: types untouched. *)
Inductive ty_lt_rel {TV : Type} :
    forall {LV1 LV2 : Type},
    (LV1 -> lifetime' LV2 -> Prop) ->
    type' LV1 TV -> type' LV2 TV -> Prop :=
  | TLR_Var : forall LV1 LV2 (G : LV1 -> lifetime' LV2 -> Prop) X,
      ty_lt_rel G (type_var X) (type_var X)
  | TLR_Fun : forall LV1 LV2 (G : LV1 -> lifetime' LV2 -> Prop) A A' l l' B B',
      ty_lt_rel G A A' -> lt_rel G l l' -> ty_lt_rel G B B' ->
      ty_lt_rel G (type_fun A l B) (type_fun A' l' B')
  | TLR_Ctor : forall LV1 LV2 (G : LV1 -> lifetime' LV2 -> Prop) K l l' Ts Ts',
      lt_rel G l l' -> ty_lt_rel_list G Ts Ts' ->
      ty_lt_rel G (type_ctor K l Ts) (type_ctor K l' Ts')
  | TLR_LtAll : forall LV1 LV2 (G : LV1 -> lifetime' LV2 -> Prop) body body',
      (forall (x : LV1) (y : LV2),
         ty_lt_rel (fun x0 l => (x0 = x /\ l = lt_var y) \/ G x0 l)
                   (body x) (body' y)) ->
      ty_lt_rel G (type_lt_all body) (type_lt_all body')
  | TLR_TyAll : forall LV1 LV2 (G : LV1 -> lifetime' LV2 -> Prop)
                       bound bound' body body',
      ty_lt_rel G bound bound' ->
      (forall X, ty_lt_rel G (body X) (body' X)) ->
      ty_lt_rel G (type_ty_all bound body) (type_ty_all bound' body')

with ty_lt_rel_list {TV : Type} :
    forall {LV1 LV2 : Type},
    (LV1 -> lifetime' LV2 -> Prop) ->
    list (type' LV1 TV) -> list (type' LV2 TV) -> Prop :=
  | TLRL_nil : forall LV1 LV2 (G : LV1 -> lifetime' LV2 -> Prop),
      ty_lt_rel_list G [] []
  | TLRL_cons : forall LV1 LV2 (G : LV1 -> lifetime' LV2 -> Prop) T T' Ts Ts',
      ty_lt_rel G T T' -> ty_lt_rel_list G Ts Ts' ->
      ty_lt_rel_list G (T :: Ts) (T' :: Ts').

Section Typing.
Context {LV TV : Type}.
Context (env : sig_env).

Inductive has_type
    : lt_ctx LV -> ty_ctx LV TV -> tterm LV TV -> type' LV TV -> Prop :=
  | T_Var : forall GL GT T,
      ty_wf GL GT T ->
      has_type GL GT (term_var T) T
  | T_Sub : forall GL GT e S T,
      has_type GL GT e S ->
      sub GL GT S T ->
      has_type GL GT e T
  | T_App : forall GL GT e1 e2 A l B,
      has_type GL GT e1 (type_fun A l B) ->
      has_type GL GT e2 A ->
      has_type GL GT (term_app e1 e2) B
  | T_Lam : forall GL GT A l B body,
      ty_wf GL GT A ->
      ty_wf GL GT B ->
      lt_wf GL l ->
      has_type GL GT (body A) B ->
      has_type GL GT (term_lam A body) (type_fun A l B)
  | T_TyLam : forall GL GT bound body Tbody,
      ty_wf GL GT bound ->
      (forall X, has_type GL (extend_ty GT X bound) (body X) (Tbody X)) ->
      has_type GL GT (term_ty_lam bound body) (type_ty_all bound Tbody)
  | T_LtLam : forall GL GT body Tbody,
      (forall x, has_type (extend_lt GL x lt_local) GT (body x) (Tbody x)) ->
      has_type GL GT (term_lt_lam body) (type_lt_all Tbody)
  | T_TyApp : forall GL GT t bound Tbody S result,
      has_type GL GT t (type_ty_all bound Tbody) ->
      ty_wf GL GT S ->
      sub GL GT S bound ->
      (forall X, ty_rel (fun Y T => Y = X /\ T = S) (Tbody X) result) ->
      has_type GL GT (term_ty_app t S) result
  | T_LtApp : forall GL GT t Tbody l result,
      has_type GL GT t (type_lt_all Tbody) ->
      lt_wf GL l ->
      (forall x, ty_lt_rel (fun y lt => y = x /\ lt = l) (Tbody x) result) ->
      has_type GL GT (term_lt_app t l) result
  | T_Ctor : forall GL GT K sig l lts Ts args fields,
      lookup_ctor_sig env K = Some sig ->
      lookup_eff_sig env K = None ->
      ctor_fields_at sig lts Ts = Some fields ->
      List.length lts = ctor_n_lt sig ->
      List.length Ts = ctor_n_ty sig ->
      Forall (lt_wf GL) lts ->
      types_wf GL GT Ts ->
      lt_wf GL l ->
      lt_sub GL (lt_of_ty_list fields) l ->
      Forall (fun l0 => lt_sub GL l0 l) lts ->
      args_typed GL GT args fields ->
      has_type GL GT (term_ctor K l lts Ts args) (type_ctor K l Ts)

  (* --- Pattern match typing (Figure 7 — Match) -------------------- *)
  (* The yes-branch runs under `n_lt` FRESH lifetime variables (the    *)
  (* existentials packed inside the scrutinee), each bounded by the    *)
  (* scrutinee lifetime Delta, plus `arity` term-binders whose types   *)
  (* are the instantiated field types `fields_fun lts`.  Both branches *)
  (* must agree on the result type.                                    *)
  (*                                                                    *)
  (* FIRST-CUT FAITHFULNESS NOTE: the de Bruijn rule applies `elim_ty_n`*)
  (* to positively eliminate the fresh lifetime vars from the branch   *)
  (* result type.  Here the result type `eta` is required NOT to       *)
  (* mention the fresh lifetimes (it is a single `type' LV TV`, shared *)
  (* by both branches and well-formed in the OUTER context).  This is  *)
  (* exactly the non-escaping case the safety theorem guarantees, and  *)
  (* it subsumes `n_lt = 0` faithfully.  General positive elimination  *)
  (* is left for a later refinement.                                   *)
  | T_Match : forall GL GT scrut K sig Ts Delta result_tag arity
                     yes_body fields_fun eta no_body,
      K <> any_tag ->
      lookup_ctor_sig env K = Some sig ->
      lookup_eff_sig env K = None ->
      List.length Ts = ctor_n_ty sig ->
      types_wf GL GT Ts ->
      lt_wf GL Delta ->
      has_type GL GT scrut (type_ctor result_tag Delta Ts) ->
      result_tag <> any_tag ->
      (forall lts : Vector.t LV (ctor_n_lt sig),
         ctor_fields_vec sig arity (Vector.map lt_var lts) Ts
           = Some (fields_fun lts)) ->
      (forall lts : Vector.t LV (ctor_n_lt sig),
         has_type (extend_lt_vec GL lts Delta) GT
           (yes_body lts (fields_fun lts)) eta) ->
      has_type GL GT no_body eta ->
      has_type GL GT
        (term_match (ctor_n_lt sig) arity scrut K yes_body no_body) eta

  (* --- Effect/handler typing (paper one-plus-one §3) -------------- *)
  (* (Cap): a runtime capability value has type `E local Ts`.  The     *)
  (* op_body lives under n_β type-binders (β-poly, bound `Any free`)   *)
  (* and two self-describing term-binders (the operation argument of   *)
  (* type sig_β and the resumption k : ret_β -local-> T_R).            *)
  | T_Cap : forall GL GT E_tag m Ts sig T_R pfun rfun op_body,
      lookup_eff_sig env E_tag = Some sig ->
      List.length Ts = eff_n_alpha sig ->
      types_wf GL GT Ts ->
      ty_wf GL GT T_R ->
      eff_param_under_betas sig Ts = Some pfun ->
      eff_ret_under_betas sig Ts = Some rfun ->
      (forall betas : Vector.t TV (eff_n_beta sig),
         has_type GL (extend_ty_vec GT betas any_at_free)
           (op_body betas (pfun betas) (type_fun (rfun betas) lt_local T_R)) T_R) ->
      has_type GL GT (term_cap (eff_n_beta sig) E_tag m Ts op_body)
                     (type_ctor E_tag lt_local Ts)

  (* (Handle): allocate a capability and run the body.  Same op-body   *)
  (* obligation as (Cap), plus the body typed against a fresh          *)
  (* capability binder; the result type must not mention `local`.      *)
  | T_Handle : forall GL GT E_tag Ts sig T_R pfun rfun op_body body,
      lookup_eff_sig env E_tag = Some sig ->
      List.length Ts = eff_n_alpha sig ->
      types_wf GL GT Ts ->
      ty_wf GL GT T_R ->
      no_local_ty T_R = true ->
      eff_param_under_betas sig Ts = Some pfun ->
      eff_ret_under_betas sig Ts = Some rfun ->
      (forall betas : Vector.t TV (eff_n_beta sig),
         has_type GL (extend_ty_vec GT betas any_at_free)
           (op_body betas (pfun betas) (type_fun (rfun betas) lt_local T_R)) T_R) ->
      has_type GL GT (body (type_ctor E_tag lt_local Ts)) T_R ->
      has_type GL GT (term_handle (eff_n_beta sig) E_tag Ts op_body body) T_R

  (* (Perform): invoke the operation; the caller supplies β-args Ss.   *)
  | T_Perform : forall GL GT recv arg E_tag Delta Ts Ss sig sig_inst ret_inst,
      has_type GL GT recv (type_ctor E_tag Delta Ts) ->
      lookup_eff_sig env E_tag = Some sig ->
      List.length Ts = eff_n_alpha sig ->
      List.length Ss = eff_n_beta sig ->
      types_wf GL GT Ss ->
      eff_param_at sig Ts Ss = Some sig_inst ->
      eff_ret_at sig Ts Ss = Some ret_inst ->
      has_type GL GT arg sig_inst ->
      has_type GL GT (term_perform recv Ss arg) ret_inst

  (* (HandlerM, runtime): a delimiter is transparent to typing.        *)
  | T_HandlerM : forall GL GT m t T,
      has_type GL GT t T ->
      has_type GL GT (term_handler_m m t) T

  (* (Resume, runtime): a reified resumption is a function value.      *)
  | T_Resume : forall GL GT m b A T_R,
      ty_wf GL GT A ->
      ty_wf GL GT T_R ->
      has_type GL GT (b A) T_R ->
      has_type GL GT (term_resume m b) (type_fun A lt_local T_R)

with args_typed
    : lt_ctx LV -> ty_ctx LV TV -> list (tterm LV TV) -> list (type' LV TV) -> Prop :=
  | AT_nil : forall GL GT,
      args_typed GL GT [] []
  | AT_cons : forall GL GT a sg args sgs,
      has_type GL GT a sg ->
      args_typed GL GT args sgs ->
      args_typed GL GT (a :: args) (sg :: sgs).

End Typing.

(* Runtime-value predicate over closed PHOAS terms. *)
Inductive value : Term -> Prop :=
  | value_lam : forall A body, value (tmLam A body)
  | value_ty_lam : forall bound body, value (tmTyLam bound body)
  | value_lt_lam : forall body, value (tmLtLam body)
  | value_ctor : forall K l lts Ts args,
      Forall value args -> value (tmCtor K l lts Ts args)
  | value_cap : forall n_beta E m Ts op_body,
      value (tmCap n_beta E m Ts op_body)
  | value_resume : forall m body,
      value (tmResume m body).

End Full.
