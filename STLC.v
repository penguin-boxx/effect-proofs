Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Relations.
From Stdlib Require Import Logic.FunctionalExtensionality.
Require Import Coq.FSets.FMapList.
Require Import Coq.Unicode.Utf8.


Definition total_map (A : Type) := string -> A.
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.
Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).
Example example_empty := (_ !-> false).
Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition partial_map (A : Type) := total_map (option A).
Definition empty {A : Type} : partial_map A :=
  t_empty None.
Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).
Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).
Notation "x '|->' v" := (update empty x v)
  (at level 100).

Lemma empty_map_none : 
  forall {A : Type} (x : string),
  @empty A x = None.
Proof.
  intros. unfold empty. unfold t_empty. reflexivity.
Qed.

Lemma match_head :
  forall {A : Type} (k : string) (v : A) (m : partial_map A),
  (k |-> v ; m) k = Some v.
Proof.
  intros.
  unfold update. unfold t_update.
  rewrite String.eqb_refl. 
  reflexivity.
Qed.

Lemma no_match_head :
  forall {A : Type} {k k' : string} (v : A) (m : partial_map A),
  k <> k' -> (k |-> v ; m) k' = m k'.
Proof.
  intros.
  unfold update. unfold t_update.
  rewrite <- String.eqb_neq in H. rewrite H.
  reflexivity.
Qed.

Definition includedin {A : Type} (m m' : partial_map A) :=
  ∀ x v, m x = Some v -> m' x = Some v.

Lemma includedin_update : ∀ (A : Type) (m m' : partial_map A)
                                 (x : string) (vx : A),
  includedin m m' ->
  includedin (x |-> vx ; m) (x |-> vx ; m').
Proof. Admitted.
 
Lemma dub_head :
  forall {A : Type} (k k' : string) (v v' : A) (m : partial_map A),
  (k |-> v ; m) k' = (k |-> v ; k |-> v' ; m) k'.
Proof.
  intros.
  destruct (k =? k')%string eqn:E.
  - apply String.eqb_eq in E; subst.
    rewrite match_head. rewrite -> match_head. reflexivity.
  - apply String.eqb_neq in E.
    repeat (rewrite no_match_head); auto.
Qed.

Lemma permut_head :
  forall {A : Type} (k k' k'' : string) (v v' : A) (m : partial_map A),
  k <> k' -> (k |-> v ; k' |-> v' ; m) k'' = (k' |-> v' ; k |-> v ; m) k''.
Proof.
  intros.
  destruct (k =? k'')%string eqn:E1; destruct (k' =? k'')%string eqn:E2;
  try (apply String.eqb_eq in E1); try (apply String.eqb_eq in E2); subst;
  try (apply String.eqb_neq in E1); try (apply String.eqb_neq in E2);
  try contradiction.
  - rewrite match_head. rewrite no_match_head. rewrite match_head. auto. auto.
  - rewrite match_head. rewrite no_match_head; auto. rewrite match_head. auto.
  - repeat (rewrite no_match_head; auto).
Qed.

Inductive ty : Type :=
  | Ty_Bool  : ty
  | Ty_Arrow : ty -> ty -> ty.

Inductive tm : Type :=
  | tm_var   : string -> tm
  | tm_app   : tm -> tm -> tm
  | tm_abs   : string -> ty -> tm -> tm
  | tm_true  : tm
  | tm_false : tm
  | tm_if    : tm -> tm -> tm -> tm.

Declare Custom Entry stlc.
Notation "<{ e }>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.
Notation "'Bool'" := Ty_Bool (in custom stlc at level 0).
Notation "'if' x 'then' y 'else' z" :=
  (tm_if x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := tm_true (in custom stlc at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := tm_false (in custom stlc at level 0).

Definition x : string := "x".
Definition y : string := "y".
Definition z : string := "z".
Hint Unfold x : core.
Hint Unfold y : core.
Hint Unfold z : core.

Notation idB :=
  <{\x:Bool, x}>.
Notation idBB :=
  <{\x:Bool->Bool, x}>.
Notation idBBBB :=
  <{\x:((Bool->Bool)->(Bool->Bool)), x}>.
Notation k := <{\x:Bool, \y:Bool, x}>.
Notation notB := <{\x:Bool, if x then false else true}>.

Inductive value : tm -> Prop :=
  | v_abs : ∀ x T2 t1,
      value <{\x:T2, t1}>
  | v_true :
      value <{true}>
  | v_false :
      value <{false}>.
Hint Constructors value : core.

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tm_var y =>
      if String.eqb x y then s else t
  | <{\y:T, t1}> =>
      if String.eqb x y then t else <{\y:T, [x:=s] t1}>
  | <{t1 t2}> =>
      <{([x:=s] t1) ([x:=s] t2)}>
  | <{true}> =>
      <{true}>
  | <{false}> =>
      <{false}>
  | <{if t1 then t2 else t3}> =>
      <{if ([x:=s] t1) then ([x:=s] t2) else ([x:=s] t3)}>
  end
where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(* Reflexive transitive closure *)
Inductive multi {X : Type} (R : relation X) : X -> X -> Prop :=
  | multi_refl (x : X) : multi R x x
  | multi_step (x y z : X) (head : R x y) (tail : multi R y z) : multi R x z.

Reserved Notation "t '-->' t'" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : ∀ x T2 t1 v2,
         value v2 ->
         <{(\x:T2, t1) v2}> --> <{ [x:=v2]t1 }>
  | ST_App1 : ∀ t1 t1' t2,
         t1 --> t1' ->
         <{t1 t2}> --> <{t1' t2}>
  | ST_App2 : ∀ v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{v1 t2}> --> <{v1  t2'}>
  | ST_IfTrue : ∀ t1 t2,
      <{if true then t1 else t2}> --> t1
  | ST_IfFalse : ∀ t1 t2,
      <{if false then t1 else t2}> --> t2
  | ST_If : ∀ t1 t1' t2 t3,
      t1 --> t1' ->
      <{if t1 then t2 else t3}> --> <{if t1' then t2 else t3}>
where "t '-->' t'" := (step t t').
Hint Constructors step : core.
Notation multistep := (multi step).
Notation "t1 '-->*' t2" := (multistep t1 t2) (at level 40).

Lemma step_example1 :
  <{idBB idB}> -->* idB.
Proof.
  eapply multi_step.
    apply ST_AppAbs.
    apply v_abs.
  simpl.
  apply multi_refl. Qed.

Definition context := partial_map ty.

Reserved Notation "Gamma '|-' t '\in' T"
            (at level 101,
             t custom stlc, T custom stlc at level 0).
Inductive has_type : context -> tm -> ty -> Prop :=
  | T_Var : ∀ Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |- x \in T1
  | T_Abs : ∀ Gamma x T1 T2 t1,
      x |-> T2 ; Gamma |- t1 \in T1 ->
      Gamma |- \x:T2, t1 \in (T2 -> T1)
  | T_App : ∀ T1 T2 Gamma t1 t2,
      Gamma |- t1 \in (T2 -> T1) ->
      Gamma |- t2 \in T2 ->
      Gamma |- t1 t2 \in T1
  | T_True : ∀ Gamma,
       Gamma |- true \in Bool
  | T_False : ∀ Gamma,
       Gamma |- false \in Bool
  | T_If : ∀ t1 t2 t3 T1 Gamma,
       Gamma |- t1 \in Bool ->
       Gamma |- t2 \in T1 ->
       Gamma |- t3 \in T1 ->
       Gamma |- if t1 then t2 else t3 \in T1

where "Gamma '|-' t '\in' T" := (has_type Gamma t T).
Hint Constructors has_type : core.

Lemma canonical_forms_bool : ∀ t,
  empty |- t \in Bool ->
  value t ->
  (t = <{true}>) \/ (t = <{false}>).
Proof.
  intros t typing val.
  destruct val; auto.
  inversion typing.
Qed.

Lemma canonical_forms_fun : ∀ t T1 T2,
  empty |- t \in (T1 -> T2) ->
  value t ->
  exists x u, t = <{\x:T1, u}>.
Proof.
  intros t T1 T2 HT HVal.
  destruct HVal as [x ? t1| |]; inversion HT; subst.
  exists x, t1. reflexivity.
Qed.

Theorem progress : ∀ t T,
  empty |- t \in T ->
  value t \/ exists t', t --> t'.
Proof.
  intros t T HTy.
  remember empty as G.
  induction HTy as [? ? ? H| | | | |].
  - subst. discriminate H.
  - left. constructor.
  - destruct IHHTy1 as [HVal1 | HStep1]; 
    destruct IHHTy2 as [HVal2 | HStep2]; auto.
    + right. inversion HVal1; subst; simpl in *; 
      try (exists <{ [x0 := t2] t0 }>; econstructor; assumption); 
      inversion HTy1.
    + right. destruct HStep2 as [t2' HStep2']. exists <{ t1 t2' }>. 
      econstructor; auto.
    + right. destruct HStep1 as [t1' HStep1']. exists <{ t1' t2 }>.
      econstructor. assumption.
    + right. destruct HStep1 as [t1' HStep1']. exists <{ t1' t2 }>.
      econstructor. assumption.
  - left. constructor.
  - left. econstructor.
  - destruct IHHTy1 as [HValT1 | [t1' HStepT1]]; auto.
    + right. subst. inversion HValT1.
      * subst. inversion HTy1.
      * exists t2. constructor.
      * exists t3. constructor.
    + right. exists <{ if t1' then t2 else t3 }>. constructor. assumption.
Qed.

Lemma weakening : ∀ Gamma Gamma' t T,
     includedin Gamma Gamma' ->
     Gamma  |- t \in T  ->
     Gamma' |- t \in T.
Proof.
  intros Gamma Gamma' t T H Ht.
  generalize dependent Gamma'.
  induction Ht; eauto using includedin_update.
Qed.

Lemma weakening_empty : ∀ Gamma t T,
     empty |- t \in T  ->
     Gamma |- t \in T.
Proof.
  intros Gamma t T.
  eapply weakening.
  discriminate.
Qed.

Lemma same_head_typing {x : string} {t : tm} {T T1 T2 : ty} {Gamma : partial_map ty}
  (HTy : (x |-> T1 ; x |-> T2 ; Gamma |- t \in T)) : (x |-> T1 ; Gamma |- t \in T).
Proof.
  remember (x |-> T1 ; x |-> T2 ; Gamma) as Gamma'.
  generalize dependent Gamma.
  generalize dependent x.
  generalize dependent T1.
  induction HTy; intros T1' x' Gamma' Geq; subst; eauto.
  - constructor. rewrite <- H. apply dub_head.
  - constructor. apply IHHTy. apply functional_extensionality. intro. erewrite <- dub_head.
    destruct (x0 =? x1)%string eqn:E.
    + apply String.eqb_eq in E; subst. rewrite match_head. rewrite match_head. reflexivity.
    + apply String.eqb_neq in E. rewrite no_match_head. symmetry. 
      rewrite no_match_head. apply dub_head. auto. auto.
Qed.

Lemma substitution_preserves_typing_from_typing_ind : ∀ Gamma x U t v T,
  x |-> U ; Gamma |- t \in T ->
  empty |- v \in U   ->
  Gamma |- [x:=v]t \in T.
Proof.
  intros Gamma x U t v T HTy_t HTy_v.
  remember (x |-> U; Gamma) as Gamma'.
  generalize dependent Gamma.
  induction HTy_t; intros Gamma' GEq; subst;  simpl; eauto.
  - destruct (x =? x0)%string eqn:E.
    + apply String.eqb_eq in E. subst. rewrite match_head in H. 
      inversion H. subst. apply weakening_empty. assumption.
    + constructor. apply String.eqb_neq in E. rewrite (no_match_head U Gamma' E) in H.
      assumption.
  - destruct (x =? x0)%string eqn:E.
    + rewrite String.eqb_eq in E; subst. constructor. eapply same_head_typing. eassumption.
    + apply String.eqb_neq in E. 
      constructor. apply IHHTy_t. apply functional_extensionality. intro x'. apply permut_head. auto.
Qed.

