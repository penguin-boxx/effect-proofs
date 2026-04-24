From Stdlib Require Import Program.Equality.

Definition name := nat.

Inductive type : Type :=
  | type_var : name -> type
  | type_fun : type -> type -> type.

Hint Constructors type.
Infix "-->" := type_fun (right associativity, at level 60).

Inductive term' {var : type -> Type} : type -> Type :=
  | term_var : forall {ty}, var ty -> term' ty
  | term_app' : forall {arg} {res}, term' (arg --> res) -> term' arg -> term' res
  | term_abs' : forall {arg} {res}, (var arg -> term' res) -> term' (arg --> res).

Hint Constructors term'.
Infix "@" := term_app' (left associativity, at level 50).

Definition term ty := forall var, term' (var := var) ty.
Definition term1 (ty_free : type) (ty : type) := 
  forall var, var ty_free -> term' (var := var) ty. 
Definition term_app {arg} {res} (f : term (arg --> res)) (arg : term arg) : term res :=
  fun var => term_app' (f var) (arg var).
Definition term_abs {arg} {res} (t : term1 arg res) : term (arg --> res) :=
  fun var => term_abs' (fun x => t var x).

Example id_example : term (type_var 0 --> type_var 0) := 
  fun var => term_abs (fun _ x => term_var x) var.

Example id_example2 : term ((type_var 0 --> type_var 0) --> (type_var 0 --> type_var 0)) := 
  fun var => term_abs (fun _ x => term_var x) var.

Fixpoint flatten {var : type -> Type} {ty : type} (t : term' (var := term') ty) {struct t} : term' ty :=
  match t with
  | term_var v => v
  | term_app' f arg => term_app' (flatten f) (flatten arg)
  | term_abs' f => term_abs' (fun x => flatten (f (term_var (var := var) x)))
  end.

Definition subst {ty1} {ty2} (inner : term ty1) (outer : term1 ty1 ty2) : term ty2 := 
  fun var => flatten (outer (term' (var := var)) (inner var)).

Inductive is_value : forall {ty}, term ty -> Prop :=
  | is_value_abs : forall {arg} {res} (f : term1 arg res), is_value (term_abs f).

Hint Constructors is_value.

Reserved Notation "t ==> t'" (no associativity, at level 90).
Inductive step : forall {ty}, term ty -> term ty -> Prop :=
  | step_beta :
      forall arg res (f : term1 arg res) (v : term arg),
      is_value v ->
      term_app (term_abs f) v ==> subst v f
  | step_app1 :
      forall {arg} {res} {t1 : term (arg --> res)} {t1' : term (arg --> res)} {t2 : term arg},
      t1 ==> t1' ->
      step (ty := res) (term_app t1 t2) (term_app t1' t2)
  | step_app2 :
      forall {arg} {res} {t1 : term (arg --> res)} {t2 : term arg} {t2' : term arg},
      t2 ==> t2' ->
      step (ty := res) (term_app t1 t2) (term_app t1 t2')
  where "t ==> t'" := (step t t').

Example step_example : 
  term_app id_example2 id_example ==> id_example.
Proof.
  eapply step_beta; auto. constructor.
Qed.

Hint Constructors step.

Theorem preservation : forall {ty} (t t' : term ty),
  step t t' ->
  True.
Proof. intros. trivial. Qed.

Inductive closed_term : forall {ty}, term ty -> Prop :=
  | closed_app : forall {arg} {res} (f : term (arg --> res)) (t : term arg),
      closed_term f ->
      closed_term t ->
      closed_term (term_app f t)
  | closed_abs : forall {arg} {res} (f : term1 arg res),
      closed_term (term_abs f).

Hint Constructors closed_term.

Axiom every_term_closed : forall {ty} (t : term ty), closed_term t.

Theorem progress : forall {ty} (t : term ty), 
  closed_term t -> is_value t \/ (exists t', step t t').
Proof. 
  intros. 
  induction H.
  { destruct IHclosed_term1; auto; destruct IHclosed_term2; auto.
    { right. inversion H1; subst. simpl_existT; subst. exists (subst t f0). eapply step_beta; auto. }
    { right. destruct H2 as [t' Ht']. exists (term_app f t'). eapply step_app2; auto. }
    { right. destruct H1 as [t' Ht']. exists (term_app t' t). eapply step_app1; auto. }
    { right. destruct H1 as [f' Hf']. exists (term_app f' t). eapply step_app1; auto. } }
  { left. constructor. }
Qed.
