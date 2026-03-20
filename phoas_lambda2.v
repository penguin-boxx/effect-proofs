From Stdlib Require Import Program.Equality.

Definition name := nat.

Inductive kind : Type :=
  | kind_type : kind
  | kind_lt : kind.

Inductive type' {tvar : kind -> Type} : kind -> Type :=
  | type_var' : forall {k}, tvar k -> type' k
  | type_fun' : type' kind_type -> type' kind_type -> type' kind_type
  | type_all' : forall {k}, (tvar k -> type' kind_type) -> type' kind_type.

Hint Constructors type'.

Definition type k := forall tvar, type' (tvar := tvar) k.
Definition type1 (k_free : kind) (k_res : kind) := forall tvar, tvar k_free -> type' (tvar := tvar) k_res.
Definition type_var {k} {tvar} (x : tvar k) := type_var' x.
Definition type_fun (arg res : type kind_type) : type kind_type :=
  fun tvar => type_fun' (arg tvar) (res tvar).
Definition type_all {k : kind} (t : type1 k kind_type) : type kind_type :=
  fun var => type_all' (fun x => t var x).

Infix "-->" := type_fun' (right associativity, at level 60).
Infix "c-->" := type_fun (right associativity, at level 60).

Fixpoint flatten_type {tvar : kind -> Type} {k : kind} (t : type' k) {struct t} : type' k :=
  match t with
  | type_var' v => v
  | type_fun' arg res => type_fun' (flatten_type arg) (flatten_type res)
  | type_all' f => type_all' (fun x => flatten_type (f (type_var' (tvar := tvar) x)))
  end.

Definition subst_type' 
  {k_arg} {k_res} {tvar : kind -> Type} 
  (inner : type' (tvar := tvar) k_arg) (outer : type1 k_arg k_res) : type' k_res := 
  flatten_type (outer type' inner).

Example id_type_example : type kind_type := type_all (fun _ ty => type_var' ty --> type_var ty).

Inductive term' 
  {tvar : kind -> Type} {var : type' (tvar := tvar) kind_type -> Type} : 
  type' (tvar := tvar) kind_type -> Type :=
  | term_var' : forall {ty}, var ty -> term' ty
  | term_app' : forall {arg} {res}, term' (arg --> res) -> term' arg -> term' res
  | term_abs' : forall {arg} {res}, (var arg -> term' res) -> term' (arg --> res)
  | term_tapp' :
      forall {k_arg} (f : type1 k_arg kind_type) (t : term' (type_all' (f tvar))) (ty : type' k_arg), 
      term' (subst_type' ty f)
  | term_tabs' : forall {k_arg} {ty}, (forall (arg : tvar k_arg), term' (ty arg)) -> term' (type_all' ty).

Hint Constructors term'.
Infix "@" := term_app' (left associativity, at level 50).
Infix "t@" := term_tapp' (left associativity, at level 50).

Example id_term_example {tvar} {var} :
  term' (tvar := tvar) (var := var) (type_all' (fun ty => type_var' ty --> type_var' ty)) :=
  term_tabs' (fun _ => term_abs' (fun x => term_var' x)).

Check term_tabs' (fun a =>
  term_tapp' (fun _ b => type_var' b --> type_var' b) id_term_example (type_var' a)) 
  : term' (type_all' (fun a => type_var' a --> type_var' a)).

Check term_tabs' (fun a =>
  term_app'
    (term_tapp' (fun _ b => type_var' b --> type_var' b) id_term_example (type_var' a --> type_var' a))
    (term_tapp' (fun _ b => type_var' b --> type_var' b) id_term_example (type_var' a)))
  : term' (type_all' (fun a => type_var' a --> type_var' a)).

Definition term (ty : type kind_type) := forall tvar var, term' (tvar := tvar) (var := var) (ty tvar).
Definition term1 (ty_free : type kind_type) (ty : type kind_type) := 
  forall tvar var, var (ty_free tvar) -> term' (var := var) (ty tvar).
Definition term_ty1 (k_free : kind) (ty : type kind_type) := 
  forall tvar var, tvar k_free -> term' (var := var) (ty tvar).
Definition term_abs {arg} {res} (t : term1 arg res) : term (arg c--> res) :=
  fun tvar var => term_abs' (fun x => t tvar var x).
Definition term_tabs
  {k_arg} {f : type1 k_arg kind_type}
  (t : term f) : term (type_all f) :=
  fun tvar var => term_tabs' (fun arg => t tvar var arg).
(* Definition term_app {arg} {res} (f : term (arg --> res)) (arg : term arg) : term res :=
  fun var => term_app' (f var) (arg var).
Definition term_tapp 
  {k_arg} {f : type1 k_arg kind_type}
  (t : term (type_all f)) (ty : type k_arg) : term (subst_type ty f) :=
  fun var => term_tapp' (t var) ty.
 *)

Fixpoint flatten
  {tvar : kind -> Type} {var : type' kind_type -> Type} {ty : type' kind_type} 
  (t : term' (tvar := tvar) (var := term') ty) {struct t} : term' ty :=
  match t with
  | term_var' v => v
  | term_app' f arg => term_app' (flatten f) (flatten arg)
  | term_abs' f => term_abs' (fun x => flatten (f (term_var' (var := var) x)))
  | term_tapp' _ t ty => term_tapp' _ (flatten t) ty
  | term_tabs' t => term_tabs' (fun a => flatten (t a))
  end.

Definition subst {ty1} {ty2} (inner : term ty1) (outer : term1 ty1 ty2) : term ty2 := 
  fun tvar var => flatten (outer tvar (term' (tvar := tvar) (var := var)) (inner tvar var)).

Inductive is_value : forall {ty}, term ty -> Prop :=
  | is_value_abs : forall {arg} {res} (f : term1 arg res), is_value (term_abs f)
  | is_value_tabs : forall {k_arg} (f : type1 k_arg kind_type) (t : term_ty1 f), is_value (term_tabs t).

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
