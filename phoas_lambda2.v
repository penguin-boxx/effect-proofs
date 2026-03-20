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

Definition subst_type {k_arg} (inner : type k_arg) (outer : type1 k_arg kind_type) : type kind_type :=
  fun tvar => subst_type' (inner tvar) outer.

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
Definition term_ty1 (k_free : kind) (f : type1 k_free kind_type) := 
  forall tvar var (a : tvar k_free), term' (var := var) (f tvar a).
Definition term_abs {arg} {res} (t : term1 arg res) : term (arg c--> res) :=
  fun tvar var => term_abs' (fun x => t tvar var x).
Definition term_tabs
  {k_arg} {f : type1 k_arg kind_type}
  (t : term_ty1 k_arg f) : term (type_all f) :=
  fun tvar var => term_tabs' (fun arg => t tvar var arg).
Definition term_tapp
  {k_arg} {f : type1 k_arg kind_type}
  (t : term (type_all f)) (ty : type k_arg) : term (subst_type ty f) :=
  fun tvar var => term_tapp' f (t tvar var) (ty tvar).
Definition term_app {arg} {res} (f : term (arg c--> res)) (x : term arg) : term res :=
  fun tvar var => term_app' (f tvar var) (x tvar var).

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

Axiom subst_ty_term :
  forall {k_arg} {f : type1 k_arg kind_type},
    term_ty1 k_arg f -> forall (ty : type k_arg), term (subst_type ty f).

Inductive is_value : forall {ty}, term ty -> Prop :=
  | is_value_abs : forall {arg} {res} (f : term1 arg res), is_value (term_abs f)
  | is_value_tabs : 
      forall {k_arg} {f : type1 k_arg kind_type} (t : term_ty1 k_arg f), 
      is_value (term_tabs t).

Hint Constructors is_value.

Reserved Notation "t ==> t'" (no associativity, at level 90).
Inductive step : forall {ty}, term ty -> term ty -> Prop :=
  | step_beta :
      forall arg res (f : term1 arg res) (v : term arg),
      is_value v ->
      term_app (term_abs f) v ==> subst v f
  | step_app1 :
      forall {arg} {res} {t1 : term (arg c--> res)} {t1' : term (arg c--> res)} {t2 : term arg},
      t1 ==> t1' ->
      step (ty := res) (term_app t1 t2) (term_app t1' t2)
  | step_app2 :
      forall {arg} {res} {t1 : term (arg c--> res)} {t2 : term arg} {t2' : term arg},
      t2 ==> t2' ->
      step (ty := res) (term_app t1 t2) (term_app t1 t2')
  | step_tapp :
      forall {k_arg} {f : type1 k_arg kind_type}
        {t : term (type_all f)} {t' : term (type_all f)} (ty_arg : type k_arg),
      t ==> t' ->
      step (ty := subst_type ty_arg f) (term_tapp t ty_arg) (term_tapp t' ty_arg)
  | step_tbeta :
      forall {k_arg} {f : type1 k_arg kind_type} (t : term_ty1 k_arg f) (ty_arg : type k_arg),
      term_tapp (term_tabs t) ty_arg ==> subst_ty_term t ty_arg
  where "t ==> t'" := (step t t').

Hint Constructors step.

(* In an intrinsically typed representation, preservation is free:
   step : forall {ty}, term ty -> term ty -> Prop
   guarantees that the type is preserved by construction. *)
Theorem preservation : forall {ty} (t t' : term ty),
  step t t' ->
  True.
Proof. trivial. Qed.

Inductive closed_term : forall {ty}, term ty -> Prop :=
  | closed_app : forall {arg} {res} (f : term (arg c--> res)) (t : term arg),
      closed_term f ->
      closed_term t ->
      closed_term (term_app f t)
  | closed_abs : forall {arg} {res} (f : term1 arg res),
      closed_term (term_abs f)
  | closed_tabs : forall {k_arg} {f : type1 k_arg kind_type} (t : term_ty1 k_arg f),
      closed_term (term_tabs t)
  | closed_tapp : forall {k_arg} {f : type1 k_arg kind_type} (t : term (type_all f)) (ty_arg : type k_arg),
      closed_term t ->
      closed_term (term_tapp t ty_arg).

Hint Constructors closed_term.

Axiom every_term_closed : forall {ty} (t : term ty), closed_term t.

Axiom canonical_abs :
  forall {arg res} (v : term (arg c--> res)),
    is_value v -> exists f : term1 arg res, v = term_abs f.

Axiom canonical_tabs :
  forall {k_arg} {f : type1 k_arg kind_type} (v : term (type_all f)),
    is_value v -> exists t : term_ty1 k_arg f, v = term_tabs t.

Theorem progress : forall {ty} (t : term ty), 
  closed_term t -> is_value t \/ (exists t', step t t').
Proof. 
  intros. 
  induction H.
  { destruct IHclosed_term1 as [Hvf | [f' Hf']].
    - destruct IHclosed_term2 as [Hvt | [t' Ht']].
      + destruct (canonical_abs f Hvf) as [f0 ->].
        right. exists (subst t f0). eapply step_beta; eauto.
      + right. exists (term_app f t'). eapply step_app2. exact Ht'.
    - right. exists (term_app f' t). eapply step_app1. exact Hf'. }
  { left. constructor. }
  { left. constructor. }
  { destruct IHclosed_term as [Hvt | [t' Ht']].
    - destruct (canonical_tabs t Hvt) as [t0 ->].
      right. exists (subst_ty_term t0 ty_arg). eapply step_tbeta.
    - right. exists (term_tapp t' ty_arg). eapply step_tapp. exact Ht'. }
Qed.
