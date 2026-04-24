From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Strings.String.
Require Import Coq.Unicode.Utf8.
From TLC Require Import LibLN.

Inductive type : Type :=
  | type_fvar (x : var) (* free type variable *)
  | type_bvar (i : nat) (* bound type variable *)
  | type_fun (arg : type) (res : type)
  | type_all (body : type).

Inductive term : Type :=
  | term_bvar (i : nat) (* bound var *)
  | term_fvar (x : var) (* free var *)
  | term_app (lhs : term) (rhs : term)
  | term_lam (body : term)
  | term_tapp (lhs : term) (ty : type)
  | term_tlam (body : term).

Coercion term_bvar : nat >-> term.
Coercion term_fvar : var >-> term.
Coercion type_fvar : var >-> type.

(* Declare Custom Entry mylang.
Notation "<{ e }>" := e (e custom mylang at level 99).
Notation "( x )" := x (in custom mylang, x at level 99).
Notation "'\f' ( A1 , .. , An ) -> T" := (tfun (cons A1 .. (cons An nil) ..) T) 
  (in custom mylang at level 50, 
    A1 custom mylang at level 99,
    An custom mylang at level 99,
    right associativity).
(* Coercion ftvar : nat >-> type. *)

Example term0 : type := <{ \f ( (ftvar 1) ) -> (ftvar 3) }>. *)

Fixpoint open_rec (k : nat) (u : term) (t : term) : term :=
  match t with
  | term_bvar i => if Nat.eqb k i then u else t
  | term_fvar x => t
  | term_app lhs rhs => term_app (open_rec k u lhs) (open_rec k u rhs)
  | term_lam body => term_lam (open_rec (S k) u body)
  | term_tapp lhs ty => term_tapp (open_rec k u lhs) ty
  | term_tlam body => term_tlam (open_rec k u body)
  end.
Definition open t u := open_rec 0 u t.

Notation "{ k ~> u } t" := (open_rec k u t) (at level 67).
Notation "t ^^ u" := (open t u) (at level 67).
Notation "t ^ x" := (open t (term_fvar x)).

Fixpoint open_rec_type (k : nat) (u : type) (t : type) : type :=
  match t with
  | type_bvar i => if Nat.eqb k i then u else t
  | type_fvar x => t
  | type_fun arg res => type_fun (open_rec_type k u arg) (open_rec_type k u res)
  | type_all body => type_all (open_rec_type (S k) u body)
  end.
Definition open_type t u := open_rec_type 0 u t.

Notation "{ k ~>* u } t" := (open_rec_type k u t) (at level 67).
Notation "t ^^* u" := (open_type t u) (at level 67).
Notation "t ^* x" := (open_type t (type_fvar x)) (at level 67).

Inductive is_term : term -> Prop :=
  | is_term_var : forall x,
      is_term (term_fvar x)
  | is_term_lam : forall L t,
      (forall x, x \notin L -> is_term (t ^ x)) ->
      is_term (term_lam t)
  | is_term_app : forall t1 t2,
      is_term t1 ->
      is_term t2 ->
      is_term (term_app t1 t2)
  | is_term_tapp : forall t ty,
      is_term t ->
      is_term (term_tapp t ty)
  | is_term_tlam : forall t,
      is_term t ->
      is_term (term_tlam t).

Inductive is_type : type -> Prop :=
  | is_type_fvar : forall x,
      is_type (type_fvar x)
  | is_type_fun : forall arg res,
      is_type arg ->
      is_type res ->
      is_type (type_fun arg res)
  | is_type_all : forall L body,
      (forall X, X \notin L -> is_type (body ^* X)) ->
      is_type (type_all body).

Inductive value : term -> Prop :=
  | value_lam : forall t, is_term (term_lam t) -> value (term_lam t)
  | value_tlam : forall t, is_term (term_tlam t) -> value (term_tlam t).

Inductive step_beta : term -> term -> Prop :=
  | step_app1 : forall t1 t1' t2,
      step_beta t1 t1' ->
      step_beta (term_app t1 t2) (term_app t1' t2)
  | step_app2 : forall v1 t2 t2',
      value v1 ->
      step_beta t2 t2' ->
      step_beta (term_app v1 t2) (term_app v1 t2')
  | step_red : forall t v,
      value v ->
      is_term t ->
      step_beta (term_app (term_lam t) v) (t ^^ v)
  | step_tapp : forall t t' ty,
      step_beta t t' ->
      step_beta (term_tapp t ty) (term_tapp t' ty)
  | step_tred : forall t ty,
      is_term t ->
      step_beta (term_tapp (term_tlam t) ty) t.

Notation "t --> t'" := (step_beta t t') (at level 68).

Definition ctx := env type.

Reserved Notation "E |= t ~: T" (at level 69).

Inductive typing : ctx -> term -> type -> Prop :=
  | typing_var : forall E x T,
      ok E ->
      binds x T E ->
      E |= (term_fvar x) ~: T
  | typing_lam : forall L E U T t,
      (forall x, x \notin L ->
        (E & x ~ U) |= t ^ x ~: T) ->
      E |= (term_lam t) ~: (type_fun U T)
  | typing_app : forall S T E t1 t2,
      E |= t1 ~: (type_fun S T) ->
      E |= t2 ~: S ->
      E |= (term_app t1 t2) ~: T
  | typing_tlam : forall L E T t,
      E |= t ~: T ->
      E |= (term_tlam t) ~: (type_all T)

where "E |= t ~: T" := (typing E t T).

Definition preservation_statement := forall E t t' T,
  E |= t ~: T ->
  t --> t' ->
  E |= t' ~: T.

Definition progress_statement := forall t T,
  empty |= t ~: T ->
     value t
  \/ exists t', t --> t'.

Fixpoint fv (t : term) : vars :=
  match t with
  | term_bvar i => \{}
  | term_fvar x => \{x}
  | term_app lhs rhs => fv lhs \u fv rhs
  | term_lam body => fv body
  end.

Fixpoint subst (x : var) (u : term) (t : term) : term :=
  match t with
  | term_bvar i => t
  | term_fvar y => If x = y then u else t
  | term_app lhs rhs => term_app (subst x u lhs) (subst x u rhs)
  | term_lam body => term_lam (subst x u body)
  end.

Notation "[ z ~> u ] t" := (subst z u t) (at level 68).

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : ctx => dom x) in
  let D := gather_vars_with (fun x : term => fv x) in
  constr:(A \u B \u C \u D).

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).
Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.
Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.
Tactic Notation "apply_fresh" constr(T) :=
  apply_fresh_base T gather_vars ltac_no_arg.
Tactic Notation "apply_fresh" "*" constr(T) :=
  apply_fresh T; auto_star.

Hint Constructors is_term value step_beta.

Axiom subst_open_var : forall x y u t,
  y <> x -> is_term u ->
  ([x ~> u]t) ^ y = [x ~> u] (t ^ y).

Axiom subst_intro : forall x t u,
  x \notin (fv t) -> is_term u ->
  t ^^ u = [x ~> u](t ^ x).

Local Hint Extern 1 (is_term _) => skip.
Local Hint Extern 1 (ok _) => skip.

Lemma typing_weaken : forall G E F t T,
   (E & G) |= t ~: T ->
   ok (E & F & G) ->
   (E & F & G) |= t ~: T.
Proof.
  introv Typ.
  (* because of limitations to the [induction] tactic,
     (limitations not entirely solved by [dependent induction]),
     we need to manually generalize the parameters of the
     judgment that we perform the induction on. *)
  gen_eq H: (E & G). gen G.
  induction Typ; intros G EQ Ok; subst.
  apply* typing_var. apply* binds_weaken.
  (* --begin case abs-- *)
  (* first we compute [L'], the set of used variables *)
  let L := gather_vars in sets L': L.
  (* now we apply [typing_abs] using [L'] *)
  apply (@typing_lam L').
  (* we can introduce a name [y] such that [y \notin L'] *)
  intros y Fry. subst L'.
  (* to apply the induction hypothesis, we need to rewrite
     the context for associativity *)
  rewrite <- concat_assoc.
  (* now we can apply the induction hypothesis *)
  apply H0.
    auto. (* we can prove [y \notin L] *)
    rewrite concat_assoc. auto.
    rewrite concat_assoc. auto.
  (* --end case abs-- *)
  apply* typing_app.
Qed.

Lemma typing_subst : forall F E t T z u U,
  (E & z ~ U & F) |= t ~: T ->
  E |= u ~: U ->
  (E & F) |= [z ~> u]t ~: T.
Proof.
  introv Typt Typu. gen_eq G: (E & z ~ U & F). gen F.
  induction Typt; intros G Equ; subst; simpl subst.
  case_var.
    binds_get H0. apply_empty* typing_weaken.
    binds_cases H0; apply* typing_var.
  apply_fresh typing_lam as y.
   rewrite* subst_open_var. apply_ih_bind* H0.
  apply* typing_app.
Qed.

Lemma preservation_result : preservation_statement.
Proof.
  introv Typ. gen t'.
  induction Typ; intros t' Red; inversions Red.
  apply* typing_app.
  apply* typing_app.
  inversions Typ1. 
    pick_fresh x. rewrite* (@subst_intro x).
    apply_empty* typing_subst.
Qed.

Lemma progress_result : progress_statement.
Proof.
  introv Typ. gen_eq E: (empty:ctx). lets Typ': Typ.
  induction Typ; intros; subst.
  false* binds_empty_inv.
  left*.
  right. destruct~ IHTyp1 as [Val1 | [t1' Red1]].
    destruct~ IHTyp2 as [Val2 | [t2' Red2]].
      inversions Typ1; inversions Val1. exists* (t ^^ t2).
      exists* (term_app t1 t2').
    exists* (term_app t1' t2).
Qed.


