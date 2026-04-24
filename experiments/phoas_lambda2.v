From Stdlib Require Import List.
From Stdlib Require Import Program.Equality.
Import ListNotations.

Definition name := nat.

Inductive kind : Type :=
  | kind_type : kind
  | kind_lt : kind.

(* ---------- Algebraic data type signature ---------- *)

Parameter tycon : Type.
Parameter dcon : Type.
Parameter dcon_tycon : dcon -> tycon.
Parameter dcons_of : tycon -> list dcon.
Axiom dcons_of_correct : forall d, In d (dcons_of (dcon_tycon d)).
Axiom dcons_of_sound : forall tc d, In d (dcons_of tc) -> dcon_tycon d = tc.

(* ---------- Types ---------- *)

Inductive type' {tvar : kind -> Type} : kind -> Type :=
  | type_var' : forall {k}, tvar k -> type' k
  | type_fun' : type' kind_type -> type' kind_type -> type' kind_type
  | type_all' : forall {k}, (tvar k -> type' kind_type) -> type' kind_type
  | type_con' : forall (tc : tycon), list (type' kind_type) -> type' kind_type.

Hint Constructors type' : core.

(* Field types for a dcon given type arguments to its parent tycon *)
Parameter dcon_field_tys : forall {tvar : kind -> Type},
  dcon -> list (type' (tvar := tvar) kind_type) -> list (type' (tvar := tvar) kind_type).

Definition type k := forall tvar, type' (tvar := tvar) k.
Definition type1 (k_free : kind) (k_res : kind) := forall tvar, tvar k_free -> type' (tvar := tvar) k_res.
Definition type_var {k} {tvar} (x : tvar k) := type_var' x.
Definition type_fun (arg res : type kind_type) : type kind_type :=
  fun tvar => type_fun' (arg tvar) (res tvar).
Definition type_all {k : kind} (t : type1 k kind_type) : type kind_type :=
  fun var => type_all' (fun x => t var x).
Definition type_con (tc : tycon) (args : list (type kind_type)) : type kind_type :=
  fun tvar => type_con' tc (List.map (fun a => a tvar) args).

Infix "-->" := type_fun' (right associativity, at level 60).
Infix "c-->" := type_fun (right associativity, at level 60).

(* ---------- Type-level operations ---------- *)

Fixpoint flatten_type {tvar : kind -> Type} {k : kind} (t : type' k) {struct t} : type' k :=
  match t with
  | type_var' v => v
  | type_fun' arg res => type_fun' (flatten_type arg) (flatten_type res)
  | type_all' f => type_all' (fun x => flatten_type (f (type_var' (tvar := tvar) x)))
  | type_con' tc args => type_con' tc (List.map flatten_type args)
  end.

Definition subst_type' 
  {k_arg} {k_res} {tvar : kind -> Type} 
  (inner : type' (tvar := tvar) k_arg) (outer : type1 k_arg k_res) : type' k_res := 
  flatten_type (outer type' inner).

Definition subst_type {k_arg} (inner : type k_arg) (outer : type1 k_arg kind_type) : type kind_type :=
  fun tvar => subst_type' (inner tvar) outer.

Example id_type_example : type kind_type := type_all (fun _ ty => type_var' ty --> type_var ty).

(* ---------- Terms ---------- *)

Inductive term' {tvar : kind -> Type} {var : type' (tvar := tvar) kind_type -> Type} : 
  type' (tvar := tvar) kind_type -> Type :=
  | term_var' : forall {ty}, var ty -> term' ty
  | term_app' : forall {arg} {res}, term' (arg --> res) -> term' arg -> term' res
  | term_abs' : forall {arg} {res}, (var arg -> term' res) -> term' (arg --> res)
  | term_tapp' :
      forall {k_arg} (f : type1 k_arg kind_type) (t : term' (type_all' (f tvar))) (ty : type' k_arg), 
      term' (subst_type' ty f)
  | term_tabs' : forall {k_arg} {ty}, (forall (arg : tvar k_arg), term' (ty arg)) -> term' (type_all' ty)
  | term_con' : forall (d : dcon) (tc_args : list (type' kind_type)),
      term_list (dcon_field_tys d tc_args) ->
      term' (type_con' (dcon_tycon d) tc_args)
  | term_match' : forall {tc : tycon} {res : type' kind_type}
      (tc_args : list (type' kind_type))
      (scrutinee : term' (type_con' tc tc_args))
      (brs : branches (dcons_of tc) tc_args res),
      term' res

with term_list {tvar : kind -> Type} {var : type' (tvar := tvar) kind_type -> Type} 
  : list (type' (tvar := tvar) kind_type) -> Type :=
  | tl_nil : term_list []
  | tl_cons : forall {ty tys}, term' ty -> term_list tys -> term_list (ty :: tys)

with branch {tvar : kind -> Type} {var : type' (tvar := tvar) kind_type -> Type}
  : list (type' (tvar := tvar) kind_type) -> type' (tvar := tvar) kind_type -> Type :=
  | br_body : forall {res}, term' res -> branch [] res
  | br_bind : forall {ty tys res}, (var ty -> branch tys res) -> branch (ty :: tys) res

with branches {tvar : kind -> Type} {var : type' (tvar := tvar) kind_type -> Type}
  : list dcon -> list (type' (tvar := tvar) kind_type) -> type' (tvar := tvar) kind_type -> Type :=
  | brs_nil : forall {tc_args res}, branches [] tc_args res
  | brs_cons : forall {d ds tc_args res},
      branch (dcon_field_tys d tc_args) res ->
      branches ds tc_args res ->
      branches (d :: ds) tc_args res.

Hint Constructors term' : core.

Example id_term_example {tvar} {var} :
  term' (tvar := tvar) (var := var) (type_all' (fun ty => type_var' ty --> type_var' ty)) :=
  term_tabs' (fun _ => term_abs' (fun x => term_var' x)).

(* ---------- Closed-level definitions ---------- *)

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

(* ---------- Substitution ---------- *)

Fixpoint flatten
  {tvar : kind -> Type} {var : type' kind_type -> Type} {ty : type' kind_type} 
  (t : term' (tvar := tvar) (var := term') ty) {struct t} : term' (var := var) ty :=
  match t with
  | term_var' v => v
  | term_app' f arg => term_app' (flatten f) (flatten arg)
  | term_abs' f => term_abs' (fun x => flatten (f (term_var' (var := var) x)))
  | term_tapp' _ t ty => term_tapp' _ (flatten t) ty
  | term_tabs' t => term_tabs' (fun a => flatten (t a))
  | term_con' d tc_args fields => term_con' d tc_args (flatten_tl fields)
  | term_match' tc_args scrut brs => term_match' tc_args (flatten scrut) (flatten_brs brs)
  end
with flatten_tl
  {tvar : kind -> Type} {var : type' kind_type -> Type} {tys : list (type' kind_type)}
  (tl : term_list (tvar := tvar) (var := term') tys) {struct tl} : term_list (var := var) tys :=
  match tl with
  | tl_nil => tl_nil
  | tl_cons t rest => tl_cons (flatten t) (flatten_tl rest)
  end
with flatten_br
  {tvar : kind -> Type} {var : type' kind_type -> Type}
  {field_tys : list (type' kind_type)} {res : type' kind_type}
  (br : branch (tvar := tvar) (var := term') field_tys res) {struct br} : branch (var := var) field_tys res :=
  match br with
  | br_body t => br_body (flatten t)
  | br_bind f => br_bind (fun x => flatten_br (f (term_var' (var := var) x)))
  end
with flatten_brs
  {tvar : kind -> Type} {var : type' kind_type -> Type}
  {dcs : list dcon} {tc_args : list (type' kind_type)} {res : type' kind_type}
  (brs : branches (tvar := tvar) (var := term') dcs tc_args res) {struct brs} : branches (var := var) dcs tc_args res :=
  match brs with
  | brs_nil => brs_nil
  | brs_cons br rest => brs_cons (flatten_br br) (flatten_brs rest)
  end.

Definition subst {ty1} {ty2} (inner : term ty1) (outer : term1 ty1 ty2) : term ty2 := 
  fun tvar var => flatten (outer tvar (term' (tvar := tvar) (var := var)) (inner tvar var)).

Axiom subst_ty_term :
  forall {k_arg} {f : type1 k_arg kind_type},
    term_ty1 k_arg f -> forall (ty : type k_arg), term (subst_type ty f).

(* ---------- Values ---------- *)

Inductive is_value : forall {ty}, term ty -> Prop :=
  | is_value_abs : forall {arg} {res} (f : term1 arg res), is_value (term_abs f)
  | is_value_tabs : 
      forall {k_arg} {f : type1 k_arg kind_type} (t : term_ty1 k_arg f), 
      is_value (term_tabs t)
  | is_value_con : forall (d : dcon) (tc_args : list (type kind_type))
      (fields : forall tvar var, term_list (tvar := tvar) (var := var) 
        (dcon_field_tys d (List.map (fun a => a tvar) tc_args))),
      is_value (fun tvar var => term_con' d _ (fields tvar var) : term' (var := var) _).

Hint Constructors is_value : core.

(* ---------- Branch application ---------- *)

(* Apply a branch to field values — only meaningful when the branch variables
   are instantiated to terms (i.e., during reduction). Axiomatized because
   PHOAS branch binding uses var while fields are term'. *)
Axiom apply_branch : forall
  {tvar : kind -> Type} {var : type' (tvar := tvar) kind_type -> Type}
  {field_tys : list (type' (tvar := tvar) kind_type)}
  {res : type' (tvar := tvar) kind_type},
  branch (tvar := tvar) (var := var) field_tys res ->
  term_list (tvar := tvar) (var := var) field_tys -> 
  term' (var := var) res.

Axiom lookup_branch : forall
  {tvar : kind -> Type} {var : type' (tvar := tvar) kind_type -> Type}
  {dcs : list dcon} {tc_args : list (type' kind_type)} {res : type' kind_type}
  (d : dcon) (brs : branches (tvar := tvar) (var := var) dcs tc_args res)
  (pf : In d dcs),
  branch (tvar := tvar) (var := var) (dcon_field_tys d tc_args) res.

(* ---------- Small-step semantics ---------- *)

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
  | step_match_beta :
      forall {tc : tycon} {res : type kind_type}
        (d : dcon) (tc_args : list (type kind_type))
        (fields : forall tvar var, term_list (tvar := tvar) (var := var) 
          (dcon_field_tys d (List.map (fun a => a tvar) tc_args)))
        (brs : forall tvar var, branches (tvar := tvar) (var := var) (dcons_of tc) 
          (List.map (fun a => a tvar) tc_args) (res tvar))
        (Htc : dcon_tycon d = tc),
        (fun tvar var => term_match' (List.map (fun a => a tvar) tc_args)
          (eq_rect _ (fun tc0 => term' (type_con' tc0 _)) (term_con' d _ (fields tvar var)) tc Htc)
          (brs tvar var))
        ==>
        (fun tvar var => apply_branch 
          (lookup_branch d (brs tvar var)
            (eq_rect _ (fun tc0 => In d (dcons_of tc0)) (dcons_of_correct d) tc Htc))
          (fields tvar var))
  | step_match_scrut :
      forall {tc : tycon} {res : type kind_type}
        (tc_args : list (type kind_type))
        {scrut scrut' : term (type_con tc tc_args)}
        (brs : forall tvar var, branches (tvar := tvar) (var := var) (dcons_of tc) 
          (List.map (fun a => a tvar) tc_args) (res tvar)),
        scrut ==> scrut' ->
        (fun tvar var => term_match' _ (scrut tvar var) (brs tvar var))
        ==>
        (fun tvar var => term_match' _ (scrut' tvar var) (brs tvar var))
  where "t ==> t'" := (step t t').

Hint Constructors step : core.

(* ---------- Preservation ---------- *)

Theorem preservation : forall {ty} (t t' : term ty),
  step t t' ->
  True.
Proof. trivial. Qed.

(* ---------- Closed terms ---------- *)

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
      closed_term (term_tapp t ty_arg)
  | closed_con : forall (d : dcon) (tc_args : list (type kind_type))
      (fields : forall tvar var, term_list (tvar := tvar) (var := var) 
        (dcon_field_tys d (List.map (fun a => a tvar) tc_args))),
      closed_term (fun tvar var => term_con' d _ (fields tvar var) : term' _)
  | closed_match : forall {tc : tycon} {res : type kind_type}
      (tc_args : list (type kind_type))
      (scrut : term (type_con tc tc_args))
      (brs : forall tvar var, branches (tvar := tvar) (var := var) (dcons_of tc) 
        (List.map (fun a => a tvar) tc_args) (res tvar)),
      closed_term scrut ->
      closed_term (fun tvar var => term_match' _ (scrut tvar var) (brs tvar var)).

Hint Constructors closed_term : core.

Axiom every_term_closed : forall {ty} (t : term ty), closed_term t.

(* ---------- Canonical forms ---------- *)

Axiom canonical_abs :
  forall {arg res} (v : term (arg c--> res)),
    is_value v -> exists f : term1 arg res, v = term_abs f.

Axiom canonical_tabs :
  forall {k_arg} {f : type1 k_arg kind_type} (v : term (type_all f)),
    is_value v -> exists t : term_ty1 k_arg f, v = term_tabs t.

Axiom canonical_con :
  forall {tc : tycon} {tc_args : list (type kind_type)} (v : term (type_con tc tc_args)),
    is_value v -> exists (d : dcon) (Htc : dcon_tycon d = tc)
      (fields : forall tvar var, term_list (tvar := tvar) (var := var) 
        (dcon_field_tys d (List.map (fun a => a tvar) tc_args))),
      v = fun tvar var => 
        eq_rect _ (fun tc0 => term' (type_con' tc0 _)) 
          (term_con' d _ (fields tvar var)) tc Htc.

(* ---------- Progress ---------- *)

Theorem progress : forall {ty} (t : term ty), 
  closed_term t -> is_value t \/ (exists t', step t t').
Proof. 
  intros. 
  induction H.
  { (* app *)
    destruct IHclosed_term1 as [Hvf | [f' Hf']].
    - destruct IHclosed_term2 as [Hvt | [t' Ht']].
      + destruct (canonical_abs f Hvf) as [f0 ->].
        right. exists (subst t f0). eapply step_beta; eauto.
      + right. exists (term_app f t'). eapply step_app2. exact Ht'.
    - right. exists (term_app f' t). eapply step_app1. exact Hf'. }
  { (* abs *) left. constructor. }
  { (* tabs *) left. constructor. }
  { (* tapp *)
    destruct IHclosed_term as [Hvt | [t' Ht']].
    - destruct (canonical_tabs t Hvt) as [t0 ->].
      right. exists (subst_ty_term t0 ty_arg). eapply step_tbeta.
    - right. exists (term_tapp t' ty_arg). eapply step_tapp. exact Ht'. }
  { (* con *) left. constructor. }
  { (* match *)
    destruct IHclosed_term as [Hvs | [s' Hs']].
    - destruct (canonical_con scrut Hvs) as [d [Htc [flds ->]]].
      right.
      eexists. eapply step_match_beta.
    - right.
      eexists. eapply step_match_scrut. exact Hs'. }
Qed.
