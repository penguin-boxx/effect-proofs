(* ================================================================== *)
(* SubstitutionTheory.v — standard LN lemma library (skeleton)        *)
(*                                                                    *)
(* Statements are committed; proofs are mostly Admitted.  Most are    *)
(* one- to two-line inductions on the term/type structure (using the  *)
(* custom `type_list_ind` / `term_list_ind` defined here for the      *)
(* nested `list type` / `list term` constructors).                    *)
(*                                                                    *)
(* Sections:                                                          *)
(*   1.  Custom induction principles (mutual list/structure)          *)
(*   2.  open–close inverses                                          *)
(*   3.  open–subst commutation                                       *)
(*   4.  subst preserves lc                                           *)
(*   5.  fv–subst / fv–open subset lemmas                             *)
(*   6.  subst_intro lemmas (open ≡ subst ∘ open(fvar))               *)
(* ================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
Import ListNotations.

From Metalib Require Export Metatheory.
Require Export Substitution.

(* ================================================================== *)
(* SECTION 1 — Custom induction principles                            *)
(* ================================================================== *)

Section TypeListInd.
  Variables (P  : type -> Prop) (Ps : list type -> Prop).
  Hypotheses
    (Hbvar  : forall n, P (type_bvar n))
    (Hfvar  : forall a, P (type_fvar a))
    (Hfun   : forall A l B, P A -> P B -> P (type_fun A l B))
    (Hctor  : forall K l Ts, Ps Ts -> P (type_ctor K l Ts))
    (Hltall : forall A, P A -> P (type_lt_all A))
    (Htyall : forall B A, P B -> P A -> P (type_ty_all B A))
    (Hnil   : Ps [])
    (Hcons  : forall A Ts, P A -> Ps Ts -> Ps (A :: Ts)).
  Fixpoint type_list_ind (T : type) : P T :=
    match T with
    | type_bvar n      => Hbvar n
    | type_fvar a      => Hfvar a
    | type_fun A l B   => Hfun A l B (type_list_ind A) (type_list_ind B)
    | type_ctor K l Ts => Hctor K l Ts
        (list_ind Ps Hnil (fun A _ r => Hcons A _ (type_list_ind A) r) Ts)
    | type_lt_all A    => Hltall A (type_list_ind A)
    | type_ty_all B A  => Htyall B A (type_list_ind B) (type_list_ind A)
    end.
End TypeListInd.

Section TermListInd.
  Variables (P : term -> Prop) (Ps : list term -> Prop).
  Hypotheses
    (Hbvar     : forall n, P (term_bvar n))
    (Hfvar     : forall a, P (term_fvar a))
    (Happ      : forall t1 t2, P t1 -> P t2 -> P (term_app t1 t2))
    (Hlam      : forall body T, P body -> P (term_lam body T))
    (Htyapp    : forall t T, P t -> P (term_ty_app t T))
    (Htylam    : forall bd body, P body -> P (term_ty_lam bd body))
    (Hltapp    : forall t l, P t -> P (term_lt_app t l))
    (Hltlam    : forall body, P body -> P (term_lt_lam body))
    (Hctor     : forall K l ls Ts ts, Ps ts -> P (term_ctor K l ls Ts ts))
    (Hmatch    : forall s K ar y n,
                   P s -> P y -> P n -> P (term_match s K ar y n))
    (Hhandle   : forall E Ts ob body,
                   P ob -> P body -> P (term_handle E Ts ob body))
    (Hperform  : forall t Ss a, P t -> P a -> P (term_perform t Ss a))
    (Hcap      : forall E m Ts ob, P ob -> P (term_cap E m Ts ob))
    (Hhandlerm : forall m t, P t -> P (term_handler_m m t))
    (Hresume   : forall m b, P b -> P (term_resume m b))
    (Hnil      : Ps [])
    (Hcons     : forall t ts, P t -> Ps ts -> Ps (t :: ts)).
  Fixpoint term_list_ind (t : term) : P t :=
    match t with
    | term_bvar n              => Hbvar n
    | term_fvar a              => Hfvar a
    | term_app t1 t2           => Happ t1 t2 (term_list_ind t1) (term_list_ind t2)
    | term_lam body T          => Hlam body T (term_list_ind body)
    | term_ty_app t T          => Htyapp t T (term_list_ind t)
    | term_ty_lam bd body      => Htylam bd body (term_list_ind body)
    | term_lt_app t l          => Hltapp t l (term_list_ind t)
    | term_lt_lam body         => Hltlam body (term_list_ind body)
    | term_ctor K l ls Ts ts   => Hctor K l ls Ts ts
        (list_ind Ps Hnil (fun u _ r => Hcons u _ (term_list_ind u) r) ts)
    | term_match s K ar y n    => Hmatch s K ar y n
        (term_list_ind s) (term_list_ind y) (term_list_ind n)
    | term_handle E Ts ob body => Hhandle E Ts ob body
        (term_list_ind ob) (term_list_ind body)
    | term_perform t Ss a      => Hperform t Ss a
        (term_list_ind t) (term_list_ind a)
    | term_cap E m Ts ob       => Hcap E m Ts ob (term_list_ind ob)
    | term_handler_m m t       => Hhandlerm m t (term_list_ind t)
    | term_resume m b          => Hresume m b (term_list_ind b)
    end.
End TermListInd.

(* ================================================================== *)
(* SECTION 2 — open / close inverses                                  *)
(* ================================================================== *)

Axiom open_lt_wrt_lt_close_lt_wrt_lt : forall l a,
  open_lt_wrt_lt (lt_fvar a) (close_lt_wrt_lt a l) = l.

Axiom close_lt_wrt_lt_open_lt_wrt_lt : forall l a,
  a `notin` fv_lt_in_lt l ->
  close_lt_wrt_lt a (open_lt_wrt_lt (lt_fvar a) l) = l.

Axiom open_ty_wrt_lt_close_ty_wrt_lt : forall T a,
  open_ty_wrt_lt (lt_fvar a) (close_ty_wrt_lt a T) = T.

Axiom close_ty_wrt_lt_open_ty_wrt_lt : forall T a,
  a `notin` fv_lt_in_ty T ->
  close_ty_wrt_lt a (open_ty_wrt_lt (lt_fvar a) T) = T.

Axiom open_ty_wrt_ty_close_ty_wrt_ty : forall T a,
  open_ty_wrt_ty (type_fvar a) (close_ty_wrt_ty a T) = T.

Axiom close_ty_wrt_ty_open_ty_wrt_ty : forall T a,
  a `notin` fv_ty_in_ty T ->
  close_ty_wrt_ty a (open_ty_wrt_ty (type_fvar a) T) = T.

Axiom open_tm_wrt_tm_close_tm_wrt_tm : forall t a,
  open_tm_wrt_tm (term_fvar a) (close_tm_wrt_tm a t) = t.

Axiom close_tm_wrt_tm_open_tm_wrt_tm : forall t a,
  a `notin` fv_tm_in_tm t ->
  close_tm_wrt_tm a (open_tm_wrt_tm (term_fvar a) t) = t.

Axiom open_tm_wrt_ty_close_tm_wrt_ty : forall t a,
  open_tm_wrt_ty (type_fvar a) (close_tm_wrt_ty a t) = t.

Axiom close_tm_wrt_ty_open_tm_wrt_ty : forall t a,
  a `notin` fv_ty_in_tm t ->
  close_tm_wrt_ty a (open_tm_wrt_ty (type_fvar a) t) = t.

Axiom open_tm_wrt_lt_close_tm_wrt_lt : forall t a,
  open_tm_wrt_lt (lt_fvar a) (close_tm_wrt_lt a t) = t.

Axiom close_tm_wrt_lt_open_tm_wrt_lt : forall t a,
  a `notin` fv_lt_in_tm t ->
  close_tm_wrt_lt a (open_tm_wrt_lt (lt_fvar a) t) = t.

(* ================================================================== *)
(* SECTION 3 — subst – open commutation                               *)
(*                                                                    *)
(* The fundamental LN identity: substituting after opening with a     *)
(* fresh atom = opening with the substitution result.                 *)
(* ================================================================== *)

Axiom subst_lt_in_lt_open_lt_wrt_lt_rec : forall l u v a k,
  lc_lifetime u ->
  subst_lt_in_lt u a (open_lt_wrt_lt_rec k v l)
  = open_lt_wrt_lt_rec k (subst_lt_in_lt u a v) (subst_lt_in_lt u a l).

Axiom subst_lt_in_lt_open_lt_wrt_lt : forall l u v a,
  lc_lifetime u ->
  subst_lt_in_lt u a (open_lt_wrt_lt v l)
  = open_lt_wrt_lt (subst_lt_in_lt u a v) (subst_lt_in_lt u a l).

Axiom subst_ty_in_ty_open_ty_wrt_ty : forall T U V a,
  lc_type U ->
  subst_ty_in_ty U a (open_ty_wrt_ty V T)
  = open_ty_wrt_ty (subst_ty_in_ty U a V) (subst_ty_in_ty U a T).

Axiom subst_lt_in_ty_open_ty_wrt_lt : forall T u v a,
  lc_lifetime u ->
  subst_lt_in_ty u a (open_ty_wrt_lt v T)
  = open_ty_wrt_lt (subst_lt_in_lt u a v) (subst_lt_in_ty u a T).

Axiom subst_tm_in_tm_open_tm_wrt_tm : forall t u v a,
  lc_term u ->
  subst_tm_in_tm u a (open_tm_wrt_tm v t)
  = open_tm_wrt_tm (subst_tm_in_tm u a v) (subst_tm_in_tm u a t).

Axiom subst_ty_in_tm_open_tm_wrt_ty : forall t U V a,
  lc_type U ->
  subst_ty_in_tm U a (open_tm_wrt_ty V t)
  = open_tm_wrt_ty (subst_ty_in_ty U a V) (subst_ty_in_tm U a t).

Axiom subst_lt_in_tm_open_tm_wrt_lt : forall t u v a,
  lc_lifetime u ->
  subst_lt_in_tm u a (open_tm_wrt_lt v t)
  = open_tm_wrt_lt (subst_lt_in_lt u a v) (subst_lt_in_tm u a t).

(* Cross-sort: substitution in one sort commutes with opening in another *)
Axiom subst_ty_in_tm_open_tm_wrt_tm : forall t U v a,
  subst_ty_in_tm U a (open_tm_wrt_tm v t)
  = open_tm_wrt_tm (subst_ty_in_tm U a v) (subst_ty_in_tm U a t).

Axiom subst_lt_in_tm_open_tm_wrt_tm : forall t u v a,
  subst_lt_in_tm u a (open_tm_wrt_tm v t)
  = open_tm_wrt_tm (subst_lt_in_tm u a v) (subst_lt_in_tm u a t).

Axiom subst_tm_in_tm_open_tm_wrt_ty : forall t u V a,
  lc_term u ->
  subst_tm_in_tm u a (open_tm_wrt_ty V t)
  = open_tm_wrt_ty V (subst_tm_in_tm u a t).

Axiom subst_tm_in_tm_open_tm_wrt_lt : forall t u v a,
  lc_term u ->
  subst_tm_in_tm u a (open_tm_wrt_lt v t)
  = open_tm_wrt_lt v (subst_tm_in_tm u a t).

(* ================================================================== *)
(* SECTION 4 — subst preserves lc                                     *)
(* ================================================================== *)

Axiom subst_lt_in_lt_lc : forall l u a,
  lc_lifetime l -> lc_lifetime u -> lc_lifetime (subst_lt_in_lt u a l).

Axiom subst_lt_in_ty_lc : forall T u a,
  lc_type T -> lc_lifetime u -> lc_type (subst_lt_in_ty u a T).

Axiom subst_ty_in_ty_lc : forall T U a,
  lc_type T -> lc_type U -> lc_type (subst_ty_in_ty U a T).

Axiom subst_tm_in_tm_lc : forall t u a,
  lc_term t -> lc_term u -> lc_term (subst_tm_in_tm u a t).

Axiom subst_ty_in_tm_lc : forall t U a,
  lc_term t -> lc_type U -> lc_term (subst_ty_in_tm U a t).

Axiom subst_lt_in_tm_lc : forall t u a,
  lc_term t -> lc_lifetime u -> lc_term (subst_lt_in_tm u a t).

(* ================================================================== *)
(* SECTION 5 — fv / subst / open subset lemmas                        *)
(* ================================================================== *)

Axiom subst_lt_in_lt_fresh_eq : forall l u a,
  a `notin` fv_lt_in_lt l -> subst_lt_in_lt u a l = l.

Axiom subst_lt_in_ty_fresh_eq : forall T u a,
  a `notin` fv_lt_in_ty T -> subst_lt_in_ty u a T = T.

Axiom subst_ty_in_ty_fresh_eq : forall T U a,
  a `notin` fv_ty_in_ty T -> subst_ty_in_ty U a T = T.

Axiom subst_tm_in_tm_fresh_eq : forall t u a,
  a `notin` fv_tm_in_tm t -> subst_tm_in_tm u a t = t.

Axiom subst_ty_in_tm_fresh_eq : forall t U a,
  a `notin` fv_ty_in_tm t -> subst_ty_in_tm U a t = t.

Axiom subst_lt_in_tm_fresh_eq : forall t u a,
  a `notin` fv_lt_in_tm t -> subst_lt_in_tm u a t = t.

Axiom fv_lt_in_lt_open_lt_wrt_lt_subset : forall l u,
  fv_lt_in_lt (open_lt_wrt_lt u l)
  [<=] union (fv_lt_in_lt u) (fv_lt_in_lt l).

Axiom fv_ty_in_ty_open_ty_wrt_ty_subset : forall T U,
  fv_ty_in_ty (open_ty_wrt_ty U T)
  [<=] union (fv_ty_in_ty U) (fv_ty_in_ty T).

Axiom fv_tm_in_tm_open_tm_wrt_tm_subset : forall t u,
  fv_tm_in_tm (open_tm_wrt_tm u t)
  [<=] union (fv_tm_in_tm u) (fv_tm_in_tm t).

(* ================================================================== *)
(* SECTION 6 — subst_intro: open via fresh atom + subst               *)
(*                                                                    *)
(* The "barendregt convention" trick used everywhere in induction:    *)
(*   open u t = subst u x (open (fvar x) t)        for fresh x        *)
(* ================================================================== *)

Axiom subst_lt_in_lt_intro : forall (a : atom) l u,
  a `notin` fv_lt_in_lt l ->
  open_lt_wrt_lt u l = subst_lt_in_lt u a (open_lt_wrt_lt (lt_fvar a) l).

Axiom subst_ty_in_ty_intro : forall (a : atom) T U,
  a `notin` fv_ty_in_ty T ->
  open_ty_wrt_ty U T = subst_ty_in_ty U a (open_ty_wrt_ty (type_fvar a) T).

Axiom subst_lt_in_ty_intro : forall (a : atom) T u,
  a `notin` fv_lt_in_ty T ->
  open_ty_wrt_lt u T = subst_lt_in_ty u a (open_ty_wrt_lt (lt_fvar a) T).

Axiom subst_tm_in_tm_intro : forall (a : atom) t u,
  a `notin` fv_tm_in_tm t ->
  open_tm_wrt_tm u t = subst_tm_in_tm u a (open_tm_wrt_tm (term_fvar a) t).

Axiom subst_ty_in_tm_intro : forall (a : atom) t U,
  a `notin` fv_ty_in_tm t ->
  open_tm_wrt_ty U t = subst_ty_in_tm U a (open_tm_wrt_ty (type_fvar a) t).

Axiom subst_lt_in_tm_intro : forall (a : atom) t u,
  a `notin` fv_lt_in_tm t ->
  open_tm_wrt_lt u t = subst_lt_in_tm u a (open_tm_wrt_lt (lt_fvar a) t).

(* ================================================================== *)
(* SECTION 7 — open of lc terms is identity / well-defined            *)
(*                                                                    *)
(* If t is locally closed then opening it does nothing.               *)
(* ================================================================== *)

Axiom open_lt_wrt_lt_lc : forall l u, lc_lifetime l -> open_lt_wrt_lt u l = l.

Axiom open_ty_wrt_ty_lc : forall T U, lc_type T -> open_ty_wrt_ty U T = T.

Axiom open_ty_wrt_lt_lc : forall T u, lc_type T -> open_ty_wrt_lt u T = T.

Axiom open_tm_wrt_tm_lc : forall t u, lc_term t -> open_tm_wrt_tm u t = t.

Axiom open_tm_wrt_ty_lc : forall t U, lc_term t -> open_tm_wrt_ty U t = t.

Axiom open_tm_wrt_lt_lc : forall t u, lc_term t -> open_tm_wrt_lt u t = t.
