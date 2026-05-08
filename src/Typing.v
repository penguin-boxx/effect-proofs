(* ================================================================== *)
(* Typing.v — typing relation (locally nameless)                      *)
(*                                                                    *)
(* Each binding in the context carries an `atom` naming the variable, *)
(* so context lookup is by atom (not de Bruijn index).                *)
(*                                                                    *)
(* Binder rules use COFINITE quantification:                          *)
(*   forall L : atoms, forall x, x `notin` L ->                       *)
(*     (bind_* x ... :: Γ) ⊢ open_* (...fvar x) body : ...            *)
(* ================================================================== *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
Import ListNotations.

From Metalib Require Export Metatheory.
Require Export Syntax.
Require Export Substitution.

(* ================================================================== *)
(* Typing context                                                     *)
(* ================================================================== *)

Inductive binding : Type :=
  | bind_tm   : atom -> type -> binding                  (* x : T        *)
  | bind_ty   : atom -> type -> binding                  (* α <: B       *)
  | bind_lt   : atom -> lifetime -> binding              (* l <: Δ       *)
  (* Constructor schema:                                                 *)
  (*   K : ∀ l̄ ᾱ. τ̄ → T@(...)                                            *)
  (*   n_lt / n_ty are the numbers of lt / ty binders;                   *)
  (*   field_schemas / result_schema have those binders open ABOVE       *)
  (*   any de Bruijn slots they introduce inside themselves.             *)
  | bind_ctor : ctor_tag -> nat -> nat -> list type -> type -> binding
  (* Effect declaration with single op:                                  *)
  (*   effect E<n_α> { op : ∀n_β βs. sig → ret }                         *)
  | bind_eff  : eff_tag -> nat -> nat -> type -> type -> binding
  .

Definition ctx := list binding.

(* --- Context lookup by atom --- *)

Fixpoint ctx_lookup_tm (Γ : ctx) (x : atom) : option type :=
  match Γ with
  | []                  => None
  | bind_tm y T :: rest => if x == y then Some T else ctx_lookup_tm rest x
  | _ :: rest           => ctx_lookup_tm rest x
  end.

Fixpoint ctx_lookup_ty (Γ : ctx) (a : atom) : option type :=
  match Γ with
  | []                  => None
  | bind_ty b B :: rest => if a == b then Some B else ctx_lookup_ty rest a
  | _ :: rest           => ctx_lookup_ty rest a
  end.

Fixpoint ctx_lookup_lt (Γ : ctx) (a : atom) : option lifetime :=
  match Γ with
  | []                  => None
  | bind_lt b Δ :: rest => if a == b then Some Δ else ctx_lookup_lt rest a
  | _ :: rest           => ctx_lookup_lt rest a
  end.

Fixpoint ctx_lookup_ctor (Γ : ctx) (K : ctor_tag)
    : option (nat * nat * list type * type) :=
  match Γ with
  | [] => None
  | bind_ctor K' n_lt n_ty fields result :: rest =>
      if Nat.eqb K K' then Some (n_lt, n_ty, fields, result)
      else ctx_lookup_ctor rest K
  | _ :: rest => ctx_lookup_ctor rest K
  end.

Fixpoint ctx_lookup_eff (Γ : ctx) (E : eff_tag)
    : option (nat * nat * type * type) :=
  match Γ with
  | [] => None
  | bind_eff E' n_α n_β sig ret :: rest =>
      if Nat.eqb E E' then Some (n_α, n_β, sig, ret)
      else ctx_lookup_eff rest E
  | _ :: rest => ctx_lookup_eff rest E
  end.

(* All atoms bound (in any namespace) by Γ.  Used by gather_atoms and  *)
(* by cofinite freshness side conditions.                              *)
Fixpoint dom_ctx (Γ : ctx) : atoms :=
  match Γ with
  | []                  => empty
  | bind_tm  x _ :: rest => add x (dom_ctx rest)
  | bind_ty  a _ :: rest => add a (dom_ctx rest)
  | bind_lt  a _ :: rest => add a (dom_ctx rest)
  | bind_ctor _ _ _ _ _ :: rest => dom_ctx rest
  | bind_eff  _ _ _ _ _ :: rest => dom_ctx rest
  end.

(* ================================================================== *)
(* Lifetime subtyping                                                 *)
(* ================================================================== *)

Reserved Notation "G '|-l' l1 '<:' l2" (at level 70, l1 at next level).

Inductive lt_sub : ctx -> lifetime -> lifetime -> Prop :=

  | LS_Free  : forall Γ l, Γ |-l lt_free <: l

  | LS_Local : forall Γ l, Γ |-l l <: lt_local

  | LS_Var   : forall Γ a Δ,
      ctx_lookup_lt Γ a = Some Δ ->
      Γ |-l lt_fvar a <: Δ

  | LS_Refl  : forall Γ l, Γ |-l l <: l

  | LS_Trans : forall Γ l1 l2 l3,
      Γ |-l l1 <: l2 -> Γ |-l l2 <: l3 -> Γ |-l l1 <: l3

  (* lt_min is the join: above both, and least such *)
  | LS_MinL  : forall Γ l1 l2 l,
      Γ |-l l1 <: l -> Γ |-l l2 <: l -> Γ |-l lt_min l1 l2 <: l

  | LS_MinR1 : forall Γ l l1 l2,
      Γ |-l l <: l1 -> Γ |-l l <: lt_min l1 l2

  | LS_MinR2 : forall Γ l l1 l2,
      Γ |-l l <: l2 -> Γ |-l l <: lt_min l1 l2

where "G '|-l' l1 '<:' l2" := (lt_sub G l1 l2).

#[export] Hint Constructors lt_sub : core.

(* ================================================================== *)
(* lt_of_ty                                                           *)
(*                                                                    *)
(* Bottom approximation of a type's lifetime restrictions.            *)
(* Type variables (free or bound) contribute lt_free.                 *)
(* Quantified types contribute lt_free.                               *)
(* ================================================================== *)

Fixpoint lt_of_ty (T : type) : lifetime :=
  let fix go (Ts : list type) : lifetime :=
    match Ts with
    | []        => lt_free
    | A :: rest => lt_min (lt_of_ty A) (go rest)
    end
  in
  match T with
  | type_bvar _      => lt_free
  | type_fvar _      => lt_free
  | type_fun _ l _   => l
  | type_ctor _ l Ts => lt_min l (go Ts)
  | type_lt_all _    => lt_free
  | type_ty_all _ _  => lt_free
  end.

Definition lt_of_ty_list (Ts : list type) : lifetime :=
  fold_right (fun T acc => lt_min (lt_of_ty T) acc) lt_free Ts.

(* Γ-aware variant: type variables look up their bound in Γ (with     *)
(* fuel = |Γ| to bound chains through bind_ty entries).                *)
Fixpoint lt_of_ty_ctx (fuel : nat) (Γ : ctx) (T : type) : lifetime :=
  match fuel with
  | O =>
      match T with
      | type_fun _ l _   => l
      | type_ctor _ l _  => l
      | _                => lt_free
      end
  | S fuel' =>
      let fix go (Ts : list type) : lifetime :=
        match Ts with
        | []        => lt_free
        | A :: rest => lt_min (lt_of_ty_ctx fuel' Γ A) (go rest)
        end
      in
      match T with
      | type_fvar a =>
          match ctx_lookup_ty Γ a with
          | Some B => lt_of_ty_ctx fuel' Γ B
          | None   => lt_free
          end
      | type_bvar _      => lt_free
      | type_fun _ l _   => l
      | type_ctor _ l Ts => lt_min l (go Ts)
      | type_lt_all _    => lt_free
      | type_ty_all _ _  => lt_free
      end
  end.

Definition lt_of_ty_G (Γ : ctx) (T : type) : lifetime :=
  lt_of_ty_ctx (length Γ) Γ T.

(* ================================================================== *)
(* "no local" syntactic check (T_Lam side condition)                  *)
(* ================================================================== *)

Fixpoint no_local_lt (l : lifetime) : bool :=
  match l with
  | lt_local     => false
  | lt_min l1 l2 => andb (no_local_lt l1) (no_local_lt l2)
  | _            => true
  end.

Fixpoint no_local_ty (T : type) : bool :=
  let fix go (Ts : list type) : bool :=
    match Ts with
    | []        => true
    | A :: rest => andb (no_local_ty A) (go rest)
    end
  in
  match T with
  | type_bvar _      => true
  | type_fvar _      => true
  | type_fun A l B   => andb (no_local_ty A) (andb (no_local_lt l) (no_local_ty B))
  | type_ctor _ l Ts => andb (no_local_lt l) (go Ts)
  | type_lt_all A    => no_local_ty A
  | type_ty_all B A  => andb (no_local_ty B) (no_local_ty A)
  end.

(* ================================================================== *)
(* Capture lifetime                                                   *)
(*                                                                    *)
(* In LN this is the lt-meet over types of free term-atoms in `body`. *)
(* ================================================================== *)

(* List-based free-tm-atoms collection.  Reduces by `cbn` to a        *)
(* concrete list normal form (no AtomSetImpl folding required).       *)
(* Duplicates are harmless: lt_min is idempotent.                      *)
Fixpoint fv_tm_in_tm_list (t : term) : list atom :=
  let fix go (ts : list term) : list atom :=
    match ts with
    | []        => []
    | u :: rest => fv_tm_in_tm_list u ++ go rest
    end
  in
  match t with
  | term_bvar _              => []
  | term_fvar a              => [a]
  | term_app t1 t2           => fv_tm_in_tm_list t1 ++ fv_tm_in_tm_list t2
  | term_lam body _          => fv_tm_in_tm_list body
  | term_ty_app t _          => fv_tm_in_tm_list t
  | term_ty_lam _ body       => fv_tm_in_tm_list body
  | term_lt_app t _          => fv_tm_in_tm_list t
  | term_lt_lam body         => fv_tm_in_tm_list body
  | term_ctor _ _ _ _ ts     => go ts
  | term_match s _ _ y n     =>
      fv_tm_in_tm_list s ++ fv_tm_in_tm_list y ++ fv_tm_in_tm_list n
  | term_handle _ _ ob body  => fv_tm_in_tm_list ob ++ fv_tm_in_tm_list body
  | term_perform t _ a       => fv_tm_in_tm_list t ++ fv_tm_in_tm_list a
  | term_cap _ _ _ ob        => fv_tm_in_tm_list ob
  | term_handler_m _ t       => fv_tm_in_tm_list t
  | term_resume _ b          => fv_tm_in_tm_list b
  end.

Definition capture_lt (Γ : ctx) (body : term) : lifetime :=
  fold_right
    (fun (x : atom) (acc : lifetime) =>
       lt_min
         (match ctx_lookup_tm Γ x with
          | Some T => lt_of_ty_G Γ T
          | None   => lt_free
          end)
         acc)
    lt_free
    (fv_tm_in_tm_list body).

(* ================================================================== *)
(* Variance / elim_var                                                *)
(*                                                                    *)
(* In LN, eliminating a fresh lt-atom `a` means walking the type and  *)
(* replacing `lt_fvar a` by either the supplied `bound` (positive),   *)
(* `lt_free` (negative), or signaling failure (invariant).            *)
(* ================================================================== *)

Inductive variance : Type :=
  | var_pos : variance
  | var_neg : variance
  | var_inv : variance
  .

Definition flip_var (p : variance) : variance :=
  match p with
  | var_pos => var_neg
  | var_neg => var_pos
  | var_inv => var_inv
  end.

Fixpoint elim_lt_at (a : atom) (bound : lifetime) (p : variance) (l : lifetime)
    : option lifetime :=
  match l with
  | lt_fvar b =>
      if a == b then
        match p with
        | var_pos => Some bound
        | var_neg => Some lt_free
        | var_inv => None
        end
      else Some (lt_fvar b)
  | lt_bvar _    => Some l
  | lt_free      => Some lt_free
  | lt_local     => Some lt_local
  | lt_min l1 l2 =>
      match elim_lt_at a bound p l1, elim_lt_at a bound p l2 with
      | Some l1', Some l2' => Some (lt_min l1' l2')
      | _, _               => None
      end
  end.

Fixpoint elim_ty_at (a : atom) (bound : lifetime) (p : variance) (T : type)
    : option type :=
  let fix go (p' : variance) (Ts : list type) : option (list type) :=
    match Ts with
    | []        => Some []
    | A :: rest =>
        match elim_ty_at a bound p' A, go p' rest with
        | Some A', Some rest' => Some (A' :: rest')
        | _, _                => None
        end
    end
  in
  match T with
  | type_bvar _      => Some T
  | type_fvar _      => Some T
  | type_fun A l B   =>
      match elim_ty_at a bound (flip_var p) A,
            elim_lt_at a bound p l,
            elim_ty_at a bound p B with
      | Some A', Some l', Some B' => Some (type_fun A' l' B')
      | _, _, _ => None
      end
  | type_ctor K l Ts =>
      match elim_lt_at a bound p l, go var_inv Ts with
      | Some l', Some Ts' => Some (type_ctor K l' Ts')
      | _, _ => None
      end
  | type_lt_all A    =>
      match elim_ty_at a bound p A with
      | Some A' => Some (type_lt_all A')
      | None    => None
      end
  | type_ty_all B A  =>
      match elim_ty_at a bound (flip_var p) B,
            elim_ty_at a bound p A with
      | Some B', Some A' => Some (type_ty_all B' A')
      | _, _ => None
      end
  end.

(* Eliminate a list of fresh lt-atoms in left-to-right order.         *)
Fixpoint elim_ty_atoms (xs : list atom) (bound : lifetime) (p : variance) (T : type)
    : option type :=
  match xs with
  | []      => Some T
  | x :: rest =>
      match elim_ty_at x bound p T with
      | None    => None
      | Some T' => elim_ty_atoms rest bound p T'
      end
  end.

(* ================================================================== *)
(* Type subtyping                                                     *)
(* ================================================================== *)

Reserved Notation "G '|-T' S '<:' T" (at level 70, S at next level).

Inductive sub : ctx -> type -> type -> Prop :=

  | SA_Refl   : forall Γ T, Γ |-T T <: T

  | SA_Trans  : forall Γ S U T,
      Γ |-T S <: U -> Γ |-T U <: T -> Γ |-T S <: T

  | SA_VarCtx : forall Γ a B,
      ctx_lookup_ty Γ a = Some B ->
      Γ |-T type_fvar a <: B

  | SA_Data   : forall Γ K l l' Ts,
      Γ |-l l <: l' ->
      Γ |-T type_ctor K l Ts <: type_ctor K l' Ts

  | SA_Any    : forall Γ T Δ,
      Γ |-l lt_of_ty_G Γ T <: Δ ->
      Γ |-T T <: type_ctor any_tag Δ []

  | SA_Fun    : forall Γ A A' l l' B B',
      Γ |-T A <: A' ->
      Γ |-l l <: l' ->
      Γ |-T B <: B' ->
      Γ |-T type_fun A' l B <: type_fun A l' B'

  | SA_LtAll  : forall (L : atoms) Γ A A',
      (forall a, a `notin` L ->
        (bind_lt a lt_local :: Γ) |-T
          open_ty_wrt_lt (lt_fvar a) A <: open_ty_wrt_lt (lt_fvar a) A') ->
      Γ |-T type_lt_all A <: type_lt_all A'

  | SA_TyAll  : forall (L : atoms) Γ B B' A A',
      Γ |-T B' <: B ->
      (forall a, a `notin` L ->
        (bind_ty a B' :: Γ) |-T
          open_ty_wrt_ty (type_fvar a) A <:
          open_ty_wrt_ty (type_fvar a) A') ->
      Γ |-T type_ty_all B A <: type_ty_all B' A'

where "G '|-T' S '<:' T" := (sub G S T).

#[export] Hint Constructors sub : core.

(* ================================================================== *)
(* Helpers: instantiate a multi-binder schema                         *)
(* ================================================================== *)

(* A constructor schema's field/result type is a `type` with n_lt     *)
(* outermost lt-binders and n_ty inner ty-binders.  To instantiate it *)
(* with concrete `lts : list lifetime` (length n_lt) and              *)
(* `Us : list type` (length n_ty), open the lt-binders first (since   *)
(* they are outer) and then the ty-binders.                           *)
Definition inst_ctor_type (lts : list lifetime) (Us : list type) (T : type) : type :=
  open_ty_wrt_ty_list Us (open_ty_wrt_lt_list lts T).

(* Instantiate the n_α + n_β type binders of an op schema. Convention *)
(* (matching the legacy):  α-binders are innermost (opened by Ts),    *)
(* β-binders are outermost (opened by Ss).                            *)
Definition inst_op_type (Ts Ss : list type) (T : type) : type :=
  open_ty_wrt_ty_list Ts (open_ty_wrt_ty_list Ss T).

(* Push n fresh lt-binders all bounded by `bound` onto Γ, naming them *)
(* with the supplied list of atoms (left-to-right = outer-to-inner).  *)
Fixpoint push_lt_atoms (xs : list atom) (bound : lifetime) (Γ : ctx) : ctx :=
  match xs with
  | []      => Γ
  | x :: rest => push_lt_atoms rest bound (bind_lt x bound :: Γ)
  end.

Fixpoint push_ty_atoms (xs : list atom) (bound : type) (Γ : ctx) : ctx :=
  match xs with
  | []      => Γ
  | x :: rest => push_ty_atoms rest bound (bind_ty x bound :: Γ)
  end.

Fixpoint push_tm_atoms (xs : list atom) (Ts : list type) (Γ : ctx) : ctx :=
  match xs, Ts with
  | x :: rxs, T :: rts => push_tm_atoms rxs rts (bind_tm x T :: Γ)
  | _, _               => Γ
  end.

(* The β-bound type used at handle-time: Any@free.                     *)
Definition any_at_free : type := type_ctor any_tag lt_free [].

(* ================================================================== *)
(* Typing relation                                                    *)
(* ================================================================== *)

Reserved Notation "G '|-t' t ':' T" (at level 70, t at next level).

Inductive typing : ctx -> term -> type -> Prop :=

  | T_Var   : forall Γ x T,
      ctx_lookup_tm Γ x = Some T ->
      Γ |-t term_fvar x : T

  | T_Sub   : forall Γ t T U,
      Γ |-t t : T ->
      Γ |-T T <: U ->
      Γ |-t t : U

  (* Term abstraction (cofinite). Closure lifetime ≥ capture lt;      *)
  (* return type contains no `local`.                                 *)
  | T_Lam   : forall (L : atoms) Γ body A l B,
      (forall x, x `notin` L ->
         (bind_tm x A :: Γ) |-t open_tm_wrt_tm (term_fvar x) body : B) ->
      Γ |-l capture_lt Γ body <: l ->
      Γ |-t term_lam body A : type_fun A l B

  | T_App   : forall Γ t1 t2 A l B,
      Γ |-t t1 : type_fun A l B ->
      Γ |-t t2 : A ->
      Γ |-t term_app t1 t2 : B

  (* Type abstraction (cofinite). *)
  | T_TyLam : forall (L : atoms) Γ bound body T,
      (forall a, a `notin` L ->
         (bind_ty a bound :: Γ) |-t
           open_tm_wrt_ty (type_fvar a) body :
           open_ty_wrt_ty (type_fvar a) T) ->
      Γ |-t term_ty_lam bound body : type_ty_all bound T

  | T_TyApp : forall Γ t B U S,
      Γ |-t t : type_ty_all B U ->
      Γ |-T S <: B ->
      Γ |-t term_ty_app t S : open_ty_wrt_ty S U

  (* Lifetime abstraction (cofinite, bound = ⊤ = lt_local). *)
  | T_LtLam : forall (L : atoms) Γ body T,
      (forall a, a `notin` L ->
         (bind_lt a lt_local :: Γ) |-t
           open_tm_wrt_lt (lt_fvar a) body :
           open_ty_wrt_lt (lt_fvar a) T) ->
      Γ |-t term_lt_lam body : type_lt_all T

  | T_LtApp : forall Γ t T l,
      Γ |-t t : type_lt_all T ->
      Γ |-t term_lt_app t l : open_ty_wrt_lt l T

  (* Constructor.                                                      *)
  (* The schema's field types `sigma_fields` live under (n_lt + n_ty) *)
  (* binders; instantiate with the supplied `lts` and `Ts` to get the *)
  (* concrete field types `rho_fields`.  The resulting *type* is the  *)
  (* schema's result, also instantiated.  Several value-ctors (a sum) *)
  (* may share the same declared type by having a common result-head *)
  (* `K_res` (e.g. `Get` and `Put` both produce `Cmd`).                *)
  | T_Ctor  : forall Γ K n_lt n_ty sigma_fields
                     K_res lr_schema Ts_res_schema
                     lts Ts rho_fields l vs lr_inst Ts_res_inst,
      ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields,
                                   type_ctor K_res lr_schema Ts_res_schema) ->
      ctx_lookup_eff  Γ K = None ->
      length lts = n_lt ->
      length Ts  = n_ty ->
      rho_fields = List.map (inst_ctor_type lts Ts) sigma_fields ->
      l = lt_of_ty_list rho_fields ->
      length vs = length rho_fields ->
      Forall2 (fun v rho => Γ |-t v : rho) vs rho_fields ->
      inst_ctor_type lts Ts (type_ctor K_res lr_schema Ts_res_schema)
        = type_ctor K_res lr_inst Ts_res_inst ->
      Γ |-t term_ctor K l lts Ts vs : type_ctor K_res lr_inst Ts_res_inst

  (* Pattern match.                                                    *)
  (* The scrutinee inhabits the schema's result type — i.e.            *)
  (* `type_ctor K_res Delta Ts_res_inst` where `K_res` is the head    *)
  (* of K's declared result type.  Note this `K_res` is not the       *)
  (* value-ctor tag `K` (sum types: `Get`/`Put` share head `Cmd`).    *)
  (*                                                                  *)
  (* Inside the yes branch we still introduce n_lt FRESH lt-atoms     *)
  (* (cofinite) to play the role of K's schema's lt-binders, and     *)
  (* eliminate them (positive, with bound Delta) afterwards.          *)
  | T_Match : forall (L : atoms) Γ scrut K n_lt n_ty
                     sigma_fields K_res lr_schema Ts_res_schema
                     Ts Delta Ts_res_inst arity yes_body eta elim_result no_body,
      K <> any_tag ->
      ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields,
                                   type_ctor K_res lr_schema Ts_res_schema) ->
      ctx_lookup_eff  Γ K = None ->
      length Ts = n_ty ->
      Γ |-t scrut : type_ctor K_res Delta Ts_res_inst ->
      arity = length sigma_fields ->
      (* Cofinite quantification over n_lt lt-atoms + arity tm-atoms. *)
      (forall (lt_xs : list atom) (tm_xs : list atom),
          length lt_xs = n_lt ->
          length tm_xs = arity ->
          NoDup lt_xs -> NoDup tm_xs ->
          (forall x, In x lt_xs -> x `notin` L) ->
          (forall x, In x tm_xs -> x `notin` L) ->
          let lts := List.map lt_fvar lt_xs in
          let rho_fields := List.map (inst_ctor_type lts Ts) sigma_fields in
          let Γ' := push_tm_atoms tm_xs rho_fields
                       (push_lt_atoms lt_xs Delta Γ) in
          Γ' |-t open_tm_wrt_tms tm_xs (open_tm_wrt_lt_list lts yes_body) :
                 eta /\
          elim_ty_atoms lt_xs Delta var_pos eta = Some elim_result) ->
      Γ |-t no_body : elim_result ->
      Γ |-t term_match scrut K arity yes_body no_body : elim_result

  (* (Cap): runtime capability value `cap E m Ts op_body`. The        *)
  (* op-body binds n_β type vars (outermost) and 2 tm vars (innermost *)
  (* arg, then resumption).                                            *)
  | T_Cap   : forall (L : atoms) Γ E_tag m Ts op_body
                     n_α n_β sig ret T_R sig_β ret_β,
      ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
      length Ts = n_α ->
      sig_β = open_ty_wrt_ty_list Ts sig ->
      ret_β = open_ty_wrt_ty_list Ts ret ->
      (forall (β_xs : list atom) (arg_x k_x : atom),
          length β_xs = n_β ->
          NoDup β_xs ->
          arg_x <> k_x ->
          (forall a, In a β_xs -> a `notin` L) ->
          arg_x `notin` L -> k_x `notin` L ->
          let Γ' := bind_tm arg_x (open_ty_wrt_ty_list (List.map type_fvar β_xs) sig_β)
                 :: bind_tm k_x   (type_fun
                                    (open_ty_wrt_ty_list (List.map type_fvar β_xs) ret_β)
                                    lt_local
                                    T_R)
                 :: push_ty_atoms β_xs any_at_free Γ in
          (* CEK convention: env after KPerformFire is [arg, k, ...ρ_cap], *)
          (* so the innermost binder (bvar 0) is `arg` and bvar 1 is `k`. *)
          Γ' |-t open_tm_wrt_tm (term_fvar k_x)
                  (open_tm_wrt_tm (term_fvar arg_x)
                    (open_tm_wrt_ty_list (List.map type_fvar β_xs) op_body)) :
                 T_R) ->
      Γ |-t term_cap E_tag m Ts op_body : type_ctor E_tag lt_local Ts

  (* (Handle): same op-body discipline as Cap, plus a body bound      *)
  (* by the freshly minted capability.                                 *)
  | T_Handle : forall (L : atoms) Γ E_tag Ts op_body body
                      n_α n_β sig ret T_R sig_β ret_β,
      ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
      length Ts = n_α ->
      sig_β = open_ty_wrt_ty_list Ts sig ->
      ret_β = open_ty_wrt_ty_list Ts ret ->
      (forall (β_xs : list atom) (arg_x k_x : atom),
          length β_xs = n_β ->
          NoDup β_xs ->
          arg_x <> k_x ->
          (forall a, In a β_xs -> a `notin` L) ->
          arg_x `notin` L -> k_x `notin` L ->
          let Γ' := bind_tm arg_x (open_ty_wrt_ty_list (List.map type_fvar β_xs) sig_β)
                 :: bind_tm k_x   (type_fun
                                    (open_ty_wrt_ty_list (List.map type_fvar β_xs) ret_β)
                                    lt_local
                                    T_R)
                 :: push_ty_atoms β_xs any_at_free Γ in
          (* CEK convention: env after KPerformFire is [arg, k, ...ρ_cap], *)
          (* so the innermost binder (bvar 0) is `arg` and bvar 1 is `k`. *)
          Γ' |-t open_tm_wrt_tm (term_fvar k_x)
                  (open_tm_wrt_tm (term_fvar arg_x)
                    (open_tm_wrt_ty_list (List.map type_fvar β_xs) op_body)) :
                 T_R) ->
      (forall x, x `notin` L ->
          (bind_tm x (type_ctor E_tag lt_local Ts) :: Γ) |-t
            open_tm_wrt_tm (term_fvar x) body : T_R) ->
      Γ |-t term_handle E_tag Ts op_body body : T_R

  | T_Perform : forall Γ recv arg E_tag Δ Ts Ss
                       n_α n_β sig ret sig_inst ret_inst,
      Γ |-t recv : type_ctor E_tag Δ Ts ->
      ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
      length Ts = n_α ->
      length Ss = n_β ->
      sig_inst = inst_op_type Ts Ss sig ->
      ret_inst = inst_op_type Ts Ss ret ->
      Γ |-t arg : sig_inst ->
      Γ |-t term_perform recv Ss arg : ret_inst

  (* (HandlerM, runtime): a delimiter is transparent to typing.       *)
  | T_HandlerM : forall Γ m t T,
      Γ |-t t : T ->
      Γ |-t term_handler_m m t : T

  (* (Resume, runtime): a reified resumption is a function value.     *)
  | T_Resume : forall (L : atoms) Γ m b A T_R,
      (forall x, x `notin` L ->
         (bind_tm x A :: Γ) |-t open_tm_wrt_tm (term_fvar x) b : T_R) ->
      Γ |-t term_resume m b : type_fun A lt_local T_R

where "G '|-t' t ':' T" := (typing G t T).

#[export] Hint Constructors typing : core.
