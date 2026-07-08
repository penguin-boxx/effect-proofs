Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.

(* =================================================================== *)
(* Typing Context                                                      *)
(*                                                                     *)
(* Γ ::= ∅  |  x:T, Γ  |  α<:B, Γ  |  l<:Δ, Γ                          *)
(*                                                                     *)
(* Each namespace uses independent de Bruijn indices.                  *)
(* Bounds are stored relative to the context *below* their binder, so  *)
(* a lookup must re-interpret the bound at the use site (the head of   *)
(* Γ).  Walking past a `bind_ty` shifts the type-variable namespace by *)
(* one (`shift_ty 1 0`); walking past a `bind_lt` shifts the lifetime  *)
(* namespace by one (`shift_lt`/`shift_lt_in_ty 1 0`).  `bind_tm`,     *)
(* `bind_ctor`, `bind_eff` introduce no ty/lt binder, so they shift    *)
(* nothing.                                                            *)

Inductive binding : Type :=
  | bind_tm  : type     -> binding  (* x : T  *)
  | bind_ty  : type     -> binding  (* α <: B *)
  | bind_lt  : lifetime -> binding  (* l <: Δ *)
  (* K : ∀ l̄(n_lt vars) ᾱ(n_ty vars). τ̄ → T@(+lt_∅(τ̄))@ᾱ               *)
  (* n_lt    : number of existential lifetime binders                  *)
  (* n_ty    : number of type binders                                  *)
  (* fields  : argument types under those binders (de Bruijn)          *)
  (* result  : result type under those binders (de Bruijn)             *)
  | bind_ctor : ctor_tag -> nat -> nat -> list type -> type -> binding
  (* Effect declaration (single-op, single-argument):                  *)
  (*   effect E<n_α type-params> { op : ∀n_β type-params. sig → ret }  *)
  (* sig is the (single) parameter type, ret is the return type;       *)
  (* both live under (n_α + n_β) type-binders, with α-vars innermost   *)
  (* (indices 0..n_α-1) and β-vars above them.                         *)
  | bind_eff : eff_tag -> nat -> nat -> type -> type -> binding
  .

Definition ctx := list binding.

Fixpoint ctx_lookup_tm (Γ : ctx) (x : nat) : option type :=
  match Γ with
  | []                => None
  | bind_tm T :: rest =>
      match x with
      | O   => Some T
      | S n => ctx_lookup_tm rest n
      end
  | bind_ty _ :: rest => option_map (shift_ty 1 0) (ctx_lookup_tm rest x)
  | bind_lt _ :: rest => option_map (shift_lt_in_ty 1 0) (ctx_lookup_tm rest x)
  | _ :: rest         => ctx_lookup_tm rest x
  end.

Fixpoint ctx_lookup_ty (Γ : ctx) (α : nat) : option type :=
  match Γ with
  | []                => None
  | bind_ty B :: rest =>
      match α with
      | O   => Some (shift_ty 1 0 B)
      | S n => option_map (shift_ty 1 0) (ctx_lookup_ty rest n)
      end
  | bind_lt _ :: rest => option_map (shift_lt_in_ty 1 0) (ctx_lookup_ty rest α)
  | _ :: rest         => ctx_lookup_ty rest α
  end.

Fixpoint ctx_lookup_lt (Γ : ctx) (l : nat) : option lifetime :=
  match Γ with
  | []                => None
  | bind_lt Δ :: rest =>
      match l with
      | O   => Some (shift_lt 1 0 Δ)
      | S n => option_map (shift_lt 1 0) (ctx_lookup_lt rest n)
      end
  | _ :: rest         => ctx_lookup_lt rest l
  end.

Definition shift_ty_ctor_sig (amount cutoff : nat)
    (sig : nat * nat * list type * type) : nat * nat * list type * type :=
  let '(n_lt, n_ty, fields, result) := sig in
  (n_lt, n_ty,
   List.map (shift_ty amount (n_ty + cutoff)) fields,
   shift_ty amount (n_ty + cutoff) result).

Definition shift_lt_ctor_sig (amount cutoff : nat)
    (sig : nat * nat * list type * type) : nat * nat * list type * type :=
  let '(n_lt, n_ty, fields, result) := sig in
  (n_lt, n_ty,
   List.map (shift_lt_in_ty amount (n_lt + cutoff)) fields,
   shift_lt_in_ty amount (n_lt + cutoff) result).

Definition shift_ty_eff_sig (amount cutoff : nat)
    (sig : nat * nat * type * type) : nat * nat * type * type :=
  let '(n_α, n_β, sig_ty, ret_ty) := sig in
  (n_α, n_β,
   shift_ty amount (n_α + n_β + cutoff) sig_ty,
   shift_ty amount (n_α + n_β + cutoff) ret_ty).

Definition shift_lt_eff_sig (amount cutoff : nat)
    (sig : nat * nat * type * type) : nat * nat * type * type :=
  let '(n_α, n_β, sig_ty, ret_ty) := sig in
  (n_α, n_β,
   shift_lt_in_ty amount cutoff sig_ty,
   shift_lt_in_ty amount cutoff ret_ty).

(* Look up a constructor signature by tag.  Returns                   *)
(*   Some (n_lt, n_ty, fields, result)                                *)
(* where n_lt / n_ty are the numbers of lifetime / type binders, and  *)
(* fields / result use de Bruijn indices under those binders.         *)
(* Walking past ambient type/lifetime binders shifts only variables   *)
(* outside the schema binders.                                        *)
Fixpoint ctx_lookup_ctor (Γ : ctx) (K : ctor_tag)
    : option (nat * nat * list type * type) :=
  match Γ with
  | [] => None
  | bind_ctor K' n_lt n_ty fields result :: rest =>
      if Nat.eqb K K' then Some (n_lt, n_ty, fields, result)
      else ctx_lookup_ctor rest K
  | bind_ty _ :: rest => option_map (shift_ty_ctor_sig 1 0) (ctx_lookup_ctor rest K)
  | bind_lt _ :: rest => option_map (shift_lt_ctor_sig 1 0) (ctx_lookup_ctor rest K)
  | _ :: rest => ctx_lookup_ctor rest K
  end.

(* Look up an effect declaration by tag. Returns                      *)
(*   Some (n_α, n_β, sig, ret).                                       *)
(* Type binders are shifted outside the α/β schema binders; lifetime  *)
(* binders shift throughout because effect schemas bind no lifetimes. *)
Fixpoint ctx_lookup_eff (Γ : ctx) (E : eff_tag)
    : option (nat * nat * type * type) :=
  match Γ with
  | [] => None
  | bind_eff E' n_α n_β sig ret :: rest =>
      if Nat.eqb E E' then Some (n_α, n_β, sig, ret)
      else ctx_lookup_eff rest E
  | bind_ty _ :: rest => option_map (shift_ty_eff_sig 1 0) (ctx_lookup_eff rest E)
  | bind_lt _ :: rest => option_map (shift_lt_eff_sig 1 0) (ctx_lookup_eff rest E)
  | _ :: rest => ctx_lookup_eff rest E
  end.

Reserved Notation "G '⊢ₗ' l1 '<:' l2" (at level 40, l1 at next level).

Inductive lt_wf : ctx -> lifetime -> Prop :=
  | LWF_Var : forall Γ x Δ,
      ctx_lookup_lt Γ x = Some Δ ->
      lt_wf Γ (lt_var x)
  | LWF_Free : forall Γ,
      lt_wf Γ lt_free
  | LWF_Local : forall Γ,
      lt_wf Γ lt_local
  | LWF_Min : forall Γ l1 l2,
      lt_wf Γ l1 ->
      lt_wf Γ l2 ->
      lt_wf Γ (lt_min l1 l2).

Inductive lifetimes_wf : ctx -> list lifetime -> Prop :=
  | LWFs_nil : forall Γ,
      lifetimes_wf Γ []
  | LWFs_cons : forall Γ l lts,
      lt_wf Γ l ->
      lifetimes_wf Γ lts ->
      lifetimes_wf Γ (l :: lts).

Inductive ty_wf : ctx -> type -> Prop :=
  | TWF_Var : forall Γ α B,
      ctx_lookup_ty Γ α = Some B ->
      ty_wf Γ B ->
      ty_wf Γ (type_var α)
  | TWF_Fun : forall Γ A l B,
      ty_wf Γ A ->
      lt_wf Γ l ->
      ty_wf Γ B ->
      ty_wf Γ (type_fun A l B)
  | TWF_Ctor : forall Γ K l Ts,
      lt_wf Γ l ->
      types_wf Γ Ts ->
      ty_wf Γ (type_ctor K l Ts)
  | TWF_LtAll : forall Γ A,
      ty_wf (bind_lt lt_local :: Γ) A ->
      ty_wf Γ (type_lt_all A)
  | TWF_TyAll : forall Γ B A,
      ty_wf Γ B ->
      ty_wf (bind_ty B :: Γ) A ->
      ty_wf Γ (type_ty_all B A)
with types_wf : ctx -> list type -> Prop :=
  | TWFs_nil : forall Γ,
      types_wf Γ []
  | TWFs_cons : forall Γ T Ts,
      ty_wf Γ T ->
      types_wf Γ Ts ->
      types_wf Γ (T :: Ts).

(* ================================================================== *)
(* Lifetime subtyping                                                 *)
(*                                                                    *)
(* Γ ⊢ₗ Δ' <: Δ  means Δ' "outlives" Δ in the         lattice:        *)
(*   free (bottom) <: local (top)                                     *)
(*   lt_min l1 l2 is the join (= least upper bound) of l1 and l2      *)
(*                                                                    *)
(* Rules:                                                             *)
(*   LS_Free    :  Γ ⊢ₗ free  <: Δ          (free is bottom)          *)
(*   LS_Local   :  Γ ⊢ₗ Δ <: local          (local is top)            *)
(*   LS_Var     :  (l <: Δ) ∈ Γ → Γ ⊢ₗ l <: Δ  (SubCtx_Δ)             *)
(*   LS_Refl    :  Γ ⊢ₗ Δ <: Δ                                        *)
(*   LS_Trans   :  transitivity                                       *)
(*   LS_MinL    :  Γ ⊢ₗ l1 <: l → Γ ⊢ₗ l2 <: l →                      *)
(*                  Γ ⊢ₗ lt_min l1 l2 <: l    (Sub+: join ≤ upper bd) *)
(*   LS_MinR1   :  Γ ⊢ₗ l <: l1 → Γ ⊢ₗ l <: lt_min l1 l2              *)
(*   LS_MinR2   :  Γ ⊢ₗ l <: l2 → Γ ⊢ₗ l <: lt_min l1 l2              *)
(* ================================================================== *)

Inductive lt_sub : ctx -> lifetime -> lifetime -> Prop :=

  | LS_Free  : forall Γ l,
      lt_wf Γ l ->
      Γ ⊢ₗ lt_free <: l

  | LS_Local : forall Γ l,
      lt_wf Γ l ->
      Γ ⊢ₗ l <: lt_local

  | LS_Var   : forall Γ x Δ,
      ctx_lookup_lt Γ x = Some Δ ->
      lt_wf Γ Δ ->
      Γ ⊢ₗ lt_var x <: Δ

  | LS_Refl  : forall Γ l,
      lt_wf Γ l ->
      Γ ⊢ₗ l <: l

  | LS_Trans : forall Γ l1 l2 l3,
      Γ ⊢ₗ l1 <: l2 ->
      Γ ⊢ₗ l2 <: l3 ->
      Γ ⊢ₗ l1 <: l3

  (* lt_min l1 l2 is the join; it lies above both l1 and l2,           *)
  (* and is the least such: if both l1 <: l and l2 <: l then           *)
  (* lt_min l1 l2 <: l.                                                *)
  | LS_MinL  : forall Γ l1 l2 l,
      Γ ⊢ₗ l1 <: l ->
      Γ ⊢ₗ l2 <: l ->
      Γ ⊢ₗ lt_min l1 l2 <: l

  | LS_MinR1 : forall Γ l l1 l2,
      Γ ⊢ₗ l <: l1 ->
      lt_wf Γ l2 ->
      Γ ⊢ₗ l <: lt_min l1 l2

  | LS_MinR2 : forall Γ l l1 l2,
      Γ ⊢ₗ l <: l2 ->
      lt_wf Γ l1 ->
      Γ ⊢ₗ l <: lt_min l1 l2

where "G '⊢ₗ' l1 '<:' l2" := (lt_sub G l1 l2).

Hint Constructors lt_sub : core.

(* ================================================================== *)
(* lt_of_ty : compute lt_∅(τ)                                         *)
(*                                                                    *)
(* lt_∅(τ) is the minimum of all lifetime restrictions in τ when      *)
(* evaluated at the empty context (type variables have no bound →     *)
(* contribute nothing).                                               *)
(*                                                                    *)
(*   lt_∅(α)           = free          (no bound in empty ctx)        *)
(*   lt_∅(T Δ τ̄)       = lt_min Δ      (lt_min of lt_∅(τ̄))            *)
(*   lt_∅(τ̄ Δ → σ)     = Δ             (only the closure lt matters)  *)
(*   lt_∅(∀l.τ)        = local         (conservative top)             *)
(*   lt_∅(∀(α<:B).τ)   = local         (conservative top)             *)
(* ================================================================== *)

Fixpoint lt_of_ty (T : type) : lifetime :=
  let fix go_list (Ts : list type) : lifetime :=
    match Ts with
    | []        => lt_free
    | A :: rest => lt_min (lt_of_ty A) (go_list rest)
    end
  in
  match T with
  | type_var _        => lt_free
  | type_fun _ l _    => l
  | type_ctor _ l Ts  => lt_min l (go_list Ts)
  | type_lt_all A     => lt_local
  | type_ty_all _ A   => lt_local
  end.

Definition lt_of_ty_list (Ts : list type) : lifetime :=
  List.fold_right (fun T acc => lt_min (lt_of_ty T) acc) lt_free Ts.

(* ================================================================== *)
(* Γ-aware lt_Γ(τ)                                                    *)
(*                                                                    *)
(*   lt_Γ(α) = lt_Γ(B)    if (α <: B) ∈ Γ                             *)
(*   lt_Γ(α) = free       otherwise                                   *)
(*                                                                    *)
(* Fuel is used to guarantee termination; calling with fuel = |Γ|     *)
(* bounds the chain length through type variables.                    *)
(* ================================================================== *)

Fixpoint lt_of_ty_ctx (fuel : nat) (Γ : ctx) (T : type) : lifetime :=
  let fix go (T : type) : lifetime :=
    match T with
    | type_var α =>
        match fuel with
        | O => lt_free
        | S fuel' =>
            match ctx_lookup_ty Γ α with
            | Some B => lt_of_ty_ctx fuel' Γ B
            | None   => lt_free
            end
        end
    | type_fun _ l _    => l
    | type_ctor _ l Ts  =>
        lt_min l ((fix gol (Ts : list type) : lifetime :=
                     match Ts with
                     | []        => lt_free
                     | A :: rest => lt_min (go A) (gol rest)
                     end) Ts)
    | type_lt_all A     => lt_local
    | type_ty_all _ A   => lt_local
    end
  in go T.

Definition lt_of_ty_G (Γ : ctx) (T : type) : lifetime :=
  lt_of_ty_ctx (List.length Γ) Γ T.

(* DESIGN NOTE — why two escape-lifetime families.                     *)
(* [lt_of_ty]/[lt_of_ty_list] are context-free (a type variable        *)
(* contributes [free], i.e. no constraint); [lt_of_ty_ctx]/[lt_of_ty_G]*)
(* consult the variable's bound in Γ.  The context-free family is used *)
(* ONLY by T_Ctor, on the already-instantiated field types: demanding  *)
(* the Γ-aware lifetime there would strengthen the premise on          *)
(* polymorphic constructor fields (a variable bounded by a local type  *)
(* would suddenly count as local) and lose source programs.  All other *)
(* rules (T_Lam's capture, T_Handle/T_HandlerM's answer check,         *)
(* T_Perform's boundary check) use the Γ-aware [lt_of_ty_G].  The two  *)
(* are reconciled where needed by the bridge lemmas                    *)
(* [lt_of_ty_list_le_lt_of_ty_ctx_list] (SubstTy.v) — context-free is  *)
(* below context-aware — and [lt_of_ty_G_ty_closed_eq] (Weakening.v) — *)
(* they agree on closed types.                                         *)

(* ================================================================== *)
(* "no local in σ" — syntactic check for T_Lam return-type side cond. *)
(*                                                                    *)
(* Very conservative on polymorphic variables.                        *)
(* ================================================================== *)

Fixpoint no_local_lt (l : lifetime) : bool :=
  match l with
  | lt_var _      => false
  | lt_local      => false
  | lt_min l1 l2  => andb (no_local_lt l1) (no_local_lt l2)
  | _             => true
  end.

Fixpoint no_local_ty (T : type) : bool :=
  let fix go (Ts : list type) : bool :=
    match Ts with
    | []        => true
    | A :: rest => andb (no_local_ty A) (go rest)
    end
  in
  match T with
  | type_var _        => false
  | type_fun A l B    => andb (no_local_ty A) (andb (no_local_lt l) (no_local_ty B))
  | type_ctor _ l Ts  => andb (no_local_lt l) (go Ts)
  | type_lt_all A     => no_local_ty A
  | type_ty_all B A   => andb (no_local_ty B) (no_local_ty A)
  end.


(* ================================================================== *)
(* Free term variables and capture lifetime                           *)
(*                                                                    *)
(* free_tm_vars c t : indices of free term vars in t that lie         *)
(*   ≥ c (with c subtracted).  Used with c = 1 inside T_Lam (the      *)
(*   lambda's own binder is "consumed").                              *)
(*                                                                    *)
(* capture_lt Γ body : +lt_Γ(τ̄) over captured variables' types —      *)
(* the closure-lifetime bound in the Lam rule.                        *)
(*   Cap-aware: a literal runtime capability form (term_cap /         *)
(*   term_handler_m) anywhere in the body forces the                  *)
(*   closure lifetime to lt_local, since free_tm_vars cannot see      *)
(*   literal capabilities.                                            *)
(* ================================================================== *)

Fixpoint free_tm_vars (cutoff : nat) (t : term) : list nat :=
  let fix go (ts : list term) : list nat :=
    match ts with
    | []        => []
    | u :: rest => free_tm_vars cutoff u ++ go rest
    end
  in
  match t with
  | term_var x =>
      if Nat.ltb x cutoff then [] else [x - cutoff]
  | term_app t1 t2       => free_tm_vars cutoff t1 ++ free_tm_vars cutoff t2
  | term_lam body _      => free_tm_vars (S cutoff) body
  | term_ty_app t _      => free_tm_vars cutoff t
  | term_ty_lam _ body   => free_tm_vars cutoff body
  | term_lt_app t _      => free_tm_vars cutoff t
  | term_lt_lam body     => free_tm_vars cutoff body
  | term_ctor _ _ _ _ ts => go ts
  | term_match scrut _ _ arity y n =>
      free_tm_vars cutoff scrut
        ++ free_tm_vars (cutoff + arity) y
        ++ free_tm_vars cutoff n
  | term_handle _ _ _ _ _ op_body body =>
      free_tm_vars (cutoff + 2) op_body
        ++ free_tm_vars (S cutoff) body
  | term_perform t _ _ arg =>
      free_tm_vars cutoff t ++ free_tm_vars cutoff arg
  | term_cap _ _ _ _ _ op_body => free_tm_vars (cutoff + 2) op_body
  | term_handler_m _ _ _ t => free_tm_vars cutoff t
  end.

Definition capture_lt (Γ : ctx) (body : term) : lifetime :=
  if has_rt_cap body then lt_local
  else
    fold_right (fun x acc =>
      lt_min
        match ctx_lookup_tm Γ x with
        | Some T => lt_of_ty_G Γ T
        | None   => lt_free
        end
        acc)
      lt_free
      (free_tm_vars 1 body).

(* ================================================================== *)
(* Variance positions for elim                                        *)
(* ================================================================== *)

Inductive variance : Type :=
  | var_pos : variance   (* covariant / positive *)
  | var_neg : variance   (* contravariant / negative *)
  | var_inv : variance   (* invariant *)
  .

Definition flip_variance (p : variance) : variance :=
  match p with
  | var_pos => var_neg
  | var_neg => var_pos
  | var_inv => var_inv
  end.

(* ================================================================== *)
(* elim_var : eliminate a single fresh lifetime variable from a type  *)
(*                                                                    *)
(* elim_var lvar Δ p T                                                *)
(*   eliminates lt_var lvar from T, approximating with:               *)
(*     Δ     in positive (covariant) positions                        *)
(*     free  in negative (contravariant) positions                    *)
(*     error (returns None) in invariant positions                    *)
(*                                                                    *)
(* We return option type; None = error.                               *)
(* We eliminate multiple vars by folding over the list.               *)
(* ================================================================== *)

Fixpoint elim_lt (lvar : nat) (bound : lifetime) (p : variance) (l : lifetime)
    : option lifetime :=
  match l with
  | lt_var x =>
      if Nat.eqb x lvar then
        match p with
        | var_pos => Some bound
        | var_neg => Some lt_free
        | var_inv => None
        end
      else Some (lt_var x)
  | lt_free      => Some lt_free
  | lt_local     => Some lt_local
  | lt_min l1 l2 =>
      match elim_lt lvar bound p l1, elim_lt lvar bound p l2 with
      | Some l1', Some l2' => Some (lt_min l1' l2')
      | _, _               => None
      end
  end.

Fixpoint elim_ty (lvar : nat) (bound : lifetime) (p : variance) (T : type)
    : option type :=
  let fix go_list p' Ts :=
    match Ts with
    | [] => Some []
    | A :: rest =>
        match elim_ty lvar bound p' A, go_list p' rest with
        | Some A', Some rest' => Some (A' :: rest')
        | _, _ => None
        end
    end
  in
  match T with
  | type_var n => Some (type_var n)
  | type_fun A l B =>
      match elim_ty lvar bound (flip_variance p) A,
            elim_lt lvar bound p l,
            elim_ty lvar bound p B with
      | Some A', Some l', Some B' => Some (type_fun A' l' B')
      | _, _, _ => None
      end
  | type_ctor K l Ts =>
      match elim_lt lvar bound p l, go_list var_inv Ts with
      | Some l', Some Ts' => Some (type_ctor K l' Ts')
      | _, _ => None
      end
  | type_lt_all A =>
      match elim_ty (S lvar) (shift_lt 1 0 bound) p A with
      | Some A' => Some (type_lt_all A')
      | None    => None
      end
  | type_ty_all B A =>
      match elim_ty lvar bound (flip_variance p) B, elim_ty lvar bound p A with
      | Some B', Some A' => Some (type_ty_all B' A')
      | _, _ => None
      end
  end.

(* Eliminate all lifetime vars in the range [0, n) from a type.        *)
(* Callers pass `bound` already shifted up by n so that it lives       *)
(* under the n eliminated binders.  Each iteration closes one binder,  *)
(* so `bound` gets closed/shrunk by `subst_lt 0 lt_free bound`.        *)
Fixpoint elim_ty_n (n : nat) (bound : lifetime) (p : variance) (T : type)
    : option type :=
  match n with
  | O    => Some T
  | S n' =>
      match elim_ty 0 bound p T with
      | None    => None
      | Some T' =>
          let T''     := subst_lt_in_ty 0 lt_free T' in
          let bound'  := subst_lt 0 lt_free bound in
          elim_ty_n n' bound' p T''
      end
  end.

(* ================================================================== *)
(* Type subtyping                                                     *)
(*                                                                    *)
(* Γ ⊢ S <: T                                                         *)
(*                                                                    *)
(*   SA_Refl    : reflexivity                                         *)
(*   SA_Trans   : transitivity                                        *)
(*   SA_VarCtx  : (α <: B) ∈ Γ → Γ ⊢ α <: B                           *)
(*   SA_Data    : Γ ⊢ₗ l <: l' → Γ ⊢ T l τ̄ <: T l' τ̄                  *)
(*                covariant in lifetime, invariant in type args       *)
(*   SA_Fun     : Γ ⊢ A <: A' (contra) ∧ Γ ⊢ₗ l <: l' (co) ∧          *)
(*                Γ ⊢ B <: B' (co) → Γ ⊢ A' l → B <: A l' → B'        *)
(*                (SubFun — contra domain, co lifetime, co codomain)  *)
(*   SA_LtAll   : (∀l is covariant) body under a fresh bound-local lt *)
(*   SA_TyAll   : F₋<: rule — contra in bound, co in body             *)
(*                Γ ⊢ B' <: B → (α<:B')::Γ ⊢ A <: A' →                *)
(*                  Γ ⊢ ∀(α<:B).A <: ∀(α<:B').A'                      *)
(* ================================================================== *)

Reserved Notation "G '⊢' S '<::' T" (at level 40, S at next level).

Inductive sub : ctx -> type -> type -> Prop :=

  | SA_Refl   : forall Γ T,
      ty_wf Γ T ->
      Γ ⊢ T <:: T

  | SA_Trans  : forall Γ S U T,
      Γ ⊢ S <:: U ->
      Γ ⊢ U <:: T ->
      Γ ⊢ S <:: T

  (* SubCtx: use the bound stored in the context for a type variable *)
  | SA_VarCtx : forall Γ α B,
      ctx_lookup_ty Γ α = Some B ->
      ty_wf Γ B ->
      Γ ⊢ type_var α <:: B

  (* SubData: covariant in the lifetime annotation, invariant in Ts *)
  | SA_Data   : forall Γ K l l' Ts,
      Γ ⊢ₗ l <: l' ->
      types_wf Γ Ts ->
      Γ ⊢ type_ctor K l Ts <:: type_ctor K l' Ts

  (* SubAny: τ <: Any@Δ when all lifetime                              *)
  (* restrictions in τ outlive Δ.                                      *)
  | SA_Any    : forall Γ T Δ,
      ty_wf Γ T ->
      lt_wf Γ Δ ->
      Γ ⊢ₗ lt_of_ty_G Γ T <: Δ ->
      Γ ⊢ T <:: type_ctor any_tag Δ []

  (* SubFun: contravariant in domain type, covariant in closure        *)
  (* lifetime and codomain.  (Paper figure 4, SubFun.)                 *)
  (* Subtype: A' -l-> B   Supertype: A -l'-> B'                        *)
  (* Requires: A <: A' (contra),  l <: l' (co),  B <: B' (co)          *)
  | SA_Fun    : forall Γ A A' l l' B B',
      Γ ⊢ A <:: A' ->
      Γ ⊢ₗ l <: l' ->
      Γ ⊢ B <:: B' ->
      Γ ⊢ type_fun A' l B <:: type_fun A l' B'

  (* type_lt_all is covariant: extend ctx with a fresh lt var          *)
  (* bounded by lt_local (no restriction — any lifetime is allowed)    *)
  | SA_LtAll  : forall Γ A A',
      (bind_lt lt_local :: Γ) ⊢ A <:: A' ->
      Γ ⊢ type_lt_all A <:: type_lt_all A'

  (* Kernel F<: for bounded type abstraction.                          *)
  (* ∀(α<:B).A <: ∀(α<:B').A' when B'<:B (contra) and                  *)
  (* A <: A' under the tighter bound B'.                               *)
  | SA_TyAll  : forall Γ B B' A A',
      ty_wf (bind_ty B :: Γ) A ->
      ty_wf (bind_ty B' :: Γ) A' ->
      Γ ⊢ B' <:: B ->
      (bind_ty B' :: Γ) ⊢ A <:: A' ->
      Γ ⊢ type_ty_all B A <:: type_ty_all B' A'

where "G '⊢' S '<::' T" := (sub G S T).

Hint Constructors sub : core.

(* ================================================================== *)
(* Helpers for constructor typing and match elimination               *)
(*                                                                    *)
(* These must be defined before `typing` so T_Ctor / T_Match can use  *)
(* them as proper inductive constructors rather than Axioms.          *)
(* ================================================================== *)

(* Instantiate n_ty type-binders (outermost-first) by substituting Ts.  *)
(* Each head argument is lifted over the remaining schema binders so    *)
(* later substitutions cannot capture its free type variables.          *)
Fixpoint inst_ty_vars (n : nat) (Ts : list type) (T : type) : type :=
  match n, Ts with
  | O, _            => T
  | S n', U :: rest => inst_ty_vars n' rest (subst_ty 0 (shift_ty n' 0 U) T)
  | S _, []         => T
  end.

(* ------------------------------------------------------------------- *)
(* Parallel substitution of lifetime schema variables.                 *)
(*                                                                     *)
(* `multi_subst_lt cutoff lts l` and `multi_subst_lt_in_ty` walk under *)
(* binders and replace `lt_var i` (with i ≥ cutoff) by either:         *)
(*   - lts[i - cutoff], lifted under `cutoff` extra binders, when      *)
(*     i - cutoff < |lts|, or                                          *)
(*   - lt_var (i - |lts|), otherwise (closing |lts| schema binders).   *)
(*                                                                     *)
(* This gives a clean semantics: lts[k] replaces schema-var-k, and     *)
(* lts[k] itself is read in the *outer* (post-instantiation) ctx —     *)
(* the user does NOT need to pre-shift entries.                        *)
(* ------------------------------------------------------------------- *)

Fixpoint multi_subst_lt (cutoff : nat) (lts : list lifetime) (l : lifetime)
    : lifetime :=
  match l with
  | lt_free       => lt_free
  | lt_local      => lt_local
  | lt_min l1 l2  => lt_min (multi_subst_lt cutoff lts l1)
                            (multi_subst_lt cutoff lts l2)
  | lt_var x =>
      if Nat.ltb x cutoff then lt_var x
      else
        let x' := x - cutoff in
        if Nat.ltb x' (List.length lts) then
          shift_lt cutoff 0 (List.nth x' lts lt_free)
        else
          lt_var (x - List.length lts)
  end.

Fixpoint multi_subst_lt_in_ty (cutoff : nat) (lts : list lifetime) (T : type)
    : type :=
  let fix go (Ts : list type) : list type :=
    match Ts with
    | []        => []
    | A :: rest => multi_subst_lt_in_ty cutoff lts A :: go rest
    end
  in
  match T with
  | type_var n        => type_var n
  | type_fun A l B    => type_fun (multi_subst_lt_in_ty cutoff lts A)
                                  (multi_subst_lt cutoff lts l)
                                  (multi_subst_lt_in_ty cutoff lts B)
  | type_ctor K l Ts  => type_ctor K (multi_subst_lt cutoff lts l) (go Ts)
  | type_lt_all A     => type_lt_all (multi_subst_lt_in_ty (S cutoff) lts A)
  | type_ty_all B A   => type_ty_all (multi_subst_lt_in_ty cutoff lts B)
                                     (multi_subst_lt_in_ty cutoff lts A)
  end.

(* Instantiate the n_lt lt-binders of a schema by parallel substitution. *)
(* lts[k] replaces schema-var-k and lives in the outer context (no       *)
(* pre-shifting required). The `n` parameter is kept for documentation   *)
(* and is intended to satisfy `n = length lts` at all call sites.        *)
Definition inst_lt_vars (_n : nat) (lts : list lifetime) (T : type) : type :=
  multi_subst_lt_in_ty 0 lts T.

(* Instantiate a constructor field/result type: first type vars, then  *)
(* lt vars. Type arguments live outside the constructor's lifetime     *)
(* schema binders, so lift them over that binder block before type     *)
(* substitution; otherwise the later lifetime substitution would       *)
(* capture free lifetimes in the type arguments.                       *)
Definition inst_ctor_type (n_lt n_ty : nat) (lts : list lifetime) (Ts : list type)
    (T : type) : type :=
  inst_lt_vars n_lt lts (inst_ty_vars n_ty (List.map (shift_lt_in_ty n_lt 0) Ts) T).

(* MATCH variant of [inst_ctor_type].  In the yes-branch the schema's      *)
(* n_lt lt-binders ARE the freshly pushed match lt-vars (lt_var 0..n_lt-1),*)
(* so they need no instantiation — only the n_ty type arguments are filled *)
(* (lifted over the n_lt lt-binders).  Using the full [inst_ctor_type]     *)
(* here would apply [inst_lt_vars (lt_var_list n_lt)], whose only net      *)
(* effect is a spurious down-shift (multi_subst_lt's [lt_var (x-|lts|)]    *)
(* branch) that ALIASES Ts-derived field lifetimes with the fresh match    *)
(* lt-vars — breaking type-substitution commutation.  Keeping the schema   *)
(* lt-vars abstract leaves rho_fields living consistently in the pushed    *)
(* context Γ'.                                                             *)
Definition inst_ctor_type_open (n_lt n_ty : nat) (Ts : list type)
    (T : type) : type :=
  inst_ty_vars n_ty (List.map (shift_lt_in_ty n_lt 0) Ts) T.

(* Push n fresh bind_lt entries (all bounded by `bound`) onto Γ.      *)
Fixpoint push_lt_vars (n : nat) (bound : lifetime) (Γ : ctx) : ctx :=
  match n with
  | O    => Γ
  | S n' => push_lt_vars n' bound (bind_lt bound :: Γ)
  end.

(* Push n fresh bind_ty entries (all bounded by `bound`) onto Γ.      *)
Fixpoint push_ty_vars (n : nat) (bound : type) (Γ : ctx) : ctx :=
  match n with
  | O    => Γ
  | S n' => push_ty_vars n' bound (bind_ty bound :: Γ)
  end.

(* Push n fresh bind_lt entries for a match/destructuring, each        *)
(* bounded by the scrutinee lifetime `Delta` (which lives in the       *)
(* OUTER Γ).  Unlike [push_lt_vars], the bound stored at level j is     *)
(* [shift_lt j 0 Delta], i.e. Delta lifted into that level's scope, so  *)
(* that EVERY pushed variable has the same effective upper bound        *)
(* [shift_lt n 0 Delta] = the one outer Delta (no per-level meaning     *)
(* drift).  This is the de-Bruijn-correct realisation of the            *)
(* match rule premise "l'_i <: Delta": the n fresh lifetimes            *)
(* are INDEPENDENTLY bounded by Delta, with no spurious inter-variable  *)
(* constraints.  Crucially it is STABLE under lt-substitution and       *)
(* lt-insertion of an outer binder (the per-level shifts commute with   *)
(* subst/shift — see [shift_lt_subst_lt_comm_many0]), which             *)
(* [push_lt_vars] is not.  For lt-closed Delta the two coincide.        *)
Fixpoint push_match_bound (n : nat) (Delta : lifetime) (Γ : ctx) : ctx :=
  match n with
  | O    => Γ
  | S n' => bind_lt (shift_lt n' 0 Delta) :: push_match_bound n' Delta Γ
  end.

(* The β-bound used for polymorphic operations: `Any@free`.            *)
(* We pick `lt_free` so that β-types may not contain `local`-tagged    *)
(* values, ensuring escape-analysis safety.                            *)
Definition any_at_free : type := type_ctor any_tag lt_free [].

(* Instantiate the α part of an op schema while β-vars remain bound.  *)
(* α arguments must be lifted over the remaining β binders so ambient *)
(* type variables in Ts cannot be captured by β instantiation later.  *)
Definition inst_op_ty_args (n_α : nat) (Ts : list type)
                         (n_β : nat) (T : type) : type :=
  inst_ty_vars n_α (List.map (shift_ty n_β 0) Ts) T.

(* Instantiate an op schema: substitute α-vars first, then β-vars.    *)
(* Convention: in the schema, α-vars are innermost (indices 0..n_α-1) *)
(* and β-vars are outermost (indices n_α..n_α+n_β-1).                 *)
Definition inst_op_all_args (n_α : nat) (Ts : list type)
                       (n_β : nat) (Ss : list type)
                       (T : type) : type :=
  inst_ty_vars n_β Ss (inst_op_ty_args n_α Ts n_β T).

(* [lt_var 0; lt_var 1; ...; lt_var (n-1)] — de Bruijn indices of the *)
(* n freshly pushed lt-vars in the order matching `inst_lt_vars`:     *)
(* schema-var-k is replaced by lt_var k (lt_var 0 is innermost).      *)
Definition lt_var_list (n : nat) : list lifetime :=
  List.map lt_var (List.seq 0 n).

(* ================================================================== *)
(* Typing relation                                                    *)
(*                                                                    *)
(* Γ ⊢ₜ t : T                                                         *)
(*                                                                    *)
(* T_Var    : ctx_lookup_tm Γ x = Some T → Γ ⊢ₜ x : T    (Var)        *)
(* T_Sub    : Γ ⊢ₜ t : T → Γ ⊢ T <:: U → Γ ⊢ₜ t : U      (Sub)        *)
(* T_Lam    : (x:A)::Γ ⊢ₜ body : B →                                  *)
(*              Γ ⊢ₜ λ(x:A).body : A -l-> B              (Lam)        *)
(*            (l = +lt_Γ(captures); use T_Sub)                        *)
(* T_App    : Γ ⊢ₜ t1 : A -l-> B → Γ ⊢ₜ t2 : A →                      *)
(*              Γ ⊢ₜ t1 t2 : B                           (App)        *)
(* T_TyLam  : (α<:B)::Γ ⊢ₜ body : T →                                 *)
(*              Γ ⊢ₜ Λ(α<:B).body : ∀(α<:B).T            (TLam)       *)
(* T_TyApp  : Γ ⊢ₜ t : ∀(α<:B).U → Γ ⊢ S <:: B →                      *)
(*              (B = Any'free ⇒ S no-local) →                         *)
(*              Γ ⊢ₜ t [S] : [α↦S] U                     (TApp)       *)
(* T_LtLam  : (l<:local)::Γ ⊢ₜ body : T →                             *)
(*              Γ ⊢ₜ Λl.body : ∀l.T                      (TLam, lt)   *)
(* T_LtApp  : Γ ⊢ₜ t : ∀l.T →                                         *)
(*              Γ ⊢ₜ t {Δ} : [l↦Δ] T                     (TApp, lt)   *)
(* ================================================================== *)

(* The op-body typing context shared by T_Cap and T_Handle: the        *)
(* operation argument $0 (innermost), the resumption $1 of type        *)
(* ret_β -local-> T_R, and the n_β β-type-binders above them.          *)
Definition op_body_ctx (Γ : ctx) (n_β : nat) (sig_β ret_β T_R : type) : ctx :=
  bind_tm sig_β
    :: bind_tm (type_fun ret_β lt_local (shift_ty n_β 0 T_R))
    :: push_ty_vars n_β any_at_free Γ.

Reserved Notation "G '⊢ₜ' t ':' T" (at level 40, t at next level).

Inductive typing : ctx -> term -> type -> Prop :=

  (* --- Var --------------------------------------------------------- *)
  | T_Var   : forall Γ x T,
      ctx_lookup_tm Γ x = Some T ->
      ty_wf Γ T ->
      Γ ⊢ₜ term_var x : T

  (* --- Subsumption ------------------------------------------------- *)
  | T_Sub   : forall Γ t T U,
      Γ ⊢ₜ t : T ->
      Γ ⊢ T <:: U ->
      Γ ⊢ₜ t : U

  (* --- Term abstraction and application ---------------------------- *)

  | T_Lam   : forall Γ body A l B,
      ty_wf Γ A ->
      ty_wf Γ B ->
      (bind_tm A :: Γ) ⊢ₜ body : B ->
      Γ ⊢ₗ capture_lt Γ body <: l ->
      Γ ⊢ₜ term_lam body A : type_fun A l B

  | T_App   : forall Γ t1 t2 A l B,
      Γ ⊢ₜ t1 : type_fun A l B ->
      Γ ⊢ₜ t2 : A ->
      Γ ⊢ₜ term_app t1 t2 : B

  (* --- Type abstraction and application (bounded polymorphism) ----- *)

  (* Introduce a type variable α bounded by `bound`.                  *)
  (* Body is typed with α in scope as the innermost bind_ty entry.    *)
  (* Prenex-Λ restriction: the body must itself be an abstraction, so *)
  (* every Λ-chain bottoms out at a λ whose capture_lt records any    *)
  (* captured capability (∀-types have no closure-lifetime slot).     *)
  | T_TyLam : forall Γ bound body T,
      ty_wf Γ bound ->
      ty_wf (bind_ty bound :: Γ) T ->
      is_abs body = true ->
      (bind_ty bound :: Γ) ⊢ₜ body : T ->
      Γ ⊢ₜ term_ty_lam bound body : type_ty_all bound T

  (* Eliminate ∀(α<:B).U by supplying type S <:: B.                  *)
  (* Result type is U with α substituted by S (de Bruijn: var 0).    *)
  | T_TyApp : forall Γ t B U S,
      Γ ⊢ₜ t : type_ty_all B U ->
      ty_wf Γ S ->
      Γ ⊢ S <:: B ->
      Γ ⊢ₜ term_ty_app t S : subst_ty 0 S U

  (* --- Lifetime abstraction and application ----------------------- *)

  (* Fresh lifetime variable with no constraint (bound lt_local = ⊤). *)
  (* Prenex-Λ restriction: see T_TyLam.                               *)
  | T_LtLam : forall Γ body T,
      ty_wf (bind_lt lt_local :: Γ) T ->
      is_abs body = true ->
      (bind_lt lt_local :: Γ) ⊢ₜ body : T ->
      Γ ⊢ₜ term_lt_lam body : type_lt_all T

  (* Apply ∀l.T to a concrete lifetime Δ; substitute l 0 ↦ Δ.       *)
  | T_LtApp : forall Γ t T l,
      Γ ⊢ₜ t : type_lt_all T ->
      lt_wf Γ l ->
      Γ ⊢ₜ term_lt_app t l : subst_lt_in_ty 0 l T

  (* --- Constructor typing ----------------------------------------- *)
  (* K[l, l̄, T̄](v̄) : instantiated result schema                       *)
  (*   Look up K's signature ∀ l̄(n_lt) ᾱ(n_ty). σ̄ → R.                *)
  (*   Instantiate field types σ̄ and result type R with the supplied  *)
  (*   l̄/T̄.  The runtime lifetime carried by the constructor is the   *)
  (*   top-level lifetime of the instantiated result type.  Field     *)
  (*   lifetimes must fit under it, preserving local-escape safety.   *)
  | T_Ctor  : forall Γ K n_lt n_ty sigma_fields result_ty_schema
                     lts Ts rho_fields result_ty result_tag l vs,
      ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) ->
      ctx_lookup_eff Γ K = None ->   (* effect-tag / data-ctor disjointness *)
      List.length lts = n_lt ->
      lifetimes_wf Γ lts ->
      rho_fields = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields ->
      List.length Ts = n_ty ->
      types_wf Γ Ts ->
      result_ty = inst_ctor_type n_lt n_ty lts Ts result_ty_schema ->
      result_ty = type_ctor result_tag l Ts ->
      ctx_lookup_eff Γ result_tag = None ->
      lt_wf Γ l ->
      Γ ⊢ₗ lt_of_ty_list rho_fields <: lt_of_ty result_ty ->
      Forall (fun l0 => Γ ⊢ₗ l0 <: l) lts ->
      List.length vs = List.length rho_fields ->
      Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rho_fields ->
      Γ ⊢ₜ term_ctor K l lts Ts vs : result_ty

  (* --- Pattern match typing --------------------------------------- *)
  (* match scrut { K arity yes | _ => no } : elim_result              *)
  (*   Push n_lt fresh lt-vars bounded by Δ → extended ctx Γ'.        *)
  (*   Instantiate K's field types → ρ̄; type yes_body under the ρ̄     *)
  (*   term-binders on top of Γ'. Eliminate the fresh lt-vars (elim⁺) *)
  (*   from the branch result type η to get elim_result.              *)
  | T_Match : forall Γ scrut K n_lt n_ty sigma_fields result_ty_schema
                     Ts Delta arity lts rho_fields scrut_result_ty
                     result_tag result_l
                     Γ' yes_body eta elim_result no_body,
      K <> any_tag ->
      ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) ->
      ctx_lookup_eff Γ K = None ->   (* effect-tag / data-ctor disjointness *)
      lts = lt_var_list n_lt ->
      rho_fields = List.map (inst_ctor_type_open n_lt n_ty Ts) sigma_fields ->
      List.length Ts = n_ty ->
      types_wf Γ Ts ->
      scrut_result_ty = inst_ctor_type n_lt n_ty (List.repeat Delta n_lt) Ts result_ty_schema ->
      scrut_result_ty = type_ctor result_tag result_l Ts ->
      ctx_lookup_eff Γ result_tag = None ->
      result_tag <> any_tag ->
      lt_wf Γ Delta ->
      Γ ⊢ₗ result_l <: Delta ->
      Γ ⊢ₜ scrut : type_ctor result_tag Delta Ts ->
      arity = List.length rho_fields ->
      Γ' = push_match_bound n_lt Delta Γ ->
      (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ' rho_fields) ⊢ₜ yes_body : eta ->
      (* Delta lives in outer Γ; eta lives under n_lt fresh lt-binders, *)
      (* so Delta must be shifted up by n_lt before being used as the   *)
      (* positive-position bound for elimination.                       *)
      elim_ty_n n_lt (shift_lt n_lt 0 Delta) var_pos eta = Some elim_result ->
      Γ ⊢ₜ no_body : elim_result ->
      Γ ⊢ₜ term_match scrut K n_lt arity yes_body no_body : elim_result

  (* ================================================================ *)
  (* Effect-handler typing                                            *)
  (* ================================================================ *)

  (* (Cap): a runtime capability value has type `E local Ts`.          *)
  (* The op_body lives under n_β type-binders (for β-poly) and 2       *)
  (* term-binders (the operation argument and the resumption).         *)
  (* Convention in op-schema: α-vars are innermost (0..n_α-1) and      *)
  (* β-vars are outermost (n_α..n_α+n_β-1). After instantiating α      *)
  (* with lifted Ts at handle-time, the schema's β-vars become         *)
  (* 0..n_β-1, matching the n_β type-binders of op_body.               *)
  | T_Cap : forall Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β,
      ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
      List.length Ts = n_α ->
      types_wf Γ Ts ->
      ty_wf Γ T_R ->
      sig_β = inst_op_ty_args n_α Ts n_β sig ->
      ret_β = inst_op_ty_args n_α Ts n_β ret ->
      (op_body_ctx Γ n_β sig_β ret_β T_R)
        ⊢ₜ op_body : shift_ty n_β 0 T_R ->
      Γ ⊢ₜ term_cap E_tag m n_β Ts T_R op_body : type_ctor E_tag lt_local Ts

  (* NOTE on op-body variable convention (matching H_Perform):         *)
  (* subst_list_tm [v; resume] op_body substitutes:                    *)
  (*   $$ 0 → v      (operation argument,  type sig_β)                 *)
  (*   $$ 1 → resume (resumption k, type ret_β -local-> T_R)           *)
  (* Both T_Cap and T_Handle use the context                           *)
  (*   bind_tm sig_β               ← $$ 0 = arg  (innermost)           *)
  (*   :: bind_tm (ret_β -local->) ← $$ 1 = k                          *)
  (*   :: push_ty_vars n_β ...      ← β type-vars above                *)

  (* (Handle): allocate a capability and run the body.                 *)
  (* The ordinary return path is typed at no-local [T_B], while the    *)
  (* public handler answer [T_R] may also be produced by operation     *)
  (* bodies. This lets deep resumptions escape through operation       *)
  (* results without letting the handler body return its own cap.      *)
  | T_Handle : forall Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β,
      ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
      List.length Ts = n_α ->
      types_wf Γ Ts ->
      ty_wf Γ T_B ->
      ty_wf Γ T_R ->
      Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free ->
      Γ ⊢ T_B <:: T_R ->
      sig_β = inst_op_ty_args n_α Ts n_β sig ->
      ret_β = inst_op_ty_args n_α Ts n_β ret ->
      (op_body_ctx Γ n_β sig_β ret_β T_R)
        ⊢ₜ op_body : shift_ty n_β 0 T_R ->
      (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) ⊢ₜ body : T_B ->
      Γ ⊢ₜ term_handle E_tag n_β Ts T_B T_R op_body body : T_R

  (* (Perform): invoke the (single) operation on a capability value.   *)
  (* Caller supplies the β-type-arguments Ss at the perform site.      *)
  (* The β-arguments and the instantiated signature must be no-local   *)
  (* in [Γ] ([forallb no_local_ty_G Ss] and [no_local_ty_G sig_inst]): *)
  (* a value crossing the operation boundary must not smuggle a local  *)
  (* capability out of scope. *)
  | T_Perform : forall Γ recv arg E_tag Δ Ts Ss n_α n_β sig ret
                       sig_inst ret_inst,
      Γ ⊢ₜ recv : type_ctor E_tag Δ Ts ->
      ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
      List.length Ts = n_α ->
      List.length Ss = n_β ->
      types_wf Γ Ss ->
      Forall (fun S => Γ ⊢ₗ lt_of_ty_G Γ S <: lt_free) Ss ->
      sig_inst = inst_op_all_args n_α Ts n_β Ss sig ->
      Γ ⊢ₗ lt_of_ty_G Γ sig_inst <: lt_free ->
      ret_inst = inst_op_all_args n_α Ts n_β Ss ret ->
      ty_wf Γ ret_inst ->
      Γ ⊢ₜ arg : sig_inst ->
      Γ ⊢ₜ term_perform recv Ss ret_inst arg : ret_inst

  (* (HandlerM, runtime): a delimiter is transparent to typing.        *)
  | T_HandlerM : forall Γ m t T_B T_R,
      ty_wf Γ T_B ->
      ty_wf Γ T_R ->
      Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free ->
      Γ ⊢ T_B <:: T_R ->
      Γ ⊢ₜ t : T_B ->
      Γ ⊢ₜ term_handler_m m T_B T_R t : T_R


where "G '⊢ₜ' t ':' T" := (typing G t T).

Hint Constructors typing : core.

(* ------------------------------------------------------------------- *)
(* Forall2 plumbing + a Forall2-aware induction principle for `typing` *)
(*                                                                     *)
(* Coq's auto-generated `typing_ind` does NOT thread per-element       *)
(* induction hypotheses through the `Forall2` premise of T_Ctor.       *)
(* `typing_ind2` below augments the T_Ctor case with exactly that      *)
(* `Forall2 (fun v rho => P Γ v rho)` hypothesis, which is what lets   *)
(* `progress` and `preservation` discharge the constructor case        *)
(* without any axioms.                                                 *)
(* ------------------------------------------------------------------- *)


Lemma typing_ind2 :
  forall (P : ctx -> term -> type -> Prop),
  (forall Γ x T, ctx_lookup_tm Γ x = Some T -> ty_wf Γ T -> P Γ (term_var x) T) ->
  (forall Γ t T U, Γ ⊢ₜ t : T -> P Γ t T -> Γ ⊢ T <:: U -> P Γ t U) ->
  (forall Γ body A l B,
    ty_wf Γ A ->
    ty_wf Γ B ->
     (bind_tm A :: Γ) ⊢ₜ body : B -> P (bind_tm A :: Γ) body B ->
    Γ ⊢ₗ capture_lt Γ body <: l ->
     P Γ (term_lam body A) (type_fun A l B)) ->
  (forall Γ t1 t2 A l B,
     Γ ⊢ₜ t1 : type_fun A l B -> P Γ t1 (type_fun A l B) ->
     Γ ⊢ₜ t2 : A -> P Γ t2 A ->
     P Γ (term_app t1 t2) B) ->
  (forall Γ bound body T,
    ty_wf Γ bound ->
    ty_wf (bind_ty bound :: Γ) T ->
     (bind_ty bound :: Γ) ⊢ₜ body : T -> P (bind_ty bound :: Γ) body T ->
     P Γ (term_ty_lam bound body) (type_ty_all bound T)) ->
  (forall Γ t B U S,
     Γ ⊢ₜ t : type_ty_all B U -> P Γ t (type_ty_all B U) ->
    ty_wf Γ S ->
     Γ ⊢ S <:: B ->
     P Γ (term_ty_app t S) (subst_ty 0 S U)) ->
  (forall Γ body T,
    ty_wf (bind_lt lt_local :: Γ) T ->
     (bind_lt lt_local :: Γ) ⊢ₜ body : T -> P (bind_lt lt_local :: Γ) body T ->
     P Γ (term_lt_lam body) (type_lt_all T)) ->
  (forall Γ t T l,
     Γ ⊢ₜ t : type_lt_all T -> P Γ t (type_lt_all T) ->
    lt_wf Γ l ->
     P Γ (term_lt_app t l) (subst_lt_in_ty 0 l T)) ->
        (forall Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
          result_ty result_tag l vs,
     ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) ->
     ctx_lookup_eff Γ K = None ->
     List.length lts = n_lt ->
    lifetimes_wf Γ lts ->
     rho_fields = List.map (inst_ctor_type n_lt n_ty lts Ts) sigma_fields ->
     List.length Ts = n_ty ->
    types_wf Γ Ts ->
      result_ty = inst_ctor_type n_lt n_ty lts Ts result_ty_schema ->
      result_ty = type_ctor result_tag l Ts ->
      ctx_lookup_eff Γ result_tag = None ->
     lt_wf Γ l ->
      Γ ⊢ₗ lt_of_ty_list rho_fields <: lt_of_ty result_ty ->
      Forall (fun l0 => Γ ⊢ₗ l0 <: l) lts ->
     List.length vs = List.length rho_fields ->
     Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rho_fields ->
     Forall2 (fun v rho => P Γ v rho) vs rho_fields ->
      P Γ (term_ctor K l lts Ts vs) result_ty) ->
        (forall Γ scrut K n_lt n_ty sigma_fields result_ty_schema Ts Delta arity lts
          rho_fields scrut_result_ty result_tag result_l
         Γ' yes_body eta elim_result no_body,
     K <> any_tag ->
     ctx_lookup_ctor Γ K = Some (n_lt, n_ty, sigma_fields, result_ty_schema) ->
     ctx_lookup_eff Γ K = None ->
     lts = lt_var_list n_lt ->
     rho_fields = List.map (inst_ctor_type_open n_lt n_ty Ts) sigma_fields ->
      List.length Ts = n_ty ->
      types_wf Γ Ts ->
      scrut_result_ty = inst_ctor_type n_lt n_ty (List.repeat Delta n_lt) Ts result_ty_schema ->
      scrut_result_ty = type_ctor result_tag result_l Ts ->
      ctx_lookup_eff Γ result_tag = None ->
      result_tag <> any_tag ->
      lt_wf Γ Delta ->
      Γ ⊢ₗ result_l <: Delta ->
      Γ ⊢ₜ scrut : type_ctor result_tag Delta Ts ->
      P Γ scrut (type_ctor result_tag Delta Ts) ->
     arity = List.length rho_fields ->
     Γ' = push_match_bound n_lt Delta Γ ->
     (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ' rho_fields) ⊢ₜ yes_body : eta ->
     P (fold_right (fun rho Γ0 => bind_tm rho :: Γ0) Γ' rho_fields) yes_body eta ->
     elim_ty_n n_lt (shift_lt n_lt 0 Delta) var_pos eta = Some elim_result ->
     Γ ⊢ₜ no_body : elim_result -> P Γ no_body elim_result ->
    P Γ (term_match scrut K n_lt arity yes_body no_body) elim_result) ->
  (forall Γ E_tag m Ts op_body n_α n_β sig ret T_R sig_β ret_β,
     ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
     List.length Ts = n_α ->
    types_wf Γ Ts ->
    ty_wf Γ T_R ->
      sig_β = inst_op_ty_args n_α Ts n_β sig ->
      ret_β = inst_op_ty_args n_α Ts n_β ret ->
     (op_body_ctx Γ n_β sig_β ret_β T_R) ⊢ₜ op_body : shift_ty n_β 0 T_R ->
     P (op_body_ctx Γ n_β sig_β ret_β T_R) op_body (shift_ty n_β 0 T_R) ->
    P Γ (term_cap E_tag m n_β Ts T_R op_body) (type_ctor E_tag lt_local Ts)) ->
  (forall Γ E_tag Ts op_body body n_α n_β sig ret T_B T_R sig_β ret_β,
     ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
     List.length Ts = n_α ->
    types_wf Γ Ts ->
    ty_wf Γ T_B ->
    ty_wf Γ T_R ->
    Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free ->
    Γ ⊢ T_B <:: T_R ->
      sig_β = inst_op_ty_args n_α Ts n_β sig ->
      ret_β = inst_op_ty_args n_α Ts n_β ret ->
     (op_body_ctx Γ n_β sig_β ret_β T_R) ⊢ₜ op_body : shift_ty n_β 0 T_R ->
     P (op_body_ctx Γ n_β sig_β ret_β T_R) op_body (shift_ty n_β 0 T_R) ->
      (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) ⊢ₜ body : T_B ->
      P (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) body T_B ->
     P Γ (term_handle E_tag n_β Ts T_B T_R op_body body) T_R) ->
  (forall Γ recv arg E_tag Δ Ts Ss n_α n_β sig ret sig_inst ret_inst,
     Γ ⊢ₜ recv : type_ctor E_tag Δ Ts -> P Γ recv (type_ctor E_tag Δ Ts) ->
     ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
     List.length Ts = n_α ->
     List.length Ss = n_β ->
    types_wf Γ Ss ->
    Forall (fun S => Γ ⊢ₗ lt_of_ty_G Γ S <: lt_free) Ss ->
     sig_inst = inst_op_all_args n_α Ts n_β Ss sig ->
      Γ ⊢ₗ lt_of_ty_G Γ sig_inst <: lt_free ->
     ret_inst = inst_op_all_args n_α Ts n_β Ss ret ->
    ty_wf Γ ret_inst ->
     Γ ⊢ₜ arg : sig_inst -> P Γ arg sig_inst ->
     P Γ (term_perform recv Ss ret_inst arg) ret_inst) ->
  (forall Γ m T_B T_R t,
    ty_wf Γ T_B ->
    ty_wf Γ T_R ->
    Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free ->
    Γ ⊢ T_B <:: T_R ->
    Γ ⊢ₜ t : T_B -> P Γ t T_B ->
    P Γ (term_handler_m m T_B T_R t) T_R) ->
  forall Γ t T, Γ ⊢ₜ t : T -> P Γ t T.
Proof.
  intros P HVar HSub HLam HApp HTyLam HTyApp HLtLam HLtApp HCtor HMatch
         HCap HHandle HPerform HHandlerM.
  fix IH 4.
  intros Γ t T H. destruct H.
  - eapply HVar; (eassumption || (apply IH; eassumption)).
  - eapply HSub; (eassumption || (apply IH; eassumption)).
  - eapply HLam; (eassumption || (apply IH; eassumption)).
  - eapply HApp; (eassumption || (apply IH; eassumption)).
  - eapply HTyLam; (eassumption || (apply IH; eassumption)).
  - eapply HTyApp; (eassumption || (apply IH; eassumption)).
  - eapply HLtLam; (eassumption || (apply IH; eassumption)).
  - eapply HLtApp; (eassumption || (apply IH; eassumption)).
  - (* T_Ctor: build the Forall2 of IHs inline so the recursive calls    *)
    (* stay on structural subterms of the derivation (guardedness).      *)
    eapply HCtor; try (eassumption || (apply IH; eassumption)).
    match goal with
    | HF : Forall2 (fun v rho => _ ⊢ₜ v : rho) ?vs ?rf |- Forall2 _ ?vs ?rf =>
        clear -IH HF; induction HF
    end.
    + constructor.
    + constructor; [ apply IH; assumption | assumption ].
  - eapply HMatch; (eassumption || (apply IH; eassumption)).
  - eapply HCap; (eassumption || (apply IH; eassumption)).
  - eapply HHandle; (eassumption || (apply IH; eassumption)).
  - eapply HPerform; (eassumption || (apply IH; eassumption)).
  - eapply HHandlerM; (eassumption || (apply IH; eassumption)).
Qed.
