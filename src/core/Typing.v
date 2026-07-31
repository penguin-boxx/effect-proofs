Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Export Context.
Require Export Wf.
Require Export LtSub.
Require Export LtAnalysis.
Require Export Elim.
Require Export Subtyping.
Require Export Instantiate.

(* ================================================================== *)
(* The typing relation.  The static semantics is split into           *)
(* dependency-ordered modules, all re-exported here so that           *)
(* `Require Import Typing` provides the full static story:            *)
(*                                                                    *)
(*   Context.v     — contexts, lookups, signature shifting            *)
(*   Wf.v          — the well-formedness judgments                    *)
(*   LtSub.v       — lifetime subtyping (the two-point lattice)       *)
(*   LtAnalysis.v  — lt_of_ty / no_local_lt / free_tm_vars /          *)
(*                   capture_lt (the escape analyses)                 *)
(*   Elim.v        — variance and fresh-lifetime elimination          *)
(*   Subtyping.v   — type subtyping (full F<:)                        *)
(*   Instantiate.v — schema instantiation and context pushing         *)
(*   Typing.v      — the typing relation itself (this file)           *)
(* ================================================================== *)

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
(*              Γ ⊢ₜ t [S] : [α↦S] U                     (TApp)       *)
(* T_LtLam  : (l<:local)::Γ ⊢ₜ body : T →                             *)
(*              Γ ⊢ₜ Λl.body : ∀l.T                      (TLam, lt)   *)
(* T_LtApp  : Γ ⊢ₜ t : ∀l.T →                                         *)
(*              Γ ⊢ₜ t {Δ} : [l↦Δ] T                     (TApp, lt)   *)
(* ================================================================== *)

(* The op-body typing context shared by T_Cap and T_Handle: the        *)
(* operation argument $0 (innermost), the resumption $1 of type        *)
(* ret_β -local-> T_R, and the n_β β-type-binders above them.          *)
(* Projections of a per-operation declaration triple (n_β, sig, ret). *)
Definition op_nb     (osig : nat * type * type) : nat  := fst (fst osig).
Definition op_sig_ty (osig : nat * type * type) : type := snd (fst osig).
Definition op_ret_ty (osig : nat * type * type) : type := snd osig.

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
      typings Γ vs rho_fields ->
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
  | T_Cap : forall Γ E_tag m Ts op_bodies n_α ops T_R,
      ctx_lookup_eff Γ E_tag = Some (n_α, ops) ->
      List.length Ts = n_α ->
      types_wf Γ Ts ->
      ty_wf Γ T_R ->
      List.map fst op_bodies = List.map op_nb ops ->
      typing_ops Γ n_α Ts T_R op_bodies ops ->
      Γ ⊢ₜ term_cap E_tag m Ts T_R op_bodies : type_ctor E_tag lt_local Ts

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
  | T_Handle : forall Γ E_tag Ts op_bodies body n_α ops T_B T_R,
      ctx_lookup_eff Γ E_tag = Some (n_α, ops) ->
      List.length Ts = n_α ->
      types_wf Γ Ts ->
      ty_wf Γ T_B ->
      ty_wf Γ T_R ->
      Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free ->
      Γ ⊢ T_B <:: T_R ->
      List.map fst op_bodies = List.map op_nb ops ->
      typing_ops Γ n_α Ts T_R op_bodies ops ->
      (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) ⊢ₜ body : T_B ->
      Γ ⊢ₜ term_handle E_tag Ts T_B T_R op_bodies body : T_R

  (* (Perform): invoke one of the capability's operations, selected    *)
  (* by its declaration index [op] via [nth_error].                    *)
  (* Caller supplies the β-type-arguments Ss at the perform site.      *)
  (* The β-arguments and the instantiated signature must be no-local   *)
  (* in [Γ] ([lt_of_ty_G Γ S <: lt_free] for each S among Ss and for   *)
  (* [sig_inst]): a value crossing the operation boundary must not     *)
  (* smuggle a local capability out of scope. *)
  | T_Perform : forall Γ recv op arg E_tag Δ Ts Ss n_α ops n_β sig ret
                       sig_inst ret_inst,
      Γ ⊢ₜ recv : type_ctor E_tag Δ Ts ->
      ctx_lookup_eff Γ E_tag = Some (n_α, ops) ->
      nth_error ops op = Some (n_β, sig, ret) ->
      List.length Ts = n_α ->
      List.length Ss = n_β ->
      types_wf Γ Ss ->
      Forall (fun S => Γ ⊢ₗ lt_of_ty_G Γ S <: lt_free) Ss ->
      sig_inst = inst_op_all_args n_α Ts n_β Ss sig ->
      Γ ⊢ₗ lt_of_ty_G Γ sig_inst <: lt_free ->
      ret_inst = inst_op_all_args n_α Ts n_β Ss ret ->
      ty_wf Γ ret_inst ->
      Γ ⊢ₜ arg : sig_inst ->
      Γ ⊢ₜ term_perform recv op Ss ret_inst arg : ret_inst

  (* (HandlerM, runtime): a delimiter is transparent to typing.        *)
  | T_HandlerM : forall Γ m t T_B T_R,
      ty_wf Γ T_B ->
      ty_wf Γ T_R ->
      Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free ->
      Γ ⊢ T_B <:: T_R ->
      Γ ⊢ₜ t : T_B ->
      Γ ⊢ₜ term_handler_m m T_B T_R t : T_R

(* Pointwise typing of a constructor's field values against their      *)
(* instantiated field types (the T_Ctor premise; isomorphic to         *)
(* `Forall2 (fun v rho => Γ ⊢ₜ v : rho)` — see typings_Forall2).       *)
with typings : ctx -> list term -> list type -> Prop :=
  | TS_Nil : forall Γ, typings Γ [] []
  | TS_Cons : forall Γ v rho vs rhos,
      Γ ⊢ₜ v : rho ->
      typings Γ vs rhos ->
      typings Γ (v :: vs) (rho :: rhos)

(* Pointwise typing of a handler's operation bodies against the        *)
(* effect's operation signatures (the shared T_Cap/T_Handle premise;   *)
(* isomorphic to the corresponding Forall2 — see typing_ops_Forall2).  *)
with typing_ops : ctx -> nat -> list type -> type ->
                  list (nat * term) -> list (nat * type * type) -> Prop :=
  | TO_Nil : forall Γ n_α Ts T_R, typing_ops Γ n_α Ts T_R [] []
  | TO_Cons : forall Γ n_α Ts T_R ob osig op_bodies ops,
      (op_body_ctx Γ (op_nb osig)
         (inst_op_ty_args n_α Ts (op_nb osig) (op_sig_ty osig))
         (inst_op_ty_args n_α Ts (op_nb osig) (op_ret_ty osig)) T_R)
        ⊢ₜ snd ob : shift_ty (op_nb osig) 0 T_R ->
      typing_ops Γ n_α Ts T_R op_bodies ops ->
      typing_ops Γ n_α Ts T_R (ob :: op_bodies) (osig :: ops)

where "G '⊢ₜ' t ':' T" := (typing G t T).

Hint Constructors typing typings typing_ops : core.

(* ------------------------------------------------------------------- *)
(* Generated mutual induction schemes.                                 *)
(*                                                                     *)
(* Because `typing`/`typings`/`typing_ops` form one mutual block, the  *)
(* Scheme command generates an induction principle that threads        *)
(* per-element induction hypotheses through the list premises of       *)
(* T_Ctor / T_Cap / T_Handle — no hand-maintained principle needed.    *)
(* (`Minimality` = the non-dependent form, matching `typing_ind`.)     *)
(* ------------------------------------------------------------------- *)

Scheme typing_mut_ind := Minimality for typing Sort Prop
  with typings_mut_ind := Minimality for typings Sort Prop
  with typing_ops_mut_ind := Minimality for typing_ops Sort Prop.

Combined Scheme typing_typings_ops_mut_ind
  from typing_mut_ind, typings_mut_ind, typing_ops_mut_ind.

(* ------------------------------------------------------------------- *)
(* Round-trip bridges: the mutual list relations are exactly the       *)
(* Forall2 forms they replaced.                                        *)
(* ------------------------------------------------------------------- *)

Lemma typings_Forall2 : forall Γ vs rhos,
  typings Γ vs rhos <-> Forall2 (fun v rho => Γ ⊢ₜ v : rho) vs rhos.
Proof.
  intros Γ vs rhos; split; intros H; induction H; constructor; assumption.
Qed.

Lemma typing_ops_Forall2 : forall Γ n_α Ts T_R op_bodies ops,
  typing_ops Γ n_α Ts T_R op_bodies ops <->
  Forall2 (fun ob osig =>
    (op_body_ctx Γ (op_nb osig)
       (inst_op_ty_args n_α Ts (op_nb osig) (op_sig_ty osig))
       (inst_op_ty_args n_α Ts (op_nb osig) (op_ret_ty osig)) T_R)
      ⊢ₜ snd ob : shift_ty (op_nb osig) 0 T_R)
    op_bodies ops.
Proof.
  intros Γ n_α Ts T_R op_bodies ops; split; intros H; induction H;
    constructor; assumption.
Qed.

(* ------------------------------------------------------------------- *)
(* Native theory of the mutual list relations: length, indexing,       *)
(* append splitting and focused replacement, stated directly on        *)
(* typings/typing_ops so downstream proofs need not detour through     *)
(* the Forall2 bridges.                                                *)
(* ------------------------------------------------------------------- *)

Lemma typings_length : forall Γ vs rhos,
  typings Γ vs rhos -> List.length vs = List.length rhos.
Proof.
  intros Γ vs rhos H; induction H; simpl; auto.
Qed.

(* Indexing: the i-th value is typed at the i-th field type. *)
Lemma typings_nth_error : forall Γ vs rhos i v,
  typings Γ vs rhos ->
  nth_error vs i = Some v ->
  exists rho, nth_error rhos i = Some rho /\ Γ ⊢ₜ v : rho.
Proof.
  intros Γ vs rhos i v H; revert i v.
  induction H; intros i v0 Hnth; [destruct i; discriminate|].
  destruct i as [|i']; simpl in *.
  - injection Hnth; intros; subst. eauto.
  - eauto.
Qed.

(* Indexing: the i-th op body is typed against the i-th op signature. *)
Lemma typing_ops_nth_error : forall Γ n_α Ts T_R op_bodies ops i ob,
  typing_ops Γ n_α Ts T_R op_bodies ops ->
  nth_error op_bodies i = Some ob ->
  exists osig, nth_error ops i = Some osig /\
    (op_body_ctx Γ (op_nb osig)
       (inst_op_ty_args n_α Ts (op_nb osig) (op_sig_ty osig))
       (inst_op_ty_args n_α Ts (op_nb osig) (op_ret_ty osig)) T_R)
      ⊢ₜ snd ob : shift_ty (op_nb osig) 0 T_R.
Proof.
  intros Γ n_α Ts T_R op_bodies ops i ob H; revert i ob.
  induction H; intros i ob0 Hnth; [destruct i; discriminate|].
  destruct i as [|i']; simpl in *.
  - injection Hnth; intros; subst. eauto.
  - eauto.
Qed.

(* Splitting along an append of the value list. *)
Lemma typings_app_inv : forall Γ vs1 vs2 rhos,
  typings Γ (vs1 ++ vs2) rhos ->
  exists rhos1 rhos2,
    rhos = rhos1 ++ rhos2 /\ typings Γ vs1 rhos1 /\ typings Γ vs2 rhos2.
Proof.
  intros Γ vs1; induction vs1 as [|v vs1 IH]; intros vs2 rhos H; simpl in *.
  - exists [], rhos. split; [reflexivity | split; [constructor | assumption]].
  - inversion H; subst.
    match goal with Htl : typings _ (vs1 ++ vs2) _ |- _ =>
      destruct (IH _ _ Htl) as (rhos1 & rhos2 & -> & H1 & H2) end.
    eexists (_ :: rhos1), rhos2.
    split; [reflexivity | split; [constructor; eassumption | assumption]].
Qed.

(* Replacing the focused element of a frame's value list preserves     *)
(* typings, given the replacement is typed at every type the original  *)
(* is (the T_Ctor frame congruence — see Frames.v).                    *)
Lemma typings_focus_replace : forall Γ vs u u' ts rhos,
  typings Γ (vs ++ u :: ts) rhos ->
  (forall rho, Γ ⊢ₜ u : rho -> Γ ⊢ₜ u' : rho) ->
  typings Γ (vs ++ u' :: ts) rhos.
Proof.
  intros Γ vs u u' ts rhos H Himpl.
  revert rhos H. induction vs as [|v vs IH]; intros rhos H; simpl in *.
  - inversion H; subst. constructor; [apply Himpl; assumption | assumption].
  - inversion H; subst. constructor; [assumption | apply IH; assumption].
Qed.

(* ------------------------------------------------------------------- *)
(* The Forall2-aware induction principle for `typing`, now derived     *)
(* from the generated mutual scheme (motives for the list relations    *)
(* are the Forall2 of per-element IHs).  Every typing mega-proof       *)
(* (Weakening, SubstLt, SubstTm, TypingSubst, ProgramCtx, Progress)    *)
(* inducts with this.                                                  *)
(* ------------------------------------------------------------------- *)

Lemma typing_ind_forall2 :
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
      is_abs body = true ->
     (bind_ty bound :: Γ) ⊢ₜ body : T -> P (bind_ty bound :: Γ) body T ->
     P Γ (term_ty_lam bound body) (type_ty_all bound T)) ->
  (forall Γ t B U S,
     Γ ⊢ₜ t : type_ty_all B U -> P Γ t (type_ty_all B U) ->
      ty_wf Γ S ->
     Γ ⊢ S <:: B ->
     P Γ (term_ty_app t S) (subst_ty 0 S U)) ->
  (forall Γ body T,
      ty_wf (bind_lt lt_local :: Γ) T ->
      is_abs body = true ->
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
  (forall Γ E_tag m Ts op_bodies n_α ops T_R,
     ctx_lookup_eff Γ E_tag = Some (n_α, ops) ->
     List.length Ts = n_α ->
    types_wf Γ Ts ->
    ty_wf Γ T_R ->
     List.map fst op_bodies = List.map op_nb ops ->
     Forall2 (fun ob osig =>
        (op_body_ctx Γ (op_nb osig)
           (inst_op_ty_args n_α Ts (op_nb osig) (op_sig_ty osig))
           (inst_op_ty_args n_α Ts (op_nb osig) (op_ret_ty osig)) T_R)
          ⊢ₜ snd ob : shift_ty (op_nb osig) 0 T_R)
       op_bodies ops ->
     Forall2 (fun ob osig =>
        P (op_body_ctx Γ (op_nb osig)
             (inst_op_ty_args n_α Ts (op_nb osig) (op_sig_ty osig))
             (inst_op_ty_args n_α Ts (op_nb osig) (op_ret_ty osig)) T_R)
          (snd ob) (shift_ty (op_nb osig) 0 T_R))
       op_bodies ops ->
    P Γ (term_cap E_tag m Ts T_R op_bodies) (type_ctor E_tag lt_local Ts)) ->
  (forall Γ E_tag Ts op_bodies body n_α ops T_B T_R,
     ctx_lookup_eff Γ E_tag = Some (n_α, ops) ->
     List.length Ts = n_α ->
    types_wf Γ Ts ->
    ty_wf Γ T_B ->
    ty_wf Γ T_R ->
    Γ ⊢ₗ lt_of_ty_G Γ T_B <: lt_free ->
    Γ ⊢ T_B <:: T_R ->
     List.map fst op_bodies = List.map op_nb ops ->
     Forall2 (fun ob osig =>
        (op_body_ctx Γ (op_nb osig)
           (inst_op_ty_args n_α Ts (op_nb osig) (op_sig_ty osig))
           (inst_op_ty_args n_α Ts (op_nb osig) (op_ret_ty osig)) T_R)
          ⊢ₜ snd ob : shift_ty (op_nb osig) 0 T_R)
       op_bodies ops ->
     Forall2 (fun ob osig =>
        P (op_body_ctx Γ (op_nb osig)
             (inst_op_ty_args n_α Ts (op_nb osig) (op_sig_ty osig))
             (inst_op_ty_args n_α Ts (op_nb osig) (op_ret_ty osig)) T_R)
          (snd ob) (shift_ty (op_nb osig) 0 T_R))
       op_bodies ops ->
      (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) ⊢ₜ body : T_B ->
      P (bind_tm (type_ctor E_tag lt_local Ts) :: Γ) body T_B ->
     P Γ (term_handle E_tag Ts T_B T_R op_bodies body) T_R) ->
  (forall Γ recv op arg E_tag Delta Ts Ss n_α ops n_β sig ret sig_inst ret_inst,
     Γ ⊢ₜ recv : type_ctor E_tag Delta Ts -> P Γ recv (type_ctor E_tag Delta Ts) ->
     ctx_lookup_eff Γ E_tag = Some (n_α, ops) ->
     nth_error ops op = Some (n_β, sig, ret) ->
     List.length Ts = n_α ->
     List.length Ss = n_β ->
    types_wf Γ Ss ->
    Forall (fun S => Γ ⊢ₗ lt_of_ty_G Γ S <: lt_free) Ss ->
     sig_inst = inst_op_all_args n_α Ts n_β Ss sig ->
      Γ ⊢ₗ lt_of_ty_G Γ sig_inst <: lt_free ->
     ret_inst = inst_op_all_args n_α Ts n_β Ss ret ->
    ty_wf Γ ret_inst ->
     Γ ⊢ₜ arg : sig_inst -> P Γ arg sig_inst ->
     P Γ (term_perform recv op Ss ret_inst arg) ret_inst) ->
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
  apply (typing_mut_ind P
    (fun Γ vs rhos => Forall2 (fun v rho => P Γ v rho) vs rhos)
    (fun Γ n_α Ts T_R obs ops =>
       Forall2 (fun ob osig =>
         P (op_body_ctx Γ (op_nb osig)
              (inst_op_ty_args n_α Ts (op_nb osig) (op_sig_ty osig))
              (inst_op_ty_args n_α Ts (op_nb osig) (op_ret_ty osig)) T_R)
           (snd ob) (shift_ty (op_nb osig) 0 T_R)) obs ops));
    try assumption.
  - (* T_Ctor: recover the Forall2-of-typings via the bridge. *)
    intros Γ K n_lt n_ty sigma_fields result_ty_schema lts Ts rho_fields
           result_ty result_tag l vs
           Hlk Heff Hlts Hwflts Hrho HTs HwfTs Hres Hshape Hreseff Hwfl
           Hesc Hbound Hlen Hvs IHvs.
    eapply HCtor; try eassumption.
    apply typings_Forall2; exact Hvs.
  - (* T_Cap *)
    intros Γ E_tag m Ts op_bodies n_α ops T_R
           Heff Hlen HwfTs HwfTR Hfst Hops IHops.
    eapply HCap; try eassumption.
    apply typing_ops_Forall2; exact Hops.
  - (* T_Handle *)
    intros Γ E_tag Ts op_bodies body n_α ops T_B T_R
           Heff Hlen HwfTs HwfTB HwfTR Hnl Hsub Hfst Hops IHops Hbody IHbody.
    eapply HHandle; try eassumption.
    apply typing_ops_Forall2; exact Hops.
  - (* T_HandlerM (binder order differs from the constructor's) *)
    intros Γ m t T_B T_R HwfTB HwfTR Hnl Hsub Ht IHt.
    apply HHandlerM; assumption.
  - (* typings nil *) intros Γ. cbv beta. constructor.
  - (* typings cons *) intros Γ v rho vs rhos Hv IHv Hvs IHvs.
    cbv beta. constructor; assumption.
  - (* typing_ops nil *) intros Γ n_α Ts T_R. cbv beta. constructor.
  - (* typing_ops cons *) intros Γ n_α Ts T_R ob osig obs ops Hob IHob Hobs IHobs.
    cbv beta. constructor; assumption.
Qed.

#[export] Hint Constructors lt_wf ty_wf types_wf lifetimes_wf lt_sub sub typing typings typing_ops : lang.
