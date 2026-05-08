(* ================================================================== *)
(* CEKTyping.v — typing for CEK runtime values, environments, konts,  *)
(* and configurations.                                                *)
(*                                                                    *)
(* Strategy: Approach (a) from the migration plan.  Type a runtime    *)
(* control term `(t, ρ)` cofinitely by opening every bvar position    *)
(* with a fresh atom and pushing the env's types into Γ.  No          *)
(* substitution-on-rvalues; no axioms about substitution stability.   *)
(*                                                                    *)
(* Conventions                                                        *)
(* ===========                                                        *)
(* env order: ρ[0] = innermost binder = `term_bvar 0`.                 *)
(* Atom-list `xs` parameterising VE_intro / VT_Lam follows the SAME    *)
(* convention: head of `xs` corresponds to ρ[0]/bvar 0.               *)
(* env_extend pushes head-of-xs at HEAD of Γ (innermost lookup).      *)
(* open_with_env_atoms applies `rev xs` so that bvar 0 is replaced    *)
(* by the head atom (matching the LN open's shifting behaviour, see   *)
(* `open_tm_wrt_tm_rec`'s `Gt => term_bvar (pred n)` clause in        *)
(* Substitution.v).                                                   *)
(* ================================================================== *)

From Stdlib Require Import List PeanoNat.
Import ListNotations.
From Metalib Require Export Metatheory.

Require Import Syntax.
Require Import Substitution.
Require Import Typing.
Require Import CEK.

(* ================================================================== *)
(* Helpers                                                            *)
(* ================================================================== *)

Fixpoint env_extend (xs : list atom) (Ts : list type) (Γ : ctx) : ctx :=
  match xs, Ts with
  | x :: rxs, T :: rTs => bind_tm x T :: env_extend rxs rTs Γ
  | _, _               => Γ
  end.

Definition open_with_env_atoms (xs : list atom) (t : term) : term :=
  open_tm_wrt_tms (List.rev xs) t.

(* ================================================================== *)
(* Mutual typing judgements                                            *)
(*                                                                     *)
(*   value_typing Γ v T                                                *)
(*     —  the runtime value v has type T under Γ.                     *)
(*                                                                     *)
(*   env_typing Γ ρ Ts                                                *)
(*     —  ρ is an environment whose i-th value has type Ts[i].        *)
(*                                                                     *)
(*   ev_typing Γ t ρ T                                                *)
(*     —  the configuration ⟨t, ρ⟩ types to T:  cofinitely picking    *)
(*        fresh atoms for every env slot, opening t with them, and   *)
(*        type-checking under the extended ctx.                       *)
(*                                                                     *)
(*   kont_typing Γ K A T                                              *)
(*     —  K consumes a value of type A and produces a value of type T.*)
(*                                                                     *)
(* ================================================================== *)

Inductive value_typing : ctx -> rvalue -> type -> Prop :=

  | VT_Lam : forall (L : atoms) Γ body ρ Ts A l B,
      env_typing Γ ρ Ts ->
      (forall x, x `notin` L ->
         ev_typing (bind_tm x A :: Γ)
                   (open_tm_wrt_tm (term_fvar x) body)
                   ρ B) ->
      Γ |-l capture_lt Γ (term_lam body A) <: l ->
      value_typing Γ (clos_lam body ρ A) (type_fun A l B)

  | VT_TyLam : forall (L : atoms) Γ bound body ρ Ts T,
      env_typing Γ ρ Ts ->
      (forall a, a `notin` L ->
         ev_typing (bind_ty a bound :: Γ)
                   (open_tm_wrt_ty (type_fvar a) body)
                   ρ
                   (open_ty_wrt_ty (type_fvar a) T)) ->
      value_typing Γ (clos_ty_lam bound body ρ) (type_ty_all bound T)

  | VT_LtLam : forall (L : atoms) Γ body ρ Ts T,
      env_typing Γ ρ Ts ->
      (forall a, a `notin` L ->
         ev_typing (bind_lt a lt_local :: Γ)
                   (open_tm_wrt_lt (lt_fvar a) body)
                   ρ
                   (open_ty_wrt_lt (lt_fvar a) T)) ->
      value_typing Γ (clos_lt_lam body ρ) (type_lt_all T)

  | VT_Ctor : forall Γ K n_lt n_ty sigma_fields
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
      Forall2 (fun v rho => value_typing Γ v rho) vs rho_fields ->
      inst_ctor_type lts Ts (type_ctor K_res lr_schema Ts_res_schema)
        = type_ctor K_res lr_inst Ts_res_inst ->
      value_typing Γ (clos_ctor K l lts Ts vs)
                     (type_ctor K_res lr_inst Ts_res_inst)

  (* A runtime cap value is morphologically equivalent to T_Cap on    *)
  (* the source `term_cap`, but evaluated under environment ρ, so we  *)
  (* re-state the rule: ρ types under Γ, and the op_body type-checks  *)
  (* under fresh β/arg/k atoms PLUS the env's atoms.                  *)
  | VT_Cap : forall (L : atoms) Γ E_tag m Ts op_body ρ Tρ
                     n_α n_β sig ret T_R sig_β ret_β,
      ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
      length Ts = n_α ->
      sig_β = open_ty_wrt_ty_list Ts sig ->
      ret_β = open_ty_wrt_ty_list Ts ret ->
      env_typing Γ ρ Tρ ->
      (forall (β_xs : list atom) (arg_x k_x : atom),
          length β_xs = n_β ->
          NoDup β_xs ->
          arg_x <> k_x ->
          (forall a, In a β_xs -> a `notin` L) ->
          arg_x `notin` L -> k_x `notin` L ->
          let Γ_β := push_ty_atoms β_xs any_at_free Γ in
          let Γ' := bind_tm arg_x (open_ty_wrt_ty_list (List.map type_fvar β_xs) sig_β)
                 :: bind_tm k_x   (type_fun
                                    (open_ty_wrt_ty_list (List.map type_fvar β_xs) ret_β)
                                    lt_local
                                    T_R)
                 :: Γ_β in
          (* op_body still evaluates under env ρ, with arg/k pre-opened. *)
          (* CEK convention: bvar 0 = arg, bvar 1 = k.                  *)
          ev_typing Γ'
            (open_tm_wrt_tm (term_fvar k_x)
              (open_tm_wrt_tm (term_fvar arg_x)
                (open_tm_wrt_ty_list (List.map type_fvar β_xs) op_body)))
            ρ T_R) ->
      value_typing Γ (clos_cap E_tag m Ts op_body ρ) (type_ctor E_tag lt_local Ts)

  (* A reified resumption: typed via its captured kont.  The kont    *)
  (* takes an A and produces a T — that is exactly the function     *)
  (* type.  Lifetime is `lt_local` because resumptions must be       *)
  (* used (and discarded) within their handler's scope.              *)
  | VT_Resume : forall Γ Kr A T,
      kont_typing Γ Kr A T ->
      value_typing Γ (clos_resume Kr) (type_fun A lt_local T)

  | VT_Sub : forall Γ v T U,
      value_typing Γ v T ->
      Γ |-T T <: U ->
      value_typing Γ v U

with env_typing : ctx -> env -> list type -> Prop :=
  | ENT_nil  : forall Γ, env_typing Γ [] []
  | ENT_cons : forall Γ v ρ T Ts,
      value_typing Γ v T ->
      env_typing Γ ρ Ts ->
      env_typing Γ (v :: ρ) (T :: Ts)

with ev_typing : ctx -> term -> env -> type -> Prop :=
  | EVT_intro : forall (L : atoms) Γ t ρ Ts T,
      env_typing Γ ρ Ts ->
      (forall xs,
         length xs = length ρ ->
         NoDup xs ->
         (forall y, In y xs -> y `notin` L) ->
         env_extend xs Ts Γ |-t open_with_env_atoms xs t : T) ->
      ev_typing Γ t ρ T

with kont_typing : ctx -> kont -> type -> type -> Prop :=

  | KT_nil : forall Γ A,
      kont_typing Γ [] A A

  (* KApp1 t2 ρ : we just produced a function v1 of type (A -l-> B). *)
  (* Next step is to evaluate t2 under ρ to a value of type A, then  *)
  (* apply.                                                           *)
  | KT_App1 : forall Γ A l B t2 ρ K T,
      ev_typing Γ t2 ρ A ->
      kont_typing Γ K B T ->
      kont_typing Γ (KApp1 t2 ρ :: K) (type_fun A l B) T

  (* KApp2 v1 : v1 is the already-evaluated function.  We expect a   *)
  (* value of v1's argument type.                                     *)
  | KT_App2 : forall Γ v1 A l B K T,
      value_typing Γ v1 (type_fun A l B) ->
      kont_typing Γ K B T ->
      kont_typing Γ (KApp2 v1 :: K) A T

  | KT_TyApp : forall Γ B U S K T,
      Γ |-T S <: B ->
      kont_typing Γ K (open_ty_wrt_ty S U) T ->
      kont_typing Γ (KTyApp S :: K) (type_ty_all B U) T

  | KT_LtApp : forall Γ U l K T,
      kont_typing Γ K (open_ty_wrt_lt l U) T ->
      kont_typing Γ (KLtApp l :: K) (type_lt_all U) T

  (* KCtor: incoming value is the next field (with type rho_fields[|vs|]).
     vs are values already typed; ts are terms still to evaluate.   *)
  | KT_Ctor : forall Γ Kt n_lt n_ty sigma_fields
                     K_res lr_schema Ts_res_schema
                     lts Tparams rho_fields l vs ts ρ Tρ K T
                     lr_inst Ts_res_inst,
      ctx_lookup_ctor Γ Kt = Some (n_lt, n_ty, sigma_fields,
                                    type_ctor K_res lr_schema Ts_res_schema) ->
      ctx_lookup_eff  Γ Kt = None ->
      length lts = n_lt ->
      length Tparams  = n_ty ->
      rho_fields = List.map (inst_ctor_type lts Tparams) sigma_fields ->
      l = lt_of_ty_list rho_fields ->
      length vs + 1 + length ts = length rho_fields ->
      env_typing Γ ρ Tρ ->
      inst_ctor_type lts Tparams (type_ctor K_res lr_schema Ts_res_schema)
        = type_ctor K_res lr_inst Ts_res_inst ->
      Forall2 (fun v rho => value_typing Γ v rho) vs (firstn (length vs) rho_fields) ->
      Forall2 (fun t rho => ev_typing Γ t ρ rho) ts (skipn (S (length vs)) rho_fields) ->
      kont_typing Γ K (type_ctor K_res lr_inst Ts_res_inst) T ->
      kont_typing Γ (KCtor Kt l lts Tparams vs ts ρ :: K)
                    (nth (length vs) rho_fields
                         (type_ctor K_res lr_inst Ts_res_inst))
                    T

  (* KMatch: the incoming value is a ctor; we type it the same way as *)
  (* T_Match in Typing.v, with cofinite atoms.                        *)
  | KT_Match : forall (L : atoms) Γ Kt n_lt n_ty
                     sigma_fields K_res lr_schema Ts_res_schema
                     Tparams Delta Ts_res_inst arity yes_body eta elim_result no_body
                     ρ Tρ K T,
      Kt <> any_tag ->
      ctx_lookup_ctor Γ Kt = Some (n_lt, n_ty, sigma_fields,
                                    type_ctor K_res lr_schema Ts_res_schema) ->
      ctx_lookup_eff  Γ Kt = None ->
      length Tparams = n_ty ->
      arity = length sigma_fields ->
      env_typing Γ ρ Tρ ->
      (forall (lt_xs : list atom) (tm_xs : list atom),
          length lt_xs = n_lt ->
          length tm_xs = arity ->
          NoDup lt_xs -> NoDup tm_xs ->
          (forall x, In x lt_xs -> x `notin` L) ->
          (forall x, In x tm_xs -> x `notin` L) ->
          let lts := List.map lt_fvar lt_xs in
          let rho_fields := List.map (inst_ctor_type lts Tparams) sigma_fields in
          ev_typing
            (push_tm_atoms tm_xs rho_fields (push_lt_atoms lt_xs Delta Γ))
            (open_tm_wrt_tms tm_xs (open_tm_wrt_lt_list lts yes_body))
            ρ eta /\
          elim_ty_atoms lt_xs Delta var_pos eta = Some elim_result) ->
      ev_typing Γ no_body ρ elim_result ->
      kont_typing Γ K elim_result T ->
      kont_typing Γ (KMatch Kt arity yes_body no_body ρ :: K)
                    (type_ctor K_res Delta Ts_res_inst) T

  (* KHandle: the delimiter; consumes the body's value (type T_R)    *)
  (* and yields the same.  The handler clause must have already been *)
  (* shown correct at handle-time, but we need it here too because   *)
  (* a perform that reaches this delimiter will fire op_body.        *)
  | KT_Handle : forall (L : atoms) Γ m E_tag Ts op_body ρ Tρ
                       n_α n_β sig ret T_R sig_β ret_β K T,
      ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
      length Ts = n_α ->
      sig_β = open_ty_wrt_ty_list Ts sig ->
      ret_β = open_ty_wrt_ty_list Ts ret ->
      env_typing Γ ρ Tρ ->
      (forall (β_xs : list atom) (arg_x k_x : atom),
          length β_xs = n_β ->
          NoDup β_xs ->
          arg_x <> k_x ->
          (forall a, In a β_xs -> a `notin` L) ->
          arg_x `notin` L -> k_x `notin` L ->
          let Γ_β := push_ty_atoms β_xs any_at_free Γ in
          let Γ' := bind_tm arg_x (open_ty_wrt_ty_list (List.map type_fvar β_xs) sig_β)
                 :: bind_tm k_x   (type_fun
                                    (open_ty_wrt_ty_list (List.map type_fvar β_xs) ret_β)
                                    lt_local
                                    T_R)
                 :: Γ_β in
          (* CEK convention: bvar 0 = arg, bvar 1 = k. *)
          ev_typing Γ'
            (open_tm_wrt_tm (term_fvar k_x)
              (open_tm_wrt_tm (term_fvar arg_x)
                (open_tm_wrt_ty_list (List.map type_fvar β_xs) op_body)))
            ρ T_R) ->
      kont_typing Γ K T_R T ->
      kont_typing Γ (KHandle m E_tag Ts op_body ρ :: K) T_R T

  (* KPerformR: the receiver was being evaluated; once a cap value  *)
  (* arrives we move to evaluating the argument.                     *)
  | KT_PerformR : forall Γ E_tag Δ Tparams Ss n_α n_β sig ret
                         sig_inst ret_inst arg ρ Tρ K T,
      ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
      length Tparams = n_α ->
      length Ss = n_β ->
      sig_inst = open_ty_wrt_ty_list (Ss ++ Tparams) sig ->
      ret_inst = open_ty_wrt_ty_list (Ss ++ Tparams) ret ->
      ev_typing Γ arg ρ sig_inst ->
      env_typing Γ ρ Tρ ->
      kont_typing Γ K ret_inst T ->
      kont_typing Γ (KPerformR Ss arg ρ :: K)
                    (type_ctor E_tag Δ Tparams) T

  (* KPerformA: the cap value v_recv has already been computed; we are
     evaluating the argument.  Once it is a value, we fire the op.   *)
  | KT_PerformA : forall Γ v_recv E_tag Δ Tparams Ss n_α n_β sig ret
                         sig_inst ret_inst K T,
      value_typing Γ v_recv (type_ctor E_tag Δ Tparams) ->
      ctx_lookup_eff Γ E_tag = Some (n_α, n_β, sig, ret) ->
      length Tparams = n_α ->
      length Ss = n_β ->
      sig_inst = open_ty_wrt_ty_list (Ss ++ Tparams) sig ->
      ret_inst = open_ty_wrt_ty_list (Ss ++ Tparams) ret ->
      kont_typing Γ K ret_inst T ->
      kont_typing Γ (KPerformA v_recv Ss :: K) sig_inst T

  | KT_Sub : forall Γ K A A' T T',
      kont_typing Γ K A T ->
      Γ |-T A' <: A ->
      Γ |-T T <: T' ->
      kont_typing Γ K A' T'
  .

#[export] Hint Constructors value_typing env_typing ev_typing kont_typing : core.

(* ================================================================== *)
(* Configuration typing                                               *)
(* ================================================================== *)

Inductive config_typing : config -> type -> Prop :=
  | CT_ev  : forall t ρ K nm A T,
      ev_typing [] t ρ A ->
      kont_typing [] K A T ->
      config_typing (C_ev t ρ K nm) T

  | CT_ret : forall v K nm A T,
      value_typing [] v A ->
      kont_typing [] K A T ->
      config_typing (C_ret v K nm) T

  | CT_done : forall v T,
      value_typing [] v T ->
      config_typing (C_done v) T
  .

#[export] Hint Constructors config_typing : core.

(* ================================================================== *)
(* Marker well-formedness invariant                                    *)
(*                                                                     *)
(* `kont_markers K` is the list of markers introduced by KHandle      *)
(* frames within K.  A configuration is "marker-well-formed" iff:     *)
(*   (a) every reachable `clos_cap E m _ _ _` has m ∈ kont_markers K  *)
(*       (so split_at_handler m K succeeds);                          *)
(*   (b) every reachable `clos_resume Kr` is internally consistent:   *)
(*       Kr is a valid prefix that ends in a KHandle frame, and its  *)
(*       caps' markers are accounted for by kont_markers (Kr ++ K).   *)
(*   (c) markers introduced by KHandle frames are pairwise distinct. *)
(*                                                                     *)
(* This invariant is required by the progress proof for               *)
(* CS_KPerformFire (where split_at_handler must succeed) and is       *)
(* preserved by every cstep rule because:                              *)
(*   - CS_Handle adds a fresh marker `nm` and the (S nm) counter      *)
(*     guarantees future allocations remain fresh;                    *)
(*   - CS_KPerformFire splits the kont, but the resulting Kr ends in  *)
(*     KHandle so its caps remain accounted for.                       *)
(* ================================================================== *)

Fixpoint kont_markers (K : kont) : list marker :=
  match K with
  | []                          => []
  | KHandle m _ _ _ _ :: rest   => m :: kont_markers rest
  | _ :: rest                   => kont_markers rest
  end.

(* Mutual well-marked-ness over rvalues, environments and konts.      *)
(* `M` is the ambient marker set: caps must have their marker in M.   *)
Inductive well_marked_v : list marker -> rvalue -> Prop :=
  | wmv_lam : forall M body ρ A,
      Forall (well_marked_v M) ρ ->
      well_marked_v M (clos_lam body ρ A)
  | wmv_ty_lam : forall M bound body ρ,
      Forall (well_marked_v M) ρ ->
      well_marked_v M (clos_ty_lam bound body ρ)
  | wmv_lt_lam : forall M body ρ,
      Forall (well_marked_v M) ρ ->
      well_marked_v M (clos_lt_lam body ρ)
  | wmv_ctor : forall M K l lts Ts vs,
      Forall (well_marked_v M) vs ->
      well_marked_v M (clos_ctor K l lts Ts vs)
  | wmv_cap : forall M E m Ts ob ρ,
      In m M ->
      Forall (well_marked_v M) ρ ->
      well_marked_v M (clos_cap E m Ts ob ρ)
  | wmv_resume : forall M Kr,
      (* Kr's own KHandle markers live above it; combined with M they  *)
      (* give the marker set in scope inside Kr.                        *)
      well_marked_K (kont_markers Kr ++ M) Kr ->
      well_marked_v M (clos_resume Kr)

with well_marked_kf : list marker -> kframe -> Prop :=
  | wmf_app1 : forall M t2 ρ,
      Forall (well_marked_v M) ρ ->
      well_marked_kf M (KApp1 t2 ρ)
  | wmf_app2 : forall M v,
      well_marked_v M v ->
      well_marked_kf M (KApp2 v)
  | wmf_tyapp : forall M T, well_marked_kf M (KTyApp T)
  | wmf_ltapp : forall M l, well_marked_kf M (KLtApp l)
  | wmf_ctor : forall M K l lts Ts vs ts ρ,
      Forall (well_marked_v M) vs ->
      Forall (well_marked_v M) ρ ->
      well_marked_kf M (KCtor K l lts Ts vs ts ρ)
  | wmf_match : forall M Kt ar y n ρ,
      Forall (well_marked_v M) ρ ->
      well_marked_kf M (KMatch Kt ar y n ρ)
  | wmf_handle : forall M m E Ts ob ρ,
      Forall (well_marked_v M) ρ ->
      well_marked_kf M (KHandle m E Ts ob ρ)
  | wmf_performR : forall M Ss arg ρ,
      Forall (well_marked_v M) ρ ->
      well_marked_kf M (KPerformR Ss arg ρ)
  | wmf_performA : forall M v Ss,
      well_marked_v M v ->
      well_marked_kf M (KPerformA v Ss)

with well_marked_K : list marker -> kont -> Prop :=
  | wmK_nil   : forall M, well_marked_K M []
  | wmK_cons  : forall M f rest,
      (* When a KHandle frame is at the head, the rest sees the       *)
      (* enclosing-marker set sans this handler's marker.              *)
      well_marked_kf M f ->
      well_marked_K (match f with
                     | KHandle m _ _ _ _ =>
                         List.remove Nat.eq_dec m M
                     | _ => M
                     end) rest ->
      well_marked_K M (f :: rest)
  .

#[export] Hint Constructors well_marked_v well_marked_kf well_marked_K : core.

(* A configuration is well-marked iff its components are, against the *)
(* marker set introduced by the kont, AND every introduced marker is *)
(* < nm (so future fresh markers from CS_Handle don't collide).       *)
Definition markers_below (n : nat) (M : list marker) : Prop :=
  Forall (fun m => m < n) M.

Definition config_wf (c : config) : Prop :=
  match c with
  | C_ev t ρ K nm =>
      Forall (well_marked_v (kont_markers K)) ρ /\
      well_marked_K (kont_markers K) K /\
      NoDup (kont_markers K) /\
      markers_below nm (kont_markers K)
  | C_ret v K nm =>
      well_marked_v (kont_markers K) v /\
      well_marked_K (kont_markers K) K /\
      NoDup (kont_markers K) /\
      markers_below nm (kont_markers K)
  | C_done v =>
      well_marked_v [] v
  end.
