Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Import ListNotations.
Require Import Syntax.
Require Import Substitution.
Require Import Typing.

(* =================================================================== *)
(* CtxMap: one specification for the seven context-map relations.      *)
(*                                                                     *)
(* The subst tier transports every static judgment (lt_wf /           *)
(* lifetimes_wf / ty_wf / types_wf / lt_sub / sub) across seven        *)
(* context maps — InsTy / InsLt / InsTm (Weakening.v), SubstLt,        *)
(* SubstTy, SubstTm and NarrowTy (SubstTy.v) — and the transport       *)
(* families are structurally the same                                  *)
(* induction: only the variable cases (lookup commutation) and the     *)
(* binder bookkeeping differ per relation.  [CtxMapSpec] captures      *)
(* exactly that interface.  A map is abstracted over a parameter type  *)
(* [P] (the insertion cutoff, or the substituted entity paired with    *)
(* its depth); [Fty] / [Flt] are the induced transformations of types  *)
(* and lifetimes at parameter [p], and [ext_lt] / [ext_ty] update the  *)
(* parameter when a judgment walks under a lifetime / type binder      *)
(* (shifts bump the cutoff, substitutions shift their payload).        *)
(*                                                                     *)
(* The spec has three groups of fields:                                *)
(*   - [Flt]/[Fty] are homomorphisms on the non-variable type and      *)
(*     lifetime constructors (with the parameter updated under the     *)
(*     [type_lt_all] / [type_ty_all] binders);                         *)
(*   - [Rel] is closed under pushing a mapped binder on both sides;    *)
(*   - one field per judgment's variable case, stating how a mapped    *)
(*     variable transports through the relation's lookups.             *)
(*                                                                     *)
(* The generic transports are proved ONCE against the spec below.      *)
(* Each relation's own file proves a single [CtxMapSpec] instance      *)
(* (from its ctx_lookup commutation lemmas) and re-derives its         *)
(* transport family as one-line corollaries, keeping the per-relation  *)
(* names and statements that the [ctxmap] hint db registers.           *)
(*                                                                     *)
(* [sub]'s SA_Any case additionally transports the escape analysis     *)
(* [lt_of_ty_G], which commutes as an EQUALITY for five of the maps    *)
(* but only MONOTONELY ([<:], via lt_of_ty_G_SubstTy_le resp.          *)
(* lt_of_ty_G_NT) for SubstTy and NarrowTy.  That fact also depends    *)
(* on the derived wf transports, so it is an extra hypothesis of       *)
(* [sub_ctx_map] rather than a [CtxMapSpec] field.                     *)
(* =================================================================== *)

Section CtxMapping.

  Variable P : Type.
  Variable Fty : P -> type -> type.
  Variable Flt : P -> lifetime -> lifetime.
  Variable ext_lt : P -> P.
  Variable ext_ty : P -> P.
  Variable Rel : P -> ctx -> ctx -> Prop.

  Record CtxMapSpec : Prop := {
    (* [Flt] is a homomorphism on the non-variable lifetimes *)
    cm_flt_free  : forall p, Flt p lt_free = lt_free;
    cm_flt_local : forall p, Flt p lt_local = lt_local;
    cm_flt_join  : forall p l1 l2,
        Flt p (lt_join l1 l2) = lt_join (Flt p l1) (Flt p l2);
    (* [Fty] is a homomorphism on the non-variable types, updating   *)
    (* the parameter under the two type-level binders                *)
    cm_fty_fun   : forall p A l B,
        Fty p (type_fun A l B) = type_fun (Fty p A) (Flt p l) (Fty p B);
    cm_fty_ctor  : forall p K l Ts,
        Fty p (type_ctor K l Ts)
        = type_ctor K (Flt p l) (List.map (Fty p) Ts);
    cm_fty_ltall : forall p A,
        Fty p (type_lt_all A) = type_lt_all (Fty (ext_lt p) A);
    cm_fty_tyall : forall p B A,
        Fty p (type_ty_all B A)
        = type_ty_all (Fty p B) (Fty (ext_ty p) A);
    (* [Rel] is closed under pushing a mapped binder on both sides.   *)
    (* The wf side conditions come for free at every use site (the    *)
    (* generic inductions always have them in hand at binder descent) *)
    (* and are what admit maps like NarrowTy whose push constructors  *)
    (* demand a well-formed binder in both contexts.                  *)
    cm_rel_lt : forall p G G' D, Rel p G G' ->
        lt_wf G D -> lt_wf G' (Flt p D) ->
        Rel (ext_lt p) (bind_lt D :: G) (bind_lt (Flt p D) :: G');
    cm_rel_ty : forall p G G' B, Rel p G G' ->
        ty_wf G B -> ty_wf G' (Fty p B) ->
        Rel (ext_ty p) (bind_ty B :: G) (bind_ty (Fty p B) :: G');
    (* variable cases: lookup commutation, one per judgment *)
    cm_lt_wf_var : forall p G G' x Δ, Rel p G G' ->
        ctx_lookup_lt G x = Some Δ ->
        lt_wf G' (Flt p (lt_var x));
    cm_lt_sub_var : forall p G G' x Δ, Rel p G G' ->
        ctx_lookup_lt G x = Some Δ ->
        lt_wf G' (Flt p Δ) ->
        G' ⊢ₗ Flt p (lt_var x) <: Flt p Δ;
    cm_ty_wf_var : forall p G G' α B, Rel p G G' ->
        ctx_lookup_ty G α = Some B ->
        ty_wf G B ->
        ty_wf G' (Fty p B) ->
        ty_wf G' (Fty p (type_var α));
    cm_sub_var : forall p G G' α B, Rel p G G' ->
        ctx_lookup_ty G α = Some B ->
        ty_wf G B ->
        ty_wf G' (Fty p B) ->
        G' ⊢ Fty p (type_var α) <:: Fty p B;
  }.

  Hypothesis spec : CtxMapSpec.

  (* ---- the generic judgment transports ---------------------------- *)

  Lemma lt_wf_ctx_map : forall G l,
    lt_wf G l -> forall p G', Rel p G G' -> lt_wf G' (Flt p l).
  Proof.
    intros G l Hwf.
    induction Hwf as [Γ x Δ Hlk|Γ|Γ|Γ l1 l2 H1 IH1 H2 IH2]; intros p G' HRel.
    - exact (cm_lt_wf_var spec p Γ G' x Δ HRel Hlk).
    - rewrite (cm_flt_free spec p). constructor.
    - rewrite (cm_flt_local spec p). constructor.
    - rewrite (cm_flt_join spec p l1 l2). constructor.
      + apply (IH1 p G' HRel).
      + apply (IH2 p G' HRel).
  Qed.

  Lemma lifetimes_wf_ctx_map : forall G lts,
    lifetimes_wf G lts -> forall p G', Rel p G G' ->
      lifetimes_wf G' (List.map (Flt p) lts).
  Proof.
    intros G lts Hwf.
    induction Hwf as [Γ|Γ l lts Hl Hlts IH]; intros p G' HRel; cbn [List.map].
    - constructor.
    - constructor.
      + apply (lt_wf_ctx_map Γ l Hl p G' HRel).
      + apply (IH p G' HRel).
  Qed.

  Lemma ty_wf_ctx_map : forall G T,
    ty_wf G T -> forall p G', Rel p G G' -> ty_wf G' (Fty p T)
  with types_wf_ctx_map : forall G Ts,
    types_wf G Ts -> forall p G', Rel p G G' ->
      types_wf G' (List.map (Fty p) Ts).
  Proof.
    - intros G T Hwf.
      induction Hwf as [Γ α B Hlk HwfB IHB
                       |Γ A l B HwfA IHA Hwfl HwfB IHB
                       |Γ K l Ts Hwfl HwfTs
                       |Γ A HwfA IHA
                       |Γ B A HwfB IHB HwfA IHA]; intros p G' HRel.
      + exact (cm_ty_wf_var spec p Γ G' α B HRel Hlk HwfB (IHB p G' HRel)).
      + rewrite (cm_fty_fun spec p A l B). constructor.
        * apply (IHA p G' HRel).
        * apply (lt_wf_ctx_map Γ l Hwfl p G' HRel).
        * apply (IHB p G' HRel).
      + rewrite (cm_fty_ctor spec p K l Ts). constructor.
        * apply (lt_wf_ctx_map Γ l Hwfl p G' HRel).
        * apply (types_wf_ctx_map Γ Ts HwfTs p G' HRel).
      + rewrite (cm_fty_ltall spec p A). constructor.
        assert (Hwfl : lt_wf G' (Flt p lt_local))
          by (rewrite (cm_flt_local spec p); constructor).
        pose proof (IHA (ext_lt p) (bind_lt (Flt p lt_local) :: G')
                      (cm_rel_lt spec p Γ G' lt_local HRel (LWF_Local Γ) Hwfl))
          as HA.
        rewrite (cm_flt_local spec p) in HA. exact HA.
      + rewrite (cm_fty_tyall spec p B A). constructor.
        * apply (IHB p G' HRel).
        * apply (IHA (ext_ty p) (bind_ty (Fty p B) :: G')
                   (cm_rel_ty spec p Γ G' B HRel HwfB (IHB p G' HRel))).
    - intros G Ts Hwf.
      induction Hwf as [Γ|Γ T Ts HwfT HwfTs IHTs]; intros p G' HRel;
        cbn [List.map].
      + constructor.
      + constructor.
        * apply (ty_wf_ctx_map Γ T HwfT p G' HRel).
        * apply (IHTs p G' HRel).
  Qed.

  Lemma lt_sub_ctx_map : forall G l1 l2, G ⊢ₗ l1 <: l2 ->
    forall p G', Rel p G G' -> G' ⊢ₗ Flt p l1 <: Flt p l2.
  Proof.
    intros G l1 l2 H.
    induction H as [Γ l Hwf|Γ l Hwf|Γ x Δ Hlk HwfD|Γ l Hwf
                   |Γ l1 l2 l3 H1 IH1 H2 IH2|Γ l1 l2 l H1 IH1 H2 IH2
                   |Γ l l1 l2 H1 IH1 Hwf2|Γ l l1 l2 H1 IH1 Hwf1];
      intros p G' HRel.
    - rewrite (cm_flt_free spec p). apply LS_Free.
      apply (lt_wf_ctx_map Γ l Hwf p G' HRel).
    - rewrite (cm_flt_local spec p). apply LS_Local.
      apply (lt_wf_ctx_map Γ l Hwf p G' HRel).
    - apply (cm_lt_sub_var spec p Γ G' x Δ HRel Hlk).
      apply (lt_wf_ctx_map Γ Δ HwfD p G' HRel).
    - apply LS_Refl. apply (lt_wf_ctx_map Γ l Hwf p G' HRel).
    - eapply LS_Trans; [apply (IH1 p G' HRel)|apply (IH2 p G' HRel)].
    - rewrite (cm_flt_join spec p l1 l2).
      apply LS_JoinL; [apply (IH1 p G' HRel)|apply (IH2 p G' HRel)].
    - rewrite (cm_flt_join spec p l1 l2). apply LS_JoinR1.
      + apply (IH1 p G' HRel).
      + apply (lt_wf_ctx_map Γ l2 Hwf2 p G' HRel).
    - rewrite (cm_flt_join spec p l1 l2). apply LS_JoinR2.
      + apply (IH1 p G' HRel).
      + apply (lt_wf_ctx_map Γ l1 Hwf1 p G' HRel).
  Qed.

  (* SA_Any's escape premise transports through [lt_of_ty_G]: an       *)
  (* equality for five of the six maps, and only a [<:] for SubstTy.   *)
  (* Taken as a hypothesis (not a spec field) because SubstTy's proof  *)
  (* of it needs the derived wf transports above.                      *)
  Hypothesis Hany : forall p G G' T Δ, Rel p G G' -> ty_wf G T ->
      G' ⊢ₗ Flt p (lt_of_ty_G G T) <: Flt p Δ ->
      G' ⊢ₗ lt_of_ty_G G' (Fty p T) <: Flt p Δ.

  Lemma sub_ctx_map : forall G T1 T2, G ⊢ T1 <:: T2 ->
    forall p G', Rel p G G' -> G' ⊢ Fty p T1 <:: Fty p T2.
  Proof.
    intros G T1 T2 H.
    induction H as [Γ T Hwf|Γ S U T H1 IH1 H2 IH2|Γ α B Hlk HwfB
                   |Γ K l l' Ts Hls HwfTs|Γ T Δ HwfT HwfD Hls
                   |Γ A A' l l' B B' H1 IH1 Hl H2 IH2
                   |Γ A A' H1 IH1|Γ B B' A A' HwfA HwfA' H1 IH1 H2 IH2];
      intros p G' HRel.
    - apply SA_Refl. apply (ty_wf_ctx_map Γ T Hwf p G' HRel).
    - eapply SA_Trans; [apply (IH1 p G' HRel)|apply (IH2 p G' HRel)].
    - apply (cm_sub_var spec p Γ G' α B HRel Hlk HwfB).
      apply (ty_wf_ctx_map Γ B HwfB p G' HRel).
    - rewrite !(cm_fty_ctor spec p K). apply SA_Data.
      + apply (lt_sub_ctx_map Γ l l' Hls p G' HRel).
      + apply (types_wf_ctx_map Γ Ts HwfTs p G' HRel).
    - rewrite (cm_fty_ctor spec p any_tag Δ []). cbn [List.map]. apply SA_Any.
      + apply (ty_wf_ctx_map Γ T HwfT p G' HRel).
      + apply (lt_wf_ctx_map Γ Δ HwfD p G' HRel).
      + apply (Hany p Γ G' T Δ HRel HwfT).
        apply (lt_sub_ctx_map Γ (lt_of_ty_G Γ T) Δ Hls p G' HRel).
    - rewrite !(cm_fty_fun spec p). apply SA_Fun.
      + apply (IH1 p G' HRel).
      + apply (lt_sub_ctx_map Γ l l' Hl p G' HRel).
      + apply (IH2 p G' HRel).
    - rewrite !(cm_fty_ltall spec p). apply SA_LtAll.
      assert (Hwfl : lt_wf G' (Flt p lt_local))
        by (rewrite (cm_flt_local spec p); constructor).
      pose proof (IH1 (ext_lt p) (bind_lt (Flt p lt_local) :: G')
                    (cm_rel_lt spec p Γ G' lt_local HRel (LWF_Local Γ) Hwfl))
        as H'.
      rewrite (cm_flt_local spec p) in H'. exact H'.
    - rewrite !(cm_fty_tyall spec p).
      destruct (sub_wf Γ B' B H1) as [HwfB' HwfB].
      pose proof (ty_wf_ctx_map Γ B HwfB p G' HRel) as HwfFB.
      pose proof (ty_wf_ctx_map Γ B' HwfB' p G' HRel) as HwfFB'.
      apply SA_TyAll.
      + apply (ty_wf_ctx_map (bind_ty B :: Γ) A HwfA (ext_ty p)
                 (bind_ty (Fty p B) :: G')
                 (cm_rel_ty spec p Γ G' B HRel HwfB HwfFB)).
      + apply (ty_wf_ctx_map (bind_ty B' :: Γ) A' HwfA' (ext_ty p)
                 (bind_ty (Fty p B') :: G')
                 (cm_rel_ty spec p Γ G' B' HRel HwfB' HwfFB')).
      + apply (IH1 p G' HRel).
      + apply (IH2 (ext_ty p) (bind_ty (Fty p B') :: G')
                 (cm_rel_ty spec p Γ G' B' HRel HwfB' HwfFB')).
  Qed.

End CtxMapping.
