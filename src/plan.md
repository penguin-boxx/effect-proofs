## Plan: Axiom-free whole-calculus safety (drop no_local@Lam, add no_local@Handle, well-scopedness, effectful progress)

Goal: make `Safety.type_safety` axiom-free AND cover the FULL calculus incl. handlers, via three typing-rule groups plus supporting metatheory/runtime invariants. Decisions locked: (D1) effect safety via ADDITIVE runtime marker invariant (typing judgment unchanged); (D2) I edit Typing/SubstitutionTheory/Safety and retire or update Counterexample*.v ONLY — user repairs Examples.v/ExamplesProofs.v (they build AFTER Safety, so my files verify independently).

### Current status
- Phase 5 wiring is implemented: `eval_ctx` admits effects, handle allocation uses fresh whole-term markers, `progress`/`type_safety` are marker-aware, and the core build passes.
- `marker_ok_plug_cap_pure_in` is now proven, so a bare capability under a pure context contradicts `marker_ok []` without an axiom.
- `Semantics.no_step_value` and `Safety.multi_step_value_inv` are proven support lemmas for the next marker-preservation replacement.
- Remaining assumptions on `Safety.type_safety` are `handler_perform_preservation`, `marker_ok_preservation`, `canonical_ctor`, `canonical_cap`, plus older substitution/context assumptions from `SubstitutionTheory.v`.
- Directly proving the current `marker_ok_preservation` statement is impossible: raw `H_Return` can step `term_handler_m m (term_cap E m Ts op_body)` to the bare cap, breaking `marker_ok []`. Replace it with a typed/source-aware preservation invariant, or with a progress-specific invariant that permits returned values and then proves they cannot continue stepping.
- Directly proving `typing_implies_wf` is blocked by missing effect-signature well-formedness: `T_Perform` returns `ret_inst`, but `ctx_lookup_eff` does not currently guarantee the looked-up `sig`/`ret` schemas are well formed after instantiation.

### Rule changes (all in Typing.v)
- R1 T_Lam (L694): REMOVE `no_local_ty B = true`.
- R2 T_Handle (L816): ADD `no_local_ty T_R = true` (prevents local-typed caps escaping via H_Return).
- R3 Well-scopedness: define `lt_wf Γ l`, `ty_wf Γ T` (every lt_var x ⇒ ctx_lookup_lt Γ x<>None; every type_var α ⇒ ctx_lookup_ty Γ α<>None; structural elsewhere; binders extend Γ for type_lt_all/type_ty_all). Add schema-wf helpers for ctor/effect declarations as needed (`ctor_sig_wf`, `eff_sig_wf`) so looked-up schemas cannot manufacture free ty/lt variables. GUARD all subtyping/lifetime rules that can fabricate ill-scoped endpoints: LS_Free/LS_Local/LS_Refl, LS_Var's bound, SA_Refl, SA_VarCtx's bound, SA_Data's type arguments, SA_Any's input/target lifetime, and type-all bounds. ADD wf premises to syntax/annotation typing rules: T_Var looked-up type (or derive from ctx/schema wf), T_Lam A, T_TyLam bound, T_TyApp S, T_LtApp l, T_Ctor Ts/lts, T_Match Ts, T_Cap/T_Handle Ts plus T_R/op-schema instantiations as needed, T_Perform Ss, and T_Resume A.

### PHASE 0 — Rule edits (Typing.v). Foundational; breaks downstream.
- Apply R1,R2,R3. Compile Typing.v alone (expect green). Downstream (SubstTheory/Safety/Examples/Counterexamples) now broken — repaired in later phases / by user.

### PHASE 1 — Well-scopedness metatheory (Typing.v + SubstitutionTheory.v). Blocks 2,3,4,5.
- Basic: lt_wf/ty_wf weakening across each binder kind; preserved by InsTm/InsTy/InsLt and SubstTm/SubstTy/SubstLt. Include schema-wf preservation for ctx_lookup_ctor/ctx_lookup_eff if schema helpers are introduced.
- Pull forward weakening capstones `typing_InsTy` and `typing_InsLt` here (not Phase 3 only). `typing_SubstTm` needs them in the SubstTm_ty/SubstTm_lt target cases to type shifted substituted values under type/lifetime binders.
- `lt_sub_implies_wf`: `Γ⊢ₗ l1<:l2 -> lt_wf Γ l1 /\ lt_wf Γ l2`. `sub_implies_wf`: both sides ty_wf.
- `typing_implies_wf`: `Γ⊢ₜ t:T -> ty_wf Γ T` (workhorse — recovers wf anywhere; requires the R3 guards on T_Var/subtyping/context-derived endpoints).
- Closedness bridge: `eval_ctx Γ -> ty_wf Γ T -> shift_ty 1 c T = T /\ shift_lt_in_ty 1 c T = T`, using eval_ctx_no_ty and a new eval_ctx_no_lt. If eval_ctx is later extended with bind_eff, these two still hold because bind_eff binds no ty/lt variables; effect schemas themselves are handled by schema-wf/R3, not by lookup absence.
- Plus annotation-closedness of values: `eval_ctx-ish Γ -> Γ⊢ₜ v:T -> shift_ty_in_tm 1 c v=v /\ shift_lt_in_tm 1 c v=v` (uses new ty_wf-on-annotation premises in T_Lam/T_TyLam/T_Cap/T_Perform/T_Resume...).
- REPAIR existing subtyping inversion infra broken by guarded rules: `sub_fun_inv`/`sub_ctor_inv`/`sub_lt_all_inv`/`sub_ty_all_inv` (Safety L205+), and any constructor of reflexive subtyping in SubstTheory.

### PHASE 2 — Discharge subst_tm_lemma (SubstitutionTheory.v). Dep: P1 (+ existing typing_InsTmAt).
- Build `SubstTm_target` first: if `SubstTm v n Γ Γ'` and `ctx_lookup_tm Γ n = Some T`, then `Γ'⊢ₜ v:T`. Its SubstTm_tm case uses `typing_InsTmAt`; its SubstTm_ty/SubstTm_lt cases use the Phase-1 `typing_InsTy`/`typing_InsLt` capstones.
- Build `typing_SubstTm : Γ⊢ₜ t:T -> SubstTm v n Γ Γ' -> Γ'⊢ₜ subst_tm n v t:T`; reuse SubstTm lookup lemmas + all three weakening capstones. 16 typing cases incl T_Ctor/T_Match/T_Cap/T_Handle/T_Resume binder stacks.
- Replace `Axiom subst_tm_lemma` with lemma: derive closedness premises (free_tm_vars + ty/lt shift-invariances from P1) from eval_ctx typing. Retire CounterexampleTmSubst.v (delete or rewrite as a positive regression once the theorem exists).

### PHASE 3 — Discharge subst_ty/lt_in_tm + subst_list_lt_in_tm (SubstitutionTheory.v). Dep: P1.
- Reuse Phase-1 `typing_InsTy`/`typing_InsLt` (16 cases each; needs missing commutation lemmas `inst_op_alpha_shift_ty/_lt`, `inst_op_arg_shift_ty/_lt` for T_Cap/T_Handle/T_Perform).
- Build `typing_SubstTy`, `typing_SubstLt`; derive `subst_ty_in_tm_lemma`, `subst_lt_in_tm_lemma`. With R1 (no_local dropped), T_Lam case no longer re-establishes no_local ⇒ provable. Retire CounterexampleTySubst.v and CounterexampleLtSubst.v after the theorems exist.
- Add/derive the parallel type-list term substitution lemma needed by handler preservation (`subst_list_ty_in_tm` over the β arguments), not just the existing nil helper.
- `subst_list_lt_in_tm_lemma` via subst_lt + chain_bounded + subst_list_lt_in_ty_each (reuse inst_ctor_type_subst_eq already proven).

### PHASE 4 — Fix ctor_lts_chain_bounded (Typing.v + SubstitutionTheory.v). Dep: P1. Parallel w/ P2,P3.
- Root cause (CounterexampleCtorChain.v): `lt_of_ty (type_fun _ l _)=l` ignores domain/codomain ⇒ contravariant locals invisible. FIX (decision F2): widen lt_of_ty + lt_of_ty_list to fold domain+codomain lifetimes, OR add ctor-schema wf premise. Widening ripples into SA_Any(lt_of_ty_G), T_Ctor bound, capture_lt, escape theorems — re-verify those.
- Discharge ctor_lts_chain_bounded. Retire CounterexampleCtorChain.v (delete or rewrite as a positive regression once the theorem exists).

### PHASE 5 — Whole-calculus safety (Safety.v + SubstitutionTheory.v). Dep: P2,P3,P4 (+R2). The novel core.
- Extend eval_ctx with `ec_eff` (allow bind_eff). eval_ctx_no_tm/no_ty/no_lt STILL hold; REMOVE eval_ctx_no_eff (now false) and everything that used it vacuously. Ensure effect declarations are well-scoped via R3/schema-wf, since lookup absence no longer hides ill-scoped effect schemas.
- Define runtime invariant `marker_ok : list marker -> term -> Prop`: handler_m m t ⇒ marker_ok (m::ms) t; term_cap E m.. ⇒ In m ms (+recurse op_body under m::ms); term_resume m b ⇒ self-provides m (marker_ok (m::ms) b); perform/others structural. Source terms ⇒ marker_ok [].
- Key lemma A (cap-free): `Γ⊢ₜ v:T -> value v -> no_local_ty T=true -> (no term_cap sub-term)` — induction on value typing; any cap forces local via lt_of_ty/capture_lt propagation.
- Key lemma B: marker_ok preservation must be typed/source-aware, not raw. H_Return can expose a runtime value syntactically, so the preservation theorem should either use typing plus `no_local_ty T_R`/cap-free regularity to recover `marker_ok []`, or expose a `marker_ok-or-value` progress invariant and combine it with the proven `no_step_value` / `multi_step_value_inv` facts.
- Re-prove `progress` (full): T_Handle⇒H_Handle; T_HandlerM⇒H_Return/recurse/H_Perform; T_Perform under handler⇒H_Perform; bare top-level perform excluded by marker_ok (cap marker not active).
- Re-prove `preservation` (full): H_Handle(subst_tm_lemma), H_Perform(parallel β type-list substitution + subst_list_tm_lemma + marker bookkeeping), H_Return(lemma A keeps type), H_Resume(subst_tm_lemma) — all target substitution lemmas must be theorems by this point.
- Restate `type_safety` for full calculus: `eval_ctx Γ -> marker_ok [] t -> Γ⊢ₜ t:T -> multi_step t t' -> ~stuck t'`.

### PHASE 6 — Final verification.
- `Print Assumptions Safety.type_safety` ⇒ no axioms.
- Per-file: `cd src && coqc -R . "" Typing.v && coqc -R . "" SubstitutionTheory.v && coqc -R . "" Safety.v`.
- Examples/ExamplesProofs = user-owned; full `make` green is the JOINT closing milestone.

**Relevant files**
- `src/Typing.v` — R1 (L694 T_Lam), R2 (L816 T_Handle), R3 sites include ctx lookups/schema helpers near L40-L140, lt_sub L162 (LS_Free/Local/Var/Refl), sub L477 (SA_Refl/VarCtx/Data/Any/all bounds), T_Var/T_Sub/T_Lam/T_TyLam/T_TyApp/T_LtApp/T_Ctor/T_Match/T_Cap/T_Handle/T_Perform/T_Resume around L680-L854; new lt_wf/ty_wf; lt_of_ty L224 for P4.
- `src/SubstitutionTheory.v` — axioms at tail (subst_tm_lemma L4147, subst_ty/lt L4158/L4165, subst_list_lt L4171); reuse typing_InsTmAt, InsTy/InsLt/SubstTm/SubstTy/SubstLt relations+lookup lemmas, inst_ctor_type_subst_eq, value-shift lemmas; add wf metatheory + capstones here.
- `src/Safety.v` — progress L612, preservation L2224, type_safety L2389, eval_ctx use, sub_*_inv L205+, escape theorems L2400+, no_typed_perform_cap_under_eval_ctx L187, canonical_* L220+.
- `src/Semantics.v` — handler reduction read-only ref: H_Handle/H_Return/H_Perform/H_Resume (L139-166), ectx/plug/pure_ectx_m (L24-74), shift_ectx_tm.
- `src/Counterexample*.v` — retire the four as their axioms become theorems (delete if they are only historical, or rewrite as positive regression tests). They are not listed in `_CoqProject`, so they do not block the core build unless explicitly compiled.

**Verification**
1. Per-phase: compile only the file(s) touched, filtering deprecation noise: `cd src && coqc -R . "" FILE.v 2>&1 | grep -vE "deprecated|Stdlib"`.
2. After P0: Typing.v compiles standalone.
3. After P2/P3/P4: SubstitutionTheory.v compiles; `Print Assumptions` shows the targeted axiom(s) gone.
4. After P5: Safety.v compiles; progress/preservation/type_safety reference no axioms; typed marker preservation + cap-free lemma proven.
5. Closing: `Print Assumptions Safety.type_safety` axiom-free; coordinate with user on Examples/ExamplesProofs repair for full `make`.

**Decisions**
- D1 (locked): additive runtime marker invariant; typing judgment unchanged.
- D2 (locked): edit Typing/SubstitutionTheory/Safety/Counterexample only; user repairs Examples.v/ExamplesProofs.v. Enumerate their breakage (apply T_Lam 3rd subgoal; apply SA_Refl/LS_Refl/LS_Free/LS_Local now need wf; T_TyApp/T_LtApp/T_Ctor/T_Match need wf args) so user can fix.
- Scratch-first for big capstones; integrate when green. No commits/push. No markdown docs.

**Further Considerations**
1. F1 Well-scopedness strictness: guard reflexivity rules (LS_Refl/SA_Refl) [chosen — else unbound vars still leak] vs only var-introducers. Guarding maximizes example breakage but is required for genuine well-scopedness.
2. F2 ctor-chain fix: (A) widen lt_of_ty to include fn domain/codomain [more faithful, ripples into SA_Any/escape thms] vs (B) add ctor-schema wf premise [localized, weaker statement]. Recommend A.
3. F3 RISK (highest): marker_ok resume case. Resumptions are first-class values that re-install their delimiter (H_Resume ⇒ handler_m m). Invariant must model resume as self-providing m; getting H_Perform (continuation capture) + H_Resume preservation right is the novel crux. Fallback if intractable: have handler_m/cap/resume reference a marker binding in Γ (folds into typing — deviates from D1).
4. F4 Marker freshness: H_Handle (Semantics L139) admits ANY marker, not fresh. If marker_ok needs distinctness, may require a fresh-marker side condition or supply; confirm whether structural confinement suffices.