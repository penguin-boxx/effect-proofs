# 03 — Module map

Files in `src/_CoqProject` (dependency) order. The namespace is flat
(`-Q <dir> ""`): import by basename. `Subst.v` and `Safety.v` are pure
re-export shims — the one-import façades of their tiers.

## core/ — the calculus

| File | Role |
|---|---|
| `Syntax.v` | Sorts, terms, `value`, `is_abs`, `has_rt_marker`; creates the opt-in `lang` hint db. |
| `Substitution.v` | The six shift/subst traversals (map-nested; see ch. 02) and the telescoping `subst_list_*` family. |
| `Semantics.v` | `ectx`/`plug`/`shift_ectx_tm`, markers (`markers_in`, `marker_bound`), `ectx_wf` (`EWF_*`), `pure_ectx_m`, `head_step`, `step`, the derived `S_*` rule API (consumers: `Progress.v` and `ExamplesProofs.v` — kept because it documents the calculus), `multi_step`. |
| `Context.v` … `Instantiate.v` | The static-semantics split; see the table in ch. 02. |
| `Typing.v` | Re-exports the seven modules above it; the mutual `typing`/`typings`/`typing_ops` block, generated schemes, `typings_*` native helpers, `typing_ind_forall2`. |

## meta/ — the de Bruijn proof engine

| File | Role |
|---|---|
| `SubstTactics.v` | FIRST in the tier so every module can use it: creates the `subst_go`/`subst_norm`/`ctxmap` hint dbs and defines `wf_transport`, `dbi`, `go_traverse(_norm)`, `sig_congr(2)` + the `sig_extra_unfold` redefinition hook. See ch. 05. |
| `ShiftLaws.v` | σ-calculus laws for the six operations: `*_zero`, `*_fuse`, `*_swap`-style commutations, the `*_ops_eq_map` bridges, closedness predicates (`tm_ty_closed` …), `type_list_ind`/`term_list_ind`, unit-test `Example`s. |
| `CtxMap.v` | The **context-map abstraction**: `CtxMapSpec` (a 13-field record over an abstract parameter type with `ext_lt`/`ext_ty` binder actions) and the six generic judgment transports (`lt_wf_ctx_map` … `sub_ctx_map`, the latter with the SA_Any escape premise as a hypothesis, not a field — it is only monotone for SubstTy). |
| `Weakening.v` | The insertion relations `InsTy`/`InsLt`/`InsTm`/`InsTmAt`, their `CtxMapSpec` instances and corollary transports, `typing_InsTmAt` (+ `typing_weaken_tm_shift`), `sub_weaken_{ty,lt}_shift`. |
| `SubstLt.v` | `SubstLt` + instance/transports; the elim-shift commutation family; **also home to `typing_InsTy`/`typing_InsLt`** — their `T_Match` cases need this file's elim/multi_subst theory, so the dependency order forces them here (header explains). |
| `SubstTy.v` | `SubstTy` + instance/transports; the F<: narrowing relation `NarrowTy` (`NT_*`) with `ty_wf_NT`-style transports and `type_ty_all_narrow_bound` (needed below, which is why narrowing lives here and not only in `Narrowing.v`). |
| `ProgramCtx.v` | `eval_ctx` — the *typing*-context predicate (only ctor/effect bindings; NOT `ectx`!) with its free-variable payoff (`typing_closed`, `typing_fv_bound`), plus `typing_implies_wf` and the `typing_weaken_ty_shift` weakening instances. |
| `CtxClosed.v` | The context-closedness bookkeeping over `eval_ctx`: `ctor_fields_closed`, `ctx_schemas_lt_closed_from`, `ctx_ty/lt_closed_from` with their binder-preservation families, the wf→closed transports, and `typing_tm_ty/lt_closed_from` — the hypothesis packages threaded through `typing_SubstTm`/`typing_SubstTy`. |
| `SubstTm.v` | `SubstTm` + instance/transports, `has_rt_marker_list`, the typed-value capture/escape facts (`typing_value_capture_lt_le_type`, `lt_local_not_escapes`), and the term-substitution payload `typing_SubstTm` with its eval-ctx corollaries. |
| `TypingSubst.v` | `typing_SubstLt` and `typing_SubstTy` — both live here because both T_TyApp cases lean on `type_ty_all_narrow_bound` (SubstTy.v), forcing the payloads below SubstTy (header explains). |
| `Subst.v` | Re-export shim for the tier (everything up to and including `TypingSubst`; `Narrowing`/`Variance` come after it in build order and are imported directly). |
| `Narrowing.v` | The rest of the F<: narrowing theory: `NT_length`, `lt_sub_NT`, `lt_of_ty_ctx` monotonicity under narrowing, the bound-replacement relation `ReplaceTy` (`RT_*`), `sub_NT`/`sub_narrow_ty`. (The inversions this feeds live in `safety/TypingInv.v`.) |
| `Variance.v` | Soundness of the `elim_ty` variance eliminator used by `T_Match` (`elim_ty_list`, `elim_ty_step_ctx`; the eval_ctx-facing `elim_ty_n_sound_pos` lives in `safety/TypingInv.v`). |

## safety/ — the deliverables

| File | Role |
|---|---|
| `Eqb.v` | Boolean equality on lifetimes/types (`lt_eqb`, `ty_eqb`) with the full spec set; shared by the evaluator, deciders, and determinism. |
| `Decide.v` | Certified reflected deciders: `lt_subb` (three-layer: cut-free `lt_le`, fuel-indexed `atom_leb`, fuel = `ctx_lt_count Γ` is complete for *every* context), `nolocb` (the REAL escape premise), `valueb` (backs `solve_value`), `sourceb`. The `lt_le` hint is `#[local]` on purpose. |
| `TypingInv.v` | **The** inversion module: subtyping shape inversions under `eval_ctx` (incl. the full ∀-inversions `sub_lt_all_inv_full`/`sub_ty_all_inv_full`), principal typing inversions for every term former (incl. the λ/Λ inversions, concluding native `typings`/`typing_ops`), `canonical_fun`, `plug_typing_inv`, wf context conversion (`ty_wf_conv`, `ty_wf_fold_bind_tm_inv`). |
| `WellScoped.v` | Runtime marker invariants, part 1: `scope_below`, `scope_ext`, `well_scoped`, `rt_closed`, `ws_rt`, vacuity on source terms, `well_scoped_mono`; the shared closed-type identity laws. |
| `WsRtLaws.v` | Part 2, the fused proof engine: `ws_rt_*` traversal/plug/confinement laws (single inductions with conjunction motives). The one impossible fusion — `well_scoped_shift_tm` — stays single-sided (`rt_closed`'s cap clause pins op-bodies at term-cutoff 2). |
| `MarkerAnnots.v` | Part 3: `marker_annots` collector, `marker_types_safe`, `marker_annots_closed`, `marker_annots_ok`, and their step preservation. |
| `Stepf.v` | The certified executable evaluator `stepf` (+ bounded driver `stepf_run`): verdict types, the `sg_*` tactic family, `stepf_sound` needs no typing hypotheses; smoke tests at the end. |
| `MarkerRename.v` | Marker-renaming equivariance (`typing_rename_markers`, `step_rename_markers`), marker alpha-equivalence (a genuine equivalence), `handle_choice_irrelevant`. |
| `Determinism.v` | `head_step_deterministic` (a real partial function), evaluator completeness and one-step determinism **modulo markers**. |
| `Progress.v` | `progress_open` (generalized over an open marker scope; the `perform_escape` third disjunct) and `progress`. |
| `Frames.v` | Evaluation-context typing recomposition: the `frame_replace` skeleton tactic, per-frame lemmas, `plug_typing_replace`. |
| `Preservation.v` | Redex-level preservation lemmas, the fused `head_step_preserves_ws_rt` / `step_preserves_ws_rt` invariant engine, `preservation`. |
| `Soundness.v` | The `safety_invariants` bundle (marker_annots_ok ∧ ws_rt ∧ typing) and `type_soundness` / `source_type_soundness`. |
| `Escape.v` | Non-escape and capability confinement (`capability_confined`, `source_capability_never_exposed`, `source_noloc_result_no_runtime_forms`, …). |
| `Occurrence.v` | Path-level confinement: every syntactic capability occurrence has its marker in scope. |
| `Boundary.v` / `BoundaryStep.v` | Guarded handler-boundary channels, stated on states and on labelled transition events (+ resumption locality). |
| `Guarantees.v` | The umbrella `source_guarantees` record and `source_safety_suite`; evaluator-facing corollaries. |
| `Safety.v` | Re-export shim for the tier. |

## examples/

| File | Role |
|---|---|
| `Examples.v` | Data/effect declarations, the `CoreNotation` module, every example program and its typing/reduction *statements* (as `Prop` definitions). Naming: `<subject>_example`; camelCase subjects mirror the paper deliberately. |
| `ExamplesTactics.v` | The tier's tactic library (ch. 05) — proofs never define tactics inline. |
| `ExamplesProofs.v` | The typing and end-to-end reduction proofs (including multi-shot and forwarding runs) and the negative escape-check witnesses. |
| `ExamplesRejection.v` | The rejection suite: complete offending terms have *no* typing derivation at their escapable interfaces, each with a positive companion at its confined interface. |
| `ExamplesSafety.v` | The classic capstones witnessed on concrete programs. |

## Dependency-forced placements (do not "fix")

- `typing_InsTy`/`typing_InsLt` in `SubstLt.v`, not `Weakening.v`.
- `typing_SubstLt`/`typing_SubstTy` together in `TypingSubst.v`, below
  `SubstTy.v`.
- `NarrowTy` in `SubstTy.v` (needed for `type_ty_all_narrow_bound`),
  with the rest of narrowing in `Narrowing.v`.
- `elim_ty`'s inner `go_list` and `lt_of_ty_ctx`'s worker stay nested
  fixes (headers explain).

Each carries a header comment stating the constraint; a future
reorganization must re-check those constraints first.
