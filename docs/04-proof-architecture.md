# 04 — Proof architecture

## The runtime invariant architecture

Typing alone is not preserved-and-sufficient for the effect layer:
runtime terms mention markers, and the `H_Perform` contraction moves a
capability's operation body across its own delimiter. The multi-step
induction therefore carries `safety_invariants` (`Soundness.v`), three
conjuncts:

1. **`marker_annots_ok`** = `marker_types_safe ∧ marker_annots_closed`
   (`MarkerAnnots.v`): every `(marker, answer-type)` annotation pair
   in the term agrees per marker (Progress's `H_Perform` case needs
   the delimiter's and the capability's `T_R` to coincide), and every
   annotation is a closed type, so substitution preserves the
   agreement.
2. **`ws_rt`** = `well_scoped ∧ rt_closed` (`WellScoped.v`):
   - `well_scoped ms t` — marker *provenance*: each capability's
     marker is in the ambient scope `ms`, and its operation body is
     well-scoped at `scope_below m ms` — the scope *outside* its own
     delimiter, which is exactly where the `H_Perform` reduct lands.
     Monotone along `scope_ext` (scope insertions), which is what
     replaces any freshness bookkeeping.
   - `rt_closed t` — capability operation bodies are term-closed:
     minted at spine positions of a closed program, they stay closed,
     making substitution into them a no-op (the closed-subterm
     identity laws).
3. **Typing** (`preservation` is unconditional subject reduction).

All three hold vacuously on source terms (`has_rt_cap t = false`),
which is how every `source_*` corollary needs only an initial typing.

**The fused engine.** The `ws_rt` preservation laws in `WsRtLaws.v`
are *single* inductions with conjunction motives (`ws_rt_subst_tm`,
`ws_rt_plug_replace`, …), and `Preservation.v` has one merged
`head_step_preserves_ws_rt` feeding `step_preserves_ws_rt`. One law is
necessarily single-sided: `well_scoped_shift_tm` has no `rt_closed`
partner because `rt_closed`'s capability clause pins operation bodies
at term-cutoff 2, which an unconstrained `shift_tm` does not preserve.

## The preservation pipeline

Redex-level lemmas (one per head rule: `tybeta_preserves`,
`matchyes_preserves`, `perform_preserves`, …) feed `preservation`.
The hard one is `perform_preserves`; its proof outline (in a banner
above the lemma) is worth reading before touching anything nearby —
in short: inversions reconcile the perform's and the capability's
effect lookups; a `push_ty_vars` type peel substitutes the β-type
arguments; the reified resumption `λx. handler_m … ((↑P)[x])` is typed
by weakening + `shift_tm_plug` + `plug_typing_replace` with the
perform's *annotation* as its principal type; and
`typing_subst_list_tm_eval_ctx_global` substitutes the two term
arguments.

`Progress.v` proves `progress_open`, generalized over an open marker
scope so the `H_Perform` case can thread the escape disjunct
(`perform_escape`): a term either is a value, steps, or is a
perform-escape `P[perform (cap … m …) …]` with `P` pure for a marker
`m` in the ambient scope. At the closed scope the third disjunct is
absurd, giving `progress`.

## The typing payloads and the context-map abstraction

Six "payload" theorems say typing is preserved by the six context
operations: `typing_InsTy`/`typing_InsLt`/`typing_InsTmAt`
(weakening), `typing_SubstLt`/`typing_SubstTy`/`typing_SubstTm`
(substitution). All apply `typing_ind_forall2` and share a skeleton.

The judgment-transport layer below them is abstracted once in
`CtxMap.v`: `CtxMapSpec` packages, over an abstract parameter type
with binder actions `ext_lt`/`ext_ty`, the homomorphism laws of the
type/lifetime maps, closure of the relation under binders, and the
four variable-case lookup facts. The six generic transports
(`lt_wf_ctx_map` … `sub_ctx_map`) are proved once; each relation
proves a `CtxMapSpec_X` instance, and the concrete transports
(`lt_wf_InsTy`, `sub_SubstTm`, …) are 1–6-line corollaries — all
registered in the `ctxmap` hint db, so proofs discharge them with
`wf_transport`. `sub_ctx_map` takes the `SA_Any` escape premise as a
*hypothesis* rather than a spec field: it is an equality for five maps
but only monotone for `SubstTy`.

**Known limit** (documented future work): a generic `typing_ctx_map`
for the payloads themselves is blocked by (a) `typing_SubstTy` alone
threading a `ctor_fields_closed` invariant, (b) the F<: narrowing
detour in its `T_TyApp`/`T_Lam` cases where the others use plain
equalities, and (c) schema instantiation at iterated binder offsets
requiring `ext`-iteration laws. Estimated as a session of its own;
the transport layer above was designed so this can be attempted
without touching call sites.

## The capstone families

- **Escape** (`Escape.v`): from `step_preserves_ws_rt` +
  `capability_confined` to the source-facing confinement and the
  deep "no runtime forms at escapable types" results.
- **Occurrence** (`Occurrence.v`): a path semantics (`scope_at`)
  mirroring `well_scoped`, giving confinement for *every* syntactic
  occurrence, with the active-position theorem as its empty-scope
  instance.
- **Boundary** (`Boundary.v`, `BoundaryStep.v`): the guarded
  handler-boundary data channels (operation argument in, delimiter
  return out), stated on states and re-stated as labelled transition
  events, plus resumption locality (`A -local-> T_R`). The channel
  matrix banner in `BoundaryStep.v` is the reference for what is
  guarded and what is exempt by design.
- **Guarantees** (`Guarantees.v`): the `source_guarantees` record —
  one theorem application (`source_safety_suite`) delivers the whole
  bundle from `eval_ctx`, `sourceb t = true`, and one typing
  derivation.

## Computation: deciders, evaluator, determinism

- `Decide.v` gives reflected deciders for the static checks; the
  lattice decider is a small cut-elimination story (`lt_le` cut-free ↔
  `lt_sub`, fuel bounded by `ctx_lt_count Γ` — complete for every
  context, no wf needed).
- `Stepf.v` is a certified evaluator: `stepf_sound` (every `Some` is a
  real step) needs no typing; `stepf`'s verdicts mirror
  `progress_open`'s disjuncts. Under the invariants, `None` means
  value (`Guarantees.v`).
- `MarkerRename.v` + `Determinism.v` close the nondeterminism story:
  typing/reduction are equivariant under injective marker renamings,
  marker alpha-equivalence is an equivalence, the fresh-marker choice
  is irrelevant (`handle_choice_irrelevant`), head reduction is a
  partial function, and any two steps from one state agree up to a
  marker bijection; the evaluator is complete modulo that choice.

## Induction principles

- `typing_ind_forall2` (core/Typing.v) — the workhorse: like the
  generated induction principle but hands the list premises back as
  `Forall2` of IHs. Derived from the mutual scheme; its three internal
  bridge uses are inherent (the motive is an arbitrary `P`).
- Mutual schemes `typing_mut_ind`/`typings_mut_ind`/`typing_ops_mut_ind`
  (+ combined), `ty_wf_mutind`/`types_wf_mutind` (SubstTy.v),
  `ty_wf_mut` (TypingInv.v) for wf context conversion.
- `type_list_ind`/`term_list_ind` (ShiftLaws.v) — structural induction
  with list/ops motives for the traversal lemmas; the `go_traverse`
  tactics close their mechanical cases.
