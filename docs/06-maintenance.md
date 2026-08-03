# 06 — Maintenance

## Build and verify

```sh
make            # parallel build of everything in src/_CoqProject
make verify     # build + axiom gate + docs-freshness gate  ← reviewers run this
make clean      # cleanall + generated makefiles
make help       # the full target list
```

The makefile generates via `rocq makefile` (the official
`rocq/rocq-prover` images ship no standalone `coq_makefile`), with a
fallback for older toolchains. When scripting builds, gate on **exit
codes**, never on grepped output — a piped `make | …` reports the last
pipe stage's status unless `pipefail` is set.

### The gates

- **Axiom gate** (`make check-assumptions`, `scripts/check_assumptions.py`):
  runs `Print Assumptions` on every capstone. The capstone list is
  **derived**: every `Theorem`/`Corollary` in every `GATED_FILES`
  entry is gated automatically — the only manual step ever is adding a
  *new capstone file* to `GATED_FILES`. Failures name the offending
  theorems.
- **Docs gate** (`make check-docs`): the committed THEOREMS.md /
  STATS.md must match regeneration. After changing any theorem, run
  `make theorem-index && make stats` and commit the diff. The same
  target then runs `scripts/check_docs_refs.py`: every file and
  every declaration-shaped identifier referenced by docs/*.md and
  README.md must still exist in the sources, so a rename cannot
  silently rot the guides — failures name the doc line and the stale
  reference (fix the doc; the script's small allowlist is only for
  genuinely informal names).
- The generator/gate scripts share `scripts/coqparse.py` — one declaration
  regex (indentation-tolerant, so a `Theorem` inside a `Section`
  cannot evade the gate) and one `_CoqProject` parser. Keep it that
  way: divergent parsing between the gate and the index was a real
  historical bug class.

### CI (`.github/workflows/ci.yml`)

Runs `make verify` in the pinned `rocq/rocq-prover:9.1.1` container on
pushes to main, PRs, and a weekly cron; compiled proofs are cached
keyed on the source hash, and the scheduled run skips the cache so a
poisoned cache cannot mask a break for more than a week. A version
assertion fails fast if the image drifts off the 9.1 series.

## Recipes

**Add a theorem to an existing capstone file** — just add it; the gate
picks it up. Then `make theorem-index && make stats` and commit the
regenerated docs.

**Add a new file** — create it, add it to `src/_CoqProject` at the
right dependency position (flat namespace: the basename must be
unique). If it holds capstones, add its path to `GATED_FILES` in
`scripts/check_assumptions.py`. If it is part of a tier a shim
re-exports (`Subst.v`, `Safety.v`), extend the shim in `_CoqProject`
order.

**Add a context operation** (a new `InsX`/`SubstX`-style relation) —
define the relation and its lookup lemmas, prove a `CtxMapSpec`
instance (pattern: any existing `CtxMapSpec_*`), take the judgment
transports as corollaries, register them in `ctxmap`. The typing
payload is still per-relation (see the documented Level-2 blockers in
`docs/04`).

**Change a typing rule** — expect to touch: the rule (`Typing.v`),
`typing_ind_forall2`'s derivation if the rule has list premises, the
principal inversion in `TypingInv.v`, the six payloads in `subst/`,
and `Preservation.v`'s redex lemma for any head rule involving it.
Build after each file; the compiler is the map.

## Conventions

**Naming.**
- `map_X` = pointwise `List.map` wrapper; `subst_list_X` = telescoping
  block substitution; `X_list`/`X_ops` = a traversal's list/op-body
  positions; `*_ops_eq_map` = primed-to-`fst/snd` normalization
  bridges. `*_go_*` lemma names survive only as bridges over the
  safety-tier traversals that still keep an inline list fix
  (`rename_marker`, `marker_annots`, `ty_eqb`) and for the named
  evaluator worker `stepf_go`; the two calculus-layer inline-fix
  exceptions (`elim_ty`'s `go_list`, `lt_of_ty_ctx`'s fuel worker —
  see 02-calculus.md) have no `_go_` lemmas.
- Constructor prefixes: `LWF_`/`TWF_` (wf), `LS_` (lifetime sub, with
  `LS_Join*` for the lattice), `SA_` (type sub), `T_` (typing), `TS_`/
  `TO_` (typings/typing_ops), `EWF_` (ectx wf), `EC_` (ectx frames),
  `H_` (head steps), `S_` (step + the derived rule API), `NT_`/`RT_`
  (narrowing/replacement), `MS_` (multi-step).
- Theorems: `source_*` = source-facing corollary needing only typing;
  `*_ctx_map` = generic over `CtxMapSpec`; suffix `_spec` = a
  `reflect` statement; `_sound`/`_complete` for the decider/evaluator
  directions.
- Examples: `<subject>_example`, with `typed_*`/`red_*` companions;
  camelCase subjects mirror the paper (deliberate).

**Comment style.** Boxed banners with aligned closing `*)` (66–70
columns, matching each file); module headers state purpose and any
placement constraint. Comments state *current* facts and constraints
the code cannot express — never development history ("was", "now
proven", phase numbers). Terminal deliverables with no internal
consumers carry a `PUBLIC API — terminal` marker so dead-code sweeps
skip them.

## Known pitfalls

- **No mutual `Fixpoint` between `term` and `list term`** — the guard
  checker rejects it (nested inductive). Recurse through
  `List.map`/`existsb`/`fold_right` in the constructor branch instead;
  the guard sees through those.
- **`well_scoped_shift_tm` has no `rt_closed` partner** and cannot:
  `rt_closed`'s cap clause pins op-bodies at term-cutoff 2. The fused
  `ws_rt` engine documents this exception; don't try to complete it.
- **`elim_ty`'s `go_list` and `lt_of_ty_ctx`'s worker are nested fixes
  on purpose** (variance parameterization / fuel-structure double
  recursion); support proofs induct on exactly those shapes.
- **Tactic-notation arguments**: context expressions with `_` holes
  must be `uconstr` parameters (`ms_head`/`ms_alloc`); plain Ltac
  constr arguments elaborate eagerly and fail. Ltac hygiene renames
  auto-generated hypothesis names inside `Ltac` bodies — match
  hypotheses by *shape*, not by `IHfoo` names (see `frame_replace`).
- **Iff lemmas inside `repeat first […]` loops can fire in both
  directions and loop** — prefer constructor branches (`TS_Cons`) or
  one-directional lemmas in tactic alternation lists.
- **Scripted span surgery** (if you ever batch-edit proofs): bound
  every edit to a single lemma; remember collapsed proofs keep `Qed.`
  on the same line (a `\nQed.` search overshoots into the next lemma);
  afterwards run a declaration-name diff (ALL kinds, including
  `Inductive`/`Record`/`Scheme`) against `git HEAD` for the touched
  files. This class of mistake has silently swallowed lemmas before.
- **`eval_ctx` vs `ectx`** — unrelated notions with similar names: a
  *typing* context of only ctor/effect declarations vs an *evaluation*
  context. `ProgramCtx.v`'s header explains.
- The two escape-lifetime families (`lt_of_ty` vs `lt_of_ty_G`) are
  both load-bearing; unification loses expressivity (design note in
  `LtAnalysis.v`).

## experiments/

Unbuilt scratch, excluded from archives (`.gitattributes
export-ignore`); provenance in `experiments/README.md`. Only
`Sugar.v` imports live `src/` modules and is kept in sync
opportunistically — it is not gated.
