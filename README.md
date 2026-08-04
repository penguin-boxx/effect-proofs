# Effects-and-Lifetimes Calculus — Mechanized Safety Proofs

A Rocq (Coq) formalization of a call-by-value calculus with **bounded type
polymorphism (F<:)**, a separate **lifetime** sort forming a two-point
lattice, **algebraic data constructors** with existential lifetime/type
schemas, and **algebraic effect handlers** with multi-shot resumptions.
The development is **axiom-free**: every capstone theorem prints
`Closed under the global context` under `Print Assumptions`.

The safety story is *lifetime-based capability confinement*: effect
capabilities are `local`-annotated values, and the lifetime subtyping
discipline guarantees that neither a capability nor any `local`-confined
datum can escape the scope that delimits it.

## Headline theorems

| Theorem                                                                                           | File                               | Statement (informal)                                                                                                                                                                                                                                                                                                 |
| ------------------------------------------------------------------------------------------------- | ---------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `type_soundness`                                                                                  | `src/safety/Soundness.v`           | A state satisfying the runtime invariants never reaches a stuck state.                                                                                                                                                                                                                                               |
| `source_type_soundness`                                                                           | `src/safety/Soundness.v`           | A well-typed **source** program (no runtime marker constructs) never gets stuck — from an `eval_ctx` program context and one typing derivation, no runtime-invariant hypotheses.                                                                                                                                     |
| `source_capability_never_exposed`                                                                 | `src/safety/Escape.v`              | Along any reduction of a well-typed source program, a live capability is never visible outside a delimiter carrying its marker.                                                                                                                                                                                      |
| `source_effect_safety`                                                                            | `src/safety/Escape.v`              | **No unhandled operation**: along any reduction of a well-typed source program, an active `perform` always finds a delimiter carrying its capability's marker in the surrounding context (runtime form: `effect_safety`).                                                                                            |
| `source_free_data_result_top_lifetime`                                                            | `src/safety/Escape.v`              | A value a source program computes at an escapable (`free`) data type carries no top-level `local` lifetime annotation (the deep form is `source_noloc_result_no_runtime_forms`).                                                                                                                                     |
| `source_handler_boundary_noloc`                                                                   | `src/safety/Boundary.v`            | Every value passing a GUARDED handler-boundary data channel — operation argument in, delimiter return out — is typed at the delimiter's declared answer type / the operation's instantiated signature, an escapable (noloc) type.                                                                                    |
| `source_boundary_step_noloc` (+ per-channel corollaries)                                          | `src/safety/BoundaryStep.v`        | The same guarantee as labelled transition EVENTS: every executed boundary reduction on a guarded channel carries a value typed at the delimiter's declared answer type / the operation's instantiated signature (both noloc); the reified resumption is typed `A -local-> T_R` (`source_boundary_resumption_local`). |
| `source_noloc_result_no_runtime_forms`                                                            | `src/safety/Escape.v`              | A value delivered at an escapable type contains **no capability and no delimiter at any depth** — under lambdas and inside constructor fields.                                                                                                                                                                       |
| `source_capability_occurrence_delimited`                                                          | `src/safety/Occurrence.v`          | EVERY syntactic capability occurrence — at any path, including under binders and inside stored operation bodies — has its marker in scope; the active-position theorem is its empty-scope instance.                                                                                                                  |
| `source_safety_suite`                                                                             | `src/safety/Guarantees.v`          | **The umbrella theorem**: one record bundling type safety, invariant preservation, both confinement forms, capability-free escapable results, guarded-channel safety, and resumption locality — from `eval_ctx`, `sourceb t = true`, and one typing derivation.                                                      |
| `lt_subb_spec` / `nolocb_spec` / `valueb_spec` / `sourceb_spec`                                   | `src/safety/Decide.v`              | Certified reflected deciders for lifetime subtyping, the REAL noloc premise, values, and source terms.                                                                                                                                                                                                               |
| `stepf_sound` / `stepf_run_sound`                                                                 | `src/safety/Stepf.v`               | A certified executable reduction strategy (and bounded driver) implementing the semantics.                                                                                                                                                                                                                           |
| `typing_rename_markers` / `step_rename_markers` / `handle_choice_irrelevant`                      | `src/safety/MarkerRename.v`        | Marker identities are operationally irrelevant: typing/reduction are equivariant under (injective) marker renaming, and the fresh-marker choice yields alpha-equivalent reducts.                                                                                                                                     |
| `head_step_deterministic` / `step_deterministic_modulo_markers` / `stepf_complete_modulo_markers` | `src/safety/Determinism.v`         | Head reduction is a partial function; any two steps from one state agree up to a marker bijection; the certified evaluator is complete for the step relation modulo the fresh-marker choice.                                                                                                                         |
| `leak_reader_rejected_at_free`, `crashEndo_match_rejected_at_data`, …                             | `src/examples/ExamplesRejection.v` | Complete offending TERMS have no typing derivation at their escapable interfaces, each paired with a positive companion at its confined interface (a precision evaluation, including the quantified-type false positive).                                                                                            |

The classic capstones are witnessed on concrete programs in
`src/examples/ExamplesSafety.v`; the rejection suite lives in
`src/examples/ExamplesRejection.v`.

## Build and verify

Requires Rocq/Coq (developed against Rocq 9.1) with the standard library.

```sh
make                     # builds everything in _CoqProject order
make verify              # build + axiom gate + docs-freshness gate
```

`make verify` re-checks the axiom-freeness of ALL capstones (the
capstone list is derived from the gated files, so it cannot go stale)
and that the committed generated docs match the sources:

```sh
make check-assumptions   # every capstone must be closed under the global context
make theorem-index       # regenerates THEOREMS.md
make stats               # regenerates STATS.md
```

See [ARTIFACT.md](ARTIFACT.md) for the full artifact guide,
[docs/](docs/README.md) for the codebase guide (architecture, module
map, automation, maintenance), and [TODO.md](TODO.md) for the future
directions under discussion.

## The calculus at a glance

Three de Bruijn variable sorts — **lifetimes**, **types**, **terms** —
in a strict dependency order. Lifetimes form a two-point subtyping
lattice (`free <: local`, joined by `lt_join`); types are full F<:
plus data constructors with existential lifetime/type schemas; terms
add single-constructor `match` and the effect layer — `handle`,
`perform`, and two runtime-only, marker-carrying forms: capability
values (`term_cap`) and continuation delimiters (`term_handler_m`).
`H_Perform` reifies the captured continuation as an ordinary lambda,
so resuming is plain β-reduction — multi-shot resumption for free.
The interesting typing side conditions are all escape checks
(`T_Lam`'s closure lifetime, `T_Handle`/`T_Perform`'s lifetime-free
boundary types, `T_Match`'s variance-aware lifetime elimination).

Full exposition — syntax, the substitution matrix, the semantics
(including the `H_Perform` rule), and the typing modules with their
escape checks: [docs/02-calculus.md](docs/02-calculus.md).

## Repository layout

```
src/
  core/      syntax, substitution, semantics, typing   (the calculus)
  meta/      de Bruijn metatheory                      (the proof engine)
  safety/    the safety theorems                       (the deliverables)
  examples/  fully verified example programs
experiments/ scratch space, not built by make
```

The authoritative build order is `src/_CoqProject` (flat `-Q <dir> ""`
namespace, import by basename; `Subst.v` and `Safety.v` are re-export
shims). Every file's role, key exports, and the dependency-forced
placements: [docs/03-module-map.md](docs/03-module-map.md).

## The runtime invariant architecture

Typing alone is not preserved-and-sufficient for the effect layer —
the `H_Perform` contraction moves a capability's operation body across
its own delimiter — so the multi-step induction carries the
three-conjunct `safety_invariants` bundle (`Soundness.v`): per-marker
annotation agreement (`marker_annots_ok`), marker provenance plus
closedness of capability operation bodies (`ws_rt` = `well_scoped ∧
rt_closed`), and typing itself (`preservation` is unconditional
subject reduction). All three hold vacuously on source terms
(`has_rt_marker t = false`), which is how the `source_*` corollaries need
only an initial typing. Each conjunct's exact role, the fused
preservation engine, and the capstone families:
[docs/04-proof-architecture.md](docs/04-proof-architecture.md).

## Examples (`src/examples/`)

`Examples.v` declares data types (Option, Result, List, lazy lists with
existential lifetimes, …) and effects (Reader, Exception with a
β-polymorphic `throw`, Id, Optionality, and the two-operation `State` —
`get` at index 0, `put` at index 1 — whose handler exercises one clause
per operation).
`ExamplesProofs.v` type-checks them and runs the reduction sequences
end-to-end (including a **multi-shot** handler that resumes twice and
sums both results, a **forwarding** example where a `throw` crosses a
live unrelated Reader delimiter, and **many-performs** Reader/State
runs whose results are validated by the bounded-addition family
`sum_fn` — the no-fixpoint workaround — via the certified evaluator
`stepf_run`). `ExamplesProofs.v` also contains *negative* witnesses:
the escape checks computationally reject programs that would leak a
`local` capability. The shared tactic library lives in
`ExamplesTactics.v`.
`ExamplesSafety.v` witnesses five of the capstones — eleven theorems
over four concrete programs (including a concrete `boundary_step`
event on the State trace, and soundness/confinement/boundary
witnesses for a **delegating** handler whose ask-clause itself
performs the outer Reader's ask) plus one type-level confinement
fact — and `ExamplesRejection.v` proves the rejection suite: complete
offending terms have **no typing derivation** at their escapable
interfaces, each paired with a positive companion at its confined
interface.

## License

MIT — see `LICENSE`.
