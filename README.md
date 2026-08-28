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

This development is the proof-side companion of the **Core∆**
(Core-Delta) calculus — the mechanized metatheory of Core∆ extended
with multi-operation algebraic effect handlers.

## Headline theorems

| Theorem                                                                                           | File                               | Statement (informal)                                                                                                                                                                                                                                                                                                                                                                                                                                                |
| ------------------------------------------------------------------------------------------------- | ---------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `type_soundness`                                                                                  | `src/safety/Soundness.v`           | A state satisfying the runtime invariants never reaches a stuck state.                                                                                                                                                                                                                                                                                                                                                                                              |
| `source_type_soundness`                                                                           | `src/safety/Soundness.v`           | A well-typed **source** program (no runtime marker constructs) never gets stuck — from an `eval_ctx` program context and one typing derivation, no runtime-invariant hypotheses.                                                                                                                                                                                                                                                                                    |
| `source_capability_never_exposed`                                                                 | `src/safety/Escape.v`              | Along any reduction of a well-typed source program, a live capability is never visible outside a delimiter carrying its marker.                                                                                                                                                                                                                                                                                                                                     |
| `source_effect_safety`                                                                            | `src/safety/Escape.v`              | **No unhandled operation**: along any reduction of a well-typed source program, an active `perform` always finds a delimiter carrying its capability's marker in the surrounding context (runtime form: `effect_safety`).                                                                                                                                                                                                                                           |
| `source_free_data_result_top_lifetime`                                                            | `src/safety/Escape.v`              | A value a source program computes at an escapable (`free`) data type carries no top-level `local` lifetime annotation (the deep form is `source_noloc_result_no_runtime_forms`).                                                                                                                                                                                                                                                                                    |
| `source_handler_boundary_noloc`                                                                   | `src/safety/Boundary.v`            | Every value passing a GUARDED handler-boundary data channel — operation argument in, delimiter return out — is typed at the delimiter's declared answer type / the operation's instantiated signature, an escapable (noloc) type; when the delimiter's declared answer type is a data-constructor type, the delivered value is literally a constructor with no top-level `local` (`source_boundary_value_non_local`).                                               |
| `source_boundary_step_noloc` (+ per-channel corollaries)                                          | `src/safety/BoundaryStep.v`        | The same guarantee as labelled transition EVENTS: every executed boundary reduction on a guarded channel carries a value typed at the delimiter's declared answer type / the operation's instantiated signature (both noloc), and the conclusion is the fired event's own decomposition — it links both endpoints of the transition under the firing rule's side conditions; the reified resumption is typed `A -local-> T_R` (`source_boundary_resumption_local`). |
| `source_noloc_result_no_runtime_forms`                                                            | `src/safety/Escape.v`              | A value delivered at an escapable type contains **no capability and no delimiter at any depth** — under lambdas and inside constructor fields.                                                                                                                                                                                                                                                                                                                      |
| `source_capability_occurrence_delimited`                                                          | `src/safety/Occurrence.v`          | EVERY syntactic capability occurrence — at any path, including under binders and inside stored operation bodies — has its marker in scope; the active-position theorem is its empty-scope instance.                                                                                                                                                                                                                                                                 |
| `source_safety_suite`                                                                             | `src/safety/Guarantees.v`          | **The umbrella theorem**: one record bundling type safety, invariant preservation, both confinement forms, capability-free escapable results, guarded-channel safety, and resumption locality — from `eval_ctx`, `sourceb t = true`, and one typing derivation.                                                                                                                                                                                                     |
| `lt_subb_spec` / `nolocb_spec` / `valueb_spec` / `sourceb_spec`                                   | `src/safety/Decide.v`              | Certified reflected deciders for lifetime subtyping, the REAL noloc premise, values, and source terms.                                                                                                                                                                                                                                                                                                                                                              |
| `stepf_sound` / `stepf_run_sound`                                                                 | `src/safety/Stepf.v`               | A certified executable reduction strategy (and bounded driver) implementing the semantics.                                                                                                                                                                                                                                                                                                                                                                          |
| `typing_rename_markers` / `step_rename_markers` / `handle_choice_irrelevant`                      | `src/safety/MarkerRename.v`        | Marker identities are operationally irrelevant: typing/reduction are equivariant under (injective) marker renaming, and the fresh-marker choice yields alpha-equivalent reducts.                                                                                                                                                                                                                                                                                    |
| `head_step_deterministic` / `step_deterministic_modulo_markers` / `stepf_complete_modulo_markers` | `src/safety/Determinism.v`         | Head reduction is a partial function; any two steps from one state agree up to a marker bijection; the certified evaluator is complete for the step relation modulo the fresh-marker choice.                                                                                                                                                                                                                                                                        |
| `leak_reader_rejected_at_free`, `crashEndo_match_rejected_at_data`, …                             | `src/examples/ExamplesRejection.v` | Complete offending TERMS have no typing derivation at their escapable interfaces, each paired with a positive companion at its confined interface (a precision evaluation, including the quantified-type false positive).                                                                                                                                                                                                                                           |

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
make example-matrix      # regenerates EXAMPLES.md
```

[EXAMPLES.md](EXAMPLES.md) is the per-program view of the examples
tier: for each example program, the type it is given, the value it
reduces to, and the gated theorems that speak about it — derived from
the sources, so it cannot drift from what is actually proved.

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

`Examples.v` declares data types (Option, Result, List, Pair, lazy
lists with existential lifetimes, …) and effects (Reader, Exception
with a β-polymorphic `throw`, Id, Optionality, the two-operation
`State`, and `Chan`, whose two operations combine a monomorphic `send`
with a β-polymorphic `poll<a>`). `ExamplesProofs.v` type-checks every
program and runs its reduction end-to-end, most of them through the
certified evaluator (`stepf_run` + `stepf_run_sound`); the calculus has
no fixpoint, so bounded arithmetic comes from the meta-generated family
`sum_fn`. The shared tactic library lives in `ExamplesTactics.v`.

The headline programs and the mechanism each one is there to show:

| Program                    | What it demonstrates                                                                                                                                                           |
| -------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `state_example`            | a two-operation handler (`get`/`put`) driven state-passing run — one clause per operation, selected by `nth_error`                                                             |
| `chan_example`             | multi-operation × β-polymorphism: one `poll<a>` clause, instantiated at `Nat` and at `Unit` in the same run, with both answers in the result pair                              |
| `multishot_example`        | a resumption invoked twice, its two results summed                                                                                                                             |
| `forward_example`          | a `throw` crossing a live, unrelated Reader delimiter                                                                                                                          |
| `delegate_example`         | an operation clause that performs the OUTER handler's operation — two delimiters of the same effect tag, told apart by markers                                                 |
| `withReader`               | a handler polymorphic over `Any'local` data, which flows INWARD only (the comment records why the result bound must stay `Any'free`)                                           |
| `unwrapOr`, `poly_const`   | full F<: at work: a non-`Any` bound reached through `SA_VarCtx`, and DISTINCT contravariant bounds in `SA_TyAll` (`sub_ty_all_bound_contra`) — neither is Kernel-F<: derivable |
| `foldEndo`, `lazyMap_body` | existential lifetimes in constructor schemas and variance-aware elimination (`elim_ty_n`)                                                                                      |
| `leak_state`               | the Listing-1 leak: rejected by typing — and its UNTYPED run really does deliver the capability into an empty context                                                          |

[EXAMPLES.md](EXAMPLES.md) is the generated per-program view of the
whole tier: type, normal form, and the gated theorems about each
program.

`ExamplesSafety.v` witnesses the capstones on concrete programs. The
umbrella `source_safety_suite` is instantiated on `state_example`,
`delegate_example` and `chan_example` (`state_example_guarantees`, …),
and the fields no earlier witness exposed
are unpacked from it verbatim — occurrence confinement at ANY depth,
runtime-form freedom of the result, and the reified resumption's local
closure lifetime — alongside `source_effect_safety`, which is not a
field of the record. Both guarded boundary channels are witnessed on
concrete EXECUTED `boundary_step` events of the State trace (the
`H_Return` collapse and a `get`'s operation-in perform, each with its
event-tied channel typing), and a reachable capability decomposition
(`state_example_cap_reachable`) shows the confinement theorems are not
vacuous. `leak_state_escape_is_real` runs the rejected program to show
what the check is for, and `leak_state_untypable_by_confinement`
re-derives its rejection from the confinement capstone alone.

`ExamplesRejection.v` proves the rejection suite: complete offending
terms — including the Listing-1-shaped `leak_state`, whose handler body
returns the capability itself — have **no typing derivation** at their
escapable interfaces, each paired with a positive companion at its
confined interface (for `leak_state`: the capability is typable INSIDE
the handler, `state_capability_typable_inside`).
`poll_local_beta_rejected` isolates `T_Perform`'s premise on the
supplied β-type-arguments: `poll`'s instantiated signature is `Unit`
whatever `a` is (`poll_local_beta_sig_is_noloc`), so that premise is
the only one that can be at fault.

## License

MIT — see `LICENSE`.
