# 01 — Overview

## What this is

A Rocq (Coq) formalization of a call-by-value calculus combining:

- **bounded type polymorphism** (full F<:, with contravariant bounds in
  `SA_TyAll`),
- a separate **lifetime sort** forming a two-point subtyping lattice
  (`free <: local`, joined by `lt_join`),
- **algebraic data constructors** with existential lifetime/type schemas
  and a variance-aware `match` eliminator,
- **algebraic effect handlers** with multi-shot resumptions, realized
  at runtime by capability values (`term_cap`) and continuation
  delimiters (`term_handler_m`) carrying *markers*.

The safety story is **lifetime-based capability confinement**: effect
capabilities are `local`-annotated values, and the lifetime subtyping
discipline guarantees that neither a capability nor any
`local`-confined datum can escape the scope that delimits it.

## The guarantees

Every capstone theorem prints `Closed under the global context` under
`Print Assumptions` — the development is **axiom-free**, with no
admitted proofs and no smuggled section hypotheses. This is enforced,
not promised: `make verify` runs an assumption gate whose capstone
list is *derived* from the gated files (it cannot go stale), plus a
freshness gate for the generated documents. See
[06 — Maintenance](06-maintenance.md) for the mechanics.

The headline theorems (full table in the top-level README):

- `type_soundness` / `source_type_soundness` — progress + preservation;
  for **source** programs (no runtime marker constructs) with no extra
  hypotheses at all.
- `source_capability_never_exposed`, `source_capability_occurrence_delimited`
  — a live capability is never visible outside its delimiter, at the
  active position and at *every* syntactic occurrence respectively.
- `source_noloc_result_no_runtime_forms`, `source_free_data_result_top_lifetime`
  — values delivered at escapable types carry no capability, no
  delimiter, no `local` annotation, at any depth.
- `source_handler_boundary_noloc`, `source_boundary_step_noloc` —
  every value crossing a guarded handler-boundary channel is
  escapably typed, stated on states and on transition events.
- `source_safety_suite` — the umbrella record bundling all of the
  above from one typing derivation.
- Certified *computation*: reflected deciders for the static checks
  (`Decide.v`), a certified evaluator (`Stepf.v`), and determinism of
  the semantics modulo the fresh-marker choice (`Determinism.v`,
  `MarkerRename.v`).

## Shape of the development

```
src/
  core/      the calculus: syntax, substitution, semantics, and the
             static semantics modules re-exported by Typing.v
  meta/      de Bruijn metatheory: shift/subst laws, the context-map
             abstraction, weakening/substitution typing payloads
  safety/    the deliverables: invariants, preservation, progress,
             soundness, confinement, deciders, evaluator, determinism
  examples/  fully verified example programs, positive and negative
experiments/ unbuilt scratch (see experiments/README.md)
scripts/     the self-checking artifact tooling
docs/        this guide
```

Roughly 29k lines across 47 files; a flat `-Q <dir> ""` namespace, so
files import each other by basename.

## Suggested reading path

1. `core/Syntax.v` — the term language fits on two screens; read the
   comments on the runtime-only forms.
2. `core/Semantics.v` — head steps, evaluation contexts, and the two
   step rules (`S_step`, `S_HandleCtx`); the `H_Perform` rule is the
   heart of the effect layer.
3. `core/Typing.v` — the typing relation; skim the re-exported modules
   as needed ([02 — The calculus](02-calculus.md) maps them).
4. `safety/WellScoped.v` then `safety/Soundness.v` — what the
   multi-step induction actually carries and how it concludes.
5. `safety/Guarantees.v` — the umbrella statement, then outward into
   Escape/Boundary/Occurrence as interest dictates.
6. `examples/Examples.v` — concrete programs exercising everything.
