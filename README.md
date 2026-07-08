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

| Theorem | File | Statement (informal) |
|---|---|---|
| `type_soundness` | `src/safety/Soundness.v` | A state satisfying the runtime invariants never reaches a stuck state. |
| `source_type_soundness` | `src/safety/Soundness.v` | A well-typed **source** program (no runtime marker constructs) never gets stuck — no extra hypotheses. |
| `source_capability_never_exposed` | `src/safety/Escape.v` | Along any reduction of a well-typed source program, a live capability is never visible outside its own delimiter. |
| `source_local_value_does_not_escape` | `src/safety/Escape.v` | A value a source program computes at an escapable (`free`) data type carries no top-level `local` lifetime. |
| `source_handler_boundary_noloc` | `src/safety/Boundary.v` | Along any execution of a well-typed source program, every value crossing a handler boundary — operation argument in, delimiter return out — is typed at an escapable (noloc) type; local values never cross. |

All five are witnessed on concrete programs in
`src/examples/ExamplesSafety.v`.

## Build and verify

Requires Rocq/Coq (developed against Rocq 9.1) with the standard library.

```sh
make                     # builds everything in _CoqProject order
```

To re-check the axiom-freeness of the capstones:

```sh
cd src
echo 'Require Import Soundness Escape Boundary.
Print Assumptions type_soundness.
Print Assumptions source_type_soundness.
Print Assumptions source_capability_never_exposed.
Print Assumptions source_local_value_does_not_escape.
Print Assumptions source_handler_boundary_noloc.' \
| coqtop -Q core "" -Q subst "" -Q safety "" -Q examples ""
```

Each must print `Closed under the global context`.

## The calculus at a glance

### Sorts and syntax (`src/core/Syntax.v`)

Three independent de Bruijn variable sorts — **lifetimes**, **types**,
**terms** — in a strict dependency order (lifetimes occur in types and
terms; types occur in terms; never the reverse).

- **Lifetimes** `Δ ::= l | free | local | Δ₁ + Δ₂`. The subtyping
  lattice puts `free` at the bottom and `local` at the top; `lt_min`
  (written `+`) is the *shorter* of two lifetimes in duration terms,
  which makes it the lattice **join**. "More local" = higher = more
  restricted.
- **Types** `τ ::= α | τ →Δ τ | K Δ τ̄ | ∀l.τ | ∀(α<:B).τ`. `Any@Δ` is
  the encoded top of the data lattice (`type_ctor any_tag Δ []`);
  effect/capability types reuse `type_ctor` at the effect tag.
- **Terms**: λ / Λα / Λl abstractions and applications, data
  constructors with existential lifetime witnesses, single-constructor
  `match`, and the effect layer: `handle`, `perform`, plus two
  **runtime-only** forms — capability values `term_cap` and the
  continuation delimiter `term_handler_m`, both carrying a *marker*
  (a runtime identity for the dynamically nearest delimiter).

Effects are deliberately minimal: **one operation per effect**
(multi-op effects are encoded with a command datatype, see `State` in
the examples), and a `perform` carries its **instantiated result type**
as an annotation. That annotation is what lets the operational
semantics reify the captured continuation as an *ordinary lambda*:

```
handler_m m T_B T_R (P[ perform (cap E m T_R op) S̄ A v ])
  -->h  op[ β̄ := S̄ ][ arg := v,
              k := λ(x:A). handler_m m T_B T_R ((↑P)[x]) ]
```

There is no dedicated "reified resumption" constructor: applying the
resumption is plain β-reduction, which re-installs the delimiter around
a fresh copy of the captured frames — multi-shot resumption for free
(see `multishotExample` in the examples).

### Semantics (`src/core/Semantics.v`)

Layered presentation: local `head_step` rules, evaluation contexts
`ectx`/`plug`, and `step` = head step under a well-formed context, plus
`S_HandleCtx`, which allocates a globally fresh marker when a source
`handle` reduces. The familiar structural rules (`S_Beta`, `S_App1`, …)
are derived lemmas via a single congruence lemma `step_in_ctx`.

### Typing (`src/core/Typing.v`)

The interesting side conditions are all escape checks:

- `T_Lam` bounds the closure lifetime by `capture_lt` — the join of the
  captured variables' type-lifetimes, forced to `local` if the body
  contains a literal runtime capability form (`has_rt_cap`).
- `T_Handle` / `T_HandlerM` demand the body answer type `T_B` be
  lifetime-free (`lt_of_ty_G Γ T_B <: lt_free`): the ordinary return
  path may not smuggle the capability out. The public answer `T_R` may
  differ (`T_B <:: T_R`), which is what lets *deep* resumptions escape
  through operation results without ever exposing the capability.
- `T_Perform` demands the operation argument and the β-type-arguments
  be lifetime-free — a value crossing the handler boundary must not
  carry a `local` capability.
- `T_Match` opens `n_lt` fresh existential lifetimes and eliminates
  them from the branch result type via the variance-aware `elim_ty`
  (soundness in `src/subst/Variance.v`).

## Repository layout

```
src/
  core/      Syntax, Substitution, Semantics, Typing   (the calculus)
  subst/     de Bruijn metatheory                      (the proof engine)
  safety/    the safety theorems                       (the deliverables)
  examples/  fully verified example programs
experiments/ scratch space, not built by make
```

Build order and roles (flat `-Q <dir> ""` namespace, import by
basename; `Subst.v` and `Safety.v` are re-export shims):

| Module | Role |
|---|---|
| `subst/ShiftLaws` | σ-calculus laws for the six shift/subst operations, closedness predicates |
| `subst/Weakening` | context-insertion relations (`InsTm`/`InsTy`/`InsLt`) and typing weakening |
| `subst/SubstLt`, `SubstTy`, `SubstTm` | per-sort substitution relations and typing substitution |
| `subst/ProgramCtx` | the `eval_ctx` predicate (contexts of only ctor/effect bindings) and its closedness corollaries |
| `subst/TypingSubstTy` | `typing_SubstTy` / `typing_SubstLt` — the type- and lifetime-substitution payload |
| `subst/Narrowing` | F<: narrowing, λ/∀ typing inversions, ∀-subtyping inversions |
| `subst/Variance` | soundness of the `elim_ty` variance eliminator used by `T_Match` |
| `safety/TypingInv` | **the** inversion module: subtyping shape inversions, principal typing inversions, canonical forms, `plug_typing_inv` |
| `safety/Markers` | the runtime marker invariants and their traversal/step lemmas |
| `safety/Progress` | progress, generalized over an open marker scope (`perform_escape`) |
| `safety/Inversions` | match/ctor-specific plumbing, free-variable bounds (`typing_closed`) |
| `safety/Frames` | evaluation-context typing recomposition (`plug_typing_replace`) |
| `safety/Preservation` | subject reduction + step-preservation of the runtime invariants |
| `safety/Soundness` | the `safety_invariants` bundle and `type_soundness` |
| `safety/Escape` | the non-escape and capability-confinement theorems |
| `safety/Boundary` | handler-boundary impermeability: values crossing a delimiter are noloc-typed |

## The runtime invariant architecture

Typing alone is not preserved-and-sufficient for the effect layer:
runtime terms mention markers, and the H_Perform contraction moves the
capability's operation body across its own delimiter. The multi-step
induction therefore carries `safety_invariants` (`Soundness.v`), three
conjuncts:

1. **`marker_annots_ok`** = `marker_types_safe ∧ marker_annots_closed`:
   every `(marker, answer-type)` annotation pair in the term agrees per
   marker, and every annotation is a closed type (so substitution
   preserves the agreement).
2. **`ws_rt`** = `well_scoped ∧ rt_closed`:
   - `well_scoped ms t` — marker *provenance*: each capability's marker
     is in the ambient scope `ms`, and its operation body is
     well-scoped at `scope_below m ms` — the scope *outside* its own
     delimiter, which is exactly where the H_Perform reduct lands.
     Progress's requirement (every live capability delimited) is the
     `In m ms` half of the same clause.
   - `rt_closed t` — capability operation bodies are term-closed: they
     are minted at spine positions of a closed program and stay closed,
     which is what makes substituting a value *into* them a no-op.
3. **Typing** (`preservation` is unconditional subject reduction).

Each conjunct has its own step-preservation theorem; all three hold
vacuously on source terms (`has_rt_cap t = false`), which is how the
`source_*` corollaries need only an initial typing.

## Design notes for readers

- **Why a fuel-based `lt_of_ty_ctx`?** The context-aware type-lifetime
  `lt_Γ(τ)` chases type-variable bounds (`lt_Γ(α) = lt_Γ(B)` for
  `α<:B ∈ Γ`), and bound chains are only bounded by `|Γ|` — hence fuel,
  wrapped as `lt_of_ty_G`. The context-free `lt_of_ty` (variables
  contribute `free`) is used only by `T_Ctor` on instantiated field
  types; bridge lemmas relate the two (see the comment at the
  definitions in `Typing.v`).
- **Why three "push binders" operations?** `push_ty_vars` /
  `push_lt_vars` push uniform bounds; `push_match_bound` stores
  per-level *shifted* copies of the scrutinee lifetime so that all `n`
  opened lifetimes share one outer bound — the version that is stable
  under substitution (comment at its definition).
- **Why does `term_cap` exist at all?** `S_HandleCtx` freezes the
  handler's operation body into a first-class capability value tagged
  with the fresh marker; the body then runs with the capability
  substituted for its binder. `term_cap` is a `term_handle` minus its
  body plus its marker.
- **`eval_ctx` vs `ectx`**: `eval_ctx` (ProgramCtx.v) is a *typing*
  context containing only constructor/effect declarations — the
  "program is closed" assumption; `ectx` (Semantics.v) is an
  *evaluation* context. Unrelated notions.

## Examples (`src/examples/`)

`Examples.v` declares data types (Option, Result, List, lazy lists with
existential lifetimes, …) and effects (Reader, State-as-command,
Exception with a β-polymorphic `throw`, Id, Optionality).
`ExamplesProofs.v` type-checks them and runs the reduction sequences
end-to-end (including a **multi-shot** handler that resumes twice and a
**forwarding** example where a `throw` crosses a live unrelated Reader
delimiter). `ExamplesProofs.v` also contains *negative* witnesses: the
escape checks computationally reject programs that would leak a `local`
capability. `ExamplesSafety.v` instantiates the four capstones on these
programs.
