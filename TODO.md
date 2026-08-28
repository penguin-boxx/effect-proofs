# TODO — future directions

Every direction discussed for this development, with status, effort, and
risk. Items move out of this file when they land (git history records
them) or into §7 when a decision closes them. Identifiers in *planned*
items (e.g. `noloc`, `typecheckb`) do not exist yet by definition; this
file is deliberately **not** scanned by `scripts/check_docs_refs.py`.

Effort scale: S = days, M = 1–3 weeks, L = months. Risk = chance the
result is not provable / needs redesign, not engineering tedium.

## 1. Calculus changes awaiting a design decision

These three interact; the agreed sequencing if all are approved is
1.3 → (1.1 + 1.2 jointly) — they touch the same payload/preservation
files, and the syntax slim should come first to avoid double churn.

### 1.1 Relax the polymorphic escapability check (relational `noloc`) — M, low risk

Today `lt_of_ty` classifies every quantified type as `local`
(`core/LtAnalysis.v`), so no polymorphic value can cross a handler
boundary — the mechanized false positive is
`poly_id_conservatively_local` (`examples/ExamplesRejection.v`).
Verified design: an inductive predicate `noloc Γ T` with exactly three
constructors — base = the current premise `Γ ⊢ₗ lt_of_ty_G Γ T <:
lt_free`; descent under `∀(α<:B)` with `bind_ty B`; descent under `∀l`
with `bind_lt lt_local` (pessimistic) — consumed at exactly three
premises: `T_Handle`, `T_Perform`'s instantiated signature,
`T_HandlerM`. `lt_of_ty`/`lt_of_ty_G` themselves stay untouched (keeps
`lt_of_ty_G_mono_sub`, the quantifier rewrite equations, the fuel
machinery, the `CtxMapSpec` commutations). Conservative extension:
every currently-typed program stays typed. Key novel proof: a
`noloc`-typed *value* contains no runtime capability, by induction on
the `noloc` derivation height, instantiating each `∀(α<:B)` **at its
own bound** (keeps Γ fixed) via `typing_SubstTy` +
`sub_ty_all_inv_full`. Staged plan (definition + decider → transport
family → mechanical premise swap → the novel value lemma → boundary
restatement + a positive `poly_id` example replacing the false
positive), ~10–15 days.

**Known-broken alternatives — do not retry** (counterexamples were
checked against the code): (a) making the *function* `lt_of_ty_G`
descend under quantifiers with bound-chasing breaks
`lt_of_ty_G_mono_sub` irreparably, because `SA_TyAll` is contravariant
in bounds (`∀(α<:Any'local).Option'free[α] <::
∀(α<:Any'free).Option'free[α]` would classify `local <:: free`);
(b) descending into constructor fields at the boundary leaks against
`T_Ctor`'s context-free escape premise (a `D'free[∀clean]` value with a
concrete `local` field carrying a capability types today and would
cross a deeper-only check). What stays local even after 1.1: quantified
types nested in ctor arguments/fields, `T_Perform`'s β-arguments, `∀l`
with the variable in a read slot (correct rejection — `T_LtApp` may
instantiate at `local`), `SA_Any` unchanged.

### 1.2 Bounded lifetime quantification `∀(l <: Δ)` — M, medium risk

The principled way to let a handler be polymorphic over data that
*crosses* its boundary: `∀(l<:free). ∀(α<:Any'l). … handle … : α` —
inside, the chase gives `lt(α) = l` and the declared bound gives
`l <: free`; `T_LtApp` then checks the instantiation against the bound.
Half the machinery already exists: `bind_lt` stores a lifetime bound
and `LS_Var` reads it (`core/LtSub.v`; `push_match_bound` already
pushes non-trivial bounds); the hardwired `lt_local` sits only in
`T_LtLam` and in the bound-less syntax of `type_lt_all`/`term_lt_lam`.
Cost: syntax slot, `T_LtLam`/`T_LtApp`, contravariant bound in
`SA_LtAll` (with the same discipline as 1.1: refine only via `noloc`,
never via `lt_of_ty`), bound shifts/substs, inversions, payloads,
`ltbeta` preservation. Nearly useless without 1.1 — do jointly.

### 1.3 Drop `term_ctor`'s result-lifetime slot — M, ~zero risk

`term_ctor K l lts Ts vs` → drop `l`: it is the only typing-derived
field stored in a term (pinned by `T_Ctor`'s equation to the
schema-instance annotation) and it is operationally dead — the
`H_MatchYes`/`H_MatchNo` contractions consume only `lts`/`vs`, and no
analysis reads it. After the change a constructor term is pure
instantiation data, annotation-mismatch terms become unrepresentable
(strengthens 2.3), and erasure (3.4) gets one annotation shorter.
Pure mechanics, but wide: all six substitution traversals + σ-laws,
the `EC_ctor` frame (also carries `l`), ws/rt/marker traversals,
`T_Ctor` + induction + inversions + payloads + `matchyes` preservation,
the example value helpers, and the `free_data_result_top_lifetime`
family restated via the declaration-computed annotation.

Related insight worth a doc note regardless of the decision: the
`bind_ctor` lifetime telescope holds *parameters*, and existentiality
is emergent — a binder absent from the result type is existential
(LazyList's `lh`/`lt`/`ll`), one present in it is a transparent sealing
parameter (`lr`).

## 2. Theorem-strengthening directions (mechanized, self-contained)

### 2.1 Boundary-channel completeness / delimiter accounting — M

Make the five-channel matrix (`safety/BoundaryStep.v` header) a
theorem: every step is (i) a frame step leaving the delimiter spine
unchanged, (ii) a fresh-delimiter allocation (`S_HandleCtx`), or (iii)
exactly one `boundary_step` event. Notably cheaper than it was: the
evaluator's `go_spec` (`safety/Stepf.v`) already classifies every step,
`stepf_complete_modulo_markers` transports the classification to the
relation, and the typing kernels `boundary_return_typing` /
`boundary_operation_typing` (`safety/Boundary.v`) pin the event types.
Main risk: formulating "spine unchanged" under nested contexts. This is
a candidate headline contribution — no adjacent mechanization has an
analog.

### 2.2 Multi-step determinism, unique normal forms, evaluator adequacy — M

All ingredients are proved (`step_rename_markers`,
`marker_alpha_equiv` as a genuine equivalence with injectivity,
`stepf_complete_modulo_markers`, `safe_stepf_none_is_value`). Missing:
"alpha-equivalence is a simulation" plus composition of marker
bijections in the diagram chase. Yields: evaluation is a partial
function up to marker permutation; `t ==>* v₁ ∧ t ==>* v₂ ⇒` the values
are marker-alpha-equivalent; `stepf_run` reaches every value a program
has.

### 2.3 Invariant-necessity counterexamples — S

Hand-built terms violating exactly one `safety_invariants` conjunct and
getting stuck, with stuckness decided computationally (`stepf … = None`
+ `valueb … = false` by `vm_compute`). Turns the "all three conjuncts
are needed" design claim into a mechanized fact. 1.3 first makes the
annotation-mismatch counterexample unrepresentable — pick conjuncts
accordingly.

### 2.4 A specification for the evaluator's stuck verdict — S

`stepf_go`'s `SR_stuck` currently carries no claim. Prove `SR_stuck ⇒
stuck` on closed terms, completing the four-way certified
classification (value / step / escape / stuck), plus the self-test
corollary: on well-typed source states the evaluator can never return
`SR_stuck`.

### 2.5 OCaml extraction — S

`stepf`/`stepf_run` and the deciders (`lt_subb`, `nolocb`, `valueb`,
`sourceb`) are pure computable definitions; extraction is an
`Extraction.v` with directives, a small driver, and a Makefile target.
Only care point: fresh-marker generation at the OCaml boundary.

## 3. Research-scale programs

### 3.1 Certified typechecker — L, low falsity risk, high engineering

The classic missing computational piece: no `typecheck`/`infer`
function and no type-subtyping decider exist. Full completeness is
impossible (full F<: subtyping is undecidable — honestly labeled in
`core/Subtyping.v`), so the honest maximum is a fuel-bounded checker
that is *sound* w.r.t. the declarative system (subtyping as an oracle
or a fueled fragment; `lt_subb`'s reflect pattern in `safety/Decide.v`
is the template), plus `vm_compute` discharge of every positive typing
in `examples/ExamplesProofs.v` — the one part of the examples tier
outside any gate. Makes the rejection suite executable end-to-end with
`stepf`. Subsumes the old "kernelize F<:" alternative.

### 3.2 Strong normalization — L, HIGH risk

The grammar has no fixpoint and no recursive types; SN of source
programs would upgrade `stepf_run` to a fuel-free total evaluator.
Risk is real research risk: logical relations × multi-shot deep
handlers that re-install delimiters. The non-claim is already stated in
`docs/07-limitations.md`; attempt only as its own paper.

### 3.3 Relational confinement — L, HIGH risk

A noninterference or contextual-equivalence statement over the boundary
LTS (naive "local data cannot influence free results" is FALSE —
capabilities influence results by design; the right statement is
independence from the handler's *representation*). The labelled
transitions of `safety/BoundaryStep.v` are the intended substrate.
Separate-paper scale.

### 3.4 Erasure / annotation irrelevance — M–L, medium risk

The semantics is type-passing (`H_Perform` reads the perform's carried
result type to build the resumption lambda). An erased semantics + a
simulation answers "is this implementable without runtime types"; the
possible negative outcome — the annotation is semantically essential —
would itself be a precise characterization. 1.3 shrinks the erasure
surface first.

### 3.5 Per-region confinement granularity — horizon

The two-point lattice confines every `local` datum against *every*
boundary (see `docs/07-limitations.md`). Marker-indexed lifetimes or
capture-set-style precision would distinguish *whose* boundary a datum
is confined to — a CC<:-scale redesign, only as a new calculus/paper.

## 4. Expressiveness playbook for `Any'local` polymorphism

Current layered story (partly landed, partly = items above):

- **Works today — inward flow**: handlers polymorphic over
  `e <: Any'local` typecheck when `e`-data flows only *into* the
  delimiter (environments, operation results via the resumption) —
  `withReader` in `examples/Examples.v` is the landed witness; its
  comment records why the *result* bound must stay `Any'free`.
- **Works today — consumer passing**: to "return" an `Any'local`-bounded
  value, take a consumer `α -{free}-> ρ` in instead (CPS exit); only
  `ρ` crosses. Worth a documented example (see §6).
- **Needs 1.1**: polymorphic *values* (`∀α<:B. …`) crossing boundaries.
- **Needs 1.1 + 1.2**: handlers *returning* `α` itself, restricted to
  escapable instantiations.
- **Needs 3.5**: anything finer than "confined against all boundaries".

## 5. Proof-engineering backlog

- **Traversal-proof migration**: ~68 `term_list_ind` proof sites across
  9 files could ride the `subst_go` rewrite database
  (`subst/SubstTactics.v`); estimated −1.2–1.5k lines. Mechanical but
  broad.
- **Grow `subst_norm` / `go_traverse_norm` adoption**: ~6 manual
  traversal proofs remain; orient all registered laws as reductions —
  `autorewrite` loops are the known failure mode.
- **`InsTmAt` instance**: the one context-map-shaped relation without a
  `CtxMapSpec` instance (symmetry, small).
- **Level-2 payload unification**: the typing payloads
  (`typing_SubstTm`/`typing_SubstLt`/`typing_SubstTy`/weakening) remain
  per-relation; a generic `typing_ctx_map` is deliberately nonexistent —
  the blockers are documented in `docs/04-proof-architecture.md`.
  Research-flavored; revisit only after 1.x settle.

## 6. Examples and documentation

- A worked consumer-passing (CPS exit) example for §4.
- Artifact polish: AEC "kick the tires" section with expected outputs
  and a Docker one-liner; a paper-claim → theorem mapping table in
  `ARTIFACT.md` (the examples half of that map is now generated —
  `EXAMPLES.md`, `make example-matrix`).
- Release steps (license done; tag + DOI) live in `ARTIFACT.md`'s TODO
  section — not duplicated here.

## 7. Deliberately not planned (decisions, with reasons)

- **No Autosubst/Tealeaves/GMeta migration**: the two extra sorts with
  lifetime-in-type/term coupling break their payoff model; the
  hand-rolled lower-triangular matrix + `CtxMapSpec` is the chosen
  design.
- **No full `well_scoped`/`rt_closed` fusion**: impossible —
  `well_scoped_shift_tm` has no `rt_closed` partner (the cap clause
  pins op-bodies at term-cutoff 2); the fused `ws_rt` engine documents
  the exception (`safety/WsRtLaws.v`).
- **No typings-native induction principle**: high churn across the
  large induction proofs for cosmetic benefit.
- **No naive noloc relaxations**: see the counterexamples recorded in
  §1.1.
