# 07 — Limitations and positioning

What this development does *not* prove or provide, and where its
design sits among adjacent systems. Nothing below is a soundness
caveat — [01 — Overview](01-overview.md) lists the guarantees and they
hold as stated; these are boundaries of scope and precision, the kind
a reviewer would ask about.

## One `local`, not many regions

The confinement lattice has a single non-trivial point. `T_Cap` types
every capability at `type_ctor E_tag lt_local Ts` (`core/Typing.v`) —
all capabilities, and all confined data, are `local` in exactly the
same way. The boundary checks are correspondingly global: `T_Handle`
and `T_HandlerM` demand `lt_of_ty_G Γ T_B <: lt_free` of the body
answer type, and `T_Perform` demands it of the operation argument type
and the β-type-arguments. All three compare against the one bottom
point `lt_free`; none is indexed by a region or a marker. The
consequence: a `local` datum is blocked by **every** handler boundary,
not just its own delimiter's. There is no way to say "local to this
handler but free with respect to that one" — two nested handlers
confine each other's data mutually, even when only one of them is the
reason the datum is confined.

Relative to adjacent systems: the `{free, local}` dichotomy is close
to the first-/second-class value split of Osvald et al. (OOPSLA 2016);
deriving effect safety from lexically scoped capabilities is the
Effekt / System C position (Brachthäuser et al.); and capture sets in
CC<:box (Boruch-Gruszecki et al., TOPLAS 2023) are strictly more
precise than any boolean classification — they name *which*
capabilities a value closes over rather than flagging *that* it does.

What this development adds over a bare two-point split: lifetime
variables and the lattice join `lt_join`, existential lifetimes in
constructor schemas, full F<: alongside the lifetime sort, multi-shot
deep handlers — and the theorem shapes: confinement at every syntactic
occurrence, not only the active position (`safety/Occurrence.v`), and
boundary guarantees per transition event and channel
(`safety/BoundaryStep.v`).

## Polymorphic values cannot cross a boundary

The escape analysis classifies every quantified type as `local`:

```
lt_of_ty (type_lt_all A)   = lt_local
lt_of_ty (type_ty_all B A) = lt_local
```

(`core/LtAnalysis.v`; the context-aware `lt_of_ty_ctx` has the same
two equations). Every ∀-type therefore fails every `<: lt_free` check,
so no polymorphic value can leave a handler through its return path or
travel through a `perform` — regardless of what its body does.

The false positive is mechanized, not hypothesized:
`poly_id_conservatively_local` in `examples/ExamplesRejection.v` shows
the closed, capability-free polymorphic identity (well typed, by
`typed_poly_id`) failing the noloc check — in the file's own words, "a
genuine precision limitation of the analysis, not a soundness issue".

The neighboring crashEndo/crashBox sections show why a naive
relaxation is dangerous: the rejection theorems there are deliberately
*not* `forall T`, because subsumption into `Any@local` is always
derivable — a match over confined data types at `Any@local` even when
every proper constructor interface rejects it, and the data stays
confined only because that one remaining interface is itself `local`
(`crashEndo_match_typable_at_local_any` proves the hatch is real).
Any refinement of the ∀-equations has to re-establish exactly this
boundary. So: this is conservatism (incompleteness), not unsoundness;
a finer analysis of quantified bodies is possible in principle, but
none is implemented.

## No effect typing

Function types carry a closure lifetime, nothing more: `type_fun :
type -> lifetime -> type` (`core/Syntax.v`). There is no effect row on
arrows, no sort of effect variables, and hence no effect polymorphism;
effects are concrete `eff_tag` indices resolved against the context.
Each `handle` delimits exactly one effect — `term_handle` carries a
single `eff_tag` — so handling several effects means nesting handlers.
And `H_Return` is an identity collapse, `term_handler_m m T_B T_R v
-->h v` (`core/Semantics.v`): there is no user return clause to
transform the result on the way out.

The position this implies: effect safety here comes from capability
scoping plus the confinement theorems, not from an effect system. The
type of a function says nothing about which operations it may perform
when applied (beyond the lifetime forced on it by capturing a
capability); what the theorems guarantee is that capabilities and
confined data never outlive their delimiter — effect *accounting* in
the type-and-effect sense is out of scope.

## Termination is a non-claim

The term grammar has no fixpoint form and the type grammar no
recursive types (`core/Syntax.v`); the examples state the workarounds
explicitly — "the calculus has no fixpoint, so `+k` is the k-fold
composition of `succ`", and addition of runtime results is the
bounded-depth family `sum_fn` (`examples/Examples.v`). But normalization is
neither claimed nor refuted: multi-shot resumptions duplicate captured
frames, and whether the calculus is strongly normalizing is simply not
investigated. All soundness theorems are partial-correctness
statements — they quantify over reachable states (`multi_step t u`)
and constrain each one; none asserts that evaluation terminates.
Likewise `safe_stepf_none_is_value` (`safety/Guarantees.v`) is a
statement about stuckness — the evaluator returns `None` only on
values — not about reaching a value.

## Subtyping is undecidable, and there is no typechecker

The subtype relation is honest full F<:: `SA_TyAll` compares bounds
contravariantly, and the comment at the rule owns the consequence —
"full F<:, which is undecidable (Pierce 1992); no complete terminating
checker is claimed" (`core/Subtyping.v`). That the bounds really do
differ is mechanized, not just permitted by the rule:
`sub_ty_all_bound_contra` derives
`∀(a<:Any'free).Unit→Nat <: ∀(a<:Option<Nat>'free).Unit→Nat`, and
`typed_poly_const_at_narrower_bound` is its term-level consequence —
neither is derivable by the Kernel rule. No algorithmic typechecker
for the term language exists. The certified deciders in
`safety/Decide.v` cover the lifetime lattice (`lt_subb`, reflected by
`lt_subb_spec`), the noloc escape check (`nolocb`), value-hood
(`valueb`), and source-hood (`sourceb`) — not typing and not type
subtyping. Example typing derivations are built interactively with the
tactic layer ([05 — Automation](05-automation.md)), not computed.

## The marker invariants are the price of a first-class capability

Two of the three runtime invariants ([04 — Proof
architecture](04-proof-architecture.md)) trace to a single design
decision: a capability is a first-class *value* that carries its own
public answer type `T_R` and its operation bodies (`term_cap E m Ts
T_R op_bodies`, `core/Syntax.v`). Two consequences follow, and each
costs an invariant.

**The answer type is duplicated.** `T_R` appears both on the
capability and on its delimiter (`term_handler_m m T_B T_R`), and
`subst_tm` copies the capability to every occurrence of its binder, so
one delimiter may face many copies. Typing cannot relate them:
`T_Cap` concludes `type_ctor E_tag lt_local Ts` — no marker, no `T_R`
— so two capabilities with different markers are typologically
indistinguishable, and no rule connects a capability to *its*
delimiter. The agreement therefore has to be an invariant outside the
type system: `marker_types_safe`, with `marker_annots_closed` keeping
it stable under substitution. It is spent in exactly one place, the
`H_Perform` case of progress
(`marker_types_ok_handler_perform_annotation_match`), which needs the
delimiter's and the capability's `T_R` to be syntactically the same
type. Nor could `T_R` simply be dropped from the capability while the
operation bodies stay there: `T_Cap` types each body *at* `T_R`, with
the resumption at `ret_β -local-> T_R`.

**The delimiter has to be found again.** Because a capability may sit
arbitrarily far from its delimiter, "the scope outside my own
delimiter" — where an operation body lands when `H_Perform` fires —
must be *reconstructed* from the ambient scope by searching for the
marker. That is `scope_below` (`WellScoped.v`) and the `pure_ectx_m`
induction that goes with it (`well_scoped_pure_cap_confined`).

**The alternative.** Store the operation bodies and `T_R` on the
delimiter and look them up by marker when the operation fires. The
capability shrinks to `(E_tag, m, Ts)` — it cannot vanish, since
`T_Perform` types the receiver at `type_ctor E_tag Δ Ts` and
`H_Perform` matches delimiters by marker — but nothing is duplicated
any more. `marker_annots` / `marker_types_safe` /
`marker_annots_closed` would have nothing to reconcile, and
`scope_below m ms` would collapse to plain `ms`, because the operation
bodies would sit at the very delimiter whose outside scope they need.

That is a real prize, and the cost is not zero: it lands in a worse
layer. `term_handler_m` is also an evaluation-context frame
(`EC_handler_m`), so `plug`, `comp_ectx`, `shift_ectx_tm`,
`pure_ectx_m`, `ectx_wf` and their law families would all traverse
term payloads inside frames, and `rt_closed`'s cutoff-2 closedness
clause would sit on a frame exactly where `shift_ectx_tm` operates —
the interaction that already forces `well_scoped_shift_tm` to stay
single-sided would become systemic rather than a single exception.
`H_Perform` would also stop being a self-contained redex: preservation
would have to take the operation body's typing from the delimiter's
derivation instead of the `T_Cap` sitting in the redex itself.

So this is a trade, not an oversight, and it is recorded here because
the question "why is there a ~1400-line file about annotations
agreeing?" deserves the answer: because the capability is first-class
and the type system *deliberately* forgets markers — which is what
makes source types marker-free and `safety/MarkerRename.v`'s
equivariance true in the first place.

## What is not limited

For contrast, none of the following is weakened by the above. The
development is axiom-free: every capstone prints `Closed under the
global context`, enforced by the derived assumption gate in `make
verify` ([06 — Maintenance](06-maintenance.md)). Soundness for source
programs is unconditional — `source_type_soundness` asks for a typing
derivation and `sourceb t = true`, nothing else. Handlers carry one
clause per declared operation of their effect, not one operation per
effect; resumptions are genuinely multi-shot (`multishot_example` in
the examples tier); and the semantics is deterministic modulo the
fresh-marker choice — not just per step
(`step_deterministic_modulo_markers`) but along whole executions:
alpha-equivalence is a simulation (`step_marker_alpha_simulation`),
normal forms are unique up to a marker bijection
(`multi_step_deterministic_modulo_markers`,
`value_unique_modulo_markers`), and the bounded evaluator reaches
every value the relation can reach
(`stepf_run_complete_modulo_markers`) — `safety/Determinism.v`, with
the renaming theory in `safety/MarkerRename.v`.

Nor is the boundary-flow matrix of `safety/BoundaryStep.v` prose any
more: its exhaustiveness is the accounting theorem
`step_boundary_accounting` — every reduction step is a frame step
(both endpoints decompose through the same context, so the delimiter
spine above the contraction is unchanged), a fresh-delimiter
allocation, or exactly one boundary event, with the event's channel
and crossing value computed by the certified classifier `classify`
(so the three classes are mutually exclusive and the event label is
unique, `boundary_event_unique`). The source-facing form
`source_step_accounting` adds the guarded-channel typing to the event
arm.
