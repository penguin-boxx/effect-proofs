# 02 — The calculus

## Sorts and syntax (`core/Syntax.v`)

Three independent de Bruijn variable sorts in a strict dependency
order: **lifetimes** occur in types and terms, **types** occur in
terms, never the reverse.

- **Lifetimes** `Δ ::= l | free | local | Δ₁ + Δ₂`. The subtyping
  lattice puts `free` at the bottom and `local` at the top; `lt_join`
  (notation `+l` in the examples) is the lattice **join** — duration-wise
  the *shorter* of the two lifetimes. "More local" = higher = more
  restricted.
- **Types** `τ ::= α | τ →Δ τ | K Δ τ̄ | ∀l.τ | ∀(α<:B).τ`. `Any@Δ` is
  the encoded top of the data lattice (`type_ctor any_tag Δ []`);
  effect/capability types reuse `type_ctor` at the effect tag.
- **Terms**: λ/Λα/Λl abstractions and applications, data constructors
  with existential lifetime witnesses, single-constructor `match`, and
  the effect layer: `handle`, `perform`, plus two **runtime-only**
  forms — capability values `term_cap` and continuation delimiters
  `term_handler_m`, both carrying a *marker* (a runtime identity for
  the dynamically nearest delimiter).

Purely syntactic helpers live beside the syntax: `is_abs` (the
prenex-Λ value restriction consulted by `T_TyLam`/`T_LtLam`) and
`has_rt_marker` (does a literal runtime form occur — the "is this a
source term" test, decided by `sourceb` in `Decide.v`).

Effect declarations carry a **list of operations** (`bind_eff E n_α
[(n_β, σ, ρ); …]`, a context binding in `core/Context.v`) — one
`(β-arity, signature, result)` triple per operation, identified by
its list index; a handler supplies one clause per operation,
`perform` selects by declaration index, and each `perform` carries
its instantiated result type as an annotation — that annotation is
what lets the semantics reify the captured continuation as an
ordinary lambda.

## Substitution (`core/Substitution.v`)

Six shift/subst pairs — the operation matrix is lower-triangular
because of the sort order:

| sort \ carrier | lifetime              | type                              | term                              |
| -------------- | --------------------- | --------------------------------- | --------------------------------- |
| lifetime       | `shift_lt`/`subst_lt` | `shift_lt_in_ty`/`subst_lt_in_ty` | `shift_lt_in_tm`/`subst_lt_in_tm` |
| type           | —                     | `shift_ty`/`subst_ty`             | `shift_ty_in_tm`/`subst_ty_in_tm` |
| term           | —                     | —                                 | `shift_tm`/`subst_tm`             |

Substituting under a binder of a lower sort shifts the replacement in
that sort (capture avoidance).

**Traversal style.** Every traversal recurses through its list
positions by *nesting `List.map` / `existsb` / `concat ∘ map` /
`fold_right`* directly in the constructor branch (Coq's guard checker
accepts recursive calls through these combinators). There are **no
inline `fix go` copies** in these functions, and consequently no
"go-bridge" lemmas for the list cases; the op-body positions (pairs
`(n_β, body)`) use a primed-pattern lambda, normalized to the
`fst`/`snd` form by the `*_ops_eq_map` lemmas registered in the
`subst_go` rewrite database. Two documented exceptions keep a nested
fix for real reasons: `elim_ty`'s `go_list` (parameterized by
variance; the elim support proofs induct on exactly that shape) and
`lt_of_ty_ctx`'s worker (a genuine fuel/structure double recursion).
Do not "modernize" those two.

The `subst_list_*` family (`subst_list_tm`, `subst_list_lt_in_tm`,
`subst_list_ty_in_tm`, `subst_list_ty`, `subst_list_lt_in_ty`)
telescopes a whole binder block at once — note the naming rule:
`subst_list_X` = telescoping block substitution; `map_shift_ty`-style
`map_*` names = plain pointwise `List.map` wrappers.

## Semantics (`core/Semantics.v`)

Layered: local `head_step` rules (`-->h`), evaluation contexts
`ectx`/`plug` with well-formedness `ectx_wf` (constructors `EWF_*` —
call-by-value discipline: everything left of the hole is a value), and
`step` (`==>`) = head step under a well-formed context plus
`S_HandleCtx`, which allocates a globally fresh marker when a source
`handle` reduces (freshness via `marker_bound`/`markers_in`; there is
deliberately *no* freshness side condition anywhere else — see the
marker-renaming theory in `safety/MarkerRename.v`).

`S_HandleCtx` is also where `term_cap` originates: it freezes the
handler's operation body into a first-class capability value tagged
with the fresh marker, and runs the handle's body with that
capability substituted for its binder — a `term_cap` is a
`term_handle` minus its body plus its marker.

The handler-elimination rule reifies the continuation as a lambda:

```
handler_m m T_B T_R (P[ perform (cap E m T̄ T_R ops) i S̄ A v ])
  -->h  opᵢ[ β̄ := S̄ ][ arg := v,
              k := λ(x:A). handler_m m T_B T_R ((↑P)[x]) ]
      where  nth_error ops i = Some (n_β, opᵢ)
```

`H_Perform` requires the captured context `P` to be both marker-pure
(`pure_ectx_m`) and value-disciplined (`ectx_wf`) — capture may not
skip a pending redex; this is what makes one-step reduction
deterministic modulo the fresh-marker choice. Applying the resumption
is plain β-reduction, which re-installs the delimiter around a fresh
copy of the captured frames — multi-shot resumption for free (see
`multishot_example` in the examples tier).

The familiar structural rules (`S_Beta`, `S_App1`, …) are *derived*
lemmas via the single congruence lemma `step_in_ctx`; `multi_step`
(`==>>` in the examples) closes `step` reflexively-transitively.

## Typing (`core/Typing.v` and the modules it re-exports)

The static semantics is split into dependency-ordered modules, all
re-exported by `Typing.v` so `Require Import Typing` provides the full
story:

| Module        | Contents                                                                                                                                                                                                                                               |
| ------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------ |
| `Context`     | `binding`/`ctx`, the five `ctx_lookup_*` (bounds re-interpreted at the use site by shifting past binders), signature shifting (`shift_{ty,lt}_{ctor,eff}_sig`)                                                                                         |
| `Wf`          | the well-formedness judgments `lt_wf`, `lifetimes_wf`, `ty_wf`/`types_wf` (constructors `LWF_*`, `TWF_*`)                                                                                                                                              |
| `LtSub`       | lifetime subtyping `Γ ⊢ₗ l₁ <: l₂` (`LS_*`; `LS_Join*` are the lattice-join rules)                                                                                                                                                                     |
| `LtAnalysis`  | the escape analyses: context-free `lt_of_ty`/`lt_of_ty_list`, fuel-based context-aware `lt_of_ty_ctx`/`lt_of_ty_G`, `no_local_lt`, `free_tm_vars`, `capture_lt`                                                                                        |
| `Elim`        | variance (`var_pos/neg/inv`, `flip_variance`) and the fresh-lifetime eliminator `elim_lt`/`elim_ty`/`elim_ty_n` (option-valued; `None` = invariant position)                                                                                           |
| `Subtyping`   | type subtyping `Γ ⊢ S <:: T` (`SA_*`; full F<: — `SA_TyAll` has contravariant bounds; `SA_Any` is the data-lattice top with the `lt_of_ty_G … <: Δ` escape premise)                                                                                    |
| `Instantiate` | schema instantiation (`inst_ty_vars`, `multi_subst_lt(_in_ty)`, `inst_lt_vars`, `inst_ctor_type(_open)`, `inst_op_ty_args`, `inst_op_all_args`) and context pushing (`push_lt_vars`, `push_ty_vars`, `push_match_bound`), `any_at_free`, `op_body_ctx` |
| `Typing`      | the typing relation itself                                                                                                                                                                                                                             |

**The typing relation is mutually inductive**: `typing` (`Γ ⊢ₜ t : T`)
with `typings` (`TS_Nil`/`TS_Cons` — a list of terms against a list of
types, used by `T_Ctor`) and `typing_ops` (`TO_Nil`/`TO_Cons` — the
handler/capability operation clauses against the effect signature,
shared by `T_Cap` and `T_Handle`). Round-trip bridges
`typings_Forall2`/`typing_ops_Forall2` connect to `Forall2` where the
generic induction principle needs it; native helpers
(`typings_length`, `typing_ops_nth_error`, `typings_app_inv`,
`typings_focus_replace`) cover the recurring list
manipulations. The Forall2-aware induction principle
`typing_ind_forall2` (derived from the generated mutual scheme) is
what every typing payload in `meta/` applies.

**The interesting side conditions are all escape checks:**

- `T_Lam` bounds the closure lifetime by `capture_lt` — the join of
  the captured variables' type-lifetimes, forced to `local` if the
  body contains a literal runtime capability form.
- `T_Handle`/`T_HandlerM` demand the body answer type `T_B` be
  lifetime-free (`lt_of_ty_G Γ T_B <: lt_free`); the public answer
  `T_R` may differ (`T_B <:: T_R`), which is what lets deep
  resumptions escape through operation results without exposing the
  capability.
- `T_Perform` demands the operation argument and β-type-arguments be
  lifetime-free — values crossing the handler boundary must not carry
  a `local` capability.
- `T_Match` opens `n_lt` fresh existential lifetimes (context pushed
  by `push_match_bound`, which stores per-level *shifted* copies of
  the scrutinee lifetime so all `n_lt` opened lifetimes share one
  outer bound — the form stable under substitution, unlike the
  uniform bounds `push_lt_vars`/`push_ty_vars` push) and eliminates
  them from the branch result via the variance-aware `elim_ty_n`.

**Two escape-lifetime families** coexist by design: the context-free
`lt_of_ty` (variables contribute `free`) used by `T_Ctor` on
instantiated field types, and the context-aware fuel-based
`lt_of_ty_G` (chases variable bounds, fuel `|Γ|`) used everywhere
else; bridge lemmas relate them (comment at their definitions in
`LtAnalysis.v`). Attempts to unify them lose expressivity — don't.
