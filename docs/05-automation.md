# 05 — Automation

## Hint databases

| DB           | Kind       | Created in            | Contents / purpose                                                                                                                                                                                                                                                         |
| ------------ | ---------- | --------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `core`       | historical | per-file              | `Hint Constructors` for the main judgments (`value`, `lt_sub`, `sub`, `typing`+`typings`+`typing_ops`, `ectx_wf`, `head_step`, `step`, …). Pre-dates the named dbs; plain `auto`/`eauto` relies on it. Internal-only hints must be `#[local]` (see `lt_le` in `Decide.v`). |
| `lang`       | opt-in     | `core/Syntax.v`       | The same judgment constructors, collected explicitly (registered in Syntax/Semantics/Typing). New proofs can `eauto with lang` instead of leaning on the historical `core` registrations.                                                                                  |
| `subst_go`   | rewrite    | `meta/SubstTactics.v` | Normalizes op-body traversals to the `fst`/`snd` map form (the `*_ops_eq_map` lemmas) plus the bridges of the still-inline traversals (`rename_marker_go_*`, `marker_annots_go_ops_eq_concat`, `markers_in_*`). Entries register at the defining lemma's `Qed`.            |
| `subst_norm` | rewrite    | `meta/SubstTactics.v` | Sort-level normalization laws (`shift_lt_zero`, `shift_lt_fuse`, `subst_lt_shift_cancel`) for closers that need more than IHs.                                                                                                                                             |
| `ctxmap`     | resolve    | `meta/SubstTactics.v` | Every judgment-transport corollary of the six context-map relations (incl. the mutual-`with` `types_wf_*`); powers `wf_transport`.                                                                                                                                         |

## The meta-tier library (`meta/SubstTactics.v`)

Sits FIRST in the tier so every subst module can use it.

- **`wf_transport`** = `solve [eauto with ctxmap]`. The standard
  discharge of any one-step judgment transport (`lt_wf` through
  `sub_free_list_*` across `InsTy`…`SubstTm`). If it fails, the goal is
  not a one-step transport — spell it out.
- **`go_traverse`** — closes one constructor case of a purely
  structural traversal *equation*: `intros; simpl; autorewrite with
  subst_go; fold every IH; reflexivity`. Applied as
  `apply (term_list_ind …); go_traverse.` Use it when *all* cases are
  mechanical; keep explicit bullets when some cases carry content.
- **`go_traverse_norm`** — same plus `subst_norm` rewrites, for leaf
  cases needing zero/fuse/cancel facts about lower sorts.
- **`dbi` / `dbi_case`** — decide every visible `Nat.eqb/ltb/leb`
  comparison, then close arithmetic with `lia`. *Currently
  forward-facing*: the existing var-case proofs interleave
  branch-dependent rewrites with their splits, so none was
  mechanically convertible; prefer `dbi` in NEW var-case proofs.
- **`sig_congr law` / `sig_congr2 law1 law2`** — close a ctor/eff
  signature congruence (destruct the tuple, unfold the sig operations,
  per-component index normalization + the core law(s)). Files defining
  further sig operations extend the unfolding via the redefinition
  hook: `Ltac sig_extra_unfold ::= unfold …` (see `SubstLt.v`,
  `TypingSubst.v`). The cancel-flavored grid entries resisted the
  generic closers — their proofs stay explicit.

## Safety-tier tactics

- **`frame_replace H Himpl`** (`Frames.v`, local) — the shared skeleton
  of every frame lemma: remember the frame, induct on the typing
  derivation, discharge `T_Sub` by the IH, expose the intro rule.
  Each frame lemma is then just its own closing rule.
- **`sg_step_intro` / `sg_esc_intro` / `sg_frame` / `sg_esc` /
  `sg_head`** (`Stepf.v`, local) — the evaluator-soundness proof
  language: dismiss impossible verdicts, propagate a step/escape
  through a frame, fire a head redex. `stepf_go_sound` reads as a
  case catalogue because of these.
- `spec_absurd`/`lspec_absurd` — vacuous-verdict dispatchers.

## Examples-tier library (`examples/ExamplesTactics.v`)

Multi-step plumbing: `ms_one`, `ms_trans`, congruence steppers
(`ms_ty_app`, `ms_app1/2` — note the marker-freshness side conditions
on `app` frames), and the reduction steppers:

- **`ms_head E tac`** — one reduction step: head redex under context
  `E` fires by `tac`; context wf discharged by `repeat constructor`;
  ends with `cbn`. Three-argument form `ms_head E wf tac` for custom
  wf discharges; **`ms_alloc app tac`** for the `S_HandleCtx`
  allocation step (`tac` discharges marker freshness). These are
  `Tactic Notation` with `uconstr` arguments *on purpose*: plain Ltac
  constr arguments elaborate eagerly and reject the `_` holes the
  context expressions carry.

Typing shapes: `solve_wf`, `solve_var`, `solve_lt`(+`_sub`,`_var`),
`solve_ctor`/`solve_nullary_ctor`/`solve_nat`,
`solve_perform arg` (the 12-premise monomorphic `T_Perform`),
`solve_perform_beta Ss arg` (the same for a β-polymorphic operation —
the extra premise is the `Forall` on the supplied β-type-arguments,
discharged by `solve_forall_noloc`), `open_handle`
(T_Handle minus the interesting premises), `open_lam` (0/1-argument:
T_Lam minus/with the body), `solve_capture` (the closure-lifetime side
condition, trying every closer), `solve_any_sub` (`S <:: Any'Δ`),
`solve_value` (reflection through `valueb_value` + `vm_compute` — use
for any concrete closed value instead of `repeat constructor`),
`solve_nat_match` (the `T_Match` instance for a Nat-typed scrutinee),
and `solve_sum_fn` (types any member/application of the bounded-sum
family `sum_fn` in any concrete context — re-derivation by tactic,
which beats weakening for closed subterms under binders).
The ctor tactics carry `TS_Nil`/`TS_Cons` branches so field-typing
goals build native `typings` directly.

## The `typings` bridges

`typings_Forall2` / `typing_ops_Forall2` convert between the mutual
relations and `Forall2`. After the native-vocabulary pass the only
remaining uses are the three inside `typing_ind_forall2` (inherent:
its motive is an arbitrary `P`). New proofs should use the native
helpers (`typings_length`, `typing_ops_nth_error`, `typings_app_inv`,
`typings_focus_replace`) and the `TS_*`/`TO_*`
constructors; reach for the bridges only at a genuine `Forall2`
boundary.

## Rules of thumb

- A new traversal lemma over terms/types: state it, apply
  `term_list_ind`/`type_list_ind`, try `go_traverse` (`_norm`) first;
  fall back to explicit bullets for the cases that carry content.
- A new judgment-transport obligation: `wf_transport.`
- A new context operation: prove a `CtxMapSpec` instance and take the
  six transports as corollaries (see `CtxMap.v` and any existing
  instance for the pattern).
- Never add a bare global `Hint` to `core` for something internal —
  `#[local]` or a named db.
