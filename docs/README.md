# Codebase guide

A reader's and maintainer's guide to this development. The top-level
[README](../README.md) says *what* is proved; [ARTIFACT.md](../ARTIFACT.md)
says how to build and verify; this directory explains *how the codebase
works* — its architecture, conventions, automation, and sharp edges.

| Chapter | Contents |
|---|---|
| [01 — Overview](01-overview.md) | What the project proves, the safety story, the verification guarantees, and a suggested reading path. |
| [02 — The calculus](02-calculus.md) | Sorts and syntax, the de Bruijn substitution matrix, operational semantics, and the typing judgment with its escape checks. |
| [03 — Module map](03-module-map.md) | Every file of the build, tier by tier: its role, key exports, and why it sits where it sits. |
| [04 — Proof architecture](04-proof-architecture.md) | The runtime invariant architecture, the preservation/progress pipeline, the capstone families, and the context-map abstraction. |
| [05 — Automation](05-automation.md) | Hint databases and the tactic libraries: what each tactic does and when to reach for it. |
| [06 — Maintenance](06-maintenance.md) | Build targets and gates, recipes for common changes, naming and comment conventions, and known pitfalls. |
| [07 — Limitations and positioning](07-limitations.md) | What is not claimed: lattice coarseness, the ∀-conservatism, no effect typing, no termination claim, undecidable subtyping — and how the design relates to adjacent systems. |

Generated documents ([THEOREMS.md](../THEOREMS.md), [STATS.md](../STATS.md))
are produced by `make theorem-index` / `make stats` and kept fresh by the
`make verify` gate; do not edit them by hand, and treat this guide as the
place for anything a generated index cannot say.
