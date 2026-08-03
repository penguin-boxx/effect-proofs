# Artifact guide

How to build, verify, and archive this development. For what the
calculus *is* and what the theorems *say*, see [README.md](README.md).

## Requirements

- **Rocq Prover 9.1.0** (the version this artifact was developed and
  checked with), including its standard library (`Rocq Stdlib`).
  Via opam:

  ```sh
  opam pin add rocq-prover 9.1.0
  ```

- GNU Make.

- Python 3 (any recent version) for the maintenance tooling —
  `make check-assumptions`, `make check-docs`, and the generators in
  `scripts/` are Python and use only its standard library. The
  proofs themselves need nothing beyond the Rocq standard library.

CI builds in the official Docker image `rocq/rocq-prover:9.1.1`
(Docker Hub publishes no 9.1.0 tag; 9.1.1 is the bugfix-only patch of
the same minor series — see `.github/workflows/ci.yml`).

## Scope of the verified development

The verified development is **exactly the files listed in
`src/_CoqProject`** — those are what `make` builds.  The assumption
gate then checks every Theorem/Corollary of the capstone files
(`GATED_FILES` in `scripts/check_assumptions.py`); since every
capstone's proof is checked transitively by `Print Assumptions`, the
axiom-freeness claim covers everything those theorems depend on.  The `experiments/` directory is unbuilt
scratch work (it contains `Admitted`/`Axiom` placeholders by nature)
and is **excluded from archival tarballs** via `.gitattributes`
(`export-ignore`), as is the local `.claude/` directory.  Axiom-freeness
claims refer to the built development, and `git archive` output
contains nothing else.

## Build

```sh
make
```

Builds every file listed in `src/_CoqProject` (dependency order) via a
generated `coq_makefile`. A full build takes a few minutes; rebuilds
are incremental.

Note when scripting the build: gate on make's **exit code**, not on
grepped output — a piped `make | ...` reports the exit code of the
last pipe stage unless `pipefail` is set.

## Verify: the self-check

```sh
make verify
```

**This is the command reviewers should run.** It builds the
development, then runs two gates:

1. **The axiom gate** (`make check-assumptions`): `Print Assumptions`
   on **every capstone theorem** — every Theorem/Corollary of every
   gated file — fails unless each one prints `Closed under the global
   context`, i.e. the development is axiom-free, with no admitted
   proofs and no smuggled hypotheses. The capstone list is **derived,
   not hand-maintained**: the single source of truth is the
   `GATED_FILES` list in `scripts/check_assumptions.py`, and every
   Theorem/Corollary declared in those files is gated automatically —
   a new theorem in a gated file cannot escape the gate.

2. **The docs-freshness gate** (`make check-docs`): the committed
   generated documents (THEOREMS.md, STATS.md) must match what the
   sources regenerate — a stale committed index fails CI. It also
   lints the hand-written guides (`scripts/check_docs_refs.py`):
   files and identifiers referenced by docs/*.md and README.md must
   exist in the sources.

## Generated documentation

```sh
make theorem-index   # regenerates THEOREMS.md
make stats           # regenerates STATS.md (also printed to stdout)
```

- [THEOREMS.md](THEOREMS.md) — every `Theorem` and `Corollary` in
  the build, with location and the first line of its statement.
- [STATS.md](STATS.md) — per-directory LOC and declaration counts.

Both are committed and deterministic; regenerate them after changing
the sources and commit the diff (`make verify` fails otherwise).
Nothing in them is hand-maintained, so any figure a paper cites can
be re-derived by running the target.

## Continuous integration

`.github/workflows/ci.yml` runs `make verify` inside the pinned Rocq
container on pushes to main, pull requests, and a weekly schedule
(the scheduled run skips the build cache so a stale cache cannot
mask a break).

## TODO — maintainer-only steps before archival

These two steps are deliberately **not** done by tooling; only the
maintainer can make these choices:

1. ~~Choose a license.~~ **Done: MIT** (see `LICENSE`).

2. **Cut the archival release.** Tag the reviewed commit
   (e.g. `git tag -a v1.0 -m "artifact for <paper>"`), push the tag,
   and archive it with a DOI — e.g. enable the repository in
   [Zenodo](https://zenodo.org)'s GitHub integration and create a
   GitHub release from the tag, which triggers DOI minting. Put the
   resulting DOI in the paper's artifact statement and in README.md.
