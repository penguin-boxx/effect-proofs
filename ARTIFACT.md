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

- GNU Make. No other dependencies — the development uses only the
  Rocq standard library.

CI builds in the official Docker image `rocq/rocq-prover:9.1.1`
(Docker Hub publishes no 9.1.0 tag; 9.1.1 is the bugfix-only patch of
the same minor series — see `.github/workflows/ci.yml`).

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
make check-assumptions
```

Rebuilds if needed, then runs `Print Assumptions` on **every capstone
theorem** (all Theorems/Corollaries of
`safety/Soundness.v`, `safety/Escape.v`, `safety/Boundary.v`, and
`examples/ExamplesSafety.v`) and fails unless each one prints
`Closed under the global context` — i.e. the development is axiom-free,
with no admitted proofs and no smuggled hypotheses. The capstone list
lives in one commented block at the top of
`scripts/check_assumptions.sh`; extend it there when a new capstone
lands.

This is the command reviewers should run. CI runs it on every push.

## Generated documentation

```sh
make theorem-index   # regenerates THEOREMS.md
make stats           # regenerates STATS.md (also printed to stdout)
```

- [THEOREMS.md](THEOREMS.md) — every `Theorem` and `Corollary` in
  `src/`, with location and the first line of its statement.
- [STATS.md](STATS.md) — per-directory LOC and declaration counts.

Both are committed and deterministic; regenerate them after changing
the sources and commit the diff. Nothing in them is hand-maintained,
so any figure a paper cites can be re-derived by running the target.

## Continuous integration

`.github/workflows/ci.yml` builds the development and runs
`make check-assumptions` inside the pinned Rocq container on every
push and pull request.

## TODO — maintainer-only steps before archival

These two steps are deliberately **not** done by tooling; only the
maintainer can make these choices:

1. ~~Choose a license.~~ **Done: MIT** (see `LICENSE`).
2.0, or CC-BY for
   text-heavy artifacts) and commit it as `LICENSE`.

2. **Cut the archival release.** Tag the reviewed commit
   (e.g. `git tag -a v1.0 -m "artifact for <paper>"`), push the tag,
   and archive it with a DOI — e.g. enable the repository in
   [Zenodo](https://zenodo.org)'s GitHub integration and create a
   GitHub release from the tag, which triggers DOI minting. Put the
   resulting DOI in the paper's artifact statement and in README.md.
