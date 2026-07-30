#!/usr/bin/env python3
# ==================================================================
#
#            CAPSTONE ASSUMPTION CHECK (self-checking artifact)
#
# Verifies that every capstone theorem of the development is closed
# under the global context — i.e. the proof depends on NO axioms, no
# admitted lemmas, no section hypotheses smuggled into the statement.
#
# The capstone list is DERIVED, not maintained: every Theorem and
# Corollary declared in a GATED_FILES file is a capstone.  Adding a
# theorem to a gated file gates it automatically; the only manual
# step is adding a NEW capstone file to GATED_FILES.
#
# Mechanism: generate a scratch .v file (in a throwaway temp dir,
# never inside the repo) that Requires the capstone modules and runs
# `Print Assumptions` on each theorem, compile it against the built
# development, and check the output:
#   - every theorem must print "Closed under the global context";
#   - any "Axioms:" occurrence is a FAIL, attributed to the theorem
#     whose Print Assumptions produced it.
# Exit status is nonzero on any failure, so CI can gate on it.
#
# Run via `make check-assumptions` (which rebuilds first) — the .vo
# files must be up to date or Require will fail / check stale proofs.
#
# ==================================================================
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import coqparse

ROOT = coqparse.ROOT

# ==================================================================
# THE GATE POLICY — the single place to extend.
#
# MAINTAINERS: when a new capstone FILE lands, add it here.  Its
# Theorems/Corollaries are then gated automatically (see decls_in).
# ==================================================================
GATED_FILES = [
    "src/safety/Soundness.v",
    "src/safety/Escape.v",
    "src/safety/Boundary.v",
    "src/safety/BoundaryStep.v",
    "src/safety/Occurrence.v",
    "src/safety/Decide.v",
    "src/safety/Stepf.v",
    "src/safety/MarkerRename.v",
    "src/safety/Determinism.v",
    "src/safety/Guarantees.v",
    "src/examples/ExamplesSafety.v",
    "src/examples/ExamplesRejection.v",
]


def main():
    os.chdir(ROOT)

    for f in GATED_FILES:
        if not Path(f).exists():
            print(f"FAIL: gated file {f} does not exist "
                  "(update GATED_FILES in scripts/check_assumptions.py).",
                  file=sys.stderr)
            sys.exit(1)

    # ---- Derive the capstone list from the gated files --------------
    capstones = []  # (module, theorem)
    for f in GATED_FILES:
        mod = Path(f).stem
        for _kind, name, _ln in coqparse.decls_in(f):
            capstones.append((mod, name))

    if not capstones:
        print("FAIL: no capstone declarations found — parsing bug?",
              file=sys.stderr)
        sys.exit(1)

    if shutil.which("rocq") is None:
        print("FAIL: `rocq` not found on PATH.  The artifact targets the "
              "Rocq Prover (see ARTIFACT.md); install it (e.g. via opam) "
              "and re-run.", file=sys.stderr)
        sys.exit(1)

    qflags = []
    for d in coqparse.coq_project_dirs():
        qflags += ["-Q", f"src/{d}", ""]

    with tempfile.TemporaryDirectory() as work:
        scratch = Path(work) / "CheckAssumptions.v"

        # ---- Generate the scratch file ------------------------------
        # Plain `Require` (not Import) + fully qualified names: the
        # namespace is flat (-Q <dir> ""), so <Module>.<theorem> is
        # unambiguous.  Require each capstone module once, in list
        # order.
        seen = []
        for mod, _thm in capstones:
            if mod not in seen:
                seen.append(mod)
        lines = [f"Require {mod}." for mod in seen]
        lines.append("")
        for mod, thm in capstones:
            lines.append(f"Print Assumptions {mod}.{thm}.")
        scratch.write_text("\n".join(lines) + "\n", encoding="utf-8")

        # ---- Compile it against the built development ---------------
        proc = subprocess.run(
            ["rocq", "c", *qflags, str(scratch)],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        out = proc.stdout
        if proc.returncode != 0:
            print(out, end="")
            print("FAIL: scratch file did not compile (is the build up to "
                  "date?  Run `make` first — `make check-assumptions` does).",
                  file=sys.stderr)
            sys.exit(1)

    # ---- Verify the output, attributing verdicts to theorems --------
    # `Print Assumptions` prints, per statement and in order, either a
    # "Closed under the global context" line or an "Axioms:" block.
    verdicts = []
    for line in out.split("\n"):
        if "Closed under the global context" in line:
            verdicts.append("closed")
        elif line.startswith("Axioms:"):
            verdicts.append("axioms")

    print(f"Capstone theorems checked: {len(capstones)} "
          f"(derived from {len(GATED_FILES)} gated files)")

    if len(verdicts) != len(capstones):
        print(out, end="")
        print(f"FAIL: expected {len(capstones)} Print Assumptions verdicts, "
              f"got {len(verdicts)} — output not attributable.",
              file=sys.stderr)
        sys.exit(1)

    offenders = [f"{mod}.{thm}"
                 for (mod, thm), v in zip(capstones, verdicts) if v != "closed"]
    if offenders:
        print(out, end="")
        print("FAIL: the following capstone theorems depend on axioms:",
              file=sys.stderr)
        for name in offenders:
            print(f"  {name}", file=sys.stderr)
        sys.exit(1)

    print(f"OK: all {len(capstones)} capstone theorems are closed under "
          "the global context.")


if __name__ == "__main__":
    main()
