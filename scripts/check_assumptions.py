#!/usr/bin/env python3
# ==================================================================
#
#            CAPSTONE ASSUMPTION CHECK (self-checking artifact)
#
# Verifies that every capstone theorem of the development is closed
# under the global context — i.e. the proof depends on NO axioms, no
# admitted lemmas, no section hypotheses smuggled into the statement.
#
# Mechanism: generate a scratch .v file (in a throwaway temp dir,
# never inside the repo) that Requires the capstone modules and runs
# `Print Assumptions` on each theorem, compile it against the built
# development, and check the output:
#   - every theorem must print "Closed under the global context"
#     (occurrence count must equal the number of theorems);
#   - any "Axioms:" occurrence is a FAIL.
# Exit status is nonzero on any failure, so CI can gate on it.
#
# Run via `make check-assumptions` (which rebuilds first) — the .vo
# files must be up to date or Require will fail / check stale proofs.
#
# ==================================================================
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# ==================================================================
# CAPSTONE LIST — the single place to extend.
#
# MAINTAINERS: when a new capstone Theorem/Corollary lands in
# safety/Soundness.v, safety/Escape.v, safety/Boundary.v,
# safety/BoundaryStep.v, safety/Occurrence.v, safety/Decide.v,
# safety/Stepf.v, safety/MarkerRename.v, safety/Determinism.v,
# safety/Guarantees.v,
# examples/ExamplesSafety.v, or
# examples/ExamplesRejection.v (or a new capstone file is added), add
# a "<Module>:<theorem>" entry here.  Every Theorem and Corollary in
# those files must be listed — the exhaustiveness self-check below
# fails the run otherwise.
# ==================================================================
CAPSTONES = [
    # safety/Soundness.v
    "Soundness:type_soundness",
    "Soundness:source_type_soundness",
    # safety/Escape.v
    "Escape:local_data_not_escapes",
    "Escape:free_data_result_top_lifetime",
    "Escape:source_free_data_result_top_lifetime",
    "Escape:capability_confined",
    "Escape:capability_never_exposed",
    "Escape:source_capability_never_exposed",
    "Escape:source_noloc_result_no_runtime_forms",
    # safety/Boundary.v
    "Boundary:handler_boundary_noloc",
    "Boundary:source_handler_boundary_noloc",
    "Boundary:source_boundary_value_non_local",
    # safety/BoundaryStep.v
    "BoundaryStep:boundary_step_is_step",
    "BoundaryStep:source_boundary_step_noloc",
    "BoundaryStep:source_boundary_result_out_noloc",
    "BoundaryStep:source_boundary_operation_in_noloc",
    "BoundaryStep:source_boundary_resumption_local",
    # safety/Occurrence.v
    "Occurrence:well_scoped_occurrence_delimited",
    "Occurrence:source_capability_occurrence_delimited",
    "Occurrence:capability_confined_from_occurrence",
    # safety/Decide.v
    "Decide:lt_le_iff",
    "Decide:lt_subb_sound",
    "Decide:lt_subb_complete",
    "Decide:lt_subb_spec",
    "Decide:nolocb_spec",
    "Decide:nolocb_spec_eval_ctx",
    "Decide:nolocb_false_rejects",
    "Decide:nolocb_true_accepts",
    "Decide:valueb_spec",
    "Decide:sourceb_spec",
    # safety/Stepf.v
    "Stepf:stepf_sound",
    "Stepf:stepf_value_none",
    "Stepf:stepf_run_sound",
    # safety/MarkerRename.v
    "MarkerRename:in_markers_in_rename_marker",
    "MarkerRename:typing_rename_markers",
    "MarkerRename:well_scoped_rename_markers",
    "MarkerRename:head_step_rename_markers",
    "MarkerRename:step_rename_markers",
    "MarkerRename:marker_alpha_equiv_refl",
    "MarkerRename:marker_alpha_equiv_sym",
    "MarkerRename:marker_alpha_equiv_trans",
    "MarkerRename:handle_choice_irrelevant",
    "MarkerRename:head_step_deterministic_no_delim",
    # safety/Determinism.v
    "Determinism:head_step_deterministic",
    "Determinism:stepf_complete_modulo_markers",
    "Determinism:step_deterministic_modulo_markers",
    # safety/Guarantees.v (the umbrella capstone)
    "Guarantees:source_safety_suite",
    "Guarantees:safe_stepf_none_is_value",
    "Guarantees:source_stepf_none_is_value",
    # examples/ExamplesSafety.v
    "ExamplesSafety:withState_example_safe",
    "ExamplesSafety:readerExample_safe",
    "ExamplesSafety:withState_example_cap_confined",
    "ExamplesSafety:file_local_confined",
    "ExamplesSafety:readerExample_boundary_noloc",
    # examples/ExamplesRejection.v
    "ExamplesRejection:leak_reader_rejected",
    "ExamplesRejection:leak_reader_rejected_at_free",
    "ExamplesRejection:some_capability_typable_inside",
    "ExamplesRejection:get_local_reader_rejected",
    "ExamplesRejection:local_box_payload_not_coercible",
    "ExamplesRejection:ask_closure_rejected_at_free",
    "ExamplesRejection:ask_closure_typable_local",
    "ExamplesRejection:leak_reader2_rejected",
    "ExamplesRejection:some_some_capability_typable_inside",
    "ExamplesRejection:typed_poly_id",
    "ExamplesRejection:poly_id_conservatively_local",
    "ExamplesRejection:crashEndo_match_rejected_at_data",
    "ExamplesRejection:crashEndo_match_rejected_at_free",
    "ExamplesRejection:crashBox_match_rejected_at_data",
    "ExamplesRejection:crashBox_match_rejected_at_free",
    "ExamplesRejection:typed_trash_val",
    "ExamplesRejection:typed_box_val",
    "ExamplesRejection:crashEndo_match_typable_at_local_any",
    "ExamplesRejection:crashBox_match_typable_at_local_any",
]

# ==================================================================
# EXHAUSTIVENESS SELF-CHECK — the list above must contain EVERY
# Theorem and Corollary declared in the gated files; a stale list
# fails the run before anything is compiled.
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

DECL_RE = re.compile(r"^(Theorem|Corollary) +([A-Za-z0-9_]+)", re.MULTILINE)


def main():
    os.chdir(ROOT)

    capstone_set = set(CAPSTONES)
    missing = False
    for f in GATED_FILES:
        mod = Path(f).stem
        text = Path(f).read_text(encoding="utf-8", errors="replace")
        for m in DECL_RE.finditer(text):
            name = m.group(2)
            if f"{mod}:{name}" not in capstone_set:
                print(f"MISSING from capstone list: {mod}:{name}")
                missing = True
    if missing:
        print("FAIL: capstone list is not exhaustive over the gated files.")
        sys.exit(1)

    with tempfile.TemporaryDirectory() as work:
        scratch = Path(work) / "CheckAssumptions.v"

        # ---- Generate the scratch file ------------------------------
        # Plain `Require` (not Import) + fully qualified names: the
        # namespace is flat (-Q <dir> ""), so <Module>.<theorem> is
        # unambiguous.  Require each capstone module once, in list
        # order.
        seen = []
        for entry in CAPSTONES:
            mod = entry.split(":", 1)[0]
            if mod not in seen:
                seen.append(mod)
        lines = [f"Require {mod}." for mod in seen]
        lines.append("")
        for entry in CAPSTONES:
            mod, thm = entry.split(":", 1)
            lines.append(f"Print Assumptions {mod}.{thm}.")
        scratch.write_text("\n".join(lines) + "\n", encoding="utf-8")

        # ---- Compile it against the built development ---------------
        proc = subprocess.run(
            ["rocq", "c",
             "-Q", "src/core", "",
             "-Q", "src/subst", "",
             "-Q", "src/safety", "",
             "-Q", "src/examples", "",
             str(scratch)],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        out = proc.stdout
        if proc.returncode != 0:
            print(out, end="")
            print("FAIL: scratch file did not compile (is the build up to date?).",
                  file=sys.stderr)
            sys.exit(1)

    # ---- Verify the output ------------------------------------------
    out_lines = out.split("\n")
    n_expected = len(CAPSTONES)
    n_closed = sum(1 for l in out_lines if "Closed under the global context" in l)
    n_axioms = sum(1 for l in out_lines if "Axioms:" in l)

    print(f"Capstone theorems checked: {n_expected}")
    print(f"Closed under the global context: {n_closed}")

    if n_axioms != 0:
        print(out, end="")
        print(f"FAIL: {n_axioms} theorem(s) depend on axioms "
              "(see 'Axioms:' blocks above).", file=sys.stderr)
        sys.exit(1)
    if n_closed != n_expected:
        print(out, end="")
        print(f"FAIL: expected {n_expected} 'Closed under the global context', "
              f"got {n_closed}.", file=sys.stderr)
        sys.exit(1)

    print(f"OK: all {n_expected} capstone theorems are closed under the global context.")


if __name__ == "__main__":
    main()
