#!/usr/bin/env python3
# ==================================================================
#
#                SHARED PARSING FOR THE MAINTENANCE SCRIPTS
#
# Single source of truth for (a) what counts as a Theorem/Corollary
# declaration and (b) which files/directories make up the build.
# check_assumptions.py, theorem_index.py and stats.py all import
# from here, so they can never disagree on either question — a
# declaration the index sees is a declaration the axiom gate sees.
#
# ==================================================================
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
COQPROJECT = ROOT / "src" / "_CoqProject"

# A capstone declaration: Theorem or Corollary, leading indentation
# allowed (declarations inside a Section must not silently escape the
# gate), name captured.
DECL_RE = re.compile(r"^[ \t]*(Theorem|Corollary)[ \t]+([A-Za-z0-9_']+)")

# All declaration keywords stats.py counts.  A line whose first token
# (after optional whitespace) is the keyword.
STAT_KEYWORDS = ["Definition", "Fixpoint", "Inductive", "Lemma", "Theorem", "Corollary"]

# Prefixed declaration forms would evade the keyword-at-line-start
# counting; guard_no_prefixed_decls() fails loudly if one ever appears.
PREFIXED_DECL_RE = re.compile(
    r"^[ \t]*(?:#\[[^\]]*\][ \t]*)?(?:Local|Global|Program)[ \t]+"
    r"(?:Definition|Fixpoint|Inductive|Lemma|Theorem|Corollary)[ \t]"
)


def coq_project_dirs():
    """Top-level src/ subdirectories declared via -Q lines, in order."""
    dirs = []
    for line in COQPROJECT.read_text(encoding="utf-8").splitlines():
        m = re.match(r"-Q\s+(\S+)\s", line)
        if m:
            dirs.append(m.group(1))
    return dirs


def coq_project_files():
    """The .v files of the build, as paths relative to src/, in
    declared (dependency) order."""
    files = []
    for line in COQPROJECT.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if line.endswith(".v") and not line.startswith("-"):
            files.append(Path(line))
    return files


def decls_in(path):
    """(kind, name, lineno) for every Theorem/Corollary in the file."""
    out = []
    text = Path(path).read_text(encoding="utf-8", errors="replace")
    for i, line in enumerate(text.split("\n"), start=1):
        m = DECL_RE.match(line)
        if m:
            out.append((m.group(1), m.group(2), i))
    return out


def guard_no_prefixed_decls(path):
    """Return the lines holding Local/Global/Program-prefixed
    declarations (they would evade the keyword counting)."""
    bad = []
    text = Path(path).read_text(encoding="utf-8", errors="replace")
    for i, line in enumerate(text.split("\n"), start=1):
        if PREFIXED_DECL_RE.match(line):
            bad.append((i, line.strip()))
    return bad


def check_or_write(outfile, content, check_mode, make_target):
    """Write `content` to `outfile`, or in check mode diff it against
    the committed version and return False on mismatch."""
    import difflib
    import sys

    path = ROOT / outfile
    if not check_mode:
        path.write_text(content, encoding="utf-8")
        return True
    old = path.read_text(encoding="utf-8") if path.exists() else ""
    if old == content:
        print(f"OK: {outfile} is up to date.")
        return True
    sys.stdout.writelines(difflib.unified_diff(
        old.splitlines(keepends=True), content.splitlines(keepends=True),
        fromfile=f"{outfile} (committed)", tofile=f"{outfile} (regenerated)"))
    print(f"FAIL: {outfile} is stale — run `make {make_target}` and commit the result.")
    return False
