#!/usr/bin/env python3
# ==================================================================
#
#                     EXAMPLE MATRIX GENERATOR
#
# Regenerates EXAMPLES.md: one row per example PROGRAM, with the
# type it is given, the value it reduces to, and the theorems that
# speak about it.  The point is exposure, not new content — the
# guarantees are already proved; this table is what lets a reader
# see, per program, which of them were instantiated on it.
#
# Everything is derived syntactically from the sources, so the table
# cannot drift:
#   - programs      = `Definition <x> : term :=` in the examples tier
#   - type          = the type of `typed_<...>`, found by its `|-t`
#                     subject (NOT by name matching)
#   - reduces to    = the right-hand side of `red_<...>`'s `==>>`
#   - witnesses     = every Theorem/Corollary in ExamplesSafety.v /
#                     ExamplesRejection.v whose STATEMENT names the
#                     program
# A program with none of the three is a helper value and is skipped.
#
# Integrity check, run in both modes: every typed_*/red_* statement
# that lands in the table must be discharged by a matching
# `<name>_proof` Theorem in ExamplesProofs.v — a statement nobody
# proves would otherwise read as a result.
#
# Run via `make example-matrix`.  EXAMPLES.md is committed;
# `--check` (used by `make check-docs` / `make verify`) fails with a
# diff when the committed file is stale.
#
# ==================================================================
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import coqparse

ROOT = coqparse.ROOT
OUTFILE = "EXAMPLES.md"

EX = "src/examples"
PROGRAM_FILES = [f"{EX}/Examples.v", f"{EX}/ExamplesRejection.v"]
WITNESS_FILES = [f"{EX}/ExamplesSafety.v", f"{EX}/ExamplesRejection.v"]
PROOF_FILE = f"{EX}/ExamplesProofs.v"

TERM_DEF_RE = re.compile(r"^Definition\s+([A-Za-z0-9_']+)\s*:\s*term\s*:=")
PROP_DEF_RE = re.compile(r"^Definition\s+((?:typed|red)_[A-Za-z0-9_']+)\s*:\s*Prop\s*:=")
SUBJ_RE = re.compile(r"⊢ₜ\s*([A-Za-z0-9_']+)")
REDUCES_RE = re.compile(r"^(.*?)==>>(.*)$", re.S)
FIRST_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")


def strip_comments(text):
    """Blank out (* ... *) comments, keeping every newline so line
    numbers survive."""
    out = []
    depth = 0
    i = 0
    while i < len(text):
        if text.startswith("(*", i):
            depth += 1
            out.append("  ")
            i += 2
        elif text.startswith("*)", i) and depth:
            depth -= 1
            out.append("  ")
            i += 2
        else:
            ch = text[i]
            out.append(ch if (depth == 0 or ch == "\n") else " ")
            i += 1
    return "".join(out)


def blocks(path):
    """(head_line, lineno, body) for every top-level Definition /
    Theorem / Corollary in the file: the body runs to the first line
    ending in '.' at paren depth 0 (for a Theorem that is its
    statement, since `Proof.` starts a new block)."""
    lines = strip_comments(
        path.read_text(encoding="utf-8", errors="replace")).split("\n")
    i = 0
    while i < len(lines):
        line = lines[i]
        if re.match(r"(Definition|Theorem|Corollary)\s", line):
            start = i
            depth = 0
            body = []
            while i < len(lines):
                depth += lines[i].count("(") - lines[i].count(")")
                body.append(lines[i])
                if depth <= 0 and lines[i].rstrip().endswith("."):
                    break
                i += 1
            yield lines[start], start + 1, "\n".join(body)
        i += 1


def squeeze(s):
    return re.sub(r"\s+", " ", s).strip().rstrip(".").strip()


def cell(s):
    """Markdown table cell: escape the pipe, wrap in a padded double
    backtick span so the calculus's own backticks (`Lf, `Ll) survive."""
    s = squeeze(s).replace("|", "\\|")
    return f"`` {s} ``" if s else "—"


def type_of(body):
    """The type in `Γ |-t subject : TYPE`: everything after the first
    ':' at paren depth 0 following the subject."""
    m = SUBJ_RE.search(body)
    if not m:
        return None, None
    rest = body[m.end():]
    depth = 0
    for k, ch in enumerate(rest):
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        elif ch == ":" and depth == 0:
            return m.group(1), rest[k + 1:]
    return m.group(1), None


def main():
    check_mode = "--check" in sys.argv[1:]

    programs = []          # (name, relpath, lineno) in source order
    seen = set()
    for rel in PROGRAM_FILES:
        for head, ln, _ in blocks(ROOT / rel):
            m = TERM_DEF_RE.match(head)
            if m and m.group(1) not in seen:
                seen.add(m.group(1))
                programs.append((m.group(1), rel, ln))

    typed = {}   # program -> (stmt_name, type_text)
    reduces = {} # program -> (stmt_name, rhs_text)
    for rel in PROGRAM_FILES:
        for head, _, body in blocks(ROOT / rel):
            m = PROP_DEF_RE.match(head)
            if not m:
                # A positive typing stated directly as a Theorem — the
                # rejection file states its companions that way.  Skip
                # anything negated or quantified: those are rejections.
                d = coqparse.DECL_RE.match(head)
                if d and "~" not in body and "forall" not in body:
                    subj, ty = type_of(body.split(":", 1)[1] if ":" in body else "")
                    if subj in seen and ty and subj not in typed:
                        # proved in place: no separate _proof to demand
                        typed[subj] = (None, ty)
                continue
            stmt = m.group(1)
            rhs_body = body.split(":=", 1)[1] if ":=" in body else ""
            if stmt.startswith("typed_"):
                subj, ty = type_of(rhs_body)
                if subj in seen and ty and subj not in typed:
                    typed[subj] = (stmt, ty)
            else:
                red = REDUCES_RE.match(rhs_body)
                if not red:
                    continue
                lhs = FIRST_IDENT_RE.search(red.group(1))
                if lhs and lhs.group(0) in seen and lhs.group(0) not in reduces:
                    # When the statement runs an APPLICATION of the
                    # program rather than the program itself, showing
                    # only the right-hand side would read as "this
                    # program reduces to that value" — which is false
                    # for a program that is already a value.  Show the
                    # whole reduction instead.
                    shown = red.group(2)
                    if squeeze(red.group(1)) != lhs.group(0):
                        shown = f"{squeeze(red.group(1))} ==>> {squeeze(shown)}"
                    reduces[lhs.group(0)] = (stmt, shown)

    # Witnesses: a capstone is ABOUT the program its name starts with
    # (`state_example_safe`, `leak_state_rejected`, ...) — the tier's
    # own naming discipline.  Attributing by mere mention would credit
    # a program for a theorem that merely uses one of its values.
    witnesses = {p: [] for p, _, _ in programs}
    for rel in WITNESS_FILES:
        for _, name, _ in coqparse.decls_in(ROOT / rel):
            owner = max((p for p in witnesses if name.startswith(p + "_")),
                        key=len, default=None)
            if owner:
                witnesses[owner].append(name)

    # Integrity: every statement in the table must have its proof.
    proofs = {n for _, n, _ in coqparse.decls_in(ROOT / PROOF_FILE)}
    proved = {p[: -len("_proof")] for p in proofs if p.endswith("_proof")}
    stated = {s for s, _ in typed.values()} | {s for s, _ in reduces.values()}
    unproved = sorted((stated - {None}) - proved)
    if unproved:
        print("FAIL: example statements with no _proof in "
              f"{PROOF_FILE}: {', '.join(unproved)}", file=sys.stderr)
        return 1

    rows = []
    for name, rel, ln in programs:
        w = witnesses[name]
        if name not in typed and name not in reduces and not w:
            continue          # a helper value, not a program
        loc = f"{rel}:{ln}"
        ty = cell(typed[name][1]) if name in typed else "—"
        rd = cell(reduces[name][1]) if name in reduces else "—"
        ws = ", ".join(f"`{x}`" for x in w) if w else "—"
        rows.append(f"| `{name}` | `{loc}` | {ty} | {rd} | {ws} |")

    out = [
        "# Example matrix",
        "",
        f"Every example program of the tier ({len(rows)} of them), with the "
        "type it is",
        "given, the value it reduces to, and the theorems that speak about "
        "it by name.",
        "",
        "A `—` in *Typed as* / *Reduces to* means the program has no such "
        "statement:",
        "open bodies (`lazyMap_body`) are typed but not run, rejected terms "
        "(`leak_state`)",
        "are neither. Every typing and reduction listed here is discharged "
        "in",
        "`src/examples/ExamplesProofs.v` — the generator fails if one is "
        "not. When a",
        "reduction statement runs an *application* of the program rather "
        "than the program",
        "itself, the whole reduction is shown, not just its result.",
        "",
        "The *Witnesses* column lists the capstones of "
        "`src/examples/ExamplesSafety.v`",
        "and `src/examples/ExamplesRejection.v` — both gated by "
        "`make check-assumptions` —",
        "that are ABOUT the program: the tier names them after it "
        "(`state_example_safe`,",
        "`leak_state_rejected`), and the generator attributes by that "
        "name, never by a",
        "mere mention of one of the program's values.",
        "",
        "Generated by `make example-matrix` — do not edit by hand.",
        "",
        "| Program | Defined | Typed as | Reduces to | Witnesses |",
        "| --- | --- | --- | --- | --- |",
    ] + rows + [""]
    text = "\n".join(out)

    target = ROOT / OUTFILE
    if check_mode:
        current = target.read_text(encoding="utf-8") if target.exists() else ""
        if current != text:
            print(f"FAIL: {OUTFILE} is stale — run `make example-matrix`.",
                  file=sys.stderr)
            return 1
        print(f"OK: {OUTFILE} is up to date.")
        return 0
    target.write_text(text, encoding="utf-8")
    print(f"Wrote {OUTFILE} ({len(rows)} programs).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
