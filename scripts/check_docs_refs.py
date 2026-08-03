#!/usr/bin/env python3
# ==================================================================
#
#                DOCS REFERENCE FRESHNESS CHECK
#
# Verifies that the hand-written guides (docs/*.md and the top-level
# README.md) do not reference things that no longer exist — the rot
# mode of prose docs after a rename: a `Theorem` cited by its old
# name, a module table naming a deleted file.
#
# Two checks, over every scanned doc:
#
#   1. FILE REFERENCES: every token that looks like a source file
#      (`Something.v`, `docs/xx.md`, `scripts/x.py`, `_CoqProject`,
#      paths in Markdown links — link targets carry the same
#      extensions, so one token scan covers both prose and links)
#      must exist on disk.  Bare names resolve against the repo
#      root, src/, the doc's own directory, every src/ subdirectory,
#      and experiments/ (home of the one documented unbuilt file).
#
#   2. IDENTIFIER REFERENCES: every single-token inline code span
#      that plausibly names a declaration (contains an underscore,
#      length >= 4, identifier-shaped) must occur — word-boundary
#      exact — in the sources: the .v files of the build plus
#      scripts/*.py and the Makefile (docs cite script/build
#      identifiers such as GATED_FILES too).  Glob-style tokens
#      (`*_ops_eq_map`, `LS_Join*`, trailing-underscore prefixes
#      like `EWF_`) become regexes and need at least one match;
#      `{a,b}` alternation expands and EVERY expansion must exist;
#      a lone `X` name segment is a documented metavariable and
#      matches like `*`.  Multi-token spans, hyphenated words, and
#      non-identifier notation are pseudo-code and are skipped, as
#      is everything inside fenced code blocks (file references are
#      still checked there — layout blocks name real files).
#
# The allowlist below is for genuinely informal names only; keep it
# small — if a doc references something that does not exist, fix the
# doc, don't grow the list.
#
# Exit status is nonzero on any failure, so CI can gate on it.
# Run via `make check-docs` / `make verify`.
#
# ==================================================================
import re
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import coqparse

ROOT = coqparse.ROOT

# ==================================================================
# ALLOWLIST — genuinely informal backticked names that look like
# declarations but deliberately are not (add sparingly, with a
# reason; anything fixable belongs in the doc, not here).
# ==================================================================
ALLOWLIST = {
    # docs/04: the generic payload transport that DELIBERATELY does
    # not exist yet — the doc names it as documented future work.
    "typing_ctx_map",
}

# File-reference tokens: path-charset runs ending in a source
# extension, plus the extensionless _CoqProject.  `*` is in the
# charset so a pattern like `docs/*.md` stays one token; such
# patterns resolve by globbing (at least one match required).
FILE_EXTS = (".v", ".md", ".py", ".yml")
PATH_TOKEN_RE = re.compile(r"[A-Za-z0-9_.\-/*]+")

# A declaration-shaped identifier (Coq allows primes).
IDENT_RE = re.compile(r"^[A-Za-z][A-Za-z0-9_']*$")
# The glob/alternation superset of the above.
GLOB_RE = re.compile(r"^[A-Za-z0-9_'*{},]+$")
BRACE_RE = re.compile(r"\{([A-Za-z0-9_',]+)\}")

SPAN_RE = re.compile(r"`([^`\n]+)`")
FENCE_RE = re.compile(r"^(?:```|~~~)")

# What the identifiers are checked against: the .v files of the
# build (via the shared _CoqProject parser) + the maintenance
# scripts + the Makefile (docs cite build-tool names like
# `coq_makefile`).
def corpus_files():
    files = [ROOT / "src" / f for f in coqparse.coq_project_files()]
    files += sorted((ROOT / "scripts").glob("*.py"), key=str)
    files.append(ROOT / "Makefile")
    return files


def corpus_tokens():
    """Every identifier-shaped token occurring in the sources.
    Set membership == word-boundary occurrence."""
    tok_re = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
    toks = set()
    for f in corpus_files():
        toks.update(tok_re.findall(
            f.read_text(encoding="utf-8", errors="replace")))
    return toks


def doc_files():
    return sorted((ROOT / "docs").glob("*.md"), key=str) + [ROOT / "README.md"]


def is_file_token(tok):
    return tok.endswith(FILE_EXTS) or tok.rstrip("/").endswith("_CoqProject")


def file_ref_ok(tok, doc_dir):
    """Resolve a file token against root, src/, the doc's own dir;
    bare names additionally against src/*/ and experiments/.  A
    token with a `*` is a glob and needs at least one match."""
    tok = tok.rstrip("/")
    bases = [ROOT, ROOT / "src", doc_dir]
    if "/" not in tok:
        bases += [d for d in sorted((ROOT / "src").iterdir())
                  if d.is_dir()]
        bases.append(ROOT / "experiments")
    if "*" in tok:
        return any(next(b.glob(tok), None) is not None for b in bases)
    return any((b / tok).exists() for b in bases)


def expand_braces(tok):
    """`shift_{ty,lt}_sig` -> [shift_ty_sig, shift_lt_sig] (product
    over every {…} group)."""
    m = BRACE_RE.search(tok)
    if not m:
        return [tok]
    out = []
    for alt in m.group(1).split(","):
        out += expand_braces(tok[:m.start()] + alt + tok[m.end():])
    return out


def glob_to_re(pat):
    parts = [re.escape(p) for p in pat.split("*")]
    return re.compile("^" + "[A-Za-z0-9_']*".join(parts) + "$")


def ident_candidates(tok):
    """Map one backticked token to the glob patterns to verify, or
    [] when the token is not a declaration reference (pseudo-code,
    notation, hyphenated prose, too short/ambiguous)."""
    if tok in ALLOWLIST or any(c.isspace() for c in tok):
        return []
    if is_file_token(tok):        # handled by the file check
        return []
    if not GLOB_RE.match(tok):    # notation, unicode, `ms_app1/2`, …
        return []
    pats = expand_braces(tok) if "{" in tok else [tok]
    out = []
    for p in pats:
        if "_" not in p:
            continue
        if p.endswith("_") and "*" not in p:
            p += "*"              # `EWF_` names a constructor prefix
        # A lone `X` segment is a documented metavariable (`map_X`).
        p = re.sub(r"(^|_)X(_|$)", r"\g<1>*\g<2>", p)
        if "*" in p:
            # 2-char stems keep the constructor-prefix families
            # (`S_*`, `H_`) checkable; a bare `_` stays informal.
            if len(p.replace("*", "")) >= 2:
                out.append(p)
        elif IDENT_RE.match(p) and len(p) >= 4:
            out.append(p)
    return out


def main():
    toks = corpus_tokens()
    missing_files = []   # (doc, lineno, token)
    missing_idents = []  # (doc, lineno, token)
    n_file_refs = 0
    n_ident_refs = 0

    for doc in doc_files():
        rel = doc.relative_to(ROOT).as_posix()
        in_fence = False
        for ln, line in enumerate(
                doc.read_text(encoding="utf-8").split("\n"), start=1):
            if FENCE_RE.match(line.lstrip()):
                in_fence = not in_fence
                continue
            # ---- file references (prose, links, AND fenced code) --
            for tok in PATH_TOKEN_RE.findall(line):
                if not is_file_token(tok):
                    continue
                n_file_refs += 1
                if not file_ref_ok(tok, doc.parent):
                    missing_files.append((rel, ln, tok))
            # ---- identifier references (prose only) ---------------
            if in_fence:
                continue
            for span in SPAN_RE.findall(line):
                for pat in ident_candidates(span):
                    n_ident_refs += 1
                    if "*" in pat:
                        rx = glob_to_re(pat)
                        if not any(rx.match(t) for t in toks):
                            missing_idents.append((rel, ln, span))
                    elif pat not in toks:
                        missing_idents.append((rel, ln, span))

    ok = True
    if missing_files:
        ok = False
        print("FAIL: docs reference files that do not exist:",
              file=sys.stderr)
        for rel, ln, tok in missing_files:
            print(f"  {rel}:{ln}: {tok}", file=sys.stderr)
    if missing_idents:
        ok = False
        print("FAIL: docs reference identifiers not found in the "
              "sources (rename rot? fix the doc, or — for genuinely "
              "informal names — extend ALLOWLIST in "
              "scripts/check_docs_refs.py):", file=sys.stderr)
        for rel, ln, tok in missing_idents:
            print(f"  {rel}:{ln}: `{tok}`", file=sys.stderr)
    if not ok:
        sys.exit(1)

    print(f"OK: docs references are fresh ({n_file_refs} file refs, "
          f"{n_ident_refs} identifier refs across {len(doc_files())} "
          "docs).")


if __name__ == "__main__":
    main()
