.PHONY: all clean check-assumptions theorem-index stats example-matrix check-docs verify extract-run help

COQ_MAKEFILE := src/Makefile.coq
NPROC := $(shell nproc 2>/dev/null || echo 2)

all: $(COQ_MAKEFILE)
	$(MAKE) -j$(NPROC) -C src -f Makefile.coq

# `rocq makefile` is the canonical generator in Rocq 9 (the standalone
# `coq_makefile` binary is a compat shim absent from the official
# rocq/rocq-prover images); fall back to it for older toolchains.
$(COQ_MAKEFILE): src/_CoqProject
	cd src && { rocq makefile -f _CoqProject -o Makefile.coq \
	  || coq_makefile -f _CoqProject -o Makefile.coq; }

# Verify every capstone theorem is closed under the global context
# (no axioms).  Depends on `all` so the check never runs against a
# stale or partial build.  The capstone list is derived from the
# gated files — see scripts/check_assumptions.py.
check-assumptions: all
	./scripts/check_assumptions.py

# Regenerate THEOREMS.md (index of every Theorem/Corollary in src/).
# Purely syntactic — deliberately does NOT depend on `all`.
theorem-index:
	./scripts/theorem_index.py

# Regenerate STATS.md (per-directory LOC and declaration counts).
# Purely syntactic — deliberately does NOT depend on `all`.
stats:
	./scripts/stats.py

# Regenerate EXAMPLES.md (per-program type, result, witnessing
# theorems).  Purely syntactic — deliberately does NOT depend on `all`.
example-matrix:
	./scripts/example_matrix.py

# Fail if the committed generated docs are stale vs. the sources, or
# if the hand-written guides reference files/identifiers that no
# longer exist (rename rot) — see scripts/check_docs_refs.py.
check-docs:
	./scripts/theorem_index.py --check
	./scripts/stats.py --check
	./scripts/example_matrix.py --check
	./scripts/check_docs_refs.py

# The one command a reviewer runs: build, axiom gate, docs freshness.
verify: all check-assumptions check-docs

# Compile the extracted evaluator (src/extraction/evaluator.ml — a
# build product of Extraction.v) with the hand-written smoke driver
# and run it.  Optional: needs an OCaml compiler; nothing in
# `make verify` depends on the OCaml toolchain.
extract-run: all
	cd src/extraction && \
	  ocamlc -o extraction_smoke evaluator.mli evaluator.ml main.ml && \
	  ./extraction_smoke

clean:
	[ ! -f $(COQ_MAKEFILE) ] || $(MAKE) -C src -f Makefile.coq cleanall
	rm -f src/Makefile.coq src/Makefile.coq.conf src/.Makefile.coq.d
	rm -f src/extraction/evaluator.ml src/extraction/evaluator.mli \
	  src/extraction/extraction_smoke src/extraction/*.cmi \
	  src/extraction/*.cmo

help:
	@echo "make                  build the development (parallel)"
	@echo "make verify           build + axiom gate + docs-freshness gate"
	@echo "make check-assumptions  axiom gate only (builds first)"
	@echo "make theorem-index    regenerate THEOREMS.md"
	@echo "make stats            regenerate STATS.md"
	@echo "make example-matrix   regenerate EXAMPLES.md"
	@echo "make check-docs       fail if the generated docs or the docs references are stale"
	@echo "make extract-run      compile and run the extracted-evaluator smoke driver (needs OCaml)"
	@echo "make clean            remove all build artifacts"
