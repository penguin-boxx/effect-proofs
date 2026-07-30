.PHONY: all clean check-assumptions theorem-index stats check-docs verify help

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

# Fail if the committed generated docs are stale vs. the sources.
check-docs:
	./scripts/theorem_index.py --check
	./scripts/stats.py --check

# The one command a reviewer runs: build, axiom gate, docs freshness.
verify: all check-assumptions check-docs

clean:
	[ ! -f $(COQ_MAKEFILE) ] || $(MAKE) -C src -f Makefile.coq cleanall
	rm -f src/Makefile.coq src/Makefile.coq.conf src/.Makefile.coq.d

help:
	@echo "make                  build the development (parallel)"
	@echo "make verify           build + axiom gate + docs-freshness gate"
	@echo "make check-assumptions  axiom gate only (builds first)"
	@echo "make theorem-index    regenerate THEOREMS.md"
	@echo "make stats            regenerate STATS.md"
	@echo "make check-docs       fail if THEOREMS.md/STATS.md are stale"
	@echo "make clean            remove all build artifacts"
