.PHONY: all clean check-assumptions theorem-index stats

COQ_MAKEFILE := src/Makefile.coq

all: $(COQ_MAKEFILE)
	$(MAKE) -C src -f Makefile.coq

$(COQ_MAKEFILE): src/_CoqProject
	cd src && coq_makefile -f _CoqProject -o Makefile.coq

# Verify every capstone theorem is closed under the global context
# (no axioms).  Depends on `all` so the check never runs against a
# stale or partial build.  See scripts/check_assumptions.sh for the
# capstone list.
check-assumptions: all
	./scripts/check_assumptions.sh

# Regenerate THEOREMS.md (index of every Theorem/Corollary in src/).
theorem-index:
	./scripts/theorem_index.sh

# Regenerate STATS.md (per-directory LOC and declaration counts).
stats:
	./scripts/stats.sh

clean:
	$(MAKE) -C src -f Makefile.coq clean 2>/dev/null || true
	rm -f src/Makefile.coq src/Makefile.coq.conf
	rm -f src/**/.*.aux
	rm -f src/**/.lia.cache
