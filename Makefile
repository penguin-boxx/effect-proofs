.PHONY: all clean

COQ_MAKEFILE := src/Makefile.coq

all: $(COQ_MAKEFILE)
	$(MAKE) -C src -f Makefile.coq

$(COQ_MAKEFILE): src/_CoqProject
	cd src && coq_makefile -f _CoqProject -o Makefile.coq

clean:
	$(MAKE) -C src -f Makefile.coq clean 2>/dev/null || true
	rm -f src/Makefile.coq src/Makefile.coq.conf
	rm -f src/.*.aux
