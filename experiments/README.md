# experiments/ — unbuilt scratch space

Nothing here is part of the verified development: these files are not
in `src/_CoqProject`, are not built by `make`, may contain
`Admitted`/`Axiom` placeholders by nature, and are excluded from
archival tarballs via `.gitattributes` (`export-ignore`).  See
ARTIFACT.md ("Scope of the verified development").

Provenance, newest first:

- `Sugar.v` — a deep-embedded surface-syntax elaborator
  (`surface_ty`/`surface_sig` compiled to core types) with four worked
  examples.  The ONLY file here that imports the live `src/` modules;
  it is kept in sync opportunistically (last touched for the
  `lt_min` → `lt_join` rename) but is not gated by CI.
- `phoas_coredelta.v`, `phoas_lambda2.v`, `phoas_stlc.v` — an
  abandoned PHOAS encoding line; the de Bruijn development in `src/`
  superseded it.
- `Fsub.v`, `STLC.v` — early standalone calculus sketches predating
  the current architecture.
- `mything.v`, `new.v`, `Play.v`, `paper.v` — exploratory scratch
  from the first design iterations (2026-05).
