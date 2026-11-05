# BostConjecture

Formalize Theorem 1.1 of `../../bost_specht_manuscript.pdf`: maximal slopes
add under Hilbert tensor products of Hermitian bundles over every number
field, with the finite-family consequence. **The main theorem is not yet
formalized.** Only external results needed for that target belong in this project.

- Lean and mathlib: `v4.35.0`; exact dependency commits are in `lake-manifest.json`.
- Mathematical route: `blueprint/src/content.tex`; remaining unwritten
  mathematical inputs: `blueprint/OPEN_PROOFS.md`.
- Reused code, licenses, modifications and application boundaries:
  `CONTRIBUTIONS.md`; verified prerequisites: `verification/RESULTS.md`.
- Additional selective code leads: `verification/TAUCETI.md`.
- Original references and source anchors: `../../references/manifest.yaml`.

From this project directory:

```sh
horizon --root ../.. check --json
horizon --root ../.. check --lean verification/ReuseAxioms.lean --json
horizon --root ../.. run BOST-SPECHT --rounds 1 --no-dashboard
```

The first proof task constructs the actual integral Specht lattice and its
scalar-extension bridge; its larger milestone is the sublinear covolume bound.
The roadmap retains the arithmetic/HN specialization, geometric contraction,
compactness and final assembly as separate outstanding milestones.

`hgraph/` is generated state. To restore its source-scope configuration in a
fresh checkout, run:

```sh
mkdir -p hgraph
ln -s ../hgraph-sources.yaml hgraph/config.yaml
```

This excludes `.lake` from project graph generation while including copied
proof code. The workspace uses the Codex harness and its local authentication;
`.env` currently supplies no API keys. GitHub publishing is disabled. The user
has authorized Horizon tasks/runs and removed token/cost budget limits; the
initial scheduler uses one concurrent session and one round per invocation.
The live local dashboard is started from the workspace with `horizon dashboard`.
