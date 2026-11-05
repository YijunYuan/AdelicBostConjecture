# Selective Schur–Weyl proof extraction

Repository: https://github.com/TauCetiProject/TauCeti

Revision: `b3b0334ab9203d9faee4b2f34cd75161463ecdd0`.
License: Apache-2.0. Copyright and authors: The Tau Ceti contributors (2026).
`original/` retains immutable upstream files; `MANIFEST.json` records SHA256
and git blob hashes. The copied source is not an installed dependency.

Authorized by I-0070 after mathematical route review. Target Lean/mathlib pins
are unchanged. The upstream uses Lean 4.36.0-rc2; its build is unestablished.

Selected code lives under `BostConjecture/RepresentationTheory/SchurWeyl/`.
Only the permutation action, inclusion-exclusion polarization, pure-power
spanning, comparison-map commutant, semisimple image double centralizer and
invertible diagonal span are selected. Coordinate-specific wrappers, bundled
GL actions, FDRep, highest weights, classification, and TauCeti tensor-Hom
infrastructure are excluded. The existing project `piTensorHomEquiv` from
Mathlib PR #44845 is reused. Generic source namespaces are preserved where
canonical APIs are absent locally; private helper names use the project namespace.

Consumers: the actual determinant-covariant rectangular tensor and its bilinear
coefficient covector in Geometry, then rectangular invariant identification and
canonical contraction nonvanishing. Until explicit local checks and consumer
bridges are recorded in GEOMETRY.md, this is unverified source material.
