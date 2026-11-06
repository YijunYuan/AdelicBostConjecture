# Selective symmetric-power polarization port

Upstream: [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti),
revision `3c3a32baea963db05c302adeb307b22baae4de78`.
Copyright (c) 2026 The Tau Ceti contributors. Authors: The Tau Ceti contributors.
License: Apache-2.0; verbatim license is [upstream/LICENSE](upstream/LICENSE).
Original source files are retrievable from the pinned repository and revision;
redundant local source snapshots are omitted.

| Original path | SHA-256 |
|---|---|
| `LICENSE` | `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` |
| `TauCeti/LinearAlgebra/SymmetricPower/Basic.lean` | `d7c2b0815d290049a793541a5ab8da4cdac366a5c48b0207c67141789f68e1d4` |
| `TauCeti/LinearAlgebra/SymmetricPower/Lift.lean` | `09af907ee522b141cacb7251606d643ebc668687b5479fd7d53530844e56bba5` |
| `TauCeti/LinearAlgebra/SymmetricPower/Algebra.lean` | `b344baa2589fbafc2a38351e41f61b6c55bfe8c0c6cba0c178fc14be85bb3e4d` |

Immutable URLs are
`https://raw.githubusercontent.com/TauCetiProject/TauCeti/3c3a32baea963db05c302adeb307b22baae4de78/`
followed by the original path in the table.

The port lives in `BostConjecture/ExternalCode/TauCeti/LinearAlgebra/SymmetricPower/`.
`Basic.lean` retains the extensionality/membership, functorial map,
quotient descent, `toTensorPower`, factorial composite and naturality cone;
unused finiteness, functor laws, range and injectivity corollaries are omitted.
`Lift.lean` retains quotient lift and commuting `consMul` and explicitly imports
Mathlib multilinear currying. `Algebra.lean` retains homogeneous multiplication,
the commuting creation-operator left inverse, injectivity and homogeneous
comparison. It retains the original algebra namespace `TauCeti.SymmetricPower`.
It omits `toSymmetricAlgebra_symmetricPower_apply` and all Basis,
BasisComparison, monomial and WordFiltration imports. The homogeneous component
is the existing submodule expression `range(ι)^d`, with its range proof supplied
by direct submodule-power induction. Lean 4.35 adaptations explicitly import
finite-product identities, parenthesize submodule coercions in equivalence
codomains, and use `Module.End.mul_apply`
for endomorphism multiplication. No second symmetric algebra, symmetric
power, polynomial or homogeneous-space representation is introduced.

Upstream uses Lean 4.36.0-rc2 and mathlib
`1b1ccf4b088b32fa3f23f2de1127433254a81e1e`; the target toolchain and pinned
mathlib remain unchanged. Original upstream build was not verified here.
Port and consumer verification is recorded in the historical geometry audit.
Current consumers include the normalized symmetric section of
`BostConjecture.Geometry.polynomialTensorMap`, its equivariance and its
nonzero-evaluation lift in
[polynomial polarization](../../../../Geometry/Polynomial/Polarization.lean).
The subsequent [rectangular invariant-space identification](../../../../Geometry/Invariants/Rectangular.lean)
and [invariant orbit criterion](../../../../InvariantTheory/Plucker/OrbitCriterion.lean)
are proved in their respective project modules; they are not assumptions of
this symmetric-power port.
