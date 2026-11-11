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

The retained generic port lives in
`BostConjecture/ExternalCode/TauCeti/LinearAlgebra/SymmetricPower/{Basic,Lift}.lean`.
`Basic.lean` retains quotient extensionality, functorial maps, tensor
symmetrization, the factorial composite and naturality. `Lift.lean` retains
the generic quotient lift. These modules remain consumers' shared API.

The finite-index homogeneous comparison is adapted in
`BostConjecture/ExternalResults/TauCeti/LinearAlgebra/SymmetricPower/Finite.lean`.
Its `FinitePower R M n` is an abbreviation for Mathlib's existing
`SymmetricPower R (ULift (Fin n)) M`; the lifted index removes the inherited
restriction that the coefficient ring lie in the smallest universe.
Canonical tensor reindexing connects this quotient to ordinary `Fin n` tensor
powers. The homogeneous target remains the existing submodule `range(ι)^n`.
Commuting creation operators, adapted through the earlier selective port from
upstream `Algebra.lean`, prove the homogeneous comparison. The original
`TauCeti.SymmetricPower` namespace, revision and license are retained, with
Yijun Yuan credited for the universe adaptation. No new quotient, module
instance or homogeneous-polynomial representation is introduced.

The old local `Algebra.lean` became unreferenced and was removed after its
consumer moved to this generalized comparison. The table above records
**original upstream** source hashes, including `Algebra.lean`; it is not an
inventory of current local files. `Basic.lean` and `Lift.lean` are retained.
The selected source omits upstream basis, monomial and WordFiltration APIs.

Upstream uses Lean 4.36.0-rc2 and mathlib
`1b1ccf4b088b32fa3f23f2de1127433254a81e1e`; the target toolchain and pinned
mathlib remain unchanged. Original upstream build was not verified here.
Local consumer builds and transitive axiom checks are recorded in the Horizon
sessions; checking this selected dependency cone does not certify the entire
upstream repository.
Current consumers include the normalized symmetric section of
`BostConjecture.Geometry.polynomialTensorMap`, its equivariance and its
nonzero-evaluation lift in
[polynomial polarization](../../../../Geometry/Polynomial/Polarization.lean).
The subsequent [rectangular invariant-space identification](../../../../Geometry/Invariants/Rectangular.lean)
and [invariant orbit criterion](../../../../InvariantTheory/Plucker/OrbitCriterion.lean)
are proved in their respective project modules; they are not assumptions of
this symmetric-power port.
