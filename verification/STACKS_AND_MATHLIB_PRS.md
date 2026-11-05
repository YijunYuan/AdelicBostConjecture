# Selective reuse survey

Snapshot: 2026-11-05. Local Lean is 4.35.0 and Mathlib is pinned at
`56a005855ea17e0b0958f73ec801ae140b0a1679`. This was a bounded search of
relevant PR titles/bodies followed by source inspection, not an audit of all
Mathlib PRs. Search families covered Specht/tableaux/seminormal forms,
invariants/orbit closure/reductivity, Gram/covolume/Hermitian geometry,
exterior powers, tensor duality and base change. No direct implementation of
the missing seminormal asymptotic, arithmetic degree theory or invariant-orbit
criterion was found in this search.

Source inspection and upstream CI are distinct from local kernel verification.
The main theorem remains open. Only a port's recorded local checks certify its
adapted code; none of the results below supplies the whole downstream bridge.

## AxiomMath/Stacks

Inspected revision: [`012108f61d7f92a6ffc35ec3f263b6da5d438125`](https://github.com/AxiomMath/Stacks/tree/012108f61d7f92a6ffc35ec3f263b6da5d438125),
Lean 4.34.0-rc2, Mathlib `16edf57de7933555826307a3d81b4391a3657a09`.
No Stacks dependency was added.

**Ported and checked:** eight declarations ending in
`Matrix.sum_tensorPow_mul_altVec`, from
[`AlternatingTensorPower.lean`](https://github.com/AxiomMath/Stacks/blob/012108f61d7f92a6ffc35ec3f263b6da5d438125/StacksFrontier/LinearAlgebra/Matrix/AlternatingTensorPower.lean).
This proves determinant covariance of the unnormalized signed alternating
tensor over an arbitrary commutative ring. Three Mathlib imports suffice;
factorial division and the unrelated projector machinery were excluded.
The intended consumer is the rectangular column/word realization of
`lem:determinant-isotypic`. The port alone does not prove invariant-space
equality or gluing over the integer ring.

- Local source: `BostConjecture/LinearAlgebra/AlternatingTensorPower.lean`.
- Exact license, hashes, declaration map and adaptations:
  [`vendor/stacks/PROVENANCE.json`](../vendor/stacks/PROVENANCE.json).
- Kernel module check: fingerprint `00296386572144c3`, 14:33:06 UTC.
- Eight transitive axiom probes: fingerprint `3469b45b67413c5d`, 14:33:32 UTC;
  only `propext`, `Classical.choice`, `Quot.sound`.
- Durable extraction pin: workspace ledger `c1ce881`.

Additional source leads, **not copied**:

| Upstream file (relative to the pinned repository) | Use and boundary |
| --- | --- |
| `StacksFrontier/RingTheory/Flat/EqualizerBaseChange.lean` | `LinearMap.bijective_liftBaseChange_of_equalizer`; local Mathlib already has `tensorKerEquiv` and `tensorEqLocusEquiv`, preferable for coaction kernels. |
| `StacksCore/RingTheory/Flat/TorsionFree.lean` | `TensorProduct.submodule_tensor_inf_tensor_submodule`, with the small `Submodule.subtype_mkQ` helper; potential independent-factor invariant intersection. |
| `StacksFrontier/LinearAlgebra/ExteriorPower/Projective.lean` | `exteriorPower.instProjective`, a short split-map proof for determinant modules. |
| `StacksFrontier/Algebra/Module/TorsionFree.lean` | Dedekind finite torsion-free projectivity follows from existing Mathlib results; no large import needed. |
| `StacksFrontier/RingTheory/Localization/Glueing/Modules.lean` | Actual module gluing; local transition compatibility is still required. |
| `StacksFrontier/Algebra/Module/Projective/Determinant/ShortExact/Construction.lean` | Intrinsic determinant exact-sequence equivalence; about eight files, and no Hermitian isometry or degree additivity. Defer until the arithmetic API needs it. |
| `StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/AbsolutelyIrreducible.lean` | Burnside/density-based irreducibility ascent from an algebraically closed field; not rational Specht irreducibility. |

The finite-group invariant base-change result does not apply directly to
products of special linear groups. The inspected `OrbitSpaces/OrbitSeparation`
file does not prove polynomial orbit separation or the Euclidean/Zariski
closure comparison needed here.

## Mathlib PRs approved for selective port

All three approved ports are now committed and individually kernel-checked.
Attribution, exact source/local hashes, adaptations and verification evidence
are recorded under `vendor/mathlib-prs/<number>/PROVENANCE.json`.

| Port | Workspace commit | Module check | Transitive axiom check |
| --- | --- | --- | --- |
| [40948 provenance](../vendor/mathlib-prs/40948/PROVENANCE.json) | `3cb8de3` | `e427c60dadb0e721` | `1408901b6978ba73`, 5 exports |
| [44845 provenance](../vendor/mathlib-prs/44845/PROVENANCE.json) | `34a095a` | `36e15fc5f32630ac` | `a1952e5fc1e7963f`, 10 exports and 3 generic consumer examples |
| [45002 provenance](../vendor/mathlib-prs/45002/PROVENANCE.json) | `898c6c5` | `e1559dd0c1901505` | `8bd3125875ce00b6`, 30 exports |

All 45 exported declarations use only the standard foundational axioms
(`propext`, `Classical.choice`, `Quot.sound`). These are narrow checks; combined
root-build evidence belongs to the subsequent Horizon integration. Exterior
base change and polar proofs are unchanged. Tensor duality expands two missing
reindex simplification lemmas inline, preserving public statements. No dependency
or toolchain revision changed.

| PR and exact inspected head | Producer and intended consumer | Remaining bridge |
| --- | --- | --- |
| [#40948](https://github.com/leanprover-community/mathlib4/pull/40948), `b642b6723caf97b7b462dd5ddeabb0226c3b5433`, Lean 4.36.0-rc2 | `exteriorPower.baseChangeEquiv` and pure-tensor formulas; determinant/Plücker scalar extension. New exterior-power module plus a small exterior-algebra retraction helper. | Determinant-line specialization, equivariance/naturality as needed, and Hermitian compatibility. This is not invariant-kernel base change. |
| [#44845](https://github.com/leanprover-community/mathlib4/pull/44845), `47365e3b9fd4329f058c31ac7aa9565a6036b17d`, Lean 4.35.0 | `PiTensorProduct.Projective`, `piTensorHomEquiv`, `dualDistribEquivOfProjective` and evaluation formulas; canonical contraction for finite projective integer-ring modules. | Factor regrouping, equivariance, isotypic restriction and norm bounds. |
| [#45002](https://github.com/leanprover-community/mathlib4/pull/45002), `41260205df493c627e1ac0e54812cfdeb6517fbc`, Lean 4.36.0-rc1 | `ContinuousLinearMap.abs`, partial-isometry polar factor, `polar_comp_abs` and projection identities; the polar step for balanced Plücker vectors. | Invertible-to-unitary specialization, positive logarithm, trace zero, exterior isometry and the GIT argument. |

Successful build/test/lint jobs were inspected at the exact heads for
[#40948](https://github.com/leanprover-community/mathlib4/actions/runs/41189329214),
[#44845](https://github.com/leanprover-community/mathlib4/actions/runs/38477252120),
and [#45002](https://github.com/leanprover-community/mathlib4/actions/runs/40184770794).
These CI results do not certify a local backport. The polar port must take
`Abs` and `Polar` from one coherent head, not mix in the later #44997 API.

## Already in the local Mathlib pin

- [#40724](https://github.com/leanprover-community/mathlib4/pull/40724):
  `exteriorPower.inner_ιMulti_ιMulti`, `inner_ιMulti_self`, and
  `OrthonormalBasis.exteriorPower` in
  `Mathlib/Analysis/InnerProductSpace/ExteriorPower.lean`. These are for real
  finite-dimensional spaces; they do not construct the required complex metric.
- [#41479](https://github.com/leanprover-community/mathlib4/pull/41479):
  binary finite-projective `TensorProduct.dualTensorHomEquiv` and
  `dualDistribEquiv` in `Mathlib/LinearAlgebra/Contraction.lean`.
  The pure-tensor evaluation is `g n * f m`; do not assume another order by defeq.
- [#43827](https://github.com/leanprover-community/mathlib4/pull/43827):
  `LinearMap.liftBaseChange_injective_iff` and range/evaluation lemmas.
  The injectivity criterion requires a source basis and independence of its
  images. The project's orbit-lattice complexification is already proved.
- [#44604](https://github.com/leanprover-community/mathlib4/pull/44604):
  exterior-algebra base change, a prerequisite for #40948.

## Deferred or unsuitable PRs

- [#42931](https://github.com/leanprover-community/mathlib4/pull/42931), head
  `9d89974763579e6a500ba28ca0b3de4dc10a8a4a`: simultaneous positive-form
  diagonalization. Potential metric comparison support, but no continuity
  bounds; defer until needed.
- [#33642](https://github.com/leanprover-community/mathlib4/pull/33642), head
  `06ec350d9934129bb2f0dea8d6f84bc0dddda0e5`: smaller invertible-matrix polar
  proof lead, closed/unmerged, with no successful kernel build established by
  this survey. [#42449](https://github.com/leanprover-community/mathlib4/pull/42449)
  had failed CI. Neither is a verified producer here.
- #45001 is included in the selected #45002 cone; #44997 is a later absolute-value
  API, not an additional independent prerequisite.
- #41028/#43719 concern split exterior products with a rank-one factor, not
  arbitrary exact-sequence determinant multiplicativity.
- #43894 assumes simplicity in its Burnside theorem; it does not prove
  Specht simplicity. #44612/#44613 provide classification/counting rather than
  the missing seminormal producer.
- #45665 is a broad base-change/projectivity refactor without a present consumer.
  #40580 Gram completeness likewise has no selected consumer.
- #34897's experimental reductive-group code contains `sorry` instances and is
  excluded. #40683 concerns entrywise bounded Hadamard matrices, not the
  seminormal Gram asymptotic.
