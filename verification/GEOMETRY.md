# Geometry verification

## Finite-free tensor realization

`BostConjecture/Geometry/TensorRealization.lean` identifies the existing
rectangular word action with `PiTensorProduct.map` using
`Module.Basis.piTensorProduct`. The general naturality theorem supports
different modules and frames. Its actual consumers prove determinant
covariance for the scalar span of the integral orbit lattice and the
change-of-frame identity. No additional external code was copied.

- Kernel check: `horizon --root /home/yijunyuan/bc-workspace check
  BostConjecture.Geometry.TensorRealization --json`, passed 2026-11-05,
  fingerprint `05f286f3d269793b` (9060 jobs).
- `verification/GeometryAxioms.lean`: five transitive probes passed,
  fingerprint `ffefd7bf352d83dc`; only `propext`, `Classical.choice`,
  `Quot.sound`.
- Blueprint: `lem:rectangular-tensor-realization` and
  `lem:rectangular-change-frame` are checked. This supplies local covariance,
  not the finite-projective determinant-twisted injection or invariant equality.

## Finite-projective ambient evaluation

`BostConjecture/Tensor/Evaluation.lean` constructs `tensorPowerPairing`
through `PiTensorProduct.dualDistribEquivOfProjective`. It proves the pure
tensor formula, simultaneous permutation invariance, the contragredient
identity, and vanishing precisely when the image tensor vanishes. It uses
finite projectivity, with no freeness assumption or certificate package.

- Kernel module check: fingerprint `77c6942507c8c1c0`, passed at
  2026-11-05 15:40:30 UTC (1730 jobs).
- Expanded `GeometryAxioms.lean`: twelve transitive probes passed at
  15:41:29 UTC, command fingerprint `ffefd7bf352d83dc`, only the same three
  standard foundational axioms. Fingerprints identify commands, not content.
- Blueprint `lem:projective-tensor-evaluation` is checked. It concerns the
  ambient algebraic pairing; it does not assert nonvanishing after restriction
  to the determinant-isotypic submodules or an archimedean norm bound.

The read-only honesty review of commit `0d893d5` classified its five exports
as proved producers with faithful finite-free blueprint scope. Root integration
has been requested from BOST-SPECHT; no root check is claimed here.

## Actual integral inclusion after flat base change

`BostConjecture/Geometry/FreeEmbedding.lean` constructs
`freeLatticeMap : R ⊗[ℤ] orbitLattice t →ₗ[R] (⨂[R] (_ : Fin n), M)`.
Its source is the scalar
extension of the integral lattice itself. Injectivity requires `Module.Flat ℤ R`;
the map, its pure tensor formula, determinant covariance and frame transition
are defined and proved over every commutative coefficient ring.

- Module kernel check `59698c2181f89f97`, passed at 15:48:07 UTC (9061 jobs).
- Seventeen combined transitive axiom probes passed at 15:51:06 UTC,
  `ffefd7bf352d83dc`, using only the three standard foundational axioms.
- Blueprint `lem:free-integral-tensor-embedding` is checked. The determinant
  line twist and finite-projective gluing are still subsequent constructions.

The additional read-only review of `1c0ac0c` found the ambient evaluation and
zero-detection proofs substantive and the blueprint scope faithful.

## Determinant-twisted free inclusion

`BostConjecture/Geometry/DeterminantFrame.lean` constructs coordinates on
the actual top exterior power through its universal alternating map. The
tensor power of these coordinates cancels the determinant weight of
`freeLatticeMap`. The resulting `freeDeterminantMap` has source
`(⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] orbitLattice t)` and is proved
independent of the chosen frame. It is injective when `R` is flat over ℤ,
and its basis-wedge normalization is proved.

- Module check `e3de615a7502d33d` passed at 2026-11-05 16:05:51 UTC,
  9062 jobs. Two earlier checks failed on extensionality tactic steps; these
  were repaired. LSP repeatedly returned partial elaboration, so a serialized
  file check was used during diagnosis before the successful module check.
- Blueprint `lem:determinant-twisted-free-inclusion` is checked and feeds
  `lem:determinant-isotypic`. The latter remains unproved.
- All 29 exported declarations passed the combined transitive axiom audit at
  16:07:24 UTC (`ffefd7bf352d83dc`): only `propext`, `Classical.choice`,
  `Quot.sound`, with no additional axioms or `sorryAx`.
- Read-only honesty reviews found the local constructions substantive;
  suggested codomain/rank wording and dependency-edge repairs were applied.

## Remaining boundaries

Localization compatibility and projective gluing of the global integral injection, the metric
isometry, regrouping and restricted canonical contraction, invariant base change and
nonvanishing detection remain open. The geometric slope inequality and
number-field target are not proved by these producers.

Arithmetic interface coordination selected
`BostConjecture.Arithmetic.ComplexFiber` and `HermitianMetric` on existing
modules; no second bundle or degree representation is introduced here.

The final graph sync had no missing-reference or stale-node warning; 388
unattached imported/helper declarations across the shared project remain an
intentional coverage warning, not verification of concurrent drafts. The
read-only roadmap hygiene review retained the nested active-lane count.
