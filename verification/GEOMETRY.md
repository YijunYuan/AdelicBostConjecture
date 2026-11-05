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

## Scalar-extension compatibility

`Tensor/BaseChange.lean` supplies the canonical scalar-extension map on
actual tensor products. `Geometry/DeterminantBaseChange.lean` proves its
compatibility with tensor coordinates, the integral orbit-lattice inclusion,
and the top exterior-power twist. The final equality holds for every source
and target frame, over any commutative algebra, without flatness. This is the
compatibility identity for localization overlaps; it is not projective gluing.

- Module check `8b2dbff47b9041a9` passed at 2026-11-05 16:29:46 UTC
  (9066 jobs), including the arbitrary-target-frame corollary, without warnings.
- Earlier file check `166c0aadf3533522` failed on scalar-tower rewrites; these
  were repaired. Its second invocation passed with one unused simp argument,
  removed before the module check. LSP often returned partial elaboration;
  serialized file checks supplied feedback in those cases.
- All 38 exports, including the interrupted round's `DeterminantFrame` exports,
  passed the renewed combined `GeometryAxioms.lean` audit at 16:32:48 UTC,
  fingerprint `ffefd7bf352d83dc`. Only `propext`, `Classical.choice`, and
  `Quot.sound` occur; no `sorryAx` or additional axiom.
- Explicit checked revision: `3ac7a36`. An intervening automatic snapshot
  captured an earlier draft and is not its verification evidence.
- The read-only honesty reviewer found substantive producer use and honest
  scope. Its requests for explicit tableau hypotheses and the global consumer
  dependency edge were applied. No new external code was copied.

## Naturality and the lightweight determinant API

`Geometry/DeterminantNaturality.lean` proves the determinant-coordinate
formula for the actual exterior-power map, its tensor-power consequence,
and naturality of the twisted inclusion as an equality of linear maps.
Arbitrary maps between free modules of the same rank are allowed; neither
invertibility nor flatness is assumed.

- Module `de84f98189cb1a15` passed at 16:38:35 UTC, 9063 jobs; explicit
  proof pin `7c76270`. All 42 exports passed the combined axiom audit at
  16:41:55 UTC, with only the same three foundational axioms.
- At BOST-ARITH's request, the four existing determinant-coordinate
  declarations were moved unchanged into `Geometry/DeterminantCoordinates.lean`,
  importing only `ExteriorPower.Basic` and `Determinant`. Arithmetic's complex
  determinant metric is a substantive consumer; no bundle representation changed.
- Post-extraction combined build `2636613889bd279e` passed at 16:45:50 UTC,
  9068 jobs, covering both new modules and `DeterminantFrame`.
- The post-extraction 42-probe audit passed at 16:49:35 UTC
  (`ffefd7bf352d83dc`), again with only the three foundational axioms.
- The read-only honesty reviewer approved the naturality scope and the exact
  extraction. Blueprint nodes distinguish the top exterior coordinates from
  their Specht-dependent consumers.

## Tensor equivalences and principal-cover descent

`e4812e5` extends `Tensor/BaseChange.lean` to the canonical equivalence
for every finite family of modules over a commutative algebra. It proves the
inverse pure-tensor formula, naturality in module maps, and compatibility
with coefficient towers. No flatness or freeness assumption is used.
`Geometry/DeterminantBaseChange.lean` consumes it in the actual determinant
power and determinant-twisted lattice source, then proves the full
scalar-linear compatibility square for any free target frame.

`f58c467` adds `Geometry/LocalizationDescent.lean`. It clears denominators
and uses a unit-ideal combination to glue compatible localized elements
inside the original module. The actual consumer descends linear maps
uniquely and recovers their full localizations. A final theorem detects
injectivity locally. No glued-module or bundle representation is introduced.
The pinned Stacks module-gluing file was inspected only; no source was copied.

- The repaired full square passed the serialized file check
  `166c0aadf3533522` at 2026-11-05 17:27:14 UTC. Earlier universe,
  simplifier, and scalar-instance rewrite failures were repaired.
- The complete descent file passed `a8a05478d0b32244` at 17:29:07 UTC.
- The combined module build of `Geometry.DeterminantBaseChange` and
  `Geometry.LocalizationDescent` passed 9068 jobs at 17:29:52 UTC,
  fingerprint `4a935afc19caf820`, without warnings. Every check used
  `--root /home/yijunyuan/bc-workspace` and the shared serialized slot.
- All 59 transitive probes in `GeometryAxioms.lean` passed at 17:31:37 UTC,
  fingerprint `ffefd7bf352d83dc`: only `propext`, `Classical.choice`, and
  `Quot.sound`, with no `sorryAx` or additional axioms. Fingerprints identify
  commands; the content pins are the commits above.
- LSP repeatedly returned partial elaboration on the large determinant
  import cone. Narrow serialized file checks supplied the missing feedback;
  further iterative repairs follow the human request in I-0025 to minimize
  shared-slot occupancy.
- The read-only honesty reviewer found substantive producer use and no
  certificate, vacuity, or overclaim. Its blueprint clarifications about
  varying denominator exponents and compatibility on original elements
  were applied. Five new blueprint nodes are checked; the global
  determinant-isotypic node remains unproved.

The first unmet construction is now the assembly of finite-projective local
frames and transport of their determinant maps onto double localizations,
followed by application of the checked descent theorem. This is needed to
construct the global injection; the general descent producer alone does not
supply it.

## Remaining boundaries

The global integral injection and finite Hilbert tensor core are proved below.
Regrouping and the local determinant isometry are also proved below. The
restricted canonical contraction with its norm bound and equivariance, invariant
base change, and nonvanishing detection remain open. The geometric slope inequality and
number-field target are not proved by these producers.

Arithmetic interface coordination selected
`BostConjecture.Arithmetic.ComplexFiber` and `HermitianMetric` on existing
modules; no second bundle or degree representation is introduced here.

Graph coverage includes intentionally unattached helper/imported declarations;
source-facing nodes carry the proved attachment and completion claims. Read-only
hygiene review retained active nested lane/ancestor items. Scratch cleanup found
no stale candidates. Root integration through the regrouping batch passed 9148
jobs at 19:08:01 UTC (`975bdb23135a0d4a`, SPECHT pin `75b41aa`); later metric
leaf imports remain a subsequent integration batch.

## Global finite-projective determinant inclusion

The local-frame and gluing frontier is closed at `b72a7fd`.
`Geometry/ProjectiveFrames.lean` produces actual finite principal frames of
prescribed constant stalk rank using Mathlib finite-presentation lifting.
`Geometry/DeterminantTower.lean` proves exterior/tensor tower identities and
constructs actual determinant charts on scalar extensions of intrinsic modules.
`Geometry/LocalizationDescent.lean` now accepts arbitrary localization models
and specializes to tensor-ring overlaps, using Mathlib identifications directly.
`Geometry/ProjectiveEmbedding.lean` consumes all three producers to construct
the unique global map and recover its free formula after **every** coefficient
extension on which the module becomes free. Flatness over the integers gives
injectivity; no freeness of the original module is assumed.

- Producer pins: `26576cb`, `3844a4b`, `1f5c5a3`; global map pin `b72a7fd`.
  Concurrent automatic snapshots captured some drafts; these explicit pins and
  the checks below, not the snapshots, are the verification evidence.
- Combined frames/tower build `123f22d12823e254` passed 9070 jobs at
  2026-11-05 17:52:30 UTC. Generalized descent module `8c0559dcf98409f5`
  passed 1613 jobs at 18:01:08 UTC.
- Global map file check `91960196857d4aa1` passed at 18:07:40 UTC.
  The strengthened arbitrary-free-base-change version passed final module
  check `8138d12f84e54487`, 9072 jobs at 18:10:28 UTC, without warnings.
- All 78 transitive probes in `GeometryAxioms.lean` passed at 18:12:02 UTC
  (`ffefd7bf352d83dc`), using only `propext`, `Classical.choice`, `Quot.sound`.
  No `sorryAx` or additional axioms occur. Every check used the explicit root
  and shared serialized slot. Earlier local proof/instance failures were repaired.
- LSP often returned partial import elaboration; narrow serialized file checks
  supplied feedback. It was responsive for later chart proof repairs.
- The read-only honesty reviewer inspected the local and global constructions
  and verification records, finding substantive producer use and no vacuity,
  target-shaped assumption package, or hidden global-gluing claim. Its two
  blueprint wording corrections were applied.
- New checked blueprint nodes distinguish principal frames, chart towers,
  tensor-model descent and the **algebraic** projective inclusion. The larger
  determinant-isotypic node remains unproved because its metric and invariant
  conclusions are still open. No new external code was copied.

The next consumers are determinant isometry,
regrouping, and the restricted contracting pairing. Arithmetic requested the generic
finite tensor Hermitian core in `Tensor/**` and retains ownership of arithmetic
conjugation and degree integration (I-0030). The corresponding I-0031 root integration subsequently passed at `75b41aa`.

## Canonical finite Hilbert tensor form

`Tensor/Hilbert.lean` at `cb7df3a` constructs the positive definite core on the
actual complex `PiTensorProduct`, proves its pure-tensor formula and uniqueness,
and proves preservation by factor isometries and reindexing. It uses Mathlib's
binary Hilbert tensor product by finite induction. No global competing norm
instance, arithmetic metric representation, or assumed metric certificate is added.

- Module check `193ff323bec46737` passed 2814 jobs at 18:30:16 UTC.
- The expanded 84-probe `GeometryAxioms.lean` check passed at 18:32:13 UTC
  (`ffefd7bf352d83dc`), with only the three standard foundational axioms.
  Initial elaboration failures were repaired before these checks.
- The honesty reviewer independently inspected the module record and source,
  finding substantive positivity and uniqueness proofs and coherent local instances.
- The source-facing finite-Hilbert-tensor blueprint node is checked. Arithmetic
  transport, determinant isometry and the contraction remain subsequent consumers.
- Checked API sent to ARITH in I-0030 and root-integration/provenance owner
  SPECHT in I-0031. All external reuse is by direct unchanged Mathlib imports.

## Regrouping and actual local metric preservation

`Tensor/Regroup.lean` at `b112a8d` constructs canonical binary distribution and
rectangular regrouping over every commutative ring by finite induction, with
pure-tensor formulas and an inverse. `2690920` adds preservation of the Hilbert
form and `Tensor/DualRegroup.lean`, using the checked finite-projective duality
equivalence without assuming freeness. The latter has actual permutation
compatibility; its dual-metric compatibility is still a separate open consumer.

`Geometry/TensorMetric.lean`, `LatticeMetric.lean` and `DeterminantMetric.lean`
prove orthonormal tensor coordinates, the canonical positive complex orbit-lattice
form with its integral Gram formula, and preservation of the prescribed metrics
by the actual free lattice and determinant maps. The determinant form is imported
from ARITH's stable `Arithmetic.ComplexDeterminant` API (I-0032), and the finite
and binary tensor forms use the actual tensor objects. No certificate hypothesis,
new Hermitian bundle representation, or external copied code was introduced.

- Regrouping module check `4b32f0baa09efcc0` passed 1324 jobs at 18:40:54 UTC.
  The dual/metric regrouping combined check `011f15acf813f299` passed 2828 jobs
  at 18:47:58 UTC; its 100-probe audit passed at 18:48:54 UTC.
- Final local metric combined check `c90072712db1300c` passed 9079 jobs at
  19:19:54 UTC, without warnings. The repaired determinant file also passed
  `20f0564e1f884ccb` at 19:17:35 UTC. Earlier elaboration and instance failures
  were repaired with explicit canonical tensor instances and public formulas.
- The expanded 110 transitive axiom probes passed with only `propext`,
  `Classical.choice`, and `Quot.sound`; no `sorryAx` or additional axioms occur.
  A mistaken build-target invocation of the audit file failed with unknown
  package `verification`; the corrected `check --lean` invocation passed.
- All checks used the explicit workspace root and serialized slot. Following
  standing I-0034, no LSP queries or artifact cleanup were performed during the
  integration freeze. The root retry resolved the earlier missing-artifact race.
- The read-only honesty reviewer approved the actual metric proofs and blueprint
  attachments, finding no hidden isometry assumption or global-contraction
  overclaim. The three new metric nodes are checked; the full determinant
  isotypic/invariant theorem and canonical contraction remain unproved.

## Complex fibers and free permutation compatibility

`Geometry/ProjectiveMetric.lean` combines the actual global base-change theorem
with the local isometry, proving preservation of the prescribed forms on every
complex fiber. It takes a Core on the canonical tensor module and derives local
norm instances. Over arbitrary rings it claims a global map; integral injectivity
still requires the earlier integer-flatness hypothesis.
`Geometry/Permutation.lean` transports position permutations through tensor
coordinates and proves actual equivariance for the free lattice and determinant
maps. The global projective permutation descent is a subsequent consumer.

The combined module check `8f5fd4cb8257389e` passed 9085 jobs at 19:34:02 UTC;
all 114 transitive probes then passed with only the foundational axioms. Initial
canonical-module instance and alphabet-relabelling elaboration failures were
repaired. Read-only honesty review approved the two source/blueprint nodes.
The full contraction still needs dual-metric/evaluation compatibility and
restricted equivariance; no contraction completion claim is made.
