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

The chart assembly and global-map consumer of these descent producers are
proved in the next section. Descent by itself was not a global injection claim.

## Remaining boundaries

The global integral injection and finite Hilbert tensor core are proved below.
Regrouping and the local determinant isometry are also proved below. The
restricted canonical pairing and equivariance are proved below; its norm bound,
invariant base change, and nonvanishing detection remain open. The geometric slope inequality and
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
maps. The global projective permutation theorem below consumes this free identity.

The combined module check `8f5fd4cb8257389e` passed 9085 jobs at 19:34:02 UTC;
all 114 transitive probes then passed with only the foundational axioms. Initial
canonical-module instance and alphabet-relabelling elaboration failures were
repaired. Read-only honesty review approved the two source/blueprint nodes.
The global equivariance and restricted algebraic pairing consumers are checked
below; no metric-contraction completion claim follows from this checkpoint.

## Global projective permutation equivariance

`Tensor/ReindexBaseChange.lean` and `Geometry/ProjectivePermutation.lean`
prove the actual global equivariance identity. The proof normalizes intrinsic
determinant-lattice generators, uses the existing principal frame cover and
base-change formula, applies free equivariance, and detects equality locally.
The original module is never assumed free. This now supplies the genuine
embedding-equivariance input to the restricted pairing.

Final module check `2a871570380819bb` passed 9075 jobs at 19:39:50 UTC
without warnings, after repairing a scalar-tower rewrite and removing an
unneeded finiteness hypothesis from the scalar-extension lemma. All 119
transitive probes then passed with only the standard foundational axioms.
Read-only honesty review found substantive use of the global cover and actual
producers, with faithful source-facing blueprint attachments.

## The actual integral equivariant restricted pairing

`Geometry/Contraction.lean` defines `dualDeterminantMap` from the constructed
projective determinant maps and finite-projective dual regrouping. Its
`canonicalPairing` restricts the actual tensor-power evaluation through those
maps, and `canonicalPairing_reindex_left` proves contragredient equivariance.
Everything is defined over the original commutative ring with finite projective
modules. The theorem claims an algebraic map and equivariance, without assuming
or claiming injectivity, metric contraction, or nonvanishing.

Module check `e7f3f665e66ab94b` passed 9081 jobs at 19:42:59 UTC without
warnings. All 124 transitive probes passed with only `propext`,
`Classical.choice`, and `Quot.sound`. Read-only honesty review approved the
actual producer route; its finite-family/evaluation notation clarifications
were applied to the checked blueprint node. The dual metric and evaluation
bound are proved next; tensor-duality compatibility, invariant base change and
nonvanishing remain subsequent producers.

## Canonical dual form and the current metric frontier

`Tensor/DualMetric.lean` constructs `dualRieszEquiv` and `dualCore` on the
existing algebraic dual. It proves the exact continuous operator-norm identity,
the evaluation bound and the orthonormal-coordinate Gram formula. ARITH accepted
this generic interface in I-0038 and owns arithmetic dual scalar-extension and
conjugation transport. No duplicate module, bundle, or arithmetic metric is added.

- Module check `14e934fc56245088` passed 2486 jobs at 19:51:41 UTC without
  warnings. The expanded 131-probe audit `ffefd7bf352d83dc` passed at
  19:52:52 UTC with only the standard foundational axioms and no `sorryAx` or additional assumptions.
- Earlier missing completeness and semilinear simplifier failures were repaired
  using `FiniteDimensional.complete` and a direct rewrite, without raising limits.
- Read-only honesty review approved the canonical dual construction and actual
  norm/evaluation consumer. The new dual-metric blueprint node is checked.
- At this checkpoint the next metric producer was isometry of the canonical
  `dualDistribEquivOfProjective` for these dual/Hilbert forms. Its full
  source-facing Riesz-vector proof is now checked in the Hilbert-tensor-duality
  node, as recorded below. This is consumed by the restricted pairing norm bound;
  invariant-space equality is not a prerequisite for that norm argument.

Commit `eecbe72` incidentally captured ARITH's staged `BinaryTensorMetric.lean`
and arithmetic blueprint edit through the shared index. This is not GEOM proof
evidence for those paths. ARITH independently verified the module before staging
(`94052864d5cf1949`, 3450 jobs at 19:43:46 UTC); the parent confirmed no deletion
or content mismatch. I-0039 records the resolution. Subsequent GEOM commits use
`commit --only` with explicit owned paths as well as explicit staging.

Earlier boundary sync: 151 blueprint nodes, 1059 Lean declarations and 683 generated
edges, with no stale/missing-reference warning. The 570 unattached declarations
are intentional helper/imported coverage, including concurrent lane work.
Read-only hygiene review retained 13 active nested items across the three proof
lanes and corrected stale frontier wording. Scratch dry-run found no stale
candidates. I-0038 and I-0039 are resolved. SPECHT subsequently supplied the fixed root pass
`975bdb23135a0d4a` at 20:05:06 UTC (9171 jobs), covering delivered leaves through
`90d9c82`; I-0036 was closed. Later metric leaves have their own checks below. I-0034 still forbids this session's legacy
LSP client; every post-freeze feedback check used the serialized kernel slot.

ARITH subsequently supplied the actual finite-projective dual scalar-extension
and fiber/conjugation interface in `Arithmetic/DualFiber.lean` at `e3a7b48`
(I-0040; module `71e786e1c6fa94d7`, 3344 jobs at 19:55:00 UTC). Its expanded
ARITH audit is maintained separately. This is the agreed algebraic transport
for the next metric consumer; it does not prove Hilbert tensor-duality isometry.

## Hilbert tensor duality and its actual regrouping consumer

`Tensor/DualCompatibility.lean` proves that the Riesz vector of a pure tensor
functional is the tensor of the factor Riesz vectors. Spanning then proves
inner preservation by the actual `dualDistribEquivOfProjective`, and the exact
dual norm gives the evaluation bound for arbitrary tensors. `HilbertMap.lean`
provides the standard Core-input factor-preservation theorem.
`DualRegroupMetric.lean` consumes these results and Hilbert regrouping to prove
metric preservation by the actual `dualRegroupEquiv` used in the pairing.
Its statement has no isometry-certificate hypothesis.

Final module check `1ea58e5bee1a69c5` passed 2832 jobs at 20:03:04 UTC without
warnings; all 136 transitive axiom probes passed with only the three standard
foundational axioms. Earlier notation and unused-simp feedback was repaired.
Read-only honesty review approved the source/blueprint correspondence and
substantive use of the generic map lemma. Both duality metric nodes are checked.
The local restricted determinant pairing bound is checked below. Its identification
with scalar extension of the integral pairing remains a subsequent consumer;
invariant detection remains separate.

## Local determinant pairing contraction

`Geometry/ContractionMetric.lean` proves the isometry of the tensor product of
actual dual determinant maps, then consumes it with dual regrouping, tensor
evaluation and the isometric inclusion to obtain the product bound on arbitrary
source tensors. The determinant, dual and lattice metrics are the prescribed
ones. No target-shaped certificate or pairing bound is assumed.

Module check `456e68d5f3c862c0` passed 9088 jobs at 20:14:08 UTC.
All 138 transitive axiom probes then passed with only `propext`,
`Classical.choice`, and `Quot.sound`, and no `sorryAx` or new axioms.
The first underspecified Core rewrite and heartbeat failure were repaired by
explicit arguments and a separately proved factor-map lemma. The final matching
of nested Core-derived instances uses a localized `maxRecDepth 1024`; there is
no heartbeat increase. An accidental workspace-cwd file check had no project
search path and was rerun from the member project. Read-only honesty review
approved the final source and the local blueprint completion marker.

This is a local pointwise contraction theorem. The global integral-to-complex
pairing diagram is still required before marking canonical-contraction checked.
ARITH supplied its intrinsic dual metric at `ba2f037` (3349-job module check,
I-0041); this complements its dual base-change interface at `e3a7b48` and will
be reused for that diagram. Invariant base change and nonvanishing remain open.

## Session 0010 handoff

Human I-0043 requested handoff after the verified local contraction so the next
round can start with the guarded LSP client. BOST-GEOM remains open. No proof
work was started after that request was read; the global pairing diagram and
contraction are explicitly deferred to that round.

Before the request was read, an initial `Tensor/EvaluationBaseChange.lean` draft
was checked and failed (`84bc78e9aaa6390a`, 20:16:11 UTC). It is not a producer:
the scalar case needs an explicit restricted-scalar linearity rewrite, and the
`LinearEquiv.baseChange` call used the wrong argument order. The exact draft is
preserved outside the build tree at workspace-relative
`.archon-horizon/runs/0005/sessions/0010-horizon-BOST-GEOM/artifacts/EvaluationBaseChange.lean.txt`;
the matching failure JSON is in that session's `checks/` directory. Its full
source-facing blueprint proof remains `notready`, without a Lean attachment.
The next round should reuse this evidence and ARITH's checked dual interfaces,
then prove the dual regrouping/determinant transport needed by canonicalPairing.

The stable local-contraction import was handed to SPECHT in I-0044, with the
138-probe evidence and the distinction from the earlier 9171-job root batch.
The shared-index incident above remains resolved; final owned commits use
explicit `commit --only` pathspecs. No other lane's drafts are certified here.

Final hygiene review confirmed the handoff and no pending owned Lean changes.
The graph sync has 158 blueprint nodes and two stale declaration nodes, both
from the removed failed evaluation draft. Their generated `lean_ok` tags are
syntactic scanner output, not kernel evidence; the failed-check reviews and
node comment explicitly record this. No blueprint node attaches to those drafts.
Helper/import coverage warnings and the ten active roadmap items across the
three lanes are retained intentionally. Scratch dry-run found no stale candidates.

## Tensor evaluation under arbitrary scalar extension

`Tensor/EvaluationBaseChange.lean` repairs the preserved failed draft and proves
the actual evaluation square and tensor-power pairing square on arbitrary
elements of both scalar extensions. The argument uses finite projectivity,
ARITH's canonical dual equivalence, and tensor-map naturality, without a
freeness or flatness assumption on the extension ring.

- Module check `0c9c7c3672723131` passed 3359 jobs at 2026-11-05 20:28:22 UTC.
- The 142-probe combined axiom audit passed at 20:29:18 UTC, fingerprint
  `ffefd7bf352d83dc`; only `propext`, `Classical.choice`, and `Quot.sound`.
- Guarded LSP feedback is active in session0012; scalar-action and coercion
  proof errors were repaired before kernel verification. No kernel check failed.
- Read-only honesty review found substantive actual-map proofs and no
  certificate or vacuity defect. The evaluation blueprint node is checked;
  canonical pairing transport through regrouping/determinant maps is still open.

`Tensor/DualRegroupBaseChange.lean` now consumes the evaluation square to prove
compatibility of the actual canonical dual regrouping on the entire scalar
extension. It constructs the ambient dual identification from the existing
tensor and dual equivalences and imposes no freeness or flatness assumption.
Module `f4bd4142fbf0161a` passed 3362 jobs at 20:33:04 UTC; all 148 combined
axiom probes passed at 20:35:38 UTC with the same three foundational axioms.
Read-only honesty review approved the source and blueprint correspondence.
The remaining pairing transport concerns its determinant factors.

`Tensor/PairingBaseChange.lean` identifies tensor-power pairing into the
scalar-extended tensor product, transporting the ambient dual by the canonical
inverse pullback. Module `6baad720253d5e6e` passed 3363 jobs at 20:44:44 UTC;
the 150-probe audit passed at 20:49:26 UTC with foundational axioms only.
An earlier invocation of that module failed on coercion of a composite
equivalence to a linear map; the explicit map identity repairs it. The new
canonical-pairing base-change blueprint node remains unmarked until the
determinant-factor assembly is verified.

The one-time read-only health review found the 12-active roadmap warning
intentional: it counts nested ancestors of the four authorized live proof
lanes. I-0044 remains open for SPECHT integration; the human owns I-0047 until
BALANCED provides its canonical semistability signatures and GEOM confirms the
consumer interface. Scratch dry-run found no stale candidates.

`Geometry/ContractionBaseChange.lean` proves the scalar-extension formula for
`canonicalPairing` on arbitrary vectors in both extended determinant sources.
It consumes the actual projective determinant naturality, dual regrouping and
evaluation squares; it assumes neither a compatibility certificate nor a metric
bound. Full module check `659b4191811118f7` passed 9089 jobs at 21:27:59 UTC;
the subsequent 156-probe transitive axiom audit passed at 21:33:18 UTC, with only
`propext`, `Classical.choice`, and `Quot.sound`. Read-only honesty review approved
the exact source-facing statement and proof chain before its blueprint node was
marked. Earlier LSP elaboration timeouts were resolved by specifying the ambient
tensor module and composing generic evaluation identities. The earlier prefix
check `e899af9a611cfc31` is not evidence for the full theorem. Source and blueprint
were committed at `b42d795` (earlier automatic snapshots held partial source).

I-0044 was closed after SPECHT confirmed its fixed 9190-job root integration
batch. The newer pairing transport and determinant assembly are outside that
batch. I-0051 confirmed ARITH's stable `piTensor`, `pullback`, `pullback_inner`
and `fiberMap_injective` interfaces. The intrinsic metric consumer is in
progress; its invalid namespace-instance setup is preserved in session0012
attempt0001. I-0047 remains human-owned while BALANCED selects its exact action
and invariant-polynomial signatures.

`Geometry/IntrinsicContraction.lean` constructs the actual isometric fiber
inclusion using ARITH's `piTensor` and `pullback`, then proves
`canonicalPairing_fiber_le` for the prescribed determinant/lattice tensor
forms. Default orthonormal frames are constructed from constant stalk rank;
no frame-existence, determinant-isometry or contraction certificate is assumed.
Module `16ecb6e32b5ff94b` passed 9107 jobs without warnings at 21:53:18 UTC.
Source SHA256: `cc133ccb15fe891ae8bbcf4797b2eddcccfed4137e263d05e36c7ffb0dbdf52c`.
Final read-only honesty review accepted the exact dimension and intrinsic
bilinear-bound nodes. The full `lem:canonical-contraction` stays unmarked.

The next required endpoint is the norm bound in the actual dual fiber.
Session0012 attempt0002 preserves `ContractionNorm.lean` (only an unfinished
bijectivity lemma); it was removed from source, and no check is claimed for it.
Prove bijectivity of `dualDeterminantTensorBaseChange` by tensoring the checked
factor equivalences and composing with `Tensor.baseChangeEquiv`. Transport the
explicit positive tensor form through this map; finite projectivity of the
source follows from the existing exterior-power, orbit-lattice and tensor
instances. Then apply `Tensor.dualCore_norm` and the operator-norm bound theorem
to `canonicalPairing_fiber_le`, identifying scalar extension of the integral
dual with its complex dual by the existing canonical equivalence. ARITH's
`HermitianMetric.dualFiber_norm` provides the intrinsic metric identification.
No new Hermitian-bundle or degree representation is needed.

Parent conversation I-0055 requests this round end after the metric check to
recycle long-lived Lean clients under increased swap pressure. BOST-GEOM stays
open. The invariant interface proposal in I-0047 is agreed, but its concrete
BALANCED exports remain pending. The final scratch dry-run has no stale
candidates. The roadmap's 15-active warning still counts nested ancestors of
the four authorized lanes; GEOM has one active proof leaf and has not changed
other owners' items.

The final serialized `--lean verification/GeometryAxioms.lean` check passed
at 21:58:27 UTC (fingerprint `ffefd7bf352d83dc`, 31.6 seconds after waiting for
the shared slot). All 159 probes report only `propext`, `Classical.choice`,
and `Quot.sound`; no `sorryAx` or custom axioms occur. This includes the three
IntrinsicContraction exports and their transitive dependencies. Their source
unit is `38aaf59`; automatic snapshots before that commit are not separate
verification evidence. Blueprint completion markers were committed at `b97bb77`.

Final scoped graph sync: 195 blueprint nodes, 1317 Lean declarations and 898
edges, with no missing labels/declarations reported. Its 692 unattached helper
warnings are retained as coverage information, not a proof-completion claim;
the new source-facing producers are attached. SPECHT received the checked
three-module import batch in I-0052; root integration of that batch is subsequent
and is not asserted by the leaf checks above.

## Canonical contraction in the actual dual fiber

`fd211a8` supplies the final dual-norm endpoint in
`Geometry/ContractionNorm.lean`. The canonical tensor transport is bijective;
its pullback of the prescribed determinant/lattice tensor form is positive.
`canonicalPairing_fiber_norm_le` bounds the actual scalar extension of
`canonicalPairing`, identified with the complex dual by `dualBaseChangeMap`.
`Tensor.dualCore_norm_le` and the existing `dualCore_norm` identify this with
the operator norm, with no certificate assumption. No external code was copied.

- Module `edec714a5cf09fb0` passed 9108 jobs at 2026-11-05 22:16:29 UTC.
  The earlier file check `60a0192492a979c0` failed on a continuous-scalar
  instance-search timeout. Factoring the general dual-norm characterization
  into the existing `Tensor/DualMetric.lean` API repaired that failure.
- The expanded 163-probe transitive audit passed at 22:17:45 UTC
  (`ffefd7bf352d83dc`); only `propext`, `Classical.choice`, and `Quot.sound`
  occur. The full log is in session0014/contraction-norm-axioms.log.
- The read-only honesty reviewer found substantive use of the actual pairing
  and prescribed metric, with no vacuity or hidden certificate. The new norm
  node and `lem:canonical-contraction` are checked; the latter attaches the
  actual integral definition, application, equivariance and norm declarations.
- Root import integration is owned by SPECHT and is not asserted by these leaf
  checks. Intermediate automatic boundary commits captured incomplete drafts;
  the explicit content pin above and successful checks certify the final unit.

The canonical contracting pairing is now proved. Invariant-space identification,
invariant base change and nonvanishing in unbounded degrees remain open, as do
the geometric slope inequality and number-field target. BALANCED confirms its
concrete polynomial/coaction exports are pending; independent-factor invariants
and the generic flat-kernel/evaluation argument can proceed independently.
The one-time read-only hygiene review retained the 15 active roadmap rows as
four live proof leaves and eleven ancestors; no status churn is needed.

## Kernel detection, independent invariants and polynomial tensors

Session0014 continues from the completed canonical contraction with actual
algebraic producers, without a new bundle or degree representation:

- `e411a3c`, `Geometry/InvariantBaseChange.lean`: the canonical flat kernel
  equivalence commutes with evaluation; faithfully flat extension detects
  nonzero evaluation on that kernel. Module `688f08cf8b0ac1ab` passed at
  22:20:10 UTC. The application to polynomial coactions remains separate.
- `46a2476`, `Geometry/IndependentInvariants.lean`: the tensor of two invariant
  subspaces is canonically the invariant subspace for independent group actions.
  Module `e6eeaf114063a89a` passed at 22:24:08 UTC.
- `534fa25`, `Geometry/PiInvariants.lean`: the two-factor theorem is consumed
  in cardinal induction to obtain unique preimages under the canonical map
  from the tensor of invariants for any finite family. The empty family is
  included, and no finite-dimensional or finite-group assumption is used.
  Module `f09e9bb818e9f5b1` passed at 22:35:58 UTC. The 177-probe audit passed
  at 22:37:27 UTC; only `propext`, `Classical.choice`, and `Quot.sound` occur.
- `7239cdf`, `Geometry/PolynomialTensor.lean`: multiplication of linear forms
  gives the actual quotient onto BALANCED's `homogeneousPolynomials`. It
  commutes with linear pullback and inverse-pullback representation, and its
  evaluation equals the existing finite-projective tensor-duality pairing.
  The nonzero-preimage theorem consumes the range and evaluation identities.
  Module `571bcbec8790f6dd` passed 2374 jobs at 22:43:25 UTC.

Read-only honesty reviews found each limited producer substantive and faithful;
no invariant preimage is claimed by the polynomial quotient theorem. No external
source was copied. Root integration is assigned to SPECHT in I-0059, with leaf
check evidence; this report does not infer a root build from those checks.

The next local producer is `lem:polynomial-symmetric-lift`. Its complete
mathematical proof now identifies the quotient kernel by tensor-word orbits
and commutative monomials, then descends normalized permutation averaging.
Mathlib's `TensorPower/Symmetric.lean` explicitly leaves the homogeneous
polynomial comparison as a TODO; importing it does not supply this bridge.
The concrete coaction scalar-extension and rational-point bridge still await
BALANCED. Rectangular SL-invariant identification remains a separate SPECHT
producer. These must feed actual contraction nonvanishing before BOST-GEOM can
be marked complete. The geometric slope inequality and Theorem 1.1 remain open.

The final serialized `--lean verification/GeometryAxioms.lean` audit passed
at 2026-11-05 22:47:59 UTC (`ffefd7bf352d83dc`, 27.552 seconds after
165.535 seconds waiting for the shared slot). All 184 probes report only
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx` or
custom axiom in their transitive dependencies. The full log is
session0014/polynomial-tensor-axioms.log. The final polynomial quotient marker
was added only after this audit and the read-only honesty review.

## Pinned polarization port and actual invariant lift

Human I-0063 authorizes the extra `LinearAlgebra/SymmetricPower/**` and
`vendor/tauceti-polarization/**` paths. The selective port retains TauCeti's
commuting-operator comparison and symmetrization proof, pinned at
`3c3a32baea963db05c302adeb307b22baae4de78`. Verbatim sources, exact hashes,
Apache-2.0 license, authors and adaptations are in the vendor provenance record.
No basis, monomial, WordFiltration or repository dependency was imported.

- `47c79f2`: `SymmetricPower/Basic.lean`; module `880e87cdefa7c2d8` passed
  at 22:52:52 UTC.
- `d56b70d`: `SymmetricPower/Lift.lean` and `Algebra.lean`; the latter module
  `4251d1bff1cb50f2` passed 1567 jobs at 22:55:33 UTC. Its first check failed
  on missing finite-product imports, submodule coercion parentheses and the
  newer upstream endomorphism multiplication rewrite. Explicit imports,
  parentheses and `Module.End.mul_apply` repaired these compatibility errors.
- `c55300f`: `Geometry/PolynomialPolarization.lean`; module
  `4df483df0e24e340` passed 2379 jobs at 22:59:38 UTC. It proves the actual
  normalized section of `polynomialTensorMap`, naturality for every linear
  pullback, permutation invariance, uniqueness among symmetric tensors, and
  `exists_invariant_tensor_evaluation_ne_zero`. The last theorem consumes
  BALANCED's unchanged intrinsic polynomial invariants and the existing
  finite-projective evaluation identity. The quotient-preimage gap is closed.

The port's scalar type convention `R : Type` is inherited from Mathlib's
symmetric power indexed by `Fin d`; it imposes no freeness or rank restriction.
The algebra comparison works over commutative semirings and arbitrary modules;
factorial normalization needs characteristic zero. The concrete evaluation
consumer uses finite-dimensional vector spaces. No orbit criterion or
rectangular invariant-space equality is encoded as an assumption package.

The earlier root batch through `PolynomialTensor` passed 9227 jobs without
warnings at 22:51:43 UTC (`975bdb23135a0d4a`, root blob
`3cc15b902cb12270bbe0b37a82b6fc3141cff1b2`). The new polarization batch and
its CONTRIBUTIONS entry are a separate handoff to SPECHT. The preceding
source-scope graph sync had 219 blueprint nodes, 1453 declarations and 1043
edges; its 728 unattached helper warnings are intentional coverage information,
not checks of concurrent drafts. The graph CLI initially rejected `sync --json`;
the corrected plain sync succeeded. No source/build claim relies on that
rejected CLI command.

The final 202-probe audit passed at 2026-11-05 23:01:48 UTC
(`ffefd7bf352d83dc`, 48.022 seconds), with only `propext`, `Classical.choice`
and `Quot.sound`. Both the read-only honesty review and a fresh source-fidelity
review found no actionable mismatch, assumption package or provenance defect.
The latter checked the raw hashes/license, selected proof closure and actual
consumer. Accordingly the homogeneous comparison and symmetric invariant-lift
nodes are marked checked. No transitive custom axiom or `sorryAx` occurs.

The next local nonvanishing producer is the actual pullback of a Pluecker
invariant to `Hom(V, tensor E)`, with its degree and group invariance, followed
by degree divisibility and canonical tensor regrouping. Polynomial coaction
scalar-extension/rational-point compatibility and rectangular SL-fixed-tensor
spanning remain separate unmet producers. They are not implied by this port,
the earlier kernel lemma or the clean root build. BOST-GEOM remains incomplete.

Final scoped graph sync: 226 blueprint nodes, 1547 Lean declarations and 1093
edges, with no missing-reference warning. The 760 unattached helpers/imports
remain intentional coverage information; checked source-facing producers are
attached. The one-time hygiene review retained nested active lane ancestors;
GEOM has one next proof leaf, BOST-GEOM-NONZERO. Scratch cleanup found no stale
candidates. Human I-0063 stays open for its initiator; I-0066 tracks the remaining
shared root/attribution integration of the polarization batch.

## Actual Pluecker polynomial pullback

`Geometry/PluckerPolynomial.lean` constructs the algebra pullback along
`A ↦ wedge (A b)` using the existing finite-projective tensor duality and
polynomial tensor quotient. It proves evaluation, multiplication of homogeneous
degrees by the source rank, and equivariance for arbitrary target linear maps
and determinant-one source maps. The resulting invariant theorem uses Mathlib's
`Representation.linHom` with independent target and special-linear source
actions. No polynomial-map certificate or new arithmetic representation is used.

- Module `b1a46f37f453cfb2` passed 2410 jobs at 2026-11-05 23:18:05 UTC.
- All 212 transitive probes passed at 23:18:54 UTC (`ffefd7bf352d83dc`),
  with only `propext`, `Classical.choice`, and `Quot.sound`. No custom axioms
  or `sorryAx` occur. LSP proof/coercion errors were repaired before these checks.
- The read-only honesty review found substantive producer consumption and
  faithful scope. Its clarification that only the source map must have
  determinant one was applied to the blueprint. Both limited nodes are checked.
- No external code was copied. Polynomial extensionality uses unchanged
  Mathlib symmetric-algebra coordinates and multivariate polynomial extensionality.

The remaining local consumer combines the actual pullback with polarization,
then regroups Hom-dual tensor powers into the determinant-isotypic factors.
Rectangular invariant identification and polynomial coaction base change are
still separate boundaries. I-0067 was consumed by the completed session0014
handoff; session0016 is its fresh continuation. The one-time read-only hygiene
review retained 12 active roadmap rows as four frontiers and eight ancestors.

`Geometry/PluckerPolarization.lean` now consumes this pullback, invariant powers
and the checked normalized lift to produce Hom-dual invariant tensors in every
multiple of the pulled-back degree. Its concrete binary consumer uses BALANCED's
actual product-SL Pluecker invariants. Module `db602ea8eca60eb6` passed 2418 jobs
without warnings at 23:25:12 UTC. The read-only honesty review found the
producer route substantive, including the degree-zero power. Positive degree,
rank divisibility and rectangular regrouping are separate; no canonical
contraction nonvanishing follows from this result alone. The expanded axiom
audit and corresponding completion marker follow in the next checked batch.

`Geometry/DegreeDivisibility.lean` constructs the actual special-linear scalar
transformations and uses nonzero homogeneous evaluation to prove both target
ranks divide the Hom invariant degree. Its Pluecker consumer proves that the
pulled-back degree is positive and divisible by the source and both target
ranks. Primitive-root existence is supplied by unchanged Mathlib over
algebraically closed characteristic-zero fields; the one-factor results only
need the corresponding roots of unity and positive rank.

- Module `b5d63bf8466120d2` passed 3054 jobs without warnings at 23:29:54 UTC.
- The combined 226-probe audit passed at 23:30:45 UTC (`ffefd7bf352d83dc`),
  with only the three standard foundational axioms. The complete log is
  `session0016/plucker-divisibility-axioms.log`. LSP is clean; no kernel check
  in the Pluecker/divisibility batch failed.
- The read-only honesty reviewer approved the actual scalar/invariance route
  and both new nodes; its blueprint dependency and explicit positive-degree
  corollary corrections were applied. The limited polarization and divisibility
  nodes are now checked. No new external code was copied.

The next local producer is the canonical regrouping of the Hom-dual invariant
tensor into the independent factor tensor powers, with evaluation compatibility.
Rectangular invariant spanning and the coaction base-change bridge remain open;
I-0070 proposes a smaller Schur-Weyl extraction for independent mathematical
review. No source theorem completion is inferred from these producers.


## Rectangular invariant spanning via the checked permutation commutant

I-0070 authorized the bounded, mathematically reviewed TauCeti extraction at
`b3b0334ab9203d9faee4b2f34cd75161463ecdd0`. Original files, Apache-2.0 notices,
hashes, exact declaration mappings and adaptations are preserved under
`vendor/tauceti-schur-weyl/`. The source snapshot and complete route were
committed at `26489ca`; this commit alone was not proof evidence. No dependencies
or pinned toolchains changed. The project reuses its existing finite-projective
`piTensorHomEquiv` from Mathlib PR44845 rather than importing TauCeti's Hom API.

The seven selected modules prove pure-power spanning, the permutation
commutant over finite projective modules, the image-level double centralizer,
and invertible diagonal density. `Geometry/RectangularCovector.lean` constructs
the actual bilinear covector, proves transpose covariance over every commutative
ring, and casts SPECHT's exact integer square sum to obtain `(a!)^k`.
`RectangularSpan.lean` applies Schur-Weyl to its actual rank-one operator and
uses `freeLatticeMap_reindex` to obtain membership in the scalar-extended
integral lattice. `RectangularInvariants.lean` proves the SL-to-GL determinant
weight by a nonzero determinant root, and proves both directions of actual
SL-fixed-space identification over algebraically closed characteristic-zero
fields with positive rank and positive column count. The tableau supplies
`n = a*k`; no invariant-space equality is assumed.

Checks (all explicit workspace-root, shared serialized slot):

- `Centralizer` plus `RectangularCovector`: `ce89f54ede192c68`, 9,071 jobs,
  passed warning-free at 2026-11-05 23:42:55 UTC.
- `SchurWeyl`: `ef26df9b15681f3a`, 2,378 jobs, passed warning-free at 23:43:45.
- `RectangularSpan`: `866b8abcaf5afdec`, 9,075 jobs, passed warning-free at 23:46:46.
- `RectangularInvariants`: `07f7559ab37fb3d2`, 9,076 jobs, passed warning-free
  at 23:53:11.
- The expanded `GeometryAxioms.lean` audit passed at 23:53:39
  (`ffefd7bf352d83dc`), all **254** transitive probes using only `propext`,
  `Classical.choice`, and `Quot.sound`. Full log:
  `session0016/schur-weyl-axioms.log`. No `sorryAx` or custom axiom occurs.
- Initial port checks exposed a factorial-notation scope issue, an invariant
  predicate unfolding and a projective-Hom simplification; all were repaired.
  Some LSP files retained stale import state, so fresh standalone LSP snippets
  and narrow serialized kernel checks were used. Final source is warning-free.

Independent read-only source review verified all 14 preserved originals against
raw files at the exact revision and approved the projective comparison,
image-level centralizer, concrete rank-one consumer and final SL endpoint.
The required honesty review found no certificate, vacuity or discarded-producer
route. Its explicit-field and blueprint dependency-reference corrections were
applied. Six limited nodes now carry checked completion markers.

The canonical nonzero contraction is still open: the Hom-dual tensor must be
regrouped with equivariance and evaluation compatibility, and the factor
invariants transported into these lattice images. Arbitrary-field descent and
actual coaction base-change are separate pending obligations (BALANCED owns the
coaction producer). No geometric slope inequality or manuscript Theorem1.1 is
claimed. Shared integration of this extraction follows parent activation in
I-0073; the earlier root check covers only the Pluecker/divisibility batch.


## Finite-projective Hom-dual regrouping and first shared integration

`Tensor/HomDual.lean` composes unchanged Mathlib reflexive duality,
`dualTensorHomEquiv` and binary tensor duality with the project's finite tensor
distribution. It proves the actual formula `(v ⊗ ell)(A) = ell(A v)`, independent
source/dual-target pullback, and equality with the existing tensor-power pairing.
The hypotheses are finite projectivity over a commutative ring, with no free
frame. The Hom evaluation uses the canonical `PiTensorProduct.dualDistrib` map;
the pairing on the target still uses the checked projective dual equivalence.

`Geometry/HomTensor.lean` consumes this construction in the actual polynomial
quotient. Its inverse regrouping preserves nonzero evaluation and all specified
source/target pullback invariances. It does not assert that the regrouped tensor
already belongs to the determinant-factor subspace.

- HomDual module `b2b137b54d3071c3` passed1,733jobs at2026-11-06 00:06:45UTC.
- The configured root `975bdb23135a0d4a` passed9,279jobs without warnings at
  00:10:13UTC, explicitly compiling HomTensor, the delivered HermitianHN and
  the root. Root blob `2cb9cf57010e30bd8da24f89e3455668d65dd18e`;
  HomDual blob `235dbe3dbba28d5a5a6f89aefd551ce1f62ee8d0`;
  HomTensor blob `f1d375e2a29f65783402e255c9950af981305975`.
- All264 GeometryAxioms probes passed at00:11:39UTC (`ffefd7bf352d83dc`),
  only `propext`, `Classical.choice`, `Quot.sound`; full log
  `session0016/hom-regroup-axioms.log`. Initial LSP constructor/implicit-argument
  and scalar-normalization errors were repaired; no failing kernel check in
  this Hom-regroup batch.
- Required honesty review approved actual producer consumption, finite
  projectivity and the canonical inverse image. Its tensor-regrouping blueprint
  dependency correction was applied. Both limited nodes are now checked.

Parent protection I-0074 transferred shared integration to GEOM after SPECHT
completion. The root now imports the checked rectangular cone and HomTensor,
and ARITH's delivered `HermitianHN` (`fb56e97`,287 owner probes). CONTRIBUTIONS
records the complete Schur-Weyl extraction and actual consumers. The shared
blueprint includes the migrated complex_closure chapter; its two nodes remain
notready. Graph sync after that include has no missing dependency references;
unattached helper/import declarations remain intentional coverage warnings.
The scratch-cleanup dry run found no stale candidates.

Next: use independent-factor invariants to restrict the regrouped tensor to
the actual rectangular images. InvariantDetection arrived after this root
boundary (I-0076) and is awaiting its next checked integration; actual coaction
base-change remains BALANCED's producer. Full BOST-GEOM is still incomplete.

## Independent invariant pairing and source rectangular restriction

`Geometry/HomInvariants.lean` constructs the tensor-power representation from
`PiTensorProduct.map`. `exists_independent_invariant_pairing` consumes the
actual normalized polynomial lift, Hom-dual regrouping and independent
invariant-space theorem to obtain source SL-fixed and dual-target G-fixed
factors with nonzero canonical tensor-power pairing. Its consumer
`exists_rectangular_invariant_pairing` restricts the source factor to the
actual scalar-extended rectangular integral lattice over an algebraically
closed characteristic-zero field. No invariant equality is an input.

The configured explicit-root check passed **9,296 jobs warning-free** at
**2026-11-06 00:32:42 UTC** (`975bdb23135a0d4a`). Root blob:
`57ed74cb5b71c6c523cf463905883c06c310d36e`; HomInvariants blob:
`efb3626845d8669a816ac494fedff25ca6211030`.
All **267 transitive geometry probes** passed at **00:33:38 UTC**
(`ffefd7bf352d83dc`), only `propext`, `Classical.choice`, `Quot.sound`.
Logs: session0016 `independent-root.log`, `independent-axioms.log`.
Independent honesty review accepted the actual producer use and boundaries.
The two matching blueprint nodes alone are marked checked.

Initial elaboration failed at an inherited indexed-tensor additive-group
instance path, including narrow check `6c1bb9cde7291d8c`. The repair constructs
the existing tensor monoid's group by `Module.addCommMonoidToAddCommGroup`;
no higher heartbeat limit remains. The failed diagnostic log is retained as
`hom-invariants-elaboration.log`. Final source LSP is clear; root/audit LSP
reported stale imports and the serialized kernel checks above settled them.
The graph command rejects `sync --json`; the corrected plain sync is used.

The full dual-target rectangular restriction, nonzero canonical determinant
pairing, field descent and coaction square remain open. This is a proved
producer milestone, not BOST-GEOM or Theorem1.1 completion.

## Independent dual factors through projective regrouping

`Tensor/DualRegroup.lean` proves actual duality/regrouping naturality for
arbitrary factor endomorphisms over commutative rings and finite projective
modules. Its consumer `Geometry/DualInvariants.lean` transports actual
ambient dual fixedness to the tensor of individual contragredient fixed
subspaces, then consumes the invariant Hom pairing to select a pure family
with nonzero evaluation. Empty factor index and degree zero are covered.

Scoped checks: DualRegroup **1,733 jobs** at00:37:40UTC (`99db6d55ce044a37`);
DualInvariants **9,094 jobs** at00:40:29UTC (`7a0c36f251e4eb40`). Both warning-free.
The configured explicit-root build passed **9,299 jobs warning-free** at
**2026-11-06 00:43:05UTC**, `975bdb23135a0d4a`; all **273 transitive probes**
passed **00:44:00UTC**, `ffefd7bf352d83dc`, foundational-only. Root blob:
`ab1b101156ac69d996273b529949f5d22dbae8e1`; DualRegroup blob:
`566476ac3357aa4f6bf0431840f99b396ac07fa9`; DualInvariants blob:
`97b05e34803937d2b0414215bd67d3706ed524f4`. Owner source checkpoint: `ef59449`.
Logs are session0016 `dual-regroup-naturality.log`, `dual-invariants.log`,
`dual-final-root.log` and `dual-final-axioms.log`.

Independent honesty review accepted the actual producer route and degenerate
cases; its correction to bind degree d in the blueprint is applied. Initial
LSP issues were an inherited tensor group instance path and induction retaining
hypotheses depending on the induction variable; both are repaired. The two
producer nodes alone are checked. The individual dual-factor rectangular
restriction, full canonical determinant pairing nonvanishing and field descent
remain subsequent obligations.


## Actual canonical determinant contraction is nonzero

`DualSpecialLinear.lean` proves transpose surjectivity using the canonical
finite-dimensional double-dual evaluation equivalence. `Nonvanishing.lean`
identifies the glued determinant map in a global frame, proves its range is
the rectangular lattice image, and consumes independently invariant factors
to prove `canonicalPairing_ne_zero_of_invariant`. This is the existing
integral determinant contraction, not a newly assumed pairing. The input is
an actual homogeneous invariant Hom polynomial nonzero at A, over an
algebraically closed characteristic-zero field, at a common positive
rectangular degree.

DualSpecialLinear passed 9,077 jobs at 00:49:51 UTC
(`4efac1b9e1a1f6e9`); Nonvanishing passed 9,107 jobs at 00:59:11 UTC
(`669d2de5ef8622e4`). The configured explicit-root build passed **9,307 jobs
warning-free at 2026-11-06 01:00:22 UTC** (`975bdb23135a0d4a`). Root blob:
`3df1683a4e20af6eb4aa70c9461018efa69928cd`; DualSpecialLinear blob:
`6c246b3bee3b46048ae9a48b5e97d4932276048d`; Nonvanishing blob:
`39ed2b0d847eba913fa3d3d0cffec73174222f80`. All **280 geometry probes** passed
01:00:31 UTC (`ffefd7bf352d83dc`), foundational-only. Logs: session0016
`canonical-nonvanishing.log`, `nonvanishing-root.log`, `nonvanishing-axioms.log`.
Independent honesty review inspected the actual consumer chain and check logs
and found no defect. The two matching nodes are marked checked.

Initial LSP repairs removed a duplicate local instance name and simplified
the actual contragredient action. Final source diagnostics are clear; stale
root-import LSP diagnostics are superseded by the serialized build. No new
mathematical axiom or sorry is used. Field descent, invariant existence and
the full nonvanishing sequence remain open; the next descent node is notready.


## Nonvanishing descends to the original coefficient ring

`NonvanishingBaseChange.lean` proves
`canonicalPairing_ne_zero_of_scalarExtension` using the actual canonical
base-change formula and the bijective determinant-source transports. The
algebra itself need not be flat, faithful or free. Its substantive consumer
`canonicalPairing_ne_zero_of_baseChange_invariant` applies the checked
algebraically closed invariant-polynomial theorem to the actual extended
map, then detects the original finite-projective pairing. No invariant
coaction square is assumed by this argument.

The existing `dualDeterminantTensorBaseChange_bijective` producer was moved
from ContractionNorm to ContractionBaseChange at `7bb83ed`, removing a
briefly duplicated draft and avoiding a metric import in the new algebraic
consumer. The metric consumer still passed 9,108 jobs warning-free at
01:12:30 UTC (`edec714a5cf09fb0`). The new module passed 9,116 jobs at
01:19:09 UTC (`d401a25e94740386`). After making four local instance names
explicit, the configured root passed **9,319 jobs warning-free at
2026-11-06 01:24:35 UTC**; root blob
`0c98b66b943e39603586e66a8cca5754e37a7722`. Source blob:
`cad0b76cfd9fca8b1f1c68695cb05f57ae099910`. All **282 geometry probes** passed
01:25:08 UTC, only standard foundational axioms. Final logs: session0016
`descent-final-root.log`, `descent-final-axioms.log`.

Failed elaboration attempts are retained in `nonvanishing-descent-elaboration.log`
and `nonvanishing-descent.log`: deep definitional transport matching needed
scoped 800,000 heartbeats and recursion depth 2,048; no proof assumption was
added. The earlier combined root/audit (`descent-root.log`,
`descent-axioms.log`) exposed anonymous-local-instance name collisions with
ContractionNorm. Explicit local names repaired those collisions before the
successful checks above. Source LSP is clear. Independent honesty review
accepted the actual descent argument and consumer; its group and free-fiber
wording corrections are applied. Full invariant existence and the positive
Plucker-power sequence are subsequent obligations at this checkpoint.


## Actual Plucker-power nonvanishing sequence

`PluckerNonvanishing.lean` proves
`canonicalPairing_ne_zero_of_plucker_invariant` by feeding actual Plucker
pullback powers to the original-ring descent theorem. Its consumer
`exists_canonicalPairing_nonzero_sequence` constructs
`d0 = s * m * product(a_i)`, proves positivity and divisibility, and supplies
positive exponents and actual reindexed row-reading tableaux for every
positive multiple. It proves the existing original-ring canonical pairing
is nonzero for these concrete parameters. Empty factor index sets are covered.
This deliberately enlarges the manuscript degree; minimality is unnecessary.

The scoped check passed **9,119 jobs warning-free at 01:28:05 UTC**
(`3bae47e9a4e3ea56`). Configured root passed **9,320 jobs warning-free at
2026-11-06 01:29:03 UTC**, blob
`4914b5ec1e5b7c87b1d3f150f640ec46f576f67e`. Source blob:
`79c6e47dc0126f826424cff5ff4377a7cc222e22`. All **284 transitive geometry
probes** passed01:29:08 UTC, only standard foundational axioms. Independent
honesty review inspected the source, manuscript page0010, blueprint and
exact logs, accepting substantive producer use and the empty case. Only
these two precise nodes and the previously reviewed descent node are checked.
Logs: session0016 `plucker-sequence-final.log`, `plucker-sequence-root.log`,
`plucker-sequence-axioms.log`. The initial `plucker-sequence.log` check failed
on two incorrectly named Nat positivity lemmas; both are repaired. Guarded
source LSP and the final expanded axiom-file LSP are clear.

The next root adds the owner-audited PolynomialAverage delivery `6db192a`:
**9,321 jobs warning-free at01:31:01 UTC**, root blob
`dfd710441a44451a4d31b9abbd1a6f383707b6e5` (`polynomial-average-root.log`).
Its delivered185-probe evidence remains owner-scoped. No task-wide completion
follows: actual coaction scalar-extension compatibility is deferred under
I-0079; the binary BALANCED invariant/origin-exclusion connection and the
geometric slope consumer remain separate. The latter is outside BOST-GEOM.

Health checkpoint: no stale scratch candidates. Reviewed active-count and
unattached-helper warnings remain intentional. I-0084 explains costly global
Horizon search refreshes; guarded local/semantic lookup is used between edits.
I-0087 activates the disjoint restriction-covolume successor: its complete
blueprint slice is included immediately after arithmetic, retaining the
original label and unproved status. No covolume Lean draft is imported.


## Binary action transport: final bounded checkpoint

`Tensor/TwoFactors.lean` composes Mathlib sum-index and singleton equivalences
and proves actual map naturality. `Geometry/BinaryPlucker.lean` now contains
only actual SL intertwining, homogeneous Plucker-invariant pullback, and exact
evaluation transport. The independent honesty/source review accepted this
producer and corrected its blueprint dependencies to the actual action and
polynomial nodes. Only `lem:two-factor-plucker-transport` is marked checked.

Serialized explicit-root evidence in run0005/session0016:

- `two-factors.log`: 1,248 jobs, 01:47:24 UTC, fingerprint c7477425fb351a36.
- `binary-transport-final.log`: 9,121 jobs, 02:24:13 UTC, fingerprint
  09af99536a6e3a1e; source blob f488e28c1deac156ec25dd41cf01241c6753f516.
- `transport-boundary-root.log`: 9,334 jobs, 02:25:14 UTC, root blob
  f6a81998382d2af5857b8617406402410857ae34.
- `transport-boundary-axioms.log`: 290 probes, 02:25:19 UTC, only
  propext/Classical.choice/Quot.sound, including all six new declarations.

The terminal theorem `exists_canonicalPairing_nonzero_sequence_of_binary_invariant`
is NOT in accepted source. Its complete attempted source and exact failed
kernel output are preserved in this session's
`attempts/0001-terminal-binary-consumer-reaches-closed-tactic-g/`.
`binary-plucker-elaboration.log` failed at 02:21:06 UTC after 131 seconds
of module work with a deterministic whnf heartbeat timeout (200000).
The tactics reached closed goals, which was insufficient evidence. Higher
heartbeat attempts, scoped transparency, explicit arguments and disabled
unused-section-variable lint did not establish a checked declaration.
Those diagnostic settings are absent from the accepted prefix.

Read-only definition/API review identified the generic versus scalar-extended
tensor group instance heads as a plausible definitional-conversion seam;
causality is not proved. Selective unfolding made no progress. The next round
should isolate that interface in the preserved consumer and use the checked
transport producer, without introducing an assumed comparison or a new
representation. `lem:binary-plucker-nonzero-sequence` stays notready.

I-0097 reconciles the construction objective: this binary terminal consumer
is the remaining GEOM requirement. The unused general coaction base-change
square is retired from the route, not proved. I-0095 keeps GEOM as sole shared
integrator across rounds. At 1e56d1d the complete determinant-Specht/slope and
arithmetic compactness blueprint slices were migrated to the two successor
owners; those files must no longer be edited by GEOM.

Shared accepted deliveries are cf39176 (exact Lemma7.2 and arithmetic
finiteness, root9329, owner195/366 probes) and 039cdb2 (actual trace lattice,
weighted metric, Haar Gram formula and rank0 endpoint, root9332, owner24
probes). Pending next-round integration: COVOLUME FiniteIndex (e4b0d01/fc5e712,
30 probes at02:00:46) and Free (d41ef38,39 probes at02:22:12, final review
handoff in I-0092), plus SPECHT-SLOPE's representation/latticeMetric delivery
in I-0098. None is silently certified by the current root.

The parent requested a normal round boundary in I-0097 to release duplicate
session LSP trees under memory pressure; no process was killed. GEOM remains
active, not done or blocked. Scratch cleanup found no stale candidates.
The graph's unattached-helper coverage warning is the previously recorded
intentional warning, not a mathematical completion statement.

Finalization retry: the accepted graph snapshot contains 318 blueprint nodes,
2,126 declarations and 1,639 edges, with no missing-reference warning; the
1,008 unattached declarations remain the documented helper-coverage warning.
All GEOM-owned source was already committed at e771072. Remaining dirty paths
belong to concurrent arithmetic lanes or pre-existing workspace inputs and
were excluded from this checkpoint.

The new I-0098 handoff 1eb4f44 delivers `Arithmetic.Specht.DeterminantBundle`
(preceded by f7155b5, e869a94 and 4480ac7). Its owner reports 9,180 checked
jobs, 16 foundational-only probes and independent honesty/source acceptance
for the actual determinant metric, every-fiber Gram comparison and tensor/dual
semistability. GEOM acknowledged this for next-round root integration; it is
not included in the 9,334-job root evidence above. Exact and geometric slopes
remain the successor's obligations. This finalization adds no Lean claim.


## Terminal binary sequence verified — session 0018

The terminal `exists_canonicalPairing_nonzero_sequence_of_binary_invariant`
now kernel-checks at source blob `ae575df89d7dbf17b767bec176ec4b9cc9f7aa7b`.
The explicit-root `check BostConjecture.Geometry.BinaryPlucker` passed 9,121
jobs without warnings at 2026-11-06 02:53:11 UTC; the exact output is
run0005/session0018 `binary-terminal.log` (fingerprint `09af99536a6e3a1e`).
The scoped unused-section-variable linter is disabled for this declaration;
all mathematical hypotheses remain, and the kernel uses the default heartbeat
budget. No additional axiom, representation or assumed comparison was added.

The failed 800,000-heartbeat diagnostic probe is preserved in this session's
`attempts/0001-terminal-binary-consumer-still-times-out-at-whnf/` and
`binary-diagnostics.log`. Explicitly typing the pullback polynomial and applying
the finite-family sequence theorem isolated the expensive step to evaluation.
Replacing the costly specialized rewrite with the basic polynomial-pullback
and exterior-map evaluation identities gave the checked proof. Guarded LSP
reported no diagnostics for the final source. Removing the scoped linter setting
caused a long-running diagnostic probe; restoring it returned clean diagnostics.
Root/audit documents reported stale imports before the module rebuild, so their
faithful evidence comes from the serialized checks.

The independent read-only honesty/source review found the terminal theorem
faithful to revised I-0097 and no further construction gap within that scope.
It uses actual independent SL-action transport and concludes nonvanishing of
the original-ring canonical pairing at all positive multiples of one degree.
The geometric slope inequality, downstream balanced-invariant application and
number-field main theorem remain separate obligations. General coaction
scalar-extension equality remains deferred, not proved.
