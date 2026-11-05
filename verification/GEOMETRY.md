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
  in this session failed.
- The read-only honesty reviewer approved the actual scalar/invariance route
  and both new nodes; its blueprint dependency and explicit positive-degree
  corollary corrections were applied. The limited polarization and divisibility
  nodes are now checked. No new external code was copied.

The next local producer is the canonical regrouping of the Hom-dual invariant
tensor into the independent factor tensor powers, with evaluation compatibility.
Rectangular invariant spanning and the coaction base-change bridge remain open;
I-0070 proposes a smaller Schur-Weyl extraction for independent mathematical
review. No source theorem completion is inferred from these producers.
