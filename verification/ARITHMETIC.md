# Arithmetic verification

## Intrinsic Hermitian line degree

`BostConjecture.Arithmetic.HermitianLine` now constructs normalized degree on
every finite projective rank-one module over the ring of integers of an
arbitrary number field. The module need not be free. `HermitianMetric` gives
positive Hermitian forms on the actual complex scalar extensions, with
conjugation compatibility on integral generators. Its fields contain no
degree or calculus assumptions.

The proof uses an injective generic coordinate, its actual fractional image
ideal, and the supplied fiber norms. The product formula proves independence
of the coordinate and the nonzero integral section. The fractional-ideal
index theorem identifies the actual quotient cardinality with the ideal-norm
ratio and proves quotient finiteness separately. The final exports are:

- `HermitianMetric.lineDegree_eq_degreeInCoordinate`: independence of choices.
- `line_quotient_finite`: finiteness of the quotient by a nonzero section.
- `HermitianMetric.lineDegree_eq` and `lineDegree_eq_sum_embeddings`: the
  manuscript's normalized quotient formula, respectively indexed by weighted
  infinite places and by all complex embeddings.

The coordinate-ideal, product-formula, metric-homogeneity and lattice-index
producers are all consumed by these intrinsic formulas. There is no custom
axiom, `sorry`, certificate assumption, or new external code copy. Mathlib
and project dependencies retain their existing pinned revisions.

## Accepted source and kernel evidence

Checks were run through the shared serialized slot with explicit workspace
root. Command fingerprints identify commands, not immutable source versions.

| Target | Fingerprint | Accepted completion (UTC) | Result |
| --- | --- | --- | --- |
| `BostConjecture.Arithmetic.HermitianLine` | `3fdba1ac3c1bde52` | 2026-11-05 16:06:26.047228 | 3100 jobs, passed, not reused |
| `verification/ArithmeticAxioms.lean` | `590174f2cda53d26` | 2026-11-05 16:07:42.919731 | 22 transitive axiom probes, passed |

All probes report only the standard foundational axioms `propext`,
`Classical.choice`, and `Quot.sound`; none reports `sorryAx` or an additional
axiom. Reproduction commands, from this member project:

```sh
"$HORIZON_BIN" --root /home/yijunyuan/bc-workspace check BostConjecture.Arithmetic.HermitianLine --json
"$HORIZON_BIN" --root /home/yijunyuan/bc-workspace check --lean verification/ArithmeticAxioms.lean --json
```

No arithmetic Lean edit followed the accepted module build. The automatic
workspace boundary snapshot `82de93e` captured the final source before the
explicit arithmetic commit could run. Its relevant Git blobs are:

| File | Blob |
| --- | --- |
| `Arithmetic/Hermitian.lean` | `8f194a7046c4f4982da89716ae01e10330ef5058` |
| `Arithmetic/LineDegree.lean` | `f08dddedc63f03a4f52ebf55b55b89420b243352` |
| `Arithmetic/LineCoordinates.lean` | `023ea919ccbb4a6b92b6a5a8d9f4947701ea8036` |
| `Arithmetic/FractionalIdealIndex.lean` | `6cb05519a2d4fc47d2cb306ecdc17df2ac2d5ecf` |
| `Arithmetic/HermitianLine.lean` | `876a7deef6cd814540aea639e49c3b5d6e3fb5ea` |
| `verification/ArithmeticAxioms.lean` | `d44333198ea1e9f123fbaf424e74439cc25232f0` |

The snapshot itself is not proof evidence for other tasks' files. Earlier
explicit arithmetic units are `1cb3dfa`, `cd244d4`, and `53c6e00`.

The earlier failed `FractionalIdealIndex` check at 15:59:19 and
`HermitianLine` check at 16:01:58 were development checks. The finite-quotient
proof was repaired and its module rebuilt as a dependency; the final remaining
doc-comment syntax error was then repaired before the accepted build above.
Slow LSP elaboration was not treated as successful verification.

## Review of the line-degree construction

Read-only honesty reviews checked the actual module/fiber representation,
the product-formula cancellation, nonfree coordinate comparison, genuine
quotient index and finiteness, and final intrinsic consumers. An initially
missing representative-independence theorem was supplied as
`sectionNorm_eq_of_place_eq`. No substantive defect remained in the reviewed
line-degree unit. Only the corresponding rank-one blueprint nodes are marked
checked.

## Integral determinant line

`Arithmetic/DeterminantLine.lean` proves exterior projectivity from an actual
finite-free splitting and uses Mathlib's exterior finiteness instance. Its
`DeterminantLine` is the top exterior power at the generic rank. The canonical
generic and complex base-change equivalences identify the fibers, prove they
have dimension one, and identify integral wedges with fiber wedges. Rank zero
is included. No freeness hypothesis is imposed on the original module.

The final warning-free module check `62776c8f61c41cfa` passed 3134 jobs at
2026-11-05 16:23:44.549726 UTC. The expanded 29-probe axiom audit
`590174f2cda53d26` passed at 16:25:42.794952 UTC, with only the same three
foundational axioms. Source was captured in boundary snapshot `0dd8464`;
explicit commit `ad2ea7e` records the extended axiom audit. The read-only
honesty review verified both the source and the accepted checks, and approved
the `lem:integral-determinant-line` attachment. The complex determinant metric
is a separate subsequent producer.

SPECHT reported integration of `HermitianLine` into the configured root build:
9113 jobs passed at 16:19:14 UTC, fingerprint `975bdb23135a0d4a`. This report
does not extend that root evidence to subsequent determinant sources.

## Remaining boundary

The full conjugate-linear fiber map and real fixed-fiber identification remain
an explicit unchecked equivalence lemma. Determinant-metric uniqueness,
frame independence, and normalization in ranks zero and one are now proved;
their new evidence is recorded below.

Dual/tensor/exact-sequence identities,
higher-rank contraction and saturation inequalities, degree finiteness/supermodularity,
and the actual HN specialization remain open. The existing abstract slope
bridge does not close them. No main-theorem completion or whole-project
verification claim follows from these arithmetic checks.

## Complex determinant metric and its degree consumer

`Arithmetic/DeterminantMetric.lean` constructs the complex determinant form
from the supplied `HermitianMetric.fiber` by taking its orthonormal frame and
transporting the scalar inner product through the top-wedge coordinate. It
proves the cross-Gram determinant formula for **arbitrary complex fiber
wedges** in `determinantFiber_inner_ιMulti`, then consumes that formula on
integral wedges. Two-variable span induction proves conjugation compatibility
on every integral determinant section. `determinant` packages these proved
forms as the intrinsic determinant metric; it assumes no degree identities.
Rank zero is supported by the empty determinant construction.

`Arithmetic/Degree.lean` defines `HermitianMetric.degree` and `slope`.
`degree_eq` applies the previously proved intrinsic line-degree formula to
this actual metrized determinant line, with the actual finite quotient and
all complex embeddings. `determinant_quotient_finite` proves the finiteness
appearing in that formula. Both the metric construction and the degree
consumer support nonfree finite projective modules over arbitrary number
fields.

The shared geometry equivalence is reused from the lightweight
`Geometry/DeterminantCoordinates.lean`, extracted by BOST-GEOM in `d470bdb`.
There is no duplicate determinant coordinate. This import reduces the
arithmetic degree build from 9072 to 3241 jobs and avoids the Specht cone.

| Final target | Fingerprint | Completion (UTC) | Result |
| --- | --- | --- | --- |
| `BostConjecture.Arithmetic.Degree` | `ea82f359ff103b59` | 2026-11-05 16:49:19.045342 | 3241 jobs, passed, no warnings, not reused |
| `verification/ArithmeticAxioms.lean` | `590174f2cda53d26` | 2026-11-05 16:50:53.589750 | 40 probes, all standard foundational axioms only |

The checked implementation is in explicit commits `6429efa` and `5d59bb0`;
no Lean source edit followed the final module pass. Reproduce with the same
explicit-root commands above, replacing the module target by
`BostConjecture.Arithmetic.Degree`.

The intermediate metric file check at 16:35 failed on star rewrite names
and an underconstrained positivity argument; both were repaired. The later
16:46 Degree check failed on the final definitional-equality step in the new
complex-wedge consumer. The explicit reflexivity step repaired that failure,
and the 16:49 build above checks the entire final dependency cone. These
failed development records do not supersede the later accepted pass.

Read-only honesty review found that the original metric is used substantively,
conjugation covers all determinant sections, and the degree consumer invokes
the real line-degree construction. The blueprint splits the checked metric
construction from its still-unchecked uniqueness theorem; it likewise keeps
zero normalization and the later calculus/HN boundary separate. The imported
Mathlib finiteness instance is recorded here rather than attached to a graph
restricted to project sources.

The final graph sync reported 101 blueprint nodes, 700 project declarations
and 386 generated edges, with no unresolved attachment warning. The 399
unattached imported/helper declarations remain an intentional shared-project
coverage warning; graph enumeration is not kernel evidence for concurrent
drafts. The nested active-roadmap count was independently reviewed and left
intact; only the three authorized proof lanes were used.

## Metric uniqueness, normalization and line contraction

The next checked units are `ComplexDeterminant.core_unique`, `core_eq`,
`HermitianMetric.determinantFiber_unique`, `lineDegree_eq_of_equiv`, the
rank-zero/rank-one determinant norms and degree identities in
`DegreeNormalization`, and `lineDegree_le_of_injective` in `LineContraction`.
The latter consumes `quotient_span_card_le`, an injection between the actual
quotients by a section. No integral freeness restriction is introduced.

- `Degree` rebuilt the uniqueness and line-isometry cone: 3241 jobs passed
  at 2026-11-05 17:12:19 UTC, `ea82f359ff103b59`.
- `DegreeNormalization` and `LineContraction`: 3243 jobs passed at 17:22:26 UTC,
  `65ae2276f8a202bb`. Unused-section-variable warnings were then removed;
  the final normalization file check `07045aa7357bebde` passed without warnings
  at 17:23:49 UTC.
- Read-only honesty review independently checked 11 new declarations at
  17:24:10 UTC (`3b98b72a68d94ccd`): only `propext`, `Classical.choice`, and
  `Quot.sound`. It approved the five corresponding scoped blueprint markers.

Source commits are `1fc05f9`, `a81126f`, and `b2fd0b0`; markers are in
`294498a`. The marker-edit command preceding `b2fd0b0` failed because it ran
from the workspace root; `294498a` supplied the promised attachments.
Intermediate normalization failures concerned exterior-degree transport and
an empty-determinant lemma application, repaired before the accepted checks.

## Actual induced submodule metrics

`SubmoduleMetric` defines the canonical complex `fiberMap`, proves its
injectivity by localization and transitivity of flatness, and constructs
`HermitianMetric.pullback` and `submodule`. `sectionNorm_pullback` and
`sectionNorm_submodule` prove equality with ambient section norms. The module
check `eeb89b7e1a75c44b` passed 3074 jobs at 2026-11-05 17:37:03 UTC.
The earlier file failure (missing explicit localization-flatness instance
and an unreduced conjugation field) was repaired before that pass.

Its source was captured by the concurrent automatic snapshot `a1924a2`
before the explicit source commit could run. That snapshot is cited only
for these independently checked arithmetic paths, not for other captured
files. The final submodule source (blob `b490dc4`) also proves finite
projectivity via Mathlib's Dedekind torsion-free/flat and finite-presentation
results; explicit source commit `9f613eb` records that addition.

`MetricScaling` (final blob `c703904`, explicit commit `64dd7e3`) constructs
uniformly scaled metrics, proves their determinant and intrinsic degree
formulas, and consumes these on actual submodules and to normalize slope
to zero. The determinant formula uses the newly proved metric uniqueness.
No degree identities are assumed as structure fields.

The final combined module check for `DegreeNormalization`, `LineContraction`,
and `MetricScaling` (including `SubmoduleMetric`) passed 3509 jobs without
warnings at 2026-11-05 17:46:25 UTC, fingerprint `95a6d06d50e391b6`.
The expanded 70-probe `ArithmeticAxioms.lean` check passed at 17:47:54 UTC,
`590174f2cda53d26`: only `propext`, `Classical.choice`, and `Quot.sound`.
The independent honesty reviewer inspected these exact source blobs and
accepted the three scoped blueprint nodes as honest partial progress.
Intermediate scaling failures involved explicit complex-real conversions and
projection elaboration in the Gram formula; all were repaired before these
accepted passes. The full calculus and HN boundary above remains open.

Lean LSP tools are unavailable in this session; serialized file checks are
the development fallback. The Lean-search MCP endpoint also points at the
member directory rather than the workspace root, so searches use explicit-root
Horizon CLI calls. Toolchain and dependencies are unchanged.


## Integral parts and intrinsic subspace degree

`IntegralSubspace` uses the canonical Mathlib tensor-localization instance,
localization Galois insertion, and `Submodule.toBaseChange.toLinearEquiv`.
It constructs the actual inverse image of a generic subspace and proves its
generic-fiber identification, rank, saturation criterion, saturated-submodule
recovery and projectivity of its quotient. Its final source blob is
`92b8319ff502fc2893735fef648c4e0c9896047f` (commits `ebede0f`, `3d4a629`).
The tensor-localization API was compared with BOST-GEOM in I-0029: both lanes
use Mathlib directly, with no new shared identification or ownership handoff.

`SubspaceDegree` defines degree using the actual induced metric on that
integral part. It proves zero normalization, the rank denominator, rescaling,
and the bottom-interval interpretation of the existing slope payoff. The
final blob is `8ca9e38a2463015de64efae09be6c1293d03d71d` (`4206a6d`).
This is a concrete degree producer, not a package assuming HN or convexity.

- Final `BostConjecture.Arithmetic.SubspaceDegree` build: 3520 jobs passed
  without warnings at 2026-11-05 18:03:32 UTC, `2e482a197f00b9e5`.
- Expanded 84-probe `verification/ArithmeticAxioms.lean` audit passed at
  18:05:12 UTC, `590174f2cda53d26`. Audit blob
  `b85e1bf4d5225dbb12f0ad07059995e26ec75b74`, commit `ecec46c`.
  Every probe uses only `propext`, `Classical.choice`, and `Quot.sound`.
- Read-only honesty review approved both scoped nodes against these source
  blobs and the accepted build; no duplicate check was launched.

Development checks failed on scalar-action elaboration, an explicit quotient
lemma argument, misplaced `omit`, and two namespaces; these were repaired
before the accepted build. There are no remaining broken arithmetic proofs
in this checked cone. The Lean LSP fallback described above remains in use.

The next producer is the canonical quotient metric: the blueprint now gives
its complete orthogonal-complement construction and compatibility with
induced metrics, kept `notready`. Full fiber conjugation precedes this
construction. Quotient-interval slope compatibility, higher-rank contraction,
saturation-degree monotonicity, dual/tensor/exact-sequence identities,
arithmetic finiteness, supermodularity and the HN filtration remain open.
The task has not been marked done and no main-theorem check is claimed.


The boundary graph sync recorded 120 blueprint nodes, 852 project declarations
and 500 generated edges, with no unresolved attachment warning. The 479
unattached helper/imported declarations remain an intentional shared-project
coverage warning, not a kernel-completion measure. The read-only janitor
review found the nine active roadmap rows to be intentional nested ancestors
of the three authorized proof lanes. New subspace work is recorded as a done
child while the remaining HN core and exact-sequence calculus stay unfinished.
Scratch cleanup found no stale candidates. I-0028 carries checked imports to
SPECHT; its next root integration result is still pending, so this report
claims only the arithmetic module checks specified above.


I-0030 assigns the generic finite complex tensor `InnerProductSpace.Core`
and pure-tensor pairing/regrouping formulas to GEOM's existing `Tensor/**`
lane. ARITH will consume them through the canonical complex scalar-extension
equivalence and prove conjugation and degree identities. No arithmetic tensor
metric is claimed checked, and no additional proof writer was launched.


## Full fiber conjugation, quotient metrics and finite tensor metrics (2026-11-05)

Claim class: **proved producers**. The inherited intrinsic representation is
unchanged. `fiberConjugate` is the canonical conjugate-linear equivalence and
`inner_conjugate` proves antiunitarity from compatibility on integral sections.
`ComplexQuotient.lift` constructs the orthogonal right inverse using Mathlib's
kernel quotient and complement equivalences. Its uniqueness proves
`fiberLift_conjugate`; this supplies the conjugation field of the constructed
`pushforward` and `quotient` metrics. No degree identities are assumed.
`ker_fiberMap_mkQ` identifies the actual submodule fiber, and
`quotientFiber_min` proves the attained distance formula there. Section
contraction and the core uniqueness formula are checked consumers.

`TensorMetric` consumes GEOM's checked `Tensor.baseChangeEquiv` and
`Tensor.hilbertCore` on the existing `ComplexFiber`. It constructs the actual
finite integral tensor metric, proves conjugation on all integral tensor
sections, and proves the integral pure-tensor pairing and norm formulas,
including the empty family. No integral freeness assumption is added.
The blueprint tensor statement explicitly quantifies integral factor sections;
it does not label an unexported arbitrary-complex-factor uniqueness theorem.

Accepted serialized checks (explicit workspace root on every invocation):

- `BostConjecture.Arithmetic.FiberConjugation`: 3338 jobs,
  `cf8191be68a4d703`, 18:28:03 UTC.
- `BostConjecture.Arithmetic.OrthogonalLift`: 2433 jobs,
  `edf793a3ea7dd4b6`, 18:29:22 UTC.
- Final combined `BostConjecture.Arithmetic.QuotientMetric
  BostConjecture.Arithmetic.TensorMetric`: 3452 jobs,
  `a9a6a8914330d729`, 18:48:33 UTC.
- Final `--lean verification/ArithmeticAxioms.lean`: **107 probes**,
  `590174f2cda53d26`, 18:49:24 UTC. Every probe reports only `propext`,
  `Classical.choice`, and `Quot.sound`; no `sorryAx` or additional axiom.

Final checked source blobs:

- `BostConjecture/Arithmetic/FiberConjugation.lean`: `39ebdb64cf567c2bf450bc97e9adaf8fc19032c9`.
- `BostConjecture/Arithmetic/OrthogonalLift.lean`: `0e760223da30f518a71a1a65666593f3664a108e`.
- `BostConjecture/Arithmetic/QuotientMetric.lean`: `92925620f1c6320443e712e600ee3b989a119f9a`.
- `BostConjecture/Arithmetic/TensorMetric.lean`: `53064c0a5ca51898e95053f8b5bb47a9c8946ce5`.
- `verification/ArithmeticAxioms.lean`: `5cf8b2557efe1c6ce7b3fdf43a40d9037a8b99f0`.

The combined check at 18:44:17 UTC (`9ccf9fba86c6b2a9`) failed on the new
quotient distance corollary: simplifying a dependent equality obscured its
metric instance. Direct rewriting followed by `exact` repaired it; the final
combined pass above supersedes that failure. Earlier LSP errors in conjugation
and tensor proofs were repaired. LSP was available during most proof work; it
briefly failed to load the concurrently edited Hilbert dependency, so the
serialized check settled that interface. No remaining broken proof is claimed
within the checked arithmetic cone.

The frontier moved from full fiber conjugation/canonical quotient metrics to
nested quotient compatibility and the determinant dual/tensor/exact-sequence
degree identities. Higher-rank contraction, saturation-degree monotonicity,
arithmetic degree finiteness, supermodularity and actual HN remain open.
The next source-facing nodes are `lem:nested-quotient-metric` and
`lem:degree-calculus`, kept `notready`. No main-theorem or task completion
is claimed. Root integration remains owned by SPECHT through I-0028.

Graph sync: 128 blueprint nodes, 931 Lean declarations, 552 generated edges;
no unresolved attachment warning. The 517 unattached declarations are the
shared helper/imported-declaration coverage warning, intentionally retained.
Read-only janitor review confirmed that ten active roadmap rows represent
three live branches and their ancestors; HN stays pending. Scratch cleanup
found no stale candidates. I-0030's delivered tensor interface was acknowledged;
GEOM owns that thread's closure. Only owned paths are included in ARITH commits.

Honesty-reviewer was used and rechecked the repaired quotient, tensor and
blueprint deltas: verdict **satisfactory, honest partial progress**. It
independently inspected the recorded 107-probe audit, found no certificate,
vacuity or target-shaped assumptions, and confirmed that the scoped completion
markers match the actual metric producers. Its requested tensor wording and
dependency corrections were applied before this report.

SPECHT subsequently confirmed the earlier arithmetic imports (through
`SubspaceDegree`) in root commit `2072f12`, with a 9141-job root check at
18:42:11 UTC (`975bdb23135a0d4a`). That snapshot does not certify this round's
new metric imports; I-0028 now tracks only their remaining integration.

## Nested quotients, determinant contraction, tensor lines and dual fibers (session 0008)

Claim class: **proved producers**, with actual intrinsic arithmetic consumers.
This advances BOST-ARITH; it does not complete its degree calculus or HN objective.

- `OrthogonalLift` / `NestedQuotient`: naturality of the canonical orthogonal
  representative proves equality of the quotient-of-induced and
  induced-quotient metrics for nested integral submodules (`9321666`).
- `ExteriorMap` / `DeterminantContraction` / `SaturationDegree`: canonical
  exterior maps commute with scalar extension; injective fiber contractions
  contract **every complex determinant vector**. The intrinsic line-degree
  inequality then proves equal-rank degree monotonicity and actual saturation
  monotonicity (`b13c978`, strengthened in `d15ab3e`).
- `TensorCoordinate`: multiplication of actual integral coordinates is
  injective, its fractional ideal is the product ideal, and the finite
  logarithmic contribution is additive (`4f53c5a`).
- `BinaryTensorMetric` / `LineTensorDegree`: the binary metric pulls back the
  existing finite-family metric through canonical Mathlib equivalences. Its
  pure norm formula and the product-ideal producer both feed
  `degreeInCoordinate_tensor`, then rank-one determinant normalization proves
  `degree_tensor_of_rank_one` (`bdcafbc`). This covers nonfree projective lines
  over arbitrary number fields, not only rational or principal lines.
- `DualFiber`: Mathlib's finite-projective tensor--Hom equivalence and scalar
  extension adjunction prove bijectivity of the canonical dual base-change
  map. Its arithmetic specialization commutes with conjugation on arbitrary
  dual and original fiber vectors (`e3a7b48`). No integral basis is assumed.

All checks below ran with explicit workspace root and the shared serialized
slot. Times are 2026-11-05 UTC; fingerprints identify commands, so the finish
time distinguishes revised checks of the same command.

| Target | Final result | Finished | Fingerprint |
| --- | --- | --- | --- |
| `Arithmetic.NestedQuotient` | 3341 jobs, passed | 19:08:30.646874 | `f11f65a7fc29184d` |
| `Arithmetic.SaturationDegree` | 3512 jobs, passed | 19:30:41.708237 | `aaa1ccb1a7ef948d` |
| `Arithmetic.TensorCoordinate` | 3104 jobs, passed | 19:38:46.720761 | `dbaf90bd7087e71c` |
| `Arithmetic.BinaryTensorMetric` | 3450 jobs, passed | 19:43:46.155444 | `94052864d5cf1949` |
| `Arithmetic.LineTensorDegree` | 3516 jobs, passed | 19:46:29.409694 | `e5c14e80f15b60d1` |
| `Arithmetic.DualFiber` | 3344 jobs, passed | 19:55:00.665920 | `71e786e1c6fa94d7` |
| `--lean verification/ArithmeticAxioms.lean` | 135 probes, passed | 19:57:25.476725 | `590174f2cda53d26` |

These final module checks have no warnings. All 135 transitive axiom probes
report only `propext`, `Classical.choice` and `Quot.sound`; none reports
`sorryAx` or an additional axiom. Earlier 123- and 131-probe audits passed at
19:32:08 and 19:47:24 respectively. Records live in run 0004, session
`0008-horizon-BOST-ARITH`, under `checks/`.

Final source blobs:

| Source | Git blob |
| --- | --- |
| `OrthogonalLift.lean` | `df850f0cd33e083744a79631faccb3c905f461b0` |
| `NestedQuotient.lean` | `296e2501706c4e855282998d3e631e273b2d6662` |
| `ExteriorMap.lean` | `176270e2c80127cdb7ba73be603ad8034f764020` |
| `DeterminantContraction.lean` | `e9d2c2b58209dd9c4022c59591609e3662fba3e3` |
| `SaturationDegree.lean` | `3fb76afdf9046eebee682a461e0257d771b36603` |
| `TensorCoordinate.lean` | `62fb090d96f685bc961a8dabfd0d17ee70cc1a2d` |
| `BinaryTensorMetric.lean` | `4d416fe1f49099443e8831ab35475b8683610eaa` |
| `LineTensorDegree.lean` | `bbe1fe037b6366fabe9aaf6cb96b7732a0df5b75` |
| `DualFiber.lean` | `dfb576f308eb40c4068be50101f12f128747d3a5` |
| `ArithmeticAxioms.lean` | `5044ca87bacbde4cb15f6c18f62d358ca57755ba` |

Development failures were repaired: exterior fiber extensionality and coercion
errors, one premature axiom audit after a failed import build, fractional-ideal
coercion and `omit` placement, dependent binary-family reduction, and dual
base-change associativity/local-universe errors. The first line tensor check
had a `letI` style warning; its final check above is clean. No failed attempt
is being used as proof evidence. I-0034 prohibits this session's legacy LSP
client from building dependencies; all feedback after that protection used
serialized kernel checks, without artifact cleanup or configuration changes.

`BinaryTensorMetric.lean` and its accompanying blueprint prose were incidentally
captured in GEOM commit `eecbe72` during shared-index staging. The independent
ARITH check above preceded that commit. I-0039 records matching blobs and the
agreement to use explicit paths on `git commit --only`; no history rewrite or
source repair was needed. Other ARITH commits used explicit owned paths.

Honesty-reviewer was used for all new scoped completion claims and independently
inspected the recorded builds, audit output, proofs, consumers and blueprint.
Verdict: **satisfactory, honest partial progress**. Requested full-fiber wording,
proof alignment and dependency edges were repaired. The six new checked nodes
are nested quotient compatibility, determinant contraction, saturation degree,
tensor coefficient ideals, line tensor degree, and dual fiber base change.

The frontier is now the **actual arithmetic dual metric**, followed by the
dual, arbitrary-rank tensor and exact-sequence determinant isometries/degree
identities. `lem:arithmetic-dual-metric` has a complete mathematical proof but
remains `notready`. GEOM delivered the checked canonical algebraic dual Core
in `90d9c82` (I-0038); the arithmetic scalar-extension half is now checked and
was acknowledged in I-0040. Degree finiteness, supermodularity and actual HN
specialization remain open. No main-theorem completion is claimed.

Earlier metric imports were integrated by SPECHT in `75b41aa` (9148 jobs,
19:08:01 UTC); that is not evidence for this session's later leaves. I-0037
tracks the checked new integration batch. The prior graph synchronization
reported 150 blueprint nodes, 1054 Lean declarations and 672 edges, with no
unresolved attachment warning. Its 572 unattached helper declarations are a
coverage warning, not proof failure; the final graph count is recorded below.
Read-only operational review found the active roadmap rows to be nested
branches and ancestors of the three authorized writers. The current count
grew as concrete subgoals were split; no extra proof writer was spawned.
Scratch cleanup found no stale candidates and preserved all three live runs.

Final graph sync: **152 blueprint nodes, 1068 Lean declarations, 702 generated
edges**; no unresolved attachment warning. The remaining 565 unattached
declarations include low-level helpers and imported APIs; their coverage warning
is retained intentionally. The roadmap currently reports 13 active rows across
the nested live branches; the health review is not repeated for the same
collection warning. The mathematical completion markers apply only to the six
scoped proved nodes above. I-0040 is closed; I-0037 remains open for SPECHT's
pending root integration, including the final DualFiber leaf if feasible.

## Session 0010: intrinsic dual metric and arbitrary-rank dual degree

The actual integral dual now has a conjugation-compatible operator metric.
Its coefficient ideal in rank one is the inverse fractional ideal, and the
coordinate length is reciprocal. These two proved facts give rank-one dual
degree negation. Perfect exterior evaluation for finite projective modules,
proved by a finite-free summand argument, commutes with scalar extension.
The complex Gram determinant calculation then proves that the canonical
integral determinant-duality map is an isometry. Its section-norm consumer
feeds line-degree invariance and proves `HermitianMetric.degree_dual` and
`slope_dual` in every rank over every number field. There is no integral
freeness hypothesis; the determinant argument includes rank zero.

Checked source units: `ba2f037` (DualMetric), `0a78001` (DualCoordinate),
`fcf7f49` (LineDualDegree), `23ac7ae` (ExteriorDual), `49b13ce`
(DeterminantDual final proof), and `9869294` (axiom audit/blueprint).
Concurrent automatic boundary snapshots captured parts of ExteriorDual,
ComplexDualDeterminant, ExteriorDualBaseChange and DeterminantDual before
explicit arithmetic commits. Those snapshots are not evidence for other
lanes' drafts. The final arithmetic source blobs covered by the checks are:

| File | Blob |
| --- | --- |
| DualMetric.lean | `a3000bcbabd067fb199d6a2b3414cc7c8d4e4edd` |
| DualCoordinate.lean | `837ede69b59e825d16e447319ad691729d334cfe` |
| LineDualDegree.lean | `99a2bbe4be5c10900d3145ab9c4001f48932ef5f` |
| ExteriorDual.lean | `166f8f918b1f515019bbdd07f275fbc42fdb5e86` |
| ComplexDualDeterminant.lean | `705dcc68245bde6e64ba7a6e12390203020ff6e6` |
| ExteriorDualBaseChange.lean | `77d58e96e12b603e0e1fa4cb090a68e06e6956c7` |
| DeterminantDual.lean | `5cd635591d5cd8d1447f38ac774b3945dab2e1ea` |

All checks used the serialized command prefix
`"$HORIZON_BIN" --root /home/yijunyuan/bc-workspace check`.
The final `BostConjecture.Arithmetic.DeterminantDual` build passed **3525 jobs**
at 2026-11-05 20:39:30 UTC (fingerprint `a40a91a973f052f9`, 57.412 seconds).
`--lean verification/ArithmeticAxioms.lean` passed **165 probes** at
20:40:51 UTC (`590174f2cda53d26`, 32.527 seconds, not reused). Every probe
reported only `propext`, `Classical.choice`, and `Quot.sound`; there is no
`sorryAx` or custom mathematical axiom. Earlier scoped builds and the
141/150-probe intermediate audits also passed. Tactical errors were repaired
in the LSP loop before the accepted source checks. The audit file's LSP kept
a stale “imports out of date” notification after its import changed; the
subsequent serialized kernel check verified the exact final file.

Read-only honesty review approved the six scoped nodes for actual dual metric,
inverse dual ideal, line dual degree, projective exterior duality,
determinant-dual isometry, and arbitrary-rank dual degree. It inspected both
the producer-to-consumer route and the transitive axiom output. No package
assumes the desired calculus. The new `dualPullbackCore` is a constructed
positive form proved equal to the existing determinant metric.

The dual-degree frontier is closed. **General tensor degree, exact-sequence
degree, degree finiteness, supermodularity, and actual HN specialization remain
open**, as does manuscript Theorem 1.1. The next route is split into canonical
exterior product, determinant product by local freeness, and exact-sequence
determinant isometry in the blueprint. I-0045 tracks the shared-root batch
containing the checked dual leaf; the newer exterior-product work is excluded
from that batch.

Operational health was reviewed once by a read-only helper. The active-count
warning concerns nested ancestors and the now four user-authorized proof
lanes (I-0046); no additional proof writer was spawned. Older arithmetic
ancestor summaries were refreshed. One broad offline declaration search was
interrupted after sustained CPU use without results; scoped source searches
found the canonical wedge, product-tensor and localization APIs. The LSP
symbol index reports an error, so source-text searches, not empty index
results, were used. Toolchain and dependencies remain fixed.

Final round delta: the warning-free **9190-job shared-root build** integrated
the duality dependency cone through DeterminantDual (SPECHT handoff I-0045,
now archived). It does not certify the later product leaves. `ExteriorProduct`
passed **1951 jobs** at 20:58:47 UTC (`603c83032a097b42`, commit `f6ba49d`).
`DeterminantProduct` passed **1962 jobs** at 21:04:14 UTC
(`99d4ae8bf4f46353`). Its final source was captured in concurrent snapshot
`c649b88`, blob `e59c9109187b1e73919f6c7a39b68f49a7ca5ef9`; the subsequent
explicit arithmetic commit command found no remaining diff. This is evidence
for that source blob only.

The final axiom audit passed **171 probes** at 21:05:11 UTC
(`590174f2cda53d26`, 14.6 seconds). Full output is retained in this session's
`arithmetic-axioms-final.log`; parsing all 171 entries gives exactly the same
three foundational axioms. Six new probes cover the actual exterior product,
its wedge formula, naturality, scalar-extension generator identity, determinant
coordinate multiplication and finite-free bijectivity. The latter identifies
the canonical product map with a tensor-coordinate isomorphism and is a real
consumer. The general projective determinant isomorphism remains unproved;
these local calculations do not close it. Its next implementation uses
Mathlib's `bijective_of_isLocalized_maximal`, localization/base-change
compatibility, projective freeness over local rings, and localization rank
invariance. No further mathematical hypothesis is to be added.

The scratch cleanup dry run found no stale candidates and preserved all four
live run directories. The source-scope graph symlink was preserved.

Read-only honesty review also approved `lem:exterior-product` and
`lem:determinant-product-free`, inspecting their kernel records, substantive
coordinate consumer, generator-form scalar extension, and all six new axiom
probes. Only these two product producer nodes receive completion markers;
`lem:determinant-product` and `lem:exact-determinant-degree` stay `notready`.

Final graph sync: **184 blueprint nodes, 1214 Lean declarations, 848 edges**;
no unresolved-reference or stale-node warning. The **621 unattached** helper
and imported declarations include concurrent drafts and are retained as an
intentional coverage warning. I-0050 hands the two checked product leaves to
SPECHT for a future root batch; that integration is pending. All eight scoped
arithmetic completion markers from this round were independently reviewed.

Finalization acknowledgment: SPECHT accepted I-0050 and queued
`Arithmetic.DeterminantProduct` for its next shared-root check. ARITH
acknowledged that plan and left the thread open for the result. No proof
source changed during finalization. The remaining workspace diff belongs to
GEOM (`Geometry/ContractionBaseChange.lean`); the untracked workspace-root
configuration/instruction files and reference PDFs predate this checkpoint.
Those paths were left untouched and excluded from arithmetic commits.


## Projective determinant descent (run 0004, round 5)

`DeterminantProduct` now proves bijectivity of the canonical product of
exterior powers for finite projective modules over an arbitrary domain.
It uses Mathlib maximal-local detection, derived local freeness, rank
invariance, and the actual exterior-product scalar-extension comparison.
`IntegralDeterminantProduct.determinantProdEquiv` consumes this proof on the
intrinsic determinant lines over the ring of integers. No global integral
basis or degree-calculus hypothesis is assumed; zero ranks are included.

The serialized product build passed 2381 jobs at 21:38:00 UTC
(`99d4ae8bf4f46353`, 92.1 seconds). The checked product source is blob
`4883dff7e5e9bfe7984930a17a214ac18462313e`, captured by concurrent
boundary snapshot `30ea45b`; the explicit pathspec commit found no diff.
This evidence applies only to the checked source, not to other drafts in
that snapshot. The integral specialization passed a serialized file check
at 21:43:06 UTC (`1763aec1d5eebeba`, 59.3 seconds). The combined
`IntegralDeterminantProduct` / `DeterminantShear` build passed 3476 jobs
at 21:44:48 UTC (`98178eeaa63148c2`, 96.4 seconds). Commit `cb6db8d`
records the final finite-frame shear fix.

Read-only honesty review found no scoped defect: the projective descent
uses its local producers, the integral equivalence consumes bijectivity,
and the finite-frame shear identity includes empty bases. Independent
`lean_verify` on `prodMap_bijective_generic` found only `propext`,
`Classical.choice`, and `Quot.sound`. The broader final axiom audit and
completion-marker reconciliation are recorded below when finished.

GEOM consumed the stable piTensor/pullback/fiberMap interface and closed
I-0051. I-0050 now hands the new checked product and shear imports to SPECHT.
The roadmap hygiene review recommends retaining its 14 active rows: ten
are ancestors and four are the authorized active proof leaves; I-0017
already records this intentional count warning.

The exact algebra extension is now checked:
- `ProjectiveDeterminantShear`: 3138-job check `74c96073a1f508bc`,
  2026-11-05 21:57:55 UTC; explicit commit `c21586b`.
- `IntegralExactDeterminant` and its actual `ExactDeterminant` dependency:
  final warning-free 3478-job check `17cadcc289f092c1`, 22:08:26 UTC.
  Explicit commit `9ed74af` records final repairs; earlier source was captured
  by concurrent ledger snapshots, which are not evidence for unrelated drafts.
- The 192-probe transitive audit `590174f2cda53d26` passed at22:08:52 UTC;
  all axiom lists contain only `propext`, `Classical.choice`, `Quot.sound`.
  Full output: run0004/session0012 `arithmetic-axioms-final.log`.
- Earlier checks failed on a section-evaluation rewrite, proof-only binder
  inclusion, and the explicit arguments of `LinearEquiv.baseChange`. These
  were repaired before the passing checks. Unused projectivity warnings on
  rank lemmas were removed. LSP kept stale-import diagnostics for the new
  dependent files, so serialized kernel checks supplied the fallback evidence.
- Honesty review approved exactly the five algebra nodes: projective product,
  finite/projective shears, exact determinant, and original-section scalar
  extension. The review prompted correction of a middle-rank premise into a
  conclusion and a narrower base-change statement; both are resolved.
- SPECHT reports earlier product/integral-product/finite-shear imports in the
  warning-free 9205-job root check `975bdb23135a0d4a` at22:04:15 UTC. Later
  exact-sequence imports were delivered through I-0050 for the next root batch.

These producers support nonfree finite projective modules and zero ranks;
no number-field restriction or assumed degree calculus was introduced.
Remaining: the complex-fiber comparison with an arbitrary orthogonal section,
the determinant isometry and exact degree identity, arbitrary-rank tensor
identity, degree finiteness/supermodularity and the actual HN specialization.

## Exact determinant isometry and degree (run0004 round5)

The exact-sequence identity is now proved for arbitrary number fields and
nonfree finite projective modules, including rank-zero summands:
`HermitianMetric.degree_exact` uses the actual induced and quotient metrics.
`determinantExactEquiv_fiber_isometry` proves norm preservation on the entire
complex determinant fiber, not just on integral generators.

- `OrthogonalDeterminant`: 3517 jobs, `1e42044f8102ba14`,22:14:28 UTC;
  explicit commit `3a03d9c`. The generic orthogonal formula is consumed by
  the actual orthogonal-quotient lemma and the intrinsic exact metric proof.
- `ExactDeterminantBaseChange`: 3373 jobs, `c966a478c62e1b93`,22:16:36 UTC;
  commit `0848924`. It permits arbitrary sections after extension to a
  faithful field, including the complex orthogonal section.
- `ExactDeterminantMetric`: 3534 jobs, `cac74a1f025f4fba`,22:18:56 UTC;
  commit `8b595d4`. Rank transports connect that formula to the existing
  intrinsic determinant lines and their constructed metrics.
- `ExactDegree`: final warning-free3544-job check `5c3b6c9b72179523`,
  2026-11-05 22:22:18 UTC, commit `2f716f5`. All integral sections are
  compared by clearing denominators from a nonzero pure determinant tensor;
  the full-fiber extension uses its actual dimension one. The degree theorem
  consumes this isometry, intrinsic line-degree invariance and proved tensor
  additivity of nonfree lines.
- Final 201-probe audit `590174f2cda53d26`,22:22:42 UTC: only `propext`,
  `Classical.choice`, `Quot.sound`; no `sorryAx` or added axioms. Full output
  is run0004/session0012 `arithmetic-axioms-exact-degree.log`.

The metric files received clean LSP diagnostics; the audit's stale-import
LSP state was superseded by the serialized kernel check. Initial local
elaboration errors involved finite-index separation, proof-only hypotheses,
rank transport rewriting and a nonexistent lemma namespace; all were fixed.
Two passing ExactDegree builds emitted unused-projectivity warnings; the
final build removes both warnings. No failed proof remains in these files.

The previous algebra handoff was integrated by SPECHT in the warning-free
9210-job root check at22:11:39 UTC, commit `4d40509`. The newer ExactDegree
import and its transitive metric leaves were sent in I-0050 for integration.
No new external source copy or dependency change was made.

Remaining mathematical frontier: arbitrary-rank tensor determinant/degree,
restriction-of-scalars covolume and degree finiteness, supermodularity, then
the actual HN specialization. The source Theorem1.1 and BOST-ARITH remain open.

Honesty-reviewer inspected the final201-probe log and the exact source at
`2f716f552f703e587659239635beef2c134ff158`; verdict satisfactory, no actionable
findings. It approved precisely the orthogonal-norm, arbitrary-field-section,
intrinsic pure-norm and exact-isometry/degree nodes. Their blueprint markers
now name the substantive checked producers. EXACT-DET and its two child units
are closed; the BOST-ARITH task remains active. The next roadmap producer is
the nonfree integral tensor determinant identity.

The janitor checkpoint found no actionable hygiene defects. The remaining
active-item count warning is intentional: the count includes ancestors of
the four authorized proof lanes, as recorded in I-0017. Temporary cleanup
found no stale candidates and protected all live runs. I-0050 remains open
for the new shared-root integration result; SPECHT acknowledged the handoff.

Final graph sync:208 blueprint nodes,1391 Lean declarations,972 generated
edges; no missing-reference warning. The719 unattached helper/imported
nodes are intentional coverage warnings, recorded in I-0004; the configured
owned-source scope remains intact. I-0061 explicitly requests ending this
round after this verified milestone so the live run resumes with fresh Lean
clients. All authored Lean is checked and committed; no unfinished draft
is left. The overall task is not marked done.

## Session 0014: arbitrary-rank intrinsic tensor degree

`TensorCompatibility` compares the entire complex tensor fiber with the
canonical Hilbert form and proves induced-metric compatibility.
`ComplexTensorQuotient` proves that the tensor of the orthogonal right
inverse is the actual orthogonal right inverse of the tensor map. Its
consumer `TensorExactMetric.tensor_pushforward` identifies the intrinsic
quotient tensor metric. `RankOneReduction` constructs an actual saturated
line in every positive-rank projective module.

`DegreeIsometry` derives isometry invariance from the two determinant
contraction inequalities. `TensorDegree.degree_tensor_exact` consumes
both tensor metric identities and exact determinant additivity. Strong
induction on the sum of generic ranks then proves `degree_tensor`, using
the established nonfree rank-one formula. `slope_tensor` gives average
slope additivity for positive ranks. All number fields and nonfree finite
projective modules remain supported; rank-zero degree is also covered.
No tensor semistability or degree-calculus field is assumed.

| Checked target | Fingerprint | Completion UTC | Result |
| --- | --- | --- | --- |
| `TensorCompatibility` | `e8fe46c5dc16170c` | 2026-11-05 22:44:20 | 3454 jobs, no warnings |
| `ComplexTensorQuotient` | `8fe6c93c9f092ba2` | 22:48:49 | 2816 jobs, no warnings |
| `TensorExactMetric` + `RankOneReduction` | `9805439ef2e1aa04` | 22:50:49 | 3537 jobs, no warnings |
| `DegreeIsometry` | `dbe6b369698a2dfb` | 22:52:06 | 3511 jobs, no warnings |
| `TensorDegree` | `d8e541c6d3f18016` | 22:55:16 | 3551 jobs, no warnings |
| `ArithmeticAxioms.lean` | `590174f2cda53d26` | 22:56:17 | 221 transitive probes, foundational axioms only |

Each check used the serialized Horizon slot with explicit workspace root.
The audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
The first source units are explicit commits `d5bdba7` and `16fe3bf`.
Concurrent automatic snapshot `5455f7f` captured the final two source files
before the explicit commit: TensorDegree blob
`a8a477a69e3ed78da04c2b3e80e4b92738f651ec`, DegreeIsometry blob
`be9c9e1f89633e60e7ceabbda23011e5e1f9c05e`. This snapshot is not evidence
for other tasks' files. No Lean edit followed the final accepted module
check. The expanded axiom audit and reviewed blueprint attachments are
committed explicitly afterward.

LSP was available for the proof loop. A stale-import diagnostic persisted
for TensorExactMetric after its dependency build, so its serialized module
build was the faithful fallback. Earlier elaboration failures concerned
induction hypotheses retaining membership assumptions, explicit quotient
lift surjectivity arguments and unfolding induced metrics; all were fixed.
Two independent scoped honesty passes approved the producers and their
actual degree/slope consumers, including the four new checked nodes.

The arbitrary-rank degree proof follows intrinsic exact determinants and
rank-one reduction. It does not construct a separate canonical general
tensor-determinant isomorphism. Supermodularity, arithmetic degree
finiteness and intrinsic HN remain open; the aggregate calculus marker is
still pending. No claim for maximal slopes or manuscript Theorem 1.1 follows.


## Session 0014: intrinsic supermodularity and quotient interval slopes

`SumQuotient` proves the projectivity and exactness of the actual sum quotient.
`SubmoduleDegree` compares the two quotient norms on `(U + V) / V` by
minimality of orthogonal lifts, then consumes exact degree and contraction.
`SubspaceSupermodular` consumes that inequality and saturation to prove
supermodularity of the intrinsic `subspaceDegree`. Its convexity instance
feeds the existing HN payoff API. The interval degree and generic-rank
identities identify every strict interval with the actual induced quotient
bundle slope. All statements support arbitrary number fields and nonfree
finite projective modules; no calculus or convexity assumption is supplied.

| Target | Fingerprint | Accepted completion (UTC) | Result |
| --- | --- | --- | --- |
| `Arithmetic.SumQuotient` | `52d82dd6262403b5` | 2026-11-05 23:02:22.753 | 3342 jobs, warning-free |
| `Arithmetic.SubmoduleDegree` | `f79b953ac12c1229` | 2026-11-05 23:06:21.048 | 3550 jobs, warning-free |
| `Arithmetic.SubspaceSupermodular` | `a75f036feec8dce9` | 2026-11-05 23:08:55.287110 | 3563 jobs, warning-free |
| `verification/ArithmeticAxioms.lean` | `590174f2cda53d26` | 2026-11-05 23:15:08.049455 | 235 probes, passed |

All checks used the explicit workspace root and serialized Horizon slot.
The read-only honesty reviewer read the original audit log, counted all
235 probes, and confirmed only `propext`, `Classical.choice`, and `Quot.sound`.
The reviewer approved the precise abstract slope, sum/intersection,
Hermitian supermodularity, and quotient-interval blueprint nodes. The unused
degree-isometry dependency edge was removed. The former combined node was
split so semistability and the chain-length claim remain explicitly open.

`SumQuotient` and `SubmoduleDegree` are in explicit commit `d436624`.
`SubspaceSupermodular` was captured by concurrent boundary `f55b9fd` before
its explicit commit; that snapshot is not evidence for unrelated files.
The explicit audit commit is `d248986`. No Lean edits followed the three
accepted producer checks. Axiom and source evidence is local; root integration
was requested from SPECHT in I-0065 and remains separate.

Degree finiteness, attained maximal slope, and the intrinsic HN filtration
remain open. The checked convexity instance alone does not establish these
or manuscript Theorem 1.1.


## Session 0014: bounded integral sections

`Arithmetic.ArchimedeanFiniteness` proves `finite_bounded_sections` for the
actual integral sections and arbitrary real bounds at every complex
embedding. Its coordinate-bound producer uses the canonical dual-fiber
comparison and finite-dimensional operator norms. The final proof embeds the
finite projective module into a finite free module and uses Mathlib's
`NumberField.Embeddings.finite_of_norm_le` on each coordinate. It does not
assume the original module is free. Negative bounds and rank zero are allowed.

The final serialized module build `b82cac78155fb967` passed 3345 jobs without
warnings at 2026-11-05 23:22:44.320552 UTC. The earlier 23:20:25 build had one
unused-section-variable warning; that warning was fixed before the final
build. The 237-probe audit `590174f2cda53d26` passed at
23:26:06.791297 UTC. The honesty reviewer parsed both original logs and
confirmed all probes use only the three standard foundational axioms.
Source and audit are in explicit commit `484fba6`; the module blob is
`a0566db856afbbee3e65058949d97d7bf6aad7e5`. No source edit followed its final
module check. Only the bounded-sections node is marked checked.

This is a concrete precursor to discreteness under restriction of scalars.
It does not assert a degree bound, bounded-degree finiteness of submodules,
maximal-slope attainment, or an intrinsic HN filtration. Those remain open.

The next source inventory found Mathlib's canonical/mixed embedding lattice
bases, the mixed integer-lattice discriminant covolume, and ZLattice's
covolume/index and discrete-lattice rank APIs. A second possible HN route is
available in the pinned library: finite-dimensional subspace lattices have
both well-founded strict orders, and `PayoffFunction.hnFiltration` uses
convexity, ADCC and a total complete codomain. Before using it for the target,
prove the actual semistability bridge from game values to quotient slopes;
`NashEquilibrium` and `IsSlopeLike.min_eq_A` provide the relevant imported
results. This inventory is not a checked intrinsic HN specialization or a
replacement for the outstanding degree-finiteness objective.


## Session 0014: actual Hermitian HN interval flag

`Slope.FiniteLength` proves the ordinary-slope interpretation of game
semistability on finite-length lattices and identifies a semistable interval's
game value with its payoff. `Arithmetic.SubspaceHN` applies the pinned HN
constructor to actual `subspaceDegree`, using proved supermodularity and
finite-dimensional subspace chain conditions. It constructs saturated
integral terms, proves their endpoints and strict steps, and proves actual
quotient slope bounds for every intermediate generic subspace and strict
successive decrease. The real-cut order supplies admissibility; no degree
finiteness or semistability conclusion is assumed.

| Target | Fingerprint | Accepted completion (UTC) | Result |
| --- | --- | --- | --- |
| `Slope.FiniteLength` | `ecc531e6f2e5ff99` | 2026-11-05 23:32:17.321136 | 1062 jobs, warning-free |
| `Arithmetic.SubspaceHN` | `2c8936e24d757242` | 2026-11-05 23:34:30.183074 | 3571 jobs, warning-free |
| `verification/ArithmeticAxioms.lean` | `590174f2cda53d26` | 2026-11-05 23:35:06.767899 | 252 probes, passed |

Explicit source commits are `09c8bf5` and `49d4769`. The honesty reviewer
checked the constructor's substantive hypotheses, its actual quotient
consumers, and all 252 probes in the original serialized log. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. Source comparison used the
Chen–Jeannin labels `Thm: equivalence of stability conditions` and
`Def: HN filtration`; the imported code remains at the pinned revision in
CONTRIBUTIONS. The two precise blueprint nodes were approved as checked.
After validation, only the stale module docstring in `SubspaceDegree` was
corrected; no definition or proof changed. Its LSP diagnostics are clean.

The blueprint now routes full HN through this actual interval flag. The
remaining producer must translate intermediate generic subspace inequalities
into semistability against every integral submodule of each quotient, then
prove the maximal-slope bound, greatest destabilizing submodule, uniqueness,
and isometry invariance. The largest-rank uniqueness assertion is explicitly
about saturated submodules; containment of every maximal-slope submodule is
also stated. These statements and the separate arithmetic degree-finiteness
objective remain unverified. `lem:hn-filtration` is still notready; no
completion claim for BOST-ARITH or manuscript Theorem 1.1 is made.

### Session 0014 boundary maintenance

The final scoped graph sync reported 249 blueprint nodes, 1707 Lean
declarations and 1224 generated edges, with no unresolved source or
declaration attachments. The 827 unattached helper/imported declarations
remain intentional coverage warnings. The one newly stale node is the
removed, unused quantitative chain-length side goal; the chosen route uses
Mathlib's well-founded subspace orders. The source-scope symlink is intact.
The scratch-cleanup dry run found no stale candidates and protected all four
live runs. The operational ground review and warning disposition are recorded
in I-0017 and I-0004.

At the finalization recheck, all ARITH-owned paths were clean. Remaining
workspace changes belonged to the concurrent root/SPECHT, GEOM and BALANCED
lanes (root imports and attribution, Specht, geometric/compactness blueprints,
Balanced verification, invariant/representation theory and vendor paths),
or were pre-existing workspace configuration/reference files. None was
staged or committed by this task. I-0065 stays open for the root integration
result; the delivered arithmetic imports were acknowledged by both consumers.


## Session 0016: actual HN grades and maximal slope

The all-integral semistability equivalence and actual quotient-preimage degree/rank
formulas are in `de1c7bb`; the saturation comparison for arbitrary quotient
submodules is in `fc452fc`; `fb56e97` proves semistability of every actual HN grade,
attainment of the maximum integral-submodule slope and containment of every
maximizer in the first saturated term. These are proved producers for arbitrary
number fields and nonfree finite projective modules.

- Serialized `check Arithmetic.Semistable Arithmetic.QuotientSubmoduleDegree`
  (full module names) passed 3573 jobs at 2026-11-05 23:49:12 UTC,
  fingerprint `2da16866e835b77e`.
- `check BostConjecture.Arithmetic.QuotientSemistable` passed 3574 jobs at
  23:54:01 UTC, fingerprint `81d3bf8b80cff84a`.
- `check BostConjecture.Arithmetic.HermitianHN` passed 3576 jobs at 23:58:15 UTC,
  fingerprint `221119cdbff26404`.
- `check --lean verification/ArithmeticAxioms.lean` passed 287 probes at
  23:59:04 UTC, fingerprint `590174f2cda53d26`; only `propext`,
  `Classical.choice` and `Quot.sound` occur. Log: session0016/arithmetic-axioms.jsonlog.
- Scoped honesty review was satisfactory: all-submodule quantifiers, actual
  quotient metrics, positivity and substantive maximum proofs were checked.

The first command attempted with unsupported `check -p` was rejected before Lean;
the commands above use explicit workspace `--root` and the shared serialized slot.
The offline MCP search tool likewise lacked workspace-root discovery; the Horizon
CLI and guarded LSP searches supplied the required searches instead.
The previous integration thread I-0065 closed after the accepted root e2e7039;
these new producers were handed to the successor shared integrator GEOM as I-0075.
The later checks below close HN uniqueness/isometry; degree finiteness remains open.

### Full intrinsic HN and representation consumers

`c030f67`, `c3747d0` and `22be758` complete uniqueness (including arbitrary
saturated integral flags), invariance under integral isometries, and the
canonical irreducible-action semistability criterion. The final 3587-job
consumer check `533e54f9712851e0` passed at 00:16:26 UTC; the 302-probe audit
passed at 00:17:17 UTC. Honesty review approved the precise full-HN nodes.
GEOM integrated the delivered endpoint at `70d1911`: its configured 9296-job
root check passed at 00:32:42 UTC, root blob
`57ed74cb5b71c6c523cf463905883c06c310d36e`.

`RestrictionOfScalars.lean` (source blob
`46f8a357ebc0191ff350c677f5b731c32da641b1`, present at `11fd898`) proves
integer freeness, canonical rational generic-fiber equivalence and the rank
formula for arbitrary finite projective integral modules. Its serialized
module check `bcd75114888b2a5e` passed at 00:23:27 UTC; the 308-probe audit
passed at 00:24:19 UTC. The source was automatically captured in `f9a60e4`;
that capture is not verification evidence for any unrelated file.

`5d1ff45`, `76c232f`, `89d2734`, `d56e6ff` and `e73bda6` establish dual and
independent binary tensor irreducibility, scalar-extension invariant submodules,
the one-complex-embedding semistability criterion, and the actual tensor/dual
metric consumers. The joint 3603-job consumer check `440a060c199d3fdc` passed
without warnings at 00:39:04 UTC. The 329-probe audit passed at 00:39:50 UTC
(`representation-axioms.jsonlog`). All recorded probes report only `propext`,
`Classical.choice`, and `Quot.sound`. Independent honesty review approved the
five precise representation and binary-consumer nodes at `e73bda6`.

The LSP occasionally retained stale imported environments after dependency
edits; serialized narrow checks and import reloads supplied the fallback.
One tensor-consumer file check failed on an unreduced identity map; this was
repaired before its successful module check. The first dual builds exposed
unused number-field hypotheses; these were removed before the final warning-free
joint check. No admitted proof or custom axiom was introduced.

`387d06a` and `a1aa8cb` complete the finite-family representation consumer.
The warning-free 3615-job `Arithmetic.IndependentPiSemistable` build passed
at 00:58:25 UTC; its 338-probe audit passed at 00:58:49 UTC, foundational
axioms only (`finite-representation-axioms.jsonlog`). Independent honesty
review approved both finite-family nodes at `a1aa8cb`. The endpoint and
scalar-restriction import were sent to GEOM in I-0075 for root integration.
This includes arbitrary independent groups, a common irreducible complex
fiber, all-embedding metric invariance, and the empty tensor product.

Full configured graph sync repaired the stale nodes caused by a scoped sync;
only unattached helper declarations remain warned (939 across all slices).
No missing cross-slice dependency warnings remain in the full sync.

The arithmetic frontier is now the real trace metric and degree-covolume formula,
then bounded-degree finiteness via primitive exterior integer lattices.
This record does not assert general tensor semistability or manuscript Theorem 1.1.
