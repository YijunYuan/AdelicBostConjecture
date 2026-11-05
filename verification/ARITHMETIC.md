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
