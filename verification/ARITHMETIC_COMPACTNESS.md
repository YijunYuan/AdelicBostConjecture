# Arithmetic compactness verification

The assigned arithmetic compactness and maximizing-pair producers are proved
for the existing `HermitianMetric`, over arbitrary number fields and arbitrary
finite projective modules over their rings of integers. No freeness over the
ring of integers is assumed. The statements also cover rank zero; positive
ranks are the manuscript application.

## Checked route

- `MaximumDegree` consumes intrinsic all-rank degree finiteness to obtain an
  actual saturated maximizer and nonnegative `maxDegree`.
- `MetricComparison`, `MaximumComparison`, `MetricTopology`, and
  `DegreeContinuity` prove local uniform norm comparisons and continuity of
  actual degree, induced degree, and maximum degree.
- `Stability` and `StabilityTopology` prove a uniform negative degree gap and
  openness of strict stability among normalized metrics.
- `TraceSystole` proves the actual normalized semistable trace lattice has
  systole at least the square root of the field degree, independently of
  covolume, using the saturated generic line and line-degree quotient formula.
- `TraceMultiplication`, `IntegralMatrices`, and `TraceActionFiniteness` bound
  actual integral multiplication matrices in compact lattice frames.
- `TraceFrames` consumes the exact discriminant/degree covolume formula,
  systole, canonical trace lattice, and accepted pinned Mahler vendor.
- `FixedAction` selects a subsequence with constant integral multiplication
  matrices and constructs actual basis-preserving ring-linear isomorphisms.
- `ComplexTraceCoordinates`, `FrameMetric`, and `FrameLimit` use the canonical
  complexified trace space and invertible limiting frames to reconstruct
  positive-definite conjugation-compatible metrics on the actual module.
- `MetricTransport` and `SemistabilityTopology` preserve normalization and
  every semistability inequality under those isomorphisms and metric limits.
- `SequentialCompactness.exists_normalized_semistable_subsequence` assembles
  these producers. Its fixed module is an original sequence member.
- `TensorContinuity` and `MaximumTransport` prove joint tensor maximum-degree
  continuity and invariance under actual integral isomorphisms.
- `MaximizingPair.isCompact_tensorMaxDegreeValues` proves compactness of the
  literal set of values realized by actual normalized semistable pairs at fixed
  ranks. `exists_maximizing_pair` returns actual modules, metrics, and a
  saturated tensor submodule realizing the global maximum. Its additional
  premise is existence of one candidate, supplied by `tensor_maxDegree_mem`.
  This is the agreed TENSOR-SEMI counterexample interface (I-0114).

The source-facing blueprint is `blueprint/src/arithmetic_compactness.tex`,
with exact manuscript pages 11–13 registered as source anchors. There is no
second arithmetic-bundle model, assumed covolume producer, assumed tensor
semistability, or extremal certificate.

## Reproducible checks

All commands use `horizon --root /home/yijunyuan/bc-workspace check` and the
shared serialized resource slot. Endpoint results on 2026-11-06:

| Target | Result |
| --- | --- |
| `BostConjecture.Arithmetic.Compactness.SequentialCompactness` | 9153 jobs passed, 03:39 UTC |
| `BostConjecture.Arithmetic.Compactness.TensorContinuity` | passed in the 3670-job endpoint check |
| `BostConjecture.Arithmetic.Compactness.MaximumTransport` | 3669 jobs passed |
| `BostConjecture.Arithmetic.Compactness.MaximizingPair` | 9156 jobs passed, 03:51:59 UTC |
| `--lean verification/ArithmeticCompactnessAxioms.lean` | 40 transitive probes passed, 03:52:37 UTC |

Every probe reports only Lean's standard foundational axioms `propext`,
`Classical.choice`, and `Quot.sound`. The compactness source directory has no
`sorry`, `admit`, or axiom declaration. The endpoint probes cover all transitive
producers, including exact covolume and the accepted vendor.

Guarded LSP was queried before and after edits. Some workers retained stale
imports; serialized narrow checks supplied feedback. Initial failed checks
caught an extra projection, duplicate canonical basis, dependent-instance
rewrite, function-composition rewrite, and missing value-set universe
annotation. All were repaired before the successful endpoint checks.

COVOLUME provenance is unchanged: exact formula `5144157`, canonical basis
relocation `739e58a`. Vendor attribution remains in `CONTRIBUTIONS.md`; MAIN
owns its consumer list and shared integration. Arithmetic compactness
`daad480` was integrated at `1c4c3f8`, with root 9375 jobs passing.
The final maximizing-pair checkpoint `e81b08b` was integrated by MAIN at
`ece5ec1`: root **9380 jobs passed without warnings at 04:06:01 UTC**.
The actual serialized log is workspace-root
`.archon-horizon/runs/0011/sessions/0004-horizon-BOST-MAIN/main-root-handoffs.log`.
Independent integration review verified that all 89 project modules in this
producer cone match the accepted tree and inspected all 40 axiom outputs.
TENSOR-SEMI accepted the consumer interface in I-0114; I-0118 records the
final root handoff. Shared `OPEN_PROOFS.md` now removes the stale obligation.

Independent read-only honesty/source review accepted the complete route,
including the literal value set, universe, nonfree domain, both subsequences,
joint continuity, isometry invariance, actual witnesses, saturated maximizer,
source statements and exact check outputs. Blueprint completion markers cover
these producers only. Strict maximizing-counterexample reduction, extremal
variation, tensor semistability and maximal-slope additivity belong to the
other lanes and are not claimed here.

Graph sync resolves every owned source and dependency attachment; both final
endpoint nodes report `lean_ok`. The 1102 unattached helper/concurrent-draft
declarations remain coverage warnings, recorded in I-0004, not unresolved
references. Final read-only hygiene review found the owned paths clean,
roadmap consistent, and no stale scratch cleanup candidates. All assigned
mathematical and integration obligations are complete.
