# Arithmetic compactness verification

The fixed-module maximum-degree and strict-stability portion of manuscript
Lemma 7.1 (pages 11–12) is proved for the existing `HermitianMetric`, over every
number field and every finite projective module over its ring of integers.

- `MaximumDegree`: an actual saturated maximizer, its nonnegative maximum,
  and upper bounds for every saturated induced degree.
- `MetricComparison`, `MaximumComparison`: uniform exponential bounds on
  actual fiber norms bound changes of induced degrees and their maximum.
- `MetricTopology`: pointwise convergence of actual fiber forms gives joint
  norm continuity and local uniform exponential comparisons.
- `DegreeContinuity`: continuity of degree, every fixed induced degree, and
  maximum degree in that topology.
- `Stability`, `StabilityTopology`: a uniform negative degree gap and openness
  of strict stability in the subtype of degree-zero metrics.

The source route is `blueprint/src/arithmetic_compactness.tex`. It replaces
the source's covolume-based finiteness argument with the completed intrinsic
`finite_saturated_submodules_degree_ge`; no covolume formula is assumed.
The source-facing compactness and maximizing-pair conclusions remain open.

## Checks

Executed with `/home/yijunyuan/bc-workspace` explicitly passed to Horizon:

```text
horizon check BostConjecture.Arithmetic.Compactness.DegreeContinuity BostConjecture.Arithmetic.Compactness.StabilityTopology
  passed: 3668 jobs, 2026-11-06 02:29 UTC
horizon check --lean verification/ArithmeticCompactnessAxioms.lean
  passed: 14 transitive axiom probes, 2026-11-06 02:30 UTC
```

Every probe reports only Lean's standard foundational axioms `propext`,
`Classical.choice`, and `Quot.sound`; none reports `sorryAx` or a new axiom.
The guarded LSP was used before and after edits. Two files initially retained
stale-import diagnostics after their producers were built; serialized narrow
Horizon checks supplied feedback. An initial `Stability` check caught an
extra `.le` projection; it was repaired and the endpoint checks passed cleanly.

The read-only `honesty-reviewer` independently checked the source shape,
actual proof consumers, topology, rank-zero behavior, build evidence and all
14 axiom outputs. Verdict: honest proved producers; full fixed-module
`lem:degree-maximum-continuity` may be marked checked. Root integration belongs
to GEOM and is a separate handoff.
