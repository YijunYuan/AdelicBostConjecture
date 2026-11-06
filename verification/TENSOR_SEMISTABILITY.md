# Tensor semistability evidence

The source tensor-semistability theorem is **open**. No unconditional tensor
semistability declaration is exported yet.

## Normalization and normalized extensions

`Main/TensorSemistability/Extensions.lean` proves the degree-zero criterion,
rescaling invariance, normalization, exact quotient degree, degree-zero
submodule/quotient semistability and normalized extension closure. The domains
are arbitrary number fields and finite projective integral modules; no integral
basis is required.

- Serialized check: `horizon --root /home/yijunyuan/bc-workspace check BostConjecture.Main.TensorSemistability.Extensions`, passed, 3575 jobs, no warnings.
- `check --lean verification/TensorSemistabilityAxioms.lean`: seven probes passed,
  each using only `propext`, `Classical.choice`, `Quot.sound`.
- Independent `honesty-reviewer` found no mathematical, source or integrity
  defect and independently repeated all seven axiom probes.
- Blueprint: `lem:semistable-normalization` and
  `lem:normalized-semistable-extension`; consumer: minimal-rank strict-factor
  reduction for `thm:tensor-semistability`.

## Actual metric change and section-formula derivative

`MetricVariation.lean` constructs actual archimedean pullbacks by arbitrary
conjugation-compatible fiber automorphisms and proves that determinant-one
families preserve the determinant metric and degree. `DegreeDerivative.lean`
proves the logarithmic derivative of intrinsic degree, also in squared-norm
form, along a metric curve with differentiable determinant section norms.

- Serialized two-module build: passed, 3510 jobs, no warnings.
- Expanded `TensorSemistabilityAxioms.lean`: twelve probes passed, all with only
  `propext`, `Classical.choice`, `Quot.sound`.
- Independent source/mathematical/honesty review accepted both bounded producers.
  Its missing dependency-edge finding was fixed in the source theorem.
- Blueprint: `lem:arithmetic-metric-variation` and
  `lem:arithmetic-degree-derivative`, both in the final theorem's dependency cone.

The line-twist, strict-factor reduction, conjugation-compatible exponential
curves, actual submodule projection-trace derivative, extremal-to-balance and
final composition remain open. These two producers do not prove balance.
COMPACTNESS's maximizing-pair endpoint and SPECHT-SLOPE's geometric endpoint are
also still producer boundaries. Shared-root integration is pending MAIN's
acceptance of the checked handoff.
