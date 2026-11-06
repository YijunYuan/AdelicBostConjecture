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

The line-twist, strict-factor reduction, actual metric variation, arithmetic
degree derivative, extremal-to-balance and final composition remain open.
COMPACTNESS's maximizing-pair endpoint and SPECHT-SLOPE's geometric endpoint are
also still producer boundaries. Shared-root integration is pending MAIN's
acceptance of the checked handoff.
