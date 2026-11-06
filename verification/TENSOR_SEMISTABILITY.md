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

## Arithmetic Gram derivative and local stationarity

`GramDegree.lean` proves the exact determinant-section squared-norm formula in
an arbitrary complex basis, cancels its positive coordinate factor at an
orthonormal base point, and proves the degree derivative is
`-(sum d)/(2*[K:Q])`. Actual local maximality forces this embedding sum to zero.

- Final serialized module check: 3243 jobs, no warnings.
- Expanded serialized axiom audit: fifteen probes, foundational axioms only.
- Independent mathematical/source/honesty review accepted the factor of two,
  nonzero coordinate cancellation and arbitrary nonfree domains.
- Blueprint `lem:arithmetic-gram-derivative` feeds
  `lem:arithmetic-degree-stationarity`, which feeds tensor semistability.

The stationarity lemma is intermediate: its actual metric curve and local
maximum are hypotheses, and it does not assert balance.

## Compatible determinant-one exponential variations

`ExponentialVariation.lean` constructs actual metrics from self-adjoint
generator families compatible with the canonical fiber conjugation. The
spectral proof establishes semilinear exponential intertwining, and trace-zero
generators preserve the actual determinant metric and degree. The curve at zero
is the original metric. No freeness or rational-field restriction occurs.

- Serialized module check: 3524 jobs, no warnings.
- Expanded serialized axiom audit: twenty-one probes, foundational axioms only.
- Blueprint: `lem:arithmetic-exponential-variation`, in the source theorem cone.
- Independent exact-source/mathematical/honesty review accepted the construction,
  including the explicit real-place commutation restriction; localization to
  arbitrary allowed single-place directions remains to be proved.

## Continuity and actual local maximality

`VariationTopology.lean` proves continuity in the actual metric topology and
preservation of normalized strict stability near zero. `ExtremalNeighborhood.lean`
proves normalized strict stability implies semistability by saturation. It then
uses the literal maximizing-pair value-set bound and an attaining saturated
submodule to prove its degree has a local maximum along continuous normalized
metric curves through strictly stable factors.

- Serialized builds: 3677 and 9171 jobs, no warnings.
- Independent mathematical/source/honesty review accepted both producers.
- Expanded serialized audit: twenty-five probes passed, each using only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Strict stability is an explicit premise of the intermediate local-maximum
  theorem; its construction by minimal-rank reduction is not claimed.

## Actual induced-degree projection-trace derivative

`SubmoduleVariation.lean` proves the arithmetic derivative
`-sum (Re trace (projection ∘ generator)) / [K:Q]` for actual compatible
automorphism curves and fixed integral submodules. It specializes to the
constructed exponential metrics, and actual local maximality forces the trace
sum to vanish. The proof consumes the accepted Gram variation and intrinsic
degree derivative, using an actual fiber isometry onto the submodule range.

- Final serialized module build: 3527 jobs, no warnings.
- Expanded serialized axiom audit: twenty-nine probes, foundational axioms only.
- Independent source/mathematical/honesty review accepted the factor, sign,
  real scalar instances and arbitrary nonfree, possibly nonsaturated submodules.
- Blueprint `lem:submodule-projection-trace-derivative` feeds the explicit
  still-open `lem:extremal-to-balance` producer.

The line-twist, strict-factor reduction, tensor variation transport,
conjugation-compatible partial-trace defects, extremal-to-balance and final
composition remain open. The checked producers do not prove balance.
The planned balance proof uses global compatible defect families and positivity
of the sum of their squared Hilbert–Schmidt norms; an independent mathematical
review accepted this adaptation, but its Lean proof remains open.
COMPACTNESS's actual maximizing pair (e81b08b) and SPECHT-SLOPE's geometric
endpoint (final 8c80c92, unchanged binary interface) have been handed off.
Shared-root integration of new units is owned by MAIN.
