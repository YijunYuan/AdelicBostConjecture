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

## Review and remaining boundary

Read-only honesty reviews checked the actual module/fiber representation,
the product-formula cancellation, nonfree coordinate comparison, genuine
quotient index and finiteness, and final intrinsic consumers. An initially
missing representative-independence theorem was supplied as
`sectionNorm_eq_of_place_eq`. No substantive defect remained in the reviewed
line-degree unit. Only the corresponding rank-one blueprint nodes are marked
checked.

The full conjugate-linear fiber map and real fixed-fiber identification remain
an explicit unchecked equivalence lemma. The next producer is the finite
projective determinant line and its complex Gram-determinant metric. Mathlib's
existing exterior inner product is real-only; it does not supply that complex
metric. Complete mathematical statements and proofs for these next two
producers are in `blueprint/src/arithmetic.tex`, still marked `notready`.

Higher-rank determinant degree, dual/tensor/exact-sequence identities,
contraction and saturation inequalities, degree finiteness/supermodularity,
and the actual HN specialization remain open. The existing abstract slope
bridge does not close them. No main-theorem completion or whole-project
verification claim follows from these arithmetic checks.
