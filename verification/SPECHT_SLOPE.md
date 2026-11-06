# Determinant–Specht and geometric slope evidence

The assigned objective remains open. The first checked producer is the actual
integral orbit-lattice representation in `Arithmetic/Specht/Representation.lean`.
Its complex irreducibility uses the accepted `complexSpechtEquiv`, equivariance,
and `OAI.Saxl.specht_irreducible`. Its invariant form is GEOM's actual complex
word Gram form. Scalar-extension cancellation intertwines the actions.

Validation: `horizon --root /home/yijunyuan/bc-workspace check
BostConjecture.Arithmetic.Specht.Representation` passed (9067 jobs, 79.5 seconds).
The three transitive axiom probes in `SpechtSlopeAxioms.lean` returned only
`propext`, `Classical.choice`, and `Quot.sound` through guarded LSP.
The scoped read-only honesty/source review found no mathematical or scope defect.

`Arithmetic/Specht/Bundle.lean` constructs the actual canonical Hermitian metric
on `𝓞 K ⊗[ℤ] orbitLattice t`, proves conjugation compatibility and every-fiber
isometry, and applies ARITH's one-complex-embedding criterion to prove intrinsic
semistability. Its generic rank is proved equal to the integral lattice rank.
The module build passed (9138 jobs, 12.7 seconds); the five added axiom probes
are foundational-only. The follow-up honesty/source review confirmed that this
is a substantive concrete consumer, with no supplied metric or representation
hypotheses.

`Arithmetic/Specht/DeterminantRepresentation.lean` constructs the permutation
representation on GEOM's actual determinant-twisted module, including its
one-dimensional determinant tensor factor. It identifies the complexification
equivariantly with the accepted Specht representation and proves irreducibility
for a finite projective module of constant stalk rank, without an integral basis.
Its kernel build passed (9110 jobs, 10.4 seconds); three further axiom probes are
foundational-only. Independent honesty/source review accepted the construction.
`Arithmetic/Specht/DeterminantBundle.lean` constructs the source-prescribed
metric by pullback through GEOM's actual injection, proves every-fiber
isometry of the actual action and the explicit determinant/lattice Gram
comparison, and proves intrinsic semistability. The actual finite tensor
family and its Hermitian dual are semistable by the existing ARITH criterion,
with the concrete hypotheses proved here. Kernel build passed (9180 jobs,
19.1 seconds); all sixteen transitive axiom probes are foundational-only.
The final scoped honesty/source review found no defect in these consumers.

`Arithmetic/Specht/LatticeDegree.lean` proves the actual lattice determinant
norm equals the checked lattice covolume, its normalized arithmetic degree is
minus the logarithm of that covolume, and its slope is minus
`rectangleLogCovolume` in the rectangular case. It consumes the stable free-basis
degree formula at d41ef38; no restriction-covolume comparison is assumed.
Kernel build passed (9146 jobs, 16.3 seconds), and the complete twenty-declaration
axiom probe passed (19.5 seconds) with only the three foundational axioms above.
Independent honesty/source review confirmed the all-embedding normalization,
absence of a discriminant factor, and the actual real-span covolume.

`Arithmetic/Specht/DeterminantTensorMetric.lean` identifies the actual GEOM
pullback metric with the existing ARITH tensor metric on the determinant powers
and lattice. Kernel build passed (9181 jobs, 77.0 seconds), and all twenty-one
transitive probes passed (31.3 seconds), foundational-only. Independent review
confirmed the canonical maps, normalization and absence of integral freeness;
its requested constant-rank/projectivity clarification was added to the blueprint.

`Arithmetic/Specht/FiniteTensorDegree.lean` proves rank multiplication and average
slope additivity for actual finite Hilbert tensor products, including the empty
family, and the intrinsic determinant-power degree formula. Kernel build passed
(3620 jobs, 23.1 seconds), all twenty-four probes passed (40.8 seconds), and the
independent honesty/source review accepted the nonfree proof and actual metric
consumers. No semistability of the factors is needed for average slope additivity.

`Arithmetic/Specht/DeterminantDegree.lean` proves the exact intrinsic slope
`n * h.slope - rectangleLogCovolume a k` for the actual canonical bundle,
for every rectangular tableau and arbitrary number fields/nonfree projective
modules of positive constant rank. The normalization is exactly the accepted
asymptotic producer's correction. Kernel build passed (9194 jobs, 9.5 seconds);
all twenty-eight transitive probes passed (4.1 seconds), foundational-only.
Independent honesty/source review accepted the normalization and tableau
independence. A rewrite elaboration timeout was repaired by explicit theorem
composition without increasing heartbeat limits.

`Slope/Geometric/PairingInjective.lean` proves injectivity of the actual nonzero
canonical pairing, using its contragredient equivariance and the concrete
complex irreducibility theorem. Kernel build passed (9181 jobs, 127.7 seconds);
all twenty-nine transitive probes passed (38.8 seconds), foundational-only.
Independent honesty/source review accepted the diagonal action and descent.

The geometric slope inequality remains open; the next consumer is intrinsic
contraction-metric identification, image-slope comparison and the verified
asymptotic limit.
Existing ARITH, SPECHT, and GEOM producers are unchanged.

Tooling: the first check invocation used unsupported `-p` and did not run Lean;
the corrected explicit-root command above passed. Guarded LSP retained a stale
import diagnostic for `Bundle.lean` after its dependency build, so its proof
loop uses serialized `horizon check --lean` pending a fresh LSP document.
The intermediate bundle checks exposed ordinary elaboration and conjugation
normalization errors; all were repaired before the successful module build.
