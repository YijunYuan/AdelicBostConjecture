# Determinant–Specht and geometric slope evidence

The assigned mathematical route is proved: actual determinant–Specht bundles,
their intrinsic metrics and exact slopes, and the geometric slope inequality
from actual complex, binary, and algebraically closed characteristic-zero
Plücker invariants. All thirty-nine transitive axiom probes are foundational-only.
MAIN integrated the exact proof revision `8c80c92` at root `d7bdece`; its root
check passed 9387 jobs without warnings at 2026-11-06 04:14:47 UTC. The assigned
objective is complete; the whole Bost main theorem is not claimed complete.

The first checked producer is the actual integral orbit-lattice representation
in `Arithmetic/Specht/Representation.lean`.
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

`Slope/Geometric/PairingMetric.lean` identifies the actual dual determinant
and finite-family metrics with GEOM's prescribed forms and proves contraction
of the actual canonical pairing at every embedding. Final module build passed
(9182 jobs, 226.3 seconds); all thirty-two transitive probes passed (28.4 seconds),
foundational-only. Independent review accepted the nonfree base-change bridges
and normalization. The combined import check initially found generated local
instance-name collisions; explicit names fixed them before the successful probe.

`Slope/Geometric/ImageSlope.lean` proves both inequalities through the actual
image, without saturation, and `PairingSlope.lean` derives the finite-degree
slope estimate with exact Specht corrections. Kernel builds passed (9184 jobs,
16.1 seconds; 9203 jobs, 15.2 seconds); all thirty-five transitive probes passed
(8.5 seconds), foundational-only. Independent reviews accepted the actual range
metric, rank argument, concrete semistability consumer and duality signs.

`Slope/Geometric/InvariantSlope.lean` proves the geometric slope inequality
from an actual positive-degree complex Plücker invariant with nonzero evaluation.
GEOM supplies nonzero pairings over the original ring; the exact finite-degree
estimate and the accepted Specht asymptotic give the limit. The chosen widths
tend to infinity because tableau cardinalities force degree = rank × width.
`BinaryInvariantSlope.lean` consumes GEOM's binary invariant producer directly.
Module checks passed (9286 jobs, 76.1 seconds; 9289 jobs, 12.6 seconds); all
thirty-eight transitive probes passed (8.9 seconds), with exactly `propext`,
`Classical.choice`, and `Quot.sound`. The final honesty review accepted both
actual-invariant consumers and the finite-projective number-field scope.
Fresh source review confirmed the actual consumer chain and requested that the
checked blueprint state its complex invariant witness explicitly. This repair
was made: the separately unproved algebraic-closure field-extension interface
is not silently certified by the geometric node.

The final bounded extension `slope_le_of_invariant` accepts an actual invariant
over any algebraically closed characteristic-zero field `F : Type`. It directly
uses GEOM's original-ring nonvanishing producer, then the same arithmetic
comparison; the complex theorem is its specialization with unchanged signature.
No map from `F` to ℂ, invariant descent, or field-extension invariance is assumed.
The final dependency build `check BostConjecture.Slope.Geometric.BinaryInvariantSlope`
passed (9289 jobs, 257.8 seconds), rebuilding the generalized theorem and binary
consumer. The complete thirty-nine-declaration probe passed (101.5 seconds)
with only the three foundational axioms above. Both independent source-fidelity
and honesty reviewers inspected and accepted the exact implementation.

The requested geometric slope route is proved and root-integrated. MAIN recorded
the root acceptance in `02fa230`, including equality of the checked 220-module
project dependency cone. Both owner and shared graph refreshes succeeded; the
final shared refresh reported 356 blueprint nodes and 2360 declarations with no
unresolved references. Its 1126 unattached helper/draft warnings are coverage
warnings, not missing theorem dependencies. Direct inspection of
`thm:geometric-slope` confirms the general invariant statement, all four Lean
attachments, and `lean_ok`. TENSOR-SEMI accepted the binary endpoint for its
balance consumer. The downstream tensor-semistability/main-theorem work remains
owned by TENSOR-SEMI and MAIN.

The migrated `lem:determinant-isotypic` remains `notready` solely
for its additional, unused full generic SL-fixed-space assertion; this is not
an assumption or dependency of the proved geometric endpoint. The actual
complex determinant–Specht representation equivalence is proved separately.
Existing ARITH, SPECHT, and GEOM producers are unchanged.

Tooling: the first check invocation used unsupported `-p` and did not run Lean;
the corrected explicit-root command above passed. Guarded LSP retained a stale
import diagnostic for `Bundle.lean` after its dependency build, so its proof
loop uses serialized `horizon check --lean` pending a fresh LSP document.
The intermediate bundle checks exposed ordinary elaboration and conjugation
normalization errors; all were repaired before the successful module build.
