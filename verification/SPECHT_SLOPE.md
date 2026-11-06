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

The exact intrinsic slope and geometric slope inequality remain open.
Existing ARITH, SPECHT, and GEOM producers are unchanged.

Tooling: the first check invocation used unsupported `-p` and did not run Lean;
the corrected explicit-root command above passed. Guarded LSP retained a stale
import diagnostic for `Bundle.lean` after its dependency build, so its proof
loop uses serialized `horizon check --lean` pending a fresh LSP document.
The intermediate bundle checks exposed ordinary elaboration and conjugation
normalization errors; all were repaired before the successful module build.
