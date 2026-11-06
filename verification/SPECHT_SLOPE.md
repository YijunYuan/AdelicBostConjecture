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

The arithmetic bundle is in progress. The determinant-twisted projective module,
its intrinsic slope, and the geometric slope inequality are not yet discharged.
Existing ARITH, SPECHT, and GEOM producers are unchanged.

Tooling: the first check invocation used unsupported `-p` and did not run Lean;
the corrected explicit-root command above passed. Guarded LSP retained a stale
import diagnostic for `Bundle.lean` after its dependency build, so its proof
loop uses serialized `horizon check --lean` pending a fresh LSP document.
