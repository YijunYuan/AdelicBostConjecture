# Balanced projections: verified boundary

Manuscript Lemma 7.2 is **not yet formalized**. The accepted code proves the
intrinsic partial-trace and actual exponential-frame Gram first-variation producers. It contains no
geometric-semistability theorem or assumed orbit criterion.

## Checked producers

| Commit | Module | Result |
| --- | --- | --- |
| `fdb954d` | `Balanced.PartialTrace` | Basis-independent contraction of tensor endomorphisms; both trace-pairing identities and scalar/traceless consequences. |
| `3361234` | `Balanced.ProjectionTrace` | Actual orthogonal-projection trace as an orthonormal frame sum; `IsBalanced` is exactly the two scalar partial-trace equations. |
| `ee2abe7` | `Balanced.GramDerivative` | Determinant derivative at the identity, complex and real Gram variation, and `IsBalanced.hasDerivAt_re_gramDet_zero`. |
| `5e76175` | `Balanced.ExponentialFlow` | Differentiation of the actual tensor exponential frame and `IsBalanced.hasDerivAt_re_gramDet_tensor_exp_zero`. |

The exponential consumer constructs the actual frame rather than assuming
its derivative. It needs no Hermitian hypothesis for this first-variation
statement; Hermitian hypotheses enter the still-open convexity argument.
The real scalar instances use the canonical restriction along ℝ → ℂ.
Zero-dimensional auxiliary cases are permitted; the open headline retains
the source requirement that the subspace is nonzero.

All checks used the serialized resource slot and explicit workspace root:

```sh
"$HORIZON_BIN" --root /home/yijunyuan/bc-workspace check BostConjecture.Balanced.PartialTrace
"$HORIZON_BIN" --root /home/yijunyuan/bc-workspace check BostConjecture.Balanced.ProjectionTrace
"$HORIZON_BIN" --root /home/yijunyuan/bc-workspace check BostConjecture.Balanced.GramDerivative
"$HORIZON_BIN" --root /home/yijunyuan/bc-workspace check BostConjecture.Balanced.ExponentialFlow
"$HORIZON_BIN" --root /home/yijunyuan/bc-workspace check --lean verification/BalancedAxioms.lean
```

Results in run `0006`, session `0002-horizon-BOST-BALANCED`: warning-free
builds of 1,897, 2,813, 2,815 and 2,821 jobs; 19 transitive axiom probes passed,
each reporting only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorryAx` or custom axioms occur in those export cones.
Guarded LSP diagnostics were used after edits. The new consumer initially
reported stale imports; the serialized dependency build and reopening via an
import-header change restored diagnostics. The exponential producer's final
LSP diagnostics and kernel build were warning-free (34.1s for the latter).
Its intermediate missing imports and coercion errors were repaired. The
updated axiom file's LSP retained a stale-import error after the producer
build; the serialized kernel check passed all 19 probes in 36.0s.
No unguarded build was used.

Root integration was handed to SPECHT in `I-0049`; it is pending in this
checkpoint and is not implied by the scoped builds.

## Remaining mathematical producers

1. The induced norm on the full exterior power and its Gram determinant
   identity; spectral exponential expansion and convexity.
2. Determinant-one unitary/logarithm adapters for the already checked polar
   decomposition port (`TJHeeringa/mathlib4`, revision
   `41260205df493c627e1ac0e54812cfdeb6517fbc`, PR 45002).
3. The canonical algebraic tensor/exterior representation and homogeneous
   invariant-polynomial interface, coordinated with GEOM in `I-0047`.
4. Constructible images and comparison of complex/Zariski closures,
   special-unitary Zariski density, and finite-degree Haar averaging.
   The blueprint now supplies the mathematical arguments, but there is no
   Lean implementation of these conclusions. Its curve-density proof uses
   finite Noether normalization, finite-map dimension facts, the intersection
   dimension theorem, finite normalization and nonsingularity of complex
   normal curves, and analytic local coordinates. Each used external
   conclusion must be proved or matched to checked library declarations.
5. Exact Plücker semistability and its invariant-polynomial conclusion,
   followed by independent source/math/honesty review and root integration.

The orbit criterion is restricted to the needed pair of special linear
groups with an **algebraic linear action**. It does not apply to arbitrary
abstract linear representations. The finite-degree separation argument uses
neither finite generation of the invariant ring nor a semistability axiom.
The orbit-criterion, exponential-convexity and polar blueprint nodes remain `notready`.

## Source registration

The parent granted the bounded reference extension in `I-0048`.

- `references/maithani-reynolds`: Aryaman Maithani, arXiv:2412.18841v2
  (11 September 2025), unmodified original TeX/PDF/archive. Original labels
  `thm:reynolds-for-lie-group` and `prop:SU-SL-dense` support finite-degree
  averaging and compact-subgroup density. SHA256 values are in the manifest.
- `references/milne-algebraic-geometry`: J. S. Milne, *Algebraic Geometry*
  v6.10 (11 November 2024), original 231-page PDF. PDF page 201 equals
  printed page 201. Its vision-verified mathematical excerpt records
  Proposition 9.6, Theorem 9.7 and Aside 9.8; it is explicitly not a full-page
  transcription. The original aside states closure comparison without proof;
  the blueprint expands the missing density argument using curves.

No source code was copied from these mathematical references. Their original
copyright/license notices are retained. Reference retrieval and the visual
excerpt were performed by the proof owner because an additional writable
helper was prohibited. Read-only source/mathematical review was used.

## Epistemic checkpoint

Claim class: **proved producers**. Before: the analytic proof had no Lean
implementation. After: actual balance implies vanishing Gram first variation
along the actual tensor exponential frame; the first analytic unmet producer
is the full exterior norm and its spectral expansion.
Consumer: `lem:balanced-plucker`, still unproved. The source-backed orbit route
is mathematical blueprint only, with all formal dependencies still open.
Honesty reviewer: used; actual projection and both balance equations are
load-bearing, with no hidden semistability assumption. Its request for explicit
ambient context in the Gram-variation blueprint has been incorporated.
Its followup semantic audit of the exponential consumer also passed. The
orbit/source reviewer verified the new mathematical proofs and original
source anchors; both requested precision edits were incorporated.

## Proposed invariant interface (not yet implemented)

The next interface proposal for `I-0047` uses existing `Representation`,
`SpecialLinearGroup`, `exteriorPower`, and `SymmetricAlgebra`; it creates no
second polynomial-function representation. Below, `K` is a field, `U`, `W`
and `X` are finite-dimensional `K`-spaces, and `G` is a group. The displayed
signatures are design proposals, not checked declarations.

- `InvariantTheory/PluckerAction.lean`:
  `pluckerRepresentation K U W s : Representation K
  (SpecialLinearGroup K U × SpecialLinearGroup K W)
  (⋀[K]^s (U ⊗[K] W))`, sending `(g,h)` to
  `exteriorPower.map s (TensorProduct.map g.val.toLinearMap h.val.toLinearMap)`.
  Algebraicity will be proved for this concrete action by its matrix coefficients.
- `InvariantTheory/Polynomial.lean`:
  `polynomialEval (x : X) : SymmetricAlgebra K (Module.Dual K X) →ₐ[K] K`
  is the universal lift of evaluation of linear forms at `x`;
  `homogeneousPolynomials K X (d : ℕ) : Submodule K
  (SymmetricAlgebra K (Module.Dual K X))` is the `d`th submodule power of
  the range of `SymmetricAlgebra.ι K (Module.Dual K X)`.
  `polynomialRepresentation (ρ : Representation K G X) : Representation K G
  (SymmetricAlgebra K (Module.Dual K X))` is the symmetric-algebra extension
  of `ρ.dual`. Thus `g` acts by pullback along `ρ g⁻¹`.
  `homogeneousInvariants ρ d` is the intersection of the degree submodule
  with `(polynomialRepresentation ρ).invariants`.
- `InvariantTheory/Semistability.lean`:
  `polynomialZariskiClosure (A : Set X) : Set X` consists of the common zeros
  of every element of `SymmetricAlgebra K (Module.Dual K X)` vanishing on `A`.
  For complex `X`,
  `IsGeometricallySemistable (ρ : Representation ℂ G X) (x : X) : Prop`
  means that zero is outside this closure of `Set.range (fun g => ρ g x)`.
  The orbit theorem for the concrete complex Plücker representation will
  prove equivalence with `∃ d > 0, ∃ p : homogeneousInvariants ρ d,
  polynomialEval x p ≠ 0`. No equivalence for arbitrary abstract representations
  is claimed.
- `InvariantTheory/Coaction.lean`: in chosen bases, form the coordinate algebra
  `A` of the pair of special linear groups by quotienting the polynomial ring
  on the two matrix-entry sets by the two determinant-minus-one relations.
  Construct the concrete degree coaction
  `pluckerPolynomialCoaction bU bW s d : homogeneousPolynomials K X d →ₗ[K]
  A ⊗[K] homogeneousPolynomials K X d`, where `X = ⋀[K]^s (U ⊗[K] W)`.
  Fix the left-coaction convention `δ(p)(g,x) = p(ρ(g)x)`; its evaluated
  pullbacks are related by group inversion to `polynomialRepresentation ρ`.
  This avoids mixing the inverse-action representation with the forward
  coordinate coaction.
  The coefficient kernel of `δ - (p ↦ 1 ⊗ p)` is the finite-degree invariant
  module that GEOM can transport under scalar extension. Prove its equivalence
  with the preceding invariant submodule over the needed infinite fields;
  do not assume that invariants under rational points commute with base change.

The use of bases is confined to constructing the coordinate coaction. The
Plücker vector space, polynomial algebra, degree, evaluation and invariant
submodule are intrinsic. GEOM confirmation and checked implementations remain
pending; polynomial laws were inspected but do not yet provide a finite-degree
coefficient API in the pinned library.

Independent review found the proposed objects faithful and requested the
explicit coaction convention above. Remaining interface proofs include the
homogeneous decomposition and finite dimensionality, coordinate-polynomial
evaluation/zero-locus comparison, the degree-subtype kernel versus the
intersection invariant module, rational-point detection over the needed
infinite fields, and scalar-extension compatibility of these maps. Flatness
of a field extension then gives kernel base change; the coordinate coaction's
codomain need not itself be finite-dimensional.
