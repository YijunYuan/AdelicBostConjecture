# Balanced projections: verified boundary

Manuscript Lemma 7.2 is **not yet formalized**. The accepted code proves the
intrinsic partial traces, actual exponential-frame Gram first variation, and
the basis-independent complex Gram metric on the full exterior power. It contains no
geometric-semistability theorem or assumed orbit criterion.

## Checked producers

| Commit | Module | Result |
| --- | --- | --- |
| `fdb954d` | `Balanced.PartialTrace` | Basis-independent contraction of tensor endomorphisms; both trace-pairing identities and scalar/traceless consequences. |
| `3361234` | `Balanced.ProjectionTrace` | Actual orthogonal-projection trace as an orthonormal frame sum; `IsBalanced` is exactly the two scalar partial-trace equations. |
| `ee2abe7` | `Balanced.GramDerivative` | Determinant derivative at the identity, complex and real Gram variation, and `IsBalanced.hasDerivAt_re_gramDet_zero`. |
| `5e76175` | `Balanced.ExponentialFlow` | Differentiation of the actual tensor exponential frame and `IsBalanced.hasDerivAt_re_gramDet_tensor_exp_zero`. |
| `497b5b1` (automatic cross-lane snapshot) | `Balanced.ExteriorMetric` | Full complex exterior Gram metric, uniqueness/basis independence, Gram norm formula and orthonormal exterior basis. |

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

SPECHT confirmed root integration through `Balanced.ExponentialFlow` in
`I-0049/C-0010`: check `975bdb23135a0d4a`, **9,205 jobs warning-free**.
The new exterior metric and Plücker norm leaf require the next root batch.

## Current exterior-metric checkpoint

Run `0006`, session `0004-horizon-BOST-BALANCED` checked
`BostConjecture.Balanced.ExteriorMetric` with the explicit-root serialized
command: **2,841 jobs, warning-free**, 115.8s including setup. The updated
`verification/BalancedAxioms.lean` kernel check passed **27 probes** in 2.6s;
all report only `propext`, `Classical.choice`, and `Quot.sound`.
Guarded LSP diagnostics are clear for the metric and its new Plücker norm
consumer. The `PluckerNorm` serialized build subsequently passed **2,853 jobs**,
warning-free (15.8s including setup), and all **30** updated transitive axiom
probes passed in 3.8s with only the same foundational axioms.

Independent `honesty-reviewer` accepted the actual exterior object, Gram
formula, spanning uniqueness, degree-zero/over-rank cases, instance pattern,
and substantive Plücker norm consumer. No completion of Lemma 7.2 follows.
The read-only reviewer had no working LSP; its independent stdin probe was
stopped without results, and acceptance uses the owner's serialized checks.

Automatic GEOM integration `497b5b1` captured BALANCED's in-flight new files
and blueprint edits, including a then-unfixed coercion in `PluckerNorm`.
The scoped metric check verifies the accepted metric; the Plücker consumer's
coercion is fixed and its scoped build and axiom probes pass. Root integration remains a
separate SPECHT handoff. The automatic cross-lane snapshot was reported in
`I-0049`; it is not evidence that every file in that commit built.

The construction reuses mathlib at revision
`56a005855ea17e0b0958f73ec801ae140b0a1679` (Apache-2.0), specifically
`Module.Basis.exteriorPower` and its coordinate API from
`Mathlib/LinearAlgebra/ExteriorPower/Basis.lean`, `pairingDual` and
`pairingDual_ιMulti_ιMulti` from `ExteriorPower/Pairing.lean`, and Euclidean
coordinate transport from `Analysis/InnerProductSpace/PiL2.lean`.
These are imports, with no copied or modified mathlib source. The existing
`Analysis/InnerProductSpace/ExteriorPower.lean` is **real-only**; it does not
supply the required complex result. Project-local `Tensor.inner_ext_of_span`
is reused for uniqueness and the isometry consumer. Shared attribution
updates belong to SPECHT.

The read-only board audit found the active-item warning intentional: BALANCED
has one active analytic leaf; other active rows include ancestors and other
proof lanes. No unrelated status was changed. Scratch dry-run found no stale
candidates. Indexed Horizon searches stalled; guarded local library search
and actual source inspection supplied the used declarations.

## Remaining mathematical producers

1. Spectral exponential expansion and convexity for the now-constructed
   complex exterior Gram norm. The actual Plücker norm-variation bridge is checked.
2. Determinant-one unitary/logarithm adapters for the already checked polar
   decomposition port (`TJHeeringa/mathlib4`, revision
   `41260205df493c627e1ac0e54812cfdeb6517fbc`, PR 45002).
3. The canonical algebraic tensor/exterior representation and homogeneous
   invariant-polynomial interface, coordinated with GEOM in `I-0047`.
4. Constructible images and comparison of complex/Zariski closures,
   special-unitary Zariski density, and finite-degree Haar averaging.
   The blueprint now supplies the mathematical arguments, but there is no
   Lean implementation of these conclusions. Its independently reviewed affine-density proof uses
   finite Noether normalization, integrally closed polynomial rings and the
   minimal-polynomial kernel theorem, lying over/Nullstellensatz, complex
   polynomial factorization and Cauchy bounds, and finite-dimensional compactness.
   Finite fibers are separated by an explicit polynomial. Root lifting uses
   the actual minimal polynomial, not an arbitrary monic annihilator. This
   replaces the earlier curve-normalization route without an analytic-chart dependency. Each used external
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
  the blueprint supplies the density argument by finite normalization and root bounds.

No source code was copied from these mathematical references. Their original
copyright/license notices are retained. Reference retrieval and the visual
excerpt were performed by the proof owner because an additional writable
helper was prohibited. Read-only source/mathematical review was used.

## Epistemic checkpoint

Claim class: **proved producers**. Before this session: actual tensor exponential-frame Gram stationarity was
proved but the complex exterior metric was missing. After: the full complex
exterior Gram metric and orthonormal basis are checked; the first analytic
unmet producer is spectral expansion/convexity, and the actual Plücker norm-variation
bridge is checked.
Consumer: `lem:balanced-plucker`, still unproved. The source-backed orbit route
is mathematical blueprint only, with all formal dependencies still open.
Honesty reviewer: used; actual projection and both balance equations are
load-bearing, with no hidden semistability assumption. Its request for explicit
ambient context in the Gram-variation blueprint has been incorporated.
Its followup semantic audit of the exponential consumer also passed. The
orbit/source reviewer verified the new mathematical proofs and original
source anchors; both requested precision edits were incorporated.

## Agreed invariant interface (not yet implemented)

The interface confirmed by GEOM in `I-0047/C-0010` uses existing `Representation`,
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
submodule are intrinsic. GEOM confirmation is complete; checked implementations remain
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
