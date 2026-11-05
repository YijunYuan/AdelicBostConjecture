# Balanced projections: verified boundary

Manuscript Lemma 7.2 is **not yet formalized**. The accepted code proves the
intrinsic partial traces, actual exponential-frame Gram first variation, and
the basis-independent complex Gram metric on the full exterior power, actual
Plücker norm stationarity, and Hermitian exterior exponential convexity. It also supplies intrinsic polynomial evaluation, homogeneous invariants,
and the elementary implication from a nonvanishing homogeneous invariant to
zero excluded from orbit closure. The converse orbit criterion is unproved.

## Checked producers

| Commit | Module | Result |
| --- | --- | --- |
| `fdb954d` | `Balanced.PartialTrace` | Basis-independent contraction of tensor endomorphisms; both trace-pairing identities and scalar/traceless consequences. |
| `3361234` | `Balanced.ProjectionTrace` | Actual orthogonal-projection trace as an orthonormal frame sum; `IsBalanced` is exactly the two scalar partial-trace equations. |
| `ee2abe7` | `Balanced.GramDerivative` | Determinant derivative at the identity, complex and real Gram variation, and `IsBalanced.hasDerivAt_re_gramDet_zero`. |
| `5e76175` | `Balanced.ExponentialFlow` | Differentiation of the actual tensor exponential frame and `IsBalanced.hasDerivAt_re_gramDet_tensor_exp_zero`. |
| `497b5b1` (automatic cross-lane snapshot) | `Balanced.ExteriorMetric` | Full complex exterior Gram metric, uniqueness/basis independence, Gram norm formula and orthonormal exterior basis. |
| `76a3ad5` | `Balanced.PluckerNorm` | Actual Plücker norm equals one; balanced tensor exponential norm squared has derivative zero. |
| `eae8dac` | `Balanced.SpectralExpansion` | Actual exterior spectral expansion, convexity and global minimum from stationarity. |

The exponential consumer constructs the actual frame rather than assuming
its derivative. It needs no Hermitian hypothesis for this first-variation
statement; Hermitian hypotheses enter the checked spectral convexity argument.
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

SPECHT confirmed root integration through `Balanced.PluckerNorm` at
`4d40509`, root blob `d29b590246c8925d6cce74559397b56db2cc8de5`:
**9,210 jobs warning-free** at 2026-11-05 22:11:39 UTC. It subsequently
integrated SpectralExpansion and InvariantTheory.Semistability: **9,223 jobs
warning-free** at 22:47:30 UTC, check `975bdb23135a0d4a`, root blob
`1e82a0a65cf1c08b5cb2f375cfa2f0c6c580183c`. TensorExponential and the
new polar leaves require the next root batch.

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
coercion is fixed and its scoped build, axiom probes and root integration pass. The automatic cross-lane snapshot was reported in
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

## Hermitian spectral checkpoint

`BostConjecture.Balanced.SpectralExpansion` passed its explicit-root serialized
kernel build: **2,861 jobs, warning-free**, 7.2s. The updated axiom audit passed
**40 probes** in 5.7s; all report only `propext`, `Classical.choice`, and
`Quot.sound`. Guarded LSP diagnostics are clear. Independent honesty review
accepted the exact spectral formula, real eigenvalues derived from Mathlib's
Hermitian spectral theorem, nonnegative coefficients, convexity and the
minimum theorem using genuine `HasDerivAt` stationarity. It found no defect
or hidden spectral assumption. Degree zero and over-rank cases are valid.

The new imports reuse Mathlib's `LinearMap.IsSymmetric.eigenvectorBasis`,
`eigenvalues`, and `apply_eigenvectorBasis` from
`Analysis/InnerProductSpace/Spectrum.lean`, the exponential series from
`Analysis/SpecialFunctions/Exponential.lean`, and convex derivative results
from `Analysis/Convex/Deriv.lean`, at the pinned revision above, without copying
or modifying source. The tensor product flow is not yet identified with the
single Hermitian exponential in this theorem; that consumer bridge is open.

## Intrinsic polynomial checkpoint

The serialized scoped builds passed for `InvariantTheory.Polynomial`
(**1,719 jobs**, 3.6s), `PolynomialAction` (**2,358 jobs**, 46.7s), and
`Semistability` (**2,675 jobs**, 20.5s), all warning-free. The updated
`BalancedAxioms` check passed **67 transitive probes** in 17.4s, all using
only the three foundational axioms. LSP is clear on all three sources;
the audit initially reported stale imports, then its new import and the
serialized dependency checks restored clear diagnostics.

The actual degree spaces are proved finite-dimensional. The inverse-pullback
representation, forward fixed-point bridge, and equivalence of homogeneous
invariants with fixed vectors of the degree representation are checked.
The canonical closure uses all vanishing intrinsic polynomials; a
nonvanishing positive-degree invariant excludes zero from the orbit closure.
No converse or equality with Euclidean closure is proved.

Independent honesty/API review accepted these definitions and proofs. Its
finite-field precision edit was incorporated: polynomial actions are defined
intrinsically by pullback, not by their values as functions. Its attachment
correction was also incorporated: `def:balanced-vector-semistability` records
the complex vector orbit-closure predicate, while the source's Plücker-line
invariant-existence definition and its equivalence remain under the open
orbit criterion. Root integration of these three modules passed in the 9,223-job batch above.

Imports reuse Mathlib's `SymmetricAlgebra.lift`, dual evaluation/transposition,
`Submodule.pow_induction_on_left'`, `Submodule.FG.pow`,
`Representation.subrepresentation` and `Representation.invariants`, at the
pinned Apache-2.0 revision above, without copying or modifying source.
Project consumers are PolynomialAction and Semistability, followed by the
pending Plücker/coaction/orbit criterion and GEOM base-change consumers.

## Tensor exponential checkpoint

`Balanced.TensorExponential` passed its serialized scoped build: **2,869 jobs**,
warning-free, 45.4s. It proves the actual tensor-sum exponential identity,
Hermitian symmetry of the generator, tensor exterior convexity and the
balanced Plücker squared-norm lower bound one. Independent honesty review
accepted the object/instance alignment and substantive use of balance,
traces, Hermitian symmetry and the initial norm. The expanded **71-probe**
audit passed in 12.5s with only foundational axioms; the producer node now
carries `leanok`. Root integration is handed to SPECHT.

Local aliases of the existing tensor normed-group and complex normed-space
instances resolved a typeclass inference failure; no metric was changed.
A guarded `lean_multi_attempt` timed out after 300s during this diagnosis;
ordinary final LSP diagnostics and the subsequent kernel build are clear.
The latest graph sync recorded 218 blueprint nodes, 1441 Lean declarations,
1030 edges and no unresolved-reference warnings. The 728 unattached
helper/import declarations are intentional, consistent with `I-0004`.

## Determinant-one polar checkpoint

`Balanced.PolarLog` passed **3,128 jobs** (3.4s),
`Balanced.ExponentialDeterminant` **2,863 jobs** (14.0s), and
`Balanced.SpecialLinearPolar` **3,178 jobs** (19.0s), all warning-free
under explicit-root serialization. The expanded **86-probe** kernel audit
passed in 12.1s with only `propext`, `Classical.choice`, and `Quot.sound`.
The exact export `specialLinear_polar` constructs a determinant-one unitary
equivalence and a traceless Hermitian operator whose exponential gives the
factorization of the supplied actual `SpecialLinearGroup` element.
Independent honesty review accepted the actual polar factor, proved strict
positivity for the totalized CFC logarithm, positive determinant root choice,
real-trace argument and dimension-zero case. Root integration is pending.
The audit LSP still reports stale imports; the serialized kernel check passed
all 86 probes. This stale-editor diagnostic is not reported as a build failure.

This substantively consumes the checked PR45002 `abs`, `ker_abs_eq`,
`norm_abs_apply`, `abs_comp_abs`, `polar` and `polar_comp_abs` at upstream
revision `41260205df493c627e1ac0e54812cfdeb6517fbc`; its existing attribution,
license and port are unchanged. It also imports the pinned Mathlib CFC
`log`, `IsSelfAdjoint.log` and `exp_log` from
`Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Basic.lean`
(Frédéric Dupuis, Apache-2.0), the Hermitian trace/eigenvalue identities,
and standard determinant/adjoint formulas, without copying source.

## Remaining mathematical producers

1. Complete root integration of the tensor exponential producer; the actual
   tensor-flow bridge and balanced norm minimum pass kernel and axiom checks.
2. Assemble the norm bound for the full special-linear Plücker orbit from
   the checked tensor minimum and determinant-one polar reduction.
3. The canonical algebraic tensor/exterior representation, coordinate coaction
   and base-change/detection bridges, coordinated with GEOM in `I-0047`.
   Intrinsic polynomials, homogeneous degree, finite dimensionality and
   homogeneous invariants are now checked.
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
The orbit-criterion blueprint nodes remain `notready`. Only the
checked analytic producers carry `leanok`; Lemma 7.2 remains open.

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
exterior Gram metric, Plücker norm stationarity and Hermitian spectral
expansion/convexity are checked. The first unmet analytic producer is the
assembly of the full special-linear orbit norm bound. Tensor-flow and
determinant-one polar/log reduction are now checked.
Consumer: `lem:balanced-plucker`, still unproved. The source-backed orbit route
is mathematical blueprint only, with all formal dependencies still open.
Honesty reviewer: used; actual projection and both balance equations are
load-bearing, with no hidden semistability assumption. Its request for explicit
ambient context in the Gram-variation blueprint has been incorporated.
Its followup semantic audit of the exponential consumer also passed. The
orbit/source reviewer verified the new mathematical proofs and original
source anchors; both requested precision edits were incorporated.

## Agreed invariant interface (partial implementation checked)

The interface confirmed by GEOM in `I-0047/C-0010` uses existing `Representation`,
`SpecialLinearGroup`, `exteriorPower`, and `SymmetricAlgebra`; it creates no
second polynomial-function representation. Below, `K` is a field, `U`, `W`
and `X` are finite-dimensional `K`-spaces, and `G` is a group. Polynomial, PolynomialAction and Semistability below are checked;
PluckerAction and Coaction remain design proposals.

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
- `InvariantTheory/PolynomialAction.lean`:
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
submodule are intrinsic. GEOM confirmation is complete; the coordinate
coaction implementation remains pending. Polynomial laws were inspected but do not provide a finite-degree
coefficient API in the pinned library.

Independent review found the proposed objects faithful and requested the
explicit coaction convention above. Remaining interface proofs include the
homogeneous decomposition, coordinate-polynomial evaluation/zero-locus
comparison, the degree-subtype coaction kernel versus fixed vectors,
rational-point detection over the needed
infinite fields, and scalar-extension compatibility of these maps. Flatness
of a field extension then gives kernel base change; the coordinate coaction's
codomain need not itself be finite-dimensional.
