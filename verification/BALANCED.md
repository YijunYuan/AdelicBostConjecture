# Balanced projections: verified boundary

Manuscript Lemma 7.2 is **not yet formalized**. The accepted code proves the
intrinsic partial traces, actual exponential-frame Gram first variation, and
the basis-independent complex Gram metric on the full exterior power, actual
Plücker norm stationarity, Hermitian exterior exponential convexity, determinant-one
polar factorization, and the full actual special-linear orbit norm bound and
Euclidean closure exclusion. It also supplies polynomial matrix coefficients, the forward coordinate pullback on every homogeneous degree, rational-point detection, and an explicit coefficient kernel equal to the canonical homogeneous invariant submodule, together with intrinsic polynomial evaluation, homogeneous invariants,
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

## Full Plücker action checkpoint

`InvariantTheory.PluckerAction` passed the explicit-root serialized scoped
build: **2,027 jobs, warning-free**, 23.9s. It is the actual exterior power
of the forward tensor action of the two Mathlib special linear groups.
Its source was captured by automatic cross-lane snapshot `f55b9fd` before
the owning evidence commit. Independent honesty review accepted its group
law, wedge formula and use by the full-orbit norm proof. The blueprint
uses the intended finite-dimensional setting; the generic Lean construction
also allows Mathlib's totalized determinant convention outside that setting.

`Balanced.OrbitNorm` at `b94d6c3` then passed **3,188 jobs, warning-free**,
55.9s including setup. Its exports `IsBalanced.one_le_plucker_norm_sq` and
`IsBalanced.zero_not_mem_closure_plucker_orbit` consume the full actual
special-linear action, polar reduction, tensor exponential minimum and
exterior Gram isometry. The expanded **92-probe** serialized kernel audit
passed in 8.6s: only `propext`, `Classical.choice`, and `Quot.sound`, with
no `sorryAx` or additional axioms. Independent honesty review accepted the
exact analytic conclusion and requested the direct headline dependency on
this producer, now incorporated. The first scoped OrbitNorm build failed on
two coercion/instance inference issues; explicit linear-map equality and
the typed norm-zero lemma repaired both. Final guarded LSP diagnostics are
clear. The earlier stale-import diagnostic was cleared by reopening with an
import-header change. Root integration of the newest leaves is requested
in `I-0060`; the last confirmed root boundary remains the one recorded above.

Boundary maintenance: the roadmap now marks only the analytic subtask done
and the orbit criterion active. The earlier independent board-hygiene review
accepted concurrent lanes and active ancestors; the current 12-active-item
warning remains intentional. Graph sync reports 230 blueprint nodes, 1,568
Lean declarations and 1,104 edges, with 775 unattached helper declarations
across the concurrent project; the new source-facing exports are attached.
The scratch cleanup dry run found no stale candidates. No helper or check
was left running for this batch.

## Remaining mathematical producers

1. Complete root integration of the newest checked producers.
2. Rational-point detection and scalar-extension compatibility for the checked
   coordinate pullback, coordinated with GEOM in `I-0047`. The full and
   homogeneous pullbacks now evaluate to the actual Plücker action. The
   converse from rational-point invariance to coefficientwise fixedness is open;
   the sufficient coefficientwise-fixed implication is checked.
3. Constructible images and comparison of complex/Zariski closures,
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
4. Exact Plücker semistability and its invariant-polynomial conclusion,
   followed by independent source/math/honesty review and root integration.

The orbit criterion is restricted to the needed pair of special linear
groups with an **algebraic linear action**. It does not apply to arbitrary
abstract linear representations. The finite-degree separation argument uses
neither finite generation of the invariant ring nor a semistability axiom.
The orbit-criterion blueprint nodes remain `notready`. Only the
checked analytic and elementary polynomial producers carry `leanok`; Lemma 7.2 remains open.

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

## Prior analytic epistemic checkpoint

Claim class: **proved producers**. Before this session: actual tensor exponential-frame Gram stationarity was
proved but the complex exterior metric was missing. After: the full complex
exterior Gram metric, Plücker norm stationarity, Hermitian spectral
expansion/convexity, tensor flow, determinant-one polar/log reduction and
the full actual special-linear orbit norm bound are checked. Zero is excluded
from the Euclidean orbit closure. The first unmet conclusion is its algebraic
closure comparison, followed by positive-degree invariant existence.
Consumer: `lem:balanced-plucker`, still unproved. The source-backed orbit route
has a complete reviewed mathematical blueprint; its constructibility,
Euclidean/Zariski comparison, density and averaging conclusions remain unproved.
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
and `X` are finite-dimensional `K`-spaces, and `G` is a group. Polynomial,
PolynomialAction, Semistability, PluckerAction, PluckerCoordinates,
SpecialLinearCoordinates and the coordinate pullbacks in Coaction are checked.
The concrete matrix polynomiality and evaluated degree map are proved.
Rational-point detection, the converse fixed-point bridge, coordinate Hopf
identities and scalar-extension compatibility remain open, as does the
Euclidean-to-algebraic orbit-closure comparison.

- `InvariantTheory/PluckerAction.lean`:
  `pluckerRepresentation K U W s : Representation K
  (SpecialLinearGroup K U × SpecialLinearGroup K W)
  (⋀[K]^s (U ⊗[K] W))`, sending `(g,h)` to
  `exteriorPower.map s (TensorProduct.map g.val.toLinearMap h.val.toLinearMap)`.
  `PluckerCoordinates` now proves polynomiality of its actual matrix coefficients
  and every orbit map in tensor/exterior bases.
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
- `InvariantTheory/SpecialLinearCoordinates.lean` forms the finite-type coordinate
  algebra `A` by the two determinant-minus-one relations and proves that its
  algebra-valued points are actual pairs of Mathlib special linear matrices.
- `InvariantTheory/Coaction.lean` constructs the concrete degree map
  `pluckerPolynomialCoaction bU bW s d : homogeneousPolynomials K X d →ₗ[K]
  A ⊗[K] homogeneousPolynomials K X d`, where `X = ⋀[K]^s (U ⊗[K] W)`.
  Fix the left-coaction convention `δ(p)(g,x) = p(ρ(g)x)`; its evaluated
  pullbacks are related by group inversion to `polynomialRepresentation ρ`.
  This avoids mixing the inverse-action representation with the forward
  coordinate coaction.
  The intended coefficient kernel is `ker (δ - (p ↦ 1 ⊗ p))`.
  Coefficientwise fixedness implies the existing homogeneous-invariant predicate.
  This kernel is now proved equal to the canonical invariant submodule over
  infinite fields with nonempty bases. Scalar-extension compatibility remains
  to be proved; rational-point invariance is not assumed to commute with base change.

The use of bases is confined to constructing the coordinate coaction. The
Plücker vector space, polynomial algebra, degree, evaluation and invariant
submodule are intrinsic. GEOM confirmation is complete; the coordinate
pullback and its degree restriction are implemented. No Hopf coaction structure
or its identities are claimed by this checkpoint. Polynomial laws were inspected but do not provide a finite-degree
coefficient API in the pinned library.

Independent review found the proposed objects faithful and requested the
explicit coaction convention above. Remaining interface proofs include the
homogeneous decomposition, zero-locus comparison,
and scalar-extension compatibility of these maps. The degree-subtype kernel
versus fixed vectors and rational-point detection over infinite fields are now proved. Flatness
of a field extension then gives kernel base change; the coordinate coaction's
codomain need not itself be finite-dimensional.

## Algebraic coordinate checkpoint

Run `0006`, session `0006-horizon-BOST-BALANCED` adds three checked producers:

| Commit / module | Checked conclusion | Serialized build |
| --- | --- | --- |
| `d0bf835`, `InvariantTheory.PluckerCoordinates` | The universal tensor entries and exterior minors evaluate to the actual action on every exterior vector. | `33a63fa2553139f3`, 2,034 jobs, warning-free (21.8s). |
| `392ba05`, `InvariantTheory.SpecialLinearCoordinates` | The determinant-one quotient is finite type and represents actual SL pairs over every commutative base algebra. | `7ff26a0219378861`, 1,816 jobs, warning-free (2.8s). |
| `35770db` (automatic ARITH snapshot), `InvariantTheory.Coaction` | Full and degree-restricted coordinate pullbacks evaluate to the existing intrinsic forward action; coefficientwise fixedness implies homogeneous invariance. | `c0f9424df17fc9eb`, 2,406 jobs, warning-free (6.3s). |

All commands use `"$HORIZON_BIN" --root /home/yijunyuan/bc-workspace check`
with the named module. Guarded LSP diagnostics are clear. The first coordinate-ring
build failed on two quotient-evaluation coercions; the corrected build above
passed. A rewriting step in the fixedness implication hit the default heartbeat
limit; an explicit congruence proof removed it without raising any limit.
Deprecated tensor induction calls were replaced before the accepted build.
The expanded `BalancedAxioms.lean` serialized check passed all **120** transitive
probes in 2.6s, each reporting a subset of `propext`, `Classical.choice`, and
`Quot.sound`, with no `sorryAx` or custom axioms. Its preceding 105-probe check
also passed; these are separate source snapshots.

Independent honesty/source review accepted the actual objects, arbitrary-vector
consumers, dimension-zero and over-rank cases, quotient point equivalence,
forward convention and flatness-based degree restriction. Its two metadata
corrections were applied: the coordinate ring has no false dependency on the
Plücker minor lemma, and the degree node no longer claims an unexported
uniqueness theorem. These are proved producers, not invariant-existence results.

The new modules import, without copying or modifying, Mathlib at the pinned
Apache-2.0 revision above: `Module.Basis.tensorProduct_repr_tmul_apply` from
`LinearAlgebra/TensorProduct/Basis.lean`; `basis_coord`, `basis_apply` and
`ιMultiDual_apply_ιMulti` from `LinearAlgebra/ExteriorPower/Basis.lean`;
`RingHom.map_det` and `LinearMap.det_toMatrix` from `LinearAlgebra/Determinant.lean`;
`Matrix.SpecialLinearGroup` from `LinearAlgebra/Matrix/SpecialLinearGroup.lean`;
`Ideal.Quotient.liftₐ` and `Algebra.FiniteType.quotient`; and
`Submodule.toBaseChange.toLinearEquiv` from `RingTheory/Flat/Basic.lean`.
Consumers are the three named modules; GEOM's invariant base-change consumer
still needs scalar-extension compatibility. The converse fixedness and detection
are now proved below. Shared attribution and root imports transferred to GEOM
under I-0074 after SPECHT completion.

## Rational-point and invariant-kernel checkpoint

The same session adds the following proved producers:

- `InvariantTheory.LocalizationDetection` (`cd7edda`): a polynomial localization
  at a nonzero denominator is detected by rational points of its principal open
  over any infinite field. Check `d8c4a4978c20cdeb`, 1,538 jobs, warning-free, 9.0s.
- `InvariantTheory.SpecialLinearDetection` (source initially captured by automatic
  snapshot `31c1bf4`; reviewed completion `7f6bb36`): the determinant-one quotient
  embeds into the localization at the product of universal determinants, using
  row normalization with the actual unit inverse. A proved left inverse makes
  this embedding injective, and actual rational SL pairs detect the quotient.
  Check `8547ce09ab06d481` passed warning-free in 20.1s.
- `InvariantTheory.InvariantDetection` (`7896195`, with earlier source captured
  by the CLOSURE baseline `f07e6af`): tensor coefficient detection proves
  `mem_homogeneousInvariants_iff_pluckerPolynomialCoaction_eq` and
  `ker_pluckerInvariantConstraint`. The explicit map is the actual degree
  coordinate map minus `p ↦ 1 ⊗ p`; its kernel equals the existing homogeneous
  polynomial representation's invariant submodule. Check `a02d77c1b9e399ed`
  passed **2,411 jobs warning-free**, 68.6s, at 2026-11-06 00:05:08 UTC.

The small Coaction refactor now reuses Mathlib's canonical
`Matrix.SpecialLinearGroup.toLin_equiv` rather than rebuilding the matrix
subtype. Its repeated scoped check passed **2,406 jobs warning-free**, 31.7s,
at 2026-11-05 23:57:19 UTC. The expanded audit at `1e19bc3` passed **137
transitive probes** in 18.6s, all reporting subsets of `propext`,
`Classical.choice`, and `Quot.sound`; no `sorryAx` or custom axiom appears.
Independent honesty/source/mathematical review accepted the retraction,
actual-point detection, tensor detection, intrinsic action bridge and exact
kernel equality. Initial elaboration/coercion errors and default-heartbeat
failures were repaired by explicit congruence and injectivity proofs without
raising limits; accepted LSP and kernel checks are warning-free.

These modules additionally import Mathlib's localization-away lifting and
surjectivity API (`RingTheory/Localization/Away/Basic.lean`), infinite-field
polynomial extensionality, `TensorProduct.equivFinsuppOfBasisRight`
(`LinearAlgebra/TensorProduct/Basis.lean`), and `toLin_equiv`
(`LinearAlgebra/SpecialLinearGroup.lean`), at the same pinned revision and
Apache-2.0 license. No Mathlib source is copied or modified. The normalization
argument adapts the retraction in the registered Maithani source's SU/SL
Zariski-density proof; it does not claim that density theorem is formalized.

SPECHT's completed root handoff `e2e7039` includes OrbitNorm and Coaction:
root blob `30f3a016666f4a42f99e905a434b65f63c1f8770`, **9,263 jobs warning-free**
at 2026-11-05 23:42:25 UTC. The new invariant-detection modules were handed
to GEOM in I-0076 for its next root/attribution batch; that integration remains
pending at this checkpoint.

## Next-producer handoff

The actual polynomial action, determinant-one coordinate algebra, forward
homogeneous coordinate map, rational-point detection and invariant-kernel
identification are proved. Scalar-extension compatibility of these maps is the
remaining algebraic bridge for GEOM's invariant descent consumer. GEOM's checked
`Geometry.PluckerPolynomial` API at `c8b4a4b` supplies `polynomial_ext`, the
Plücker pullback and its degree/equivariance consumer.

The source-facing orbit criterion still requires the closure comparison
assigned to CLOSURE, special-unitary density, finite-degree Haar averaging and
homogeneous extraction. BALANCED retains the actual polynomial-image/orbit
identification and final assembly. The norm bound and invariant-kernel equality
do not alone prove Lemma 7.2, which remains open.

## Independent complex-closure producer (I-0072 / I-0074)

Parent activated BOST-CLOSURE in the freed SPECHT slot under I-0074; four
proof writers remain the maximum. The exact output proposition below was
type-checked with the existing definitions (the theorem is unproved):

```lean
theorem closure_polynomial_image_zeroLocus
    {σ τ E : Type*} [Fintype σ] [Fintype τ]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (b : Module.Basis τ ℂ E) (I : Ideal (MvPolynomial σ ℂ))
    (q : τ → MvPolynomial σ ℂ) :
    closure ((fun a : σ → ℂ => ∑ i, MvPolynomial.eval a (q i) • b i) ''
      MvPolynomial.zeroLocus ℂ I) =
    polynomialZariskiClosure (K := ℂ)
      ((fun a : σ → ℂ => ∑ i, MvPolynomial.eval a (q i) • b i) ''
        MvPolynomial.zeroLocus ℂ I)
```

Prerequisite imports for the signature are `InvariantTheory.Semistability`,
`Mathlib.RingTheory.Nullstellensatz`, and
`Mathlib.Analysis.Normed.Module.FiniteDimension`. The successor must prove the
used constructibility, finite-normalization/root-persistence density, and
intrinsic-versus-coordinate polynomial zero-locus bridge, importing existing
checked library results wherever they match. It must not assume closure
comparison, constructibility or root persistence as a hypothesis.
The existing complete blueprint proofs are `lem:balanced-constructible-image`
and `lem:balanced-constructible-closure`; source anchors are Milne page 0201
and manuscript page 0012. The finite-normalization proof is an explicit
supplement to Milne's unproved closure-comparison aside.

CLOSURE exclusively owns: `InvariantTheory/ComplexClosure/**`,
`blueprint/src/complex_closure.tex`, `verification/ComplexClosureAxioms.lean`,
and `verification/COMPLEX_CLOSURE.md`. The two complete blueprint nodes were
moved verbatim (117 lines) under bounded authorization at `ecbcee9`; GEOM has
added the shared include after compactness and before main. Both nodes remain
notready; CLOSURE never writes compactness or the root/shared attribution files.

BALANCED retains the canonical polynomial, semistability and Plücker action
definitions and their source-facing assembly. The concrete consumer takes
`σ = (ι × ι) ⊕ (κ × κ)`, `I = specialLinearPairIdeal ℂ ι κ`,
`b = (bU.tensorProduct bW).exteriorPower s`, and
`q = pluckerOrbitPolynomial bU bW s z`. The checked `InvariantTheory.OrbitImage.pluckerOrbit_polynomial_image`
identifies this image with the actual orbit; the returned closure
equality then turns `IsBalanced.zero_not_mem_closure_plucker_orbit` into
the existing `IsGeometricallySemistable` predicate. Invariant extraction
remains BALANCED-owned and is still required for the source's Plücker-line
conclusion and GEOM consumer.


## Actual orbit-image checkpoint

`InvariantTheory.OrbitImage` at `84a679f` proves both the complete zero-locus
parametrization by intrinsic special-linear pairs and the full equality
`pluckerOrbit_polynomial_image`. This holds over every field, for arbitrary
exterior vectors, including empty factor bases, degree zero and over-rank
exterior powers. It is the actual-image input to CLOSURE's endpoint above.
The explicit-root serialized module check passed **2,415 jobs warning-free**
in 16.6s; the expanded `BalancedAxioms.lean` passed **139 transitive probes**
in 2.3s, all with only the same foundational axioms. Guarded LSP is clear.
Independent honesty/source/mathematical review found no proxy, missing image
direction, hidden criterion or defect. The Nullstellensatz module is imported
for its canonical `MvPolynomial.zeroLocus`; no Nullstellensatz theorem is used
by this bridge. Initial coordinate coercions were repaired before the accepted
check. This remains a proved producer, not a proof of Lemma 7.2.


## Coordinate-algebra scalar-extension checkpoint

`InvariantTheory.SpecialLinearBaseChange` at `79ef712` proves
`specialLinearPairBaseChangeEquiv` and its pure-tensor representative formula:
`L ⊗[K] A_K ≃ₐ[L] A_L` for arbitrary commutative rings. The two determinant
relations and their generated ideal are explicitly transported. The scoped
check `ec578f42bc0b9d89` passed **1,830 jobs warning-free**, 3.1s; the expanded
axiom audit passed **142 probes** in 3.0s, all foundational-only. Independent
honesty/source/mathematical review accepted the natural equivalence and its
hypothesis generality. Accepted LSP diagnostics are clear; intermediate
coercion and unused-variable warnings were repaired.

Reused imports, at the pinned Mathlib revision and Apache-2.0 license, are
`Algebra.TensorProduct.tensorQuotientEquiv` from
`RingTheory/TensorProduct/Quotient.lean`, `MvPolynomial.algebraTensorAlgEquiv`
from `RingTheory/TensorProduct/MvPolynomial.lean`, and
`Ideal.quotientEquivAlg` from `RingTheory/Ideal/Quotient/Operations.lean`.
No copied or modified external source is introduced. This is the coefficient
algebra comparison only, not the full coaction scalar-extension theorem.

The next proof is fixed in `lem:balanced-coaction-base-change` (complete
mathematical proof, still notready in Lean): transport the actual exterior
space using existing exterior/tensor base-change maps; transport its dual
and polynomial algebra via dual bases and `SymmetricAlgebra.equivMvPolynomial`;
restrict to homogeneous degree; prove the two actual coaction/constraint
squares and evaluation transport on generators. GEOM then applies its checked
faithfully-flat kernel/evaluation theorem. No invariant-base-change property
is supplied as a hypothesis.

Final hygiene: the task and parent orbit milestone remain active, source
Lemma 7.2 remains notready, and all owned changes are committed. The roadmap
active-count warning includes ancestors and the four authorized lanes and
was independently reviewed as intentional. Scratch dry-run had no candidates.
The graph found one GEOM in-flight dependency-label typo, independently
localized and handed to its owner in I-0076. GEOM repaired it; the final sync
has no missing dependency references. Unattached helper declarations remain
the existing broad-scope warning described by I-0004. Integration of
InvariantDetection, OrbitImage and SpecialLinearBaseChange is handed to GEOM
and is not yet certified by a new root build here.
