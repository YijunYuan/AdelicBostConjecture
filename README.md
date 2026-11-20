# AdelicBostConjecture

This project formalizes Theorem 1.2 of **On the tensor product of semistable
Hermitian adelic vector bundles over an adelic curve**, by Huayi Chen and
Yijun Yuan, and deduces its number-field specialization, Conjecture 1.1.
For nonzero Hermitian adelic bundles on a proper adelic curve over a countable
field of characteristic zero, maximal slopes add under orthogonal tensor
products. Consequently, tensor products of semistable bundles are semistable.
Archimedean absolute values have their usual real or complex normalization;
tensor norms are Hilbert norms at Archimedean places and epsilon norms elsewhere.

The binary and finite-family conclusions and the tensor HN filtration identity
are proved unconditionally. Their proofs use the completed norms and discharge
the geometric inequality and the smaller-rank induction hypotheses. The
statement coverage below records the remaining differences between the
formalization and the full generality of intermediate assertions in
**On the tensor product of semistable Hermitian adelic vector bundles over an
adelic curve**. Thus the main theorem is formalized, but complete alignment of
every intermediate statement is not claimed.

## Public results

The adelic declarations belong to `ArakelovGeometry.AdelicVectorBundle`.

| Result | Declaration |
| --- | --- |
| Theorem 1.2: binary maximal-slope additivity | `maximalSlope_orthogonalTensorPair` |
| Theorem 1.2: finite-family additivity | `maximalSlope_orthogonalTensorOfNormMeasurability` |
| Theorem 1.2: binary tensor semistability | `isSemistable_orthogonalTensorPair` |
| Theorem 1.2: finite-family tensor semistability | `isSemistable_orthogonalTensorOfNormMeasurability` |
| Corollary 7.3: weighted tensor HN compatibility | `hermitianHNFiltration_orthogonalTensorPair` |

The finite-family declarations also include the empty family, whose tensor
product is a semistable line of slope zero. Countability supplies
`S.NormMeasurabilityHypotheses` through
`ArakelovGeometry.AdelicStructure.hasCommonCountableDenseSubfield_of_countable`.
Hermitian and semistability hypotheses are typeclass arguments; the tensor
semistability conclusions are registered instances. For example,
`maximalSlope_orthogonalTensorPair V W` proves
`(V ⊗ʰ W).maximalSlope = V.maximalSlope + W.maximalSlope` for nonzero
Hermitian factors. The notation uses `open scoped TensorProduct`.

The classical theorem is
`AdelicBostConjecture.Arithmetic.HermitianMetric.maxSlope_tensor`. For finite
projective modules over the ring of integers of a number field, with nonzero
generic fibers and Hermitian metrics `h` and `g`, it proves

```lean
(h ⊗[𝓞 K] g).maxSlope = h.maxSlope + g.maxSlope
```

Adelization identifies adelic maximal slope with `[K : ℚ]` times the
normalized classical maximal slope. The degree and tensor-norm comparisons
also cover nonfree projective modules. The classical statement and definitions
retain the conventions of revision `81cf08a874039fde5d23c0fbf3970f7d28c3beca`.

## Statement coverage

Numbering follows **On the tensor product of semistable Hermitian adelic
vector bundles over an adelic curve**. Corresponding declaration docstrings
contain these numbers. A result may be split across several declarations;
the table gives its principal entry points. Short declaration names are
qualified by the module or namespace indicated in the surrounding text.

| Statement | Formal counterpart and coverage |
| --- | --- |
| Proposition 2.3 | `isHermitian_standard_constructions`, `quotient_dual_norm_eq_annihilator`, `dual_quotient_norm_eq_restriction` |
| Proposition 2.4 | `slope_bounds_of_nonzero_map`; `slope_le_of_nonzero_completed_contraction` is the specialization used in Section 6 |
| Theorem 2.5 | `hermitianHNFlag_spec`, `hermitianHNOrderedSlope_extrema`, `eq_hermitianHNFiltration_of_semistable_grades` |
| Proposition 2.6 | `isMeanSlopeSemistable_of_isIrreducible`, `isMeanSlopeSemistable_orthogonalTensor_and_dual_of_isIrreducible_baseChange` |
| Proposition 3.14 | `integralRepresentation_baseChange_isAbsolutelyIrreducible` |
| Proposition 3.15 | `finrank_orbitLattice_eq_card_standard`, `rectangleRank_eq_factorials` |
| Proposition 4.17 | `norm_orthogonalStandardBasis_sq_eq_prefixNormProduct`, `log_det_standard_gram_div_card_eq_average`; fixed colex order |
| Proposition 5.1 | `tendsto_rectangleLogCovolume_div`, `tendsto_neg_specht_slope_div` |
| Proposition 5.2 | `card_rectanglePrefix`, `sum_occupancyWeight_eq_closed`, `rectanglePrefix_probability_eq_weighted`, `rectanglePrefix_average_eq_weighted` |
| Lemma 5.3 | `sampling_concentration` for any finite population and marked subset; `occupancyMass_concentration` for the occupancy application |
| Lemma 5.4 | `rectanglePrefixGapProbability_uniform`, expressing an eventual bound uniform over intermediate times |
| Lemma 6.1 | `projectiveDeterminantMap_injective`, `projectiveDeterminantMap_norm_infinite`, `projectiveDeterminantMap_norm_finite`, `determinantSpechtBundle_slope`; invariant-image coverage is restricted as described below |
| Theorem 6.2 | `slope_le_sum_of_geometricallySemistable`; equation (6.6) is `slope_sum_le_orthogonalTensor_quotient_of_geometricallySemistable` |
| Lemma 7.1 | `hermitianHNFiltration_orthogonalTensorPair_of_semistable_grades` |
| Lemma 7.2 | `tensorFiltrationQuotient_eventual_hn_upper` |
| Theorem 1.2 and Corollary 7.3 | The public results above and `tensorHN_and_semistable` |

The proof follows the integral orbit lattice, the standard-sublattice Gram
bound, the exact Vandermonde-weighted prefix distribution, and simultaneous
rank induction. Local docstrings also identify unnumbered steps and displayed
equations, including (3.17), (5.7), (5.10)–(5.13), (6.3)–(6.6), and (7.4).
Finite probability expectations are finite weighted sums. Tableau labels and
row indices start at zero in Lean. These conventions preserve the mathematical
statements after the corresponding index translation.

The following differences remain:

1. **Section 2.6, general Euclidean lattices.** The constant adelic construction
   and degree formula (2.10) are implemented for integral Specht lattices with
   their word metric. There is no general constructor here for an arbitrary
   Euclidean lattice with an arbitrary real Gram matrix. The required Specht
   specialization is proved.
2. **Definition 4.14 and Proposition 4.17, order independence.** The exact norm
   formula is proved for the fixed colex order. Independence under every total
   order extending tableau dominance, as recalled from Ryom-Hansen, is not
   formalized; neither is the comparison with the explicitly defined dominance
   relation of Definitions 4.4 and 4.8.
3. **Equation (3.10) and Lemma 6.1, invariant image over the original field.**
   `mem_range_freeLatticeMap_iff_specialLinear_fixed` assumes an algebraically
   closed field. The stated invariant-image equality over every characteristic-zero
   base field and the general descent of invariant polynomials in Section 6
   are not exposed as theorems. The geometric proof works over the
   algebraic closure and descends nonvanishing of the canonical pairing, which
   suffices for the formal proof of Theorem 6.2.
4. **Section 3.5, equation (3.15).** The exact two-case norm formula for the
   single anti-symmetrization map on every local normed vector space is not
   stated as a theorem. The code proves the factorial norm of rectangular
   polytabloids, the Archimedean determinant–Specht isometry, and the finite-place
   contraction separately. These supply the estimates used in the main proof.

Historical comparisons in the introduction, illustrative tableau examples,
and the discussion comparing Schur-functor indexing conventions are not
claimed as formalized results. They are not additional inputs to the main
formal proof. Source attribution describes mathematical correspondence;
formal proofs may use a different established argument, such as Jacobson
density for Burnside's criterion or Schur–Weyl duality for invariant spanning.

## References used in docstrings

Citation keys below identify the external works independently of
**On the tensor product of semistable Hermitian adelic vector bundles over an
adelic curve**. Docstrings give the relevant theorem, proposition, section,
or equation within the cited work. Upstream projects used for code reuse are
listed under [External code](#external-code); donor revisions and license
notices are preserved in the project contribution and provenance records.

| Key | Reference |
| --- | --- |
| `bc` | Jean-Benoît Bost and Huayi Chen, *Concerning the semistability of tensor products in Arakelov geometry*, Journal de Mathématiques Pures et Appliquées 99(4), 436–488 (2013). [DOI](https://doi.org/10/f4vnsj). |
| `bgow` | Peter Bürgisser, Ankit Garg, Rafael Oliveira, Michael Walter and Avi Wigderson, *Alternating minimization, scaling algorithms, and the null-cone problem from invariant theory* (2017). [arXiv:1711.08039](https://arxiv.org/abs/1711.08039). |
| `bost96` | Jean-Benoît Bost, *Périodes et isogénies des variétés abéliennes sur les corps de nombres*, Séminaire Bourbaki, exposé 795, Astérisque 237, 115–161 (1996). [Numdam](https://www.numdam.org/item/SB_1994-1995__37__115_0/). |
| `bost97` | Jean-Benoît Bost, *Hermitian vector bundle and stability*, unpublished lecture at the conference *Algebraische Zahlentheorie*, Oberwolfach, 24 July 1997. The conjecture is also documented in Bost–Chen (`bc`), Problems 1.3–1.5; no online original is asserted. |
| `cm` | Huayi Chen and Atsushi Moriwaki, *Arakelov Geometry over Adelic Curves*, Lecture Notes in Mathematics 2258, Springer (2020). [DOI](https://doi.org/10/p6jz). |
| `cmp` | Huayi Chen and Atsushi Moriwaki, *Positivity in Arakelov Geometry over Adelic Curves: Hilbert-Samuel Formula and Equidistribution Theorem*, Progress in Mathematics 355, Springer Nature Switzerland (2024). [DOI](https://doi.org/10/hcsp3t). |
| `frt` | J. S. Frame, G. de B. Robinson and R. M. Thrall, *The Hook Graphs of the Symmetric Group*, Canadian Journal of Mathematics 6, 316–324 (1954). [DOI](https://doi.org/10/fdvfmr). |
| `kn` | Matthias Kuenzer and Gabriele Nebe, *Elementary divisors of Gram matrices of certain Specht modules* (2003 version). [arXiv:math/0203129v3](https://arxiv.org/abs/math/0203129v3). |
| `kowalski` | Emmanuel Kowalski, *An Introduction to the Representation Theory of Groups*, Graduate Studies in Mathematics 155, American Mathematical Society (2014). [DOI](https://doi.org/10/rz83). |
| `rh` | Steen Ryom-Hansen, *On the denominators of Young's seminormal basis* (2009 version). [arXiv:0904.4243v2](https://arxiv.org/abs/0904.4243v2). |

The supplied works by Narasimhan–Seshadri and Stuhler concern the historical
motivation in the introduction. They are not invoked as unproved inputs to
the adelic tensor theorem. Other references appearing only in that historical
discussion are likewise not dependencies of its formal proof.

## External code

The `ExternalCode` modules contain selected proofs adapted from the following
projects. The table links to the upstream repositories and, where applicable,
the originating mathlib pull requests. Donor revisions, licenses and local
adaptations are documented in the accompanying provenance records.

| Module group | Upstream project | Reused material |
| --- | --- | --- |
| `OAI` | [openai/math](https://github.com/openai/math) | Tableau and word models, polytabloids and Specht submodules from the Saxl development |
| `TauCeti` | [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti) | Lattice covolumes, symmetric powers, Garnir relations, Specht straightening and Schur–Weyl duality |
| `Etingof` | [mathlib-initiative/Etingof-RepresentationTheory-draft1](https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1) | Partitions, Young diagrams and the hook-length formula for standard tableaux |
| `Stacks` | [AxiomMath/Stacks](https://github.com/AxiomMath/Stacks) | Determinant covariance of alternating tensors under matrix tensor powers |
| `MathlibPRs.PR40948` | [Thmoas-Guan/mathlib4_fork](https://github.com/Thmoas-Guan/mathlib4_fork), [mathlib PR #40948](https://github.com/leanprover-community/mathlib4/pull/40948) | Exterior-power base change and homogeneous projection |
| `MathlibPRs.PR44845` | [DanielJHorton/mathlib4](https://github.com/DanielJHorton/mathlib4), [mathlib PR #44845](https://github.com/leanprover-community/mathlib4/pull/44845) | Finite projective tensor products and duality |

## Organization and build

| Module group | Contents |
| --- | --- |
| `Adelic` | Normed bundles, preliminaries, auxiliary semistability, contractions, geometric inequalities and rank induction |
| `Classical` | Integral Hermitian metrics, degree and slope, adelization and the number-field theorem |
| `Specht` | Integral orbit lattices, seminormal norms, hook counts, prefix probabilities and covolume limits |
| `Geometry` | Determinant maps, invariant tensors, polarization and nonvanishing |
| `Arithmetic` | Shared dual base change and representation theory |
| `Tensor` | Regrouping, duality and scalar-extension compatibility |
| `InvariantTheory` | Polynomial actions and homogeneous components |
| `ExternalCode` | Selected upstream proofs with preserved attribution and licenses |

Import `AdelicBostConjecture` to obtain both the adelic and classical results.
Lean and mathlib are pinned to `v4.35.0`. Install Lean through `elan`, then run:

```sh
lake exe cache get
lake --wfail build
```

The warning-failing build uses the mathlib standard linter set,
`relaxedAutoImplicit = false`, and `maxSynthPendingDepth = 3`.
ArakelovGeometry is pinned to `df942e19748f3ab6c41cce7827af7607e2934735`;
HarderNarasimhan is pinned to `14b3090e1e169b77fe381102a1289f24c2b08a11`.
The dependencies remain unmodified. The HN variation and compatibility
adapters are local to this project.

The public theorem axiom checks are:

```lean
import AdelicBostConjecture

#print axioms ArakelovGeometry.AdelicVectorBundle.maximalSlope_orthogonalTensorPair
#print axioms ArakelovGeometry.AdelicVectorBundle.maximalSlope_orthogonalTensorOfNormMeasurability
#print axioms AdelicBostConjecture.Arithmetic.HermitianMetric.maxSlope_tensor
```

The permitted axioms are `propext`, `Classical.choice` and `Quot.sound`.
Neither `sorryAx` nor an additional mathematical axiom is permitted.

Code and documentation follow the [mathlib contribution guidelines](https://mathlib.org/contribute/),
including their documentation, style and naming conventions. Original code is
released under Apache-2.0; reused code retains its upstream licenses and attribution.
