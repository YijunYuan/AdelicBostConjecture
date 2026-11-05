# Tau Ceti selective-reuse survey

Integration update: the Gram/covolume subset below has now been adapted into
`BostConjecture/Lattice/Covolume.lean` (95 lines, six declarations), built on
Lean 4.35 and audited with only standard foundational axioms. It uses Mathlib's
relative-index formula to avoid the separate fundamental-domain helper.
See `CONTRIBUTIONS.md` and `vendor/tauceti/PROVENANCE.json`. The rest of this
document records the original source survey; its larger candidates remain unported.

Specht integration update (run 0003): the original project proofs in
`BostConjecture/Specht/{Integral,Tableau,Metric}.lean` now construct the integral
orbit span, prove its all-polytabloid and equivariant complexification bridges,
and give the Gram theorem a concrete discrete Hilbert-lattice consumer.
`Standard.lean` now proves independence by an original leading-word argument;
`Rectangle.lean` and `Norm.lean` give the concrete word realization and initial
norm. The next producer is rational standard-polytabloid spanning in this word
model. The rational-versus-integral warning in §2 below remains in force.

Inspected 2026-11-05 for the Bost manuscript's integral Specht/Gram and tensor-invariant prerequisites. **Recommendation: first adapt only the covolume–Gram and lattice-inclusion lemmas below; then adapt the rational standard-polytabloid proof into the existing word-space model. Do not require TauCeti as a Lake dependency.**

## Revision, licence, and evidence

- Repository: [TauCetiProject/TauCeti](https://github.com/TauCetiProject/TauCeti).
- Pinned commit: [b3b0334ab9203d9faee4b2f34cd75161463ecdd0](https://github.com/TauCetiProject/TauCeti/commit/b3b0334ab9203d9faee4b2f34cd75161463ecdd0).
- [Toolchain](https://raw.githubusercontent.com/TauCetiProject/TauCeti/b3b0334ab9203d9faee4b2f34cd75161463ecdd0/lean-toolchain): Lean 4.36.0-rc2. Mathlib manifest pin: `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`. Local target is Lean/mathlib 4.35.0, so this is a **backport**, not a tested drop-in.
- [Apache-2.0 licence](https://raw.githubusercontent.com/TauCetiProject/TauCeti/b3b0334ab9203d9faee4b2f34cd75161463ecdd0/LICENSE); inspected files retain “The Tau Ceti contributors” copyright/authorship. No root NOTICE at the pinned commit.
- Acquired only the union of three selected import cones: 130 Lean files, through the authenticated GitHub connector. No repository clone and no project import. Source copies and metadata are in `.archon-horizon/tmp/adhoc/reuse_tauceti/{upstream,sources.json}`; the pinned URLs in this report remain the durable acquisition record.
- All 130 inspected files use `module`. A comment-stripped source scan found no `sorry`, `admit`, `axiom`, `proof_wanted`, `native_decide`, or `unsafe`. **No local build or transitive axiom check was performed.** This is inspected source, not a kernel-verified integration claim.
- No OpenAI/Etingof attribution or imports occur in this downloaded cone. The Specht code uses a different tabloid/categorical representation model; treat it as a separate proof source rather than assuming compatibility with OAI's word-space implementation.

## 1. First small adaptation: covolume and Gram determinant

Source files:

1. [Gram/Hadamard.lean](https://raw.githubusercontent.com/TauCetiProject/TauCeti/b3b0334ab9203d9faee4b2f34cd75161463ecdd0/TauCeti/Analysis/InnerProductSpace/Gram/Hadamard.lean), SHA256 `c60d2eb74730e2ff414d171d280e41866868dba0f1da0a48f14dd3a6d34b47b5`.
2. [Group/FundamentalDomain.lean](https://raw.githubusercontent.com/TauCetiProject/TauCeti/b3b0334ab9203d9faee4b2f34cd75161463ecdd0/TauCeti/MeasureTheory/Group/FundamentalDomain.lean), SHA256 `c2432d7ded0431a70b441accf90955da010e88d039b4577c5019c36f8ea9e320`.
3. [ZLattice/Covolume.lean](https://raw.githubusercontent.com/TauCetiProject/TauCeti/b3b0334ab9203d9faee4b2f34cd75161463ecdd0/TauCeti/Algebra/Module/ZLattice/Covolume.lean), SHA256 `9375db3e2c088ad79c9aee5ae1c279904a07374c687847993c9eb622e80d26ce`.

Select these declarations, without copying the files' unrelated dual-lattice, growth, Hadamard, or group-transport machinery:

| Declaration | Source line | Role |
| --- | ---: | --- |
| `OrthonormalBasis.det_gram_eq_norm_det_sq` | Hadamard:86 | Gram determinant equals squared absolute coordinate determinant. |
| `MeasureTheory.IsFundamentalDomain.measure_le_of_disjoint_smul` and its generated additive form | FundamentalDomain:346 | Small lemma reducing disjoint translates to Mathlib's pairwise-disjoint comparison. |
| `ZLattice.covolume_le_covolume_of_le` | Covolume:135 | For a full lattice contained in a discrete superlattice, the superlattice's covolume is no greater. |
| `OrthonormalBasis.volume_fundamentalDomain` | Covolume:240 | Orthonormal parallelotope has volume one. |
| `OrthonormalBasis.volume_real_fundamentalDomain` | Covolume:247 | Real-valued version of that normalization. |
| `ZLattice.covolume_sq_eq_det_gram` | Covolume:253 | Covolume squared equals Gram determinant of an integral basis in any finite-dimensional real inner product space. |
| `ZLattice.covolume_span_sq_eq_det_gram` | Covolume:266 | Specialization to the integral span of a real basis. |

The full Covolume module has a 12-file / 2,389-line TauCeti import cone. The selected proof bodies have a much smaller mathematical cone: the determinant calculation and fundamental-domain comparison above use Mathlib directly. Extracting them should avoid all other TauCeti imports, subject to checking the backport.

**Local Mathlib check:** `horizon search` was run for the three exact names `ZLattice.covolume_sq_eq_det_gram`, `ZLattice.covolume_le_covolume_of_le`, and `OrthonormalBasis.det_gram_eq_norm_det_sq`. The names are absent in the indexed local Mathlib 4.35.0, confirmed by exact-name source lookup. Relevant existing producers are:

- `ZLattice.covolume_eq_det_mul_measureReal`, `Mathlib/Algebra/Module/ZLattice/Covolume.lean:116`;
- `ZLattice.covolume_div_covolume_eq_relIndex`, same module:149 (coordinate-space alternative for inclusion);
- `Matrix.gram_eq_conjTranspose_mul`, `Mathlib/Analysis/InnerProductSpace/GramMatrix.lean:131`;
- `LinearMap.normDet_sq_eq_det_gram`, `Mathlib/Analysis/InnerProductSpace/NormDet.lean:303` (related existing determinant API);
- `MeasureTheory.IsFundamentalDomain.measure_le_of_pairwise_disjoint`, `Mathlib/MeasureTheory/Group/FundamentalDomain.lean:424`.

Thus the proposed extraction is a small bridge between existing Mathlib APIs. Use those producers instead of copying TauCeti's broader positive-semidefinite or measure-theory layers.

**Intended substantive consumer:** standard polytabloids span a full sublattice of the integral orbit lattice; inclusion reverses covolumes, and the standard-polytabloid Gram determinant bounds the orbit lattice's covolume. This still requires constructing the real span, proving discreteness/fullness and integral coefficient compatibility, and proving the manuscript's seminormal Gram formula and its asymptotics. These lemmas alone do not discharge any Specht asymptotic theorem.

## 2. Rational standard polytabloid basis: valuable proof to adapt

- [Specht/Module.lean](https://raw.githubusercontent.com/TauCetiProject/TauCeti/b3b0334ab9203d9faee4b2f34cd75161463ecdd0/TauCeti/RepresentationTheory/Symmetric/Specht/Module.lean) defines the unscaled signed column sum in the tabloid permutation module.
- [Specht/Garnir.lean](https://raw.githubusercontent.com/TauCetiProject/TauCeti/b3b0334ab9203d9faee4b2f34cd75161463ecdd0/TauCeti/RepresentationTheory/Symmetric/Specht/Garnir.lean) proves the antisymmetrizer/Garnir relation.
- [Specht/Straightening.lean](https://raw.githubusercontent.com/TauCetiProject/TauCeti/b3b0334ab9203d9faee4b2f34cd75161463ecdd0/TauCeti/RepresentationTheory/Symmetric/Specht/Straightening.lean) proves `TauCeti.YoungTableau.polytabloid_mem_span_polytabloid_standard`.
- [Specht/StandardBasis.lean](https://raw.githubusercontent.com/TauCetiProject/TauCeti/b3b0334ab9203d9faee4b2f34cd75161463ecdd0/TauCeti/RepresentationTheory/Symmetric/Specht/StandardBasis.lean) proves `TauCeti.linearIndependent_polytabloid`, `TauCeti.spechtSubrepresentation_eq_span_standard`, and constructs `TauCeti.standardPolytabloidBasis`.

The last three files contain 349 + 510 + 400 lines; their full import closure is **59 files / 15,214 lines**, mostly due to the categorical permutation-module/induction representation. Do not vendor the closure. Adapt their combinatorial Garnir relation, terminating straightening argument, and triangular linear-independence proof to the accepted OAI word-space model.

**Important mathematical boundary:** straightening groups the internal permutations into `N • e_t` and cancels the nonzero rational scalar `N`. It proves a **rational** span/basis theorem, not an integral standard-basis theorem. The polytabloids themselves are unscaled signed sums. This is well suited to the “integral orbit lattice + full-rank standard sublattice” approach, if that approach is proved sufficient for the manuscript. It does not automatically identify the integral orbit lattice with the standard integral span.

Remaining bridges: tableau and tabloid/row-word equivalence; compatibility of signed column sums; rational/real/complex scalar extension and span; the canonical tabloid Hilbert metric; integral orbit lattice preservation; standard basis correspondence with the hook-length count; seminormal monic Gram determinant.

## 3. Schur–Weyl: useful larger reserve

[TensorAction/GeneralLinear.lean](https://raw.githubusercontent.com/TauCetiProject/TauCeti/b3b0334ab9203d9faee4b2f34cd75161463ecdd0/TauCeti/RepresentationTheory/Symmetric/TensorAction/GeneralLinear.lean) proves:

- `TauCeti.centralizer_range_tensorPowerRep_asAlgebraHom_eq_range_permTensorActionAlgHom`;
- `TauCeti.centralizer_range_permTensorActionAlgHom_eq_range_tensorPowerRep_asAlgebraHom`;
- the corresponding `mem_range_*_iff_forall_commute_*` criteria.

These are actual mutual centralizer statements for the diagonal general-linear and factor-permutation actions on `(k^n)^{⊗d}`, over an infinite field with `d!` nonzero. **There is no restriction `d ≤ n`**, so they remain relevant at fixed rank and growing tensor degree. The full cone is 40 files / 9,075 lines. This is not yet the rectangular determinant-isotypic/invariant realization or integral isometric embedding required by manuscript Lemma 6.1. Reserve it for a consumer-directed extraction after the simpler Specht bridges.

## Other findings and limits of the search

- [Arakelov/Covolume.lean](https://raw.githubusercontent.com/TauCetiProject/TauCeti/b3b0334ab9203d9faee4b2f34cd75161463ecdd0/TauCeti/NumberTheory/Height/Arakelov/Covolume.lean) proves `Submodule.covolume_intLattice`: the covolume of `V ∩ ℤ^n` equals the Euclidean height of a rational subspace. Its cone is 40 files / 9,163 lines. It explicitly covers **K = ℚ**, not the general number-field discriminant formula or arbitrary Hermitian metrics. It attributes its proof plan to `rwst/Subspace-Theorems@9894a1c4baf805296b249e95575f0e16e8e1afa3`, `ArithmeticHeights/RationalLattice.lean`, Apache-2.0. Preserve that secondary provenance if reused. No immediate wholesale copy is recommended.
- TauCeti code searches for `seminormal`, `"seminormalBasis"`, and `"Gram determinant" "Specht"` found no Specht seminormal norm/Gram product implementation. The first query returned content separation for Hecke algebras and unrelated crystal normality. Searches for `"Kempf-Ness"`, `"nullCone"`, and Hilbert–Mumford did not identify the needed reductive-group orbit/invariant criterion. These are bounded search results, **not proof that no implementation exists**.
- The finite-group Hilbert-ideal/null-cone material returned by broad searches does not establish the needed general-linear/special-linear reductive-group criterion.
- Other project searches were stopped once the concrete TauCeti candidates above were identified, per the instruction to prioritize quick, selective reuse.

## Next Horizon task

Adapt only the rational straightening argument into the existing word model.
The lattice, metric, Gram comparison, and standard independence are already
proved locally. Rational spanning and real transport must supply the basis
hypothesis of `BostConjecture.Specht.covolume_sq_le_det_gram`; the seminormal
Gram identity remains a separate obligation.

The unported TauCeti source remains an **unverified candidate source**.
Accepted local proof/build evidence and scoped honesty review are recorded in
`RESULTS.md`; no source inspection alone discharges the remaining producers.

