# Reused formalizations

The target is manuscript Theorem 1.1 for arbitrary number fields and positive
ranks. The results below are prerequisites; none proves that theorem by itself.
No claim of authorship is made for upstream code. Only needed module closures
are imported. Each copied file retains upstream notices and identifies local
changes. The installed mathlib revision is pinned in `lake-manifest.json`.

## Harder–Narasimhan games — Yijun Yuan

- Repository: <https://github.com/YijunYuan/HarderNarasimhan>
- Revision: `14b3090e1e169b77fe381102a1289f24c2b08a11`.
- License: Apache-2.0; copyright and author notices remain in the unmodified
  Lake dependency. This is the user's project.
- Integration: pinned Lake dependency, Lean/mathlib `v4.35.0`.
- Imports: `HarderNarasimhan.Filtration.Unique`,
  `HarderNarasimhan.PayoffFunction.Slope`, and
  `HarderNarasimhan.PayoffFunction.NashEquilibrium` (13-module source closure).
- Results: HN existence/uniqueness, additive-interval slopes are slope-like,
  and the game/ordinary slope semistability comparison.
- Source: Chen–Jeannin, *Harder–Narasimhan games*,
  <https://arxiv.org/abs/2306.08283>, especially §§2.2, 3.3, 4.3–4.4.
- Intended consumer: arithmetic HN theory in the manuscript's §§2 and 7.
  Still required: saturated subobjects versus generic-fibre subspaces,
  actual Hermitian quotient degrees, degree supermodularity, and Hermitian
  duality. The library's order-dual operation alone is not Hermitian duality.
  Interval degree additivity is distinct from modularity of object degree;
  only supermodularity of the latter is appropriate here.

## Complex Specht modules and Euclidean Mahler compactness — openai/math

- Repository: <https://github.com/openai/math>
- Revision: `4eaee87548250b2682affda7d05d947c05554bae` (upstream Lean 4.34.1).
- License: Apache-2.0, exact upstream `lean/LICENSE` retained at
  `vendor/openai/LICENSE`.
- Source map and original SHA-256 hashes: `vendor/openai/PROVENANCE.json`.
  Local paths preserve the upstream `lean/OAI/` hierarchy under `vendor/openai/OAI/`.
- Copied Specht cone: `RepresentationTheory/Saxl/{Model,Basic,Polytabloid,SpechtSubmodule}.lean`.
  Results include `OAI.Saxl.specht_irreducible` and
  `OAI.Saxl.specht_cyclic_of_ne_zero` for the actual complex orbit span of a
  column-antisymmetrized row tabloid.
- Copied Mahler cone: `NumberTheory/ArithmeticGroups/Lattices/` files
  `ShortestVector`, `ProjectedLattice`, `BasisLift`, `BoundedBasis`,
  `OrthogonalStretch`, `Minkowski/Ellipsoid`, `UniformShortSpan`, `FrameMatrices`.
  The key result is `FrameMatrices.Construction.exists_compact_lattice_frames`
  in that namespace: a compact set of nondegenerate frames containing an
  integral basis of every full discrete real lattice with covolume in a fixed
  positive interval and a common positive lower bound on nonzero vector norms.
- Local changes: Lean 4.35 module headers, public imports and exposed public
  declarations; source/modification notices; removed unused Kronecker
  multiplicity, staircase and Saxl-conjecture code from `Model` and `Basic`.
  Retained theorem statements and proof bodies otherwise unchanged.
- Intended consumers: rectangular Specht irreducibility (§6) and the underlying
  real-lattice compactness step (§7). The project-local
  `BostConjecture/Specht/{Integral,Tableau,Metric}.lean` now consumes this
  Specht cone to construct the integral orbit lattice, prove its equality
  with the all-polytabloid span, identify its complex scalar extension
  equivariantly, and realize its orthonormal word metric. These are original
  bridge proofs using the unmodified vendor declarations. The original local
  `Norm`, `Rectangle`, `Standard`, and `OneRow` modules add the rectangular
  word realization, initial norm, standard-family independence, and one-row
  covolume calculation. `Standard` uses an original lexicographic proof;
  the separately attributed TauCeti adaptation below supplies rational
  straightening. Still required: determinant-isotypic bridges; for
  compactness, restriction of scalars, arithmetic covolume/systole formulas,
  persistence of the integer-ring action, and degree continuity.

## Hook-length formula — Etingof representation-theory formalization

- Repository: <https://github.com/mathlib-initiative/Etingof-RepresentationTheory-draft1>
- Revision: `c6d86a8bd52065aafb8251fa1cdcd55b609743ef` (upstream Lean 4.32.2).
- Source tree: `clean-code/release/RepresentationTheory/`, copied selectively to
  `vendor/etingof/RepresentationTheory/`. The exact release `LICENSE` and
  `NOTICE` are retained at `vendor/etingof/`.
- Root: `RepresentationTheory.Combinatorics.YoungDiagram.CornerStatistics`;
  the five-file import closure proves
  `Partition.auxiliaryCard_mul_hookLengthProduct_eq_factorial` in that namespace.
  Despite the upstream generic naming, the objects counted are bijective
  increasing fillings of partition cells and the factors are actual hook lengths.
- Local changes and exact file hashes are recorded in the vendor provenance
  record. Changes update Lean 4.35 visibility and proof elaboration.
- Intended consumer: tableau counts in the rectangular prefix law (§5).
  The tableau-type comparison, prefix bijections, and seminormal Gram identity
  remain separate obligations. This formula alone does not prove the
  manuscript's covolume bound.

## Gram determinants and covolumes — The Tau Ceti contributors

- Repository: <https://github.com/TauCetiProject/TauCeti>.
- Revision: `b3b0334ab9203d9faee4b2f34cd75161463ecdd0`.
- License: Apache-2.0, original `LICENSE` retained at `vendor/tauceti/LICENSE`.
- Extracted from `TauCeti/Analysis/InnerProductSpace/Gram/Hadamard.lean`
  and `TauCeti/Algebra/Module/ZLattice/Covolume.lean` into the 95-line
  `BostConjecture/Lattice/Covolume.lean`. Copyright and attribution are preserved.
  Exact file/declaration hashes and changes are in `vendor/tauceti/PROVENANCE.json`.
- Local changes: backport from Lean 4.36.0-rc2 to 4.35; narrow Mathlib imports;
  derive lattice-inclusion covolume monotonicity using Mathlib's relative-index
  formula, avoiding an additional fundamental-domain comparison helper.
- Results: coordinate Gram determinant, volume of orthonormal fundamental
  domains, Gram formulas for covolumes, and reversal of covolume under lattice
  inclusion, in arbitrary finite-dimensional real inner product spaces.
- Intended consumer: the full-rank standard-polytabloid sublattice's Gram
  determinant bounds the actual integral orbit lattice's covolume. The
  orbit lattice is now constructed as `BostConjecture.Specht.spanLattice`,
  with discreteness and fullness proved. The consumer
  `BostConjecture.Specht.covolume_sq_eq_integer_gram` applies the copied
  Gram theorem, and `one_le_covolume` derives its lower bound.
  `covolume_sq_le_det_gram` now consumes the copied lattice-inclusion theorem
  and span Gram formula for an integral real basis, with that hypothesis
  explicit. `oneRow_covolume_eq_one` supplies an actual integral basis and
  computes its covolume. `standardRealBasis` now supplies the standard
  integral real basis to `covolume_sq_le_det_standard_gram`; the seminormal
  Gram formula remains open. No TauCeti Lake
  dependency was added.

## Rational Garnir straightening — The Tau Ceti contributors

- Repository: <https://github.com/TauCetiProject/TauCeti>, revision
  `b3b0334ab9203d9faee4b2f34cd75161463ecdd0`; Apache-2.0, with the original
  license at `vendor/tauceti/LICENSE` and notices in each adapted file.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Garnir.lean`: adapted
  `exists_ne_rowIndex_relabel_eq`, the signed Garnir relation, Garnir set
  definitions, cardinality and internal-column-permutation lemmas to
  `BostConjecture/Specht/{Garnir,GarnirSets}.lean`.
- `TauCeti/RepresentationTheory/Symmetric/Specht/Straightening.lean`: adapted
  the collected internal multiplicity and rational span lemmas, bounded
  straightening weight, strict-progress lemmas and
  `polytabloid_mem_span_polytabloid_standard` to `Garnir.lean` and
  `Straightening.lean`.
- Selected helpers only: `Combinatorics/Young/Diagram.lean`'s
  `card_filter_fst_lt_filter_snd_eq`; `Algebra/BigOperators/Finset/Swap.lean`'s
  `sum_swap_apply_add`; `Algebra/Order/BigOperators/Sum/LtSum.lean`'s
  `sum_lt_sum_of_forall_lt` and `sum_lt_sum_image_sdiff` (all paths under
  `TauCeti/`). Helpers are private within their consuming modules.
- Modifications: port to Lean 4.35; use existing `OAI.Saxl.Tableau n μ`
  and integral word polytabloids; remove the categorical permutation module
  and all its imports; prove cancellation directly over the integers by a
  finite-sum involution; extend coefficientwise to rationals; use the existing
  standardness predicate and prove the label/cardinality bridge. No alternate
  tableau, representation or lattice was introduced.
- Consumer: `BostConjecture.Specht.polytabloidRat_mem_span_standard` supplies
  rational spanning to `Basis.lean`, whose original scalar-extension and
  basis proofs construct `standardRealBasis`, establish the integral rank
  formula, and apply `covolume_sq_le_det_standard_gram`. Division by a positive internal multiplicity
  occurs over the rationals: no integral basis claim is made.
- Only these needed proof pieces are adapted, with their local dependency cone
  checked. Source hashes and target modules are recorded in
  `vendor/tauceti/PROVENANCE.json`; transitive axiom probes are recorded in
  `verification/SpechtAxioms.lean` and results in `verification/RESULTS.md`.

## Verification

Run `horizon --root ../.. check --json` from this project, then
`horizon --root ../.. check --lean verification/ReuseAxioms.lean --json`.
The latter audits the transitive axioms of the named reused producers.
Source inspections and successful prerequisite builds do not certify the
unwritten arithmetic bridges or main theorem. Current evidence is recorded in
`verification/RESULTS.md` once the corresponding checks finish.
