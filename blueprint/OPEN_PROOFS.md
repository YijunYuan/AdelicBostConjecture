The mathematical reduction is written in `src/`, but its dependency cone is
not yet closed. The integral word orbit span and its complex scalar-extension
map are proved in `BostConjecture/Specht/Integral.lean`. `Tableau.lean`
identifies the orbit with all polytabloids; `Metric.lean` constructs the
discrete full Hilbert lattice in its own real span and proves its covolume
is at least one using an integer Gram determinant. Its covolume square is
bounded above by the Gram determinant of any integral family that is a real
basis. `Garnir.lean`, `GarnirSets.lean`, and `Straightening.lean` now prove
rational standard spanning. `Basis.lean` constructs the actual standard real
basis, proves its integrality and rank count, and discharges that hypothesis.
`Norm.lean` proves that a polytabloid's squared norm is the column-group order.
`Rectangle.lean` identifies balanced row words and proves the initial norm
`(a!)^k`. `Standard.lean` proves standard-polytabloid independence over any
ring by lexicographic triangularity. `OneRow.lean` proves covolume one and
the sublinear limit for the one-row case. `ColumnTensor.lean` identifies
the existing polytabloids with products of unnormalized alternating columns;
`Covariance.lean` proves determinant covariance for the word matrix action
on the integral lattice, its scalar span over every commutative ring, and the
checked complex Specht module. `Orthogonal.lean` constructs the monic
orthogonal basis for any total order, proves its determinant-one basis change,
and expresses the standard Gram determinant as the product of its actual
squared norms. `RealAction.lean` constructs the real isometric action and
proves symmetry, commutation, and the adjacent recurrence of the concrete
Murphy operators. `Content.lean` computes the concrete Murphy coefficient at the original
row word as the box content. `Central.lean` uses the checked complex
column-antisymmetrizer line theorem to prove that the sum of all Murphy
operators acts by total diagram content on the actual real span and
integral orbit lattice. `Prefix.lean` now constructs the actual standard prefix diagrams and
content increments. `Branching.lean` proves frozen-tail integral restriction,
prefix equivariance, lifts of smaller lattice vectors and the sliced central
scalar. `Filtration.lean` identifies the standard-basis largest-label
filtration with the ambient word-support filtration and proves its stability.
`Quotient.lean` identifies the successive branching quotient at the last
box of any standard tableau with its smaller real Specht space, by an actual
surjective coefficient restriction and an exact kernel calculation. Individual
content eigenvalues still require the resulting colexicographic triangularity. The standard Gram bound is now
unconditional; its explicit seminormal evaluation, the invariant-space identification,
and the general covolume asymptotic remain open.

The following producers still need complete source-backed mathematical proofs:

- The standard-basis frontier is closed through rational straightening and
  real transport. The all-polytabloid lattice is retained; the standard
  integral sublattice supplies the Gram upper bound, so integral
  standard spanning is unnecessary for this route.
- `lem:rectangular-invariants` depends independently on
  `lem:rectangular-absolute-irreducible` and `lem:rectangular-sl-invariants`.
  Its complex orbit representation now has an explicit integral model and
  tensor-product scalar-extension equivalence. Characteristic-zero descent
  and the invariant-space identification remain open.
- `lem:specht-branching-quotient` is now proved for the last box of each
  standard tableau. The first unmet Gram producer is the induction giving
  `lem:prefix-content-triangular` in the sufficient
  colexicographic total order; it no longer requires the stronger partial-order
  dominance statement. `lem:monic-seminormal` then requires the spectral identification
  and the resulting correctly normalized adjacent-transposition formula.
  Monic orthogonalization and the abstract Gram norm-product identity are
  proved; no assertion that these actual norms equal the prefix product is
  yet available. The following norm
  formula is proved mathematically from this precise input. Ryom-Hansen
  arXiv:0904.4243v1, Section 2, equation (1), supplies the exact source
  normalization but recalls Murphy's theorem rather than proving the action
  formula locally. This source is not a Lean axiom or a completed producer.
  Retrieval of the cited Murphy 1981 paper reached bibliographic metadata
  only; `references/murphy-seminormal-1981/notes.md` records the access boundary.
  The checked eigenvector diagonal-coefficient lemma explicitly assumes two
  eigenvalue equations and does not discharge the content-spectrum producer.
- `lem:invariant-orbit-criterion`: equality of Euclidean and Zariski orbit
  closures, and detection by homogeneous invariants for products of special
  linear groups. The following balanced-projection argument uses both parts.

These are unproved producer obligations, not assumptions under which the
main result is declared finished. The current manuscript proposes the route;
the blueprint's mathematical proofs still require independent review.

The seminormal Gram identity is for the standard family. For the orbit lattice
it yields only `0 ≤ 2c_a(d) ≤ E log γ`; the sublinear limit follows by squeezing.
Determinant covariance in word coordinates is proved. Identification with
abstract tensor maps and flat scalar-extended injectivity in a free frame
are proved by the geometry modules. Projective local-frame gluing and the full invariant
generic fiber for nonvanishing remain requirements of the contraction route.

All cited manuscript page anchors resolve to registered vision transcriptions
that were read before attachment. The shifted-coordinate tableau count has
an explicit corner-recurrence proof, supplementing the manuscript's use of
the hook-length formula. The compact lattice-frame lemma has an explicit
bounded-basis proof, supplementing its appeal to Mahler compactness.

The finite-dimensional convex-interval lemma specializes Chen–Jeannin §4.3
to strictly increasing ranks. Its geometric application separately proves
degree supermodularity and the quotient-degree identification. No modularity
of Hermitian degree or already-proved tensor semistability is assumed.
