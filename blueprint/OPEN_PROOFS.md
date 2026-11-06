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
surjective coefficient restriction and an exact kernel calculation. `LastMurphy.lean` uses that kernel
to identify prefix central and last-Murphy content actions modulo earlier
rows. `Extension.lean` and `Colex.lean` construct the actual standard-tableau
corner lift and its order compatibility. `Triangular.lean` proves recursive
colexicographic Murphy triangularity for all labels; `Spectral.lean` uses it
and symmetry to prove the content eigenvalues of the actual monic orthogonal
basis. `Adjacent.lean` proves the normalized adjacent action;
`ColumnReading.lean` and `AdjacentPath.lean` supply its initial value and
increasing legal paths. `PrefixNorm.lean` and `PrefixNormInitial.lean` prove
the concrete prefix product, positivity, swap ratio and initial value.
`Seminormal.lean` identifies the actual squared norms with that product,
evaluates the standard Gram determinant, and proves the canonical orbit
covolume bound by the uniform logarithmic average. `Asymptotic.lean`
now proves the general sublinear covolume limit for every fixed positive
height, using actual prefix separation and logarithmic expectations.
Rectangular SL invariant identification over algebraically closed characteristic-zero
fields is now checked in `Geometry.RectangularInvariants`. Arbitrary-field descent,
canonical contraction nonvanishing and the number-field main theorem remain open.

Current boundaries and remaining producers:

- The standard-basis frontier is closed through rational straightening and
  real transport. The all-polytabloid lattice is retained; the standard
  integral sublattice supplies the Gram upper bound, so integral
  standard spanning is unnecessary for this route.
- `lem:rectangular-invariants` depends independently on
  `lem:rectangular-absolute-irreducible` and `lem:rectangular-sl-invariants`.
  Its complex orbit representation now has an explicit integral model and
  tensor-product scalar-extension equivalence. The actual SL-fixed-space is
  identified over algebraically closed characteristic-zero fields in
  `Geometry.RectangularInvariants`; arbitrary-field descent remains open.
- The Gram producer is closed, including the coefficient-one normalization
  and the actual prefix norm formula. Uniform bulk separation and its
  logarithmic expectation consumer are proved.
  `Complement.lean` and `PrefixCount.lean`
  prove the rotated complement and actual prefix-fiber bijection, yielding
  the exact product of the two smaller standard-tableau counts.
  `ComplementCount.lean` and `PrefixWeights.lean` turn that count into the
  exact squared-Vandermonde binomial weight. `Hypergeometric.lean`,
  `OccupancySort.lean`, and `ShiftedShapes.lean` prove the labelled law,
  sorting multiplicity, and equivalence with actual rectangular subdiagrams.
  `PrefixDistribution.lean` and `PrefixNormalizer.lean` prove the closed
  normalizer and exact prefix probability formula. The uniform
  bulk lower bound for that normalizer is proved in `BulkNormalizer.lean`.
  `Sampling.lean` proves actual finite-subset binomial moments and the
  Bernoulli exponential-moment bound; `OccupancyMGF.lean` transports it to
  the labelled law and proves two-sided and simultaneous concentration.
  The explicitly documented weaker tail constant suffices for the limit.
  `WeightedGap.lean`, `BulkGap.lean` and `GapAsymptotics.lean` prove the
  finite weighted bad-gap bound and a prefix-time-independent majorant
  tending to zero. `PrefixEvent.lean` transports symmetric observables
  through actual prefix fibers and sorting; `Separation.lean` proves
  uniform bulk separation for the actual standard-tableau prefixes.
  `LogInsertion.lean` and `LogExpectation.lean` prove the insertion-log
  estimates and the actual averaged bulk/boundary bound.
  `Asymptotic.lean` consumes this bound and the unchanged orbit-lattice
  Gram comparison to prove `tendsto_rectangleLogCovolume_div`.
  The stated covolume asymptotic objective is complete; it does not use
  or close the independent rectangular invariant-space identification.
  `HookCount.lean`
  bridges the imported hook formula
  to the accepted tableau indexing; `ShiftedCount.lean` proves the row hook
  interval partition and the factorial/Vandermonde enumeration.
  No seminormal theorem is assumed: the
  action and norms are now proved in the canonical word realization.
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
are proved by the geometry modules. The full determinant-twist base-change square,
general finite-principal-cover descent, finite-projective local frames,
overlap transport and the global determinant injection are proved.
The finite Hilbert tensor form and its pure-tensor formula are proved.
Determinant metric compatibility, the actual integral pairing and its
equivariance are proved in the delivered geometry modules. Generic dual
evaluation and the restricted pairing are bounded, the latter in
`ContractionNorm.lean`. The full invariant generic fiber for nonvanishing
remains a requirement of the route.

All cited manuscript page anchors resolve to registered vision transcriptions
that were read before attachment. The shifted-coordinate tableau count has
an explicit row-hook partition proof, converting the checked hook-length
formula into the coordinates used by the manuscript. The compact lattice-frame lemma has an explicit
bounded-basis proof, supplementing its appeal to Mahler compactness.

The finite-dimensional convex-interval lemma specializes Chen–Jeannin §4.3
to strictly increasing ranks. Its geometric application separately proves
degree supermodularity and the quotient-degree identification. No modularity
of Hermitian degree or already-proved tensor semistability is assumed.
