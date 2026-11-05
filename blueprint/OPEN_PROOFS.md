The mathematical reduction is written in `src/`, but its dependency cone is
not yet closed. The integral word orbit span and its complex scalar-extension
map are proved in `BostConjecture/Specht/Integral.lean`. `Tableau.lean`
identifies the orbit with all polytabloids; `Metric.lean` constructs the
discrete full Hilbert lattice in its own real span and proves its covolume
is at least one using an integer Gram determinant. Its covolume square is
bounded above by the Gram determinant of any integral family that is a real
basis; that basis hypothesis is not yet discharged for standard polytabloids.
`Norm.lean` proves that a polytabloid's squared norm is the column-group order.
`Rectangle.lean` identifies balanced row words and proves the initial norm
`(a!)^k`. `Standard.lean` proves standard-polytabloid independence over any
ring by lexicographic triangularity. `OneRow.lean` proves covolume one and
the sublinear limit for the one-row case. Rational spanning remains unproved.
This does not establish the rational standard basis,
the invariant-space identification, or the covolume asymptotic.

The following producers still need complete source-backed mathematical proofs:

- `lem:rational-standard-spanning` is the first unmet basis producer;
  independence is now checked. `lem:rational-standard-basis` and its real-transport consumer
  `lem:real-standard-basis` remain open. The all-polytabloid lattice is retained:
  a rational standard basis gives a full-rank sublattice and the Gram upper
  bound, so integral straightening is unnecessary for this route.
- `lem:rectangular-invariants` depends independently on
  `lem:rectangular-absolute-irreducible` and `lem:rectangular-sl-invariants`.
  Its complex orbit representation now has an explicit integral model and
  tensor-product scalar-extension equivalence. The rational standard-basis theorem,
  characteristic-zero descent, and invariant-space identification remain open.
- `lem:monic-seminormal`: construction of the monic seminormal basis and its
  correctly normalized adjacent-transposition formula. The following norm
  formula is proved mathematically from this precise input. Ryom-Hansen
  arXiv:0904.4243v1, Section 2, equation (1), supplies the exact source
  normalization but recalls Murphy's theorem rather than proving the action
  formula locally. This source is not a Lean axiom or a completed producer.
- `lem:invariant-orbit-criterion`: equality of Euclidean and Zariski orbit
  closures, and detection by homogeneous invariants for products of special
  linear groups. The following balanced-projection argument uses both parts.

These are unproved producer obligations, not assumptions under which the
main result is declared finished. The current manuscript proposes the route;
the blueprint's mathematical proofs still require independent review.

The seminormal Gram identity is for the standard family. For the orbit lattice
it yields only `0 ≤ 2c_a(d) ≤ E log γ`; the sublinear limit follows by squeezing.
Determinant covariance for local-frame gluing and the full invariant generic
fiber for nonvanishing stay independent requirements of the contraction route.

All cited manuscript page anchors resolve to registered vision transcriptions
that were read before attachment. The shifted-coordinate tableau count has
an explicit corner-recurrence proof, supplementing the manuscript's use of
the hook-length formula. The compact lattice-frame lemma has an explicit
bounded-basis proof, supplementing its appeal to Mahler compactness.

The finite-dimensional convex-interval lemma specializes Chen–Jeannin §4.3
to strictly increasing ranks. Its geometric application separately proves
degree supermodularity and the quotient-degree identification. No modularity
of Hermitian degree or already-proved tensor semistability is assumed.
