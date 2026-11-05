The mathematical reduction is written in `src/`, but its dependency cone is
not yet closed. The integral word orbit span and its complex scalar-extension
map are proved in `BostConjecture/Specht/Integral.lean`; their three precise
nodes carry Lean attachments. This does not establish the integral standard
basis, the invariant-space identification, or the covolume asymptotic.

Three theorem nodes still need complete source-backed mathematical proofs:

- `lem:rectangular-invariants` is split into `lem:integral-standard-basis`,
  `lem:rectangular-absolute-irreducible`, and `lem:rectangular-sl-invariants`.
  Its complex orbit representation now has an explicit integral model and
  tensor-product scalar-extension equivalence. The standard-basis theorem,
  characteristic-zero descent, and invariant-space identification remain open.
- `lem:monic-seminormal`: construction of the monic seminormal basis and its
  correctly normalized adjacent-transposition formula. The following norm
  formula is proved from this precise input.
- `lem:invariant-orbit-criterion`: equality of Euclidean and Zariski orbit
  closures, and detection by homogeneous invariants for products of special
  linear groups. The following balanced-projection argument uses both parts.

These are unproved producer obligations, not assumptions under which the
main result is declared finished. The current manuscript proposes the route;
the blueprint's mathematical proofs still require independent review.

All cited manuscript page anchors resolve to registered vision transcriptions
that were read before attachment. The shifted-coordinate tableau count has
an explicit corner-recurrence proof, supplementing the manuscript's use of
the hook-length formula. The compact lattice-frame lemma has an explicit
bounded-basis proof, supplementing its appeal to Mahler compactness.

The finite-dimensional convex-interval lemma specializes Chen–Jeannin §4.3
to strictly increasing ranks. Its geometric application separately proves
degree supermodularity and the quotient-degree identification. No modularity
of Hermitian degree or already-proved tensor semistability is assumed.
