The mathematical reduction is written in `src/`, but its dependency cone is
not yet closed. Every node is marked `notready`; there are no accepted Lean
attachments or `leanok` claims in this blueprint.

Three theorem nodes still need complete source-backed mathematical proofs:

- `lem:rectangular-invariants`: the integral standard-polytabloid basis,
  absolute irreducibility, and the rectangular special-linear invariant-space
  identification. The copied complex Specht irreducibility result covers only
  one part; it does not supply integral or invariant-space bridges.
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
