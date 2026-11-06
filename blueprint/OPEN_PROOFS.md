# Remaining main-theorem proof obligations

The target is manuscript Theorem 1.1 over every number field, for arbitrary
positive-rank finite projective modules over its ring of integers, with the
actual Hilbert tensor metric. **The binary maximal-slope equality and its
finite-family equality remain open.** Weighted HN compatibility and the
appendices are outside the target.

## Remaining producer-to-consumer route

1. **TENSOR-SEMI, checked at `9ba97a4`:** construct the conjugation-compatible traceless partial-trace
   defects of the actual maximizing tensor submodule. Combine actual metric
   stationarity with trace-square positivity to prove both defects vanish.
   This supplies `lem:extremal-to-balance`.
2. **TENSOR-SEMI:** apply the proved balanced-Plücker geometric semistability
   and geometric slope inequality to the actual strictly stable maximizing
   counterexample. Its positive degree contradicts the resulting slope bound.
   Undo normalization to prove unconditional `thm:tensor-semistability`.
3. **MAIN:** apply that proved endpoint to each pair of actual HN grades and
   transport semistability through the checked integral quotient isometry.
   The integral filtration bound gives the upper bound; the unconditional
   attained-submodule lower bound gives `thm:bost-main`.
4. **MAIN:** use the actual finite tensor regrouping isometries and the binary
   identity to prove `cor:bost-finite-family`. The empty tensor has maximal
   slope zero, providing the induction base. Average-slope additivity gives
   the semistability consequence.

The balance node is checked in its owner cone and awaits the next shared-root
batch. The other three headline nodes remain uncompleted. No assumed producer package,
local-maximum premise in the final theorem, or clean prerequisite build
substitutes for these steps. The two active owners retain their disjoint
scopes; completed lanes are not reopened.

## Accepted producers used by this route

- **Specht:** the actual integral orbit lattice, standard basis, monic
  seminormal norms, Gram upper bound, exact prefix distribution and sublinear
  rectangular covolume limit are checked. The orbit lattice uses the bound
  `0 ≤ 2c_a(d) ≤ E log γ`; equality with the standard integral span is not
  required or claimed.
- **GEOM:** determinant tensor realization, canonical contraction, norm bound
  and the original-ring nonzero sequence are checked through the concrete
  binary Plücker action. The unused general coaction scalar-extension square
  is retired from this route, not proved.
- **COVOLUME / COMPACTNESS:** the trace-metric covolume formula includes
  nonfree modules and rank zero. Fixed-rank normalized arithmetic compactness
  and actual globally maximizing pairs are checked (`e81b08b`).
- **SPECHT-SLOPE:** the determinant-Specht degree calculation and actual
  geometric slope endpoint are checked (`8c80c92`).
- **LINE / STRICT:** arbitrary nonprincipal rank-one twists in both tensor
  orders (`032df77`) are substantively consumed by the internal minimal-rank
  and strictly stable maximizing-counterexample construction (`b49b67f`).
- **TENSOR-SEMI:** normalized extensions, actual exponential metric variation,
  local maximality and degree derivatives, scalar partial-trace defects,
  conjugate bases, and actual conjugation/projection-trace transport are
  checked through the full owner handoff `6cc3fd8`. The additionally reviewed
  `9ba97a4` proves actual defect vanishing and balance; it awaits shared-root
  integration with the unconditional endpoint.
- **MAIN:** the actual saturated lexicographic HN tensor flag, consecutive
  integral quotient isomorphisms and all-fiber Hilbert metric identities,
  grade slope bounds, filtered slope bound, maximal-slope isometry invariance,
  and binary/finite lower bounds are checked. `40987f0` additionally supplies
  the integral-filtration adapter and the exact empty-tensor maximum.

Source anchors refer to registered vision transcriptions. The blueprint gives
pure mathematical statements, proofs and dependency edges; current build and
transitive-axiom boundaries are recorded in `verification/MAIN.md` and the
owner evidence files. `CONTRIBUTIONS.md` records all pinned external reuse.
Generated graph counts may include concurrent drafts outside the accepted
root import closure and are not independent completion evidence.
