# Restriction-of-scalars covolume

## Exact boundary

The endpoint remains `lem:restriction-covolume`, consumed by
`lem:arithmetic-compactness`: the Euclidean Haar covolume of the actual
trace-metric integer lattice equals
`abs(discriminant K)^(a/2) * exp(-[K:ℚ] * h.degree)` for every finite
projective module over the ring of integers, including rank zero.
`HermitianMetric.traceCovolume_eq_discr_degree` in `Main.lean` now proves
this exact identity for all the stated inputs. Its serialized module check
passed 3652 jobs at 2026-11-06 02:46:57 UTC (`e742aa919b53262c`). The final
transitive audit, independent reviews, graph and shared-root integration
have accepted the endpoint. This bounded producer is complete.

## Acceptance evidence

The exact theorem is committed at `5144157`. The only subsequent source
change, `739e58a`, moves the identical `traceBasis` and `traceBasis_apply`
definitions from `Exact` to `TraceSpace`, making the canonical basis API
available to the compactness consumer without duplicate definitions.
The full `Main` dependency build passed again, 3652 jobs, at
2026-11-06 02:55:28 UTC. The 63-declaration transitive axiom audit passed
at 02:49:05 UTC and again after relocation at 02:57:55 UTC. Every probe,
including the exact endpoint, reports only `propext`, `Classical.choice`
and `Quot.sound`; there are no additional axioms or `sorryAx`.

Independent mathematical/source review inspected all ten source modules,
the upstream intrinsic-degree APIs, and manuscript equations (18)–(19)
visually. It accepted the exact normalization and arbitrary-projective
statement, including rank zero and nonprincipal ideals. Independent
honesty review accepted the constructed metric/lattice and the substantive
real-form, quotient, exact-sequence and induction chain, and inspected
all 63 final probe outputs. Neither review found an actionable defect.
The honesty reviewer separately rechecked `739e58a` and confirmed that
the relocation preserves both declarations, all proofs and the verdict.

The graph attaches `lem:restriction-covolume` to the exact theorem, retains
the `page0011` source anchor, and retains `lem:arithmetic-compactness` as
its consumer. COMPACTNESS removed its identical local basis definitions and
successfully rebuilt `TraceMultiplication` on the canonical API. The final
graph sync reports 329 blueprint nodes, 2206 Lean declarations and 1698
generated edges, with no duplicate or missing-attachment warning. Its 1060
unattached-declaration warnings concern auxiliary/existing declarations and
ongoing work in other lanes; they do not indicate an unproved dependency of
this endpoint.

GEOM integrated `Arithmetic.RestrictionCovolume.Main` in the shared root,
whose serialized configured build passed **9354 jobs without warnings at
2026-11-06 03:04:06 UTC**, fingerprint `975bdb23135a0d4a`, root blob
`c234f9e6ab31c82d4de652bca29437e8e6ef514c`. Shared provenance and results
are recorded in `CONTRIBUTIONS.md` and `verification/RESULTS.md`. The parent
reported independent read-only acceptance of this exact handoff, its 63
probes and the shared root in I-0102 at 03:05:57 UTC. Arithmetic compactness
and manuscript Theorem 1.1 remain downstream work; this result discharges
only the exact restriction-covolume producer.

The persistent post-relocation LSP buffer reported stale imported
declarations; the successful serialized rebuild and subsequent axiom audit
checked the current files. The temporary-directory cleanup dry run found
no stale candidates and protected all four live runs.

## Constructed real space and lattice

`Arithmetic.RestrictionCovolume.TraceSpace` constructs the real span of
the simultaneous integral sections in the product of all complex fibers.
`HermitianMetric.traceCore` sums the real parts of the given pairings over
all embeddings. The induced metric therefore satisfies
`traceSection_norm_sq`, and each individual section norm is bounded by the
trace norm. Bounded-section finiteness proves discreteness of the actual
image `traceLattice`; fullness follows from the span construction.

`realTensorEquiv` is proved bijective using Mathlib's lattice-basis theorem
and agrees with `r ⊗ x ↦ r • traceSection x`. It is thus the canonical real
scalar extension, not an assumed comparison. `traceSpace_finrank` gives
the dimension `[K:ℚ] * a`. No integral freeness over `𝓞 K` is assumed.
The new blueprint node `lem:real-trace-lattice` supplies this producer to
the existing restriction-covolume node.

Kernel check: workspace-root serialized Horizon check of
`BostConjecture.Arithmetic.RestrictionCovolume.TraceSpace` passed, 3353 jobs,
fingerprint `95819e0a2a987609`. The dedicated 14-declaration axiom probe
passed (fingerprint `2bec001e17d69f56`); every listed construction and
lattice/tensor bridge uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Exact calculation

`Conjugation.lean` now proves conjugation on every vector of the real
trace space and both weighted-place pairing and squared-norm formulas.
`Covolume.lean` defines `traceCovolume` using Mathlib's actual Euclidean
Haar volume of `TraceSpace`, proves positivity and its trace Gram
determinant formula for any integer basis, and proves the exact
discriminant/degree formula when the generic rank is zero.
The module checks passed 3354 and 3609 jobs respectively (fingerprints
`d54fe514bd33c398`, `4654fd507b6b48db`).

`FiniteIndex.lean` proves that every equal-generic-rank integral submodule
has covolume `Nat.card (M ⧸ P) * h.traceCovolume`. It embeds that submodule
in the original trace space, proves fullness from the discrete-rank theorem,
identifies the induced Gram matrices, and transfers Mathlib's lattice
index to the actual integral quotient. Kernel check: 3610 jobs,
fingerprint `3318ef1836a96ed0`. The 30-probe transitive axiom audit passed
at 2026-11-06 02:00:46 UTC with only the three foundational axioms.

`Free.lean` proves the exact formula for an integral basis. The real trace
Gram matrix, complexified, factors as `E* G E`, with `E` the Kronecker
product of the identity and the transpose of the all-embedding matrix,
and `G` the block diagonal matrix of the given fiber Gram matrices.
Mathlib's `discr_eq_basisMatrix_det_sq` supplies the exact discriminant.
Conjugation makes the trace pairings real; counting all embeddings
incorporates the weight-two complex blocks, with no residual power of two.
The determinant metric and the existing intrinsic degree then give
`traceCovolume_eq_discr_degree_of_basis`. The serialized module check
passed 3610 jobs at 2026-11-06 02:21:16 UTC, fingerprint `d689c513700aeb5a`.
An earlier command used the workspace root as its Lake working directory
and failed before compilation; the successful command above uses the
member project directory with explicit Horizon `--root`.
The expanded 39-probe audit passed at 02:22:12 UTC, with only `propext`,
`Classical.choice` and `Quot.sound`. The LSP audit buffer retained an
out-of-date-import diagnostic after the dependency build; the serialized
kernel audit above checked the actual current imports and declarations.

`Line.lean` proves `traceCovolume_eq_discr_degree_of_rank_one` for every
projective line. It applies the actual free Gram computation to the
principal submodule generated by a nonzero section, transfers its covolume
by the checked finite-index formula, and substitutes the existing intrinsic
line quotient-degree formula. The module check passed 3612 jobs at
02:25:05 UTC, fingerprint `5651ddfe6a717bfa`.
Its 42-probe audit passed at 02:27:16 UTC with only the foundational
axioms. Independent review accepted the projective-line theorem and the
mathematical saturated-sequence route at `c0aef89`.

`RealForm.lean` proves that complexifying the actual trace inclusion is
bijective and that its real span is exactly the conjugation-compatible
fiber families. The injectivity and fixed-real-form arguments use the
imaginary part of the pairing with the imaginary component, which equals
its squared norm. The module check passed 3417 jobs at 02:32:54 UTC,
fingerprint `299f8d2f9c795120`. This supplies the domain bridge for the
componentwise orthogonal quotient lift.
The 48-probe audit passed at 02:34:58 UTC. These files were captured by
GEOM lifecycle snapshot `05276d0` before the explicit owned-path commit;
they were authored entirely by COVOLUME/run0008.

`Quotient.lean` constructs the actual trace maps and orthogonal right
inverse, proves its pairing and orthogonality, identifies the actual
kernel, and gives the resulting orthogonal splitting equivalence. Its
final module check passed 3420 jobs at 02:40:43 UTC (`5e5975d98e63773b`);
the expanded 58-probe audit passed at 02:40:50 UTC, foundational-only.
It is committed at `dc8a4f9`.

`Exact.lean` proves `traceCovolume_exact` using an integral splitting,
integer bases, their actual real trace extensions and the orthogonal
splitting. The basis-coordinate matrix has identity diagonal blocks;
the orthogonal Gram matrix has the two actual trace Gram blocks.
The module check passed 3614 jobs at 02:44:29 UTC (`9bcd316d640812a0`).

`Main.lean` uses the stable exact degree identity and saturated rank-one
reduction to induct on generic rank. Rank zero uses the actual empty
lattice and intrinsic degree normalization; rank one permits nonprincipal
ideals. The exact covolume theorem and exact degree theorem combine the
line and quotient induction hypotheses. No general finite-index
determinant-degree identity, freeness of the original module or
semistability assumption is used. All source-facing nodes in this slice
now have kernel-checked attachments.

The fixed TraceSpace producer received independent honesty review:
**honest/proved producer**, no actionable defect; metric and lattice data
are constructed and bounded-section finiteness is used substantively.
Root integration is delegated to GEOM in I-0092. The first source files
were captured by ARITH's lifecycle integration `21ba17f` just before the
explicit owned-path commit `cafb32d`, which contains only the audit-doc
delta. Authorship of those files is BOST-COVOLUME/run0008; no manual ARITH
source edits occurred.
The extension review also accepted `Conjugation` and `Covolume` at
`9b40453`; its requested rank-zero blueprint dependency was added.
Conjugation's source was first captured by lifecycle snapshot `b75a4e2`,
again with COVOLUME/run0008 authorship. The same axiom command fingerprint
is reused across source revisions; timestamps and probe counts above
identify the actual checked versions.
Independent review accepted `FiniteIndex` at `fc5e712` (source first
captured `e4b0d01`), including the actual quotient index and induced-metric
comparison. Its two requested dependency edges were added. GEOM integrated
TraceSpace/Conjugation/Covolume at `039cdb2`, with the shared root check
passing 9332 jobs at 02:12:49 UTC. Further imports are handed off in I-0092.
Independent review accepted the exact free-frame producer at `d41ef38`
after clarifying the blueprint's interleaved matrix index convention.
It also confirmed the mathematical validity of the saturated rank-one
induction route, conditional on proving the actual quotient-metric bridge.

## Reuse

This unit imports existing project arithmetic results and Mathlib's
`Module.Basis.ofZLatticeBasis`, `ZLattice.rank`, and scalar-extension APIs;
it copies no external source. Mathlib is the unchanged pinned dependency
`leanprover-community/mathlib4` at
`56a005855ea17e0b0958f73ec801ae140b0a1679` (Apache-2.0).
The original Mathlib lattice APIs are in
`Mathlib/Algebra/Module/ZLattice/Basic.lean`; the tensor maps are in
`Mathlib/LinearAlgebra/TensorProduct/{Lift,Basis}.lean`.
The existing project imports retain their own recorded provenance.
The Gram computation reuses `BostConjecture.Lattice.Covolume` directly;
that existing module already records its TauCeti adaptation and license.
No duplicate lattice or Gram implementation was introduced.
The new embedding calculation directly imports Mathlib's
`NumberTheory/NumberField/Discriminant/Basic.lean` and
`LinearAlgebra/Matrix/Kronecker.lean`, using `basisMatrix`,
`discr_eq_basisMatrix_det_sq`, `det_kronecker`, and `det_blockDiagonal`.
These are canonical pinned-library imports, not adapted copies.
The exact-sequence construction also reuses
`Mathlib/Algebra/Exact/Basic.lean` (`Function.Exact.splitSurjectiveEquiv`)
directly. Its consumer is `HermitianMetric.traceSplitEquiv`, and the
integral splitting in `traceCovolume_exact` uses the same API. No external
source was copied or modified, and no dependency or toolchain changed.
