# Maximal-slope proof evidence

Theorem 1.1 and its finite-family equality remain **open**. The actual HN
filtration, its integral Hermitian grades, their slope bounds, and the binary
and finite-family lower bounds are now proved for arbitrary number fields and
nonfree finite projective modules. No conditional equality is presented as the
source theorem.

## Proved MAIN producers

- `LowerBound.lean`: tensors the actual attained first HN submodules, identifies
  their induced image metric, and proves `maxSlope_add_le_tensor`.
- `FilteredBound.lean`: actual quotient semistability and bounded grade slopes
  bound every integral submodule, including nonsaturated ones, and maximal slope.
- `Arithmetic/TensorSubmodule.lean` and `TensorFlag.lean`: construct actual
  tensor images and a saturated lexicographic HN tensor filtration. The shared
  arithmetic extraction `de43a48` is byte-identical to the former declaration
  body, with a compatibility re-export and no Main dependency.
- `QuotientTransport.lean` (`f92bf10`): successive quotient metrics and
  two-factor tensor quotient metrics agree on every complex fiber.
- `TensorGrades.lean` (`f52ada8`): constructs the actual integral refinement
  quotient isomorphism using right exactness and proves its Hilbert isometry.
- `HNGrades.lean` (`a135f7e`): specializes this isometry to every flattened HN
  grade, including block transitions, and proves the factor-slope sum and its
  bound by the two maximal slopes. Positive factor-grade ranks are proved.
- `Isometry.lean` (`a135f7e`): actual integral isometric injections increase
  maximal slope; integral isomorphisms preserve it.
- `PiLowerBound.lean` (`72e704c`): the actual finite Hilbert tensor product has
  maximal slope at least the sum of factor maxima, including the empty family.
  It consumes the binary lower bound and existing regrouping/reindexing isometries.

## Exact verification boundary

The configured root at **`d0c9f8a`** passed **9404 jobs without warnings** at
**2026-11-06 04:47:44 UTC**. Root blob:
`b9b9d21ff4d7a46534e763f325b015979669e88f`.
All **52** declarations in `verification/MainAxioms.lean` have matching
transitive axiom outputs containing exactly `propext`, `Classical.choice`, and
`Quot.sound`; the serialized audit passed at **04:46:24 UTC**. Its MAIN source
cone is unchanged by the final STRICT root import. No `sorryAx` or additional
mathematical axiom occurs in these audited cones. The final equalities cannot
be axiom-audited because they are not yet defined.

```text
horizon --root /home/yijunyuan/bc-workspace check
horizon --root /home/yijunyuan/bc-workspace check --lean verification/MainAxioms.lean
```

Durable logs are in run0011/session `0004-horizon-BOST-MAIN`:
`main-root-final.log`, `main-axioms-final.log`, `main-graph-final.log`.
Earlier narrow checks passed for quotient transport (3583 jobs), the authorized
extraction/consumers (3585), generic tensor grades (3586), and HN grades (3587).
The HN specialization required a local 800000-heartbeat elaboration budget;
its kernel build completed in 276 seconds. The root subsequently checked
Isometry and PiLowerBound in 2.1 and 2.4 seconds respectively.
Guarded LSP checks guided all Lean edits. Intermediate proof errors were fixed;
umbrella/audit LSP stale-import diagnostics were superseded by successful
serialized kernel checks. One commit invocation used a project-relative cwd
with workspace pathspecs and was corrected. No broken owned proof remains.

Independent honesty/source/mathematical reviewers inspected the actual quotient
maps, nonfree module coverage, block endpoints, grade slope consumers, finite
induction, exact logs and all axiom outputs. Two blueprint corrections made the
finite index range explicit and removed an unattached tensor-grade positivity
assertion. Six new MAIN nodes are now checked; the main theorem and finite-family
equality remain notready. These reviews certify proved producers only.

## Current-owner integration

The final root imports the exact independently accepted handoffs:

| Lane | Source checkpoint | Actual endpoint / evidence |
| --- | --- | --- |
| COMPACTNESS | `e81b08b` | Nonfree global maximizing pairs; 40 foundational-only probes |
| SPECHT-SLOPE | `8c80c92` | Actual geometric slope inequality; 39 probes |
| TENSOR-SEMI | `5eee92c`, `2fef69d`, `e0b0bb1`, `7fd2332` | Local maximum, actual metric derivatives, scalar defects and conjugate bases; latest 49 probes |
| LINE-TWIST | `032df77` | Both tensor orders for arbitrary nonprincipal lines; 10 probes |
| STRICT-REDUCTION | `b49b67f` | Internally minimal, strictly stable normalized global maximizing counterexample; 10 probes |

Review compared each current import cone against its owner checkpoint, including
56 LINE and 104 STRICT project modules. Both LINE endpoints are substantively
used by STRICT to exclude rank one. STRICT has no MAIN or final tensor-semista
dependency. Broad automatic snapshots were not used as acceptance evidence.
Attribution and pinned external sources remain in `CONTRIBUTIONS.md`.

## Remaining route and hygiene

TENSOR-SEMI must finish actual arithmetic conjugation/projection-trace transport,
extremal balance and unconditional tensor semistability. MAIN then applies that
proved theorem to the actual HN grades, transports semistability through the
checked integral isometry, and applies the filtered bound for the upper bound.
Together with the unconditional lower bound this gives the binary equality.
The finite equality uses the checked finite lower bound and an upper-bound
induction on the actual finite tensor metric; average-slope additivity gives
its semistability consequence. No assumed producer package substitutes for
these unfinished steps.

`BOST-MAIN-FILTRATION` and `BOST-MAIN-LOWER` are done; `BOST-MAIN-UPPER` and
`BOST-MAIN-FINITE` record the remaining work. BOST-MAIN remains active.
Graph sync resolves all source/dependency attachments (370 blueprint nodes,
2423 declarations); 1137 unattached helper/concurrent-draft declarations are
intentional coverage warnings. This latest graph also sees the ongoing
ProjectionConjugation draft, which is outside the checked root boundary. Ground found no stale scratch candidates and
accepted the repaired roadmap with no consistency warnings. All helpers were
read-only; MAIN retains sole shared integration ownership.

Parent convergence handoff I-0138 confirms that completed LINE/STRICT lanes
should exit and that no additional writer is needed. MAIN continues solely
with the proved TENSOR endpoint as the next input for its remaining consumer
proofs. The finalization scan found only pre-existing untracked workspace
configuration/instruction files and the two reference PDFs; these are outside
MAIN ownership and were not staged. All authored MAIN source and evidence are
committed.
