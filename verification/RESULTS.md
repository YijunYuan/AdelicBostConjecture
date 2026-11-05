# Dependency integration evidence — 2026-11-05

## Monic orthogonalization and Murphy operators — session 0011

`Orthogonal.lean` constructs a monic orthogonal basis from the existing
standard real basis for any total order and proves the exact Gram norm
product and its orbit-covolume consumers. `RealAction.lean` restricts the
real isometric word action to the actual Specht span and proves symmetry,
pairwise commutation and the adjacent recurrence of its Murphy sums.
The adjacent diagonal-coefficient corollary explicitly requires two
eigenvalue equations; it is not a proof of the content spectrum.

The explicit-root serialized check of both modules passed (9,061 jobs).
`check --lean verification/SeminormalAxioms.lean` passed all 22 probes;
only `propext`, `Classical.choice`, and `Quot.sound` occur. LSP diagnostics
are clean. Local elaboration failures were repaired before this checkpoint.
Full umbrella integration and the required honesty review follow separately.

Claim class: **proved producers**, with one **conditional spectral corollary**.
The first unmet source producer is now the content-triangular Murphy action
and its dominance-order control; the explicit prefix norm product and the
general covolume limit remain unproved. The original Murphy proof could not
be retrieved; its access record is `references/murphy-seminormal-1981/notes.md`.

## Rectangular determinant covariance and PR integration — session 0009

Commits `f3d37a3` and `c5a4975` identify the actual integer rectangular
polytabloid with a product of unnormalized alternating columns, and prove
that its word tensor-power matrix action is multiplication by `det(u)^k`.
The result holds over every commutative ring and is consumed by the actual
integral orbit lattice, its scalar span and the existing complex Specht
module. `wordTensorAction_prod` proves the action applies the matrix
independently to pure-tensor factors. No factorial division, invariant-space
hypothesis or replacement lattice is used.

- `horizon check BostConjecture.Specht.ColumnTensor --json` passed at
  **14:45:03 UTC** (9,058 jobs; fingerprint `b98225d4a0b91993`).
- The configured `horizon check --json` with covariance passed at
  **14:54:07 UTC** (9,095 jobs).
- `horizon check --lean verification/CovarianceAxioms.lean --json` passed at
  **14:55:12 UTC** (fingerprint `137e2cddfd6ab359`). All **19** transitive
  probes, comprising eight Stacks exports and eleven new public declarations,
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- The combined configured build after adding all three approved Mathlib PR
  root imports passed at **14:56:32 UTC** (**9,101 jobs**, 18.528 seconds).
  No Lean source changed after this check. The PR source ports and their
  45 export axiom checks belong to the parent; this session integrated root
  imports and attribution links. See `STACKS_AND_MATHLIB_PRS.md` for the
  parent's API review and historical Polar check-cache caveat.

All commands used the workspace Horizon CLI. The recurring resource-slot
notice had measured waits of 0.001 seconds (known issue I-0001). Narrow
producer LSP diagnostics are clean; the umbrella import file remained in
partial LSP elaboration, so its evidence is the completed kernel build.
Initial local proof elaboration errors were repaired; no kernel check failed.

Claim class: **proved producers**. Covariance frontier before: the isolated
alternating-vector theorem lacked its rectangular word consumer. After:
column factorization and actual lattice/complex-Specht covariance are checked.
Consumer: `lem:determinant-isotypic`; abstract tensor-map transport, projective
local-frame gluing, metric compatibility and invariant-space equality are
still open. The main Gram frontier remains `lem:monic-seminormal`, followed
by the prefix law and sublinear estimate; manuscript Theorem 1.1 is unproved.

Final graph: 60 blueprint nodes, 485 Lean declarations, 199 edges, 25 checked
blueprint nodes and zero stale nodes. A mistyped covariance dependency was
corrected. The 302 unattached helper/imported declarations are intentional
coverage warnings (I-0004), including approved PR producers without source
completion claims. The source-scope symlink is preserved; scratch cleanup
found no stale candidates.

Honesty-reviewer: **used, satisfactory**. It independently checked the
column producer and its axioms, reviewed the final covariance consumers and
recorded checks, and found no target-shaped hypothesis, vacuity or replacement
lattice. Its two metadata findings (page-9 anchors and the all-tableaux
dependency label) were repaired. One capacity interruption was recovered;
the review then completed. Boundary memory I-0010 preserves the distinction
between word covariance and the remaining tensor/gluing/invariant obligations.

## Rational spanning and the actual standard Gram bound — session 0007

Commits `e29f2ab` and `54e9cbf` prove integral Garnir cancellation,
rational standard-polytabloid spanning by a bounded-moment induction,
coefficientwise transport to the actual standard real basis, the equality
of integral orbit rank with standard-tableau count, and the unconditional
standard Gram covolume and logarithmic inequalities. The pinned TauCeti
adaptation uses the existing word/tableau model; no alternate representation
or integral standard-basis assertion is introduced.

- `horizon --root /home/yijunyuan/bc-workspace check BostConjecture.Specht.Straightening --json`
  passed at **14:22:29 UTC** (9,056 jobs, 8.441 seconds).
- `horizon --root /home/yijunyuan/bc-workspace check --json` passed at
  **14:29:33 UTC** (9,092 jobs, 13.012 seconds).
- `horizon --root /home/yijunyuan/bc-workspace check --lean verification/SpechtAxioms.lean --json`
  passed at **14:30:50 UTC** (14.908 seconds). All **50** transitive probes
  report only `propext`, `Classical.choice`, and `Quot.sound`.

LSP diagnostics were used throughout. Initial Garnir doc-comment placement
errors were repaired; no build or proof failure remains. The only later
Lean change cleans comment references and trailing whitespace. Known
resource-slot notices had recorded waits of 0.001 seconds (I-0001).

Claim class: **proved producers**. Frontier before:
`lem:rational-standard-spanning`; after: `lem:monic-seminormal`.
Consumer: `standardRealBasis` and its lattice membership now discharge
`covolume_sq_le_det_gram` to yield `covolume_sq_le_det_standard_gram` and
its logarithmic version. The real basis is explicitly in the coordinate
real span; no unproved real tensor-equivalence is claimed by its node.
The seminormal Gram formula, prefix law, general sublinear limit and
manuscript Theorem 1.1 remain unproved.

Honesty-reviewer: **used, satisfactory**. Two reviewer attempts were unable
to start because of model capacity; the subsequent `gpt-6.1-sol` high-effort
review completed and independently reproduced the spanning and logarithmic
bound axiom checks. Its blueprint/integration findings were applied:
coordinate-span wording, explicit column moment, root import, new probes,
and removal of stale open-frontier prose. No target-shaped hypothesis,
vacuity or unused spanning scaffold was found.

Final graph: 58 blueprint nodes, 408 Lean declarations, 23 checked blueprint
nodes, zero stale nodes. The obsolete rational tensor-basis plan node was
removed; the actual consumer uses rational spanning directly. The 236
unattached helper/imported declarations remain intentional coverage warnings
(I-0004). Source-scope symlink is preserved; scratch cleanup found no stale
candidates. I-0008 was acknowledged: the parent owns the new Stacks alternating
tensor extraction; its rectangular determinant-covariance bridge remains
separate downstream work, not part of this session's verification claim.

## Rectangular and standard-family producers — session 0005

Commits `38d00f7`, `4f1312f`, `5fcb018`, `8ee59c6`, and `fa614ea`
prove the polytabloid norm, integral-real-basis Gram upper bound,
rectangular word realization and factorial initial norm, standard-polytabloid
independence over every ring, and the one-row covolume/limit respectively.

`horizon check --json` passed at **14:09:21 UTC** (9,088 jobs,
6.784 seconds). `horizon check --lean verification/SpechtAxioms.lean --json`
passed at **14:10:06 UTC** (10.499 seconds). All 38 transitive probes report
only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or new
axioms occur. LSP feedback was used throughout. An early Standard inverse
coercion error and local proof attempts were repaired before these checks;
no accepted proof is broken. The known resource-slot message again had
recorded wait at most 0.001 seconds.

Claim class: **proved producers**, with an explicit **conditional interface**
for the Gram bound requiring an integral real basis. Frontier before:
rectangular specialization and standard basis. Frontier after:
`lem:rational-standard-spanning`, then real transport and seminormal action.
Consumer: the standard real basis will feed `covolume_sq_le_det_gram`;
the actual one-row integral basis already feeds `oneRow_covolume_eq_one`.
The general covolume limit and manuscript Theorem 1.1 remain unproved.

The reviewed minimal route uses the all-polytabloid orbit lattice and the
full-rank standard sublattice, so the exact standard-family Gram identity
gives `0 ≤ 2c_a(d) ≤ E log γ`. No integral standard-spanning theorem or
index estimate is assumed. Ryom-Hansen v1 is attached as the precise source
of the still-open seminormal action formula, not as Lean proof evidence.

Honesty-reviewer: **used**, satisfactory through `fa614ea`, including the
one-row attachment and build/axiom records. Final graph sync reports 56
blueprint nodes, 339 Lean declarations, 18 checked blueprint nodes and zero
stale nodes. Its 212 unattached helper/imported declarations are intentional
coverage warnings recorded in I-0004. The source-scope symlink is unchanged;
scratch cleanup found no stale candidates.
The janitor boundary review confirmed consistent roadmap children, no open
conversations, and no additional cleanup needed.

## Integral Specht producers — run 0003

Commits `45d3fe4`, `f34d7fc`, and `c78c52b` add
`BostConjecture/Specht/{Integral,Tableau,Metric}.lean`:

- A nonzero finite free integral orbit span, equal to the span of all
  polytabloids of the shape, with permutation stability.
- An injective complex tensor-extension map onto `OAI.Saxl.Specht`, with
  an explicit linear equivalence and equivariance.
- An orthonormal word metric in `EuclideanSpace`, a discrete full lattice
  in its own real span, and a concrete consumer of the reused covolume–Gram
  theorem. Its Gram determinant is an integer, yielding covolume at least one.

The configured `horizon --root /home/yijunyuan/bc-workspace check --json`
passed at **13:40:32 UTC** (9,084 jobs, 15.856 seconds). The serialized
`check --lean verification/SpechtAxioms.lean --json` passed at
**13:41:48 UTC** (6.486 seconds). All 17 transitive axiom probes report
only `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx`
or additional axiom. LSP diagnostics were used throughout; initial local
elaboration errors were repaired before the successful builds. No accepted
proof or build remains broken.

Claim class: **proved producers**. Frontier before: missing integral orbit,
scalar extension, and Hilbert realization. Frontier after: the rectangular
specialization and integral standard-polytabloid basis, then monic seminormal
Gram formula and prefix/asymptotic producers. The standard-polytabloid span
has not been identified with the all-polytabloid lattice in Lean. Neither
the sublinear limit nor manuscript Theorem 1.1 is formalized.
Consumer: `covolume_sq_eq_integer_gram` and `one_le_covolume`, then the
nonnegativity step of `thm:specht-sublinear-covolume`.

Honesty-reviewer: **used**; its read-only source/body and artifact review
found no honesty defect in the seven new checked blueprint nodes and confirmed
that the standard-basis boundary stays open. It identified the need to sync
the generated graph, which is now done. The graph has 43 blueprint nodes,
292 Lean declarations, seven checked blueprint nodes, and no stale nodes.
The 198 unattached helper/imported declarations are an intentional coverage
warning, not completion evidence. The source-scope symlink is preserved.
The known Horizon 0.1.5 resource-slot message recurred with recorded waits
of 0–0.001 seconds; no actual contention was observed. Scratch cleanup's
dry run found no stale candidates. Parent task BOST-SPECHT remains open.

## Accepted Lean state

- Lean `leanprover/lean4:v4.35.0`.
- mathlib `v4.35.0` at `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- HarderNarasimhan `14b3090e1e169b77fe381102a1289f24c2b08a11` uses the same toolchain and mathlib commit.
- 12 selectively copied OpenAI modules, 5 Etingof release modules, and a 95-line TauCeti Gram/covolume extraction with six theorems; exact provenance and local changes are in the corresponding vendor records.
- `BostConjecture/Slope/Subspace.lean` proves positivity of strict-interval ranks, slope-likeness of degree differences, explicit finite slope evaluation, and convexity from degree supermodularity on actual finite-dimensional subspaces. It does not define Hermitian arithmetic degree or prove its properties.

## Kernel checks

All commands ran in `projects/BostConjecture` with the explicit workspace root.

```
horizon --root /home/yijunyuan/bc-workspace check --json
horizon --root /home/yijunyuan/bc-workspace check --lean verification/ReuseAxioms.lean --json
```

The configured build passed without warnings at **2026-11-05 13:20:16 UTC**
(9,081 jobs including cached prerequisites, 9.965 seconds). The subsequent
axiom check also passed. All 19 audited declarations report
only `propext`, `Classical.choice`, and `Quot.sound`; none reports `sorryAx` or
an additional axiom. The probe file gives the exact declaration list.

Original OpenAI source was also replayed successfully on 4.35 before adaptation.
Etingof proof elaboration and local slope adapter errors encountered during
porting were repaired; the accepted state has no remaining build errors.
The Etingof worker additionally checked the division form of the hook-length
formula with the same foundational-axiom result.

## Scope and review

Claim class: **proved prerequisite producers**. Arithmetic application is still
an **unproved bridge**, and manuscript Theorem 1.1 is **not formalized**.
The main frontier remains integral rectangular Specht lattices with compatible
metrics and sublinear normalized covolume, plus intrinsic Hermitian arithmetic
objects and their slope theory. Intended consumers are manuscript §§2, 5–7.

A bounded independent ground handoff review found no blocking issue in the
configuration, pinned provenance, source boundaries or next-task scope.
An independent external-boundary reviewer read the Mahler proof cone and the
pinned HN contracts. It confirmed that the former proves real-lattice compact
frames, and the latter abstract HN existence/uniqueness; neither discharges the
number-field/metric bridges. A bounded mathematical route review found no
concrete defect in the inspected manuscript steps, but is not a complete
correctness certification.

No honesty-reviewer was dispatched for this bounded import batch: no new
certificate, target-shaped assumption, or main-theorem completion claim was
introduced. Future bridge/completion reviews remain required as appropriate.

Root-session Lean LSP tools were unavailable in its tool roster, so local
adapter edits used narrow serialized kernel checks. The Etingof worker had
working LSP diagnostics and used them before its final kernel checks.

Horizon 0.1.5 emits a spurious resource-slot waiting message even when its
recorded wait is about 0.002 seconds: its `flock` success return is tested
against zero. This is recorded as a tooling issue, not proof evidence.
