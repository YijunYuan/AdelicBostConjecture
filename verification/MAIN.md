# Maximal-slope theorem: final verification

Manuscript Theorem 1.1 and its finite-family corollary are proved over every
number field for positive-rank finite projective modules over its ring of
integers, including nonfree modules. The metrics are the actual Hilbert tensor
metrics. No normalization, balance, maximizer or assumed semistability premise
occurs in either maximal-slope identity.

## Exact accepted Lean source

- Source revision: `dd5c6b6ed81b960910d4b63c941cbd144a9e87eb`.
- MAIN consumer checkpoint: `fe9f652`.
- Root blob: `8878f1ce6ea8f15ceca334713ff837b6b0723fef`.
- All 335 root-reachable project modules match that source revision. Subsequent
  evidence/blueprint changes do not alter these Lean sources.

`HermitianMetric.maxSlope_tensor` is the binary identity.
`HermitianMetric.maxSlope_piTensor` is the finite-family identity, including
empty and singleton families, and `HermitianMetric.isSemistable_piTensor` is
its semistability consequence. All are exported by `BostConjecture.lean`.

## Kernel and transitive axiom evidence

Run0011/session `0006-horizon-BOST-MAIN` contains the actual logs and records:

- `main-root-final.log`: explicit-root `horizon check`, **9413 jobs**, exit0,
  no warnings, finished **2026-11-06 06:02:11.878281 UTC**. Record:
  `checks/2026-11-06T06-02-11.878281+00-00-975bdb23135a0d4a.json`.
- `main-final-axioms.log`: explicit-root
  `horizon check --lean verification/MainAxioms.lean`, exit0, finished
  **2026-11-06 06:03:07.979012 UTC**. Record:
  `checks/2026-11-06T06-03-07.979012+00-00-c2186924c8587570.json`.

All **60** probe outputs match the declaration names and order in
`verification/MainAxioms.lean`. Each contains exactly `propext`,
`Classical.choice`, and `Quot.sound`. These are Lean's standard foundations;
there is no `sorryAx` or additional mathematical axiom in any audited
transitive cone. The six final probes explicitly include tensor semistability,
HN tensor-grade semistability, the binary upper bound and equality, and both
finite-family conclusions. Both checks are fresh, with `reused:false`.

The first binary consumer check hit the default 200000-heartbeat limit at the
HN-grade transport. Its source/diagnostics are preserved in session attempt0002.
A theorem-local 800000 budget, with unchanged proof and statement, passed the
fresh 9403-job check at05:58:48.348278 UTC. Guarded LSP retained stale imports
following the shared instance repair; narrow dependency refreshes and a clean
full-source `lean_run_code` for PiTensor preceded the final build. No error or
warning remains in the accepted checks. The CLI's spurious resource-slot
message is tracked in I-0001; both final records show only0.002s waiting.

## Actual producer-to-consumer route

1. `LowerBound` tensors actual attained first HN submodules. The induced image
   is isometric and its tensor slope is the sum, giving the unconditional lower
   bound. `PiLowerBound` extends it through actual regrouping isometries and
   proves the exact empty-unit maximum.
2. `TensorFlag`, `TensorGrades` and `HNGrades` construct a saturated integral
   tensor refinement, its consecutive integral quotient isometries, positive
   factor-grade ranks, and slope bounds, including block transitions.
3. `Tensor.hnTensorGrade_isSemistable` applies the proved unconditional
   `IsSemistable.tensor` to the actual HN quotient metrics. `FilteredBound`
   bounds every positive-rank submodule, including nonsaturated ones. The upper
   and attained lower bounds give `maxSlope_tensor`.
4. `PiTensor` consumes the binary equality, the independent finite lower bound,
   and actual regrouping/reindexing isometries. Average-slope additivity then
   gives finite tensor semistability.

Accepted producer pins are COMPACTNESS `e81b08b`, SPECHT-SLOPE `8c80c92`,
LINE `032df77`, STRICT `b49b67f`, and TENSOR `b3236e1` with balance `9ba97a4`,
rescaling `392e101`, and geometric bridge `aae85ac`. The bounded two-instance
repair `f8975ea` preserves the public arithmetic API. Its dependency cone was
rebuilt by TENSOR, then the MAIN cone and root were freshly checked above.
The 318-module TENSOR cone contains no `Main.MaxSlope` dependency.

## Independent review and source scope

Independent source-fidelity, mathematical-correctness and honesty reviewers
accept the final MAIN statements and their substantive consumers. The source
review uses original manuscript pages1–3 and13, with registered transcriptions;
`Bost.pdf` is not substituted for the number-field target. The honesty reviewer
also compared all335 root-reachable project files and all60 actual axiom
outputs against the exact pin. The independent verification review is recorded
alongside these in this session's transcript.

The blueprint attaches `lem:hn-tensor-grade-semistable`, `thm:bost-main`, and
`cor:bost-finite-family` to these exact declarations. External reuse remains
pinned and attributed in `CONTRIBUTIONS.md`; no new external assumption or
changed dependency is introduced. Weighted HN compatibility, effective rates,
appendices, and unused general descent interfaces are outside this target.

Claim class: **proved endpoint**. Frontier before: unconditional tensor
semistability followed by final HN consumers. Frontier after: no unmet producer
for Theorem1.1 or its finite-family corollary. `honesty-reviewer`: used.
Earlier prerequisite-only root boundaries remain in `RESULTS.md` and ledger
history; they are not evidence for this final revision.
