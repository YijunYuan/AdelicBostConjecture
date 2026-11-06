# Parallel Horizon scheduling

## Live checkpoint at 2026-11-06 04:09 UTC

The user requests **four continuing Horizon proof lanes until the entire main
theorem and its used dependencies are complete**, with no budget cap. The parent
only schedules, reviews handoffs and monitors memory; Horizon owns mathematical
Lean and blueprint authorship. The four-writer cap includes writable helpers.
Keep runs in foreground tool sessions and refill completed slots with substantive
remaining work. Never resume a completed task simply to fill a slot. Reduce
concurrency at a safe checkpoint if memory pressure is sustained. No publication
or push is authorized.

| Run | Task | Current responsibility |
| --- | --- | --- |
| `0009` | `BOST-SPECHT-SLOPE` | Actual determinant-Specht slope and geometric slope inequality |
| `0010` | `BOST-COMPACTNESS` | Arithmetic compactness and maximizing pairs |
| `0011` | `BOST-MAIN` | HN tensor filtration, maximal-slope theorem and shared integration |
| `0012` | `BOST-TENSOR-SEMI` | Arithmetic first variation, extremal-to-balance and tensor semistability |

MAIN started at 03:12:19 UTC (PID 765334); TENSOR-SEMI at 03:12:26 (PID 765881).
Their foreground tool sessions remain open. Standing protection `I-0104`
supersedes archived `I-0095`. The accepted migration is `439d654`; its
handoff `I-0102` is archived. `I-0106` coordinates the live ownership transfer.
MAIN continues in session `0004` after normal session `0002` ended at
03:49:38 UTC. Its run remains live; this did not free a writer slot.

MAIN is now the sole editor of root `BostConjecture.lean`, `CONTRIBUTIONS.md`,
`verification/RESULTS.md`, and shared blueprint includes/index/OPEN_PROOFS.
Its proof scope is `Main/MaxSlope/**`, `main.tex` and its verification pair.
TENSOR-SEMI owns `Main/TensorSemistability/**`, `tensor_semistability.tex`
and its verification pair. It owns extensions/twists and the actual arithmetic
local-maximum-to-balance argument, then consumes COMPACTNESS, SPECHT-SLOPE and
accepted Lemma 7.2. MAIN consumes its proved tensor semistability for the final
HN upper bound; the dependency does not run in reverse. Lower-bound and
filtration work can proceed independently. No unfinished producer may become
an assumed premise of a claimed completed source theorem.

SPECHT-SLOPE retains `Arithmetic/Specht/**`, `Slope/Geometric/**`,
`specht_slope.tex` and its verification pair. COMPACTNESS retains
`Arithmetic/Compactness/**`, `arithmetic_compactness.tex` and its pair.
Completed APIs stay stable unless the parent coordinates an exact extension.
Late compactness `870179a` was outside the final GEOM root scope and is a
checked handoff for MAIN; subsequent Specht handoffs likewise go to MAIN.

## Accepted completed producers

**Original Lemma 7.2 is fully verified; the user was notified around 01:47 UTC.**
The exact theorem is `Balanced.IsBalanced.plucker_semistable` in
`Balanced/PluckerSemistability.lean:118`, including an actual positive-degree
homogeneous invariant nonzero on each nonzero intrinsic Plucker representative.
Scoped build: 3,619 jobs; 195 foundational-only transitive axiom probes;
independent exact-source, mathematical and honesty acceptance. Root `cf391765`
passed 9,329 warning-free jobs. Final theorem blob:
`74e9fb060b2cacbc37a15d35bac52921477a659f`. BALANCED exited normally at
01:53:33, final evidence `65ac4e1`. Do not resume it or re-notify as a new result.

GEOM completed and exited normally at **03:11:03 UTC**. Terminal
`exists_canonicalPairing_nonzero_sequence_of_binary_invariant` is committed at
`1557324`, blob `ae575df89d7dbf17b767bec176ec4b9cc9f7aa7b`. Its 9,121-job
module check and all 291 foundational-only probes passed. Failed conversion
attempts remain preserved, not accepted as proofs. The direct original-ring
contraction route is proved; the unused generic coaction descent remains retired.

COVOLUME completed and exited normally at **03:11:14 UTC**. Exact
`HermitianMetric.traceCovolume_eq_discr_degree` at `5144157` covers arbitrary
number fields, nonfree projectives and rank zero. Identical canonical trace-basis
relocation `739e58a` was reconciled with COMPACTNESS. Rebuilt target: 3,652 jobs;
63 foundational-only probes; independent source, mathematical and honesty
acceptance. Final evidence `1a816f3`.

Both were integrated at **`ec99c23`**, with **9,354 warning-free root jobs**
at 03:04:06 UTC. Independent read-only handoff review accepted exact endpoints,
axiom outputs, root imports and migration `439d654`. The latter preserves
the two tensor-semistability nodes and their complete mathematics, with no
duplicate labels. Both predecessor foreground commands returned exit 0 before
either successor was launched. These completions do not prove the main theorem.

Other completed predecessors: ARITH `0004` exited 01:50:45, evidence `c4f4348`,
366 foundational-only probes; SPECHT `0003` exited 23:50:16, exact canonical
covolume asymptotic `e2e7039`/`8d57641`; CLOSURE `0007` exited 01:16:41,
proof `53f1119`, root `d29f2d3`, evidence `f7ffd4f`, 40 probes. Do not resume.

## Resource and runtime checkpoint

Before successor startup: 15.41 GiB available, PSI avg10 zero, swap 2.42 GiB,
unchanged swap-out counter 9,146,901 and zero OOM kills. A bounded read-only
startup review at 03:13:57 UTC accepted exactly four engines, old GEOM/COVOLUME
descendants gone, no orphan Lean process, and actual guarded successor MCPs
765594/766135. Memory after startup: 14.71 GiB available, PSI zero, swap 2.41 GiB,
unchanged swap-out and no OOM. Dashboard returned HTTP 200 in 0.11 seconds.
All new runs retain gpt-6-astra/xhigh/subscription. Broad checks use
the explicit workspace root and one serialized Horizon check slot.
Dashboard remains at port 8765. No fifth proof writer is authorized.

Earlier transient pressure at 02:16 was traced to two GEOM LSP trees loading
the same module. Its normal 0016→0018 handoff removed the duplication; all
old trees were confirmed gone. No emergency kill or user HN process change
occurred. Advisory `I-0084` records global search-index rebuild costs:
batch searches at stable checkpoints and avoid redundant forced reindexing.

At 03:31:44 a further read-only resource review found exactly four engines,
8.48 GiB available, no duplicate same-file workers and no OOM. Transient PSI
had receded; no resource-driven handoff was warranted. Reviewer clients remain
under their owners' normal lifecycle. The separate Specht combined-import
failure was a generated-instance name collision, repaired by explicit names;
its combined axiom audit passed again at 03:38:43. I-0112 is resolved/archived.

At 04:09, all four proof lanes continue. MAIN's lower bound, filtered bound,
tensor images/quotient metrics and saturated lexicographic flag are checked
(`5913d84`, `66d4baa`, `04dd654`); its actual consecutive-grade isometries
remain open. Simultaneous tensor quotient metrics are checked at `f92bf10`.
TENSOR-SEMI has checked extensions and metric/degree variation
(`57f5cfc`, `bbafa44`), conjugation-compatible exponential variation (`e68943d`)
and actual extremal neighborhoods (`5eee92c`); balance remains open.
COMPACTNESS's exact maximizing-pair endpoint `e81b08b` passed 9,156 module jobs
and 40 foundational-only probes. Its actual nonfree module/metric/saturated
global-maximizer witnesses and source route are independently accepted. Root
`ece5ec1` passed 9,380 warning-free jobs at 04:06:01, evidence `f670cb2`.
Its task still needs normal closure/exit before reuse of the slot.
SPECHT-SLOPE's complex/binary invariant result was accepted at `cf57d33`/
`7249a02` with scope correction `ea93f72`. Subsequent generalization directly
reuses GEOM's proved original-ring pairing; new source `8c80c92` has a fresh
dependency build and 39-probe audit. Final root integration/exit remain pending;
the earlier 38 probes are not evidence for that later source revision.
These are intermediate producer checks, not a main-theorem completion claim.

A bounded read-only route review and both current owners accepted one future
split in `I-0113`: actual Hermitian line twists for arbitrary nonprincipal
rank-one modules, in both factor orders, including real submodule/metric
transport. Reserve `Main/LineTwist/**`, `line_twist.tex` and a dedicated
verification pair only after a genuine slot frees and a committed handoff.
The line-twist result must not import general tensor semistability.

The newly checked maximizing-pair API then made a second split concrete.
Both owners accepted `I-0120`: reserve `Main/StrictReduction/**`,
`strict_reduction.tex` and its verification pair. From a normalized actual
semistable counterexample, construct internally rank-sum minimality and actual
strictly stable normalized maximizing factors of ranks at least two, with
positive saturated maximizing submodule and the existing `IsGreatest` bound.
Inputs are Extensions, MaximizingPair, LINE-TWIST and shared arithmetic tensor
submodule metrics; no MAIN theorem or variation/balance input is allowed.
TENSOR-SEMI retains normalization, its active variation/balance chain and final
contradiction. No successor task or blueprint migration has started yet.

`I-0121` authorizes one bounded MAIN extraction after its in-flight root boundary:
move the unchanged `TensorFiltration.lean` declarations to
`Arithmetic/TensorSubmodule.lean` with direct arithmetic imports, preserving
names/proofs and leaving the old module as a re-export. MAIN confirmed that no
LowerBound declarations are used. The checked leaf handoff is required before
StrictReduction starts; avoid a reverse dependency or duplicate proof machinery.
Both successors launch only after actual free slots and explicit handoffs.

## Earlier checkpoints

The sections below preserve dated history; the live table and I-0104 above
govern current ownership. Do not resume completed SPECHT run `0003`.

Coordinator checkpoint: 2026-11-06 07:20 Asia/Shanghai (2026-11-05 23:20 UTC).

The user assigned the parent session scheduling only, with no spending cap. The user subsequently authorized a fourth dedicated
Lemma 7.2 lane if memory pressure is low; the total cap is now four proof
writers, including writable helpers. Horizon owns all mathematical work.
The new four-slot ownership protection `I-0046` supersedes the archived `I-0012`;
existing proof ownership is retained. No publishing or pushing is authorized by this arrangement.

| Run | Task | Proof ownership | Current frontier |
| --- | --- | --- | --- |
| `0003` | `BOST-SPECHT` | `Specht/**`, `Lattice/**`, Specht blueprint | Bulk concentration, separation and logarithmic expectation for covolume asymptotics |
| `0004` | `BOST-ARITH` | `Arithmetic/**`, `Slope/**`, arithmetic blueprint | Exact-sequence determinants, general tensor-degree identities and intrinsic HN specialization |
| `0005` | `BOST-GEOM` | `Geometry/**`, `Tensor/**`, geometry blueprint | Invariant scalar extension and nonvanishing after the checked contracting pairing |
| `0006` | `BOST-BALANCED` | `Balanced/**`, `InvariantTheory/**`, balanced/orbit sections of compactness blueprint | Exact manuscript Lemma 7.2, including the needed analytic and orbit-closure/invariant criteria |

Each task owns its corresponding verification files. BOST-SPECHT is the sole
editor of the shared root import, `CONTRIBUTIONS.md`, `RESULTS.md`, and shared
blueprint index/status files. Checked APIs pass between tasks through the inbox.
The arithmetic and geometry lanes share the existing `ComplexFiber`,
`HermitianMetric`, and determinant-coordinate interfaces.

## Continuing the runs

All four foreground runs are active. Run `0006` started at 20:35:37 UTC with
session `0002-horizon-BOST-BALANCED`, PID `390675`. Before resuming any
run, inspect `horizon ps --json` and its terminal session status. Resume an exited
run with meaningful remaining work, keeping the total at four. For example:

```sh
/home/yijunyuan/.local/bin/horizon --root /home/yijunyuan/bc-workspace ps --json
/home/yijunyuan/.local/bin/horizon --root /home/yijunyuan/bc-workspace run --resume 0004 --rounds 10 --no-dashboard --json
```

Keep the command in the foreground and monitor it. Writable proof helpers also
consume a proof slot. Read-only reviews remain part of the Horizon workflow.
All kernel checks use the explicit workspace root and the single shared check
slot; prefer narrow checks during repair and complete the required final checks.

SPECHT session `0023` ended successfully at 21:03:42 UTC. The coordinator
checked its report, confirmed only the other three runs were live and the cap
was four, then resumed run `0003` for another ten rounds. The successor is
`0026-horizon-BOST-SPECHT`, round 11, started at 21:05:14 UTC; run PID `409475`.

## Accepted evidence and open boundaries

The latest recorded joint boundary is SPECHT session `0028`, evidence
`8e22cbc`: the configured root build passed **9,223 jobs without warnings** at
22:47:30 UTC, and its 22 new Specht axiom probes used only the standard
foundational axioms. That root includes `Arithmetic.ExactDegree`,
`Geometry.ContractionNorm`, `Balanced.SpectralExpansion`, and
`InvariantTheory.Semistability`, with the owners' scoped checks and audits.
It does not certify later tensor-flow, tensor-degree or invariant-base-change
producers, nor any headline result still open below.

The current sessions are SPECHT `0030`, ARITH `0014`, GEOM `0016`, and BALANCED
`0006`; all four foreground invocations continue normally.

- **SPECHT:** the canonical integral lattice, Gram bound and exact finite
  prefix distribution are checked. The current round has additionally checked
  the bulk normalizer bound, finite sampling moments, actual occupancy MGF
  and coordinate/union concentration bounds. Weighted separation,
  logarithmic expectation and the general covolume limit remain open.
- **ARITH:** intrinsic dual degree, the nonfree exact-sequence determinant,
  full complex-fiber determinant isometry and exact-sequence degree additivity
  are checked, including zero ranks and splitting independence. `ExactDegree`
  passed 3,544 warning-free jobs and the final 201 foundational-only probes
  (`2f716f5`, evidence `9c913aa`, satisfactory independent review). This
  degree endpoint is root integrated. The lane has since checked tensor-metric
  compatibility and saturated rank-one reduction for degree induction.
  Arbitrary-rank tensor degree is now verified with 221 foundational-only
  probes and independent review. Actual Hermitian subspace supermodularity
  and interval/quotient slopes have since passed review and 235 probes.
  Arithmetic degree finiteness and HN specialization remain open.
- **GEOM:** the actual canonical contracting pairing is checked through its
  intrinsic dual-fiber norm bound (`fd211a8`, evidence `8045b27`), with 163
  foundational-only probes and satisfactory honesty review, now root integrated.
  New invariant base-change, independent-factor invariants and polynomial
  quotient/evaluation producers are separately checked with 184 probes.
  The natural invariant tensor lift is now checked through the TauCeti port
  below, with 202 probes. Rectangular invariant-space identification, the
  full nonvanishing construction and invariant base-change bridges remain open.
- **BALANCED:** actual Plucker norm variation (`76a3ad5`) is checked and root
  integrated. The complex exterior metric is an original construction using
  imported mathlib basis/pairing APIs; the existing real-only exterior metric
  was not silently treated as a complex theorem. Spectral expansion, convexity
  and stationary minimum (`eae8dac`) now have a module check, independent
  review and 40 foundational-only probes, now root integrated. The actual
  tensor-flow bridge and balanced norm minimum passed a module check at
  22:45:07 UTC (`cc2ec60`), followed by its axiom check. Determinant-one polar
  factorization and the traceless Hermitian logarithm now have scoped builds,
  86 foundational-only probes and satisfactory independent review. The actual
  Plucker representation, full special-linear orbit norm lower bound and
  Euclidean closure exclusion are now checked (`b94d6c3`, final evidence
  `5148896`): 3,188 warning-free jobs, 92 foundational-only probes and
  satisfactory honesty review. Newest root integration is pending. Algebraic
  closure comparison and nonvanishing homogeneous invariant existence remain
  open, so the source Lemma 7.2 is not complete.

Manuscript **Lemma 7.2 and the main theorem remain unproved**. The dedicated
lane has made substantive analytic progress; no norm estimate, interface
agreement or source-backed blueprint is counted as the full semistability
conclusion. The reviewed smaller closure route below is still unformalized.

Use exact source revisions and check evidence in [RESULTS.md](RESULTS.md),
[ARITHMETIC.md](ARITHMETIC.md), [GEOMETRY.md](GEOMETRY.md) and
[BALANCED.md](BALANCED.md). Automatic cross-task snapshots can capture live
drafts: commit presence alone is not verification. Check fingerprints identify
commands, so latest cache records can be replaced by reruns. Use explicit
owned paths on the commit command and preserve source/check timestamps.
Unattached helper/imported graph nodes and ancestor-inclusive roadmap counts
remain documented coverage warnings, not extra proof writers or completion.

## LSP dependency-build race and recovery

On 2026-11-05 at 19:01 UTC, a root build reached 9,147/9,148 jobs but
could not load `Tensor/Hilbert.olean` after its successful build. A process
snapshot subsequently showed an LSP `lake setup-file` compiling that same
dependency while a Horizon-serialized build was running. Pausing those LSP
queries allowed the root retry to pass 9,148 jobs at 19:08:01 UTC. This is a
build-artifact incident, not a Specht proof failure.

`tools/lean_lsp_no_build.py` now launches the workspace MCP with
`lean-lsp-mcp==0.33.0` and `leanclient==0.13.2`. It forces LSP document opens
to use `dependencyBuildMode=never` and disables the client's internal
stale-import retry that otherwise switches to `once`. Diagnostic errors remain
visible. Build imports with explicit-root `horizon check`, then query LSP again.
The uncoordinated `lean_build` MCP tool is disabled in the Codex configuration.

The tracked `config.yaml` harness arguments carry this launch configuration.
The generated, ledger-excluded `.codex/config.toml` also carries it so new
sessions of already-running Horizon processes receive the fix. Project-level
MCP configuration is documented in the
[official Codex documentation](https://learn.chatgpt.com/docs/extend/mcp?surface=cli).
Installed packages, user-wide configuration, and the user's separate
HarderNarasimhan process were not modified.

Validation: `codex mcp get lean-lsp --json` from the member project resolves
the guarded launcher; Horizon harness/TOML parsing succeeds. The isolated
end-to-end smoke test passes all four checks: missing imports reported,
normal diagnostics working, stale imports reported, and dependency artifacts
unchanged. Reproduce with:

```sh
uvx --from lean-lsp-mcp==0.33.0 --with leanclient==0.13.2 python tools/check_lean_lsp_no_build.py
```

The repair is committed as `d0f37d5`. At the initial four-lane rollout, all
four proof sessions had actual guarded MCP processes, verified by command
and parent ancestry:

- ARITH `0010`: wrapper PIDs `364426`/`364450`, Codex `364286`, run PID `161941`.
- SPECHT `0023`: wrapper PIDs `375430`/`375478`, Codex `375307`, run PID `76365`.
- GEOM `0012`: wrapper PIDs `379185`/`379198`, Codex `379060`, run PID `163151`.
- BALANCED `0002`: wrapper PIDs `391121`/`391456`, Codex `390896`, run PID `390675`.

These PIDs record the completed guarded-client rollout; SPECHT subsequently
continued in session `0026`, whose guarded launcher PID `409947` was verified
under Codex `409818` and run PID `409475`. The old sessions ended normally. Temporary transition protection `I-0034` is
archived; guarded diagnostics are permitted and kernel builds still use the
shared Horizon check slot. The launcher and configuration remain in effect.
Handoff hints `I-0042` and `I-0043` are archived after verifying continuation;
the earlier integration-cutoff thread `I-0033` was already consumed.

The coordinator has made no mathematical edits: all proof changes above were
produced by Horizon. Continuation remains authorized. The additional BALANCED lane follows the
user's explicit request; no fifth proof writer is authorized. Dashboard HTTP health was checked
successfully at `http://127.0.0.1:8765`.

## Fourth-lane resource and completion conditions

Before authorizing the fourth run, the coordinator measured 23.46 GiB total
RAM and 8.86 GiB available, memory pressure avg10 0.03%, and no sustained swap
out in the interval sample. About 4.49 GiB of swap was already occupied; this
is recorded separately from active swapping. Keep builds serialized and
monitor memory after startup. The immediate postlaunch sample retained
8.63 GiB available with memory-pressure avg10 0.18%. The read-only operational
review at 20:39 UTC confirmed four distinct healthy lanes, 8.79–9.01 GiB
available, PSI avg10 0.04%, and no swap-out increase or OOM kills. The roadmap
warning counts nine ancestors plus four active fronts; it is retained
intentionally, with current evidence added to `I-0017`. No extra proof writer
was launched for that review.

BALANCED owns the shared geometric-semistability and orbit-criterion API and
coordinates its consumers with GEOM through `I-0047`. Its proof must cover the actual source
conclusion, including all external results it uses; an analytic norm bound
alone does not complete Lemma 7.2. The parent will notify the user in this chat
only after the exact theorem, transitive axioms, independent review and required
integration have passed. No wait for Specht asymptotics or HN is required.

In `I-0048`, the coordinator granted BALANCED a bounded reference-only
extension: new `references/maithani-reynolds/` and
`references/milne-algebraic-geometry/` directories, their manifest entries,
and their entries in `blueprint/src/refs.bib`. Only the used pages/results
should be registered; SPECHT retains shared root/progress-file ownership.
The shared invariant-polynomial design in `I-0047` is agreed: GEOM confirmed
BALANCED's SymmetricAlgebra degree/evaluation API and forward-coaction
convention, and BALANCED consumed that confirmation. Implementation, degree
base change, coaction compatibility and the rational-point invariant bridge
remain proof obligations. Design agreement does not certify these exports
or complete the orbit criterion.

A bounded read-only strategy review identified the current curve-based
Euclidean/Zariski closure comparison as a costly dependency cone, and checked
existing Noether-normalization, constructibility, Cauchy-bound, minpoly and
lying-over declarations. In `I-0054`, the coordinator handed BALANCED a
candidate finite-map/root-persistence route for independent mathematical
review. Horizon's independent review accepted that mathematical route,
requiring the actual minimal polynomial and `ker_eval` for root lifting.
BALANCED is replacing the curve proof and pruning its unused dependencies;
all complex-point adapters and Lean closure conclusions remain open. The
route decision in `I-0054` is concluded, without claiming formalization or
attributing the entire alternative to the partial external source lead.

At 21:56 UTC, available memory was 7.46 GiB, PSI avg10 6.76% and avg60
6.93%, with zero OOM kills. Swap occupancy had risen to 8.64 GiB;
the process sample shows substantial shared Lean-library mappings alongside
active elaboration. Monitor actual available memory, swap deltas and sustained
PSI rather than summing per-process RSS. In `I-0055`, the coordinator asked
GEOM to finish its in-flight metric check, preserve the unfinished dual-norm
work and hand off at its verified pairing boundary. GEOM `0012` ended
successfully at 22:01:50 UTC; `0014` started at 22:02:58 UTC. After this
client recycling, available memory rose to 10.36 GiB and PSI avg10 fell to
0.00% (avg60 0.17%), with zero OOM kills. The four proof lanes continue,
including the dedicated Lemma 7.2 lane; continue resource monitoring.

The same bounded handoff was used for ARITH in `I-0061`: `0012` ended normally
at 22:28:47 UTC after the verified exact-sequence degree milestone; `0014`
started at 22:29:07 UTC. Available memory then measured 10.33 GiB, PSI avg10
0.00% and zero OOM kills. The consumed hint is archived; arithmetic work
continues without adding a proof writer.

In `I-0063`, GEOM accepted a narrowly scoped TauCeti polarization extraction;
BALANCED confirmed its existing polynomial/degree/pullback definitions will
stay fixed. GEOM has temporary ownership of new
`BostConjecture/LinearAlgebra/SymmetricPower/**` and
`vendor/tauceti-polarization/**`, including exact attribution and checks.
SPECHT retains shared root and contribution-file ownership. The immutable
source survey and remaining bridge obligations are recorded in
[STACKS_AND_MATHLIB_PRS.md](STACKS_AND_MATHLIB_PRS.md) (`0a1be77`).
GEOM subsequently checked the port and actual invariant-tensor consumer
(`c55300f`, evidence `94cc6d8`): 2,379 build jobs, 202 foundational-only probes,
and satisfactory honesty/source-fidelity reviews. Its root/contribution handoff
is `I-0066`; rectangular invariant identification is still open. No full TauCeti
dependency or fifth proof writer is authorized.

The preventive resource handoff `I-0067` coincided with GEOM `0014` ending
normally at 23:08:29 UTC and `0016` starting immediately afterward. Available
memory recovered from 6.78 to 9.47 GiB; no OOM occurred. All four foreground
runs continue. The 23:04 scratch dry run found no stale candidates and protected
all live runs; dashboard HTTP health remained 200.

BALANCED's analogous checked-boundary handoff `I-0069` completed normally:
session `0004` ended at 23:18:08 UTC and `0006` started at 23:18:12 UTC.
The report retains the analytic endpoint and exact open algebraic boundary;
the successor explicitly continues from that boundary. The 23:19 resource
sample showed 8.55 GiB available, swap occupancy 2.77 GiB, PSI avg10 0.76%
and no OOM kills. The four-lane authorization remains sufficient.

In `I-0070`, GEOM independently assessed and accepted a smaller Schur–Weyl
route for the actual rectangular invariant span over algebraically closed
characteristic-zero fields. The source survey `de76963` records the proposed
615-line extraction and explicit rank-one consumer; local implementation,
integer normalization, orbit transport and any required field descent remain
unverified. GEOM now has bounded ownership of new
`BostConjecture/RepresentationTheory/SchurWeyl/**` and
`vendor/tauceti-schur-weyl/**` for that port. Existing #44845 tensor-Hom code
must be reused; no full TauCeti import or extra proof writer is authorized.
The route decision is complete; the resulting theorem is not.
