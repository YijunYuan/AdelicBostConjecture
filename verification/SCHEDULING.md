# Parallel Horizon scheduling

## Live checkpoint at 2026-11-06 02:02 UTC

The user explicitly requests **four continuing Horizon proof lanes until the
entire main theorem is complete**, with no budget cap. The parent only schedules,
reviews handoffs and monitors memory; Horizon owns all mathematical authorship.
The four-writer cap includes writable helpers. Keep runs in foreground tool
sessions, refill completed slots with actual remaining dependencies, and reduce
concurrency at safe checkpoints if memory pressure is sustained. Do not restart
a completed task merely to fill a slot. No push/publication is authorized.

**Original Lemma 7.2 is fully verified and the user was notified in this chat
at approximately 01:47 UTC.** The exact theorem is
`BostConjecture.Balanced.IsBalanced.plucker_semistable` in
`Balanced/PluckerSemistability.lean:118`, including an actual positive-degree
homogeneous invariant nonzero on each nonzero intrinsic Plucker representative.
Its scoped build passed 3,619 jobs; all 195 transitive axiom probes are
foundational-only. Independent source, mathematical and honesty reviews accepted
the original statement. Integration `cf391765` passed 9,329 warning-free root
jobs at 01:44:09 UTC. Blueprint attachments and completion markers are accepted.
The final theorem blob is `74e9fb060b2cacbc37a15d35bac52921477a659f`.
No additional build is needed for this milestone.

| Run | Task | Current responsibility |
| --- | --- | --- |
| `0005` | `BOST-GEOM` | Binary Plucker/contraction consumers and shared integration |
| `0010` | `BOST-COMPACTNESS` | Metric continuity, arithmetic compactness and maximizing pairs |
| `0008` | `BOST-COVOLUME` | Actual restriction-of-scalars trace-metric covolume |
| `0009` | `BOST-SPECHT-SLOPE` | Actual determinant-Specht bundles and geometric slope inequality |

ARITH run `0004` finished normally at 01:50:45 UTC, with its full task marked
done. Its arbitrary-number-field, nonfree-projective degree calculus, actual HN
specialization and all-rank degree finiteness are checked: 366 foundational-only
probes, root `cf391765`, final evidence `c4f4348`. Do not resume it.
SPECHT run `0003` completed the canonical-lattice covolume limit at 23:50:16 UTC
(evidence `e2e7039`/`8d57641`, root 9,263 jobs). CLOSURE run `0007` completed at
01:16:41 UTC (proof `53f1119`, integration `d29f2d3`, evidence `f7ffd4f`, 40
foundational-only probes). Neither completion implies the main theorem is done.

Standing ownership is `I-0095`, superseding archived `I-0087`. GEOM
alone edits the shared root, attribution, results and blueprint index files.
COVOLUME owns only `Arithmetic/RestrictionCovolume/**`,
`blueprint/src/restriction_covolume.tex`, `verification/RestrictionCovolumeAxioms.lean`
and `verification/RESTRICTION_COVOLUME.md`; its stable input handoff is in
`ARITHMETIC.md`. Completed source APIs stay stable unless parent coordinates a
specific extension. The remaining main theorem, contraction and compactness
claims are open. The bounded read-only review and GEOM handshake accepted the two successors
in `I-0094`. GEOM committed the complete blueprint migration and includes at `1e56d1d`.
The two successors started at 02:01:05/02:01:13 UTC (PIDs 714087/714164),
restoring four live foreground runs. Their first sessions are both `0002`. SPECHT-SLOPE owns `Arithmetic/Specht/**`, `Slope/Geometric/**`,
`specht_slope.tex` and its verification pair. COMPACTNESS owns
`Arithmetic/Compactness/**`, `arithmetic_compactness.tex` and its verification
pair. Metric continuity and arithmetic reconstruction can proceed before the
pending covolume identity. One complex irreducible fiber suffices for the
actual Specht application; do not expand to a general irreducibility library.
The generic coaction square has no remaining consumer on this route and its
roadmap item is retired, without claiming it proved.

At 01:57 UTC, before successor startup, available memory was 15.15 GiB,
PSI avg10 0.00%, swap used 3.12 GiB and OOM kills zero; swap-out was unchanged.
Independent read-only warmup review at 02:02:50 UTC accepted exactly four
engines on gpt-6-astra/xhigh/subscription, actual guarded successor MCPs
714795/714952, no extra writer or source overlap, 14.48 GiB available, PSI
avg10 zero, unchanged swap-out, OOM zero and dashboard HTTP 200. GEOM and
both successors acknowledged the completed migration in I-0094. All active proof runs use the guarded Lean LSP; broad checks
remain serialized through explicit-root Horizon checks. Dashboard remains on
port 8765. Advisory `I-0084` records global search-index rebuild costs: batch
searches at stable checkpoints and avoid redundant forced reindexing.

## Earlier checkpoints

The sections below preserve dated history; the live table and I-0095 above
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
