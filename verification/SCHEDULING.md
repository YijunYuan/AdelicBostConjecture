# Parallel Horizon scheduling

Coordinator checkpoint: 2026-11-06 06:31 Asia/Shanghai (2026-11-05 22:31 UTC).

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
/home/yijunyuan/.local/bin/horizon --root /home/yijunyuan/bc-workspace run --resume 0003 --rounds 10 --no-dashboard --json
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

The latest completed joint boundary is SPECHT session `0026`, final evidence
`4d40509`: the configured root build passed **9,210 jobs without warnings** at
22:11:39 UTC, and its 38 new Specht axiom probes used only the standard
foundational axioms. That root includes the intrinsic exact-sequence
determinant and Plucker norm handoffs, with separate 192- and 30-probe audits,
as well as the earlier geometry pairing base-change leaf. It does not certify
later independent producers or any headline result still open below.

The current sessions are SPECHT `0028`, ARITH `0014`, GEOM `0014`, and BALANCED
`0004`; all four foreground invocations continue normally.

- **SPECHT:** the canonical integral lattice, Gram bound and exact finite
  prefix distribution are checked. The current round has additionally checked
  the bulk normalizer bound (`76b7bf8`). Concentration, uniform separation,
  logarithmic expectation and the general covolume limit remain open.
- **ARITH:** intrinsic dual degree, the nonfree exact-sequence determinant,
  full complex-fiber determinant isometry and exact-sequence degree additivity
  are checked, including zero ranks and splitting independence. `ExactDegree`
  passed 3,544 warning-free jobs and the final 201 foundational-only probes
  (`2f716f5`, evidence `9c913aa`, satisfactory independent review). This newer
  degree endpoint awaits the next root batch. General tensor degree,
  finiteness, supermodularity and HN specialization remain open.
- **GEOM:** the actual canonical contracting pairing is checked through its
  intrinsic dual-fiber norm bound (`fd211a8`, evidence `8045b27`), with 163
  foundational-only probes and satisfactory honesty review. This newer
  endpoint awaits a subsequent root batch. The lane is now working on
  invariant scalar extension and nonzero evaluation; invariant detection and
  the full geometric task remain open.
- **BALANCED:** actual Plucker norm variation (`76a3ad5`) is checked and root
  integrated. The complex exterior metric is an original construction using
  imported mathlib basis/pairing APIs; the existing real-only exterior metric
  was not silently treated as a complex theorem. Spectral expansion, convexity
  and stationary minimum (`eae8dac`) now have a module check, independent
  review and 40 foundational-only probes. The tensor-flow bridge,
  determinant-one polar/logarithm reduction and algebraic orbit/invariant
  criterion remain open. The spectral leaf awaits subsequent root integration.

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
