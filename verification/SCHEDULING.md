# Parallel Horizon scheduling

Coordinator checkpoint: 2026-11-06 05:44 Asia/Shanghai (2026-11-05 21:44 UTC).

The user assigned the parent session scheduling only, with no spending cap. The user subsequently authorized a fourth dedicated
Lemma 7.2 lane if memory pressure is low; the total cap is now four proof
writers, including writable helpers. Horizon owns all mathematical work.
The new four-slot ownership protection `I-0046` supersedes the archived `I-0012`;
existing proof ownership is retained. No publishing or pushing is authorized by this arrangement.

| Run | Task | Proof ownership | Current frontier |
| --- | --- | --- | --- |
| `0003` | `BOST-SPECHT` | `Specht/**`, `Lattice/**`, Specht blueprint | Tableau enumeration and prefix-distribution estimates for covolume asymptotics |
| `0004` | `BOST-ARITH` | `Arithmetic/**`, `Slope/**`, arithmetic blueprint | Exact-sequence determinants, general tensor-degree identities and intrinsic HN specialization |
| `0005` | `BOST-GEOM` | `Geometry/**`, `Tensor/**`, geometry blueprint | Scalar extension of the integral pairing, global contraction, then invariant/nonvanishing arguments |
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

The latest completed joint boundary is SPECHT session `0023`, final evidence
commit `81945dd`: the root build passed 9,190 jobs at 20:56:40 UTC, and 34
new counting/weight axiom probes used only the standard foundational axioms.
The new producers identify actual tableau prefixes and prove their exact
squared-Vandermonde binomial weights. The earlier seminormal norm product,
rectangular Gram determinant and canonical orbit-lattice covolume bound
(`333c037`) remain in use. Distribution normalization, bulk separation and
the general covolume asymptotic are still open.

ARITH session `0008` exited normally at 20:03:40 UTC, committed through
`3131d4b`, with 135 foundational-only probes. Its successor `0010` has checked
general-rank dual degree (`49b13ce`, audit `9869294`, 165 probes), and is active
on exact-sequence determinants. GEOM session `0010` exited normally at 20:23:44 UTC,
committed through `5344b4d`: local contraction at `00eec3c` passed 9,088 jobs
and 138 foundational-only probes. The 9,190-job root batch now includes
`Arithmetic.LineDualDegree`, `Arithmetic.DeterminantDual`,
`Geometry.ContractionMetric`, `Tensor.EvaluationBaseChange`, and
`Tensor.DualRegroupBaseChange`. Later undelivered leaves are excluded.

The current sessions are SPECHT `0026`, ARITH `0012`, GEOM `0012`, and BALANCED `0004`.
ARITH `0010` handed off with final evidence `1c0421a` and 171
foundational-only probes. Its exact exterior-product and finite-free
determinant-product producers await root integration in `I-0050`;
ARITH `0012` continues the nonfree projective descent.
The saved hook-count and evaluation-base-change drafts have been repaired,
checked and integrated. GEOM's full pairing transport and global contraction
consumer remain in progress. BALANCED has checked intrinsic partial traces
(`fdb954d`), their actual orthogonal-projection consumer (`3361234`), and the
Gram determinant first variation (`ee2abe7`); its 16-probe axiom audit passed
at 21:04:53 UTC with standard foundational axioms only, and the scoped honesty
review was satisfactory. The actual exponential-flow consumer subsequently
passed 2,821 jobs at 21:28:53 UTC (`5e76175`), with all 19 export probes
foundational-only at 21:30:33 UTC. Evidence `9cddfb6` records satisfactory
source, mathematical and honesty reviews. Their updated root handoff is
`I-0049`. BALANCED `0002` ended successfully at 21:38:47 UTC and `0004`
started at 21:40:05 UTC after the coordinator's checkpoint hint `I-0053`.
The next analytic step uses the existing exterior-power inner-product API
to connect Gram variation with the Plucker norm. These leaves are not yet
the full Lemma 7.2 or part of the
9,190-job root boundary. Use the owners' exact source
revisions and checks in [RESULTS.md](RESULTS.md), [ARITHMETIC.md](ARITHMETIC.md),
and [GEOMETRY.md](GEOMETRY.md), rather than treating live drafts as accepted.

Automatic project-wide boundary snapshots can capture another task's drafts;
their presence in a commit is not verification. Use explicit owned pathspecs
and preserve exact check timestamps and source revisions. Check fingerprints
identify commands, so their latest cache records can be overwritten by reruns.

The two earlier geometry capacity interruptions are recorded in `I-0018`;
the missing audit was recovered and that incident is archived. The temporary
check-queue hint `I-0025` was acknowledged and archived. Subsequent completed
rounds inspected by the coordinator exited successfully. The latest temporary
directory dry run found no stale candidates and protected all three live runs.

The manuscript main theorem remains unproved. General Specht asymptotics,
arithmetic degree calculus/HN, metric contraction, and invariant/nonvanishing
arguments still require work. Manuscript Lemma 7.2, balanced projections imply
Plücker semistability, still has an empty Lean attachment; its analytic argument
and invariant orbit-closure criterion are now assigned to the new BALANCED
lane, rather than counted as completed by the existing milestones. A successful local batch
does not close those tasks.

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
Exact semistability API signatures are still being settled in `I-0047`.
The coordinator requested these signatures at the next coherent exponential
proof boundary, before GEOM begins its invariant consumer. BALANCED has
proposed concrete signatures in its verification record; GEOM confirmation
is still pending.

A bounded read-only strategy review identified the current curve-based
Euclidean/Zariski closure comparison as a costly dependency cone, and checked
existing Noether-normalization, constructibility, Cauchy-bound, minpoly and
lying-over declarations. In `I-0054`, the coordinator handed BALANCED a
candidate finite-map/root-persistence route for independent mathematical
review before any blueprint replacement. The candidate is not an accepted
proof, source attribution, or Lean result. The analytic lane continues while
Horizon decides whether this smaller affine route is valid and useful.

At 21:43 UTC, available memory was 7.64 GiB, PSI avg10 7.92% and avg60
4.07%, with zero OOM kills. Swap occupancy rose during transient pressure;
the process sample shows substantial shared Lean-library mappings alongside
active elaboration. Monitor actual available memory, swap deltas and sustained
PSI rather than summing per-process RSS. No
resource condition currently requires reducing the four proof lanes.
