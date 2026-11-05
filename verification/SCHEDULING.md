# Parallel Horizon scheduling

Coordinator checkpoint: 2026-11-06 04:28 Asia/Shanghai (2026-11-05 20:28 UTC).

The user assigned the parent session scheduling only, with at most three
concurrent proof tasks and no spending cap. Horizon owns the mathematics.
The standing ownership rule is inbox `I-0012`; configuration was committed in
`d9a1468`. No publishing or pushing is authorized by this arrangement.

| Run | Task | Proof ownership | Current frontier |
| --- | --- | --- | --- |
| `0003` | `BOST-SPECHT` | `Specht/**`, `Lattice/**`, Specht blueprint | Tableau enumeration and prefix-distribution estimates for covolume asymptotics |
| `0004` | `BOST-ARITH` | `Arithmetic/**`, `Slope/**`, arithmetic blueprint | Dual degree, general tensor/exact-sequence identities and intrinsic HN specialization |
| `0005` | `BOST-GEOM` | `Geometry/**`, `Tensor/**`, geometry blueprint | Scalar extension of the integral pairing, global contraction, then invariant/nonvanishing arguments |

Each task owns its corresponding verification files. BOST-SPECHT is the sole
editor of the shared root import, `CONTRIBUTIONS.md`, `RESULTS.md`, and shared
blueprint index/status files. Checked APIs pass between tasks through the inbox.
The arithmetic and geometry lanes share the existing `ComplexFiber`,
`HermitianMetric`, and determinant-coordinate interfaces.

## Continuing the runs

The three foreground runs are active at this checkpoint. Before resuming any
run, inspect `horizon ps --json` and its terminal session status. Resume an exited
run with meaningful remaining work, keeping the total at three. For example:

```sh
/home/yijunyuan/.local/bin/horizon --root /home/yijunyuan/bc-workspace ps --json
/home/yijunyuan/.local/bin/horizon --root /home/yijunyuan/bc-workspace run --resume 0003 --rounds 10 --no-dashboard --json
```

Keep the command in the foreground and monitor it. Writable proof helpers also
consume a proof slot. Read-only reviews remain part of the Horizon workflow.
All kernel checks use the explicit workspace root and the single shared check
slot; prefer narrow checks during repair and complete the required final checks.

## Accepted evidence and open boundaries

The latest completed joint boundary is SPECHT session `0021`, final evidence
commit `baa0cc7`: the root build passed 9,171 jobs at 20:05:06 UTC, and 49
new axiom probes used only the standard foundational axioms. This includes
the actual seminormal norm product, rectangular Gram determinant and canonical
orbit-lattice covolume bound (`333c037`). The asymptotic is still open.

ARITH session `0008` exited normally at 20:03:40 UTC, committed through
`3131d4b`, with 135 foundational-only probes. Its successor `0010` is active
on general-rank dual degree after checking the intrinsic dual metric and
line dual degree. GEOM session `0010` exited normally at 20:23:44 UTC,
committed through `5344b4d`: local contraction at `00eec3c` passed 9,088 jobs
and 138 foundational-only probes. That newer metric batch awaits the next root
integration through `I-0044`; it is not included in the 9,171-job result above.

The current sessions are SPECHT `0023`, ARITH `0010`, and GEOM `0012`.
SPECHT `0023` is the last currently planned round of run `0003`; resume the
run after it exits if the task remains incomplete, without exceeding three
proof writers. The saved hook-count draft has since been repaired and checked.
GEOM's saved evaluation-base-change draft has also passed a new module check;
its global pairing consumer remains in progress. Use the owners' exact source
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
and invariant orbit-closure criterion are not discharged by the three lanes'
current milestones. A successful local batch
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

The repair is committed as `d0f37d5`. All three current proof sessions now have
actual guarded MCP processes, verified by command and parent ancestry:

- ARITH `0010`: wrapper PIDs `364426`/`364450`, Codex `364286`, run PID `161941`.
- SPECHT `0023`: wrapper PIDs `375430`/`375478`, Codex `375307`, run PID `76365`.
- GEOM `0012`: wrapper PIDs `379185`/`379198`, Codex `379060`, run PID `163151`.

The old sessions ended normally. Temporary transition protection `I-0034` is
archived; guarded diagnostics are permitted and kernel builds still use the
shared Horizon check slot. The launcher and configuration remain in effect.
Handoff hints `I-0042` and `I-0043` are archived after verifying continuation;
the earlier integration-cutoff thread `I-0033` was already consumed.

The coordinator has made no mathematical edits: all proof changes above were
produced by Horizon. Continuation remains authorized; no new proof writer or
fourth run was launched at this checkpoint. Dashboard HTTP health was checked
successfully at `http://127.0.0.1:8765`.
