# Parallel Horizon scheduling

Coordinator checkpoint: 2026-11-06 04:09 Asia/Shanghai (2026-11-05 20:09 UTC).

The user assigned the parent session scheduling only, with at most three
concurrent proof tasks and no spending cap. Horizon owns the mathematics.
The standing ownership rule is inbox `I-0012`; configuration was committed in
`d9a1468`. No publishing or pushing is authorized by this arrangement.

| Run | Task | Proof ownership | Current frontier |
| --- | --- | --- | --- |
| `0003` | `BOST-SPECHT` | `Specht/**`, `Lattice/**`, Specht blueprint | Tableau enumeration and prefix-distribution estimates for covolume asymptotics |
| `0004` | `BOST-ARITH` | `Arithmetic/**`, `Slope/**`, arithmetic blueprint | Dual degree, general tensor/exact-sequence identities and intrinsic HN specialization |
| `0005` | `BOST-GEOM` | `Geometry/**`, `Tensor/**`, geometry blueprint | Actual integral pairing and its norm bound, consuming projective isometry and equivariance |

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

The latest completed joint boundary reviewed here is `75b41aa`: the configured
root build passed 9,148 jobs at 19:08:01 UTC, after the artifact-race recovery
below. SPECHT session `0019` exited successfully and its 32 new-producer probes
used only standard foundational axioms. Later accepted producers include:

- `c0009e2`, `66af066`, and `b0d9750`: adjacent action, the column-reading
  initial norm, and legal-swap connectivity. Adjacent action and initial-value
  modules passed; the path file passed at 19:40:38 UTC. The manuscript norm
  product and asymptotic are still open.
- `d15ab3e` and audit `31f3fff`: full-fiber determinant contraction and saturation
  degree inequality. The `SaturationDegree` build passed at 19:30:41 UTC;
  123 arithmetic axiom probes passed at 19:32:08 UTC. `4f53c5a` additionally
  proves tensor coordinate-ideal multiplication; the metric/degree consumer
  remains under development.
- `77dd408`, `9868e05`, and `f409e4a`: prescribed local determinant isometry,
  complex-fiber isometry, and global position equivariance. The projective
  equivariance build passed at 19:39:50 UTC. The first pairing-module check
  passed at 19:42:59 UTC, but this is not yet a certified contraction bound.

The next fixed root-import batch is coordinated in `I-0036` and `I-0037`.
Current drafts and later additions need their own evidence.
Detailed source revisions, checks and remaining claims
belong in [RESULTS.md](RESULTS.md), [ARITHMETIC.md](ARITHMETIC.md), and
[GEOMETRY.md](GEOMETRY.md).

Update at 20:09 UTC: `333c037` proves the seminormal norm product, rectangular
Gram determinant and canonical orbit-lattice covolume bound. The root build
passed 9,171 jobs at 20:05:06 UTC and `SpechtSeminormalAxioms.lean` passed
at 20:06:19 UTC; the session's final integration report is still in progress.
ARITH session `0008` exited normally at 20:03:40 UTC, committed through
`3131d4b`, with 135 foundational-only probes. Its successor `0010` is active
and has checked the intrinsic dual metric (`ba2f037`). GEOM additionally
committed tensor-duality and dual-regrouping isometry as `178980b`; the
determinant-pairing norm consumer is still being checked. None of these
updates proves the covolume asymptotic or manuscript main theorem.

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
arguments still require work. A successful local batch
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

The change takes effect when an MCP process starts. Old unwrapped clients must
continue using serialized kernel feedback; protection `I-0034` tracks that
transition. New guarded clients may use LSP without compiling dependencies.
The repair is committed as `d0f37d5`; its four tracked files were rechecked
against ledger HEAD. ARITH's new session `0010` has actual guarded launcher
processes `364426`/`364450`, traced through Codex `364286` to run `0004` PID
`161941`, and has successfully used LSP diagnostics. SPECHT `0021` and GEOM
`0010` still have old clients and remain kernel-only until normal session
turnover. A configuration listing alone is not evidence that a running MCP
process was replaced.
The completed previous integration-cutoff thread `I-0033` is archived.

The coordinator has made no mathematical edits: all proof changes above were
produced by Horizon. Continuation remains authorized; no new proof writer or
fourth run was launched at this checkpoint. Dashboard HTTP health was checked
successfully at `http://127.0.0.1:8765`.
