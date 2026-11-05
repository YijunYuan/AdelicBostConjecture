# Parallel Horizon scheduling

Coordinator checkpoint: 2026-11-06 01:52 Asia/Shanghai (2026-11-05 17:52 UTC).

The user assigned the parent session scheduling only, with at most three
concurrent proof tasks and no spending cap. Horizon owns the mathematics.
The standing ownership rule is inbox `I-0012`; configuration was committed in
`d9a1468`. No publishing or pushing is authorized by this arrangement.

| Run | Task | Proof ownership | Current frontier |
| --- | --- | --- | --- |
| `0003` | `BOST-SPECHT` | `Specht/**`, `Lattice/**`, Specht blueprint | Recursive Murphy triangularity, then seminormal norms and covolume asymptotics |
| `0004` | `BOST-ARITH` | `Arithmetic/**`, `Slope/**`, arithmetic blueprint | Saturated integral submodules, remaining degree calculus and intrinsic HN specialization |
| `0005` | `BOST-GEOM` | `Geometry/**`, `Tensor/**`, geometry blueprint | Finite-projective chart assembly and overlap transport, then global determinant inclusion |

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

The latest joint boundary reviewed here is `e148582`: the configured root build
passed 9,127 jobs, including geometry descent, and the 34 new Specht probes used
only standard foundational axioms. Current drafts and later arithmetic additions
need their own evidence. Detailed source revisions, checks and remaining claims
belong in [RESULTS.md](RESULTS.md), [ARITHMETIC.md](ARITHMETIC.md), and
[GEOMETRY.md](GEOMETRY.md).

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
arithmetic degree calculus/HN, projective assembly, metric contraction, and
invariant/nonvanishing arguments still require work. A successful local batch
does not close those tasks.
