# Strict maximizing counterexamples

The source-facing producer is
`BostConjecture.Arithmetic.Compactness.exists_strict_maximizing_counterexample`
in `Main/StrictReduction/MaximizingCounterexample.lean`, committed at `b49b67f`.
It proves `lem:strict-maximizing-counterexample` from manuscript pages 12–13.

From any actual positive-rank normalized semistable pair whose Hilbert tensor
is not semistable, it constructs actual finite projective factors over the
same number field, of ranks at least two, with degree zero and the existing
`IsStable` predicates. It returns an actual saturated tensor submodule of
positive degree equal to the actual tensor `maxDegree`, and an `IsGreatest`
proof for the existing `tensorMaxDegreeValues` at the factors' ranks.
No integral freeness hypothesis is imposed.

The proof constructs the least rank sum using `Nat.find`, applies the checked
arithmetic maximizing-pair producer, excludes rank one using both LINE-TWIST
exports, and derives strict stability by applying normalized tensor extension
closure to a hypothetical degree-zero proper saturated factor submodule.

## Verification

All commands were run through `horizon --root /home/yijunyuan/bc-workspace check`.

| Unit | Source commit | Kernel evidence (UTC, 2026-11-06) |
| --- | --- | --- |
| `MinimalRank` | `81f0fcf` | 9163 jobs passed, 04:27:18 |
| `TensorExtension` | `8fb4ac2` | 3677 jobs passed, 04:28:33 |
| `StrictFactors` | `d3bf378` | 9167 jobs passed, 04:36:37 |
| `MaximizingCounterexample` | `b49b67f` | 9171 jobs passed, 04:39:47 |
| `verification/StrictReductionAxioms.lean` | `b49b67f` | ten probes passed, 04:40:18 |
| Shared root `BostConjecture` | `d0c9f8a` | 9404 jobs passed without warnings, 04:47:44 |

All ten transitive axiom probes report exactly `propext`, `Classical.choice`,
and `Quot.sound`; there is no `sorryAx` or additional mathematical axiom.
The final producer audit therefore covers the full LINE-TWIST, compactness,
degree, exact-metric and strict-reduction dependency cone.

Independent read-only source, mathematics and honesty review accepted all
four blueprint nodes, the actual witness construction and the use of each
load-bearing producer. The reviewer also independently probed all ten
declarations. Final source SHA256:
`2a5fa2fc6d699dd1663fb6781830d256d5d57d2d5196debc78dfbb697cd1f2b0`.

The first strict-factor draft failed a narrow check because quotient
projectivity needed an explicit finite-presentation construction; that was
repaired before the accepted `d3bf378` build. A stale-import LSP document and
one timed-out fresh guarded LSP were superseded by clean LSP feedback and the
serialized checks above. No unresolved proof failure remains in this slice.

## Integration boundary

The exact consumer is
`HermitianMetric.isLocalMax_degree_of_maximizing_pair`: the returned strict
metrics, normalization, saturated submodule, attaining equality and global
maximality match its existing inputs. TENSOR owns metric variation, balance
and final tensor semistability; those conclusions are not claimed here.

TENSOR accepted the exact checked producer handoff (I-0132), and LINE accepted
the checked uses of both rank-one semistability exports (I-0127). MAIN's
independent integration review compared all 104 project modules in the
producer cone against `b49b67f`, then imported the endpoint in `d0c9f8a`.
The combined shared-root check passed 9404 jobs without warnings at 04:47:44
UTC (I-0134); the root blob is
`b9b9d21ff4d7a46534e763f325b015979669e88f`. Its saved log is
`runs/0011/sessions/0004-horizon-BOST-MAIN/main-root-final.log` under
`.archon-horizon/`.

All four strict-reduction blueprint nodes are `lean_ok`. The final slice sync
resolved all source and dependency references (369 blueprint nodes and 2416
Lean declarations); the existing unattached-helper coverage warning remains
intentional. The assigned strict-reduction task is complete. The downstream
tensor-semistability and main-theorem conclusions remain with their owners.

No shared producer, toolchain or dependency was changed; no external source
code was copied. Existing arithmetic and mathlib declarations were reused.
