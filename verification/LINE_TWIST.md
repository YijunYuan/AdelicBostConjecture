# Actual Hermitian line twists

The producer is proved at `032df77`, following the integral submodule construction
`6f23c6f`. It applies over every number field to finite projective modules,
including nonprincipal rank-one modules. No integral basis, normalization,
saturation hypothesis, tensor-semistability endpoint, compactness theorem or
geometric slope theorem is assumed.

## Exports and actual submodules

Import `BostConjecture.Main.LineTwist.Semistability`.

- `HermitianMetric.IsSemistable.tensor_rankOne_right` proves semistability of
  `h.tensor g` from semistability of `h`, positive generic rank of its module,
  and generic rank one of the module of `g`.
- `HermitianMetric.IsSemistable.tensor_rankOne_left` proves semistability of
  `g.tensor h` under the same hypotheses.
- `slope_tensor_rankOne_right` and `slope_tensor_rankOne_left` give the ambient
  shift by `g.degree`.
- `slope_submodule_tensor_of_rank_one` gives the exact shift for **every**
  positive-rank integral tensor submodule, using `lineUntwist`.

`lineUntwist C` consists of the integral vectors whose tensor with every line
element belongs to `C`. Integral dual contraction and a finite projective
splitting prove `tensorRight_lineUntwist`, without assuming a correspondence.
Flatness identifies the tensor injection with its image; its generic rank is
preserved. The existing `tensorRightEquiv_inner` transports the entire induced
Hilbert form. Existing `degree_tensor`/`slope_tensor` then give the slope shift.
The other order uses the actual integral tensor symmetry and `tensor_comm_inner`.

## Kernel and axiom evidence

All commands ran through the serialized Horizon checker with explicit
`--root /home/yijunyuan/bc-workspace` and the fixed project toolchain.

| Target | Result | Finished UTC, 2026-11-06 |
| --- | --- | --- |
| `check BostConjecture.Main.LineTwist.Submodule` | exit 0; 3555 jobs | 04:28:07 |
| `check BostConjecture.Main.LineTwist.Semistability` | exit 0; 3580 jobs | 04:35:41 |
| `check --lean verification/LineTwistAxioms.lean` | exit 0; 10 probes | 04:36:45 |

All ten transitive axiom probes report exactly `propext`, `Classical.choice`,
and `Quot.sound`. No `sorryAx` or custom mathematical axiom occurs. Guarded LSP
diagnostics were clean before the kernel checks. The final module waited
120.264 seconds for the shared resource slot, then checked in 10.446 seconds;
this was queue contention, not a failed proof.

## Independent review and source alignment

The independent source/mathematical reviewer accepted the actual integral
submodule recovery, nonprincipal scope, both-order metrics and semistability.
Its two blueprint precision suggestions were applied: the auxiliary lemma
explicitly expands the rank-one assertion in Proposition 7.3, and its statement
specifies finite projective modules.

The independent `honesty-reviewer` returned **honest / satisfactory**. It checked
the substantive producer-to-slope-to-semistability route, independently verified
the left-order endpoint's foundational axioms, and found no prohibited boundary
in the 56-module project import closure. There is no new certificate structure.

Blueprint nodes `lem:line-twist-submodules` and `lem:line-twist` contain complete
mathematical proofs, exact Lean attachments, and source anchors to manuscript
pages 12–13. Both are `leanok`. The final statement formalizes the rank-one
twist used in Proposition 7.3; it does not assert general tensor semistability.

## Integration boundary

The exact checked exports were handed to STRICT in I-0127, to MAIN in I-0135,
and to TENSOR in I-0136. The required external consumer and checked shared-root
acceptance are pending; the task remains active until their evidence is recorded.

No external code was newly vendored or adapted. The proof uses the pinned
mathlib and existing attributed project APIs. Shared source and integration files
remain owned by MAIN. Scratch cleanup found no stale candidates.
