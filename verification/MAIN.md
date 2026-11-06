# Maximal-slope proof evidence

Theorem 1.1 and its finite-family corollary remain **open**. No final
maximal-slope equality is exported. This checkpoint proves five source-facing
producers over arbitrary number fields and nonfree finite projective modules.

- `LowerBound.lean` (`5913d84`): `maxSlope_add_le_tensor` tensors the actual
  first HN submodules, proves the metric identification on their integral image,
  and consumes `slope_tensor` and `slope_submodule_le_maxSlope`.
- `FilteredBound.lean` (`5913d84`): the actual semistable quotient intervals,
  exact degree/rank differences and supermodularity bound every integral
  submodule, including nonsaturated ones.
- `TensorFiltration.lean` (`66d4baa`): actual tensor image and quotient
  isomorphisms, projective quotient, and all-fiber induced/quotient isometries.
- `TensorFlag.lean` (`04dd654`): right exactness identifies the actual sum
  steps with mapped kernels; torsion freeness proves saturation. The flattened
  lexicographic HN flag is monotone, begins at zero and reaches the full tensor
  product after the product of the factor flag lengths.

## Verification

All checks used the guarded LSP loop and explicit-root serialized Horizon CLI.
The narrow LowerBound build passed 3581 jobs. TensorFiltration/FilteredBound
passed 3583 jobs, and TensorFlag passed 3583 jobs, without compiler warnings.

At source checkpoint `e3516a5`, the configured root build passed **9368 jobs**
without warnings at **2026-11-06 03:39:46 UTC**. The root blob is
`0636620c96f45373d116c7370d2bffbd67c4a4e5`.
`verification/MainAxioms.lean` passed at **03:38:50 UTC**: all **30** transitive
axiom outputs contain exactly `propext`, `Classical.choice`, and `Quot.sound`.
There is no `sorryAx` or custom mathematical axiom in these audited cones.
The final theorem itself cannot yet be axiom-audited because it is not defined.

Exact commands:

```text
horizon --root /home/yijunyuan/bc-workspace check
horizon --root /home/yijunyuan/bc-workspace check --lean verification/MainAxioms.lean
```

Logs are in run0011/session `0002-horizon-BOST-MAIN` as `main-root.log`,
`main-axioms.log`, and `main-graph.log`. An initial check invocation with
unsupported `--project` and graph invocation with unsupported `--json` were
rejected before execution and corrected. The guarded LSP reported stale
imports on the audit/root files before the serialized producer builds finished;
all final kernel checks succeeded. No broken proof remains in owned source.

The read-only `honesty-reviewer` independently inspected exact manuscript
pp. 1/13, all four files and dependencies, all 30 outputs, root/check records,
source hashes, substantive producer use and five blueprint attachments. Verdict:
honest proved producers. Its block-endpoint wording and attribution corrections
were applied. This review does not certify the unfinished main theorem.

## Integration and remaining boundary

The root imports only checked current-owner handoffs: COMPACTNESS `870179a`,
SPECHT-SLOPE tree `e84df35`, and TENSOR-SEMI `57f5cfc`/`bbafa44`. Their imported
files were compared against these trees and are unchanged. Concurrent drafts
of compactness reconstruction, geometric pairing metrics and arithmetic Gram
variation are outside this root's added imports.

Five MAIN blueprint nodes are marked checked. `lem:hn-tensor-grades` is the
next independent obligation: construct the canonical integral isomorphism from
each consecutive tensor-flag quotient to the tensor of the two HN grades,
and prove its all-fiber Hilbert isometry. Its complete mathematical proof is
in `main.tex`. The final upper bound must then consume proved unconditional
tensor semistability; no assumed producer package replaces that endpoint.
The main identity and finite-family theorem remain notready.

Graph sync resolved all source/dependency/Lean attachments. Its 1099 unattached
helper/concurrent-draft declarations are coverage warnings only. A read-only
Ground hygiene pass accepted nine active roadmap items as four authorized
lanes, three active subgoals and two ancestors. No stale scratch candidates
were found, no fifth writer was launched, and MAIN retains shared integration.
