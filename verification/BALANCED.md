# Balanced projections: verified boundary

Manuscript Lemma 7.2 is **not yet formalized**. The accepted code proves the
intrinsic partial-trace and Gram first-variation producers. It contains no
geometric-semistability theorem or assumed orbit criterion.

## Checked producers

| Commit | Module | Result |
| --- | --- | --- |
| `fdb954d` | `Balanced.PartialTrace` | Basis-independent contraction of tensor endomorphisms; both trace-pairing identities and scalar/traceless consequences. |
| `3361234` | `Balanced.ProjectionTrace` | Actual orthogonal-projection trace as an orthonormal frame sum; `IsBalanced` is exactly the two scalar partial-trace equations. |
| `ee2abe7` | `Balanced.GramDerivative` | Determinant derivative at the identity, complex and real Gram variation, and `IsBalanced.hasDerivAt_re_gramDet_zero`. |

The final declaration concerns differentiable frame curves whose derivative
is the tensor generator. It still needs the actual exponential-flow consumer.
The real scalar instances use the canonical restriction along ℝ → ℂ.
Zero-dimensional auxiliary cases are permitted; the open headline retains
the source requirement that the subspace is nonzero.

All checks used the serialized resource slot and explicit workspace root:

```sh
"$HORIZON_BIN" --root /home/yijunyuan/bc-workspace check BostConjecture.Balanced.PartialTrace
"$HORIZON_BIN" --root /home/yijunyuan/bc-workspace check BostConjecture.Balanced.ProjectionTrace
"$HORIZON_BIN" --root /home/yijunyuan/bc-workspace check BostConjecture.Balanced.GramDerivative
"$HORIZON_BIN" --root /home/yijunyuan/bc-workspace check --lean verification/BalancedAxioms.lean
```

Results in run `0006`, session `0002-horizon-BOST-BALANCED`: warning-free
builds of 1,897, 2,813 and 2,815 jobs; 16 transitive axiom probes passed,
each reporting only `propext`, `Classical.choice`, and `Quot.sound`.
No `sorryAx` or custom axioms occur in those export cones.
Guarded LSP diagnostics were used after edits. The new consumer initially
reported stale imports; the serialized dependency build and reopening via an
import-header change restored diagnostics. No unguarded build was used.

Root integration was handed to SPECHT in `I-0049`; it is pending in this
checkpoint and is not implied by the scoped builds.

## Remaining mathematical producers

1. The actual tensor exponential flow and its derivative; the induced norm
   on the full exterior power; spectral exponential expansion and convexity.
2. Determinant-one unitary/logarithm adapters for the already checked polar
   decomposition port (`TJHeeringa/mathlib4`, revision
   `41260205df493c627e1ac0e54812cfdeb6517fbc`, PR 45002).
3. The canonical algebraic tensor/exterior representation and homogeneous
   invariant-polynomial interface, coordinated with GEOM in `I-0047`.
4. Constructible images and comparison of complex/Zariski closures,
   special-unitary Zariski density, and finite-degree Haar averaging.
   The blueprint now supplies the mathematical arguments, but there is no
   Lean implementation of these conclusions. Its curve-density proof uses
   finite Noether normalization, finite-map dimension facts, the intersection
   dimension theorem, finite normalization and nonsingularity of complex
   normal curves, and analytic local coordinates. Each used external
   conclusion must be proved or matched to checked library declarations.
5. Exact Plücker semistability and its invariant-polynomial conclusion,
   followed by independent source/math/honesty review and root integration.

The orbit criterion is restricted to the needed pair of special linear
groups with an **algebraic linear action**. It does not apply to arbitrary
abstract linear representations. The finite-degree separation argument uses
neither finite generation of the invariant ring nor a semistability axiom.
All orbit and exponential/polar blueprint nodes remain `notready`.

## Source registration

The parent granted the bounded reference extension in `I-0048`.

- `references/maithani-reynolds`: Aryaman Maithani, arXiv:2412.18841v2
  (11 September 2025), unmodified original TeX/PDF/archive. Original labels
  `thm:reynolds-for-lie-group` and `prop:SU-SL-dense` support finite-degree
  averaging and compact-subgroup density. SHA256 values are in the manifest.
- `references/milne-algebraic-geometry`: J. S. Milne, *Algebraic Geometry*
  v6.10 (11 November 2024), original 231-page PDF. PDF page 201 equals
  printed page 201. Its vision-verified mathematical excerpt records
  Proposition 9.6, Theorem 9.7 and Aside 9.8; it is explicitly not a full-page
  transcription. The original aside states closure comparison without proof;
  the blueprint expands the missing density argument using curves.

No source code was copied from these mathematical references. Their original
copyright/license notices are retained. Reference retrieval and the visual
excerpt were performed by the proof owner because an additional writable
helper was prohibited. Read-only source/mathematical review was used.

## Epistemic checkpoint

Claim class: **proved producers**. Before: the analytic proof had no Lean
implementation. After: actual balance implies vanishing Gram first variation;
the first analytic unmet producer is the actual exponential/exterior flow.
Consumer: `lem:balanced-plucker`, still unproved. The source-backed orbit route
is mathematical blueprint only, with all formal dependencies still open.
Honesty reviewer: used; actual projection and both balance equations are
load-bearing, with no hidden semistability assumption. Its request for explicit
ambient context in the Gram-variation blueprint has been incorporated.
