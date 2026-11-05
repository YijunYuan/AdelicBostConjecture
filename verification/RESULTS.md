# Dependency integration evidence — 2026-11-05

## Accepted Lean state

- Lean `leanprover/lean4:v4.35.0`.
- mathlib `v4.35.0` at `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- HarderNarasimhan `14b3090e1e169b77fe381102a1289f24c2b08a11` uses the same toolchain and mathlib commit.
- 12 selectively copied OpenAI modules and 5 Etingof release modules; exact provenance and local changes in the corresponding vendor records.
- `BostConjecture/Slope/Subspace.lean` proves positivity of strict-interval ranks, slope-likeness of degree differences, explicit finite slope evaluation, and convexity from degree supermodularity on actual finite-dimensional subspaces. It does not define Hermitian arithmetic degree or prove its properties.

## Kernel checks

All commands ran in `projects/BostConjecture` with the explicit workspace root.

```
horizon --root /home/yijunyuan/bc-workspace check --json
horizon --root /home/yijunyuan/bc-workspace check --lean verification/ReuseAxioms.lean --json
```

The configured build passed without warnings at **2026-11-05 13:06:11 UTC**
(9,080 jobs including cached prerequisites, 5.978 seconds). The axiom check
passed at **13:07:12 UTC** (4.478 seconds). All 13 audited declarations report
only `propext`, `Classical.choice`, and `Quot.sound`; none reports `sorryAx` or
an additional axiom. The probe file gives the exact declaration list.

Original OpenAI source was also replayed successfully on 4.35 before adaptation.
Etingof proof elaboration and local slope adapter errors encountered during
porting were repaired; the accepted state has no remaining build errors.
The Etingof worker additionally checked the division form of the hook-length
formula with the same foundational-axiom result.

## Scope and review

Claim class: **proved prerequisite producers**. Arithmetic application is still
an **unproved bridge**, and manuscript Theorem 1.1 is **not formalized**.
The main frontier remains integral rectangular Specht lattices with compatible
metrics and sublinear normalized covolume, plus intrinsic Hermitian arithmetic
objects and their slope theory. Intended consumers are manuscript §§2, 5–7.

An independent external-boundary reviewer read the Mahler proof cone and the
pinned HN contracts. It confirmed that the former proves real-lattice compact
frames, and the latter abstract HN existence/uniqueness; neither discharges the
number-field/metric bridges. A bounded mathematical route review found no
concrete defect in the inspected manuscript steps, but is not a complete
correctness certification.

No honesty-reviewer was dispatched for this bounded import batch: no new
certificate, target-shaped assumption, or main-theorem completion claim was
introduced. Future bridge/completion reviews remain required as appropriate.

Root-session Lean LSP tools were unavailable in its tool roster, so local
adapter edits used narrow serialized kernel checks. The Etingof worker had
working LSP diagnostics and used them before its final kernel checks.

Horizon 0.1.5 emits a spurious resource-slot waiting message even when its
recorded wait is about 0.002 seconds: its `flock` success return is tested
against zero. This is recorded as a tooling issue, not proof evidence.
