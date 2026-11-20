/-
Copyright (c) 2026 The openai/math contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The openai/math contributors
-/
/-
Adapted from openai/math, commit 4eaee87548250b2682affda7d05d947c05554bae.
Original path: lean/OAI/RepresentationTheory/Saxl/Basic.lean
Released under Apache 2.0; see BostConjecture/ExternalCode/OAI/LICENSE.
Local changes: see CONTRIBUTIONS.md in the BostConjecture project root.
This file has been modified for Lean 4.35 module visibility and removal of unused Saxl-specific
declarations.
-/
module

public import BostConjecture.ExternalCode.OAI.RepresentationTheory.Saxl.Model

/-!
# Column permutations and polytabloid coefficients

Column permutations and polytabloid coefficients.

## Source

Adapted from <https://github.com/openai/math>, revision
`4eaee87548250b2682affda7d05d947c05554bae`.
Original source:
* `lean.OAI.RepresentationTheory.Saxl.Basic`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in the project contribution records.
-/

@[expose] public section

namespace OAI

noncomputable section

open scoped TensorProduct

universe uG uV uW

namespace Saxl

/- Column permutations cannot also fix the row word unless they are identity. -/
theorem column_perm_rowWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (g : columnGroup t) (hg : rowWord t ∘ (g : Equiv.Perm (Fin n)) = rowWord t) :
    g = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  apply t.injective
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Fin.val (congrFun hg i)
  · exact g.property i

/- The coefficient of the canonical row word in its polytabloid is one. -/
theorem polytabloid_rowWord {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t (rowWord t) = 1 := by
  classical
  unfold polytabloid
  simp only [Finset.sum_apply, Pi.smul_apply, wordRep, MonoidHom.coe_mk,
    OneHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
  rw [Finset.sum_eq_single (1 : columnGroup t)]
  · simp
  · intro b hb hb1
    have hn : rowWord t ∘ (b : Equiv.Perm (Fin n)) ≠ rowWord t :=
      fun h => hb1 (column_perm_rowWord t b h)
    simp [hn]
  · simp

end Saxl

end

end OAI
