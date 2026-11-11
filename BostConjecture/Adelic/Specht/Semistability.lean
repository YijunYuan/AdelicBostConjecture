/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Specht.Permutation
public import BostConjecture.Adelic.Semistability.Group
public import BostConjecture.Adelic.Semistability.Specht

/-!
# Semistability of the actual constant Specht bundle

The integral position action is absolutely irreducible over every characteristic-zero
field. Its completed action preserves the word Gram metric at infinity and the integral
basis max norm elsewhere. The finite-group criterion therefore proves mean-slope
semistability for the actual adelic bundle in this paper, Lemmas 2.6 and 6.1.
-/

@[expose] public section
noncomputable section

namespace BostConjecture.Specht

open Module ArakelovGeometry
open scoped TensorProduct

variable {K : Type*} [Field K] [CharZero K] (S : AdelicStructure K) [S.IsProper]
  {n : ℕ} {μ : YoungDiagram} (t : OAI.Saxl.Tableau n μ)
  {ι : Type*} [Fintype ι] (b : Basis ι ℤ (orbitLattice t))
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hcount : S.HasCommonCountableDenseSubfield)

/-- The actual constant Specht bundle is semistable on every proper adelic curve
with the stated regularity and ordinary Archimedean norms. -/
theorem latticeBundle_isMeanSlopeSemistable :
    (latticeBundle S t b hN hcount).IsMeanSlopeSemistable (Or.inr hcount) hN := by
  let := Arithmetic.Specht.orbitLattice_baseChange_nontrivial K t
  let ρ := Arithmetic.representationBaseChange K (Arithmetic.Specht.integralRepresentation t)
  let : ρ.IsIrreducible := Arithmetic.Specht.integralRepresentation_baseChange_isIrreducible K t
  apply (latticeBundle S t b hN hcount).isMeanSlopeSemistable_of_isIrreducible
    (Or.inr hcount) hN (latticeBundle_isHermitian S t b hN hcount) Module.finrank_pos ρ
  intro g ω z
  exact latticeNormFamily_orbitAction S t b g ω z

end BostConjecture.Specht
