/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Adelic.Semistability.Independent

/-!
# Line factors in irreducible isometric actions

A trivial action on a one-dimensional factor preserves irreducibility.
The actual completed orthogonal tensor norms are invariant, so the group
criterion applies to the binary tensor type used by determinant--Specht bundles.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace AdelicBostConjecture.Arithmetic

variable {K G : Type*} {D E : Type*} [Field K] [Group G]
  [AddCommGroup D] [Module K D] [FiniteDimensional K D]
  [AddCommGroup E] [Module K E]

/-- A trivial one-dimensional factor does not change the representation. -/
def trivialLineTensorEquiv (hD : Module.finrank K D = 1) (ρ : Representation K G E) :
    ((Representation.trivial K G D).tprod ρ).Equiv ρ := by
  let e : D ≃ₗ[K] K := LinearEquiv.ofFinrankEq D K
    (hD.trans (Module.finrank_self K).symm)
  refine Representation.Equiv.mk
    ((TensorProduct.congr e (LinearEquiv.refl K E)).trans (TensorProduct.lid K E)) ?_
  intro g
  ext d x
  simp

/-- Tensoring an irreducible action with a trivial line preserves irreducibility. -/
theorem isIrreducible_trivialLineTensor (hD : Module.finrank K D = 1)
    (ρ : Representation K G E) [ρ.IsIrreducible] :
    ((Representation.trivial K G D).tprod ρ).IsIrreducible :=
  isIrreducible_of_equiv (trivialLineTensorEquiv hD ρ)

/-- The line-factor representation equivalence survives any scalar extension. -/
def trivialLineTensorBaseChangeEquiv (hD : Module.finrank K D = 1)
    (ρ : Representation K G E) (L : Type*) [Field L] [Algebra K L] :
    (representationBaseChange L ((Representation.trivial K G D).tprod ρ)).Equiv
      (representationBaseChange L ρ) := by
  let e := trivialLineTensorEquiv hD ρ
  refine Representation.Equiv.mk (e.toLinearEquiv.baseChange K L _ _) ?_
  intro g
  change (e.toLinearMap.baseChange L).comp
      ((((Representation.trivial K G D).tprod ρ) g).baseChange L) =
    ((ρ g).baseChange L).comp (e.toLinearMap.baseChange L)
  rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, e.isIntertwining' g]

/-- This paper, Lemma 6.1, absolute irreducibility after a determinant twist.

Absolute irreducibility is preserved by a trivial one-dimensional factor. -/
theorem isIrreducible_baseChange_trivialLineTensor (hD : Module.finrank K D = 1)
    (ρ : Representation K G E) (L : Type*) [Field L] [Algebra K L]
    [(representationBaseChange L ρ).IsIrreducible] :
    (representationBaseChange L ((Representation.trivial K G D).tprod ρ)).IsIrreducible :=
  isIrreducible_of_equiv (trivialLineTensorBaseChangeEquiv hD ρ L)

end AdelicBostConjecture.Arithmetic

namespace ArakelovGeometry

open AdelicBostConjecture.Arithmetic

variable {K G : Type*} {D E : Type*} [Field K] [Group G] {S : AdelicStructure K}
  [AddCommGroup D] [Module K D] [FiniteDimensional K D]
  [AddCommGroup E] [Module K E] [FiniteDimensional K E]

/-- A trivial line factor and an isometric action preserve the actual binary
orthogonal tensor norms on every completed fibre. -/
theorem NormFamily.orthogonalTensorPair_norm_trivialLineTensor
    (ξ : NormFamily S D) (η : NormFamily S E)
    [hN : S.IsArchimedeanNormalized]
    [hξ : ξ.IsHermitian] [hη : η.IsHermitian] (ρ : Representation K G E)
    (hρ : ∀ g ω z, η.norm ω ((ρ g).baseChange (S.ϕ ω).Completion z) = η.norm ω z)
    (g : G) (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (D ⊗[K] E)) :
    (ξ ⊗ʰ η).norm ω
        ((((Representation.trivial K G D).tprod ρ) g).baseChange (S.ϕ ω).Completion z) =
      (ξ ⊗ʰ η).norm ω z := by
  let τ := (Representation.trivial K G D).tprod ρ
  have hle (a : G) (x : (S.ϕ ω).Completion ⊗[K] (D ⊗[K] E)) :
      (ξ ⊗ʰ η).norm ω
          ((τ a).baseChange (S.ϕ ω).Completion x) ≤
        (ξ ⊗ʰ η).norm ω x := by
    apply NormFamily.orthogonalTensorPair_map_norm_le_of_norm_eq ξ η ξ η
          (LinearMap.id) (ρ a) ω
    · intro y
      simp
    · exact hρ a ω
  apply le_antisymm (hle g z)
  have hinv : (τ g⁻¹).baseChange (S.ϕ ω).Completion
      ((τ g).baseChange (S.ϕ ω).Completion z) = z :=
    (representationBaseChange (S.ϕ ω).Completion τ).inv_self_apply g z
  simpa only [hinv] using hle g⁻¹ ((τ g).baseChange (S.ϕ ω).Completion z)

namespace AdelicVectorBundle

/-- A Hermitian line times an irreducible isometric bundle is semistable,
on the actual binary tensor type used by the determinant--Specht pairing. -/
theorem isMeanSlopeSemistable_lineTensor_of_isIrreducible [S.IsProper]
    (L : AdelicVectorBundle S) (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hL : L.IsHermitian] [hV : V.IsHermitian]
    (hD : Module.finrank K L = 1) (hE : 0 < Module.finrank K V)
    (ρ : Representation K G V) [ρ.IsIrreducible]
    (hρ : ∀ g ω z, V.norm ω ((ρ g).baseChange (S.ϕ ω).Completion z) = V.norm ω z) :
    (L ⊗ʰ V).IsMeanSlopeSemistable := by
  let : ((Representation.trivial K G L).tprod ρ).IsIrreducible :=
    isIrreducible_trivialLineTensor hD ρ
  apply isMeanSlopeSemistable_of_isIrreducible _
    (by simpa only [Module.finrank_tensorProduct, hD, one_mul] using hE)
    ((Representation.trivial K G L).tprod ρ)
  exact NormFamily.orthogonalTensorPair_norm_trivialLineTensor
    L.toNormFamily V.toNormFamily ρ hρ

/-- The actual line tensor and its actual dual are both semistable. -/
theorem isMeanSlopeSemistable_lineTensor_and_dual_of_isIrreducible [S.IsProper]
    (L : AdelicVectorBundle S) (V : AdelicVectorBundle S)
    [hS : S.NormMeasurabilityHypotheses]
    [hN : S.IsArchimedeanNormalized]
    [hL : L.IsHermitian] [hV : V.IsHermitian]
    (hD : Module.finrank K L = 1) (hE : 0 < Module.finrank K V)
    (ρ : Representation K G V) [ρ.IsIrreducible]
    (hρ : ∀ g ω z, V.norm ω ((ρ g).baseChange (S.ϕ ω).Completion z) = V.norm ω z) :
    (L ⊗ʰ V).IsMeanSlopeSemistable ∧
      ((L ⊗ʰ V).dualOfNormMeasurability).IsMeanSlopeSemistable := by
  have hs := isMeanSlopeSemistable_lineTensor_of_isIrreducible
    L V hD hE ρ hρ
  exact ⟨hs, (isMeanSlopeSemistable_dual_iff_of_isHermitian
      (L ⊗ʰ V)
       hs.1).mpr hs⟩

end AdelicVectorBundle

end ArakelovGeometry
