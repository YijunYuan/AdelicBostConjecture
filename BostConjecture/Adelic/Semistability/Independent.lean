/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Semistability.Group
public import BostConjecture.Arithmetic.Representation.BaseChange
public import BostConjecture.Arithmetic.Representation.IndependentPiIrreducible
public import ArakelovGeometry.AdelicVectorBundle.Construction.Tensor.Countable
public import ArakelovGeometry.AdelicVectorBundle.HarderNarasimhan.Hermitian.Semistability
public import ArakelovGeometry.AdelicVectorBundle.Tensor.PairMap

/-!
# Independent products of absolutely irreducible isometric actions

For the second assertion of Lemma 2.6 of this paper, irreducibility is checked
over a common algebraically closed extension of the original field. The
canonical tensor base-change equivalence and faithful scalar extension descend
irreducibility to the original field. The actual orthogonal tensor norms are
preserved by the product action, using the proved tensor contraction estimate
for an element and its inverse. The group criterion then proves semistability
of the tensor bundle, and Hermitian duality proves it for its dual.

The algebraic representation constructions are the existing ones in
`BostConjecture.Arithmetic`; no number-field hypotheses are used here.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open ArakelovGeometry

namespace BostConjecture.Arithmetic

section Descent

variable {K L G E : Type*} [Field K] [Field L] [Algebra K L] [Monoid G]
  [AddCommGroup E] [Module K E] [Nontrivial E]

/-- Irreducibility after a field extension implies irreducibility over the
original field, by faithful scalar extension of invariant subspaces. -/
theorem isIrreducible_of_representationBaseChange (ρ : Representation K G E)
    [Representation.IsIrreducible (representationBaseChange L ρ)] :
    ρ.IsIrreducible := by
  let : Nontrivial (Subrepresentation ρ) :=
    ⟨⟨⊥, ⊤, fun he => bot_ne_top (congrArg Subrepresentation.toSubmodule he)⟩⟩
  constructor
  intro P
  rcases eq_bot_or_eq_top (subrepresentationBaseChange L P) with h | h
  · left
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.baseChange_injective (A := L)
    change P.toSubmodule.baseChange L = (⊥ : Submodule K E).baseChange L
    rw [Submodule.baseChange_bot]
    exact congrArg Subrepresentation.toSubmodule h
  · right
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.baseChange_injective (A := L)
    change P.toSubmodule.baseChange L = (⊤ : Submodule K E).baseChange L
    rw [Submodule.baseChange_top]
    exact congrArg Subrepresentation.toSubmodule h

end Descent

section Independent

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [Finite ι]
  {G E : ι → Type*} [∀ i, Monoid (G i)]
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]

/-- Scalar extension of an independent tensor action is intertwined with
the independent action on the scalar-extended factors by the canonical map. -/
def independentPiRepresentationBaseChangeEquiv (ρ : ∀ i, Representation K (G i) (E i)) :
    (representationBaseChange L (independentPiRepresentation ρ)).Equiv
      (independentPiRepresentation (fun i => representationBaseChange L (ρ i))) :=
  Representation.Equiv.mk (tensorBaseChangeEquiv K L E) (by
    intro g
    apply LinearMap.ext
    intro z
    exact tensorBaseChangeEquiv_map K L (fun i => ρ i (g i)) z)

variable [∀ i, FiniteDimensional K (E i)] [∀ i, Nontrivial (E i)] [IsAlgClosed L]

/-- Independent tensor products are irreducible over the original field when
each factor is irreducible over one common algebraically closed extension. -/
theorem isIrreducible_independentPi_of_representationBaseChange
    (ρ : ∀ i, Representation K (G i) (E i))
    [∀ i, Representation.IsIrreducible (representationBaseChange L (ρ i))] :
    Representation.IsIrreducible (independentPiRepresentation ρ) := by
  let : Representation.IsIrreducible
      (independentPiRepresentation (fun i => representationBaseChange L (ρ i))) :=
    isIrreducible_independentPi _
  let : Representation.IsIrreducible
      (representationBaseChange L (independentPiRepresentation ρ)) :=
    isIrreducible_of_equiv (independentPiRepresentationBaseChangeEquiv (L := L) ρ)
  let b := Basis.piTensorProduct (fun i => Module.Free.chooseBasis K (E i))
  let : Nontrivial (⨂[K] i, E i) := b.repr.symm.injective.nontrivial
  exact isIrreducible_of_representationBaseChange (L := L) _

end Independent

end BostConjecture.Arithmetic

namespace ArakelovGeometry

open BostConjecture.Arithmetic

variable {K : Type*} [Field K] {S : AdelicStructure K} {ι : Type*} [Fintype ι]
  {G E : ι → Type*} [∀ i, Group (G i)]
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)]
  [∀ i, FiniteDimensional K (E i)]

/-- Independent completed factor isometries preserve the actual finite
orthogonal tensor norm, including its epsilon norms at finite places. -/
theorem NormFamily.orthogonalTensor_norm_independentPiRepresentation
    (ξ : ∀ i, NormFamily S (E i))
    [hN : S.IsArchimedeanNormalized]
    [hξ : ∀ i, (ξ i).IsHermitian] (ρ : ∀ i, Representation K (G i) (E i))
    (hρ : ∀ i g ω z, (ξ i).norm ω
      ((ρ i g).baseChange (S.ϕ ω).Completion z) = (ξ i).norm ω z)
    (g : ∀ i, G i) (ω : S.Ω) (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
    (NormFamily.orthogonalTensor ξ).norm ω
      ((independentPiRepresentation ρ g).baseChange (S.ϕ ω).Completion z) =
      (NormFamily.orthogonalTensor ξ).norm ω z := by
  let τ := independentPiRepresentation ρ
  have hle (a : ∀ i, G i) (x : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, E i)) :
      (NormFamily.orthogonalTensor ξ).norm ω
          ((τ a).baseChange (S.ϕ ω).Completion x) ≤
        (NormFamily.orthogonalTensor ξ).norm ω x :=
    NormFamily.orthogonalTensor_map_norm_le_of_norm_eq ξ ξ
      (fun i => ρ i (a i)) ω (fun i => hρ i (a i) ω) x
  apply le_antisymm (hle g z)
  have hinv : (τ g⁻¹).baseChange (S.ϕ ω).Completion
      ((τ g).baseChange (S.ϕ ω).Completion z) = z :=
    (representationBaseChange (S.ϕ ω).Completion τ).inv_self_apply g z
  simpa only [hinv] using hle g⁻¹ ((τ g).baseChange (S.ϕ ω).Completion z)

namespace AdelicVectorBundle

/-- Lemma 2.6, finite-family conclusion: absolutely irreducible independent
isometric actions make the actual orthogonal tensor bundle and its dual
mean-slope semistable over the original field. -/
theorem isMeanSlopeSemistable_orthogonalTensor_and_dual_of_isIrreducible_baseChange
    [S.IsProper] (V : ∀ i, AdelicVectorBundle S (E i))
    [hS : S.HasMeasurableBase]
    [hN : S.IsArchimedeanNormalized]
    [hV : ∀ i, (V i).IsHermitian]
    (hr : ∀ i, 0 < Module.finrank K (E i))
    (ρ : ∀ i, Representation K (G i) (E i))
    (L : Type*) [Field L] [Algebra K L] [IsAlgClosed L]
    [∀ i, Representation.IsIrreducible (representationBaseChange L (ρ i))]
    (hρ : ∀ i g ω z, (V i).toNormFamily.norm ω
      ((ρ i g).baseChange (S.ϕ ω).Completion z) = (V i).toNormFamily.norm ω z) :
    (orthogonalTensorOfMeasurableBase V).IsMeanSlopeSemistable ∧
      ((orthogonalTensorOfMeasurableBase V).dualOfMeasurableBase).IsMeanSlopeSemistable := by
  let : ∀ i, Nontrivial (E i) := fun i => Module.nontrivial_of_finrank_pos (hr i)
  let b := Basis.piTensorProduct (fun i => Module.Free.chooseBasis K (E i))
  let : Nontrivial (⨂[K] i, E i) := b.repr.symm.injective.nontrivial
  let : Representation.IsIrreducible (independentPiRepresentation ρ) :=
    isIrreducible_independentPi_of_representationBaseChange (L := L) ρ
  let T := orthogonalTensorOfMeasurableBase V
  have hT : T.IsHermitian :=
    orthogonalTensorOfMeasurableBase_isHermitian V
  have hpos : 0 < Module.finrank K (⨂[K] i, E i) := Module.finrank_pos
  have hs : T.IsMeanSlopeSemistable :=
    T.isMeanSlopeSemistable_of_isIrreducible hpos
      (independentPiRepresentation ρ)
      (NormFamily.orthogonalTensor_norm_independentPiRepresentation
        (fun i => (V i).toNormFamily) ρ hρ)
  exact ⟨hs, (T.isMeanSlopeSemistable_dual_iff_of_isHermitian hpos).mpr hs⟩

end AdelicVectorBundle

end ArakelovGeometry
