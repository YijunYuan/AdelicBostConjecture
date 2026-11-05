module

public import BostConjecture.Arithmetic.SubmoduleMetric
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Integral parts of generic subspaces

The integral part of a subspace of `K ⊗[𝓞 K] M` is its actual inverse image
in `M`. Localization identifies its generic fiber with the original subspace.
Its quotient in `M` is torsion-free and therefore finite projective.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- The actual intersection of an integral module with a generic subspace. -/
def integralPart (X : Submodule K (K ⊗[𝓞 K] M)) : Submodule (𝓞 K) M :=
  (X.restrictScalars (𝓞 K)).comap (TensorProduct.mk (𝓞 K) K M 1)

omit [NumberField K] in
@[simp]
lemma mem_integralPart (X : Submodule K (K ⊗[𝓞 K] M)) (x : M) :
    x ∈ integralPart X ↔ (1 : K) ⊗ₜ[𝓞 K] x ∈ X := Iff.rfl

/-- Mathlib's submodule base change is its localization in the generic fiber. -/
lemma baseChange_eq_localized (P : Submodule (𝓞 K) M) :
    P.baseChange K = P.localized' K (nonZeroDivisors (𝓞 K))
      (TensorProduct.mk (𝓞 K) K M 1) := by
  rw [Submodule.baseChange_eq_span, Submodule.localized'_eq_span]
  rfl

@[simp]
lemma baseChange_integralPart (X : Submodule K (K ⊗[𝓞 K] M)) :
    (integralPart X).baseChange K = X := by
  rw [baseChange_eq_localized]
  exact (Submodule.localized'gi K (nonZeroDivisors (𝓞 K))
    (TensorProduct.mk (𝓞 K) K M 1)).l_u_eq X

/-- Localization gives the canonical generic-fiber identification. -/
def integralPartGenericEquiv (X : Submodule K (K ⊗[𝓞 K] M)) :
    K ⊗[𝓞 K] integralPart X ≃ₗ[K] X := by
  let : Module.Flat (𝓞 K) K := IsLocalization.flat K (nonZeroDivisors (𝓞 K))
  exact (Submodule.toBaseChange.toLinearEquiv K (integralPart X)).trans
    (LinearEquiv.ofEq _ _ (baseChange_integralPart X))

lemma integralPart_generic_finrank (X : Submodule K (K ⊗[𝓞 K] M)) :
    Module.finrank K (K ⊗[𝓞 K] integralPart X) = Module.finrank K X :=
  (integralPartGenericEquiv X).finrank_eq

omit [NumberField K] in
lemma integralPart_mono {X Y : Submodule K (K ⊗[𝓞 K] M)} (h : X ≤ Y) :
    integralPart X ≤ integralPart Y := fun _ hx => h hx

omit [NumberField K] in
@[simp]
lemma integralPart_inf (X Y : Submodule K (K ⊗[𝓞 K] M)) :
    integralPart (X ⊓ Y) = integralPart X ⊓ integralPart Y := rfl

omit [NumberField K] in
@[simp]
lemma integralPart_top : integralPart (⊤ : Submodule K (K ⊗[𝓞 K] M)) = ⊤ := rfl

omit [NumberField K] in
@[simp]
lemma integralPart_bot [Module.Projective (𝓞 K) M] :
    integralPart (⊥ : Submodule K (K ⊗[𝓞 K] M)) = ⊥ := by
  ext x
  change (1 : K) ⊗ₜ[𝓞 K] x = 0 ↔ x = 0
  exact (Module.Flat.tensorProduct_mk_injective (𝓞 K) M K).eq_iff' (map_zero _)

omit [NumberField K] in
/-- Integral parts are saturated: a nonzero integral multiple cannot enter
the submodule unless the original section already belongs to it. -/
lemma mem_integralPart_of_smul_mem (X : Submodule K (K ⊗[𝓞 K] M))
    {a : 𝓞 K} (ha : a ≠ 0) {x : M} (hx : a • x ∈ integralPart X) :
    x ∈ integralPart X := by
  change (1 : K) ⊗ₜ[𝓞 K] x ∈ X
  have hx' : (a : K) • ((1 : K) ⊗ₜ[𝓞 K] x) ∈ X := by
    rw [mem_integralPart, TensorProduct.tmul_smul, ← algebraMap_smul K] at hx
    exact hx
  have ha' : (a : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ha
  simpa only [smul_smul, inv_mul_cancel₀ ha', one_smul] using X.smul_mem (a : K)⁻¹ hx'

instance integralPartQuotientTorsionFree (X : Submodule K (K ⊗[𝓞 K] M)) :
    Module.IsTorsionFree (𝓞 K) (M ⧸ integralPart X) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro a q haq
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  obtain ⟨x, rfl⟩ := (integralPart X).mkQ_surjective q
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply mem_integralPart_of_smul_mem X ha
  exact (Submodule.Quotient.mk_eq_zero _).mp (by simpa using haq)

/-- Saturated quotients are finite projective over the ring of integers. -/
instance integralPartQuotientProjective [Module.Finite (𝓞 K) M]
    (X : Submodule K (K ⊗[𝓞 K] M)) : Module.Projective (𝓞 K) (M ⧸ integralPart X) := by
  let : Module.FinitePresentation (𝓞 K) (M ⧸ integralPart X) :=
    Module.finitePresentation_of_finite (𝓞 K) _
  exact Module.Flat.projective_of_finitePresentation

end BostConjecture.Arithmetic
