/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.ExternalCode.MathlibPRs.PR40948.LinearAlgebra.ExteriorPower.BaseChange
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import BostConjecture.Arithmetic.Bundle.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# The intrinsic integral determinant line

The determinant is the actual top exterior power of the integral module.
Finite projectivity is proved by applying exterior powers to a finite-free
splitting; no integral basis of the original module is chosen. Canonical
exterior-power base change identifies its generic and archimedean fibers.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace exteriorPower

/-- Exterior powers of finite projective modules are projective, including
over rings where the exterior degree factorial is not invertible. -/
instance instProjective {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    Module.Projective R (⋀[R]^n M) := by
  obtain ⟨d, p, i, _, _, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  apply Module.Projective.of_split (map n i) (map n p)
  rw [← map_comp, hpi, map_id]

end exteriorPower

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K]
variable (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]

/-- The determinant of an integral module, using its rank over the number field. -/
abbrev DeterminantLine := ⋀[𝓞 K]^(Module.finrank K (K ⊗[𝓞 K] M)) M

/-- The canonical generic fiber of the integral determinant. -/
def determinantGenericEquiv :
    K ⊗[𝓞 K] DeterminantLine (K := K) M ≃ₗ[K]
      ⋀[K]^(Module.finrank K (K ⊗[𝓞 K] M)) (K ⊗[𝓞 K] M) :=
  exteriorPower.baseChangeEquiv (𝓞 K) M K _

lemma determinant_generic_finrank [Module.Finite (𝓞 K) M] :
    Module.finrank K (K ⊗[𝓞 K] DeterminantLine (K := K) M) = 1 := by
  rw [(determinantGenericEquiv M).finrank_eq, exteriorPower.finrank_eq, Nat.choose_self]

instance determinant_nontrivial [Module.Finite (𝓞 K) M] :
    Nontrivial (DeterminantLine (K := K) M) := by
  by_contra h
  have : Subsingleton (DeterminantLine (K := K) M) := not_nontrivial_iff_subsingleton.mp h
  have hdim := determinant_generic_finrank (K := K) M
  rw [Module.finrank_zero_of_subsingleton] at hdim
  exact Nat.zero_ne_one hdim

/-- Extension from the generic fiber has the same dimension as the complex fiber. -/
lemma complexFiber_finrank (σ : K →+* ℂ) :
    Module.finrank ℂ (ComplexFiber M σ) = Module.finrank K (K ⊗[𝓞 K] M) := by
  let : Algebra K ℂ := σ.toAlgebra
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : IsScalarTower (𝓞 K) K ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [← (AlgebraTensorModule.cancelBaseChange (𝓞 K) K ℂ ℂ M).finrank_eq,
    Module.finrank_baseChange]

/-- The canonical complex fiber of the integral determinant. -/
def determinantComplexEquiv (σ : K →+* ℂ) :
    ComplexFiber (DeterminantLine (K := K) M) σ ≃ₗ[ℂ]
      ⋀[ℂ]^(Module.finrank K (K ⊗[𝓞 K] M)) (ComplexFiber M σ) := by
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  exact exteriorPower.baseChangeEquiv (𝓞 K) M ℂ _

/-- The complex determinant equivalence takes the integral wedge to its fiber wedge. -/
lemma determinantComplexEquiv_section (σ : K →+* ℂ)
    (x : Fin (Module.finrank K (K ⊗[𝓞 K] M)) → M) :
    determinantComplexEquiv M σ
        (fiberSection (DeterminantLine (K := K) M) σ (exteriorPower.ιMulti (𝓞 K) _ x)) =
      exteriorPower.ιMulti ℂ _ (fiberSection M σ ∘ x) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  exact exteriorPower.baseChangeEquiv_apply_tmul (𝓞 K) M ℂ _ x

end BostConjecture.Arithmetic
