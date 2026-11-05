module

public import BostConjecture.Geometry.DeterminantBaseChange
public import BostConjecture.Geometry.DeterminantNaturality

/-!
# Compatibility of determinant charts in coefficient towers

The intrinsic base-change identifications commute with a second coefficient
extension. This transports the free inclusion between local frames of a
possibly nonfree original module.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct exteriorPower
open scoped TensorProduct

variable {R S T M : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [AddCommGroup M] [Module R M] {n a k : ℕ}

/-- Exterior-power scalar extension is compatible with coefficient towers. -/
theorem exteriorPowerScalarExtension_trans (η : ⋀[R]^a M) :
    exteriorPower.map a
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M).toLinearMap
      (exteriorPower.baseChangeEquiv S (S ⊗[R] M) T a
        (1 ⊗ₜ[S] exteriorPower.baseChangeEquiv R M S a (1 ⊗ₜ[R] η))) =
      exteriorPower.baseChangeEquiv R M T a (1 ⊗ₜ[R] η) := by
  let eRS : (⋀[R]^a M) →ₗ[R] (⋀[S]^a (S ⊗[R] M)) :=
    (exteriorPower.baseChangeEquiv R M S a).toLinearMap.restrictScalars R ∘ₗ
      TensorProduct.mk R S _ 1
  let eST : (⋀[S]^a (S ⊗[R] M)) →ₗ[S] (⋀[T]^a (T ⊗[S] (S ⊗[R] M))) :=
    (exteriorPower.baseChangeEquiv S (S ⊗[R] M) T a).toLinearMap.restrictScalars S ∘ₗ
      TensorProduct.mk S T _ 1
  let eRT : (⋀[R]^a M) →ₗ[R] (⋀[T]^a (T ⊗[R] M)) :=
    (exteriorPower.baseChangeEquiv R M T a).toLinearMap.restrictScalars R ∘ₗ
      TensorProduct.mk R T _ 1
  have h : (exteriorPower.map a
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M).toLinearMap
        ).restrictScalars R ∘ₗ eST.restrictScalars R ∘ₗ eRS = eRT := by
    ext v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, eRS, eST, eRT,
      exteriorPower.baseChangeEquiv_apply_tmul, exteriorPower.map_apply_ιMulti]
    congr 1
    ext i
    simp [Function.comp_def]
  exact LinearMap.congr_fun h η

/-- The tensor power of the determinant scalar extension has the same tower law. -/
theorem determinantPowerScalarExtension_trans (η : ⨂[R] (_ : Fin k), ⋀[R]^a M) :
    PiTensorProduct.map (fun _ : Fin k => exteriorPower.map a
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M).toLinearMap)
      (determinantPowerScalarExtension (R := S) (S := T) k a
        (determinantPowerScalarExtension (R := R) (S := S) k a η)) =
      determinantPowerScalarExtension (R := R) (S := T) k a η := by
  induction η using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, LinearMap.map_smul_of_tower]
    congr 1
    simp only [determinantPowerScalarExtension, LinearMap.comp_apply,
      LinearMap.restrictScalars_apply, Tensor.scalarExtension_tprod, map_tprod,
      LinearEquiv.coe_coe]
    congr 1
    funext i
    exact exteriorPowerScalarExtension_trans (S := S) (v i)
  | add x y hx hy => simp only [map_add, hx, hy]

end BostConjecture.Geometry
