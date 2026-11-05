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
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    change exteriorPower.map a
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M).toLinearMap
      (exteriorPower.baseChangeEquiv S (S ⊗[R] M) T a
        (1 ⊗ₜ[S] exteriorPower.baseChangeEquiv R M S a (1 ⊗ₜ[R] ιMulti R a v))) =
      exteriorPower.baseChangeEquiv R M T a (1 ⊗ₜ[R] ιMulti R a v)
    rw [exteriorPower.baseChangeEquiv_apply_tmul, exteriorPower.baseChangeEquiv_apply_tmul,
      exteriorPower.map_apply_ιMulti, exteriorPower.baseChangeEquiv_apply_tmul]
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

/-- After cancelling successive scalar extensions, local tensor realizations agree. -/
theorem freeDeterminantMap_scalarExtension_trans (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (b : Basis (Fin a) S (S ⊗[R] M)) (c : Basis (Fin a) T (T ⊗[R] M))
    (η : ⨂[R] (_ : Fin k), ⋀[R]^a M) (x : Specht.orbitLattice t) :
    PiTensorProduct.map (fun _ : Fin n =>
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M).toLinearMap)
      (Tensor.scalarExtension S T (fun _ : Fin n => S ⊗[R] M)
        (freeDeterminantMap hk t b
          (determinantPowerScalarExtension k a η ⊗ₜ[S] (1 ⊗ₜ[ℤ] x)))) =
      freeDeterminantMap hk t c
        (determinantPowerScalarExtension k a η ⊗ₜ[T] (1 ⊗ₜ[ℤ] x)) := by
  rw [scalarExtension_freeDeterminantMap]
  simp only [TensorProduct.AlgebraTensorModule.map_tmul, Algebra.linearMap_apply,
    map_one, LinearMap.id_apply]
  rw [map_freeDeterminantMap_tmul hk t (b.baseChange T) c,
    determinantPowerScalarExtension_trans]

/-- The actual determinant chart, expressed on scalar extensions of the global
source and target. It needs only a frame after extension, not a frame over `R`. -/
def determinantChart (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (b : Basis (Fin a) S (S ⊗[R] M)) :
    S ⊗[R] ((⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] Specht.orbitLattice t)) →ₗ[S]
      S ⊗[R] (⨂[R] (_ : Fin n), M) :=
  (Tensor.baseChangeEquiv R S (fun _ : Fin n => M)).symm.toLinearMap ∘ₗ
    freeDeterminantMap hk t b ∘ₗ
      (determinantTwistBaseChangeEquiv (Specht.orbitLattice t) k a).toLinearMap

/-- Normalization of the chart on the intrinsic generators. -/
theorem determinantChart_tmul (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (b : Basis (Fin a) S (S ⊗[R] M))
    (s : S) (η : ⨂[R] (_ : Fin k), ⋀[R]^a M) (x : Specht.orbitLattice t) :
    determinantChart hk t b (s ⊗ₜ[R] (η ⊗ₜ[R] (1 ⊗ₜ[ℤ] x))) =
      s • (Tensor.baseChangeEquiv R S (fun _ : Fin n => M)).symm
        (freeDeterminantMap hk t b
          (determinantPowerScalarExtension k a η ⊗ₜ[S] (1 ⊗ₜ[ℤ] x))) := by
  simp [determinantChart]

/-- Each chart is injective over any coefficient ring flat over the integers. -/
theorem determinantChart_injective [Module.Flat ℤ S] (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (b : Basis (Fin a) S (S ⊗[R] M)) : Function.Injective (determinantChart hk t b) :=
  (Tensor.baseChangeEquiv R S (fun _ : Fin n => M)).symm.injective.comp
    ((freeDeterminantMap_injective hk t b).comp
      (determinantTwistBaseChangeEquiv (Specht.orbitLattice t) k a).injective)

private theorem tensorBaseChange_tower (z : S ⊗[R] (⨂[R] (_ : Fin n), M)) :
    Tensor.baseChangeEquiv R T (fun _ : Fin n => M)
      (TensorProduct.map (IsScalarTower.toAlgHom R S T).toLinearMap LinearMap.id z) =
    PiTensorProduct.map (fun _ : Fin n =>
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M).toLinearMap)
      (Tensor.scalarExtension S T (fun _ : Fin n => S ⊗[R] M)
        (Tensor.baseChangeEquiv R S (fun _ : Fin n => M) z)) := by
  induction z using TensorProduct.inductionOn with
  | tmul s z =>
    change algebraMap S T s • Tensor.scalarExtension R T (fun _ : Fin n => M) z =
      PiTensorProduct.map (fun _ : Fin n =>
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S T T M).toLinearMap)
        (Tensor.scalarExtension S T (fun _ : Fin n => S ⊗[R] M)
          (s • Tensor.scalarExtension R S (fun _ : Fin n => M) z))
    simp only [map_smul, LinearMap.map_smul_of_tower, Tensor.scalarExtension_trans,
      algebraMap_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Charts computed in any two successive local frames agree on the original source. -/
theorem determinantChart_trans (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (b : Basis (Fin a) S (S ⊗[R] M)) (c : Basis (Fin a) T (T ⊗[R] M))
    (p : (⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] Specht.orbitLattice t)) :
    TensorProduct.map (IsScalarTower.toAlgHom R S T).toLinearMap LinearMap.id
      (determinantChart hk t b (1 ⊗ₜ[R] p)) =
        determinantChart hk t c (1 ⊗ₜ[R] p) := by
  induction p using TensorProduct.inductionOn with
  | tmul η z =>
    induction z using TensorProduct.inductionOn with
    | tmul r x =>
      rw [show r ⊗ₜ[ℤ] x = r • (1 ⊗ₜ[ℤ] x) by simp [TensorProduct.smul_tmul']]
      simp only [TensorProduct.tmul_smul, map_smul, LinearMap.map_smul_of_tower]
      congr 1
      apply (Tensor.baseChangeEquiv R T (fun _ : Fin n => M)).injective
      rw [tensorBaseChange_tower]
      simp only [determinantChart_tmul, one_smul, LinearEquiv.apply_symm_apply]
      exact freeDeterminantMap_scalarExtension_trans hk t b c η x
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

end BostConjecture.Geometry
