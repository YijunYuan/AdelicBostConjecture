module

public import BostConjecture.Geometry.HomInvariants
public import BostConjecture.Geometry.PiInvariants
public import BostConjecture.Tensor.DualRegroup

/-! # Independent invariants in the actual dual-target tensor grouping -/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct InvariantTheory
open scoped TensorProduct

variable {F : Type} [Field F] {ι : Type*} [Finite ι]
  {E G : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module F (E i)]
  [∀ i, Group (G i)] (ρ : ∀ i, Representation F (G i) (E i))

/-- The canonical independent tensor action of a family of representations. -/
def independentTensorRepresentation : Representation F (∀ i, G i) (⨂[F] i, E i) where
  toFun g := map (fun i => ρ i (g i))
  map_one' := by simp
  map_mul' g h := by simp only [Pi.mul_apply, map_mul, PiTensorProduct.map_mul]

variable [∀ i, FiniteDimensional F (E i)] {d : ℕ}

local instance dualTensorAddCommGroup (i : ι) :
    AddCommGroup (⨂[F] (_ : Fin d), Dual F (E i)) :=
  Module.addCommMonoidToAddCommGroup F

/-- The actual fixed ambient dual tensor comes from the tensor product of the
individual contragredient fixed subspaces through canonical dual regrouping. -/
theorem exists_dual_independent_invariants
    (ℓ : ⨂[F] (_ : Fin d), Dual F (⨂[F] i, E i))
    (hℓ : ∀ g : ∀ i, G i,
      map (fun _ => (independentTensorRepresentation ρ g⁻¹).dualMap) ℓ = ℓ) :
    ∃ y : ⨂[F] i, (tensorPowerRepresentation (ρ i).dual d).invariants,
      Tensor.dualRegroupEquiv F E
        (map (fun i => Submodule.subtype
          (tensorPowerRepresentation (ρ i).dual d).invariants) y) = ℓ := by
  let : ∀ i, AddCommGroup (⨂[F] (_ : Fin d), Dual F (E i)) :=
    fun _ => Module.addCommMonoidToAddCommGroup F
  obtain ⟨z, rfl⟩ := (Tensor.dualRegroupEquiv F E).surjective ℓ
  have hz (g : ∀ i, G i) :
      map (fun i => tensorPowerRepresentation (ρ i).dual d (g i)) z = z := by
    apply (Tensor.dualRegroupEquiv_fixed_iff F E (fun i => ρ i (g i)⁻¹) z).mp
    exact hℓ g
  obtain ⟨y, hy⟩ :=
    (exists_piTensor_invariants_iff (fun i => tensorPowerRepresentation (ρ i).dual d) z).mpr hz
  exact ⟨y, congrArg (Tensor.dualRegroupEquiv F E) hy⟩

local instance tensorTargetAddCommGroup : AddCommGroup (⨂[F] i, E i) :=
  Module.addCommMonoidToAddCommGroup F

variable [CharZero F] {V : Type*} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- A nonzero invariant Hom polynomial detects a nonzero pairing on a source
invariant and individual contragredient invariant tensor factors. -/
theorem exists_independent_dual_pairing (A : V →ₗ[F] (⨂[F] i, E i))
    {p : SymmetricAlgebra F (Dual F (V →ₗ[F] (⨂[F] i, E i)))}
    (hp : p ∈ homogeneousInvariants
      (homSpecialLinearRepresentation (independentTensorRepresentation ρ)) d)
    (hpA : polynomialEval A p ≠ 0) :
    ∃ (v : ⨂[F] (_ : Fin d), V) (w : ∀ i, ⨂[F] (_ : Fin d), Dual F (E i)),
      (∀ h : SpecialLinearGroup F V, map (fun _ => (h : V →ₗ[F] V)) v = v) ∧
      (∀ i (g : G i), map (fun _ => (ρ i g⁻¹).dualMap) (w i) = w i) ∧
      Tensor.tensorPowerPairing A v (Tensor.dualRegroupEquiv F E (tprod F w)) ≠ 0 := by
  obtain ⟨v, ℓ, hv, hℓ, hvℓ⟩ :=
    exists_independent_invariant_pairing (independentTensorRepresentation ρ) A hp hpA
  obtain ⟨y, hy⟩ := exists_dual_independent_invariants ρ ℓ hℓ
  let P : (⨂[F] i, (tensorPowerRepresentation (ρ i).dual d).invariants) →ₗ[F] F :=
    (Tensor.tensorPowerPairing A v).comp ((Tensor.dualRegroupEquiv F E).toLinearMap.comp
      (map (fun i => (tensorPowerRepresentation (ρ i).dual d).invariants.subtype)))
  have hPy : P y ≠ 0 := by simpa only [P, LinearMap.comp_apply, LinearEquiv.coe_coe, hy] using hvℓ
  have hex : ∃ w, P (tprod F w) ≠ 0 := by
    by_contra! hall
    apply hPy
    clear hy hPy
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r w => rw [map_smul, hall, smul_zero]
    | add y z hy hz => rw [map_add, hy, hz, add_zero]
  obtain ⟨w, hw⟩ := hex
  refine ⟨v, (fun i => (w i).val), hv, (fun i g => (w i).property g), ?_⟩
  simpa only [P, LinearMap.comp_apply, LinearEquiv.coe_coe, map_tprod,
    Submodule.subtype_apply] using hw

end BostConjecture.Geometry
