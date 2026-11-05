module

public import BostConjecture.Geometry.DeterminantMetric
public import BostConjecture.Tensor.DualRegroupMetric

/-!
# The actual local determinant pairing is contracting

The estimate uses the prescribed determinant and lattice forms, the actual
dual regrouping, and an isometric inclusion into the Hilbert tensor product.
No bound or isometry certificate for the determinant maps is assumed.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct
open scoped TensorProduct

variable {ι : Type*} [Fintype ι] (E : ι → Type*)
  [∀ j, NormedAddCommGroup (E j)] [∀ j, InnerProductSpace ℂ (E j)]
  [∀ j, FiniteDimensional ℂ (E j)]

local instance : InnerProductSpace.Core ℂ (⨂[ℂ] j, E j) := Tensor.hilbertCore E

local instance : NormedAddCommGroup (⨂[ℂ] j, E j) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ⨂[ℂ] j, E j)

local instance : SeminormedAddCommGroup (⨂[ℂ] j, E j) :=
  (inferInstance : NormedAddCommGroup (⨂[ℂ] j, E j)).toSeminormedAddCommGroup

local instance : InnerProductSpace ℂ (⨂[ℂ] j, E j) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (⨂[ℂ] j, E j))

local instance (j : ι) : InnerProductSpace.Core ℂ (Dual ℂ (E j)) := Tensor.dualCore (E j)

local instance (j : ι) : NormedAddCommGroup (Dual ℂ (E j)) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := Dual ℂ (E j))

local instance (j : ι) : InnerProductSpace ℂ (Dual ℂ (E j)) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (Dual ℂ (E j)))

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {n s l : ℕ} {a k : ι → ℕ}

/-- The tensor of the actual dual determinant maps preserves its prescribed form. -/
theorem freeDeterminantTensorMap_inner
    (hk : ∀ j, 0 < k j)
    (t : ∀ j, OAI.Saxl.Tableau n (Specht.rectangle (a j) (k j)))
    (b : ∀ j, OrthonormalBasis (Fin (a j)) ℂ (Dual ℂ (E j)))
    (u v : ⨂[ℂ] j, (⨂[ℂ] (_ : Fin (k j)), ⋀[ℂ]^(a j) (Dual ℂ (E j))) ⊗[ℂ]
      (ℂ ⊗[ℤ] Specht.orbitLattice (t j))) :
    (Tensor.tensorCore (fun j => Tensor.tensorCore (fun _ : Fin n => Tensor.dualCore (E j)))).inner
      (PiTensorProduct.map (fun j => freeDeterminantMap (hk j) (t j) (b j).toBasis) u)
      (PiTensorProduct.map (fun j => freeDeterminantMap (hk j) (t j) (b j).toBasis) v) =
    (Tensor.tensorCore (fun j => Tensor.binaryCore
      (Tensor.tensorCore (fun _ : Fin (k j) => Arithmetic.ComplexDeterminant.core (b j)))
      (latticeComplexCore (t j)))).inner u v := by
  refine Tensor.tensorCore_map_inner
    (fun j => Tensor.binaryCore
      (Tensor.tensorCore (fun _ : Fin (k j) => Arithmetic.ComplexDeterminant.core (b j)))
      (latticeComplexCore (t j)))
    (fun j => Tensor.tensorCore (fun _ : Fin n => Tensor.dualCore (E j)))
    (fun j => freeDeterminantMap (hk j) (t j) (b j).toBasis) ?_ u v
  intro j x y
  change (Tensor.hilbertCore (fun _ : Fin n => Dual ℂ (E j))).inner _ _ = _
  exact freeDeterminantMap_inner (hk j) (t j) (b j) x y

/-- The concrete determinant-restricted evaluation satisfies the product norm
bound in every orthonormal complex frame. -/
theorem freeDeterminantPairing_le (i : V →ₗᵢ[ℂ] (⨂[ℂ] j, E j))
    (hl : 0 < l) (v : OAI.Saxl.Tableau n (Specht.rectangle s l))
    (bV : OrthonormalBasis (Fin s) ℂ V)
    (hk : ∀ j, 0 < k j)
    (t : ∀ j, OAI.Saxl.Tableau n (Specht.rectangle (a j) (k j)))
    (b : ∀ j, OrthonormalBasis (Fin (a j)) ℂ (Dual ℂ (E j)))
    (z : (⨂[ℂ] (_ : Fin l), ⋀[ℂ]^s V) ⊗[ℂ] (ℂ ⊗[ℤ] Specht.orbitLattice v))
    (u : ⨂[ℂ] j, (⨂[ℂ] (_ : Fin (k j)), ⋀[ℂ]^(a j) (Dual ℂ (E j))) ⊗[ℂ]
      (ℂ ⊗[ℤ] Specht.orbitLattice (t j))) :
    ‖Tensor.tensorPowerPairing i.toLinearMap (freeDeterminantMap hl v bV.toBasis z)
      (Tensor.dualRegroupEquiv ℂ E (PiTensorProduct.map
        (fun j => freeDeterminantMap (hk j) (t j) (b j).toBasis) u))‖ ≤
      Real.sqrt (((Tensor.binaryCore
        (Tensor.tensorCore (fun _ : Fin l => Arithmetic.ComplexDeterminant.core bV))
        (latticeComplexCore v)).inner z z).re) *
      Real.sqrt (((Tensor.tensorCore (fun j => Tensor.binaryCore
        (Tensor.tensorCore (fun _ : Fin (k j) => Arithmetic.ComplexDeterminant.core (b j)))
        (latticeComplexCore (t j)))).inner u u).re) := by
  let f (j : ι) := freeDeterminantMap (hk j) (t j) (b j).toBasis
  let g := freeDeterminantMap hl v bV.toBasis
  have h := Tensor.tensorDual_evaluation_le (fun _ : Fin n => ⨂[ℂ] j, E j)
    (Tensor.dualRegroupEquiv ℂ E (PiTensorProduct.map f u))
    (PiTensorProduct.map (fun _ : Fin n => i.toLinearMap) (g z))
  rw [Tensor.dualRegroupEquiv_inner,
    Tensor.hilbertCore_map_inner (fun _ : Fin n => V) (fun _ => i),
    freeDeterminantMap_inner] at h
  rw [freeDeterminantTensorMap_inner E hk t b] at h
  dsimp only [f, g] at h
  rw [Tensor.tensorPowerPairing_apply]
  -- Comparing the nested Core-derived module instances needs deeper reduction.
  set_option maxRecDepth 1024 in
    exact h.trans_eq (mul_comm _ _)

end BostConjecture.Geometry
