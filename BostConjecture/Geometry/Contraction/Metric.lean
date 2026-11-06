/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Determinant.Metric
public import BostConjecture.Tensor.Dual.RegroupMetric

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

/-- Tensor-power evaluation is bounded by the source and dual tensor forms. -/
private theorem tensorPowerPairing_le {V W : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    {n : ℕ} (i : V →ₗᵢ[ℂ] W) (z : ⨂[ℂ] (_ : Fin n), V)
    (u : ⨂[ℂ] (_ : Fin n), Dual ℂ W) :
    ‖Tensor.tensorPowerPairing i.toLinearMap z u‖ ≤
      Real.sqrt (((Tensor.hilbertCore (fun _ : Fin n => V)).inner z z).re) *
        Real.sqrt (((Tensor.tensorCore (fun _ : Fin n => Tensor.dualCore W)).inner u u).re) := by
  have h := Tensor.tensorDual_evaluation_le (fun _ : Fin n => W) u
    (PiTensorProduct.map (fun _ : Fin n => i.toLinearMap) z)
  rw [Tensor.hilbertCore_map_inner (fun _ : Fin n => V) (fun _ => i)] at h
  simpa only [Tensor.tensorPowerPairing_apply, mul_comm] using h

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

omit [Fintype ι] in
/-- The tensor of the actual dual determinant maps preserves its prescribed form. -/
theorem freeDeterminantTensorMap_inner [Finite ι]
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
  have h := tensorPowerPairing_le i (freeDeterminantMap hl v bV.toBasis z)
    (Tensor.dualRegroupEquiv ℂ E (PiTensorProduct.map
      (fun j => freeDeterminantMap (hk j) (t j) (b j).toBasis) u))
  rw [Tensor.dualRegroupEquiv_inner, freeDeterminantMap_inner,
    freeDeterminantTensorMap_inner E hk t b] at h
  exact h

end BostConjecture.Geometry
