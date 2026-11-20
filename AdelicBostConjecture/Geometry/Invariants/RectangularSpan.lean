/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import AdelicBostConjecture.Geometry.Invariants.RectangularCovector
public import AdelicBostConjecture.ExternalCode.TauCeti.RepresentationTheory.SchurWeyl.SchurWeyl
public import Mathlib.Algebra.CharZero.Infinite
public import AdelicBostConjecture.Geometry.Tensor.Permutation

/-!
# Determinant-covariant tensors are in the rectangular lattice span

Schur-Weyl is applied to the actual rank-one operator formed from the rectangular
coefficient covector. The integer square normalization and the checked integral
position action identify its value with the scalar-extended orbit lattice.
-/

@[expose] public section

noncomputable section

namespace AdelicBostConjecture.Geometry

open Module PiTensorProduct
open scoped TensorProduct

variable {F M : Type*} [Field F] [CharZero F] [AddCommGroup M] [Module F M]
  [FiniteDimensional F M] {n a k : ℕ}

omit [CharZero F] [FiniteDimensional F M] in
/-- Every permutation-span operator carries the rectangular tensor into the
actual scalar-extended integral orbit lattice. -/
theorem permutation_span_apply_rectangularTensor (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) F M)
    {T : Module.End F (⨂[F] (_ : Fin n), M)}
    (hT : T ∈ Submodule.span F (Set.range (reindexRepresentation F M (Fin n)))) :
    T (rectangularTensor hk t b) ∈ LinearMap.range (freeLatticeMap hk t b) := by
  induction hT using Submodule.span_induction with
  | mem T hT =>
    obtain ⟨σ, rfl⟩ := hT
    obtain ⟨z, hz⟩ := rectangularTensor_mem_range hk t b
    refine ⟨(Specht.orbitAction t σ).baseChange F z, ?_⟩
    rw [freeLatticeMap_reindex, hz]
    rfl
  | zero => exact Submodule.zero_mem _
  | add T S hT hS ihT ihS => exact Submodule.add_mem _ ihT ihS
  | smul c T hT ihT => exact Submodule.smul_mem _ c ihT

/-- An actual determinant-covariant tensor lies in the scalar-extended
rectangular lattice. No invariant-space equality is assumed. -/
theorem mem_range_freeLatticeMap_of_determinant_covariant (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) F M)
    (v : ⨂[F] (_ : Fin n), M)
    (hv : ∀ g : (Module.End F M)ˣ,
      PiTensorProduct.map (fun _ => (g : Module.End F M)) v =
        (LinearMap.toMatrix b b (g : Module.End F M)).det ^ k • v) :
    v ∈ LinearMap.range (freeLatticeMap hk t b) := by
  let T := (rectangularCovector hk t b).smulRight v
  have hcomm (g : (Module.End F M)ˣ) :
      Commute T (PiTensorProduct.map fun _ : Fin n => (g : Module.End F M)) := by
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, T, LinearMap.smulRight_apply,
      rectangularCovector_map, map_smul, hv, smul_smul]
    rw [mul_comm]
  let : NeZero ((Fintype.card (Fin n)).factorial : F) :=
    ⟨Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)⟩
  have hT := mem_permutation_span_of_commute_units T hcomm
  have hz := permutation_span_apply_rectangularTensor hk t b hT
  change rectangularCovector hk t b (rectangularTensor hk t b) • v ∈ _ at hz
  rw [rectangularCovector_tensor] at hz
  have hc : (a.factorial : F) ^ k ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a))
  have hi := Submodule.smul_mem (LinearMap.range (freeLatticeMap hk t b))
    (((a.factorial : F) ^ k)⁻¹) hz
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hi

end AdelicBostConjecture.Geometry
