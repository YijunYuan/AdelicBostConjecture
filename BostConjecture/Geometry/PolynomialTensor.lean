module

public import BostConjecture.InvariantTheory.PolynomialAction
public import BostConjecture.Tensor.Evaluation
public import Mathlib.LinearAlgebra.Multilinear.Curry

/-! # The tensor quotient onto intrinsic homogeneous polynomials

Multiplication of linear forms supplies the actual quotient map. It commutes
with linear pullback and with the canonical finite-projective tensor evaluation.
Invariant lifting through this quotient requires a further symmetrization proof.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct InvariantTheory
open scoped TensorProduct

variable {F X Y : Type*} [Field F] [AddCommGroup X] [Module F X]
  [AddCommGroup Y] [Module F Y]

/-- Multiplication of the linear forms in an actual tensor power. -/
def polynomialTensorMap (F X : Type*) [Field F] [AddCommGroup X] [Module F X] (d : ℕ) :
    (⨂[F] (_ : Fin d), Dual F X) →ₗ[F] SymmetricAlgebra F (Dual F X) :=
  PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra F (Fin d)
    (SymmetricAlgebra F (Dual F X))).compLinearMap fun _ => SymmetricAlgebra.ι F _)

@[simp]
theorem polynomialTensorMap_tprod {d : ℕ} (ℓ : Fin d → Dual F X) :
    polynomialTensorMap F X d (tprod F ℓ) = ∏ i, SymmetricAlgebra.ι F _ (ℓ i) := by
  simp [polynomialTensorMap]

private theorem polynomialTensorMap_cons {d : ℕ} (ℓ : Dual F X)
    (u : ⨂[F] (_ : Fin d), Dual F X) :
    polynomialTensorMap F X (d + 1)
      (PiTensorProduct.lift ((tprod F (s := fun _ : Fin (d + 1) => Dual F X)).curryLeft ℓ) u) =
      SymmetricAlgebra.ι F _ ℓ * polynomialTensorMap F X d u := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r x => simp [Fin.prod_univ_succ]
  | add u v hu hv => simp only [map_add, hu, hv, mul_add]

/-- The actual image is exactly the canonical degree subspace. -/
theorem range_polynomialTensorMap (d : ℕ) :
    LinearMap.range (polynomialTensorMap F X d) = homogeneousPolynomials F X d := by
  classical
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    have hprod {n : ℕ} (ℓ : Fin n → Dual F X) :
        (∏ i, SymmetricAlgebra.ι F _ (ℓ i)) ∈ homogeneousPolynomials F X n := by
      induction n with
      | zero =>
        simp [homogeneousPolynomials]
      | succ n hn =>
        rw [Fin.prod_univ_succ]
        change _ ∈ (LinearMap.range (SymmetricAlgebra.ι F (Dual F X))) ^ (n + 1)
        rw [pow_succ']
        exact Submodule.mul_mem_mul ⟨ℓ 0, rfl⟩ (hn (fun i => ℓ i.succ))
    induction u using PiTensorProduct.induction_on with
    | smul_tprod r ℓ =>
      rw [map_smul, polynomialTensorMap_tprod]
      exact (homogeneousPolynomials F X d).smul_mem r (hprod ℓ)
    | add u v hu hv =>
      rw [map_add]
      exact (homogeneousPolynomials F X d).add_mem hu hv
  · intro p hp
    induction hp using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      refine ⟨r • tprod F (fun i : Fin 0 => Fin.elim0 i), ?_⟩
      simp [Algebra.algebraMap_eq_smul_one]
    | add p q d hp hq ihp ihq =>
      exact (LinearMap.range (polynomialTensorMap F X d)).add_mem ihp ihq
    | mem_mul m hm d p hp ih =>
      obtain ⟨ℓ, rfl⟩ := hm
      obtain ⟨u, rfl⟩ := ih
      exact ⟨_, polynomialTensorMap_cons ℓ u⟩

/-- Naturality of the tensor quotient for every linear map. -/
theorem polynomialTensorMap_map_dual {d : ℕ} (f : X →ₗ[F] Y)
    (u : ⨂[F] (_ : Fin d), Dual F Y) :
    polynomialTensorMap F X d (PiTensorProduct.map (fun _ => f.dualMap) u) =
      polynomialPullback f (polynomialTensorMap F Y d u) := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r ℓ => simp; rfl
  | add u v hu hv => simp only [map_add, hu, hv]

/-- The quotient intertwines the actual tensor dual action and the intrinsic
polynomial representation, whose action is inverse pullback. -/
theorem polynomialTensorMap_representation {G : Type*} [Group G]
    (ρ : Representation F G X) (g : G) {d : ℕ}
    (u : ⨂[F] (_ : Fin d), Dual F X) :
    polynomialTensorMap F X d (PiTensorProduct.map (fun _ => (ρ g⁻¹).dualMap) u) =
      polynomialRepresentation ρ g (polynomialTensorMap F X d u) :=
  polynomialTensorMap_map_dual (ρ g⁻¹) u

/-- Polynomial evaluation is the existing finite-projective tensor evaluation. -/
theorem polynomialEval_tensorMap [FiniteDimensional F X] {d : ℕ}
    (x : X) (u : ⨂[F] (_ : Fin d), Dual F X) :
    polynomialEval x (polynomialTensorMap F X d u) =
      dualDistribEquivOfProjective F (fun _ : Fin d => X) u
        (tprod F fun _ : Fin d => x) := by
  induction u using PiTensorProduct.induction_on with
  | smul_tprod r ℓ => simp [finprod_eq_prod_of_fintype]
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]

/-- A nonvanishing homogeneous polynomial has a tensor preimage with nonzero
canonical evaluation. No invariance of that preimage is asserted here. -/
theorem exists_tensor_evaluation_ne_zero [FiniteDimensional F X] {d : ℕ}
    {p : SymmetricAlgebra F (Dual F X)} (hp : p ∈ homogeneousPolynomials F X d)
    {x : X} (hx : polynomialEval x p ≠ 0) :
    ∃ u : ⨂[F] (_ : Fin d), Dual F X,
      polynomialTensorMap F X d u = p ∧
        dualDistribEquivOfProjective F (fun _ : Fin d => X) u
          (tprod F fun _ : Fin d => x) ≠ 0 := by
  obtain ⟨u, hu⟩ := (show p ∈ LinearMap.range (polynomialTensorMap F X d) by
    rwa [range_polynomialTensorMap])
  refine ⟨u, hu, ?_⟩
  rwa [← polynomialEval_tensorMap, hu]

end BostConjecture.Geometry
