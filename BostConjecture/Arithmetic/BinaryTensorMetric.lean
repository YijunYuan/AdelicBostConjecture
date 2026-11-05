module

public import BostConjecture.Arithmetic.TensorMetric
public import BostConjecture.Arithmetic.SubmoduleMetric

/-!
# The binary form of the intrinsic Hilbert tensor metric

The existing finite-family metric is transported along Mathlib's canonical
sum-index equivalence. This supplies the usual binary tensor API, with no
second choice of Hermitian form.
-/

@[expose] public section

noncomputable section

open NumberField PiTensorProduct
open scoped TensorProduct

namespace BostConjecture.Arithmetic

universe u

/-- The two factors, indexed for the existing finite tensor construction. -/
abbrev binaryTensorFamily (M N : Type u) : Unit ⊕ Unit → Type u
  | .inl _ => M
  | .inr _ => N

instance {M N : Type u} [AddCommGroup M] [AddCommGroup N] (i : Unit ⊕ Unit) :
    AddCommGroup (binaryTensorFamily M N i) := by
  cases i <;> exact inferInstance

instance {R : Type*} [CommRing R] {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (i : Unit ⊕ Unit) :
    Module R (binaryTensorFamily M N i) := by
  cases i <;> exact inferInstance

variable (R : Type*) [CommRing R] (M N : Type u)
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- The binary tensor as the two-factor finite tensor product. -/
def binaryTensorEquiv :
    M ⊗[R] N ≃ₗ[R] (⨂[R] i, binaryTensorFamily M N i) :=
  (TensorProduct.congr (subsingletonEquiv (R := R) (s := fun _ : Unit => M) ()).symm
    (subsingletonEquiv (R := R) (s := fun _ : Unit => N) ()).symm).trans
      (tmulEquivDep R (binaryTensorFamily M N))

@[simp]
lemma binaryTensorEquiv_tmul (x : M) (y : N) :
    binaryTensorEquiv R M N (x ⊗ₜ[R] y) =
      tprod R (fun i => Sum.casesOn i (fun _ => x) (fun _ => y)) := by
  simp [binaryTensorEquiv, subsingletonEquiv_symm_apply', tmulEquivDep_apply]

variable {R M N}
variable {K : Type*} [Field K] [NumberField K] [Module (𝓞 K) M] [Module (𝓞 K) N]

namespace HermitianMetric

/-- Binary Hilbert tensor metric, using the established finite-family metric. -/
def tensor (h : HermitianMetric (K := K) M) (g : HermitianMetric (K := K) N) :
    HermitianMetric (K := K) (M ⊗[𝓞 K] N) :=
  (piTensor (fun i : Unit ⊕ Unit => Sum.casesOn i (fun _ => h) (fun _ => g))).pullback
    (binaryTensorEquiv (𝓞 K) M N).toLinearMap (binaryTensorEquiv (𝓞 K) M N).injective

/-- The binary tensor norm has the same pure-tensor formula. -/
@[simp]
lemma sectionNorm_tensor_tmul (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) (σ : K →+* ℂ) (x : M) (y : N) :
    (h.tensor g).sectionNorm σ (x ⊗ₜ[𝓞 K] y) = h.sectionNorm σ x * g.sectionNorm σ y := by
  simp [tensor, sectionNorm_piTensor_tprod, Fintype.prod_sum_type]

end HermitianMetric
end BostConjecture.Arithmetic
