/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Specht.DeterminantBundle
public import BostConjecture.Arithmetic.Tensor.Compatibility
public import BostConjecture.Tensor.Metric.Map

/-!
# The canonical determinant–Specht metric as an arithmetic tensor metric

The determinant–Specht bundle metric agrees with the arithmetic Hilbert
tensor metric. This comparison allows the tensor degree formulas to apply
to the auxiliary bundles used in Section 6 of this paper.
-/

@[expose] public section

noncomputable section

open Module NumberField TensorProduct

namespace BostConjecture.Arithmetic.Specht

open scoped HermitianMetric

open BostConjecture.Specht

private lemma binaryCore_map_inner {A B C D : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    (a : InnerProductSpace.Core ℂ A) (b : InnerProductSpace.Core ℂ B)
    (c : InnerProductSpace.Core ℂ C) (d : InnerProductSpace.Core ℂ D)
    (f : A →ₗ[ℂ] C) (g : B →ₗ[ℂ] D)
    (hf : ∀ x y, c.inner (f x) (f y) = a.inner x y)
    (hg : ∀ x y, d.inner (g x) (g y) = b.inner x y)
    (x y : A ⊗[ℂ] B) :
    (Tensor.binaryCore c d).inner (TensorProduct.map f g x) (TensorProduct.map f g y) =
      (Tensor.binaryCore a b).inner x y := by
  apply Tensor.inner_ext_of_span (fun z : A × B => z.1 ⊗ₜ[ℂ] z.2)
    (by simpa only [Set.range, Prod.exists] using TensorProduct.span_tmul_eq_top ℂ A B)
    (Tensor.binaryCore c d) (Tensor.binaryCore a b)
    (TensorProduct.map f g) LinearMap.id _ x y
  intro z w
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, Tensor.binaryCore_inner_tmul, hf, hg]

universe u

variable {K M : Type u} [Field K] [NumberField K] [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] {n k : ℕ}

local instance (t : OAI.Saxl.Tableau n
    (rectangle (Module.finrank K (K ⊗[𝓞 K] M)) k)) :
    AddCommGroup ((⨂[𝓞 K] (_ : Fin k), DeterminantLine (K := K) M) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice t)) := Module.addCommMonoidToAddCommGroup (𝓞 K)

/-- The metric defined through the projective determinant inclusion is exactly
ARITH's Hilbert tensor of the intrinsic determinant powers and the actual lattice. -/
theorem determinantMetric_eq_tensor (h : HermitianMetric K M) (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (rectangle (Module.finrank K (K ⊗[𝓞 K] M)) k))
    (ha : ∀ p : PrimeSpectrum (𝓞 K),
      Module.rankAtStalk M p = Module.finrank K (K ⊗[𝓞 K] M)) :
    determinantMetric h hk t ha =
      (HermitianMetric.piTensor (fun _ : Fin k => h.determinant)) ⊗[𝓞 K]
        (latticeMetric (K := K) t) := by
  apply HermitianMetric.ext_inner
  intro σ x y
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let b := (stdOrthonormalBasis ℂ (ComplexFiber M σ)).reindex
    (finCongr (complexFiber_finrank M σ))
  have hd (u v : ComplexFiber (DeterminantLine (K := K) M) σ) :
      (ComplexDeterminant.core b).inner (determinantComplexEquiv M σ u)
        (determinantComplexEquiv M σ v) = (h.determinant.fiber σ).inner u v := rfl
  have hp (u v : ComplexFiber (⨂[𝓞 K] (_ : Fin k), DeterminantLine (K := K) M) σ) :
      (Tensor.tensorCore (fun _ : Fin k => ComplexDeterminant.core b)).inner
        (Geometry.determinantPowerBaseChangeEquiv k _ u)
        (Geometry.determinantPowerBaseChangeEquiv k _ v) =
      ((HermitianMetric.piTensor (fun _ : Fin k => h.determinant)).fiber σ).inner u v := by
    exact Tensor.tensorCore_map_inner (fun _ : Fin k => h.determinant.fiber σ)
      (fun _ : Fin k => ComplexDeterminant.core b)
      (fun _ => (determinantComplexEquiv M σ).toLinearMap) (fun _ => hd) _ _
  rw [determinantMetric_fiber_inner h hk t ha σ b]
  erw [HermitianMetric.tensor_inner]
  exact binaryCore_map_inner
    ((HermitianMetric.piTensor (fun _ : Fin k => h.determinant)).fiber σ)
    ((latticeMetric (K := K) t).fiber σ)
    (Tensor.tensorCore (fun _ : Fin k => ComplexDeterminant.core b))
    (Geometry.latticeComplexCore t)
    (Geometry.determinantPowerBaseChangeEquiv k _).toLinearMap
    (latticeFiberEquiv t σ).toLinearMap hp (fun _ _ => rfl) _ _

end BostConjecture.Arithmetic.Specht
