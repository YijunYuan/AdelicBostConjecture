/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Line.TensorCoordinate
public import BostConjecture.Arithmetic.Tensor.BinaryMetric
public import BostConjecture.Arithmetic.Degree.Normalization

/-!
# Tensor additivity of intrinsic Hermitian line degree

The finite contribution uses the actual tensor coordinate ideal; the
archimedean contribution uses the existing Hilbert tensor metric. Neither
factor needs an integral basis.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

universe u

variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]

omit [NumberField K] in
/-- The generic rank of the actual integral binary tensor product. -/
lemma tensor_generic_finrank :
    Module.finrank K (K ⊗[𝓞 K] (M ⊗[𝓞 K] N)) =
      Module.finrank K (K ⊗[𝓞 K] M) * Module.finrank K (K ⊗[𝓞 K] N) := by
  rw [(TensorProduct.AlgebraTensorModule.distribBaseChange (𝓞 K) K M N).finrank_eq,
    Module.finrank_tensorProduct]

namespace HermitianMetric

/-- Tensor coordinates multiply the actual archimedean coordinate lengths. -/
lemma coordinateLength_tensor_tmul (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) (f : M →ₗ[𝓞 K] K) (q : N →ₗ[𝓞 K] K)
    (x : M) (y : N) (v : InfinitePlace K) :
    (h.tensor g).coordinateLength (tensorCoordinate f q) (x ⊗ₜ[𝓞 K] y) v =
      h.coordinateLength f x v * g.coordinateLength q y v := by
  simp only [coordinateLength, sectionNorm_tensor_tmul, tensorCoordinate_tmul,
    map_mul, div_mul_div_comm]

variable [Module.Finite (𝓞 K) M] [Module.Finite (𝓞 K) N]
    [Module.Projective (𝓞 K) M] [Module.Projective (𝓞 K) N]
    [Nontrivial M] [Nontrivial N]

/-- Additivity of the coordinate formula uses both finite and archimedean
tensor producers. -/
theorem degreeInCoordinate_tensor (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) (f : M →ₗ[𝓞 K] K) (q : N →ₗ[𝓞 K] K)
    (hf : Function.Injective f) (hq : Function.Injective q)
    {x : M} {y : N} (hx : x ≠ 0) (hy : y ≠ 0) :
    (h.tensor g).degreeInCoordinate (tensorCoordinate f q) (x ⊗ₜ[𝓞 K] y) =
      h.degreeInCoordinate f x + g.degreeInCoordinate q y := by
  have hl : (h.tensor g).coordinateLength (tensorCoordinate f q) (x ⊗ₜ[𝓞 K] y) =
      fun v => h.coordinateLength f x v * g.coordinateLength q y v := by
    funext v
    exact coordinateLength_tensor_tmul h g f q x y v
  simp only [degreeInCoordinate, BostConjecture.Arithmetic.lineDegree, hl,
    logIdealNorm_tensorCoordinate f q hf hq,
    archLog_mul (fun v => ne_of_gt (h.coordinateLength_pos f hf hx v))
      (fun v => ne_of_gt (g.coordinateLength_pos q hq hy v))]
  ring

/-- Actual normalized determinant degree is additive on intrinsic Hermitian
lines with the Hilbert tensor metric, over any number field. -/
theorem degree_tensor_of_rank_one (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N)
    (hM : Module.finrank K (K ⊗[𝓞 K] M) = 1)
    (hN : Module.finrank K (K ⊗[𝓞 K] N) = 1) :
    (h.tensor g).degree = h.degree + g.degree := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  obtain ⟨y, hy⟩ := exists_ne (0 : N)
  let f := lineCoordinate (M := M) hM
  let q := lineCoordinate (M := N) hN
  have hf := lineCoordinate_injective (M := M) hM
  have hq := lineCoordinate_injective (M := N) hN
  have ht : x ⊗ₜ[𝓞 K] y ≠ 0 := by
    intro he
    have hz := congrArg (tensorCoordinate f q) he
    simp only [tensorCoordinate_tmul, map_zero] at hz
    exact (mul_ne_zero (fun hz => hx (hf (by simpa using hz)))
      (fun hz => hy (hq (by simpa using hz)))) hz
  let : Nontrivial (M ⊗[𝓞 K] N) := ⟨⟨_, _, ht⟩⟩
  have hr : Module.finrank K (K ⊗[𝓞 K] (M ⊗[𝓞 K] N)) = 1 := by
    rw [tensor_generic_finrank, hM, hN, mul_one]
  rw [(h.tensor g).degree_eq_lineDegree hr, h.degree_eq_lineDegree hM,
    g.degree_eq_lineDegree hN,
    (h.tensor g).lineDegree_eq_degreeInCoordinate hr (tensorCoordinate f q)
      (tensorCoordinate_injective f q hf hq) ht,
    h.lineDegree_eq_degreeInCoordinate hM f hf hx,
    g.lineDegree_eq_degreeInCoordinate hN q hq hy]
  exact degreeInCoordinate_tensor h g f q hf hq hx hy

end HermitianMetric
end BostConjecture.Arithmetic
