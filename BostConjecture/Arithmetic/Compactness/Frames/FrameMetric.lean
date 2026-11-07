/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Compactness.Frames.ComplexTraceCoordinates

/-!
# Positive Hermitian forms from invertible real trace frames

Complexifying an invertible real frame gives an honest positive-definite
Hermitian form on the product of actual fibers. Restricting it to a fiber
preserves positive definiteness; conjugation compatibility will follow from
the closed equations along the converging sequence of actual metrics.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct Matrix


namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Invertible complex coordinates supplied by the real trace frame. -/
def complexFrameEquiv (h : HermitianMetric K M) (b : Module.Basis ι ℤ M)
    (B : GeneralLinearGroup ι ℝ) :
    ((σ : K →+* ℂ) → ComplexFiber M σ) ≃ₗ[ℂ] EuclideanSpace ℂ ι :=
  ((h.complexTraceBasis b).equivFun.trans
    (GeneralLinearGroup.toLin (GeneralLinearGroup.map (algebraMap ℝ ℂ) B)).toLinearEquiv).trans
      (EuclideanSpace.basisFun ι ℂ).toBasis.equivFun.symm

lemma complexFrameEquiv_apply (h : HermitianMetric K M)
    (b : Module.Basis ι ℤ M) (B : GeneralLinearGroup ι ℝ)
    (x : (σ : K →+* ℂ) → ComplexFiber M σ) (i : ι) :
    h.complexFrameEquiv b B x i =
      ∑ j, (B.val i j : ℂ) * (h.complexTraceBasis b).repr x j := by
  simp only [complexFrameEquiv, LinearEquiv.trans_apply, Module.Basis.equivFun_apply]
  rfl

/-- An invertible real frame induces a positive-definite product form. -/
@[instance_reducible]
def frameProductCore (h : HermitianMetric K M) (b : Module.Basis ι ℤ M)
    (B : GeneralLinearGroup ι ℝ) :
    InnerProductSpace.Core ℂ ((σ : K →+* ℂ) → ComplexFiber M σ) where
  inner x y := inner ℂ (h.complexFrameEquiv b B x) (h.complexFrameEquiv b B y)
  conj_inner_symm x y := inner_conj_symm _ _
  re_inner_nonneg x := inner_self_nonneg
  add_left x y z := by rw [map_add, inner_add_left]
  smul_left x y c := by rw [map_smul, inner_smul_left]
  definite x hx := by
    apply (h.complexFrameEquiv b B).injective
    rw [map_zero]
    exact inner_self_eq_zero.mp hx

/-- The Gram entries are the usual real column inner products. -/
lemma frameProductCore_basis (h : HermitianMetric K M)
    (b : Module.Basis ι ℤ M) (B : GeneralLinearGroup ι ℝ) (i j : ι) :
    (h.frameProductCore b B).inner (h.complexTraceBasis b i) (h.complexTraceBasis b j) =
      (∑ k, B.val k i * B.val k j : ℝ) := by
  change inner ℂ (h.complexFrameEquiv b B (h.complexTraceBasis b i))
    (h.complexFrameEquiv b B (h.complexTraceBasis b j)) = _
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, complexFrameEquiv_apply, Finsupp.single_apply, mul_comm]

open Classical in
/-- Restriction of the product form to one actual fiber is positive definite. -/
@[instance_reducible]
def frameFiberCore (h : HermitianMetric K M) (b : Module.Basis ι ℤ M)
    (B : GeneralLinearGroup ι ℝ) (σ : K →+* ℂ) :
    InnerProductSpace.Core ℂ (ComplexFiber M σ) where
  inner x y := (h.frameProductCore b B).inner (Pi.single σ x) (Pi.single σ y)
  conj_inner_symm x y := (h.frameProductCore b B).conj_inner_symm _ _
  re_inner_nonneg x := (h.frameProductCore b B).re_inner_nonneg _
  add_left x y z := by rw [Pi.single_add, (h.frameProductCore b B).add_left]
  smul_left x y c := by rw [Pi.single_smul, (h.frameProductCore b B).smul_left]
  definite x hx := by
    have hz := (h.frameProductCore b B).definite (Pi.single σ x) hx
    simpa using congrFun hz σ

/-- An actual orthonormal coordinate frame gives the asserted trace Gram matrix. -/
lemma trace_inner_eq_sum_frame (h : HermitianMetric K M)
    (b : Module.Basis ι ℤ M) (b₀ : OrthonormalBasis ι ℝ h.TraceSpace)
    (B : GeneralLinearGroup ι ℝ) (hB : B.val = b₀.toBasis.toMatrix (h.traceBasis b))
    (i j : ι) :
    inner ℝ (h.traceSection (b i)) (h.traceSection (b j)) =
      ∑ k, B.val k i * B.val k j := by
  have hb (i k : ι) : b₀.repr (h.traceSection (b i)) k = B.val k i := by
    rw [hB, Module.Basis.toMatrix_apply, traceBasis_apply, b₀.coe_toBasis_repr_apply]
  rw [← b₀.repr.inner_map_map, EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, star_trivial, hb]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

end BostConjecture.Arithmetic.HermitianMetric
