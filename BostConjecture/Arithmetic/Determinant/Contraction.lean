/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Degree.Normalization
public import BostConjecture.Arithmetic.Line.Contraction
public import BostConjecture.Arithmetic.Submodule.Metric
public import BostConjecture.Arithmetic.Exterior.Map
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

/-!
# Contraction on determinant lines

The determinant norm is the absolute top-wedge coordinate in an orthonormal
frame. Gram--Schmidt and Cauchy--Schwarz bound the determinant of a contraction.
Scalar extension then transfers this inequality to intrinsic arithmetic degree.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct exteriorPower
open scoped InnerProductSpace

namespace BostConjecture.Arithmetic

namespace ComplexDeterminant

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {r : ℕ}

/-- The determinant norm is the absolute value of its orthonormal coordinate. -/
lemma norm_eq_coordinate (b : OrthonormalBasis (Fin r) ℂ E) (x : ⋀[ℂ]^r E) :
    Real.sqrt (((core b).inner x x).re) = ‖Geometry.determinantCoordinates b.toBasis x‖ := by
  rw [core_inner]
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  exact (Complex.norm_def _).symm

/-- Hadamard's bound in an orthonormal frame, with unit-length column bounds. -/
lemma norm_det_le_one (b : OrthonormalBasis (Fin r) ℂ F) (v : Fin r → F)
    (hv : ∀ i, ‖v i‖ ≤ 1) : ‖b.toBasis.det v‖ ≤ 1 := by
  let : FiniteDimensional ℂ F := b.toBasis.finiteDimensional_of_finite
  let c : OrthonormalBasis (Fin r) ℂ F := InnerProductSpace.gramSchmidtOrthonormalBasis
    (Module.finrank_eq_card_basis b.toBasis) v
  have he := core_eq b c
  have hn : ‖b.toBasis.det v‖ = ‖c.toBasis.det v‖ := by
    rw [← Geometry.determinantCoordinates_ιMulti, ← Geometry.determinantCoordinates_ιMulti,
      ← norm_eq_coordinate, ← norm_eq_coordinate, he]
  rw [hn, InnerProductSpace.gramSchmidtOrthonormalBasis_det, norm_prod]
  calc
    ∏ i, ‖inner ℂ (c i) (v i)‖ ≤ ∏ _i : Fin r, (1 : ℝ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro i _
      simpa only [c.norm_eq_one, one_mul] using (norm_inner_le_norm (c i) (v i)).trans
        (mul_le_mul_of_nonneg_left (hv i) (norm_nonneg (c i)))
    _ = 1 := by simp

/-- A linear contraction contracts the actual top exterior Hermitian norm. -/
lemma norm_map_le (b : OrthonormalBasis (Fin r) ℂ E) (c : OrthonormalBasis (Fin r) ℂ F)
    (f : E →ₗ[ℂ] F) (hf : ∀ x, ‖f x‖ ≤ ‖x‖) (x : ⋀[ℂ]^r E) :
    Real.sqrt (((core c).inner (map r f x) (map r f x)).re) ≤
      Real.sqrt (((core b).inner x x).re) := by
  obtain ⟨a, rfl⟩ := (Geometry.determinantCoordinates b.toBasis).symm.surjective x
  rw [Geometry.determinantCoordinates_symm_apply, map_smul, map_apply_ιMulti]
  rw [norm_eq_coordinate, norm_eq_coordinate]
  simp only [map_smul, Geometry.determinantCoordinates_ιMulti, Module.Basis.det_self,
    smul_eq_mul, mul_one, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg a)
    (norm_det_le_one c (f ∘ b) (fun i => (hf (b i)).trans_eq (b.norm_eq_one i)))

/-- Transport of the exterior degree preserves its intrinsic determinant norm. -/
lemma norm_degreeCongr {s : ℕ} (hrs : r = s)
    (b : OrthonormalBasis (Fin r) ℂ E) (c : OrthonormalBasis (Fin s) ℂ E)
    (x : ⋀[ℂ]^r E) :
    Real.sqrt (((core c).inner (degreeCongr hrs x) (degreeCongr hrs x)).re) =
      Real.sqrt (((core b).inner x x).re) := by
  subst s
  change Real.sqrt (((core c).inner x x).re) = _
  rw [core_eq c b]

end ComplexDeterminant

namespace HermitianMetric

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M]

/-- The intrinsic determinant fiber has the exterior norm in every orthonormal frame. -/
lemma determinantFiber_norm_eq (h : HermitianMetric K M) (σ : K →+* ℂ) :
    letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
    letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
    letI := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
    ∀ (b : OrthonormalBasis (Fin (Module.finrank K (K ⊗[𝓞 K] M))) ℂ (ComplexFiber M σ))
      (x : ComplexFiber (DeterminantLine (K := K) M) σ),
      Real.sqrt (((h.determinantFiber σ).inner x x).re) =
        Real.sqrt (((ComplexDeterminant.core b).inner (determinantComplexEquiv M σ x)
          (determinantComplexEquiv M σ x)).re) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  intro b x
  let b₀ := (stdOrthonormalBasis ℂ (ComplexFiber M σ)).reindex
    (finCongr (complexFiber_finrank M σ))
  change Real.sqrt (((ComplexDeterminant.core b₀).inner (determinantComplexEquiv M σ x)
    (determinantComplexEquiv M σ x)).re) = _
  rw [ComplexDeterminant.core_eq b₀ b]

variable {N : Type*} [AddCommGroup N] [Module (𝓞 K) N] [Module.Finite (𝓞 K) N]

/-- Fiberwise contraction descends to every vector of the complex determinant fiber. -/
theorem determinantFiber_norm_map_le (h : HermitianMetric K M)
    (g : HermitianMetric K N) (f : M →ₗ[𝓞 K] N)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = Module.finrank K (K ⊗[𝓞 K] N))
    (hc : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      Real.sqrt (((g.fiber σ).inner (fiberMap f σ x) (fiberMap f σ x)).re) ≤
        Real.sqrt (((h.fiber σ).inner x x).re))
    (σ : K →+* ℂ) (x : ComplexFiber (DeterminantLine (K := K) M) σ) :
    Real.sqrt (((g.determinantFiber σ).inner (fiberMap (determinantMap f hr) σ x)
      (fiberMap (determinantMap f hr) σ x)).re) ≤
      Real.sqrt (((h.determinantFiber σ).inner x x).re) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber N σ) := g.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber N σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  let b := (stdOrthonormalBasis ℂ (ComplexFiber M σ)).reindex
    (finCongr (complexFiber_finrank M σ))
  let c := (stdOrthonormalBasis ℂ (ComplexFiber N σ)).reindex
    (finCongr (complexFiber_finrank N σ))
  let d := c.reindex (finCongr hr.symm)
  rw [g.determinantFiber_norm_eq σ c, h.determinantFiber_norm_eq σ b,
    determinantMap_fiber, ComplexDeterminant.norm_degreeCongr hr d c]
  exact ComplexDeterminant.norm_map_le b d (fiberMap f σ) (hc σ) _

/-- Fiberwise contraction descends to contraction of every integral determinant section. -/
theorem determinant_sectionNorm_map_le (h : HermitianMetric K M)
    (g : HermitianMetric K N) (f : M →ₗ[𝓞 K] N)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = Module.finrank K (K ⊗[𝓞 K] N))
    (hc : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      Real.sqrt (((g.fiber σ).inner (fiberMap f σ x) (fiberMap f σ x)).re) ≤
        Real.sqrt (((h.fiber σ).inner x x).re))
    (σ : K →+* ℂ) (x : DeterminantLine (K := K) M) :
    g.determinant.sectionNorm σ (determinantMap f hr x) ≤ h.determinant.sectionNorm σ x := by
  have he := h.determinantFiber_norm_map_le g f hr hc σ (fiberSection _ σ x)
  rwa [fiberMap_section] at he

variable [NumberField K] [Module.Projective (𝓞 K) M] [Module.Projective (𝓞 K) N]

/-- An injective contraction of equal generic rank increases intrinsic arithmetic degree. -/
theorem degree_le_of_injective (h : HermitianMetric K M)
    (g : HermitianMetric K N) (f : M →ₗ[𝓞 K] N) (hf : Function.Injective f)
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = Module.finrank K (K ⊗[𝓞 K] N))
    (hc : ∀ (σ : K →+* ℂ) (x : ComplexFiber M σ),
      Real.sqrt (((g.fiber σ).inner (fiberMap f σ x) (fiberMap f σ x)).re) ≤
        Real.sqrt (((h.fiber σ).inner x x).re)) : h.degree ≤ g.degree :=
  h.determinant.lineDegree_le_of_injective g.determinant (determinantMap f hr)
    (determinantMap_injective f hf hr) (determinant_generic_finrank M)
    (determinant_generic_finrank N) (h.determinant_sectionNorm_map_le g f hr hc)

end HermitianMetric

end BostConjecture.Arithmetic
