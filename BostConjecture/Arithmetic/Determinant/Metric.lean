/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Determinant.Line
public import BostConjecture.Geometry.Determinant.Coordinates
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# The complex determinant metric

The top exterior power is metrized through an orthonormal frame. Its pairing
on two wedges is the determinant of the matrix of pairwise inner products.
This intrinsic formula removes the frame choice and proves compatibility
with conjugation on the integral determinant line.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct exteriorPower
open scoped InnerProductSpace ComplexConjugate

namespace BostConjecture.Arithmetic

namespace ComplexDeterminant

/-- A Hermitian form on a complex line is determined by the squared norm of
one coordinate unit. -/
lemma core_ext_of_unit {F : Type*} [AddCommGroup F] [Module ℂ F]
    (e : F ≃ₗ[ℂ] ℂ) (c d : InnerProductSpace.Core ℂ F)
    (he : (c.inner (e.symm 1) (e.symm 1)).re =
      (d.inner (e.symm 1) (e.symm 1)).re) : c = d := by
  have him (h : InnerProductSpace.Core ℂ F) (x : F) : (h.inner x x).im = 0 := by
    let := h
    exact InnerProductSpace.Core.inner_self_im (𝕜 := ℂ) x
  have he' : c.inner (e.symm 1) (e.symm 1) = d.inner (e.symm 1) (e.symm 1) :=
    Complex.ext he (by rw [him, him])
  have hs (h : InnerProductSpace.Core ℂ F) (a b : ℂ) :
      h.inner (e.symm a) (e.symm b) = star a * b * h.inner (e.symm 1) (e.symm 1) := by
    let := h
    have ha : e.symm a = a • e.symm 1 := by
      rw [← map_smul, smul_eq_mul, mul_one]
    have hb : e.symm b = b • e.symm 1 := by
      rw [← map_smul, smul_eq_mul, mul_one]
    rw [ha, hb, InnerProductSpace.Core.inner_smul_left,
      InnerProductSpace.Core.inner_smul_right]
    simp only [RCLike.star_def]
    ring
  have hinner : c.inner = d.inner := by
    funext x y
    obtain ⟨a, rfl⟩ := e.symm.surjective x
    obtain ⟨b, rfl⟩ := e.symm.surjective y
    rw [hs c a b, hs d a b, he']
  rcases c with ⟨⟨⟨ci⟩, cs, cp, ca, cm⟩, cd⟩
  rcases d with ⟨⟨⟨di⟩, ds, dp, da, dm⟩, dd⟩
  cases hinner
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {r : ℕ}

/-- The positive Hermitian core transported from the orthonormal top-wedge coordinate. -/
@[instance_reducible]
def core (b : OrthonormalBasis (Fin r) ℂ E) : InnerProductSpace.Core ℂ (⋀[ℂ]^r E) := by
  let e := Geometry.determinantCoordinates b.toBasis
  letI := NormedAddCommGroup.induced (⋀[ℂ]^r E) ℂ e e.injective
  letI := InnerProductSpace.induced e.toLinearMap
  exact InnerProductSpace.toCore

lemma core_inner (b : OrthonormalBasis (Fin r) ℂ E) (x y : ⋀[ℂ]^r E) :
    (core b).inner x y =
      star (Geometry.determinantCoordinates b.toBasis x) *
        Geometry.determinantCoordinates b.toBasis y := by
  change inner ℂ (Geometry.determinantCoordinates b.toBasis x)
    (Geometry.determinantCoordinates b.toBasis y) = _
  exact mul_comm _ _

/-- The cross Gram formula on the actual top exterior power, including degree zero. -/
lemma core_inner_ιMulti (b : OrthonormalBasis (Fin r) ℂ E) (x y : Fin r → E) :
    (core b).inner (ιMulti ℂ r x) (ιMulti ℂ r y) =
      (Matrix.of fun i j => inner ℂ (x i) (y j)).det := by
  rw [core_inner, Geometry.determinantCoordinates_ιMulti,
    Geometry.determinantCoordinates_ιMulti, Module.Basis.det_apply, Module.Basis.det_apply]
  have hgram : (Matrix.of fun i j => inner ℂ (x i) (y j)) =
      (b.toBasis.toMatrix x).conjTranspose * b.toBasis.toMatrix y := by
    ext i j
    simp [Matrix.mul_apply, Module.Basis.toMatrix_apply, b.repr_apply_apply,
      b.sum_inner_mul_inner]
  rw [hgram, Matrix.det_mul, Matrix.det_conjTranspose]

/-- The Gram norm formula determines the determinant metric uniquely. -/
lemma core_unique (b : OrthonormalBasis (Fin r) ℂ E)
    (c : InnerProductSpace.Core ℂ (⋀[ℂ]^r E))
    (hc : ∀ x : Fin r → E, (c.inner (ιMulti ℂ r x) (ιMulti ℂ r x)).re =
      ((Matrix.of fun i j => inner ℂ (x i) (x j)).det).re) : c = core b := by
  apply core_ext_of_unit (Geometry.determinantCoordinates b.toBasis)
  simpa only [Geometry.determinantCoordinates_symm_apply, one_smul,
    core_inner_ιMulti] using hc b.toBasis

/-- Different orthonormal frames define the same Hermitian form. -/
lemma core_eq (b c : OrthonormalBasis (Fin r) ℂ E) : core b = core c :=
  core_unique c (core b) (fun x => congrArg Complex.re (core_inner_ιMulti b x x))

end ComplexDeterminant

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M]

namespace HermitianMetric

/-- The positive complex metric on the actual determinant fiber. -/
@[instance_reducible]
def determinantFiber (h : HermitianMetric (K := K) M) (σ : K →+* ℂ) :
    InnerProductSpace.Core ℂ (ComplexFiber (DeterminantLine (K := K) M) σ) := by
  letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  letI := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let b := (stdOrthonormalBasis ℂ (ComplexFiber M σ)).reindex
    (finCongr (complexFiber_finrank M σ))
  let e := determinantComplexEquiv M σ ≪≫ₗ Geometry.determinantCoordinates b.toBasis
  letI := NormedAddCommGroup.induced _ ℂ e e.injective
  letI := InnerProductSpace.induced e.toLinearMap
  exact InnerProductSpace.toCore

/-- The determinant pairing on arbitrary complex fiber wedges is the cross
Gram determinant, transported through the canonical base-change equivalence. -/
lemma determinantFiber_inner_ιMulti (h : HermitianMetric (K := K) M) (σ : K →+* ℂ)
    (x y : Fin (Module.finrank K (K ⊗[𝓞 K] M)) → ComplexFiber M σ) :
    (h.determinantFiber σ).inner
        ((determinantComplexEquiv M σ).symm (ιMulti ℂ _ x))
        ((determinantComplexEquiv M σ).symm (ιMulti ℂ _ y)) =
      (Matrix.of fun i j => (h.fiber σ).inner (x i) (y j)).det := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let b := (stdOrthonormalBasis ℂ (ComplexFiber M σ)).reindex
    (finCongr (complexFiber_finrank M σ))
  change (ComplexDeterminant.core b).inner
    (determinantComplexEquiv M σ ((determinantComplexEquiv M σ).symm (ιMulti ℂ _ x)))
    (determinantComplexEquiv M σ ((determinantComplexEquiv M σ).symm (ιMulti ℂ _ y))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact ComplexDeterminant.core_inner_ιMulti b x y

/-- The Gram norm identity uniquely characterizes the actual complex determinant
fiber metric, including in rank zero. -/
lemma determinantFiber_unique (h : HermitianMetric (K := K) M) (σ : K →+* ℂ)
    (c : InnerProductSpace.Core ℂ (ComplexFiber (DeterminantLine (K := K) M) σ))
    (hc : ∀ x : Fin (Module.finrank K (K ⊗[𝓞 K] M)) → ComplexFiber M σ,
      (c.inner ((determinantComplexEquiv M σ).symm (ιMulti ℂ _ x))
        ((determinantComplexEquiv M σ).symm (ιMulti ℂ _ x))).re =
      ((Matrix.of fun i j => (h.fiber σ).inner (x i) (x j)).det).re) :
    c = h.determinantFiber σ := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let b := (stdOrthonormalBasis ℂ (ComplexFiber M σ)).reindex
    (finCongr (complexFiber_finrank M σ))
  apply ComplexDeterminant.core_ext_of_unit
    (determinantComplexEquiv M σ ≪≫ₗ Geometry.determinantCoordinates b.toBasis)
  simp only [LinearEquiv.symm_trans_apply,
    Geometry.determinantCoordinates_symm_apply, one_smul]
  rw [hc, h.determinantFiber_inner_ιMulti]

/-- Pairing integral wedges is the determinant of the original fiber pairings. -/
lemma determinantFiber_inner_wedge (h : HermitianMetric (K := K) M) (σ : K →+* ℂ)
    (x y : Fin (Module.finrank K (K ⊗[𝓞 K] M)) → M) :
    (h.determinantFiber σ).inner
        (fiberSection (DeterminantLine (K := K) M) σ (ιMulti (𝓞 K) _ x))
        (fiberSection (DeterminantLine (K := K) M) σ (ιMulti (𝓞 K) _ y)) =
      (Matrix.of fun i j => (h.fiber σ).inner
        (fiberSection M σ (x i)) (fiberSection M σ (y j))).det := by
  have hs (z : Fin (Module.finrank K (K ⊗[𝓞 K] M)) → M) :
      fiberSection (DeterminantLine (K := K) M) σ (ιMulti (𝓞 K) _ z) =
        (determinantComplexEquiv M σ).symm (ιMulti ℂ _ (fiberSection M σ ∘ z)) := by
    apply (determinantComplexEquiv M σ).injective
    rw [LinearEquiv.apply_symm_apply, determinantComplexEquiv_section]
  rw [hs x, hs y, h.determinantFiber_inner_ιMulti]
  rfl

/-- The determinant forms inherit conjugation compatibility on every integral
section, proved from the spanning integral wedges. -/
lemma determinantFiber_conjugate (h : HermitianMetric (K := K) M)
    (σ : K →+* ℂ) (x y : DeterminantLine (K := K) M) :
    (h.determinantFiber (ComplexEmbedding.conjugate σ)).inner
        (fiberSection _ (ComplexEmbedding.conjugate σ) x)
        (fiberSection _ (ComplexEmbedding.conjugate σ) y) =
      star ((h.determinantFiber σ).inner (fiberSection _ σ x) (fiberSection _ σ y)) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber (DeterminantLine (K := K) M) σ) :=
    h.determinantFiber σ
  let : InnerProductSpace.Core ℂ
      (ComplexFiber (DeterminantLine (K := K) M) (ComplexEmbedding.conjugate σ)) :=
    h.determinantFiber (ComplexEmbedding.conjugate σ)
  have hx : x ∈ Submodule.span (𝓞 K) (Set.range (ιMulti (𝓞 K)
      (Module.finrank K (K ⊗[𝓞 K] M)) (M := M))) := by
    rw [ιMulti_span]
    trivial
  have hy : y ∈ Submodule.span (𝓞 K) (Set.range (ιMulti (𝓞 K)
      (Module.finrank K (K ⊗[𝓞 K] M)) (M := M))) := by
    rw [ιMulti_span]
    trivial
  refine Submodule.span_induction₂ (p := fun x y _ _ =>
    (h.determinantFiber (ComplexEmbedding.conjugate σ)).inner
        (fiberSection _ (ComplexEmbedding.conjugate σ) x)
        (fiberSection _ (ComplexEmbedding.conjugate σ) y) =
      star ((h.determinantFiber σ).inner (fiberSection _ σ x) (fiberSection _ σ y)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    simp only [determinantFiber_inner_wedge, h.conjugate]
    exact ((starRingEnd ℂ).map_det _).symm
  · intro y _
    simp only [fiberSection, tmul_zero, InnerProductSpace.Core.inner_zero_left, star_zero]
  · intro x _
    simp only [fiberSection, tmul_zero, InnerProductSpace.Core.inner_zero_right, star_zero]
  · intro x y z _ _ _ hx hy
    simpa only [fiberSection, tmul_add, InnerProductSpace.Core.inner_add_left, star_add]
      using congrArg₂ (· + ·) hx hy
  · intro x y z _ _ _ hy hz
    simpa only [fiberSection, tmul_add, InnerProductSpace.Core.inner_add_right, star_add]
      using congrArg₂ (· + ·) hy hz
  · intro a x y _ _ hxy
    simp only [fiberSection_smul, InnerProductSpace.Core.inner_smul_left,
      ComplexEmbedding.conjugate_coe_eq, map_mul, hxy, RCLike.star_def]
  · intro a x y _ _ hxy
    simp only [fiberSection_smul, InnerProductSpace.Core.inner_smul_right,
      ComplexEmbedding.conjugate_coe_eq, map_mul, hxy, RCLike.star_def]

/-- The intrinsic Hermitian metric on the integral determinant line. -/
def determinant (h : HermitianMetric (K := K) M) :
    HermitianMetric (K := K) (DeterminantLine (K := K) M) where
  fiber := h.determinantFiber
  conjugate := h.determinantFiber_conjugate

/-- The induced determinant norm is the square root of the Gram determinant. -/
theorem determinant_sectionNorm_wedge_sq (h : HermitianMetric (K := K) M)
    (σ : K →+* ℂ) (x : Fin (Module.finrank K (K ⊗[𝓞 K] M)) → M) :
    (h.determinant.sectionNorm σ (ιMulti (𝓞 K) _ x)) ^ 2 =
      ((Matrix.of fun i j => (h.fiber σ).inner
        (fiberSection M σ (x i)) (fiberSection M σ (x j))).det).re := by
  change (Real.sqrt ((h.determinantFiber σ).inner _ _).re) ^ 2 = _
  have hn : 0 ≤ ((h.determinantFiber σ).inner
      (fiberSection (DeterminantLine (K := K) M) σ (ιMulti (𝓞 K) _ x))
      (fiberSection (DeterminantLine (K := K) M) σ (ιMulti (𝓞 K) _ x))).re :=
    (h.determinantFiber σ).re_inner_nonneg _
  rw [Real.sq_sqrt hn, h.determinantFiber_inner_wedge]

end HermitianMetric

end BostConjecture.Arithmetic
