module

public import BostConjecture.Arithmetic.DeterminantLine
public import BostConjecture.Geometry.DeterminantFrame
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

/-- Pairing integral wedges is the determinant of the original fiber pairings. -/
lemma determinantFiber_inner_wedge (h : HermitianMetric (K := K) M) (σ : K →+* ℂ)
    (x y : Fin (Module.finrank K (K ⊗[𝓞 K] M)) → M) :
    (h.determinantFiber σ).inner
        (fiberSection (DeterminantLine (K := K) M) σ (ιMulti (𝓞 K) _ x))
        (fiberSection (DeterminantLine (K := K) M) σ (ιMulti (𝓞 K) _ y)) =
      (Matrix.of fun i j => (h.fiber σ).inner
        (fiberSection M σ (x i)) (fiberSection M σ (y j))).det := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let b := (stdOrthonormalBasis ℂ (ComplexFiber M σ)).reindex
    (finCongr (complexFiber_finrank M σ))
  change (ComplexDeterminant.core b).inner
    (determinantComplexEquiv M σ _)
    (determinantComplexEquiv M σ _) = _
  rw [determinantComplexEquiv_section, determinantComplexEquiv_section]
  exact ComplexDeterminant.core_inner_ιMulti b (fiberSection M σ ∘ x) (fiberSection M σ ∘ y)

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
