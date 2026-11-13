/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.ExternalCode.MathlibPRs.PR40948.LinearAlgebra.ExteriorPower.BaseChange
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import BostConjecture.Geometry.Determinant.Coordinates
public import BostConjecture.Classical.Line.Hermitian

/-!
# Determinant metrics and normalized Hermitian degree

The intrinsic determinant line, its Gram metric, and the normalized degree
retain the definitions from `81cf08a874039fde5d23c0fbf3970f7d28c3beca`.
-/

@[expose] public section
noncomputable section

section DeterminantLine

open NumberField TensorProduct

namespace exteriorPower

/-- Exterior powers of finite projective modules are projective, including
over rings where the exterior degree factorial is not invertible. -/
instance instProjective {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    Module.Projective R (⋀[R]^n M) := by
  obtain ⟨d, p, i, _, _, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  apply Module.Projective.of_split (map n i) (map n p)
  rw [← map_comp, hpi, map_id]

end exteriorPower

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K]
variable (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]

/-- The determinant of an integral module, using its rank over the number field. -/
abbrev DeterminantLine := ⋀[𝓞 K]^(Module.finrank K (K ⊗[𝓞 K] M)) M

/-- The canonical generic fiber of the integral determinant. -/
def determinantGenericEquiv :
    K ⊗[𝓞 K] DeterminantLine (K := K) M ≃ₗ[K]
      ⋀[K]^(Module.finrank K (K ⊗[𝓞 K] M)) (K ⊗[𝓞 K] M) :=
  exteriorPower.baseChangeEquiv (𝓞 K) M K _

lemma determinant_generic_finrank [Module.Finite (𝓞 K) M] :
    Module.finrank K (K ⊗[𝓞 K] DeterminantLine (K := K) M) = 1 := by
  rw [(determinantGenericEquiv M).finrank_eq, exteriorPower.finrank_eq, Nat.choose_self]

instance determinant_nontrivial [Module.Finite (𝓞 K) M] :
    Nontrivial (DeterminantLine (K := K) M) := by
  by_contra h
  have : Subsingleton (DeterminantLine (K := K) M) := not_nontrivial_iff_subsingleton.mp h
  have hdim := determinant_generic_finrank (K := K) M
  rw [Module.finrank_zero_of_subsingleton] at hdim
  exact Nat.zero_ne_one hdim

/-- Extension from the generic fiber has the same dimension as the complex fiber. -/
lemma complexFiber_finrank (σ : K →+* ℂ) :
    Module.finrank ℂ (ComplexFiber M σ) = Module.finrank K (K ⊗[𝓞 K] M) := by
  let : Algebra K ℂ := σ.toAlgebra
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : IsScalarTower (𝓞 K) K ℂ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [← (AlgebraTensorModule.cancelBaseChange (𝓞 K) K ℂ ℂ M).finrank_eq,
    Module.finrank_baseChange]

/-- The canonical complex fiber of the integral determinant. -/
def determinantComplexEquiv (σ : K →+* ℂ) :
    ComplexFiber (DeterminantLine (K := K) M) σ ≃ₗ[ℂ]
      ⋀[ℂ]^(Module.finrank K (K ⊗[𝓞 K] M)) (ComplexFiber M σ) := by
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  exact exteriorPower.baseChangeEquiv (𝓞 K) M ℂ _

/-- The complex determinant equivalence takes the integral wedge to its fiber wedge. -/
lemma determinantComplexEquiv_section (σ : K →+* ℂ)
    (x : Fin (Module.finrank K (K ⊗[𝓞 K] M)) → M) :
    determinantComplexEquiv M σ
        (fiberSection (DeterminantLine (K := K) M) σ (exteriorPower.ιMulti (𝓞 K) _ x)) =
      exteriorPower.ιMulti ℂ _ (fiberSection M σ ∘ x) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  exact exteriorPower.baseChangeEquiv_apply_tmul (𝓞 K) M ℂ _ x

end BostConjecture.Arithmetic

end DeterminantLine

section DeterminantMetric

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
def determinantFiber (h : HermitianMetric K M) (σ : K →+* ℂ) :
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
lemma determinantFiber_inner_ιMulti (h : HermitianMetric K M) (σ : K →+* ℂ)
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

/-- Pairing integral wedges is the determinant of the original fiber pairings. -/
lemma determinantFiber_inner_wedge (h : HermitianMetric K M) (σ : K →+* ℂ)
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
lemma determinantFiber_conjugate (h : HermitianMetric K M)
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
def determinant (h : HermitianMetric K M) :
    HermitianMetric K (DeterminantLine (K := K) M) where
  fiber := h.determinantFiber
  conjugate := h.determinantFiber_conjugate

/-- The induced determinant norm is the square root of the Gram determinant. -/
theorem determinant_sectionNorm_wedge_sq (h : HermitianMetric K M)
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

end DeterminantMetric

section ArithmeticDegree

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Normalized arithmetic degree of the intrinsic metrized determinant line. -/
def degree (h : HermitianMetric K M) : ℝ :=
  h.determinant.lineDegree (determinant_generic_finrank M)

/-- Normalized slope; its geometric applications use positive generic rank. -/
def slope (h : HermitianMetric K M) : ℝ :=
  h.degree / (Module.finrank K (K ⊗[𝓞 K] M) : ℝ)

end BostConjecture.Arithmetic.HermitianMetric

end ArithmeticDegree
