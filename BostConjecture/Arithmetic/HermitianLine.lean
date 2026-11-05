module

public import BostConjecture.Arithmetic.Hermitian
public import BostConjecture.Arithmetic.FractionalIdealIndex
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Intrinsic Hermitian line degree

The degree of a finite projective rank-one integral module is computed from
its actual coordinate ideal and its given archimedean metric. Both the
integral section used to recover the metric length and the generic coordinate
are proved irrelevant. Generic rank one is a dimension statement about the
canonical scalar extension, not a chosen integral basis.

Reference: bost_specht_manuscript.pdf, §2, page 3. The quotient-cardinality
formula follows from the fractional-ideal index theorem.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct
open scoped nonZeroDivisors

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- A generic rank-one module admits an integral coordinate in the number field.
Only its generic fiber is trivialized; the integral module need not be free. -/
def lineCoordinate [Module.Finite (𝓞 K) M]
    (hrank : Module.finrank K (K ⊗[𝓞 K] M) = 1) : M →ₗ[𝓞 K] K :=
  ((LinearEquiv.ofFinrankEq (R := K) (K ⊗[𝓞 K] M) K
    (by simpa using hrank)).restrictScalars (𝓞 K)).toLinearMap ∘ₗ
      TensorProduct.mk (𝓞 K) K M 1

lemma lineCoordinate_injective [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    (hrank : Module.finrank K (K ⊗[𝓞 K] M) = 1) :
    Function.Injective (lineCoordinate (M := M) hrank) :=
  (LinearEquiv.injective _).comp (Module.Flat.tensorProduct_mk_injective (𝓞 K) M K)

namespace HermitianMetric

/-- The norm of the vector with coordinate one, recovered from an integral section. -/
def coordinateLength (h : HermitianMetric (K := K) M) (f : M →ₗ[𝓞 K] K)
    (x : M) (v : InfinitePlace K) : ℝ :=
  h.sectionNorm v.embedding x / v (f x)

omit [NumberField K] in
lemma coordinateLength_pos [Module.Projective (𝓞 K) M]
    (h : HermitianMetric (K := K) M) (f : M →ₗ[𝓞 K] K)
    (hf : Function.Injective f) {x : M} (hx : x ≠ 0) (v : InfinitePlace K) :
    0 < h.coordinateLength f x v := by
  apply div_pos (h.sectionNorm_pos v.embedding hx)
  exact InfinitePlace.pos_iff.mpr (fun heq => hx (hf (by simpa using heq)))

/-- The intrinsic fiber metric determines the same length from any nonzero
integral section, including for a nonfree rank-one module. -/
lemma coordinateLength_eq (h : HermitianMetric (K := K) M)
    (f : M →ₗ[𝓞 K] K) (hf : Function.Injective f)
    {x y : M} (hx : x ≠ 0) (hy : y ≠ 0) :
    h.coordinateLength f x = h.coordinateLength f y := by
  funext v
  have hfx : f x ≠ 0 := fun heq => hx (hf (by simpa using heq))
  have hfy : f y ≠ 0 := fun heq => hy (hf (by simpa using heq))
  obtain ⟨a, b, hb, hab⟩ := exists_smul_eq_of_injective f hf hx y
  have hbv : v (b : K) ≠ 0 :=
    ne_of_gt (InfinitePlace.pos_iff.mpr (RingOfIntegers.coe_ne_zero_iff.mpr hb))
  have hn := congrArg (h.sectionNorm v.embedding) hab
  rw [h.sectionNorm_smul, h.sectionNorm_smul,
    InfinitePlace.norm_embedding_eq, InfinitePlace.norm_embedding_eq] at hn
  have hc := congrArg (fun z => v (f z)) hab
  simp only [map_smul, Algebra.smul_def, map_mul] at hc
  apply (div_eq_div_iff (ne_of_gt (InfinitePlace.pos_iff.mpr hfx))
    (ne_of_gt (InfinitePlace.pos_iff.mpr hfy))).mpr
  apply mul_left_cancel₀ hbv
  change v (algebraMap (𝓞 K) K b) * (h.sectionNorm v.embedding x * v (f y)) =
    v (algebraMap (𝓞 K) K b) * (h.sectionNorm v.embedding y * v (f x))
  linear_combination (v (f x)) * hn - (h.sectionNorm v.embedding x) * hc

omit [NumberField K] in
/-- The fiber length under a change of coordinate. -/
lemma coordinateLength_smul (h : HermitianMetric (K := K) M)
    (f : M →ₗ[𝓞 K] K) (x : M) (a : K) (v : InfinitePlace K) :
    h.coordinateLength (a • f) x v = v a⁻¹ * h.coordinateLength f x v := by
  simp only [coordinateLength, LinearMap.smul_apply, smul_eq_mul, map_mul, map_inv₀]
  ring

variable [Module.Finite (𝓞 K) M]

/-- The degree computed from the integral module, its coordinate ideal, and its
actual Hermitian metric. -/
def degreeInCoordinate (h : HermitianMetric (K := K) M) (f : M →ₗ[𝓞 K] K) (x : M) : ℝ :=
  lineDegree (coordinateIdeal f) (h.coordinateLength f x)

lemma degreeInCoordinate_eq_section (h : HermitianMetric (K := K) M)
    (f : M →ₗ[𝓞 K] K) (hf : Function.Injective f)
    {x y : M} (hx : x ≠ 0) (hy : y ≠ 0) :
    h.degreeInCoordinate f x = h.degreeInCoordinate f y := by
  rw [degreeInCoordinate, degreeInCoordinate, h.coordinateLength_eq f hf hx hy]

/-- Independence of the generic coordinate, proved using the product formula. -/
theorem degreeInCoordinate_eq [Module.Projective (𝓞 K) M] [Nontrivial M]
    (h : HermitianMetric (K := K) M) (f g : M →ₗ[𝓞 K] K)
    (hf : Function.Injective f) (hg : Function.Injective g)
    {x y : M} (hx : x ≠ 0) (hy : y ≠ 0) :
    h.degreeInCoordinate f x = h.degreeInCoordinate g y := by
  rw [h.degreeInCoordinate_eq_section g hg hy hx]
  let c : K := g x / f x
  have hc : c ≠ 0 := div_ne_zero
    (fun heq => hx (hg (by simpa using heq)))
    (fun heq => hx (hf (by simpa using heq)))
  have hgf : g = c • f := linearMap_eq_smul_of_injective f g hf hx
  rw [hgf, degreeInCoordinate, degreeInCoordinate, coordinateIdeal_smul]
  have hlength : h.coordinateLength (c • f) x =
      fun v => v c⁻¹ * h.coordinateLength f x v := by
    funext v
    exact h.coordinateLength_smul f x c v
  rw [hlength]
  symm
  simpa only [inv_inv] using lineDegree_changeSection (coordinateIdeal f)
    (coordinateIdeal_ne_zero f hf) (h.coordinateLength f x)
    (h.coordinateLength_pos f hf hx) (inv_ne_zero hc)

omit [Module.Finite (𝓞 K) M] in
/-- Counting the two conjugate complex embeddings recovers the place weights. -/
lemma sum_log_sectionNorm (h : HermitianMetric (K := K) M) (x : M) :
    (∑ σ : K →+* ℂ, Real.log (h.sectionNorm σ x)) =
      archLog (fun v => h.sectionNorm v.embedding x) := by
  classical
  rw [archLog, ← Finset.univ.sum_fiberwise (fun σ : K →+* ℂ => InfinitePlace.mk σ)]
  apply Finset.sum_congr rfl
  intro v _
  have hc (σ : K →+* ℂ) (hσ : σ ∈ (Finset.univ.filter (fun σ => InfinitePlace.mk σ = v))) :
      Real.log (h.sectionNorm σ x) = Real.log (h.sectionNorm v.embedding x) := by
    congr 1
    apply h.sectionNorm_eq_of_place_eq
    rw [(Finset.mem_filter.mp hσ).2, InfinitePlace.mk_embedding]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]

variable [Module.Projective (𝓞 K) M] [Nontrivial M]

/-- Normalized degree of an intrinsic Hermitian line. Its generic rank is computed
on the canonical generic fiber. The defining choices are eliminated by
`lineDegree_eq_degreeInCoordinate`. -/
def lineDegree (h : HermitianMetric (K := K) M)
    (hrank : Module.finrank K (K ⊗[𝓞 K] M) = 1) : ℝ :=
  h.degreeInCoordinate (lineCoordinate hrank) (Classical.choose (exists_ne (0 : M)))

/-- Compute the intrinsic degree using any injective coordinate and any nonzero
integral section. No coordinate or integral trivialization is part of the bundle. -/
theorem lineDegree_eq_degreeInCoordinate (h : HermitianMetric (K := K) M)
    (hrank : Module.finrank K (K ⊗[𝓞 K] M) = 1)
    (f : M →ₗ[𝓞 K] K) (hf : Function.Injective f) {x : M} (hx : x ≠ 0) :
    h.lineDegree hrank = h.degreeInCoordinate f x :=
  h.degreeInCoordinate_eq _ _ (lineCoordinate_injective hrank) hf
    (Classical.choose_spec (exists_ne (0 : M))) hx

/-- The intrinsic degree has the section formula with the finite norm ratio and
the actual section norms. The equality of that ratio to the finite quotient
cardinality is not assumed here. -/
theorem lineDegree_eq_normRatio (h : HermitianMetric (K := K) M)
    (hrank : Module.finrank K (K ⊗[𝓞 K] M) = 1)
    (f : M →ₗ[𝓞 K] K) (hf : Function.Injective f) {x : M} (hx : x ≠ 0) :
    h.lineDegree hrank =
      (Real.log ((FractionalIdeal.absNorm
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (f x)) : ℝ) /
        (FractionalIdeal.absNorm (coordinateIdeal f) : ℝ)) -
        archLog (fun v => h.sectionNorm v.embedding x)) / (Module.finrank ℚ K : ℝ) := by
  rw [h.lineDegree_eq_degreeInCoordinate hrank f hf hx, degreeInCoordinate]
  have hfx : f x ≠ 0 := fun heq => hx (hf (by simpa using heq))
  rw [← lineDegree_eq_section (coordinateIdeal f) (coordinateIdeal_ne_zero f hf)
    (h.coordinateLength f x) (h.coordinateLength_pos f hf hx) hfx]
  congr 2
  apply congrArg archLog
  funext v
  dsimp only [coordinateLength]
  exact mul_div_cancel₀ _ (ne_of_gt (InfinitePlace.pos_iff.mpr hfx))

/-- The manuscript's normalized degree formula on the actual finite quotient and
actual archimedean section norms. It holds for every nonzero integral section. -/
theorem lineDegree_eq (h : HermitianMetric (K := K) M)
    (hrank : Module.finrank K (K ⊗[𝓞 K] M) = 1) {x : M} (hx : x ≠ 0) :
    h.lineDegree hrank =
      (Real.log (Nat.card (M ⧸ (𝓞 K ∙ x))) -
        archLog (fun v => h.sectionNorm v.embedding x)) / (Module.finrank ℚ K : ℝ) := by
  let f := lineCoordinate (M := M) hrank
  have hf := lineCoordinate_injective (M := M) hrank
  have hcard : (Nat.card (M ⧸ (𝓞 K ∙ x)) : ℝ) =
      (FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 K)⁰ (f x)) : ℝ) /
        (FractionalIdeal.absNorm (coordinateIdeal f) : ℝ) := by
    exact_mod_cast coordinate_quotient_card f hf hx
  rw [h.lineDegree_eq_normRatio hrank f hf hx, ← hcard]

/-- The same intrinsic formula indexed by all complex embeddings, exactly as
in the manuscript; complex conjugate embeddings are both counted. -/
theorem lineDegree_eq_sum_embeddings (h : HermitianMetric (K := K) M)
    (hrank : Module.finrank K (K ⊗[𝓞 K] M) = 1) {x : M} (hx : x ≠ 0) :
    h.lineDegree hrank =
      (Real.log (Nat.card (M ⧸ (𝓞 K ∙ x))) -
        ∑ σ : K →+* ℂ, Real.log (h.sectionNorm σ x)) / (Module.finrank ℚ K : ℝ) := by
  rw [h.lineDegree_eq hrank hx, h.sum_log_sectionNorm]

end HermitianMetric

/-- A nonzero section of an intrinsic projective line has finite quotient. -/
theorem line_quotient_finite [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Nontrivial M] (hrank : Module.finrank K (K ⊗[𝓞 K] M) = 1)
    {x : M} (hx : x ≠ 0) : Finite (M ⧸ (𝓞 K ∙ x)) :=
  coordinate_quotient_finite (lineCoordinate hrank) (lineCoordinate_injective hrank) hx

end BostConjecture.Arithmetic
