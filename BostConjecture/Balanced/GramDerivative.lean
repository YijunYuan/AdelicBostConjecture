module

public import BostConjecture.Balanced.ProjectionTrace
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # First variation of the Gram determinant -/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private def determinantMultilinear : ContinuousMultilinearMap ℂ (fun _ : ι => ι → ℂ) ℂ :=
  { Matrix.detRowAlternating.toMultilinearMap with
    cont := continuous_id.matrix_det }

private theorem det_updateRow_one (i : ι) (v : ι → ℂ) :
    (Matrix.updateRow (1 : Matrix ι ι ℂ) i v).det = v i := by
  have hv : (∑ j, v j • (1 : Matrix ι ι ℂ) j) = v := by
    ext k
    simp [Matrix.one_apply]
  simpa [hv] using Matrix.det_updateRow_sum (1 : Matrix ι ι ℂ) i v

/-- At the identity, the derivative of the determinant along a real matrix curve is its trace. -/
theorem hasDerivAt_det_of_eq_one {M : ℝ → Matrix ι ι ℂ} {M' : Matrix ι ι ℂ}
    {t : ℝ} (hM : HasDerivAt M M' t) (h0 : M t = 1) :
    HasDerivAt (fun x => (M x).det) M'.trace t := by
  have hd := ((determinantMultilinear (ι := ι)).hasFDerivAt (M t)).restrictScalars ℝ
  have h := hd.comp_hasDerivAt t hM
  convert h using 1
  · rfl
  · change M'.trace = (determinantMultilinear (ι := ι)).linearDeriv (M t) M'
    erw [ContinuousMultilinearMap.linearDeriv_apply]
    rw [h0]
    change M'.trace = ∑ i, (Matrix.updateRow (1 : Matrix ι ι ℂ) i (M' i)).det
    simp [det_updateRow_one, Matrix.trace]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

/-- The actual Gram determinant has first variation twice the real projection trace. -/
theorem hasDerivAt_gramDet (S : Submodule ℂ E) (v : OrthonormalBasis ι ℂ S)
    (A : Module.End ℂ E) (f : ℝ → ι → E)
    (h0 : ∀ i, f 0 i = (v i : E))
    (hf : ∀ i, HasDerivAt (fun t => f t i) (A (v i : E)) 0) :
    HasDerivAt (fun t => (Matrix.of fun i j => inner ℂ (f t i) (f t j)).det)
      (2 * (LinearMap.trace ℂ E (S.starProjection.toLinearMap.comp A)).re : ℂ) 0 := by
  let D : Matrix ι ι ℂ := fun i j =>
    inner ℂ (v i : E) (A (v j : E)) + inner ℂ (A (v i : E)) (v j : E)
  have hd : HasDerivAt (fun t => (Matrix.of fun i j => inner ℂ (f t i) (f t j))) D 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    apply hasDerivAt_pi.mpr
    intro j
    simpa [D, h0] using (hf i).inner ℂ (hf j)
  have hid : (Matrix.of fun i j => inner ℂ (f 0 i) (f 0 j)) = 1 := by
    ext i j
    simp only [Matrix.of_apply, h0, ← Submodule.coe_inner, v.inner_eq_ite, Matrix.one_apply]
  convert hasDerivAt_det_of_eq_one hd hid using 1
  rw [trace_starProjection_comp_eq_sum S v]
  have hc := Complex.add_conj (∑ i, inner ℂ (v i : E) (A (v i : E)))
  simp only [Complex.ofReal_mul, Complex.ofReal_ofNat] at hc
  rw [← hc]
  change _ = ∑ i, (inner ℂ (v i : E) (A (v i : E)) +
    inner ℂ (A (v i : E)) (v i : E))
  simp_rw [← inner_conj_symm (A (v _ : E)) (v _ : E)]
  rw [Finset.sum_add_distrib, map_sum]

/-- The real Gram determinant variation, in the form used by squared exterior norms. -/
theorem hasDerivAt_re_gramDet (S : Submodule ℂ E) (v : OrthonormalBasis ι ℂ S)
    (A : Module.End ℂ E) (f : ℝ → ι → E)
    (h0 : ∀ i, f 0 i = (v i : E))
    (hf : ∀ i, HasDerivAt (fun t => f t i) (A (v i : E)) 0) :
    HasDerivAt (fun t => (Matrix.of fun i j => inner ℂ (f t i) (f t j)).det.re)
      (2 * (LinearMap.trace ℂ E (S.starProjection.toLinearMap.comp A)).re) 0 := by
  convert! Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_gramDet S v A f h0 hf) using 1
  simp

variable {U W : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  [FiniteDimensional ℂ U] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [FiniteDimensional ℂ W]

open scoped TensorProduct

local instance : Module ℝ (U ⊗[ℂ] W) := (NormedSpace.restrictScalars ℝ ℂ _).toModule
local instance : NormedSpace ℝ (U ⊗[ℂ] W) := NormedSpace.restrictScalars ℝ ℂ _

/-- Balance makes the Gram first variation vanish for traceless tensor generators. -/
theorem IsBalanced.hasDerivAt_re_gramDet_zero
    {S : Submodule ℂ (U ⊗[ℂ] W)} (hS : IsBalanced S) (v : OrthonormalBasis ι ℂ S)
    (H : Module.End ℂ U) (J : Module.End ℂ W)
    (hH : LinearMap.trace ℂ U H = 0) (hJ : LinearMap.trace ℂ W J = 0)
    (f : ℝ → ι → U ⊗[ℂ] W) (h0 : ∀ i, f 0 i = (v i : U ⊗[ℂ] W))
    (hf : ∀ i, HasDerivAt (fun t => f t i)
      ((TensorProduct.map H LinearMap.id + TensorProduct.map LinearMap.id J :
        Module.End ℂ (U ⊗[ℂ] W)) (v i)) 0) :
    HasDerivAt (fun t => (Matrix.of fun i j => inner ℂ (f t i) (f t j)).det.re) 0 0 := by
  have h := hasDerivAt_re_gramDet S v
    (TensorProduct.map H LinearMap.id + TensorProduct.map LinearMap.id J) f h0 hf
  rw [trace_comp_tensorSum_eq_zero S.starProjection.toLinearMap H J _ _ hS.1 hS.2 hH hJ] at h
  simpa using h

end BostConjecture.Balanced
