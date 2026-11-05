module

public import BostConjecture.Arithmetic.ExteriorDualBaseChange
public import BostConjecture.Arithmetic.ComplexDualDeterminant
public import BostConjecture.Arithmetic.LineDualDegree
public import BostConjecture.Arithmetic.DeterminantContraction

/-!
# Intrinsic determinant duality

The actual integral determinant of the dual identifies with the dual
determinant. Its archimedean evaluation agrees with canonical complex
exterior evaluation.
-/

@[expose] public section

noncomputable section

open NumberField Module TensorProduct exteriorPower

namespace BostConjecture.Arithmetic

section DegreeTransport

variable (R S V : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module R V]

/-- Exterior degree transport commutes with scalar extension on every vector. -/
lemma degreeCongr_baseChange {m n : ℕ} (h : m = n) (z : S ⊗[R] (⋀[R]^m V)) :
    baseChangeEquiv R V S n ((degreeCongr (R := R) (V := V) h).toLinearMap.baseChange S z) =
      degreeCongr h (baseChangeEquiv R V S m z) := by
  subst n
  simp [degreeCongr]

end DegreeTransport

namespace ComplexDeterminant

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] {r : ℕ}

/-- Isometries preserve the top exterior norm in arbitrary orthonormal frames. -/
lemma norm_map_eq (b : OrthonormalBasis (Fin r) ℂ E) (c : OrthonormalBasis (Fin r) ℂ F)
    (e : E ≃ₗ[ℂ] F) (he : ∀ x, ‖e x‖ = ‖x‖) (x : ⋀[ℂ]^r E) :
    Real.sqrt (((core c).inner (map r e.toLinearMap x) (map r e.toLinearMap x)).re) =
      Real.sqrt (((core b).inner x x).re) := by
  apply le_antisymm (norm_map_le b c e.toLinearMap (fun y => (he y).le) x)
  have h := norm_map_le c b e.symm.toLinearMap
    (fun y => by simpa using (he (e.symm y)).symm.le) (map r e.toLinearMap x)
  simpa only [← LinearMap.comp_apply, ← exteriorPower.map_comp,
    LinearEquiv.symm_comp, exteriorPower.map_id,
    LinearMap.id_apply] using h

end ComplexDeterminant

variable {K : Type*} [Field K]
variable (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Canonical integral determinant duality, including the generic-rank identification. -/
def determinantDualEquiv : DeterminantLine (K := K) (Dual (𝓞 K) M) ≃ₗ[𝓞 K]
    Dual (𝓞 K) (DeterminantLine (K := K) M) :=
  (degreeCongr (dual_generic_finrank (K := K) (M := M))).trans
    (pairingDualEquiv (𝓞 K) M _)

/-- Integral determinant duality agrees with complex exterior evaluation on all fibers. -/
lemma determinantDual_fiber_eval (σ : K →+* ℂ)
    (f : ComplexFiber (DeterminantLine (K := K) (Dual (𝓞 K) M)) σ)
    (x : ComplexFiber (DeterminantLine (K := K) M) σ) :
    dualFiberEquiv (DeterminantLine (K := K) M) σ
        (fiberMap (determinantDualEquiv M).toLinearMap σ f) x =
      pairingDual ℂ (ComplexFiber M σ) (finrank K (K ⊗[𝓞 K] M))
        (map _ (dualFiberEquiv M σ).toLinearMap
          (degreeCongr (dual_generic_finrank (K := K) (M := M))
            (determinantComplexEquiv (Dual (𝓞 K) M) σ f)))
        (determinantComplexEquiv M σ x) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  change dualBaseChangeEquiv (𝓞 K) ℂ (DeterminantLine (K := K) M)
    (((pairingDual (𝓞 K) M _).comp
      (degreeCongr (dual_generic_finrank (K := K) (M := M))).toLinearMap).baseChange ℂ f) x = _
  rw [LinearMap.baseChange_comp]
  change dualBaseChangeEquiv (𝓞 K) ℂ (DeterminantLine (K := K) M)
    ((pairingDual (𝓞 K) M _).baseChange ℂ
      ((degreeCongr (dual_generic_finrank (K := K) (M := M))).toLinearMap.baseChange ℂ f)) x = _
  rw [exteriorPairing_baseChange, degreeCongr_baseChange]
  rfl

namespace HermitianMetric

variable {M}

/-- Evaluation at an orthonormal determinant generator computes the actual dual form. -/
lemma determinant_dualFiber_inner_eval (h : HermitianMetric (K := K) M) (σ : K →+* ℂ)
    (f g : ComplexFiber (Dual (𝓞 K) (DeterminantLine (K := K) M)) σ) :
    let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
    let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
    let := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
    let b := (stdOrthonormalBasis ℂ (ComplexFiber M σ)).reindex
      (finCongr (complexFiber_finrank M σ))
    (h.determinant.dual.fiber σ).inner f g =
        star (dualFiberEquiv _ σ f ((determinantComplexEquiv M σ).symm (ιMulti ℂ _ b))) *
          dualFiberEquiv _ σ g ((determinantComplexEquiv M σ).symm (ιMulti ℂ _ b)) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let b := (stdOrthonormalBasis ℂ (ComplexFiber M σ)).reindex
    (finCongr (complexFiber_finrank M σ))
  have he (φ : ComplexFiber (Dual (𝓞 K) (DeterminantLine (K := K) M)) σ) :
      dualFiberEquiv _ σ φ ((determinantComplexEquiv M σ).symm (ιMulti ℂ _ b)) =
        star (Geometry.determinantCoordinates b.toBasis
          (determinantComplexEquiv M σ (h.determinant.dualRiesz σ φ))) := by
    rw [← h.determinant.dualRiesz_inner]
    change (ComplexDeterminant.core b).inner _ _ = _
    rw [ComplexDeterminant.core_inner, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      Geometry.determinantCoordinates_ιMulti]
    change _ * b.toBasis.det b.toBasis = _
    rw [Basis.det_self, mul_one]
  change (h.determinant.dualFiber σ).inner f g = _
  rw [dualFiber_inner]
  change (ComplexDeterminant.core b).inner _ _ = _
  rw [ComplexDeterminant.core_inner, he, he, star_star]
  exact mul_comm _ _

/-- Canonical integral determinant duality preserves every archimedean fiber norm. -/
theorem determinantDual_fiber_norm (h : HermitianMetric (K := K) M) (σ : K →+* ℂ)
    (x : ComplexFiber (DeterminantLine (K := K) (Dual (𝓞 K) M)) σ) :
    Real.sqrt (((h.determinant.dual.fiber σ).inner
      (fiberMap (determinantDualEquiv M).toLinearMap σ x)
      (fiberMap (determinantDualEquiv M).toLinearMap σ x)).re) =
        Real.sqrt (((h.dual.determinant.fiber σ).inner x x).re) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber (Dual (𝓞 K) M) σ) := h.dual.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ComplexFiber (Dual (𝓞 K) M) σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber (Dual (𝓞 K) M) σ))
  let : InnerProductSpace.Core ℂ (Dual ℂ (ComplexFiber M σ)) :=
    Tensor.dualCore (ComplexFiber M σ)
  let := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := Dual ℂ (ComplexFiber M σ))
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (Dual ℂ (ComplexFiber M σ)))
  let b := (stdOrthonormalBasis ℂ (ComplexFiber M σ)).reindex
    (finCongr (complexFiber_finrank M σ))
  let c := (stdOrthonormalBasis ℂ (ComplexFiber (Dual (𝓞 K) M) σ)).reindex
    (finCongr (complexFiber_finrank (Dual (𝓞 K) M) σ))
  let hr := dual_generic_finrank (K := K) (M := M)
  let d := c.reindex (finCongr hr)
  let e := (stdOrthonormalBasis ℂ (Dual ℂ (ComplexFiber M σ))).reindex
    (finCongr ((show finrank ℂ (Dual ℂ (ComplexFiber M σ)) = finrank ℂ (ComplexFiber M σ)
      from Subspace.dual_finrank_eq).trans (complexFiber_finrank M σ)))
  let y := map _ (dualFiberEquiv M σ).toLinearMap
    (degreeCongr hr (determinantComplexEquiv (Dual (𝓞 K) M) σ x))
  have hi : (h.determinant.dual.fiber σ).inner
      (fiberMap (determinantDualEquiv M).toLinearMap σ x)
      (fiberMap (determinantDualEquiv M).toLinearMap σ x) =
        (ComplexDeterminant.dualPullbackCore b).inner y y := by
    rw [h.determinant_dualFiber_inner_eval, determinantDual_fiber_eval,
      LinearEquiv.apply_symm_apply]
    let : InnerProductSpace.Core ℂ (⋀[ℂ]^(finrank K (K ⊗[𝓞 K] M)) (ComplexFiber M σ)) :=
      ComplexDeterminant.core b
    let := InnerProductSpace.Core.toNormedAddCommGroup
      (𝕜 := ℂ) (F := ⋀[ℂ]^(finrank K (K ⊗[𝓞 K] M)) (ComplexFiber M σ))
    let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ
      (⋀[ℂ]^(finrank K (K ⊗[𝓞 K] M)) (ComplexFiber M σ)))
    exact (ComplexDeterminant.dualCore_inner_eval b
      (pairingDual ℂ _ _ y) (pairingDual ℂ _ _ y)).symm
  rw [hi, ComplexDeterminant.dualPullbackCore_eq b e]
  change Real.sqrt (((ComplexDeterminant.core e).inner
    (map _ (dualFiberEquiv M σ).toLinearMap _)
    (map _ (dualFiberEquiv M σ).toLinearMap _)).re) = _
  rw [ComplexDeterminant.norm_map_eq d e (dualFiberEquiv M σ) (fun _ => rfl),
    ComplexDeterminant.norm_degreeCongr hr c d]
  exact (h.dual.determinantFiber_norm_eq σ c x).symm

/-- Canonical integral determinant duality is an isometry on integral sections. -/
lemma determinantDual_sectionNorm (h : HermitianMetric (K := K) M) (σ : K →+* ℂ)
    (x : DeterminantLine (K := K) (Dual (𝓞 K) M)) :
    h.determinant.dual.sectionNorm σ (determinantDualEquiv M x) =
      h.dual.determinant.sectionNorm σ x := by
  have he := h.determinantDual_fiber_norm σ (fiberSection _ σ x)
  rw [fiberMap_section] at he
  exact he

variable [NumberField K]

/-- The intrinsic normalized degree of the actual Hermitian dual is the negative degree. -/
theorem degree_dual (h : HermitianMetric (K := K) M) : h.dual.degree = -h.degree := by
  have hr := determinant_generic_finrank (K := K) M
  have hrd : finrank K (K ⊗[𝓞 K] Dual (𝓞 K) (DeterminantLine (K := K) M)) = 1 :=
    dual_generic_finrank.trans hr
  let : Nontrivial (Dual (𝓞 K) (DeterminantLine (K := K) M)) := by
    by_contra hn
    have : Subsingleton (Dual (𝓞 K) (DeterminantLine (K := K) M)) :=
      not_nontrivial_iff_subsingleton.mp hn
    rw [Module.finrank_zero_of_subsingleton] at hrd
    exact Nat.zero_ne_one hrd
  calc
    h.dual.degree = h.determinant.dual.lineDegree hrd :=
      h.dual.determinant.lineDegree_eq_of_equiv h.determinant.dual (determinantDualEquiv M)
        (determinant_generic_finrank (Dual (𝓞 K) M)) hrd
        (fun σ x => (h.determinantDual_sectionNorm σ x).symm)
    _ = h.determinant.dual.degree := (h.determinant.dual.degree_eq_lineDegree hrd).symm
    _ = -h.determinant.degree := h.determinant.degree_dual_of_rank_one hr
    _ = -h.degree := congrArg Neg.neg (h.determinant.degree_eq_lineDegree hr)

/-- Duality reverses normalized slope, with no freeness or positive-rank assumption. -/
theorem slope_dual (h : HermitianMetric (K := K) M) : h.dual.slope = -h.slope := by
  simp only [slope, degree_dual, dual_generic_finrank, neg_div]

end HermitianMetric

end BostConjecture.Arithmetic
