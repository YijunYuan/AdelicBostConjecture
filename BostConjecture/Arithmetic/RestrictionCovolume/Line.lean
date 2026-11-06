module

public import BostConjecture.Arithmetic.RestrictionCovolume.Free
public import BostConjecture.Arithmetic.RestrictionCovolume.FiniteIndex

/-!
# Trace covolume of projective lines

A nonzero integral section generates a free submodule of finite index.
Its actual trace covolume and the intrinsic line quotient formula give
the discriminant formula without assuming that the original line is free.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct
open scoped Classical

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable (h : HermitianMetric (K := K) M)

omit [NumberField K] [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
/-- The absolute self-pairing of an integral section is its squared section norm. -/
lemma norm_section_inner_self (σ : K →+* ℂ) (x : M) :
    ‖(h.fiber σ).inner (fiberSection M σ x) (fiberSection M σ x)‖ =
      (h.sectionNorm σ x) ^ 2 := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  change ‖inner ℂ (fiberSection M σ x) (fiberSection M σ x)‖ = ‖fiberSection M σ x‖ ^ 2
  rw [inner_self_eq_norm_sq_to_K]
  simp

/-- The actual covolume of a principal submodule in its induced metric. -/
lemma traceCovolume_principal {x : M} (hx : x ≠ 0) :
    (h.submodule (𝓞 K ∙ x)).traceCovolume =
      |(NumberField.discr K : ℝ)| ^ (1 / 2 : ℝ) * ∏ σ : K →+* ℂ, h.sectionNorm σ x := by
  let P := 𝓞 K ∙ x
  let b := (Module.Basis.singleton (Fin 1) (𝓞 K)).map
    (LinearEquiv.toSpanNonzeroSingleton (𝓞 K) M x hx)
  have hb (i : Fin 1) : (b i : M) = x := by simp [b]
  have hs := (h.submodule P).traceCovolume_sq_eq_discr_mul_prod b
  simp only [Matrix.det_unique, Matrix.of_apply, pow_one] at hs
  have he (σ : K →+* ℂ) :
      ((h.submodule P).fiber σ).inner (fiberSection P σ (b default))
        (fiberSection P σ (b default)) =
      (h.fiber σ).inner (fiberSection M σ x) (fiberSection M σ x) := by
    change (h.fiber σ).inner (fiberSection M σ (b default))
      (fiberSection M σ (b default)) = _
    rw [hb]
  simp_rw [he, h.norm_section_inner_self, Finset.prod_pow] at hs
  have hp : (|(NumberField.discr K : ℝ)| ^ (1 / 2 : ℝ)) ^ 2 =
      |(NumberField.discr K : ℝ)| := by
    rw [← Real.rpow_mul_natCast (abs_nonneg _)]
    norm_num
  have hn : 0 ≤ |(NumberField.discr K : ℝ)| ^ (1 / 2 : ℝ) *
      ∏ σ : K →+* ℂ, h.sectionNorm σ x :=
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Finset.prod_nonneg fun _ _ =>
      Real.sqrt_nonneg _)
  nlinarith [(h.submodule P).traceCovolume_pos, mul_pow
    (|(NumberField.discr K : ℝ)| ^ (1 / 2 : ℝ)) (∏ σ : K →+* ℂ, h.sectionNorm σ x) 2]

/-- The exact formula for every projective line, including nonprincipal ideals. -/
theorem traceCovolume_eq_discr_degree_of_rank_one
    (hr : Module.finrank K (K ⊗[𝓞 K] M) = 1) :
    h.traceCovolume = |(NumberField.discr K : ℝ)| ^
        ((Module.finrank K (K ⊗[𝓞 K] M) : ℝ) / 2) *
      Real.exp (-(Module.finrank ℚ K : ℝ) * h.degree) := by
  let : Nontrivial M := Module.nontrivial_of_finrank_pos
    (show 0 < Module.finrank (𝓞 K) M from
      (TensorProduct.isBaseChange (𝓞 K) M K).finrank_eq ▸ (by omega))
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  let P := 𝓞 K ∙ x
  let b := (Module.Basis.singleton (Fin 1) (𝓞 K)).map
    (LinearEquiv.toSpanNonzeroSingleton (𝓞 K) M x hx)
  have hP : Module.finrank K (K ⊗[𝓞 K] P) = 1 := by
    rw [(TensorProduct.isBaseChange (𝓞 K) P K).finrank_eq]
    simpa using Module.finrank_eq_card_basis b
  have hi := h.traceCovolume_submodule P (hP.trans hr.symm)
  rw [h.traceCovolume_principal hx] at hi
  let := line_quotient_finite hr hx
  have hq : 0 < (Nat.card (M ⧸ P) : ℝ) := by exact_mod_cast Nat.card_pos
  have hD : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))
  have he : Real.exp (-(Module.finrank ℚ K : ℝ) * h.degree) =
      (∏ σ : K →+* ℂ, h.sectionNorm σ x) / (Nat.card (M ⧸ P) : ℝ) := by
    rw [h.degree_eq_lineDegree hr, h.lineDegree_eq_sum_embeddings hr hx]
    have ha (s : ℝ) : -(Module.finrank ℚ K : ℝ) *
        ((Real.log (Nat.card (M ⧸ P)) - s) / (Module.finrank ℚ K : ℝ)) =
          s - Real.log (Nat.card (M ⧸ P)) := by field_simp; ring
    rw [ha, Real.exp_sub, Real.exp_sum, Real.exp_log hq]
    congr 1
    exact Finset.prod_congr rfl fun σ _ => Real.exp_log (h.sectionNorm_pos σ hx)
  rw [he, hr, Nat.cast_one, ← mul_div_assoc]
  exact (eq_div_iff (ne_of_gt hq)).mpr (by nlinarith [hi])

end BostConjecture.Arithmetic.HermitianMetric
