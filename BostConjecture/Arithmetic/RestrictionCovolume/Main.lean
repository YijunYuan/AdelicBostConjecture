module

public import BostConjecture.Arithmetic.RestrictionCovolume.Exact
public import BostConjecture.Arithmetic.RestrictionCovolume.Line
public import BostConjecture.Arithmetic.ExactDegree
public import BostConjecture.Arithmetic.RankOneReduction

/-!
# Exact restriction-of-scalars covolume

The actual Euclidean Haar covolume of the restriction-of-scalars trace
lattice equals the absolute field discriminant to half the generic rank,
times the exponential of minus the unnormalized intrinsic degree.
The proof covers nonfree finite projective modules and rank zero by
saturated rank-one induction, using actual quotient metrics.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type u} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Exact Euclidean Haar covolume of the actual trace lattice over every number
field, for arbitrary finite projective integral modules including rank zero. -/
theorem traceCovolume_eq_discr_degree (h : HermitianMetric (K := K) M) :
    h.traceCovolume = |(NumberField.discr K : ℝ)| ^
        ((Module.finrank K (K ⊗[𝓞 K] M) : ℝ) / 2) *
      Real.exp (-(Module.finrank ℚ K : ℝ) * h.degree) := by
  generalize hn : Module.finrank K (K ⊗[𝓞 K] M) = n
  induction n using Nat.strong_induction_on generalizing M with
  | h n ih =>
    by_cases hz : Module.finrank K (K ⊗[𝓞 K] M) = 0
    · simpa only [← hn] using h.traceCovolume_eq_discr_degree_of_rank_zero hz
    obtain ⟨P, hPproj, hP, hQ⟩ := exists_rank_one_submodule (M := M) (Nat.pos_of_ne_zero hz)
    let := hPproj
    have hline := (h.submodule P).traceCovolume_eq_discr_degree_of_rank_one hP
    have hquot := ih _ (show Module.finrank K (K ⊗[𝓞 K] (M ⧸ P)) < n by omega)
      (h.quotient P) rfl
    have hdeg := h.degree_exact P.subtype P.mkQ (LinearMap.exact_subtype_mkQ P)
      P.injective_subtype P.mkQ_surjective
    change h.degree = (h.submodule P).degree + (h.quotient P).degree at hdeg
    have hr : (n : ℝ) = 1 + (Module.finrank K (K ⊗[𝓞 K] (M ⧸ P)) : ℝ) := by
      exact_mod_cast hn.symm.trans hQ
    have hdiscr : 0 < |(NumberField.discr K : ℝ)| := by
      apply abs_pos.mpr
      exact_mod_cast NumberField.discr_ne_zero K
    rw [h.traceCovolume_exact P, hline, hquot, hP, Nat.cast_one, hdeg,
      show (n : ℝ) / 2 = (1 / 2 : ℝ) +
        (Module.finrank K (K ⊗[𝓞 K] (M ⧸ P)) : ℝ) / 2 by linarith,
      Real.rpow_add hdiscr, mul_add, Real.exp_add]
    ring

end BostConjecture.Arithmetic.HermitianMetric
