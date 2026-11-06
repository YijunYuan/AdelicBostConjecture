module

public import BostConjecture.Main.MaxSlope.Isometry
public import BostConjecture.Arithmetic.Specht.FiniteTensorDegree

/-!
# Unconditional lower bound for actual finite Hilbert tensor products

The established finite tensor metric is used throughout. Canonical arithmetic
regrouping and reindexing are isometries; no iterated replacement model is needed.
-/

@[expose] public section
noncomputable section
open NumberField TensorProduct PiTensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- Every actual finite tensor of positive-rank modules has positive generic rank,
including the unit tensor of an empty family. -/
instance piTensorGenericNontrivial {ι : Type} [Fintype ι] (M : ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module (𝓞 K) (M i)]
    [∀ i, Module.Finite (𝓞 K) (M i)] [∀ i, Nontrivial (K ⊗[𝓞 K] M i)] :
    Nontrivial (K ⊗[𝓞 K] (⨂[𝓞 K] i, M i)) := by
  apply Module.nontrivial_of_finrank_pos (R := K)
  rw [Specht.piTensor_generic_finrank]
  exact Finset.prod_pos (fun i _ => Module.finrank_pos)

/-- The sum of attained maximal slopes is a lower bound for the maximal slope
of the actual finite tensor product, with no semistability assumption. -/
theorem sum_maxSlope_le_piTensor {ι : Type} [Fintype ι] (M : ι → Type u)
    [∀ i, AddCommGroup (M i)] [∀ i, Module (𝓞 K) (M i)]
    [∀ i, Module.Finite (𝓞 K) (M i)] [∀ i, Module.Projective (𝓞 K) (M i)]
    [∀ i, Nontrivial (K ⊗[𝓞 K] M i)]
    (h : ∀ i, HermitianMetric (K := K) (M i)) :
    ∑ i, (h i).maxSlope ≤ (piTensor h).maxSlope := by
  classical
  revert M
  refine Fintype.induction_empty_option (P := fun ι _ =>
    ∀ (M : ι → Type u) [∀ i, AddCommGroup (M i)] [∀ i, Module (𝓞 K) (M i)]
      [∀ i, Module.Finite (𝓞 K) (M i)] [∀ i, Module.Projective (𝓞 K) (M i)]
      [∀ i, Nontrivial (K ⊗[𝓞 K] M i)]
      (h : ∀ i, HermitianMetric (K := K) (M i)),
      ∑ i, (h i).maxSlope ≤ (piTensor h).maxSlope) ?_ ?_ ?_ ι
  · intro α β _ e ih M _ _ _ _ _ h
    let : Fintype α := Fintype.ofEquiv β e.symm
    have hm := maxSlope_eq_of_equiv (piTensor h)
      (piTensor (fun i => h (e i))) (reindex (𝓞 K) M e.symm)
      (Specht.piTensor_reindex_inner M h e)
    rw [hm, ← Equiv.sum_comp e (fun i => (h i).maxSlope)]
    exact ih (fun i => M (e i)) (fun i => h (e i))
  · intro M _ _ _ _ _ h
    simpa [slope, Specht.degree_piTensor_empty] using (piTensor h).slope_le_maxSlope
  · intro α _ ih M _ _ _ _ _ h
    have hm := maxSlope_eq_of_equiv (piTensor h)
      ((piTensor (fun i => h (some i))).tensor (h none)) (Tensor.optionEquiv (𝓞 K) M)
      (Specht.piTensor_option_inner M h)
    rw [hm, Fintype.sum_option]
    calc
      (h none).maxSlope + ∑ i, (h (some i)).maxSlope ≤
          (piTensor (fun i => h (some i))).maxSlope + (h none).maxSlope := by
        linarith only [ih (fun i => M (some i)) (fun i => h (some i))]
      _ ≤ _ := maxSlope_add_le_tensor _ _

end BostConjecture.Arithmetic.HermitianMetric
