module

public import BostConjecture.Arithmetic.Compactness.MaximizingPair
public import BostConjecture.Arithmetic.TensorDegree
public import BostConjecture.Main.TensorSemistability.Extensions

/-!
# The least rank sum of an actual normalized counterexample

The rank sum is chosen by well-ordering from positive values of the existing
actual tensor maximum-degree value set. No minimality assumption is introduced.

Reference: bost_specht_manuscript.pdf, Proposition 7.3, pages 12–13.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

universe u
variable {K : Type*} [Field K] [NumberField K]

namespace HermitianMetric

variable {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]

/-- A normalized metric is semistable exactly when its saturated maximum degree
is nonpositive. Saturation handles all integral test submodules. -/
theorem isSemistable_iff_maxDegree_nonpos (h : HermitianMetric (K := K) M)
    (h0 : h.degree = 0) : h.IsSemistable ↔ h.maxDegree ≤ 0 := by
  rw [h.isSemistable_iff_degree_nonpos h0]
  constructor
  · intro hs
    obtain ⟨P, _, hP⟩ := h.exists_degree_eq_maxDegree
    rw [← hP]
    exact hs P
  · intro hm P
    exact (h.degree_submodule_le_maxDegree P).trans hm

/-- An actual normalized tensor counterexample has positive maximum degree. -/
theorem maxDegree_tensor_pos_of_not_isSemistable
    (h : HermitianMetric (K := K) M) (g : HermitianMetric (K := K) N)
    (h0 : h.degree = 0) (g0 : g.degree = 0)
    (hbad : ¬ (h.tensor g).IsSemistable) : 0 < (h.tensor g).maxDegree := by
  have ht0 : (h.tensor g).degree = 0 := by simp [degree_tensor, h0, g0]
  exact lt_of_not_ge (fun hd => hbad ((h.tensor g).isSemistable_iff_maxDegree_nonpos ht0 |>.mpr hd))

end HermitianMetric

namespace Compactness

/-- Well-ordering chooses a least positive-rank counterexample sum among the
existing value sets of actual normalized semistable pairs. -/
theorem exists_minimal_positive_tensorMaxDegree
    (hex : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      ∃ d ∈ tensorMaxDegreeValues.{u} K a b, 0 < d) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      (∃ d ∈ tensorMaxDegreeValues.{u} K a b, 0 < d) ∧
      ∀ a' b' : ℕ, 0 < a' → 0 < b' → a' + b' < a + b →
        ∀ d ∈ tensorMaxDegreeValues.{u} K a' b', d ≤ 0 := by
  classical
  let p : ℕ → Prop := fun n => ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a + b = n ∧
    ∃ d ∈ tensorMaxDegreeValues.{u} K a b, 0 < d
  have hp : ∃ n, p n := by
    obtain ⟨a, b, ha, hb, hd⟩ := hex
    exact ⟨a + b, a, b, ha, hb, rfl, hd⟩
  obtain ⟨a, b, ha, hb, hab, hd⟩ := Nat.find_spec hp
  refine ⟨a, b, ha, hb, hd, ?_⟩
  intro a' b' ha' hb' hlt d hd
  by_contra hpos
  exact Nat.find_min hp (hab ▸ hlt)
    ⟨a', b', ha', hb', rfl, d, hd, lt_of_not_ge hpos⟩

/-- The least-rank value bound implies semistability for every smaller actual
normalized semistable pair, without choosing representatives or free bases. -/
theorem isSemistable_tensor_of_smaller_rank_sum
    {a b : ℕ}
    (hmin : ∀ a' b' : ℕ, 0 < a' → 0 < b' → a' + b' < a + b →
      ∀ d ∈ tensorMaxDegreeValues.{u} K a' b', d ≤ 0)
    {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]
    (h : HermitianMetric (K := K) M) (g : HermitianMetric (K := K) N)
    (hrM : 0 < Module.finrank K (K ⊗[𝓞 K] M))
    (hrN : 0 < Module.finrank K (K ⊗[𝓞 K] N))
    (hlt : Module.finrank K (K ⊗[𝓞 K] M) +
      Module.finrank K (K ⊗[𝓞 K] N) < a + b)
    (h0 : h.degree = 0) (g0 : g.degree = 0)
    (hs : h.IsSemistable) (gs : g.IsSemistable) :
    (h.tensor g).IsSemistable := by
  apply ((h.tensor g).isSemistable_iff_maxDegree_nonpos
    (by simp [HermitianMetric.degree_tensor, h0, g0])).mpr
  exact hmin _ _ hrM hrN hlt _ (tensor_maxDegree_mem h g rfl rfl h0 g0 hs gs)

end Compactness

end BostConjecture.Arithmetic
