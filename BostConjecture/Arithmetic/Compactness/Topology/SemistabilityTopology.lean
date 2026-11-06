/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Compactness.Topology.DegreeContinuity
public import BostConjecture.Arithmetic.HN.Semistable

/-!
# Preservation of normalization and semistability under metric limits

All submodule slopes are continuous for the actual topology of Hermitian
metrics. Their non-strict inequalities, and the normalization equation, are
closed conditions. Positive definiteness of the limiting metric is part of
the ambient metric space, not inferred from a semidefinite limit.

Reference: this paper, page 11, Lemma 7.1.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct Filter
open scoped Topology

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]

/-- Slope is continuous on a fixed underlying integral module. -/
theorem continuous_slope :
    Continuous (fun h : HermitianMetric (K := K) M => h.slope) :=
  continuous_degree.div_const _

/-- Each fixed induced slope is continuous. -/
theorem continuous_slope_submodule (P : Submodule (𝓞 K) M) :
    Continuous (fun h : HermitianMetric (K := K) M => (h.submodule P).slope) :=
  continuous_slope.comp (continuous_submodule P)

/-- Semistability is a closed condition on actual Hermitian metrics. -/
theorem isClosed_isSemistable :
    IsClosed {h : HermitianMetric (K := K) M | h.IsSemistable} := by
  simp only [IsSemistable, Set.ofPred_forall]
  exact isClosed_iInter fun P => isClosed_iInter fun _ =>
    isClosed_le (continuous_slope_submodule P) continuous_slope

/-- Degree-zero semistability is closed; every submodule inequality is retained. -/
theorem isClosed_normalized_semistable :
    IsClosed {h : HermitianMetric (K := K) M | h.degree = 0 ∧ h.IsSemistable} :=
  (isClosed_eq continuous_degree continuous_const).inter isClosed_isSemistable

/-- A limit of normalized semistable actual metrics is normalized and semistable. -/
theorem normalized_semistable_of_tendsto {α : Type*} {l : Filter α} [l.NeBot]
    {h : α → HermitianMetric (K := K) M} {g : HermitianMetric (K := K) M}
    (ht : Tendsto h l (𝓝 g))
    (hs : ∀ᶠ i in l, (h i).degree = 0 ∧ (h i).IsSemistable) :
    g.degree = 0 ∧ g.IsSemistable :=
  isClosed_normalized_semistable.mem_of_tendsto ht hs

end BostConjecture.Arithmetic.HermitianMetric
