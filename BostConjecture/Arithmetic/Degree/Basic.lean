/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Determinant.Metric

/-!
# Intrinsic normalized Hermitian degree

Degree is the already proved intrinsic line degree of the actual metrized
determinant line. The section formula uses the actual finite quotient and
the constructed complex determinant norms; no arithmetic identities are
assumed as structure fields.
-/

@[expose] public section

noncomputable section

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

/-- Degree computed from any nonzero integral determinant section, with every
complex embedding counted. -/
theorem degree_eq (h : HermitianMetric K M)
    {ξ : DeterminantLine (K := K) M} (hξ : ξ ≠ 0) :
    h.degree = (Real.log (Nat.card (DeterminantLine (K := K) M ⧸ (𝓞 K ∙ ξ))) -
      ∑ σ : K →+* ℂ, Real.log (h.determinant.sectionNorm σ ξ)) / (Module.finrank ℚ K : ℝ) :=
  h.determinant.lineDegree_eq_sum_embeddings (determinant_generic_finrank M) hξ

/-- The finite quotient appearing in the determinant degree formula is finite. -/
theorem determinant_quotient_finite {ξ : DeterminantLine (K := K) M} (hξ : ξ ≠ 0) :
    Finite (DeterminantLine (K := K) M ⧸ (𝓞 K ∙ ξ)) :=
  line_quotient_finite (determinant_generic_finrank M) hξ

end BostConjecture.Arithmetic.HermitianMetric
