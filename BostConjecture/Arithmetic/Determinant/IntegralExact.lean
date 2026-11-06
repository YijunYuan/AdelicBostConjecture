/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Determinant.Exact
public import BostConjecture.Arithmetic.Degree.Normalization

/-!
# Exact sequences of intrinsic integral determinant lines

The projective exact determinant isomorphism is transported to the existing
`DeterminantLine` objects. The arithmetic rank is the dimension of the actual
generic fiber, not a chosen free model of the integral module.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct exteriorPower

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K]
variable {M N P : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N] [Module.Finite (𝓞 K) N]
    [Module.Projective (𝓞 K) N] [AddCommGroup P] [Module (𝓞 K) P]

variable (i : M →ₗ[𝓞 K] P) (q : P →ₗ[𝓞 K] N) (h : Function.Exact i q)
    (hi : Function.Injective i) (hq : Function.Surjective q)

omit [Module.Projective (𝓞 K) M] in
include h hi hq in
/-- The arithmetic ranks in a projective exact sequence are additive. -/
lemma generic_finrank_exact :
    Module.finrank K (K ⊗[𝓞 K] P) =
      Module.finrank K (K ⊗[𝓞 K] M) + Module.finrank K (K ⊗[𝓞 K] N) := by
  rw [(TensorProduct.isBaseChange (𝓞 K) P K).finrank_eq,
    (TensorProduct.isBaseChange (𝓞 K) M K).finrank_eq,
    (TensorProduct.isBaseChange (𝓞 K) N K).finrank_eq]
  exact exteriorPower.finrank_exact i q h hi hq

/-- The canonical exact isomorphism between the existing intrinsic determinant lines. -/
def determinantExactEquiv :
    DeterminantLine (K := K) M ⊗[𝓞 K] DeterminantLine (K := K) N ≃ₗ[𝓞 K]
      DeterminantLine (K := K) P :=
  (TensorProduct.congr
    (degreeCongr (TensorProduct.isBaseChange (𝓞 K) M K).finrank_eq)
    (degreeCongr (TensorProduct.isBaseChange (𝓞 K) N K).finrank_eq)).trans
      ((exteriorPower.exactEquiv i q h hi hq).trans
        (degreeCongr ((exteriorPower.finrank_exact i q h hi hq).symm.trans
          (TensorProduct.isBaseChange (𝓞 K) P K).finrank_eq.symm)))

/-- Its value can be computed with every section, without making that section
part of the intrinsic determinant-line representation. -/
lemma determinantExactEquiv_apply_of_section
    (s : N →ₗ[𝓞 K] P) (hs : q.comp s = LinearMap.id)
    (z : DeterminantLine (K := K) M ⊗[𝓞 K] DeterminantLine (K := K) N) :
    determinantExactEquiv i q h hi hq z =
      degreeCongr ((exteriorPower.finrank_exact i q h hi hq).symm.trans
        (TensorProduct.isBaseChange (𝓞 K) P K).finrank_eq.symm)
        (map (Module.finrank (𝓞 K) M + Module.finrank (𝓞 K) N) (i.coprod s)
          (prodMap (𝓞 K) M N _ _
            ((TensorProduct.congr
              (degreeCongr (TensorProduct.isBaseChange (𝓞 K) M K).finrank_eq)
              (degreeCongr (TensorProduct.isBaseChange (𝓞 K) N K).finrank_eq)) z))) := by
  simp only [determinantExactEquiv, LinearEquiv.trans_apply,
    exactEquiv_eq_of_section i q h hi hq s hs, exactEquivOfSection_apply]

end BostConjecture.Arithmetic
