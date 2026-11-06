/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Determinant.Product
public import BostConjecture.Arithmetic.Degree.Normalization

/-!
# The integral determinant of a direct sum

The finite-projective determinant product is identified with the intrinsic
integral determinant lines, whose ranks are measured over the number field.
-/

@[expose] public section

noncomputable section

open TensorProduct

namespace BostConjecture.Arithmetic

open NumberField

variable {K : Type*} [Field K]
variable (M N : Type*) [AddCommGroup M] [Module (𝓞 K) M] [Module.Finite (𝓞 K) M]
    [Module.Projective (𝓞 K) M] [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]

omit [Module.Projective (𝓞 K) M] [Module.Projective (𝓞 K) N] in
lemma generic_finrank_prod :
    Module.finrank K (K ⊗[𝓞 K] (M × N)) =
      Module.finrank K (K ⊗[𝓞 K] M) + Module.finrank K (K ⊗[𝓞 K] N) := by
  rw [(TensorProduct.prodRight (𝓞 K) K K M N).finrank_eq, Module.finrank_prod]

/-- Canonical determinant isomorphism of an integral direct sum, including
nonfree projective modules and zero ranks. -/
def determinantProdEquiv :
    DeterminantLine (K := K) M ⊗[𝓞 K] DeterminantLine (K := K) N ≃ₗ[𝓞 K]
      DeterminantLine (K := K) (M × N) :=
  (LinearEquiv.ofBijective _ (exteriorPower.prodMap_bijective_generic
    (R := 𝓞 K) (M := M) (N := N) K)).trans
      (exteriorPower.degreeCongr (generic_finrank_prod M N).symm)

@[simp]
lemma determinantProdEquiv_apply (z : DeterminantLine (K := K) M ⊗[𝓞 K]
    DeterminantLine (K := K) N) :
    determinantProdEquiv M N z = exteriorPower.degreeCongr (generic_finrank_prod M N).symm
      (exteriorPower.prodMap (𝓞 K) M N _ _ z) := rfl

end BostConjecture.Arithmetic
