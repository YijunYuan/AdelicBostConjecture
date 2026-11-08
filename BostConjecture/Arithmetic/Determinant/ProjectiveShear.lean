/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Determinant.Shear
public import BostConjecture.Arithmetic.Determinant.Line
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Determinant shears without an integral basis

Exterior-power naturality and injection into the generic fiber descend the
finite-frame shear identity to arbitrary finite projective modules over a domain.
-/

@[expose] public section

noncomputable section

open Module TensorProduct

namespace exteriorPower

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- Exterior scalar extension is natural on every integral exterior vector. -/
lemma map_baseChange_section (S : Type*) [CommRing S] [Algebra R S]
    (f : M →ₗ[R] N) (n : ℕ) (x : ⋀[R]^n M) :
    baseChangeEquiv R N S n (1 ⊗ₜ[R] map n f x) =
      map n (f.baseChange S) (baseChangeEquiv R M S n (1 ⊗ₜ[R] x)) := by
  have he :
      (((baseChangeEquiv R N S n).toLinearMap.restrictScalars R).comp
        (TensorProduct.mk R S (⋀[R]^n N) 1)).comp (map n f) =
      ((map n (f.baseChange S)).restrictScalars R).comp
        (((baseChangeEquiv R M S n).toLinearMap.restrictScalars R).comp
          (TensorProduct.mk R S (⋀[R]^n M) 1)) := by
    apply linearMap_ext
    apply AlternatingMap.ext
    intro v
    change baseChangeEquiv R N S n (1 ⊗ₜ[R] map n f (ιMulti R n v)) =
      map n (f.baseChange S) (baseChangeEquiv R M S n (1 ⊗ₜ[R] ιMulti R n v))
    rw [map_apply_ιMulti, baseChangeEquiv_apply_tmul, baseChangeEquiv_apply_tmul,
      map_apply_ιMulti]
    rfl
  exact LinearMap.congr_fun he x

variable [IsDomain R] [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]

/-- A shear acts trivially on the actual projective determinant line. -/
lemma map_upperShear_top (t : N →ₗ[R] M)
    (x : ⋀[R]^(Module.finrank R M + Module.finrank R N) (M × N)) :
    map (Module.finrank R M + Module.finrank R N) (upperShear t) x = x := by
  let F := FractionRing R
  let p := TensorProduct.prodRight R F F M N
  let n := Module.finrank R M + Module.finrank R N
  apply Module.Flat.tensorProduct_mk_injective R (⋀[R]^n (M × N)) F
  apply (baseChangeEquiv R (M × N) F n).injective
  apply map_injective p.symm.toLinearMap (by
    apply LinearMap.ext
    exact fun z => p.symm_apply_apply z)
  simp only [TensorProduct.mk_apply]
  rw [map_baseChange_section F (upperShear t) n x]
  have hp : p.toLinearMap.comp ((upperShear t).baseChange F) =
      (upperShear (t.baseChange F)).comp p.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c z
    simp [p, tmul_add]
  change (map n p.toLinearMap) ((map n ((upperShear t).baseChange F))
    (baseChangeEquiv R (M × N) F n (1 ⊗ₜ[R] x))) = _
  rw [← LinearMap.comp_apply, ← map_comp, hp, map_comp, LinearMap.comp_apply]
  exact map_upperShear_top_of_basis
    (Module.finBasisOfFinrankEq F (F ⊗[R] M) (TensorProduct.isBaseChange R M F).finrank_eq)
    (Module.finBasisOfFinrankEq F (F ⊗[R] N) (TensorProduct.isBaseChange R N F).finrank_eq)
    (t.baseChange F) _

end exteriorPower
