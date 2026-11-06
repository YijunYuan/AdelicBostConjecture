/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Exterior.Dual
public import BostConjecture.Arithmetic.Determinant.Metric
public import BostConjecture.Tensor.Dual.Metric

/-!
# Compatibility of complex determinant metrics with duality

Evaluation at an orthonormal top wedge computes the dual determinant form.
The determinant of the dual Gram matrix then proves that canonical exterior
duality preserves the actual Hilbert forms.
-/

@[expose] public section

noncomputable section

open scoped BostConjecture.Tensor

open Module exteriorPower

namespace BostConjecture.Arithmetic.ComplexDeterminant

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {r : ℕ}

/-- The dual determinant form is computed by evaluation at an orthonormal top wedge. -/
lemma dualCore_inner_eval (b : OrthonormalBasis (Fin r) ℂ E)
    (f g : Dual ℂ (⋀[ℂ]^r E)) :
    letI : InnerProductSpace.Core ℂ (⋀[ℂ]^r E) := core b
    letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ⋀[ℂ]^r E)
    letI := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (⋀[ℂ]^r E))
    (Tensor.dualCore (⋀[ℂ]^r E)).inner f g =
      star (f (ιMulti ℂ r b)) * g (ιMulti ℂ r b) := by
  let : InnerProductSpace.Core ℂ (⋀[ℂ]^r E) := core b
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ⋀[ℂ]^r E)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (⋀[ℂ]^r E))
  have he (φ : Dual ℂ (⋀[ℂ]^r E)) :
      φ (ιMulti ℂ r b) = star (Geometry.determinantCoordinates b.toBasis
        (Tensor.dualRieszEquiv (⋀[ℂ]^r E) φ)) := by
    rw [← Tensor.dualRieszEquiv_inner]
    change (core b).inner _ _ = _
    rw [core_inner, Geometry.determinantCoordinates_ιMulti]
    change star (Geometry.determinantCoordinates b.toBasis
      (Tensor.dualRieszEquiv (⋀[ℂ]^r E) φ)) * b.toBasis.det b.toBasis = _
    rw [Basis.det_self, mul_one]
  rw [Tensor.dualCore_inner]
  change (core b).inner _ _ = _
  rw [core_inner, he, he, star_star]
  exact mul_comm _ _

/-- Pull back the dual determinant metric through canonical exterior evaluation. -/
@[instance_reducible]
def dualPullbackCore (b : OrthonormalBasis (Fin r) ℂ E) :
    InnerProductSpace.Core ℂ (⋀[ℂ]^r (Dual ℂ E)) := by
  letI : InnerProductSpace.Core ℂ (⋀[ℂ]^r E) := core b
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ⋀[ℂ]^r E)
  letI := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (⋀[ℂ]^r E))
  let e := pairingDualEquiv ℂ E r
  exact
    { inner := fun x y => (Tensor.dualCore (⋀[ℂ]^r E)).inner (e x) (e y)
      conj_inner_symm := fun _ _ => (Tensor.dualCore _).conj_inner_symm _ _
      re_inner_nonneg := fun _ => (Tensor.dualCore _).re_inner_nonneg _
      add_left := by intros; simp only [map_add, InnerProductSpace.Core.inner_add_left]
      smul_left := by intros; simp only [map_smul, InnerProductSpace.Core.inner_smul_left]
      definite := by
        intro x hx
        apply e.injective
        simpa only [map_zero] using (Tensor.dualCore _).definite _ hx }

/-- The pulled-back form has the dual Gram determinant on arbitrary wedges. -/
lemma dualPullbackCore_inner_ιMulti (b : OrthonormalBasis (Fin r) ℂ E)
    (f g : Fin r → Dual ℂ E) :
    (dualPullbackCore b).inner (ιMulti ℂ r f) (ιMulti ℂ r g) =
      (Matrix.of fun i j => (Tensor.dualCore E).inner (f i) (g j)).det := by
  let : InnerProductSpace.Core ℂ (⋀[ℂ]^r E) := core b
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ⋀[ℂ]^r E)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (⋀[ℂ]^r E))
  change (Tensor.dualCore (⋀[ℂ]^r E)).inner
    (pairingDual ℂ E r (ιMulti ℂ r f)) (pairingDual ℂ E r (ιMulti ℂ r g)) = _
  rw [dualCore_inner_eval, pairingDual_ιMulti_ιMulti, pairingDual_ιMulti_ιMulti]
  have hg : (Matrix.of fun i j => (Tensor.dualCore E).inner (f i) (g j)) =
      (Matrix.of fun i j => f j (b i)).conjTranspose * (Matrix.of fun i j => g j (b i)) := by
    ext i j
    simp [Matrix.mul_apply, Tensor.dualCore_inner_basis E b]
  rw [hg, Matrix.det_mul, Matrix.det_conjTranspose]

section DualInner

local instance : NormedAddCommGroup (Dual ℂ E) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := Dual ℂ E)
local instance : InnerProductSpace ℂ (Dual ℂ E) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (Dual ℂ E))

/-- The canonical exterior-duality map is an isometry for determinant and operator-dual forms. -/
lemma dualPullbackCore_eq (b : OrthonormalBasis (Fin r) ℂ E)
    (d : OrthonormalBasis (Fin r) ℂ (Dual ℂ E)) : dualPullbackCore b = core d := by
  apply core_unique d
  intro f
  exact congrArg Complex.re (dualPullbackCore_inner_ιMulti b f f)

end DualInner

end BostConjecture.Arithmetic.ComplexDeterminant
