module

public import BostConjecture.Tensor.DualCompatibility
public import BostConjecture.Tensor.DualRegroup
public import BostConjecture.Tensor.HilbertMap
public import BostConjecture.Tensor.HilbertRegroup

/-! # Isometry of the canonical dual regrouping -/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open Module PiTensorProduct
open scoped TensorProduct

variable {ι κ : Type*} [Fintype ι] [Finite κ] (E : ι → Type*)
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, FiniteDimensional ℂ (E i)]

local instance : InnerProductSpace.Core ℂ (⨂[ℂ] i, E i) := hilbertCore E

local instance : NormedAddCommGroup (⨂[ℂ] i, E i) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ⨂[ℂ] i, E i)

local instance : SeminormedAddCommGroup (⨂[ℂ] i, E i) :=
  (inferInstance : NormedAddCommGroup (⨂[ℂ] i, E i)).toSeminormedAddCommGroup

local instance : InnerProductSpace ℂ (⨂[ℂ] i, E i) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (⨂[ℂ] i, E i))

/-- The same canonical dual regrouping used in the integral pairing preserves
the iterated Hilbert forms, with no isometry hypothesis on that equivalence. -/
theorem dualRegroupEquiv_inner (u v : ⨂[ℂ] i, ⨂[ℂ] (_ : κ), Dual ℂ (E i)) :
    (tensorCore (fun _ : κ => dualCore (⨂[ℂ] i, E i))).inner
      (dualRegroupEquiv ℂ E u) (dualRegroupEquiv ℂ E v) =
      (tensorCore (fun i => tensorCore (fun _ : κ => dualCore (E i)))).inner u v := by
  change (tensorCore (fun _ : κ => dualCore (⨂[ℂ] i, E i))).inner
    (PiTensorProduct.map (fun _ : κ => (dualDistribEquivOfProjective ℂ E).toLinearMap)
      (regroupEquiv ℂ (fun i (_ : κ) => Dual ℂ (E i)) u))
    (PiTensorProduct.map (fun _ : κ => (dualDistribEquivOfProjective ℂ E).toLinearMap)
      (regroupEquiv ℂ (fun i (_ : κ) => Dual ℂ (E i)) v)) = _
  rw [tensorCore_map_inner
    (fun _ : κ => tensorCore (fun i => dualCore (E i)))
    (fun _ : κ => dualCore (⨂[ℂ] i, E i))
    (fun _ : κ => (dualDistribEquivOfProjective ℂ E).toLinearMap)
    (fun _ => dualDistribEquivOfProjective_inner E)]
  exact regroupEquiv_inner (fun i (_ : κ) => dualCore (E i)) u v

end BostConjecture.Tensor
