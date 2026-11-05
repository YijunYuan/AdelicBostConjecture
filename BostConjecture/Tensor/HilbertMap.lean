module

public import BostConjecture.Tensor.Hilbert

/-! # Tensor maps preserve prescribed factor forms -/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open PiTensorProduct
open scoped TensorProduct

variable {ι : Type*} [Finite ι] {M N : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
  [∀ i, AddCommGroup (N i)] [∀ i, Module ℂ (N i)]

/-- The canonical tensor map preserves the tensor forms when its factor maps
preserve their given forms. This is the Core-input version of factor isometry. -/
theorem tensorCore_map_inner (c : ∀ i, InnerProductSpace.Core ℂ (M i))
    (d : ∀ i, InnerProductSpace.Core ℂ (N i)) (f : ∀ i, M i →ₗ[ℂ] N i)
    (hf : ∀ i x y, (d i).inner (f i x) (f i y) = (c i).inner x y)
    (u v : ⨂[ℂ] i, M i) :
    (tensorCore d).inner (PiTensorProduct.map f u) (PiTensorProduct.map f v) =
      (tensorCore c).inner u v := by
  apply inner_ext_of_span (PiTensorProduct.tprod ℂ)
    (span_tprod_eq_top (R := ℂ) (s := M))
    (tensorCore d) (tensorCore c) (PiTensorProduct.map f) LinearMap.id _ u v
  intro x y
  simp only [map_tprod, LinearMap.id_apply, tensorCore_inner_tprod, hf]

end BostConjecture.Tensor
