module

public import BostConjecture.Tensor.Hilbert
public import BostConjecture.Tensor.Regroup

/-!
# Hilbert tensor regrouping

The algebraic interchange preserves the actual iterated Hilbert forms.
The proof extends the double pure-tensor formula by spanning.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open PiTensorProduct
open scoped TensorProduct

private theorem inner_ext_of_span {A V W γ : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (v : γ → A)
    (hv : Submodule.span ℂ (Set.range v) = ⊤)
    (c : InnerProductSpace.Core ℂ V) (d : InnerProductSpace.Core ℂ W)
    (f : A →ₗ[ℂ] V) (g : A →ₗ[ℂ] W)
    (h : ∀ i j, c.inner (f (v i)) (f (v j)) = d.inner (g (v i)) (g (v j)))
    (x y : A) : c.inner (f x) (f y) = d.inner (g x) (g y) := by
  let c' : PreInnerProductSpace.Core ℂ V := { __ := c }
  let d' : PreInnerProductSpace.Core ℂ W := { __ := d }
  have hx : x ∈ Submodule.span ℂ (Set.range v) := hv.symm ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span ℂ (Set.range v) := hv.symm ▸ Submodule.mem_top
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact h i j
  | zero_left y hy =>
    simp only [map_zero, InnerProductSpace.Core.inner_zero_left (c := c'),
      InnerProductSpace.Core.inner_zero_left (c := d')]
  | zero_right x hx =>
    simp only [map_zero, InnerProductSpace.Core.inner_zero_right (c := c'),
      InnerProductSpace.Core.inner_zero_right (c := d')]
  | add_left x y z hx hy hz h₁ h₂ =>
    simp only [map_add, c.add_left, d.add_left, h₁, h₂]
  | add_right x y z hx hy hz h₁ h₂ =>
    simp only [map_add, InnerProductSpace.Core.inner_add_right (c := c'),
      InnerProductSpace.Core.inner_add_right (c := d'), h₁, h₂]
  | smul_left r x y hx hy h => simp only [map_smul, c.smul_left, d.smul_left, h]
  | smul_right r x y hx hy h =>
    simp only [map_smul, InnerProductSpace.Core.inner_smul_right (c := c'),
      InnerProductSpace.Core.inner_smul_right (c := d'), h]

variable {ι κ : Type*} [Finite ι] [Finite κ] {P : ι → κ → Type*}
  [∀ i j, AddCommGroup (P i j)] [∀ i j, Module ℂ (P i j)]

/-- Regrouping preserves the iterated canonical Hilbert form, for arbitrary tensors. -/
theorem regroupEquiv_inner (c : ∀ i j, InnerProductSpace.Core ℂ (P i j))
    (x y : ⨂[ℂ] i, ⨂[ℂ] j, P i j) :
    (tensorCore (fun j => tensorCore (fun i => c i j))).inner
      (regroupEquiv ℂ P x) (regroupEquiv ℂ P y) =
      (tensorCore (fun i => tensorCore (c i))).inner x y := by
  apply inner_ext_of_span (fun v : ∀ i j, P i j => tprod ℂ (fun i => tprod ℂ (v i)))
    (PiTensorProduct.submodule_span_eq_top (fun i => span_tprod_eq_top (R := ℂ) (s := P i)))
    _ _ (regroupEquiv ℂ P).toLinearMap LinearMap.id _ x y
  intro v w
  simp only [LinearEquiv.coe_coe, regroupEquiv_tprod, LinearMap.id_apply,
    tensorCore_inner_tprod]
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype κ := Fintype.ofFinite κ
  simp only [finprod_eq_prod_of_fintype]
  exact Finset.prod_comm

end BostConjecture.Tensor
