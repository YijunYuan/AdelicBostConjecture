/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Tensor.Algebra.BaseChange
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# The Hermitian form on finite tensor products

The finite tensor product carries the unique positive Hermitian form whose
value on two pure tensors is the product of the factor inner products. The
construction reuses Mathlib's binary Hilbert tensor product and the canonical
finite tensor decompositions. It changes no arithmetic fiber representation.

## Implementation notes

The canonical core is a scoped instance in `BostConjecture.Tensor`. The induced
norm remains local: arbitrary arithmetic metrics on the same underlying tensor
product are explicit data and must not compete in global instance search.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open PiTensorProduct
open scoped TensorProduct

@[instance_reducible]
private def coreOfEquiv {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (e : V ≃ₗ[ℂ] W) :
    InnerProductSpace.Core ℂ V := by
  let := NormedAddCommGroup.induced V W e e.injective
  let := InnerProductSpace.induced e.toLinearMap
  exact InnerProductSpace.toCore

private theorem coreOfEquiv_inner {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (e : V ≃ₗ[ℂ] W) (x y : V) :
    (coreOfEquiv e).inner x y = inner ℂ (e x) (e y) := rfl

/-- Equality of pulled-back Hermitian forms can be checked on any spanning family. -/
theorem inner_ext_of_span {A V W γ : Type*}
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

variable {ι : Type*} (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℂ (E i)]

/-- Existence of the positive tensor form, by finite induction from the binary tensor product. -/
theorem exists_hilbertCore [Finite ι] :
    ∃ h : InnerProductSpace.Core ℂ (⨂[ℂ] i, E i),
      ∀ x y : ∀ i, E i, h.inner (tprod ℂ x) (tprod ℂ y) = ∏ᶠ i, inner ℂ (x i) (y i) := by
  classical
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    obtain ⟨c, hc⟩ := ih (fun i => E (e i))
    let : InnerProductSpace.Core ℂ (⨂[ℂ] i, E (e i)) := c
    let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ⨂[ℂ] i, E (e i))
    let := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (⨂[ℂ] i, E (e i)))
    refine ⟨coreOfEquiv (W := ⨂[ℂ] i, E (e i)) (reindex ℂ E e.symm), ?_⟩
    intro x y
    rw [coreOfEquiv_inner, reindex_tprod, reindex_tprod]
    change c.inner (tprod ℂ (fun i => x (e i))) (tprod ℂ (fun i => y (e i))) = _
    simpa only [hc] using finprod_comp_equiv e (f := fun i => inner ℂ (x i) (y i))
  | h_empty =>
    refine ⟨coreOfEquiv (isEmptyEquiv PEmpty (R := ℂ) (s := E)), ?_⟩
    intro x y
    simp [coreOfEquiv_inner, finprod_eq_prod_of_fintype]
  | h_option ih =>
    obtain ⟨c, hc⟩ := ih (fun i => E (some i))
    let : InnerProductSpace.Core ℂ (⨂[ℂ] i, E (some i)) := c
    let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ⨂[ℂ] i, E (some i))
    let := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (⨂[ℂ] i, E (some i)))
    refine ⟨coreOfEquiv (optionEquiv ℂ E), ?_⟩
    intro x y
    rw [coreOfEquiv_inner, optionEquiv_tprod, optionEquiv_tprod, TensorProduct.inner_tmul]
    change c.inner (tprod ℂ (fun i => x (some i))) (tprod ℂ (fun i => y (some i))) *
      inner ℂ (x none) (y none) = _
    rw [hc, finprod_option (Set.toFinite _), mul_comm]

/-- The canonical positive Hermitian core on the actual finite tensor product. -/
@[instance_reducible]
scoped instance hilbertCore [Finite ι] : InnerProductSpace.Core ℂ (⨂[ℂ] i, E i) :=
  (exists_hilbertCore E).choose

/-- Its defining formula is the usual Hilbert tensor product formula. -/
theorem hilbertCore_inner_tprod [Finite ι] (x y : ∀ i, E i) :
    (hilbertCore E).inner (tprod ℂ x) (tprod ℂ y) = ∏ᶠ i, inner ℂ (x i) (y i) :=
  (exists_hilbertCore E).choose_spec x y

private theorem inner_ext_tprod {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (c : InnerProductSpace.Core ℂ V) (d : InnerProductSpace.Core ℂ W)
    (f : (⨂[ℂ] i, E i) →ₗ[ℂ] V) (g : (⨂[ℂ] i, E i) →ₗ[ℂ] W)
    (h : ∀ x y : ∀ i, E i, c.inner (f (tprod ℂ x)) (f (tprod ℂ y)) =
      d.inner (g (tprod ℂ x)) (g (tprod ℂ y))) (x y : ⨂[ℂ] i, E i) :
    c.inner (f x) (f y) = d.inner (g x) (g y) :=
  inner_ext_of_span (PiTensorProduct.tprod ℂ) (span_tprod_eq_top (R := ℂ) (s := E)) c d f g h x y

/-- The pure-tensor formula determines the Hermitian core uniquely. -/
theorem hilbertCore_unique [Finite ι] (c : InnerProductSpace.Core ℂ (⨂[ℂ] i, E i))
    (hc : ∀ x y : ∀ i, E i,
      c.inner (tprod ℂ x) (tprod ℂ y) = ∏ᶠ i, inner ℂ (x i) (y i)) :
    c = hilbertCore E := by
  have hinner : c.inner = (hilbertCore E).inner := by
    funext x y
    exact inner_ext_tprod E c (hilbertCore E) (LinearMap.id) (LinearMap.id)
      (fun x y => (hc x y).trans (hilbertCore_inner_tprod E x y).symm) x y
  generalize hd : hilbertCore E = d at hinner ⊢
  rcases c with ⟨⟨⟨ci⟩, cs, cp, ca, cm⟩, cd⟩
  rcases d with ⟨⟨⟨di⟩, ds, dp, da, dm⟩, dd⟩
  cases hinner
  rfl

/-- Tensoring linear isometries preserves the canonical Hilbert tensor form. -/
theorem hilbertCore_map_inner [Finite ι] {F : ι → Type*}
    [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace ℂ (F i)]
    (f : ∀ i, E i →ₗᵢ[ℂ] F i) (x y : ⨂[ℂ] i, E i) :
    (hilbertCore F).inner (map (fun i => (f i).toLinearMap) x)
      (map (fun i => (f i).toLinearMap) y) = (hilbertCore E).inner x y := by
  apply inner_ext_tprod E (hilbertCore F) (hilbertCore E)
    (map (fun i => (f i).toLinearMap)) LinearMap.id _ x y
  intro x y
  simp only [map_tprod, LinearMap.id_apply, hilbertCore_inner_tprod]
  congr 1
  funext i
  exact (f i).inner_map_map (x i) (y i)

/-- Relabelling tensor factors preserves the canonical Hilbert tensor form. -/
theorem hilbertCore_reindex_inner [Finite ι] {κ : Type*} (e : ι ≃ κ)
    (x y : ⨂[ℂ] i, E i) :
    letI : Finite κ := Finite.of_equiv ι e
    (hilbertCore (fun k => E (e.symm k))).inner (reindex ℂ E e x)
      (reindex ℂ E e y) = (hilbertCore E).inner x y := by
  let : Finite κ := Finite.of_equiv ι e
  apply inner_ext_tprod E (hilbertCore (fun k => E (e.symm k))) (hilbertCore E)
    (reindex ℂ E e).toLinearMap LinearMap.id _ x y
  intro x y
  simp only [LinearEquiv.coe_coe, reindex_tprod, LinearMap.id_apply,
    hilbertCore_inner_tprod]
  exact finprod_comp_equiv e.symm (f := fun i => inner ℂ (x i) (y i))

variable {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

/-- Tensor the given Hermitian cores, using their induced norms only locally. -/
@[instance_reducible]
def tensorCore [Finite ι] (c : ∀ i, InnerProductSpace.Core ℂ (M i)) :
    InnerProductSpace.Core ℂ (⨂[ℂ] i, M i) := by
  let : ∀ i, InnerProductSpace.Core ℂ (M i) := c
  let : ∀ i, NormedAddCommGroup (M i) := fun i =>
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : ∀ i, InnerProductSpace ℂ (M i) := fun i =>
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (M i))
  exact hilbertCore M

/-- The tensor of Hermitian cores has the same pure-product formula. -/
theorem tensorCore_inner_tprod [Finite ι] (c : ∀ i, InnerProductSpace.Core ℂ (M i))
    (x y : ∀ i, M i) :
    (tensorCore c).inner (tprod ℂ x) (tprod ℂ y) = ∏ᶠ i, (c i).inner (x i) (y i) := by
  let : ∀ i, InnerProductSpace.Core ℂ (M i) := c
  let : ∀ i, NormedAddCommGroup (M i) := fun i =>
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : ∀ i, InnerProductSpace ℂ (M i) := fun i =>
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (M i))
  exact hilbertCore_inner_tprod _ x y

/-- Starting with inner product spaces recovers the original canonical tensor core. -/
theorem tensorCore_toCore [Finite ι] :
    tensorCore (fun i => InnerProductSpace.toCore (𝕜 := ℂ) (E := E i)) = hilbertCore E := by
  apply hilbertCore_unique
  exact tensorCore_inner_tprod _

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The binary Hilbert tensor form for two given Hermitian cores. -/
@[instance_reducible]
def binaryCore (c : InnerProductSpace.Core ℂ V) (d : InnerProductSpace.Core ℂ W) :
    InnerProductSpace.Core ℂ (V ⊗[ℂ] W) := by
  let := c
  let := d
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := V)
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := W)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ V)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ W)
  exact InnerProductSpace.toCore

/-- The binary tensor form multiplies the two factor pairings. -/
theorem binaryCore_inner_tmul (c : InnerProductSpace.Core ℂ V) (d : InnerProductSpace.Core ℂ W)
    (x x' : V) (y y' : W) :
    (binaryCore c d).inner (x ⊗ₜ[ℂ] y) (x' ⊗ₜ[ℂ] y') = c.inner x x' * d.inner y y' := by
  let := c
  let := d
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := V)
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := W)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ V)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ W)
  exact TensorProduct.inner_tmul (𝕜 := ℂ) x x' y y'

end BostConjecture.Tensor
