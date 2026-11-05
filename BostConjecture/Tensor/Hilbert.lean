module

public import BostConjecture.Tensor.BaseChange
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# The Hermitian form on finite tensor products

The finite tensor product carries the unique positive Hermitian form whose
value on two pure tensors is the product of the factor inner products. The
construction reuses Mathlib's binary Hilbert tensor product and the canonical
finite tensor decompositions. It changes no arithmetic fiber representation.
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
    rw [hc]
    exact finprod_comp_equiv e (f := fun i => inner ℂ (x i) (y i))
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
def hilbertCore [Finite ι] : InnerProductSpace.Core ℂ (⨂[ℂ] i, E i) :=
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
    c.inner (f x) (f y) = d.inner (g x) (g y) := by
  let c' : PreInnerProductSpace.Core ℂ V := { __ := c }
  let d' : PreInnerProductSpace.Core ℂ W := { __ := d }
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    induction y using PiTensorProduct.induction_on with
    | smul_tprod s y =>
      simp only [map_smul, c.smul_left, d.smul_left,
        InnerProductSpace.Core.inner_smul_right (c := c'),
        InnerProductSpace.Core.inner_smul_right (c := d'), h]
    | add y z hy hz =>
      simpa only [map_add, InnerProductSpace.Core.inner_add_right (c := c'),
        InnerProductSpace.Core.inner_add_right (c := d')] using congrArg₂ (· + ·) hy hz
  | add x z hx hz =>
    simpa only [map_add, c.add_left, d.add_left] using congrArg₂ (· + ·) hx hz

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

end BostConjecture.Tensor
