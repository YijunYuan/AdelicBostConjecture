module

public import BostConjecture.Tensor.BaseChange
public import Mathlib.LinearAlgebra.PiTensorProduct.Generators
public import Mathlib.RingTheory.PiTensorProduct

/-!
# Regrouping finite tensor products

Canonical distribution and rectangular interchange use only the universal
tensor operations. No module in this file is assumed free or projective.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Tensor

open PiTensorProduct
open scoped TensorProduct

variable (R : Type*) [CommRing R] {ι : Type*}
variable (M N : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

/-- Finite distribution, with its canonical pure-tensor formula. -/
theorem exists_tensorDistribEquiv [Finite ι] :
    ∃ e : (⨂[R] i, M i) ⊗[R] (⨂[R] i, N i) ≃ₗ[R] (⨂[R] i, M i ⊗[R] N i),
      ∀ (x : ∀ i, M i) (y : ∀ i, N i),
        e (tprod R x ⊗ₜ[R] tprod R y) = tprod R (fun i => x i ⊗ₜ[R] y i) := by
  classical
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    obtain ⟨f, hf⟩ := ih (fun i => M (e i)) (fun i => N (e i))
    refine ⟨(TensorProduct.congr (reindex R M e.symm) (reindex R N e.symm)).trans
      (f.trans (reindex R (fun i => M i ⊗[R] N i) e.symm).symm), ?_⟩
    intro x y
    apply (reindex R (fun i => M i ⊗[R] N i) e.symm).injective
    simp [hf]
  | h_empty =>
    refine ⟨(TensorProduct.congr (isEmptyEquiv PEmpty (R := R) (s := M))
      (isEmptyEquiv PEmpty (R := R) (s := N))).trans
      ((TensorProduct.lid R R).trans
        (isEmptyEquiv PEmpty (R := R) (s := fun i => M i ⊗[R] N i)).symm), ?_⟩
    intro x y
    apply (isEmptyEquiv PEmpty (R := R) (s := fun i => M i ⊗[R] N i)).injective
    simp
  | h_option ih =>
    obtain ⟨f, hf⟩ := ih (fun i => M (some i)) (fun i => N (some i))
    refine ⟨(TensorProduct.congr (optionEquiv R M) (optionEquiv R N)).trans
      ((TensorProduct.tensorTensorTensorComm R _ _ _ _).trans
        ((TensorProduct.congr f (LinearEquiv.refl R _)).trans
          (optionEquiv R (fun i => M i ⊗[R] N i)).symm)), ?_⟩
    intro x y
    apply (optionEquiv R (fun i => M i ⊗[R] N i)).injective
    simp [hf]

/-- Pair corresponding factors in two finite tensor products. -/
def tensorDistribEquiv [Finite ι] :
    (⨂[R] i, M i) ⊗[R] (⨂[R] i, N i) ≃ₗ[R] (⨂[R] i, M i ⊗[R] N i) :=
  (exists_tensorDistribEquiv R M N).choose

@[simp]
theorem tensorDistribEquiv_tprod [Finite ι] (x : ∀ i, M i) (y : ∀ i, N i) :
    tensorDistribEquiv R M N (tprod R x ⊗ₜ[R] tprod R y) =
      tprod R (fun i => x i ⊗ₜ[R] y i) :=
  (exists_tensorDistribEquiv R M N).choose_spec x y

@[simp]
theorem tensorDistribEquiv_symm_tprod [Finite ι] (x : ∀ i, M i) (y : ∀ i, N i) :
    (tensorDistribEquiv R M N).symm (tprod R (fun i => x i ⊗ₜ[R] y i)) =
      tprod R x ⊗ₜ[R] tprod R y :=
  (tensorDistribEquiv R M N).symm_apply_eq.mpr (tensorDistribEquiv_tprod R M N x y).symm

variable {κ : Type*} (P : ι → κ → Type*)
  [∀ i j, AddCommGroup (P i j)] [∀ i j, Module R (P i j)]

/-- Finite tensor products may be taken in either order. -/
theorem exists_regroupEquiv [Finite ι] [Finite κ] :
    ∃ e : (⨂[R] i, ⨂[R] j, P i j) ≃ₗ[R] (⨂[R] j, ⨂[R] i, P i j),
      ∀ x : ∀ i j, P i j,
        e (tprod R (fun i => tprod R (x i))) =
          tprod R (fun j => tprod R (fun i => x i j)) := by
  classical
  induction κ using Finite.induction_empty_option with
  | of_equiv e ih =>
    obtain ⟨f, hf⟩ := ih (fun i j => P i (e j))
    refine ⟨(congr (fun i => reindex R (P i) e.symm)).trans
      (f.trans (reindex R (fun j => ⨂[R] i, P i j) e.symm).symm), ?_⟩
    intro x
    apply (reindex R (fun j => ⨂[R] i, P i j) e.symm).injective
    simp [hf]
  | h_empty =>
    let : Fintype ι := Fintype.ofFinite ι
    refine ⟨(congr (fun i => isEmptyEquiv PEmpty (R := R) (s := P i))).trans
      ((constantBaseRingEquiv ι R).toLinearEquiv.trans
        (isEmptyEquiv PEmpty (R := R) (s := fun j => ⨂[R] i, P i j)).symm), ?_⟩
    intro x
    apply (isEmptyEquiv PEmpty (R := R) (s := fun j => ⨂[R] i, P i j)).injective
    simp
  | h_option ih =>
    obtain ⟨f, hf⟩ := ih (fun i j => P i (some j))
    refine ⟨(congr (fun i => optionEquiv R (P i))).trans
      ((tensorDistribEquiv R (fun i => ⨂[R] j, P i (some j)) (fun i => P i none)).symm.trans
        ((TensorProduct.congr f (LinearEquiv.refl R _)).trans
          (optionEquiv R (fun j => ⨂[R] i, P i j)).symm)), ?_⟩
    intro x
    apply (optionEquiv R (fun j => ⨂[R] i, P i j)).injective
    simp [hf]

/-- The canonical interchange of the two finite tensor index sets. -/
def regroupEquiv [Finite ι] [Finite κ] :
    (⨂[R] i, ⨂[R] j, P i j) ≃ₗ[R] (⨂[R] j, ⨂[R] i, P i j) :=
  (exists_regroupEquiv R P).choose

@[simp]
theorem regroupEquiv_tprod [Finite ι] [Finite κ] (x : ∀ i j, P i j) :
    regroupEquiv R P (tprod R (fun i => tprod R (x i))) =
      tprod R (fun j => tprod R (fun i => x i j)) :=
  (exists_regroupEquiv R P).choose_spec x

/-- Nested pure tensors determine a linear map on an iterated finite tensor product. -/
theorem tensorTensor_ext [Finite ι] {Q : Type*} [AddCommGroup Q] [Module R Q]
    {f g : (⨂[R] i, ⨂[R] j, P i j) →ₗ[R] Q}
    (h : ∀ x : ∀ i j, P i j,
      f (tprod R (fun i => tprod R (x i))) = g (tprod R (fun i => tprod R (x i)))) :
    f = g :=
  PiTensorProduct.ext_of_span_eq_top (fun i => span_tprod_eq_top (R := R) (s := P i)) h

/-- Interchanging the two index sets in the opposite order gives the inverse. -/
theorem regroupEquiv_symm [Finite ι] [Finite κ] :
    (regroupEquiv R P).symm = regroupEquiv R (fun j i => P i j) := by
  apply LinearEquiv.toLinearMap_injective
  apply tensorTensor_ext R (fun j i => P i j)
  intro x
  apply (regroupEquiv R P).injective
  simp

end BostConjecture.Tensor
