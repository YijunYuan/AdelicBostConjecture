/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Main.TensorSemistability.ConjugateBasis
public import BostConjecture.Main.TensorSemistability.PartialTraceDefect

/-!
# Conjugate transport of orthogonal projections and partial traces

These identities provide the conjugation compatibility of the actual
arithmetic partial-trace defect variations.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Balanced

open scoped InnerProductSpace TensorProduct

variable {U V W X : Type*}
    [NormedAddCommGroup U] [InnerProductSpace ℂ U] [FiniteDimensional ℂ U]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]

/-- A conjugate-linear isometry carrying one subspace onto another intertwines
their actual orthogonal projections. -/
theorem starProjection_conjugate (e : U ≃ₗ⋆[ℂ] V)
    (he : ∀ x y, inner ℂ (e x) (e y) = star (inner ℂ x y))
    (S : Submodule ℂ U) (T : Submodule ℂ V)
    (hST : ∀ x, e x ∈ T ↔ x ∈ S) (x : U) :
    T.starProjection (e x) = e (S.starProjection x) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact (hST _).2 (S.starProjection_apply_mem x)
  · intro y hy
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_sub, he, S.starProjection_inner_eq_zero x z ((hST z).1 hy), star_zero]

omit [FiniteDimensional ℂ U] [FiniteDimensional ℂ V]
    [FiniteDimensional ℂ W] [FiniteDimensional ℂ X] in
/-- Tensoring conjugate isometries preserves the Hilbert pairing up to conjugation. -/
theorem inner_tensor_conjugate (e : U ≃ₗ⋆[ℂ] V) (f : W ≃ₗ⋆[ℂ] X)
    (he : ∀ x y, inner ℂ (e x) (e y) = star (inner ℂ x y))
    (hf : ∀ x y, inner ℂ (f x) (f y) = star (inner ℂ x y))
    (z z' : U ⊗[ℂ] W) :
    inner ℂ (TensorProduct.congr e f z) (TensorProduct.congr e f z') =
      star (inner ℂ z z') := by
  induction z using TensorProduct.inductionOn with
  | tmul u w =>
    induction z' using TensorProduct.inductionOn with
    | tmul u' w' => simp only [TensorProduct.congr_tmul, TensorProduct.inner_tmul, he, hf,
        star_mul, mul_comm]
    | add a b ha hb => simp only [map_add, inner_add_right, star_add, ha, hb]
  | add a b ha hb => simp only [map_add, inner_add_left, star_add, ha, hb]

/-- Right partial trace commutes with conjugate-isometric tensor transport. -/
theorem partialTraceRight_conjugate (e : U ≃ₗ⋆[ℂ] V) (f : W ≃ₗ⋆[ℂ] X)
    (he : ∀ x y, inner ℂ (e x) (e y) = star (inner ℂ x y))
    (hf : ∀ x y, inner ℂ (f x) (f y) = star (inner ℂ x y))
    (P : Module.End ℂ (U ⊗[ℂ] W)) (Q : Module.End ℂ (V ⊗[ℂ] X))
    (hPQ : ∀ z, Q (TensorProduct.congr e f z) = TensorProduct.congr e f (P z))
    (y : U) :
    partialTraceRight ℂ V X Q (e y) = e (partialTraceRight ℂ U W P y) := by
  let b := stdOrthonormalBasis ℂ W
  apply ext_inner_left ℂ
  intro x
  obtain ⟨x, rfl⟩ := e.surjective x
  rw [inner_partialTraceRight (conjugateOrthonormalBasis f hf b), he,
    inner_partialTraceRight b, star_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [conjugateOrthonormalBasis_apply, ← TensorProduct.congr_tmul, hPQ,
    inner_tensor_conjugate e f he hf]

/-- Left partial trace commutes with conjugate-isometric tensor transport. -/
theorem partialTraceLeft_conjugate (e : U ≃ₗ⋆[ℂ] V) (f : W ≃ₗ⋆[ℂ] X)
    (he : ∀ x y, inner ℂ (e x) (e y) = star (inner ℂ x y))
    (hf : ∀ x y, inner ℂ (f x) (f y) = star (inner ℂ x y))
    (P : Module.End ℂ (U ⊗[ℂ] W)) (Q : Module.End ℂ (V ⊗[ℂ] X))
    (hPQ : ∀ z, Q (TensorProduct.congr e f z) = TensorProduct.congr e f (P z))
    (y : W) :
    partialTraceLeft ℂ V X Q (f y) = f (partialTraceLeft ℂ U W P y) := by
  let b := stdOrthonormalBasis ℂ U
  apply ext_inner_left ℂ
  intro x
  obtain ⟨x, rfl⟩ := f.surjective x
  rw [inner_partialTraceLeft (conjugateOrthonormalBasis e he b), hf,
    inner_partialTraceLeft b, star_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [conjugateOrthonormalBasis_apply, ← TensorProduct.congr_tmul, hPQ,
    inner_tensor_conjugate e f he hf]

end BostConjecture.Balanced
