/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Determinant.Contraction
public import BostConjecture.Arithmetic.Exterior.Product

/-!
# Determinant norms of orthogonal summands

The exterior product of two orthogonal isometric embeddings multiplies
actual determinant norms. This is the complex metric calculation for the
canonical determinant of an exact sequence.
-/

@[expose] public section

noncomputable section

open TensorProduct exteriorPower
open scoped InnerProductSpace

namespace BostConjecture.Arithmetic.ComplexDeterminant

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] {a b : ℕ}

/-- Orthogonal isometric summands multiply top exterior norms, including rank zero. -/
lemma norm_prodMap (p : OrthonormalBasis (Fin a) ℂ E)
    (q : OrthonormalBasis (Fin b) ℂ F) (c : OrthonormalBasis (Fin (a + b)) ℂ G)
    (f : E →ₗ[ℂ] G) (g : F →ₗ[ℂ] G)
    (hf : ∀ x y, inner ℂ (f x) (f y) = inner ℂ x y)
    (hg : ∀ x y, inner ℂ (g x) (g y) = inner ℂ x y)
    (ho : ∀ x y, inner ℂ (f x) (g y) = 0)
    (x : ⋀[ℂ]^a E) (y : ⋀[ℂ]^b F) :
    Real.sqrt (((core c).inner
      (map (a + b) (f.coprod g) (prodMap ℂ E F a b (x ⊗ₜ[ℂ] y)))
      (map (a + b) (f.coprod g) (prodMap ℂ E F a b (x ⊗ₜ[ℂ] y)))).re) =
      Real.sqrt (((core p).inner x x).re) * Real.sqrt (((core q).inner y y).re) := by
  classical
  let D := (map (a + b) (f.coprod g)).comp (prodMap ℂ E F a b)
  have he : D (ιMulti ℂ a p ⊗ₜ[ℂ] ιMulti ℂ b q) =
      ιMulti ℂ (a + b) (Fin.append (f ∘ p) (g ∘ q)) := by
    simp only [D, LinearMap.comp_apply, prodMap_ιMulti, map_apply_ιMulti]
    congr 1
    funext k
    refine Fin.addCases ?_ ?_ k <;> intro k <;> simp
  have hm : (Matrix.of fun i j => inner ℂ
      (Fin.append (f ∘ p) (g ∘ q) i) (Fin.append (f ∘ p) (g ∘ q) j)) = 1 := by
    ext i j
    refine Fin.addCases ?_ ?_ i <;> intro i <;>
      refine Fin.addCases ?_ ?_ j <;> intro j
    · simp [hf, p.inner_eq_ite, Matrix.one_apply]
    · have hn : Fin.castAdd b i ≠ Fin.natAdd a j := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
        omega
      simp [ho, hn]
    · have hn : Fin.natAdd a i ≠ Fin.castAdd b j := by
        simp only [ne_eq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
        omega
      have hz : inner ℂ (g (q i)) (f (p j)) = 0 := inner_eq_zero_symm.mpr (ho _ _)
      simp [hn, hz]
    · simp [hg, q.inner_eq_ite, Matrix.one_apply]
  have hu : ‖Geometry.determinantCoordinates c.toBasis
      (D (ιMulti ℂ a p ⊗ₜ[ℂ] ιMulti ℂ b q))‖ = 1 := by
    rw [← norm_eq_coordinate, he, core_inner_ιMulti, hm, Matrix.det_one]
    norm_num
  obtain ⟨r, rfl⟩ := (Geometry.determinantCoordinates p.toBasis).symm.surjective x
  obtain ⟨s, rfl⟩ := (Geometry.determinantCoordinates q.toBasis).symm.surjective y
  change Real.sqrt (((core c).inner (D _) (D _)).re) = _
  simp only [Geometry.determinantCoordinates_symm_apply, smul_tmul, tmul_smul,
    map_smul, norm_eq_coordinate, Geometry.determinantCoordinates_ιMulti,
    Module.Basis.det_self, smul_eq_mul, mul_one, norm_mul]
  change ‖s‖ * (‖r‖ * ‖Geometry.determinantCoordinates c.toBasis
    (D (ιMulti ℂ a p ⊗ₜ[ℂ] ιMulti ℂ b q))‖) = ‖r‖ * ‖s‖
  rw [hu, mul_one, mul_comm]

end BostConjecture.Arithmetic.ComplexDeterminant
