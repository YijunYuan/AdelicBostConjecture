/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Specht.Lattice.Basis

/-!
# The real isometric action and Murphy operators on the Specht span

Position permutations act on the existing Hilbert word realization. Restriction
to the actual real orbit span supplies symmetric commuting Murphy operators
and their adjacent recurrence. The content eigenvalues are proved in the spectral module.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n d : ℕ} {μ : YoungDiagram}

/-- The position representation on orthonormal real word coordinates. -/
def wordRepReal (n d : ℕ) :
    Representation ℝ (Equiv.Perm (Fin n)) (EuclideanSpace ℝ (Fin n → Fin d)) where
  toFun g :=
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (wordPerm n d g).symm).toLinearEquiv.toLinearMap
  map_one' := by ext x w; rfl
  map_mul' g h := by ext x w; rfl

@[simp] theorem wordRepReal_realCast (g : Equiv.Perm (Fin n))
    (x : (Fin n → Fin d) → ℤ) :
    wordRepReal n d g (realCast n d x) = realCast n d (wordRepInt n d g x) := rfl

theorem inner_wordRepReal (g : Equiv.Perm (Fin n))
    (x y : EuclideanSpace ℝ (Fin n → Fin d)) :
    inner ℝ (wordRepReal n d g x) (wordRepReal n d g y) = inner ℝ x y :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (wordPerm n d g).symm).inner_map_map x y

theorem wordRepReal_mem_realSpan (t : Tableau n μ) (g : Equiv.Perm (Fin n))
    {x : EuclideanSpace ℝ (Fin n → Fin (μ.colLen 0))} (hx : x ∈ realSpan t) :
    wordRepReal n (μ.colLen 0) g x ∈ realSpan t := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    rw [wordRepReal_realCast]
    exact Submodule.subset_span
      ⟨_, wordRepInt_mem_orbitLattice t g hz, rfl⟩
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using (realSpan t).add_mem ihx ihy
  | smul a x hx ih => simpa only [map_smul] using (realSpan t).smul_mem a ih

/-- The position representation restricted to the real span of the integral lattice. -/
def realSpechtRep (t : Tableau n μ) : Representation ℝ (Equiv.Perm (Fin n)) (realSpan t) where
  toFun g := (wordRepReal n (μ.colLen 0) g).restrict fun _ hx => wordRepReal_mem_realSpan t g hx
  map_one' := by ext x w; rfl
  map_mul' g h := by ext x w; rfl

@[simp] theorem realSpechtRep_coe (t : Tableau n μ) (g : Equiv.Perm (Fin n)) (x : realSpan t) :
    (realSpechtRep t g x : EuclideanSpace ℝ (Fin n → Fin (μ.colLen 0))) =
      wordRepReal n (μ.colLen 0) g x := rfl

theorem inner_realSpechtRep (t : Tableau n μ) (g : Equiv.Perm (Fin n)) (x y : realSpan t) :
    inner ℝ (realSpechtRep t g x) (realSpechtRep t g y) = inner ℝ x y := by
  change inner ℝ (wordRepReal n (μ.colLen 0) g x.val)
    (wordRepReal n (μ.colLen 0) g y.val) = inner ℝ x.val y.val
  exact inner_wordRepReal (n := n) (d := μ.colLen 0) g x.val y.val

theorem inner_realSpechtRep_move (t : Tableau n μ) (g : Equiv.Perm (Fin n)) (x y : realSpan t) :
    inner ℝ (realSpechtRep t g x) y = inner ℝ x (realSpechtRep t g⁻¹ y) := by
  have h := inner_realSpechtRep t g x (realSpechtRep t g⁻¹ y)
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using h

theorem realSpechtRep_swap_symmetric (t : Tableau n μ) (i j : Fin n) :
    (realSpechtRep t (Equiv.swap i j)).IsSymmetric := by
  intro x y
  simpa using inner_realSpechtRep_move t (Equiv.swap i j) x y

/-- The action on the standard real basis is literal relabeling of the integral polytabloid. -/
theorem realSpechtRep_standardRealBasis_coe (t : Tableau n μ) (g : Equiv.Perm (Fin n))
    (T : {u : Tableau n μ // IsStandard u}) :
    (realSpechtRep t g (standardRealBasis t T) : EuclideanSpace ℝ (Fin n → Fin (μ.colLen 0))) =
      realCast n (μ.colLen 0) (polytabloidInt (relabel g T.val)) := by
  rw [realSpechtRep_coe, standardRealBasis_coe, wordRepReal_realCast, polytabloidInt_relabel]

/-- The Murphy operator with zero-based label `j`, on the actual real Specht span. -/
def murphyOperator (t : Tableau n μ) (j : Fin n) : Module.End ℝ (realSpan t) :=
  ∑ i ∈ Finset.Iio j, realSpechtRep t (Equiv.swap i j)

theorem murphyOperator_symmetric (t : Tableau n μ) (j : Fin n) :
    (murphyOperator t j).IsSymmetric := by
  intro x y
  simp only [murphyOperator, LinearMap.sum_apply, sum_inner, inner_sum]
  exact Finset.sum_congr rfl fun i _ => realSpechtRep_swap_symmetric t i j x y

/-- A permutation of the labels preceding `j` commutes with the `j`th Murphy operator. -/
theorem realSpechtRep_commute_murphyOperator (t : Tableau n μ) (j : Fin n)
    (g : Equiv.Perm (Fin n)) (hfix : g j = j)
    (hprefix : ∀ i, i < j ↔ g i < j) :
    Commute (realSpechtRep t g) (murphyOperator t j) := by
  change _ * _ = _ * _
  simp only [murphyOperator, Finset.mul_sum, Finset.sum_mul, ← map_mul]
  apply Finset.sum_bijective g g.bijective
  · intro i
    simpa only [Finset.mem_Iio] using hprefix i
  · intro i hi
    rw [Equiv.mul_swap_eq_swap_mul, hfix]

theorem realSpechtRep_swap_commute_murphyOperator (t : Tableau n μ)
    (i h j : Fin n) (hij : i < j) (hhj : h < j) :
    Commute (realSpechtRep t (Equiv.swap i h)) (murphyOperator t j) := by
  apply realSpechtRep_commute_murphyOperator
  · exact Equiv.swap_apply_of_ne_of_ne hij.ne' hhj.ne'
  · intro x
    by_cases hxi : x = i
    · subst x
      simpa only [Equiv.swap_apply_left] using iff_of_true hij hhj
    by_cases hxh : x = h
    · subst x
      simpa only [Equiv.swap_apply_right] using iff_of_true hhj hij
    rw [Equiv.swap_apply_of_ne_of_ne hxi hxh]

/-- The adjacent-transposition recurrence for the concrete Murphy sums. -/
theorem murphyOperator_succ (t : Tableau n μ) (i j : Fin n) (hij : i.val + 1 = j.val) :
    murphyOperator t j =
      realSpechtRep t (Equiv.swap i j) * murphyOperator t i * realSpechtRep t (Equiv.swap i j) +
        realSpechtRep t (Equiv.swap i j) := by
  have hset : Finset.Iio j = insert i (Finset.Iio i) := by
    ext k
    simp only [Finset.mem_Iio, Finset.mem_insert, Fin.ext_iff, Fin.lt_def]
    omega
  have hconj (k : Fin n) (hk : k ∈ Finset.Iio i) :
      realSpechtRep t (Equiv.swap k j) =
        realSpechtRep t (Equiv.swap i j) * realSpechtRep t (Equiv.swap k i) *
          realSpechtRep t (Equiv.swap i j) := by
    have hki : k < i := Finset.mem_Iio.mp hk
    have hkj : k ≠ j := by
      intro h
      subst k
      have := hki
      simp only [Fin.lt_def] at this
      omega
    have h := Equiv.swap_apply_apply (Equiv.swap i j) k i
    simpa only [Equiv.swap_apply_of_ne_of_ne hki.ne hkj, Equiv.swap_apply_left,
      Equiv.swap_inv, map_mul] using congrArg (realSpechtRep t) h
  change (∑ k ∈ Finset.Iio j, realSpechtRep t (Equiv.swap k j)) = _
  rw [hset, Finset.sum_insert (by simp), add_comm]
  congr 1
  simpa only [murphyOperator, Finset.mul_sum, Finset.sum_mul] using Finset.sum_congr rfl hconj

/-- In affine-Hecke form the adjacent recurrence has scalar correction exactly one. -/
theorem murphyOperator_mul_swap (t : Tableau n μ) (i j : Fin n) (hij : i.val + 1 = j.val) :
    murphyOperator t j * realSpechtRep t (Equiv.swap i j) =
      realSpechtRep t (Equiv.swap i j) * murphyOperator t i + 1 := by
  have hs : realSpechtRep t (Equiv.swap i j) * realSpechtRep t (Equiv.swap i j) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  rw [murphyOperator_succ t i j hij, add_mul, mul_assoc, hs, mul_one]

/-- The adjacent diagonal coefficient is forced by the Murphy eigenvalues.
The hypotheses are spectral equations for a vector, not a content-spectrum assertion. -/
theorem inner_swap_of_murphy_eigenvector (t : Tableau n μ) (i j : Fin n)
    (hij : i.val + 1 = j.val) (x : realSpan t) (a b : ℝ)
    (hi : murphyOperator t i x = a • x) (hj : murphyOperator t j x = b • x)
    (hab : b - a ≠ 0) :
    inner ℝ x (realSpechtRep t (Equiv.swap i j) x) = ‖x‖ ^ 2 / (b - a) := by
  have hr := congrArg (fun f : Module.End ℝ (realSpan t) => f x)
    (murphyOperator_mul_swap t i j hij)
  change murphyOperator t j (realSpechtRep t (Equiv.swap i j) x) =
    realSpechtRep t (Equiv.swap i j) (murphyOperator t i x) + x at hr
  have hs := murphyOperator_symmetric t j x (realSpechtRep t (Equiv.swap i j) x)
  rw [hj, hr, hi, map_smul] at hs
  simp only [real_inner_smul_left (F := realSpan t), real_inner_smul_right (F := realSpan t),
    inner_add_right, real_inner_self_eq_norm_sq] at hs
  apply (eq_div_iff hab).mpr
  nlinarith

/-- The squared-norm ratio forced by two distinct adjacent Murphy eigenvalues.
Identification of the residual with the next monic standard vector remains separate. -/
theorem norm_swap_residual_of_murphy_eigenvector (t : Tableau n μ) (i j : Fin n)
    (hij : i.val + 1 = j.val) (x : realSpan t) (a b : ℝ)
    (hi : murphyOperator t i x = a • x) (hj : murphyOperator t j x = b • x)
    (hab : b - a ≠ 0) :
    ‖realSpechtRep t (Equiv.swap i j) x - (b - a)⁻¹ • x‖ ^ 2 =
      (1 - ((b - a)⁻¹) ^ 2) * ‖x‖ ^ 2 := by
  have hn : ‖realSpechtRep t (Equiv.swap i j) x‖ ^ 2 = ‖x‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using inner_realSpechtRep t (Equiv.swap i j) x x
  rw [norm_sub_sq_real, real_inner_smul_right (F := realSpan t),
    real_inner_comm (F := realSpan t) x (realSpechtRep t (Equiv.swap i j) x),
    inner_swap_of_murphy_eigenvector t i j hij x a b hi hj hab,
    hn, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  simp only [div_eq_mul_inv]
  ring

end BostConjecture.Specht
