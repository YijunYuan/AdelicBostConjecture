module

public import BostConjecture.Specht.Hypergeometric
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# Sorting labelled occupancies

An occupancy with distinct entries is uniquely a decreasing occupancy
together with a permutation of its labelled blocks.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open Finset

/-- Occupancies in strictly decreasing order. -/
abbrev SortedOccupancy (a M A : ℕ) := {b : Occupancy a M A // StrictAnti b.val}

/-- Relabelling blocks preserves the total occupancy. -/
def occupancyPerm {a M A : ℕ} (b : Occupancy a M A) (σ : Equiv.Perm (Fin a)) :
    Occupancy a M A :=
  ⟨b.val ∘ σ, (Equiv.sum_comp σ (fun i => (b.val i).val)).trans b.property⟩

@[simp] theorem occupancyPerm_apply {a M A : ℕ} (b : Occupancy a M A)
    (σ : Equiv.Perm (Fin a)) (i : Fin a) : (occupancyPerm b σ).val i = b.val (σ i) := rfl

/-- Forget the ordering while retaining the block labels. -/
def unsortOccupancy {a M A : ℕ} (x : SortedOccupancy a M A × Equiv.Perm (Fin a)) :
    {b : Occupancy a M A // Function.Injective b.val} :=
  ⟨occupancyPerm x.1.val x.2, x.1.property.injective.comp x.2.injective⟩

theorem unsortOccupancy_injective (a M A : ℕ) :
    Function.Injective (@unsortOccupancy a M A) := by
  rintro ⟨⟨b, hb⟩, σ⟩ ⟨⟨c, hc⟩, τ⟩ he
  have he' : b.val ∘ σ = c.val ∘ τ := congrArg (fun x => x.val.val) he
  have hcomp : b.val ∘ (τ.symm.trans σ) = c.val := by
    funext i
    simpa using congrFun he' (τ.symm i)
  have hsorted : Antitone (b.val ∘ (τ.symm.trans σ)) := hcomp ▸ hc.antitone
  have hbc : b.val = c.val := by
    have hu := Tuple.unique_antitone (f := b.val) (σ := Equiv.refl _)
      (τ := τ.symm.trans σ) hb.antitone hsorted
    simpa only [Equiv.coe_refl, Function.comp_id, hcomp] using hu
  have hσ : σ = τ := by
    apply Equiv.ext
    intro i
    apply hb.injective
    simpa only [Function.comp_apply, ← hbc] using congrFun he' i
  have hbc' : b = c := Subtype.ext hbc
  subst c
  subst τ
  rfl

theorem unsortOccupancy_surjective (a M A : ℕ) :
    Function.Surjective (@unsortOccupancy a M A) := by
  intro b
  let σ := Tuple.sort (fun i => OrderDual.toDual (b.val.val i))
  have hs : Antitone (b.val.val ∘ σ) :=
    Tuple.monotone_sort (fun i => OrderDual.toDual (b.val.val i))
  let s : SortedOccupancy a M A :=
    ⟨occupancyPerm b.val σ, hs.strictAnti_of_injective (b.property.comp σ.injective)⟩
  refine ⟨(s, σ.symm), ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  funext i
  exact congrArg b.val.val (σ.apply_symm_apply i)

/-- Every distinct labelled tuple has exactly one decreasing form and one labelling. -/
def sortedOccupancyEquiv (a M A : ℕ) :
    SortedOccupancy a M A × Equiv.Perm (Fin a) ≃
      {b : Occupancy a M A // Function.Injective b.val} :=
  Equiv.ofBijective unsortOccupancy
    ⟨unsortOccupancy_injective a M A, unsortOccupancy_surjective a M A⟩

/-- Sorting a symmetric weight that vanishes on collisions contributes the factor `a!`. -/
theorem sum_occupancy_eq_factorial_mul_sorted {a M A : ℕ}
    (w : Occupancy a M A → ℝ)
    (hperm : ∀ b σ, w (occupancyPerm b σ) = w b)
    (hzero : ∀ b, ¬Function.Injective b.val → w b = 0) :
    ∑ b, w b = (a.factorial : ℝ) * ∑ b : SortedOccupancy a M A, w b.val := by
  classical
  have hsub : (∑ b : {b : Occupancy a M A // Function.Injective b.val}, w b.val) =
      ∑ b, w b := by
    rw [← Finset.sum_subtype (univ.filter fun b : Occupancy a M A =>
      Function.Injective b.val) (by simp) w, sum_filter]
    apply sum_congr rfl
    intro b _
    split_ifs with hb
    · rfl
    · exact (hzero b hb).symm
  rw [← hsub, ← (sortedOccupancyEquiv a M A).sum_comp]
  change (∑ x : SortedOccupancy a M A × Equiv.Perm (Fin a),
    w (occupancyPerm x.1.val x.2)) = _
  simp_rw [hperm]
  rw [Fintype.sum_prod_type]
  simp [Fintype.card_perm, ← mul_sum]

/-- Squared Vandermonde weight times the labelled hypergeometric mass. -/
def occupancyWeight {a M A : ℕ} (b : Occupancy a M A) : ℝ :=
  (Matrix.vandermonde (fun i => ((b.val i).val : ℝ))).det ^ 2 * occupancyMass b

theorem occupancyMass_perm {a M A : ℕ} (b : Occupancy a M A)
    (σ : Equiv.Perm (Fin a)) : occupancyMass (occupancyPerm b σ) = occupancyMass b := by
  unfold occupancyMass
  congr 1
  exact Equiv.prod_comp σ (fun i => (M.choose (b.val i).val : ℝ))

theorem occupancyWeight_perm {a M A : ℕ} (b : Occupancy a M A)
    (σ : Equiv.Perm (Fin a)) : occupancyWeight (occupancyPerm b σ) = occupancyWeight b := by
  unfold occupancyWeight
  rw [occupancyMass_perm]
  have hm : Matrix.vandermonde (fun i => (((occupancyPerm b σ).val i).val : ℝ)) =
      (Matrix.vandermonde (fun i => ((b.val i).val : ℝ))).submatrix σ id := by
    ext i j
    rfl
  rw [hm, Matrix.det_permute, mul_pow]
  have hs : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) ^ 2 = 1 := by
    rw [pow_two]
    exact_mod_cast Int.units_coe_mul_self (Equiv.Perm.sign σ)
  rw [hs, one_mul]

theorem occupancyWeight_eq_zero_of_not_injective {a M A : ℕ} (b : Occupancy a M A)
    (hb : ¬Function.Injective b.val) : occupancyWeight b = 0 := by
  have hz : (Matrix.vandermonde (fun i => ((b.val i).val : ℝ))).det = 0 := by
    by_contra hz
    apply hb
    intro i j hij
    exact Matrix.det_vandermonde_ne_zero_iff.mp hz (by rw [hij])
  simp [occupancyWeight, hz]

/-- The labelled squared-Vandermonde mass is `a!` times the decreasing mass. -/
theorem sum_occupancyWeight_eq_factorial_mul_sorted (a M A : ℕ) :
    ∑ b : Occupancy a M A, occupancyWeight b =
      (a.factorial : ℝ) * ∑ b : SortedOccupancy a M A, occupancyWeight b.val :=
  sum_occupancy_eq_factorial_mul_sorted occupancyWeight occupancyWeight_perm
    occupancyWeight_eq_zero_of_not_injective

end BostConjecture.Specht
