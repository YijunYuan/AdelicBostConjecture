/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.ExternalCode.OAI.RepresentationTheory.Saxl.SpechtSubmodule
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Integral polytabloids in word coordinates

The integral orbit span embeds in the complex word realization of `OAI.Saxl`.
The definitions use integer coefficients before extending scalars; no metric is
placed on the function space in this file.

Reference: this paper, Definition 3.6.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl
open scoped TensorProduct

variable {n d : ℕ} {μ : YoungDiagram}

/-- This paper, Definition 3.3.

The position action on integer word coefficients. -/
def wordRepInt (n d : ℕ) :
    Representation ℤ (Equiv.Perm (Fin n)) ((Fin n → Fin d) → ℤ) where
  toFun g :=
    { toFun := fun x w => x (w ∘ g)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  map_one' := by ext x w; rfl
  map_mul' g h := by ext x w; rfl

/-- Coefficientwise extension of integer words to complex words. -/
def complexCast (n d : ℕ) : ((Fin n → Fin d) → ℤ) →ₗ[ℤ] WordSpace n d where
  toFun x w := (x w : ℂ)
  map_add' x y := by ext w; simp
  map_smul' a x := by ext w; simp

theorem complexCast_injective : Function.Injective (complexCast n d) := by
  intro x y h
  ext w
  exact Int.cast_injective (congrFun h w)

@[simp] theorem complexCast_wordRep (g : Equiv.Perm (Fin n))
    (x : (Fin n → Fin d) → ℤ) :
    complexCast n d (wordRepInt n d g x) = wordRep n d g (complexCast n d x) := rfl

/-- This paper, Definition 3.6, equation (3.3). See [Kuenzer–Nebe, Section 2.1][kn].

The integral column antisymmetrizer of the row word. -/
def polytabloidInt (t : Tableau n μ) : (Fin n → Fin (μ.colLen 0)) → ℤ := by
  classical
  letI := Fintype.ofFinite (columnGroup t)
  exact ∑ g : columnGroup t,
    (Equiv.Perm.sign (g : Equiv.Perm (Fin n)) : ℤ) •
      wordRepInt n (μ.colLen 0) g (Pi.single (rowWord t) 1)

@[simp] theorem complexCast_polytabloid (t : Tableau n μ) :
    complexCast n (μ.colLen 0) (polytabloidInt t) = polytabloid t := by
  classical
  unfold polytabloidInt polytabloid
  simp only [map_sum, map_smul, complexCast_wordRep]
  apply Finset.sum_congr rfl
  intro g hg
  rw [Int.cast_smul_eq_zsmul]
  congr 2
  ext w
  simp [complexCast, Pi.single_apply]

theorem polytabloidInt_rowWord (t : Tableau n μ) : polytabloidInt t (rowWord t) = 1 := by
  apply Int.cast_injective (α := ℂ)
  simpa [complexCast, polytabloid_rowWord] using congrFun (complexCast_polytabloid t) (rowWord t)

theorem polytabloidInt_ne_zero (t : Tableau n μ) : polytabloidInt t ≠ 0 := by
  intro h
  have := polytabloidInt_rowWord t
  simp [h] at this

/-- This paper, Definition 3.6, equation (3.4). The equality with the span of all tableaux is
`orbitLattice_eq_span_polytabloids`.

The integral span of the permutation orbit of one polytabloid. -/
def orbitLattice (t : Tableau n μ) : Submodule ℤ ((Fin n → Fin (μ.colLen 0)) → ℤ) :=
  Submodule.span ℤ (Set.range fun g => wordRepInt n (μ.colLen 0) g (polytabloidInt t))

theorem orbit_mem_orbitLattice (t : Tableau n μ) (g : Equiv.Perm (Fin n)) :
    wordRepInt n (μ.colLen 0) g (polytabloidInt t) ∈ orbitLattice t :=
  Submodule.subset_span ⟨g, rfl⟩

theorem polytabloidInt_mem_orbitLattice (t : Tableau n μ) :
    polytabloidInt t ∈ orbitLattice t := by
  simpa using orbit_mem_orbitLattice t 1

theorem wordRepInt_mem_orbitLattice (t : Tableau n μ) (g : Equiv.Perm (Fin n))
    {x : (Fin n → Fin (μ.colLen 0)) → ℤ} (hx : x ∈ orbitLattice t) :
    wordRepInt n (μ.colLen 0) g x ∈ orbitLattice t := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    simpa only [map_mul, Module.End.mul_apply] using orbit_mem_orbitLattice t (g * h)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih => simpa only [map_smul] using Submodule.smul_mem _ a ih

theorem orbitLattice_fg (t : Tableau n μ) : (orbitLattice t).FG :=
  Submodule.fg_span (Set.finite_range _)

instance orbitLattice_finite (t : Tableau n μ) : Module.Finite ℤ (orbitLattice t) :=
  Module.Finite.of_fg (orbitLattice_fg t)

instance orbitLattice_free (t : Tableau n μ) : Module.Free ℤ (orbitLattice t) := inferInstance

theorem orbitLattice_ne_bot (t : Tableau n μ) : orbitLattice t ≠ ⊥ := by
  intro h
  have hp := polytabloidInt_mem_orbitLattice t
  rw [h, Submodule.mem_bot] at hp
  exact polytabloidInt_ne_zero t hp

/-- Every integral orbit vector lies in the checked complex Specht module. -/
theorem complexCast_mem_spechtSub (t : Tableau n μ)
    {x : (Fin n → Fin (μ.colLen 0)) → ℤ} (hx : x ∈ orbitLattice t) :
    complexCast n (μ.colLen 0) x ∈ spechtSub t := by
  change complexCast n (μ.colLen 0) x ∈ (spechtSub t).toSubmodule
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    rw [complexCast_wordRep, complexCast_polytabloid]
    exact (spechtSub t).apply_mem_toSubmodule g (mem_cyclic _ _)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
    simpa only [map_smul, ← Int.cast_smul_eq_zsmul ℂ] using
      Submodule.smul_mem (spechtSub t).toSubmodule (a : ℂ) ih

/-- Complex linear span of the actual integral orbit lattice. -/
theorem complex_span_orbitLattice (t : Tableau n μ) :
    Submodule.span ℂ (complexCast n (μ.colLen 0) '' (orbitLattice t : Set _)) =
      (spechtSub t).toSubmodule := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact complexCast_mem_spechtSub t hx
  · change Submodule.span ℂ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    apply Submodule.subset_span
    exact ⟨_, orbit_mem_orbitLattice t g, by simp⟩

/-- The scalar-extension map induced by the integral word-coordinate inclusion. -/
def complexification (t : Tableau n μ) :
    ℂ ⊗[ℤ] orbitLattice t →ₗ[ℂ] WordSpace n (μ.colLen 0) :=
  (TensorProduct.piScalarRight ℤ ℂ ℂ (Fin n → Fin (μ.colLen 0))).toLinearMap.comp
    ((orbitLattice t).subtype.baseChange ℂ)

@[simp] theorem complexification_tmul (t : Tableau n μ) (z : ℂ) (x : orbitLattice t) :
    complexification t (z ⊗ₜ[ℤ] x) = z • complexCast n (μ.colLen 0) x := by
  ext w
  simp [complexification, complexCast, mul_comm]

theorem complexification_injective (t : Tableau n μ) :
    Function.Injective (complexification t) :=
  (TensorProduct.piScalarRight ℤ ℂ ℂ (Fin n → Fin (μ.colLen 0))).injective.comp
    (Module.Flat.lTensor_preserves_injective_linearMap
      (orbitLattice t).subtype Subtype.val_injective)

theorem range_complexification (t : Tableau n μ) :
    LinearMap.range (complexification t) = (spechtSub t).toSubmodule := by
  rw [← complex_span_orbitLattice]
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul z x =>
      rw [complexification_tmul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, x.property, rfl⟩)
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨1 ⊗ₜ[ℤ] (⟨x, hx⟩ : orbitLattice t), by simp⟩

/-- The integral orbit span has the existing complex Specht module as its scalar extension. -/
def complexSpechtEquiv (t : Tableau n μ) : ℂ ⊗[ℤ] orbitLattice t ≃ₗ[ℂ] OAI.Saxl.Specht t :=
  (LinearEquiv.ofInjective (complexification t) (complexification_injective t)).trans
    (LinearEquiv.ofEq _ _ (range_complexification t))

@[simp] theorem complexSpechtEquiv_tmul (t : Tableau n μ) (z : ℂ) (x : orbitLattice t) :
    (complexSpechtEquiv t (z ⊗ₜ[ℤ] x) : WordSpace n (μ.colLen 0)) =
      z • complexCast n (μ.colLen 0) x :=
  complexification_tmul t z x

/-- The position action restricted to the integral orbit lattice. -/
def orbitAction (t : Tableau n μ) (g : Equiv.Perm (Fin n)) :
    orbitLattice t →ₗ[ℤ] orbitLattice t :=
  (wordRepInt n (μ.colLen 0) g).restrict fun _ hx => wordRepInt_mem_orbitLattice t g hx

/-- Scalar extension intertwines the integer and complex permutation actions. -/
theorem complexSpechtEquiv_equivariant (t : Tableau n μ) (g : Equiv.Perm (Fin n))
    (x : ℂ ⊗[ℤ] orbitLattice t) :
    complexSpechtEquiv t ((orbitAction t g).baseChange ℂ x) =
      spechtRep t g (complexSpechtEquiv t x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
    apply Subtype.ext
    simp only [LinearMap.baseChange_tmul, complexSpechtEquiv_tmul]
    change z • complexCast n (μ.colLen 0) (wordRepInt n (μ.colLen 0) g x.val) =
      wordRep n (μ.colLen 0) g (complexSpechtEquiv t (z ⊗ₜ[ℤ] x))
    rw [complexSpechtEquiv_tmul, complexCast_wordRep, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end BostConjecture.Specht
