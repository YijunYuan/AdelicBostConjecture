/-
Copyright (c) 2026 The openai/math contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The openai/math contributors
-/
/-
Adapted from openai/math, commit 4eaee87548250b2682affda7d05d947c05554bae.
Original path: lean/OAI/NumberTheory/ArithmeticGroups/Lattices/BasisLift.lean
Released under Apache 2.0; see BostConjecture/ExternalCode/OAI/LICENSE.
Local changes: see CONTRIBUTIONS.md in the BostConjecture project root.
This file has been modified for Lean 4.35 module visibility.
-/
module

public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Data.EReal.Inv
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.NormNum.GCD

/-!
# Basis Lift

## Source

Adapted from <https://github.com/openai/math>, revision
`4eaee87548250b2682affda7d05d947c05554bae`.
Original source:
* `lean/OAI/NumberTheory/ArithmeticGroups/Lattices/BasisLift.lean`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in `CONTRIBUTIONS.md`.
-/

@[expose] public section

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.BasisLift.Construction

noncomputable section

/-! Lifting a basis through a quotient with a primitive cyclic kernel. -/

open Set _root_.Module

theorem basis_lift_cyclic_kernel
    {R M N ι : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M]
    [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (v : M) (hv0 : v ≠ 0)
    (hker : f.ker = Submodule.span R ({v} : Set M))
    (b : Basis ι R N) (u : ι → M) (hu : ∀ i, f (u i) = b i) :
    ∃ B : Basis (Unit ⊕ ι) R M,
      B (Sum.inl ()) = v ∧ ∀ i, B (Sum.inr i) = u i := by
  classical
  let s : N →ₗ[R] M := b.constr R u
  have hs : f.comp s = LinearMap.id := by
    apply b.ext
    intro i
    simpa [s] using hu i
  have hfv : f v = 0 := by
    apply LinearMap.mem_ker.mp
    simpa only [hker] using Submodule.mem_span_singleton_self v
  let d : (R × N) →ₗ[R] M := (LinearMap.toSpanSingleton R M v).coprod s
  have hd : ∀ a : R × N, d a = a.1 • v + s a.2 := fun _ => rfl
  have hfd (a : R × N) : f (d a) = a.2 := by
    rw [hd, map_add, map_smul, hfv, smul_zero, zero_add]
    exact LinearMap.congr_fun hs a.2
  have hinj : Function.Injective d := by
    apply (LinearMap.ker_eq_bot).mp
    apply le_antisymm
    · intro a ha
      have ha0 : d a = 0 := ha
      have hsnd : a.2 = 0 := by simpa [ha0] using (hfd a).symm
      have hfst : a.1 = 0 := by
        have he : a.1 • v = 0 := by simpa [hd, hsnd] using ha0
        exact (smul_eq_zero.mp he).resolve_right hv0
      exact Prod.ext hfst hsnd
    · exact bot_le
  have hsurj : Function.Surjective d := by
    intro x
    have hx : x - s (f x) ∈ f.ker := by
      change f (x - s (f x)) = 0
      rw [map_sub, show f (s (f x)) = f x from LinearMap.congr_fun hs (f x), sub_self]
    rw [hker] at hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨(a, f x), ?_⟩
    simpa only [hd, ha] using sub_add_cancel _ _
  let e := LinearEquiv.ofBijective d ⟨hinj, hsurj⟩
  refine ⟨((Basis.singleton Unit R).prod b).map e, ?_, ?_⟩
  · change d ((Basis.singleton Unit R).prod b (Sum.inl ())) = v
    rw [hd, Basis.prod_apply_inl_fst, Basis.prod_apply_inl_snd]
    simp
  · intro i
    change d ((Basis.singleton Unit R).prod b (Sum.inr i)) = u i
    rw [hd, Basis.prod_apply_inr_fst, Basis.prod_apply_inr_snd]
    simp [s]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.BasisLift.Construction
