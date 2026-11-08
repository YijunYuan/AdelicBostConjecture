/-
Copyright (c) 2026 The openai/math contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The openai/math contributors
-/
/-
Adapted from openai/math, commit 4eaee87548250b2682affda7d05d947c05554bae.
Original path: lean/OAI/NumberTheory/ArithmeticGroups/Lattices/BoundedBasis.lean
Released under Apache 2.0; see BostConjecture/ExternalCode/OAI/LICENSE.
Local changes: see CONTRIBUTIONS.md in the BostConjecture project root.
This file has been modified for Lean 4.35 module visibility.
-/
module

public import BostConjecture.ExternalCode.OAI.NumberTheory.ArithmeticGroups.Lattices.BasisLift
public import BostConjecture.ExternalCode.OAI.NumberTheory.ArithmeticGroups.Lattices.ProjectedLattice
public import BostConjecture.ExternalCode.OAI.NumberTheory.ArithmeticGroups.Lattices.ShortestVector
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Bounded Basis

## Source

Adapted from <https://github.com/openai/math>, revision
`4eaee87548250b2682affda7d05d947c05554bae`.
Original source:
* `lean/OAI/NumberTheory/ArithmeticGroups/Lattices/BoundedBasis.lean`.

The original declaration namespaces and license notices are retained, except for
project-specific adaptations documented in `CONTRIBUTIONS.md`.
-/

@[expose] public section

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedBasis.Construction

open ProjectedLattice.Construction ShortestVector.Construction BasisLift.Construction

noncomputable section

section

/-! One step of lattice basis reduction, with controlled lifts from an
orthogonal projection. -/

open Set _root_.Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def latticeProjection (Λ : Submodule ℤ E) (v : E) : Λ →ₗ[ℤ] projectedLattice Λ v where
  toFun x := ⟨perpendicularProjection v x.val, ⟨x.val, x.property, rfl⟩⟩
  map_add' x y := Subtype.ext ((perpendicularProjection v).map_add x.val y.val)
  map_smul' m x := Subtype.ext
    (((perpendicularProjection v).toLinearMap.restrictScalars ℤ).map_smul m x.val)

theorem shortest_projection_kernel (Λ : Submodule ℤ E) (v : Λ) (hv0 : v.val ≠ 0)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖v.val‖ ≤ ‖x‖) :
    (latticeProjection Λ v.val).ker = Submodule.span ℤ ({v} : Set Λ) := by
  classical
  ext x
  change latticeProjection Λ v.val x = 0 ↔ _
  rw [← Subtype.val_inj]
  change perpendicularProjection v.val x.val = 0 ↔ _
  rw [perpendicularProjection, Submodule.orthogonalProjectionOnto_eq_zero_iff,
    Submodule.orthogonal_orthogonal]
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨m, hm⟩ := shortest_vector_scalar_is_integer Λ v.property hv0 hmin t
      (ht ▸ x.property)
    refine Submodule.mem_span_singleton.mpr ⟨m, Subtype.ext ?_⟩
    simpa only [hm, Int.cast_smul_eq_zsmul, Submodule.coe_smul] using ht
  · intro hx
    obtain ⟨m, hm⟩ := Submodule.mem_span_singleton.mp hx
    refine Submodule.mem_span_singleton.mpr ⟨(m : ℝ), ?_⟩
    simpa only [Int.cast_smul_eq_zsmul, Submodule.coe_smul] using congrArg Subtype.val hm

theorem exists_reduced_basis_lift (Λ : Submodule ℤ E) (v : Λ) (hv0 : v.val ≠ 0)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → ‖v.val‖ ≤ ‖x‖)
    {ι : Type*} (b : Basis ι ℤ (projectedLattice Λ v.val)) :
    ∃ B : Basis (Unit ⊕ ι) ℤ Λ,
      B (Sum.inl ()) = v ∧
      ∀ i, perpendicularProjection v.val (B (Sum.inr i)).val = (b i).val ∧
        ‖(B (Sum.inr i)).val‖ ≤ ‖(b i).val‖ + ‖v.val‖ / 2 := by
  classical
  have hpre (i : ι) : ∃ y : Λ,
      latticeProjection Λ v.val y = b i ∧ ‖y.val‖ ≤ ‖(b i).val‖ + ‖v.val‖ / 2 := by
    obtain ⟨x, hx, he⟩ := (b i).property
    obtain ⟨y, hy, hyp, hyb⟩ := projection_reduced_lift Λ v.property hx
    refine ⟨⟨y, hy⟩, Subtype.ext (hyp.trans he), ?_⟩
    simpa only [show perpendicularProjection v.val x = (b i).val from he] using hyb
  choose u hu hub using hpre
  let : Module.IsTorsionFree ℤ E := Module.IsTorsionFree.trans ℝ
  obtain ⟨B, hB0, hBi⟩ := basis_lift_cyclic_kernel (latticeProjection Λ v.val) v
    (show v ≠ 0 from fun he => hv0 (congrArg Subtype.val he))
    (shortest_projection_kernel Λ v hv0 hmin) b u hu
  refine ⟨B, hB0, fun i => ?_⟩
  rw [hBi]
  exact ⟨congrArg Subtype.val (hu i), hub i⟩

end

/-! A lattice spanned by short vectors has an integral basis with uniformly
bounded lengths. The proof iterates shortest-vector projection. -/

open Set _root_.Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem projection_short_vectors_span (Λ : Submodule ℤ E) (R : ℝ)
    (hspan : Submodule.span ℝ {x : E | x ∈ Λ ∧ ‖x‖ ≤ R} = ⊤) (v : E) :
    Submodule.span ℝ {x : (Submodule.span ℝ ({v} : Set E))ᗮ |
      x ∈ projectedLattice Λ v ∧ ‖x‖ ≤ R} = ⊤ := by
  classical
  let p := (perpendicularProjection v).toLinearMap
  have hp : p.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    exact fun y => ⟨y.val, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self y⟩
  apply top_unique
  calc
    ⊤ = Submodule.span ℝ (p '' {x : E | x ∈ Λ ∧ ‖x‖ ≤ R}) := by
      rw [← Submodule.map_span, hspan, Submodule.map_top, hp]
    _ ≤ Submodule.span ℝ {x | x ∈ projectedLattice Λ v ∧ ‖x‖ ≤ R} := by
      apply Submodule.span_mono
      rintro _ ⟨x, ⟨hx, hxb⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      exact ((Submodule.span ℝ ({v} : Set E))ᗮ.norm_orthogonalProjectionOnto_apply_le x).trans hxb

theorem bounded_spanning_lattice_basis (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (hdim : finrank ℝ E = n)
    (R : ℝ) (hR : 0 ≤ R)
    (hspan : Submodule.span ℝ {x : E | x ∈ Λ ∧ ‖x‖ ≤ R} = ⊤) :
    ∃ b : Basis (Fin n) ℤ Λ, ∀ i, ‖(b i).val‖ ≤ n * R := by
  classical
  induction n generalizing E with
  | zero =>
    let : Subsingleton E := Module.finrank_zero_iff.mp hdim
    exact ⟨Basis.empty Λ, fun i => Fin.elim0 i⟩
  | succ n ih =>
    have hy : ∃ y : E, (y ∈ Λ ∧ ‖y‖ ≤ R) ∧ y ≠ 0 := by
      by_contra! hzero
      have he : (⊤ : Submodule ℝ E) = ⊥ := hspan.symm.trans
        (Submodule.span_eq_bot.mpr (fun x hx => hzero x hx))
      have hz := congrArg (fun W : Submodule ℝ E => finrank ℝ W) he
      simp only [finrank_top, finrank_bot] at hz
      omega
    obtain ⟨y, ⟨hyΛ, hyR⟩, hy0⟩ := hy
    obtain ⟨v, hvΛ, hv0, hmin⟩ := exists_shortest_lattice_vector Λ y hyΛ hy0
    have hvR : ‖v‖ ≤ R := (hmin y hyΛ hy0).trans hyR
    let W : Submodule ℝ E := Submodule.span ℝ {v}
    let Λ' := projectedLattice Λ v
    let : DiscreteTopology Λ' := projected_lattice_discrete Λ hvΛ hv0 hmin
    have hdim' : finrank ℝ Wᗮ = n := by
      have he := W.finrank_add_finrank_orthogonal
      have hW : finrank ℝ W = 1 := finrank_span_singleton hv0
      omega
    obtain ⟨b, hb⟩ := ih Λ' hdim' (projection_short_vectors_span Λ R hspan v)
    obtain ⟨B, hB0, hBi⟩ := exists_reduced_basis_lift Λ ⟨v, hvΛ⟩ hv0 hmin b
    have hB (i : Unit ⊕ Fin n) : ‖(B i).val‖ ≤ (n + 1 : ℕ) * R := by
      rcases i with u | i
      · cases u
        rw [hB0]
        have hn : 0 ≤ (n : ℝ) * R := mul_nonneg (Nat.cast_nonneg n) hR
        push_cast
        change ‖v‖ ≤ _
        nlinarith
      · have hh := (hBi i).2
        have hi := hb i
        change ‖(b i).val‖ ≤ (n : ℝ) * R at hi
        push_cast
        nlinarith
    let e : (Unit ⊕ Fin n) ≃ Fin (n + 1) := Fintype.equivFinOfCardEq (by simp [Nat.add_comm])
    refine ⟨B.reindex e, fun i => ?_⟩
    simpa only [Basis.reindex_apply] using hB (e.symm i)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedBasis.Construction
