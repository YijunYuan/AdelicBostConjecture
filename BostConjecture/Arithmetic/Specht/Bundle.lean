/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Specht.Representation
public import BostConjecture.Arithmetic.Representation.ComplexIrreducibleSemistable

/-!
# The canonical arithmetic Specht bundle

The existing integral orbit lattice is extended to the ring of integers.
The canonical word Gram form defines all of its archimedean metrics, and the
actual permutation action proves intrinsic semistability.

Reference: this paper, Lemma 6.1, pages 8–9.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.Specht

open BostConjecture.Specht

variable {K : Type*} [Field K] {n : ℕ} {μ : YoungDiagram}

/-- The canonical fiber of the scalar-extended orbit lattice. -/
def latticeFiberEquiv (t : OAI.Saxl.Tableau n μ) (σ : K →+* ℂ) :
    ComplexFiber (𝓞 K ⊗[ℤ] orbitLattice t) σ ≃ₗ[ℂ] (ℂ ⊗[ℤ] orbitLattice t) :=
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  AlgebraTensorModule.cancelBaseChange ℤ (𝓞 K) ℂ ℂ (orbitLattice t)

@[simp]
lemma latticeFiberEquiv_section (t : OAI.Saxl.Tableau n μ) (σ : K →+* ℂ)
    (r : 𝓞 K) (x : orbitLattice t) :
    latticeFiberEquiv t σ (fiberSection _ σ (r ⊗ₜ[ℤ] x)) = σ r ⊗ₜ[ℤ] x := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  change (r • (1 : ℂ)) ⊗ₜ[ℤ] x = _
  simp only [Algebra.smul_def, mul_one]
  rfl

/-- The canonical lattice form transported to its actual arithmetic fiber. -/
@[instance_reducible]
def latticeFiber (t : OAI.Saxl.Tableau n μ) (σ : K →+* ℂ) :
    InnerProductSpace.Core ℂ (ComplexFiber (𝓞 K ⊗[ℤ] orbitLattice t) σ) where
  inner x y := (Geometry.latticeComplexCore t).inner
    (latticeFiberEquiv t σ x) (latticeFiberEquiv t σ y)
  conj_inner_symm x y := (Geometry.latticeComplexCore t).conj_inner_symm _ _
  re_inner_nonneg x := (Geometry.latticeComplexCore t).re_inner_nonneg _
  add_left := by intros; simp only [map_add, (Geometry.latticeComplexCore t).add_left]
  smul_left := by intros; simp only [map_smul, (Geometry.latticeComplexCore t).smul_left]
  definite := by
    intro x hx
    apply (latticeFiberEquiv t σ).injective
    simpa only [LinearEquiv.map_zero] using (Geometry.latticeComplexCore t).definite _ hx

/-- Word coefficients conjugate when the arithmetic embedding is conjugated. -/
lemma latticeFiberEquiv_conjugate_coeff (t : OAI.Saxl.Tableau n μ) (σ : K →+* ℂ)
    (x : 𝓞 K ⊗[ℤ] orbitLattice t) (w : Fin n → Fin (μ.colLen 0)) :
    complexification t (latticeFiberEquiv t (ComplexEmbedding.conjugate σ)
      (fiberSection _ _ x)) w =
        star (complexification t (latticeFiberEquiv t σ (fiberSection _ σ x)) w) := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp [latticeFiberEquiv_section, complexification_tmul, complexCast,
      ComplexEmbedding.conjugate_coe_eq]
  | add x y hx hy =>
    simp only [fiberSection, tmul_add, map_add, Pi.add_apply, star_add] at hx hy ⊢
    rw [hx, hy]

/-- The canonical arithmetic Specht metric, with no auxiliary metric choices. -/
def latticeMetric (t : OAI.Saxl.Tableau n μ) :
    HermitianMetric K (𝓞 K ⊗[ℤ] orbitLattice t) where
  fiber := latticeFiber t
  conjugate := by
    intro σ x y
    change (Geometry.latticeComplexCore t).inner
      (latticeFiberEquiv t (ComplexEmbedding.conjugate σ) (fiberSection _ _ x))
      (latticeFiberEquiv t (ComplexEmbedding.conjugate σ) (fiberSection _ _ y)) =
        star ((Geometry.latticeComplexCore t).inner
          (latticeFiberEquiv t σ (fiberSection _ σ x))
          (latticeFiberEquiv t σ (fiberSection _ σ y)))
    simp only [Geometry.latticeComplexCore_inner,
      latticeFiberEquiv_conjugate_coeff, star_sum, star_mul, mul_comm]

/-- The actual representation on the ring-of-integers extension of the orbit lattice. -/
def latticeRepresentation (t : OAI.Saxl.Tableau n μ) :
    Representation (𝓞 K) (Equiv.Perm (Fin n)) (𝓞 K ⊗[ℤ] orbitLattice t) :=
  representationBaseChange (𝓞 K) (integralRepresentation t)

/-- The complex arithmetic fiber is the irreducible complex Specht representation. -/
instance latticeRepresentation_irreducible (t : OAI.Saxl.Tableau n μ) (σ : K →+* ℂ) :
    Representation.IsIrreducible (complexRepresentation (latticeRepresentation t) σ) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  exact isIrreducible_of_equiv (scalarExtensionRepresentationEquiv (𝓞 K) t)

/-- The action is an isometry in every actual archimedean fiber. -/
theorem latticeMetric_action_inner (t : OAI.Saxl.Tableau n μ)
    (g : Equiv.Perm (Fin n)) (σ : K →+* ℂ)
    (x y : ComplexFiber (𝓞 K ⊗[ℤ] orbitLattice t) σ) :
    ((latticeMetric t).fiber σ).inner
      (fiberMap (latticeRepresentation t g) σ x) (fiberMap (latticeRepresentation t g) σ y) =
        ((latticeMetric t).fiber σ).inner x y := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  have he (z : ComplexFiber (𝓞 K ⊗[ℤ] orbitLattice t) σ) :
      latticeFiberEquiv t σ (fiberMap (latticeRepresentation t g) σ z) =
        (orbitAction t g).baseChange ℂ (latticeFiberEquiv t σ z) :=
    LinearMap.congr_fun ((scalarExtensionRepresentationEquiv (𝓞 K) t).isIntertwining' g) z
  change (Geometry.latticeComplexCore t).inner
    (latticeFiberEquiv t σ (fiberMap (latticeRepresentation t g) σ x))
    (latticeFiberEquiv t σ (fiberMap (latticeRepresentation t g) σ y)) =
      (Geometry.latticeComplexCore t).inner (latticeFiberEquiv t σ x) (latticeFiberEquiv t σ y)
  rw [he, he]
  exact latticeComplexCore_action_inner t g _ _

/-- The generic rank is the rank of the original integral orbit lattice. -/
theorem lattice_generic_finrank (t : OAI.Saxl.Tableau n μ) :
    Module.finrank K (K ⊗[𝓞 K] (𝓞 K ⊗[ℤ] orbitLattice t)) =
      Module.finrank ℤ (orbitLattice t) := by
  rw [(AlgebraTensorModule.cancelBaseChange ℤ (𝓞 K) K K (orbitLattice t)).finrank_eq,
    Module.finrank_baseChange]

instance lattice_generic_nontrivial (t : OAI.Saxl.Tableau n μ) :
    Nontrivial (K ⊗[𝓞 K] (𝓞 K ⊗[ℤ] orbitLattice t)) := by
  let : Nontrivial (orbitLattice t) := Submodule.nontrivial_iff_ne_bot.mpr (orbitLattice_ne_bot t)
  apply Module.nontrivial_of_finrank_pos (R := K)
  rw [lattice_generic_finrank]
  exact Module.finrank_pos

/-- The actual canonical arithmetic Specht lattice is semistable. -/
theorem latticeMetric_isSemistable [NumberField K] (t : OAI.Saxl.Tableau n μ) :
    (latticeMetric (K := K) t).IsSemistable := by
  let σ : K →+* ℂ := Classical.choice inferInstance
  exact (latticeMetric t).isSemistable_of_complex_irreducible
    (latticeRepresentation t) σ (latticeMetric_action_inner t)

end BostConjecture.Arithmetic.Specht
