/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Representation.IndependentTensorIrreducible
public import BostConjecture.Arithmetic.Representation.ComplexIrreducibleSemistable
public import BostConjecture.Arithmetic.Tensor.Compatibility

/-!
# Intrinsic semistability for independent irreducible tensor factors

The canonical fiber tensor equivalence intertwines the product action, and
the already constructed Hermitian tensor metric makes that action isometric.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

universe u
variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
variable {G H : Type*} [Group G] [Group H]

omit [NumberField K] in
@[simp]
lemma complexRepresentation_section (ρ : Representation (𝓞 K) G M)
    (σ : K →+* ℂ) (g : G) (x : M) :
    complexRepresentation ρ σ g (fiberSection M σ x) = fiberSection M σ (ρ g x) := rfl

/-- Fiber scalar extension intertwines the actual independent tensor action. -/
def complexTensorRepresentationEquiv (ρ : Representation (𝓞 K) G M)
    (τ : Representation (𝓞 K) H N) (σ : K →+* ℂ) :
    (complexRepresentation (independentTensorRepresentation ρ τ) σ).Equiv
      (independentTensorRepresentation (complexRepresentation ρ σ) (complexRepresentation τ σ)) :=
  Representation.Equiv.mk (binaryTensorFiberEquiv σ) (by
    intro g
    apply LinearMap.ext_on_range (span_fiberSection_tmul σ)
    rintro ⟨x, y⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, complexRepresentation_section,
      independentTensorRepresentation, Representation.tprod_apply, MonoidHom.comp_apply,
      TensorProduct.map_tmul, binaryTensorFiberEquiv_section])

namespace HermitianMetric

/-- Independent integral isometries act isometrically for the actual Hilbert tensor metric. -/
lemma tensor_action_inner (h : HermitianMetric (K := K) M) (k : HermitianMetric (K := K) N)
    (ρ : Representation (𝓞 K) G M) (τ : Representation (𝓞 K) H N)
    (hρ : ∀ (a : G) (σ : K →+* ℂ) (x y : ComplexFiber M σ),
      (h.fiber σ).inner (fiberMap (ρ a) σ x) (fiberMap (ρ a) σ y) = (h.fiber σ).inner x y)
    (hτ : ∀ (b : H) (σ : K →+* ℂ) (x y : ComplexFiber N σ),
      (k.fiber σ).inner (fiberMap (τ b) σ x) (fiberMap (τ b) σ y) = (k.fiber σ).inner x y)
    (a : G × H) (σ : K →+* ℂ) (x y : ComplexFiber (M ⊗[𝓞 K] N) σ) :
    ((h.tensor k).fiber σ).inner
      (fiberMap (independentTensorRepresentation ρ τ a) σ x)
      (fiberMap (independentTensorRepresentation ρ τ a) σ y) =
      ((h.tensor k).fiber σ).inner x y := by
  apply Tensor.inner_ext_of_span
    (fun xy : M × N => fiberSection _ σ (xy.1 ⊗ₜ[𝓞 K] xy.2))
    (span_fiberSection_tmul σ) ((h.tensor k).fiber σ) ((h.tensor k).fiber σ)
    (fiberMap (independentTensorRepresentation ρ τ a) σ) LinearMap.id _ x y
  intro b c
  change ((h.tensor k).fiber σ).inner
    (fiberSection _ σ (ρ a.1 b.1 ⊗ₜ[𝓞 K] τ a.2 b.2))
    (fiberSection _ σ (ρ a.1 c.1 ⊗ₜ[𝓞 K] τ a.2 c.2)) = _
  simp only [LinearMap.id_apply]
  rw [tensor_inner_section, tensor_inner_section]
  exact congrArg₂ (· * ·)
    (hρ a.1 σ (fiberSection _ σ b.1) (fiberSection _ σ c.1))
    (hτ a.2 σ (fiberSection _ σ b.2) (fiberSection _ σ c.2))

variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]
variable [Nontrivial (K ⊗[𝓞 K] M)] [Nontrivial (K ⊗[𝓞 K] N)]

/-- Independent actions irreducible at one embedding give a semistable tensor bundle. -/
theorem isSemistable_tensor_of_complex_irreducible
    (h : HermitianMetric (K := K) M) (k : HermitianMetric (K := K) N)
    (ρ : Representation (𝓞 K) G M) (τ : Representation (𝓞 K) H N) (σ : K →+* ℂ)
    [Representation.IsIrreducible (complexRepresentation ρ σ)]
    [Representation.IsIrreducible (complexRepresentation τ σ)]
    (hρ : ∀ (a : G) (s : K →+* ℂ) (x y : ComplexFiber M s),
      (h.fiber s).inner (fiberMap (ρ a) s x) (fiberMap (ρ a) s y) = (h.fiber s).inner x y)
    (hτ : ∀ (b : H) (s : K →+* ℂ) (x y : ComplexFiber N s),
      (k.fiber s).inner (fiberMap (τ b) s x) (fiberMap (τ b) s y) = (k.fiber s).inner x y) :
    (h.tensor k).IsSemistable := by
  let : Nontrivial (K ⊗[𝓞 K] (M ⊗[𝓞 K] N)) := Module.nontrivial_of_finrank_pos (R := K) (by
    rw [tensor_generic_finrank]
    exact Nat.mul_pos Module.finrank_pos Module.finrank_pos)
  let : Representation.IsIrreducible
      (independentTensorRepresentation (complexRepresentation ρ σ) (complexRepresentation τ σ)) :=
    isIrreducible_independentTensor _ _
  let : Representation.IsIrreducible
      (complexRepresentation (independentTensorRepresentation ρ τ) σ) :=
    isIrreducible_of_equiv (complexTensorRepresentationEquiv ρ τ σ)
  exact (h.tensor k).isSemistable_of_complex_irreducible
    (independentTensorRepresentation ρ τ) σ (h.tensor_action_inner k ρ τ hρ hτ)

end HermitianMetric
end BostConjecture.Arithmetic
