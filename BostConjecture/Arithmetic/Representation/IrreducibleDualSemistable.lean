/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Representation.ComplexIrreducibleSemistable
public import BostConjecture.Arithmetic.Representation.Dual
public import BostConjecture.Arithmetic.Tensor.Compatibility
public import BostConjecture.Arithmetic.Line.DualDegree

/-!
# Intrinsic dual semistability from irreducibility

Finite-projective dual base change intertwines contragredient actions. Riesz
duality proves that the integral dual action preserves the actual dual metric.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct Module

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
variable {G : Type*} [Group G]

/-- The canonical dual fiber equivalence intertwines contragredient actions. -/
def complexDualRepresentationEquiv (ρ : Representation (𝓞 K) G M) (σ : K →+* ℂ) :
    (complexRepresentation ρ.dual σ).Equiv (complexRepresentation ρ σ).dual :=
  Representation.Equiv.mk (dualFiberEquiv M σ) (by
    intro g
    apply LinearMap.ext_on_range (span_fiberSection σ)
    intro f
    apply LinearMap.ext_on_range (span_fiberSection σ)
    intro x
    change dualFiberEquiv M σ (fiberMap (ρ.dual g) σ (fiberSection _ σ f))
      (fiberSection M σ x) =
      dualFiberEquiv M σ (fiberSection _ σ f)
        (fiberMap (ρ g⁻¹) σ (fiberSection M σ x))
    rw [fiberMap_section, fiberMap_section, dualFiberEquiv_section, dualFiberEquiv_section]
    rfl)

lemma dualFiberEquiv_action (ρ : Representation (𝓞 K) G M) (σ : K →+* ℂ) (a : G)
    (f : ComplexFiber (Dual (𝓞 K) M) σ) (x : ComplexFiber M σ) :
    dualFiberEquiv M σ (fiberMap (ρ.dual a) σ f) x =
      dualFiberEquiv M σ f (fiberMap (ρ a⁻¹) σ x) :=
  congrArg (fun q : Dual ℂ (ComplexFiber M σ) => q x)
    (Representation.IntertwiningMap.isIntertwining _ _
      (complexDualRepresentationEquiv ρ σ).toIntertwiningMap a f)

namespace HermitianMetric

/-- Riesz duality commutes with an isometric group action. -/
lemma dualRiesz_action (h : HermitianMetric (K := K) M)
    (ρ : Representation (𝓞 K) G M)
    (hρ : ∀ (a : G) (σ : K →+* ℂ) (x y : ComplexFiber M σ),
      (h.fiber σ).inner (fiberMap (ρ a) σ x) (fiberMap (ρ a) σ y) = (h.fiber σ).inner x y)
    (a : G) (σ : K →+* ℂ) (f : ComplexFiber (Dual (𝓞 K) M) σ) :
    h.dualRiesz σ (fiberMap (ρ.dual a) σ f) = fiberMap (ρ a) σ (h.dualRiesz σ f) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  apply ext_inner_right ℂ
  intro x
  obtain ⟨y, rfl⟩ := (complexRepresentation ρ σ).apply_bijective a |>.surjective x
  change (h.fiber σ).inner _ (fiberMap (ρ a) σ y) =
    (h.fiber σ).inner _ (fiberMap (ρ a) σ y)
  rw [h.dualRiesz_inner, dualFiberEquiv_action, hρ a σ, h.dualRiesz_inner]
  exact congrArg (dualFiberEquiv M σ f) ((complexRepresentation ρ σ).inv_self_apply a y)

/-- The actual dual metric makes the contragredient integral action isometric. -/
lemma dual_action_inner (h : HermitianMetric (K := K) M)
    (ρ : Representation (𝓞 K) G M)
    (hρ : ∀ (a : G) (σ : K →+* ℂ) (x y : ComplexFiber M σ),
      (h.fiber σ).inner (fiberMap (ρ a) σ x) (fiberMap (ρ a) σ y) = (h.fiber σ).inner x y)
    (a : G) (σ : K →+* ℂ) (f g : ComplexFiber (Dual (𝓞 K) M) σ) :
    (h.dual.fiber σ).inner (fiberMap (ρ.dual a) σ f) (fiberMap (ρ.dual a) σ g) =
      (h.dual.fiber σ).inner f g := by
  change (h.fiber σ).inner (h.dualRiesz σ (fiberMap (ρ.dual a) σ g))
    (h.dualRiesz σ (fiberMap (ρ.dual a) σ f)) =
    (h.fiber σ).inner (h.dualRiesz σ g) (h.dualRiesz σ f)
  rw [h.dualRiesz_action ρ hρ, h.dualRiesz_action ρ hρ, hρ]

/-- An action irreducible at one embedding gives a semistable dual bundle. -/
theorem isSemistable_dual_of_complex_irreducible [NumberField K] [Nontrivial (K ⊗[𝓞 K] M)]
    (h : HermitianMetric (K := K) M) (ρ : Representation (𝓞 K) G M) (σ : K →+* ℂ)
    [Representation.IsIrreducible (complexRepresentation ρ σ)]
    (hρ : ∀ (a : G) (s : K →+* ℂ) (x y : ComplexFiber M s),
      (h.fiber s).inner (fiberMap (ρ a) s x) (fiberMap (ρ a) s y) = (h.fiber s).inner x y) :
    h.dual.IsSemistable := by
  let : Nontrivial (K ⊗[𝓞 K] Dual (𝓞 K) M) := Module.nontrivial_of_finrank_pos (R := K) (by
    rw [dual_generic_finrank]
    exact Module.finrank_pos)
  let : Representation.IsIrreducible (complexRepresentation ρ σ).dual := isIrreducible_dual _
  let : Representation.IsIrreducible (complexRepresentation ρ.dual σ) :=
    isIrreducible_of_equiv (complexDualRepresentationEquiv ρ σ)
  exact h.dual.isSemistable_of_complex_irreducible ρ.dual σ (h.dual_action_inner ρ hρ)

end HermitianMetric
end BostConjecture.Arithmetic
