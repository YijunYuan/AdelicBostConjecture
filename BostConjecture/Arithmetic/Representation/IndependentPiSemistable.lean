/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Representation.ComplexIrreducibleSemistable
public import BostConjecture.Arithmetic.Representation.IndependentPiIrreducible
public import BostConjecture.Arithmetic.Representation.IrreducibleDualSemistable

/-!
# Semistability of finite independent tensor bundles and their duals

This file treats the actual finite integral tensor module with its established
Hilbert metric. All fiber comparisons are canonical, with nonfree projective
factors allowed.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct PiTensorProduct

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι] {M G : ι → Type*}
variable [∀ i, AddCommGroup (M i)] [∀ i, Module (𝓞 K) (M i)] [∀ i, Group (G i)]

omit [NumberField K] [Fintype ι] in
/-- Pure integral tensors span the entire complex fiber. -/
lemma span_fiberSection_piTensor [Finite ι] (σ : K →+* ℂ) :
    Submodule.span ℂ (Set.range (fun x : ∀ i, M i =>
      fiberSection _ σ (tprod (𝓞 K) x))) = ⊤ := by
  let := Fintype.ofFinite ι
  apply Submodule.map_injective_of_injective (tensorFiberEquiv M σ).injective
  rw [Submodule.map_top, LinearEquiv.range, Submodule.map_span, ← Set.range_comp]
  simpa only [Function.comp_def, LinearEquiv.coe_coe, tensorFiberEquiv_section_tprod] using
    PiTensorProduct.submodule_span_eq_top (fun i => span_fiberSection (M := M i) σ)

/-- The canonical finite tensor fiber equivalence intertwines the componentwise action. -/
def complexPiRepresentationEquiv (ρ : ∀ i, Representation (𝓞 K) (G i) (M i))
    (σ : K →+* ℂ) :
    (complexRepresentation (independentPiRepresentation ρ) σ).Equiv
      (independentPiRepresentation (fun i => complexRepresentation (ρ i) σ)) :=
  Representation.Equiv.mk (tensorFiberEquiv M σ) (by
    intro g
    apply LinearMap.ext_on_range (span_fiberSection_piTensor σ)
    intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, complexRepresentation_section,
      independentPiRepresentation, MonoidHom.coe_mk, OneHom.coe_mk,
      PiTensorProduct.map_tprod, tensorFiberEquiv_section_tprod])

namespace HermitianMetric

omit [NumberField K] in
/-- Componentwise isometries preserve the actual finite Hilbert tensor metric. -/
lemma piTensor_action_inner (h : ∀ i, HermitianMetric K (M i))
    (ρ : ∀ i, Representation (𝓞 K) (G i) (M i))
    (hρ : ∀ i (a : G i) (σ : K →+* ℂ) (x y : ComplexFiber (M i) σ),
      ((h i).fiber σ).inner (fiberMap (ρ i a) σ x) (fiberMap (ρ i a) σ y) =
        ((h i).fiber σ).inner x y)
    (a : ∀ i, G i) (σ : K →+* ℂ) (x y : ComplexFiber (⨂[𝓞 K] i, M i) σ) :
    ((piTensor h).fiber σ).inner
      (fiberMap (independentPiRepresentation ρ a) σ x)
      (fiberMap (independentPiRepresentation ρ a) σ y) = ((piTensor h).fiber σ).inner x y := by
  apply Tensor.inner_ext_of_span (fun z : ∀ i, M i => fiberSection _ σ (tprod (𝓞 K) z))
    (span_fiberSection_piTensor σ) ((piTensor h).fiber σ) ((piTensor h).fiber σ)
    (fiberMap (independentPiRepresentation ρ a) σ) LinearMap.id _ x y
  intro b c
  simp only [fiberMap_section, independentPiRepresentation, MonoidHom.coe_mk,
    OneHom.coe_mk, PiTensorProduct.map_tprod, LinearMap.id_apply]
  change (tensorFiber h σ).inner
    (fiberSection _ σ (tprod (𝓞 K) (fun i => ρ i (a i) (b i))))
    (fiberSection _ σ (tprod (𝓞 K) (fun i => ρ i (a i) (c i)))) =
    (tensorFiber h σ).inner (fiberSection _ σ (tprod (𝓞 K) b))
      (fiberSection _ σ (tprod (𝓞 K) c))
  rw [tensorFiber_inner_tprod, tensorFiber_inner_tprod]
  exact Finset.prod_congr rfl (fun i _ => hρ i (a i) σ
    (fiberSection _ σ (b i)) (fiberSection _ σ (c i)))

variable [∀ i, Module.Finite (𝓞 K) (M i)] [∀ i, Module.Projective (𝓞 K) (M i)]
variable [∀ i, Nontrivial (K ⊗[𝓞 K] M i)]

/-- The finite tensor bundle and its dual are semistable under independent irreducible actions. -/
theorem isSemistable_piTensor_and_dual_of_complex_irreducible
    (h : ∀ i, HermitianMetric K (M i))
    (ρ : ∀ i, Representation (𝓞 K) (G i) (M i)) (σ : K →+* ℂ)
    [∀ i, Representation.IsIrreducible (complexRepresentation (ρ i) σ)]
    (hρ : ∀ i (a : G i) (s : K →+* ℂ) (x y : ComplexFiber (M i) s),
      ((h i).fiber s).inner (fiberMap (ρ i a) s x) (fiberMap (ρ i a) s y) =
        ((h i).fiber s).inner x y) :
    (piTensor h).IsSemistable ∧ (piTensor h).dual.IsSemistable := by
  let b := Basis.piTensorProduct (fun i => Module.Free.chooseBasis K (K ⊗[𝓞 K] M i))
  let : Nontrivial (⨂[K] i, K ⊗[𝓞 K] M i) := b.repr.symm.injective.nontrivial
  let : Nontrivial (K ⊗[𝓞 K] (⨂[𝓞 K] i, M i)) :=
    (Tensor.baseChangeEquiv (𝓞 K) K M).symm.injective.nontrivial
  let : Representation.IsIrreducible
      (independentPiRepresentation (fun i => complexRepresentation (ρ i) σ)) :=
    isIrreducible_independentPi _
  let : Representation.IsIrreducible (complexRepresentation (independentPiRepresentation ρ) σ) :=
    isIrreducible_of_equiv (complexPiRepresentationEquiv ρ σ)
  exact ⟨(piTensor h).isSemistable_of_complex_irreducible (independentPiRepresentation ρ) σ
      (piTensor_action_inner h ρ hρ),
    (piTensor h).isSemistable_dual_of_complex_irreducible (independentPiRepresentation ρ) σ
      (piTensor_action_inner h ρ hρ)⟩

end HermitianMetric
end BostConjecture.Arithmetic
