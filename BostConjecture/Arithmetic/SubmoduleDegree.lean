module

public import BostConjecture.Arithmetic.SumQuotient
public import BostConjecture.Arithmetic.ExactDegree
public import BostConjecture.Arithmetic.SaturationDegree
public import BostConjecture.Arithmetic.TensorCompatibility

/-!
# The degree inequality for sums and intersections

Two actual exact sequences have the same sum quotient. Its quotient norm
from the larger module is smaller, so determinant contraction and exact
degree additivity give supermodularity before saturation.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- Restricting an induced form along a nested inclusion gives the same induced form. -/
lemma pullback_submodule_inclusion (h : HermitianMetric (K := K) M)
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) :
    (h.submodule T).pullback (Submodule.inclusion hPT) (Submodule.inclusion_injective hPT) =
      h.submodule P := by
  apply ext_inner
  intro σ x y
  exact h.submodule_inner_inclusion hPT σ x y

variable [Module.Finite (𝓞 K) M]

/-- Enlarging the space of lifts can only decrease the actual orthogonal quotient norm. -/
lemma pushforward_norm_le_of_inclusion (h : HermitianMetric (K := K) M)
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T)
    {Q : Type*} [AddCommGroup Q] [Module (𝓞 K) Q]
    (q : T →ₗ[𝓞 K] Q) (hq : Function.Surjective q)
    (hp : Function.Surjective (q.comp (Submodule.inclusion hPT)))
    (σ : K →+* ℂ) (z : ComplexFiber Q σ) :
    Real.sqrt (((((h.submodule T).pushforward q hq).fiber σ).inner z z).re) ≤
      Real.sqrt (((((h.submodule P).pushforward (q.comp (Submodule.inclusion hPT)) hp).fiber σ).inner z z).re) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber P σ) := (h.submodule P).fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber P σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber P σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber T σ) := (h.submodule T).fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber T σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber T σ))
  let x := (h.submodule P).fiberLift (q.comp (Submodule.inclusion hPT)) hp σ z
  have he : fiberMap q σ (fiberMap (Submodule.inclusion hPT) σ x) = z := by
    change ((fiberMap q σ).comp (fiberMap (Submodule.inclusion hPT) σ)) x = z
    rw [← fiberMap_comp]
    exact (h.submodule P).fiberMap_fiberLift _ hp σ z
  change ‖(h.submodule T).fiberLift q hq σ z‖ ≤ ‖x‖
  calc
    _ ≤ ‖fiberMap (Submodule.inclusion hPT) σ x‖ := by
      change ‖ComplexQuotient.lift (fiberMap q σ) (fiberMap_surjective q hq σ) z‖ ≤ _
      simpa only [he] using ComplexQuotient.norm_lift_map_le (fiberMap q σ)
        (fiberMap_surjective q hq σ) (fiberMap (Submodule.inclusion hPT) σ x)
    _ = ‖x‖ := congrArg (fun z : ℂ => Real.sqrt z.re)
      (h.submodule_inner_inclusion hPT σ x x)

variable [Module.Projective (𝓞 K) M]

/-- The arithmetic degree inequality for two submodules when the second is saturated. -/
theorem degree_submodule_sup (h : HermitianMetric (K := K) M)
    (U V : Submodule (𝓞 K) M) [Module.IsTorsionFree (𝓞 K) (M ⧸ V)] :
    (h.submodule U).degree + (h.submodule V).degree ≤
      (h.submodule (U ⊓ V)).degree + (h.submodule (U ⊔ V)).degree := by
  let T := U ⊔ V
  let Q := T ⧸ V.comap T.subtype
  let q : T →ₗ[𝓞 K] Q := (V.comap T.subtype).mkQ
  have hq : Function.Surjective q := (V.comap T.subtype).mkQ_surjective
  let f : U →ₗ[𝓞 K] Q := LinearMap.subToSupQuotient U V
  have hf : Function.Surjective f := subToSupQuotient_surjective U V
  let HU := (h.submodule U).pushforward f hf
  let HT := (h.submodule T).pushforward q hq
  have hdU := (h.submodule U).degree_exact
    (Submodule.inclusion (inf_le_left : U ⊓ V ≤ U)) f
    (exact_inf_subToSupQuotient U V) (Submodule.inclusion_injective _) hf
  rw [pullback_submodule_inclusion] at hdU
  have hdT := (h.submodule T).degree_exact
    (Submodule.inclusion (le_sup_right : V ≤ U ⊔ V)) q
    (exact_inclusion_quotient le_sup_right) (Submodule.inclusion_injective _) hq
  rw [pullback_submodule_inclusion] at hdT
  have hdQ : HU.degree ≤ HT.degree := by
    apply HU.degree_le_of_injective HT LinearMap.id Function.injective_id rfl
    intro σ z
    have he : fiberMap (LinearMap.id : Q →ₗ[𝓞 K] Q) σ z = z := by
      let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
      exact LinearMap.congr_fun LinearMap.baseChange_id z
    rw [he]
    exact h.pushforward_norm_le_of_inclusion le_sup_left q hq hf σ z
  change (h.submodule U).degree = (h.submodule (U ⊓ V)).degree + HU.degree at hdU
  change (h.submodule T).degree = (h.submodule V).degree + HT.degree at hdT
  change _ ≤ (h.submodule (U ⊓ V)).degree + (h.submodule T).degree
  linarith

end BostConjecture.Arithmetic.HermitianMetric
