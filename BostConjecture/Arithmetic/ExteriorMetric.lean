module

public import BostConjecture.Arithmetic.ExteriorMap
public import BostConjecture.Arithmetic.TensorCompatibility
public import BostConjecture.Balanced.ExteriorMetric

/-!
# Intrinsic Hermitian exterior powers

Canonical exterior scalar extension transports the checked complex Gram metric
to each arithmetic exterior module. Conjugation is proved on spanning wedges.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct exteriorPower
open scoped InnerProductSpace

namespace BostConjecture.Arithmetic

variable {K : Type*} [Field K]
variable {M : Type*} [AddCommGroup M] [Module (𝓞 K) M]

/-- The canonical complex fiber equivalence for an arbitrary exterior degree. -/
def exteriorFiberEquiv (M : Type*) [AddCommGroup M] [Module (𝓞 K) M]
    (σ : K →+* ℂ) (r : ℕ) :
    ComplexFiber (⋀[𝓞 K]^r M) σ ≃ₗ[ℂ] (⋀[ℂ]^r (ComplexFiber M σ)) :=
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  exteriorPower.baseChangeEquiv (𝓞 K) M ℂ r

@[simp]
lemma exteriorFiberEquiv_section (σ : K →+* ℂ) (r : ℕ) (x : Fin r → M) :
    exteriorFiberEquiv M σ r (fiberSection _ σ (ιMulti (𝓞 K) r x)) =
      ιMulti ℂ r (fiberSection M σ ∘ x) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  exact exteriorPower.baseChangeEquiv_apply_tmul (𝓞 K) M ℂ r x

variable {N : Type*} [AddCommGroup N] [Module (𝓞 K) N]

/-- Naturality of exterior scalar extension on all complex vectors. -/
lemma exteriorMap_fiber (f : M →ₗ[𝓞 K] N) (σ : K →+* ℂ) (r : ℕ)
    (x : ComplexFiber (⋀[𝓞 K]^r M) σ) :
    exteriorFiberEquiv N σ r (fiberMap (map r f) σ x) =
      map r (fiberMap f σ) (exteriorFiberEquiv M σ r x) := by
  have he : (exteriorFiberEquiv N σ r).toLinearMap.comp (fiberMap (map r f) σ) =
      (map r (fiberMap f σ)).comp (exteriorFiberEquiv M σ r).toLinearMap := by
    apply LinearMap.ext_on_range (span_fiberSection σ)
    intro y
    exact exteriorMap_section f σ r y
  exact LinearMap.congr_fun he x

namespace HermitianMetric

variable [Module.Finite (𝓞 K) M]

/-- The exterior Gram form on the actual arithmetic complex fiber. -/
@[instance_reducible]
def exteriorFiber (h : HermitianMetric (K := K) M) (r : ℕ) (σ : K →+* ℂ) :
    InnerProductSpace.Core ℂ (ComplexFiber (⋀[𝓞 K]^r M) σ) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let := NormedAddCommGroup.induced _ _ (exteriorFiberEquiv M σ r)
    (exteriorFiberEquiv M σ r).injective
  let := InnerProductSpace.induced (exteriorFiberEquiv M σ r).toLinearMap
  exact InnerProductSpace.toCore

/-- The cross Gram formula on arbitrary complex wedges. -/
lemma exteriorFiber_inner_ιMulti (h : HermitianMetric (K := K) M) (r : ℕ)
    (σ : K →+* ℂ) (x y : Fin r → ComplexFiber M σ) :
    (h.exteriorFiber r σ).inner
      ((exteriorFiberEquiv M σ r).symm (ιMulti ℂ r x))
      ((exteriorFiberEquiv M σ r).symm (ιMulti ℂ r y)) =
      (Matrix.of fun i j => (h.fiber σ).inner (x i) (y j)).det := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  change inner ℂ ((exteriorFiberEquiv M σ r) ((exteriorFiberEquiv M σ r).symm _))
    ((exteriorFiberEquiv M σ r) ((exteriorFiberEquiv M σ r).symm _)) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact Balanced.exterior_inner_ιMulti x y

/-- The exterior form on pure integral wedges. -/
lemma exteriorFiber_inner_wedge (h : HermitianMetric (K := K) M) (r : ℕ)
    (σ : K →+* ℂ) (x y : Fin r → M) :
    (h.exteriorFiber r σ).inner (fiberSection _ σ (ιMulti (𝓞 K) r x))
      (fiberSection _ σ (ιMulti (𝓞 K) r y)) =
      (Matrix.of fun i j => (h.fiber σ).inner
        (fiberSection M σ (x i)) (fiberSection M σ (y j))).det := by
  have hs (z : Fin r → M) : fiberSection _ σ (ιMulti (𝓞 K) r z) =
      (exteriorFiberEquiv M σ r).symm (ιMulti ℂ r (fiberSection M σ ∘ z)) := by
    apply (exteriorFiberEquiv M σ r).injective
    simp only [LinearEquiv.apply_symm_apply, exteriorFiberEquiv_section]
  rw [hs x, hs y, h.exteriorFiber_inner_ιMulti]
  rfl

/-- The exterior forms inherit conjugation compatibility on every integral
section, proved from the spanning integral wedges. -/
lemma exteriorFiber_conjugate (h : HermitianMetric (K := K) M)
    (r : ℕ) (σ : K →+* ℂ) (x y : ⋀[𝓞 K]^r M) :
    (h.exteriorFiber r (ComplexEmbedding.conjugate σ)).inner
        (fiberSection _ (ComplexEmbedding.conjugate σ) x)
        (fiberSection _ (ComplexEmbedding.conjugate σ) y) =
      star ((h.exteriorFiber r σ).inner (fiberSection _ σ x) (fiberSection _ σ y)) := by
  let : InnerProductSpace.Core ℂ (ComplexFiber (⋀[𝓞 K]^r M) σ) :=
    h.exteriorFiber r σ
  let : InnerProductSpace.Core ℂ
      (ComplexFiber (⋀[𝓞 K]^r M) (ComplexEmbedding.conjugate σ)) :=
    h.exteriorFiber r (ComplexEmbedding.conjugate σ)
  have hx : x ∈ Submodule.span (𝓞 K) (Set.range (ιMulti (𝓞 K)
      r (M := M))) := by
    rw [ιMulti_span]
    trivial
  have hy : y ∈ Submodule.span (𝓞 K) (Set.range (ιMulti (𝓞 K)
      r (M := M))) := by
    rw [ιMulti_span]
    trivial
  refine Submodule.span_induction₂ (p := fun x y _ _ =>
    (h.exteriorFiber r (ComplexEmbedding.conjugate σ)).inner
        (fiberSection _ (ComplexEmbedding.conjugate σ) x)
        (fiberSection _ (ComplexEmbedding.conjugate σ) y) =
      star ((h.exteriorFiber r σ).inner (fiberSection _ σ x) (fiberSection _ σ y)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    simp only [exteriorFiber_inner_wedge, h.conjugate]
    exact ((starRingEnd ℂ).map_det _).symm
  · intro y _
    simp only [fiberSection, tmul_zero, InnerProductSpace.Core.inner_zero_left, star_zero]
  · intro x _
    simp only [fiberSection, tmul_zero, InnerProductSpace.Core.inner_zero_right, star_zero]
  · intro x y z _ _ _ hx hy
    simpa only [fiberSection, tmul_add, InnerProductSpace.Core.inner_add_left, star_add]
      using congrArg₂ (· + ·) hx hy
  · intro x y z _ _ _ hy hz
    simpa only [fiberSection, tmul_add, InnerProductSpace.Core.inner_add_right, star_add]
      using congrArg₂ (· + ·) hy hz
  · intro a x y _ _ hxy
    simp only [fiberSection_smul, InnerProductSpace.Core.inner_smul_left,
      ComplexEmbedding.conjugate_coe_eq, map_mul, hxy, RCLike.star_def]
  · intro a x y _ _ hxy
    simp only [fiberSection_smul, InnerProductSpace.Core.inner_smul_right,
      ComplexEmbedding.conjugate_coe_eq, map_mul, hxy, RCLike.star_def]

/-- The intrinsic Hermitian exterior metric on the integral exterior module. -/
def exterior (h : HermitianMetric (K := K) M) (r : ℕ) :
    HermitianMetric (K := K) (⋀[𝓞 K]^r M) where
  fiber := h.exteriorFiber r
  conjugate := h.exteriorFiber_conjugate r

/-- In top degree the general exterior metric agrees with the determinant metric. -/
lemma exteriorFiber_top_eq (h : HermitianMetric (K := K) M) (σ : K →+* ℂ) :
    h.exteriorFiber (Module.finrank K (K ⊗[𝓞 K] M)) σ = h.determinantFiber σ := by
  apply h.determinantFiber_unique σ
  intro x
  exact congrArg Complex.re (h.exteriorFiber_inner_ιMulti _ σ x x)

/-- An integral map isometric on a fiber induces an isometry on every exterior fiber. -/
lemma exteriorFiber_inner_map [Module.Finite (𝓞 K) N]
    (h : HermitianMetric (K := K) M) (g : HermitianMetric (K := K) N)
    (f : M →ₗ[𝓞 K] N) (r : ℕ) (σ : K →+* ℂ)
    (hf : ∀ x y, (g.fiber σ).inner (fiberMap f σ x) (fiberMap f σ y) =
      (h.fiber σ).inner x y)
    (x y : ComplexFiber (⋀[𝓞 K]^r M) σ) :
    (g.exteriorFiber r σ).inner (fiberMap (map r f) σ x) (fiberMap (map r f) σ y) =
      (h.exteriorFiber r σ).inner x y := by
  let e := exteriorFiberEquiv M σ r
  let d := exteriorFiberEquiv N σ r
  have hm (z : ⋀[ℂ]^r (ComplexFiber M σ)) :
      fiberMap (map r f) σ (e.symm z) = d.symm (map r (fiberMap f σ) z) := by
    apply d.injective
    rw [LinearEquiv.apply_symm_apply, exteriorMap_fiber, LinearEquiv.apply_symm_apply]
  have he := Tensor.inner_ext_of_span (ιMulti ℂ r)
    (ιMulti_span ℂ r (ComplexFiber M σ)) (g.exteriorFiber r σ) (h.exteriorFiber r σ)
    ((fiberMap (map r f) σ).comp e.symm.toLinearMap) e.symm.toLinearMap
    (fun a b => by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hm, map_apply_ιMulti]
      rw [g.exteriorFiber_inner_ιMulti, h.exteriorFiber_inner_ιMulti]
      congr 1
      ext i j
      exact hf _ _) (e x) (e y)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using he

variable [NumberField K]

/-- The actual determinant inclusion of any integral submodule is isometric. -/
lemma determinant_submodule_sectionNorm (h : HermitianMetric (K := K) M)
    (P : Submodule (𝓞 K) M) (σ : K →+* ℂ) (x : DeterminantLine (K := K) P) :
    (h.exterior (Module.finrank K (K ⊗[𝓞 K] P))).sectionNorm σ
        (map _ P.subtype x) = (h.submodule P).determinant.sectionNorm σ x := by
  unfold sectionNorm
  change Real.sqrt ((h.exteriorFiber _ σ).inner _ _).re =
    Real.sqrt (((h.submodule P).determinantFiber σ).inner _ _).re
  rw [← fiberMap_section, ← (h.submodule P).exteriorFiber_top_eq]
  congr 2
  exact (h.submodule P).exteriorFiber_inner_map h P.subtype _ σ (fun _ _ => rfl) _ _

end HermitianMetric
end BostConjecture.Arithmetic
