module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Orthogonal representatives of a linear surjection

A surjection from a finite-dimensional Hermitian space has a canonical
right inverse into the orthogonal complement of its kernel. Pulling back
along this map constructs the quotient Hermitian form without a metric
assumption on the target.
-/

@[expose] public section

noncomputable section

open scoped InnerProductSpace

namespace BostConjecture.Arithmetic
namespace ComplexQuotient

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [FiniteDimensional ℂ E] [AddCommGroup F] [Module ℂ F]

/-- The target of a surjection identified with the orthogonal kernel complement. -/
def orthogonalEquiv (f : E →ₗ[ℂ] F) (hf : Function.Surjective f) :
    F ≃ₗ[ℂ] (LinearMap.ker f)ᗮ :=
  (f.quotKerEquivOfSurjective hf).symm ≪≫ₗ
    (LinearMap.ker f).quotientEquivOfIsCompl _ (LinearMap.ker f).isCompl_orthogonal

/-- The unique orthogonal right inverse of a surjective linear map. -/
def lift (f : E →ₗ[ℂ] F) (hf : Function.Surjective f) : F →ₗ[ℂ] E :=
  (LinearMap.ker f)ᗮ.subtype ∘ₗ (orthogonalEquiv f hf).toLinearMap

lemma lift_mem (f : E →ₗ[ℂ] F) (hf : Function.Surjective f) (y : F) :
    lift f hf y ∈ (LinearMap.ker f)ᗮ := (orthogonalEquiv f hf y).property

@[simp]
lemma map_lift (f : E →ₗ[ℂ] F) (hf : Function.Surjective f) (y : F) :
    f (lift f hf y) = y := by
  change f ((orthogonalEquiv f hf y : (LinearMap.ker f)ᗮ) : E) = y
  have he := (orthogonalEquiv f hf).symm_apply_apply y
  exact he

lemma lift_injective (f : E →ₗ[ℂ] F) (hf : Function.Surjective f) :
    Function.Injective (lift f hf) := Function.LeftInverse.injective (map_lift f hf)

/-- Orthogonality and the image under the surjection uniquely determine a vector. -/
lemma eq_lift (f : E →ₗ[ℂ] F) (hf : Function.Surjective f) {x : E} {y : F}
    (hx : x ∈ (LinearMap.ker f)ᗮ) (hxy : f x = y) : x = lift f hf y := by
  apply sub_eq_zero.mp
  apply (Submodule.disjoint_def.mp (LinearMap.ker f).isCompl_orthogonal.disjoint)
  · change f (x - lift f hf y) = 0
    rw [map_sub, hxy, map_lift, sub_self]
  · exact (LinearMap.ker f)ᗮ.sub_mem hx (lift_mem f hf y)

lemma lift_map (f : E →ₗ[ℂ] F) (hf : Function.Surjective f) (x : E) :
    lift f hf (f x) = (LinearMap.ker f)ᗮ.projection (LinearMap.ker f)
      (LinearMap.ker f).isCompl_orthogonal.symm x := by
  change (((LinearMap.ker f).quotientEquivOfIsCompl _
    (LinearMap.ker f).isCompl_orthogonal
    ((f.quotKerEquivOfSurjective hf).symm (f x))) : E) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply,
    Submodule.quotientEquivOfIsCompl_apply_mk]
  rfl

/-- The orthogonal lift never increases the norm of a representative. -/
lemma norm_lift_map_le (f : E →ₗ[ℂ] F) (hf : Function.Surjective f) (x : E) :
    ‖lift f hf (f x)‖ ≤ ‖x‖ := by
  rw [lift_map]
  have he : (LinearMap.ker f)ᗮᗮ = LinearMap.ker f :=
    (LinearMap.ker f).orthogonal_orthogonal
  simpa only [he] using (LinearMap.ker f)ᗮ.norm_projection_orthogonal_le x

/-- The positive Hermitian form defined by orthogonal representatives. -/
@[instance_reducible]
def core (f : E →ₗ[ℂ] F) (hf : Function.Surjective f) :
    InnerProductSpace.Core ℂ F := by
  letI := NormedAddCommGroup.induced F E (lift f hf) (lift_injective f hf)
  letI := InnerProductSpace.induced (lift f hf)
  exact InnerProductSpace.toCore

lemma core_inner (f : E →ₗ[ℂ] F) (hf : Function.Surjective f) (x y : F) :
    (core f hf).inner x y = inner ℂ (lift f hf x) (lift f hf y) := rfl

end ComplexQuotient
end BostConjecture.Arithmetic
