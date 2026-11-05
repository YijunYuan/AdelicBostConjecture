module

public import BostConjecture.Arithmetic.DeterminantContraction

/-!
# Isometry invariance of intrinsic determinant degree

Apply the proved determinant contraction inequality to an integral
isomorphism and its inverse. All pairings are on the actual complex fibers.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic.HermitianMetric

variable {K : Type*} [Field K] [NumberField K]
variable {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N] [Module.Finite (𝓞 K) N]
    [Module.Projective (𝓞 K) N]

/-- An integral isomorphism preserving the fiber forms preserves intrinsic degree. -/
lemma degree_eq_of_equiv (h : HermitianMetric (K := K) M)
    (g : HermitianMetric (K := K) N) (e : M ≃ₗ[𝓞 K] N)
    (he : ∀ (σ : K →+* ℂ) (x y : ComplexFiber M σ),
      (g.fiber σ).inner (fiberMap e.toLinearMap σ x) (fiberMap e.toLinearMap σ y) =
        (h.fiber σ).inner x y) : h.degree = g.degree := by
  have hr := (e.baseChange (𝓞 K) K M N).finrank_eq
  apply le_antisymm
  · exact h.degree_le_of_injective g e.toLinearMap e.injective hr
      (fun σ x => le_of_eq (congrArg (fun z : ℂ => Real.sqrt z.re) (he σ x x)))
  · apply g.degree_le_of_injective h e.symm.toLinearMap e.symm.injective hr.symm
    intro σ x
    have hn := he σ (fiberMap e.symm.toLinearMap σ x) (fiberMap e.symm.toLinearMap σ x)
    have hi : fiberMap e.toLinearMap σ (fiberMap e.symm.toLinearMap σ x) = x := by
      let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
      exact (e.baseChange (𝓞 K) ℂ M N).apply_symm_apply x
    rw [hi] at hn
    exact le_of_eq (congrArg (fun z : ℂ => Real.sqrt z.re) hn.symm)

end BostConjecture.Arithmetic.HermitianMetric
