/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Specht.DeterminantRepresentation
public import BostConjecture.Geometry.Descent.Metric
public import BostConjecture.Arithmetic.Representation.IndependentPiSemistable

/-!
# The actual determinant–Specht Hermitian bundle

The canonical metric is induced by the projective determinant inclusion.
Its permutation action is isometric in every complex fiber and irreducible
at one complex embedding, proving intrinsic arithmetic semistability.

Reference: this paper, Lemma 6.1, pages 8–9.
-/

@[expose] public section

noncomputable section

open Module NumberField TensorProduct
open scoped MonoidAlgebra

namespace BostConjecture.Arithmetic.Specht

open BostConjecture.Specht

variable {K M : Type*} [Field K] [NumberField K] [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] {n a k : ℕ}

local instance (t : OAI.Saxl.Tableau n (rectangle a k)) :
    AddCommGroup ((⨂[𝓞 K] (_ : Fin k), ⋀[𝓞 K]^a M) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice t)) := Module.addCommMonoidToAddCommGroup (𝓞 K)

/-- The canonical metric is induced by the actual projective determinant inclusion. -/
def determinantMetric (h : HermitianMetric K M) (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (rectangle a k))
    (ha : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk M p = a) :
    HermitianMetric K ((⨂[𝓞 K] (_ : Fin k), ⋀[𝓞 K]^a M) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice t)) :=
  (HermitianMetric.piTensor (fun _ : Fin n => h)).pullback
    (Geometry.projectiveDeterminantMap hk t ha)
    (Geometry.projectiveDeterminantMap_injective hk t ha)

omit [NumberField K] in
/-- The concrete determinant representation is irreducible at every complex embedding. -/
theorem determinant_complex_irreducible (t : OAI.Saxl.Tableau n (rectangle a k))
    (ha : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk M p = a) (σ : K →+* ℂ) :
    Representation.IsIrreducible
      (complexRepresentation (determinantRepresentation (R := 𝓞 K) (M := M) t) σ) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  exact determinantRepresentation_irreducible_of_rankAtStalk t ha

/-- Nonvanishing of the complex Specht fiber proves positivity of generic rank. -/
theorem determinant_generic_nontrivial (t : OAI.Saxl.Tableau n (rectangle a k))
    (ha : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk M p = a) :
    Nontrivial (K ⊗[𝓞 K] ((⨂[𝓞 K] (_ : Fin k), ⋀[𝓞 K]^a M) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice t))) := by
  let σ : K →+* ℂ := Classical.choice inferInstance
  let ρ := complexRepresentation (determinantRepresentation (R := 𝓞 K) (M := M) t) σ
  let : Representation.IsIrreducible ρ := determinant_complex_irreducible t ha σ
  let : Nontrivial (ComplexFiber ((⨂[𝓞 K] (_ : Fin k), ⋀[𝓞 K]^a M) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice t)) σ) :=
    IsSimpleModule.nontrivial ℂ[Equiv.Perm (Fin n)] ρ.asModule
  apply Module.nontrivial_of_finrank_pos (R := K)
  simpa only [← complexFiber_finrank _ σ] using Module.finrank_pos

/-- Position permutations are isometries for the actual induced determinant metric. -/
theorem determinantMetric_action_inner (h : HermitianMetric K M) (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (rectangle a k))
    (ha : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk M p = a)
    (g : Equiv.Perm (Fin n)) (σ : K →+* ℂ)
    (x y : ComplexFiber ((⨂[𝓞 K] (_ : Fin k), ⋀[𝓞 K]^a M) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice t)) σ) :
    ((determinantMetric h hk t ha).fiber σ).inner
      (fiberMap (determinantRepresentation t g) σ x)
      (fiberMap (determinantRepresentation t g) σ y) =
        ((determinantMetric h hk t ha).fiber σ).inner x y := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let f := Geometry.projectiveDeterminantMap hk t ha
  let e := PiTensorProduct.reindex (𝓞 K) (fun _ : Fin n => M) g
  have he : f ∘ₗ determinantRepresentation t g = e.toLinearMap ∘ₗ f :=
    LinearMap.ext (projectiveDeterminantMap_equivariant hk t ha g)
  have he' : f.baseChange ℂ ∘ₗ (determinantRepresentation t g).baseChange ℂ =
      e.toLinearMap.baseChange ℂ ∘ₗ f.baseChange ℂ := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, he]
  have he'' (z : ComplexFiber ((⨂[𝓞 K] (_ : Fin k), ⋀[𝓞 K]^a M) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice t)) σ) :
      tensorFiberEquiv (fun _ : Fin n => M) σ
        (fiberMap f σ (fiberMap (determinantRepresentation t g) σ z)) =
      PiTensorProduct.reindex ℂ (fun _ : Fin n => ComplexFiber M σ) g
        (tensorFiberEquiv (fun _ : Fin n => M) σ (fiberMap f σ z)) := by
    change Tensor.baseChangeEquiv (𝓞 K) ℂ (fun _ : Fin n => M)
      (f.baseChange ℂ ((determinantRepresentation t g).baseChange ℂ z)) = _
    rw [show f.baseChange ℂ ((determinantRepresentation t g).baseChange ℂ z) =
      e.toLinearMap.baseChange ℂ (f.baseChange ℂ z) from LinearMap.congr_fun he' z]
    exact Tensor.baseChangeEquiv_reindex (𝓞 K) ℂ g _
  change (Tensor.hilbertCore (fun _ : Fin n => ComplexFiber M σ)).inner
    (tensorFiberEquiv (fun _ : Fin n => M) σ
      (fiberMap f σ (fiberMap (determinantRepresentation t g) σ x)))
    (tensorFiberEquiv (fun _ : Fin n => M) σ
      (fiberMap f σ (fiberMap (determinantRepresentation t g) σ y))) =
    (Tensor.hilbertCore (fun _ : Fin n => ComplexFiber M σ)).inner
      (tensorFiberEquiv (fun _ : Fin n => M) σ (fiberMap f σ x))
      (tensorFiberEquiv (fun _ : Fin n => M) σ (fiberMap f σ y))
  rw [he'', he'']
  exact Tensor.hilbertCore_reindex_inner (fun _ : Fin n => ComplexFiber M σ) g _ _

/-- The actual induced metric equals the prescribed determinant and lattice
Gram metric in every archimedean fiber. -/
theorem determinantMetric_fiber_inner (h : HermitianMetric K M) (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (rectangle a k))
    (ha : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk M p = a) (σ : K →+* ℂ) :
    letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
    letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
    letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
    letI := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
    ∀ (b : OrthonormalBasis (Fin a) ℂ (ComplexFiber M σ))
      (x y : ComplexFiber ((⨂[𝓞 K] (_ : Fin k), ⋀[𝓞 K]^a M) ⊗[𝓞 K]
        (𝓞 K ⊗[ℤ] orbitLattice t)) σ),
      ((determinantMetric h hk t ha).fiber σ).inner x y =
        (Tensor.binaryCore
          (Tensor.tensorCore (fun _ : Fin k => ComplexDeterminant.core b))
          (Geometry.latticeComplexCore t)).inner
            (Geometry.determinantTwistBaseChangeEquiv (orbitLattice t) k a x)
            (Geometry.determinantTwistBaseChangeEquiv (orbitLattice t) k a y) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  exact fun b x y => Geometry.projectiveDeterminantMap_inner hk t ha b x y

section Family

variable {ι : Type*} [Fintype ι] (E : ι → Type*)
  [∀ j, AddCommGroup (E j)] [∀ j, Module (𝓞 K) (E j)]
  [∀ j, Module.Finite (𝓞 K) (E j)] [∀ j, Module.Projective (𝓞 K) (E j)]
  {r q : ι → ℕ}

local instance (t : ∀ j, OAI.Saxl.Tableau n (rectangle (r j) (q j))) :
    ∀ j, AddCommGroup ((⨂[𝓞 K] (_ : Fin (q j)), ⋀[𝓞 K]^(r j) (E j)) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice (t j))) :=
  fun _ => Module.addCommMonoidToAddCommGroup (𝓞 K)

/-- Independent actions prove semistability of the actual finite family of
determinant–Specht bundles and of its actual Hermitian dual. -/
theorem determinantMetric_piTensor_and_dual_isSemistable
    (h : ∀ j, HermitianMetric K (E j)) (hq : ∀ j, 0 < q j)
    (t : ∀ j, OAI.Saxl.Tableau n (rectangle (r j) (q j)))
    (hr : ∀ j (p : PrimeSpectrum (𝓞 K)), Module.rankAtStalk (E j) p = r j) :
    (HermitianMetric.piTensor (fun j => determinantMetric (h j) (hq j) (t j) (hr j))).IsSemistable ∧
      (HermitianMetric.piTensor
        (fun j => determinantMetric (h j) (hq j) (t j) (hr j))).dual.IsSemistable := by
  let σ : K →+* ℂ := Classical.choice inferInstance
  let : ∀ j, Nontrivial (K ⊗[𝓞 K]
      ((⨂[𝓞 K] (_ : Fin (q j)), ⋀[𝓞 K]^(r j) (E j)) ⊗[𝓞 K]
        (𝓞 K ⊗[ℤ] orbitLattice (t j)))) :=
    fun j => determinant_generic_nontrivial (t j) (hr j)
  let : ∀ j, Representation.IsIrreducible
      (complexRepresentation (determinantRepresentation (R := 𝓞 K) (M := E j) (t j)) σ) :=
    fun j => determinant_complex_irreducible (t j) (hr j) σ
  exact HermitianMetric.isSemistable_piTensor_and_dual_of_complex_irreducible
    (fun j => determinantMetric (h j) (hq j) (t j) (hr j))
    (fun j => determinantRepresentation (t j)) σ
    (fun j => determinantMetric_action_inner (h j) (hq j) (t j) (hr j))

end Family

end BostConjecture.Arithmetic.Specht
