/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Geometry.Contraction.Metric
public import BostConjecture.Geometry.Contraction.BaseChange
public import BostConjecture.Arithmetic.Tensor.Metric
public import BostConjecture.Arithmetic.Submodule.Metric

/-!
# The canonical pairing on intrinsic Hermitian fibers

The integral pairing is identified with its realization in the canonical
complex fibers. The induced and dual Hermitian forms give its intrinsic
contraction estimate.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module NumberField PiTensorProduct Arithmetic
open scoped TensorProduct

/-- A constant stalk rank is the dimension after extension to a field. -/
theorem scalarExtension_finrank_of_rankAtStalk
    {R F M : Type*} [CommRing R] [Field F] [Algebra R F]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    {a : ℕ} (ha : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = a) :
    Module.finrank F (F ⊗[R] M) = a := by
  let p : PrimeSpectrum F := ⟨⊥, inferInstance⟩
  simpa [Module.rankAtStalk_eq_finrank_of_free] using
    (Module.rankAtStalk_baseChange (R := R) (M := M) p).trans
      (ha (p.comap (algebraMap R F)))

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
  (E : ι → Type*) [∀ j, AddCommGroup (E j)] [∀ j, Module (𝓞 K) (E j)]
  (hE : ∀ j, HermitianMetric (K := K) (E j)) (σ : K →+* ℂ)

variable {V : Type*} [AddCommGroup V] [Module (𝓞 K) V]
  (i : V →ₗ[𝓞 K] (⨂[𝓞 K] j, E j)) (hi : Function.Injective i)

/-- The actual complex fiber inclusion is isometric for the intrinsic induced metric. -/
def tensorSubmoduleFiberIsometry :
  letI : ∀ j, InnerProductSpace.Core ℂ (ComplexFiber (E j) σ) := fun j => (hE j).fiber σ
  letI : ∀ j, NormedAddCommGroup (ComplexFiber (E j) σ) := fun j =>
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber (E j) σ)
  letI : ∀ j, InnerProductSpace ℂ (ComplexFiber (E j) σ) := fun j =>
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber (E j) σ))
  letI := Tensor.hilbertCore (fun j => ComplexFiber (E j) σ)
  letI := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ⨂[ℂ] j, ComplexFiber (E j) σ)
  letI : SeminormedAddCommGroup (⨂[ℂ] j, ComplexFiber (E j) σ) :=
    (inferInstance : NormedAddCommGroup (⨂[ℂ] j, ComplexFiber (E j) σ)).toSeminormedAddCommGroup
  letI := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (⨂[ℂ] j, ComplexFiber (E j) σ))
  letI := ((HermitianMetric.piTensor hE).pullback i hi).fiber σ
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber V σ)
  letI := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber V σ))
  ComplexFiber V σ →ₗᵢ[ℂ] (⨂[ℂ] j, ComplexFiber (E j) σ) := by
  letI : ∀ j, InnerProductSpace.Core ℂ (ComplexFiber (E j) σ) := fun j => (hE j).fiber σ
  letI : ∀ j, NormedAddCommGroup (ComplexFiber (E j) σ) := fun j =>
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber (E j) σ)
  letI : ∀ j, InnerProductSpace ℂ (ComplexFiber (E j) σ) := fun j =>
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber (E j) σ))
  letI := Tensor.hilbertCore (fun j => ComplexFiber (E j) σ)
  letI := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ⨂[ℂ] j, ComplexFiber (E j) σ)
  letI : SeminormedAddCommGroup (⨂[ℂ] j, ComplexFiber (E j) σ) :=
    (inferInstance : NormedAddCommGroup (⨂[ℂ] j, ComplexFiber (E j) σ)).toSeminormedAddCommGroup
  letI := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (⨂[ℂ] j, ComplexFiber (E j) σ))
  letI := ((HermitianMetric.piTensor hE).pullback i hi).fiber σ
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber V σ)
  letI := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber V σ))
  exact LinearMap.isometryOfInner
    ((tensorFiberEquiv E σ).toLinearMap ∘ₗ fiberMap i σ) (fun _ _ => rfl)

variable [∀ j, Module.Finite (𝓞 K) (E j)] [∀ j, Module.Projective (𝓞 K) (E j)]
  [Module.Finite (𝓞 K) V] [Module.Projective (𝓞 K) V]
  {n s l : ℕ} {a k : ι → ℕ}

local instance (t : ∀ j, OAI.Saxl.Tableau n (Specht.rectangle (a j) (k j))) :
    ∀ j, AddCommGroup
      ((⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
        ((𝓞 K) ⊗[ℤ] Specht.orbitLattice (t j))) :=
  fun _ => Module.addCommMonoidToAddCommGroup (𝓞 K)

local instance (t : ∀ j, OAI.Saxl.Tableau n (Specht.rectangle (a j) (k j))) :
    ∀ j, Module (𝓞 K)
      ((⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
        ((𝓞 K) ⊗[ℤ] Specht.orbitLattice (t j))) := fun _ => inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The scalar extension of the actual integral pairing is contracting for the
intrinsic induced metric and the canonical determinant and orbit-lattice forms. -/
theorem canonicalPairing_fiber_le
    (hk : ∀ j, 0 < k j)
    (t : ∀ j, OAI.Saxl.Tableau n (Specht.rectangle (a j) (k j)))
    (ha : ∀ j (p : PrimeSpectrum (𝓞 K)), Module.rankAtStalk (Dual (𝓞 K) (E j)) p = a j)
    (hl : 0 < l) (v : OAI.Saxl.Tableau n (Specht.rectangle s l))
    (hs : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk V p = s) :
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  letI : ∀ j, InnerProductSpace.Core ℂ (ComplexFiber (E j) σ) := fun j => (hE j).fiber σ
  letI : ∀ j, NormedAddCommGroup (ComplexFiber (E j) σ) := fun j =>
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber (E j) σ)
  letI : ∀ j, InnerProductSpace ℂ (ComplexFiber (E j) σ) := fun j =>
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber (E j) σ))
  letI : ∀ j, InnerProductSpace.Core ℂ (Dual ℂ (ComplexFiber (E j) σ)) :=
    fun j => Tensor.dualCore (ComplexFiber (E j) σ)
  letI : ∀ j, NormedAddCommGroup (Dual ℂ (ComplexFiber (E j) σ)) := fun j =>
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := Dual ℂ (ComplexFiber (E j) σ))
  letI : ∀ j, InnerProductSpace ℂ (Dual ℂ (ComplexFiber (E j) σ)) := fun j =>
    InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (Dual ℂ (ComplexFiber (E j) σ)))
  letI := ((HermitianMetric.piTensor hE).pullback i hi).fiber σ
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber V σ)
  letI := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber V σ))
  ∀ (bV : OrthonormalBasis (Fin s) ℂ (ComplexFiber V σ) :=
      (stdOrthonormalBasis ℂ (ComplexFiber V σ)).reindex
        (finCongr (scalarExtension_finrank_of_rankAtStalk hs)))
    (b : ∀ j, OrthonormalBasis (Fin (a j)) ℂ (Dual ℂ (ComplexFiber (E j) σ)) :=
      fun j => (stdOrthonormalBasis ℂ (Dual ℂ (ComplexFiber (E j) σ))).reindex
        (finCongr (((Arithmetic.dualBaseChangeEquiv (𝓞 K) ℂ (E j)).finrank_eq).symm.trans
          (scalarExtension_finrank_of_rankAtStalk (ha j)))))
    (z : ℂ ⊗[𝓞 K] ((⨂[𝓞 K] (_ : Fin l), ⋀[𝓞 K]^s V) ⊗[𝓞 K]
      ((𝓞 K) ⊗[ℤ] Specht.orbitLattice v)))
    (u : ℂ ⊗[𝓞 K] (⨂[𝓞 K] j,
      (⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
        ((𝓞 K) ⊗[ℤ] Specht.orbitLattice (t j)))),
    let z' := determinantTwistBaseChangeEquiv (R := 𝓞 K) (S := ℂ) (M := V)
      (Specht.orbitLattice v) l s z
    let u' := dualDeterminantTensorBaseChange (R := 𝓞 K) (S := ℂ) E t u
    ‖Arithmetic.dualBaseChangeMap (𝓞 K) ℂ
      (⨂[𝓞 K] j, (⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
        ((𝓞 K) ⊗[ℤ] Specht.orbitLattice (t j)))
      ((canonicalPairing E hk t ha hl v hs i).baseChange ℂ z) u‖ ≤
      Real.sqrt (((Tensor.binaryCore
        (Tensor.tensorCore (fun _ : Fin l => Arithmetic.ComplexDeterminant.core bV))
        (latticeComplexCore v)).inner z' z').re) *
      Real.sqrt (((Tensor.tensorCore (fun j => Tensor.binaryCore
        (Tensor.tensorCore (fun _ : Fin (k j) => Arithmetic.ComplexDeterminant.core (b j)))
        (latticeComplexCore (t j)))).inner u' u').re) := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : ∀ j, InnerProductSpace.Core ℂ (ComplexFiber (E j) σ) := fun j => (hE j).fiber σ
  let : ∀ j, NormedAddCommGroup (ComplexFiber (E j) σ) := fun j =>
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber (E j) σ)
  let : ∀ j, InnerProductSpace ℂ (ComplexFiber (E j) σ) := fun j =>
    InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber (E j) σ))
  let : ∀ j, InnerProductSpace.Core ℂ (Dual ℂ (ComplexFiber (E j) σ)) :=
    fun j => Tensor.dualCore (ComplexFiber (E j) σ)
  let : ∀ j, NormedAddCommGroup (Dual ℂ (ComplexFiber (E j) σ)) := fun j =>
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := Dual ℂ (ComplexFiber (E j) σ))
  let : ∀ j, InnerProductSpace ℂ (Dual ℂ (ComplexFiber (E j) σ)) := fun j =>
    InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ (Dual ℂ (ComplexFiber (E j) σ)))
  let := ((HermitianMetric.piTensor hE).pullback i hi).fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber V σ)
  let := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber V σ))
  intro bV b z u
  have he := canonicalPairing_baseChange (R := 𝓞 K) (S := ℂ) E hk t ha
    (fun j => (b j).toBasis) hl v hs bV.toBasis i z u
  have hb := freeDeterminantPairing_le (fun j => ComplexFiber (E j) σ)
    (tensorSubmoduleFiberIsometry E hE σ i hi) hl v bV hk t b
    (determinantTwistBaseChangeEquiv (R := 𝓞 K) (S := ℂ) (M := V)
      (Specht.orbitLattice v) l s z)
    (dualDeterminantTensorBaseChange (R := 𝓞 K) (S := ℂ) E t u)
  refine Eq.trans_le ?_ hb
  apply congrArg (norm : ℂ → ℝ)
  refine he.trans ?_
  congr 1

end BostConjecture.Geometry
