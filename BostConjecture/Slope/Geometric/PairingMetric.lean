/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Specht.DeterminantBundle
public import BostConjecture.Geometry.Contraction.Norm
public import BostConjecture.Tensor.Metric.Map

/-!
# The intrinsic Hermitian metrics of the canonical pairing

The determinant and Specht forms define the source metric for the
canonical pairing. The fiberwise contraction estimates are expressed in
these intrinsic arithmetic metrics.
-/

@[expose] public section

noncomputable section

open Module NumberField TensorProduct

namespace BostConjecture.Slope.Geometric

open Arithmetic Arithmetic.Specht BostConjecture.Specht

section Factor

variable {K M : Type*} [Field K] [NumberField K]
  [AddCommGroup M] [Module (𝓞 K) M]
  [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
  (h : HermitianMetric K M) (σ : K →+* ℂ) {n a k : ℕ}

local instance factorDualDeterminantAddGroup (t : OAI.Saxl.Tableau n (rectangle a k)) :
    AddCommGroup ((⨂[𝓞 K] (_ : Fin k), ⋀[𝓞 K]^a (Dual (𝓞 K) M)) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice t)) := Module.addCommMonoidToAddCommGroup (𝓞 K)

/-- The prescribed complex dual determinant form is the actual canonical
arithmetic metric, through the canonical dual determinant base change. -/
theorem dualDeterminantTwist_inner (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (rectangle a k))
    (ha : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk (Dual (𝓞 K) M) p = a)
    :
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  letI := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  letI : InnerProductSpace.Core ℂ (Dual ℂ (ComplexFiber M σ)) := Tensor.dualCore (ComplexFiber M σ)
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := Dual ℂ (ComplexFiber M σ))
  letI := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (Dual ℂ (ComplexFiber M σ)))
    ∀ (b : OrthonormalBasis (Fin a) ℂ (Dual ℂ (ComplexFiber M σ)))
    (x y : ComplexFiber ((⨂[𝓞 K] (_ : Fin k), ⋀[𝓞 K]^a (Dual (𝓞 K) M)) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice t)) σ),
    (Tensor.binaryCore (Tensor.tensorCore (fun _ : Fin k => ComplexDeterminant.core b))
      (Geometry.latticeComplexCore t)).inner
      (Geometry.dualDeterminantTwistBaseChange (orbitLattice t) k a x)
      (Geometry.dualDeterminantTwistBaseChange (orbitLattice t) k a y) =
        ((determinantMetric h.dual hk t ha).fiber σ).inner x y := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : InnerProductSpace.Core ℂ (Dual ℂ (ComplexFiber M σ)) := Tensor.dualCore (ComplexFiber M σ)
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := Dual ℂ (ComplexFiber M σ))
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (Dual ℂ (ComplexFiber M σ)))
  intro b x y
  have hx := Geometry.projectiveDualDeterminantMap_baseChange hk t ha b.toBasis x
  have hy := Geometry.projectiveDualDeterminantMap_baseChange hk t ha b.toBasis y
  exact (Geometry.freeDeterminantMap_inner hk t b _ _).symm.trans
    ((congrArg₂ (Tensor.hilbertCore (fun _ : Fin n => Dual ℂ (ComplexFiber M σ))).inner
      hx.symm hy.symm).trans
      (Tensor.tensorCore_map_inner (fun _ : Fin n => h.dual.fiber σ)
        (fun _ : Fin n => Tensor.dualCore (ComplexFiber M σ))
        (fun _ => (dualFiberEquiv M σ).toLinearMap) (fun _ _ _ => rfl) _ _))

end Factor

section Family

variable {K ι : Type*} [Field K] [NumberField K] [Fintype ι]
  (E : ι → Type*) [∀ j, AddCommGroup (E j)] [∀ j, Module (𝓞 K) (E j)]
  [∀ j, Module.Finite (𝓞 K) (E j)] [∀ j, Module.Projective (𝓞 K) (E j)]
  (hE : ∀ j, HermitianMetric K (E j)) (σ : K →+* ℂ)
  {n : ℕ} {a k : ι → ℕ}

local instance familyDualDeterminantAddGroup (t : ∀ j, OAI.Saxl.Tableau n (rectangle (a j) (k j))) :
    ∀ j, AddCommGroup ((⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice (t j))) := fun _ => Module.addCommMonoidToAddCommGroup (𝓞 K)

private theorem core_ext {W : Type*} [AddCommGroup W] [Module ℂ W]
    {c d : InnerProductSpace.Core ℂ W} (h : ∀ x y, c.inner x y = d.inner x y) : c = d := by
  have hi : c.inner = d.inner := funext fun x => funext fun y => h x y
  rcases c with ⟨⟨⟨ci⟩, cs, cp, ca, cm⟩, cd⟩
  rcases d with ⟨⟨⟨di⟩, ds, dp, da, dm⟩, dd⟩
  cases hi
  rfl

/-- The prescribed fiber form is the intrinsic arithmetic tensor metric. -/
theorem dualDeterminantFiberCore_eq (hk : ∀ j, 0 < k j)
    (t : ∀ j, OAI.Saxl.Tableau n (rectangle (a j) (k j)))
    (ha : ∀ j (p : PrimeSpectrum (𝓞 K)), Module.rankAtStalk (Dual (𝓞 K) (E j)) p = a j) :
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
  ∀ b : ∀ j, OrthonormalBasis (Fin (a j)) ℂ (Dual ℂ (ComplexFiber (E j) σ)),
    Geometry.dualDeterminantFiberCore (R := 𝓞 K) E t b =
      (HermitianMetric.piTensor
        (fun j => determinantMetric (hE j).dual (hk j) (t j) (ha j))).fiber σ := by
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
  intro b
  apply core_ext
  exact fun x y => Tensor.tensorCore_map_inner
    (fun j => (determinantMetric (hE j).dual (hk j) (t j) (ha j)).fiber σ)
    (fun j => Tensor.binaryCore
      (Tensor.tensorCore (fun _ : Fin (k j) => ComplexDeterminant.core (b j)))
      (Geometry.latticeComplexCore (t j)))
    (fun j => Geometry.dualDeterminantTwistBaseChange (R := 𝓞 K) (S := ℂ) (M := E j)
      (orbitLattice (t j)) (k j) (a j))
    (fun j => dualDeterminantTwist_inner (hE j) σ (hk j) (t j) (ha j) (b j)) _ _

end Family

section Pairing

variable {K ι : Type*} [Field K] [NumberField K] [Fintype ι]
  (E : ι → Type*) [∀ j, AddCommGroup (E j)] [∀ j, Module (𝓞 K) (E j)]
  [∀ j, Module.Finite (𝓞 K) (E j)] [∀ j, Module.Projective (𝓞 K) (E j)]
  (hE : ∀ j, HermitianMetric K (E j))
  {V : Type*} [AddCommGroup V] [Module (𝓞 K) V]
  [Module.Finite (𝓞 K) V] [Module.Projective (𝓞 K) V]
  (i : V →ₗ[𝓞 K] (⨂[𝓞 K] j, E j)) (hi : Function.Injective i)
  {n s l : ℕ} {a k : ι → ℕ}

local instance pairingDualDeterminantAddGroup
    (t : ∀ j, OAI.Saxl.Tableau n (rectangle (a j) (k j))) :
    ∀ j, AddCommGroup ((⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice (t j))) := fun _ => Module.addCommMonoidToAddCommGroup (𝓞 K)

local instance pairingSourceDeterminantAddGroup (v : OAI.Saxl.Tableau n (rectangle s l)) :
    AddCommGroup ((⨂[𝓞 K] (_ : Fin l), ⋀[𝓞 K]^s V) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice v)) := Module.addCommMonoidToAddCommGroup (𝓞 K)

/-- The actual canonical pairing contracts the intrinsic arithmetic metrics
at every complex embedding. -/
theorem canonicalPairing_intrinsic_norm_le (hk : ∀ j, 0 < k j)
    (t : ∀ j, OAI.Saxl.Tableau n (rectangle (a j) (k j)))
    (ha : ∀ j (p : PrimeSpectrum (𝓞 K)), Module.rankAtStalk (Dual (𝓞 K) (E j)) p = a j)
    (hl : 0 < l) (v : OAI.Saxl.Tableau n (rectangle s l))
    (hs : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk V p = s)
    (σ : K →+* ℂ) (z : ComplexFiber
      ((⨂[𝓞 K] (_ : Fin l), ⋀[𝓞 K]^s V) ⊗[𝓞 K] (𝓞 K ⊗[ℤ] orbitLattice v)) σ) :
    Real.sqrt (((HermitianMetric.piTensor (fun j =>
      determinantMetric (hE j).dual (hk j) (t j) (ha j))).dual.fiber σ).inner
        (fiberMap (Geometry.canonicalPairing E hk t ha hl v hs i) σ z)
        (fiberMap (Geometry.canonicalPairing E hk t ha hl v hs i) σ z)).re ≤
      Real.sqrt (((determinantMetric ((HermitianMetric.piTensor hE).pullback i hi)
        hl v hs).fiber σ).inner z z).re := by
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
  let bV := (stdOrthonormalBasis ℂ (ComplexFiber V σ)).reindex
    (finCongr (Geometry.scalarExtension_finrank_of_rankAtStalk hs))
  let b j := (stdOrthonormalBasis ℂ (Dual ℂ (ComplexFiber (E j) σ))).reindex
    (finCongr (((dualBaseChangeEquiv (𝓞 K) ℂ (E j)).finrank_eq).symm.trans
      (Geometry.scalarExtension_finrank_of_rankAtStalk (ha j))))
  have hb := Geometry.canonicalPairing_fiber_norm_le E hE σ i hi hk t ha hl v hs bV b z
  have hc := dualDeterminantFiberCore_eq E hE σ hk t ha b
  let D := ComplexFiber (⨂[𝓞 K] j, (⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
    (𝓞 K ⊗[ℤ] orbitLattice (t j))) σ
  let dn (c : InnerProductSpace.Core ℂ D) (f : Dual ℂ D) : ℝ := by
    letI := c
    letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := D)
    letI := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ D)
    exact Real.sqrt ((Tensor.dualCore D).inner f f).re
  have hd := congrArg (fun c => dn c (dualBaseChangeMap (𝓞 K) ℂ _
    ((Geometry.canonicalPairing E hk t ha hl v hs i).baseChange ℂ z))) hc
  have hs' := congrArg (fun w : ℂ => Real.sqrt w.re)
    (determinantMetric_fiber_inner _ hl v hs σ bV z z)
  exact hd.symm.le.trans (hb.trans_eq hs'.symm)

end Pairing

end BostConjecture.Slope.Geometric
