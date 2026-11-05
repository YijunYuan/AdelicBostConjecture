module

public import BostConjecture.Geometry.IntrinsicContraction

/-! # The canonical pairing in the actual dual fiber norm -/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module NumberField PiTensorProduct Arithmetic
open scoped TensorProduct

section BaseChange

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [Fintype ι]
  (E : ι → Type*) [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
  [∀ j, Module.Finite R (E j)] [∀ j, Module.Projective R (E j)]
  {n : ℕ} {a k : ι → ℕ}
  (t : ∀ j, OAI.Saxl.Tableau n (Specht.rectangle (a j) (k j)))

local instance : ∀ j, AddCommGroup
    ((⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t j))) :=
  fun _ => Module.addCommMonoidToAddCommGroup R

local instance : ∀ j, Module R
    ((⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t j))) := fun _ => inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The transport of all dual determinant factors is a genuine scalar-extension
identification, so it transports their positive tensor form. -/
theorem dualDeterminantTensorBaseChange_bijective :
    Function.Bijective (dualDeterminantTensorBaseChange (R := R) (S := S) E t) := by
  let e := (Tensor.baseChangeEquiv R S (fun j =>
    (⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t j)))).trans
    (PiTensorProduct.congr (fun j => LinearEquiv.ofBijective
      (dualDeterminantTwistBaseChange (R := R) (S := S) (M := E j)
        (Specht.orbitLattice (t j)) (k j) (a j))
      (dualDeterminantTwistBaseChange_bijective (Specht.orbitLattice (t j)) (k j) (a j))))
  change Function.Bijective e
  exact e.bijective

end BaseChange

section FiberCore

variable {R ι : Type*} [CommRing R] [Algebra R ℂ] [Fintype ι]
  (E : ι → Type*) [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
  [∀ j, Module.Finite R (E j)] [∀ j, Module.Projective R (E j)]
  [∀ j, InnerProductSpace.Core ℂ (Dual ℂ (ℂ ⊗[R] E j))]
  {n : ℕ} {a k : ι → ℕ}
  (t : ∀ j, OAI.Saxl.Tableau n (Specht.rectangle (a j) (k j)))

local instance : ∀ j, NormedAddCommGroup (Dual ℂ (ℂ ⊗[R] E j)) := fun j =>
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := Dual ℂ (ℂ ⊗[R] E j))

local instance : ∀ j, InnerProductSpace ℂ (Dual ℂ (ℂ ⊗[R] E j)) := fun j =>
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (Dual ℂ (ℂ ⊗[R] E j)))

variable
  (b : ∀ j, OrthonormalBasis (Fin (a j)) ℂ (Dual ℂ (ℂ ⊗[R] E j)))

local instance : ∀ j, AddCommGroup
    ((⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t j))) :=
  fun _ => Module.addCommMonoidToAddCommGroup R

local instance : ∀ j, Module R
    ((⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t j))) := fun _ => inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The prescribed determinant/lattice tensor form on the actual complex fiber.
Positivity follows from the proved injectivity of canonical scalar transport. -/
@[instance_reducible]
def dualDeterminantFiberCore : InnerProductSpace.Core ℂ
    (ℂ ⊗[R] (⨂[R] j, (⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t j)))) := by
  let c := Tensor.tensorCore (fun j => Tensor.binaryCore
    (Tensor.tensorCore (fun _ : Fin (k j) => Arithmetic.ComplexDeterminant.core (b j)))
    (latticeComplexCore (t j)))
  let f := dualDeterminantTensorBaseChange (R := R) (S := ℂ) E t
  exact
    { inner := fun x y => c.inner (f x) (f y)
      conj_inner_symm := fun _ _ => c.conj_inner_symm _ _
      re_inner_nonneg := fun _ => c.re_inner_nonneg _
      add_left := by intros; simp only [map_add, c.add_left]
      smul_left := by intros; simp only [map_smul, c.smul_left]
      definite := by
        intro x hx
        apply (dualDeterminantTensorBaseChange_bijective E t).injective
        simpa only [map_zero] using c.definite (f x) hx }

end FiberCore

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι]
  (E : ι → Type*) [∀ j, AddCommGroup (E j)] [∀ j, Module (𝓞 K) (E j)]
  (hE : ∀ j, HermitianMetric (K := K) (E j)) (σ : K →+* ℂ)

variable {V : Type*} [AddCommGroup V] [Module (𝓞 K) V]
  (i : V →ₗ[𝓞 K] (⨂[𝓞 K] j, E j)) (hi : Function.Injective i)

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
/-- The actual canonical pairing has norm at most one in the operator dual
of the prescribed intrinsic determinant fiber metric. -/
theorem canonicalPairing_fiber_norm_le
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
          (scalarExtension_finrank_of_rankAtStalk (ha j))))),
  letI := dualDeterminantFiberCore (R := 𝓞 K) E t b
  letI := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ℂ ⊗[𝓞 K] (⨂[𝓞 K] j, (⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
      ((𝓞 K) ⊗[ℤ] Specht.orbitLattice (t j))))
  letI : SeminormedAddCommGroup (ℂ ⊗[𝓞 K] (⨂[𝓞 K] j, (⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
      ((𝓞 K) ⊗[ℤ] Specht.orbitLattice (t j)))) :=
    (inferInstance : NormedAddCommGroup (ℂ ⊗[𝓞 K] (⨂[𝓞 K] j, (⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
      ((𝓞 K) ⊗[ℤ] Specht.orbitLattice (t j))))).toSeminormedAddCommGroup
  letI := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ℂ ⊗[𝓞 K] (⨂[𝓞 K] j, (⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
      ((𝓞 K) ⊗[ℤ] Specht.orbitLattice (t j)))))
  ∀ (z : ℂ ⊗[𝓞 K] ((⨂[𝓞 K] (_ : Fin l), ⋀[𝓞 K]^s V) ⊗[𝓞 K]
      ((𝓞 K) ⊗[ℤ] Specht.orbitLattice v))),
    let z' := determinantTwistBaseChangeEquiv (R := 𝓞 K) (S := ℂ) (M := V)
      (Specht.orbitLattice v) l s z
    let f := Arithmetic.dualBaseChangeMap (𝓞 K) ℂ (⨂[𝓞 K] j, (⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
      ((𝓞 K) ⊗[ℤ] Specht.orbitLattice (t j)))
      ((canonicalPairing E hk t ha hl v hs i).baseChange ℂ z)
    Real.sqrt (((Tensor.dualCore (ℂ ⊗[𝓞 K] (⨂[𝓞 K] j, (⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
      ((𝓞 K) ⊗[ℤ] Specht.orbitLattice (t j))))).inner f f).re) ≤
      Real.sqrt (((Tensor.binaryCore
        (Tensor.tensorCore (fun _ : Fin l => Arithmetic.ComplexDeterminant.core bV))
        (latticeComplexCore v)).inner z' z').re) := by
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
  intro bV b
  let := dualDeterminantFiberCore (R := 𝓞 K) E t b
  let := InnerProductSpace.Core.toNormedAddCommGroup
    (𝕜 := ℂ) (F := ℂ ⊗[𝓞 K] (⨂[𝓞 K] j, (⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
      ((𝓞 K) ⊗[ℤ] Specht.orbitLattice (t j))))
  let : SeminormedAddCommGroup (ℂ ⊗[𝓞 K] (⨂[𝓞 K] j, (⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
      ((𝓞 K) ⊗[ℤ] Specht.orbitLattice (t j)))) :=
    (inferInstance : NormedAddCommGroup (ℂ ⊗[𝓞 K] (⨂[𝓞 K] j, (⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
      ((𝓞 K) ⊗[ℤ] Specht.orbitLattice (t j))))).toSeminormedAddCommGroup
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ℂ ⊗[𝓞 K] (⨂[𝓞 K] j, (⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
      ((𝓞 K) ⊗[ℤ] Specht.orbitLattice (t j)))))
  intro z
  apply Tensor.dualCore_norm_le _ _ (Real.sqrt_nonneg _)
  intro u
  exact canonicalPairing_fiber_le E hE σ i hi hk t ha hl v hs bV b z u

end BostConjecture.Geometry
