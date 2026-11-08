/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Balanced.PluckerSemistability
public import BostConjecture.Slope.Geometric.BinaryInvariantSlope
public import BostConjecture.Main.TensorSemistability.ArithmeticTensorFiber

/-!
# The geometric slope inequality for an actual balanced tensor submodule

The balanced Plücker vector satisfies the geometric invariant criterion.
Applying the contraction slope bound gives the arithmetic inequality needed
for the extremal tensor submodule.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct Module

namespace BostConjecture.Arithmetic

universe u
variable {K M N : Type u} [Field K] [NumberField K]
    [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]
    [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]

/-- A finite projective integral module has its generic rank at every prime. -/
theorem rankAtStalk_eq_genericRank (q : PrimeSpectrum (𝓞 K)) :
    Module.rankAtStalk M q = Module.finrank K (K ⊗[𝓞 K] M) := by
  let p : PrimeSpectrum K := ⟨⊥, inferInstance⟩
  have he := Module.rankAtStalk_baseChange (R := 𝓞 K) (M := M) p
  rw [Module.rankAtStalk_eq_finrank_of_free] at he
  have hp : p.comap (algebraMap (𝓞 K) K) ≤ q := by
    change Ideal.comap (algebraMap (𝓞 K) K) ⊥ ≤ q.asIdeal
    rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)]
    exact bot_le
  exact (Module.rankAtStalk_eq_of_le_of_finite_of_flat M hp).symm.trans he.symm

omit [NumberField K] [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N] in
/-- The binary and two-factor finite-family scalar-extension maps coincide. -/
theorem twoFactor_baseChange_binaryTensorEquiv (σ : K →+* ℂ)
    (z : ComplexFiber (M ⊗[𝓞 K] N) σ) :
    Tensor.twoFactorEquiv ℂ (fun i => ComplexFiber (binaryTensorFamily M N i) σ)
      (tensorFiberEquiv (binaryTensorFamily M N) σ
        (fiberMap (binaryTensorEquiv (𝓞 K) M N).toLinearMap σ z)) =
      binaryTensorFiberEquiv σ z := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  induction z using TensorProduct.inductionOn with
  | tmul c z =>
    have hz : Tensor.twoFactorEquiv ℂ (fun i => ComplexFiber (binaryTensorFamily M N i) σ)
        (tensorFiberEquiv (binaryTensorFamily M N) σ
          (fiberMap (binaryTensorEquiv (𝓞 K) M N).toLinearMap σ (fiberSection _ σ z))) =
        binaryTensorFiberEquiv σ (fiberSection _ σ z) := by
      induction z using TensorProduct.inductionOn with
      | tmul x y => simp
      | add x y hx hy => simpa only [fiberSection, tmul_add, map_add] using congrArg₂ (· + ·) hx hy
    have hc : c ⊗ₜ[𝓞 K] z = c • fiberSection _ σ z := by simp [fiberSection, smul_tmul']
    simpa only [hc, map_smul] using congrArg (c • ·) hz
  | add x y hx hy => simp only [map_add, hx, hy]

namespace HermitianMetric

/-- The finite-family geometric inequality specialized to the actual binary tensor metric. -/
theorem slope_submodule_tensor_le_of_invariant
    (h : HermitianMetric K M) (k : HermitianMetric K N)
    (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (hrM : 0 < Module.finrank K (K ⊗[𝓞 K] M))
    (hrN : 0 < Module.finrank K (K ⊗[𝓞 K] N))
    {s : ℕ} (hs : Module.finrank K (K ⊗[𝓞 K] P) = s) (hspos : 0 < s)
    (σ : K →+* ℂ) (bV : Basis (Fin s) ℂ (ComplexFiber P σ))
    {d : ℕ} {p : SymmetricAlgebra ℂ (Module.Dual ℂ
      (⋀[ℂ]^s (ComplexFiber M σ ⊗[ℂ] ComplexFiber N σ)))} (hd : 0 < d)
    (hpinv : p ∈ InvariantTheory.homogeneousInvariants
      (InvariantTheory.pluckerRepresentation ℂ (ComplexFiber M σ) (ComplexFiber N σ) s) d) :
    InvariantTheory.polynomialEval (exteriorPower.ιMulti ℂ s (fun j =>
      binaryTensorFiberEquiv σ (fiberMap P.subtype σ (bV j)))) p ≠ 0 →
    ((h ⊗[𝓞 K] k).submodule P).slope ≤ h.slope + k.slope := by
  let f := (binaryTensorFiberEquiv σ).toLinearMap.comp (fiberMap P.subtype σ)
  let E := binaryTensorFamily M N
  let hE : ∀ j, HermitianMetric K (E j) :=
    fun j => Sum.casesOn j (fun _ => h) (fun _ => k)
  let : ∀ j, Module.Finite (𝓞 K) (E j) := fun j =>
    Sum.casesOn j (fun _ => inferInstance) (fun _ => inferInstance)
  let : ∀ j, Module.Projective (𝓞 K) (E j) := fun j =>
    Sum.casesOn j (fun _ => inferInstance) (fun _ => inferInstance)
  let i := (binaryTensorEquiv (𝓞 K) M N).toLinearMap.comp P.subtype
  have hi : Function.Injective i := (binaryTensorEquiv (𝓞 K) M N).injective.comp P.injective_subtype
  let a (j : Unit ⊕ Unit) := Module.finrank K (K ⊗[𝓞 K] E j)
  have ha (j : Unit ⊕ Unit) (q : PrimeSpectrum (𝓞 K)) :
      Module.rankAtStalk (Module.Dual (𝓞 K) (E j)) q = a j := by
    rw [rankAtStalk_eq_genericRank]
    exact (dualBaseChangeEquiv (𝓞 K) K (E j)).finrank_eq.trans Subspace.dual_finrank_eq
  have hs' (q : PrimeSpectrum (𝓞 K)) : Module.rankAtStalk P q = s :=
    (rankAtStalk_eq_genericRank q).trans hs
  have hap (j) : 0 < a j := by cases j <;> assumption
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  have hfiber (x : ComplexFiber P σ) :
      Tensor.twoFactorEquiv ℂ (fun j => ComplexFiber (E j) σ)
        (((Tensor.baseChangeEquiv (𝓞 K) ℂ E).toLinearMap ∘ₗ i.baseChange ℂ) x) = f x := by
    simp only [i, LinearMap.baseChange_comp, LinearMap.comp_apply]
    exact twoFactor_baseChange_binaryTensorEquiv σ (fiberMap P.subtype σ x)
  have hfun : (fun j : Fin s =>
      Tensor.twoFactorEquiv ℂ (fun j => ComplexFiber (E j) σ)
        (((Tensor.baseChangeEquiv (𝓞 K) ℂ E).toLinearMap ∘ₗ i.baseChange ℂ) (bV j))) =
      (fun j => f (bV j)) := funext fun j => hfiber (bV j)
  intro hp
  have hb := BostConjecture.Slope.Geometric.slope_le_of_binary_complex_invariant
    (K := K) (V := P) E hE i hi (s := s) (a := a)
    hspos hap ha hs' σ
  simp only [E, binaryTensorFamily, instAddCommGroupBinaryTensorFamily,
    instModuleBinaryTensorFamily] at hb
  have hb := hb bV hd hpinv
  rw [hfun] at hb
  have hb := hb hp
  have hm : (piTensor hE).pullback i hi = (h ⊗[𝓞 K] k).submodule P := by
    apply ext_inner
    intro τ x y
    change ((piTensor hE).fiber τ).inner (fiberMap i τ x) (fiberMap i τ y) =
      ((piTensor hE).fiber τ).inner
        (fiberMap (binaryTensorEquiv (𝓞 K) M N).toLinearMap τ (fiberMap P.subtype τ x))
        (fiberMap (binaryTensorEquiv (𝓞 K) M N).toLinearMap τ (fiberMap P.subtype τ y))
    simp only [fiberMap, i, LinearMap.baseChange_comp,
      LinearMap.comp_apply]
  rwa [hm] at hb

/-- A positive-rank actual tensor submodule with a balanced complex fiber
satisfies the geometric slope bound. -/
theorem slope_submodule_tensor_le_of_isBalanced
    (h : HermitianMetric K M) (k : HermitianMetric K N)
    (P : Submodule (𝓞 K) (M ⊗[𝓞 K] N))
    (hrM : 0 < Module.finrank K (K ⊗[𝓞 K] M))
    (hrN : 0 < Module.finrank K (K ⊗[𝓞 K] N))
    (hrP : 0 < Module.finrank K (K ⊗[𝓞 K] P)) (σ : K →+* ℂ) :
  letI : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  letI := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  letI : InnerProductSpace.Core ℂ (ComplexFiber N σ) := k.fiber σ
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber N σ)
  letI := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  Balanced.IsBalanced (tensorSubmoduleFiber P σ) →
    ((h ⊗[𝓞 K] k).submodule P).slope ≤ h.slope + k.slope := by
  let : InnerProductSpace.Core ℂ (ComplexFiber M σ) := h.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber M σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber M σ))
  let : InnerProductSpace.Core ℂ (ComplexFiber N σ) := k.fiber σ
  let := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ) (F := ComplexFiber N σ)
  let := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (ComplexFiber N σ))
  intro hbal
  let S := tensorSubmoduleFiber P σ
  let s := Module.finrank ℂ S
  have hs : s = Module.finrank K (K ⊗[𝓞 K] P) := finrank_tensorSubmoduleFiber P σ
  let v := stdOrthonormalBasis ℂ S
  let f := (binaryTensorFiberEquiv σ).toLinearMap.comp (fiberMap P.subtype σ)
  have hf : Function.Injective f := (binaryTensorFiberEquiv σ).injective.comp
    (fiberMap_injective P.subtype P.injective_subtype σ)
  let e : ComplexFiber P σ ≃ₗ[ℂ] S := LinearEquiv.ofInjective f hf
  let bV : Basis (Fin s) ℂ (ComplexFiber P σ) := v.toBasis.map e.symm
  have hbV (j : Fin s) : f (bV j) = (v j : ComplexFiber M σ ⊗[ℂ] ComplexFiber N σ) := by
    change (e (e.symm (v j)) : ComplexFiber M σ ⊗[ℂ] ComplexFiber N σ) = _
    rw [e.apply_symm_apply]
  let z := exteriorPower.ιMulti ℂ s (fun j => (v j : ComplexFiber M σ ⊗[ℂ] ComplexFiber N σ))
  have hz : z ∈ LinearMap.range (exteriorPower.map s S.subtype) :=
    ⟨exteriorPower.ιMulti ℂ s v, by simp [z, Function.comp_def]⟩
  have hz0 : z ≠ 0 := by
    intro he
    have hn := Balanced.plucker_norm_sq S v
    change ‖z‖ ^ 2 = 1 at hn
    have hn0 : ‖z‖ = 0 := norm_eq_zero.mpr he
    rw [hn0] at hn
    norm_num at hn
  have hS : S ≠ ⊥ := by
    intro he
    have hh : s = 0 := by simp [s, he]
    omega
  obtain ⟨_, d, hd, p, hp⟩ := hbal.plucker_semistable hS hz hz0
  apply slope_submodule_tensor_le_of_invariant h k P hrM hrN hs.symm (hs.symm ▸ hrP)
    σ bV hd p.property
  change InvariantTheory.polynomialEval (exteriorPower.ιMulti ℂ s (fun j => f (bV j))) p.val ≠ 0
  simpa only [hbV] using hp

end HermitianMetric

end BostConjecture.Arithmetic
