/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Slope.Geometric.InvariantSlope
public import BostConjecture.Geometry.Plucker.Binary

/-!
# Geometric slope from the actual binary Plücker invariant

A nonvanishing binary Plücker invariant supplies the finite-family
contraction sequence. The geometric slope inequality then applies to
subspaces of a binary tensor product.
-/

@[expose] public section

noncomputable section

open Module NumberField TensorProduct
open scoped BigOperators

namespace BostConjecture.Slope.Geometric

open Arithmetic InvariantTheory

universe u
variable {K V : Type u} [Field K] [NumberField K]
  (E : Unit ⊕ Unit → Type u) [∀ j, AddCommGroup (E j)] [∀ j, Module (𝓞 K) (E j)]
  [∀ j, Module.Finite (𝓞 K) (E j)] [∀ j, Module.Projective (𝓞 K) (E j)]
  (hE : ∀ j, HermitianMetric (K := K) (E j))
  [AddCommGroup V] [Module (𝓞 K) V]
  [Module.Finite (𝓞 K) V] [Module.Projective (𝓞 K) V]
  (i : V →ₗ[𝓞 K] (⨂[𝓞 K] j, E j)) (hi : Function.Injective i)
  {s : ℕ} {a : Unit ⊕ Unit → ℕ}

/-- The binary invariant supplied by geometric semistability feeds the actual
nonzero canonical pairings and hence the intrinsic arithmetic slope inequality. -/
theorem slope_le_of_binary_complex_invariant (hspos : 0 < s) (hapos : ∀ j, 0 < a j)
    (ha : ∀ j (q : PrimeSpectrum (𝓞 K)), Module.rankAtStalk (Dual (𝓞 K) (E j)) q = a j)
    (hs : ∀ q : PrimeSpectrum (𝓞 K), Module.rankAtStalk V q = s)
    (σ : K →+* ℂ) :
  letI : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  ∀ (bV : Basis (Fin s) ℂ (ComplexFiber V σ)) {m : ℕ}
    {p : SymmetricAlgebra ℂ (Dual ℂ
      (⋀[ℂ]^s ((ComplexFiber (E (.inl ())) σ) ⊗[ℂ] (ComplexFiber (E (.inr ())) σ))))},
    0 < m → p ∈ homogeneousInvariants
      (pluckerRepresentation ℂ (ComplexFiber (E (.inl ())) σ) (ComplexFiber (E (.inr ())) σ) s) m →
    polynomialEval (exteriorPower.ιMulti ℂ s (fun j =>
      Tensor.twoFactorEquiv ℂ (fun j => ComplexFiber (E j) σ)
        (((Tensor.baseChangeEquiv (𝓞 K) ℂ E).toLinearMap ∘ₗ i.baseChange ℂ) (bV j)))) p ≠ 0 →
    ((HermitianMetric.piTensor hE).pullback i hi).slope ≤
      (hE (.inl ())).slope + (hE (.inr ())).slope := by
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  intro bV m p hm hp hEval
  let bE j := (Module.finBasis ℂ (Dual ℂ (ComplexFiber (E j) σ))).reindex
    (finCongr (((dualBaseChangeEquiv (𝓞 K) ℂ (E j)).finrank_eq).symm.trans
      (Geometry.scalarExtension_finrank_of_rankAtStalk (ha j))))
  obtain ⟨d₀, hd, _, _, hseq⟩ :=
    Geometry.exists_canonicalPairing_nonzero_sequence_of_binary_invariant
      (F := ℂ) i hspos hapos hm ha hs bV bE hp hEval
  simpa only [Fintype.sum_sum_type, Fintype.sum_unique] using
    slope_le_of_nonzero_pairings E hE i hi hspos hapos ha hs hd hseq

end BostConjecture.Slope.Geometric
