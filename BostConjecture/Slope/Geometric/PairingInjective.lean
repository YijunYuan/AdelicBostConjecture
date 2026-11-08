/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Specht.DeterminantBundle
public import BostConjecture.Geometry.Contraction.Basic

/-!
# Injectivity of the actual nonzero canonical pairing

Equivariance and irreducibility turn a nonzero determinant pairing into
an injection. Scalar extension detects its kernel over the ring of integers.
-/

@[expose] public section

noncomputable section

open Module NumberField TensorProduct

namespace BostConjecture.Slope.Geometric

open Arithmetic Arithmetic.Specht BostConjecture.Specht

universe u

variable {K V : Type u} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  (E : ι → Type u) [∀ j, AddCommGroup (E j)] [∀ j, Module (𝓞 K) (E j)]
  [∀ j, Module.Finite (𝓞 K) (E j)] [∀ j, Module.Projective (𝓞 K) (E j)]
  [AddCommGroup V] [Module (𝓞 K) V]
  [Module.Finite (𝓞 K) V] [Module.Projective (𝓞 K) V]
  {n s l : ℕ} {a k : ι → ℕ}

local instance (t : ∀ j, OAI.Saxl.Tableau n (rectangle (a j) (k j))) :
    ∀ j, AddCommGroup ((⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice (t j))) := fun _ => Module.addCommMonoidToAddCommGroup (𝓞 K)

local instance (v : OAI.Saxl.Tableau n (rectangle s l)) :
    AddCommGroup ((⨂[𝓞 K] (_ : Fin l), ⋀[𝓞 K]^s V) ⊗[𝓞 K]
      (𝓞 K ⊗[ℤ] orbitLattice v)) := Module.addCommMonoidToAddCommGroup (𝓞 K)

/-- Nonvanishing and the actual simultaneous equivariance force injectivity of
the canonical pairing over the original ring; no injectivity is assumed of this map. -/
theorem canonicalPairing_injective
    (hk : ∀ j, 0 < k j) (t : ∀ j, OAI.Saxl.Tableau n (rectangle (a j) (k j)))
    (ha : ∀ j (p : PrimeSpectrum (𝓞 K)), Module.rankAtStalk (Dual (𝓞 K) (E j)) p = a j)
    (hl : 0 < l) (v : OAI.Saxl.Tableau n (rectangle s l))
    (hs : ∀ p : PrimeSpectrum (𝓞 K), Module.rankAtStalk V p = s)
    (i : V →ₗ[𝓞 K] (⨂[𝓞 K] j, E j))
    (hne : Geometry.canonicalPairing E hk t ha hl v hs i ≠ 0) :
    Function.Injective (Geometry.canonicalPairing E hk t ha hl v hs i) := by
  let f := Geometry.canonicalPairing E hk t ha hl v hs i
  let ρ : Representation (𝓞 K) (Equiv.Perm (Fin n))
      (⨂[𝓞 K] j, (⨂[𝓞 K] (_ : Fin (k j)), ⋀[𝓞 K]^(a j) (Dual (𝓞 K) (E j))) ⊗[𝓞 K]
        (𝓞 K ⊗[ℤ] orbitLattice (t j))) := (independentPiRepresentation (fun j =>
    determinantRepresentation (R := 𝓞 K) (M := Dual (𝓞 K) (E j)) (t j))).comp
      { toFun := fun g _ => g
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
  let F : (determinantRepresentation (R := 𝓞 K) (M := V) v).IntertwiningMap ρ.dual :=
    f.intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g z
      apply LinearMap.ext
      exact fun u => Geometry.canonicalPairing_reindex_left E hk t ha hl v hs i g z u)
  let σ : K →+* ℂ := Classical.choice inferInstance
  let : Algebra (𝓞 K) ℂ := (σ.comp (algebraMap (𝓞 K) K)).toAlgebra
  let : Representation.IsIrreducible
      (complexRepresentation (determinantRepresentation (R := 𝓞 K) (M := V) v) σ) :=
    determinant_complex_irreducible v hs σ
  let FC : Representation.IntertwiningMap
      (complexRepresentation (determinantRepresentation (R := 𝓞 K) (M := V) v) σ)
      (complexRepresentation ρ.dual σ) :=
    { toLinearMap := fiberMap f σ
      isIntertwining' g := by
        change f.baseChange ℂ ∘ₗ (determinantRepresentation v g).baseChange ℂ =
          (ρ.dual g).baseChange ℂ ∘ₗ f.baseChange ℂ
        exact (LinearMap.baseChange_comp (A := ℂ) (determinantRepresentation v g) f).symm.trans
          ((congrArg (LinearMap.baseChange ℂ) (F.isIntertwining' g)).trans
            (LinearMap.baseChange_comp (A := ℂ) f (ρ.dual g))) }
  have hFC : FC ≠ 0 := by
    intro hzero
    apply hne
    apply LinearMap.ext
    intro z
    apply fiberSection_injective _ σ
    have hz := congrArg (fun q => q (fiberSection _ σ z)) hzero
    change fiberMap f σ (fiberSection _ σ z) = 0 at hz
    have hz' : fiberSection _ σ (f z) = 0 := (fiberMap_section f σ z).symm.trans hz
    simpa only [LinearMap.zero_apply, fiberSection, TensorProduct.tmul_zero] using hz' 
  have hinj := (Representation.IsIrreducible.injective_or_eq_zero FC).resolve_right hFC
  intro x y hxy
  apply fiberSection_injective _ σ
  apply hinj
  change fiberMap f σ (fiberSection _ σ x) = fiberMap f σ (fiberSection _ σ y)
  simpa only [fiberMap_section, fiberMap_section] using congrArg (fiberSection _ σ) hxy

end BostConjecture.Slope.Geometric
