/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Exterior.Product
public import BostConjecture.Geometry.Determinant.Coordinates
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Determinants of products

The canonical exterior product sends the tensor of two determinant generators
to the determinant generator of the concatenated basis. Localization descends
this calculation to finite projective modules over a domain and gives the
actual integral determinant isomorphism over the ring of integers.
-/

@[expose] public section

noncomputable section

open Module TensorProduct

namespace exteriorPower

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {a b : ℕ}

lemma prodBasis_reindex (p : Basis (Fin a) R M) (q : Basis (Fin b) R N) :
    Fin.append (fun i => (p i, 0)) (fun j => (0, q j)) =
      (p.prod q).reindex finSumFinEquiv := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

/-- The top exterior product multiplies the two determinant coordinates. -/
lemma prodMap_coordinates (p : Basis (Fin a) R M) (q : Basis (Fin b) R N)
    (x : ⋀[R]^a M) (y : ⋀[R]^b N) :
    BostConjecture.Geometry.determinantCoordinates ((p.prod q).reindex finSumFinEquiv)
        (prodMap R M N a b (x ⊗ₜ[R] y)) =
      BostConjecture.Geometry.determinantCoordinates p x *
        BostConjecture.Geometry.determinantCoordinates q y := by
  obtain ⟨r, rfl⟩ := (BostConjecture.Geometry.determinantCoordinates p).symm.surjective x
  obtain ⟨s, rfl⟩ := (BostConjecture.Geometry.determinantCoordinates q).symm.surjective y
  simp only [BostConjecture.Geometry.determinantCoordinates_symm_apply,
    smul_tmul, tmul_smul, map_smul, prodMap_ιMulti, prodBasis_reindex,
    BostConjecture.Geometry.determinantCoordinates_ιMulti, Basis.det_self,
    smul_eq_mul, mul_one]
  exact mul_comm s r

/-- The canonical determinant product is an isomorphism in every finite free frame. -/
lemma prodMap_bijective_of_basis (p : Basis (Fin a) R M) (q : Basis (Fin b) R N) :
    Function.Bijective (prodMap R M N a b) := by
  let d := BostConjecture.Geometry.determinantCoordinates ((p.prod q).reindex finSumFinEquiv)
  let e := (TensorProduct.congr (BostConjecture.Geometry.determinantCoordinates p)
    (BostConjecture.Geometry.determinantCoordinates q)) ≪≫ₗ
      TensorProduct.lid R R ≪≫ₗ d.symm
  have he : prodMap R M N a b = e.toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    apply d.injective
    change d (prodMap R M N a b (x ⊗ₜ[R] y)) =
      d (d.symm (BostConjecture.Geometry.determinantCoordinates p x *
        BostConjecture.Geometry.determinantCoordinates q y))
    simpa only [LinearEquiv.apply_symm_apply] using prodMap_coordinates p q x y
  rw [he]
  exact e.bijective

variable (S : Type*) [CommRing S] [Algebra R S]

/-- Bijectivity of the exterior product after scalar extension can be checked
on the exterior powers of the extended summands. -/
lemma prodMap_baseChange_bijective
    (h : Function.Bijective (prodMap S (S ⊗[R] M) (S ⊗[R] N) a b)) :
    Function.Bijective ((prodMap R M N a b).baseChange S) := by
  let e := (AlgebraTensorModule.distribBaseChange R S (⋀[R]^a M) (⋀[R]^b N)) ≪≫ₗ
    TensorProduct.congr (baseChangeEquiv R M S a) (baseChangeEquiv R N S b)
  let p := TensorProduct.prodRight R S S M N
  let t := (map (a + b) p.toLinearMap).comp (baseChangeEquiv R (M × N) S (a + b)).toLinearMap
  have ht : Function.Bijective t :=
    (show Function.Bijective (map (a + b) p.toLinearMap) from
      ⟨map_injective p.symm.toLinearMap (by
        apply LinearMap.ext
        exact fun x => p.symm_apply_apply x), map_surjective p.surjective⟩).comp
        (baseChangeEquiv R (M × N) S (a + b)).bijective
  have he : t.comp ((prodMap R M N a b).baseChange S) =
      (prodMap S (S ⊗[R] M) (S ⊗[R] N) a b).comp e.toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro s z
    have hz : t (1 ⊗ₜ[R] prodMap R M N a b z) =
        prodMap S (S ⊗[R] M) (S ⊗[R] N) a b (e (1 ⊗ₜ[R] z)) := by
      induction z using TensorProduct.inductionOn with
      | tmul x y =>
        simpa [t, e, p] using prodMap_baseChange_section R M N S a b x y
      | add x y hx hy => simp only [map_add, tmul_add, hx, hy]
    rw [show s ⊗ₜ[R] z = s • ((1 : S) ⊗ₜ[R] z) by
      simp only [smul_tmul', smul_eq_mul, mul_one], map_smul, map_smul]
    exact congrArg (s • ·) hz
  have hc : Function.Bijective (t.comp ((prodMap R M N a b).baseChange S)) := by
    rw [he]
    exact h.comp e.bijective
  exact ⟨fun x y hxy => hc.injective (congrArg t hxy), fun y => by
    obtain ⟨x, hx⟩ := hc.surjective (t y)
    exact ⟨x, ht.injective hx⟩⟩

end exteriorPower

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N]

/-- Maximal-local scalar extension detects bijectivity. -/
lemma bijective_of_baseChange_maximal (f : M →ₗ[R] N)
    (h : ∀ (p : Ideal R) [p.IsMaximal],
      Function.Bijective (f.baseChange (Localization.AtPrime p))) : Function.Bijective f := by
  apply bijective_of_isLocalized_maximal
    (fun p _ => Localization.AtPrime p ⊗[R] M)
    (fun p _ => TensorProduct.mk R (Localization.AtPrime p) M 1)
    (fun p _ => Localization.AtPrime p ⊗[R] N)
    (fun p _ => TensorProduct.mk R (Localization.AtPrime p) N 1) f
  intro p hp
  have he : IsLocalizedModule.map p.primeCompl
      (TensorProduct.mk R (Localization.AtPrime p) M 1)
      (TensorProduct.mk R (Localization.AtPrime p) N 1) f =
      (f.baseChange (Localization.AtPrime p)).restrictScalars R := by
    apply IsLocalizedModule.linearMap_ext p.primeCompl
      (TensorProduct.mk R (Localization.AtPrime p) M 1)
      (TensorProduct.mk R (Localization.AtPrime p) N 1)
    apply LinearMap.ext
    exact fun x => IsLocalizedModule.map_apply p.primeCompl
      (TensorProduct.mk R (Localization.AtPrime p) M 1)
      (TensorProduct.mk R (Localization.AtPrime p) N 1) f x
  rw [he]
  exact h p

end LinearMap

namespace exteriorPower

variable {R M N : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]

/-- The actual determinant product is bijective for finite projective modules
over a domain; global freeness is not required. -/
lemma prodMap_bijective :
    Function.Bijective (prodMap R M N (Module.finrank R M) (Module.finrank R N)) := by
  refine LinearMap.bijective_of_baseChange_maximal (R := R)
    (prodMap R M N (Module.finrank R M) (Module.finrank R N)) ?_
  intro p hp
  let S := Localization.AtPrime p
  let : Module.Free S (S ⊗[R] M) := Module.free_of_flat_of_isLocalRing
  let : Module.Free S (S ⊗[R] N) := Module.free_of_flat_of_isLocalRing
  have hm : Module.finrank S (S ⊗[R] M) = Module.finrank R M :=
    (TensorProduct.isBaseChange R M S).finrank_eq
  have hn : Module.finrank S (S ⊗[R] N) = Module.finrank R N :=
    (TensorProduct.isBaseChange R N S).finrank_eq
  apply prodMap_baseChange_bijective S
  exact prodMap_bijective_of_basis (Module.finBasisOfFinrankEq S (S ⊗[R] M) hm)
    (Module.finBasisOfFinrankEq S (S ⊗[R] N) hn)

/-- The canonical determinant product for finite projective modules. -/
def prodEquiv :
    (⋀[R]^(Module.finrank R M) M) ⊗[R] (⋀[R]^(Module.finrank R N) N) ≃ₗ[R]
      ⋀[R]^(Module.finrank R M + Module.finrank R N) (M × N) :=
  LinearEquiv.ofBijective _ prodMap_bijective

end exteriorPower
