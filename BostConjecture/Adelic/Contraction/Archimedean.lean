/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Adelic.Specht.Bundle
public import BostConjecture.Adelic.Slope.DeterminantSpecht
public import BostConjecture.Adelic.Geometry.Plucker
public import BostConjecture.Adelic.Contraction.Tensor
public import BostConjecture.Geometry.Descent.Embedding
public import ArakelovGeometry.AdelicVectorBundle.Determinant.HermitianBasis

/-!
# Archimedean determinant–Specht isometry

Orthonormal tensor coordinates preserve the integral word Gram norm over every
`RCLike` field. This includes both real and complex Archimedean completions,
with their given absolute values and without normalizing alternating tensors.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Adelic.Contraction

open Module ArakelovGeometry Specht OAI.Saxl
open BostConjecture.Geometry
open scoped TensorProduct

section WordNorm

local instance (m : ℕ) : DecidableEq (Fin m) := Classical.decEq _

variable {L E : Type*} [RCLike L] [NormedAddCommGroup E]
  [InnerProductSpace L E] {n a k : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- Substitution of an orthonormal frame preserves exactly the word Gram norm.
The sum is over all words, not over an integral basis of the Specht lattice. -/
theorem orthogonal_freeLatticeMap_norm (hk : 0 < k)
    (t : Tableau n (rectangle a k)) (b : OrthonormalBasis (Fin a) L E)
    (z : L ⊗[ℤ] orbitLattice t) :
    orthogonalTensorSeminorm (fun _ : Fin n => b) (freeLatticeMap hk t b.toBasis z) =
      Real.sqrt (∑ w, ‖wordCoordinates L t z w‖ ^ 2) := by
  classical
  simp only [orthogonalTensorSeminorm, Seminorm.comp_apply, coe_normSeminorm,
    LinearEquiv.coe_coe]
  rw [PiLp.norm_eq_of_L2]
  congr 1
  simp only [orthogonalTensorCoordinates, LinearEquiv.trans_apply,
    freeLatticeMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    tensorCoordinates, LinearEquiv.apply_symm_apply]
  exact @Fintype.sum_equiv _ _ ℝ _ _ _ (rectangleAlphabetEquiv hk).symm _ _
    (fun _ => rfl)

end WordNorm

section DeterminantGenerator

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {a k : ℕ}

/-- A fixed basis wedge generates its determinant tensor power, with coordinate
one. This includes the empty tensor power. -/
theorem determinantPowerCoordinates_basis (b : Basis (Fin a) R M) :
    determinantPowerCoordinates k b
      (⨂ₜ[R] (_ : Fin k), exteriorPower.ιMulti R a b) = 1 := by
  simp [Basis.det_self]

/-- Every determinant twist has a unique lattice vector after fixing a frame.
This is an algebraic decomposition on the entire tensor source. -/
theorem exists_determinantPower_tmul (b : Basis (Fin a) R M)
    (x : (⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] N) :
    ∃ z : N, x = (⨂ₜ[R] (_ : Fin k), exteriorPower.ιMulti R a b) ⊗ₜ[R] z := by
  let e := (LinearEquiv.rTensor N (determinantPowerCoordinates k b)).trans
    (TensorProduct.lid R N)
  refine ⟨e x, e.injective ?_⟩
  simp only [e, LinearEquiv.trans_apply, LinearEquiv.rTensor_tmul,
    determinantPowerCoordinates_basis, TensorProduct.lid_tmul, one_smul]

end DeterminantGenerator

section ScalarTransport

variable {K L E A : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup E] [Module K E] [AddCommGroup A] {a k : ℕ}

/-- The algebraic determinant-twist identification transports its normalized
generators to the actual exterior, tensor, and lattice completed fibres. -/
theorem determinantTwistBaseChangeEquiv_symm_tprod
    (η : Fin k → ⋀[L]^a (L ⊗[K] E)) (z : L ⊗[ℤ] A) :
    (determinantTwistBaseChangeEquiv (R := K) (S := L) (M := E) A k a).symm
      ((⨂ₜ[L] q, η q) ⊗ₜ[L] z) =
    (TensorProduct.AlgebraTensorModule.distribBaseChange K L
      (⨂[K] (_ : Fin k), ⋀[K]^a E) (K ⊗[ℤ] A)).symm
      (((tensorBaseChangeEquiv K L (fun _ : Fin k => ⋀[K]^a E)).symm
        (⨂ₜ[L] q, (exteriorBaseChangeEquiv K L E a).symm (η q))) ⊗ₜ[L]
          (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ K L L A).symm z) := by
  simp [determinantTwistBaseChangeEquiv, determinantPowerBaseChangeEquiv,
    exteriorBaseChangeEquiv_eq, ← BostConjecture.Adelic.Geometry.tensorBaseChangeEquiv_eq]

end ScalarTransport

section Completed

universe u v

variable {K : Type u} [Field K] [CharZero K] {S : AdelicStructure.{u, v} K}
  {E : Type u} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (ξ : NormFamily S E)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hξ : ξ.IsHermitian hN) {n k : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- The word isometry uses the prescribed norms on both actual completed
fibres, and the canonical cancellation of the intermediate field. -/
theorem orthogonal_freeLatticeMap_completed_norm
    (hk : 0 < k) (t : Tableau n (rectangle (finrank K E) k))
    {ι : Type*} [Fintype ι] (c : Basis ι ℤ (orbitLattice t))
    (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    letI := hN ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    letI := ξ.fibreNormedAddCommGroup ω
    letI := ξ.fibreNormedSpace ω
    letI := hξ.fibreInnerProductSpace ω hω
    ∀ (b : OrthonormalBasis (Fin (finrank K E)) (S.ϕ ω).Completion
        ((S.ϕ ω).Completion ⊗[K] E))
      (x : (S.ϕ ω).Completion ⊗[K] (K ⊗[ℤ] orbitLattice t)),
    (NormFamily.orthogonalTensor (fun _ : Fin n => ξ) hN (fun _ => hξ)).norm ω
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion (fun _ : Fin n => E)).symm
        (freeLatticeMap hk t b.toBasis
          (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ K (S.ϕ ω).Completion
            (S.ϕ ω).Completion (orbitLattice t) x))) =
      (latticeNormFamily S t c).norm ω x := by
  let := hN ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := ξ.fibreNormedAddCommGroup ω
  let := ξ.fibreNormedSpace ω
  let := hξ.fibreInnerProductSpace ω hω
  intro b x
  rw [NormFamily.orthogonalTensor_norm_of_infinite]
  change orthogonalTensorSeminorm
    (fun _ : Fin n => stdOrthonormalBasis (S.ϕ ω).Completion
      ((S.ϕ ω).Completion ⊗[K] E))
    ((tensorBaseChangeEquiv K (S.ϕ ω).Completion (fun _ : Fin n => E))
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion (fun _ : Fin n => E)).symm _)) = _
  rw [LinearEquiv.apply_symm_apply,
    orthogonalTensorSeminorm_eq _ (fun _ : Fin n => b),
    orthogonal_freeLatticeMap_norm, latticeNormFamily_norm_infinite S t c ω hω]
  congr 1
  simp only [fibreWordCoordinates_cancel]
  congr 2
  exact Subsingleton.elim _ _

end Completed

section Bundle

universe u v

variable {K : Type u} [Field K] [CharZero K] {S : AdelicStructure.{u, v} K}
  {E : Type u} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  (V : AdelicVectorBundle S E)
  (hN : ∀ ω ∈ S.Ωinf, IsRCLikeNormedField (S.ϕ ω).Completion)
  (hcount : S.HasCommonCountableDenseSubfield) (hV : V.IsHermitian hN)

set_option backward.isDefEq.respectTransparency false in
/-- On determinant pure tensors the actual auxiliary norm is the product of
the actual determinant norms and the completed Specht norm, at every place. -/
theorem determinantSpechtBundle_norm_tprod {n k : ℕ}
    (t : Tableau n (rectangle (finrank K E) k))
    (c : Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice t))) ℤ (orbitLattice t))
    (ω : S.Ω)
    (η : Fin k → ⋀[(S.ϕ ω).Completion]^(finrank K E) ((S.ϕ ω).Completion ⊗[K] E))
    (z : (S.ϕ ω).Completion ⊗[ℤ] orbitLattice t) :
    (determinantSpechtBundle V hN hcount k t c).norm ω
      ((determinantTwistBaseChangeEquiv (R := K) (S := (S.ϕ ω).Completion) (M := E)
        (orbitLattice t) k (finrank K E)).symm ((⨂ₜ[(S.ϕ ω).Completion] q, η q)
          ⊗ₜ[(S.ϕ ω).Completion] z)) =
      (∏ q, V.toNormFamily.determinant.norm ω
        ((exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm (η q))) *
      (latticeNormFamily S t c).norm ω
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ K (S.ϕ ω).Completion
          (S.ϕ ω).Completion (orbitLattice t)).symm z) := by
  rw [determinantTwistBaseChangeEquiv_symm_tprod]
  change (NormFamily.orthogonalTensorPair _ _ hN
    (determinantPower_isHermitian V (Or.inr hcount) hN k)
    (latticeBundle_isHermitian S t c hN hcount)).norm ω _ = _
  rw [NormFamily.orthogonalTensorPair_norm_tmul_completed]
  congr 1
  change (NormFamily.orthogonalTensor _ hN _).norm ω _ = _
  rw [NormFamily.orthogonalTensor_norm_tprod]
  rfl

omit [CharZero K] in
set_option backward.isDefEq.respectTransparency false in
/-- The power of an orthonormal determinant generator has norm one for the
actual adelic determinant tensor power. -/
theorem determinantPower_norm_orthonormalBasis (k : ℕ) (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    letI := hN ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    letI := V.toNormFamily.fibreNormedAddCommGroup ω
    letI := V.toNormFamily.fibreNormedSpace ω
    letI := hV.fibreInnerProductSpace ω hω
    ∀ b : OrthonormalBasis (Fin (finrank K E)) (S.ϕ ω).Completion
        ((S.ϕ ω).Completion ⊗[K] E),
      (determinantPower V (Or.inr hcount) hN k).norm ω
        ((tensorBaseChangeEquiv K (S.ϕ ω).Completion
          (fun _ : Fin k => ⋀[K]^(finrank K E) E)).symm
            (⨂ₜ[(S.ϕ ω).Completion] (_ : Fin k),
              (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
                (exteriorPower.ιMulti (S.ϕ ω).Completion _ b))) = 1 := by
  let := hN ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := V.toNormFamily.fibreNormedAddCommGroup ω
  let := V.toNormFamily.fibreNormedSpace ω
  let := hV.fibreInnerProductSpace ω hω
  intro b
  change (NormFamily.orthogonalTensor _ hN _).norm ω _ = 1
  rw [NormFamily.orthogonalTensor_norm_tprod]
  simp only [AdelicVectorBundle.determinantOfMeasurableBase_toNormFamily,
    hV.determinant_norm_orthonormalBasis V.toNormFamily ω hω b, Finset.prod_const_one]

set_option backward.isDefEq.respectTransparency false in
/-- Tensoring with the completed orthonormal determinant generator leaves the
actual Specht norm unchanged. -/
theorem determinantSpechtBundle_norm_generator {n k : ℕ}
    (t : Tableau n (rectangle (finrank K E) k))
    (c : Basis (Fin (finrank K (K ⊗[ℤ] orbitLattice t))) ℤ (orbitLattice t))
    (ω : S.Ω) (hω : ω ∈ S.Ωinf) :
    letI := hN ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    letI := V.toNormFamily.fibreNormedAddCommGroup ω
    letI := V.toNormFamily.fibreNormedSpace ω
    letI := hV.fibreInnerProductSpace ω hω
    ∀ (b : OrthonormalBasis (Fin (finrank K E)) (S.ϕ ω).Completion
        ((S.ϕ ω).Completion ⊗[K] E))
      (x : (S.ϕ ω).Completion ⊗[K] (K ⊗[ℤ] orbitLattice t)),
      (determinantSpechtBundle V hN hcount k t c).norm ω
        ((TensorProduct.AlgebraTensorModule.distribBaseChange K (S.ϕ ω).Completion
          (⨂[K] (_ : Fin k), ⋀[K]^(finrank K E) E) (K ⊗[ℤ] orbitLattice t)).symm
          (((tensorBaseChangeEquiv K (S.ϕ ω).Completion
            (fun _ : Fin k => ⋀[K]^(finrank K E) E)).symm
              (⨂ₜ[(S.ϕ ω).Completion] (_ : Fin k),
                (exteriorBaseChangeEquiv K (S.ϕ ω).Completion E _).symm
                  (exteriorPower.ιMulti (S.ϕ ω).Completion _ b)))
            ⊗ₜ[(S.ϕ ω).Completion] x)) = (latticeNormFamily S t c).norm ω x := by
  let := hN ω hω
  let := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
  let := V.toNormFamily.fibreNormedAddCommGroup ω
  let := V.toNormFamily.fibreNormedSpace ω
  let := hV.fibreInnerProductSpace ω hω
  intro b x
  change (NormFamily.orthogonalTensorPair _ _ hN
    (determinantPower_isHermitian V (Or.inr hcount) hN k)
    (latticeBundle_isHermitian S t c hN hcount)).norm ω _ = _
  rw [NormFamily.orthogonalTensorPair_norm_tmul_completed,
    determinantPower_norm_orthonormalBasis V hN hcount hV k ω hω b, one_mul]
  rfl

end Bundle

end BostConjecture.Adelic.Contraction
