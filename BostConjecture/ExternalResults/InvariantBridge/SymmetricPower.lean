/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Yijun Yuan
-/
module

public import BostConjecture.ExternalCode.TauCeti.LinearAlgebra.SymmetricPower.Lift
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Symmetric powers with universe-lifted finite indices

The scalar ring and the index of Mathlib `SymmetricPower` share a universe.
Using `ULift (Fin n)` preserves the actual symmetric quotient while allowing
arbitrary coefficient universes. The finite-coordinate maps below recover the
usual degree conventions without restricting the scalar ring.

Adapted from TauCeti revision `3c3a32baea963db05c302adeb307b22baae4de78`,
`TauCeti/LinearAlgebra/SymmetricPower/{Lift,Algebra}.lean`, Apache-2.0, through
this project’s existing selective ports. The adaptation changes only finite
index transport and its proofs; it retains the upstream namespace and quotient.
The intended consumer is `BostConjecture.Geometry.Polynomial.Polarization`.
-/

public section

open scoped TensorProduct

namespace TauCeti.SymmetricPower

universe u v w

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The existing symmetric quotient indexed in the scalar ring's universe. -/
abbrev FinitePower (n : ℕ) := _root_.SymmetricPower R (ULift.{u} (Fin n)) M

/-- Pure symmetric tensors expressed in ordinary finite coordinates. -/
noncomputable def finiteTprod (n : ℕ) :
    MultilinearMap R (fun _ : Fin n ↦ M) (FinitePower R M n) :=
  (_root_.SymmetricPower.tprod R).domDomCongr Equiv.ulift

/-- Permuting finite coordinates does not change their symmetric tensor. -/
theorem finiteTprod_perm (n : ℕ) (m : Fin n → M) (e : Equiv.Perm (Fin n)) :
    finiteTprod R M n (m ∘ e) = finiteTprod R M n m := by
  have h := _root_.SymmetricPower.tprod_equiv
    (R := R) ((Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n).symm.permCongr e)
    (fun i : ULift.{u} (Fin n) ↦ m i.down)
  simpa [finiteTprod, MultilinearMap.domDomCongr_apply, Function.comp_def] using h

/-- The symmetric-power map acts componentwise in finite coordinates. -/
@[simp]
theorem finiteMap_tprod {N : Type w} [AddCommMonoid N] [Module R N]
    (f : M →ₗ[R] N) (n : ℕ) (m : Fin n → M) :
    _root_.SymmetricPower.map f (finiteTprod R M n m) =
      finiteTprod R N n (fun i ↦ f (m i)) := by
  simp [finiteTprod, MultilinearMap.domDomCongr_apply]

variable {R M}

/-- A linear map on the lifted symmetric power is determined by finite pure tensors. -/
theorem finite_ext {N : Type w} [AddCommMonoid N] [Module R N] {n : ℕ}
    {f g : FinitePower R M n →ₗ[R] N}
    (h : ∀ m : Fin n → M, f (finiteTprod R M n m) = g (finiteTprod R M n m)) : f = g := by
  apply _root_.SymmetricPower.ext
  intro m
  simpa [finiteTprod, MultilinearMap.domDomCongr_apply] using h (fun i ↦ m ⟨i⟩)

/-- The universal property in ordinary finite coordinates, over any scalar universe. -/
noncomputable def finiteLift {N : Type w} [AddCommMonoid N] [Module R N] {n : ℕ}
    (f : MultilinearMap R (fun _ : Fin n ↦ M) N)
    (hf : ∀ e : Equiv.Perm (Fin n), f.domDomCongr e = f) :
    FinitePower R M n →ₗ[R] N :=
  _root_.SymmetricPower.lift (f.domDomCongr Equiv.ulift.symm) (by
    intro e
    ext m
    simpa [MultilinearMap.domDomCongr_apply, Function.comp_def, Equiv.ulift] using
      congrArg (fun f : MultilinearMap R (fun _ : Fin n ↦ M) N ↦ f (fun i ↦ m ⟨i⟩))
        (hf ((Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n).permCongr e)))

/-- The finite-coordinate lift takes its prescribed values on pure tensors. -/
@[simp]
theorem finiteLift_tprod {N : Type w} [AddCommMonoid N] [Module R N] {n : ℕ}
    (f : MultilinearMap R (fun _ : Fin n ↦ M) N)
    (hf : ∀ e : Equiv.Perm (Fin n), f.domDomCongr e = f) (m : Fin n → M) :
    finiteLift f hf (finiteTprod R M n m) = f m := by
  simp [finiteLift, finiteTprod, MultilinearMap.domDomCongr_apply]

private theorem finiteTprod_cons_invariant (n : ℕ) (m : M) (e : Equiv.Perm (Fin n)) :
    ((finiteTprod R M (n + 1)).curryLeft m).domDomCongr e =
      (finiteTprod R M (n + 1)).curryLeft m := by
  ext v
  simp only [MultilinearMap.domDomCongr_apply, MultilinearMap.curryLeft_apply]
  rw [← finiteTprod_perm R M (n + 1) (Fin.cons m v)
    (Equiv.Perm.decomposeFin.symm (0, e))]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ i => simp

variable (R M)

/-- Multiplication by one generator in the lifted finite symmetric powers. -/
noncomputable def finiteConsMul (n : ℕ) :
    M →ₗ[R] FinitePower R M n →ₗ[R] FinitePower R M (n + 1) where
  toFun m := finiteLift ((finiteTprod R M (n + 1)).curryLeft m)
    (finiteTprod_cons_invariant n m)
  map_add' m m' := finite_ext fun v ↦ by simp
  map_smul' c m := finite_ext fun v ↦ by simp

/-- Multiplication by a generator prepends it to a pure symmetric tensor. -/
@[simp]
theorem finiteConsMul_tprod (n : ℕ) (m : M) (v : Fin n → M) :
    finiteConsMul R M n m (finiteTprod R M n v) =
      finiteTprod R M (n + 1) (Fin.cons m v) := by
  simp [finiteConsMul, MultilinearMap.curryLeft_apply]

/-- Multiplications by two generators commute. -/
theorem finiteConsMul_comm (n : ℕ) (m m' : M) (x : FinitePower R M n) :
    finiteConsMul R M (n + 1) m (finiteConsMul R M n m' x) =
      finiteConsMul R M (n + 1) m' (finiteConsMul R M n m x) := by
  suffices h : finiteConsMul R M (n + 1) m ∘ₗ finiteConsMul R M n m' =
      finiteConsMul R M (n + 1) m' ∘ₗ finiteConsMul R M n m from LinearMap.congr_fun h x
  apply finite_ext
  intro v
  simp only [LinearMap.comp_apply, finiteConsMul_tprod]
  rw [← finiteTprod_perm R M (n + 2) (Fin.cons m (Fin.cons m' v)) (Equiv.swap 0 1)]
  exact congrArg (finiteTprod R M (n + 2))
    (Matrix.cons_cons_comp_swap_zero_one m m' v)

private noncomputable def finiteAlgebraMultilinear (n : ℕ) :
    MultilinearMap R (fun _ : Fin n ↦ M) (SymmetricAlgebra R M) :=
  (MultilinearMap.mkPiAlgebra R (Fin n) (SymmetricAlgebra R M)).compLinearMap
    (fun _ ↦ SymmetricAlgebra.ι R M)

private theorem finiteAlgebraMultilinear_invariant (n : ℕ) (e : Equiv.Perm (Fin n)) :
    (finiteAlgebraMultilinear R M n).domDomCongr e = finiteAlgebraMultilinear R M n := by
  ext m
  exact Equiv.prod_comp e (fun i ↦ SymmetricAlgebra.ι R M (m i))

/-- Multiplication of generators on the lifted symmetric quotient. -/
noncomputable def finiteToSymmetricAlgebra (n : ℕ) :
    FinitePower R M n →ₗ[R] SymmetricAlgebra R M :=
  finiteLift (finiteAlgebraMultilinear R M n) (finiteAlgebraMultilinear_invariant R M n)

/-- A finite pure symmetric tensor maps to the product of its generators. -/
@[simp]
theorem finiteToSymmetricAlgebra_tprod (n : ℕ) (m : Fin n → M) :
    finiteToSymmetricAlgebra R M n (finiteTprod R M n m) =
      ∏ i, SymmetricAlgebra.ι R M (m i) := by
  simp [finiteToSymmetricAlgebra, finiteAlgebraMultilinear]

/-- Multiplication preserves the homogeneous degree. -/
theorem finiteToSymmetricAlgebra_mem (n : ℕ) (x : FinitePower R M n) :
    finiteToSymmetricAlgebra R M n x ∈
      (LinearMap.range (SymmetricAlgebra.ι R M)) ^ n := by
  apply LinearMap.apply_mem_of_forall_symmetricPower_tprod
  intro m
  change finiteToSymmetricAlgebra R M n (finiteTprod R M n (fun i ↦ m ⟨i⟩)) ∈ _
  rw [finiteToSymmetricAlgebra_tprod]
  have hp (k : ℕ) (v : Fin k → M) :
      ∏ i, SymmetricAlgebra.ι R M (v i) ∈ (LinearMap.range (SymmetricAlgebra.ι R M)) ^ k := by
    induction k with
    | zero => simp
    | succ k hk =>
      rw [Fin.prod_univ_succ, pow_succ']
      exact Submodule.mul_mem_mul ⟨v 0, rfl⟩ (hk (fun i ↦ v i.succ))
  exact hp n _

/-- Multiplication with its codomain restricted to the actual homogeneous component. -/
@[expose]
noncomputable def finiteToHomogeneous (n : ℕ) :
    FinitePower R M n →ₗ[R] ↥((LinearMap.range (SymmetricAlgebra.ι R M)) ^ n) :=
  (finiteToSymmetricAlgebra R M n).codRestrict _ (finiteToSymmetricAlgebra_mem R M n)

/-- Multiplication has precisely the homogeneous component as its range. -/
theorem range_finiteToSymmetricAlgebra (n : ℕ) :
    LinearMap.range (finiteToSymmetricAlgebra R M n) =
      (LinearMap.range (SymmetricAlgebra.ι R M)) ^ n := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact finiteToSymmetricAlgebra_mem R M n x
  · intro p hp
    induction hp using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      refine ⟨r • finiteTprod R M 0 isEmptyElim, ?_⟩
      simp [Algebra.algebraMap_eq_smul_one]
    | add p q d hp hq ihp ihq =>
      exact (LinearMap.range (finiteToSymmetricAlgebra R M d)).add_mem ihp ihq
    | mem_mul m hm d p hp ih =>
      obtain ⟨m, rfl⟩ := hm
      obtain ⟨x, rfl⟩ := ih
      refine ⟨finiteConsMul R M d m x, ?_⟩
      have h : (finiteToSymmetricAlgebra R M (d + 1)).comp (finiteConsMul R M d m) =
          (LinearMap.mulLeft R (SymmetricAlgebra.ι R M m)).comp
            (finiteToSymmetricAlgebra R M d) := by
        apply finite_ext
        intro v
        simp [Fin.prod_univ_succ]
      exact LinearMap.congr_fun h x

private abbrev FiniteAllDegrees := ∀ k : ℕ, FinitePower R M k

private noncomputable def finiteShiftComponent (m : M) :
    (j : ℕ) → FiniteAllDegrees R M →ₗ[R] FinitePower R M j
  | 0 => 0
  | k + 1 => finiteConsMul R M k m ∘ₗ LinearMap.proj k

private noncomputable def finiteShiftMul : M →ₗ[R] Module.End R (FiniteAllDegrees R M) where
  toFun m := LinearMap.pi (finiteShiftComponent R M m)
  map_add' m m' := by
    ext f j
    cases j <;> simp [finiteShiftComponent]
  map_smul' c m := by
    ext f j
    cases j <;> simp [finiteShiftComponent]

private theorem finiteShiftMul_comm (m m' : M) :
    finiteShiftMul R M m * finiteShiftMul R M m' =
      finiteShiftMul R M m' * finiteShiftMul R M m := by
  ext f j
  rcases j with _ | _ | k
  · simp [finiteShiftMul, finiteShiftComponent]
  · simp [finiteShiftMul, finiteShiftComponent]
  · simp [finiteShiftMul, finiteShiftComponent, finiteConsMul_comm]

private theorem finiteShiftMul_single (m : M) (k : ℕ) (x : FinitePower R M k) :
    finiteShiftMul R M m (Pi.single (M := fun k ↦ FinitePower R M k) k x) =
      Pi.single (M := fun k ↦ FinitePower R M k) (k + 1) (finiteConsMul R M k m x) := by
  funext j
  rcases j with _ | j
  · simp [finiteShiftMul, finiteShiftComponent]
  · by_cases h : j = k
    · subst h
      simp [finiteShiftMul, finiteShiftComponent]
    · simp [finiteShiftMul, finiteShiftComponent, Pi.single_eq_of_ne h,
        Pi.single_eq_of_ne (Nat.succ_ne_succ_iff.mpr h)]

private noncomputable def finiteShiftMulAdjoin :
    M →ₗ[R] Algebra.adjoin R (Set.range (finiteShiftMul R M)) :=
  (finiteShiftMul R M).codRestrict
    (Subalgebra.toSubmodule (Algebra.adjoin R (Set.range (finiteShiftMul R M))))
    fun m ↦ Algebra.subset_adjoin (Set.mem_range_self m)

open scoped IsMulCommutative in
private noncomputable def finiteShiftAlgHom :
    SymmetricAlgebra R M →ₐ[R] Algebra.adjoin R (Set.range (finiteShiftMul R M)) :=
  have := Algebra.isMulCommutative_adjoin R (s := Set.range (finiteShiftMul R M)) <| by
    rintro _ ⟨m, rfl⟩ _ ⟨m', rfl⟩ -
    exact finiteShiftMul_comm R M m m'
  SymmetricAlgebra.lift (finiteShiftMulAdjoin R M)

private theorem coe_finiteShiftAlgHom_ι (m : M) :
    (finiteShiftAlgHom R M (SymmetricAlgebra.ι R M m) : Module.End R (FiniteAllDegrees R M)) =
      finiteShiftMul R M m := by
  simp only [finiteShiftAlgHom, SymmetricAlgebra.lift_ι_apply]
  rfl

private noncomputable def finiteUnitTensor : FiniteAllDegrees R M :=
  Pi.single (M := fun k ↦ FinitePower R M k) 0 (finiteTprod R M 0 isEmptyElim)

private theorem finiteShiftAlgHom_prod_unit (n : ℕ) (m : Fin n → M) :
    (finiteShiftAlgHom R M (∏ i, SymmetricAlgebra.ι R M (m i)) :
        Module.End R (FiniteAllDegrees R M)) (finiteUnitTensor R M) =
      Pi.single (M := fun k ↦ FinitePower R M k) n (finiteTprod R M n m) := by
  induction n with
  | zero => simp [finiteUnitTensor, Subsingleton.elim m isEmptyElim]
  | succ n ih =>
    rw [Fin.prod_univ_succ, map_mul, Subalgebra.coe_mul, Module.End.mul_apply, ih,
      coe_finiteShiftAlgHom_ι, finiteShiftMul_single, finiteConsMul_tprod,
      ← Fin.tail_def, Fin.cons_self_tail]

private noncomputable def finiteOfSymmetricAlgebra (n : ℕ) :
    SymmetricAlgebra R M →ₗ[R] FinitePower R M n :=
  LinearMap.proj n ∘ₗ LinearMap.applyₗ (finiteUnitTensor R M) ∘ₗ
    (Algebra.adjoin R (Set.range (finiteShiftMul R M))).val.toLinearMap ∘ₗ
      (finiteShiftAlgHom R M).toLinearMap

private theorem finiteOf_comp_toSymmetricAlgebra (n : ℕ) :
    finiteOfSymmetricAlgebra R M n ∘ₗ finiteToSymmetricAlgebra R M n = LinearMap.id := by
  apply finite_ext
  intro m
  simp [finiteOfSymmetricAlgebra, finiteShiftAlgHom_prod_unit]

variable {R M}

/-- Multiplication embeds each lifted finite symmetric power in its symmetric algebra. -/
theorem finiteToSymmetricAlgebra_injective (n : ℕ) :
    Function.Injective (finiteToSymmetricAlgebra R M n) :=
  Function.LeftInverse.injective (g := finiteOfSymmetricAlgebra R M n)
    (LinearMap.congr_fun (finiteOf_comp_toSymmetricAlgebra R M n))

/-- The lifted finite symmetric power is the homogeneous component, in every universe. -/
@[expose]
noncomputable def finiteEquivHomogeneous (n : ℕ) :
    FinitePower R M n ≃ₗ[R] ↥((LinearMap.range (SymmetricAlgebra.ι R M)) ^ n) := by
  refine LinearEquiv.ofBijective (finiteToHomogeneous R M n) ⟨?_, ?_⟩
  · intro x y h
    exact finiteToSymmetricAlgebra_injective n (congrArg Subtype.val h)
  · intro p
    obtain ⟨x, hx⟩ := (range_finiteToSymmetricAlgebra R M n).ge p.property
    exact ⟨x, Subtype.ext hx⟩

/-- The homogeneous equivalence is induced by multiplication of generators. -/
@[simp]
theorem coe_finiteEquivHomogeneous_apply (n : ℕ) (x : FinitePower R M n) :
    (finiteEquivHomogeneous n x : SymmetricAlgebra R M) =
      finiteToSymmetricAlgebra R M n x := rfl

variable (R M)

/-- The ordinary tensor-power quotient, transported to the lifted index. -/
noncomputable def finiteMk (n : ℕ) : (⨂[R] (_ : Fin n), M) →ₗ[R] FinitePower R M n :=
  (_root_.SymmetricPower.mk R (ULift.{u} (Fin n)) M).comp
    (PiTensorProduct.reindex R (fun _ : Fin n ↦ M) Equiv.ulift.symm).toLinearMap

/-- The quotient sends ordinary pure tensors to their finite symmetric tensors. -/
@[simp]
theorem finiteMk_tprod (n : ℕ) (m : Fin n → M) :
    finiteMk R M n (PiTensorProduct.tprod R m) = finiteTprod R M n m := by
  simp [finiteMk, finiteTprod, MultilinearMap.domDomCongr_apply,
    _root_.SymmetricPower.tprod]

/-- Symmetrization followed by reindexing to ordinary finite tensor positions. -/
noncomputable def finiteToTensorPower (n : ℕ) :
    FinitePower R M n →ₗ[R] (⨂[R] (_ : Fin n), M) :=
  (PiTensorProduct.reindex R (fun _ : ULift.{u} (Fin n) ↦ M) Equiv.ulift).toLinearMap.comp
    (_root_.SymmetricPower.toTensorPower R (ULift.{u} (Fin n)) M)

/-- The quotient of finite symmetrization is multiplication by the degree factorial. -/
theorem finiteMk_comp_toTensorPower (n : ℕ) :
    finiteMk R M n ∘ₗ finiteToTensorPower R M n =
      n.factorial • LinearMap.id (R := R) (M := FinitePower R M n) := by
  have h := _root_.SymmetricPower.mk_comp_toTensorPower
    (R := R) (ι := ULift.{u} (Fin n)) (M := M)
  apply LinearMap.ext
  intro x
  simpa only [finiteMk, finiteToTensorPower, LinearMap.comp_apply, LinearEquiv.coe_coe,
    ← PiTensorProduct.reindex_symm, LinearEquiv.symm_apply_apply, Fintype.card_ulift,
    Fintype.card_fin] using LinearMap.congr_fun h x

/-- Symmetrization in finite coordinates commutes with every linear map. -/
theorem finiteToTensorPower_comp_map {N : Type w} [AddCommMonoid N] [Module R N]
    (n : ℕ) (f : M →ₗ[R] N) :
    finiteToTensorPower R N n ∘ₗ _root_.SymmetricPower.map f =
      (PiTensorProduct.map fun _ : Fin n ↦ f) ∘ₗ finiteToTensorPower R M n := by
  apply finite_ext
  intro m
  simp [finiteToTensorPower, finiteTprod, MultilinearMap.domDomCongr_apply]

end TauCeti.SymmetricPower
