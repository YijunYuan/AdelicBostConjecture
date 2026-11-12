/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Tensor.Dual.Regroup
public import BostConjecture.Adelic.Contraction.PairingBaseChange
public import ArakelovGeometry.AdelicVectorBundle.Tensor.Hermitian.Coherence
public import ArakelovGeometry.AdelicVectorBundle.Tensor.PairMap

/-!
# Completed norms for rectangular tensor regrouping

The interchange of two finite tensor index sets preserves the prescribed Hilbert
and epsilon tensor norms. This supplies the regrouping step in the canonical
determinant pairing.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Adelic.Contraction

open Module ArakelovGeometry
open scoped TensorProduct

private theorem multilinear_bound_of_generator_bounds
    {L I : Type*} [NormedField L] [Fintype I]
    {X : I → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace L (X i)]
    {G : I → Type*} [∀ i, Nonempty (G i)] (v : ∀ i, G i → X i)
    (w : ∀ i, G i → ℝ) (hw : ∀ i x, 0 ≤ w i x)
    {W : Type*} [SeminormedAddCommGroup W] [NormedSpace L W]
    (f : MultilinearMap L X W)
    (hlinear : ∀ i (g : X i →ₗ[L] W) (A : ℝ), 0 ≤ A →
      (∀ x, ‖g (v i x)‖ ≤ A * w i x) → ∀ z, ‖g z‖ ≤ A * ‖z‖)
    {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x : ∀ i, G i, ‖f (fun i ↦ v i (x i))‖ ≤ C * ∏ i, w i (x i))
    (z : ∀ i, X i) : ‖f z‖ ≤ C * ∏ i, ‖z i‖ := by
  classical
  have hs (s : Finset I) : ∀ (x : ∀ i, G i) (z : ∀ i, X i),
      ‖f (fun i ↦ if i ∈ s then z i else v i (x i))‖ ≤
        C * ∏ i, if i ∈ s then ‖z i‖ else w i (x i) := by
    induction s using Finset.induction_on with
    | empty =>
      intro x z
      simpa only [Finset.notMem_empty, ite_false] using hf x
    | @insert i s hi ih =>
      intro x z
      let m : ∀ j, X j := fun j ↦ if j ∈ s then z j else v j (x j)
      let c : I → ℝ := fun j ↦ if j ∈ s then ‖z j‖ else w j (x j)
      let A := C * ∏ j ∈ Finset.univ.erase i, c j
      have hA : 0 ≤ A := mul_nonneg hC (Finset.prod_nonneg fun j _ ↦ by
        dsimp [c]
        split_ifs
        · exact norm_nonneg _
        · exact hw _ _)
      have hbase (y : G i) : ‖(f.toLinearMap m i) (v i y)‖ ≤ A * w i y := by
        have h := ih (Function.update x i y) z
        have hm : (fun j ↦ if j ∈ s then z j else v j (Function.update x i y j)) =
            Function.update m i (v i y) := by
          funext j
          by_cases hj : j = i
          · subst j
            simp only [hi, ite_false, Function.update_self]
          · simp only [Function.update_of_ne hj, m]
        have hc : (fun j ↦ if j ∈ s then ‖z j‖ else w j (Function.update x i y j)) =
            Function.update c i (w i y) := by
          funext j
          by_cases hj : j = i
          · subst j
            simp only [hi, ite_false, Function.update_self]
          · simp only [Function.update_of_ne hj, c]
        rw [hm, hc, Finset.prod_update_of_mem (Finset.mem_univ i),
          Finset.sdiff_singleton_eq_erase] at h
        change ‖f (Function.update m i (v i y))‖ ≤ _
        simpa only [A, mul_assoc, mul_left_comm, mul_comm] using h
      have h := hlinear i (f.toLinearMap m i) A hA hbase (z i)
      have hm : Function.update m i (z i) =
          (fun j ↦ if j ∈ insert i s then z j else v j (x j)) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp only [Function.update_self, Finset.mem_insert_self, ite_true]
        · simp only [Function.update_of_ne hj, Finset.mem_insert, hj, false_or, m]
      have hc : (fun j ↦ if j ∈ insert i s then ‖z j‖ else w j (x j)) =
          Function.update c i ‖z i‖ := by
        funext j
        by_cases hj : j = i
        · subst j
          simp only [Function.update_self, Finset.mem_insert_self, ite_true]
        · simp only [Function.update_of_ne hj, Finset.mem_insert, hj, false_or, c]
      change ‖f (Function.update m i (z i))‖ ≤ _ at h
      rw [hm] at h
      rw [hc, Finset.prod_update_of_mem (Finset.mem_univ i),
        Finset.sdiff_singleton_eq_erase]
      simpa only [A, mul_assoc, mul_left_comm, mul_comm] using h
  simpa only [Finset.mem_univ, ite_true] using
    hs Finset.univ (fun i ↦ Classical.choice (inferInstance : Nonempty (G i))) z

section BaseChange

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
  {I J : Type*} [Finite I] [Finite J] (P : I → J → Type*)
  [∀ i j, AddCommGroup (P i j)] [∀ i j, Module K (P i j)]

/-- Rectangular regrouping commutes with both levels of scalar extension. -/
theorem regroup_baseChange (z : L ⊗[K] (⨂[K] i, ⨂[K] j, P i j)) :
    PiTensorProduct.map (fun j ↦ (tensorBaseChangeEquiv K L (fun i ↦ P i j)).toLinearMap)
      (tensorBaseChangeEquiv K L (fun j ↦ ⨂[K] i, P i j)
        ((Tensor.regroupEquiv K P).toLinearMap.baseChange L z)) =
    Tensor.regroupEquiv L (fun i j ↦ L ⊗[K] P i j)
      (PiTensorProduct.map (fun i ↦ (tensorBaseChangeEquiv K L (P i)).toLinearMap)
        (tensorBaseChangeEquiv K L (fun i ↦ ⨂[K] j, P i j) z)) := by
  let f := (PiTensorProduct.map
    (fun j ↦ (tensorBaseChangeEquiv K L (fun i ↦ P i j)).toLinearMap)) ∘ₗ
      (tensorBaseChangeEquiv K L (fun j ↦ ⨂[K] i, P i j)).toLinearMap ∘ₗ
        (Tensor.regroupEquiv K P).toLinearMap.baseChange L
  let g := (Tensor.regroupEquiv L (fun i j ↦ L ⊗[K] P i j)).toLinearMap ∘ₗ
    PiTensorProduct.map (fun i ↦ (tensorBaseChangeEquiv K L (P i)).toLinearMap) ∘ₗ
      (tensorBaseChangeEquiv K L (fun i ↦ ⨂[K] j, P i j)).toLinearMap
  have h : f = g := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c z
    have hc : (f.restrictScalars K).comp (TensorProduct.mk K L _ c) =
        (g.restrictScalars K).comp (TensorProduct.mk K L _ c) := by
      apply Tensor.tensorTensor_ext K P
      intro x
      simp [f, g, Tensor.regroupEquiv_tprod]
    exact LinearMap.congr_fun hc z
  exact LinearMap.congr_fun h z

/-- Regrouping sends arbitrary completed double pure tensors to their transpose. -/
theorem regroup_baseChange_tprod (x : ∀ i j, L ⊗[K] P i j) :
    (Tensor.regroupEquiv K P).toLinearMap.baseChange L
      ((tensorBaseChangeEquiv K L (fun i ↦ ⨂[K] j, P i j)).symm
        (⨂ₜ[L] i, (tensorBaseChangeEquiv K L (P i)).symm (⨂ₜ[L] j, x i j))) =
    (tensorBaseChangeEquiv K L (fun j ↦ ⨂[K] i, P i j)).symm
      (⨂ₜ[L] j, (tensorBaseChangeEquiv K L (fun i ↦ P i j)).symm
        (⨂ₜ[L] i, x i j)) := by
  apply (tensorBaseChangeEquiv K L (fun j ↦ ⨂[K] i, P i j)).injective
  apply (PiTensorProduct.congr (fun j ↦ tensorBaseChangeEquiv K L (fun i ↦ P i j))).injective
  change PiTensorProduct.map (fun j ↦ (tensorBaseChangeEquiv K L (fun i ↦ P i j)).toLinearMap)
    (tensorBaseChangeEquiv K L (fun j ↦ ⨂[K] i, P i j) _) = _
  rw [regroup_baseChange]
  simp only [LinearEquiv.apply_symm_apply, PiTensorProduct.map_tprod, LinearEquiv.coe_coe,
    Tensor.regroupEquiv_tprod, PiTensorProduct.congr_tprod]

/-- Completed double pure tensors span the original iterated tensor fibre. -/
theorem span_completed_nested_tprod :
    Submodule.span L (Set.range (fun x : ∀ i j, L ⊗[K] P i j ↦
      (tensorBaseChangeEquiv K L (fun i ↦ ⨂[K] j, P i j)).symm
        (⨂ₜ[L] i, (tensorBaseChangeEquiv K L (P i)).symm (⨂ₜ[L] j, x i j)))) = ⊤ := by
  let e := (tensorBaseChangeEquiv K L (fun i ↦ ⨂[K] j, P i j)).trans
    (PiTensorProduct.congr (fun i ↦ tensorBaseChangeEquiv K L (P i)))
  have hv := PiTensorProduct.submodule_span_eq_top
    (fun i ↦ PiTensorProduct.span_tprod_eq_top (R := L) (s := fun j ↦ L ⊗[K] P i j))
  have he := congrArg (Submodule.map e.symm.toLinearMap) hv
  rw [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at he
  simpa [e, ← Set.range_comp, Function.comp_def] using he

end BaseChange

section Finite

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {I : Type*} [Fintype I] {P : I → Type*}
  [∀ i, AddCommGroup (P i)] [∀ i, Module K (P i)] [∀ i, FiniteDimensional K (P i)]

/-- The epsilon universal bound on the actual completed tensor fibre. -/
theorem norm_linearMap_le_orthogonalTensor_of_finite
    (ξ : ∀ i, NormFamily S (P i))
    [hN : S.IsArchimedeanNormalized]
    [hξ : ∀ i, (ξ i).IsHermitian] (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    {W : Type*} [SeminormedAddCommGroup W] [NormedSpace (S.ϕ ω).Completion W]
    (f : ((S.ϕ ω).Completion ⊗[K] (⨂[K] i, P i)) →ₗ[(S.ϕ ω).Completion] W)
    (hW : ∀ x y : W, ‖x + y‖ ≤ max ‖x‖ ‖y‖) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x : ∀ i, (S.ϕ ω).Completion ⊗[K] P i,
      ‖f ((tensorBaseChangeEquiv K (S.ϕ ω).Completion P).symm
      (⨂ₜ[(S.ϕ ω).Completion] i, x i))‖ ≤ C * ∏ i, (ξ i).norm ω (x i))
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, P i)) :
    ‖f z‖ ≤ C * (NormFamily.orthogonalTensor ξ).norm ω z := by
  let L := (S.ϕ ω).Completion
  let : ∀ i, NormedAddCommGroup (L ⊗[K] P i) := fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (L ⊗[K] P i) := fun i ↦ (ξ i).fibreNormedSpace ω
  let e := tensorBaseChangeEquiv K L P
  have h := norm_linearMap_le_mul_injective_of_ultrametric_factors
    (f ∘ₗ e.symm.toLinearMap) hW hC hf (e z)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
  rw [NormFamily.orthogonalTensor_norm_of_finite _ ω hω]
  exact h

end Finite

section NestedFinite

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {I J : Type*} [Fintype I] [Fintype J] {P : I → J → Type*}
  [∀ i j, AddCommGroup (P i j)] [∀ i j, Module K (P i j)]
  [∀ i j, FiniteDimensional K (P i j)]

/-- A bound on completed double pure tensors extends with the same constant
for iterated epsilon norms. -/
theorem norm_linearMap_le_nested_orthogonalTensor_of_finite
    (ξ : ∀ i j, NormFamily S (P i j))
    [hN : S.IsArchimedeanNormalized]
    [hξ : ∀ i j, (ξ i j).IsHermitian] (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    {W : Type*} [SeminormedAddCommGroup W] [NormedSpace (S.ϕ ω).Completion W]
    (f : ((S.ϕ ω).Completion ⊗[K] (⨂[K] i, ⨂[K] j, P i j)) →ₗ[(S.ϕ ω).Completion] W)
    (hW : ∀ x y : W, ‖x + y‖ ≤ max ‖x‖ ‖y‖) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ x : ∀ i j, (S.ϕ ω).Completion ⊗[K] P i j,
      ‖f ((tensorBaseChangeEquiv K (S.ϕ ω).Completion (fun i ↦ ⨂[K] j, P i j)).symm
        (⨂ₜ[(S.ϕ ω).Completion] i,
          (tensorBaseChangeEquiv K (S.ϕ ω).Completion (P i)).symm
            (⨂ₜ[(S.ϕ ω).Completion] j, x i j)))‖ ≤ C * ∏ i, ∏ j, (ξ i j).norm ω (x i j))
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, ⨂[K] j, P i j)) :
    ‖f z‖ ≤ C * (NormFamily.orthogonalTensor
      (fun i ↦ NormFamily.orthogonalTensor (ξ i))).norm ω z := by
  let L := (S.ϕ ω).Completion
  let X i := L ⊗[K] (⨂[K] j, P i j)
  let η i := NormFamily.orthogonalTensor (ξ i)
  let : ∀ i, NormedAddCommGroup (X i) := fun i ↦ (η i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (X i) := fun i ↦ (η i).fibreNormedSpace ω
  let g := f.compMultilinearMap
    ((tensorBaseChangeEquiv K L (fun i ↦ ⨂[K] j, P i j)).symm.toLinearMap.compMultilinearMap
      (PiTensorProduct.tprod L))
  apply norm_linearMap_le_orthogonalTensor_of_finite η
     ω hω f hW hC
  intro x
  change ‖g x‖ ≤ C * ∏ i, ‖x i‖
  exact multilinear_bound_of_generator_bounds (X := X) (G := fun i ↦ ∀ j, L ⊗[K] P i j)
    (fun i y ↦ (tensorBaseChangeEquiv K L (P i)).symm (⨂ₜ[L] j, y j))
    (fun i y ↦ ∏ j, (ξ i j).norm ω (y j))
    (fun i y ↦ Finset.prod_nonneg (fun j _ ↦ (ξ i j).norm_nonneg ω (y j)))
    g (fun i g A hA hg z ↦ by
      change ‖g z‖ ≤ A * (η i).norm ω z
      exact norm_linearMap_le_orthogonalTensor_of_finite (ξ i) ω hω g hW hA hg z)
    hC (fun y ↦ by
      change ‖f _‖ ≤ _
      exact hf y) x

/-- Rectangular regrouping contracts the actual iterated epsilon norms at every
finite place, including a trivial valuation. -/
theorem regroup_norm_le_finite
    (ξ : ∀ i j, NormFamily S (P i j))
    [hN : S.IsArchimedeanNormalized]
    [hξ : ∀ i j, (ξ i j).IsHermitian] (ω : S.Ω) (hω : ω ∈ S.Ωfin)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, ⨂[K] j, P i j)) :
    (NormFamily.orthogonalTensor
      (fun j ↦ NormFamily.orthogonalTensor (fun i ↦ ξ i j))).norm ω
      ((Tensor.regroupEquiv K P).toLinearMap.baseChange (S.ϕ ω).Completion z) ≤
    (NormFamily.orthogonalTensor
      (fun i ↦ NormFamily.orthogonalTensor (ξ i))).norm ω z := by
  let τ := NormFamily.orthogonalTensor
    (fun j ↦ NormFamily.orthogonalTensor (fun i ↦ ξ i j))
  let := τ.fibreNormedAddCommGroup ω
  let := τ.fibreNormedSpace ω
  have h := norm_linearMap_le_nested_orthogonalTensor_of_finite ξ ω hω
    ((Tensor.regroupEquiv K P).toLinearMap.baseChange (S.ϕ ω).Completion)
    ((NormFamily.orthogonalTensor_isHermitian _).1 ω hω)
    (C := 1) zero_le_one (fun x ↦ by
      change τ.norm ω _ ≤ _
      rw [regroup_baseChange_tprod]
      simp only [τ, NormFamily.orthogonalTensor_norm_tprod, one_mul]
      exact (Finset.prod_comm).le) z
  change τ.norm ω _ ≤ 1 * _ at h
  simpa only [one_mul] using h

end NestedFinite

section Infinite

attribute [-instance] PiTensorProduct.instSeminormedAddCommGroup PiTensorProduct.instNormedSpace

private theorem inner_ext_span {L A V W G : Type*} [RCLike L]
    [AddCommGroup A] [Module L A] [NormedAddCommGroup V] [InnerProductSpace L V]
    [NormedAddCommGroup W] [InnerProductSpace L W]
    (v : G → A) (hv : Submodule.span L (Set.range v) = ⊤)
    (f : A →ₗ[L] V) (g : A →ₗ[L] W)
    (h : ∀ i j, inner L (f (v i)) (f (v j)) = inner L (g (v i)) (g (v j)))
    (x y : A) : inner L (f x) (f y) = inner L (g x) (g y) := by
  have hx : x ∈ Submodule.span L (Set.range v) := hv.symm ▸ Submodule.mem_top
  have hy : y ∈ Submodule.span L (Set.range v) := hv.symm ▸ Submodule.mem_top
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, rfl⟩ := hy
    exact h i j
  | zero_left y hy => simp
  | zero_right x hx => simp
  | add_left x y z hx hy hz h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | add_right x y z hx hy hz h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
  | smul_left r x y hx hy h => simp only [map_smul, inner_smul_left, h]
  | smul_right r x y hx hy h => simp only [map_smul, inner_smul_right, h]

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {I : Type*} [Fintype I] {P : I → Type*}
  [∀ i, AddCommGroup (P i)] [∀ i, Module K (P i)] [∀ i, FiniteDimensional K (P i)]

/-- The actual completed Hilbert tensor inner product has the product formula. -/
theorem orthogonalTensor_fibre_inner_tprod
    (ξ : ∀ i, NormFamily S (P i))
    [hN : S.IsArchimedeanNormalized]
    [hξ : ∀ i, (ξ i).IsHermitian] (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (x y : ∀ i, (S.ϕ ω).Completion ⊗[K] P i) :
    letI := hN ω hω
    letI := IsRCLikeNormedField.rclike (S.ϕ ω).Completion
    letI : ∀ i, NormedAddCommGroup ((S.ϕ ω).Completion ⊗[K] P i) :=
      fun i ↦ (ξ i).fibreNormedAddCommGroup ω
    letI : ∀ i, NormedSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] P i) :=
      fun i ↦ (ξ i).fibreNormedSpace ω
    letI : ∀ i, InnerProductSpace (S.ϕ ω).Completion ((S.ϕ ω).Completion ⊗[K] P i) :=
      fun i ↦ (ξ i).fiberInnerProductSpace ω hω
    letI := (NormFamily.orthogonalTensor ξ).fibreNormedAddCommGroup ω
    letI := (NormFamily.orthogonalTensor ξ).fibreNormedSpace ω
    letI := (NormFamily.orthogonalTensor ξ).fiberInnerProductSpace ω hω
    inner (S.ϕ ω).Completion
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion P).symm (⨂ₜ[(S.ϕ ω).Completion] i, x i))
      ((tensorBaseChangeEquiv K (S.ϕ ω).Completion P).symm (⨂ₜ[(S.ϕ ω).Completion] i, y i)) =
      ∏ i, inner (S.ϕ ω).Completion (x i) (y i) := by
  let L := (S.ϕ ω).Completion
  let := hN ω hω
  let := IsRCLikeNormedField.rclike L
  let : ∀ i, NormedAddCommGroup (L ⊗[K] P i) := fun i ↦ (ξ i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (L ⊗[K] P i) := fun i ↦ (ξ i).fibreNormedSpace ω
  let : ∀ i, InnerProductSpace L (L ⊗[K] P i) :=
    fun i ↦ (ξ i).fiberInnerProductSpace ω hω
  let := (NormFamily.orthogonalTensor ξ).fibreNormedAddCommGroup ω
  let := (NormFamily.orthogonalTensor ξ).fibreNormedSpace ω
  let := (NormFamily.orthogonalTensor ξ).fiberInnerProductSpace ω hω
  let b := fun i ↦ stdOrthonormalBasis L (L ⊗[K] P i)
  let := orthogonalTensorNormedAddCommGroup b
  let := orthogonalTensorNormedSpace b
  let := orthogonalTensorInnerProductSpace b
  let e : (L ⊗[K] (⨂[K] i, P i)) ≃ₗᵢ[L] (⨂[L] i, L ⊗[K] P i) :=
    { toLinearEquiv := tensorBaseChangeEquiv K L P
      norm_map' := fun z ↦ (NormFamily.orthogonalTensor_norm_of_infinite ξ ω hω z).symm }
  have he := e.inner_map_map
    ((tensorBaseChangeEquiv K L P).symm (⨂ₜ[L] i, x i))
    ((tensorBaseChangeEquiv K L P).symm (⨂ₜ[L] i, y i))
  change inner L (tensorBaseChangeEquiv K L P _) (tensorBaseChangeEquiv K L P _) = _ at he
  simp only [LinearEquiv.apply_symm_apply] at he
  rw [← he]
  exact orthogonalTensorCore_tprod b x y

end Infinite

section NestedInfinite

attribute [-instance] PiTensorProduct.instSeminormedAddCommGroup PiTensorProduct.instNormedSpace

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {I J : Type*} [Fintype I] [Fintype J] {P : I → J → Type*}
  [∀ i j, AddCommGroup (P i j)] [∀ i j, Module K (P i j)]
  [∀ i j, FiniteDimensional K (P i j)]

/-- Rectangular regrouping preserves the actual completed Hilbert norms over
both real and complex completions. -/
theorem regroup_norm_infinite
    (ξ : ∀ i j, NormFamily S (P i j))
    [hN : S.IsArchimedeanNormalized]
    [hξ : ∀ i j, (ξ i j).IsHermitian] (ω : S.Ω) (hω : ω ∈ S.Ωinf)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, ⨂[K] j, P i j)) :
    (NormFamily.orthogonalTensor
      (fun j ↦ NormFamily.orthogonalTensor (fun i ↦ ξ i j))).norm ω
      ((Tensor.regroupEquiv K P).toLinearMap.baseChange (S.ϕ ω).Completion z) =
    (NormFamily.orthogonalTensor
      (fun i ↦ NormFamily.orthogonalTensor (ξ i))).norm ω z := by
  let L := (S.ϕ ω).Completion
  let := hN ω hω
  let := IsRCLikeNormedField.rclike L
  let η i := NormFamily.orthogonalTensor (ξ i)
  let hη i := NormFamily.orthogonalTensor_isHermitian (ξ i)
  let θ j := NormFamily.orthogonalTensor (fun i ↦ ξ i j)
  let hθ j := NormFamily.orthogonalTensor_isHermitian (fun i ↦ ξ i j)
  let σ := NormFamily.orthogonalTensor η
  let τ := NormFamily.orthogonalTensor θ
  let : ∀ i j, NormedAddCommGroup (L ⊗[K] P i j) :=
    fun i j ↦ (ξ i j).fibreNormedAddCommGroup ω
  let : ∀ i j, NormedSpace L (L ⊗[K] P i j) := fun i j ↦ (ξ i j).fibreNormedSpace ω
  let : ∀ i j, InnerProductSpace L (L ⊗[K] P i j) :=
    fun i j ↦ (ξ i j).fiberInnerProductSpace ω hω
  let : ∀ i, NormedAddCommGroup (L ⊗[K] (⨂[K] j, P i j)) :=
    fun i ↦ (η i).fibreNormedAddCommGroup ω
  let : ∀ i, NormedSpace L (L ⊗[K] (⨂[K] j, P i j)) :=
    fun i ↦ (η i).fibreNormedSpace ω
  let : ∀ i, InnerProductSpace L (L ⊗[K] (⨂[K] j, P i j)) :=
    fun i ↦ (η i).fiberInnerProductSpace ω hω
  let : ∀ j, NormedAddCommGroup (L ⊗[K] (⨂[K] i, P i j)) :=
    fun j ↦ (θ j).fibreNormedAddCommGroup ω
  let : ∀ j, NormedSpace L (L ⊗[K] (⨂[K] i, P i j)) :=
    fun j ↦ (θ j).fibreNormedSpace ω
  let : ∀ j, InnerProductSpace L (L ⊗[K] (⨂[K] i, P i j)) :=
    fun j ↦ (θ j).fiberInnerProductSpace ω hω
  let := σ.fibreNormedAddCommGroup ω
  let := σ.fibreNormedSpace ω
  let := (NormFamily.orthogonalTensor η).fiberInnerProductSpace ω hω
  let := τ.fibreNormedAddCommGroup ω
  let := τ.fibreNormedSpace ω
  let := (NormFamily.orthogonalTensor θ).fiberInnerProductSpace ω hω
  let f := (Tensor.regroupEquiv K P).toLinearMap.baseChange L
  have hi (x y : L ⊗[K] (⨂[K] i, ⨂[K] j, P i j)) :
      inner L (f x) (f y) = inner L x y := by
    apply inner_ext_span _ (span_completed_nested_tprod K L P) f LinearMap.id
    intro x y
    change inner L ((Tensor.regroupEquiv K P).toLinearMap.baseChange L _)
      ((Tensor.regroupEquiv K P).toLinearMap.baseChange L _) = _
    rw [regroup_baseChange_tprod, regroup_baseChange_tprod]
    simp only [LinearMap.id_apply]
    rw [orthogonalTensor_fibre_inner_tprod θ ω hω,
      orthogonalTensor_fibre_inner_tprod η ω hω]
    calc
      _ = ∏ j, ∏ i, inner L (x i j) (y i j) := by
        apply Finset.prod_congr rfl
        intro j _
        exact orthogonalTensor_fibre_inner_tprod
          (fun i ↦ ξ i j) ω hω _ _
      _ = ∏ i, ∏ j, inner L (x i j) (y i j) := Finset.prod_comm
      _ = _ := by
        symm
        apply Finset.prod_congr rfl
        intro i _
        exact orthogonalTensor_fibre_inner_tprod (ξ i) ω hω _ _
  change ‖f z‖ = ‖z‖
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have h := congrArg RCLike.re (hi z z)
  simpa only [inner_self_eq_norm_sq_to_K, ← map_pow, RCLike.ofReal_re] using h

end NestedInfinite

section Regroup

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {I J : Type*} [Fintype I] [Fintype J] {P : I → J → Type*}
  [∀ i j, AddCommGroup (P i j)] [∀ i j, Module K (P i j)]
  [∀ i j, FiniteDimensional K (P i j)]

/-- Rectangular regrouping contracts at every place for the prescribed norms. -/
theorem regroup_norm_le
    (ξ : ∀ i j, NormFamily S (P i j))
    [hN : S.IsArchimedeanNormalized]
    [hξ : ∀ i j, (ξ i j).IsHermitian] (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, ⨂[K] j, P i j)) :
    (NormFamily.orthogonalTensor
      (fun j ↦ NormFamily.orthogonalTensor (fun i ↦ ξ i j))).norm ω
      ((Tensor.regroupEquiv K P).toLinearMap.baseChange (S.ϕ ω).Completion z) ≤
    (NormFamily.orthogonalTensor
      (fun i ↦ NormFamily.orthogonalTensor (ξ i))).norm ω z := by
  by_cases hω : ω ∈ S.Ωfin
  · exact regroup_norm_le_finite ξ ω hω z
  · exact (regroup_norm_infinite ξ ω hω z).le

end Regroup

section DualRegroup

variable {K : Type*} [Field K] {S : AdelicStructure K}
  {I κ : Type*} [Fintype I] [Fintype κ] {E : I → Type*}
  [∀ i, AddCommGroup (E i)] [∀ i, Module K (E i)] [∀ i, FiniteDimensional K (E i)]

/-- The actual dual regrouping used by the determinant pairing contracts on
completed fibres for the prescribed Hilbert and epsilon tensor norms. -/
theorem dualRegroupEquiv_norm_le
    (ξ : ∀ i, NormFamily S (E i))
    [hN : S.IsArchimedeanNormalized]
    [hξ : ∀ i, (ξ i).IsHermitian] (ω : S.Ω)
    (z : (S.ϕ ω).Completion ⊗[K] (⨂[K] i, ⨂[K] (_ : κ), Dual K (E i))) :
    (NormFamily.orthogonalTensor
      (fun _ : κ ↦ (NormFamily.orthogonalTensor ξ).dual)).norm ω
      ((Tensor.dualRegroupEquiv K E).toLinearMap.baseChange (S.ϕ ω).Completion z) ≤
    (NormFamily.orthogonalTensor
      (fun i ↦ NormFamily.orthogonalTensor (fun _ : κ ↦ (ξ i).dual))).norm ω z := by
  have he : (Tensor.dualRegroupEquiv K E (κ := κ)).toLinearMap =
      (PiTensorProduct.map (fun _ : κ ↦ (PiTensorProduct.dualDistrib :
        (⨂[K] i, Dual K (E i)) →ₗ[K] Dual K (⨂[K] i, E i)))) ∘ₗ
        (Tensor.regroupEquiv K (fun i (_ : κ) ↦ Dual K (E i))).toLinearMap := by
    change (PiTensorProduct.map (fun _ : κ ↦
      (PiTensorProduct.dualDistribEquivOfProjective K E).toLinearMap)) ∘ₗ _ = _
    simp only [dualDistribEquivOfProjective_toLinearMap_eq]
  rw [he, LinearMap.baseChange_comp, LinearMap.comp_apply]
  refine (NormFamily.orthogonalTensor_map_norm_le_of_norm_eq
    (fun _ : κ ↦ NormFamily.orthogonalTensor (fun i ↦ (ξ i).dual))
    (fun _ : κ ↦ (NormFamily.orthogonalTensor ξ).dual)
    (fun _ : κ ↦ PiTensorProduct.dualDistrib) ω
    (fun _ x ↦ NormFamily.orthogonalTensor_dual_norm ξ ω x) _).trans ?_
  exact regroup_norm_le (fun i (_ : κ) ↦ (ξ i).dual)
     ω z

end DualRegroup

end BostConjecture.Adelic.Contraction
