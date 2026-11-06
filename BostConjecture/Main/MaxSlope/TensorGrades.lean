module

public import BostConjecture.Main.MaxSlope.TensorFlag
public import BostConjecture.Main.MaxSlope.QuotientTransport

/-!
# The actual integral grades of the HN tensor refinement

The tensor of two consecutive submodules surjects onto the consecutive sum
quotient. Right exactness computes its kernel and gives the canonical integral
identification with the tensor of the two factor quotients.
-/

@[expose] public section
noncomputable section
open NumberField TensorProduct

namespace BostConjecture.Arithmetic

universe u
variable {K : Type*} [Field K]
variable {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]

/-- Pure tensors in the upper factor submodules map to the actual sum step. -/
def tensorStepMap (P T : Submodule (𝓞 K) M) (U : Submodule (𝓞 K) N) :
    T ⊗[𝓞 K] U →ₗ[𝓞 K] tensorStep P T U :=
  (TensorProduct.map T.subtype U.subtype).codRestrict _
    (fun x => (show LinearMap.range (TensorProduct.map T.subtype U.subtype) ≤
      tensorStep P T U from le_sup_right) ⟨x, rfl⟩)

/-- The actual projection onto a consecutive sum quotient. -/
def tensorGradeProjection (P T : Submodule (𝓞 K) M) (Q U : Submodule (𝓞 K) N) :
    T ⊗[𝓞 K] U →ₗ[𝓞 K]
      (tensorStep P T U ⧸ (tensorStep P T Q).comap (tensorStep P T U).subtype) :=
  ((tensorStep P T Q).comap (tensorStep P T U).subtype).mkQ.comp (tensorStepMap P T U)

lemma tensorGradeProjection_surjective (P T : Submodule (𝓞 K) M)
    (Q U : Submodule (𝓞 K) N) : Function.Surjective (tensorGradeProjection P T Q U) := by
  intro z
  obtain ⟨x, rfl⟩ := ((tensorStep P T Q).comap (tensorStep P T U).subtype).mkQ_surjective z
  obtain ⟨a, ha, b, ⟨w, rfl⟩, he⟩ := Submodule.mem_sup.mp x.property
  refine ⟨w, ?_⟩
  apply (Submodule.Quotient.eq _).mpr
  change TensorProduct.map T.subtype U.subtype w - (x : M ⊗[𝓞 K] N) ∈ tensorStep P T Q
  rw [← he]
  simpa using (tensorStep P T Q).neg_mem ((show tensorRight N P ≤ tensorStep P T Q from le_sup_left) ha)

/-- Right exactness computes the kernel of the actual consecutive-grade map. -/
lemma tensorGradeProjection_ker [Module.Flat (𝓞 K) N]
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) (Q U : Submodule (𝓞 K) N)
    [Module.Flat (𝓞 K) (T ⧸ P.comap T.subtype)] :
    LinearMap.ker (tensorGradeProjection P T Q U) =
      LinearMap.ker (TensorProduct.map (P.comap T.subtype).mkQ (Q.comap U.subtype).mkQ) := by
  have hi := Module.Flat.rTensor_preserves_injective_linearMap (M := N)
    T.subtype T.injective_subtype
  have hj := Module.Flat.lTensor_preserves_injective_linearMap
    (M := T ⧸ P.comap T.subtype) (submoduleQuotientMap Q U) (submoduleQuotientMap_injective Q U)
  have hc : (TensorProduct.map (P.comap T.subtype).mkQ Q.mkQ).comp (U.subtype.lTensor T) =
      ((submoduleQuotientMap Q U).lTensor (T ⧸ P.comap T.subtype)).comp
        (TensorProduct.map (P.comap T.subtype).mkQ (Q.comap U.subtype).mkQ) := by
    ext t u
    rfl
  have ht (x : T ⊗[𝓞 K] U) :
      TensorProduct.map T.subtype U.subtype x = T.subtype.rTensor N (U.subtype.lTensor T x) := by
    have he : TensorProduct.map T.subtype U.subtype =
        (T.subtype.rTensor N).comp (U.subtype.lTensor T) := by ext; rfl
    exact LinearMap.congr_fun he x
  ext x
  change tensorGradeProjection P T Q U x = 0 ↔ _
  rw [tensorGradeProjection, LinearMap.comp_apply]
  change Submodule.Quotient.mk (tensorStepMap P T U x) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change TensorProduct.map T.subtype U.subtype x ∈ tensorStep P T Q ↔ _
  rw [tensorStep_eq_map_ker hPT Q, ht]
  constructor
  · rintro ⟨y, hy, he⟩
    have he' : y = U.subtype.lTensor T x := hi he
    rw [he'] at hy
    change TensorProduct.map (P.comap T.subtype).mkQ (Q.comap U.subtype).mkQ x = 0
    apply hj
    rw [map_zero]
    exact (LinearMap.congr_fun hc x).symm.trans hy
  · intro hx
    refine ⟨U.subtype.lTensor T x, ?_, rfl⟩
    change TensorProduct.map (P.comap T.subtype).mkQ Q.mkQ (U.subtype.lTensor T x) = 0
    rw [← LinearMap.comp_apply, hc, LinearMap.comp_apply, hx, map_zero]

/-- The canonical integral isomorphism from an actual sum grade to the tensor
of the factor quotients. No free integral module or splitting is chosen. -/
def tensorGradeEquiv [Module.Flat (𝓞 K) N]
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) (Q U : Submodule (𝓞 K) N)
    [Module.Flat (𝓞 K) (T ⧸ P.comap T.subtype)] :
    (tensorStep P T U ⧸ (tensorStep P T Q).comap (tensorStep P T U).subtype) ≃ₗ[𝓞 K]
      ((T ⧸ P.comap T.subtype) ⊗[𝓞 K] (U ⧸ Q.comap U.subtype)) :=
  ((tensorGradeProjection P T Q U).quotKerEquivOfSurjective
    (tensorGradeProjection_surjective P T Q U)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ (tensorGradeProjection_ker hPT Q U) ≪≫ₗ
      (TensorProduct.map (P.comap T.subtype).mkQ (Q.comap U.subtype).mkQ).quotKerEquivOfSurjective
        (TensorProduct.map_surjective (P.comap T.subtype).mkQ_surjective
          (Q.comap U.subtype).mkQ_surjective)

@[simp]
lemma tensorGradeEquiv_projection [Module.Flat (𝓞 K) N]
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) (Q U : Submodule (𝓞 K) N)
    [Module.Flat (𝓞 K) (T ⧸ P.comap T.subtype)] (x : T ⊗[𝓞 K] U) :
    tensorGradeEquiv hPT Q U (tensorGradeProjection P T Q U x) =
      TensorProduct.map (P.comap T.subtype).mkQ (Q.comap U.subtype).mkQ x := by
  simp [tensorGradeEquiv, LinearMap.quotKerEquivOfSurjective_symm_apply]

/-- Every refinement step lies in the tensor of its larger first submodule. -/
lemma tensorStep_le_tensorRight {P T : Submodule (𝓞 K) M} (hPT : P ≤ T)
    (U : Submodule (𝓞 K) N) : tensorStep P T U ≤ tensorRight N T := by
  rw [← tensorStep_top hPT]
  exact tensorStep_mono le_rfl le_rfl le_top

/-- The actual refinement step regarded inside `T ⊗ N`. -/
def tensorStepLift [Module.Flat (𝓞 K) N]
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) (U : Submodule (𝓞 K) N) :
    tensorStep P T U →ₗ[𝓞 K] T ⊗[𝓞 K] N :=
  (tensorRightEquiv N T).symm.toLinearMap.comp
    (Submodule.inclusion (tensorStep_le_tensorRight hPT U))

lemma tensorStepLift_comp [Module.Flat (𝓞 K) N]
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) (U : Submodule (𝓞 K) N) :
    (T.subtype.rTensor N).comp (tensorStepLift hPT U) = (tensorStep P T U).subtype := by
  ext x
  exact congrArg Subtype.val ((tensorRightEquiv N T).apply_symm_apply
    (Submodule.inclusion (tensorStep_le_tensorRight hPT U) x))

lemma tensorStepLift_stepMap [Module.Flat (𝓞 K) N]
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) (U : Submodule (𝓞 K) N) :
    (tensorStepLift hPT U).comp (tensorStepMap P T U) = U.subtype.lTensor T := by
  apply (LinearMap.cancel_left
    (Module.Flat.rTensor_preserves_injective_linearMap (M := N) T.subtype T.injective_subtype)).mp
  rw [← LinearMap.comp_assoc, tensorStepLift_comp]
  ext t u
  rfl

lemma tensorStepLift_mem_ker [Module.Flat (𝓞 K) N]
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) (Q U : Submodule (𝓞 K) N)
    (x : tensorStep P T U) :
    tensorStepLift hPT U x ∈ LinearMap.ker (TensorProduct.map (P.comap T.subtype).mkQ Q.mkQ) ↔
      (x : M ⊗[𝓞 K] N) ∈ tensorStep P T Q := by
  rw [tensorStep_eq_map_ker hPT Q]
  constructor
  · intro hx
    exact ⟨tensorStepLift hPT U x, hx, LinearMap.congr_fun (tensorStepLift_comp hPT U) x⟩
  · rintro ⟨y, hy, he⟩
    have he' : y = tensorStepLift hPT U x :=
      Module.Flat.rTensor_preserves_injective_linearMap T.subtype T.injective_subtype
        (he.trans (LinearMap.congr_fun (tensorStepLift_comp hPT U) x).symm)
    exact he' ▸ hy

/-- A consecutive sum grade embeds in the quotient of `T ⊗ N`. -/
def tensorGradeInclusion [Module.Flat (𝓞 K) N]
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) (Q U : Submodule (𝓞 K) N) :
    (tensorStep P T U ⧸ (tensorStep P T Q).comap (tensorStep P T U).subtype) →ₗ[𝓞 K]
      ((T ⧸ P.comap T.subtype) ⊗[𝓞 K] (N ⧸ Q)) :=
  ((tensorStep P T Q).comap (tensorStep P T U).subtype).liftQ
    ((TensorProduct.map (P.comap T.subtype).mkQ Q.mkQ).comp (tensorStepLift hPT U))
    (fun x hx => (tensorStepLift_mem_ker hPT Q U x).mpr hx)

lemma tensorGradeInclusion_injective [Module.Flat (𝓞 K) N]
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) (Q U : Submodule (𝓞 K) N) :
    Function.Injective (tensorGradeInclusion hPT Q U) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm _ bot_le
  intro z hz
  obtain ⟨x, rfl⟩ := ((tensorStep P T Q).comap (tensorStep P T U).subtype).mkQ_surjective z
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact (tensorStepLift_mem_ker hPT Q U x).mp hz

lemma tensorGradeInclusion_comp [Module.Flat (𝓞 K) N]
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) (Q U : Submodule (𝓞 K) N) :
    (tensorGradeInclusion hPT Q U).comp
        ((tensorStep P T Q).comap (tensorStep P T U).subtype).mkQ =
      (TensorProduct.map (P.comap T.subtype).mkQ Q.mkQ).comp (tensorStepLift hPT U) := by
  ext
  rfl

/-- The quotient inclusion is the tensor of the canonical factor inclusion. -/
lemma tensorGradeInclusion_eq [Module.Flat (𝓞 K) N]
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) (Q U : Submodule (𝓞 K) N)
    [Module.Flat (𝓞 K) (T ⧸ P.comap T.subtype)] :
    tensorGradeInclusion hPT Q U =
      ((submoduleQuotientMap Q U).lTensor (T ⧸ P.comap T.subtype)).comp
        (tensorGradeEquiv hPT Q U).toLinearMap := by
  apply LinearMap.ext
  intro z
  obtain ⟨x, rfl⟩ := tensorGradeProjection_surjective P T Q U z
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, tensorGradeEquiv_projection]
  change TensorProduct.map (P.comap T.subtype).mkQ Q.mkQ
    (tensorStepLift hPT U (tensorStepMap P T U x)) = _
  rw [show tensorStepLift hPT U (tensorStepMap P T U x) = U.subtype.lTensor T x from
    LinearMap.congr_fun (tensorStepLift_stepMap hPT U) x]
  have hc : (TensorProduct.map (P.comap T.subtype).mkQ Q.mkQ).comp (U.subtype.lTensor T) =
      ((submoduleQuotientMap Q U).lTensor (T ⧸ P.comap T.subtype)).comp
        (TensorProduct.map (P.comap T.subtype).mkQ (Q.comap U.subtype).mkQ) := by
    ext t u
    rfl
  exact LinearMap.congr_fun hc x

variable [NumberField K]

/-- Scalar extension preserves the kernel of an actual surjection. -/
lemma ker_fiberMap_of_surjective (f : M →ₗ[𝓞 K] N) (hf : Function.Surjective f)
    (σ : K →+* ℂ) :
    LinearMap.ker (fiberMap f σ) = LinearMap.range (fiberMap (LinearMap.ker f).subtype σ) := by
  let e := f.quotKerEquivOfSurjective hf
  have hc : e.toLinearMap.comp (LinearMap.ker f).mkQ = f := by ext; rfl
  have he := congrArg (fun a => fiberMap a σ) hc
  rw [fiberMap_comp] at he
  rw [← he, ← ker_fiberMap_mkQ]
  ext x
  change fiberMap e.toLinearMap σ (fiberMap (LinearMap.ker f).mkQ σ x) = 0 ↔
    fiberMap (LinearMap.ker f).mkQ σ x = 0
  constructor
  · intro hx
    apply fiberMap_injective _ e.injective σ
    simpa only [map_zero] using hx
  · intro hx
    rw [hx, map_zero]

/-- The lower tensor quotient kernel lies in the actual upper sum-step fiber. -/
lemma tensorStepLift_kernel [Module.Flat (𝓞 K) N]
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T)
    {Q U : Submodule (𝓞 K) N} (hQU : Q ≤ U) (σ : K →+* ℂ) :
    LinearMap.ker (fiberMap (TensorProduct.map (P.comap T.subtype).mkQ Q.mkQ) σ) ≤
      LinearMap.range (fiberMap (tensorStepLift hPT U) σ) := by
  let q := TensorProduct.map (P.comap T.subtype).mkQ Q.mkQ
  let k : LinearMap.ker q →ₗ[𝓞 K] tensorStep P T U :=
    ((T.subtype.rTensor N).comp (LinearMap.ker q).subtype).codRestrict _ (by
      intro x
      apply tensorStep_mono le_rfl le_rfl hQU
      rw [tensorStep_eq_map_ker hPT Q]
      exact ⟨x, x.property, rfl⟩)
  have hl : (tensorStepLift hPT U).comp k = (LinearMap.ker q).subtype := by
    apply (LinearMap.cancel_left
      (Module.Flat.rTensor_preserves_injective_linearMap (M := N) T.subtype T.injective_subtype)).mp
    rw [← LinearMap.comp_assoc, tensorStepLift_comp]
    rfl
  rw [ker_fiberMap_of_surjective _
    (TensorProduct.map_surjective (P.comap T.subtype).mkQ_surjective Q.mkQ_surjective)]
  rintro x ⟨y, rfl⟩
  refine ⟨fiberMap k σ y, ?_⟩
  rw [← LinearMap.comp_apply, ← fiberMap_comp, hl]

namespace HermitianMetric

variable [Module.Finite (𝓞 K) M] [Module.Finite (𝓞 K) N]

omit [Module.Finite (𝓞 K) M] [Module.Finite (𝓞 K) N] in
/-- The lift of an actual sum step into `T ⊗ N` preserves induced metrics. -/
lemma tensorStepLift_inner [Module.Flat (𝓞 K) N]
    (h : HermitianMetric (K := K) M) (g : HermitianMetric (K := K) N)
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) (U : Submodule (𝓞 K) N)
    (σ : K →+* ℂ) (x y : ComplexFiber (tensorStep P T U) σ) :
    (((h.submodule T).tensor g).fiber σ).inner
      (fiberMap (tensorStepLift hPT U) σ x) (fiberMap (tensorStepLift hPT U) σ y) =
      (((h.tensor g).submodule (tensorStep P T U)).fiber σ).inner x y := by
  rw [show (h.submodule T).tensor g = (h.tensor g).pullback (T.subtype.rTensor N)
      (Module.Flat.rTensor_preserves_injective_linearMap T.subtype T.injective_subtype) from
    (tensor_pullback h g T.subtype T.injective_subtype).symm]
  change ((h.tensor g).fiber σ).inner
    (fiberMap (T.subtype.rTensor N) σ (fiberMap (tensorStepLift hPT U) σ x))
    (fiberMap (T.subtype.rTensor N) σ (fiberMap (tensorStepLift hPT U) σ y)) = _
  simp only [← LinearMap.comp_apply, ← fiberMap_comp, tensorStepLift_comp]
  rfl

/-- The canonical integral consecutive-grade isomorphism is a Hilbert isometry
on every complex fiber. -/
lemma tensorGradeEquiv_inner [Module.Flat (𝓞 K) N]
    (h : HermitianMetric (K := K) M) (g : HermitianMetric (K := K) N)
    {P T : Submodule (𝓞 K) M} (hPT : P ≤ T)
    {Q U : Submodule (𝓞 K) N} (hQU : Q ≤ U)
    [Module.Flat (𝓞 K) (T ⧸ P.comap T.subtype)]
    [Module.Flat (𝓞 K) (U ⧸ Q.comap U.subtype)]
    (σ : K →+* ℂ)
    (x y : ComplexFiber
      (tensorStep P T U ⧸ (tensorStep P T Q).comap (tensorStep P T U).subtype) σ) :
    ((((h.submodule T).quotient (P.comap T.subtype)).tensor
        ((g.submodule U).quotient (Q.comap U.subtype))).fiber σ).inner
      (fiberMap (tensorGradeEquiv hPT Q U).toLinearMap σ x)
      (fiberMap (tensorGradeEquiv hPT Q U).toLinearMap σ y) =
      ((((h.tensor g).submodule (tensorStep P T U)).quotient
        ((tensorStep P T Q).comap (tensorStep P T U).subtype)).fiber σ).inner x y := by
  have hn := pushforward_natural_inner
    ((h.tensor g).submodule (tensorStep P T U)) ((h.submodule T).tensor g)
    (tensorStepLift hPT U) (tensorStepLift_inner h g hPT U)
    ((tensorStep P T Q).comap (tensorStep P T U).subtype).mkQ
    ((tensorStep P T Q).comap (tensorStep P T U).subtype).mkQ_surjective
    (TensorProduct.map (P.comap T.subtype).mkQ Q.mkQ)
    (TensorProduct.map_surjective (P.comap T.subtype).mkQ_surjective Q.mkQ_surjective)
    (tensorGradeInclusion hPT Q U) (tensorGradeInclusion_injective hPT Q U)
    (tensorGradeInclusion_comp hPT Q U).symm (tensorStepLift_kernel hPT hQU) σ x y
  rw [tensor_map_pushforward (h.submodule T) g (P.comap T.subtype).mkQ
    (P.comap T.subtype).mkQ_surjective Q.mkQ Q.mkQ_surjective,
    tensorGradeInclusion_eq, fiberMap_comp] at hn
  let a := (h.submodule T).quotient (P.comap T.subtype)
  have hid : a.pullback LinearMap.id Function.injective_id = a := by
    apply ext_section_inner
    intro τ v w
    simp only [pullback_inner, fiberMap_section, LinearMap.id_apply]
  have ht := tensor_map_pullback a (g.quotient Q) LinearMap.id (submoduleQuotientMap Q U)
    Function.injective_id (submoduleQuotientMap_injective Q U)
  rw [hid, ← g.quotient_submodule hQU] at ht
  have hi := congrArg (fun b : HermitianMetric (K := K)
      ((T ⧸ P.comap T.subtype) ⊗[𝓞 K] (U ⧸ Q.comap U.subtype)) =>
    (b.fiber σ).inner (fiberMap (tensorGradeEquiv hPT Q U).toLinearMap σ x)
      (fiberMap (tensorGradeEquiv hPT Q U).toLinearMap σ y)) ht
  exact hi.symm.trans hn

end HermitianMetric

end BostConjecture.Arithmetic
