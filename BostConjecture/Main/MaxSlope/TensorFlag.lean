/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Tensor.Submodule
public import BostConjecture.Main.MaxSlope.LowerBound

/-!
# The actual lexicographic HN tensor steps

Each step is the image of the kernel of the two quotient maps on
`Eᵢ ⊗ F`. Right exactness identifies it with
`Eᵢ₋₁ ⊗ F + Eᵢ ⊗ Fⱼ`; torsion freeness proves saturation in `E ⊗ F`.
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BostConjecture.Arithmetic

universe u
variable {K : Type*} [Field K]
variable {M N : Type u} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]

/-- The actual sum step in the lexicographic tensor refinement. -/
def tensorStep (P T : Submodule (𝓞 K) M) (Q : Submodule (𝓞 K) N) :
    Submodule (𝓞 K) (M ⊗[𝓞 K] N) :=
  tensorRight N P ⊔ LinearMap.range (TensorProduct.map T.subtype Q.subtype)

/-- Right exactness realizes the sum step as an actual image of a kernel. -/
lemma tensorStep_eq_map_ker {P T : Submodule (𝓞 K) M} (hPT : P ≤ T)
    (Q : Submodule (𝓞 K) N) :
    tensorStep P T Q =
      (LinearMap.ker (TensorProduct.map (P.comap T.subtype).mkQ Q.mkQ)).map
        (T.subtype.rTensor N) := by
  rw [TensorProduct.map_ker
    (LinearMap.exact_subtype_mkQ (P.comap T.subtype)) (P.comap T.subtype).mkQ_surjective
    (LinearMap.exact_subtype_mkQ Q) Q.mkQ_surjective, Submodule.map_sup]
  have he₁ : (LinearMap.range (Q.subtype.lTensor T)).map (T.subtype.rTensor N) =
      LinearMap.range (TensorProduct.map T.subtype Q.subtype) := by
    rw [LinearMap.range_eq_map, ← Submodule.map_comp, ← LinearMap.range_eq_map]
    congr 1
    ext t q
    rfl
  have he₂ : (LinearMap.range ((P.comap T.subtype).subtype.rTensor N)).map
      (T.subtype.rTensor N) = tensorRight N P := by
    let e : (P.comap T.subtype) ≃ₗ[𝓞 K] P :=
      (Submodule.comapSubtypeEquivOfLe hPT)
    have he : (T.subtype.rTensor N).comp ((P.comap T.subtype).subtype.rTensor N) =
        (P.subtype.rTensor N).comp (e.toLinearMap.rTensor N) := by
      ext p n
      rfl
    rw [LinearMap.range_eq_map, ← Submodule.map_comp, ← LinearMap.range_eq_map, he,
      LinearMap.range_comp_of_range_eq_top _
        (LinearMap.range_eq_top.mpr (LinearMap.rTensor_surjective N e.surjective))]
    rfl
  rw [he₁, he₂]
  exact sup_comm _ _

lemma tensorStep_mono {P P' T T' : Submodule (𝓞 K) M}
    {Q Q' : Submodule (𝓞 K) N} (hP : P ≤ P') (hT : T ≤ T') (hQ : Q ≤ Q') :
    tensorStep P T Q ≤ tensorStep P' T' Q' := by
  apply sup_le_sup (tensorRight_mono N hP)
  rintro x ⟨y, rfl⟩
  refine ⟨TensorProduct.map (Submodule.inclusion hT) (Submodule.inclusion hQ) y, ?_⟩
  have he : (TensorProduct.map T'.subtype Q'.subtype).comp
      (TensorProduct.map (Submodule.inclusion hT) (Submodule.inclusion hQ)) =
      TensorProduct.map T.subtype Q.subtype := by
    ext t q
    rfl
  exact LinearMap.congr_fun he y

@[simp]
lemma tensorStep_bot (P T : Submodule (𝓞 K) M) :
    tensorStep P T (⊥ : Submodule (𝓞 K) N) = tensorRight N P := by
  have he : TensorProduct.map T.subtype (⊥ : Submodule (𝓞 K) N).subtype = 0 := by
    ext t q
    simp [show (q : N) = 0 from q.property]
  simp [tensorStep, he]

@[simp]
lemma tensorStep_top {P T : Submodule (𝓞 K) M} (hPT : P ≤ T) :
    tensorStep P T (⊤ : Submodule (𝓞 K) N) = tensorRight N T := by
  have he : LinearMap.range (TensorProduct.map T.subtype (⊤ : Submodule (𝓞 K) N).subtype) =
      tensorRight N T := by
    have he : TensorProduct.map T.subtype (⊤ : Submodule (𝓞 K) N).subtype =
        (T.subtype.rTensor N).comp ((⊤ : Submodule (𝓞 K) N).subtype.lTensor T) := by
      ext t q
      rfl
    rw [he, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (LinearMap.lTensor_surjective T
        (fun x => ⟨⟨x, trivial⟩, rfl⟩)))]
    rfl
  rw [tensorStep, he, sup_eq_right.mpr (tensorRight_mono N hPT)]

variable [NumberField K]
variable [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M]
    [Module.Finite (𝓞 K) N] [Module.Projective (𝓞 K) N]

omit [Module.Finite (𝓞 K) M] [Module.Projective (𝓞 K) M] in
/-- The actual sum step has torsion-free quotient; no saturation is added to
the sum and no integral free basis is used. -/
lemma tensorStep_quotient_torsionFree {P T : Submodule (𝓞 K) M} (hPT : P ≤ T)
    (Q : Submodule (𝓞 K) N)
    [Module.IsTorsionFree (𝓞 K) (M ⧸ P)]
    [Module.Projective (𝓞 K) (M ⧸ T)] [Module.Projective (𝓞 K) (N ⧸ Q)] :
    Module.IsTorsionFree (𝓞 K) ((M ⊗[𝓞 K] N) ⧸ tensorStep P T Q) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro a z haz
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  obtain ⟨x, rfl⟩ := (tensorStep P T Q).mkQ_surjective z
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have hax : a • x ∈ tensorStep P T Q :=
    (Submodule.Quotient.mk_eq_zero _).mp (by simpa using haz)
  rw [tensorStep_eq_map_ker hPT] at hax ⊢
  have hv : a • x ∈ tensorRight N T := by
    obtain ⟨y, _, hy⟩ := hax
    exact ⟨y, hy⟩
  have hx : x ∈ tensorRight N T := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    apply (smul_eq_zero.mp (show a • (tensorRight N T).mkQ x = 0 from by
      rw [← map_smul]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hv)).resolve_left ha
  obtain ⟨y, rfl⟩ := hx
  refine ⟨y, ?_, rfl⟩
  obtain ⟨w, hw, he⟩ := hax
  have he' : w = a • y :=
    Module.Flat.rTensor_preserves_injective_linearMap T.subtype T.injective_subtype
      (by simpa using he)
  rw [he'] at hw
  change TensorProduct.map (P.comap T.subtype).mkQ Q.mkQ y = 0
  have hw' : TensorProduct.map (P.comap T.subtype).mkQ Q.mkQ (a • y) = 0 := hw
  apply (smul_eq_zero.mp (show a • TensorProduct.map (P.comap T.subtype).mkQ Q.mkQ y = 0 from by
    simpa only [map_smul] using hw')).resolve_left ha

namespace HermitianMetric

variable [Nontrivial (K ⊗[𝓞 K] M)] [Nontrivial (K ⊗[𝓞 K] N)]

/-- The actual lexicographic HN tensor step before flattening the two indices. -/
def hnTensorStep (h : HermitianMetric K M) (g : HermitianMetric K N)
    (i j : ℕ) : Submodule (𝓞 K) (M ⊗[𝓞 K] N) :=
  tensorStep (h.hnSubmodule i) (h.hnSubmodule (i + 1)) (g.hnSubmodule j)

lemma hnTensorStep_mono (h : HermitianMetric K M) (g : HermitianMetric K N)
    {i i' j j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') :
    h.hnTensorStep g i j ≤ h.hnTensorStep g i' j' :=
  tensorStep_mono (h.hnSubmodule_monotone hi)
    (h.hnSubmodule_monotone (Nat.add_le_add_right hi 1)) (g.hnSubmodule_monotone hj)

@[simp]
lemma hnTensorStep_zero (h : HermitianMetric K M) (g : HermitianMetric K N)
    (i : ℕ) : h.hnTensorStep g i 0 = tensorRight N (h.hnSubmodule i) := by
  simp [hnTensorStep]

@[simp]
lemma hnTensorStep_length (h : HermitianMetric K M) (g : HermitianMetric K N)
    (i : ℕ) : h.hnTensorStep g i g.hnFlag.length = tensorRight N (h.hnSubmodule (i + 1)) := by
  simp only [hnTensorStep, g.hnSubmodule_length]
  exact tensorStep_top (h.hnSubmodule_monotone (Nat.le_succ i))

instance hnTensorStepQuotientTorsionFree (h : HermitianMetric K M)
    (g : HermitianMetric K N) (i j : ℕ) :
    Module.IsTorsionFree (𝓞 K) ((M ⊗[𝓞 K] N) ⧸ h.hnTensorStep g i j) := by
  unfold hnTensorStep hnSubmodule
  exact tensorStep_quotient_torsionFree
    (integralPart_mono (h.hnFlag.monotone (Nat.le_succ i))) _

instance hnTensorStepQuotientProjective (h : HermitianMetric K M)
    (g : HermitianMetric K N) (i j : ℕ) :
    Module.Projective (𝓞 K) ((M ⊗[𝓞 K] N) ⧸ h.hnTensorStep g i j) := by
  let : Module.FinitePresentation (𝓞 K) ((M ⊗[𝓞 K] N) ⧸ h.hnTensorStep g i j) :=
    Module.finitePresentation_of_finite (𝓞 K) _
  exact Module.Flat.projective_of_finitePresentation

/-- The lexicographic tensor flag, with repeated block endpoints identified. -/
def hnTensorFlag (h : HermitianMetric K M) (g : HermitianMetric K N)
    (k : ℕ) : Submodule (𝓞 K) (M ⊗[𝓞 K] N) :=
  h.hnTensorStep g (k / g.hnFlag.length) (k % g.hnFlag.length)

instance hnTensorFlagQuotientProjective (h : HermitianMetric K M)
    (g : HermitianMetric K N) (k : ℕ) :
    Module.Projective (𝓞 K) ((M ⊗[𝓞 K] N) ⧸ h.hnTensorFlag g k) :=
  hnTensorStepQuotientProjective h g _ _

@[simp]
lemma hnTensorFlag_zero (h : HermitianMetric K M) (g : HermitianMetric K N) :
    h.hnTensorFlag g 0 = ⊥ := by simp [hnTensorFlag]

@[simp]
lemma hnTensorFlag_length (h : HermitianMetric K M) (g : HermitianMetric K N) :
    h.hnTensorFlag g (h.hnFlag.length * g.hnFlag.length) = ⊤ := by
  simp [hnTensorFlag, Nat.ne_of_gt g.hnFlag_length_pos]

lemma hnTensorFlag_monotone (h : HermitianMetric K M)
    (g : HermitianMetric K N) : Monotone (h.hnTensorFlag g) := by
  intro k l hkl
  have hd := Nat.div_le_div_right hkl (c := g.hnFlag.length)
  by_cases he : k / g.hnFlag.length = l / g.hnFlag.length
  · apply h.hnTensorStep_mono g hd
    have hk := Nat.mod_add_div k g.hnFlag.length
    have hl := Nat.mod_add_div l g.hnFlag.length
    rw [he] at hk
    omega
  · have hs : k / g.hnFlag.length + 1 ≤ l / g.hnFlag.length := by omega
    calc
      h.hnTensorFlag g k ≤ h.hnTensorStep g (k / g.hnFlag.length) g.hnFlag.length :=
        h.hnTensorStep_mono g le_rfl (Nat.mod_lt k g.hnFlag_length_pos).le
      _ = tensorRight N (h.hnSubmodule (k / g.hnFlag.length + 1)) := h.hnTensorStep_length g _
      _ ≤ tensorRight N (h.hnSubmodule (l / g.hnFlag.length)) :=
        tensorRight_mono N (h.hnSubmodule_monotone hs)
      _ = h.hnTensorStep g (l / g.hnFlag.length) 0 := (h.hnTensorStep_zero g _).symm
      _ ≤ h.hnTensorFlag g l := h.hnTensorStep_mono g le_rfl (Nat.zero_le _)

end HermitianMetric

end BostConjecture.Arithmetic
