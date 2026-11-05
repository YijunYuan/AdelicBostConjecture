module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.LocalProperties.Submodule
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Descent on a finite principal cover

Compatible localized elements and linear maps descend to the original module.
The constructions use denominator clearing and a unit-ideal partition, without
introducing a new representation of the global module.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

variable {R Q : Type*} [CommRing R] [AddCommGroup Q] [Module R Q]

/-- Compatible sections descend for arbitrary models of the localized modules. -/
theorem existsUnique_of_isLocalizedModule_compatible (s : Set R) [Finite s]
    (hs : Ideal.span s = ⊤)
    (Qₛ : s → Type*) [∀ i, AddCommGroup (Qₛ i)] [∀ i, Module R (Qₛ i)]
    (loc : ∀ i : s, Q →ₗ[R] Qₛ i)
    [∀ i : s, IsLocalizedModule (Submonoid.powers (i : R)) (loc i)]
    (x : ∀ i : s, Qₛ i)
    (h : ∀ i j : s,
      IsLocalizedModule.map (Submonoid.powers (i : R)) (loc i)
        (LocalizedModule.mkLinearMap (Submonoid.powers (i : R)) (Qₛ j)) (loc j) (x i) =
      LocalizedModule.mkLinearMap (Submonoid.powers (i : R)) (Qₛ j) (x j)) :
    ∃! q : Q, ∀ i : s, loc i q = x i := by
  classical
  let := Fintype.ofFinite s
  have hrep (i : s) : ∃ (N : ℕ) (q : Q), ∀ j : s, loc j q = (i : R) ^ N • x j := by
    obtain ⟨n, q, hq⟩ := IsLocalizedModule.Away.surj (loc i) (i : R) (x i)
    have heq (j : s) :
        LocalizedModule.mkLinearMap (Submonoid.powers (i : R))
            (Qₛ j) (loc j q) =
          LocalizedModule.mkLinearMap (Submonoid.powers (i : R))
            (Qₛ j) ((i : R) ^ n • x j) := by
      have hj := congrArg (IsLocalizedModule.map (Submonoid.powers (i : R))
        (loc i) (LocalizedModule.mkLinearMap (Submonoid.powers (i : R))
          (Qₛ j)) (loc j)) hq
      simpa only [map_smul, IsLocalizedModule.map_apply, h i j] using hj.symm
    choose m hm using fun j => IsLocalizedModule.Away.exists_of_eq (i : R) (heq j)
    let B := Finset.univ.sup m
    refine ⟨B + n, (i : R) ^ B • q, ?_⟩
    intro j
    have hj : m j ≤ B := Finset.le_sup (f := m) (Finset.mem_univ j)
    calc
      loc j ((i : R) ^ B • q) = (i : R) ^ (B - m j) • ((i : R) ^ m j • loc j q) := by
        rw [map_smul, ← mul_smul, ← pow_add, Nat.sub_add_cancel hj]
      _ = (i : R) ^ (B - m j) • ((i : R) ^ m j • ((i : R) ^ n • x j)) := by rw [hm j]
      _ = (i : R) ^ (B + n) • x j := by
        rw [← mul_smul, ← pow_add, Nat.sub_add_cancel hj, ← mul_smul, ← pow_add]
  choose N q hq using hrep
  have hspan := Ideal.span_range_pow_eq_top s hs N
  have hone : (1 : R) ∈ Ideal.span (Set.range (fun i : s => (i : R) ^ N i)) := by
    rw [hspan]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hone
  refine ⟨∑ i, c i • q i, ?_, ?_⟩
  · intro j
    simp only [map_sum, map_smul, hq, ← mul_smul, ← Finset.sum_smul]
    simpa only [smul_eq_mul, one_smul] using congrArg (fun r : R => r • x j) hc
  · intro y hy
    apply Module.eq_of_isLocalized_span s hs _ loc
    intro j
    rw [hy]
    simp only [map_sum, map_smul, hq, ← mul_smul, ← Finset.sum_smul]
    simpa only [smul_eq_mul, one_smul] using (congrArg (fun r : R => r • x j) hc).symm


/-- Compatible sections on a finite principal cover come from a unique global element. -/
theorem existsUnique_of_localization_compatible (s : Set R) [Finite s]
    (hs : Ideal.span s = ⊤)
    (x : ∀ r : s, LocalizedModule (Submonoid.powers (r : R)) Q)
    (h : ∀ i j : s,
      IsLocalizedModule.map (Submonoid.powers (i : R))
        (LocalizedModule.mkLinearMap (Submonoid.powers (i : R)) Q)
        (LocalizedModule.mkLinearMap (Submonoid.powers (i : R))
          (LocalizedModule (Submonoid.powers (j : R)) Q))
        (LocalizedModule.mkLinearMap (Submonoid.powers (j : R)) Q) (x i) =
      LocalizedModule.mkLinearMap (Submonoid.powers (i : R))
        (LocalizedModule (Submonoid.powers (j : R)) Q) (x j)) :
    ∃! q : Q, ∀ r : s, LocalizedModule.mkLinearMap (Submonoid.powers (r : R)) Q q = x r :=
  existsUnique_of_isLocalizedModule_compatible s hs
    (fun i => LocalizedModule (Submonoid.powers (i : R)) Q)
    (fun i => LocalizedModule.mkLinearMap (Submonoid.powers (i : R)) Q) x h

open scoped TensorProduct

/-- Descent in the scalar-extension models, with overlaps expressed by tensoring
the two localization rings. -/
theorem existsUnique_of_tensorLocalization_compatible (s : Set R) [Finite s]
    (hs : Ideal.span s = ⊤)
    (x : ∀ i : s, Localization.Away (i : R) ⊗[R] Q)
    (h : ∀ i j : s,
      TensorProduct.map (Algebra.TensorProduct.includeLeft :
        Localization.Away (i : R) →ₐ[R]
          Localization.Away (i : R) ⊗[R] Localization.Away (j : R)).toLinearMap
        (LinearMap.id : Q →ₗ[R] Q) (x i) =
      TensorProduct.map (Algebra.TensorProduct.includeRight :
        Localization.Away (j : R) →ₐ[R]
          Localization.Away (i : R) ⊗[R] Localization.Away (j : R)).toLinearMap
        (LinearMap.id : Q →ₗ[R] Q) (x j)) :
    ∃! q : Q, ∀ i : s, (1 : Localization.Away (i : R)) ⊗ₜ[R] q = x i := by
  apply existsUnique_of_isLocalizedModule_compatible s hs
    (fun i => Localization.Away (i : R) ⊗[R] Q)
    (fun i => TensorProduct.mk R (Localization.Away (i : R)) Q 1) x
  intro i j
  let r := TensorProduct.map (Algebra.TensorProduct.includeRight :
    Localization.Away (j : R) →ₐ[R]
      Localization.Away (i : R) ⊗[R] Localization.Away (j : R)).toLinearMap
    (LinearMap.id : Q →ₗ[R] Q)
  let l := TensorProduct.map (Algebra.TensorProduct.includeLeft :
    Localization.Away (i : R) →ₐ[R]
      Localization.Away (i : R) ⊗[R] Localization.Away (j : R)).toLinearMap
    (LinearMap.id : Q →ₗ[R] Q)
  let : IsLocalizedModule (Submonoid.powers (i : R))
      (Algebra.TensorProduct.includeRight : Localization.Away (j : R) →ₐ[R]
        Localization.Away (i : R) ⊗[R] Localization.Away (j : R)).toLinearMap := by
    change IsLocalizedModule (Submonoid.powers (i : R))
      (TensorProduct.mk R (Localization.Away (i : R)) (Localization.Away (j : R)) 1)
    infer_instance
  let : IsLocalizedModule (Submonoid.powers (i : R)) r :=
    IsLocalizedModule.rTensor (R := R) (A := R) (N := Q) (S := Submonoid.powers (i : R))
      (Algebra.TensorProduct.includeRight : Localization.Away (j : R) →ₐ[R]
        Localization.Away (i : R) ⊗[R] Localization.Away (j : R)).toLinearMap
  let e := IsLocalizedModule.linearEquiv (Submonoid.powers (i : R))
    (LocalizedModule.mkLinearMap (Submonoid.powers (i : R))
      (Localization.Away (j : R) ⊗[R] Q)) r
  apply e.injective
  have he : e.toLinearMap ∘ₗ
      IsLocalizedModule.map (Submonoid.powers (i : R))
        (TensorProduct.mk R (Localization.Away (i : R)) Q 1)
        (LocalizedModule.mkLinearMap (Submonoid.powers (i : R))
          (Localization.Away (j : R) ⊗[R] Q))
        (TensorProduct.mk R (Localization.Away (j : R)) Q 1) = l := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers (i : R))
      (TensorProduct.mk R (Localization.Away (i : R)) Q 1) r
    apply LinearMap.ext
    intro q
    simp only [LinearMap.comp_apply, IsLocalizedModule.map_apply]
    change e (LocalizedModule.mkLinearMap (Submonoid.powers (i : R))
      (Localization.Away (j : R) ⊗[R] Q) (1 ⊗ₜ[R] q)) = l (1 ⊗ₜ[R] q)
    rw [show e (LocalizedModule.mkLinearMap (Submonoid.powers (i : R))
      (Localization.Away (j : R) ⊗[R] Q) (1 ⊗ₜ[R] q)) = r (1 ⊗ₜ[R] q) from
      IsLocalizedModule.linearEquiv_apply _ _ _ _]
    simp [l, r]
  have hei := LinearMap.congr_fun he (x i)
  change e (IsLocalizedModule.map _ _ _ _ (x i)) = _ at hei
  rw [hei]
  simpa only [e, IsLocalizedModule.linearEquiv_apply] using h i j

variable {P : Type*} [AddCommGroup P] [Module R P]

/-- Local linear maps whose values agree on overlaps descend uniquely. It suffices
to check compatibility on the images of the original module. -/
theorem existsUnique_linearMap_of_localization_compatible (s : Set R) [Finite s]
    (hs : Ideal.span s = ⊤)
    (u : ∀ r : s, LocalizedModule (Submonoid.powers (r : R)) P →ₗ[R]
      LocalizedModule (Submonoid.powers (r : R)) Q)
    (h : ∀ (p : P) (i j : s),
      IsLocalizedModule.map (Submonoid.powers (i : R))
        (LocalizedModule.mkLinearMap (Submonoid.powers (i : R)) Q)
        (LocalizedModule.mkLinearMap (Submonoid.powers (i : R))
          (LocalizedModule (Submonoid.powers (j : R)) Q))
        (LocalizedModule.mkLinearMap (Submonoid.powers (j : R)) Q)
        (u i (LocalizedModule.mkLinearMap (Submonoid.powers (i : R)) P p)) =
      LocalizedModule.mkLinearMap (Submonoid.powers (i : R))
        (LocalizedModule (Submonoid.powers (j : R)) Q)
        (u j (LocalizedModule.mkLinearMap (Submonoid.powers (j : R)) P p))) :
    ∃! U : P →ₗ[R] Q, ∀ i : s,
      IsLocalizedModule.map (Submonoid.powers (i : R))
        (LocalizedModule.mkLinearMap (Submonoid.powers (i : R)) P)
        (LocalizedModule.mkLinearMap (Submonoid.powers (i : R)) Q) U = u i := by
  classical
  let locP (r : s) := LocalizedModule.mkLinearMap (Submonoid.powers (r : R)) P
  let locQ (r : s) := LocalizedModule.mkLinearMap (Submonoid.powers (r : R)) Q
  have hex (p : P) : ∃ q : Q, ∀ i : s, locQ i q = u i (locP i p) :=
    (existsUnique_of_localization_compatible s hs (fun i => u i (locP i p)) (h p)).exists
  choose g hg using hex
  let U : P →ₗ[R] Q :=
    { toFun := g
      map_add' := by
        intro p q
        apply Module.eq_of_isLocalized_span s hs _ locQ
        intro i
        simp only [hg, map_add]
      map_smul' := by
        intro r p
        apply Module.eq_of_isLocalized_span s hs _ locQ
        intro i
        simp only [hg, map_smul, RingHom.id_apply] }
  have hU (i : s) : IsLocalizedModule.map (Submonoid.powers (i : R)) (locP i) (locQ i) U = u i := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers (i : R)) (locP i) (locQ i)
    ext p
    simpa only [LinearMap.comp_apply, IsLocalizedModule.map_apply, U, LinearMap.coe_mk,
      AddHom.coe_mk] using hg p i
  refine ⟨U, hU, ?_⟩
  intro V hV
  ext p
  apply Module.eq_of_isLocalized_span s hs _ locQ
  intro i
  have hv := LinearMap.congr_fun (hV i) (locP i p)
  change locQ i (V p) = locQ i (g p)
  rw [hg]
  simpa only [locP, IsLocalizedModule.map_apply] using hv

/-- Injectivity can be checked on the localizations of a principal cover. -/
theorem injective_of_localizedMap_injective (s : Set R) (hs : Ideal.span s = ⊤)
    (U : P →ₗ[R] Q)
    (h : ∀ i : s, Function.Injective
      (IsLocalizedModule.map (Submonoid.powers (i : R))
        (LocalizedModule.mkLinearMap (Submonoid.powers (i : R)) P)
        (LocalizedModule.mkLinearMap (Submonoid.powers (i : R)) Q) U)) :
    Function.Injective U := by
  intro p q hpq
  apply Module.eq_of_isLocalized_span s hs _
    (fun i => LocalizedModule.mkLinearMap (Submonoid.powers (i : R)) P)
  intro i
  apply h i
  simp only [IsLocalizedModule.map_apply, hpq]

end BostConjecture.Geometry
