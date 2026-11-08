/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.InvariantTheory.ComplexClosure.IntegralLifting
public import BostConjecture.InvariantTheory.ComplexClosure.FiniteFiber
public import BostConjecture.InvariantTheory.ComplexClosure.Coordinates
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.Topology.Sequences

/-!
# Polynomial normalization maps on complex points

The algebraic lifting and root-persistence producers are applied to the
coordinate quotient and its actual complex points.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open Filter
open scoped Topology

/-- A character of a coordinate quotient is evaluation at an actual zero-locus point. -/
theorem exists_point_of_quotient_algHom {K τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K)) (ψ : (MvPolynomial τ K ⧸ I) →ₐ[K] K) :
    ∃ x ∈ MvPolynomial.zeroLocus K I,
      ∀ p, ψ (Ideal.Quotient.mk I p) = MvPolynomial.eval x p := by
  let x : τ → K := fun i => ψ (Ideal.Quotient.mk I (MvPolynomial.X i))
  have he : MvPolynomial.aeval x = ψ.comp (Ideal.Quotient.mkₐ K I) := by
    ext i
    simp [x]
  refine ⟨x, ?_, fun p => (DFunLike.congr_fun he p).symm⟩
  intro p hp
  rw [he, AlgHom.comp_apply]
  change ψ (Ideal.Quotient.mk I p) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

/-- A regular function on an integral polynomial normalization has a monic equation
whose every specialized root is realized by a point in the corresponding fiber. -/
theorem exists_monic_lifting_polynomial {K σ τ : Type*} [Field K] [IsAlgClosed K] [Finite τ]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime] (q : σ → MvPolynomial τ K)
    (hq : ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval q)).toRingHom.IsIntegral)
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval q)))
    (u : MvPolynomial τ K) :
    ∃ F : Polynomial (MvPolynomial σ K), F.Monic ∧ 0 < F.natDegree ∧
      (∀ x ∈ MvPolynomial.zeroLocus K I,
        (F.map (MvPolynomial.eval (fun i => MvPolynomial.eval x (q i)))).IsRoot
          (MvPolynomial.eval x u)) ∧
      ∀ a z, (F.map (MvPolynomial.eval a)).IsRoot z →
        ∃ x ∈ MvPolynomial.zeroLocus K I,
          (∀ i, MvPolynomial.eval x (q i) = a i) ∧ MvPolynomial.eval x u = z := by
  let R := MvPolynomial σ K
  let B := MvPolynomial τ K ⧸ I
  let f : R →ₐ[K] B := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval q)
  let : Algebra R B := f.toRingHom.toAlgebra
  have : IsScalarTower K R B := IsScalarTower.of_algHom f
  have : Module.IsTorsionFree R B := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : Algebra.IsIntegral R B := ⟨hq⟩
  let v : B := Ideal.Quotient.mk I u
  have hv : IsIntegral R v := Algebra.IsIntegral.isIntegral v
  refine ⟨minpoly R v, minpoly.monic hv, minpoly.natDegree_pos hv, ?_, ?_⟩
  · intro x hx
    let χ : B →ₐ[K] K := Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) hx
    have hχ (p : MvPolynomial τ K) : χ (Ideal.Quotient.mk I p) = MvPolynomial.eval x p :=
      DFunLike.congr_fun (Ideal.Quotient.liftₐ_comp I (MvPolynomial.aeval x) hx) p
    have hc : χ.comp f = MvPolynomial.aeval (fun i => MvPolynomial.eval x (q i)) := by
      ext i
      simp only [f, AlgHom.comp_apply, MvPolynomial.aeval_X]
      exact hχ (q i)
    have hc' : χ.toRingHom.comp f.toRingHom =
        MvPolynomial.eval (fun i => MvPolynomial.eval x (q i)) := congrArg AlgHom.toRingHom hc
    have h := congrArg χ (minpoly.aeval R v)
    change χ.toRingHom ((minpoly R v).eval₂ f.toRingHom v) = χ 0 at h
    rw [map_zero, Polynomial.hom_eval₂, hc'] at h
    change (minpoly R v).eval₂ _ (χ (Ideal.Quotient.mk I u)) = 0 at h
    rw [hχ] at h
    simpa only [Polynomial.IsRoot, Polynomial.eval_map] using h
  · intro a z hz
    have haeval : (MvPolynomial.aeval a : R →ₐ[K] K).toRingHom =
        MvPolynomial.eval a := by
      ext i
      · change MvPolynomial.aeval a (MvPolynomial.C i) =
          MvPolynomial.eval a (MvPolynomial.C i)
        simp
      · change MvPolynomial.aeval a (MvPolynomial.X i) =
          MvPolynomial.eval a (MvPolynomial.X i)
        rw [MvPolynomial.aeval_X, MvPolynomial.eval_X]
    obtain ⟨ψ, hψ, hψu⟩ := exists_algHom_of_minpoly_eq_zero (R := R) (B := B)
      v (MvPolynomial.aeval a) z (by
        rw [haeval]
        simpa only [Polynomial.IsRoot, Polynomial.eval_map] using hz)
    obtain ⟨x, hx, he⟩ := exists_point_of_quotient_algHom I ψ
    refine ⟨x, hx, fun i => ?_, ?_⟩
    · have h := hψ (MvPolynomial.X i)
      change ψ (f (MvPolynomial.X i)) = MvPolynomial.aeval a (MvPolynomial.X i) at h
      simp only [f, AlgHom.comp_apply] at h
      rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X] at h
      change ψ (Ideal.Quotient.mk I (q i)) = a i at h
      rwa [he] at h
    · exact (he u).symm.trans hψu

/-- Base sequences approaching a point admit a subsequence of lifts approaching that point. -/
theorem exists_lifts_tendsto_subseq {σ τ : Type*} [Finite τ]
    (I : Ideal (MvPolynomial τ ℂ)) [I.IsPrime] (q : σ → MvPolynomial τ ℂ)
    (hq : ((Ideal.Quotient.mkₐ ℂ I).comp (MvPolynomial.aeval q)).toRingHom.IsIntegral)
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ ℂ I).comp (MvPolynomial.aeval q)))
    {p : τ → ℂ} (hp : p ∈ MvPolynomial.zeroLocus ℂ I)
    {a : ℕ → σ → ℂ}
    (ha : Tendsto a atTop (𝓝 (fun i => MvPolynomial.eval p (q i)))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ x : ℕ → τ → ℂ,
      (∀ k, x k ∈ MvPolynomial.zeroLocus ℂ I ∧
        ∀ i, MvPolynomial.eval (x k) (q i) = a (φ k) i) ∧ Tendsto x atTop (𝓝 p) := by
  classical
  let S := {x : τ → ℂ | x ∈ MvPolynomial.zeroLocus ℂ I ∧
    ∀ i, MvPolynomial.eval x (q i) = MvPolynomial.eval p (q i)} \ {p}
  have hS : S.Finite := (finite_zeroLocus_fiber I q hq _).sdiff
  obtain ⟨u, hup, huS⟩ := exists_polynomial_separator S hS (p := p) (by simp [S])
  obtain ⟨F, hF, hd, hFroot, hFlift⟩ := exists_monic_lifting_polynomial I q hq hinj u
  obtain ⟨z, hz, hzt⟩ := exists_roots_tendsto_specialization F hF hd ha
    (by simpa only [hup] using hFroot p hp)
  choose x hx hxa hxu using fun k => hFlift (a k) (z k) (hz k)
  obtain ⟨B, hB⟩ := exists_bound_zeroLocus_fibers I q hq ha
  have hcompact : IsCompact (Set.univ.pi (fun i : τ => Metric.closedBall (0 : ℂ) (B i))) :=
    isCompact_univ_pi (fun i => isCompact_closedBall 0 (B i))
  obtain ⟨y, _, φ, hφ, hxt⟩ := hcompact.tendsto_subseq (x := x) (fun k => by
    intro i _
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      (show ‖x k i‖ ≤ (B i : ℝ) from hB k (x k) (hx k) (hxa k) i))
  have hy : y ∈ MvPolynomial.zeroLocus ℂ I :=
    (isClosed_zeroLocus I).mem_of_tendsto hxt (Eventually.of_forall (fun k => hx (φ k)))
  have hyq (i : σ) : MvPolynomial.eval y (q i) = MvPolynomial.eval p (q i) := by
    have h₁ := (MvPolynomial.continuous_eval (q i)).continuousAt.tendsto.comp hxt
    have h₂ := ((continuous_apply i).continuousAt.tendsto.comp ha).comp hφ.tendsto_atTop
    exact tendsto_nhds_unique h₁ (by simpa only [Function.comp_def, hxa] using h₂)
  have hyu : MvPolynomial.eval y u = 1 := by
    have h₁ := (MvPolynomial.continuous_eval u).continuousAt.tendsto.comp hxt
    exact tendsto_nhds_unique h₁ (by
      simpa only [Function.comp_def, hxu] using hzt.comp hφ.tendsto_atTop)
  have hyp : y = p := by
    by_contra hne
    have hz := huS y ⟨⟨hy, hyq⟩, by simpa only [Set.mem_singleton_iff] using hne⟩
    exact one_ne_zero (hyu.symm.trans hz)
  subst y
  exact ⟨φ, hφ, x ∘ φ, fun k => ⟨hx (φ k), hxa (φ k)⟩, hxt⟩

/-- An integral injective polynomial normalization is open on complex points. -/
theorem isOpenMap_polynomial_normalization {σ τ : Type*} [Finite σ] [Finite τ]
    (I : Ideal (MvPolynomial τ ℂ)) [I.IsPrime] (q : σ → MvPolynomial τ ℂ)
    (hq : ((Ideal.Quotient.mkₐ ℂ I).comp (MvPolynomial.aeval q)).toRingHom.IsIntegral)
    (hinj : Function.Injective ((Ideal.Quotient.mkₐ ℂ I).comp (MvPolynomial.aeval q))) :
    IsOpenMap (fun p : MvPolynomial.zeroLocus ℂ I =>
      fun i => MvPolynomial.eval p.val (q i)) := by
  intro U hU
  apply isClosed_compl_iff.mp
  apply IsSeqClosed.isClosed
  intro a b ha hb
  rintro ⟨p, hpU, rfl⟩
  obtain ⟨φ, _, x, hx, hxt⟩ := exists_lifts_tendsto_subseq I q hq hinj p.property hb
  have ht : Tendsto (fun k => (⟨x k, (hx k).1⟩ : MvPolynomial.zeroLocus ℂ I))
      atTop (𝓝 p) := tendsto_subtype_rng.mpr hxt
  obtain ⟨k, hk⟩ := (ht.eventually (hU.mem_nhds hpU)).exists
  exact ha (φ k) ⟨⟨x k, (hx k).1⟩, hk, funext (hx k).2⟩

end BostConjecture.InvariantTheory
