module

public import BostConjecture.InvariantTheory.ComplexClosure.Normalization
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Density of principal opens on complex affine varieties

Noether normalization and its Euclidean openness reduce density to the
identity principle for polynomials on products of infinite sets.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.InvariantTheory

open scoped Topology

/-- Noether normalization is represented by actual coordinate polynomials. -/
theorem exists_integral_inj_polynomial_map {K τ : Type*} [Field K] [Finite τ]
    (I : Ideal (MvPolynomial τ K)) (hI : I ≠ ⊤) :
    ∃ n : ℕ, ∃ q : Fin n → MvPolynomial τ K,
      Function.Injective ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval q)) ∧
      ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval q)).toRingHom.IsIntegral := by
  have : Nontrivial (MvPolynomial τ K ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  obtain ⟨n, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg K (MvPolynomial τ K ⧸ I)
  choose q hq using fun i : Fin n => Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  have he : (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval q) = g := by
    ext i
    simpa only [AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk] using hq i
  exact ⟨n, q, he ▸ hg, he ▸ hint⟩

/-- A complex polynomial vanishing on a nonempty Euclidean open set is zero. -/
theorem eq_zero_of_eval_zero_on_open {τ : Type*} [Finite τ]
    (p : MvPolynomial τ ℂ) {U : Set (τ → ℂ)} (hU : IsOpen U) (hne : U.Nonempty)
    (hp : ∀ x ∈ U, MvPolynomial.eval x p = 0) : p = 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨V, hV, hVU⟩ := isOpen_pi_iff'.mp hU x hx
  apply MvPolynomial.funext_set V (fun i => infinite_of_mem_nhds (x i) ((hV i).1.mem_nhds (hV i).2))
  intro y hy
  simpa using hp y (hVU hy)

/-- The nonvanishing set of a nonzero complex polynomial is Euclidean dense. -/
theorem dense_setOf_eval_ne_zero {τ : Type*} [Finite τ]
    {p : MvPolynomial τ ℂ} (hp : p ≠ 0) :
    Dense {x : τ → ℂ | MvPolynomial.eval x p ≠ 0} := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  by_contra! h
  apply hp (eq_zero_of_eval_zero_on_open p hU hne ?_)
  intro x hx
  by_contra hx'
  exact Set.notMem_empty x (h ▸ (show x ∈ U ∩ {x | MvPolynomial.eval x p ≠ 0} from ⟨hx, hx'⟩))

/-- A nonzero regular function has its zero-set image contained in a proper hypersurface
under an integral polynomial map. -/
theorem exists_nonzero_polynomial_vanishing_on_image {K σ τ : Type*} [Field K]
    (I : Ideal (MvPolynomial τ K)) [I.IsPrime] (q : σ → MvPolynomial τ K)
    (hq : ((Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval q)).toRingHom.IsIntegral)
    {u : MvPolynomial τ K} (hu : u ∉ I) :
    ∃ g : MvPolynomial σ K, g ≠ 0 ∧
      ∀ x ∈ MvPolynomial.zeroLocus K I, MvPolynomial.eval x u = 0 →
        MvPolynomial.eval (fun i => MvPolynomial.eval x (q i)) g = 0 := by
  let R := MvPolynomial σ K
  let B := MvPolynomial τ K ⧸ I
  let f : R →ₐ[K] B := (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.aeval q)
  let : Algebra R B := f.toRingHom.toAlgebra
  have : Algebra.IsIntegral R B := ⟨hq⟩
  let v : B := Ideal.Quotient.mk I u
  have hv : v ≠ 0 := fun h => hu (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hP : Ideal.span ({v} : Set B) ≠ ⊥ := by
    intro h
    have hm := Ideal.subset_span (Set.mem_singleton v)
    change v ∈ Ideal.span ({v} : Set B) at hm
    rw [h, Ideal.mem_bot] at hm
    exact hv hm
  obtain ⟨g, hg, hg0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (Ideal.under_ne_bot R hP)
  refine ⟨g, hg0, fun x hx hxu => ?_⟩
  have hg' : f g ∈ Ideal.span ({v} : Set B) := hg
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hg'
  let χ : B →ₐ[K] K := Ideal.Quotient.liftₐ I (MvPolynomial.aeval x) hx
  have hχ (p : MvPolynomial τ K) : χ (Ideal.Quotient.mk I p) = MvPolynomial.eval x p :=
    DFunLike.congr_fun (Ideal.Quotient.liftₐ_comp I (MvPolynomial.aeval x) hx) p
  have hc : χ.comp f = MvPolynomial.aeval (fun i => MvPolynomial.eval x (q i)) := by
    ext i
    simp only [f, AlgHom.comp_apply, MvPolynomial.aeval_X]
    exact hχ (q i)
  have hvχ : χ v = 0 := (hχ u).trans hxu
  have he := congrArg χ hw
  rw [map_mul, hvχ, zero_mul] at he
  exact (DFunLike.congr_fun hc g).symm.trans he

/-- A nonempty principal Zariski open is Euclidean dense in a prime zero locus. -/
theorem dense_principalOpen_zeroLocus {τ : Type*} [Finite τ]
    (I : Ideal (MvPolynomial τ ℂ)) [I.IsPrime]
    {u : MvPolynomial τ ℂ} (hu : u ∉ I) :
    Dense {x : MvPolynomial.zeroLocus ℂ I | MvPolynomial.eval x.val u ≠ 0} := by
  obtain ⟨n, q, hinj, hq⟩ := exists_integral_inj_polynomial_map I Ideal.IsPrime.ne_top'
  obtain ⟨g, hg, hgu⟩ := exists_nonzero_polynomial_vanishing_on_image I q hq hu
  apply dense_iff_inter_open.mpr
  intro U hU hne
  let π : MvPolynomial.zeroLocus ℂ I → Fin n → ℂ :=
    fun x i => MvPolynomial.eval x.val (q i)
  have hopen : IsOpen (π '' U) := isOpenMap_polynomial_normalization I q hq hinj U hU
  obtain ⟨a, ⟨x, hx, rfl⟩, ha⟩ :=
    dense_iff_inter_open.mp (dense_setOf_eval_ne_zero hg) (π '' U) hopen (hne.image π)
  refine ⟨x, hx, fun hxu => ha ?_⟩
  exact hgu x.val x.property hxu

end BostConjecture.InvariantTheory
