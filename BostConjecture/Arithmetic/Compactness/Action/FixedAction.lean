/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Compactness.Action.TraceActionFiniteness

/-!
# Constant integral actions and genuine module identifications

Finite tuples of integral action matrices have constant subsequences. Equality
on an integral basis of the coefficient ring forces the corresponding integer
basis equivalence to be linear over the entire ring of integers.

Reference: this paper, page 11, Lemma 7.1.
-/

@[expose] public section

noncomputable section

open NumberField Matrix

namespace BostConjecture.Arithmetic.Compactness

/-- Infinite pigeonhole, with an actual increasing subsequence. -/
theorem exists_constant_subsequence_of_finite_range {α : Type*} {f : ℕ → α}
    (hf : (Set.range f).Finite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, f (φ n) = f (φ 0) := by
  let : Finite (Set.range f) := hf.to_subtype
  let g : ℕ → Set.range f := fun n => ⟨f n, ⟨n, rfl⟩⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber g
  let := hy
  let e := Nat.Subtype.orderIsoOfNat (g ⁻¹' {y})
  refine ⟨fun n => (e n).val, e.strictMono, ?_⟩
  intro n
  have hn := congrArg Subtype.val (e n).property
  have h0 := congrArg Subtype.val (e 0).property
  exact hn.trans h0.symm

variable {K : Type*} [Field K]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
variable {M N : Type*} [AddCommGroup M] [Module (𝓞 K) M]
    [AddCommGroup N] [Module (𝓞 K) N]

/-- Multiplication matrices are determined by an integral basis of the ring. -/
theorem action_matrix_eq_of_basis (a : Module.Basis κ ℤ (𝓞 K))
    (b : Module.Basis ι ℤ M) (c : Module.Basis ι ℤ N)
    (h : ∀ j, LinearMap.toMatrix b b (Algebra.lsmul ℤ ℤ M (a j)) =
      LinearMap.toMatrix c c (Algebra.lsmul ℤ ℤ N (a j))) (r : 𝓞 K) :
    LinearMap.toMatrix b b (Algebra.lsmul ℤ ℤ M r) =
      LinearMap.toMatrix c c (Algebra.lsmul ℤ ℤ N r) := by
  let f : 𝓞 K →ₗ[ℤ] Matrix ι ι ℤ :=
    (LinearMap.toMatrix b b).toLinearMap.comp (Algebra.lsmul ℤ ℤ M).toLinearMap
  let g : 𝓞 K →ₗ[ℤ] Matrix ι ι ℤ :=
    (LinearMap.toMatrix c c).toLinearMap.comp (Algebra.lsmul ℤ ℤ N).toLinearMap
  have he : f = g := a.ext h
  exact LinearMap.congr_fun he r

/-- Matching all multiplication matrices upgrades the canonical integer
basis equivalence to an isomorphism of the actual integral modules. -/
def linearEquivOfActionMatrices (b : Module.Basis ι ℤ M) (c : Module.Basis ι ℤ N)
    (h : ∀ r : 𝓞 K, LinearMap.toMatrix b b (Algebra.lsmul ℤ ℤ M r) =
      LinearMap.toMatrix c c (Algebra.lsmul ℤ ℤ N r)) : M ≃ₗ[𝓞 K] N where
  __ := b.repr.trans c.repr.symm
  map_smul' r x := by
    apply c.repr.injective
    change c.repr (c.repr.symm (b.repr (r • x))) =
      c.repr (r • c.repr.symm (b.repr x))
    rw [LinearEquiv.apply_symm_apply]
    apply DFunLike.coe_injective
    have hb := LinearMap.toMatrix_mulVec_repr b b (Algebra.lsmul ℤ ℤ M r) x
    have hc := LinearMap.toMatrix_mulVec_repr c c (Algebra.lsmul ℤ ℤ N r)
      (c.repr.symm (b.repr x))
    simp only [Algebra.lsmul_apply] at hb hc
    rw [LinearEquiv.apply_symm_apply] at hc
    exact hb.symm.trans ((congrArg (fun A => A *ᵥ b.repr x) (h r)).trans hc)

@[simp]
theorem linearEquivOfActionMatrices_apply_basis
    (b : Module.Basis ι ℤ M) (c : Module.Basis ι ℤ N)
    (h : ∀ r : 𝓞 K, LinearMap.toMatrix b b (Algebra.lsmul ℤ ℤ M r) =
      LinearMap.toMatrix c c (Algebra.lsmul ℤ ℤ N r)) (i : ι) :
    linearEquivOfActionMatrices b c h (b i) = c i := by
  change c.repr.symm (b.repr (b i)) = c i
  simp

section Sequence

universe u

variable [NumberField K] [Finite κ]
variable (A : ℕ → Type u) [∀ n, AddCommGroup (A n)] [∀ n, Module (𝓞 K) (A n)]

omit [NumberField K] in
/-- Finite possibilities on an integral ring basis give a subsequence of
actual ring-linear module identifications carrying each integral frame. -/
theorem exists_module_identifications_of_finite_actions
    (a : Module.Basis κ ℤ (𝓞 K)) (b : ∀ n, Module.Basis ι ℤ (A n))
    (hf : ∀ j, (Set.range fun n =>
      LinearMap.toMatrix (b n) (b n) (Algebra.lsmul ℤ ℤ (A n) (a j))).Finite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ e : ∀ n, A (φ 0) ≃ₗ[𝓞 K] A (φ n),
        ∀ n i, e n (b (φ 0) i) = b (φ n) i := by
  let f := fun n j => LinearMap.toMatrix (b n) (b n) (Algebra.lsmul ℤ ℤ (A n) (a j))
  have hfin : (Set.range f).Finite := by
    apply (Set.Finite.pi' hf).subset
    rintro _ ⟨n, rfl⟩ j
    exact ⟨n, rfl⟩
  obtain ⟨φ, hφ, he⟩ := exists_constant_subsequence_of_finite_range hfin
  have hmat (n : ℕ) (r : 𝓞 K) :
      LinearMap.toMatrix (b (φ 0)) (b (φ 0)) (Algebra.lsmul ℤ ℤ (A (φ 0)) r) =
        LinearMap.toMatrix (b (φ n)) (b (φ n)) (Algebra.lsmul ℤ ℤ (A (φ n)) r) :=
    action_matrix_eq_of_basis a _ _ (fun j => (congrFun (he n) j).symm) r
  exact ⟨φ, hφ, fun n => linearEquivOfActionMatrices _ _ (hmat n),
    fun n i => linearEquivOfActionMatrices_apply_basis _ _ _ i⟩

variable [∀ n, Module.Finite (𝓞 K) (A n)] [∀ n, Module.Projective (𝓞 K) (A n)]

/-- Compact actual trace frames yield a fixed underlying arithmetic module
after passage to an increasing subsequence. -/
theorem exists_module_identifications_of_compact_frames
    (a : Module.Basis κ ℤ (𝓞 K))
    (h : ∀ n, HermitianMetric K (A n)) (b : ∀ n, Module.Basis ι ℤ (A n))
    (b₀ : ∀ n, OrthonormalBasis ι ℝ (h n).TraceSpace)
    {S : Set (GeneralLinearGroup ι ℝ)} (hS : IsCompact S)
    (B : ℕ → GeneralLinearGroup ι ℝ) (hBS : ∀ n, B n ∈ S)
    (hB : ∀ n, (B n).val = (b₀ n).toBasis.toMatrix ((h n).traceBasis (b n))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ e : ∀ n, A (φ 0) ≃ₗ[𝓞 K] A (φ n),
        ∀ n i, e n (b (φ 0) i) = b (φ n) i := by
  apply exists_module_identifications_of_finite_actions A a b
  intro j
  apply (finite_actual_integral_actions (a j) hS).subset
  rintro _ ⟨n, rfl⟩
  exact integral_action_mem (h n) (a j) (b n) (b₀ n) (B n) (hBS n) (hB n)

end Sequence

end BostConjecture.Arithmetic.Compactness
