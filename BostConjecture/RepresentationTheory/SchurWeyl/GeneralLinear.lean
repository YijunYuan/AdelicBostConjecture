/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.MvPolynomial
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-! Invertible diagonal operators span all diagonal operators.
Two selected TauCeti density slices; see vendor/tauceti-schur-weyl/PROVENANCE.md. -/

@[expose] public section

open Matrix MvPolynomial

namespace MultilinearMap

universe u v v' w w'

variable {ι : Type u} {m : Type v} {n : Type v'} {K : Type w} [Finite ι]

section CommSemiring

variable [Finite m] [Finite n] [CommSemiring K]

/-- **The diagonal of a multilinear form on matrices is a polynomial in the matrix entries.**
Expanding each of the `ι` arguments in the matrix units, the value `Θ (Y, …, Y)` is a sum of
constants times monomials `∏ᵢ Y (a i).1 (a i).2` indexed by the functions `a : ι → m × n`. -/
theorem exists_mvPolynomial_eval_eq_apply_const
    (Θ : MultilinearMap K (fun _ : ι => Matrix m n K) K) :
    ∃ P : MvPolynomial (m × n) K, ∀ Y : Matrix m n K,
      MvPolynomial.eval (fun p : m × n => Y p.1 p.2) P = Θ fun _ => Y := by
  classical
  cases nonempty_fintype ι
  cases nonempty_fintype m
  cases nonempty_fintype n
  refine ⟨∑ a : ι → m × n, C (Θ fun i => single (a i).1 (a i).2 1) * ∏ i, X (a i), fun Y => ?_⟩
  have hY : Y = ∑ p : m × n, Y p.1 p.2 • single p.1 p.2 (1 : K) := by
    simp [Fintype.sum_prod_type, ← matrix_eq_sum_single]
  -- Expand each argument of `Θ` in the matrix units (rewriting only the right-hand side).
  conv_rhs => rw [hY, Θ.map_sum]; simp only [Θ.map_smul_univ, smul_eq_mul]
  simp [mul_comm]

end CommSemiring

section Field

variable {M : Type w'} [Fintype m] [DecidableEq m] [Field K] [Infinite K] [AddCommGroup M]
  [Module K M]

/-- **A multilinear map on matrices whose diagonal vanishes on the invertible matrices has
vanishing diagonal**, over an infinite field `K` and with values in any `K`-vector space `M`. Each
coordinate of the diagonal in a basis of `M` is a polynomial function of the matrix entries (the
square case of `MultilinearMap.exists_mvPolynomial_eval_eq_apply_const`), and over an infinite
field the invertible matrices are Zariski dense. -/
theorem apply_const_eq_zero_of_eq_zero_on_gl (Θ : MultilinearMap K (fun _ : ι => Matrix m m K) M)
    (h : ∀ g : GL m K, (Θ fun _ => (g : Matrix m m K)) = 0) (Y : Matrix m m K) :
    (Θ fun _ => Y) = 0 := by
  let b := Module.Free.chooseBasis K M
  refine b.ext_elem fun i => ?_
  obtain ⟨P, hP⟩ := ((b.coord i).compMultilinearMap Θ).exists_mvPolynomial_eval_eq_apply_const
  have hzero : P = 0 := MvPolynomial.eq_of_eval_eq_on_gl fun g => by simp [hP, h g]
  simpa [hzero] using (hP Y).symm

end Field

end MultilinearMap

open Matrix

open scoped TensorProduct

namespace PiTensorProduct

universe u v w

variable {K : Type u} {V : Type v} {ι : Type w} [Field K] [Infinite K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] [Finite ι]

/-- **The diagonal operator of an endomorphism is a combination of the diagonal operators of the
invertible ones**, over an infinite field and for a finite-dimensional `V`. -/
theorem map_const_mem_span_range_map_const_units (f : V →ₗ[K] V) :
    map (fun _ : ι => f) ∈ Submodule.span K
      (Set.range fun u : (V →ₗ[K] V)ˣ => map fun _ : ι => (u : V →ₗ[K] V)) := by
  classical
  cases nonempty_fintype ι
  set S := Submodule.span K
    (Set.range fun u : (V →ₗ[K] V)ˣ => map fun _ : ι => (u : V →ₗ[K] V)) with _hSdef
  suffices h : ∀ φ : Module.Dual K ((⨂[K] _ : ι, V) →ₗ[K] (⨂[K] _ : ι, V)),
      (∀ y ∈ S, φ y = 0) → φ (map fun _ : ι => f) = 0 by
    exact (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S _).mp fun φ hφ =>
      h φ ((Submodule.mem_dualAnnihilator _).mp hφ)
  intro φ hφ
  set e := Module.finBasis K V with _
  set Θ : MultilinearMap K
      (fun _ : ι => Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K) K :=
    (LinearMap.compMultilinearMap φ
      (mapMultilinear K (fun _ : ι => V) fun _ : ι => V)).compLinearMap
        fun _ => (Matrix.toLinAlgEquiv e).toLinearMap with hΘdef
  have hΘ : ∀ X, (Θ fun _ => X) = φ (map fun _ : ι => Matrix.toLinAlgEquiv e X) := fun _ => by
    simp only [hΘdef, MultilinearMap.compLinearMap_apply, LinearMap.compMultilinearMap_apply,
      mapMultilinear_apply, AlgEquiv.toLinearMap_apply]
  have hgl : ∀ g : GL (Fin (Module.finrank K V)) K,
      (Θ fun _ => (g : Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) K)) = 0 := by
    intro g
    rw [hΘ]
    obtain ⟨u, hu⟩ := g.isUnit.map (Matrix.toLinAlgEquiv e)
    exact hφ _ (Submodule.subset_span ⟨u, congrArg _ (funext fun _ => hu)⟩)
  have hf := Θ.apply_const_eq_zero_of_eq_zero_on_gl hgl (LinearMap.toMatrixAlgEquiv e f)
  rwa [hΘ, Matrix.toLinAlgEquiv_toMatrixAlgEquiv] at hf

/-- **The diagonal operators of the invertible endomorphisms span the same subspace as all the
diagonal operators**, over an infinite field and for a finite-dimensional `V`. -/
theorem span_range_map_const_units_eq_span_range_map_const :
    Submodule.span K (Set.range fun u : (V →ₗ[K] V)ˣ => map fun _ : ι => (u : V →ₗ[K] V)) =
      Submodule.span K (Set.range fun f : V →ₗ[K] V => map fun _ : ι => f) :=
  le_antisymm (Submodule.span_le.2 (by rintro _ ⟨u, rfl⟩; exact Submodule.subset_span ⟨_, rfl⟩))
    (Submodule.span_le.2 (by
      rintro _ ⟨f, rfl⟩; exact map_const_mem_span_range_map_const_units f))

end PiTensorProduct
