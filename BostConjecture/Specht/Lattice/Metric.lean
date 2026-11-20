/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.ExternalCode.TauCeti.Lattice.Covolume
public import BostConjecture.Specht.Lattice.Integral

/-!
# The orthonormal word metric on the integral Specht lattice

Integer word coefficients embed in `EuclideanSpace`, whose coordinate vectors
are orthonormal. The image of the orbit lattice is discrete and is a full
integer lattice in its own real linear span. Reference: this paper, Section 3.2.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n d : ℕ} {μ : YoungDiagram}

/-- Integer word vectors in the Hilbert space with orthonormal word coordinates. -/
def realCast (n d : ℕ) :
    ((Fin n → Fin d) → ℤ) →ₗ[ℤ] EuclideanSpace ℝ (Fin n → Fin d) where
  toFun x := WithLp.toLp 2 (fun w => (x w : ℝ))
  map_add' x y := by ext w; simp
  map_smul' a x := by ext w; simp

theorem realCast_injective : Function.Injective (realCast n d) := by
  intro x y h
  ext w
  exact Int.cast_injective (congrArg (fun z : EuclideanSpace ℝ (Fin n → Fin d) => z w) h)

/-- The word metric is the sum of coordinate products. -/
theorem inner_realCast (x y : (Fin n → Fin d) → ℤ) :
    inner ℝ (realCast n d x) (realCast n d y) = ∑ w, (x w : ℝ) * (y w : ℝ) := by
  simp [PiLp.inner_apply, realCast, mul_comm]

@[simp] theorem realCast_single (w : Fin n → Fin d) :
    realCast n d (Pi.single w 1) = EuclideanSpace.basisFun (Fin n → Fin d) ℝ w := by
  classical
  ext a
  simp [realCast, EuclideanSpace.basisFun_apply, EuclideanSpace.single, Pi.single_apply]

theorem realCast_single_orthonormal :
    Orthonormal ℝ (fun w : Fin n → Fin d => realCast n d (Pi.single w 1)) := by
  simpa only [realCast_single] using (EuclideanSpace.basisFun (Fin n → Fin d) ℝ).orthonormal

/-- The image of the integral orbit lattice in the real word Hilbert space. -/
def realLattice (t : Tableau n μ) : Submodule ℤ (EuclideanSpace ℝ (Fin n → Fin (μ.colLen 0))) :=
  (orbitLattice t).map (realCast n (μ.colLen 0))

/-- The real span in which the Specht lattice's covolume is measured. -/
def realSpan (t : Tableau n μ) : Submodule ℝ (EuclideanSpace ℝ (Fin n → Fin (μ.colLen 0))) :=
  Submodule.span ℝ (realLattice t : Set _)

/-- The same lattice, regarded as a submodule of its real span. -/
def spanLattice (t : Tableau n μ) : Submodule ℤ (realSpan t) :=
  ZLattice.comap ℝ (realLattice t) (realSpan t).subtype

/-- Nonzero integer coordinate vectors have Hilbert norm at least one. -/
theorem one_le_norm_realCast {x : (Fin n → Fin d) → ℤ} (hx : x ≠ 0) :
    1 ≤ ‖realCast n d x‖ := by
  obtain ⟨w, hw⟩ : ∃ w, x w ≠ 0 := Function.ne_iff.mp hx
  have hi : (1 : ℝ) ≤ |(x w : ℝ)| := by exact_mod_cast Int.one_le_abs hw
  exact hi.trans (by simpa [realCast, Real.norm_eq_abs] using
    PiLp.norm_apply_le (realCast n d x) w)

theorem one_le_norm_realLattice (t : Tableau n μ) (x : realLattice t) (hx : x ≠ 0) :
    1 ≤ ‖x‖ := by
  obtain ⟨y, hy, he⟩ := x.property
  have hy0 : y ≠ 0 := by
    intro h
    apply hx
    apply Subtype.ext
    simpa [h] using he.symm
  change 1 ≤ ‖(x : EuclideanSpace ℝ (Fin n → Fin (μ.colLen 0)))‖
  simpa only [he] using one_le_norm_realCast hy0

instance realLattice_discreteTopology (t : Tableau n μ) : DiscreteTopology (realLattice t) :=
  DiscreteTopology.of_forall_le_norm zero_lt_one (one_le_norm_realLattice t)

instance spanLattice_discreteTopology (t : Tableau n μ) : DiscreteTopology (spanLattice t) :=
  ZLattice.comap_discreteTopology ℝ (realLattice t) continuous_subtype_val
    (realSpan t).subtype_injective

theorem image_spanLattice (t : Tableau n μ) :
    (realSpan t).subtype '' (spanLattice t : Set _) = (realLattice t : Set _) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, Submodule.subset_span hx⟩, hx, rfl⟩

/-- The orbit lattice is full in its real span. -/
instance spanLattice_isZLattice (t : Tableau n μ) : IsZLattice ℝ (spanLattice t) where
  span_top := by
    apply Submodule.map_injective_of_injective (realSpan t).subtype_injective
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, image_spanLattice]
    rfl

/-- The integral orbit module embeds in its real Hilbert span. -/
def latticeEmbedding (t : Tableau n μ) : orbitLattice t →ₗ[ℤ] realSpan t :=
  (realCast n (μ.colLen 0)).restrict (q := (realSpan t).restrictScalars ℤ)
    fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩

theorem latticeEmbedding_injective (t : Tableau n μ) :
    Function.Injective (latticeEmbedding t) :=
  fun _ _ h => Subtype.ext (realCast_injective (congrArg Subtype.val h))

theorem range_latticeEmbedding (t : Tableau n μ) :
    LinearMap.range (latticeEmbedding t) = spanLattice t := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.property, rfl⟩
  · rintro ⟨y, hy, he⟩
    exact ⟨⟨y, hy⟩, Subtype.ext he⟩

/-- The original integral orbit module and its Hilbert realization are the same lattice. -/
def latticeEquiv (t : Tableau n μ) : orbitLattice t ≃ₗ[ℤ] spanLattice t :=
  (LinearEquiv.ofInjective (latticeEmbedding t) (latticeEmbedding_injective t)).trans
    (LinearEquiv.ofEq _ _ (range_latticeEmbedding t))

@[simp] theorem latticeEquiv_coe (t : Tableau n μ) (x : orbitLattice t) :
    (latticeEquiv t x : realSpan t) = latticeEmbedding t x := rfl

theorem inner_latticeEmbedding (t : Tableau n μ) (x y : orbitLattice t) :
    inner ℝ (latticeEmbedding t x) (latticeEmbedding t y) =
      ∑ w, ((x : (Fin n → Fin (μ.colLen 0)) → ℤ) w : ℝ) * (y.val w : ℝ) := by
  change inner ℝ (realCast n (μ.colLen 0) x.val) (realCast n (μ.colLen 0) y.val) = _
  exact inner_realCast x.val y.val

open Module MeasureTheory

/-- The covolume square is the determinant of an integer coordinate Gram matrix. -/
theorem covolume_sq_eq_integer_gram (t : Tableau n μ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℤ (orbitLattice t)) :
    ZLattice.covolume (spanLattice t) ^ 2 =
      (((Matrix.of fun i j : ι => ∑ w, (b i).val w * (b j).val w).det : ℤ) : ℝ) := by
  rw [ZLattice.covolume_sq_eq_det_gram _ (b.map (latticeEquiv t))]
  change _ = (Int.castRingHom ℝ) _
  rw [RingHom.map_det]
  congr 1
  ext i j
  simpa [Matrix.gram_apply] using inner_latticeEmbedding t (b i) (b j)

/-- Integral word coordinates force the Specht covolume to be at least one. -/
theorem one_le_covolume (t : Tableau n μ) : 1 ≤ ZLattice.covolume (spanLattice t) := by
  let b := Module.finBasis ℤ (orbitLattice t)
  let G : Matrix (Fin (finrank ℤ (orbitLattice t))) (Fin (finrank ℤ (orbitLattice t))) ℤ :=
    Matrix.of fun i j => ∑ w, (b i).val w * (b j).val w
  have he : ZLattice.covolume (spanLattice t) ^ 2 = (G.det : ℝ) :=
    covolume_sq_eq_integer_gram t b
  have hp := ZLattice.covolume_pos (spanLattice t) volume
  have hG : 0 < G.det := by
    have : (0 : ℝ) < (G.det : ℝ) := he ▸ sq_pos_of_pos hp
    exact_mod_cast this
  have hG1 : (1 : ℝ) ≤ (G.det : ℝ) := by exact_mod_cast hG
  nlinarith

/-- This paper, equation (3.17), lower bound. -/
theorem log_covolume_nonneg (t : Tableau n μ) :
    0 ≤ Real.log (ZLattice.covolume (spanLattice t)) :=
  Real.log_nonneg (one_le_covolume t)

/-- Integral vectors forming a real basis give a Gram upper bound, without
requiring them to form an integral basis of the full orbit lattice. -/
theorem covolume_sq_le_det_gram (t : Tableau n μ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ (realSpan t))
    (hb : ∀ i, b i ∈ spanLattice t) :
    ZLattice.covolume (spanLattice t) ^ 2 ≤ (Matrix.gram ℝ b).det := by
  have hle : Submodule.span ℤ (Set.range b) ≤ spanLattice t := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hb i
  rw [← ZLattice.covolume_span_sq_eq_det_gram b]
  exact pow_le_pow_left₀ (ZLattice.covolume_pos (spanLattice t) volume).le
    (ZLattice.covolume_le_covolume_of_le hle) 2

/-- The logarithmic Gram bound used for the full-rank standard sublattice route. -/
theorem two_mul_log_covolume_le_log_det_gram (t : Tableau n μ) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (b : Basis ι ℝ (realSpan t))
    (hb : ∀ i, b i ∈ spanLattice t) :
    2 * Real.log (ZLattice.covolume (spanLattice t)) ≤ Real.log (Matrix.gram ℝ b).det := by
  have h := Real.log_le_log
    (sq_pos_of_pos (ZLattice.covolume_pos (spanLattice t) volume))
    (covolume_sq_le_det_gram t b hb)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

end BostConjecture.Specht
