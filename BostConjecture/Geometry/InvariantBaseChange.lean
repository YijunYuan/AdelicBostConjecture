module

public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Scalar extension of evaluation on a coefficient kernel

This uses Mathlib's canonical flat kernel equivalence. The future coaction
consumer must still identify its degree space and coefficient map with their
scalar extensions; no abstract group invariants are silently substituted for
an algebraic coaction kernel.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open TensorProduct

variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]
  (f : M →ₗ[R] N) (e : M →ₗ[R] P)

/-- Restriction of evaluation commutes with the actual flat kernel isomorphism. -/
theorem baseChange_apply_tensorKer [Module.Flat R S] (x : S ⊗[R] LinearMap.ker f) :
    e.baseChange S (LinearMap.tensorKerEquiv S S f x) =
      (e.comp (LinearMap.ker f).subtype).baseChange S x := by
  induction x using TensorProduct.inductionOn with
  | tmul s x => simp
  | add x y hx hy => simp only [map_add, hx, hy, Submodule.coe_add]

/-- Nonzero evaluation on a coefficient kernel is detected by faithfully flat
scalar extension, without finiteness or freeness assumptions. -/
theorem exists_ker_baseChange_ne_zero_iff [Module.FaithfullyFlat R S] :
    (∃ y ∈ LinearMap.ker (f.baseChange S), e.baseChange S y ≠ 0) ↔
      ∃ x ∈ LinearMap.ker f, e x ≠ 0 := by
  constructor
  · rintro ⟨y, hy, hey⟩
    by_contra h
    push Not at h
    have he : e.comp (LinearMap.ker f).subtype = 0 := by
      ext x
      exact h x x.property
    obtain ⟨x, hx⟩ := (LinearMap.tensorKerEquiv S S f).surjective ⟨y, hy⟩
    have hh := baseChange_apply_tensorKer S f e x
    rw [hx, he] at hh
    exact hey (by simpa using hh)
  · rintro ⟨x, hx, hex⟩
    refine ⟨1 ⊗ₜ[R] x, ?_, ?_⟩
    · simp only [LinearMap.mem_ker, LinearMap.baseChange_tmul,
        LinearMap.mem_ker.mp hx, TensorProduct.tmul_zero]
    · simpa only [LinearMap.baseChange_tmul] using
        (Module.FaithfullyFlat.one_tmul_eq_zero_iff (R := R) (M := P) (A := S) (e x)).not.mpr hex

end BostConjecture.Geometry
