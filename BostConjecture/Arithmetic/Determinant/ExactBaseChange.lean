/-
Copyright (c) 2026 Yijun Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yijun Yuan
-/
module

public import BostConjecture.Arithmetic.Determinant.Exact
public import Mathlib.RingTheory.Flat.Equalizer

/-!
# Computing the exact determinant with sections after scalar extension

Over a faithfully receiving field, the integral exact determinant can be
computed using any section of the extended quotient map. The section need
not descend to the integral module; this permits the orthogonal section.
-/

@[expose] public section

noncomputable section

open Module TensorProduct

namespace exteriorPower

variable {R M N P : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    [AddCommGroup P] [Module R P]
    (i : M →ₗ[R] P) (q : P →ₗ[R] N) (h : Function.Exact i q) (hi : Function.Injective i)

include h hi in
/-- Section independence written at specified exterior degrees. -/
lemma map_coprod_prodMap_eq_of_sections (a b : ℕ)
    (ha : Module.finrank R M = a) (hb : Module.finrank R N = b)
    (s t : N →ₗ[R] P) (hs : q.comp s = LinearMap.id) (ht : q.comp t = LinearMap.id)
    (z : (⋀[R]^a M) ⊗[R] (⋀[R]^b N)) :
    map (a + b) (i.coprod s) (prodMap R M N a b z) =
      map (a + b) (i.coprod t) (prodMap R M N a b z) := by
  subst a b
  exact LinearEquiv.congr_fun (exactEquivOfSection_eq i q h hi s t hs ht) z

/-- An arbitrary section after extension to a faithful field computes the
actual integral exact determinant, including sections that do not descend. -/
lemma exactEquiv_baseChange_field_section (hq : Function.Surjective q)
    (S : Type*) [Field S] [Algebra R S] [FaithfulSMul R S]
    (t : (S ⊗[R] N) →ₗ[S] (S ⊗[R] P))
    (ht : (q.baseChange S).comp t = LinearMap.id)
    (x : ⋀[R]^(Module.finrank R M) M) (y : ⋀[R]^(Module.finrank R N) N) :
    baseChangeEquiv R P S (Module.finrank R M + Module.finrank R N)
        (1 ⊗ₜ[R] exactEquiv i q h hi hq (x ⊗ₜ[R] y)) =
      map (Module.finrank R M + Module.finrank R N) ((i.baseChange S).coprod t)
        (prodMap S (S ⊗[R] M) (S ⊗[R] N) (Module.finrank R M) (Module.finrank R N)
          (baseChangeEquiv R M S _ (1 ⊗ₜ[R] x) ⊗ₜ[S]
            baseChangeEquiv R N S _ (1 ⊗ₜ[R] y))) := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  rw [exactEquiv_baseChange_section i q h hi hq S s hs]
  have he : Function.Exact (i.baseChange S) (q.baseChange S) := lTensor_exact S h hq
  have hiS : Function.Injective (i.baseChange S) :=
    LinearMap.lTensor_injective_of_exact_of_flat q hq i hi h S
  have hsS : (q.baseChange S).comp (s.baseChange S) = LinearMap.id := by
    rw [← LinearMap.baseChange_comp, hs, LinearMap.baseChange_id]
  exact map_coprod_prodMap_eq_of_sections (i.baseChange S) (q.baseChange S) he hiS
    _ _ (TensorProduct.isBaseChange R M S).finrank_eq
    (TensorProduct.isBaseChange R N S).finrank_eq _ _ hsS ht _

end exteriorPower
