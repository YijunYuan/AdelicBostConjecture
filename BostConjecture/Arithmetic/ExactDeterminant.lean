module

public import BostConjecture.Arithmetic.DeterminantProduct
public import BostConjecture.Arithmetic.ProjectiveDeterminantShear

/-!
# The determinant of a projective exact sequence

A section of the quotient map constructs an actual determinant isomorphism.
The projective shear identity proves that the result is independent of this
section. No integral basis or determinant-calculus certificate is used.
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

/-- The determinant isomorphism constructed from a section of an exact sequence. -/
def exactEquivOfSection (s : N →ₗ[R] P) (hs : q.comp s = LinearMap.id) :
    (⋀[R]^(Module.finrank R M) M) ⊗[R] (⋀[R]^(Module.finrank R N) N) ≃ₗ[R]
      ⋀[R]^(Module.finrank R M + Module.finrank R N) P := by
  let e := (h.splitSurjectiveEquiv hi ⟨s, hs⟩).1.symm
  exact prodEquiv.trans (LinearEquiv.ofBijective (map _ e.toLinearMap)
    ⟨map_injective e.symm.toLinearMap (by
      apply LinearMap.ext
      intro x
      exact e.symm_apply_apply x), map_surjective e.surjective⟩)

@[simp]
lemma exactEquivOfSection_apply (s : N →ₗ[R] P) (hs : q.comp s = LinearMap.id)
    (z : (⋀[R]^(Module.finrank R M) M) ⊗[R] (⋀[R]^(Module.finrank R N) N)) :
    exactEquivOfSection i q h hi s hs z =
      map (Module.finrank R M + Module.finrank R N) (i.coprod s)
        (prodMap R M N _ _ z) := rfl

/-- Changing the section does not change the projective determinant isomorphism. -/
lemma exactEquivOfSection_eq (s s' : N →ₗ[R] P)
    (hs : q.comp s = LinearMap.id) (hs' : q.comp s' = LinearMap.id) :
    exactEquivOfSection i q h hi s hs = exactEquivOfSection i q h hi s' hs' := by
  let e := (h.splitSurjectiveEquiv hi ⟨s, hs⟩).1.symm
  let t := (LinearMap.fst R M N).comp (e.symm.toLinearMap.comp s')
  have he (x : M × N) : e x = i x.1 + s x.2 := rfl
  have hq (x : P) : (e.symm x).2 = q x :=
    (LinearMap.congr_fun (h.splitSurjectiveEquiv hi ⟨s, hs⟩).2.2 x).symm
  have ht (y : N) : i (t y) + s y = s' y := by
    have hy := e.apply_symm_apply (s' y)
    have hqs : q (s' y) = y := LinearMap.congr_fun hs' y
    rw [he, hq, hqs] at hy
    exact hy
  have hc : i.coprod s' = (i.coprod s).comp (upperShear t) := by
    apply LinearMap.ext
    intro x
    change i x.1 + s' x.2 = i (x.1 + t x.2) + s x.2
    rw [map_add, add_assoc, ht]
  apply LinearEquiv.ext
  intro z
  simp only [exactEquivOfSection_apply]
  rw [hc, map_comp, LinearMap.comp_apply, map_upperShear_top]

/-- Projectivity provides the section; its choice has no effect on the map. -/
def exactEquiv (hq : Function.Surjective q) :
    (⋀[R]^(Module.finrank R M) M) ⊗[R] (⋀[R]^(Module.finrank R N) N) ≃ₗ[R]
      ⋀[R]^(Module.finrank R M + Module.finrank R N) P :=
  exactEquivOfSection i q h hi
    (q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)).choose
    (q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)).choose_spec

lemma exactEquiv_eq_of_section (hq : Function.Surjective q)
    (s : N →ₗ[R] P) (hs : q.comp s = LinearMap.id) :
    exactEquiv i q h hi hq = exactEquivOfSection i q h hi s hs :=
  exactEquivOfSection_eq i q h hi _ _ _ _

omit [Module.Projective R M] in
include h hi in
/-- Rank additivity of a finite projective exact sequence over a domain. -/
lemma finrank_exact (hq : Function.Surjective q) :
    Module.finrank R P = Module.finrank R M + Module.finrank R N := by
  obtain ⟨s, hs⟩ := q.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hq)
  let e := (h.splitSurjectiveEquiv hi ⟨s, hs⟩).1
  let F := FractionRing R
  rw [← (TensorProduct.isBaseChange R P F).finrank_eq, (e.baseChange R F P (M × N)).finrank_eq,
    (TensorProduct.prodRight R F F M N).finrank_eq, Module.finrank_prod,
    (TensorProduct.isBaseChange R M F).finrank_eq,
    (TensorProduct.isBaseChange R N F).finrank_eq]

/-- The exact determinant map commutes with scalar extension on integral
determinant tensors, using any section of the original sequence. -/
lemma exactEquiv_baseChange_section (hq : Function.Surjective q)
    (S : Type*) [CommRing S] [Algebra R S]
    (s : N →ₗ[R] P) (hs : q.comp s = LinearMap.id)
    (x : ⋀[R]^(Module.finrank R M) M) (y : ⋀[R]^(Module.finrank R N) N) :
    baseChangeEquiv R P S (Module.finrank R M + Module.finrank R N)
        (1 ⊗ₜ[R] exactEquiv i q h hi hq (x ⊗ₜ[R] y)) =
      map (Module.finrank R M + Module.finrank R N)
        ((i.baseChange S).coprod (s.baseChange S))
        (prodMap S (S ⊗[R] M) (S ⊗[R] N) (Module.finrank R M) (Module.finrank R N)
          (baseChangeEquiv R M S _ (1 ⊗ₜ[R] x) ⊗ₜ[S]
            baseChangeEquiv R N S _ (1 ⊗ₜ[R] y))) := by
  rw [exactEquiv_eq_of_section i q h hi hq s hs, exactEquivOfSection_apply,
    map_baseChange_section]
  rw [← prodMap_baseChange_section R M N S]
  have hc : ((i.baseChange S).coprod (s.baseChange S)).comp
      (TensorProduct.prodRight R S S M N).toLinearMap = (i.coprod s).baseChange S := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro c z
    simp [tmul_add]
  rw [← LinearMap.comp_apply, ← map_comp, hc]

end exteriorPower
