module

public import BostConjecture.Arithmetic.DeterminantLine

/-!
# Perfect exterior duality for finite projective modules

Mathlib's canonical determinant evaluation is natural. A finite-free
splitting transports its perfectness from the wedge basis calculation to
every finite projective module, without an integral basis or division by
an exterior-degree factorial.
-/

@[expose] public section

noncomputable section

namespace exteriorPower

open Module

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- Naturality of canonical exterior duality. -/
lemma pairingDual_natural (f : M →ₗ[R] N) (n : ℕ) :
    (pairingDual R M n).comp (map n f.dualMap) =
      (map n f).dualMap.comp (pairingDual R N n) := by
  apply linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply linearMap_ext
  apply AlternatingMap.ext
  intro w
  simp [map_apply_ιMulti, pairingDual_ιMulti_ιMulti]

/-- The exterior pairing is bijective in a finite basis. -/
lemma pairingDual_bijective_of_basis {ι : Type*} [Finite ι]
    (b : Basis ι R M) (n : ℕ) : Function.Bijective (pairingDual R M n) := by
  classical
  let e := (b.dualBasis.exteriorPower n).equiv ((b.exteriorPower n).dualBasis) (Equiv.refl _)
  have he : pairingDual R M n = e.toLinearMap := by
    apply (b.dualBasis.exteriorPower n).ext
    intro s
    simp [e, pairingDual_apply_dualBasis_exteriorPower]
  rw [he]
  exact e.bijective

variable (R M) [Module.Finite R M] [Module.Projective R M]

/-- Canonical exterior evaluation is perfect for finite projective modules. -/
lemma pairingDual_bijective (n : ℕ) : Function.Bijective (pairingDual R M n) := by
  obtain ⟨d, p, i, _, _, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  let e : (⋀[R]^n (Dual R (Fin d → R))) ≃ₗ[R] Dual R (⋀[R]^n (Fin d → R)) :=
    LinearEquiv.ofBijective (pairingDual R (Fin d → R) n)
      (pairingDual_bijective_of_basis (Pi.basisFun R (Fin d)) n)
  let q := (map n i.dualMap).comp (e.symm.toLinearMap.comp (map n p).dualMap)
  have he (z : ⋀[R]^n (Dual R (Fin d → R))) : e z = pairingDual R (Fin d → R) n z := rfl
  have hnat (f : M →ₗ[R] (Fin d → R)) (z : ⋀[R]^n (Dual R (Fin d → R))) :
      pairingDual R M n (map n f.dualMap z) =
        (map n f).dualMap (pairingDual R (Fin d → R) n z) :=
    LinearMap.congr_fun (pairingDual_natural f n) z
  have hnatp (z : ⋀[R]^n (Dual R M)) :
      (map n p).dualMap (pairingDual R M n z) =
        pairingDual R (Fin d → R) n (map n p.dualMap z) :=
    (LinearMap.congr_fun (pairingDual_natural p n) z).symm
  have hleft : Function.LeftInverse q (pairingDual R M n) := by
    intro z
    dsimp only [q, LinearMap.comp_apply]
    rw [hnatp, ← he, e.symm_apply_apply]
    change ((map n i.dualMap).comp (map n p.dualMap)) z = z
    rw [← map_comp, ← LinearMap.dualMap_comp_dualMap, hpi]
    simp
  have hright : Function.RightInverse q (pairingDual R M n) := by
    intro f
    dsimp only [q, LinearMap.comp_apply]
    rw [hnat i, ← he, e.apply_symm_apply]
    change ((map n i).dualMap.comp (map n p).dualMap) f = f
    rw [← LinearMap.dualMap_comp_dualMap, ← map_comp, hpi]
    simp
  exact ⟨hleft.injective, hright.surjective⟩

/-- The canonical finite-projective exterior-duality equivalence. -/
def pairingDualEquiv (n : ℕ) : ⋀[R]^n (Dual R M) ≃ₗ[R] Dual R (⋀[R]^n M) :=
  LinearEquiv.ofBijective (pairingDual R M n) (pairingDual_bijective R M n)

@[simp]
lemma pairingDualEquiv_apply (n : ℕ) (z : ⋀[R]^n (Dual R M)) :
    pairingDualEquiv R M n z = pairingDual R M n z := rfl

end exteriorPower
