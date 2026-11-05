module

public import BostConjecture.Geometry.DeterminantFrame

/-!
# Position equivariance of the determinant tensor inclusion

The integral orbit action is transported through the canonical tensor basis.
The determinant twist carries the trivial position action.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct
open scoped TensorProduct

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {n a k : ℕ}

/-- Position permutation acts on word coordinates by precomposition. -/
theorem tensorCoordinates_reindex (b : Basis (Fin a) R M) (σ : Equiv.Perm (Fin n))
    (z : ⨂[R] (_ : Fin n), M) (w : Fin n → Fin a) :
    tensorCoordinates n b (reindex R (fun _ : Fin n => M) σ z) w =
      tensorCoordinates n b z (w ∘ σ) := by
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    simp only [map_smul, reindex_tprod, tensorCoordinates_tprod, Pi.smul_apply]
    congr 1
    simpa using σ.symm.prod_comp (fun q => b.repr (v q) (w (σ q)))
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- The free lattice realization intertwines the actual integral orbit action. -/
theorem freeLatticeMap_reindex (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M)
    (σ : Equiv.Perm (Fin n)) (z : R ⊗[ℤ] Specht.orbitLattice t) :
    freeLatticeMap hk t b ((Specht.orbitAction t σ).baseChange R z) =
      reindex R (fun _ : Fin n => M) σ (freeLatticeMap hk t b z) := by
  induction z using TensorProduct.inductionOn with
  | tmul r x =>
    apply (tensorCoordinates n b).injective
    ext w
    simp [tensorCoordinates_reindex, Specht.orbitAction, Specht.wordRepInt,
      Specht.rectangleAlphabetEquiv, Function.comp_def]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The determinant factor is fixed and the integral lattice carries the
position action in the determinant-twisted inclusion. -/
theorem freeDeterminantMap_reindex (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k)) (b : Basis (Fin a) R M)
    (σ : Equiv.Perm (Fin n))
    (z : (⨂[R] (_ : Fin k), ⋀[R]^a M) ⊗[R] (R ⊗[ℤ] Specht.orbitLattice t)) :
    freeDeterminantMap hk t b
      (TensorProduct.map LinearMap.id ((Specht.orbitAction t σ).baseChange R) z) =
    reindex R (fun _ : Fin n => M) σ (freeDeterminantMap hk t b z) := by
  induction z using TensorProduct.inductionOn with
  | tmul η x =>
    simp only [TensorProduct.map_tmul, LinearMap.id_apply, freeDeterminantMap_tmul,
      freeLatticeMap_reindex, map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

end BostConjecture.Geometry
