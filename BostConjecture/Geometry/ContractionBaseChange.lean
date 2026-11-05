module

public import BostConjecture.Geometry.Contraction
public import BostConjecture.Tensor.PairingBaseChange

/-! # Scalar extension of the actual integral determinant pairing -/

@[expose] public section

noncomputable section

namespace BostConjecture.Geometry

open Module PiTensorProduct
open scoped TensorProduct

private theorem tensorMap_comp_apply_eq {K I : Type*} [CommRing K]
    {A B C D : I → Type*}
    [∀ i, AddCommMonoid (A i)] [∀ i, Module K (A i)]
    [∀ i, AddCommMonoid (B i)] [∀ i, Module K (B i)]
    [∀ i, AddCommMonoid (C i)] [∀ i, Module K (C i)]
    [∀ i, AddCommMonoid (D i)] [∀ i, Module K (D i)]
    (f : ∀ i, A i →ₗ[K] B i) (g : ∀ i, B i →ₗ[K] D i)
    (h : ∀ i, A i →ₗ[K] C i) (k : ∀ i, C i →ₗ[K] D i)
    (hf : ∀ i x, g i (f i x) = k i (h i x)) (w : ⨂[K] i, A i) :
    map g (map f w) = map k (map h w) := by
  induction w using PiTensorProduct.induction_on with
  | smul_tprod r x => simp only [map_smul, map_tprod, hf]
  | add x y hx hy => simp only [map_add, hx, hy]

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
  {n a k : ℕ}

/-- The determinant twist of the integral dual is transported using the actual
dual base-change equivalence on every exterior factor. -/
def dualDeterminantTwistBaseChange (L : Type*) [AddCommGroup L] (k a : ℕ) :
    S ⊗[R] ((⨂[R] (_ : Fin k), ⋀[R]^a (Dual R M)) ⊗[R] (R ⊗[ℤ] L)) →ₗ[S]
      (⨂[S] (_ : Fin k), ⋀[S]^a (Dual S (S ⊗[R] M))) ⊗[S] (S ⊗[ℤ] L) :=
  TensorProduct.map
    (map (fun _ : Fin k => exteriorPower.map a
      (Arithmetic.dualBaseChangeEquiv R S M).toLinearMap)) LinearMap.id ∘ₗ
        (determinantTwistBaseChangeEquiv (R := R) (S := S) (M := Dual R M) L k a).toLinearMap

/-- Scalar extension of the actual projective dual determinant map equals its
free formula in every frame of the complex or algebraic dual. -/
theorem projectiveDualDeterminantMap_baseChange (hk : 0 < k)
    (t : OAI.Saxl.Tableau n (Specht.rectangle a k))
    (ha : ∀ p : PrimeSpectrum R, Module.rankAtStalk (Dual R M) p = a)
    (b : Basis (Fin a) S (Dual S (S ⊗[R] M)))
    (x : S ⊗[R] ((⨂[R] (_ : Fin k), ⋀[R]^a (Dual R M)) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice t))) :
    map (fun _ : Fin n => (Arithmetic.dualBaseChangeEquiv R S M).toLinearMap)
      (Tensor.baseChangeEquiv R S (fun _ : Fin n => Dual R M)
        ((projectiveDeterminantMap hk t ha).baseChange S x)) =
    freeDeterminantMap hk t b (dualDeterminantTwistBaseChange (Specht.orbitLattice t) k a x) := by
  let c := b.map (Arithmetic.dualBaseChangeEquiv R S M).symm
  rw [projectiveDeterminantMap_baseChange_of_basis hk t ha c]
  simp only [determinantChart, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact LinearMap.congr_fun
    (map_freeDeterminantMap hk t c b (Arithmetic.dualBaseChangeEquiv R S M).toLinearMap) _

/-- The canonical dual determinant transport is bijective. -/
theorem dualDeterminantTwistBaseChange_bijective (L : Type*) [AddCommGroup L] (k a : ℕ) :
    Function.Bijective (dualDeterminantTwistBaseChange (R := R) (S := S) (M := M) L k a) := by
  let d := Arithmetic.dualBaseChangeEquiv R S M
  let e : (⋀[S]^a (S ⊗[R] Dual R M)) ≃ₗ[S] ⋀[S]^a (Dual S (S ⊗[R] M)) :=
    LinearEquiv.ofBijective (exteriorPower.map a d.toLinearMap)
      ⟨exteriorPower.map_injective d.symm.toLinearMap (by ext x; simp),
        exteriorPower.map_surjective d.surjective⟩
  let f := (determinantTwistBaseChangeEquiv (R := R) (S := S) (M := Dual R M) L k a).trans
    (TensorProduct.congr (PiTensorProduct.congr (fun _ : Fin k => e)) (LinearEquiv.refl S _))
  change Function.Bijective f
  exact f.bijective

variable {ι : Type*} [Fintype ι] (E : ι → Type*)
  [∀ j, AddCommGroup (E j)] [∀ j, Module R (E j)]
  [∀ j, Module.Finite R (E j)] [∀ j, Module.Projective R (E j)]
  {a k : ι → ℕ}
  (hk : ∀ j, 0 < k j)
  (t : ∀ j, OAI.Saxl.Tableau n (Specht.rectangle (a j) (k j)))
  (ha : ∀ j (p : PrimeSpectrum R), Module.rankAtStalk (Dual R (E j)) p = a j)
  (b : ∀ j, Basis (Fin (a j)) S (Dual S (S ⊗[R] E j)))

local instance : ∀ j, AddCommGroup
    ((⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t j))) := fun _ =>
        Module.addCommMonoidToAddCommGroup R

local instance : ∀ j, Module R
    ((⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t j))) := fun _ => inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- The tensor product of the canonical dual determinant scalar extensions. -/
def dualDeterminantTensorBaseChange :
    S ⊗[R] (⨂[R] j, (⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t j))) →ₗ[S]
    (⨂[S] j, (⨂[S] (_ : Fin (k j)), ⋀[S]^(a j) (Dual S (S ⊗[R] E j))) ⊗[S]
      (S ⊗[ℤ] Specht.orbitLattice (t j))) :=
  map (fun j => dualDeterminantTwistBaseChange (R := R) (S := S) (M := E j)
    (Specht.orbitLattice (t j)) (k j) (a j)) ∘ₗ
      (Tensor.baseChangeEquiv R S (fun j =>
        (⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
          (R ⊗[ℤ] Specht.orbitLattice (t j)))).toLinearMap

set_option backward.isDefEq.respectTransparency false in
/-- The actual tensor of projective determinant factors, including dual regrouping,
has the expected free formula after scalar extension. -/
theorem dualDeterminantMap_baseChange
    (u : S ⊗[R] (⨂[R] j, (⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t j)))) :
    map (R := S) (fun _ : Fin n => (Tensor.tensorDualBaseChangeEquiv R S E).toLinearMap)
      (Tensor.baseChangeEquiv R S (fun _ : Fin n => Dual R (⨂[R] j, E j))
        ((dualDeterminantMap (R := R) E hk t ha).baseChange S u)) =
    Tensor.dualRegroupEquiv S (fun j => S ⊗[R] E j)
      (map (R := S) (fun j => freeDeterminantMap (hk j) (t j) (b j))
        (dualDeterminantTensorBaseChange (R := R) (S := S) E t u)) := by
  simp only [dualDeterminantMap, dualDeterminantTensorBaseChange,
    LinearMap.baseChange_comp, LinearMap.comp_apply]
  rw [Tensor.dualRegroup_baseChange]
  have hn := LinearMap.congr_fun (Tensor.baseChangeEquiv_natural R S
    (fun j => projectiveDeterminantMap (R := R) (M := Dual R (E j))
      (hk j) (t j) (ha j))) u
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hn
  rw [hn]
  congr 1
  simp only [LinearEquiv.coe_coe]
  apply tensorMap_comp_apply_eq
  intro j x
  exact projectiveDualDeterminantMap_baseChange (hk j) (t j) (ha j) (b j) x

variable {V : Type*} [AddCommGroup V] [Module R V]
  [Module.Finite R V] [Module.Projective R V] {s l : ℕ}
  (hl : 0 < l) (v : OAI.Saxl.Tableau n (Specht.rectangle s l))
  (hs : ∀ p : PrimeSpectrum R, Module.rankAtStalk V p = s)
  (bV : Basis (Fin s) S (S ⊗[R] V))

/-- The scalar extension of the actual integral pairing is the free determinant
pairing, on arbitrary vectors in both scalar-extended sources. -/
theorem canonicalPairing_baseChange (i : V →ₗ[R] (⨂[R] j, E j))
    (z : S ⊗[R] ((⨂[R] (_ : Fin l), ⋀[R]^s V) ⊗[R] (R ⊗[ℤ] Specht.orbitLattice v)))
    (u : S ⊗[R] (⨂[R] j, (⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
      (R ⊗[ℤ] Specht.orbitLattice (t j)))) :
    Arithmetic.dualBaseChangeMap R S
      (⨂[R] j, (⨂[R] (_ : Fin (k j)), ⋀[R]^(a j) (Dual R (E j))) ⊗[R]
        (R ⊗[ℤ] Specht.orbitLattice (t j)))
      ((canonicalPairing E hk t ha hl v hs i).baseChange S z) u =
    Tensor.tensorPowerPairing (W := ⨂[S] j, S ⊗[R] E j)
      ((Tensor.baseChangeEquiv R S E).toLinearMap ∘ₗ i.baseChange S)
      (freeDeterminantMap hl v bV
        (determinantTwistBaseChangeEquiv (R := R) (S := S) (M := V)
          (Specht.orbitLattice v) l s z))
      (Tensor.dualRegroupEquiv S (fun j => S ⊗[R] E j)
        (map (fun j => freeDeterminantMap (hk j) (t j) (b j))
          (dualDeterminantTensorBaseChange (R := R) (S := S) E t u))) := by
  rw [← dualDeterminantMap_baseChange E hk t ha b u]
  have hz : freeDeterminantMap hl v bV
      (determinantTwistBaseChangeEquiv (R := R) (S := S) (M := V)
        (Specht.orbitLattice v) l s z) =
      Tensor.baseChangeEquiv R S (fun _ : Fin n => V)
        ((projectiveDeterminantMap hl v hs).baseChange S z) := by
    rw [projectiveDeterminantMap_baseChange_of_basis hl v hs bV]
    simp [determinantChart]
  let iS := (Tensor.baseChangeEquiv R S E).toLinearMap ∘ₗ i.baseChange S
  let uS := map (fun _ : Fin n => (Tensor.tensorDualBaseChangeEquiv R S E).toLinearMap)
    (Tensor.baseChangeEquiv R S (fun _ : Fin n => Dual R (⨂[R] j, E j))
      ((dualDeterminantMap E hk t ha).baseChange S u))
  refine Eq.trans ?_ (congrArg (fun w => Tensor.tensorPowerPairing iS w uS) hz).symm
  refine Eq.trans ?_ (Tensor.tensorPowerPairing_tensorBaseChange R S E i
    ((projectiveDeterminantMap (R := R) (M := V) hl v hs).baseChange S z)
    ((dualDeterminantMap E hk t ha).baseChange S u)).symm
  induction z using TensorProduct.inductionOn with
  | tmul a z =>
    induction u using TensorProduct.inductionOn with
    | tmul b u =>
      simp only [LinearMap.baseChange_tmul, Arithmetic.dualBaseChangeMap_tmul,
        Arithmetic.dualBaseChangeEquiv_tmul, canonicalPairing_apply]
    | add u w hu hw => simp only [map_add, hu, hw]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end BostConjecture.Geometry
