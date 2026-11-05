module

public import BostConjecture.Specht.Integral

/-!
# Independence of the enumerating tableau

Relabeling a tableau conjugates its column stabilizer and transports its
integral polytabloid. Thus the integral orbit span is the span of all
polytabloids of the shape. Reference: manuscript §3, page 4.
-/

@[expose] public section

noncomputable section

namespace BostConjecture.Specht

open OAI.Saxl

variable {n : ℕ} {μ : YoungDiagram}

/-- Relabel positions by `g`, without changing the Young diagram. -/
def relabel (g : Equiv.Perm (Fin n)) (t : Tableau n μ) : Tableau n μ := g.symm.trans t

@[simp] theorem rowWord_relabel (g : Equiv.Perm (Fin n)) (t : Tableau n μ) :
    rowWord (relabel g t) = rowWord t ∘ (g⁻¹ : Equiv.Perm (Fin n)) := rfl

/-- Relabeling conjugates the column group. -/
def columnGroupRelabelEquiv (g : Equiv.Perm (Fin n)) (t : Tableau n μ) :
    columnGroup t ≃ columnGroup (relabel g t) where
  toFun h := ⟨g * h * g⁻¹, by
    intro i
    simpa [relabel] using h.property (g⁻¹ i)⟩
  invFun h := ⟨g⁻¹ * h * g, by
    intro i
    simpa [relabel] using h.property (g i)⟩
  left_inv h := by apply Subtype.ext; simp [mul_assoc]
  right_inv h := by apply Subtype.ext; simp [mul_assoc]

@[simp] theorem complexCast_single {d : ℕ} (w : Fin n → Fin d) :
    complexCast n d (Pi.single w 1) = Pi.single w 1 := by
  classical
  ext a
  simp [complexCast, Pi.single_apply]

theorem wordRepInt_single {d : ℕ} (g : Equiv.Perm (Fin n)) (w : Fin n → Fin d) :
    wordRepInt n d g (Pi.single w 1) = Pi.single (w ∘ (g⁻¹ : Equiv.Perm (Fin n))) 1 := by
  apply complexCast_injective
  simp [wordRep_single]

/-- The integral polytabloid transforms by the same position permutation as the tableau. -/
theorem polytabloidInt_relabel (g : Equiv.Perm (Fin n)) (t : Tableau n μ) :
    polytabloidInt (relabel g t) = wordRepInt n (μ.colLen 0) g (polytabloidInt t) := by
  classical
  let := Fintype.ofFinite (columnGroup t)
  let := Fintype.ofFinite (columnGroup (relabel g t))
  unfold polytabloidInt
  rw [← Equiv.sum_comp (columnGroupRelabelEquiv g t)]
  simp only [map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro h hh
  have hs : (Equiv.Perm.sign
      ((columnGroupRelabelEquiv g t h : columnGroup (relabel g t)) : Equiv.Perm (Fin n)) : ℤ) =
      (Equiv.Perm.sign (h : Equiv.Perm (Fin n)) : ℤ) := by
    change (Equiv.Perm.sign (g * (h : Equiv.Perm (Fin n)) * g⁻¹) : ℤ) = _
    rw [map_mul, map_mul, map_inv, mul_comm (Equiv.Perm.sign g), mul_assoc,
      mul_inv_cancel, mul_one]
  rw [hs]
  congr 1
  rw [wordRepInt_single, wordRepInt_single, wordRepInt_single, rowWord_relabel]
  congr 1
  ext i
  simp [columnGroupRelabelEquiv]

/-- The orbit generators are precisely all integral polytabloids of the shape. -/
theorem range_orbit_eq_range_polytabloid (t : Tableau n μ) :
    Set.range (fun g => wordRepInt n (μ.colLen 0) g (polytabloidInt t)) =
      Set.range (polytabloidInt (n := n) (μ := μ)) := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨relabel g t, polytabloidInt_relabel g t⟩
  · rintro ⟨u, rfl⟩
    refine ⟨t.trans u.symm, ?_⟩
    change wordRepInt n (μ.colLen 0) (t.trans u.symm) (polytabloidInt t) = _
    rw [← polytabloidInt_relabel]
    congr 1
    ext i <;> simp [relabel]

/-- The orbit lattice equals the integral span of all polytabloids. -/
theorem orbitLattice_eq_span_polytabloids (t : Tableau n μ) :
    orbitLattice t = Submodule.span ℤ (Set.range (polytabloidInt (n := n) (μ := μ))) := by
  rw [orbitLattice, range_orbit_eq_range_polytabloid]

theorem orbitLattice_eq (t u : Tableau n μ) : orbitLattice t = orbitLattice u := by
  rw [orbitLattice_eq_span_polytabloids, orbitLattice_eq_span_polytabloids]

end BostConjecture.Specht
